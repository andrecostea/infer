(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
module AccessExpression = HilExp.AccessExpression
module F = Format
module L = Logging
module MF = MarkupFormatter

let describe_pname = MF.wrap_monospaced Procname.pp

let pp_exp fmt exp =
  match !Language.curr_language with
  | Clang ->
      AccessExpression.pp fmt exp
  | Java ->
      AccessPath.pp fmt (AccessExpression.to_access_path exp)


let rec should_keep_exp formals (exp : AccessExpression.t) =
  match exp with
  | FieldOffset (prefix, fld) ->
      (not (String.is_substring ~substring:"$SwitchMap" (Fieldname.get_field_name fld)))
      && should_keep_exp formals prefix
  | ArrayOffset (prefix, _, _) | AddressOf prefix | Dereference prefix ->
      should_keep_exp formals prefix
  | Base (LogicalVar _, _) ->
      false
  | Base (((ProgramVar pvar as var), _) as base) ->
      Var.appears_in_source_code var
      && (not (Pvar.is_static_local pvar))
      && (Pvar.is_global pvar || FormalMap.is_formal base formals)


module Access = struct
  type t =
    | Read of {exp: AccessExpression.t}
    | Write of {exp: AccessExpression.t}
    | ContainerRead of {exp: AccessExpression.t; pname: Procname.t}
    | ContainerWrite of {exp: AccessExpression.t; pname: Procname.t}
    | InterfaceCall of {exp: AccessExpression.t; pname: Procname.t}
  [@@deriving compare]

  let make_field_access exp ~is_write = if is_write then Write {exp} else Read {exp}

  let make_container_access exp pname ~is_write =
    if is_write then ContainerWrite {exp; pname} else ContainerRead {exp; pname}


  let make_unannotated_call_access exp pname = InterfaceCall {exp; pname}

  let is_write = function
    | InterfaceCall _ | Read _ | ContainerRead _ ->
        false
    | ContainerWrite _ | Write _ ->
        true


  let is_container_write = function
    | InterfaceCall _ | Read _ | Write _ | ContainerRead _ ->
        false
    | ContainerWrite _ ->
        true


  let get_access_exp = function
    | Read {exp} | Write {exp} | ContainerWrite {exp} | ContainerRead {exp} | InterfaceCall {exp} ->
        exp


  let should_keep formals access = get_access_exp access |> should_keep_exp formals

  let map ~f access =
    match access with
    | Read {exp} ->
        let exp' = f exp in
        if phys_equal exp exp' then access else Read {exp= exp'}
    | Write {exp} ->
        let exp' = f exp in
        if phys_equal exp exp' then access else Write {exp= exp'}
    | ContainerWrite ({exp} as record) ->
        let exp' = f exp in
        if phys_equal exp exp' then access else ContainerWrite {record with exp= exp'}
    | ContainerRead ({exp} as record) ->
        let exp' = f exp in
        if phys_equal exp exp' then access else ContainerRead {record with exp= exp'}
    | InterfaceCall ({exp} as record) ->
        let exp' = f exp in
        if phys_equal exp exp' then access else InterfaceCall {record with exp= exp'}

  let pp fmt = function
    | Read {exp} ->
        F.fprintf fmt "Read of %a" AccessExpression.pp exp
    | Write {exp} ->
        F.fprintf fmt "Write to %a" AccessExpression.pp exp
    | ContainerRead {exp; pname} ->
        F.fprintf fmt "Read of container %a via %a" AccessExpression.pp exp Procname.pp pname
    | ContainerWrite {exp; pname} ->
        F.fprintf fmt "Write to container %a via %a" AccessExpression.pp exp Procname.pp pname
    | InterfaceCall {exp; pname} ->
        F.fprintf fmt "Call to un-annotated interface method %a.%a" AccessExpression.pp exp
          Procname.pp pname

  let pp_json access =
    let access_mode, exp =
    match access with
      | Read {exp}  -> "Read",  F.asprintf "%a" AccessExpression.pp exp
      | Write {exp} -> "Write", F.asprintf "%a" AccessExpression.pp exp
      | ContainerRead {exp; _}  -> "Read",  F.asprintf "%a" AccessExpression.pp exp
      | ContainerWrite {exp; _} -> "Write", F.asprintf "%a" AccessExpression.pp exp
      | InterfaceCall {exp; _}  -> "Unk",   F.asprintf "%a" AccessExpression.pp exp
    in
    {Jsonbug_j.kind = access_mode
    ; Jsonbug_j.exp = exp
    }

  let mono_lang_pp = MF.wrap_monospaced pp_exp

  let describe fmt = function
    | Read {exp} | Write {exp} ->
        F.fprintf fmt "access to %a" mono_lang_pp exp
    | ContainerRead {exp; pname} ->
        F.fprintf fmt "Read of container %a via call to %s" mono_lang_pp exp
          (MF.monospaced_to_string (Procname.get_method pname))
    | ContainerWrite {exp; pname} ->
        F.fprintf fmt "Write to container %a via call to %s" mono_lang_pp exp
          (MF.monospaced_to_string (Procname.get_method pname))
    | InterfaceCall {pname} ->
        F.fprintf fmt "Call to un-annotated interface method %a" Procname.pp pname
end

module CallPrinter = struct
  type t = CallSite.t

  let pp fmt cs = F.fprintf fmt "call to %a" Procname.pp (CallSite.pname cs)
end

module LockDomain = struct
  include AbstractDomain.CountDomain (struct
    (** arbitrary threshold for max locks we expect to be held simultaneously *)
    let max = 5
  end)

  let acquire_lock = increment

  let release_lock = decrement

  let integrate_summary ~caller_astate ~callee_astate = add caller_astate callee_astate

  let is_locked t = not (is_bottom t)
end

(* ======================================= *)
(* @inherited from the starvation analysis *)
(* ======================================= *)
module Lock = struct
  include AbstractAddress

  let pp_locks fmt lock = F.fprintf fmt " locks %a" describe lock

  let make_java_synchronized formals procname =
    match procname with
    | Procname.Java java_pname when Procname.Java.is_static java_pname ->
        (* this is crafted so as to match synchronized(CLASSNAME.class) constructs *)
        let typename_str = Procname.Java.get_class_type_name java_pname |> Typ.Name.name in
        let hilexp = HilExp.(Constant (Cclass (Ident.string_to_name typename_str))) in
        make formals hilexp
    | Procname.Java _ ->
        FormalMap.get_formal_base 0 formals
        |> Option.bind ~f:(fun base ->
               let hilexp = HilExp.(AccessExpression (AccessExpression.base base)) in
               make formals hilexp )
    | _ ->
        L.die InternalError "Non-Java methods cannot be synchronized.@\n"


  let compare_wrt_reporting t1 t2 =
    let mk_str t = root_class t |> Option.value_map ~default:"" ~f:Typ.Name.to_string in
    (* use string comparison on types as a stable order to decide whether to report a deadlock *)
    String.compare (mk_str t1) (mk_str t2)
end

module Event = struct
  type t =
    | LockAcquire of Lock.t
    (* | MonitorWait of Lock.t *)
  [@@deriving compare]

  let pp fmt = function
    | LockAcquire lock ->
        F.fprintf fmt "LockAcquire(%a)" Lock.pp lock
    (* | MonitorWait lock ->
     *     F.fprintf fmt "MonitorWait(%a)" Lock.pp lock *)

  let describe fmt elem =
    match elem with
    | LockAcquire lock ->
        Lock.pp_locks fmt lock
    (* | MonitorWait lock ->
     *     F.fprintf fmt "calls `wait` on %a" Lock.describe lock *)

  let make_acquire lock = LockAcquire lock

  (* let make_object_wait lock = MonitorWait lock *)

  let apply_subst subst event =
    (* let make_monitor_wait lock = MonitorWait lock in *)
    let make_lock_acquire lock = LockAcquire lock in
    let apply_subst_aux make lock =
      match Lock.apply_subst subst lock with
      | None ->
          None
      | Some lock' when phys_equal lock lock' ->
          Some event
      | Some lock' ->
          Some (make lock')
    in
    match event with
    (* | MonitorWait lock ->
     *     apply_subst_aux make_monitor_wait lock *)
    | LockAcquire lock ->
        apply_subst_aux make_lock_acquire lock
end


(** A lock acquisition with source location and procname in which it occurs. The location & procname
    are *ignored* for comparisons, and are only for reporting. *)
module Acquisition = struct
  type t = {lock: Lock.t; loc: Location.t [@compare.ignore]; procname: Procname.t [@compare.ignore]}
  [@@deriving compare]

  let pp fmt {lock} = Lock.pp fmt lock

  let pp_json {lock} = F.asprintf "%a" Lock.pp lock

  let describe fmt {lock} = Lock.pp_locks fmt lock

  let make ~procname ~loc lock = {lock; loc; procname}

  (* let compare acq1 acq2 = 0 *)

  let compare_loc {loc= loc1} {loc= loc2} = Location.compare loc1 loc2

  let make_trace_step acquisition =
    let description = F.asprintf "%a" describe acquisition in
    Errlog.make_trace_element 0 acquisition.loc description []


  let make_dummy lock = {lock; loc= Location.dummy; procname= Procname.Linters_dummy_method}

  let apply_subst subst acquisition =
    match Lock.apply_subst subst acquisition.lock with
    | None ->
        None
    | Some lock when phys_equal acquisition.lock lock ->
        Some acquisition
    | Some lock ->
        Some {acquisition with lock}

end

(** Set of acquisitions; due to order over acquisitions, each lock appears at most once. *)
module Acquisitions = struct
  include PrettyPrintable.MakePPSet (Acquisition)

  (* use the fact that location/procname are ignored in comparisons *)
  let lock_is_held lock acquisitions = mem (Acquisition.make_dummy lock) acquisitions

  let lock_is_held_in_other_thread tenv lock acquisitions =
    exists (fun acq -> Lock.equal_across_threads tenv lock acq.lock) acquisitions


  let no_locks_common_across_threads tenv acqs1 acqs2 =
    for_all (fun acq1 -> not (lock_is_held_in_other_thread tenv acq1.lock acqs2)) acqs1


  let apply_subst subst acqs =
    fold
      (fun acq acc ->
        match Acquisition.apply_subst subst acq with None -> acc | Some acq' -> add acq' acc )
      acqs empty

  let pp_json acq =
    List.map (elements acq) ~f:(fun a -> Acquisition.pp_json a)

end

module LockState : sig
  include AbstractDomain.WithTop

  val acquire : procname:Procname.t -> loc:Location.t -> Lock.t -> t -> t

  val release : ?lock:Lock.t option -> t -> t

  val is_lock_taken : Event.t -> t -> bool

  val get_acquisitions : t -> Acquisitions.t
end = struct
  (* abstraction limit for lock counts *)
  let max_lock_depth_allowed = 5

  module LockCount = AbstractDomain.DownwardIntDomain (struct
    let max = max_lock_depth_allowed
  end)

  module Map = AbstractDomain.InvertedMap (Lock) (LockCount)

  (* [acquisitions] has the currently held locks, so as to avoid a linear fold in [get_acquisitions].
     This should also increase sharing across returned values from [get_acquisitions]. *)
  (* acquisitions_lifo - temp hack until the nested bug gets fixed *)
  type t = {map: Map.t [@compare.ignore];
            acquisitions: Acquisitions.t;
            acquisitions_lifo: Acquisitions.elt list [@compare.ignore]} (* acquisitions_lifo is temporarily added to cope with the ensted sync bug *)
  [@@deriving compare]

  let get_acquisitions {acquisitions} = acquisitions

  let pp fmt {map; acquisitions} =
    (* let () = print_endline "ANDREEA LockState lifo: " in
     * let () = List.iter acquisitions_lifo ~f:(Acquisition.pp fmt) in *)
    F.fprintf fmt "{map= %a; acquisitions= %a; }" Map.pp map Acquisitions.pp acquisitions


  let join lhs rhs =
    let map = Map.join lhs.map rhs.map in
    let acquisitions = Acquisitions.inter lhs.acquisitions rhs.acquisitions in
    let acquisitions_lifo = lhs.acquisitions_lifo@rhs.acquisitions_lifo in
    {map; acquisitions; acquisitions_lifo }


  let widen ~prev ~next ~num_iters =
    let map = Map.widen ~prev:prev.map ~next:next.map ~num_iters in
    let acquisitions = Acquisitions.inter prev.acquisitions next.acquisitions in
    let acquisitions_lifo = prev.acquisitions_lifo@next.acquisitions_lifo in
    {map; acquisitions; acquisitions_lifo }

  let leq ~lhs ~rhs = Map.leq ~lhs:lhs.map ~rhs:rhs.map

  let top = {map= Map.top; acquisitions= Acquisitions.empty; acquisitions_lifo = []}

  let is_top {map} = Map.is_top map

  let is_lock_taken event {acquisitions} =
    match event with
    | Event.LockAcquire lock ->
        Acquisitions.mem (Acquisition.make_dummy lock) acquisitions
    (* | _ -> *)
        (* false *)


  let acquire ~procname ~loc lock {map; acquisitions; acquisitions_lifo} =
    let should_add_acquisition = ref false in
    let map =
      Map.update lock
        (function
          | None ->
              (* lock was not already held, so add it to [acquisitions] *)
              should_add_acquisition := true ;
              Some LockCount.(increment top)
          | Some count ->
              Some (LockCount.increment count) )
        map
    in
    let acquisitions, acquisitions_lifo =
      if !should_add_acquisition then
        let acquisition  = Acquisition.make ~procname ~loc lock in
        let acquisitions_lifo = acquisition::acquisitions_lifo in
        Acquisitions.add acquisition acquisitions, acquisitions_lifo
      else acquisitions, acquisitions_lifo
    in
    {map; acquisitions; acquisitions_lifo}

  (* let release lock {map; acquisitions} =
   *   let should_remove_acquisition = ref false in
   *   let map =
   *     Map.update lock
   *       (function
   *         | None ->
   *             None
   *         | Some count ->
   *             let new_count = LockCount.decrement count in
   *             if LockCount.is_top new_count then (
   *               (\* lock was held, but now it is not, so remove from [aqcuisitions] *\)
   *               should_remove_acquisition := true ;
   *               None )
   *             else Some new_count )
   *       map
   *   in
   *   let acquisitions =
   *     if !should_remove_acquisition then
   *       let acquisition = Acquisition.make_dummy lock in
   *       Acquisitions.remove acquisition acquisitions
   *     else acquisitions
   *   in
   *   {map; acquisitions} *)

  (***** Overwrite the above release to bypass the nested sync bug *****)
  let release ?lock:(lock = None) {map; acquisitions; acquisitions_lifo} =
    let should_remove_acquisition = ref false in
    let map_fn lock =
      Map.update lock
        (function
          | None -> None
          | Some count ->
              let new_count = LockCount.decrement count in
              if LockCount.is_top new_count then (
                (* lock was held, but now it is not, so remove from [aqcuisitions] *)
                should_remove_acquisition := true ;
                None )
              else Some new_count )
        map
    in
    let acquisitions_fn lock acquisitions =
      if !should_remove_acquisition then
        let acquisition = Acquisition.make_dummy lock in
        Acquisitions.remove acquisition acquisitions
      else acquisitions
    in
    match lock with
    | Some lock ->
        let map = map_fn lock in
        let map, lock, acquisitions_lifo =
          if !should_remove_acquisition then
            let acquisition = Acquisition.make_dummy lock in
            let acquisitions_lifo = List.fold_left acquisitions_lifo ~init:[]
                ~f:(fun a lk -> a@(if Acquisition.compare lk acquisition == 0 then [] else [lk] ))
            in
            map, lock, acquisitions_lifo
          else
            begin
              match acquisitions_lifo with
              | []     -> map, lock, acquisitions_lifo
              | acq::t -> let map = map_fn acq.lock in
                  map, acq.lock, t
            end
        in
        let acquisitions = acquisitions_fn lock acquisitions in
        {map; acquisitions; acquisitions_lifo}
    | None ->
        match acquisitions_lifo with
        | []     -> {map; acquisitions; acquisitions_lifo}
        | acq::t ->
            let map = map_fn acq.lock in
            let acquisitions = acquisitions_fn acq.lock acquisitions in
            let acquisitions_lifo = t in
            {map; acquisitions; acquisitions_lifo}

end


(* ======================================= *)
(*                  END                    *)
(* @inherited from the starvation analysis *)
(* ======================================= *)

module ThreadsDomain = struct
  type t = NoThread | AnyThreadButSelf | AnyThread [@@deriving compare]

  let bottom = NoThread

  (* NoThread < AnyThreadButSelf < Any *)
  let leq ~lhs ~rhs =
    phys_equal lhs rhs
    ||
    match (lhs, rhs) with
    | NoThread, _ ->
        true
    | _, NoThread ->
        false
    | _, AnyThread ->
        true
    | AnyThread, _ ->
        false
    | _ ->
        Int.equal 0 (compare lhs rhs)


  let join astate1 astate2 =
    if phys_equal astate1 astate2 then astate1
    else
      match (astate1, astate2) with
      | NoThread, astate | astate, NoThread ->
          astate
      | AnyThread, _ | _, AnyThread ->
          AnyThread
      | AnyThreadButSelf, AnyThreadButSelf ->
          AnyThreadButSelf


  let widen ~prev ~next ~num_iters:_ = join prev next

  let pp fmt astate =
    F.pp_print_string fmt
      ( match astate with
      | NoThread ->
          "NoThread"
      | AnyThreadButSelf ->
          "AnyThreadButSelf"
      | AnyThread ->
          "AnyThread" )


  (* at least one access is known to occur on a background thread *)
  let can_conflict astate1 astate2 =
    match join astate1 astate2 with AnyThread -> true | NoThread | AnyThreadButSelf -> false

  (* at least one access is known to occur on a background thread *)
  let can_run_in_parallel astate1 astate2 =
    match join astate1 astate2 with AnyThread -> true | NoThread | AnyThreadButSelf -> false

    (** given the current thread state [caller_thread] and the thread state under which a critical
      pair occurred, [pair_thread], decide whether to throw away the pair (returning [None]) because
      it cannot occur within a call from the current state, or adapt its thread state appropriately. *)
  let apply_to_pair caller_thread pair_thread =
    match (caller_thread, pair_thread) with
    | NoThread, _ ->
        (* callee pair knows more than us *)
        Some pair_thread
    | AnyThread, _
    | _, AnyThread ->
        Some AnyThread
    | _, _ ->
        (* caller is UI or BG and callee does not disagree, so use that *)
        Some caller_thread

  let is_bottom = function NoThread -> true | _ -> false

  let is_any_but_self = function AnyThreadButSelf -> true | _ -> false

  let is_any = function AnyThread -> true | _ -> false

  let integrate_summary ~caller_astate ~callee_astate =
    (* if we know the callee runs on the main thread, assume the caller does too. otherwise, keep
       the caller's thread context *)
    match callee_astate with AnyThreadButSelf -> callee_astate | _ -> caller_astate
end

module CriticalPairElement = struct
  type t = {acquisitions: Acquisitions.t; event: Event.t; thread: ThreadsDomain.t}
  [@@deriving compare]

  let pp fmt {acquisitions; event} =
    F.fprintf fmt "{acquisitions= %a; event= %a}" Acquisitions.pp acquisitions Event.pp event


  let describe = pp

  let apply_subst subst elem =
    match Event.apply_subst subst elem.event with
    | None ->
        None
    | Some event' ->
        let acquisitions' = Acquisitions.apply_subst subst elem.acquisitions in
        Some {elem with acquisitions= acquisitions'; event= event'}
end

let is_recursive_lock event tenv =
  let is_class_and_recursive_lock = function
    | {Typ.desc= Tptr ({desc= Tstruct name}, _)} | {desc= Tstruct name} ->
        ConcurrencyModels.is_recursive_lock_type name
    | typ ->
        L.debug Analysis Verbose "Asked if non-struct type %a is a recursive lock type.@."
          (Typ.pp_full Pp.text) typ ;
        true
  in
  match event with
  | Event.LockAcquire lock_path ->
      Lock.get_typ tenv lock_path |> Option.exists ~f:is_class_and_recursive_lock
  (* | _ ->
   *     false *)


module CriticalPair = struct
  include ExplicitTrace.MakeTraceElem (CriticalPairElement) (ExplicitTrace.DefaultCallPrinter)

  let pp_opt fmt pair = match pair with 
      | None   -> F.pp_print_string fmt "Emptyyy"
      | Some p -> pp fmt p

  let make ~loc acquisitions event thread = make {acquisitions; event; thread} loc

  (* let is_blocking_call {elem= {event}} = match event with LockAcquire _ -> true (\* | _ -> false *\) *)

  let get_final_acquire {elem= {event}} =
    match event with LockAcquire lock -> Some lock (* | _ -> None *)


  let may_deadlock tenv ({elem= pair1} as t1 : t) ({elem= pair2} as t2 : t) =
    ThreadsDomain.can_run_in_parallel pair1.thread pair2.thread
    && Option.both (get_final_acquire t1) (get_final_acquire t2)
       |> Option.exists ~f:(fun (lock1, lock2) ->
              (not (Lock.equal_across_threads tenv lock1 lock2))
              && Acquisitions.lock_is_held_in_other_thread tenv lock2 pair1.acquisitions
              && Acquisitions.lock_is_held_in_other_thread tenv lock1 pair2.acquisitions
              && Acquisitions.no_locks_common_across_threads tenv pair1.acquisitions
                   pair2.acquisitions )


  let apply_subst subst pair =
    match CriticalPairElement.apply_subst subst pair.elem with
    | None ->
        None
    | Some elem' ->
        Some (map ~f:(fun _elem -> elem') pair)


  let integrate_summary_opt ?subst ?tenv existing_acquisitions call_site
      (caller_thread : ThreadsDomain.t) (callee_pair : t) =
    let substitute_pair subst callee_pair =
      match subst with None -> Some callee_pair | Some subst -> apply_subst subst callee_pair
    in
    let filter_out_reentrant_relock callee_pair =
      match tenv with
      | None ->
          Some callee_pair
      | Some tenv
        when get_final_acquire callee_pair
             |> Option.for_all ~f:(fun lock ->
                    (not (Acquisitions.lock_is_held lock existing_acquisitions))
                    || not (is_recursive_lock callee_pair.elem.event tenv) ) ->
          Some callee_pair
      | _ ->
          None
    in
    substitute_pair subst callee_pair
    |> Option.bind ~f:filter_out_reentrant_relock
    |> Option.bind ~f:(fun callee_pair ->
           ThreadsDomain.apply_to_pair caller_thread callee_pair.elem.thread
           |> Option.map ~f:(fun thread ->
                  let f (elem : CriticalPairElement.t) =
                    let acquisitions = Acquisitions.union existing_acquisitions elem.acquisitions in
                    ({elem with acquisitions; thread} : elem_t)
                  in
                  with_callsite (map ~f callee_pair) call_site ) )


  let get_earliest_lock_or_call_loc ~procname ({elem= {acquisitions}} as t) =
    let initial_loc = get_loc t in
    Acquisitions.fold
      (fun {procname= acq_procname; loc= acq_loc} acc ->
        if Procname.equal procname acq_procname && Int.is_negative (Location.compare acq_loc acc)
        then acq_loc
        else acc )
      acquisitions initial_loc


  let make_trace ?(header = "") ?(include_acquisitions = true) top_pname
      ({elem= {acquisitions; event}; trace; loc} as pair) =
    let acquisitions_map =
      if include_acquisitions then
        Acquisitions.fold
          (fun ({procname} as acq : Acquisition.t) acc ->
            Procname.Map.update procname
              (function None -> Some [acq] | Some acqs -> Some (acq :: acqs))
              acc )
          acquisitions Procname.Map.empty
      else Procname.Map.empty
    in
    let header_step =
      let description = F.asprintf "%s%a" header describe_pname top_pname in
      let loc = get_loc pair in
      Errlog.make_trace_element 0 loc description []
    in
    (* construct the trace segment starting at [call_site] and ending at next call *)
    let make_call_stack_step fake_first_call call_site =
      let procname = CallSite.pname call_site in
      let trace =
        Procname.Map.find_opt procname acquisitions_map
        |> Option.value ~default:[]
        (* many acquisitions can be on same line (eg, std::lock) so use stable sort
           to produce a deterministic trace *)
        |> List.stable_sort ~compare:Acquisition.compare_loc
        |> List.map ~f:Acquisition.make_trace_step
      in
      if CallSite.equal call_site fake_first_call then trace
      else
        let descr = F.asprintf "%a" ExplicitTrace.DefaultCallPrinter.pp call_site in
        let call_step = Errlog.make_trace_element 0 (CallSite.loc call_site) descr [] in
        call_step :: trace
    in
    (* construct a call stack trace with the lock acquisitions interleaved *)
    let call_stack =
      (* fake outermost call so as to include acquisitions in the top level caller *)
      let fake_first_call = CallSite.make top_pname Location.dummy in
      List.map (fake_first_call :: trace) ~f:(make_call_stack_step fake_first_call)
    in
    let endpoint_step =
      let endpoint_descr = F.asprintf "%a" Event.describe event in
      Errlog.make_trace_element 0 loc endpoint_descr []
    in
    List.concat (([header_step] :: call_stack) @ [[endpoint_step]])

  let can_run_in_parallel t1 t2 = ThreadsDomain.can_run_in_parallel t1.elem.thread t2.elem.thread
end

(** skip adding an order pair [(_, event)] if

    - we have no tenv, or,
    - [event] is not a lock event, or,
    - we do not hold the lock, or,
    - the lock is not recursive. *)
let should_skip ?tenv event lock_state =
  Option.exists tenv ~f:(fun tenv ->
      LockState.is_lock_taken event lock_state && is_recursive_lock event tenv )


module CriticalPairs = struct
  include CriticalPair.FiniteSet

  let with_callsite astate ?tenv ?subst lock_state call_site thread =
    let existing_acquisitions = LockState.get_acquisitions lock_state in
    fold
      (fun critical_pair acc ->
        CriticalPair.integrate_summary_opt ?subst ?tenv existing_acquisitions call_site thread
          critical_pair
        |> Option.fold ~init:acc ~f:(fun acc (new_pair : CriticalPair.t) ->
               if should_skip ?tenv new_pair.elem.event lock_state then acc else add new_pair acc )
        )
        astate empty

  (* let merge critical_pairs = () *)

end

module FlatLock = AbstractDomain.Flat (Lock)

module GuardToLockMap = struct
  include AbstractDomain.InvertedMap (HilExp) (FlatLock)

  (* let remove_guard astate guard = remove guard astate
   * 
   * let add_guard astate ~guard ~lock = add guard (FlatLock.v lock) astate *)
end


module OwnershipAbstractValue = struct
  type t = OwnedIf of IntSet.t | Unowned [@@deriving compare]

  let owned = OwnedIf IntSet.empty

  let is_owned = function OwnedIf set -> IntSet.is_empty set | Unowned -> false

  let unowned = Unowned

  let make_owned_if formal_index = OwnedIf (IntSet.singleton formal_index)

  let leq ~lhs ~rhs =
    phys_equal lhs rhs
    ||
    match (lhs, rhs) with
    | _, Unowned ->
        true (* Unowned is top *)
    | Unowned, _ ->
        false
    | OwnedIf s1, OwnedIf s2 ->
        IntSet.subset s1 s2


  let join astate1 astate2 =
    if phys_equal astate1 astate2 then astate1
    else
      match (astate1, astate2) with
      | _, Unowned | Unowned, _ ->
          Unowned
      | OwnedIf s1, OwnedIf s2 ->
          OwnedIf (IntSet.union s1 s2)


  let widen ~prev ~next ~num_iters:_ = join prev next

  let pp fmt = function
    | Unowned ->
        F.pp_print_string fmt "Unowned"
    | OwnedIf s ->
        if IntSet.is_empty s then F.pp_print_string fmt "Owned"
        else
          F.fprintf fmt "OwnedIf%a"
            (PrettyPrintable.pp_collection ~pp_item:Int.pp)
            (IntSet.elements s)
end

module AccessSnapshot = struct
  module AccessSnapshotElem = struct
    type t =
      { access: Access.t
      ; thread: ThreadsDomain.t
      ; lock: bool
      ; locks: Acquisitions.t
      ; critical_pair: CriticalPair.t option
      ; ownership_precondition: OwnershipAbstractValue.t
      ; unique_id: string
      }
    [@@deriving compare]

    (* let pp_critical_pair fmt pair = match pair with
     *   | None -> F.pp_print_string fmt "Empty"
     *   | Some p -> CriticalPair.pp fmt p *)

    let pp fmt {access; thread; lock; locks;  ownership_precondition} =
      F.fprintf fmt "Access: %a Thread: %a Lock: %b Acquisitions: %a Pre: %a" Access.pp access ThreadsDomain.pp
        thread lock
        Acquisitions.pp locks
        OwnershipAbstractValue.pp ownership_precondition

    let pp_json {access; thread; lock; locks; ownership_precondition} =
      { Jsonbug_j.access = Access.pp_json access
      ; thread = F.asprintf "%a" ThreadsDomain.pp thread
      ; locks  = Acquisitions.pp_json locks
      ; ownership_pre = F.asprintf "%a" OwnershipAbstractValue.pp ownership_precondition
      }

    let describe fmt {access} = Access.describe fmt access
  end

  include ExplicitTrace.MakeTraceElemModuloLocation (AccessSnapshotElem) (CallPrinter)

  let pp_json {elem; loc; trace} =
    {
      Jsonbug_j.elem = AccessSnapshotElem.pp_json elem
    ; loc   = loc.Location.line 
    ; trace =  List.map trace ~f:(fun t -> F.asprintf "%a" ExplicitTrace.DefaultCallPrinter.pp t)
    ; hash   = elem.unique_id
    }

  let is_write {elem= {access}} = Access.is_write access

  let is_container_write {elem= {access}} = Access.is_container_write access

  let filter formals t =
    if
      (not (OwnershipAbstractValue.is_owned t.elem.ownership_precondition))
      && Access.should_keep formals t.elem.access
    then Some t
    else None


  let make_if_not_owned formals access lock locks critical_pair thread ownership_precondition  loc =
    let unique_id = Utils.better_hash (formals,access,locks,thread,loc) |> Caml.Digest.to_hex in
    make {access; lock; locks; critical_pair; thread; ownership_precondition; unique_id} loc |> filter formals


  let make_unannotated_call_access formals exp pname lock locks critical_pair ownership loc =
    let lock = LockDomain.is_locked lock in
    let access = Access.make_unannotated_call_access exp pname in
    make_if_not_owned formals access lock locks critical_pair ownership loc


  let make_access formals acc_exp ~is_write loc lock locks critical_pair thread ownership_precondition =
    let lock = LockDomain.is_locked lock in
    let access = Access.make_field_access acc_exp ~is_write in
    make_if_not_owned formals access lock locks critical_pair thread ownership_precondition loc


  let make_container_access formals acc_exp ~is_write callee loc lock lock_state critical_pair thread ownership_precondition
      =
    let lock = LockDomain.is_locked lock in
    let access = Access.make_container_access acc_exp callee ~is_write in
    let locks = LockState.get_acquisitions lock_state in
    make_if_not_owned formals access lock locks critical_pair thread ownership_precondition loc


  let map_opt formals ~f t =
    map t ~f:(fun elem -> {elem with access= Access.map ~f elem.access}) |> filter formals


  let update_callee_access formals snapshot callsite ownership_precondition threads lock lock_state critical_pair =
    let thread =
      ThreadsDomain.integrate_summary ~callee_astate:snapshot.elem.thread ~caller_astate:threads
    in
    let lock = snapshot.elem.lock || LockDomain.is_locked lock in
    let locks = Acquisitions.union snapshot.elem.locks (LockState.get_acquisitions lock_state) in
    (* ANDREEA-TODO: join critical_pairs*)
    with_callsite snapshot callsite
    |> map ~f:(fun elem -> {elem with lock; thread; locks; critical_pair; ownership_precondition})
    |> filter formals


  let is_unprotected {elem= {thread; lock; ownership_precondition}} =
    (not (ThreadsDomain.is_any_but_self thread))
    && (not lock)
    && not (OwnershipAbstractValue.is_owned ownership_precondition)

  (* let common_locks locks1 locks2 =
   *   if  *)
end

module AccessDomain = struct
  include AbstractDomain.FiniteSet (AccessSnapshot)

  let add_opt snapshot_opt astate =
    Option.fold snapshot_opt ~init:astate ~f:(fun acc s -> add s acc)

   let pp_json domain = List.map (elements domain) ~f:(fun snapshot -> AccessSnapshot.pp_json snapshot)
  
end

module OwnershipDomain = struct
  include AbstractDomain.Map (AccessExpression) (OwnershipAbstractValue)

  (* return the first non-Unowned ownership value found when checking progressively shorter
     prefixes of [access_exp] *)
  let rec get_owned (access_exp : AccessExpression.t) astate =
    match find_opt access_exp astate with
    | Some (OwnershipAbstractValue.OwnedIf _ as v) ->
        v
    | _ -> (
      match access_exp with
      | Base _ ->
          OwnershipAbstractValue.Unowned
      | AddressOf prefix | Dereference prefix | FieldOffset (prefix, _) | ArrayOffset (prefix, _, _)
        ->
          get_owned prefix astate )


  let rec ownership_of_expr expr ownership =
    let open HilExp in
    match expr with
    | AccessExpression access_expr ->
        get_owned access_expr ownership
    | Constant _ ->
        OwnershipAbstractValue.owned
    | Exception e (* treat exceptions as transparent wrt ownership *) | Cast (_, e) ->
        ownership_of_expr e ownership
    | _ ->
        OwnershipAbstractValue.unowned


  let propagate_assignment lhs_access_exp rhs_exp ownership =
    if AccessExpression.get_base lhs_access_exp |> fst |> Var.is_global then
      (* do not assign ownership to access expressions rooted at globals *)
      ownership
    else
      let rhs_ownership_value = ownership_of_expr rhs_exp ownership in
      add lhs_access_exp rhs_ownership_value ownership


  let propagate_return ret_access_exp return_ownership actuals ownership =
    let get_ownership formal_index init =
      List.nth actuals formal_index
      (* simply skip formal if we cannot find its actual, as opposed to assuming non-ownership *)
      |> Option.fold ~init ~f:(fun acc expr ->
             OwnershipAbstractValue.join acc (ownership_of_expr expr ownership) )
    in
    let ret_ownership_wrt_actuals =
      match return_ownership with
      | OwnershipAbstractValue.Unowned ->
          return_ownership
      | OwnershipAbstractValue.OwnedIf formal_indexes ->
          IntSet.fold get_ownership formal_indexes OwnershipAbstractValue.owned
    in
    add ret_access_exp ret_ownership_wrt_actuals ownership
end

module Attribute = struct
  type t = Nothing | Functional | OnMainThread | LockHeld | Synchronized [@@deriving equal]

  let pp fmt t =
    ( match t with
    | Nothing ->
        "Nothing"
    | Functional ->
        "Functional"
    | OnMainThread ->
        "OnMainThread"
    | LockHeld ->
        "LockHeld"
    | Synchronized ->
        "Synchronized" )
    |> F.pp_print_string fmt


  let top = Nothing

  let is_top = function Nothing -> true | _ -> false

  let join t t' = if equal t t' then t else Nothing

  let leq ~lhs ~rhs = equal (join lhs rhs) rhs

  let widen ~prev ~next ~num_iters:_ = join prev next
end

module AttributeMapDomain = struct
  include AbstractDomain.SafeInvertedMap (AccessExpression) (Attribute)

  let get acc_exp t = find_opt acc_exp t |> Option.value ~default:Attribute.top

  let is_functional t access_expression =
    match find_opt access_expression t with Some Functional -> true | _ -> false


  let is_synchronized t access_expression =
    match find_opt access_expression t with Some Synchronized -> true | _ -> false


  let rec attribute_of_expr attribute_map (e : HilExp.t) =
    match e with
    | AccessExpression access_expr ->
        get access_expr attribute_map
    | Constant _ ->
        Attribute.Functional
    | Exception expr (* treat exceptions as transparent wrt attributes *) | Cast (_, expr) ->
        attribute_of_expr attribute_map expr
    | UnaryOperator (_, expr, _) ->
        attribute_of_expr attribute_map expr
    | BinaryOperator (_, expr1, expr2) ->
        let attribute1 = attribute_of_expr attribute_map expr1 in
        let attribute2 = attribute_of_expr attribute_map expr2 in
        Attribute.join attribute1 attribute2
    | Closure _ | Sizeof _ ->
        Attribute.top


  let propagate_assignment lhs_access_expression rhs_exp attribute_map =
    let rhs_attribute = attribute_of_expr attribute_map rhs_exp in
    add lhs_access_expression rhs_attribute attribute_map
end

type t =
  { threads: ThreadsDomain.t
  ; locks: LockDomain.t
  ; lock_state: LockState.t
  ; critical_pairs: CriticalPairs.t
  ; accesses: AccessDomain.t
  ; ownership: OwnershipDomain.t
  ; attribute_map: AttributeMapDomain.t }


let pp fmt {threads; locks; lock_state;  accesses; ownership; attribute_map} =
  F.fprintf fmt "Threads: %a, Locks: %a Lock State: %a  @\nAccesses %a @\nOwnership: %a @\nAttributes: %a @\n"
    ThreadsDomain.pp threads LockDomain.pp locks LockState.pp lock_state AccessDomain.pp accesses OwnershipDomain.pp
    ownership AttributeMapDomain.pp attribute_map

let bottom =
  let threads = ThreadsDomain.bottom in
  let locks = LockDomain.bottom in
  let lock_state= LockState.top in
  let critical_pairs = CriticalPairs.bottom in
  let accesses = AccessDomain.empty in
  let ownership = OwnershipDomain.empty in
  let attribute_map = AttributeMapDomain.empty in
  {threads; locks; lock_state; critical_pairs; accesses; ownership; attribute_map}


let is_bottom {threads; locks; lock_state; accesses; ownership; attribute_map} =
    (* let () = print_endline "\n ANDREEA is_botoom: " in *)
    ThreadsDomain.is_bottom threads && LockDomain.is_bottom locks && AccessDomain.is_empty accesses
    && LockState.is_top lock_state
    && OwnershipDomain.is_empty ownership
    && AttributeMapDomain.is_empty attribute_map


let leq ~lhs ~rhs =
  (* let () = print_endline "\n ANDREEA leq: " in *)
  if phys_equal lhs rhs then true
  else
    ThreadsDomain.leq ~lhs:lhs.threads ~rhs:rhs.threads
    && LockDomain.leq ~lhs:lhs.locks ~rhs:rhs.locks
    && LockState.leq ~lhs:lhs.lock_state ~rhs:rhs.lock_state
    && AccessDomain.leq ~lhs:lhs.accesses ~rhs:rhs.accesses
    && AttributeMapDomain.leq ~lhs:lhs.attribute_map ~rhs:rhs.attribute_map


let join astate1 astate2 =
  (* let () = print_endline "\n ANDREEA (join: astate1): " in
   * let () = pp Format.std_formatter astate1 in
   * let () = print_endline "\n ANDREEA (join: astate2): " in
   * let () = pp Format.std_formatter astate2 in *)
  let astate =
  if phys_equal astate1 astate2 then astate1
  else
    let threads = ThreadsDomain.join astate1.threads astate2.threads in
    let locks = LockDomain.join astate1.locks astate2.locks in
    let critical_pairs = CriticalPairs.join astate1.critical_pairs astate2.critical_pairs in
    let lock_state = LockState.join astate1.lock_state astate2.lock_state in
    let accesses = AccessDomain.join astate1.accesses astate2.accesses in
    let ownership = OwnershipDomain.join astate1.ownership astate2.ownership in
    let attribute_map = AttributeMapDomain.join astate1.attribute_map astate2.attribute_map in
    {threads; locks; lock_state; critical_pairs; accesses; ownership; attribute_map}
  in
  (* let () = print_endline "\n ANDREEA (join: astate): " in
   * let () = pp Format.std_formatter astate in *)
  astate

let widen ~prev ~next ~num_iters =
  (* let () = print_endline "\n ANDREEA (widen: prev): " in
   * let () = pp Format.std_formatter prev in
   * let () = print_endline "\n ANDREEA (widen: next): " in
   * let () = pp Format.std_formatter next in *)
  let astate = 
  if phys_equal prev next then prev
  else
    let threads = ThreadsDomain.widen ~prev:prev.threads ~next:next.threads ~num_iters in
    let locks = LockDomain.widen ~prev:prev.locks ~next:next.locks ~num_iters in
    let lock_state = LockState.widen ~prev:prev.lock_state ~next:next.lock_state ~num_iters in
    let critical_pairs = CriticalPairs.widen ~prev:prev.critical_pairs ~next:next.critical_pairs ~num_iters in
    let accesses = AccessDomain.widen ~prev:prev.accesses ~next:next.accesses ~num_iters in
    let ownership = OwnershipDomain.widen ~prev:prev.ownership ~next:next.ownership ~num_iters in
    let attribute_map =
      AttributeMapDomain.widen ~prev:prev.attribute_map ~next:next.attribute_map ~num_iters
    in
    {threads; locks; lock_state; critical_pairs; accesses; ownership; attribute_map}
  in
  (* let () = print_endline "\n ANDREEA (join: astate): " in
   * let () = pp Format.std_formatter astate in *)
  astate

let add_critical_pair ?tenv lock_state event thread ~loc acc =
  if should_skip ?tenv event lock_state then acc
  else
    let acquisitions = LockState.get_acquisitions lock_state in
    let critical_pair = CriticalPair.make ~loc acquisitions event thread in
    CriticalPairs.add critical_pair acc

let acquire ?tenv ({lock_state; critical_pairs} as astate) ~procname ~loc locks = (* astate *)
  { astate with
    critical_pairs=
      List.fold locks ~init:critical_pairs ~f:(fun acc lock ->
          let event = Event.make_acquire lock in
          add_critical_pair ?tenv lock_state event astate.threads ~loc acc )
  ; lock_state=
      List.fold locks ~init:lock_state ~f:(fun acc lock -> LockState.acquire ~procname ~loc lock acc)
  }

let acquire ?tenv astate ~procname ~loc locks = (* astate *)
  let result = acquire ?tenv astate ~procname ~loc locks in
  let () = if false then
    let () = print_endline "\n ACQUIRE astate: \n" in
    let () = pp Format.std_formatter astate in
    let () = print_endline "\n ACQUIRE result: \n" in
    let () = pp Format.std_formatter result in
    ()
  in result

let release ({lock_state} as astate) locks =
  (***** BEGIN hack to solve nested sync ******)
  match locks with
  | [] ->
      { astate with lock_state = LockState.release lock_state }
  | _  ->
  (***** END hack to solve nested sync ******)
      { astate with
        lock_state= List.fold locks ~init:lock_state ~f:(fun acc l -> LockState.release ~lock:(Some l) acc) }

let release astate locks =
  let result = release astate locks in
  let () = if false then
      let () = print_endline "\n RELEASE locks: \n" in
      let () = List.iter locks ~f:(Lock.pp Format.std_formatter) in
      let () = print_endline "\n RELEASE astate: \n" in
      let () = pp Format.std_formatter astate in
      let () = print_endline "\n RELEASE result: \n" in
      let () = pp Format.std_formatter result in
      ()
  in result


type summary =
  { threads: ThreadsDomain.t
  ; locks: LockDomain.t
  ; critical_pairs: CriticalPairs.t
  ; accesses: AccessDomain.t
  ; return_ownership: OwnershipAbstractValue.t
  ; return_attribute: Attribute.t
  ; attributes: AttributeMapDomain.t }

let empty_summary =
  { threads= ThreadsDomain.bottom
  ; locks= LockDomain.bottom
  ; critical_pairs= CriticalPairs.bottom
  ; accesses= AccessDomain.bottom
  ; return_ownership= OwnershipAbstractValue.unowned
  ; return_attribute= Attribute.top
  ; attributes= AttributeMapDomain.top }

let pp_summary fmt {threads; locks; critical_pairs; accesses; return_ownership; return_attribute; attributes} =
  F.fprintf fmt
    "@\n\
     Threads: %a, Locks: %a @\n\
     Critical Pairs: %a @\n\
     Accesses %a @\n\
     Ownership: %a @\n\
     Return Attribute: %a @\n\
     Attributes: %a @\n"
    ThreadsDomain.pp threads LockDomain.pp locks CriticalPairs.pp critical_pairs AccessDomain.pp accesses OwnershipAbstractValue.pp
    return_ownership Attribute.pp return_attribute AttributeMapDomain.pp attributes

let pp_summary_json { accesses; } = AccessDomain.pp_json accesses 


let add_unannotated_call_access formals pname actuals loc (astate : t) =
  match actuals with
  | [] ->
      astate
  | receiver_hilexp :: _ -> (
    match HilExp.get_access_exprs receiver_hilexp with
    | [] | _ :: _ :: _ ->
        (* if no access exps involved, or if more than one (should be impossible), ignore *)
        astate
    | [receiver] ->
        let snapshot =
          AccessSnapshot.make_unannotated_call_access formals receiver pname astate.locks
            (LockState.get_acquisitions astate.lock_state)
            (CriticalPairs.choose_opt astate.critical_pairs) (* astate.critical_pairs TODO-Andreea: needs something meaningful here. Perhaps a flattened critical_pairs? *)
            astate.threads Unowned loc
        in
        {astate with accesses= AccessDomain.add_opt snapshot astate.accesses} )

let astate_to_summary proc_desc formals {threads; locks; critical_pairs; accesses; ownership; attribute_map} =
  let proc_name = Procdesc.get_proc_name proc_desc in
  let return_var_exp =
    AccessExpression.base
      (Var.of_pvar (Pvar.get_ret_pvar proc_name), Procdesc.get_ret_type proc_desc)
  in
  let return_ownership = OwnershipDomain.get_owned return_var_exp ownership in
  let return_attribute = AttributeMapDomain.get return_var_exp attribute_map in
  let locks =
    (* if method is [synchronized] released the lock once. *)
    if Procdesc.is_java_synchronized proc_desc then LockDomain.release_lock locks else locks
  in
  let attributes =
    (* store only the [Synchronized] attribute for class initializers/constructors *)
    if Procname.is_java_class_initializer proc_name || Procname.is_constructor proc_name then
      AttributeMapDomain.filter
        (fun exp attribute ->
          match attribute with Synchronized -> should_keep_exp formals exp | _ -> false )
        attribute_map
    else AttributeMapDomain.top
  in
  (* fix critical_pairs *)
  {threads; locks; critical_pairs; accesses; return_ownership; return_attribute; attributes}

let with_callsite critical_pairs ?tenv ?subst lock_state call_site thread =
  CriticalPairs.with_callsite critical_pairs ?tenv ?subst lock_state call_site thread

let pp_pair_opt fmt pair = match pair with 
      | None   -> F.pp_print_string fmt "Empty"
      | Some p -> CriticalPair.pp fmt p

let get_acquisitions lock_state = LockState.get_acquisitions lock_state

let different_locks acqs1 acqs2 =
  Acquisitions.disjoint acqs1 acqs2
