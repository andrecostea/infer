(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
module AccessExpression = HilExp.AccessExpression
module F = Format

val pp_exp : F.formatter -> AccessExpression.t -> unit
(** language sensitive pretty-printer *)

module Access : sig
  type t =
    | Read of {exp: AccessExpression.t}  (** Field or array read *)
    | Write of {exp: AccessExpression.t}  (** Field or array write *)
    | ContainerRead of {exp: AccessExpression.t; pname: Procname.t}  (** Read of container object *)
    | ContainerWrite of {exp: AccessExpression.t; pname: Procname.t}
        (** Write to container object *)
    | InterfaceCall of {exp: AccessExpression.t; pname: Procname.t}
        (** Call to method of interface not annotated with [@ThreadSafe] *)

  val pp : F.formatter -> t -> unit

  val get_access_exp : t -> AccessExpression.t
end

(* ======================================= *)
(* @inherited from the starvation analysis *)
(* ======================================= *)

(** Abstract address for a lock. There are two notions of equality:

    - Equality for comparing two addresses within the same thread/process/trace. Under this,
      identical globals and identical class objects compare equal. Locks represented by access paths
      rooted at method parameters must have equal access paths to compare equal. Paths rooted at
      locals are ignored.
    - Equality for comparing two addresses in two distinct threads/traces. Globals and class objects
      are compared in the same way, but locks represented by access paths rooted at parameters need
      only have equal access lists (ie [x.f.g == y.f.g]). This allows demonically aliasing
      parameters in *distinct* threads. This relation is used in [may_deadlock]. *)
module Lock : sig
  include module type of AbstractAddress

  val pp_locks : F.formatter -> t -> unit

  val make_java_synchronized : FormalMap.t -> Procname.t -> t option
  (** create the monitor locked when entering a synchronized java method *)

  val compare_wrt_reporting : t -> t -> int
  (** a stable order for avoiding reporting deadlocks twice based on the root variable type *)
end

module Event : sig
  type t =
    | LockAcquire of Lock.t
    (* | MonitorWait of Lock.t *)
  [@@deriving compare]

  val describe : F.formatter -> t -> unit
end

module LockState : AbstractDomain.WithTop

(** a lock acquisition with location information *)
module Acquisition : sig
  type t = private
    {lock: Lock.t; loc: Location.t [@compare.ignore]; procname: Procname.t [@compare.ignore]}
  [@@deriving compare]
end

(** A set of lock acquisitions with source locations and procnames. *)
module Acquisitions : sig
  include PrettyPrintable.PPSet with type elt = Acquisition.t

  val lock_is_held : Lock.t -> t -> bool
  (** is the given lock in the set *)

  val lock_is_held_in_other_thread : Tenv.t -> Lock.t -> t -> bool
  (** is the given lock held, modulo memory abstraction across threads *)
end

(* ======================================= *)
(*                   END                   *)
(* @inherited from the starvation analysis *)
(* ======================================= *)


(** Overapproximation of number of time the lock has been acquired *)
module LockDomain : sig
  include AbstractDomain.WithBottom

  val acquire_lock : t -> t
  (** record acquisition of a lock *)

  val release_lock : t -> t
  (** record release of a lock *)

  val integrate_summary : caller_astate:t -> callee_astate:t -> t
  (** integrate current state with a callee summary *)
end

(** Abstraction of threads that may run in parallel with the current thread. NoThread <
    AnyThreadExceptSelf < AnyThread *)
module ThreadsDomain : sig
  type t =
    | NoThread
        (** No threads can run in parallel with the current thread (concretization: empty set). We
            assume this by default unless we see evidence to the contrary (annotations, use of
            locks, etc.) *)
    | AnyThreadButSelf
        (** Current thread can run in parallel with other threads, but not with a copy of itself.
            (concretization : [{ t | t \in TIDs && t != t_cur }]) *)
    | AnyThread
        (** Current thread can run in parallel with any thread, including itself (concretization:
            set of all TIDs ) *)

  val can_conflict : t -> t -> bool
  (** return true if two accesses with these thread values can run concurrently *)

  val can_run_in_parallel : t -> t -> bool
  (** return true if two accesses with these thread values can run concurrently *)

  val is_any : t -> bool

  val integrate_summary : caller_astate:t -> callee_astate:t -> t
  (** integrate current state with a callee summary *)
end

module OwnershipAbstractValue : sig
  type t = private
    | OwnedIf of IntSet.t
        (** Owned if the formals at the given indexes are owned in the caller; unconditionally owned
            if the set of formals is empty = bottom of the lattice *)
    | Unowned  (** Unowned value; top of the lattice *)

  val owned : t

  val make_owned_if : int -> t

  val join : t -> t -> t
end

(* ======================================= *)
(* @inherited from the starvation analysis *)
(* ======================================= *)

(** An event and the currently-held locks at the time it occurred. *)
module CriticalPairElement : sig
  type t = private {acquisitions: Acquisitions.t; event: Event.t; thread: ThreadsDomain.t}
end

(** A [CriticalPairElement] equipped with a call stack. The intuition is that if we have a critical
    pair `(locks, event)` in the summary of a method then there is a trace of that method where
    `event` occurs, and right before it occurs the locks held are exactly `locks` (no over/under
    approximation). We call it "critical" because the information here alone determines deadlock
    conditions. *)
module CriticalPair : sig
  type t = private {elem: CriticalPairElement.t; loc: Location.t; trace: CallSite.t list}

  include PrettyPrintable.PrintableOrderedType with type t := t

  val pp_opt : F.formatter -> t option -> unit

  val get_loc : t -> Location.t
  (** outermost callsite location *)

  val get_earliest_lock_or_call_loc : procname:Procname.t -> t -> Location.t
  (** outermost callsite location OR lock acquisition *)

  val may_deadlock : Tenv.t -> t -> t -> bool
  (** two pairs can run in parallel and satisfy the conditions for deadlock *)

  val make_trace :
    ?header:string -> ?include_acquisitions:bool -> Procname.t -> t -> Errlog.loc_trace

  val can_run_in_parallel : t -> t -> bool
  (** can two pairs describe events on two threads that can run in parallel *)
end

module CriticalPairs : AbstractDomain.FiniteSetS with type elt = CriticalPair.t

module GuardToLockMap : AbstractDomain.WithTop

(* ======================================= *)
(*                   END                   *)
(* @inherited from the starvation analysis *)
(* ======================================= *)


(** snapshot of the relevant state at the time of a heap access: concurrent thread(s), lock(s) held,
    ownership precondition *)
module AccessSnapshot : sig
  module AccessSnapshotElem : sig
    type t =
      { access: Access.t
      ; thread: ThreadsDomain.t
      ; lock: bool
      ; locks: Acquisitions.t 
      ; critical_pair: CriticalPair.t option
      ; ownership_precondition: OwnershipAbstractValue.t }
  end

  include ExplicitTrace.TraceElem with type elem_t = AccessSnapshotElem.t

  val is_write : t -> bool
  (** is it a write OR a container write *)

  val is_container_write : t -> bool

  val get_loc : t -> Location.t

  val make_access :
       FormalMap.t
    -> AccessExpression.t
    -> is_write:bool
    -> Location.t
    -> LockDomain.t
    -> Acquisitions.t
    -> CriticalPair.t option
    -> ThreadsDomain.t
    -> OwnershipAbstractValue.t
    -> t option

  val make_container_access :
       FormalMap.t
    -> AccessExpression.t
    -> is_write:bool
    -> Procname.t
    -> Location.t
    -> LockDomain.t
    -> LockState.t
    -> CriticalPair.t option
    -> ThreadsDomain.t
    -> OwnershipAbstractValue.t
    -> t option

  val is_unprotected : t -> bool
  (** return true if not protected by lock, thread, or ownership *)

  val map_opt : FormalMap.t -> f:(AccessExpression.t -> AccessExpression.t) -> t -> t option

  val update_callee_access :
       FormalMap.t
    -> t
    -> CallSite.t
    -> OwnershipAbstractValue.t
    -> ThreadsDomain.t
    -> LockDomain.t
    -> LockState.t
    -> CriticalPair.t option
    -> t option
end

module AccessDomain : sig
  include AbstractDomain.FiniteSetS with type elt = AccessSnapshot.t

  val add_opt : elt option -> t -> t
end

module OwnershipDomain : sig
  type t

  val empty : t

  val add : AccessExpression.t -> OwnershipAbstractValue.t -> t -> t

  val get_owned : AccessExpression.t -> t -> OwnershipAbstractValue.t

  val propagate_assignment : AccessExpression.t -> HilExp.t -> t -> t

  val propagate_return : AccessExpression.t -> OwnershipAbstractValue.t -> HilExp.t list -> t -> t

  val ownership_of_expr : HilExp.t -> t -> OwnershipAbstractValue.t
end

module Attribute : sig
  type t =
    | Nothing
    | Functional  (** holds a value returned from a callee marked [@Functional] *)
    | OnMainThread  (** boolean is true if the current procedure is running on the main thread *)
    | LockHeld  (** boolean is true if a lock is currently held *)
end

module AttributeMapDomain : sig
  type t

  val find : AccessExpression.t -> t -> Attribute.t

  val add : AccessExpression.t -> Attribute.t -> t -> t

  val is_functional : t -> AccessExpression.t -> bool

  val propagate_assignment : AccessExpression.t -> HilExp.t -> t -> t
  (** propagate attributes from the leaves to the root of an RHS Hil expression *)
end

type t =
  { threads: ThreadsDomain.t  (** current thread: main, background, or unknown *)
  ; locks: LockDomain.t  (** boolean that is true if a lock must currently be held *)
  ; lock_state: LockState.t
  ; critical_pairs: CriticalPairs.t
  ; accesses: AccessDomain.t
        (** read and writes accesses performed without ownership permissions *)
  ; ownership: OwnershipDomain.t  (** map of access paths to ownership predicates *)
  ; attribute_map: AttributeMapDomain.t
        (** map of access paths to attributes such as owned, functional, ... *) }

include AbstractDomain.WithBottom with type t := t

val add_unannotated_call_access : FormalMap.t -> Procname.t -> HilExp.t list -> Location.t -> t -> t

(** same as astate, but without [attribute_map] (since these involve locals) and with the addition
    of the ownership/attributes associated with the return value as well as the set of formals which
    may escape *)
type summary =
  { threads: ThreadsDomain.t
  ; locks: LockDomain.t
  ; critical_pairs: CriticalPairs.t
  ; accesses: AccessDomain.t
  ; return_ownership: OwnershipAbstractValue.t
  ; return_attribute: Attribute.t }

val empty_summary : summary

val pp_summary : F.formatter -> summary -> unit



val acquire : ?tenv:Tenv.t -> t -> procname:Procname.t -> loc:Location.t -> Lock.t list -> t
(** simultaneously acquire a number of locks, no-op if list is empty *)

val release : t -> Lock.t list -> t
(** simultaneously release a number of locks, no-op if list is empty *)

val with_callsite : CriticalPairs.t -> ?tenv:Tenv.t -> ?subst:AbstractAddress.subst -> LockState.t -> CallSite.t -> ThreadsDomain.t -> CriticalPairs.t

val pp_pair_opt : F.formatter -> CriticalPair.t option -> unit

val get_acquisitions : LockState.t -> Acquisitions.t

val different_locks : Acquisitions.t -> Acquisitions.t -> bool
