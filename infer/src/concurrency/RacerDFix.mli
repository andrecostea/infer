(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd

val file_analysis : RacerDFixDomain.summary InterproceduralAnalysis.file_t -> IssueLog.t

val analyze_procedure :
  RacerDFixDomain.summary InterproceduralAnalysis.t -> RacerDFixDomain.summary option
