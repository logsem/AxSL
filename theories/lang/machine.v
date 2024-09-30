(*                                                                                  *)
(*  BSD 2-Clause License                                                            *)
(*                                                                                  *)
(*  This applies to all files in this archive except folder                         *)
(*  "system-semantics".                                                             *)
(*                                                                                  *)
(*  Copyright (c) 2023,                                                             *)
(*     Zongyuan Liu                                                                 *)
(*     Angus Hammond                                                                *)
(*     Jean Pichon-Pharabod                                                         *)
(*     Thibaut Pérami                                                               *)
(*                                                                                  *)
(*  All rights reserved.                                                            *)
(*                                                                                  *)
(*  Redistribution and use in source and binary forms, with or without              *)
(*  modification, are permitted provided that the following conditions are met:     *)
(*                                                                                  *)
(*  1. Redistributions of source code must retain the above copyright notice, this  *)
(*     list of conditions and the following disclaimer.                             *)
(*                                                                                  *)
(*  2. Redistributions in binary form must reproduce the above copyright notice,    *)
(*     this list of conditions and the following disclaimer in the documentation    *)
(*     and/or other materials provided with the distribution.                       *)
(*                                                                                  *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"     *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE       *)
(*  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE  *)
(*  DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE    *)
(*  FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL      *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR      *)
(*  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER      *)
(*  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,   *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE   *)
(*  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.            *)
(*                                                                                  *)

(** This file includes our instantiation of [CandidateExecutions],
    and wrappers for types of [system-semantics-coq] *)
Require Import stdpp.strings.
Require Import stdpp.bitvector.definitions.

Require Export self.CandidateExecutions.
Require Import ISASem.Interface.
Require Export ISASem.SailArmInstTypes.
Require Import SSCCommon.Common.

Open Scope stdpp_scope.
Definition AAval (n : N):= bv (8 * n).


Module AAArch <: Arch.
  Definition reg := string.
  Definition reg_eq : EqDecision reg := _.
  Definition reg_countable : @Countable reg reg_eq := _.
  Definition val_size : N := 8.
  Definition val := AAval val_size.
  Definition reg_type := val.
  (* addresses and registers are of the same length for simplicity *)
  Definition va_size := 64%N.
  Definition pa := val.
  Definition pa_eq : EqDecision pa := _.
  Definition pa_countable : @Countable pa pa_eq := _.
  (* XXX extra types, not sure about it *)
  Definition arch_ak := unit.
  (* XXX what is this? *)
  Definition translation := unit.
  Inductive dmb_kind := | Sy | Ld | St.
  Inductive barrier_type :=
  | DMB (k : dmb_kind) | ISB.
  Definition barrier := barrier_type.
  (* below are not used, so empty *)
  Definition abort := False.
  Definition cache_op := False.
  Definition tlb_op := False.
  Definition fault := False.
End AAArch.

Module AAInter <: InterfaceT AAArch := Interface AAArch.
Module AACandExec := CandidateExecutions AAArch AAInter.

Definition Val := AAArch.val.
Definition Addr := AAArch.val.
Definition RegName := AAInter.reg.
Definition DmbKind := AAArch.dmb_kind.
Definition BarrierKind := AAArch.barrier.

Definition InstTrace := AACandExec.iTrace ().
Definition InstSem := AACandExec.iMon ().
Definition Event := AACandExec.iEvent.
Notation Eid := EID.t.

Require Import SSCCommon.GRel.
Notation Rel := (grel Eid) (only parsing).
