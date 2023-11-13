(** This file includes our instantiation of [CandidateExecutions],
    and wrappers for types of [system-semantics-coq] *)
Require Import stdpp.strings.
Require Import stdpp.unstable.bitvector.

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
  Definition arch_ak := unit.
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
