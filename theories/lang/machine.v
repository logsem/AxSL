(**************************************************************************************)
(*  BSD 2-Clause License                                                              *)
(*                                                                                    *)
(*  This applies to all files in this archive except folder                           *)
(*  "system-semantics".                                                               *)
(*                                                                                    *)
(*  Copyright (c) 2023,                                                               *)
(*       Zongyuan Liu                                                                 *)
(*       Angus Hammond                                                                *)
(*       Jean Pichon-Pharabod                                                         *)
(*       Thibaut Pérami                                                               *)
(*                                                                                    *)
(*  All rights reserved.                                                              *)
(*                                                                                    *)
(*  Redistribution and use in source and binary forms, with or without                *)
(*  modification, are permitted provided that the following conditions are met:       *)
(*                                                                                    *)
(*  1. Redistributions of source code must retain the above copyright notice, this    *)
(*     list of conditions and the following disclaimer.                               *)
(*                                                                                    *)
(*  2. Redistributions in binary form must reproduce the above copyright notice,      *)
(*     this list of conditions and the following disclaimer in the documentation      *)
(*     and/or other materials provided with the distribution.                         *)
(*                                                                                    *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"       *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE         *)
(*  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE    *)
(*  DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE      *)
(*  FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL        *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR        *)
(*  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER        *)
(*  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,     *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE     *)
(*  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.              *)
(*                                                                                    *)
(**************************************************************************************)

(** This file includes our instantiation of [CandidateExecutions],
    and wrappers for types of [system-semantics-coq] *)
Require Import stdpp.strings.
Require Import stdpp.bitvector.definitions.

Require Export self.CandidateExecutions.
Require Import ISASem.Interface.
Require Export ISASem.SailArmInstTypes.
Require Import SSCCommon.Common.

Export IfNotations.

Open Scope stdpp_scope.


(* Adapted from ArchSemArm.ArmInst *)
Module Arm.
  Module Arch <: Arch.

    Definition reg := string.
    #[export] Typeclasses Transparent reg.
    Instance reg_eq : EqDecision (reg) := _.

    Instance reg_countable : Countable reg := _.

    Definition CHERI := false.
    Definition cap_size := 16%N. (* dummy value since CHERI is off*)

    Definition dw_size := 64%N.

    Definition reg_type (r: reg) := bv dw_size.
    #[export] Typeclasses Transparent reg_type.

    Definition reg_type_eq r : EqDecision (reg_type r) := _.
    Definition reg_type_countable r : Countable (reg_type r) := _.
    Definition reg_type_inhabited r : Inhabited (reg_type r) := _.

    Instance ctrans_reg_type : CTrans reg_type.
    Proof. unfold CTrans. intros ? ? ->. done. Defined.

   Instance ctrans_reg_type_simpl : CTransSimpl reg_type.
   Proof.
     unfold CTransSimpl. intros ? ? ?.
     unfold reg_type in a.
     unfold reg in x.
     unfold ctrans.
     unfold ctrans_reg_type.
     symmetry.
     unfold eq_rec_r.
     rewrite <-Eqdep.EqdepTheory.eq_rec_eq.
     done.
   Qed.

   Instance reg_type_eq_dep_dec : EqDepDecision reg_type.
   Proof.
     unfold EqDepDecision.
     intros ? ? -> ??.
     rewrite JMeq_simpl.
     apply _.
   Qed.

    (** None means default access (strict or relaxed is up to the concurrency model).
        Some s, means access with a MSR/MRS with name "s" *)
    Definition reg_acc := unit.
    #[export] Typeclasses Transparent reg_acc.
    Definition reg_acc_eq : EqDecision reg_acc := _.


    Definition pa := bv dw_size.
    #[export] Typeclasses Transparent pa.
    Definition pa_eq : EqDecision pa := _.
    Definition pa_countable : Countable pa := _.
    Definition pa_addZ (pa:pa) z := (pa `+Z` z)%bv.
    Arguments pa_addZ !pa z /.

    Ltac pa_unfold := change pa with (bv dw_size) in *.
    Ltac pa_solve := pa_unfold; bv_solve.

    Lemma pa_addZ_assoc pa z z' :
      pa_addZ (pa_addZ pa z) z' = pa_addZ pa (z + z')%Z.
    Proof. unfold pa_addZ. pa_solve. Qed.
    Lemma pa_addZ_zero pa : pa_addZ pa 0 = pa.
    Proof. unfold pa_addZ. pa_solve. Qed.

    Definition pa_diffN (pa' pa : pa) :=
      Some $ Z.to_N $ bv_unsigned ((pa' : bv dw_size) - pa).
    Lemma pa_diffN_addZ pa pa' n :
      pa_diffN pa' pa = Some n → pa_addZ pa (Z.of_N n) = pa'.
    Proof.
      unfold pa_diffN, pa_addZ. cdestruct n |- ?.
      pa_solve.
    Qed.

    Lemma pa_diffN_existZ pa pa' z :
      pa_addZ pa z = pa' → is_Some (pa_diffN pa' pa).
    Proof. unfold pa_diffN, pa_addZ. hauto q:on. Qed.

    Lemma pa_diffN_minimalZ pa pa' n :
      pa_diffN pa' pa = Some n →
        ∀ z', pa_addZ pa z' = pa' → (z' < 0 ∨ (Z.of_N n) ≤ z')%Z.
    Proof. unfold pa_diffN, pa_addZ. cdestruct pa',n |- ***. pa_solve. Qed.


    (* Definition pa := Z. *)
    (* #[export] Typeclasses Transparent pa. *)
    (* Definition pa_eq : EqDecision pa := _. *)
    (* Definition pa_countable : Countable pa := _. *)
    (* Definition pa_addZ (pa:pa) z := (pa + z)%Z. *)
    (* Arguments pa_addZ !pa z /. *)

    (* Lemma pa_addZ_assoc pa z z' : *)
    (*   pa_addZ (pa_addZ pa z) z' = pa_addZ pa (z + z')%Z. *)
    (* Proof. unfold pa_addZ. lia. Qed. *)
    (* Lemma pa_addZ_zero pa : pa_addZ pa 0 = pa. *)
    (* Proof. unfold pa_addZ. lia. Qed. *)

    (* Definition pa_diffN (pa' pa: pa) := *)
    (* if bool_decide (0 <= (pa' - pa))%Z *)
    (*   then Some (Z.to_N (pa' - pa)) else None. *)
    (*   (* Some $ Z.to_N $ (pa' - pa)%Z. *) *)


    (* Lemma pa_diffN_addZ pa pa' n: *)
    (*   pa_diffN pa' pa = Some n → pa_addZ pa (Z.of_N n) = pa'. *)
    (* Proof. *)
    (*   unfold pa_diffN, pa_addZ, set. *)
    (*   cdestruct |- ***. subst. *)
    (*   (* destruct ((pa' - pa)%Z) eqn: Heqn. *) *)

    (*   (* unfold Z.to_N. *) *)
    (*   (* lia. *) *)
    (*   (* lia. *) *)
    (*   (* unfold Z.to_N. *) *)
    (*   (* lia. *) *)
    (* Admitted. *)

    (* Lemma pa_diffN_existZ (pa pa': pa) z: *)
    (*   (z >= 0) %Z -> *)
    (*   pa_addZ pa z = pa' → is_Some (pa_diffN pa' pa). *)
    (* Proof. *)
    (*   unfold pa_addZ. *)
    (*   unfold pa_diffN. *)
    (*   cdestruct |- ?. *)
    (*   subst. *)
    (*   case_bool_decide;try naive_solver lia. *)
    (*   done. *)
    (* Qed. *)

    (* #[local] Opaque N.le. *)
    (* Lemma pa_diffN_minimalZ pa pa' n: *)
    (*   pa_diffN pa' pa = Some n → *)
    (*   ∀ z', pa_addZ pa z' = pa' → (z' < 0 ∨ (Z.of_N n) ≤ z')%Z. *)
    (* Proof. *)
    (*   unfold pa_diffN, pa_addZ. *)
    (*   case_bool_decide. *)
    (*   cdestruct |- ***. *)
    (*   subst. lia. *)
    (*   inversion 1. *)
    (* Qed. *)

    (* Definition pa := bv va_size. *)
    (* #[export] Typeclasses Transparent pa. *)
    (* Definition pa_eq : EqDecision pa := _. *)
    (* Definition pa_countable : Countable pa := _. *)
    (* Definition pa_addZ (pa:pa) z := (pa `+Z` z)%bv. *)
    (* Arguments pa_addZ !pa z /. *)

    (* Lemma pa_addZ_assoc pa z z' : *)
    (*   pa_addZ (pa_addZ pa z) z' = pa_addZ pa (z + z')%Z. *)
    (* Proof. bv_solve. Qed. *)
    (* Lemma pa_addZ_zero pa : pa_addZ pa 0 = pa. *)
    (* Proof. bv_solve. Qed. *)

    (* Definition pa_diffN (pa' pa: pa) := Some $ Z.to_N $ bv_unsigned (pa' - pa). *)

    (* Lemma pa_diffN_addZ pa pa' n: *)
    (*   pa_diffN pa' pa = Some n → pa_addZ pa (Z.of_N n) = pa'. *)
    (* Proof. *)
    (* unfold pa_diffN, pa_addZ, set. *)
    (* destruct pa, pa'. cbn. *)
    (* cdestruct n |- ** # CDestrMatch. *)
    (* bv_solve. *)
    (* Qed. *)
    (* Lemma pa_diffN_existZ (pa pa': pa) z: *)
    (*   pa_addZ pa z = pa' → is_Some (pa_diffN pa' pa). *)
    (* Proof. *)
    (*   destruct pa, pa'. *)
    (*   cdestruct |- ?. *)
    (*   unfold pa_diffN. hauto q:on. *)
    (* Qed. *)
    (* #[local] Opaque N.le. *)
    (* Lemma pa_diffN_minimalZ pa pa' n: *)
    (*   pa_diffN pa' pa = Some n → *)
    (*   ∀ z', pa_addZ pa z' = pa' → (z' < 0 ∨ (Z.of_N n) ≤ z')%Z. *)
    (* Proof. *)
    (*   unfold pa_diffN. *)
    (*   cdestruct pa, pa', n |- ** # CDestrMatch. *)
    (*   bv_solve. *)
    (* Qed. *)


    #[global] Instance Access_variety_eq_dec : EqDecision Access_variety.
    Proof. solve_decision. Defined.

    #[global] Instance Access_strength_eq_dec : EqDecision Access_strength.
    Proof. solve_decision. Defined.

    #[global] Instance Explicit_access_kind_eq_dec : EqDecision Explicit_access_kind.
    Proof. solve_decision. Defined.

    #[global] Instance Access_kind_eq_dec `{EqDecision arch_ak} : EqDecision (Access_kind arch_ak).
    Proof. solve_decision. Defined.

    #[global] Instance arm_acc_type_eq_dec : EqDecision arm_acc_type.
    Proof. solve_decision. Defined.

    #[global] Instance MemAttrHints_eq_dec : EqDecision MemAttrHints.
    Proof. solve_decision. Defined.

    #[global] Instance MemType_eq_dec : EqDecision MemType.
    Proof. solve_decision. Defined.

    #[global] Instance DeviceType_eq_dec : EqDecision DeviceType.
    Proof. solve_decision. Defined.

    #[global] Instance Shareability_eq_dec : EqDecision Shareability.
    Proof. solve_decision. Defined.

    #[global] Instance MemoryAttributes_eq_dec : EqDecision MemoryAttributes.
    Proof. solve_decision. Defined.

    #[global] Instance TGx_eq_dec : EqDecision TGx.
    Proof. solve_decision. Defined.

    #[global] Instance S1TTWParams_eq_dec : EqDecision S1TTWParams.
    Proof. solve_decision. Defined.

    #[global] Instance S2TTWParams_eq_dec : EqDecision S2TTWParams.
    Proof. solve_decision. Defined.

    #[global] Instance Level_eq_dec : EqDecision Level.
    Proof. unfold Level. solve_decision. Defined.

    #[global] Instance Regime_eq_dec : EqDecision Regime.
    Proof. solve_decision. Defined.

    #[global] Instance TranslationInfo_eq_dec : EqDecision TranslationInfo.
    Proof. solve_decision. Defined.

    #[global] Instance MBReqDomain_eq_dec : EqDecision MBReqDomain.
    Proof. solve_decision. Defined.

    #[global] Instance MBReqTypes_eq_dec : EqDecision MBReqTypes.
    Proof. solve_decision. Defined.

    #[global] Instance DxB_eq_dec : EqDecision DxB.
    Proof. solve_decision. Defined.

    #[global] Instance Barrier_eq_dec : EqDecision Barrier.
    Proof. solve_decision. Defined.

    #[global] Instance AccType_eq_dec : EqDecision AccType.
    Proof. solve_decision. Defined.


    Definition mem_acc := Access_kind arm_acc_type.
    #[export] Typeclasses Transparent mem_acc.
    Definition mem_acc_eq : EqDecision mem_acc := _.
    Definition is_explicit (acc : mem_acc) :=
      if acc is AK_explicit _ then true else false.
    Definition is_ifetch (acc : mem_acc) :=
      if acc is AK_ifetch _ then true else false.
    Definition is_ttw (acc : mem_acc) :=
      if acc is AK_ttw _ then true else false.
    Definition is_relaxed (acc : mem_acc) :=
      if acc is AK_explicit eak then
        eak.(Explicit_access_kind_strength) =? AS_normal else false.
    Definition is_rel_acq (acc : mem_acc) :=
      if acc is AK_explicit eak then
        eak.(Explicit_access_kind_strength) =? AS_rel_or_acq else false.
    Definition is_acq_rcpc (acc : mem_acc) :=
      if acc is AK_explicit eak then
        eak.(Explicit_access_kind_strength) =? AS_acq_rcpc else false.
    Definition is_standalone (acc : mem_acc) :=
      if acc is AK_explicit eak then
        eak.(Explicit_access_kind_variety) =? AV_plain else false.
    Definition is_exclusive (acc : mem_acc) :=
      if acc is AK_explicit eak then
        eak.(Explicit_access_kind_variety) =? AV_exclusive else false.
    Definition is_atomic_rmw (acc : mem_acc) :=
      if acc is AK_explicit eak then
        eak.(Explicit_access_kind_variety) =? AV_atomic_rmw else false.

    Definition barrier := SailArmInstTypes.Barrier.
    Definition barrier_eq : EqDecision SailArmInstTypes.Barrier := _.

    Definition abort := False.
    Definition cache_op := unit.
    Definition cache_op_eq : EqDecision unit := _.

    Definition tlb_op := unit.
    Definition tlb_op_eq : EqDecision unit := _.
    Definition fault := unit.
    Definition fault_eq : EqDecision unit := _.


  End Arch.
  Module Interface := Interface Arch.
End Arm.

Bind Scope string_scope with Arm.Arch.reg.

Module AACand := CandidateExecutions Arm.

Export Arm.Arch.

Module AAInter := Arm.Interface.

Definition Val := bv Arm.Arch.dw_size.
#[export] Typeclasses Transparent Val.
Definition Addr := bv Arm.Arch.dw_size.
#[export] Typeclasses Transparent Addr.

Definition RegName := Arm.Arch.reg.
#[export] Typeclasses Transparent RegName.

Definition BarrierKind := Arm.Arch.barrier.
Definition AccessKind := Arm.Arch.mem_acc.

Definition InstTrace := AAInter.iTrace ().
Definition InstSem := AAInter.iMon ().

Definition Event := AAInter.iEvent.

Notation Eid := AACand.EID.t.

Require Import SSCCommon.GRel.
Notation Rel := (grel Eid) (only parsing).
