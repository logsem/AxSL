(*                                                                               *)
(*  BSD 2-clause License                                                         *)
(*                                                                               *)
(*  This applies to all files in this archive except where                       *)
(*  specified otherwise.                                                         *)
(*                                                                               *)
(*  Copyright (c) 2022                                                           *)
(*    Thibaut Pérami                                                             *)
(*    Jean Pichon-Pharabod                                                       *)
(*    Brian Campbell                                                             *)
(*    Alasdair Armstrong                                                         *)
(*    Ben Simner                                                                 *)
(*    Peter Sewell                                                               *)
(*                                                                               *)
(*  All rights reserved.                                                         *)
(*                                                                               *)
(*  Redistribution and use in source and binary forms, with or without           *)
(*  modification, are permitted provided that the following conditions           *)
(*  are met:                                                                     *)
(*                                                                               *)
(*    * Redistributions of source code must retain the above copyright           *)
(*      notice, this list of conditions and the following disclaimer.            *)
(*    * Redistributions in binary form must reproduce the above copyright        *)
(*      notice, this list of conditions and the following disclaimer in the      *)
(*      documentation and/or other materials provided with the distribution.     *)
(*                                                                               *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS          *)
(*  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT            *)
(*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A      *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER    *)
(*  OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,     *)
(*  EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,          *)
(*  PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;  *)
(*  OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,     *)
(*  WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR      *)
(*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF       *)
(*  ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                                   *)
(*                                                                               *)

Require Import Strings.String.
Require Import stdpp.unstable.bitvector.
Require Import stdpp.strings.
Require Import stdpp.base.
Require Import stdpp.countable.
Require Import Interface.
Require Import Sail.Base.
Require Export SailArmInstTypes.
Require Import Coq.Reals.Reals.
From RecordUpdate Require Import RecordSet.

Require Import stdpp.decidable.

Inductive regval  :=
  | Regval_unknown : regval
  | Regval_vector : list regval -> regval
  | Regval_list : list regval -> regval
  | Regval_option : option regval -> regval
  | Regval_bool : bool -> regval
  | Regval_int : Z -> regval
  | Regval_real : R -> regval
  | Regval_string : string -> regval
  | Regval_bitvector z : bv z -> regval
  | Regval_struct : list (string * regval) -> regval.

Definition regval_bv (n : N) (rv : regval) : option (bv n).
Proof.
  destruct rv.
  exact None.
  exact None.
  exact None.
  exact None.
  exact None.
  exact None.
  exact None.
  exact None.
  destruct (decide (n = z)).
  destruct e.
  exact (Some b).
  exact None.
  exact None.
Qed.

#[global] Instance FullAddress_eta : Settable _ :=
  settable! Build_FullAddress <FullAddress_paspace; FullAddress_address>.

#[global] Instance PASpace_eq_dec : EqDecision PASpace.
Proof. solve_decision. Qed.
#[global] Instance FullAddress_eq_dec : EqDecision FullAddress.
Proof. solve_decision. Qed.

Definition PASpace_to_nat (pa : PASpace) : nat :=
  match pa with
  | PAS_NonSecure => 0
  | PAS_Secure => 1
  | PAS_Root => 2
  | PAS_Realm => 3
  end.

Definition PASpace_from_nat (pa : nat) :=
  match pa with
  | 0%nat => Some PAS_NonSecure
  | 1%nat => Some PAS_Secure
  | 2%nat => Some PAS_Root
  | 3%nat => Some PAS_Realm
  | _ => None
  end.

Lemma PASpace_from_nat_to_nat (pa : PASpace) :
  PASpace_from_nat (PASpace_to_nat pa) = Some pa.
Proof. by destruct pa. Qed.

#[global] Instance PASpace_countable : Countable PASpace.
Proof.
  apply (inj_countable PASpace_to_nat PASpace_from_nat PASpace_from_nat_to_nat).
Qed.

#[global] Instance FullAddress_countable : Countable FullAddress.
Proof.
  eapply (inj_countable (fun fa => (FullAddress_paspace fa, FullAddress_address fa))
                        (fun x => Some (Build_FullAddress x.1 x.2))).
  intro x. by destruct x.
Qed.

Module Arm <: Arch.
  Definition reg := string.
  Definition reg_eq : EqDecision reg := _.
  Definition reg_countable : Countable reg := _.
  Definition reg_type := regval.
  Definition va_size := 64%N.
  Definition pa := FullAddress.
  Definition pa_eq : EqDecision pa := _.
  Definition pa_countable : Countable pa := _.
  Definition arch_ak := arm_acc_type.
  Definition translation := TranslationInfo.
  Definition abort := PhysMemRetStatus.
  Definition barrier := Barrier.
  Definition cache_op := CacheRecord.
  Definition tlb_op := TLBI.
  Definition fault := Exn.
End Arm.
Bind Scope string_scope with Arm.reg.

Module Inst := Interface Arm.

Export Inst.
