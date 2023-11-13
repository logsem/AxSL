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

(* The file contains the [interp_mod] modality, which allows one to access
 [annot_interp] with a basic update modality *)
From iris.proofmode Require Import base tactics classes.
From self.low Require Import iris.

Definition interp_mod_def `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} (P : iProp Σ) : iProp Σ :=
  ∀ na, annot_interp na ==∗ P ∗ annot_interp na.

Definition interp_mod_aux : seal (@interp_mod_def). Proof. by eexists. Qed.
Definition interp_mod := interp_mod_aux.(unseal).
Arguments interp_mod {Σ _ _ _}.
Definition interp_mod_eq : @interp_mod = @interp_mod_def := interp_mod_aux.(seal_eq).
Notation "|=i=> P" := (interp_mod P) (at level 20) : bi_scope.

Section lemma.
  Context `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG}.

  Lemma interp_mod_mono P Q :
    (P -∗ Q)
    ⊢
    (|=i=> P) -∗ |=i=> Q.
  Proof.
    iIntros "H".
    rewrite interp_mod_eq /interp_mod_def.
    iIntros "P". iIntros (?) "Hannot".
    iMod ("P" with "Hannot") as "[P $]". iModIntro.
    by iApply "H".
  Qed.

  Lemma interp_mod_strong_mono P Q :
    (P ==∗ Q)
    ⊢
    (|=i=> P) -∗ |=i=> Q.
  Proof.
    iIntros "H".
    rewrite interp_mod_eq /interp_mod_def.
    iIntros "P". iIntros (?) "Hannot".
    iMod ("P" with "Hannot") as "[P $]".
    by iApply "H".
  Qed.

  Lemma interp_mod_bupd P:
    (|==> |=i=> P)%I ⊢ |=i=> P.
  Proof.
    iIntros "H".
    rewrite interp_mod_eq /interp_mod_def.
    iIntros (?) "Hannot". iMod "H".
    iMod ("H" with "Hannot") as "[P $]".
    done.
  Qed.

  Lemma interp_mod_bupd' P:
    (|==> P)%I ⊢ |=i=> P.
  Proof.
    iIntros "H".
    rewrite interp_mod_eq /interp_mod_def.
    iIntros (?) "Hannot". iMod "H".
    by iFrame.
  Qed.

  Lemma interp_mod_frame_l P Q:
    P ∗ |=i=> Q ⊢ |=i=> (P ∗ Q).
  Proof.
    iIntros "[P Q]".
    iApply (interp_mod_mono with "[P]").
    2:{ iFrame. }
    iIntros "?". iFrame.
  Qed.

  Lemma interp_mod_frame_r P Q:
    (|=i=> P) ∗ Q ⊢ |=i=> (P ∗ Q).
  Proof.
    iIntros "[P Q]".
    iApply (interp_mod_mono with "[Q]").
    2:{ iFrame. }
    iIntros "?". iFrame.
  Qed.

  Lemma interp_mod_sep P Q:
    |=i=> P ∗ |=i=> Q ⊢ |=i=> (P ∗ Q).
  Proof.
    iIntros "[P Q]".
    rewrite interp_mod_eq /interp_mod_def.
    iIntros (?) "Hannot".
    iMod ("P" with "Hannot") as "[$ Hannot]".
    by iMod ("Q" with "Hannot") as "[$ $]".
  Qed.

  Lemma interp_mod_intro P:
    P ⊢ |=i=> P.
  Proof.
    iIntros "P".
    rewrite interp_mod_eq /interp_mod_def.
    iIntros (?) "Hannot".
    by iFrame.
  Qed.

  Lemma interp_mod_wand_r P Q:
    (|=i=> P) ∗ (P -∗ Q) ⊢ |=i=> Q.
  Proof.
    iIntros "[P H]".
    by iApply (interp_mod_mono with "H").
  Qed.

  Lemma interp_mod_trans P:
    (|=i=> |=i=> P) ⊢ |=i=> P.
  Proof.
    iIntros "P".
    rewrite interp_mod_eq /interp_mod_def.
    iIntros (?) "Hannot".
    iMod ("P" with "Hannot") as "[P Hannot]".
    iMod ("P" with "Hannot") as "[P Hannot]".
    by iFrame.
  Qed.

  Lemma interp_mod_or P Q:
    (|=i=> P) ∨ (|=i=> Q) ⊢ |=i=> (P ∨ Q).
  Proof.
    iIntros "H".
    iDestruct "H" as "[H|H]";
    (iApply interp_mod_mono;[|iFrame]);[iApply bi.or_intro_l| iApply bi.or_intro_r].
  Qed.

  Lemma interp_mod_and P Q:
    |=i=> (P ∧ Q) ⊢ |=i=> P ∧ |=i=> Q.
  Proof.
    iIntros "H".
    iSplit; (iApply interp_mod_mono;[|iFrame]); [iApply bi.and_elim_l| iApply bi.and_elim_r].
  Qed.

  Lemma interp_mod_exists {A} P:
    (∃ x : A, |=i=> P x) ⊢ |=i=> (∃ x : A, P x).
  Proof.
    iIntros "[% H]".
    iApply interp_mod_mono;[|iFrame].
    iIntros "?"; iExists _;iFrame.
  Qed.

  Lemma interp_mod_forall {A} P:
    |=i=> (∀ x : A, P x) ⊢ ∀ x : A, |=i=> (P x).
  Proof.
    iIntros "H". iIntros (?).
    iApply interp_mod_mono;[|iFrame].
    iIntros "H". iApply "H".
  Qed.

  (* These don't hold *)
  (* Lemma interp_mod_except_0 P: *)
  (*    ◇ (|=i=> P) ⊢ |=i=> (◇ P). *)

  (* Lemma interp_mod_plain P: *)
  (*   Plain P → (|=i=> P) ⊢ P. *)

  Global Instance interp_mod_proper :
    Proper ( bi_entails --> flip bi_entails ) interp_mod.
  Proof.
    rewrite /Proper.
    intros ? ? Hi.
    iIntros "?".
    iApply interp_mod_mono.
    2: { iFrame. }
    iIntros "?".
    by iApply Hi.
  Qed.

  Global Instance interp_mod_proper' :
    Proper (bi_entails ==> bi_entails ) interp_mod.
  Proof.
    rewrite /Proper.
    intros ? ? Hi.
    iIntros "?".
    iApply interp_mod_mono.
    2: { iFrame. }
    iIntros "?".
    by iApply Hi.
  Qed.


  Global Instance interp_mod_ne :
    NonExpansive interp_mod.
  Proof.
    rewrite interp_mod_eq /interp_mod_def.
    intros ????.
    do 5 f_equiv;done.
  Qed.

  Global Instance interp_mod_proper'' :
    Proper ((≡) ==> (≡)) interp_mod := ne_proper _.

End lemma.

From stdpp Require Import nat_cancel.
From iris.proofmode Require Import modality_instances classes.
From iris.proofmode Require Import ltac_tactics class_instances.
From iris.prelude Require Import options.

Section class_instances_updates.
  Context `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG}.
  Implicit Types P Q R : (iProp Σ).

  Global Instance from_assumption_iupd p P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (|=i=> Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply interp_mod_intro. Qed.

  Global Instance from_pure_iupd a P φ :
    FromPure a P φ → FromPure a (|=i=> P) φ.
  Proof. rewrite /FromPure=> HR. setoid_rewrite <- HR.  apply interp_mod_intro. Qed.

  Global Instance into_wand_iupd p q R P Q :
    IntoWand false false R P Q → IntoWand p q (|=i=> R) (|=i=> P) (|=i=> Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite !bi.intuitionistically_if_elim HR.
    apply bi.wand_intro_l. by rewrite interp_mod_sep bi.wand_elim_r.
  Qed.

  Global Instance into_wand_iupd_persistent p q R P Q :
    IntoWand false q R P Q → IntoWand p q (|=i=> R) P (|=i=> Q).
  Proof.
    rewrite /IntoWand /= => HR.
    rewrite bi.intuitionistically_if_elim HR.
    apply bi.wand_intro_l. by rewrite interp_mod_frame_l bi.wand_elim_r.
  Qed.

  Global Instance into_wand_iupd_args p q R P Q :
    IntoWand p false R P Q → IntoWand' p q R (|=i=> P) (|=i=> Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    apply bi.wand_intro_l. by rewrite bi.intuitionistically_if_elim interp_mod_wand_r.
  Qed.

  Global Instance from_sep_iupd P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (|=i=> P) (|=i=> Q1) (|=i=> Q2).
  Proof. rewrite /FromSep=> HR. rewrite interp_mod_sep.
         iApply interp_mod_mono. iIntros "[? ?]". iApply HR. by iFrame. Qed.

  Global Instance from_or_iupd  P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (|=i=> P) (|=i=> Q1) (|=i=> Q2).
  Proof. rewrite /FromOr=><-. apply interp_mod_or. Qed.

  Global Instance into_and_iupd P Q1 Q2 :
    IntoAnd false P Q1 Q2 → IntoAnd false (|=i=> P) (|=i=> Q1) (|=i=> Q2).
  Proof. rewrite /IntoAnd/==>->. apply interp_mod_and. Qed.

  Global Instance from_exist_iupd {A} P (Φ : A → iProp Σ) :
    FromExist P Φ → FromExist (|=i=> P) (λ a, |=i=> Φ a)%I.
  Proof. rewrite /FromExist=><-. apply interp_mod_exists. Qed.

  Global Instance into_forall_bupd {A} P (Φ : A → iProp Σ) :
    IntoForall P Φ → IntoForall (|=i=> P) (λ a, |=i=> Φ a)%I.
  Proof. rewrite /IntoForall=>->. apply interp_mod_forall. Qed.

  (* Global Instance is_except_0_bupd P : IsExcept0 P → IsExcept0 (|=i=> P). *)
  (* Proof. *)
  (*   rewrite /IsExcept0=> HP. *)
  (*   by rewrite -{2}HP -(except_0_idemp P) -except_0_bupd -(except_0_intro P). *)
  (* Qed. *)

  Global Instance from_modal_iupd P :
    FromModal True modality_id (|=i=> P) (|=i=> P) P.
  Proof. by rewrite /FromModal /= -interp_mod_intro. Qed.

  Global Instance elim_modal_iupd p P Q :
    ElimModal True p false (|=i=> P) P (|=i=> Q) (|=i=> Q).
  Proof.
    rewrite /ElimModal
      bi.intuitionistically_if_elim interp_mod_frame_r. iIntros (_).
    setoid_rewrite bi.wand_elim_r. by rewrite interp_mod_trans.
  Qed.

  (* Global Instance elim_modal_bupd_plain_goal p P Q : *)
  (*   Plain Q → ElimModal True p false (|=i=> P) P Q Q. *)
  (* Proof. *)
  (*   intros. rewrite /ElimModal bi.intuitionistically_if_elim *)
  (*     interp_mod_frame_r bi.wand_elim_r. bupd_plain. *)
  (* Qed. *)

  (* Global Instance elim_modal_bupd_plain *)
  (*     `{!BiBUpd PROP, !BiPlainly PROP, !BiBUpdPlainly PROP} p P Q : *)
  (*   Plain P → ElimModal True p p (|==> P) P Q Q. *)
  (* Proof. intros. by rewrite /ElimModal bupd_plain wand_elim_r. Qed. *)

  Global Instance elim_modal_bupd_iupd p P Q :
    ElimModal True p false (|==> P) P (|=i=> Q) (|=i=> Q) | 10.
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      interp_mod_bupd' interp_mod_frame_r bi.wand_elim_r interp_mod_trans.
  Qed.
  Global Instance elim_modal_iupd_iupd p P Q :
    ElimModal True p false (|=i=> P) P (|=i=> Q) (|=i=> Q).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      interp_mod_frame_r bi.wand_elim_r interp_mod_trans.
  Qed.

  Global Instance add_modal_iupd P Q : AddModal (|=i=> P) P (|=i=> Q).
  Proof. by rewrite /AddModal interp_mod_frame_r bi.wand_elim_r interp_mod_trans. Qed.

  Global Instance elim_acc_iupd {X} α β mγ Q :
    ElimAcc (X:=X) True interp_mod interp_mod α β mγ
      (|=i=> Q)
      (λ x, |=i=> β x ∗ (mγ x -∗? |=i=> Q))%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iDestruct ("Hinner" with "Hα") as "[Hβ Hfin]".
    iMod ("Hclose" with "Hβ") as ">Hγ". by iApply "Hfin".
  Qed.
End class_instances_updates.
