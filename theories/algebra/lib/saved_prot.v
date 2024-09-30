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

From iris.base_logic.lib Require Import saved_prop.
From iris.proofmode Require Import proofmode.

(* Saved protocol *)
Notation savedProtG Σ A B := (savedAnythingG Σ (A -d> B -d> ▶ ∙)).
Notation savedProtΣ A B := (savedAnythingΣ (A -d> B -d> ▶ ∙)).

Section saved_prot.
  Context `{!savedProtG Σ A B}.

  Definition saved_prot_own (γ : gname) (Φ : A → B -> iProp Σ) :=
    saved_anything_own (F := A -d> B -d> ▶ ∙) γ (dfrac.DfracDiscarded) (λ a b, Next (Φ a b)).

  Global Instance saved_prot_own_contractive `{!savedProtG Σ A B} γ :
    Contractive (saved_prot_own γ : (A -d> B -d> iPropO Σ) → iProp Σ).
  Proof.
    solve_proper_core ltac:(fun _ => first [ intros ??; progress simpl | by auto | f_contractive | f_equiv ]).
  Qed.

  Global Instance saved_prot_persistent γ Φ :
    Persistent (saved_prot_own γ Φ).
  Proof. apply _. Qed.

  (** Allocation *)
  Lemma saved_prot_alloc_strong (I : gname → Prop) (Φ : A → B -> iProp Σ):
    pred_infinite I →
    ⊢ |==> ∃ γ, ⌜I γ⌝ ∗ saved_prot_own γ Φ.
  Proof. intros ?. by apply saved_anything_alloc_strong. Qed.

  Lemma saved_prot_alloc_cofinite (G : gset gname) (Φ : A → B -> iProp Σ):
    ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ saved_prot_own γ Φ.
  Proof. by apply saved_anything_alloc_cofinite. Qed.

  Lemma saved_prot_alloc (Φ : A → B -> iProp Σ) :
    ⊢ |==> ∃ γ, saved_prot_own γ Φ.
  Proof. apply saved_anything_alloc. done. Qed.

  (** Validity *)
  Lemma saved_prot_valid γ Φ Ψ x y :
    saved_prot_own γ Φ -∗ saved_prot_own γ Ψ -∗ ▷ (Φ x y ≡ Ψ x y).
  Proof.
    iIntros "HΦ HΨ".
    iCombine "HΦ HΨ" gives "(_ & Hag)".
    iApply later_equivI.
    iDestruct (discrete_fun_equivI with "Hag") as "Hag'".
    iSpecialize ("Hag'" $! x).
    iApply (discrete_fun_equivI with "Hag'").
  Qed.
  Lemma saved_prot_agree γ Φ Ψ x y:
    saved_prot_own γ Φ -∗ saved_prot_own γ Ψ -∗ ▷ (Φ x y ≡ Ψ x y).
  Proof. iIntros "HΦ HΨ". iPoseProof (saved_prot_valid with "HΦ HΨ") as "$". Qed.

End saved_prot.
