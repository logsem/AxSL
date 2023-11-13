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

(* This file contains the definition of weakest preconditions of the low-level logic *)
From iris.proofmode Require Import base tactics classes.
From iris.bi.lib Require Import fixpoint.
From iris.prelude Require Import options.

From iris_named_props Require Export named_props.

From self.low Require Export iris interp_mod.
Import uPred.

(* to facilitate TC search *)
Class Terminated (s : LThreadState.t) :=
  _terminated : LThreadState.is_terminated s = true.

Import LThreadState.

Definition post_lifting `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} Φ tid :=
  (λ (s : LThreadState.t),  ∀ (na : mea Σ),
     annot_interp na ==∗
     (annot_interp na ∗
     (([∗ map] e ↦ R ∈ na, if bool_decide (Graph.is_local_node_of tid e) then R
                                  else True%I) -∗ ▷ |==> Φ s)))%I.

Lemma post_lifting_interp_mod `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} Φ tid s :
  |=i=> post_lifting Φ tid s -∗ post_lifting Φ tid s.
Proof.
  iIntros "H".
  rewrite /post_lifting.
  iIntros (?) "Hna".
  rewrite interp_mod_eq /interp_mod_def.
  iMod ("H" with "Hna") as "[H Hna]".
  by iMod ("H" with "Hna") as "[$ $]".
Qed.

Definition sswp_def `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} `{!Protocol} (tid: Tid) :
  LThreadState.t -d> (LThreadState.t -d> iPropO Σ) -d> iPropO Σ :=
  (λ s Φ,
    if LThreadState.is_terminated s then |=i=> Φ s
    else
    (
      ∀ (gs : GlobalState.t) pg s' ls,
        let gr := gs.(GlobalState.gs_graph) in
        (* the graph is forall quantified and interpreted,
          it combining with resources gives us partial facts about the graph *)
        "%Hgraph_co" ∷ ⌜AAConsistent.t gr⌝ ∗
        "%Hgraph_wf" ∷ ⌜AACandExec.NMSWF.wf gr⌝ ∗
        "#Hinterp_global" ∷ (□ gconst_interp gs) ∗
        "%Hstep" ∷ ⌜LThreadStep.t gs tid s s'⌝ ∗
        "%Hat_prog" ∷ ⌜LThreadState.at_progress s pg⌝ ∗
        "Hinterp_local" ∷ local_interp gs tid pg ls -∗
        (if (bool_decide (ThreadState.progress_is_valid gr tid pg)) then
           ∀ (na : mea Σ),
           "Hannot_at_prog" ∷ na_at_progress gr tid pg na ∗
           "Hinterp_annot" ∷ annot_interp na
           ==∗
           let e := (ThreadState.progress_to_node pg tid) in
           let s_lob := (Graph.lob_pred_of gr e) in
           let s_obs := (Graph.obs_pred_of gr e) in
           ∃ (R: iProp Σ) (na_used na_unused : mea Σ) (ls' : log_ts_t),
             (na_splitting_wf s_lob na na_used na_unused ∗
              flow_eq s_lob s_obs e na_used R) ∗
             annot_interp ({[e := R]} ∪ na_unused ∪ na) ∗
             (local_interp gs tid (LThreadState.get_progress s') ls') ∗
             Φ s'
         else |=i=>
             ((local_interp gs tid (LThreadState.get_progress s') ls) ∗
             Φ s')))
    )%I.

Definition sswp_aux : seal (@sswp_def). Proof. by eexists. Qed.
Definition sswp := sswp_aux.(unseal).
Arguments sswp {Σ _ _ _ _ _}.
Lemma sswp_eq `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} `{!Protocol} : sswp = @sswp_def Σ _ _ _ _ _.
Proof. rewrite -sswp_aux.(seal_eq) //. Qed.

Definition wp_pre `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} `{!Protocol} (tid : Tid)
    (wp : LThreadState.t -> (LThreadState.t -> iProp Σ) -> iProp Σ)
        : LThreadState.t -> (LThreadState.t -> iProp Σ) -> iProp Σ :=
  (λ s Φ,
    if LThreadState.is_terminated s then (post_lifting Φ tid) s
    else
    (
      ∀ (gs : GlobalState.t) pg s' ls,
        let gr := gs.(GlobalState.gs_graph) in
        (* the graph is forall quantified and interpreted,
          it combining with resources gives us partial facts about the graph *)
        "%Hgraph_co" ∷ ⌜AAConsistent.t gr⌝ ∗
        "%Hgraph_wf" ∷ ⌜AACandExec.NMSWF.wf gr⌝ ∗
        "#Hinterp_global" ∷ (□ gconst_interp gs) ∗
        "%Hstep" ∷ ⌜LThreadStep.t gs tid s s'⌝ ∗
        "%Hat_prog" ∷ ⌜LThreadState.at_progress s pg⌝ ∗
        "Hinterp_local" ∷ local_interp gs tid pg ls -∗
        (if (bool_decide (ThreadState.progress_is_valid gr tid pg)) then
           ∀ (na : mea Σ),
           "Hannot_at_prog" ∷ na_at_progress gr tid pg na ∗
           "Hinterp_annot" ∷ annot_interp na ==∗
           let e := (ThreadState.progress_to_node pg tid) in
           let s_lob := (Graph.lob_pred_of gr e) in
           let s_obs := (Graph.obs_pred_of gr e) in
           ∃ (R: iProp Σ) (na_used na_unused : mea Σ) (ls' : log_ts_t),
             (na_splitting_wf s_lob na na_used na_unused ∗
               flow_eq s_lob s_obs e na_used R) ∗
             annot_interp ({[e := R]} ∪ na_unused ∪ na) ∗
             (local_interp gs tid (LThreadState.get_progress s') ls') ∗
             wp s' Φ
         else |=i=>
             ((local_interp gs tid (LThreadState.get_progress s') ls) ∗
           wp s' Φ)))
    )%I.

Local Lemma wp_pre_mono `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} `{!Protocol} tid
    (wp1 wp2 : LThreadState.t -> (LThreadState.t -> iProp Σ) -> iProp Σ) :
  ⊢ (□ ∀ s Φ, wp1 s Φ -∗ wp2 s Φ) →
    ∀ s Φ, wp_pre tid wp1 s Φ -∗ wp_pre tid wp2 s Φ.
Proof.
  iIntros "#H"; iIntros (s Φ) "Hwp". rewrite /wp_pre.
  destruct (LThreadState.is_terminated s); first done.
  iIntros (????) "Hs". iDestruct ("Hwp" with "Hs") as "Hwp".
  case_bool_decide.
  - iIntros (?) "Hs'". iDestruct ("Hwp" with "Hs'") as ">(%&%&%&%&(?&HFE)&?&?&Hwp)";iModIntro.
    iExists _,_,_,_. iFrame "HFE". iFrame. by iApply "H".
  - iDestruct "Hwp" as ">[? ?]".
    iModIntro. iFrame. by iApply "H".
Qed.

Local Definition wp_pre' `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} `{!Protocol} tid :
  (prodO (leibnizO LThreadState.t) (LThreadState.t -d> iPropO Σ) → iPropO Σ) -> (prodO (leibnizO LThreadState.t) (LThreadState.t -d> iPropO Σ) → iPropO Σ) :=
  uncurry ∘ wp_pre tid ∘ curry.

#[local] Instance wp_pre_mono' `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} `{!Protocol} tid: BiMonoPred (wp_pre' tid).
Proof.
  constructor.
  - iIntros (wp1 wp2 ??) "#H". iIntros ([s Φ]); iRevert (s Φ).
    iApply wp_pre_mono. iIntros "!>" (??).
    iApply ("H" $! (s, Φ)).
  - intros wp Hwp n [s1 Φ1] [s2 Φ2] [?%leibniz_equiv ?]. simplify_eq/=.
    rewrite /curry /wp_pre /post_lifting. do 14 (f_equiv || done).
    2:{ rewrite /Datatypes.curry. by apply pair_ne. }
    do 13 (f_equiv || done). rewrite /Datatypes.curry. by apply pair_ne.
Qed.

Local Definition wp_def `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} `{!Protocol} (tid: Tid) : LThreadState.t -> (LThreadState.t -> iProp Σ) -> iProp
Σ:=
  λ s Φ, bi_least_fixpoint (wp_pre' tid) (s,Φ).

Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp := wp_aux.(unseal).

Arguments wp {Σ _ _ _ _ _}.
Lemma wp_eq `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} `{!Protocol} : wp = @wp_def Σ _ _ _ _ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

(** Notations *)
Notation "'SSWP' m @ id {{ Φ } }" := (sswp id m Φ)
  (at level 20, m, Φ at level 200, only parsing) : bi_scope.

Notation "'WP' m @ id {{ Φ } }" := (wp id m Φ)
  (at level 20, m, Φ at level 200, only parsing) : bi_scope.

Notation "'SSWP' m @ id {{ v , Q } }" := (sswp id m (λ v, Q))
  (at level 20, m, Q at level 200,
   format "'[' 'SSWP'  m  '/' '[       ' @  id  {{  v ,  Q  } } ']' ']'") : bi_scope.

Notation "'WP' m @ id {{ v , Q } }" := (wp id m (λ v, Q))
  (at level 20, m, Q at level 200,
   format "'[' 'WP'  m  '/' '[       ' @  id   {{  v ,  Q  } } ']' ']'") : bi_scope.

Section wp.
  Context `{CMRA Σ}.
  Context `{!invGS_gen HasNoLc Σ}.
  Context `{!irisG}.
  Context `{!irisGL}.
  Context `{!Protocol}.
  Implicit Types Φ : LThreadState.t → iProp Σ.
  Implicit Types s : LThreadState.t.
  Implicit Types id : Tid.
  Import LThreadState.

  Lemma wp_unfold id s Φ :
    WP s @ id {{ Φ }} ⊣⊢ wp_pre id (wp id) s Φ.
  Proof. rewrite wp_eq /wp_def least_fixpoint_unfold //. Qed.

  Lemma wp_ind tid Ψ :
    (∀ n s, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ s)) →
    □ (∀ s Φ, wp_pre tid (λ s Φ, Ψ s Φ ∧ WP s @ tid {{ Φ }}) s Φ -∗ Ψ s Φ) -∗
    ∀ s Φ, WP s @ tid {{ Φ }} -∗ Ψ s Φ.
  Proof.
    iIntros (HΨ). iIntros "#IH" (s Φ) "H". rewrite wp_eq.
    set (Ψ' := uncurry Ψ :
           prodO (leibnizO LThreadState.t) (LThreadState.t -d> iPropO Σ) → iPropO Σ).
    assert (NonExpansive Ψ').
    { intros n [s1 Φ1] [s2 Φ2]
        [?%leibniz_equiv ?]; simplify_eq/=. by apply HΨ. }
    iApply (least_fixpoint_ind _ Ψ' with "[] H").
    iIntros "!>" ([? ?]) "H". by iApply "IH".
  Qed.

  Lemma wp_sswp id s Φ :
    WP s @ id {{ Φ }} ⊣⊢ SSWP s @ id {{s', WP s' @ id {{ Φ }} }}.
  Proof.
    rewrite wp_unfold sswp_eq /wp_pre /sswp_def.
    destruct (is_terminated s) eqn:Hm;
    repeat setoid_rewrite (wp_unfold id s);rewrite /wp_pre ?Hm //=.
    iSplitL.
    - by iIntros "? !>".
    - iApply post_lifting_interp_mod.
  Qed.

  #[global] Instance sswp_ne id s n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (sswp id s).
  Proof. rewrite sswp_eq /sswp_def; intros ?? Heq; repeat f_equiv. Qed.

  #[global] Instance wp_ne id s n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (wp id s).
  Proof.
    intros Φ1 Φ2 HΦ. rewrite !wp_eq.
    by apply (least_fixpoint_ne _), pair_ne, HΦ.
  Qed.

  #[global] Instance sswp_proper id  s :
    Proper (pointwise_relation _ (≡) ==> (≡)) (sswp id s).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply sswp_ne=>v; apply equiv_dist.
  Qed.

  #[global] Instance wp_proper id  s :
    Proper (pointwise_relation _ (≡) ==> (≡)) (wp id s).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
  Qed.

  (* #[global] Instance sswp_contractive id  s n : *)
  (*   TCEq (is_terminated s) false → *)
  (*   Proper (pointwise_relation _ (dist_later n) ==> dist n) (sswp id s). *)
  (* Proof. *)
  (*   intros He Φ Ψ HΦ. rewrite !sswp_eq /sswp_def He. *)
  (*   repeat apply bi.forall_ne =>?. *)
  (*   by repeat (f_contractive || f_equiv). *)
  (* Qed. *)

  (* #[global] Instance wp_contractive id  s n : *)
  (*   TCEq (is_terminated s) false → *)
  (*   Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp id  s). *)
  (* Proof. *)
  (*   intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He. *)
  (*   repeat apply bi.forall_ne =>?. *)
  (*   by repeat (f_contractive || f_equiv). *)
  (* Qed. *)

  Lemma sswp_terminated' id Φ s :
    is_terminated s = true → Φ s ⊢ SSWP s @ id {{ Φ }}.
  Proof. iIntros (Hs) "HΦ". rewrite sswp_eq /sswp_def Hs. by iFrame. Qed.
  Lemma sswp_terminated_inv' id  Φ s :
    is_terminated s = true → SSWP s @ id {{ Φ }} -∗ |=i=> Φ s.
  Proof. intros Hs; rewrite sswp_eq /sswp_def Hs //. by iIntros "$". Qed.

  Lemma wp_terminated' id Φ s :
    is_terminated s = true → post_lifting Φ id s ⊢ WP s @ id {{ Φ }}.
  Proof. iIntros (Hs) "HΦ". rewrite wp_unfold /wp_pre Hs. auto. Qed.
  Lemma wp_terminated_inv' id  Φ s :
    is_terminated s = true → WP s @ id {{ Φ }} -∗ post_lifting Φ id s.
  Proof. intros Hs; rewrite wp_unfold /wp_pre Hs. iIntros "$". Qed.

  Lemma sswp_strong_mono id s Φ Ψ :
    SSWP s @ id {{ Φ }} -∗ (∀ k, Φ k -∗ Ψ k) -∗ SSWP s @ id {{ Ψ }}.
  Proof.
    iIntros "H HΦ".
    rewrite sswp_eq /sswp_def.
    destruct (is_terminated s) eqn:?.
    { iMod "H". iModIntro. by iApply ("HΦ" with "[-]"). }
    iIntros (????) "Hs". iDestruct ("H" with "Hs") as "Hwp".
    case_bool_decide.
    - iIntros (?) "Hs'". iDestruct ("Hwp" with "Hs'") as ">(%&%&%&%&(?&FE)&?&?&Hwp)".
      iExists _,_,_,_. iFrame "FE". iFrame. by iApply "HΦ".
    - iDestruct "Hwp" as ">[? Hwp]". iModIntro. iFrame. by iApply "HΦ".
  Qed.

  Lemma sswp_strong_mono' id s Φ Ψ :
    SSWP s @ id {{ Φ }} -∗ (∀ k, Φ k -∗ |=i=> Ψ k) -∗ SSWP s @ id {{ Ψ }}.
  Proof.
    iIntros "H HΦ".
    rewrite sswp_eq /sswp_def.
    destruct (is_terminated s) eqn:?.
    { iMod "H". by iApply ("HΦ" with "[-]"). }
    iIntros (????) "Hs". iDestruct ("H" with "Hs") as "Hwp".
    case_bool_decide.
    - iIntros (?) "[Hs' Hannot]".
      rewrite interp_mod_eq /interp_mod_def.
      iDestruct ("Hwp" with "[$Hs' $Hannot]") as ">(%&%&%&%&(?&FE)&Hannot&Hwp)".
      iDestruct "Hwp" as "[Hwp H]". iSpecialize ("HΦ" with "H"). iDestruct ("HΦ" with "Hannot") as ">[? ?]".
      iExists _,_,_,_. iFrame "FE". by iFrame.
    - iDestruct "Hwp" as ">[? Hwp]". iMod ("HΦ" with "Hwp"). iModIntro. iFrame.
  Qed.

  Lemma post_lifting_strong_mono id s Φ Ψ :
    post_lifting Φ id s -∗ (∀ k : t, Φ k ==∗ Ψ k) -∗ post_lifting Ψ id s.
  Proof.
    iIntros "H HΦ". rewrite /post_lifting. iIntros (?) "Hinterp_annot".
    iDestruct ("H" with "Hinterp_annot") as ">[$ H]".
    iModIntro. iIntros "P". iSpecialize ("H" with "P"). iNext. iMod "H".
    by iApply "HΦ".
  Qed.

  Lemma wp_strong_mono id s Φ Ψ :
    WP s @ id {{ Φ }} -∗ (∀ k, Φ k ==∗ Ψ k) -∗ WP s @ id {{ Ψ }}.
  Proof.
    iIntros "H HΦ". iRevert (Ψ) "HΦ"; iRevert (s Φ) "H".
    iApply wp_ind; first solve_proper.
    iIntros "!>" (s Φ) "IH"; iIntros (Ψ) "HΦ".
    rewrite !wp_unfold /wp_pre.
    destruct (is_terminated s) eqn:?.
    { by iApply (post_lifting_strong_mono with "IH HΦ"). }
    iIntros (????) "Hs". iDestruct ("IH" with "Hs") as "Hwp".
    case_bool_decide.
    - iIntros (?) "Hs'". iDestruct ("Hwp" with "Hs'") as ">(%&%&%&%&(?&FE)&?&?&Hwp)".
      iExists _,_,_,_. iFrame "FE". iFrame. iApply ("Hwp" with "HΦ").
    - iMod "Hwp" as "[? Hwp]". iModIntro;iFrame. iApply ("Hwp" with "HΦ").
  Qed.

  Lemma bupd_sswp id s Φ :
    (|==> SSWP s @ id {{ Φ }}) ⊢ SSWP s @ id {{ Φ }}.
  Proof.
    rewrite sswp_eq /sswp_def. iIntros "H".
    destruct (is_terminated s) eqn:?.
    { by iApply interp_mod_bupd. }
    iIntros (????) "Hs". iDestruct ("H" with "Hs") as "Hwp".
    case_bool_decide.
    - iIntros (?) "Hs'". iDestruct ("Hwp" with "Hs'") as ">>(%&%&%&%&(?&FE)&?&Hwp)".
      iExists _,_,_,_. iFrame "FE". by iFrame.
    - iMod "Hwp" as ">[? ?]". iModIntro. iFrame.
  Qed.

  Lemma iupd_sswp id s Φ :
    (|=i=> SSWP s @ id {{ Φ }}) ⊢ SSWP s @ id {{ Φ }}.
  Proof.
    rewrite sswp_eq /sswp_def. iIntros "H".
    destruct (is_terminated s) eqn:?.
    { iMod "H";done. }
    iIntros (????) "Hs". iDestruct ("H" with "Hs") as "Hwp".
    case_bool_decide.
    - iIntros (?) "[Hs' Hannot]".
      rewrite interp_mod_eq /interp_mod_def.
      iDestruct ("Hwp" with "Hannot") as ">[Hwp Hannot]".
      iDestruct ("Hwp" with "[$Hs' $Hannot]") as ">(%&%&%&%&(?&FE)&?&Hwp)".
      iModIntro. iExists _,_,_,_. iFrame "FE". by iFrame.
    - iMod "Hwp" as ">[? ?]". iModIntro. iFrame.
  Qed.

  Lemma sswp_bupd id s Φ :
    SSWP s @ id {{ k, |==> Φ k }} ⊢ SSWP s @ id {{ Φ }}.
  Proof.
    rewrite sswp_eq /sswp_def. iIntros "H".
    destruct (is_terminated s) eqn:?.
    { rewrite interp_mod_eq /interp_mod_def.
      iIntros (?) "Hannot". iDestruct ("H" with "Hannot") as ">[>$ $]". done. }
    iIntros (????) "Hs". iDestruct ("H" with "Hs") as "Hwp".
    case_bool_decide.
    - iIntros (?) "Hs'". iDestruct ("Hwp" with "Hs'") as ">(%&%&%&%&(?&FE)&?&?&Hwp)".
      iExists _,_,_,_. iFrame "FE". by iFrame.
    - iMod "Hwp" as "[? Hwp]". iApply interp_mod_bupd. iMod "Hwp".
      iModIntro. iModIntro. iFrame.
  Qed.

  Lemma sswp_iupd id s Φ :
    SSWP s @ id {{ k, |=i=> Φ k }} ⊢ SSWP s @ id {{ Φ }}.
  Proof.
    rewrite sswp_eq /sswp_def. iIntros "H".
    destruct (is_terminated s) eqn:?.
    { iMod "H";done. }
    iIntros (????) "Hs". iDestruct ("H" with "Hs") as "Hwp".
    case_bool_decide.
    - iIntros (?) "[Hs' Hannot]".
      rewrite interp_mod_eq /interp_mod_def.
      iDestruct ("Hwp" with "[$Hs' $Hannot]") as ">(%&%&%&%&(?&FE)&Hannot&Hwp)".
      iDestruct "Hwp" as "[? Hwp]".
      iDestruct ("Hwp" with "Hannot") as ">[Hwp Hannot]".
      iExists _,_,_,_. iFrame "FE". by iFrame.
    - iMod "Hwp" as "[? Hwp]". iMod "Hwp". iModIntro. iFrame.
  Qed.

  Lemma bupd_wp id s Φ :
    (|==> WP s @ id {{ Φ }}) ⊢ WP s @ id {{ Φ }}.
  Proof.
    rewrite wp_unfold /wp_pre. iIntros "H". destruct (is_terminated s) eqn:?.
    { iApply post_lifting_interp_mod. iApply interp_mod_bupd. iMod "H". iModIntro. iModIntro. done. }
    iIntros (????) "Hs". iDestruct ("H" with "Hs") as "Hwp".
    case_bool_decide.
    - iIntros (?) "Hs'". iDestruct ("Hwp" with "Hs'") as ">>(%&%&%&%&(?&FE)&?&?&Hwp)".
      iExists _,_,_,_. iFrame "FE". by iFrame.
    - iMod "Hwp" as ">[? Hwp]". iModIntro;iFrame.
  Qed.

  Lemma iupd_wp id s Φ :
    (|=i=> WP s @ id {{ Φ }}) ⊢ WP s @ id {{ Φ }}.
  Proof.
    rewrite wp_unfold /wp_pre. iIntros "H". destruct (is_terminated s) eqn:?.
    { iApply post_lifting_interp_mod. done. }
    iIntros (????) "Hs". iDestruct ("H" with "Hs") as "Hwp".
    case_bool_decide.
    - iIntros (?) "[Hs' Hannot]".
      rewrite interp_mod_eq /interp_mod_def.
      iDestruct ("Hwp" with "Hannot") as ">[Hwp Hannot]".
      iDestruct ("Hwp" with "[$Hs' $Hannot]") as ">(%&%&%&%&(?&FE)&?&Hwp)".
      iModIntro. iExists _,_,_,_. iFrame "FE". by iFrame.
    - iMod "Hwp" as ">[? Hwp]". iModIntro;iFrame.
  Qed.

  Lemma wp_bupd id s Φ :
    WP s @ id {{ k, |==> Φ k }} ⊢ WP s @ id {{ Φ }}.
  Proof. iIntros "H". iApply (wp_strong_mono id with "H"); auto. Qed.

  (* don't need this lemma since we removed masks for now *)
  (* Lemma sswp_fupd_around id E1 E2 s Φ : *)
  (*   (|={E1,E2}=> SSWP s @ id; E2 {{ k, |={E2,E1}=> Φ k }}) ⊢ SSWP s @ id; E1 {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "H". *)
  (*   rewrite sswp_eq /sswp_def. *)
  (*   destruct (is_terminated s). *)
  (*   { by iDestruct "H" as ">>> $". } *)
  (*   iIntros (gs α β) "H'". iMod "H". *)
  (*   iMod ("H" with "H'") as "H". *)
  (*   iModIntro. *)
  (*   iIntros (s' Hstep). *)
  (*   iMod ("H" with "[//]") as "H". *)
  (*   iModIntro. iNext. *)
  (*   iMod "H" as "[$ >$]"; done. *)
  (* Qed. *)

  Lemma sswp_step_bupd id s P Φ :
    (|==> P) -∗
    SSWP s @ id {{ k, P ==∗ Φ k }} -∗
                 SSWP s @ id {{ Φ }}.
  Proof.
    rewrite sswp_eq /sswp_def. iIntros "HP H".
    destruct (is_terminated s).
    { iMod "H". iApply interp_mod_bupd'. iMod "HP". by iApply "H". }
    iIntros (????) "Hs". iDestruct ("H" with "Hs") as "Hwp".
    case_bool_decide.
    - iIntros (?) "Hs'". iDestruct ("Hwp" with "Hs'") as ">(%&%&%&%&(?&FE)&?&?&Hwp)".
      iExists _,_,_,_. iFrame "FE". iFrame.
      iMod ("Hwp" with "HP") as "$".
    - iMod "Hwp" as "[? Hwp]". iApply interp_mod_bupd'.
      iMod "HP". iMod ("Hwp" with "HP") as "$". done.
  Qed.

  Lemma sswp_step_iupd id s P Φ :
    (|=i=> P) -∗
    SSWP s @ id {{ k, P -∗ |=i=> Φ k }} -∗
                 SSWP s @ id {{ Φ }}.
  Proof.
    rewrite sswp_eq /sswp_def. iIntros "HP H".
    destruct (is_terminated s).
    { iMod "H". iMod "HP". by iApply "H". }
    iIntros (????) "Hs". iDestruct ("H" with "Hs") as "Hwp".
    case_bool_decide.
    - iIntros (?) "[Hs' Hannot]".
      rewrite interp_mod_eq /interp_mod_def.
      iDestruct ("HP" with "Hannot") as ">[HP Hannot]".
      iDestruct ("Hwp" with "[$Hs' $Hannot]") as ">(%&%&%&%&(?&FE)&Hannot&Hwp)".
      iDestruct "Hwp" as "[? Hwp]". iDestruct ("Hwp" with "HP") as "Hwp".
      iDestruct ("Hwp" with "Hannot") as ">[Hwp ?]".
      iExists _,_,_,_. iFrame "FE". by iFrame.
    - iMod "Hwp" as "[? Hwp]".
      iMod "HP".  iMod ("Hwp" with "HP") as "?".
      iModIntro;iFrame.
  Qed.

  Lemma wp_step_bupd id s P Φ :
    (|==> P) -∗
    WP s @ id {{ k, P ==∗ Φ k }} -∗
               WP s @ id {{ Φ }}.
  Proof.
    rewrite !wp_unfold /wp_pre. iIntros "HP H".
    destruct (is_terminated s).
    { iApply (post_lifting_strong_mono with "H"). iIntros (?) "H". iMod "HP". by iApply "H". }
    iIntros (????) "Hs". iDestruct ("H" with "Hs") as "Hwp".
    case_bool_decide.
    - iIntros (?) "Hs'". iDestruct ("Hwp" with "Hs'") as ">(%&%&%&%&(?&FE)&?&?&Hwp)".
      iExists _,_,_,_. iFrame "FE". iFrame.
      iMod "HP". iModIntro. iApply (wp_strong_mono with "Hwp").
      iIntros (k) "H"; iApply "H"; done.
    - iMod "HP". iMod "Hwp" as "[? Hwp]".
      iApply interp_mod_bupd'. iFrame.
      iApply (wp_strong_mono with "Hwp").
      iModIntro. iIntros (k) "H"; iApply "H"; done.
  Qed.

  Lemma wp_step_iupd id s P Φ :
    (|=i=> P) -∗
    WP s @ id {{ k, P -∗ |==> Φ k }} -∗
               WP s @ id {{ Φ }}.
  Proof.
    rewrite !wp_unfold /wp_pre. iIntros "HP H".
    destruct (is_terminated s).
    { iApply post_lifting_interp_mod. iMod "HP". iModIntro. iApply (post_lifting_strong_mono with "H"). iIntros (?) "H". by iApply "H". }
    iIntros (????) "Hs". iDestruct ("H" with "Hs") as "Hwp".
    case_bool_decide.
    - iIntros (?) "Hs'". iDestruct ("Hwp" with "Hs'") as ">(%&%&%&%&(?&FE)&Hannot&?&Hwp)".
      iExists _,_,_,_. iFrame "FE".
      rewrite interp_mod_eq /interp_mod_def.
      iDestruct ("HP" with "Hannot") as ">[HP Hannot]".
      iFrame. iApply (wp_strong_mono with "Hwp").
      iModIntro. iIntros (k) "H"; iApply "H"; done.
    - iMod "HP". iMod "Hwp" as "[? Hwp]".
      iApply interp_mod_bupd'. iFrame.
      iApply (wp_strong_mono with "Hwp").
      iModIntro. iIntros (k) "H"; iApply "H"; done.
  Qed.

  (** * Derived rules *)
  Lemma sswp_mono id s Φ Ψ :
    (∀ k, Φ k ⊢ Ψ k) → SSWP s @ id {{ Φ }} ⊢ SSWP s @ id {{ Ψ }}.
  Proof.
    iIntros (HΦ) "H"; iApply (sswp_strong_mono with "H"); auto.
    iIntros (v) "?". by iApply HΦ.
  Qed.

  Lemma wp_mono id s Φ Ψ :
    (∀ k, Φ k ⊢ Ψ k) → WP s @ id {{ Φ }} ⊢ WP s @ id {{ Ψ }}.
  Proof.
    iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
    iIntros (v) "?". by iApply HΦ.
  Qed.

  (* Lemma sswp_mask_mono id E1 E2 s Φ : *)
  (*   E1 ⊆ E2 → SSWP s @ id; E1 {{ Φ }} ⊢ SSWP s @ id; E2 {{ Φ }}. *)
  (* Proof. iIntros (?) "H"; iApply (sswp_strong_mono with "H"); auto. Qed. *)

  (* Lemma wp_mask_mono id E1 E2 s Φ : *)
  (*   E1 ⊆ E2 → WP s @ id; E1 {{ Φ }} ⊢ WP s @ id; E2 {{ Φ }}. *)
  (* Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed. *)

  Global Instance sswp_mono' id s :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (sswp id s).
  Proof. by intros Φ Φ' ?; apply sswp_mono. Qed.

  Global Instance wp_mono' id s :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp id s).
  Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

  Global Instance sswp_flip_mono' id s :
    Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (sswp id s).
  Proof. by intros Φ Φ' ?; apply sswp_mono. Qed.

  Global Instance wp_flip_mono' id s :
    Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp id s).
  Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

  Lemma sswp_terminated id Φ s :
    Terminated s → Φ s ⊢ SSWP s @ id {{ Φ }}.
  Proof. apply sswp_terminated'. Qed.

  Lemma wp_terminated id Φ s :
    Terminated s -> (post_lifting Φ id) s ⊢ WP s @ id {{ Φ }}.
  Proof. apply wp_terminated'. Qed.

  Lemma wp_terminated_bupd' id Φ s :
    Terminated s → (post_lifting Φ id) s ⊢ WP s @ id {{ Φ }}.
  Proof.
    intros; rewrite -wp_bupd -wp_terminated' //.
    iIntros "?". iApply (post_lifting_strong_mono with "[-]");auto.
  Qed.

  (* Lemma sswp_terminated'' id Φ s `{!Terminated s} : *)
  (*   Φ s ⊢ SSWP s @ id {{ Φ }}. *)
  (* Proof. intros; rewrite -sswp_bupd -sswp_terminated //. Qed. *)

  (* Lemma wp_terminated'' id Φ s `{!Terminated s} : *)
  (*   ((post_lifting Φ id) s) ⊢ WP s @ id {{ Φ }}. *)
  (* Proof. *)
  (*   intros; rewrite -wp_bupd -wp_terminated //. *)
  (*   iIntros "?". iApply (post_lifting_strong_mono with "[-]");auto. *)
  (* Qed. *)

  Lemma sswp_terminated_inv id Φ s :
    Terminated s → SSWP s @ id {{ Φ }} -∗ |=i=> Φ s.
  Proof. by apply sswp_terminated_inv'. Qed.

  Lemma wp_terminated_inv id Φ s :
    Terminated s → WP s @ id {{ Φ }} -∗ (post_lifting Φ id) s.
  Proof. apply wp_terminated_inv'. Qed.

  Lemma sswp_frame_l id s Φ R :
    R ∗ SSWP s @ id {{ Φ }} ⊢ SSWP s @ id {{ k, R ∗ Φ k }}.
  Proof. iIntros "[? H]". iApply (sswp_strong_mono with "H"); auto with iFrame. Qed.

  Lemma wp_frame_l id s Φ R :
    R ∗ WP s @ id {{ Φ }} ⊢ WP s @ id {{ k, R ∗ Φ k }}.
  Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

  Lemma sswp_frame_r id s Φ R :
    SSWP s @ id {{ Φ }} ∗ R ⊢ SSWP s @ id {{ k, Φ k ∗ R }}.
  Proof. iIntros "[H ?]". iApply (sswp_strong_mono with "H"); auto with iFrame. Qed.

  Lemma wp_frame_r id s Φ R :
    WP s @ id {{ Φ }} ∗ R ⊢ WP s @ id {{ k, Φ k ∗ R }}.
  Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

  Lemma sswp_frame_step_l id s Φ R :
    (|==> R) ∗ SSWP s @ id {{ Φ }} ⊢ SSWP s @ id {{ k, R ∗ Φ k }}.
  Proof.
    iIntros "[Hu Hwp]". iApply (sswp_step_bupd with "Hu"); try done.
    iApply (sswp_mono with "Hwp"). by iIntros (?) "$$".
  Qed.

  Lemma sswp_frame_step_l'' id s Φ R :
    (|=i=> R) ∗ SSWP s @ id {{ Φ }} ⊢ SSWP s @ id {{ k, R ∗ Φ k }}.
  Proof.
    iIntros "[Hu Hwp]". iApply (sswp_step_iupd with "Hu"); try done.
    iApply (sswp_mono with "Hwp"). iIntros (?) "??". iModIntro. iFrame.
  Qed.

  Lemma wp_frame_step_l id s Φ R :
    (|==> R) ∗ WP s @ id {{ Φ }} ⊢ WP s @ id {{ k, R ∗ Φ k }}.
  Proof.
    iIntros "[Hu Hwp]". iApply (wp_step_bupd with "Hu"); try done.
    iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
  Qed.

  Lemma wp_frame_step_l'' id s Φ R :
    (|=i=> R) ∗ WP s @ id {{ Φ }} ⊢ WP s @ id {{ k, R ∗ Φ k }}.
  Proof.
    iIntros "[Hu Hwp]". iApply (wp_step_iupd with "Hu"); try done.
    iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
  Qed.

  Lemma sswp_frame_step_r id  s Φ R :
    SSWP s @ id {{ Φ }} ∗ (|==> R) ⊢ SSWP s @ id {{ k, Φ k ∗ R }}.
  Proof.
    rewrite [(SSWP _ @ _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
    apply sswp_frame_step_l.
  Qed.

  Lemma sswp_frame_step_r'' id  s Φ R :
    SSWP s @ id {{ Φ }} ∗ (|=i=> R) ⊢ SSWP s @ id {{ k, Φ k ∗ R }}.
  Proof.
    rewrite [(SSWP _ @ _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
    apply sswp_frame_step_l''.
  Qed.

  Lemma wp_frame_step_r id s Φ R :
    WP s @ id {{ Φ }} ∗ (|==> R) ⊢ WP s @ id {{ k, Φ k ∗ R }}.
  Proof.
    rewrite [(WP _ @ _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
    apply wp_frame_step_l.
  Qed.

  Lemma wp_frame_step_r'' id s Φ R :
    WP s @ id {{ Φ }} ∗ (|=i=> R) ⊢ WP s @ id {{ k, Φ k ∗ R }}.
  Proof.
    rewrite [(WP _ @ _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
    apply wp_frame_step_l''.
  Qed.

  Lemma sswp_frame_step_l' id s Φ R :
    R ∗ SSWP s @ id {{ Φ }} ⊢ SSWP s @ id {{ k, R ∗ Φ k }}.
  Proof. iIntros "[??]". iApply (sswp_frame_step_l id); try iFrame; eauto. Qed.

  Lemma wp_frame_step_l' id s Φ R :
    R ∗ WP s @ id {{ Φ }} ⊢ WP s @ id {{ k, R ∗ Φ k }}.
  Proof. iIntros "[??]". iApply (wp_frame_step_l id); try iFrame; eauto. Qed.

  Lemma sswp_frame_step_r' id s Φ R :
    SSWP s @ id {{ Φ }} ∗ R ⊢ SSWP s @ id {{ k, Φ k ∗ R }}.
  Proof. iIntros "[??]". iApply (sswp_frame_step_r id); try iFrame; eauto. Qed.

  Lemma wp_frame_step_r' id s Φ R :
    WP s @ id {{ Φ }} ∗ R ⊢ WP s @ id {{ k, Φ k ∗ R }}.
  Proof. iIntros "[??]". iApply (wp_frame_step_r id); try iFrame; eauto. Qed.

  Lemma sswp_wand id s Φ Ψ :
    SSWP s @ id {{ Φ }} -∗ (∀ k, Φ k -∗ Ψ k) -∗ SSWP s @ id {{ Ψ }}.
  Proof.
    iIntros "Hwp H". iApply (sswp_strong_mono with "Hwp"); auto.
  Qed.

  Lemma wp_wand id s Φ Ψ :
    WP s @ id {{ Φ }} -∗ (∀ k, Φ k -∗ Ψ k) -∗ WP s @ id {{ Ψ }}.
  Proof.
    iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
    iIntros (?) "?". by iApply "H".
  Qed.

  Lemma sswp_wand_l id s Φ Ψ :
    (∀ k, Φ k -∗ Ψ k) ∗ SSWP s @ id {{ Φ }} ⊢ SSWP s @ id {{ Ψ }}.
  Proof. iIntros "[H Hwp]". iApply (sswp_wand with "Hwp H"). Qed.

  Lemma wp_wand_l id s Φ Ψ :
    (∀ v, Φ v -∗ Ψ v) ∗ WP s @ id {{ Φ }} ⊢ WP s @ id {{ Ψ }}.
  Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.

  Lemma sswp_wand_r id s Φ Ψ :
    SSWP s @ id {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ SSWP s @ id {{ Ψ }}.
  Proof. iIntros "[Hwp H]". iApply (sswp_wand with "Hwp H"). Qed.

  Lemma wp_wand_r id s Φ Ψ :
    WP s @ id {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP s @ id {{ Ψ }}.
  Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.

  Lemma sswp_frame_wand_l id s Q Φ :
    Q ∗ SSWP s @ id {{ v, Q -∗ Φ v }} -∗ SSWP s @ id {{ Φ }}.
  Proof.
    iIntros "[HQ HWP]". iApply (sswp_wand with "HWP").
    iIntros (v) "HΦ". by iApply "HΦ".
  Qed.

  Lemma wp_frame_wand_l id s Q Φ :
    Q ∗ WP s @ id {{ v, Q -∗ Φ v }} -∗ WP s @ id {{ Φ }}.
  Proof.
    iIntros "[HQ HWP]". iApply (wp_wand with "HWP").
    iIntros (v) "HΦ". by iApply "HΦ".
  Qed.

End wp.

Section proofmode_classes.
  Context `{CMRA Σ}.
  Context `{!invGS_gen HasNoLc Σ}.
  Context `{!irisG}.
  Context `{!irisGL}.
  Context `{!Protocol}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : LThreadState.t → iProp Σ.
  (* Implicit Types E : coPset. *)
  Implicit Types id : Tid.

  #[global] Instance frame_sswp p id s R Φ Ψ :
    (∀ k, Frame p R (Φ k) (Ψ k)) →
    Frame p R (SSWP s @ id {{ Φ }}) (SSWP s @ id {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite sswp_frame_l. apply sswp_mono, HR. Qed.

  #[global] Instance frame_wp p id s R Φ Ψ :
    (∀ k, Frame p R (Φ k) (Ψ k)) →
    Frame p R (WP s @ id {{ Φ }}) (WP s @ id {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  (* omit the following two for now *)
  (* #[global] Instance is_except_0_sswp id s Φ : IsExcept0 (SSWP s @ id {{ Φ }}). *)
  (* Proof. rewrite /IsExcept0. -bupd_sswp. -bupd_intro. apply _. Qed. *)

  (* #[global] Instance is_except_0_wp id E s Φ : IsExcept0 (WP s @ id; E {{ Φ }}). *)
  (* Proof. by rewrite /IsExcept0 -{2}bupd_wp -except_0_fupd -fupd_intro. Qed. *)

  #[global] Instance elim_modal_bupd_sswp p id s P Φ :
    ElimModal True p false (|==> P) P (SSWP s @ id {{ Φ }}) (SSWP s @ id {{ Φ }}).
  Proof.
    intros H'.
    rewrite /ElimModal bi.intuitionistically_if_elim
      bupd_frame_r bi.wand_elim_r bupd_sswp //.
  Qed.

  #[global] Instance elim_modal_iupd_sswp p id s P Φ :
    ElimModal True p false (|=i=> P) P (SSWP s @ id {{ Φ }}) (SSWP s @ id {{ Φ }}).
  Proof.
    intros H'.
    rewrite /ElimModal bi.intuitionistically_if_elim
      interp_mod_frame_r bi.wand_elim_r iupd_sswp //.
  Qed.

  #[global] Instance elim_modal_bupd_wp p id s P Φ :
    ElimModal True p false (|==> P) P (WP s @ id {{ Φ }}) (WP s @ id {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim
       bupd_frame_r bi.wand_elim_r bupd_wp //.
  Qed.

  #[global] Instance elim_modal_iupd_wp p id s P Φ :
    ElimModal True p false (|=i=> P) P (WP s @ id {{ Φ }}) (WP s @ id {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim
       interp_mod_frame_r bi.wand_elim_r iupd_wp //.
  Qed.

  (* #[global] Instance elim_modal_fupd_sswp p id E s P Φ : *)
  (*   ElimModal True p false (|={E}=> P) P (SSWP s @ id; E {{ Φ }}) (SSWP s @ id; E {{ Φ }}). *)
  (* Proof. *)
  (*   by rewrite /ElimModal bi.intuitionistically_if_elim *)
  (*     fupd_frame_r bi.wand_elim_r fupd_sswp. *)
  (* Qed. *)

  (* #[global] Instance elim_modal_fupd_wp p id E s P Φ : *)
  (*   ElimModal True p false (|={E}=> P) P (WP s @ id; E {{ Φ }}) (WP s @ id; E {{ Φ }}). *)
  (* Proof. *)
  (*   by rewrite /ElimModal bi.intuitionistically_if_elim *)
  (*     fupd_frame_r bi.wand_elim_r fupd_wp. *)
  (* Qed. *)

  (* #[global] Instance elim_modal_fupd_sswp_around p id E1 E2 s P Φ : *)
  (*   ElimModal True p false (|={E1,E2}=> P) P *)
  (*           (SSWP s @ id; E1 {{ Φ }}) (SSWP s @ id; E2 {{ v, |={E2,E1}=> Φ v }})%I. *)
  (* Proof. *)
  (*   intros. by rewrite /ElimModal bi.intuitionistically_if_elim *)
  (*     fupd_frame_r bi.wand_elim_r sswp_fupd_around. *)
  (* Qed. *)

  #[global] Instance add_modal_bupd_sswp id s P Φ :
    AddModal (|==> P) P (SSWP s @ id {{ Φ }}).
  Proof. rewrite /AddModal bupd_frame_r bi.wand_elim_r bupd_sswp //. Qed.

  #[global] Instance add_modal_iupd_sswp id s P Φ :
    AddModal (|=i=> P) P (SSWP s @ id {{ Φ }}).
  Proof. rewrite /AddModal interp_mod_frame_r bi.wand_elim_r iupd_sswp //. Qed.

  #[global] Instance add_modal_bupd_wp id s P Φ :
    AddModal (|==> P) P (WP s @ id {{ Φ }}).
  Proof. rewrite /AddModal bupd_frame_r bi.wand_elim_r bupd_wp //. Qed.

  #[global] Instance add_modal_iupd_wp id s P Φ :
    AddModal (|=i=> P) P (WP s @ id {{ Φ }}).
  Proof. rewrite /AddModal interp_mod_frame_r bi.wand_elim_r iupd_wp //. Qed.

  (* #[global] Instance elim_acc_sswp {X} id E1 E2 α β γ s Φ : *)
  (*   ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1) *)
  (*           α β γ (SSWP s @ id E1 {{ Φ }}) *)
  (*           (λ x, SSWP s @ id; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I. *)
  (* Proof. *)
  (*   intros _. *)
  (*   iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]". *)
  (*   iApply (sswp_wand with "(Hinner Hα)"). *)
  (*   iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose". *)
  (* Qed. *)

  (* #[global] Instance elim_acc_wp_nonatomic {X} id E α β γ s Φ : *)
  (*   ElimAcc (X:=X) True (fupd E E) (fupd E E) *)
  (*           α β γ (WP s @ id; E {{ Φ }}) *)
  (*           (λ x, WP s @ id; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I. *)
  (* Proof. *)
  (*   rewrite /ElimAcc. *)
  (*   iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]". *)
  (*   iApply wp_fupd. *)
  (*   iApply (wp_wand with "(Hinner Hα)"). *)
  (*   iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose". *)
  (* Qed. *)

End proofmode_classes.
