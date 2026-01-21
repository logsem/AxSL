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

(* This file contains the definition of weakest preconditions of the low-level logic *)
From iris.proofmode Require Import base tactics classes.
From iris.bi.lib Require Import fixpoint.
From iris.prelude Require Import options.

From iris_named_props Require Export named_props.

From self.low Require Export iris interp_mod annotations.

(* TODO remove dep on opsem *)
From self.lang Require Export opsem.
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

Definition flow_eq_dyn_def `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} (gr: Graph.t) (e: Eid) (flow_in: mea Σ) (R: iProp Σ) : iProp Σ :=
   ∀ (σ: ob_st) (s_ob: gset Eid),
  (* NOTE: can also use [ob_pred_of], but not necessary *)
  "Hob_pred_sub" ∷ ⌜(Graph.obs_pred_of gr e) ⊆ s_ob ⌝ -∗
  (* NOTE: this is not helpful for adequacy proof,
     but can help us not consider the opposite case when proving proof rules *)
  "Hob_pred_nin" ∷ ⌜e ∉ s_ob ⌝ -∗
  (* interpretation for [σ] *)
  "Hob_st" ∷ ob_st_interp gr σ s_ob -∗
  (* local ob resources, give more info about [σ] *)
  "R_lob_in" ∷ ([∗ map] R_in ∈ flow_in, R_in)
  (* some external resources hold at [σ] before [e] (at all ob-predecessors of [e]) *)
  ={⊤,∅}=∗ ▷ |={∅,⊤}=>
  (* may update [σ] to [σ'] *)
  ∃ (σ': ob_st),
  (* update interpretation accordingly *)
  "Hob_st" ∷ ob_st_interp gr σ' ({[ e ]} ∪ s_ob) ∗
  "R" ∷ R.

  (* We don't want to unfold [flow_eq_dyn] *)
  Local Definition flow_eq_dyn_aux : seal (@flow_eq_dyn_def). Proof. by eexists. Qed.
  Definition flow_eq_dyn := flow_eq_dyn_aux.(unseal).
  Definition flow_eq_dyn_unseal :
    @flow_eq_dyn = @flow_eq_dyn_def := flow_eq_dyn_aux.(seal_eq).
  Global Arguments flow_eq_dyn {Σ _ _ _}.

  Lemma flow_eq_dyn_proper `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} gr e flow_in R1 R2 :
    □ ▷(R1 -∗ R2) -∗
    flow_eq_dyn gr e flow_in R1 -∗
    flow_eq_dyn gr e flow_in R2.
  Proof.
    iIntros "#Himpl".
    rewrite flow_eq_dyn_unseal. unfold flow_eq_dyn_def.
    iIntros "H % %". repeat iNamed 1.
    iSpecialize ("H" with "Hob_pred_sub Hob_pred_nin Hob_st R_lob_in").
    iMod "H". iModIntro. iNext. iMod "H".
    iDestruct "H" as "(% &$&R)".
    iApply "Himpl". by iFrame.
  Qed.

(* The only diff between [sswp] and [wp] is that [sswp] is a one time thing - [\phi] holds after a step,
   while in [wp], we have to keep showing [wp] for the updated states, until termination when we show [\phi].
   The rest - what we do for each step we take is idential. See comments in the defintion of [wp] for explanations.
 *)
Definition sswp_def `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} (tid: Tid) :
  LThreadState.t -d> (LThreadState.t -d> iPropO Σ) -d> iPropO Σ :=
  (λ s Φ,
    if LThreadState.is_terminated s then |=i=> Φ s
    else
    (
      ∀ (gs : GlobalState.t) pg s' ls,
        let gr := gs.(GlobalState.gs_graph) in
        "%Hgraph_co" ∷ ⌜AAConsistent.t gr⌝ ∗
        "%Hgraph_wf" ∷ ⌜AACand.NMSWF.wf gr⌝ ∗
        "#Hinterp_global" ∷ (□ gconst_interp gs) ∗
        "%Hstep" ∷ ⌜LThreadStep.t gs tid s s'⌝ ∗
        "%Hat_prog" ∷ ⌜LThreadState.at_progress s pg⌝ ∗
        "Hinterp_local" ∷ local_interp gs tid pg ls -∗
        if (bool_decide (progress_is_valid gr tid pg)) then
          let e := (ThreadState.progress_to_node pg tid) in
           (* [e] is valid, we need to do things *)
           ∀ (na : mea Σ),
           "Hannot_at_prog" ∷ na_at_progress gr tid pg na ∗
           "Hinterp_annot" ∷ annot_interp na -∗
        |==> ▷ |==>
           let s_lob := (Graph.lob_pred_of gr e) in
           ∃ (R: iProp Σ) (na_used na_unused : mea Σ) (ls' : log_ts_t),
             na_splitting_wf s_lob na na_used na_unused ∗
             flow_eq_dyn gr e na_used R ∗
             annot_interp ({[e := R]} ∪ na_unused ∪ na) ∗
             (local_interp gs tid (LThreadState.get_progress s') ls') ∗
             Φ s'
        else
          (* [e] is not valie, we skip it *)
           ∀ (na : mea Σ),
           "Hinterp_annot" ∷ annot_interp na -∗
        |==> ▷ |==>
           annot_interp na ∗ local_interp gs tid (LThreadState.get_progress s') ls ∗  Φ s'
    ))%I.

Definition sswp_aux : seal (@sswp_def). Proof. by eexists. Qed.
Definition sswp := sswp_aux.(unseal).
Arguments sswp {Σ _ _ _ _}.
Lemma sswp_eq `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} : sswp = @sswp_def Σ _ _ _ _.
Proof. rewrite -sswp_aux.(seal_eq) //. Qed.

Definition wp_pre `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} (tid : Tid)
    (wp : LThreadState.t -d> (LThreadState.t -d> iProp Σ) -d> iProp Σ)
        : LThreadState.t -d> (LThreadState.t -d> iProp Σ) -d> iProp Σ :=
  (λ s Φ,
     (* In case that [s] is a terminated state, we show that [\phi] hold when all annotated resources holds.
      Note that it is a trick (done by [post_lifting]) aiming for recovering a post condition without annotations at all.
      The downside is that it breaks vertical compositionality *)
    if LThreadState.is_terminated s then (post_lifting Φ tid) s
    else
    (
      ∀ (gs : GlobalState.t) pg s' ls,
        let gr := gs.(GlobalState.gs_graph) in
        (* the graph [gr] is universally quantified and interpreted
           it combining with graph resources gives us partial facts about the graph *)
        (* [gr] is consistent wrt user Arm model *)
        "%Hgraph_co" ∷ ⌜AAConsistent.t gr⌝ ∗
        (* [gr] is well-formed *)
        "%Hgraph_wf" ∷ ⌜AACand.NMSWF.wf gr⌝ ∗
        (* logical interpretation of [gr] *)
        "#Hinterp_global" ∷ (□ gconst_interp gs) ∗
        (* taking an Opax step *)
        "%Hstep" ∷ ⌜LThreadStep.t gs tid s s'⌝ ∗
        (* [s] is in sync with the (thread local) checking progress [pg] *)
        "%Hat_prog" ∷ ⌜LThreadState.at_progress s pg⌝ ∗
        (* thread local logical interpretation for local logical (ghost) state [ls], wrt [gs], [tid], and [pg] *)
        "Hinterp_local" ∷ local_interp gs tid pg ls -∗
        (* if current [pg] of thread [tid] is valid - if we are checking a valid event of [gr] *)
        (
        if (bool_decide (progress_is_valid gr tid pg)) then
          let e := (progress_to_node pg tid) in
           (* CASE: [pg] is valid *)
           (* [na] is the node annotation ~= eid -> iProp *)
           ∀ (na : mea Σ),
           (* [na] is in sync with checking progress [pg] - making sure every checked event has an annotation *)
           "Hannot_at_prog" ∷ na_at_progress gr tid pg na ∗
           (* the logical interpretation of [na] *)
           "Hinterp_annot" ∷ annot_interp na -∗
        |==> ▷ |==>
           (* [s_lob] is the set of all local ob predecessors of [e] *)
           let s_lob := (Graph.lob_pred_of gr e) in
           (* [R] is the annotation for [e],
              [na_used] is what resources from [s_lob] to get [R],
              [na_unused] is the remaining resources on [s_lob],
              [ls'] is the new local logical state.
              these have to be given by the user to proceed *)
           ∃ (R: iProp Σ) (na_used na_unused : mea Σ) (ls' : log_ts_t),
             (* show [na_used] and [na_unused] effectively split the fragement of [na] whose domain is [s_lob] *)
             na_splitting_wf s_lob na na_used na_unused ∗
             (* validate the resources flowing to [e] (i.e [na_used] and external ones from the protocol) result in [R] *)
             flow_eq_dyn gr e na_used R ∗
             (* update the interpretation to reflect the movement *)
             annot_interp ({[e := R]} ∪ na_unused ∪ na) ∗
             (* reestablish the relation between new logical state [ls'] and new physical state [s'] *)
             (local_interp gs tid (LThreadState.get_progress s') ls') ∗
             (* get a wp for the next state [s'] *)
             wp s' Φ
        else
          (* CASE: [pg] is not valid - usually means we have just finished checking an instruction *)
          (* one can do some annotation spliting (cf the modality [|=i=>]) *)
          (* but nothing else - in particular no resource flowing *)
          (* XXX: maybe we can do more things here, don't see anything else that can help though *)
           ∀ (na : mea Σ),
           "Hinterp_annot" ∷ annot_interp na -∗
        |==> ▷ |==>
           annot_interp na ∗ local_interp gs tid (LThreadState.get_progress s') ls ∗ wp s' Φ
        ))
  )%I.

(* #[local] Lemma wp_pre_mono `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} tid *)
(*     (wp1 wp2 : LThreadState.t -> (LThreadState.t -> iProp Σ) -> iProp Σ) : *)
(*   ⊢ (□ ∀ s Φ, wp1 s Φ -∗ wp2 s Φ) → *)
(*     ∀ s Φ, wp_pre tid wp1 s Φ -∗ wp_pre tid wp2 s Φ. *)
(* Proof. *)
(*   iIntros "#H"; iIntros (s Φ) "Hwp". rewrite /wp_pre. *)
(*   destruct (LThreadState.is_terminated s); first done. *)
(*   iIntros (????) "Hs". iDestruct ("Hwp" with "Hs") as "Hwp". *)
(*   case_bool_decide. *)
(*   - iIntros (?) "Hs'". iDestruct ("Hwp" with "Hs'") as ">(%&%&%&%&(?&$)&?&Hannot&?&Hwp)";iModIntro. *)
(*     iExists R,_. iSpecialize ("H" with "Hwp"). iFrame. *)
(*   - iDestruct "Hwp" as ">[? ?]". *)
(*     iModIntro. iFrame. by iApply "H". *)
(* Qed. *)

(* (* wrapper around [wp_pre] to make the type suitable for fixed point computation *) *)
(* #[local] Definition wp_pre' `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} tid : *)
(*   (prodO (leibnizO LThreadState.t) (LThreadState.t -d> iPropO Σ) -d> iPropO Σ) -> *)
(*   (prodO (leibnizO LThreadState.t) (LThreadState.t -d> iPropO Σ) -d> iPropO Σ) := *)
(*   uncurry ∘ wp_pre tid ∘ curry. *)

#[local] Instance wp_pre_contractive `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} tid : Contractive (wp_pre tid).
Proof.
  rewrite /wp_pre => n wp wp' Hwp s Φ.
  repeat (f_contractive || f_equiv).
Qed.


(* #[local] Instance wp_pre_mono' `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} tid: BiMonoPred (wp_pre' tid). *)
(* Proof. *)
(*   constructor. *)
(*   - iIntros (wp1 wp2 ??) "#H". iIntros ([s Φ]); iRevert (s Φ). *)
(*     iApply wp_pre_mono. iIntros "!>" (??). *)
(*     iApply ("H" $! (s, Φ)). *)
(*   - intros wp Hwp n [s1 Φ1] [s2 Φ2] [?%leibniz_equiv ?]. simplify_eq/=. *)
(*     rewrite /curry /wp_pre /post_lifting. do 14 (f_equiv || done). *)
(*     2:{ rewrite /Datatypes.curry. by apply pair_ne. } *)
(*     do 14 (f_equiv || done). rewrite /Datatypes.curry. by apply pair_ne. *)
(* Qed. *)

(* we take a least fixed point of [wp_pre] to get really [wp] *)
(* #[local] Definition wp_def `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} (tid: Tid) : *)
(*   LThreadState.t -> (LThreadState.t -> iProp Σ) -> iProp Σ:= *)
(*   λ s Φ, bi_least_fixpoint (wp_pre' tid) (s,Φ). *)

Definition wp_def `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} (tid: Tid) :
  LThreadState.t -> (LThreadState.t -> iProp Σ) -> iProp Σ := fixpoint (wp_pre tid).
Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp := wp_aux.(unseal).
Arguments wp {Σ _ _ _ _}.

Lemma wp_eq `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!irisG} `{!irisGL} : wp = @wp_def Σ _ _ _ _.
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

(* Texan triples - sswp *)
Notation "'{SS{{' P } } } m @ id {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ SSWP m @ id  {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {SS{{  P  } } }  '/  ' m  '/' @  id  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.

Notation "'{SS{{' P } } } m @ id {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ SSWP m  @ id {{ Φ }})%I
    (at level 20,
     format "'[hv' {SS{{  P  } } }  '/  ' m  '/' @  id {{{  RET  pat ;  Q  } } } ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)

Notation "'{SS{{' P } } } e @ id {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ SSWP e @ id {{ Φ }}) : stdpp_scope.
Notation "'{SS{{' P } } } e @ id {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ SSWP e @ id {{ Φ }}) : stdpp_scope.


Section wp.
  Context `{CMRA Σ}.
  Context `{!invGS_gen HasNoLc Σ}.
  Context `{!irisG}.
  Context `{!irisGL}.
  Implicit Types Φ : LThreadState.t → iProp Σ.
  Implicit Types s : LThreadState.t.
  Implicit Types id : Tid.
  Import LThreadState.

  Lemma wp_unfold id s Φ :
    WP s @ id {{ Φ }} ⊣⊢ wp_pre id (wp id) s Φ.
  Proof. rewrite wp_eq. apply (fixpoint_unfold (wp_pre id)). Qed.

  Lemma wp_sswp id s Φ :
    WP s @ id {{ Φ }} ⊣⊢ SSWP s @ id {{s', WP s' @ id {{ Φ }} }}.
  Proof.
    rewrite wp_unfold sswp_eq /wp_pre /sswp_def.
    destruct (is_terminated s) eqn:Hm;
    repeat setoid_rewrite (wp_unfold id s);rewrite /wp_pre ?Hm //=.
    iSplit.
    - by iIntros "? !>".
    - iApply post_lifting_interp_mod.
  Qed.

  #[global] Instance sswp_ne id s n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (sswp id s).
  Proof. rewrite sswp_eq /sswp_def; intros ?? Heq; repeat f_equiv. Qed.

  #[global] Instance wp_ne id s n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (wp id s).
  Proof.
    revert s. induction (lt_wf n) as [n _ IH]=> s Φ Ψ HΦ.
    rewrite !wp_unfold /wp_pre /post_lifting.
    repeat ((f_contractive || f_equiv); try apply IH); eauto;
    eapply dist_le; eauto with lia.
  Qed.

  #[global] Instance sswp_proper id s :
    Proper (pointwise_relation _ (≡) ==> (≡)) (sswp id s).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply sswp_ne=>v; apply equiv_dist.
  Qed.

  #[global] Instance wp_proper id s :
    Proper (pointwise_relation _ (≡) ==> (≡)) (wp id s).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
  Qed.

  #[global] Instance sswp_contractive id s n :
    TCEq (is_terminated s) false →
    Proper (pointwise_relation _ (dist_later n) ==> dist n) (sswp id s).
  Proof.
    intros He Φ Ψ HΦ. rewrite !sswp_eq /sswp_def He.
    repeat apply bi.forall_ne =>?.
    by repeat (f_contractive || f_equiv).
  Qed.

  #[global] Instance wp_contractive id s n :
    TCEq (is_terminated s) false →
    Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp id  s).
  Proof.
    intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He.
    repeat apply bi.forall_ne =>?.
    by repeat (f_contractive || f_equiv).
  Qed.

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
    - iIntros (?) "Hs'".
      iMod ("Hwp" with "Hs'") as "Hwp".
      iModIntro. iNext.
      iDestruct "Hwp" as ">(%&%&%&%&(?&FE)&?&?&?&Hwp)".
      iExists R,_,_. iFrame. by iApply "HΦ".
    - iIntros (?) "H".
      iDestruct ("Hwp" with "H") as ">H".
      iModIntro. iNext.
      iMod "H" as "(? & ? & ?)".
      iFrame. by iApply "HΦ".
  Qed.

  Lemma sswp_strong_mono' id s Φ Ψ :
    SSWP s @ id {{ Φ }} -∗  (∀ k, Φ k -∗ |=i=> Ψ k) -∗ SSWP s @ id {{ Ψ }}.
  Proof.
    iIntros "H HΦ".
    rewrite sswp_eq /sswp_def.
    destruct (is_terminated s) eqn:?.
    { iMod "H". by iApply ("HΦ" with "[-]"). }
    iIntros (????) "Hs". iDestruct ("H" with "Hs") as "Hwp".
    case_bool_decide.
    - iIntros (?) "[Hs' Hannot]".
      rewrite interp_mod_eq /interp_mod_def.

      iMod ("Hwp" with "[$Hs' $Hannot]") as "Hwp".
      iModIntro. iNext.
      iDestruct "Hwp" as ">(%&%&%&%&?&FE&Hannot&?&H)".
      iSpecialize ("HΦ" with "H"). iDestruct ("HΦ" with "Hannot") as ">[? ?]".
      iExists R. by iFrame.
    - iIntros (?) "H".
      iDestruct ("Hwp" with "H") as ">H".
      iModIntro. iNext.
      iMod "H" as "(Ha & $ & Hwp)".
      rewrite interp_mod_eq.
      iMod ("HΦ" with "Hwp Ha") as "[? ?]".
      by iFrame.
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
    iIntros "H HΦ".
    iLöb as "IH" forall ( s Φ Ψ).
    rewrite !wp_unfold  /wp_pre.
    destruct (is_terminated s) eqn:?.
    { by iApply (post_lifting_strong_mono with "H HΦ"). }

    iIntros (????) "Hs". iDestruct ("H" with "Hs") as "Hwp".
    case_bool_decide.
    - iIntros (?) "Hs'".
      iDestruct ("Hwp" with "Hs'") as ">Hwp".
      iModIntro. iNext.
       iMod "Hwp" as "(%&%&%&%&?&FE&?&?&Hwp)".
      iExists R. iFrame. iApply ("IH" with "Hwp HΦ").
    - iIntros (?) "Hs'".
      iDestruct ("Hwp" with "Hs'") as ">Hwp".
      iModIntro. iNext. iMod "Hwp" as "($ & $ &Hwp)".
      iModIntro. iApply ("IH" with "Hwp HΦ").
  Qed.

  Lemma bupd_sswp id s Φ :
    (|==> SSWP s @ id {{ Φ }}) ⊢ SSWP s @ id {{ Φ }}.
  Proof.
    rewrite sswp_eq /sswp_def. iIntros "H".
    destruct (is_terminated s) eqn:?.
    { by iApply interp_mod_bupd. }
    iIntros (????) "Hs". iDestruct ("H" with "Hs") as "Hwp".
    case_bool_decide.
    - iIntros (?) "Hs'".
      iMod ("Hwp" with "Hs'") as ">Hwp".
      iModIntro. iNext.
      iDestruct "Hwp" as ">(%&%&%&%&?&?&?&Hwp)".
      iExists R. by iFrame.
    - iIntros (?) "H".
      iDestruct ("Hwp" with "H") as ">H".
      done.
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
      iMod ("Hwp" with "[$Hs' $Hannot]") as "Hwp".
      iModIntro. iNext.
      iDestruct "Hwp" as ">(%&%&%&%&?&?&?&Hwp)";iModIntro.
      iExists R. by iFrame.
    - iIntros (?) "H".
      rewrite interp_mod_eq.
      iDestruct ("Hwp" with "H") as ">[Hwp H]".
      iDestruct ("Hwp" with "H") as ">$".
      all: by iFrame.
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
    - iIntros (?) "Hs'".
      iMod ("Hwp" with "Hs'") as "Hwp".
      iModIntro. iNext.
      iDestruct "Hwp" as ">(%&%&%&%&?&?&?&?&>Hwp)".
      iExists R. by iFrame.
    - iIntros (?) "H".
      iMod ("Hwp" with "H") as "Hwp".
      iModIntro. iNext.
      iMod "Hwp" as "($&$&?)".
      iFrame.
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
      iDestruct ("Hwp" with "[$Hs' $Hannot]") as ">Hwp".
      iModIntro.
      iNext.
      iMod "Hwp" as "(%&%&%&%&?&?&Hannot&Hwp)".
      iDestruct "Hwp" as "[? Hwp]".
      iDestruct ("Hwp" with "Hannot") as ">[Hwp Hannot]".
      iExists R. by iFrame.
    - iIntros (?) "H".
      rewrite interp_mod_eq.
      iDestruct ("Hwp" with "H") as ">Hwp".
      iModIntro. iNext.
      iDestruct "Hwp" as ">(Hwp & $& H)".
      iMod ("H" with "Hwp") as "[? ?]".
      by iFrame.
  Qed.

  Lemma bupd_wp id s Φ :
    (|==> WP s @ id {{ Φ }}) ⊢ WP s @ id {{ Φ }}.
  Proof.
    rewrite wp_unfold /wp_pre. iIntros "H". destruct (is_terminated s) eqn:?.
    { iApply post_lifting_interp_mod. iApply interp_mod_bupd. iMod "H". iModIntro. iModIntro. done. }
    iIntros (????) "Hs". iDestruct ("H" with "Hs") as "Hwp".
    case_bool_decide.
    - iIntros (?) "Hs'". iDestruct ("Hwp" with "Hs'") as ">>Hwp".
      iModIntro. iNext.
      iDestruct "Hwp" as ">(%&%&%&%&?&?&?&?&Hwp)".
      iExists R. by iFrame.
    - iIntros (?) "H".
      iDestruct ("Hwp" with "H") as ">Hwp".
      done.
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

      iDestruct ("Hwp" with "[$Hs' $Hannot]") as ">Hwp".
      iModIntro. iNext.
      iDestruct "Hwp" as ">(%&%&%&%&?&?&?&Hwp)";iModIntro.
      iExists R. by iFrame.
    - iIntros (?) "H".
      rewrite interp_mod_eq.
      iDestruct ("Hwp" with "H") as ">[Hwp H]".
      iDestruct ("Hwp" with "H") as ">Hwp".
      iModIntro. done.
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
    - iIntros (?) "Hs'".
      iDestruct ("Hwp" with "Hs'") as ">Hwp".
      iModIntro. iNext.
      iDestruct "Hwp" as ">(%&%&%&%&?&?&?&?&Hwp)".
      iExists R. iFrame. iMod ("Hwp" with "HP") as "$".
    - iIntros (?) "H".
      iDestruct ("Hwp" with "H") as ">Hwp".
      iModIntro. iNext.
      iMod "Hwp" as "(? & Hwp & H)". iFrame.
      iMod "HP". iMod ("H" with "HP") as "$". done.
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
      iDestruct ("Hwp" with "[$Hs' $Hannot]") as ">Hwp".
      iModIntro. iNext.
      iMod "Hwp" as "(%&%&%&%&?&?&Hannot&Hwp)".
      iDestruct "Hwp" as "[? Hwp]". iDestruct ("Hwp" with "HP") as "Hwp".
      iDestruct ("Hwp" with "Hannot") as ">[Hwp ?]".
      iExists R. by iFrame.
    - iIntros (?) "H".
      iDestruct ("Hwp" with "H") as ">Hwp".
      iModIntro. iNext.
      iMod "Hwp" as "(Ha & $ & Hwp)".
      rewrite interp_mod_eq.
      iMod ("HP" with "Ha") as "[HP Ha]".
      iDestruct ("Hwp" with "HP Ha") as ">[? ?]".
      by iFrame.
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
    - iIntros (?) "Hs'".
      iDestruct ("Hwp" with "Hs'") as ">Hwp".
      iModIntro. iNext.
      iDestruct "Hwp" as ">(%&%&%&%&?&?&?&?&Hwp)".
      iExists R. iFrame. iMod "HP". iModIntro. iApply (wp_strong_mono with "Hwp").
      iIntros (k) "H"; iApply "H"; done.
    - iIntros (?) "H".
      iDestruct ("Hwp" with "H") as ">Hwp".
      iModIntro. iNext.
      iMod "Hwp" as "(? & Hwp & H)". iFrame.
      iMod "HP".
      iApply (wp_strong_mono with "H").
      iModIntro. iIntros (k) "H"; iApply "H"; done.
  Qed.

  Lemma wp_step_iupd id s P Φ :
    (|=i=> P) -∗
    WP s @ id {{ k, P -∗ |==> Φ k }} -∗
               WP s @ id {{ Φ }}.
  Proof.
    rewrite !wp_unfold /wp_pre. iIntros "HP H".
    destruct (is_terminated s).
    {
      iApply post_lifting_interp_mod.
      iMod "HP".
      iModIntro.
      iApply (post_lifting_strong_mono with "H").
      iIntros (?) "H". by iApply "H".
    }
    iIntros (????) "Hs". iDestruct ("H" with "Hs") as "Hwp".
    case_bool_decide.
    - iIntros (?) "Hs'".
      iDestruct ("Hwp" with "[$Hs']") as ">Hwp".
      iModIntro. iNext.
      iMod "Hwp" as "(%&%&%&%&?&?&Hannot&? &Hwp)".
      rewrite interp_mod_eq.
      iDestruct ("HP" with "Hannot") as ">[HP Hannot]".
      iExists R. iFrame. iApply (wp_strong_mono with "Hwp").
      iModIntro. iIntros (k) "H"; iApply "H"; done.
    - iIntros (?) "H".
      iDestruct ("Hwp" with "H") as ">Hwp".
      iModIntro. iNext.
      iMod "Hwp" as "(Ha & Hwp & H)".
      rewrite interp_mod_eq.
      iMod ("HP" with "Ha") as "[Ha HP]".
      iFrame.
      iApply (wp_strong_mono with "H").
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
