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

(* This file contains the definition of edge annotation and node annotation, which are used by weakestpres *)
From iris.algebra Require Import gmap gset.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi Require Import big_op.
From iris.proofmode Require Import tactics.

From iris_named_props Require Import named_props.

From self Require Import stdpp_extra iris_extra.
From self.algebra Require Import base.
From self.lang Require Import mm opsem.
From self.low.lib Require Import ind.

Notation mea Σ := (gmap Eid (iProp Σ)).
Notation sra Σ := (gmap Eid (mea Σ)).

Section definition.
Import Graph.

(** Node Annotation *)
(* resources that are avaliable on each node *)
Class NodeAnnot `{CMRA Σ} :=
  {
    (* wf of [na]: for all local nodes in [dom(na)], their progresses < current progress [ρ] *)
    na_local_wf tid (na : mea Σ) := set_Forall (fun e => is_local_node_of tid e) (dom na);
    (* [na] is in sync with progress: all local nodes in the domain of na are po pred of current node *)
    na_at_progress (gr : Graph.t) (tid : Tid) (pg : ThreadState.progress) (na : mea Σ) : iProp Σ :=
      "%Hna_dom_eq" ∷ ⌜filter (λ e : Eid, Graph.is_local_node_of tid e) (dom na) = LThreadStep.eids_from_init gr tid pg⌝;
    (* [na] can be splitted: we use this when flowing things *)
    na_splitting_wf (s_lob : gset Eid) (na na_used na_unused : mea Σ) : iProp Σ :=
      "%Hnau_dom_sub" ∷ ⌜dom na_used ⊆ s_lob⌝ ∗
      "#Hnau_wf" ∷ [∗ map] e ↦ Pu;Puu ∈ na_used;na_unused,
          ▷ □ (from_option (λ P, P) emp (na !! e) -∗ (Pu ∗ Puu));
    (* [na] is complete: we have all nodes in [dom(na)] *)
    na_full (gr : Graph.t) (na : mea Σ) : iProp Σ :=
      "%Hna_dom_full" ∷ ⌜dom na = Candidate.non_initial_eids gr⌝;
  }.

#[global] Instance na_instance `{CMRA Σ}: NodeAnnot := {}.

End definition.

Section lemma.

  (** about [na_at_progress] *)
  Lemma na_at_progress_not_elem_of `{CMRA Σ} gr tid pg na:
    na_at_progress gr tid pg na ⊢
    ⌜ThreadState.progress_to_node pg tid ∉ dom na⌝.
  Proof.
    iIntros "Hpg".  rewrite /na_at_progress. iNamed "Hpg".
    iPureIntro.
    assert(G : ThreadState.progress_to_node pg tid ∉ LThreadStep.eids_from_init gr tid pg).
    { unfold LThreadStep.eids_from_init.
      rewrite elem_of_filter.
      rewrite /ThreadState.progress_to_node /ThreadState.progress_of_node /=.
      intros [Hpg _].
      by apply (ThreadState.progress_lt_refl_False pg).
    }
    rewrite -Hna_dom_eq in G.
    rewrite elem_of_filter in G.
    by contradict G.
  Qed.

  Import Graph.

  Context `{Σ: !gFunctors}.
  Context `{CMRA Σ}.
  Context `{!invGS_gen HasNoLc Σ}.

  (* specialised lemmas for induction on ob *)
  Lemma ob_set_ind_L (gr : Graph.t) (s_all : gset Eid) (P : gset Eid → Prop) :
    AAConsistent.t gr ->
    P ∅ → (∀ (x : Eid) (X : gset Eid), x ∉ X -> x ∈ s_all ->
                                       rel_subset (AAConsistent.ob gr) X s_all ->
                                       set_Forall (λ x', (x', x) ∉ (AAConsistent.ob gr)) ({[x]} ∪ X) →
                                       P X → P ({[ x ]} ∪ X)) →
                                       ∀ X, X ⊆ s_all -> rel_semi_last_set (AAConsistent.ob gr) X s_all -> P X.
  Proof.
    intros Hcs. apply rel_set_ind_L.
    - destruct Hcs as [_ Hac _]. assumption.
    - unfold ob. apply GRel.grel_transitive_plus.
  Qed.

  Lemma ob_set_ind_L3 (gr : Graph.t) (s_all : gset Eid) (P : gset Eid → Prop) :
    AAConsistent.t gr ->
    P ∅ → (∀ (x: Eid) (X : gset Eid), rel_semi_last_set (AAConsistent.ob gr) X s_all  -> x ∈ get_rel_first (AAConsistent.ob gr) X -> P (X ∖ {[x]}) → P X) →
                                       ∀ X, rel_semi_last_set (AAConsistent.ob gr) X s_all -> P X.
  Proof.
    intros Hcs. apply rel_set_ind_L3.
    - destruct Hcs as [_ Hac _]. assumption.
    - unfold ob. apply GRel.grel_transitive_plus.
  Qed.

End lemma.

Notation "s '⊆[ob' gr ] s'" := (rel_semi_last_set (AAConsistent.ob gr) s s') (at level 80).
Notation "s '⊂[ob' gr ] s'" := (rel_subset (AAConsistent.ob gr) s s') (at level 80).
