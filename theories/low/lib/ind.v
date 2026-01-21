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

(* Induction scheme for any poset *)
From SSCCommon Require Import Common CSets GRel.

Require Import stdpp.prelude.

Require Import ssreflect.

Open Scope stdpp_scope.

Section ind.
  Context `{C: Countable A}.
  Notation Rel := (grel A).

  (* Nodes in [s] are not [r]-before any nodes in [s' ∖ s] *)
  (* We would use [s] as the set of unchecked nodes (that are [r:=ob]-after checked nodes),
     [s'] as the full set of nodes *)
  (* This is weaker in the sense that nodes in [s] can be ordered *)
  Definition rel_semi_last_set (r : Rel) (s s' : gset A) :=
    set_Forall (λ e_last, set_Forall (λ e, (e_last, e) ∉ r) (s' ∖ s)) s.

  Notation "s ⊆[ r ] s'" := (rel_semi_last_set r s s') (at level 80).

  (* In this WF relation [s] is strictly smaller than [s'], which is not always the case for [rel_semi_last_set] *)
  Definition rel_subset (r: Rel) (s s' : gset A) : Prop := s ⊂ s' ∧ s ⊆[ r ] s'.
  Notation "s ⊂[ r ] s'" := (rel_subset r s s') (at level 80).

  Lemma rel_semi_last_set_mono (r: Rel) (s s' s'' : gset A) :
    s ⊂ s' -> s' ⊆ s'' ->
    s ⊆[ r ] s'  -> s' ⊆[ r ] s'' ->
    s ⊆[ r ] s''.
  Proof.
    intros Hsub Hsub' Hob Hob'.
    apply set_subseteq_inv_L in Hsub'.
    destruct Hsub' as [Hsub'| ->];last done.
    intros x Hin.
    specialize (Hob x Hin). simpl in Hob.
    intros x'' Hin''.
    destruct (decide (x'' ∈ s')).
    - intro.
      specialize (Hob x'').
      ospecialize* Hob. set_solver + e Hin'' Hsub Hsub'.
      done. done.
    - rewrite /rel_semi_last_set in Hob'.
      destruct (decide (x ∈ s')).
    + specialize (Hob' x).
      ospecialize (Hob' _). set_solver + e.
      simpl in Hob'.
      apply Hob'.
      set_solver + Hin'' n.
    + set_solver + Hsub n0 Hin.
  Qed.

  Lemma rel_subset_wf r : well_founded (rel_subset r).
  Proof.
    apply (wf_projected (<)%nat size).
    - intros ?? (? & _).
      by apply subset_size.
    - apply lt_wf.
  Qed.

  (* Get the nodes that are [r]-before other nodes from [s] *)
  Definition get_rel_first (r : Rel) (s : gset A) :=
    filter (λ e, set_Forall (λ e', (e', e) ∉ r) s) s.

  Lemma get_rel_first_subseteq r s :
    get_rel_first r s ⊆ s.
  Proof.
    intros ? Hin.
    apply elem_of_filter in Hin.
    destruct Hin;done.
  Qed.

  (* FIXME clean up *)
  (* If [s] is not empty, then [get_rel_first s] is not empty *)
  Lemma get_rel_first_non_empty r s :
    grel_irreflexive r ->
    grel_transitive r ->
    (exists x, x ∈ s) ->
    exists x, x ∈ get_rel_first r s.
  Proof.
    intros Hac Htr.
    eapply (well_founded_induction _
              (λ s, (∃ x : A, x ∈ s) → ∃ x : A, x ∈ get_rel_first r s)).
    Unshelve.
    2: { exact (⊂). }
    2 : {
      eapply (wf_projected (<)%nat size).
      - intros ??. apply subset_size.
      - apply lt_wf.
    }
    clear s. intros s IH Hnem.
    destruct Hnem as [x Hin].
    destruct (decide (x ∈ get_rel_first r s));[exists x;done|].
    rewrite /get_rel_first elem_of_filter in n. rewrite not_and_l in n.
    destruct n; last set_solver + H Hin.
    apply not_set_Forall_Exists in H. 2: apply _.
    destruct H as [x0 [Hin' Hr]].
    assert (x0 ≠ x).
    {
      intros ->.
      rewrite grel_irreflexive_spec in Hac.
      simpl in Hr. apply Hr.
      intro Hxx. specialize (Hac (x, x) Hxx). done.
    }
    specialize (IH (s∖ {[x]})). ospecialize* IH.
    set_solver + Hin.
    (* set_solver + Hsub. *)
    exists x0. set_solver + H Hin Hin'.
    destruct IH as [x2 ?].
    destruct (decide ((x, x2) ∈ r)).
    {
      apply elem_of_filter in H0.
      destruct H0.
      assert (x0 ∈ s ∖ {[x]}) by set_solver + H Hin'.
      specialize (H0 x0 H2).
      simpl in H0. simpl in Hr.
      assert ((x0, x) ∈ r).
      destruct (decide ((x0, x) ∈ r)). done.
      exfalso. apply Hr. done.
      exfalso. apply H0.
      pose proof (grel_transitive_spec r) as [Htran _].
      ospecialize (Htran _).
     apply Htr.
      eapply Htran;eauto.
    }
    {
      exists x2. apply elem_of_filter.
      split. 2:{ apply elem_of_filter in H0. destruct H0. set_solver + H1. }
      rewrite (union_difference_L {[x]} s); first set_solver + Hin.
      apply set_Forall_union.
      apply set_Forall_singleton. done.
      apply elem_of_filter in H0. destruct H0. done.
    }
  Qed.

  (* Get the nodes that are [r]-after other nodes from [s] *)
  Definition get_rel_last (r : Rel) (s : gset A) :=
    filter (λ e, set_Forall (λ e', (e, e') ∉ r) s) s.

  Lemma get_rel_last_subseteq r s :
    get_rel_first r s ⊆ s.
  Proof.
    intros ? Hin.
    apply elem_of_filter in Hin.
    destruct Hin;done.
  Qed.

  (* For any [s], either we can find a '⊆[r]' subset, or it is empty *)
  Lemma rel_semi_last_set_choose_or_empty r s:
    grel_irreflexive r ->
    grel_transitive r ->
    (∃ x, x ∈ s ∧ (s ∖ {[x]}) ⊆[r] s) ∨ s ≡ ∅.
  Proof.
    intros Hac Htr.
    destruct (set_choose_or_empty (get_rel_first r s)) as [[x Hx_in]|HX].
    - left. exists x.
      apply elem_of_filter in Hx_in.
      destruct Hx_in as (Hlast & Hin ).
      split;first done.
      intros y Hy_in.
      assert (Hy_in' : y ∈ s) by set_solver + Hy_in.
      specialize (Hlast y Hy_in').
      assert ((s ∖ (s ∖ {[x]})) = {[x]}) as ->.
      rewrite difference_difference_r_L.
      set_solver + Hin.
      apply set_Forall_singleton. done.
    - destruct (set_choose_or_empty s) as [[y Hy_in]|HY].
      + exfalso.
        pose proof (get_rel_first_non_empty r s Hac Htr) as Hnem.
        ospecialize* Hnem. exists y;done.
        set_solver + Hnem HX.
      + right;done.
  Qed.

  Lemma rel_set_ind (r: Rel) (s_all : gset A) (P : gset A → Prop) :
    Proper ((≡) ==> iff) P →
    grel_irreflexive r ->
    grel_transitive r ->
    P ∅ →
    (∀ (x : A) (X : gset A), x ∉ X -> x ∈ s_all ->
                                 X ⊂[r] s_all ->
                                 set_Forall (λ x', (x', x) ∉ r) ({[x]} ∪ X) →
                                 P X → P ({[ x ]} ∪ X)) →
    ∀ X, X ⊆ s_all -> X ⊆[r] s_all -> P X.
  Proof.
    intros ? Hac Htr Hemp Hadd.
    eapply (well_founded_induction _ (λ X, X ⊆ s_all -> X ⊆[r] s_all → P X)).
    Unshelve.
    2:{ exact (rel_subset r). }
    2:{ apply rel_subset_wf. }
    intros X IH HX_subeq HX_semi_first.
    destruct (rel_semi_last_set_choose_or_empty r X Hac Htr) as [[x [Hx_in HX_x_semi_first]]|HX].
    - rewrite (union_difference {[x]} X);[set_solver + Hx_in|].
      apply Hadd;[set_solver + | set_solver + Hx_in  HX_subeq | | |].
      {
        split. set_solver + Hx_in HX_subeq.
        eapply rel_semi_last_set_mono;eauto.
        set_solver + Hx_in HX_subeq.
      }
      {
        apply set_Forall_union.
        {
          rewrite set_Forall_singleton.
          rewrite grel_irreflexive_spec in Hac.
          intro Hxx. specialize (Hac (x, x) Hxx). done.
        }
        {
          intros x0 Hx0_in.
          apply (HX_x_semi_first x0 Hx0_in).
          set_solver + Hx_in.
        }
      }
      apply IH.
      split. set_solver + Hx_in. done.
      set_solver + HX_subeq.
        eapply rel_semi_last_set_mono;eauto.
        set_solver + Hx_in.
    - by rewrite HX.
  Qed.

  Lemma rel_set_ind_L (r : Rel) (s_all : gset A) (P : gset A → Prop) :
    grel_irreflexive r ->
    grel_transitive r ->
    P ∅ → (∀ (x : A) (X : gset A), x ∉ X -> x ∈ s_all ->
                                       X ⊂[r] s_all ->
                                       set_Forall (λ x', (x', x) ∉ r) ({[x]} ∪ X) →
                  P X → P ({[ x ]} ∪ X)) → ∀ X, X ⊆ s_all -> X ⊆[r] s_all -> P X.
  Proof. apply rel_set_ind. by intros ?? ->%leibniz_equiv_iff. Qed.


End ind.

Section ind_get_first.
  Context `{C: Countable A}.
  Implicit Type (s: gset A).
  Implicit Type (r: grel A).

  Notation "s ⊂[ r ] s'" := (rel_subset r s s') (at level 80).
  Notation "s ⊆[ r ] s'" := (rel_semi_last_set r s s') (at level 80).

  (* For any [s], either we can find a '⊆[r]' subset, or it is empty *)
  Lemma rel_semi_last_set_choose_or_empty3 r s:
    grel_irreflexive r ->
    grel_transitive r ->
    (∃ x, x ∈ get_rel_first r s) ∨ s ≡ ∅.
  Proof.
    intros Hac Htr.
    destruct (set_choose_or_empty (get_rel_first r s)) as [[x Hx_in]|HX].
    - left. exists x. assumption.
    - destruct (set_choose_or_empty s) as [[y Hy_in]|HY].
      + exfalso.
        pose proof (get_rel_first_non_empty r s Hac Htr) as Hnem.
        ospecialize* Hnem. exists y;done.
        set_solver + Hnem HX.
      + right;done.
  Qed.

  Lemma rel_set_ind3 r (s_all : gset A) (P : gset A → Prop) :
    Proper ((≡) ==> iff) P →
    grel_irreflexive r ->
    grel_transitive r ->
    P ∅ →
    (∀ (x: A) (X : gset A), X ⊆[r] s_all -> x ∈ get_rel_first r X -> P (X ∖ {[x]}) → P X) →
    ∀ X, X ⊆[r] s_all -> P X.
  Proof.
    intros ? Hac Htr Hemp Hadd.
    eapply (well_founded_induction _ (λ X, X ⊆[r] s_all → P X)).
    Unshelve.
    2:{ exact (rel_subset r). }
    2:{ apply rel_subset_wf. }
    intros X IH HX_semi_first.
    destruct (rel_semi_last_set_choose_or_empty3 r X Hac Htr) as [[x HX_get_first]|HX_e].
    - apply (Hadd x);[assumption|assumption|].
      apply IH.
      {
        split; set_solver.
      }
      {
        set_solver + HX_semi_first HX_get_first.
      }
    - by rewrite HX_e.
  Qed.

  Lemma rel_set_ind_L3 (r : grel A) (s_all : gset A) (P : gset A → Prop) :
    grel_irreflexive r ->
    grel_transitive r ->
    P ∅ → (∀ (x: A) (X : gset A), X ⊆[r] s_all -> x ∈ get_rel_first r X -> P (X ∖ {[x]}) → P X) → ∀ X, X ⊆[r] s_all -> P X.
  Proof. apply rel_set_ind3. by intros ?? ->%leibniz_equiv_iff. Qed.

End ind_get_first.
