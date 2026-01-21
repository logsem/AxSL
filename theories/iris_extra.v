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

From iris.bi Require Import big_op.
From iris.prelude Require Import options.
From iris.bi Require Import telescopes derived_laws_later.
From iris.proofmode Require Import base modality_instances classes classes_make.
From iris.proofmode Require Import ltac_tactics.
From stdpp Require Import countable fin_sets functions.
From iris.algebra Require Import list gmap.
Import interface.bi derived_laws.bi derived_laws_later.bi.
Require Import self.stdpp_extra.
Import bi.

(* upstream to [iris/proofmode/class_instances.v] *)
Section class_instances.

Context {PROP : bi}.
Implicit Types P Q R : PROP.

#[global] Instance into_pure_big_sepM2 `{Countable K} {A B}
    (Φ : K → A -> B → PROP) (φ : K → A -> B → Prop) (m1 : gmap K A) (m2 : gmap K B):
  (∀ k x y, IntoPure (Φ k x y) (φ k x y)) →
  IntoPure ([∗ map] k↦x;y ∈ m1;m2, Φ k x y) ((∀ k : K, is_Some (m1 !! k) ↔ is_Some (m2 !! k)) ∧
       (∀ k y1 y2, m1 !! k = Some y1 → m2 !! k = Some y2 → φ k y1 y2)).
Proof.
  rewrite /IntoPure. intros HΦ. setoid_rewrite HΦ.
  rewrite pure_and. apply and_intro.
  - apply big_sepM2_lookup_iff.
  - apply big_sepM2_pure_1.
Qed.

#[global] Instance into_pure_big_sepL2 `{!BiAffine PROP} {A B}
  (Φ : nat → A -> B → PROP) (φ : nat → A -> B → Prop) (l1 : list A) (l2 : list B):
  (∀ k x y, IntoPure (Φ k x y) (φ k x y)) →
  IntoPure ([∗ list] k↦x;y ∈ l1;l2, Φ k x y) (length l1 = length l2 ∧ ∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → φ k y1 y2).
Proof.
  rewrite /IntoPure. intros HΦ.
  setoid_rewrite HΦ.
  rewrite big_sepL2_pure.
  done.
Qed.

End class_instances.

Section big_op.

  Import bi.
  Context {PROP : bi}.
  Implicit Types P Q : PROP.
  Implicit Types Ps Qs : list PROP.
  Implicit Types A : Type.

  Lemma big_sepL2_bupd `{!BiBUpd PROP} {A B} (Φ : nat → A → B → PROP) l1 l2 :
    ([∗ list] k↦x;y ∈ l1;l2, |==> Φ k x y) ⊢ |==> [∗ list] k↦x;y ∈ l1;l2, Φ k x y.
  Proof.
    rewrite !big_sepL2_alt !persistent_and_affinely_sep_l.
    etrans; [| by apply bupd_frame_l]. apply sep_mono_r. apply big_sepL_bupd.
  Qed.

Section sep_list2.
  (* upstream *)
  Context {A B : Type}.
  Implicit Types Φ Ψ : nat → A → B → PROP.


  (* very ugly but I've tried my best.. *)
  Lemma big_sepL2_snoc_inv_l  Φ x1 l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1++ [x1]; l2, Φ k y1 y2) ⊢
    ∃ x2 l2', (⌜l2 = l2'++[x2] ⌝ ∧
              Φ (length l1) x1 x2) ∗ [∗ list] k↦y1;y2 ∈ l1;l2', Φ k y1 y2.
  Proof.
    rewrite big_sepL2_app_inv_l.
    apply bi.exist_elim. intro.
    apply bi.exist_elim. intro.
    apply bi.pure_elim_l. intro.
    rewrite bi.sep_comm.
    rewrite big_sepL2_alt.
    rewrite bi.exist_exist.
    rewrite -(bi.exist_intro a).
    rewrite -bi.sep_exist_r.
    apply bi.sep_mono. 2 : done.
    apply bi.pure_elim_l. intro Hl.
    assert (∃ x0, [x0] = a0) as [x0 <-].
    - simpl in Hl.
      destruct a0.
      + simpl in Hl. lia.
      + destruct a0.
        * exists b. done.
        * simpl in Hl;lia.
    - simpl. rewrite -(bi.exist_intro x0).
      apply bi.and_intro.
      + apply bi.pure_intro. done.
      + assert (length l1 + 0 = length l1) as -> by lia.
        simpl. apply bi.sep_elim_l. apply _.
  Qed.

End sep_list2.

Section gmap.
(*
  From stdpp Require Import countable fin_sets functions.
  From iris.algebra Require Import list gmap.
  From iris.bi Require Import derived_laws_later.
  From iris.prelude Require Import options.
  Import interface.bi derived_laws.bi derived_laws_later.bi.
  Require Import self.stdpp_extra.
*)
  Lemma big_sepS_to_map `{Countable K}  {A : Type} (m: gmap K A) (s: gset K) (f: A -> PROP) :
    dom m ⊆ s ->
    ([∗ set] x ∈ s, from_option f emp (m !! x))%I ⊣⊢
    ([∗ map] _ ↦ y ∈ m, f y)%I.
  Proof.
    revert s. induction m as [|?? m Hlk] using map_ind; intros s Hdom.
    - rewrite -(big_sepS_proper (λ _, emp)%I).
      2:{ intros. simpl. rewrite lookup_empty //=. }
      rewrite big_sepS_emp. rewrite big_sepM_empty //.
    - rewrite dom_insert_L in Hdom.
    rewrite (union_difference_singleton_L i s). 2:set_solver + Hdom.
    rewrite big_sepS_union. 2:set_solver +. rewrite big_sepS_singleton.
    rewrite lookup_insert /=.
    rewrite big_sepM_insert;auto.
    rewrite -(big_sepS_proper (λ y, from_option f emp (m !! y))%I).
    2:{ intros ? Hin. rewrite lookup_insert_ne //. set_solver + Hin. }
    rewrite (IHm (s ∖ {[i]})) //.
    apply not_elem_of_dom in Hlk.
    set_solver + Hlk Hdom.
  Qed.

  Lemma big_sepS_fold_to_gmap `{Countable A} (X : gset A) (f : A -> PROP):
   ([∗ map] _ ↦ y ∈ ((set_fold (λ e acc, <[e:=f e]> acc) ∅ X)), y) ⊣⊢
   [∗ set] x ∈ X, f x.
  Proof.
    rewrite set_fold_to_gmap_imap //. rewrite map_union_empty.
    rewrite -(big_sepS_to_map _ X).
    2: rewrite map_imap_dom_Some dom_gset_to_gmap //.
    rewrite big_sepS_proper.
    - reflexivity.
    - intros x Hin.
      rewrite map_lookup_imap lookup_gset_to_gmap. case_guard;done.
  Qed.

  Lemma big_sepM_sepM2_zip `{Countable K} {A B} (m1: gmap K A) (m2: gmap K B) (f: K-> A->B->PROP) :
    dom m1 = dom m2 ->
    ([∗ map] k↦v ∈ m1, from_option (λ v', f k v v') emp (m2 !! k)) ⊣⊢
    [∗ map] k↦v;v' ∈ m1;m2, f k v v'.
  Proof.
    revert m1.
    induction m2 as [|k v' m2 Hlk'] using map_ind.
    {
      intros ? Hdom. rewrite dom_empty_L in Hdom. apply dom_empty_inv_L in Hdom. subst m1.
      rewrite big_sepM_empty big_sepM2_empty //.
    }
    {
      intros ? Heq.
      assert (is_Some (m1 !! k)) as [v Hlk].
      { apply elem_of_dom. rewrite Heq. rewrite dom_insert_L. set_solver +. }
      rewrite (big_sepM_delete _ _ k);eauto.
      rewrite -(insert_id m1 k v) //. rewrite (big_sepM2_delete _ _ _ k v v').
      2:{ apply lookup_insert_Some;auto. }
      2:{ apply lookup_insert_Some;auto. }
      rewrite lookup_insert /=. rewrite delete_insert_delete. rewrite delete_insert //.
      specialize (IHm2 (delete k m1)). ospecialize (IHm2 _).
      - rewrite dom_delete_L. rewrite Heq. rewrite dom_insert_L. apply not_elem_of_dom in Hlk'. set_solver + Hlk'.
      - rewrite -IHm2.
        f_equiv. apply big_sepM_proper.
        intros ?? Hlk''.
        assert (k ≠ k0). { apply lookup_delete_Some in Hlk''. destruct Hlk'';done. }
        f_equiv. rewrite lookup_insert_ne //.
    }
  Qed.

End gmap.
End big_op.
