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

From stdpp Require Import ssreflect list sets fin_maps fin_map_dom gmap.

Lemma head_app{A} (l1 l2 :list A): head (l1 ++ l2) = match head l1 with
                                                     | Some x => Some x
                                                     | None => head l2
                                                     end.
Proof. destruct l1; done. Qed.

Lemma list_sum_zero l : list_sum l = 0 -> Forall (fun e => e = 0) l.
Proof.
  intros Hsum.
  induction l;first done.
  rewrite /= in Hsum.
  assert (a = 0) as -> by lia.
  rewrite Nat.add_0_l in Hsum.
  apply Forall_cons_2;auto.
Qed.

Lemma list_filter_split {A} (l : list A) (P: A -> Prop) `{forall x : A, Decision (P x)}:
        l ≡ₚ filter (λ x, P x) l ++ filter (λ x, ¬ P x) l.
  Proof.
    induction l.
    rewrite !filter_nil. done.
    destruct (decide (P a)).
    {
      rewrite filter_cons_True //.
      rewrite filter_cons_False //.
      rewrite {1}IHl.
      rewrite app_comm_cons //.
      intro. done.
    }
    {
      rewrite filter_cons_False //.
      rewrite filter_cons_True //.
      rewrite {1}IHl.
      rewrite -Permutation_cons_app.
      reflexivity. done.
    }
  Qed.

  Lemma list_foldr_absorb {A B} (l1 l2 : list A) (f : A -> B -> B) (b : B) (x : A):
    Forall (λ x', x' = x) l1 ->
    (forall b', f x b' = f x (f x b')) ->
    f x (foldr f b (l1 ++ l2)) = f x (foldr f b l2).
  Proof.
    intros.
    induction l1. done.
    rewrite -app_comm_cons.
    rewrite foldr_cons.
    apply Forall_cons_1 in H. destruct H as [-> Hforall].
    rewrite IHl1 //.
  Qed.


Section list_subset_ind.
  (* An induction principle that works well with [big_sepL/big_sepL2] *)
  Definition list_subset {A} (l l' : list A) := ∃ x l'', l' ≡ₚ l ++ (x :: l'') .

  Lemma list_subset_wf {A} : wf ((@list_subset A))%stdpp.
  Proof.
    intros l.
    apply (Acc_impl (fun l1 l2 => length l1 < length l2)).
    apply (wf_projected (lt) length).
    done. apply lt_wf.
    intros ? ? [? [? Hp]].
    rewrite Hp.
    rewrite app_length. rewrite cons_length.
    lia.
  Qed.

  Lemma list_subset_ind {A} (P : list A → Prop) :
    P [] → (∀ l'', (∀l', list_subset l' l'' ->  P l') → P l'') → forall l', P l'.
  Proof.
    intros.
    apply well_founded_induction with (list_subset).
    apply list_subset_wf.
    intros. destruct x eqn:Heqn. done.
    apply H0.
    intros. apply H1. done.
  Qed.

End list_subset_ind.

Section prefix_ind.
  (* An induction principle that works well with [big_sepL/big_sepL2] *)
  Definition prefix_strict {A} (l l' : list A) := ∃ x, l' = l ++ [x].

  Lemma prefix_strict_wf {A} : wf ((@prefix_strict A))%stdpp.
  Proof.
    intros l.
    apply (Acc_impl (fun l1 l2 => length l1 < length l2)).
    apply (wf_projected (lt) length).
    done.
    apply lt_wf.
    intros ? ? [].
    rewrite H.
    rewrite app_length.
    simpl. lia.
  Qed.

  Lemma prefix_strict_cons {A} (l l' : list A) x : l = x :: l' -> ∃ l'', prefix_strict l'' l.
  Proof.
    intros.
    revert x l H.
    induction l'.
    exists []. exists x. done.
    {
      intros.
      specialize (IHl' a (a::l')).
      feed specialize IHl'.
      done.
      destruct IHl' as [l'' []].
      exists (x::l'').
      exists x0.
      rewrite H.
      rewrite H0.
      done.
    }
  Qed.

  Lemma prefix_strict_ind {A} (P : list A → Prop) :
    P [] → (∀ l' l'', prefix_strict l' l'' ->  P l' → P l'') → forall l', P l'.
  Proof.
    intros.
    apply well_founded_induction with (prefix_strict).
    apply prefix_strict_wf.
    intros.
    destruct x eqn:Heqn.
    done.
    pose proof (prefix_strict_cons x l a).
    feed specialize H2;first done.
    destruct H2.
    rewrite -Heqn.
    apply (H0 x0);first done.
    apply H1.
    rewrite -Heqn //.
  Qed.
End prefix_ind.

Section sets.
  Context `{Countable T}.
  Implicit Type A B C : gset T.

  Lemma union_split_difference_intersection_L A B:
    A = (A ∖ B) ∪ (A ∩ B) ∧ (A ∖ B) ## (A ∩ B).
  Proof.
    split.
    rewrite union_intersection_l_L difference_union_L. set_solver.
    set_solver.
  Qed.

  Lemma union_split_difference_intersection_subseteq_L A B:
    B ⊆ A ->
    A = (A ∖ B) ∪ B ∧ (A ∖ B) ## B.
  Proof.
    intro H0.
    pose proof (union_split_difference_intersection_L A B) as H1.
    assert (A ∩ B = B) by set_solver + H0.
    set_solver + H1 H2.
  Qed.

  Lemma difference_split_subseteq_L A B C :
    A ⊆ B -> B ⊆ C ->
    C ∖ A = (C ∖ B) ∪ (B ∖ A).
  Proof.
    intros H1 H2.
    pose proof (union_split_difference_intersection_subseteq_L B A H1) as [Heq Hdisj].
    rewrite {1}Heq.
    rewrite difference_union_distr_r_L.
    rewrite union_intersection_r_L.
    rewrite difference_union_L.
    set_solver.
  Qed.

End sets.

Section set_filter.
  Context `{FinSet A C}.

  Lemma set_filter_subseteq (s1 s2 : C) `{∀ x : A, Decision (P x)}:
    s1 ⊆ s2 ->
    filter P s1 ⊆ filter P s2.
  Proof.
    intros ?? Hin. apply elem_of_filter in Hin. destruct Hin as [Heq Hin].
    apply elem_of_filter. split;auto.
  Qed.

  Lemma set_filter_split (s : C) P `{∀ x : A, Decision (P x)}:
    filter P s ∪ filter (λ x, ¬P x) s ≡ s ∧ filter P s ## filter (λ x, ¬P x) s.
  Proof.
    split.
    {
      apply set_equiv.
      intros.
      rewrite elem_of_union.
      split.
      intros [|].
      apply elem_of_filter in H8. naive_solver.
      apply elem_of_filter in H8. naive_solver.
      intro.
      destruct (decide (P x)).
      left;apply elem_of_filter;done.
      right;apply elem_of_filter;done.
    }
    intros ???. apply elem_of_filter in H8. apply elem_of_filter in H9. naive_solver.
  Qed.
End set_filter.

Section theorems.

  Lemma map_filter_split {A} `{FinMap K M} (m : M A) P `{∀ x : K, Decision (P x)}:
    filter (λ '(k,v), P k) m ∪ filter (λ '(k,v), ¬P k) m = m.
  Proof.
    apply map_eq_iff.
    intros.
    rewrite lookup_union.
    rewrite 2!map_filter_lookup.
    destruct (m !! i) eqn:Hlk;simpl.
    {
      rewrite option_guard_bool_decide.
      case_bool_decide.
      rewrite option_guard_False;auto.
      rewrite option_guard_True //.
    }
    done.
  Qed.

  Lemma map_difference_union_exists {A} `{!Equiv A} `{FinMapDom K M D}
    `{!RelDecision (≡@{D})}
    `{!RelDecision (∈@{D})} (m1 m2 : M A) :
    dom m1 ⊆ dom m2 ->
    exists m3, m3 ⊆ m2 ∧
          dom m3 ≡@{D} dom m1 ∧
          m3 ∪ (m2 ∖ m1) =@{M A} m2.
  Proof.
    intros Hsub. revert m1 Hsub.
    induction m2 using map_ind.
    - intros. exists ∅. split;auto. rewrite dom_empty in Hsub.
      apply set_subseteq_antisymm in Hsub.
      feed specialize Hsub.
      apply empty_subseteq.
      rewrite !Hsub.
      split. rewrite dom_empty //.
      apply dom_empty_iff in Hsub.
      subst m1.
      rewrite map_difference_empty. rewrite map_union_empty //.
    - intros. rewrite dom_insert in Hsub.
      destruct (decide (i ∈ dom m1)).
      assert (dom (delete i m1) ⊆ dom m) as Hdom.
      assert (delete i ({[i := x]} ∪ m) = m) as <-.
      rewrite -insert_union_singleton_l.
      by apply delete_insert.
      rewrite 2!dom_delete.
      apply difference_mono_r.
      rewrite dom_union dom_singleton //.
      specialize (IHm2 _ Hdom).
      destruct IHm2 as [m3 (Hsubm3 & Hdomm3 & Heqm3)].
      exists (<[i := x]> m3).
      split. apply insert_subseteq_l. apply lookup_insert_Some. left;done.
      transitivity m. done. by apply insert_subseteq_r.
      split.
      rewrite elem_of_dom in e. destruct e.
      assert (m1 = <[i:= x0]> (delete i m1)) as ->.
      rewrite insert_delete //.
      rewrite !dom_insert.
      f_equiv. done.
      rewrite -insert_union_l. rewrite -{2}Heqm3.
      f_equal. f_equal.
      apply elem_of_dom in e. destruct e as [x1 Hlk1].
      rewrite -{1}(insert_delete m1 i x1) //.
      erewrite difference_insert. rewrite insert_delete.
      apply map_eq. intros. rewrite !lookup_difference_with.
      destruct (m !! i0) eqn:Heqn;simpl.
      apply elem_of_dom_2 in Heqn.
      apply not_elem_of_dom in H14.
      rewrite lookup_delete_ne //.
      set_solver + Heqn H14.
      done. exact Hlk1.
      assert (dom m1 ⊆ dom m) as Hdom.
      {
        apply not_elem_of_dom in H14.
        set_solver.
      }
      specialize (IHm2 _ Hdom).
      destruct IHm2 as [m3 (Hsubm3 & Hdomm3 & Heqm3)].
      exists m3. split. apply insert_subseteq_r. rewrite -not_elem_of_dom. rewrite Hdomm3 //. done.
      split. done.
      rewrite -{2} Heqm3.
      assert (<[i:=x]> m ∖ m1 = <[i:=x]> (m ∖ m1)) as ->.
      rewrite insert_difference.
      rewrite delete_notin //. apply not_elem_of_dom. auto.
      rewrite insert_union_r //.
      apply not_elem_of_dom.
      set_solver.
  Qed.

End theorems.

Section set_fold_to_gmap.
  Context `{Countable A}.

  Lemma set_fold_to_gmap_insert {B} (X : gset A) (f : A -> B) (m1 m2 : gmap A B) (x : A):
    x ∉ dom m1 ->
    {[x]} ∪ dom m1 ## dom m2 ->
    {[x]} ∪ dom m1 ## X ->
    set_fold (λ e acc, <[e:= f e]> acc) m2 X ∪ <[x:= f x]> m1
    = set_fold (λ e acc, <[e:= f e]> acc) (<[x:= f x]> m2) X ∪ m1.
    revert m1 m2.
    induction X using set_ind_L.
    {
      intros ?? Hnin Hdisj1 Hdisj2. rewrite 2!set_fold_empty //.
      rewrite -insert_union_r //.
      rewrite insert_union_l //.
      apply not_elem_of_dom. set_solver + Hdisj1.
    }
    {
      intros ?? Hnin Hdisj1 Hdisj2.
      setoid_rewrite (set_fold_disj_union_strong _ (λ e acc, <[e:= f e]> acc)).
      rewrite 2!set_fold_singleton.
      erewrite IHX;eauto. rewrite insert_commute //.
      set_solver + Hdisj2.
      rewrite dom_insert_L. set_solver + Hnin Hdisj1 Hdisj2.
      set_solver + Hdisj2.
      intros. apply _.
      intros. by apply insert_commute.
      set_solver.
      intros. apply _.
      intros. by apply insert_commute.
      set_solver.
    }
  Qed.

  Lemma map_imap_dom_Some {B C} (m : gmap A B) (f : A -> B -> C) :
    dom (map_imap (λ k v, Some (f k v)) m) = dom m.
  Proof.
    induction m using map_ind.
    rewrite map_imap_empty //.
    rewrite map_imap_insert. rewrite 2!dom_insert_L. rewrite IHm //.
  Qed.

  Lemma set_fold_to_gmap_imap {B} (X : gset A) (Y : gmap A B) (f : A -> B):
    X ## dom Y ->
    (set_fold (λ e (acc : gmap A B), <[e:=f e]> acc) Y X) = map_imap (λ k _, Some (f k)) (gset_to_gmap tt X) ∪ Y.
  Proof.
    revert Y. induction X as [|x X Hin] using set_ind_L;intros Y.
    - rewrite set_fold_empty //. rewrite map_imap_empty. rewrite map_empty_union //.
    - intros Hdisj. rewrite set_fold_disj_union_strong.
      rewrite set_fold_singleton.
      rewrite IHX //.
      rewrite gset_to_gmap_union_singleton. rewrite map_imap_insert.
      rewrite -(union_insert_delete _ (<[x:=f x]> Y) x (f x)).
      rewrite delete_insert //. apply not_elem_of_dom. set_solver + Hdisj.
      apply not_elem_of_dom. rewrite map_imap_dom_Some. rewrite dom_gset_to_gmap. set_solver + Hin.
      apply lookup_insert.
      set_solver.
      intros. rewrite insert_commute //.
      set_solver.
  Qed.

  Lemma set_fold_to_gmap_dom {B} (X : gset A) (f : A -> B):
  dom (set_fold (λ e (acc : gmap A B), <[e:=f e]> acc) ∅ X) = X.
  Proof.
    rewrite set_fold_to_gmap_imap //. rewrite dom_union_L.
    rewrite map_imap_dom_Some. rewrite dom_gset_to_gmap //. set_solver.
  Qed.

  Lemma set_fold_to_gmap_lookup {B} (X : gset A) (f : A -> B) k:
    k ∈ X ->
    (set_fold (λ e (acc : gmap A B), <[e:=f e]> acc) ∅ X) !! k = Some (f k).
  Proof.
    intros. rewrite set_fold_to_gmap_imap //. rewrite lookup_union_l //.
    rewrite map_lookup_imap. rewrite lookup_gset_to_gmap. case_option_guard; done.
  Qed.

End set_fold_to_gmap.
