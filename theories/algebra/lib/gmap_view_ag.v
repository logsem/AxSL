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

(** This file contains a variant of [gmap_view]: gmap K (agree V) *)
(** Most of lemmas are their proofs are copied from [iris.algebra/lib/gmap_view] and tweaked *)
From iris.algebra Require Export view gmap.
From iris.algebra Require Import proofmode_classes.

From iris.proofmode Require Import tactics.

Local Definition gmap_view_ag_fragUR (K : Type) `{Countable K} (V : ofe) : ucmra :=
  gmapUR K (agreeR V).

Section rel.
  Context (K : Type) `{Countable K} (V : ofe).
  Implicit Types (m : gmap K V) (k : K) (v : V) (n : nat).
  Implicit Types (f : gmap K (agree V)).

  Local Definition gmap_view_ag_rel_raw n m f : Prop :=
    map_Forall (λ k (v: agree V), ∃ v', v ≡{n}≡ to_agree v' ∧ m !! k = Some v') f.

  Local Lemma gmap_view_ag_rel_raw_mono n1 n2 m1 m2 f1 f2 :
    gmap_view_ag_rel_raw n1 m1 f1 →
    m1 ≡{n2}≡ m2 →
    f2 ≼{n2} f1 →
    n2 ≤ n1 →
    gmap_view_ag_rel_raw n2 m2 f2.
  Proof.
    intros Hrel Hm Hf Hn k va Hk.
    (* For some reason applying the lemma in [Hf] does not work... *)
    destruct (lookup_includedN n2 f2 f1) as [Hf' _]. specialize (Hf' Hf). clear Hf.
    specialize (Hf' k). rewrite Hk in Hf'.
    apply option_includedN in Hf'.
    destruct Hf' as [[=]|(? & va' & [= <-] & Hf1 & Hincl)].
    specialize (Hrel _ _ Hf1) as (v & Hagree & Hm1). simpl in *.
    specialize (Hm k).
    edestruct (dist_Some_inv_l _ _ _ _ Hm Hm1) as (v' & Hm2 & Hv).
    exists v'. split; last done.
    rewrite -Hv.
    destruct Hincl as [Heqva|Hinclva].
    - simpl in *. rewrite Heqva. eapply dist_le; last eassumption. done.
    - etrans; last first.
      { eapply dist_le; last eassumption. done. }
      eapply agree_valid_includedN; last done.
      eapply cmra_validN_le; last eassumption.
      rewrite Hagree. done.
  Qed.

  Local Lemma gmap_view_ag_rel_raw_valid n m f :
    gmap_view_ag_rel_raw n m f → ✓{n} f.
  Proof.
    intros Hrel k. destruct (f !! k) as [va|] eqn:Hf; rewrite Hf; last done.
    specialize (Hrel _ _ Hf) as (v & Hagree & Hm1). simpl in *.
    rewrite Hagree. done.
  Qed.

  Local Lemma gmap_view_ag_rel_raw_unit n :
    ∃ m, gmap_view_ag_rel_raw n m ε.
  Proof. exists ∅. apply: map_Forall_empty. Qed.

  Local Canonical Structure gmap_view_ag_rel : view_rel (gmapO K V) (gmap_view_ag_fragUR K V) :=
    ViewRel gmap_view_ag_rel_raw gmap_view_ag_rel_raw_mono
            gmap_view_ag_rel_raw_valid gmap_view_ag_rel_raw_unit.

  Local Lemma gmap_view_ag_rel_exists n (f : gmap K (agreeR V)) :
    (∃ m, gmap_view_ag_rel n m f) ↔ ✓{n} f.
  Proof.
    split.
    { intros [m Hrel]. eapply gmap_view_ag_rel_raw_valid, Hrel. }
    intros Hf.
    cut (∃ m, gmap_view_ag_rel n m f ∧ ∀ k, f !! k = None → m !! k = None).
    { naive_solver. }
    induction f as [|k ag f Hk' IH] using map_ind.
    { exists ∅. split; [|done]. apply: map_Forall_empty. }
    move: (Hf k). rewrite lookup_insert=> [/= ?].
    destruct (to_agree_uninjN n ag) as [v ?]; [done|].
    destruct IH as (m & Hm & Hdom).
    { intros k'. destruct (decide (k = k')) as [->|?]; [by rewrite Hk'|].
      move: (Hf k'). by rewrite lookup_insert_ne. }
    exists (<[k:=v]> m).
    rewrite /gmap_view_ag_rel /= /gmap_view_ag_rel_raw map_Forall_insert //=. split_and!.
    - exists v. by rewrite lookup_insert.
    - eapply map_Forall_impl; [apply Hm|]; simpl.
      intros k' ag' (v'&?&?). exists v'.
      rewrite lookup_insert_ne; naive_solver.
    - intros k'. rewrite !lookup_insert_None. naive_solver.
  Qed.

  Local Lemma gmap_view_ag_rel_unit n m : gmap_view_ag_rel n m ε.
  Proof. apply: map_Forall_empty. Qed.

  Local Lemma gmap_view_ag_rel_discrete :
    OfeDiscrete V → ViewRelDiscrete gmap_view_ag_rel.
  Proof.
    intros ? n m f Hrel k va Hk.
    destruct (Hrel _ _ Hk) as (v & Hagree & Hm).
    exists v.  split; last by auto.
    eapply discrete_iff; first by apply _.
    eapply discrete_iff; first by apply _.
    done.
  Qed.
End rel.

Local Existing Instance gmap_view_ag_rel_discrete.
Notation gmap_view_ag K V := (view (@gmap_view_ag_rel_raw K _ _ V)).
Definition gmap_view_agO (K : Type) `{Countable K} (V : ofe) : ofe :=
  viewO (gmap_view_ag_rel K V).
Definition gmap_view_agR (K : Type) `{Countable K} (V : ofe) : cmra :=
  viewR (gmap_view_ag_rel K V).
Definition gmap_view_agUR (K : Type) `{Countable K} (V : ofe) : ucmra :=
  viewUR (gmap_view_ag_rel K V).

Section definitions.
  Context {K : Type} `{Countable K} {V : ofe}.

  Definition gmap_view_ag_auth (m : gmap K V) : gmap_view_agR K V :=
    ●V m.
  Definition gmap_view_ag_frag (k : K) (v : V) : gmap_view_agR K V :=
    ◯V {[k := (to_agree v)]}.
End definitions.

Section lemmas.
  Context {K : Type} `{Countable K} {V : ofe}.
  Implicit Types (m : gmap K V) (k : K) (v : V).

  Global Instance : Params (@gmap_view_ag_auth) 4 := {}.
  Global Instance gmap_view_ag_auth_ne : NonExpansive (gmap_view_ag_auth (K:=K) (V:=V)).
  Proof. solve_proper. Qed.
  Global Instance gmap_view_ag_auth_proper : Proper ((≡) ==> (≡)) (gmap_view_ag_auth (K:=K) (V:=V)).
  Proof. apply ne_proper, _. Qed.

  Global Instance : Params (@gmap_view_ag_frag) 5 := {}.
  Global Instance gmap_view_ag_frag_ne k : NonExpansive (gmap_view_ag_frag (V:=V) k).
  Proof. solve_proper. Qed.
  Global Instance gmap_view_ag_frag_proper k : Proper ((≡) ==> (≡)) (gmap_view_ag_frag (V:=V) k).
  Proof. apply ne_proper, _. Qed.


  (* Helper lemmas *)
  Local Lemma gmap_view_ag_rel_lookup n m k v :
    gmap_view_ag_rel K V n m {[k := to_agree v]} ↔ m !! k ≡{n}≡ Some v.
  Proof.
    split.
    - intros Hrel.
      edestruct (Hrel k) as (v' & Hagree & ->).
      { rewrite lookup_singleton. done. }
      simpl in *. apply (inj _) in Hagree. rewrite Hagree.
      done.
    - intros (v' & Hm & Hv')%dist_Some_inv_r' j va.
      destruct (decide (k = j)) as [<-|Hne]; last by rewrite lookup_singleton_ne.
      rewrite lookup_singleton. intros [= <-]. simpl.
      exists v'. split_and!; by rewrite ?Hv'.
  Qed.

 (** Composition and validity *)
  Lemma gmap_view_ag_auth_valid m : ✓ gmap_view_ag_auth m.
  Proof.
    rewrite view_auth_dfrac_valid. by intuition eauto using gmap_view_ag_rel_unit.
  Qed.

  Lemma gmap_view_ag_frag_validN n k v : ✓{n} gmap_view_ag_frag k v.
  Proof.
    rewrite view_frag_validN gmap_view_ag_rel_exists singleton_validN.
    naive_solver.
  Qed.
  Lemma gmap_view_ag_frag_valid k v : ✓ gmap_view_ag_frag k v.
  Proof.
    rewrite cmra_valid_validN.
    intros. apply gmap_view_ag_frag_validN.
  Qed.

  Lemma gmap_view_ag_frag_op k v :
    gmap_view_ag_frag k v ≡ gmap_view_ag_frag k v ⋅ gmap_view_ag_frag k v.
  Proof. rewrite -view_frag_op singleton_op agree_idemp //. Qed.

  Lemma gmap_view_ag_frag_op_validN n k v1 v2 :
    ✓{n} (gmap_view_ag_frag k v1 ⋅ gmap_view_ag_frag k v2) ↔
    v1 ≡{n}≡ v2.
  Proof.
    rewrite view_frag_validN gmap_view_ag_rel_exists singleton_op singleton_validN.
    by rewrite to_agree_op_validN.
  Qed.
  Lemma gmap_view_ag_frag_op_valid k v1 v2 :
    ✓ (gmap_view_ag_frag k v1 ⋅ gmap_view_ag_frag k v2) ↔ v1 ≡ v2.
  Proof.
    rewrite view_frag_valid. setoid_rewrite gmap_view_ag_rel_exists.
    rewrite -cmra_valid_validN singleton_op singleton_valid.
    by rewrite to_agree_op_valid.
  Qed.
  (* FIXME: Having a [valid_L] lemma is not consistent with [auth] and [view]; they
     have [inv_L] lemmas instead that just have an equality on the RHS. *)
  Lemma gmap_view_ag_frag_op_valid_L `{!LeibnizEquiv V} k v1 v2 :
    ✓ (gmap_view_ag_frag k v1 ⋅ gmap_view_ag_frag k v2) ↔ v1 = v2.
  Proof. unfold_leibniz. apply gmap_view_ag_frag_op_valid. Qed.

  Lemma gmap_view_ag_both_validN n m k v :
    ✓{n} (gmap_view_ag_auth m ⋅ gmap_view_ag_frag k v) ↔
    m !! k ≡{n}≡ Some v.
  Proof.
    rewrite /gmap_view_ag_auth /gmap_view_ag_frag.
    rewrite view_both_dfrac_validN gmap_view_ag_rel_lookup.
    split; first naive_solver.
    intro; split;done.
  Qed.
  Lemma gmap_view_ag_both_valid m k v :
    ✓ (gmap_view_ag_auth m ⋅ gmap_view_ag_frag k v) ↔
    m !! k ≡ Some v.
  Proof.
    rewrite /gmap_view_ag_auth /gmap_view_ag_frag.
    rewrite view_both_dfrac_valid. setoid_rewrite gmap_view_ag_rel_lookup.
    split=>[[_ Hm]|Hm].
    - apply equiv_dist=>n. apply Hm.
    - split; first done. intros n.
      revert n. apply equiv_dist. apply Hm.
  Qed.
  Lemma gmap_view_ag_both_valid_L `{!LeibnizEquiv V} m k v :
    ✓ (gmap_view_ag_auth m ⋅ gmap_view_ag_frag k v) ↔
    m !! k = Some v.
  Proof. unfold_leibniz. apply gmap_view_ag_both_valid. Qed.

(** Frame-preserving updates *)
  Lemma gmap_view_ag_alloc m k v :
    m !! k = None →
    gmap_view_ag_auth m ~~> gmap_view_ag_auth (<[k := v]> m) ⋅ gmap_view_ag_frag k v.
  Proof.
    intros Hfresh Hdq. apply view_update_alloc=>n bf Hrel j ag /=.
    rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
    - assert (bf !! k = None) as Hbf.
      { destruct (bf !! k) as [ag'|] eqn:Hbf; last done.
        specialize (Hrel _ _ Hbf). destruct Hrel as (v' & _ & Hm).
        exfalso. rewrite Hm in Hfresh. done. }
      rewrite lookup_singleton Hbf right_id.
      intros [= <-]. eexists. split; first done.
      rewrite lookup_insert. done.
    - rewrite lookup_singleton_ne; last done.
      rewrite left_id=>Hbf.
      specialize (Hrel _ _ Hbf). destruct Hrel as (v' & ? & Hm).
      eexists. split; first done.
      rewrite lookup_insert_ne //.
  Qed.

  Lemma gmap_view_ag_alloc_big m m' :
    m' ##ₘ m →
    gmap_view_ag_auth m ~~>
      gmap_view_ag_auth (m' ∪ m) ⋅ ([^op map] k↦v ∈ m', gmap_view_ag_frag k v).
  Proof.
    intros. induction m' as [|k v m' ? IH] using map_ind; decompose_map_disjoint.
    { rewrite big_opM_empty left_id_L right_id. done. }
    rewrite IH //.
    rewrite big_opM_insert // assoc.
    apply cmra_update_op; last done.
    rewrite -insert_union_l. apply (gmap_view_ag_alloc _ k).
    by apply lookup_union_None.
  Qed.

  Lemma gmap_view_ag_alloc_lookup m k v :
    m !! k = Some v →
    gmap_view_ag_auth m ~~> gmap_view_ag_auth m ⋅ gmap_view_ag_frag k v.
  Proof.
    intros Hfresh Hdq. apply view_update_alloc=>n bf Hrel j ag /=.
    rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
    - destruct (bf !! k) as [ag'|] eqn:Hbf.
      + specialize (Hrel _ _ Hbf). destruct Hrel as (v' & Hag' & Hm).
        rewrite Hm in Hfresh. inversion Hfresh;subst v';clear Hfresh.
        rewrite Hbf.
        rewrite lookup_singleton.
        rewrite -Some_op.
        intro Hsome. inversion Hsome;subst ag;clear Hsome.
        exists v.
        rewrite Hag'. split;last done.
        symmetry.
        apply agree_valid_includedN.
        by rewrite agree_idemp.
        eexists _. reflexivity.
      + rewrite lookup_singleton Hbf right_id.
        intros [= <-]. eexists. split; done.
    - rewrite lookup_singleton_ne; last done.
      rewrite left_id=>Hbf.
      specialize (Hrel _ _ Hbf). destruct Hrel as (v' & ? & Hm).
      eexists. split; done.
  Qed.

  Lemma gmap_view_ag_alloc_lookup_big m m0 :
    m0 ⊆ m →
    gmap_view_ag_auth m ~~>
      gmap_view_ag_auth m ⋅ ([^op map] k↦v ∈ m0, gmap_view_ag_frag k v).
  Proof.
    intros Hsub. revert Hsub.
    induction m0 as [|k v m0 Hnotdom IH] using map_ind; intros Hsub.
    { rewrite big_opM_empty /=.
      rewrite ucmra_unit_right_id //. }
    assert (m !! k = Some v) as Hlk.
    rewrite map_subseteq_spec in Hsub.
    apply Hsub. apply lookup_insert_Some; left; done.
    rewrite big_opM_insert //.
    rewrite [gmap_view_ag_frag _ _ ⋅ _]comm assoc.
    etrans.
    apply IH. etrans; last exact Hsub. by apply insert_subseteq.
    rewrite -assoc [ _ ⋅ gmap_view_ag_frag _ _]comm assoc .
    apply cmra_update_op;last done.
    by apply gmap_view_ag_alloc_lookup.
  Qed.

 (* Typeclass instances *)
  Global Instance gmap_view_ag_frag_core_id k v :CoreId (gmap_view_ag_frag k v).
  Proof. apply _. Qed.

  Global Instance gmap_view_ag_cmra_discrete : OfeDiscrete V → CmraDiscrete (gmap_view_agR K V).
  Proof. apply _. Qed.

  Global Instance gmap_view_ag_frag_mut_is_op k v :
    IsOp' (gmap_view_ag_frag k v) (gmap_view_ag_frag k v) (gmap_view_ag_frag k v).
  Proof. rewrite /IsOp'. apply gmap_view_ag_frag_op. Qed.

End lemmas.

Program Definition gmap_view_agURF (K : Type) `{Countable K} (F : oFunctor) : urFunctor := {|
  urFunctor_car A _ B _ := gmap_view_agUR K (oFunctor_car F A B);
  urFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (rel:=gmap_view_ag_rel K (oFunctor_car F A1 B1))
              (rel':=gmap_view_ag_rel K (oFunctor_car F A2 B2))
              (gmapO_map (K:=K) (oFunctor_map F fg))
              (gmapO_map (K:=K) (agreeO_map (oFunctor_map F fg)))
|}.
Next Obligation.
  intros K ?? F A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  apply viewO_map_ne.
  - apply gmapO_map_ne, oFunctor_map_ne. done.
  - apply gmapO_map_ne. apply agreeO_map_ne, oFunctor_map_ne. done.
Qed.
Next Obligation.
  intros K ?? F A ? B ? x;simpl in *. rewrite -{2}(view_map_id x).
  apply (view_map_ext _ _ _ _)=> y.
  - rewrite /= -{2}(map_fmap_id y).
    apply map_fmap_equiv_ext=>k ??.
    apply oFunctor_map_id.
  - rewrite /= -{2}(map_fmap_id y).
    apply map_fmap_equiv_ext=>k ag ?.
    simpl. rewrite -{2}(agree_map_id ag).
    eapply agree_map_ext; first by apply _.
    apply oFunctor_map_id.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl in *.
  rewrite -view_map_compose.
  apply (view_map_ext _ _ _ _)=> y.
  - rewrite /= -map_fmap_compose.
    apply map_fmap_equiv_ext=>k ??.
    apply oFunctor_map_compose.
  - rewrite /= -map_fmap_compose.
    apply map_fmap_equiv_ext=>k [df va] ?.
    simpl. rewrite -agree_map_compose.
    eapply agree_map_ext; first by apply _.
    apply oFunctor_map_compose.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? B1 ? B2 ? fg; simpl.
  (* [apply] does not work, probably the usual unification probem (Coq #6294) *)
  apply: view_map_cmra_morphism; [apply _..|]=> n m f.
  intros Hrel k ag Hf. move: Hf.
  rewrite !lookup_fmap.
  destruct (f !! k) as [ag'|] eqn:Hfk; rewrite Hfk; last done.
  simpl=> [= <-].
  specialize (Hrel _ _ Hfk). simpl in Hrel. destruct Hrel as (v & Hagree & Hm).
  exists (oFunctor_map F fg v).
  rewrite Hm. split; last by auto.
  rewrite Hagree. rewrite agree_map_to_agree. done.
Qed.

Global Instance gmap_view_agURF_contractive (K : Type) `{Countable K} F :
  oFunctorContractive F → urFunctorContractive (gmap_view_agURF K F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  apply viewO_map_ne.
  - apply gmapO_map_ne. apply oFunctor_map_contractive. done.
  - apply gmapO_map_ne.
    apply agreeO_map_ne, oFunctor_map_contractive. done.
Qed.

Program Definition gmap_view_agRF (K : Type) `{Countable K} (F : oFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := gmap_view_agR K (oFunctor_car F A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (rel:=gmap_view_ag_rel K (oFunctor_car F A1 B1))
              (rel':=gmap_view_ag_rel K (oFunctor_car F A2 B2))
              (gmapO_map (K:=K) (oFunctor_map F fg))
              (gmapO_map (K:=K) (agreeO_map (oFunctor_map F fg)))
|}.
Solve Obligations with apply gmap_view_agURF.

Global Instance gmap_view_agRF_contractive (K : Type) `{Countable K} F :
  oFunctorContractive F → rFunctorContractive (gmap_view_agRF K F).
Proof. apply gmap_view_agURF_contractive. Qed.

#[export] Typeclasses Opaque gmap_view_ag_auth gmap_view_ag_frag.
