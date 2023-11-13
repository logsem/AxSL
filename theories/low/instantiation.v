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

(** This file contains the instantiation of the low-level logic,
 this is the file that all helper files import*)
From iris_named_props Require Export named_props.
From iris.bi Require Import derived_laws.

From self.lang Require Import mm opsem.
From self.algebra Require Export base.
From self.low Require Export edge event weakestpre interp_mod.

Class ThreadGNL := {
    AALocalMapN : gname;
    AAPoSrcN : gname;
  }.

#[global] Arguments AALocalMapN {_}.
#[global] Arguments AAPoSrcN {_}.

Section interp.
  Context `{CMRA Σ} `{!AABaseG}.

  (** Graph *)
  Import AACandExec.
  Definition global_interp (gs : GlobalState.t) :=
    ("Hgr_ag" ∷ graph_agree gs.(GlobalState.gs_graph) ∗
    "Hinstr_ag" ∷ instr_table_agree gs.(GlobalState.gs_gimem))%I.

  Definition annot_interp (m : gmap Eid (iProp Σ)) : iProp Σ :=
    ∃ (annot : gmap Eid gname),
      ghost_map_ag_auth AANodeAnnotN annot ∗
      ⌜dom annot = dom m⌝ ∗
      ([∗ map] eid ↦ gn;P ∈ annot;m,
         ∃ (res : gmap gname (iProp Σ)),
           own gn (● (GSet (dom res))) ∗
           ([∗ map] gnp ↦ R ∈ res, saved_prop_own gnp (DfracOwn (1/2)) R)∗
           ▷ ■ (([∗ map] _ ↦ R ∈ res, R) ∗-∗ P)).

  Definition token_interp (s : gset Eid) : iProp Σ :=
    own AARmwTokenN (● (GSet s)).

  Definition my_annot_interp (m : gmap Eid (iProp Σ)) : iProp Σ :=
    "Hinterp_annot" ∷ annot_interp m ∗
    "Hinterp_token" ∷ token_interp (dom m).

  Record LogicalLocalState := mk_lls{
      lls_lws : gmap Addr (option Eid);
      lls_pop : option Eid;
    }.

  #[global] Instance eta : Settable _ := settable! mk_lls <lls_lws; lls_pop>.

  Context `{!ThreadGNL}.
  Definition last_write_interp (gs : GlobalState.t) (tid : Tid) (pg : ThreadState.progress)
    (ls : gmap Addr (option Eid)) : iProp Σ :=
    let gr := gs.(GlobalState.gs_graph) in
    let local_writes :=
      filter (λ '(e, _),
                (Graph.is_local_node_of tid) e ∧ ThreadState.progress_of_node e <p pg ∧ e ∈ AACandExec.Candidate.mem_writes gr)
      (AACandExec.Candidate.event_map gr) in
    let last_local_writes :=
      filter (λ '(e, _), map_Forall
                    (λ e' _, (e, e') ∈ AACandExec.Candidate.loc gr ->
                        ThreadState.progress_of_node e' <=p ThreadState.progress_of_node e)
                    local_writes) local_writes in
    ⌜ ∀ (a : Addr) (e : Eid), ls !! a = Some (Some e) <-> (∃ E, last_local_writes !! e = Some E ∧
                                                  AAConsistent.event_is_write_with_addr E a )⌝ ∗
    ⌜ ∀ (a : Addr), ls !! a = Some None -> (map_Forall (λ e E,
                                                          (AAConsistent.event_is_write_with_addr E a = false)) local_writes)⌝ ∗
    ghost_map_auth AALocalMapN 1%Qp ls.

  Definition lpo_src_def o_eid :=
    from_option (λ eid,
                   ((∃ gr, graph_agree gr ∗ ⌜is_Some (gr !! eid)⌝) ∗
                     ∃ gn, own AAPoSrcN (Cinr (to_agree (gn, (EID.tid eid)))) ∗ own gn (●MN{DfracOwn (1/2)%Qp} (ThreadState.progress_of_node eid))
                   )%I) ((own AAPoSrcN (Cinl (to_dfrac_agree (DfracOwn (1/2)%Qp) ())))%I) o_eid.

  Definition po_src_def eid :=
   ((∃ gr, graph_agree gr ∗ ⌜is_Some (gr !! eid)⌝) ∗ ∃ gn, own AAPoSrcN (Cinr (to_agree (gn, (EID.tid eid)))) ∗ own gn (◯MN (ThreadState.progress_of_node eid)))%I.

  Definition po_pred_interp (gs : GlobalState.t) (tid : Tid) (pg : ThreadState.progress)
    (ls : option Eid) : iProp Σ :=
    let gr := gs.(GlobalState.gs_graph) in
    graph_agree gr ∗
    from_option (λ e',
                   ∃ gn, own AAPoSrcN (Cinr (to_agree (gn, (EID.tid e')) )) ∗
                   own gn (●MN{DfracOwn (1/2)%Qp} (ThreadState.progress_of_node e')) ∗ ⌜ EID.tid e' = tid ∧ ThreadState.progress_of_node e' <p pg
                        ∧ ThreadState.progress_is_valid (GlobalState.gs_graph gs) tid (ThreadState.progress_of_node e') ⌝
      )%I (own AAPoSrcN (Cinl (to_dfrac_agree (DfracOwn (1/2)%Qp) ())) )%I ls.


  Definition my_local_interp (gs : GlobalState.t) (tid : Tid) (pg : ThreadState.progress) (ls : LogicalLocalState) :=
    ("Hinterp_local_lws" ∷ last_write_interp gs tid pg (ls.(lls_lws)) ∗
    "Hinterp_po_src" ∷ po_pred_interp gs tid pg (ls.(lls_pop)))%I.

End interp.

Definition instr_def `{CMRA Σ} `{!AABaseG} (a : Addr) (oi : option Instruction) : iProp Σ :=
  ∃ gi, instr_table_agree gi ∗ ⌜gi !! a = oi⌝.
Definition instr_aux : seal (@instr_def). Proof. by eexists. Qed.
Definition instr := instr_aux.(unseal).
Arguments instr {Σ _ _}.
Definition instr_eq : @instr = @instr_def := instr_aux.(seal_eq).
Notation "a ↦ᵢ i" := (instr a (Some i)) (at level 20) : bi_scope.
Notation "a ↦ᵢ -" := (instr a None) (at level 20) : bi_scope.

Definition annot_own_def `{CMRA Σ} `{!AABaseG} eid (P : iProp Σ) :iProp Σ :=
  ∃ n n', ghost_map_ag_elem AANodeAnnotN eid n ∗ own n (◯ (GSet {[n']})) ∗ saved_prop_own n' (DfracOwn (1/2)) P.
Definition annot_own_aux : seal(@annot_own_def). Proof. by eexists. Qed.
Definition annot_own := annot_own_aux.(unseal).
Arguments annot_own {Σ _ _}.
Definition annot_own_eq : @annot_own = @annot_own_def := annot_own_aux.(seal_eq).
Notation "n ↦ₐ P" := (annot_own n P) (at level 20) : bi_scope.

Definition rmw_token_def `{CMRA Σ} `{!AABaseG} (e : Eid) :=
  own AARmwTokenN (◯ (GSet {[e]})).
Definition rmw_token_aux : seal(@rmw_token_def). Proof. by eexists. Qed.
Definition rmw_token := rmw_token_aux.(unseal).
Arguments rmw_token {Σ _ _}.
Definition rmw_token_eq : @rmw_token = @rmw_token_def := rmw_token_aux.(seal_eq).
Notation "Tok{ n }" := (rmw_token n) (at level 20,
                         format "'Tok{' n  '}'") : bi_scope.

Definition lpo_src_aux : seal (@lpo_src_def). Proof. by eexists. Qed.
Definition lpo_src := lpo_src_aux.(unseal).
Arguments lpo_src {Σ _ _ _}.
Definition lpo_src_eq : @lpo_src = @lpo_src_def := lpo_src_aux.(seal_eq).
Notation "e '-{LPo}>'" := (lpo_src e) (at level 20) : bi_scope.

Definition po_src_aux : seal (@po_src_def). Proof. by eexists. Qed.
Definition po_src := po_src_aux.(unseal).
Arguments po_src {Σ _ _ _}.
Definition po_src_eq : @po_src = @po_src_def := po_src_aux.(seal_eq).
Notation "e '-{Po}>'" := (po_src e) (at level 20) : bi_scope.

Definition last_local_write `{CMRA Σ} `{!AABaseG} `{!ThreadGNL} (tid : Tid) (addr : Addr) (w : option Eid) : iProp Σ :=
  addr ↪[AALocalMapN]{DfracOwn 1} w.

Lemma annot_interp_alloc `{CMRA Σ} `{!AABaseInG}:
  ⊢  |==> ∃ GN, (∃ (annot : gmap Eid gname),
                    ghost_map_ag_auth GN annot ∗
                    ⌜dom annot = dom (∅ : gmap Eid (iProp Σ))⌝ ∗
                    ([∗ map] eid ↦ gn;P ∈ annot;(∅ : gmap Eid (iProp _)),
                       ∃ (res : gmap gname (iProp Σ)),
                         own gn (● (GSet (dom res))) ∗
                         ([∗ map] gnp ↦ R ∈ res, saved_prop_own gnp (DfracOwn (1/2)) R)∗
                         ▷ ■ (([∗ map] _ ↦ R ∈ res, R) ∗-∗ P))).
Proof.
  iDestruct (ghost_map_ag_alloc_empty) as ">[% ?]".
  iModIntro. iExists _. iExists ∅. iFrame.
  iSplit;first done.
  done.
Qed.

Lemma token_interp_alloc `{CMRA Σ} `{!AABaseInG}:
  ⊢  |==> ∃ GN, (own GN (● (GSet (∅ : gset Eid)))).
Proof.
  iDestruct (own_alloc (● (GSet (∅ : gset Eid)))) as ">[% ?]".
  apply auth_auth_valid. done.
  iModIntro. iExists _. iFrame.
Qed.

Lemma graph_agree_alloc `{CMRA Σ} `{!AABaseInG} gr:
  ⊢  |==> ∃ GN, own GN ((to_agree gr) : (agreeR (leibnizO Graph.t))).
Proof.
  iDestruct (own_alloc (to_agree gr)) as ">[% ?]". done.
  iModIntro. iExists _. iFrame.
Qed.

Lemma instr_table_agree_alloc `{CMRA Σ} `{!AABaseInG} gi:
  ⊢  |==> ∃ GN, own GN (to_agree (gi: gmapO Addr (leibnizO Instruction))).
Proof.
  iDestruct (own_alloc (to_agree gi)) as ">[% ?]". done.
  iModIntro. iExists _. iFrame.
Qed.

Lemma interp_alloc `{CMRA Σ} `{!AABaseInG} gs:
  ⊢  |==> ∃ `{!AABaseG}, my_annot_interp ∅ ∗ global_interp gs ∗ graph_agree (gs.(GlobalState.gs_graph)) ∗ instr_table_agree (gs.(GlobalState.gs_gimem)).
Proof.
  iStartProof.
  rewrite /my_annot_interp.
  iDestruct (annot_interp_alloc) as ">[%g1 H1]".
  iDestruct (token_interp_alloc) as ">[%g2 H2]".
  iDestruct (graph_agree_alloc (GlobalState.gs_graph gs)) as ">[%g3 #H3]".
  iDestruct (instr_table_agree_alloc (GlobalState.gs_gimem gs)) as ">[%g4 #H4]".
  iModIntro.
  iExists (GenAABaseG Σ _ _ g3 g1 g4 g2).
  iFrame. rewrite /global_interp.
  rewrite graph_agree_eq;iFrame.
  rewrite instr_table_agree_eq;iFrame.
  iFrame "#".
Qed.

Lemma my_local_interp_alloc `{CMRA Σ} `{!AABaseG} gs pg (i:Tid) locs:
  ThreadState.progress_is_init (GlobalState.gs_graph gs) i pg ->
  graph_agree (gs.(GlobalState.gs_graph)) ⊢ |==> ∃ `{!ThreadGNL},
    my_local_interp gs i pg (mk_lls (gset_to_gmap None locs) None) ∗
    ([∗ set] k ∈ locs, k ↪[AALocalMapN] None) ∗
    None -{LPo}>.
Proof.
  iIntros (Hinit). rewrite /my_local_interp. iIntros "?".
  iDestruct (ghost_map_alloc (gset_to_gmap None locs)) as ">[%g1 [? ?]]".
  rewrite /po_pred_interp /=. rewrite lpo_src_eq.
  iDestruct (own_alloc ((Cinl (to_dfrac_agree (DfracOwn (1/2)%Qp) ())) ⋅ (Cinl (to_dfrac_agree (DfracOwn (1/2)%Qp) ())) )) as ">[%g2 H]". done.
  iExists (Build_ThreadGNL g1 g2).
  rewrite own_op. iDestruct "H" as "[$ $]". iFrame.
  iModIntro. rewrite big_sepM_gset_to_gmap. iFrame.
  iPureIntro. split.
  {
    intros. split.
    intros Hlk. rewrite lookup_gset_to_gmap_Some /= in Hlk. destruct Hlk;done.
    intros [? [Hlk ?]]. exfalso. rewrite map_filter_lookup_Some in Hlk.
    destruct Hlk as [Hlk ?].
    rewrite map_filter_lookup_Some in Hlk.
    destruct Hlk as (?&?&?&?).
    rewrite /ThreadState.progress_is_init in Hinit.
    specialize (Hinit e). feed specialize Hinit.
    apply elem_of_filter. split;auto.
    set_unfold. eexists;eauto. split;eauto.
    rewrite -AACandExec.Candidate.event_map_match //.
    simpl in Hinit. eapply ThreadState.progress_le_gt_False;eauto.
  }
  {
    intro. rewrite lookup_gset_to_gmap_Some.
    intros _. intros e E Hfilter.
    rewrite map_filter_lookup_Some in Hfilter.
    rewrite /ThreadState.progress_is_init in Hinit.
    destruct Hfilter as [? [? [? ?]]].
    specialize (Hinit e). feed specialize Hinit.
    apply elem_of_filter. split;auto.
    set_unfold. eexists;eauto. split;eauto.
    rewrite -AACandExec.Candidate.event_map_match //.
    simpl in Hinit. exfalso. eapply ThreadState.progress_le_gt_False;eauto.
  }
Qed.

Section lemma.
  Context `{CMRA Σ}.
  Context `{!AABaseG}.


  #[global] Instance instr_persis a i: Persistent (a ↦ᵢ i).
  Proof.
    rewrite instr_eq /instr_def. apply _.
  Qed.

  #[global] Instance instr_persis' a: Persistent (a ↦ᵢ -).
  Proof.
    rewrite instr_eq /instr_def. apply _.
  Qed.

  Lemma instr_agree_Some gs a i:
    global_interp gs -∗
    a ↦ᵢ i -∗
    ⌜gs.(GlobalState.gs_gimem) !! a = Some i⌝.
  Proof.
    iIntros "[_ Hinstr] Hi". rewrite instr_eq /instr_def.
    iDestruct "Hi" as "[% [Hag %Hlk]]".
    iDestruct (instr_table_agree_agree with "Hinstr Hag") as %->.
    done.
  Qed.

  Lemma instr_agree_None gs a:
    global_interp gs -∗
    a ↦ᵢ - -∗
    ⌜gs.(GlobalState.gs_gimem) !! a = None⌝.
  Proof.
    iIntros "[_ Hinstr] Hi". rewrite instr_eq /instr_def.
    iDestruct "Hi" as "[% [Hag %Hlk]]".
    iDestruct (instr_table_agree_agree with "Hinstr Hag") as %->.
    done.
  Qed.

  Lemma graph_edge_agree gs e1 e2 E:
    global_interp gs -∗
    e1 -{ E }> e2 -∗
    ⌜Edge.ef_edge_interp gs.(GlobalState.gs_graph) E e1 e2 ⌝.
  Proof.
    iIntros "[Hgr _] He". rewrite edge_eq /edge_def.
    iNamed "He". iDestruct (graph_agree_agree with "Hgr Hgr_interp_e") as %->.
    done.
  Qed.

  Lemma graph_event_agree gs e E:
    global_interp gs -∗
    e -{E}> E -∗
    ⌜ Event.event_interp gs.(GlobalState.gs_graph) E e⌝.
  Proof.
    iIntros "[Hgr _] He". rewrite event_eq /event_def.
    iNamed "He". iDestruct (graph_agree_agree with "Hgr Hgr_interp_e") as %->.
    done.
  Qed.

  Lemma graph_edge_agree_big_pred gs s e E:
    global_interp gs -∗
    ([∗ set] e1 ∈ s, e1 -{ E }> e) -∗
    [∗ set] e1 ∈ s, ⌜Edge.ef_edge_interp gs.(GlobalState.gs_graph) E e1 e⌝.
  Proof.
    iInduction s as [|??] "IH" using set_ind_L.
    iIntros. rewrite big_sepS_empty //.
    iIntros "Hgr Hs".
    rewrite !big_sepS_union; try set_solver.
    iDestruct "Hs" as "[He Hs]".
    rewrite !big_sepS_singleton.
    iDestruct (graph_edge_agree with "Hgr He") as %?.
    iSplit. done. iApply ("IH" with "Hgr Hs").
  Qed.

  Lemma token_excl a b:
    Tok{a} -∗ Tok{b} -∗ ⌜a ≠ b⌝.
  Proof.
    rewrite rmw_token_eq /rmw_token_def.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    iPureIntro. rewrite auth_frag_op_valid in Hvalid.
    rewrite gset_disj_valid_op in Hvalid.
    set_solver + Hvalid.
  Qed.

  Lemma token_alloc {gs tid pg na}:
    na_at_progress (GlobalState.gs_graph gs) tid pg na ∗
    token_interp (dom na) ==∗
    let eid := ThreadState.progress_to_node pg tid in
    token_interp ({[eid]} ∪ (dom na)) ∗ Tok{ eid }.
  Proof.
    iIntros "[Hnin Hint]".
    iDestruct (na_at_progress_not_elem_of with "Hnin") as %Hnin.
    rewrite rmw_token_eq /rmw_token_def /token_interp.
    rewrite -own_op. iApply (own_update with "Hint").
    apply auth_update_alloc.
    apply gset_disj_alloc_empty_local_update.
    set_solver + Hnin.
  Qed.

  Lemma annot_merge n P Q :
    n ↦ₐ P -∗ n ↦ₐ Q -∗ (∀ na, annot_interp na ==∗ (n ↦ₐ (P ∗ Q)) ∗ annot_interp na).
  Proof.
    iIntros "Heid Heid'". rewrite annot_own_eq /annot_interp /annot_own_def.
    iDestruct "Heid" as "[%name [%gn (Hname_mapped & Hset & Hprop)]]".
    iDestruct "Heid'" as "[%name' [%gn' (Hname_mapped' & Hset' & Hprop')]]".
    iDestruct (ghost_map_ag_elem_agree with "Hname_mapped Hname_mapped'") as %->. iClear "Hname_mapped'".
    iIntros (?) "[%name_map (map_auth & %Hdom & Hmap)]".
    iDestruct (ghost_map_ag_lookup with "map_auth Hname_mapped") as "%Hlk_nm".
    assert (is_Some (na !! n)) as [? Hlk_na].
    { apply elem_of_dom. rewrite -Hdom. eapply elem_of_dom_2;eauto. }
    iDestruct (big_sepM2_delete with "Hmap") as "[(%&Hset_a &Hres_map&#Hsep) Hmap]";eauto.
    iDestruct (own_valid_2 with "Hset_a Hset") as %Hset_v.
    rewrite auth_both_valid_discrete in Hset_v. destruct Hset_v as [Hset_v _].
    assert (is_Some (res !! gn)) as [R Hlk_res].
    { apply elem_of_dom. rewrite gset_disj_included in Hset_v. set_solver. }
    iDestruct (own_valid_2 with "Hset_a Hset'") as %Hset_v'.
    rewrite auth_both_valid_discrete in Hset_v'. destruct Hset_v' as [Hset_v' _].
    assert (is_Some (res !! gn')) as [R' Hlk_res'].
    { apply elem_of_dom. rewrite gset_disj_included in Hset_v'. set_solver. }
    iDestruct (own_valid_2 with "Hset Hset'") as %Hset_vv.
    rewrite auth_frag_op_valid in Hset_vv. rewrite gset_disj_valid_op in Hset_vv.

    iDestruct (big_sepM_delete with "Hres_map") as "[Hsp' Hres_map]";eauto.
    iDestruct (saved_prop_agree with "Hprop' Hsp'") as "#Hequiv'".
    iDestruct (big_sepM_delete with "Hres_map") as "[Hsp Hres_map]";eauto.
    { rewrite (lookup_delete_ne _ gn'). exact Hlk_res. set_solver + Hset_vv. }
    iDestruct (saved_prop_agree with "Hprop Hsp") as "#Hequiv".

    iMod (saved_prop_update_halves (P ∗ Q) gn with "Hprop Hsp") as "[Hprop1 Hprop2]".
    iMod (saved_prop_update_halves emp gn' with "Hprop' Hsp'") as "[Hprop1' Hprop2']".

    iModIntro.
    iSplitR "map_auth Hset_a Hprop1 Hprop1' Hmap Hres_map".
    { iExists name',gn. iFrame. }
    iExists name_map. iFrame. iSplit;first done.
    iApply big_sepM2_delete;eauto. iFrame.
    iExists (<[gn' := emp%I]>(<[gn := (P ∗ Q)%I]> res)).
    assert (dom (<[gn' := emp%I]>(<[gn := (P ∗ Q)%I]> res)) = dom res) as ->.
    { apply elem_of_dom_2 in Hlk_res,Hlk_res'. rewrite !dom_insert_L. set_solver + Hlk_res Hlk_res'. }
    iFrame. rewrite 2!big_sepM_insert_delete. iFrame.
    rewrite delete_insert_ne. 2:{ apply elem_of_dom_2 in Hlk_res.  set_solver + Hset_vv. }
    rewrite 2!big_sepM_insert_delete. iFrame.
    iNext. rewrite (bi.sep_comm P Q).
    rewrite -bi.sep_assoc. iRewrite "Hequiv". iRewrite "Hequiv'".
    rewrite -!big_sepM_delete //. rewrite bi.emp_sep //.
    rewrite lookup_delete_ne //. set_solver + Hset_vv.
  Qed.

  Definition annot_agree m eid P :
    annot_interp m -∗ eid ↦ₐ P -∗
    ⌜eid ∈ dom m⌝ ∗ ∃ R, from_option (λ P', ▷ ■ (P' ∗-∗ P ∗ R)) emp (m !! eid).
  Proof.
    iIntros "Hint Heid".
    rewrite annot_own_eq /annot_interp /annot_own_def.
    iDestruct "Hint" as "[%name_map (map_auth & %Hdom & Hmap)]".
    iDestruct "Heid" as "[%name [%gn (Hname_mapped & Hset & Hprop)]]".
    iDestruct (ghost_map_ag_lookup with "map_auth Hname_mapped") as "%H'".
    assert (is_Some (m !! eid)) as [? Hlk].
    { apply elem_of_dom. rewrite -Hdom. eapply elem_of_dom_2;eauto. }
    iDestruct (big_sepM2_lookup with "Hmap") as "(%&Hset_a &Hmap&#Hsep)";eauto.
    iDestruct (own_valid_2 with "Hset_a Hset") as %Hset_v.
    rewrite auth_both_valid_discrete in Hset_v. destruct Hset_v as [Hset_v _].
    assert (is_Some (res !! gn)) as [R Hlk_res].
    { apply elem_of_dom. rewrite gset_disj_included in Hset_v. set_solver. }
    iDestruct (big_sepM_lookup with "Hmap") as "Hsp";eauto.
    iDestruct (saved_prop_agree with "Hprop Hsp") as "Hequiv".
    iSplit. iPureIntro. apply elem_of_dom. eexists;eauto.
    rewrite Hlk /=. rewrite big_sepM_delete //.
    iExists _. iNext. iRewrite "Hequiv".
    rewrite bi.wand_iff_sym. iExact "Hsep".
  Qed.

  Definition annot_agree_big m m':
    annot_interp m -∗
    ([∗ map] eid ↦ P ∈ m', eid ↦ₐ P) -∗
    ⌜dom m' ⊆ dom m ⌝ ∗
    ∃ m'', [∗ map] eid ↦ R;R' ∈ m';m'', from_option (λ P', ▷ ■ (P' ∗-∗ R ∗ R')) emp (m !! eid).
  Proof.
    iIntros "Hannot Hm".
    iInduction m' as [|] "IH" using map_ind.
    iSplit. iPureIntro. rewrite dom_empty_L //. iExists ∅. done.
    rewrite !big_sepM_insert //. iDestruct "Hm" as "[H Hm]".
    iDestruct (annot_agree with "Hannot H") as "#[% [%R Hequiv]]".
    iDestruct ("IH" with "Hannot Hm") as "[%Hdom [%m' IH']]".
    iSplit. iPureIntro. rewrite dom_insert_L. set_solver.
    iExists (<[i := R]> m'). iDestruct (big_sepM2_dom with "IH'") as %Hdom'.
    rewrite big_sepM2_insert //.
    2:{ apply not_elem_of_dom. rewrite -Hdom'. by apply not_elem_of_dom. }
    iFrame. iFrame "Hequiv".
  Qed.

  Definition annot_update m eid P :
    annot_interp m -∗
    eid ↦ₐ P ==∗
    ∃R, annot_interp (<[eid:=R]>m) ∗ from_option(λ P', ▷ ■ (P' ∗-∗ P ∗ R)) emp (m !! eid).
  Proof.
    iIntros "Hint Heid".
    iDestruct (annot_agree with "Hint Heid") as "[%Hdom #_]".
    rewrite elem_of_dom in Hdom. destruct Hdom as [? Hlk]. rewrite Hlk /=.
    rewrite annot_own_eq /annot_interp /annot_own_def.
    iDestruct "Hint" as "[%name_map (map_auth & %Hdom & Hmap)]".
    iDestruct "Heid" as "[%name [%gn (Hname_mapped & Hset & Hprop)]]".
    iDestruct (ghost_map_ag_lookup with "map_auth Hname_mapped") as "%H'".
    iDestruct (big_sepM2_delete with "Hmap") as "[(%&Hset_a &Hmap'&#Hsep) Hmap]";eauto.
    iDestruct (own_valid_2 with "Hset_a Hset") as %Hset_v.
    rewrite auth_both_valid_discrete in Hset_v. destruct Hset_v as [Hset_v _].
    assert (is_Some (res !! gn)) as [R' Hlk_res].
    { apply elem_of_dom. rewrite gset_disj_included in Hset_v. set_solver. }
    iDestruct (big_sepM_delete with "Hmap'") as "[Hsp Hmap']";eauto.
    iDestruct (saved_prop_agree with "Hprop Hsp") as "#Hequiv".
    iMod (saved_prop_update_halves emp%I gn _ _ with "Hprop Hsp") as "(Hprop1 & Hprop2)".
    iModIntro.
    rewrite big_sepM_delete //.
    iExists ([∗ map] y ∈ delete gn res, y)%I.
    iSplitL. 2:{ iNext. iRewrite "Hequiv".  rewrite bi.wand_iff_sym //. }
           iExists _. iFrame.
    iSplitR. rewrite dom_insert_L. iPureIntro.
    assert (eid ∈ dom m). apply elem_of_dom. eexists;done.
    set_solver + H1 Hdom.
    iApply big_sepM2_delete;eauto.
    rewrite lookup_insert_Some. left;split;eauto.
    rewrite delete_insert_delete. iFrame.
    iExists (<[gn := emp%I]>res).
    rewrite dom_insert_L.
    assert (({[gn]} ∪ dom res) = dom res) as ->.
    { assert (gn ∈ dom res). apply elem_of_dom. eexists;done.
      set_solver + H1. }
    rewrite big_sepM_insert_delete //. iFrame.
    iNext. iModIntro. rewrite big_sepM_insert_delete //. iSplit;[iIntros "[_ $]"|iIntros "$"].
  Qed.

  Definition annot_update_big {m m'}:
    annot_interp m -∗
    ([∗ map] eid ↦ P ∈ m', eid ↦ₐ P) ==∗
    ∃m'', ⌜dom m'' = dom m'⌝ ∗
      annot_interp (m'' ∪ m) ∗
          ([∗ map] eid ↦ R; R' ∈ m'; m'', from_option(λ P',▷ ■ (P' ∗-∗ R ∗ R')) emp (m !! eid)).
  Proof.
    iIntros "Hannot Hm".
    iInduction m' as [|] "IH" using map_ind.
    iModIntro. iExists ∅. iSplitR;first done. rewrite map_empty_union. iFrame. done.
    rewrite big_sepM_insert //. iDestruct "Hm" as "[Hi Hm]".
    iDestruct ("IH" with "Hannot Hm") as ">[% (%Hdom & Hannot & Hequiv)]".
    iDestruct (annot_update _ _ x with "Hannot Hi") as ">[% [Hannot Hi]]".
    iModIntro. iExists (<[i := R]> m'').
    iSplitR. { iPureIntro. rewrite !dom_insert_L. rewrite Hdom //. }
    rewrite !insert_union_l. iFrame.
    iApply (big_sepM2_insert_2 with "[Hi]").
    { rewrite lookup_union_r //.
      apply not_elem_of_dom. rewrite Hdom. by apply not_elem_of_dom. }
    done.
  Qed.

  Definition annot_alloc na pg tid gs P :
    annot_interp na ∗ na_at_progress (GlobalState.gs_graph gs) tid pg na
    ==∗
    let eid := ThreadState.progress_to_node pg tid in
    annot_interp (<[eid:=P]>na) ∗
    eid ↦ₐ P.
  Proof.
    iIntros "(Hannot & Hpg)". unfold na_at_progress. iDestruct (na_at_progress_not_elem_of with "Hpg") as %H'.
    unfold annot_interp. iDestruct "Hannot" as "[%name_map (map_auth & %Hdom & Hmap)]".
    iMod (saved_prop_alloc P (DfracOwn 1)) as "[%γ new_prop]". { done. }
    iMod (own_alloc ((● GSet {[γ]}) ⋅ ◯ (GSet {[γ]}))) as "[%gn Hset]".
    { rewrite auth_both_valid_discrete.
      split;last done. apply gset_disj_included. set_solver +. }
    rewrite own_op. iDestruct "Hset" as "[Hset_a Hset_f]".
    iMod (ghost_map_ag_insert (ThreadState.progress_to_node pg tid) gn with "map_auth") as "(map_auth & Hname_mapped)".
    { rewrite -not_elem_of_dom Hdom //. }
    iModIntro.
    iDestruct "new_prop" as "(new_prop1 & new_prop2)".
    iSplitR "Hname_mapped Hset_f new_prop2".
    - iExists _. iFrame. iSplitR. { iPureIntro. set_solver + Hdom. }
      rewrite big_sepM2_insert;eauto.
      2: { apply not_elem_of_dom. rewrite Hdom //. }
      2: { by apply not_elem_of_dom. }
      iSplitL "Hset_a new_prop1".
      { iExists {[γ := P]}. rewrite dom_singleton_L. rewrite !big_sepM_singleton. iFrame. iNext. rewrite -bi.wand_iff_refl //. }
      done.
    - rewrite annot_own_eq /annot_own_def.
      iExists gn, γ. iFrame.
  Qed.

  Lemma annot_split n P Q:
    n ↦ₐ (P ∗ Q) -∗ (∀ na, annot_interp na ==∗ (n ↦ₐ P ∗ n ↦ₐ Q) ∗ annot_interp na).
  Proof.
    iIntros "Heid". rewrite annot_own_eq /annot_own_def.
    rewrite /annot_interp. iIntros (?) "Hint".
    iDestruct "Heid" as "[%name [%gn (#Hname_mapped & Hset & Hprop)]]".
    iDestruct "Hint" as "[%name_map (map_auth & %Hdom & Hmap)]".
    iDestruct (ghost_map_ag_lookup with "map_auth Hname_mapped") as "%H'".
    assert (is_Some (na !! n)) as [? Hlk].
    { apply elem_of_dom. rewrite -Hdom. eapply elem_of_dom_2;eauto. }
    iDestruct (big_sepM2_delete with "Hmap") as "[(%&Hset_a &Hres_map&#Hsep) Hmap]";eauto.
    iDestruct (own_valid_2 with "Hset_a Hset") as %Hset_v.
    rewrite auth_both_valid_discrete in Hset_v. destruct Hset_v as [Hset_v _].
    assert (is_Some (res !! gn)) as [R Hlk_res].
    { apply elem_of_dom. rewrite gset_disj_included in Hset_v. set_solver. }
    iDestruct (big_sepM_delete with "Hres_map") as "[Hsp Hres_map]";eauto.
    iDestruct (saved_prop_agree with "Hprop Hsp") as "#Hequiv".
    iMod (saved_prop_alloc_cofinite (dom res) P (DfracOwn 1)) as "[%gnp [%Hnin new_prop]]". { done. }
    iMod (saved_prop_update_halves Q gn with "Hprop Hsp") as "[Hprop1 Hprop2]".
    iDestruct "new_prop" as "[Hprop1' Hprop2']".
    iMod (own_update _ _ (● GSet ({[gnp]}∪ (dom res)) ⋅ (◯ GSet {[gnp]})) with "Hset_a") as "Hset_a".
    apply auth_update_alloc. apply gset_disj_alloc_empty_local_update. set_solver + Hnin.
    iDestruct (own_op with "Hset_a") as "[Hset_a Hset']".
    iModIntro.
    iSplitR "map_auth Hset_a Hprop1 Hprop1' Hmap Hres_map".
    { iSplitL "Hset' Hprop2'". iExists name,gnp. by iFrame.  iExists name, gn. by iFrame. }
    iExists name_map. iFrame. iSplit;first done.
    iApply big_sepM2_delete;eauto. iFrame.
    iExists (<[gnp := P]>(<[gn := Q]> res)).
    assert (dom (<[gnp:=P]> (<[gn:=Q]> res)) = {[gnp]}∪ dom res) as ->.
    { apply elem_of_dom_2 in Hlk_res. rewrite !dom_insert_L. set_solver + Hlk_res. }
    iFrame. rewrite 2!big_sepM_insert_delete. iFrame.
    rewrite delete_insert_ne. 2:{ apply elem_of_dom_2 in Hlk_res.  set_solver + Hlk_res Hnin. }
    assert ((delete gnp res) = res) as ->. rewrite delete_notin //. by apply not_elem_of_dom.
    rewrite 2!big_sepM_insert_delete. iFrame.
    iNext. iClear "Hname_mapped". iModIntro.
    rewrite bi.sep_assoc. iRewrite "Hequiv".
    rewrite -big_sepM_delete //.
  Qed.

  (** [my_local_interp] *)

  Import ThreadState.

  Context `{HH: !ThreadGNL}.

  Lemma lpo_to_po eid :
    Some eid -{LPo}> -∗
    Some eid -{LPo}> ∗
    eid -{Po}>.
  Proof.
    iIntros "Hlpo".
    rewrite po_src_eq /po_src_def lpo_src_eq /lpo_src_def /=.
    iDestruct "Hlpo" as "[#Hgr [% (#Hag & Hown)]]".
    iEval (rewrite mono_pg_auth_lb_op) in "Hown".
    iDestruct "Hown" as "(Hown & Hown')".
    iFrame "Hgr". iSplitL "Hown"; iExists gn; iFrame "#∗".
  Qed.

  #[global] Instance persistent_po_src `{CMRA Σ} `{!AABaseG} `{!ThreadGNL} eid : Persistent (eid -{Po}>).
  Proof. rewrite po_src_eq /po_src_def. apply _. Qed.

  Lemma po_pred_interp_agree gs {tid : Tid} pg ls o_e:
    po_pred_interp gs tid pg ls -∗
    o_e -{LPo}> -∗
    ⌜ from_option (λ e, EID.tid e = tid ∧ ThreadState.progress_of_node e <p pg
                        ∧ ThreadState.progress_is_valid (GlobalState.gs_graph gs) tid (ThreadState.progress_of_node e)) True o_e⌝.
  Proof.
    iIntros "[Hgr H1] H2". rewrite lpo_src_eq /lpo_src_def.
    destruct o_e;simpl;last done.
    iDestruct "H2" as "[Hgr' [% [H2 H3]]]".
    rewrite /po_pred_interp.
    destruct ls;simpl.
    iDestruct "H1" as "[% [H1 [H1' H1'']]]".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    rewrite -Cinr_op in Hvalid. rewrite Cinr_valid in Hvalid.
    rewrite to_agree_op_valid_L in Hvalid. inversion_clear Hvalid.
    iDestruct (own_valid_2 with "H1' H3") as %Hvalid.
    rewrite mono_pg_auth_dfrac_op_valid in Hvalid.
    destruct Hvalid as [_ ->].
    done.
    iDestruct (own_valid_2 with "H1 H2") as "Hvalid".
    rewrite csum_validI /=. iExFalso;done.
  Qed.

  Lemma po_pred_interp_agree' gs {tid : Tid} pg ls e:
    po_pred_interp gs tid pg ls -∗
    e -{Po}> -∗
    ⌜EID.tid e = tid ∧ ThreadState.progress_of_node e <p pg
                        ∧ ThreadState.progress_is_valid (GlobalState.gs_graph gs) tid (ThreadState.progress_of_node e) ⌝.
  Proof.
    iIntros "[Hgr H1] H2". rewrite po_src_eq /po_src_def.
    iDestruct "H2" as "[[% [Hgr' %Hv]] [% [H2 H3]]]".
    iDestruct (graph_agree_agree with "Hgr Hgr'") as %<-.
    rewrite /po_pred_interp.
    destruct ls;simpl.
    iDestruct "H1" as "[% [H1 [H1' %H1'']]]".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    rewrite -Cinr_op in Hvalid. rewrite Cinr_valid in Hvalid.
    rewrite to_agree_op_valid_L in Hvalid.
    inversion Hvalid. subst gn0. clear Hvalid.
    iDestruct (own_valid_2 with "H1' H3") as %Hvalid.
    rewrite mono_pg_both_dfrac_valid in Hvalid.
    destruct Hvalid as [_ Hle].
    iPureIntro. destruct H1'' as [? []].
    split;[auto|].
    split;[|auto].
    - eapply progress_lt_trans'2. 2: eauto.
      destruct (progress_of_node e).
      destruct (progress_of_node _).
      rewrite /pg_le in Hle.
      destruct Hle. left;lia. right;lia.
    - rewrite /progress_is_valid.
      rewrite -H1 H3. rewrite progress_to_node_of_node //.
      rewrite /AACandExec.Candidate.valid_eid.
      destruct Hv.
      set_unfold. eexists;eauto.
    - iDestruct (own_valid_2 with "H1 H2") as "Hvalid".
      rewrite csum_validI /=. iExFalso;done.
  Qed.

  Lemma po_pred_interp_agree_big' gs {tid : Tid} pg ls s:
    po_pred_interp gs tid pg ls -∗
    ([∗ set] e ∈ s, e -{Po}>) -∗
    [∗ set] e ∈ s, ⌜EID.tid e = tid ∧ ThreadState.progress_of_node e <p pg
                        ∧ ThreadState.progress_is_valid (GlobalState.gs_graph gs) tid (ThreadState.progress_of_node e) ⌝.
  Proof.
    induction s using set_ind_L.
    - iIntros. done.
    - iIntros "H1 H2".
      rewrite !big_sepS_union. rewrite !big_sepS_singleton.
      iDestruct "H2" as "[H21 H22]".
      iDestruct (po_pred_interp_agree' with "H1 H21") as "#$".
      by iApply (IHs with "H1"). all: set_solver + H1.
  Qed.

  Lemma po_pred_interp_skip gs {tid : Tid} ts ts' ls :
    get_progress ts = get_progress ts' ->
    po_pred_interp gs tid (get_progress ts) ls -∗
    po_pred_interp gs tid (get_progress (incr_cntr ts')) ls.
  Proof.
    rewrite /po_pred_interp.
    iIntros (Heq) "[$ H]".
    destruct ls;last iFrame.
    simpl. iDestruct "H" as "[% (?&?&?&%&?)]".
    iExists _. iFrame. iSplit;first done.
    iSplit;last done.
    iPureIntro.
    eapply progress_lt_trans. eauto.
    rewrite Heq. apply progress_adjacent_incr_cntr'.
    rewrite progress_le_inv. right;done.
  Qed.

  Lemma po_pred_interp_skip' gs {tid : Tid} ts ts' ls :
    get_progress ts = get_progress ts' ->
    po_pred_interp gs tid (get_progress ts) ls -∗
    po_pred_interp gs tid (get_progress (reset_cntr ts')) ls.
  Proof.
    rewrite /po_pred_interp.
    iIntros (Heq) "[$ H]".
    destruct ls;last iFrame.
    simpl. iDestruct "H" as "[% (?&?&?&%&?)]".
    iExists _. iFrame. iSplit;first done.
    iSplit;last done.
    iPureIntro.
    eapply progress_lt_trans. eauto.
    rewrite Heq. left. simpl;lia.
  Qed.

  Lemma po_pred_interp_update gs {tid : Tid} ts ts' ls ls':
    get_progress ts = get_progress ts' ->
    progress_is_valid (GlobalState.gs_graph gs) tid (get_progress ts) ->
    po_pred_interp gs tid (get_progress ts) ls -∗
    ls' -{LPo}> ==∗
    po_pred_interp gs tid (get_progress (incr_cntr ts')) (Some (progress_to_node (get_progress ts) tid)) ∗
    Some (progress_to_node (get_progress ts) tid) -{LPo}>.
  Proof.
    iIntros (Heq Hv) "[Hgr H1] H2".
    rewrite lpo_src_eq /lpo_src_def.
    destruct ls';simpl.
    {
      iDestruct "H2" as "[[% [Hgr' ?]] [% [H2 H3]]]".
      iDestruct (graph_agree_agree with "Hgr Hgr'") as %<-.
      rewrite /po_pred_interp. destruct ls;simpl.
      iDestruct "H1" as "[% [H1 [H1' H1'']]]".
      iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
      rewrite -Cinr_op in Hvalid. rewrite Cinr_valid in Hvalid.
      rewrite to_agree_op_valid_L in Hvalid. inversion_clear Hvalid. iFrame.
      iDestruct (own_valid_2 with "H1' H3") as %Hvalid.
      rewrite mono_pg_auth_dfrac_op_valid in Hvalid.
      destruct Hvalid as [_ ->].
      iDestruct "H1''" as %Ht0. destruct Ht0 as [Htid [Hle ?]].
      iDestruct (own_update_2 _ _ _ (●MN (progress_of_node (progress_to_node (get_progress ts) tid))) with "H1' H3") as ">[H1' H3]".
      rewrite -mono_pg_auth_dfrac_op. rewrite dfrac_op_own.
      assert (1 / 2 + 1 / 2 = 1)%Qp as ->. apply (bool_decide_unpack _). by compute.
      apply mono_pg_update.
      destruct Hle as [|];simpl in *.
      left;simpl;lia. right;simpl;lia.
      iModIntro. rewrite progress_of_node_to_node. iSplitL "H1 H1'".
      iExists _. rewrite Htid. iSplitL "H1". iExact "H1". iFrame.
      iPureIntro. split;auto. split;auto. apply progress_adjacent_incr_cntr'.
      rewrite progress_le_inv;right;done.
      iSplitL "Hgr". iExists _. iSplitL. iFrame "Hgr".
      iPureIntro. rewrite /progress_is_valid in Hv.
      set_unfold. destruct Hv as [? [? _]]. eexists. eauto.
      iExists _. rewrite Htid. iFrame.
      iDestruct (own_valid_2 with "H1 H2") as "Hvalid".
      rewrite csum_validI /=. iExFalso;done.
    }
    {
      rewrite /po_pred_interp. destruct ls;simpl.
      {
        iDestruct "H1" as "[% [H1 [H1' H1'']]]".
        iDestruct (own_valid_2 with "H1 H2") as "Hvalid".
        rewrite csum_validI /=. iExFalso;done.
      }
      iDestruct (own_alloc (●MN (progress_of_node (progress_to_node (get_progress ts) tid)))) as ">[%gn [H3 H3']]".
      apply mono_pg_auth_valid.
      iDestruct (own_update_2 AAPoSrcN _ _ (Cinr ((to_agree ((gn, (tid : nat) ): (prodO gnameO natO) )  )) ) with "H1 H2") as ">H1".
      rewrite -Cinl_op. rewrite -dfrac_agree_op. rewrite dfrac_op_own.
      assert (1 / 2 + 1 / 2 = 1)%Qp as ->. apply (bool_decide_unpack _). by compute.
      apply cmra_update_exclusive.
      rewrite Cinr_valid. done.
      iModIntro. rewrite progress_of_node_to_node.
      iDestruct "Hgr" as "#?". iDestruct "H1" as "#?".
      iFrame "#". iSplitL "H3".
      iExists _. iSplitR. iFrame "#". iFrame "H3". iPureIntro. split;auto. split;auto. apply progress_adjacent_incr_cntr'.
      rewrite progress_le_inv;right;done.
      iSplitR. iExists _. iSplitL. iFrame "#".
      iPureIntro. rewrite /progress_is_valid in Hv.
      set_unfold. destruct Hv as [? [? _]]. eexists. eauto.
      iExists _. iSplitR. iFrame "#". done.
    }
  Qed.

  Lemma last_write_interp_agree_None {gs} {tid : Tid} pg ls addr:
    "Hinterp_local" ∷ last_write_interp gs tid pg ls -∗
    "Hlocal"  ∷ last_local_write tid addr None -∗
    ⌜ forall eid_w E_w , (gs.(GlobalState.gs_graph)) !! eid_w = Some E_w ->
                   AAConsistent.event_is_write_with_addr E_w addr ->
               (¬ (Graph.is_local_node_of tid eid_w)) ∨ (Graph.is_local_node_of tid eid_w) ∧ pg <=p ThreadState.progress_of_node eid_w ⌝.
  Proof.
    repeat iNamed 1.
    iDestruct "Hinterp_local" as "[%Hft_Some [%Hft_None Hauth]]".
    iCombine "Hauth Hlocal" gives %Hlk.
    iPureIntro. intros eid E Heid_lk Hw.
    destruct (decide (EID.tid eid = tid)) as [Htid|];[right|left; done].
    destruct (decide (pg <=p ThreadState.progress_of_node eid)) as [|Hnle];[done|exfalso].

    assert (ThreadState.progress_of_node eid <p pg) as Hlt.
    {
      destruct pg, (ThreadState.progress_of_node eid).
      apply Decidable.not_not. apply Decidable.dec_or; rewrite /Decidable.decidable; lia.
      intro.
      apply Decidable.not_or in Hnle.
      destruct Hnle;simpl in *.
      apply H1.
      destruct (decide (n = n1)).
      right. split;simpl;first lia.
      apply Decidable.not_and in H3.
      destruct H3;first done. lia.
      rewrite /Decidable.decidable; lia.
      left;simpl;lia.
    }
    clear Hnle. specialize (Hft_None addr Hlk eid E).
    feed specialize Hft_None.
    apply map_filter_lookup_Some.
    split;auto. rewrite AACandExec.Candidate.event_map_match //.
    split;[auto |split]. done.
    eapply AAConsistent.event_is_write_with_addr_elem_of_mem_writes;eauto.
    rewrite Hft_None //in Hw.
  Qed.

  Lemma last_write_interp_agree_Some {gs} {tid : Tid} {pg ls} addr eid_w:
    "Hinterp_local" ∷ last_write_interp gs tid pg ls -∗
    "Hlocal"  ∷ last_local_write tid addr (Some eid_w) -∗
    ⌜∃ E_w, (gs.(GlobalState.gs_graph)) !! eid_w = Some E_w ∧
    AAConsistent.event_is_write_with_addr E_w addr ∧
              (Graph.is_local_node_of tid eid_w) ∧ ThreadState.progress_of_node eid_w <p pg ∧
              ( ∀ eid_w' E_w', (gs.(GlobalState.gs_graph)) !! eid_w' = Some E_w' ->
                               AAConsistent.event_is_write_with_addr E_w' addr ->
                               (¬ (Graph.is_local_node_of tid eid_w') ∨
                                  (pg <=p ThreadState.progress_of_node eid_w' ∧ Graph.is_local_node_of tid eid_w') ∨
                                  (ThreadState.progress_of_node eid_w' <=p ThreadState.progress_of_node eid_w ∧ Graph.is_local_node_of tid eid_w')))⌝.
  Proof.
    repeat iNamed 1.
    iDestruct "Hinterp_local" as "[%Hft_Some [%Hft_None Hauth]]".
    iCombine "Hauth Hlocal" gives %Hlk. iPureIntro.
    rewrite Hft_Some in Hlk. destruct Hlk as (?&Hft&HW).
    apply map_filter_lookup_Some in Hft. destruct Hft as [Hft Hforall].
    apply map_filter_lookup_Some in Hft. destruct Hft as (?&?&?&?).
    repeat eexists;eauto. { rewrite -AACandExec.Candidate.event_map_match //. }
    intros eid_w' E_w' Hevent Hwrite.
    destruct (decide (EID.tid eid_w' = tid)) as [Htid|];[right|left; done].
    destruct (decide (pg <=p ThreadState.progress_of_node eid_w')) as [|Hnle]; [left;done|right].
    rewrite map_Forall_lookup in Hforall.
    split; [|done]. 
    apply (Hforall _ E_w').
    + apply map_filter_lookup_Some.
      rewrite AACandExec.Candidate.event_map_match.
      split; [done|].
      split; [done|].
      split.
      { by apply progress_nle_gt. }
      by eapply AAConsistent.event_is_write_with_addr_elem_of_mem_writes.
   +  eapply Graph.wf_loc_inv_writes2.
      exists addr, x, E_w'.
      split; [by rewrite -AACandExec.Candidate.event_map_match |].
      split; [done|].
      by split; [done|].
  Qed.

  Lemma last_write_interp_progress_write {gs ls} {tid : Tid} ts ts' addr ot :
    AACandExec.NMSWF.wf (gs.(GlobalState.gs_graph)) ->
    get_progress ts = get_progress ts' ->
    (exists E, gs.(GlobalState.gs_graph) !! progress_to_node (get_progress ts) tid = Some E ∧ AAConsistent.event_is_write_with_addr E addr) ->
    last_write_interp gs tid (get_progress ts) ls -∗
    last_local_write tid addr ot -∗
    |==>
      last_write_interp gs tid (get_progress (incr_cntr ts')) (<[addr := (Some (progress_to_node (get_progress ts) tid))]> ls) ∗
      last_local_write tid addr (Some (progress_to_node (get_progress ts) tid)).
  Proof.
    iIntros (Hwf Hpg HW) "HL Hl".
    destruct ot;simpl.
    - iDestruct (last_write_interp_agree_Some with "HL Hl") as %(?&?&?&?&?).
      iDestruct "HL" as "[%Hft_Some [%Hft_None Hauth]]".
      iCombine "Hauth Hl" gives %Hlk.
      iDestruct (ghost_map_update with "Hauth Hl") as ">[$ $]". iModIntro. iPureIntro.
      split.
      {
        intros.
        destruct (decide(addr = a)).
        {
          subst a. rewrite lookup_insert_Some.
          split.
          {
            intros [[_ Hinv]| []];last done. inversion Hinv;subst e. clear Hinv.
            destruct HW as [W [Hlk_w HW]].
            exists W. split;auto.
            rewrite map_filter_lookup_Some. split.
            rewrite map_filter_lookup_Some. split;auto.
            rewrite AACandExec.Candidate.event_map_match //.

            split;auto;split;auto.
            clear Hft_None.
            apply progress_adjacent_incr_cntr'.
            rewrite progress_le_inv. right. rewrite progress_of_node_to_node //.
            set_unfold.
            destruct W;destruct o;try inversion HW.
            eexists;eexists;eexists;eauto.
            intros ?? Hft.
            rewrite map_filter_lookup_Some in Hft.
            intro.
            destruct Hft as (?&?&Hlt&?).
            apply progress_adjacent_incr_cntr' in Hlt.
            rewrite progress_of_node_to_node. rewrite Hpg //.
          }
          {
            intros [W Hft].
            rewrite map_filter_lookup_Some in Hft. destruct Hft as [[Hft Hforall] HW'].
            rewrite map_filter_lookup_Some in Hft. destruct Hft as (?&?&Hlt&?).
            apply progress_adjacent_incr_cntr' in Hlt. rewrite progress_le_inv in Hlt.
            destruct Hlt as [|Hq].
            2:{
              left. split;auto. f_equal. rewrite Hpg -Hq. apply progress_to_node_of_node. done.
            }
            exfalso.
            destruct HW as [W' [Hlk' HW'']].
            specialize (Hforall (progress_to_node (get_progress ts') tid) W').
            feed specialize Hforall.
            apply map_filter_lookup_Some_2.
            rewrite AACandExec.Candidate.event_map_match.
            rewrite Hpg in Hlk'. done.
            split. rewrite -Hpg //.
            split. rewrite progress_of_node_to_node.
            apply progress_adjacent_incr_cntr'. rewrite progress_le_inv;right;done.
            rewrite -Hpg.
            set_unfold.

            destruct W';destruct o;try inversion HW''.
            simpl in HW''.
            eexists;eexists;eexists. eauto.
            eapply Graph.wf_loc_inv_writes2.
            repeat eexists. rewrite -AACandExec.Candidate.event_map_match. eauto.
            eauto. rewrite -Hpg. eauto. auto.
            rewrite progress_of_node_to_node in Hforall.
            eapply progress_le_gt_False;done.
          }
        }
        {
          rewrite lookup_insert_ne //. clear Hft_None.
          rewrite Hft_Some. clear Hft_Some.
          do 2 f_equiv.
          rewrite !map_filter_lookup_Some.
          {
            split; intros [[(Hlk_e & Htid & Hlt & Hin) Hforall] Haddr]; split;auto;split;auto.
            split;auto;split;auto;split;auto.
            - eapply progress_lt_trans;eauto. rewrite /incr_cntr;right.  do 2 destruct (get_progress _) eqn:?; simpl;inversion Hpg. lia.
            - intros i ? Hlk_i ?.
              rewrite map_filter_lookup_Some in Hlk_i.
              destruct Hlk_i as (Hlk_i & Htid' & Hlt' & Hw_i).
              specialize (Hforall i x0).
              feed specialize Hforall;auto.
              apply map_filter_lookup_Some.
              split;auto;split;auto; split;auto;eauto.
              eapply Graph.wf_loc_inv_writes in H5.
              2: assumption.
              2:{ exists a0. split. rewrite -AACandExec.Candidate.event_map_match //. exact Haddr. }
              destruct H5 as (?&Hlk_i'&[Hw_i'|?]).
              2:{ rewrite AACandExec.Candidate.event_map_match in Hlk_i.
                  rewrite Hlk_i in Hlk_i'. inversion Hlk_i';subst x1.
                  set_unfold. destruct Hw_i as [? [? [? ?]]].
                  rewrite Hlk_i in H6. inversion H6;subst.
                  destruct x; destruct o;simpl in H5; contradiction.
                }
              rewrite AACandExec.Candidate.event_map_match in Hlk_e.
              rewrite AACandExec.Candidate.event_map_match in Hlk_i.
              rewrite Hlk_i in Hlk_i'. inversion Hlk_i';subst x1.
              apply progress_adjacent_incr_cntr' in Hlt'. rewrite progress_le_inv in Hlt'.
              destruct Hlt' as [|Heq];[rewrite Hpg //|exfalso].

              assert (i = progress_to_node (get_progress ts) tid).
              {
                rewrite -Hpg in Heq. rewrite -Heq.
                rewrite progress_to_node_of_node //.
              }
              subst i.
              destruct HW as [? Hlk_w].
              rewrite Hlk_i in Hlk_w.
              destruct Hlk_w as [Heq' Haddr']. inversion Heq';subst x1.
              destruct x0;destruct o;auto.
              simpl in Hw_i'. simpl in Haddr'.
              rewrite Is_true_true in Haddr'. rewrite andb_true_iff in Haddr'. destruct Haddr' as [_ Haddr'].
              rewrite Is_true_true in Hw_i'. rewrite andb_true_iff in Hw_i'. destruct Hw_i' as [_ H8].
              case_bool_decide;last done.
              case_bool_decide;last done.
              rewrite H5 in H6. done.
            - split;auto;split;auto. split;auto.
              apply progress_adjacent_incr_cntr' in Hlt. rewrite progress_le_inv in Hlt.
              destruct Hlt as [|Heq];[rewrite Hpg //|exfalso].

              assert (e = progress_to_node (get_progress ts) tid).
              {
                rewrite -Hpg in Heq. rewrite -Heq.
                rewrite progress_to_node_of_node //.
              }
              subst e.
              (* cannot be on the same address *)
              destruct HW as [? Hlk_w].
              rewrite AACandExec.Candidate.event_map_match in Hlk_e.
              rewrite Hlk_e in Hlk_w.
              destruct Hlk_w as [Heq' Haddr']. inversion Heq';subst.
              destruct x0;destruct o;auto. simpl in Haddr. simpl in Haddr'.
              rewrite Is_true_true in Haddr'. rewrite andb_true_iff in Haddr'. destruct Haddr' as [_ Haddr'].
              rewrite Is_true_true in Haddr. rewrite andb_true_iff in Haddr. destruct Haddr as [_ Haddr].
              case_bool_decide;last done.
              case_bool_decide;last done. rewrite H5 // in H6.
            - intros i ? Hlk_i ?.
              rewrite map_filter_lookup_Some in Hlk_i.
              destruct Hlk_i as [Hlk_i [Htid' [Hlt' Hw_i]]].
              specialize (Hforall i x0).
              feed specialize Hforall;auto.
              apply map_filter_lookup_Some.
              split;auto;split;auto; split;auto.
              eapply progress_lt_trans;eauto.
              apply progress_adjacent_incr_cntr'. rewrite progress_le_inv;right;done.
          }
        }
      }
      {
        intro.
        destruct (decide(addr = a)).
        {
          subst a. rewrite lookup_insert_Some.
          intros [[_ Hinv]|[]];[inversion Hinv|done].
        }
        {
          rewrite lookup_insert_ne //.
          intro HHlk. specialize (Hft_None a HHlk).
          clear Hft_Some.

          intros i ? Hlk_i.
          rewrite map_filter_lookup_Some in Hlk_i.
          destruct Hlk_i as [Hlk_i [Htid' [Hlt' Hw_i]]].

          apply progress_adjacent_incr_cntr' in Hlt'. rewrite progress_le_inv in Hlt'.
          destruct Hlt' as [|Heq];[|].
          eapply (Hft_None i).
          rewrite map_filter_lookup_Some.
          split;auto; split;auto; split;auto.
          rewrite Hpg //.
          (* cannot on same address *)
          assert (i = progress_to_node (get_progress ts) tid).
          {
            rewrite -Hpg in Heq. rewrite -Heq.
            rewrite progress_to_node_of_node //.
          }
          subst i.

          destruct HW as [? Hlk_w].
          rewrite AACandExec.Candidate.event_map_match in Hlk_i.
          rewrite Hlk_i in Hlk_w.
          destruct Hlk_w as [Heq' Haddr']. inversion Heq';subst.
          destruct x1;destruct o;auto. simpl in Haddr'.
          rewrite Is_true_true in Haddr'. rewrite andb_true_iff in Haddr'. destruct Haddr' as [_ Haddr'].
          case_bool_decide;last done. simpl.
          rewrite H5.
          case_bool_decide. done. apply andb_false_r.
        }
      }
    (* ot = None *)
    - destruct HW as [W [Hlk_w HW]].
      iDestruct (last_write_interp_agree_None with "HL Hl") as %[Htid|_];eauto.
      { (* in another thread *)
        iDestruct "HL" as "[%Hft_Some [%Hft_None Hauth]]".
        iCombine "Hauth Hl" gives %Hlk.
        iDestruct (ghost_map_update with "Hauth Hl") as ">[$ $]". iModIntro. iPureIntro.
        simpl in Htid. done.
      }
      { (* in same thread, but later *)
        iDestruct "HL" as "[%Hft_Some [%Hft_None Hauth]]".
        iCombine "Hauth Hl" gives %Hlk.
        iDestruct (ghost_map_update with "Hauth Hl") as ">[$ $]". iModIntro. iPureIntro.

      split.
      {
        intros.
        destruct (decide(addr = a)).
        {
          subst a. rewrite lookup_insert_Some.
          split.
          {
            intros [[_ Hinv]| []];last done. inversion Hinv;subst e. clear Hinv.
            exists W. split;auto.
            rewrite map_filter_lookup_Some. split.
            rewrite map_filter_lookup_Some. split;auto.
            rewrite AACandExec.Candidate.event_map_match //.

            split;auto;split;auto.
            clear Hft_None.
            apply progress_adjacent_incr_cntr'.
            rewrite progress_le_inv. right. rewrite progress_of_node_to_node //.
            set_unfold. destruct W;destruct o;try inversion HW.
            simpl in HW. rewrite Is_true_true in HW. rewrite andb_true_iff in HW. destruct HW as [? _].
            eexists;eexists;eexists. eassumption.
            intros ?? Hft.
            rewrite map_filter_lookup_Some in Hft.
            intro.
            destruct Hft as (?&?&Hlt&?).
            apply progress_adjacent_incr_cntr' in Hlt.
            rewrite progress_of_node_to_node. rewrite Hpg //.
          }
          { intros [W' Hft].
            rewrite map_filter_lookup_Some in Hft. destruct Hft as [[Hft Hforall] HW'].
            rewrite map_filter_lookup_Some in Hft. destruct Hft as (?&?&Hlt&?).
            apply progress_adjacent_incr_cntr' in Hlt. rewrite progress_le_inv in Hlt.
            destruct Hlt as [|Hq].
            2:{
              left. split;auto. f_equal. rewrite Hpg -Hq. apply progress_to_node_of_node. done.
            }
            exfalso.
            specialize (Hforall (progress_to_node (get_progress ts') tid) W).
            feed specialize Hforall.
            apply map_filter_lookup_Some_2.
            rewrite AACandExec.Candidate.event_map_match.
            rewrite Hpg in Hlk_w. done.
            split. rewrite -Hpg //.
            split. rewrite progress_of_node_to_node.
            apply progress_adjacent_incr_cntr'. rewrite progress_le_inv;right;done.
            rewrite -Hpg.
            set_unfold. destruct W;destruct o;try inversion HW.
            simpl in HW. rewrite Is_true_true in HW. rewrite andb_true_iff in HW. destruct HW as [? _].
            eexists;eexists;eexists. eassumption.
            eapply Graph.wf_loc_inv_writes2.
            repeat eexists. rewrite -AACandExec.Candidate.event_map_match. eauto.
            eauto. rewrite -Hpg. eauto. auto.
            rewrite progress_of_node_to_node in Hforall.
            eapply progress_le_gt_False;done.
          }
        }
        { rewrite lookup_insert_ne //. clear Hft_None.
          rewrite Hft_Some. clear Hft_Some.
          do 2 f_equiv.
          rewrite !map_filter_lookup_Some.
          {
            split; intros [[(Hlk_e & Htid & Hlt & Hin) Hforall] Haddr]; split;auto;split;auto.
            split;auto;split;auto;split;auto.
            - eapply progress_lt_trans;eauto. rewrite /incr_cntr;right.  do 2 destruct (get_progress _) eqn:?; simpl;inversion Hpg. lia.
            - intros i ? Hlk_i ?.
              rewrite map_filter_lookup_Some in Hlk_i.
              destruct Hlk_i as (Hlk_i & Htid' & Hlt' & Hw_i).
              specialize (Hforall i x).
              feed specialize Hforall;auto.
              apply map_filter_lookup_Some.
              split;auto;split;auto; split;auto.
              eapply Graph.wf_loc_inv_writes in H1.
              2: assumption.
              2:{ exists a0. split. rewrite -AACandExec.Candidate.event_map_match //. exact Haddr. }
              destruct H1 as (?&Hlk_i'&[Hw_i'|?]).
              2:{ rewrite AACandExec.Candidate.event_map_match in Hlk_i.
                  rewrite Hlk_i in Hlk_i'. inversion Hlk_i';subst x0.
                  set_unfold. destruct Hw_i as [? [? [? ?]]].
                  rewrite Hlk_i in H2. inversion H2;subst.
                  destruct a0; destruct o;simpl in H1; contradiction.
                }
              rewrite AACandExec.Candidate.event_map_match in Hlk_e.
              rewrite AACandExec.Candidate.event_map_match in Hlk_i.
              rewrite Hlk_i in Hlk_i'. inversion Hlk_i';subst x0.
              apply progress_adjacent_incr_cntr' in Hlt'. rewrite progress_le_inv in Hlt'.
              destruct Hlt' as [|Heq];[rewrite Hpg //|exfalso].

              assert (i = progress_to_node (get_progress ts) tid).
              {
                rewrite -Hpg in Heq. rewrite -Heq.
                rewrite progress_to_node_of_node //.
              }
              subst i.
              rewrite Hlk_i in Hlk_w.
              inversion Hlk_w;subst x.
              destruct W;destruct o;auto.
              simpl in Hw_i'. simpl in HW.
              rewrite Is_true_true in HW. rewrite andb_true_iff in HW. destruct HW as [_ HW].
              rewrite Is_true_true in Hw_i'. rewrite andb_true_iff in Hw_i'. destruct Hw_i' as [_ H4].
              case_bool_decide;last done.
              case_bool_decide;last done.
              rewrite H1 in H2. done.
            - split;auto;split;auto. split;auto.
              apply progress_adjacent_incr_cntr' in Hlt. rewrite progress_le_inv in Hlt.
              destruct Hlt as [|Heq];[rewrite Hpg //|exfalso].

              assert (e = progress_to_node (get_progress ts) tid).
              {
                rewrite -Hpg in Heq. rewrite -Heq.
                rewrite progress_to_node_of_node //.
              }
              subst e.
              (* cannot be on the same address *)
              rewrite AACandExec.Candidate.event_map_match in Hlk_e.
              rewrite Hlk_e in Hlk_w.
              inversion Hlk_w ;subst.
              destruct W;destruct o;auto. simpl in Haddr. simpl in HW.
              rewrite Is_true_true in HW. rewrite andb_true_iff in HW. destruct HW as [_ HW].
              rewrite Is_true_true in Haddr. rewrite andb_true_iff in Haddr. destruct Haddr as [_ Haddr].
              case_bool_decide;last done.
              case_bool_decide;last done. rewrite H1 // in H2.
            - intros i ? Hlk_i ?.
              rewrite map_filter_lookup_Some in Hlk_i.
              destruct Hlk_i as [Hlk_i [Htid' [Hlt' Hw_i]]].
              specialize (Hforall i x).
              feed specialize Hforall;auto.
              apply map_filter_lookup_Some.
              split;auto;split;auto; split;auto.
              eapply progress_lt_trans;eauto.
              apply progress_adjacent_incr_cntr'. rewrite progress_le_inv;right;done.
          }
        }
      }
      {
        intro.
        destruct (decide(addr = a)).
        {
          subst a. rewrite lookup_insert_Some.
          intros [[_ Hinv]|[]];[inversion Hinv|done].
        }
        { rewrite lookup_insert_ne //. intros HHlk.
          specialize (Hft_None a HHlk).

          clear Hft_Some.
          intros i ? Hlk_i.
          rewrite map_filter_lookup_Some in Hlk_i.
          destruct Hlk_i as [Hlk_i [Htid' [Hlt' Hw_i]]].

          apply progress_adjacent_incr_cntr' in Hlt'. rewrite progress_le_inv in Hlt'.
          destruct Hlt' as [|Heq];[|].
          eapply (Hft_None i).
          rewrite map_filter_lookup_Some.
          split;auto; split;auto; split;auto.
          rewrite Hpg //.
          (* cannot on same address *)
          assert (i = progress_to_node (get_progress ts) tid).
          {
            rewrite -Hpg in Heq. rewrite -Heq.
            rewrite progress_to_node_of_node //.
          }
          subst i.
          rewrite AACandExec.Candidate.event_map_match in Hlk_i.
          rewrite Hlk_i in Hlk_w.
          inversion Hlk_w;subst.
          destruct W;destruct o;auto. simpl in HW.
          rewrite Is_true_true in HW. rewrite andb_true_iff in HW. destruct HW as [_ HW].
          case_bool_decide;last done. simpl.
          rewrite H1.
          case_bool_decide; first done. apply andb_false_r.
        }
      }
      }
  Qed.

  Lemma last_write_interp_progress_non_write {gs ls} {tid : Tid} ts ts' :
    get_progress ts = get_progress ts' ->
    (progress_to_node (get_progress ts) tid) ∉ AACandExec.Candidate.mem_writes gs.(GlobalState.gs_graph) ->
    last_write_interp gs tid (get_progress ts) ls -∗
    last_write_interp gs tid (get_progress (incr_cntr ts')) ls.
  Proof.
    iIntros (Hpg Hnw) "[%Hft_Some [%Hft_None $]]". iPureIntro.
    assert (Hequiv:forall i, EID.tid i = tid ∧ progress_of_node i <p get_progress ts ∧ i ∈ AACandExec.Candidate.mem_writes (GlobalState.gs_graph gs)
                        ↔ EID.tid i = tid ∧ progress_of_node i <p get_progress (incr_cntr ts') ∧ i ∈ AACandExec.Candidate.mem_writes (GlobalState.gs_graph gs)).
    { intro e.
      split;intros [Hitd [Hlt Hin]]; split;auto;split;auto.
      - eapply progress_lt_trans;eauto. rewrite /incr_cntr;right.  do 2 destruct (get_progress _) eqn:?; simpl;inversion Hpg. lia.
      - apply progress_adjacent_incr_cntr' in Hlt. rewrite progress_le_inv in Hlt.
        destruct Hlt as [|Heq];[rewrite Hpg //|exfalso].

        assert (e = progress_to_node (get_progress ts) tid).
        {
          rewrite -Hpg in Heq. rewrite -Heq.
          rewrite progress_to_node_of_node //.
        }
        subst e.  done.
    }
    split; intros.
    {
      rewrite Hft_Some. do 3 f_equiv.
      rewrite !map_filter_lookup_Some. do 2 f_equiv.
      apply Hequiv.
      apply map_filter_ext. intros.
      apply Hequiv.
    }
    {
      specialize (Hft_None a H1).
      intros ???. specialize (Hft_None i x). feed specialize Hft_None.
      rewrite -H2. f_equiv. apply map_filter_ext. intros.
      apply Hequiv. done.
    }
  Qed.

  Lemma last_write_interp_progress_non_write' {gs ls} {tid : Tid} ts ts' :
    get_progress ts = get_progress ts' ->
    ts_is_done_instr (gs.(GlobalState.gs_graph)) tid ts ->
    last_write_interp gs tid (get_progress ts) ls -∗
    last_write_interp gs tid (get_progress (reset_cntr ts')) ls.
  Proof.
    iIntros (Hpg Hnw) "[%Hft_Some [%Hft_None $]]". iPureIntro.
    (* this proof is different, the rest is identical *)
    assert (Hequiv: forall i, EID.tid i = tid ∧ progress_of_node i <p get_progress ts ∧ i ∈ AACandExec.Candidate.mem_writes (GlobalState.gs_graph gs)
                        ↔ EID.tid i = tid ∧ progress_of_node i <p get_progress (reset_cntr ts') ∧ i ∈ AACandExec.Candidate.mem_writes (GlobalState.gs_graph gs)).
    {
      split;intros [Hitd [Hlt Hin]]; split;auto;split;auto.
      - eapply progress_lt_trans;eauto. rewrite /reset_cntr;left. do 2 destruct (get_progress _) eqn:?; simpl;inversion Hpg. lia.
      - rewrite /reset_cntr /get_progress /= in Hlt.
        assert (EID.iid i <= iis_iid (ts_iis ts'))%nat.
        {
          destruct Hlt; simpl in H1. lia.
          destruct H1;lia.
        }
        rewrite Hpg. Nat.le_elim H1.
        left. simpl;lia.
        specialize (Hnw i). feed specialize Hnw.
        apply elem_of_filter. split;auto.
        case_bool_decide;case_bool_decide;auto. rewrite Hpg in H3. done.
        set_solver.
        rewrite -Hpg //.
    }
    split; intros.
    {
      rewrite Hft_Some. do 3 f_equiv.
      rewrite !map_filter_lookup_Some. do 2 f_equiv.
      apply Hequiv.
      apply map_filter_ext. intros.
      apply Hequiv.
    }
    {
      specialize (Hft_None a H1).
      intros ???. specialize (Hft_None i x). feed specialize Hft_None.
      rewrite -H2. f_equiv. apply map_filter_ext. intros.
      apply Hequiv. done.
    }
  Qed.

End lemma.

(* User-level protocol, user need to provide an instance *)
Class UserProt `{CMRA Σ} := {
  prot : prot_t Σ;
}.

(* We provide a default implementation of [UserProt -> Protocol] *)
#[global] Instance user_prot_to_prot `{CMRA Σ} `{!AABaseG} `{!UserProt} : Protocol :=
  Build_Protocol _ _ (λ e,
  ∀ kind_s kind_v addr val, e -{E}> (Event.W kind_s kind_v addr val) -∗
    prot addr val e)%I.

(* The final CMRA typeclass to be assumed *)
Class AAIrisG `{CMRA Σ} `{aairis_inv : !invGS_gen HasNoLc Σ} `{aairis_base : !AABaseG}:= {}.

(* Instantiation of low-level logic *)
#[global] Instance instantiation_irisG `{AAIrisG} : irisG := {
    annot_interp := my_annot_interp;
    gconst_interp := global_interp;
  }.

#[global] Instance instantiation_irisGL `{AAIrisG} `{!ThreadGNL} : irisGL := {
    local_interp := my_local_interp;
  }.
