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

(** This file contains the instantiation for the logical (ghost) state *)
From iris_named_props Require Export named_props.
From iris.bi Require Import derived_laws.

From self.lang Require Import mm opsem.
From self.algebra Require Export base.
From self.low Require Export edge event iris interp_mod.

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
  Record LogicalLocalState := mk_lls {
      lls_lws : gmap Addr (option Eid);
      lls_pop : option Eid;
    }.

  #[global] Instance eta : Settable _ := settable! mk_lls <lls_lws; lls_pop>.

  Context `{!ThreadGNL}.

  Definition current_local_writes gr tid pg : gmap Eid iEvent :=
      filter (λ '(e, _), (Graph.is_local_node_of tid) e
        ∧ ThreadState.progress_of_node e <p pg
        ∧ e ∈ AACandExec.Candidate.mem_writes gr)
      (AACandExec.Candidate.event_map gr).

  #[local] Lemma current_local_writes_lookup_unfold gr tid pg eid E:
    (current_local_writes gr tid pg !! eid = Some E) <->
      (gr !! eid = Some E ∧ (Graph.is_local_node_of tid) eid
       ∧ ThreadState.progress_of_node eid <p pg
       ∧ eid ∈ AACandExec.Candidate.mem_writes gr).
  Proof.
    unfold current_local_writes.
    rewrite map_lookup_filter_Some.
    f_equiv.
    rewrite Candidate.event_map_match //.
  Qed.


  Definition no_current_local_writes (ls : gmap Addr (option Eid)) gr tid pg :=
    ∀ (a : Addr), ls !! a = Some None
      -> (map_Forall (λ e E, (AAConsistent.event_is_write_with_addr E a = false)) (current_local_writes gr tid pg)).

  Definition last_local_writes gr tid pg:=
    let local_writes := (current_local_writes gr tid pg) in
      filter (λ '(e, _), map_Forall
                    (λ e' _, (e, e') ∈ AACandExec.Candidate.loc gr ->
                        ThreadState.progress_of_node e' <=p ThreadState.progress_of_node e)
                    local_writes) local_writes.

  #[local] Lemma last_local_writes_lookup_unfold gr tid pg eid E:
    (last_local_writes gr tid pg !! eid = Some E) <->
      (current_local_writes gr tid pg !! eid = Some E ∧
       forall eid' E', (gr !! eid' = Some E' ∧ eid' ∈ AACandExec.Candidate.mem_writes gr ∧
                  (eid, eid') ∈ AACandExec.Candidate.loc gr ∧ (Graph.is_local_node_of tid) eid' ∧
                  ThreadState.progress_of_node eid' <p pg)
                  -> ThreadState.progress_of_node eid' <=p ThreadState.progress_of_node eid
      ).
  Proof.
    unfold last_local_writes.
    rewrite map_lookup_filter_Some.
    f_equiv.
    unfold map_Forall.
    split;intros Hh;intros ??.
    - intros (?&?&?&?&?).
      eapply Hh;last assumption. rewrite current_local_writes_lookup_unfold.
      repeat (split;first eassumption). assumption.
    - rewrite current_local_writes_lookup_unfold.
      intros (?&?&?&?) ?.
      eapply Hh.
      repeat (split;first eassumption). assumption.
  Qed.

  Definition are_last_local_writes (ls : gmap Addr (option Eid)) gr tid pg :=
                ∀ (a : Addr) (e : Eid), ls !! a = Some (Some e)
      <-> (∃ E, (last_local_writes gr tid pg) !! e = Some E ∧ AAConsistent.event_is_write_with_addr E a).

  Definition last_write_interp (gs : GlobalState.t) (tid : Tid) (pg : ThreadState.progress)
    (ls : gmap Addr (option Eid)) : iProp Σ :=
    let gr := gs.(GlobalState.gs_graph) in
    let local_writes :=
      filter (λ '(e, _), (Graph.is_local_node_of tid) e
        ∧ ThreadState.progress_of_node e <p pg
        ∧ e ∈ AACandExec.Candidate.mem_writes gr)
      (AACandExec.Candidate.event_map gr) in
    let last_local_writes :=
      filter (λ '(e, _), map_Forall
                    (λ e' _, (e, e') ∈ AACandExec.Candidate.loc gr ->
                        ThreadState.progress_of_node e' <=p ThreadState.progress_of_node e)
                    local_writes) local_writes in
    ⌜are_last_local_writes ls gr tid pg ⌝ ∗
    ⌜ no_current_local_writes ls gr tid pg ⌝ ∗
    ghost_map_auth AALocalMapN 1%Qp ls.

  Definition lpo_src_def o_eid :=
    from_option (λ eid,
                   ((∃ gr, graph_agree gr ∗ ⌜is_Some (gr !! eid)⌝) ∗
                     ∃ gn, own AAPoSrcN (Cinr (to_agree (gn, (EID.tid eid)))) ∗
                           own gn (●MN{DfracOwn (1/2)%Qp} (ThreadState.progress_of_node eid))
                   )%I) ((own AAPoSrcN (Cinl (to_dfrac_agree (DfracOwn (1/2)%Qp) ())))%I) o_eid.

  Definition po_src_def eid :=
    ((∃ gr, graph_agree gr ∗ ⌜is_Some (gr !! eid)⌝) ∗
      ∃ gn, own AAPoSrcN (Cinr (to_agree (gn, (EID.tid eid)))) ∗
            own gn (◯MN (ThreadState.progress_of_node eid)))%I.

  Definition po_pred_interp (gs : GlobalState.t) (tid : Tid) (pg : ThreadState.progress)
    (ls : option Eid) : iProp Σ :=
    let gr := gs.(GlobalState.gs_graph) in
    graph_agree gr ∗
    from_option
      (λ e',
         ∃ gn, own AAPoSrcN (Cinr (to_agree (gn, (EID.tid e')) )) ∗
               own gn (●MN{DfracOwn (1/2)%Qp} (ThreadState.progress_of_node e')) ∗
               ⌜ EID.tid e' = tid ∧ ThreadState.progress_of_node e' <p pg ∧
               ThreadState.progress_is_valid (GlobalState.gs_graph gs) tid (ThreadState.progress_of_node e') ⌝
      )%I (own AAPoSrcN (Cinl (to_dfrac_agree (DfracOwn (1/2)%Qp) ())) )%I ls.


  Definition my_local_interp (gs : GlobalState.t) (tid : Tid) (pg : ThreadState.progress)
    (ls : LogicalLocalState) :=
    ("Hinterp_local_lws" ∷ last_write_interp gs tid pg (ls.(lls_lws)) ∗
    "Hinterp_po_src" ∷ po_pred_interp gs tid pg (ls.(lls_pop)))%I.

End interp.

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

Definition last_local_write `{CMRA Σ} `{!AABaseG} `{!ThreadGNL} (tid : Tid) (addr : Addr)
  (w : option Eid) : iProp Σ :=
  addr ↪[AALocalMapN]{DfracOwn 1} w.

Lemma my_local_interp_alloc `{CMRA Σ} `{!AABaseG} gs pg (i:Tid) locs:
  ThreadState.progress_is_init (GlobalState.gs_graph gs) i pg ->
  graph_agree (gs.(GlobalState.gs_graph)) ⊢ |==> ∃ `(!ThreadGNL),
    my_local_interp gs i pg (mk_lls (gset_to_gmap None locs) None) ∗
    ([∗ set] k ∈ locs, k ↪[AALocalMapN] None) ∗
    None -{LPo}>.
Proof.
  iIntros (Hinit). rewrite /my_local_interp. iIntros "?".
  iDestruct (ghost_map_alloc (gset_to_gmap None locs)) as ">[%g1 [? ?]]".
  rewrite /po_pred_interp /=. rewrite lpo_src_eq.
  iDestruct (own_alloc ((Cinl (to_dfrac_agree (DfracOwn (1/2)%Qp) ())) ⋅
                        (Cinl (to_dfrac_agree (DfracOwn (1/2)%Qp) ())))) as ">[%g2 H]". done.
  iExists (Build_ThreadGNL g1 g2).
  rewrite own_op. iDestruct "H" as "[$ $]". iFrame.
  iModIntro. rewrite big_sepM_gset_to_gmap. iFrame.
  iPureIntro. split.
  {
    intros. split.
    intros Hlk. rewrite lookup_gset_to_gmap_Some /= in Hlk. destruct Hlk;done.
    intros [? [Hlk ?]]. exfalso. rewrite map_lookup_filter_Some in Hlk.
    destruct Hlk as [Hlk ?].
    rewrite map_lookup_filter_Some in Hlk.
    destruct Hlk as (?&?&?&?).
    rewrite /ThreadState.progress_is_init in Hinit.
    specialize (Hinit e). ospecialize* Hinit.
    apply elem_of_filter. split;auto.
    set_unfold. eexists;eauto. split;eauto.
    rewrite -AACandExec.Candidate.event_map_match //.
    simpl in Hinit. eapply ThreadState.progress_le_gt_False;eauto.
  }
  {
    intro. rewrite lookup_gset_to_gmap_Some.
    intros _. intros e E Hfilter.
    rewrite map_lookup_filter_Some in Hfilter.
    rewrite /ThreadState.progress_is_init in Hinit.
    destruct Hfilter as [? [? [? ?]]].
    specialize (Hinit e). ospecialize* Hinit.
    apply elem_of_filter. split;auto.
    set_unfold. eexists;eauto. split;eauto.
    rewrite -AACandExec.Candidate.event_map_match //.
    simpl in Hinit. exfalso. eapply ThreadState.progress_le_gt_False;eauto.
  }
Qed.


Section lemma.
  Import ThreadState.
  Context `{CMRA Σ}.
  Context `{!AABaseG}.
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

  #[global] Instance persistent_po_src `{CMRA Σ} `{!AABaseG} `{!ThreadGNL} eid :
    Persistent (eid -{Po}>).
  Proof. rewrite po_src_eq /po_src_def. apply _. Qed.

  Lemma po_pred_interp_agree gs {tid : Tid} pg ls o_e:
    po_pred_interp gs tid pg ls -∗
    o_e -{LPo}> -∗
    ⌜ from_option
      (λ e, EID.tid e = tid ∧
            ThreadState.progress_of_node e <p pg ∧
            ThreadState.progress_is_valid (GlobalState.gs_graph gs)
              tid (ThreadState.progress_of_node e)) True o_e⌝.
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
    ⌜EID.tid e = tid ∧
    ThreadState.progress_of_node e <p pg ∧
    ThreadState.progress_is_valid (GlobalState.gs_graph gs) tid (ThreadState.progress_of_node e) ⌝.
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
    [∗ set] e ∈ s, ⌜EID.tid e = tid ∧
                   ThreadState.progress_of_node e <p pg ∧
                   ThreadState.progress_is_valid (GlobalState.gs_graph gs) tid
                     (ThreadState.progress_of_node e) ⌝.
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
      iModIntro. rewrite progress_of_node_to_node.
      iFrame.
      rewrite Htid. iFrame.
      iPureIntro. split;auto. split;auto. split;auto. apply progress_adjacent_incr_cntr'.
      rewrite progress_le_inv;right;done.
      rewrite /progress_is_valid in H1.
      rewrite /progress_is_valid in Hv.
      set_unfold. destruct Hv as [? [? _]]. eexists. eauto.
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
       iFrame "H3". iPureIntro. split;auto. split;auto. apply progress_adjacent_incr_cntr'.
      rewrite progress_le_inv;right;done.
      iSplitR. rewrite /progress_is_valid in Hv.
      iPureIntro.
      set_unfold in Hv. destruct Hv as [? [? _]]. eexists; exact H1.
      done.
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
    ospecialize* Hft_None.
    apply map_lookup_filter_Some.
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
    apply map_lookup_filter_Some in Hft. destruct Hft as [Hft Hforall].
    apply map_lookup_filter_Some in Hft. destruct Hft as (?&?&?&?).
    repeat eexists;eauto. { rewrite -AACandExec.Candidate.event_map_match //. }
    intros eid_w' E_w' Hevent Hwrite.
    destruct (decide (EID.tid eid_w' = tid)) as [Htid|];[right|left; done].
    destruct (decide (pg <=p ThreadState.progress_of_node eid_w')) as [|Hnle]; [left;done|right].
    rewrite map_Forall_lookup in Hforall.
    split; [|done].
    apply (Hforall _ E_w').
    + apply map_lookup_filter_Some.
      rewrite AACandExec.Candidate.event_map_match.
      split; [done|].
      split; [done|].
      split.
      { by apply progress_nle_gt. }
      by eapply AAConsistent.event_is_write_with_addr_elem_of_mem_writes.
    + eapply Graph.wf_loc_inv_writes2.
      exists addr, x, E_w'.
      split; [by rewrite -AACandExec.Candidate.event_map_match |].
      split; [done|].
      by split; [done|].
  Qed.

  #[local] Lemma is_mem_writes_helper gr eid E addr:
    gr !! eid = Some E ->
    AAConsistent.event_is_write_with_addr E addr ->
    eid ∈ AACandExec.Candidate.mem_writes gr.
  Proof.
    intros ? HW.
    set_unfold.
    destruct E;destruct o;try inversion HW.
    eexists;eexists;eexists;eauto.
  Qed.

  #[local] Lemma step_is_last_write tid ts addr e W W' gr:
  gr !! progress_to_node (get_progress ts) tid = Some W ->
  AAConsistent.event_is_write_with_addr W addr ->
  last_local_writes gr tid (get_progress (incr_cntr ts)) !! e = Some W' ->
  AAConsistent.event_is_write_with_addr W' addr ->
  (progress_to_node (get_progress ts) tid) = e.
  Proof.
    intros Hlk HW Hlk_l HW'.
    rewrite last_local_writes_lookup_unfold current_local_writes_lookup_unfold in Hlk_l.
    destruct Hlk_l as [(?&?&Hlt&?) Hforall].
    apply progress_adjacent_incr_cntr' in Hlt. rewrite progress_le_inv in Hlt.
    destruct Hlt as [|Hq].
    2:{ rewrite  -Hq. apply progress_to_node_of_node. done. }
    exfalso.

    specialize (Hforall (progress_to_node (get_progress ts) tid) W). ospecialize* Hforall.
    split. assumption.
    split. eapply is_mem_writes_helper; eassumption.
    split. eapply Graph.wf_loc_inv_writes2.
    repeat eexists;try eassumption.
    split. cbn. reflexivity.
    rewrite progress_of_node_to_node.
    apply progress_adjacent_incr_cntr'. rewrite progress_le_inv;right;done.

    rewrite progress_of_node_to_node in Hforall.
    eapply progress_le_gt_False;done.
  Qed.

  #[local] Lemma last_local_writes_lookup_ne_Some gr tid ts e addr addr' E ls:
    AACandExec.NMSWF.wf gr ->
    gr !! progress_to_node (get_progress ts) tid = Some E ->
    AAConsistent.event_is_write_with_addr E addr ->
    are_last_local_writes ls gr tid (get_progress ts) ->
    addr ≠ addr' ->
    ls !! addr' = Some (Some e)
    ↔ (∃ E : Event,
          last_local_writes gr tid (get_progress (incr_cntr ts)) !! e = Some E
          ∧ AAConsistent.event_is_write_with_addr E addr').
  Proof.
    assert (HsameEaddr: forall eid E E' a a',
              gr !! eid = Some E ->
              AAConsistent.event_is_write_with_addr E a ->
              gr !! eid = Some E' ->
              AAConsistent.event_is_write_with_addr E' a' ->
              E = E' ∧ a = a').
    {
      clear.
      intros ????? Hlk_i Haddr Hlk_w Haddr'.
      rewrite Hlk_i in Hlk_w.
      inversion Hlk_w; subst.
      destruct E';destruct o;try contradiction.
      simpl in *.
      rewrite Is_true_true in Haddr Haddr'.
      split;first done.
      rewrite andb_true_iff in Haddr Haddr'.
      destruct Haddr as [_ Haddr].
      rewrite Is_true_true in Haddr'.
      rewrite andb_true_iff in Haddr'.
      destruct Haddr' as [_ Haddr'].
      case_bool_decide; last congruence.
      case_bool_decide; last congruence.
      subst. congruence.
    }
    intros Hwf Hlk HE Hft_Some Hneq.
    rewrite Hft_Some. clear Hft_Some.
    do 2 f_equiv.
    rewrite 2!last_local_writes_lookup_unfold.
    rewrite 2!current_local_writes_lookup_unfold.
      split; intros [[(Hlk_e & Htid & Hlt & Hin) Hforall] Haddr]; repeat (split;try assumption).
      -
        apply progress_adjacent_incr_cntr'.
        apply progress_le_inv. left;assumption.
      - intros i ? (Hlk_i & Hw_i & Hloc' &Htid'  & Hlt' ).
        specialize (Hforall i E').
        ospecialize* Hforall; try eassumption.
        repeat (split;try assumption).
        eapply Graph.wf_loc_inv_writes in Hloc'.
        2: assumption.
        2:{ eexists. split. eassumption. exact Haddr. }
        destruct Hloc' as (?&Hlk_i'&[Hw_i'|?]).
        2:{
          rewrite Hlk_i in Hlk_i'. inversion Hlk_i';subst.
          set_unfold. rewrite Hlk_i in Hw_i.
          destruct Hw_i as [? [? [? ?]]].
          inversion H2;subst. simpl in H1. contradiction.
        }
        rewrite Hlk_i in Hlk_i'. inversion Hlk_i'; subst E'.
        apply progress_adjacent_incr_cntr' in Hlt'. rewrite progress_le_inv in Hlt'.
        destruct Hlt' as [|Heq];[assumption|exfalso].

        assert (i = progress_to_node (get_progress ts) tid).
        {
          rewrite -Heq. rewrite progress_to_node_of_node //.
        }
        subst i.

        specialize (HsameEaddr _ _ _ _ _ Hlk_i Hw_i' Hlk HE) as [-> ->].
        contradiction.

      - apply progress_adjacent_incr_cntr' in Hlt. rewrite progress_le_inv in Hlt.
        destruct Hlt as [|Heq];[assumption|exfalso].

        assert (e = progress_to_node (get_progress ts) tid).
        {
          rewrite -Heq. rewrite progress_to_node_of_node //.
        }
        subst e.
        (* cannot be on the same address *)
        specialize (HsameEaddr _ _ _ _ _ Hlk_e Haddr Hlk HE) as [-> ->].
        contradiction.
      -
        intros i ? (?&?&?&?&?).
        eapply Hforall.
        repeat (split;try eassumption).
        eapply progress_lt_trans. eassumption.
        apply progress_adjacent_incr_cntr'. rewrite progress_le_inv;right;done.
  Qed.

  #[local] Lemma last_local_writes_lookup_ne_None gr tid ts W addr addr' ls:
  gr!! progress_to_node (get_progress ts) tid = Some W ->
  AAConsistent.event_is_write_with_addr W addr ->
  no_current_local_writes ls gr tid (get_progress ts) ->
  addr ≠ addr' ->
  ls !! addr' = Some None
  → map_Forall (λ (_ : Eid) (E : Event), AAConsistent.event_is_write_with_addr E addr' = false)
      (current_local_writes gr tid (get_progress (incr_cntr ts))).
  Proof.
    assert (HsameE: forall eid E E',
              gr !! eid = Some E ->
              gr !! eid = Some E' ->
              E = E').
    {
      clear.
      intros ??? Hlk_i Hlk_w.
      rewrite Hlk_i in Hlk_w.
      inversion Hlk_w; subst.
      done.
    }
    intros Hlk HW Hft_None Hneq.
    intros Hlk_ls i ? Hlk_i.
    rewrite current_local_writes_lookup_unfold in Hlk_i.
    destruct Hlk_i as [Hlk_i [Htid' [Hlt' Hw_i]]].

    apply progress_adjacent_incr_cntr' in Hlt'. rewrite progress_le_inv in Hlt'.
    destruct Hlt' as [|Heq];[|].
    eapply (Hft_None _ Hlk_ls i).
    rewrite current_local_writes_lookup_unfold.
    repeat (split;try assumption).
    (* cannot on same address *)
    assert (i = progress_to_node (get_progress ts) tid).
    {
      rewrite -Heq. rewrite progress_to_node_of_node //.
    }
    subst i.

    specialize (HsameE _ _ _ Hlk Hlk_i) as ->.

    destruct x;destruct o;try contradiction.
    simpl in HW.
    rewrite Is_true_true in HW. rewrite andb_true_iff in HW. destruct HW as [_ HW].
    case_bool_decide;last congruence. simpl. subst.
    case_bool_decide. contradiction. apply andb_false_r.
  Qed.


  Lemma last_write_interp_progress_write {gs ls} {tid : Tid} ts ts' addr ot :
    AACandExec.NMSWF.wf (gs.(GlobalState.gs_graph)) ->
    get_progress ts = get_progress ts' ->
    (exists E, gs.(GlobalState.gs_graph) !! progress_to_node (get_progress ts) tid = Some E
          ∧ AAConsistent.event_is_write_with_addr E addr) ->
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
        intros ??.
        destruct (decide(addr = a)).
        {
          subst a. rewrite lookup_insert_Some.
          split.
          {
            intros [[_ Hinv]| []];last contradiction. inversion Hinv;subst e. clear Hinv.
            destruct HW as [W [Hlk_w HW]].
            exists W. split;try assumption.
            rewrite last_local_writes_lookup_unfold. split.
            {
              rewrite current_local_writes_lookup_unfold.
              repeat (split;try assumption).
              clear Hft_None.
              apply progress_adjacent_incr_cntr'.
              rewrite progress_le_inv. right. rewrite progress_of_node_to_node //.
              eapply is_mem_writes_helper;eassumption.
            }
            {
              intros ?? (_&_&_&?&Hlt).
              apply progress_adjacent_incr_cntr' in Hlt.
              rewrite progress_of_node_to_node. rewrite Hpg //.
            }
          }
          {
            destruct HW as [W [Hlk' HW]]. rewrite Hpg in Hlk'.
            intros [W' [Hft HW']]. left. split;first reflexivity. f_equal. rewrite Hpg.
            eapply step_is_last_write;try eassumption.
          }
        }
        {
          rewrite lookup_insert_ne;last assumption.
          rewrite Hpg in Hft_Some. rewrite Hpg in HW.
          destruct HW as [? [? ?]].
          eapply last_local_writes_lookup_ne_Some;eassumption.
        }
      }
      {
        intro.
        destruct (decide(addr = a)).
        {
          subst a. rewrite lookup_insert_Some.
          intros [[_ Hinv]|[]];[inversion Hinv|contradiction].
        }
        {
          rewrite lookup_insert_ne;last done.
          rewrite Hpg in Hft_None.
          destruct HW as [? [HW ?]]. rewrite Hpg in HW.
          eapply last_local_writes_lookup_ne_None;try eassumption.
        }
      }
    (* ot = None *)
    - destruct HW as [W [Hlk_w HW]].
      iDestruct (last_write_interp_agree_None with "HL Hl") as %Hnone.
      ospecialize* Hnone;[eassumption|eassumption|].
      destruct Hnone as [Htid|_].
      { (* in another thread *)
        iDestruct "HL" as "[%Hft_Some [%Hft_None Hauth]]".
        iCombine "Hauth Hl" gives %Hlk.
        iDestruct (ghost_map_update with "Hauth Hl") as ">[$ $]". iModIntro. iPureIntro.
        simpl in Htid. contradiction.
      }
      { (* in same thread, but later *)
        iDestruct "HL" as "[%Hft_Some [%Hft_None Hauth]]".
        iCombine "Hauth Hl" gives %Hlk.
        iDestruct (ghost_map_update with "Hauth Hl") as ">[$ $]". iModIntro. iPureIntro.

      split.
      {
        intros ??.
        destruct (decide(addr = a)).
        {
          subst a. rewrite lookup_insert_Some.
          split.
          {
            intros [[_ Hinv]| []];last contradiction. inversion Hinv;subst e. clear Hinv.
            exists W. split;last assumption.
            rewrite last_local_writes_lookup_unfold.
            rewrite current_local_writes_lookup_unfold.
            split. repeat (split;try assumption).
            clear Hft_None.
            apply progress_adjacent_incr_cntr'.
            rewrite progress_le_inv. right. rewrite progress_of_node_to_node //.
            eapply is_mem_writes_helper;eassumption.
            intros ?? (?&?&?&?&Hlt).
            apply progress_adjacent_incr_cntr' in Hlt.
            rewrite progress_of_node_to_node. rewrite Hpg //.
          }
          {
            intros [W' [Hft ?]].
            left. split;first reflexivity. f_equal. rewrite Hpg.
            rewrite Hpg in Hlk_w.
            eapply step_is_last_write;try eassumption.
          }
        }
        {
          rewrite lookup_insert_ne;last assumption.
          rewrite Hpg in Hlk_w. rewrite Hpg in Hft_Some.
          eapply last_local_writes_lookup_ne_Some;eassumption.
        }
      }
      {
        intro.
        destruct (decide(addr = a)).
        {
          subst a. rewrite lookup_insert_Some.
          intros [[_ Hinv]|[]];[inversion Hinv| contradiction].
        }
        {
          rewrite lookup_insert_ne;last assumption.
          rewrite Hpg in Hlk_w.
          rewrite Hpg in Hft_None.
          eapply last_local_writes_lookup_ne_None;eassumption.
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
    split; rewrite /are_last_local_writes /no_current_local_writes;intros.
    {
      rewrite /are_last_local_writes in Hft_Some.
      rewrite Hft_Some. do 3 f_equiv.
      rewrite !map_lookup_filter_Some. do 2 f_equiv.
      apply Hequiv.
      apply map_filter_ext. intros.
      apply Hequiv.
    }
    {
      specialize (Hft_None _ H1).
      intros ???. specialize (Hft_None i x). ospecialize* Hft_None.
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
        specialize (Hnw i). ospecialize* Hnw.
        apply elem_of_filter. split;auto.
        case_bool_decide;case_bool_decide;auto. rewrite Hpg in H3. done.
        set_solver.
        rewrite -Hpg //.
    }
    split; rewrite /are_last_local_writes /no_current_local_writes;intros.
    {
      rewrite Hft_Some. do 3 f_equiv.
      rewrite !map_lookup_filter_Some. do 2 f_equiv.
      apply Hequiv.
      apply map_filter_ext. intros.
      apply Hequiv.
    }
    {
      specialize (Hft_None a H1).
      intros ???. specialize (Hft_None i x). ospecialize* Hft_None.
      rewrite -H2. f_equiv. apply map_filter_ext. intros.
      apply Hequiv. done.
    }
  Qed.
End lemma.

#[global] Instance instantiation_irisGL `{CMRA Σ} `{!AABaseG} `{!ThreadGNL} : irisGL := {
    local_interp := my_local_interp;
  }.
