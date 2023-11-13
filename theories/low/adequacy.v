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

From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import wsat.
From self.low Require Export weakestpre.
From self.low Require Import lifting.
Import uPred.

Section adequacy.
  Context `{CMRA Σ}.
  Context `{!invGS_gen HasNoLc Σ}.
  Context `{!irisG}.
  Context `{!Protocol}.
  Implicit Types σ : LThreadState.t.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : LThreadState.t → iProp Σ.
  Implicit Types Φs : list (LThreadState.t → iProp Σ).

  Definition idx_to_tid (n : nat) : Tid := Pos.of_nat (S n).
  Lemma idx_to_tid_eq (n : nat) : (idx_to_tid n) =@{nat} S n.
  Proof. rewrite /idx_to_tid. lia. Qed.

  Import Graph.

  (* if all [wp]s terminiate with the [LTSDone] state *)
  Notation tpwp gs σs Φs := ([∗ list] idx ↦ σ;Φ ∈ σs;Φs,
                          ∃ `(_ : !irisGL) lσ,
                            (local_interp gs (idx_to_tid idx) (LThreadState.get_progress σ) lσ) ∗
                            WP σ @ (idx_to_tid idx) {{ σ', (Φ σ') }})%I.

  Notation tpsteps gs σs σs' := ("#Htpstep" ∷ [∗ list] idx ↦ σ;σ'∈σs;σs',
                                   ∃ n, ⌜nsteps (LThreadStep.t gs (idx_to_tid idx)) (S n) σ σ'⌝)%I.

  Notation tpstate_done σs := ([∗ list] σ ∈ σs, ⌜Terminated σ⌝)%I.

  Notation tpstate_init gr σs := ([∗ list] idx ↦ σ ∈ σs,
                                    ∃ pg, ⌜LThreadState.at_progress σ pg⌝ ∗
                                          ⌜ThreadState.progress_is_init gr (idx_to_tid idx) pg⌝)%I.

  Notation tppost_lifting σs Φs := ([∗ list] idx ↦ σ;Φ∈σs;Φs, post_lifting Φ (idx_to_tid idx) σ)%I.

  Notation tpnode_annot_full gr σs na na_full :=
      (⌜dom na ∪
          foldl (λ s idx, filter (Graph.is_local_node_of (idx_to_tid idx)) (Candidate.valid_eid gr) ∪ s)
          ∅ (seq 0 (length σs)) = dom na_full⌝)%I.


  (** Phase one *)
  Lemma adequacy_po_aux gs σs σs' node_annot edge_annot Φs:
    AAConsistent.t gs.(GlobalState.gs_graph) ->
    AACandExec.NMSWF.wf gs.(GlobalState.gs_graph) ->
    "#Htpstep" ∷ tpsteps gs σs σs' -∗
    "#Htpinit" ∷ tpstate_init gs.(GlobalState.gs_graph) σs -∗
    "#Htpdone" ∷ tpstate_done σs' -∗
    "#Hgs" ∷ □ gconst_interp gs -∗
    "Hannot_interp" ∷ annot_interp node_annot -∗
    (* none of the nodes has been checked *)
    "#Hna_dom" ∷ ([∗ list] idx ↦ _ ∈ σs, ⌜filter (Graph.is_local_node_of (idx_to_tid idx)) (dom node_annot) = ∅⌝) -∗
    "#Hea_wf" ∷ ea_lob_wf (gs.(GlobalState.gs_graph)) edge_annot node_annot -∗
    "Htpwp" ∷ tpwp gs σs Φs ==∗
    ∃ (node_annot' : mea Σ) (edge_annot' : sra Σ),
      annot_interp node_annot' ∗
      tpnode_annot_full (gs.(GlobalState.gs_graph)) σs node_annot node_annot' ∗
      ea_lob_wf (gs.(GlobalState.gs_graph)) edge_annot' node_annot' ∗
      tppost_lifting σs' Φs.
  Proof.
    intros Hgr_cs Hgr_wf.
    revert σs σs' Φs node_annot edge_annot.
    induction σs as [|σs_pre σs Hσs_pre] using prefix_strict_ind;
      intros σs' Φs node_annot edge_annot;simpl; repeat iNamed 1; iNamed "Htpstep".
    { (* empty case *)
      iDestruct (big_sepL2_nil_inv_l with "Htpstep") as %->.
      iDestruct (big_sepL2_nil_inv_l with "Htpwp") as %->.
      iModIntro. iExists node_annot, edge_annot. iFrame.
      iSplit. rewrite union_empty_r_L //. iSplit;[iPureIntro|];done.
    }
    (* induction case *)
    destruct Hσs_pre as [σ ->].

    iDestruct (big_sepL2_snoc_inv_l with "Htpstep") as (σ' σs_pre') "([-> [% %Hstep]] & Htpstep')".
    iDestruct (big_sepL2_length with "Htpstep'") as "%Hlen_eq".
    iDestruct (big_sepL_snoc with "Htpinit") as "(Htpinit' & [%pg [%Hpg %Hinit]])".
    iDestruct (big_sepL_snoc with "Htpdone") as "(Htpdone' & %Hterm)".
    iDestruct (big_sepL_snoc with "Hna_dom") as "(Hna_dom' & %Hna_ept)".
    iClear "Htpstep".
    iDestruct (big_sepL2_snoc_inv_l with "Htpwp") as (Φ Φs') "([-> (%&%&Hlocal_interp &Hwp)] & Htpwp)".
    rewrite Hpg /=.
    iDestruct (wp_steps with "Hlocal_interp Hgs Hwp") as "H";eauto.
    {
      iMod ("H" $! node_annot edge_annot with "[$Hannot_interp Hea_fe]") as "(%node_annot'&%edge_annot'&%lσ'&Hannot_interp&Hea_wf&Hlocal_interp'&%Hna_dom&Hpost)".
      iSplitR. iPureIntro. rewrite Hna_ept. symmetry. by apply LThreadStep.eids_from_init_empty.
      iSplit; [|iSplit]; done.
      specialize (IHσs1 σs_pre' Φs').
      iDestruct(IHσs1 with "Htpstep' Htpinit' Htpdone' Hgs Hannot_interp [] Hea_wf Htpwp")
        as ">(%node_annot_full&%edge_annot_full&Hannot_interp&Hna_full&Hea_wf&Hposts)".
      {
        iDestruct "Hna_dom'" as %Hna_dom'. iPureIntro.
        intros k ? Hlk;simpl.
        rewrite -Hna_dom. rewrite filter_union_L.
        erewrite Hna_dom';eauto. rewrite union_empty_r_L.
        apply set_eq. split;last done. rewrite elem_of_filter.
        intros [Htid_eq Hin].
        exfalso. apply LThreadStep.eids_between_inv_tid_eq in Hin.
        rewrite Hin in Htid_eq. apply lookup_lt_Some in Hlk.
        rewrite /idx_to_tid in Htid_eq. lia.
      }
      iModIntro. iExists node_annot_full,edge_annot_full.
      iFrame "Hea_wf".
      rewrite big_sepL2_snoc. rewrite Hlen_eq. iFrame.
      rewrite -Hna_dom. iDestruct "Hna_full" as %Hna_full.
      iPureIntro. rewrite app_length /=. rewrite seq_app /=.
      rewrite foldl_snoc.
      rewrite (LThreadStep.eids_between_full gs (idx_to_tid (length σs_pre)) σ σ') //.
      rewrite -Hna_full. rewrite -Hlen_eq. set_solver +.
      subst pg;done. eexists. eauto.
    }
  Qed.

  Lemma adequacy_po gs σs σs' Φs:
    AAConsistent.t gs.(GlobalState.gs_graph) ->
    AACandExec.NMSWF.wf gs.(GlobalState.gs_graph) ->
    "#Htpstep" ∷ tpsteps gs σs σs' -∗
    "#Htpinit" ∷ tpstate_init gs.(GlobalState.gs_graph) σs -∗
    "#Htpdone" ∷ tpstate_done σs' -∗
    "#Hgs" ∷ □ gconst_interp gs -∗
    "Hannot_interp" ∷ annot_interp ∅ -∗
    (* ensure that we checked events of all threads *)
    "%Hnum_thd" ∷ ⌜S (length σs) = Candidate.num_of_thd gs.(GlobalState.gs_graph)⌝ -∗
    "Htpwp" ∷ tpwp gs σs Φs ==∗
    ∃ (node_annot' : mea Σ) (edge_annot' : sra Σ),
      "Hannot_interp" ∷ annot_interp node_annot' ∗
      "%Hannot_full" ∷ na_full gs.(GlobalState.gs_graph) node_annot' ∗
      "Hea" ∷ ea_lob_wf (gs.(GlobalState.gs_graph)) edge_annot' node_annot' ∗
      "Hlifting" ∷ tppost_lifting σs' Φs.
  Proof.
    iIntros (??). repeat iNamed 1.
    iDestruct (adequacy_po_aux _ _ _ _ ∅ ∅
                with "Htpstep Htpinit Htpdone Hgs Hannot_interp [] [] Htpwp")
      as ">(%node_annot & %edge_annot & Hannot_interp & %Hna_dom & Hea_wf & Hpost)";auto.
    iModIntro. iExists node_annot, edge_annot.
    iFrame. iPureIntro. rewrite -Hna_dom. rewrite dom_empty_L union_empty_l_L.
    erewrite <-Candidate.non_initial_eids_fold;eauto. clear Hna_dom.
    induction (seq 0 (length σs)) as [|? ? Hpre] using prefix_strict_ind;first done.
    destruct Hpre. subst. rewrite 2!foldl_snoc. rewrite -idx_to_tid_eq. rewrite IHl1 //.
  Qed.

  (** Some notations for phase two *)
  (* used as the conclusion of FSL style adequacy *)
  Notation tppost_hold node_annot σs Φs :=
    ("R" ∷ ([∗ map] _ ↦ R ∈ node_annot, R) -∗ |==> ▷ |==> [∗ list] s;Φ ∈ σs;Φs, Φ s)%I.

  (* used as the conclusion in the Iris version *)
  Notation tppost σs Φs := ([∗ list] idx ↦ σ;Φ∈σs;Φs, Φ σ)%I.

  (** Phase two (FSL and Iris flavours) *)

  (* RSL/FSL flavour *)
  Lemma ea_obs_saturation gr node_annot edge_annot σs Φs:
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    (* Conclusion of phase-1 *)
    "%Hna_full" ∷ na_full gr node_annot -∗
    "Hea" ∷ ea_lob_wf gr edge_annot node_annot -∗
    (* Initial resources, used to establish FE for initial nodes *)
    "#R_init" ∷ ([∗ set] e ∈ Candidate.initials gr, □ prot_node e) -∗
    "Hpost_hold" ∷ tppost_hold node_annot σs Φs -∗
     ∃ node_annot' edge_annot',
       "Hna_complete" ∷ ⌜dom node_annot' = Candidate.valid_eid gr⌝ ∗
       "Hea" ∷ ea_ob_wf gr edge_annot' node_annot' ∗
       "Hpost_hold" ∷ tppost_hold node_annot' σs Φs.
  Proof.
    iIntros (Hwf Hcs). repeat iNamed 1.
    iDestruct (ea_init_extend with "[//] Hea R_init") as "Hea";auto.
    iNamed "Hea".
    iDestruct (ea_lob_wf_impl_ind with "Hea") as "[Hea %Hdom_eq]".
    iDestruct (ea_obs_saturation_aux2 with "Hea") as "Hea";auto.
    rewrite Hdom_eq //.
    iDestruct (ea_ob_wf_ind_equiv gr _ _) as "[Heq _]".
    iDestruct ("Heq" with "[Hea]") as "Hea".
    iSplit. 2:iExact "Hea". rewrite -Hdom_eq. rewrite map_imap_dom_Some //.
    (* show the goal *)
    iExists _, _. iSplit;[|iSplitL "Hea";[iExact "Hea"|]]. done.
    iNamed 1. iApply "Hpost_hold". rewrite big_sepM_union.
    iDestruct "R" as "[_ $]". apply map_disjoint_dom.
    rewrite Hna_full. rewrite dom_gset_to_gmap. pose proof (Candidate.valid_eid_disjoint_union gr) as [_ ?];done.
  Qed.

  Lemma tppost_lifting_hold_aux node_annot σs Φs:
    "Hannot" ∷ annot_interp node_annot -∗
    "Hlifting" ∷ tppost_lifting σs Φs -∗
    ("R" ∷ ([∗ list] i ∈ (seq 0 (length σs)),
              [∗ map] _ ↦ R ∈ filter (λ '(e, _) , e.(EID.tid) = S i) node_annot, R)
      -∗ |==> ▷ |==> [∗ list] s;Φ ∈ σs;Φs, Φ s)%I.
  Proof.
    revert Φs node_annot.
    induction σs as [|σs_pre σs Hσs_pre] using prefix_strict_ind; intros Φs node_annot; repeat iNamed 1.
    { (* empty case *)
      rewrite big_sepL2_nil_inv_l.
      iDestruct "Hlifting" as %->.
      rewrite big_sepL2_nil //.
    }
    (* induction case *)
    destruct Hσs_pre as [σ ->].
    iDestruct (big_sepL2_snoc_inv_l with "Hlifting") as (Φ Φs_pre) "([-> Hpl] & Hlifting)".
    iDestruct ("Hpl" with "Hannot") as ">[Hannot Hpl]".
    rewrite big_sepL2_snoc. rewrite app_length. simpl.
    assert ((length σs_pre + 1) = S (length σs_pre))%nat as -> by lia.
    rewrite seq_S /=. rewrite big_sepL_snoc.
    iDestruct "R" as "[R Rσ]".
    iDestruct ("Hpl" with "[Rσ]") as "?".
    rewrite big_sepM_filter.
    iApply (big_sepM_impl with "Rσ").
    iModIntro. iIntros (???) "R".
    case_bool_decide as Htid;last done. iApply "R". rewrite Htid idx_to_tid_eq //.
    iDestruct (IHσs1 Φs_pre with "Hannot Hlifting R") as ">IH".
    iModIntro. iNext. iMod "IH" as "$". done.
   Qed.

  Lemma tppost_lifting_hold gr node_annot σs Φs:
    dom node_annot = Candidate.non_initial_eids gr ->
    "%Hnum_thd" ∷ ⌜S (length σs) = Candidate.num_of_thd gr⌝ -∗
    "Hannot" ∷ annot_interp node_annot -∗
    "Hlifting" ∷ tppost_lifting σs Φs -∗
    tppost_hold node_annot σs Φs.
  Proof.
    iIntros (Hdom_eq). repeat iNamed 1.
    iApply (tppost_lifting_hold_aux with "Hannot Hlifting [R]").
    iApply big_sepL_proper.
    iIntros. iApply big_sepM_filter.
    simpl. rewrite big_sepL_sepM.
    iApply (big_sepM_impl with "R").
    iModIntro. iIntros (?? Hlk) "R".
    rewrite (big_sepL_delete _ _ (EID.tid k - 1)).
    iSplitL "R". iIntros. done.
    2: {
      rewrite lookup_seq. split. simpl. reflexivity.
      apply elem_of_dom_2 in Hlk. rewrite Hdom_eq in Hlk.
      apply Candidate.non_initial_tid_inv in Hlk. lia.
    }
    iApply (big_sepL_impl). iApply big_sepL_emp. done.
    iModIntro. iIntros (?? Hlk') "_".
    case_decide as Htid;first done. apply lookup_seq in Hlk'.
    destruct Hlk' as [-> Hlt]. iIntros (Heq). exfalso. apply Htid. lia.
  Qed.

  (* Iris flavour *)
  Lemma step_fupdN_mono n P Q E1 E2:
    (P -∗ Q) ⊢ (|={E1}[E2]▷=>^ n P) -∗ |={E1}[E2]▷=>^ n Q.
  Proof.
    iIntros "Himp P".
    iInduction n as [|] "IH" . by iApply "Himp".
    rewrite 2!Nat.iter_succ. iApply (step_fupd_mono with "[Himp] P"). by iApply "IH".
  Qed.

  Lemma adequacy_ob_aux gr node_annot edge_annot:
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    dom edge_annot = Candidate.valid_eid gr ->
    dom edge_annot = dom node_annot ->
    forall edge_annot_last,
    ob_semi_last_set gr (dom edge_annot_last) (dom edge_annot) ->
    edge_annot_last ⊆ edge_annot ->
      ea_ob_wf_ind gr edge_annot_last node_annot -∗
      (* We have resources of ob_first nodes in [edge_annot] *)
      ([∗ set] e_first ∈ (dom edge_annot) ∖ (dom edge_annot_last),
          let s_ob := (Graph.ob_succ_of gr e_first) in
         ([∗ set] e_out ∈ s_ob,
            from_option (λ gm, from_option id emp (gm !! e_first)) emp (edge_annot_last !! e_out))) -∗
      |={⊤}[∅]▷=>^ (size (dom edge_annot_last))
      ([∗ set] e_first ∈ (dom edge_annot_last),
          "R_na" ∷ from_option id emp (node_annot !! e_first)).
  Proof.
    intros Hwf Hcs Hea_full Hea_dom_eq.
    match goal with
    | [  |- forall x, ?G ] =>
        set (P := (λ (X : gset Eid), forall (x: sra Σ), dom x = X -> G))
    end.
    intros eal Heal_last Heal_sub.
    eapply (ob_set_ind_L gr (dom edge_annot) P Hcs).
    {
      rewrite Hea_full //.
    }
    {
      clear eal Heal_last Heal_sub.
      rewrite /P. intros eal Heal_dom Heal_last Heal_sub.
      iIntros "Hea R_init". iNamed "Hea". rewrite Heal_dom size_empty /=.
      apply dom_empty_inv_L in Heal_dom; subst eal. rewrite big_sepS_empty //.
    }
    {
      clear eal Heal_last Heal_sub.
      intros ef sl Hef_nv Hef_elem Hsl_last Hef_first IHsl. rewrite /P in IHsl.
      rewrite /P /=.
      intros eal Heal_dom Heal_last Heal_sub. iIntros "Hea R_init". iNamed "Hea".

      (* split FEs into current FE and the rest *)
      assert (is_Some (eal !! ef)) as [gmf Heal_lk].
      { apply elem_of_dom. rewrite Heal_dom. set_solver +. }
      rewrite -{2}(insert_id _ ef gmf Heal_lk).
      rewrite big_sepM_insert_delete. iDestruct "Hea_fe" as "[FE Hea_fe]".
      assert (is_Some (node_annot !! ef)) as [R Hna_lk].
      { apply elem_of_dom. rewrite -Hea_dom_eq. set_solver + Hef_elem. }
      rewrite Hna_lk /=.

      (* split resources of ob first nodes into the part satisfy premises of FE, and the rest *)
      (* first show that ob-first nodes of [ef] are in all ob-first node *)
      assert ((dom edge_annot ∖ dom eal) =
              (ob_pred_of gr ef) ∪ ((dom edge_annot ∖ dom eal) ∖ (ob_pred_of gr ef))) as Hsplit.
      {
         apply union_difference_L.
         apply subseteq_difference_r.
         intros ep Hpred Hnpred.
         rewrite -Heal_dom in Hef_first. apply (Hef_first _ Hnpred).
         by apply elem_of_ob_pred_of.
         rewrite Hea_full.
         apply ob_pred_of_valid. assumption.
      }
      rewrite Hsplit big_sepS_union. 2:set_solver +. iDestruct "R_init" as "[R_ob_pred R_rest_out]".
      (* then preparation for applying FE *)

      (* get resources flowing in *)
      iAssert ((([∗ set] y ∈ ob_pred_of gr ef,
                   "R_ob_out" ∷ ([∗ set] e_out ∈ ob_succ_of gr y ∖ {[ef]},
                                   from_option (λ gm : mea Σ, default emp (gm !! y)) emp (eal !! e_out))) ∗
                [∗ set] y ∈ ob_pred_of gr ef, from_option id emp (gmf !! y))%I
              ) with "[R_ob_pred]" as "[R_ob_pred_out R_ob_in]".
      {
        iDestruct (big_sepS_impl _ (λ e, ([∗ set] e_out ∈ (ob_succ_of gr e ∖ {[ef]}),
                                            from_option (λ gm : mea Σ, default emp (gm !! e)) emp (eal !! e_out))
                                         ∗ from_option (λ gm : mea Σ, default emp (gm !! e)) emp (eal !! ef))%I
                    with "R_ob_pred []") as "R_split".
        { iModIntro. iIntros (??) "H".
          rewrite {1}(union_difference_singleton_L ef (ob_succ_of gr x)).
          2: { by apply elem_of_ob_pred_of_succ. }
          rewrite big_sepS_union. 2: set_solver +. iDestruct "H" as "[H $]".
          rewrite big_sepS_singleton //.
        }
        iDestruct (big_sepS_sep with "R_split") as "[$ R_right]".
        iApply (big_sepS_impl with "R_right").
        iModIntro. iIntros (??) "?". rewrite Heal_lk //.
      }
      (* move ulu *)
      rewrite {2}Heal_dom. rewrite size_union. 2: set_solver + Hef_nv. rewrite size_singleton Nat.iter_succ.

      (* apply FE *)
      iDestruct ("FE" with "[R_ob_in]") as "R_ef".
      {
        specialize (Hea_ob_wf ef gmf Heal_lk).
        iApply big_sepS_to_map. exact Hea_ob_wf. done.
      }
      iApply (step_fupd_mono with "[-R_ef] R_ef"). iNamed 1.
      (* apply IH *)
      assert (dom (delete ef eal) = sl) as Hsl_dom.
      { rewrite dom_delete_L Heal_dom. set_solver + Hef_nv. }

      specialize (IHsl (delete ef eal)). feed specialize IHsl.
      exact Hsl_dom.
      rewrite Hsl_dom. destruct Hsl_last;done.
      etransitivity;last exact Heal_sub. apply delete_subseteq.
      iDestruct (IHsl with "[Hea_fe] [R_ob_pred_out R_rest_out R_out]") as "IH".
      {
        iSplit.
        { iPureIntro. by apply map_Forall_delete. }
        iApply (big_sepM_impl with "Hea_fe").
        iModIntro. iIntros (e_sl gm_sl Heal_lk_sl) "FE_sl".
        destruct (decide (is_Some(node_annot !! e_sl))) as [[R_sl Hna_lk_sl]|Hn].
        2:{
          assert (node_annot !! e_sl = None) as ->;auto.
          apply not_elem_of_dom. intro. apply Hn. by apply elem_of_dom.
        }
        rewrite Hna_lk_sl. iIntros "R_in". iDestruct ("FE_sl" with "R_in") as "R_out".
        iApply (step_fupd_mono with "[] R_out").
        iNamed 1. iFrame.
        iApply (big_sepS_impl with "R_out").
        iModIntro. iIntros (e_succ Hsucc) "R".
        rewrite lookup_delete_ne //.
        {
          (* e_succ ≠ ef *)
          destruct (decide (e_succ ∈ sl)) as [Hx_in | Hx_nin]. set_solver + Hx_in Hsl_dom.
          assert (e_succ ∈ dom edge_annot) as Hx_in_all.
          { rewrite Hea_full. pose proof (elem_of_ob_succ_of_valid _ _ _ Hwf Hsucc) as Hsub. set_solver + Hsub. }
          destruct Hsl_last as [_ Hsl_last].
          specialize (Hsl_last e_sl). feed specialize Hsl_last.
          rewrite lookup_delete_Some in Heal_lk_sl. destruct Heal_lk_sl as [Hneq Hlk].
          apply elem_of_dom_2 in Hlk.
          set_solver + Hlk Hneq Hsl_dom.
          simpl in Hsl_last. exfalso. eapply (Hsl_last e_succ). set_solver + Hx_nin Hx_in_all.
          apply elem_of_ob_pred_of.
          rewrite elem_of_ob_pred_of_succ //.
        }
      }
      {
        (* split the goal *)
        rewrite dom_delete_L. rewrite difference_difference_r_L.
        assert (dom edge_annot ∩ {[ef]} = {[ef]}) as -> by set_solver + Hef_elem.
        rewrite big_sepS_union. 2: set_solver + Heal_dom.
        rewrite big_sepS_singleton.
        iSplitR "R_out".
        {
          rewrite {2}Hsplit. rewrite big_sepS_union. 2: set_solver +.
          iSplitL "R_ob_pred_out".
          {
            iApply (big_sepS_impl with "R_ob_pred_out"). iModIntro. iIntros (? Hpred) "R".
            rewrite {2}(union_difference_singleton_L ef (ob_succ_of gr x)).
            2:{ rewrite -elem_of_ob_pred_of_succ //. }
            rewrite big_sepS_union. 2:set_solver +.
            rewrite big_sepS_singleton.
            rewrite lookup_delete. iSplitR;first done.
            iApply (big_sepS_impl with "R"). iModIntro. iIntros (? Hsucc) "R".
            rewrite lookup_delete_ne //. set_solver + Hsucc.
          }
          {
            iApply (big_sepS_impl with "R_rest_out"). iModIntro. iIntros (? Hin) "R".
            iApply (big_sepS_impl with "R"). iModIntro. iIntros (? Hsucc) "R".
            rewrite lookup_delete_ne //.
            intros <-. rewrite -elem_of_ob_pred_of_succ in Hsucc.
            set_solver + Hin Hsucc.
          }
        }
        {
          iApply (big_sepS_impl with "R_out"). iModIntro. iIntros (? Hsucc) "R".
          rewrite lookup_delete_ne //. by apply elem_of_ob_succ_of_ne in Hsucc.
        }
      }
      rewrite Hsl_dom. iApply (step_fupdN_mono with "[-IH] IH"). iIntros "R_sl".
      rewrite Heal_dom big_sepS_union. 2: set_solver + Hef_nv. rewrite big_sepS_singleton.
      rewrite Hna_lk. iFrame.
    }
    2:{ exact Heal_last. }
    { by apply subseteq_dom. }
    { reflexivity. }
    { done. }
    { done. }
  Qed.


  Lemma adequacy_ob gr node_annot edge_annot:
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    dom edge_annot = Candidate.valid_eid gr ->
    ea_ob_wf gr edge_annot node_annot -∗
    |={⊤}[∅]▷=>^ (size (Candidate.valid_eid gr))
      ([∗ set] e_first ∈ (dom edge_annot),
         "R_na" ∷ from_option id emp (node_annot !! e_first)).
  Proof.
    iIntros (Hwf Hcs Hdom) "Hea_fe".
    iDestruct (ea_ob_wf_ind_equiv with "Hea_fe") as "[% Hea_fe]".
    assert (size (Candidate.valid_eid gr) = size (dom edge_annot)) as ->. rewrite Hdom //.
    iApply (adequacy_ob_aux with "Hea_fe []");eauto.
    rewrite /ob_semi_last_set difference_diag_L. intros ??. apply set_Forall_empty.
    rewrite difference_diag_L. rewrite big_sepS_empty //.
  Qed.

  (** Full adequacy*)

  (* RSL/FSL version *)
  Lemma adequacy_post_hold gs σs σs' Φs:
    AAConsistent.t gs.(GlobalState.gs_graph) ->
    AACandExec.NMSWF.wf gs.(GlobalState.gs_graph) ->
    "#Htpstep" ∷ tpsteps gs σs σs' -∗
    "Htpinit" ∷ tpstate_init gs.(GlobalState.gs_graph) σs -∗
    "Htpdone" ∷ tpstate_done σs' -∗
    "Hgs" ∷ □ gconst_interp gs -∗
    (* Initial resources, used to establish FE for initial nodes *)
    "#R_init" ∷ ([∗ set] e ∈ Candidate.initials gs.(GlobalState.gs_graph), □ prot_node e) -∗
    "Hannot_interp" ∷ annot_interp ∅ -∗
    "#Hnum_thd" ∷ ⌜S (length σs) = Candidate.num_of_thd gs.(GlobalState.gs_graph)⌝ -∗
    "Htpwp" ∷ tpwp gs σs Φs ==∗
    ∃ (node_annot : mea Σ) (edge_annot : sra Σ),
      ea_ob_wf (gs.(GlobalState.gs_graph)) edge_annot node_annot ∗
      ⌜dom node_annot = Candidate.valid_eid gs.(GlobalState.gs_graph)⌝ ∗
      tppost_hold node_annot σs' Φs.
  Proof.
    iIntros (??). repeat iNamed 1.
    iDestruct (adequacy_po with "Htpstep Htpinit Htpdone Hgs Hannot_interp Hnum_thd Htpwp")
      as ">(% &%&H1)";auto.
    iNamed "H1".
    rewrite big_sepL2_alt. iDestruct "Htpstep" as "[-> _]".
    iDestruct (tppost_lifting_hold with "Hnum_thd Hannot_interp Hlifting") as "Hpost_hold";auto.
    iDestruct (ea_obs_saturation with "[//] Hea R_init Hpost_hold") as "(% &%& [Heq H2])";auto.
    iNamed "H2".
    iModIntro. iExists _, _. iFrame "Hea". iFrame.
  Qed.

  Lemma bupd_step_fupdN_bupd n P:
    (|==> |={⊤}[∅]▷=>^n |==> P) ⊢ |={⊤}[∅]▷=>^n |==> P.
  Proof.
    iIntros "H".
    destruct n. simpl. iMod "H" as "$".
    simpl.
    iApply (fupd_elim _ ⊤). done.
    iApply bupd_fupd. done.
  Qed.

  (* Iris version (depends on FSL vesion) *)
  Lemma adequacy_post gs σs σs' Φs:
    AAConsistent.t gs.(GlobalState.gs_graph) ->
    AACandExec.NMSWF.wf gs.(GlobalState.gs_graph) ->
    S (length σs) = Candidate.num_of_thd gs.(GlobalState.gs_graph) ->
    (length σs = length σs' ∧
       ∀ idx σ σ', σs !! idx = Some σ → σs' !! idx = Some σ' → (∃ n, nsteps (LThreadStep.t gs (idx_to_tid idx)) (S n) σ σ')) ->
    (∀ idx σ, σs !! idx = Some σ → (∃ pg, LThreadState.at_progress σ pg ∧
                                          ThreadState.progress_is_init gs.(GlobalState.gs_graph) (idx_to_tid idx) pg)) ->
    (∀ (k:nat) σ, σs' !! k = Some σ → Terminated σ) ->
    (* WPs + initial interpretations *)
    ⊢ ((|==> "#R_init" ∷ ([∗ set] e ∈ Candidate.initials gs.(GlobalState.gs_graph), □ prot_node e)
             ∗ "Hgs" ∷ □ gconst_interp gs
             ∗ "Hannot_interp" ∷ annot_interp ∅
             ∗ "Htpwp" ∷ tpwp gs σs Φs)
        -∗ |={⊤}[∅]▷=>^ (size (Candidate.valid_eid gs.(GlobalState.gs_graph))) |==> ▷ |==> tppost σs' Φs)%I.
  Proof.
    iIntros (?? Hnum_thd Htpstep Htpinit Htpdone). iIntros "H".
    iApply bupd_step_fupdN_bupd. iMod "H". iNamed "H".
    iMod (adequacy_post_hold gs σs σs' Φs with "[] [] [] Hgs R_init Hannot_interp [//] Htpwp")
      as "(%&%&Hea&%Hdom&Hpost_hold)".
    done. done.
    iApply (big_sepL2_impl (λ idx σ σ', ⌜∃ n, nsteps (LThreadStep.t gs (idx_to_tid idx)) (S n) σ σ'⌝%I)).
    rewrite big_sepL2_pure. done. iModIntro. iIntros (? ? ? ? ? [? ?]). iExists _. done.
    iApply (big_sepL_impl (λ idx σ , ⌜∃ pg, LThreadState.at_progress σ pg ∧
                                          ThreadState.progress_is_init gs.(GlobalState.gs_graph) (idx_to_tid idx) pg⌝%I)).
    rewrite big_sepL_pure. done. iModIntro. iIntros (? ? ? [? ?]). iExists _. done.
    done.
    iModIntro. iNamed "Hea".
    iDestruct (adequacy_ob with "[Hea_fe]") as "Hna";eauto.
    rewrite -Hea_dom_eq in Hdom. exact Hdom.
    iSplit;first iPureIntro;eauto.
    iApply (step_fupdN_mono with "[-Hna] Hna"). iIntros "Hna".
    rewrite big_sepS_to_map. 2: set_solver + Hea_dom_eq.
    iMod ("Hpost_hold" with "Hna"). done.
  Qed.

  (* Iris version with pure post conditions *)
  Lemma adequacy_post_pure gs σs σs' (Φps : list (_ -> Prop)) :
    AAConsistent.t gs.(GlobalState.gs_graph) ->
    AACandExec.NMSWF.wf gs.(GlobalState.gs_graph) ->
    S (length σs) = Candidate.num_of_thd gs.(GlobalState.gs_graph) ->
    (length σs = length σs' ∧
       ∀ idx σ σ', σs !! idx = Some σ → σs' !! idx = Some σ' → (∃ n, nsteps (LThreadStep.t gs (idx_to_tid idx)) (S n) σ σ')) ->
    (∀ idx σ, σs !! idx = Some σ → (∃ pg, LThreadState.at_progress σ pg ∧
                                          ThreadState.progress_is_init gs.(GlobalState.gs_graph) (idx_to_tid idx) pg)) ->
    (∀ (k:nat) σ, σs' !! k = Some σ → Terminated σ) ->
    (* WPs + initial interpretations *)
    ⊢ ((|==> "#R_init" ∷ ([∗ set] e ∈ Candidate.initials gs.(GlobalState.gs_graph), □ prot_node e)
       ∗ "Hgs" ∷ □ gconst_interp gs
       ∗ "Hannot_interp" ∷ annot_interp ∅
       ∗ "Htpwp" ∷ ([∗ list] idx ↦ σ;Φp ∈ σs;Φps,
                          ∃ `(_ : !irisGL) lσ, local_interp gs (idx_to_tid idx) (LThreadState.get_progress σ) lσ ∗
                            WP σ @ (idx_to_tid idx) {{ σ', ⌜Φp σ'⌝ }}))
       -∗ |={⊤}[∅]▷=>^ (size (Candidate.valid_eid gs.(GlobalState.gs_graph))) |==> ▷ |==>
          ⌜length σs' = length Φps ∧ ∀ (idx: nat) σ' (Φ: _ -> Prop), σs' !! idx = Some σ' → Φps !! idx = Some Φ
                                                                   → Φ σ'⌝).
  Proof.
    iIntros (?? Hnum_thd Htpstep Htpinit Htpdone). iIntros "H".
    iApply bupd_step_fupdN_bupd. iMod "H". iNamed "H".
    iAssert (tpwp gs σs ((λ Φp, (λ v,  ⌜Φp v⌝)%I) <$> Φps))%I with "[Htpwp]" as "Htpwp".
    {
      iDestruct (big_sepL2_impl _ (λ idx σ Φp, ∃ `(_ : !irisGL) lσ,
                                   local_interp gs (idx_to_tid idx) (LThreadState.get_progress σ) lσ ∗
                            WP σ @ (idx_to_tid idx) {{ σ', ⌜Φp σ'⌝ }})%I with "Htpwp []") as "Htpwp".
      {
        iModIntro. iIntros (?????) "[%GL wps]".
        iExists GL. iFrame.
      }
      rewrite big_sepL2_fmap_r.
      iApply (big_sepL2_impl with "Htpwp").
      iModIntro. iIntros (?????) "[% [% H]]".
      iExists _,_. done.
    }
    iMod (adequacy_post_hold gs σs σs' ((λ Φp, (λ v,  ⌜Φp v⌝)%I) <$> Φps)  with "[] [] [] Hgs R_init Hannot_interp [//] Htpwp")
      as "(%&%&Hea&%Hdom&Hpost_hold)".
    done. done.
    iApply (big_sepL2_impl (λ idx σ σ', ⌜∃ n, nsteps (LThreadStep.t gs (idx_to_tid idx)) (S n) σ σ'⌝%I)).
    rewrite big_sepL2_pure. done. iModIntro. iIntros (? ? ? ? ? [? ?]). iExists _. done.
    iApply (big_sepL_impl (λ idx σ , ⌜∃ pg, LThreadState.at_progress σ pg ∧
                                          ThreadState.progress_is_init gs.(GlobalState.gs_graph) (idx_to_tid idx) pg⌝%I)).
    rewrite big_sepL_pure. done. iModIntro. iIntros (? ? ? [? ?]). iExists _. done.
    done.

    iModIntro. iNamed "Hea".
    iDestruct (adequacy_ob with "[Hea_fe]") as "Hna";eauto.
    rewrite -Hea_dom_eq in Hdom. exact Hdom.
    iSplit;first iPureIntro;eauto.
    iDestruct (step_fupdN_mono _ _ (|==> ▷ |==> ⌜
       length σs' = length Φps
              ∧ (∀ (k : nat) (y1 : LThreadState.t) (y2 : LThreadState.t → Prop), σs' !! k = Some y1 → Φps !! k = Some y2 → y2 y1)⌝) with "[-Hna] Hna") as "H". iIntros "Hna".
    rewrite big_sepS_to_map.
    2: set_solver + Hea_dom_eq.
    iMod ("Hpost_hold" with "Hna") as "H".
    rewrite big_sepL2_fmap_r. rewrite big_sepL2_pure.
    iModIntro. iExact "H". done.
  Qed.

End adequacy.

(* Final Coq level adequacy *)
Lemma adequacy_pure `{CMRA Σ} `{!invGpreS Σ} gs σs σs' (Φps : list (_ -> Prop)) :
  AAConsistent.t gs.(GlobalState.gs_graph) ->
  AACandExec.NMSWF.wf gs.(GlobalState.gs_graph) ->
  S (length σs) = AACandExec.Candidate.num_of_thd gs.(GlobalState.gs_graph) ->
  (length σs = length σs' ∧
   ∀ idx σ σ', σs !! idx = Some σ → σs' !! idx = Some σ' → (∃ n, nsteps (LThreadStep.t gs (idx_to_tid idx)) (S n) σ σ')) ->
  (∀ idx σ, σs !! idx = Some σ → (∃ pg, LThreadState.at_progress σ pg ∧
                                        ThreadState.progress_is_init gs.(GlobalState.gs_graph) (idx_to_tid idx) pg)) ->
  (∀ (k:nat) σ, σs' !! k = Some σ → Terminated σ) ->
  (forall `{Hinv : !invGS_gen HasNoLc Σ},
      ⊢@{iProp Σ} |==> ∃ `{!irisG} `{!Protocol},
      ("#R_init" ∷ ([∗ set] e ∈ AACandExec.Candidate.initials gs.(GlobalState.gs_graph), □ prot_node e)
       ∗ "Hgs" ∷ □ gconst_interp gs
       ∗ "Hannot_interp" ∷ annot_interp ∅
       ∗ "Htpwp" ∷ ([∗ list] idx ↦ σ;Φp ∈ σs;Φps, ∃ `(_ : !irisGL) lσ, local_interp gs (idx_to_tid idx) (LThreadState.get_progress σ) lσ
                                                                       ∗ WP σ @ (idx_to_tid idx) {{ σ', ⌜Φp σ'⌝ }}))) ->
  length σs' = length Φps ∧ forall (idx: nat) σ' (Φ: _ -> Prop), σs' !! idx = Some σ' → Φps !! idx = Some Φ → Φ σ'.
Proof.
  intros ?????? HH.
  eapply pure_soundness.
  eapply (step_fupdN_soundness_no_lc' _
            (size (AACandExec.Candidate.valid_eid gs.(GlobalState.gs_graph)) + 1)
            (size (AACandExec.Candidate.valid_eid gs.(GlobalState.gs_graph)) + 1)).
  intros. specialize (HH Hinv).

  iIntros "_".
  rewrite comm. rewrite (step_fupdN_add 1) /=. iMod HH as "(%Hiris & %Hprot & H)".

  iDestruct (@adequacy_post_pure Σ H Hinv Hiris Hprot gs σs σs' Φps with "[H]") as "H";try done.

  assert (Hfold:∀ P, (|={⊤}[∅]▷=>^1 P) ⊢@{iProp Σ} |={⊤}[∅]▷=> P) by done. iApply Hfold.
  rewrite -step_fupdN_add. rewrite Nat.add_comm /=. rewrite step_fupdN_add.
  iApply (step_fupdN_mono with "[] H").

  iIntros "H'". iMod "H'".
  iApply fupd_mask_intro. set_solver +.
  iIntros "Hclose". iNext. iMod "Hclose" as "_". by iMod "H'" as "$".
Qed.
