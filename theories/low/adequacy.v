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
From self.low.lib Require Import ind.
Import uPred.

Section adequacy.
  Context `{CMRA Σ}.
  Context `{!invGS_gen HasNoLc Σ}.
  Context `{!irisG}.
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


  (*** Phase one - induction on [po] *)
  (* This is the induction version of [adequacy_po]
     We do induction on [po].
     We can obtain a local [node_annot'] and construct a local [edge_annot'],
     that are related by [ea_lob_wf] from initial ones *)
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
    "#Hea_wf" ∷ ea_local_wf (gs.(GlobalState.gs_graph)) edge_annot node_annot -∗
    "Htpwp" ∷ tpwp gs σs Φs ==∗
    ∃ (node_annot' : mea Σ) (edge_annot' : sra Σ),
      annot_interp node_annot' ∗
      tpnode_annot_full (gs.(GlobalState.gs_graph)) σs node_annot node_annot' ∗
      ea_local_wf (gs.(GlobalState.gs_graph)) edge_annot' node_annot' ∗
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
      iSplit. rewrite union_empty_r_L. clear;done. iSplit;[iPureIntro|]. split;assumption. clear;done.
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
    iDestruct (wp_steps with "Hlocal_interp Hgs Hwp") as "H";try assumption. eassumption.
    {
      iMod ("H" $! node_annot edge_annot with "[$Hannot_interp Hea_fe]")
        as "(%node_annot'&%edge_annot'&%lσ'&Hannot_interp&Hea_wf&Hlocal_interp'&%Hna_dom&Hpost)".
      iSplitR. iPureIntro. rewrite Hna_ept. symmetry. by apply LThreadStep.eids_from_init_empty.
      iSplit; [|iSplit]. iPureIntro;assumption.  iPureIntro;assumption. iFrame.
      specialize (IHσs1 σs_pre' Φs').
      iDestruct(IHσs1 with "Htpstep' Htpinit' Htpdone' Hgs Hannot_interp [] Hea_wf Htpwp")
        as ">(%node_annot_full&%edge_annot_full&Hannot_interp&Hna_full&Hea_wf&Hposts)".
      {
        iDestruct "Hna_dom'" as %Hna_dom'. iPureIntro.
        intros k ? Hlk;simpl.
        rewrite -Hna_dom. rewrite filter_union_L.
        erewrite Hna_dom';[|eassumption]. rewrite union_empty_r_L.
        apply set_eq. split; [|clear; done]. rewrite elem_of_filter.
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
      rewrite (LThreadStep.eids_between_full gs (idx_to_tid (length σs_pre)) σ σ');try eassumption.
      rewrite -Hna_full. rewrite -Hlen_eq. set_solver +.
      subst pg;done. eexists. eassumption.
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
      "Hea" ∷ ea_local_wf (gs.(GlobalState.gs_graph)) edge_annot' node_annot' ∗
      "Hlifting" ∷ tppost_lifting σs' Φs.
  Proof.
    iIntros (??). repeat iNamed 1.
    iDestruct (adequacy_po_aux _ _ _ _ ∅ ∅
                with "Htpstep Htpinit Htpdone Hgs Hannot_interp [] [] Htpwp")
      as ">(%node_annot & %edge_annot & Hannot_interp & %Hna_dom & Hea_wf & Hpost)" ;
      try eassumption; try (clear;done).
    iModIntro. iExists node_annot, edge_annot.
    iFrame. iPureIntro. rewrite -Hna_dom. rewrite dom_empty_L union_empty_l_L.
    erewrite <-Candidate.non_initial_eids_fold;try eassumption. clear Hna_dom.
    induction (seq 0 (length σs)) as [|? ? Hpre] using prefix_strict_ind;first done.
    destruct Hpre. subst. rewrite 2!foldl_snoc. rewrite -idx_to_tid_eq. rewrite IHl1 //.
  Qed.

  (** Some notations for phase two *)
  (* used as the conclusion of FSL style adequacy *)
  Notation tppost_hold node_annot σs Φs :=
    ("R" ∷ ([∗ map] _ ↦ R ∈ node_annot, R) -∗ |==> ▷ |==> [∗ list] s;Φ ∈ σs;Φs, Φ s)%I.

  (* used as the conclusion in the Iris version *)
  Notation tppost σs Φs := ([∗ list] idx ↦ σ;Φ∈σs;Φs, Φ σ)%I.

  (*** Phase two - induction on [ob] *)

  Definition ea_local_wf_ind (gr :  Graph.t) (ea : sra Σ) (na : mea Σ) : iProp Σ:=
      "%Hea_lob_wf" ∷ ([∗ map] e ↦ gm ∈ ea, ⌜dom gm ⊆ (Graph.lob_pred_of gr e)⌝) ∗
      (* here we swap [na] and [ea] *)
      "Hea_fe" ∷ ([∗ map] e ↦ flow_in ∈ ea,
                    from_option (λ R, flow_eq_ea gr e flow_in ea R) emp (na !! e)).

  (* Convert [ea_local_ext_wf] to the induction version, second step of phase-2
     This is followed by [ea_obs_saturation_aux2] *)
  Lemma ea_local_wf_impl_ind gr node_annot edge_annot:
    ea_local_wf gr edge_annot node_annot -∗
    ea_local_wf_ind gr edge_annot node_annot ∗ ⌜dom edge_annot = dom node_annot ⌝.
  Proof.
    iNamed 1. iSplit;[|done]. iSplit. iPureIntro;done.
    rewrite big_sepM_sepM2_zip //.
    rewrite big_sepM2_flip //.
    rewrite -big_sepM_sepM2_zip //.
  Qed.

  Lemma ea_local_wf_ind_ext gr node_annot edge_annot:
    "Hea" ∷ ea_local_wf_ind gr edge_annot node_annot -∗
    "%Hna_full" ∷ na_full gr node_annot -∗
    "%Hea_dom" ∷ ⌜dom edge_annot = dom node_annot ⌝ -∗
    "Hea" ∷ ea_local_wf_ind gr edge_annot (gset_to_gmap emp%I (Candidate.initials gr) ∪ node_annot).
  Proof.
    repeat iNamed 1.
    iNamed "Hea".
    iSplit;first done.
    iApply (big_sepM_impl with "Hea_fe").
    iModIntro.
    iIntros (?? Hlk) "H".
    assert (is_Some (node_annot !! k)) as [R Hna_lk].
    { apply elem_of_dom. rewrite -Hea_dom. apply elem_of_dom. eexists;eassumption. }
    rewrite Hna_lk /=.
    rewrite lookup_union.
    assert (gset_to_gmap emp%I (initials gr) !! k = None) as ->.
    {
      apply not_elem_of_dom. rewrite dom_gset_to_gmap.
      pose proof (valid_eid_disjoint_union gr) as [_ Hdisj].
      apply elem_of_dom_2 in Hna_lk. rewrite Hna_full in Hna_lk.
      set_solver + Hdisj Hna_lk.
    }
    rewrite Hna_lk //=.
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


  (* The phase-2 ob induction proof, where we apply all flow equations *)
  Lemma adequacy_ob_aux gr node_annot:
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    dom node_annot = Candidate.valid_eid gr ->
    ∀ edge_annot_last (σ: ob_st),
    (dom edge_annot_last) ⊆[ob gr] (dom node_annot) ->
    dom edge_annot_last ⊆ dom node_annot ->
    ⊢
    ob_st_interp gr σ ((dom node_annot) ∖ (dom edge_annot_last))
    -∗
    ea_local_wf_ind gr edge_annot_last node_annot
    -∗
    (* lob *)
    ([∗ set] e_first ∈ (dom node_annot) ∖ (dom edge_annot_last),
       let s_ob := (Graph.ob_succ_of gr e_first) in
       ([∗ set] e_out ∈ s_ob,
          from_option (λ gm, from_option id emp (gm !! e_first)) emp (edge_annot_last !! e_out)))
    -∗
    |={⊤}[∅]▷=>^ (size (dom edge_annot_last))
      ([∗ set] e ∈ (dom edge_annot_last),
         "R_na" ∷ from_option id emp (node_annot !! e)) ∗
    ∃ (σ': ob_st), ob_st_interp gr σ' (dom node_annot).
  Proof.
    intros Hwf Hcs Hna_full.
    match goal with
    | [  |- forall x, ?G ] =>
        set (P := (λ (X : gset Eid), forall (x: sra Σ), dom x = X -> G))
    end.
    intros eal Heal_last Heal_sub.
    eapply (ob_set_ind_L3 gr (dom node_annot) P Hcs).
    {
      clear eal Heal_last Heal_sub.
      rewrite /P. intros eal Heal_dom σ Heal_last.
      iIntros (?) "Hob_st Hea R_lob".
      rewrite Heal_dom.
      rewrite size_empty /=.
      rewrite difference_empty_L.
      iFrame.
      clear;done.
    }
    {
      clear eal Heal_last Heal_sub.
      intros ef sl Hsl_last Hef_last IHsl. rewrite /P in IHsl.
      rewrite /P /=.
      intros eal <-. iIntros (? Heal_last Heal_sub) "Hob_st Hea R_lob".

      iNamed "Hea".
      (* split FEs into current FE and the rest *)
      assert (is_Some (eal !! ef)) as [gmf Heal_lk].
      { apply elem_of_dom. set_solver + Hef_last. }
      rewrite big_sepM_delete;last eassumption.
      iDestruct "Hea_fe" as "[FE Hea_fe]".
      assert (is_Some (node_annot !! ef)) as [R Hna_lk].
      { apply elem_of_dom. set_solver + Hef_last Heal_sub. }
      rewrite Hna_lk /=.

      (* split resources of ob first nodes into the part satisfy premises of FE (for [ef]), and the rest *)

      assert ((dom node_annot ∖ dom eal) =
              (ob_pred_of gr ef) ∪ ((dom node_annot ∖ dom eal) ∖ (ob_pred_of gr ef))) as Hsplit.
      {
         apply union_difference_L.
         apply subseteq_difference_r.
         intros ep Hpred Hnpred.
         set_solver + Hef_last Hnpred Hpred.
         rewrite Hna_full.
         apply ob_pred_of_valid. assumption.
      }
      rewrite {2}Hsplit big_sepS_union. 2:set_solver +. iDestruct "R_lob" as "[R_lob_in R_lob_rest]".

      (* get resources flowing in *)
      iAssert ((([∗ set] y ∈ ob_pred_of gr ef,
                   "R_lob_out" ∷ ([∗ set] e_out ∈ ob_succ_of gr y ∖ {[ef]},
                                   from_option (λ gm : mea Σ, default emp (gm !! y)) emp (eal !! e_out))) ∗
                [∗ set] y ∈ ob_pred_of gr ef, from_option id emp (gmf !! y))%I
              ) with "[R_lob_in]" as "[R_lob_in_rest R_lob_in]".
      {
        iDestruct (big_sepS_impl _ (λ e, ([∗ set] e_out ∈ (ob_succ_of gr e ∖ {[ef]}),
                                            from_option (λ gm : mea Σ, default emp (gm !! e)) emp (eal !! e_out))
                                         ∗ from_option (λ gm : mea Σ, default emp (gm !! e)) emp (eal !! ef))%I
                    with "R_lob_in []") as "R_split".
        { iModIntro. iIntros (??) "H".
          rewrite {1}(union_difference_singleton_L ef (ob_succ_of gr x)).
          2: { by apply elem_of_ob_pred_of_succ. }
          rewrite big_sepS_union. 2: set_solver +. iDestruct "H" as "[H $]".
          rewrite big_sepS_singleton. iFrame.
        }
        iDestruct (big_sepS_sep with "R_split") as "[$ R_right]".
        iApply (big_sepS_impl with "R_right").
        iModIntro. iIntros (??) "?". rewrite Heal_lk. iFrame.
      }

      rewrite {1}/flow_eq_ea flow_eq_dyn_unseal /flow_eq_dyn_def.
      iSpecialize ("FE" with "[] [] Hob_st [R_lob_in]").
      {
        (* "H_ob_pred" ∷ ⌜obs_pred_of gr ef ⊆ dom node_annot ∖ dom eal⌝ *)
        (* ef is indeed ob first *)
        iPureIntro.
        rewrite Hsplit.
        pose proof (ob_pred_of_disj_union gr ef Hwf Hcs) as [Hunion _].
        transitivity (ob_pred_of gr ef).
        apply union_subseteq in Hunion. destruct Hunion as [_ Hunion]. assumption.
        set_solver +.
      }
      {
        iPureIntro;set_solver + Hef_last.
      }
      {
        (* "R_lob_in" : [∗ set] y ∈ ob_pred_of gr ef, default emp (gmf !! y) *)
        (* --------------------------------------∗ *)
        (* "R_lob_in" ∷ ([∗ map] R_in ∈ gmf, R_in) *)
        (* we have lob flowing in *)
        specialize (Hea_lob_wf ef gmf Heal_lk).
        rewrite big_sepS_to_map. iApply (big_sepM_mono with "R_lob_in"). iIntros (???) "$".
        etrans. apply Hea_lob_wf.
        pose proof (ob_pred_of_disj_union gr ef Hwf Hcs) as [Hsub _].
        apply union_subseteq in Hsub. destruct Hsub as [Hsub _].
        set_solver + Hsub.
      }

      assert (dom (delete ef eal) = (dom eal) ∖ {[ef]}) as Heal_dom.
      { rewrite dom_delete_L //. }

      assert ((size (dom eal)) = S (size (dom (delete ef eal)))) as ->.
      {
        rewrite -{1}(insert_id _ ef gmf Heal_lk).
        rewrite -insert_delete_insert.
        rewrite dom_insert_L. rewrite size_union. rewrite size_singleton. lia.
        rewrite Heal_dom. set_solver +.
      }

      simpl. iApply (step_fupd_wand with "FE [Hea_fe R_lob_rest R_lob_in_rest]").

      iIntros "[% HN]". iNamed "HN". iNamed "R".

      (* apply IH *)
      ospecialize* (IHsl (delete ef eal)).
      { exact Heal_dom. }
      {
        eapply rel_semi_last_set_mono; last exact Heal_last.
        apply subset_dom. apply delete_subset. set_solver + Heal_lk.
        assumption.
        rewrite Heal_dom.
        eapply rel_semi_last_set_mono; [|reflexivity| | ].
        rewrite -Heal_dom.
        apply subset_dom. apply delete_subset. set_solver + Heal_lk.
        set_solver + Hef_last.
        set_solver +.
      }
      {
        etransitivity;last exact Heal_sub.  apply subseteq_dom. apply delete_subseteq.
      }
      assert (({[ef]} ∪ dom node_annot ∖ dom eal) = (dom node_annot ∖ dom (delete ef eal))) as ->.
      {
        rewrite Heal_dom.
        rewrite difference_difference_r_L.
        assert (dom node_annot ∩ {[ef]} = {[ef]}) as ->.
        { apply elem_of_dom_2 in Hna_lk. set_solver + Hna_lk. }
        rewrite union_comm_L //.
      }

      iDestruct "R" as "[R R_lob]".

      iDestruct (IHsl with "Hob_st [Hea_fe] [R_lob R_lob_rest R_lob_in_rest]") as "IH".
      {
        iSplit.
        { iPureIntro. by apply map_Forall_delete. }
        iApply (big_sepM_impl with "Hea_fe").
        iModIntro. iIntros (e_sl gm_sl Heal_lk_sl) "FE_sl".
        destruct (decide (is_Some(node_annot !! e_sl))) as [[R_sl Hna_lk_sl]|Hn].
        2:{
          assert (node_annot !! e_sl = None) as ->.
          apply not_elem_of_dom. intro. apply Hn. by apply elem_of_dom.
          iFrame.
        }
        rewrite Hna_lk_sl /=.
        rewrite /flow_eq_ea.

        fold flow_eq_dyn_def.

        iApply (flow_eq_dyn_proper with "[] FE_sl").
        {
          iModIntro. iNext.
          iIntros "[$ R]".
          iApply (big_sepS_impl with "R").
          iModIntro. iIntros (e_succ Hsucc) "R".
          rewrite lookup_delete_ne;[iFrame|].
          {
            apply lob_succ_of_subseteq_ob in Hsucc.
            (* e_succ ≠ ef *)
            destruct (decide (e_succ ∈ (dom eal))) as [Hx_in | Hx_nin].
            {
              intros ->.
              rewrite lookup_delete_Some in Heal_lk_sl.
              clear - Hef_last Hsucc Heal_lk_sl.
              destruct Heal_lk_sl. set_unfold.
              destruct Hef_last.
              eapply H1. rewrite elem_of_dom. eexists;eassumption. set_solver.
            }
            {
              assert (e_succ ∈ dom node_annot) as Hx_in_all.
              { rewrite Hna_full. pose proof (elem_of_ob_succ_of_valid _ _ _ Hwf Hsucc) as Hsub. set_solver + Hsub. }
              ospecialize (Hsl_last e_sl _).
              rewrite lookup_delete_Some in Heal_lk_sl. destruct Heal_lk_sl as [Hneq Hlk].
              apply elem_of_dom_2 in Hlk.
              set_solver + Hlk Hneq.
              simpl in Hsl_last. exfalso. eapply (Hsl_last e_succ). set_solver + Hx_nin Hx_in_all.
              apply elem_of_ob_pred_of.
              rewrite elem_of_ob_pred_of_succ //.
            }
          }
        }
      }
      {
        (* split the goal *)
        rewrite dom_delete_L. rewrite difference_difference_r_L.
        assert (dom node_annot ∩ {[ef]} = {[ef]}) as ->.
        { apply elem_of_dom_2 in Hna_lk. set_solver + Hna_lk. }
        rewrite big_sepS_union.
        2: {  apply elem_of_dom_2 in Heal_lk. set_solver + Heal_lk. }
        rewrite big_sepS_singleton.
        iSplitR "R_lob".
        {
          rewrite {2}Hsplit. rewrite big_sepS_union. 2: set_solver +.
          iSplitL "R_lob_in_rest".
          {
            iApply (big_sepS_impl with "R_lob_in_rest"). iModIntro. iIntros (? Hpred) "R".
            rewrite {2}(union_difference_singleton_L ef (ob_succ_of gr x)).
            2:{ rewrite -elem_of_ob_pred_of_succ //. }
            rewrite big_sepS_union. 2:set_solver +.
            rewrite big_sepS_singleton.
            rewrite lookup_delete. iSplitR;first (clear;done).
            iApply (big_sepS_impl with "R"). iModIntro. iIntros (? Hsucc) "R".
            rewrite lookup_delete_ne. iFrame. set_solver + Hsucc.
          }
          {
            iApply (big_sepS_impl with "R_lob_rest"). iModIntro. iIntros (? Hin) "R".
            iApply (big_sepS_impl with "R"). iModIntro. iIntros (? Hsucc) "R".
            rewrite lookup_delete_ne. iFrame.
            intros <-. rewrite -elem_of_ob_pred_of_succ in Hsucc.
            set_solver + Hin Hsucc.
          }
        }
        {
          assert (ob_succ_of gr ef = lob_succ_of gr ef ∪ (ob_succ_of gr ef ∖ (lob_succ_of gr ef))) as ->.
          { pose proof (lob_succ_of_subseteq_ob gr ef). apply union_difference_L. set_solver + H1. }
          rewrite big_sepS_union.
          2:{ clear. apply disjoint_difference_r1. reflexivity. }
          iSplitL "R_lob".
          iApply (big_sepS_impl with "R_lob"). iModIntro. iIntros (? Hsucc) "R".
          rewrite lookup_delete_ne. iFrame. apply lob_succ_of_subseteq_ob in Hsucc. by apply elem_of_ob_succ_of_ne in Hsucc.
          iApply (big_sepS_mono (λ _, emp%I));last (iApply big_sepS_emp;clear;done).
          iIntros (??) "_".
          destruct (decide (ef = x)) as  [->|]. rewrite lookup_delete /=. clear;done.
          rewrite lookup_delete_ne;last assumption.
          destruct (eal !! x) eqn: Hlk.
          2: clear;done.
          apply Hea_lob_wf in Hlk.
          simpl.
          assert (g !! ef = None).
          { rewrite -not_elem_of_dom.
            intros Hdom. apply Hlk in Hdom. apply elem_of_lob_pred_of_succ in Hdom.
            apply elem_of_difference in H1. destruct H1.
            contradiction.
          }
          rewrite H2. clear;done.
        }
      }
      iApply (step_fupdN_mono with "[R] IH"). iIntros "[R_sl $]".
      rewrite Heal_dom. iApply (big_sepS_delete with "[$R_sl R]").
      apply elem_of_dom. eexists;eassumption.
      rewrite Hna_lk. iFrame.

      }
    { eassumption. }
    { reflexivity. }
    { done. }
  Qed.

  Lemma adequacy_ob gr node_annot edge_annot (σ: ob_st):
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    dom edge_annot = Candidate.non_initial_eids gr ->
    ob_st_interp gr σ (Candidate.initials gr) -∗
    ea_local_wf gr edge_annot node_annot -∗
    |={⊤}[∅]▷=>^ (size (Candidate.non_initial_eids gr))
      ([∗ map] R ∈ node_annot, "R_na" ∷ R) ∗ ∃ (σ': ob_st), ob_st_interp gr σ' (Candidate.valid_eid gr).
  Proof.
    iIntros (Hwf Hcs Hdom) "Hob_st Hea_fe".
    iDestruct (ea_local_wf_impl_ind with "Hea_fe") as "[Hea_fe %]".
    iNamed "Hea_fe".
    iDestruct (ea_local_wf_ind_ext with "[$Hea_fe //] [] [//]") as "Hea_fe".
    { iPureIntro. rewrite -Hdom. symmetry;assumption. }
    assert (Candidate.initials gr = (dom (gset_to_gmap emp%I (initials gr) ∪ node_annot)) ∖ (dom edge_annot)) as Heq.
    {
      rewrite H1. rewrite dom_union_L dom_gset_to_gmap. rewrite -H1 Hdom.
      pose proof (valid_eid_disjoint_union gr) as [_ Hdisj].
      set_solver + Hdisj.
    }
    rewrite Heq.
    iDestruct (adequacy_ob_aux with "[Hob_st] Hea_fe []") as "HH"; rewrite -?H1;try eassumption.
    {
      rewrite -Heq. rewrite dom_union_L dom_gset_to_gmap. rewrite -H1 Hdom.
      pose proof (valid_eid_disjoint_union gr) as [Hunion _].
      set_solver + Hunion.
    }
    {
      rewrite -Heq.
      rewrite dom_union_L dom_gset_to_gmap. rewrite -H1 Hdom.
      clear Heq H1 Hdom.
      rewrite /rel_semi_last_set.
      assert ((initials gr ∪ non_initial_eids gr) ∖ non_initial_eids gr = initials gr) as ->.
      { pose proof (valid_eid_disjoint_union gr) as [_ Hdisj]. set_solver + Hdisj. }
      intros ???.
      intros Hin.
      pose proof (no_ob_pred_initial gr x0 Hwf Hcs Hin).
      set_solver + H2.
    }
    { rewrite -Heq. rewrite dom_union_L. rewrite H1. set_solver +. }
    { rewrite -{2}Heq. iExact "Hob_st". }
    {
      rewrite -Heq. rewrite -Heq.
      iApply (big_sepS_mono (λ _, emp%I));[|iApply big_sepS_emp;clear;done].
      iIntros (??) "_".
      iApply (big_sepS_mono (λ _, emp%I));[|iApply big_sepS_emp;clear;done].
      iIntros (??) "_".
      destruct (edge_annot !! x0) eqn:Hlk.
      simpl. apply Hea_lob_wf in Hlk.
      pose proof (ob_succ_of_disj_union gr x Hwf Hcs) as [Hsub _].
      assert (ob_succ_of gr x = lob_succ_of gr x ∪ (ob_succ_of gr x ∖ lob_succ_of gr x )).
      {
        Local Opaque ob lob obs.
        apply union_subseteq in Hsub.
        destruct Hsub as [Hsub _].
        apply union_difference_L. assumption.
      }
      rewrite H4 in H3. apply elem_of_union in H3. destruct H3.
      pose proof (no_lob_succ_initial gr x Hwf Hcs H2). set_solver + H3 H5.
      assert (x0 ∉ lob_succ_of gr x) by set_solver + H3.
      rewrite -elem_of_lob_pred_of_succ in H5.
      assert (g !! x = None) as Hnone.
      { apply not_elem_of_dom. set_solver + H5 Hlk. }
      rewrite Hnone. all: clear;done.
    }
    rewrite {1}Hdom.
    iApply (step_fupdN_wand with "HH []").
    iIntros "[H1 H2]".
    rewrite -Heq.
    assert (valid_eid gr = (dom (gset_to_gmap emp%I (initials gr) ∪ node_annot))) as ->.
    {
      rewrite dom_union_L. rewrite dom_gset_to_gmap. rewrite -H1 Hdom.
      pose proof (valid_eid_disjoint_union gr) as [Hunion _]. set_solver + Hunion.
    }
    iFrame.
    iDestruct (big_sepS_mono _ (λ e, "R_na" ∷ default emp (node_annot !! e))%I with "H1") as "H1".
    {
      iIntros. rewrite lookup_union_r. iFrame.
      apply not_elem_of_dom. rewrite dom_gset_to_gmap. rewrite Hdom in H2.
      pose proof (valid_eid_disjoint_union gr) as [_ Hdisj]. set_solver + Hdisj H2.
    }
    iApply big_sepS_to_map;[|iFrame].
    rewrite H1;reflexivity.
  Qed.

  (** Full adequacy*)

  (* RSL/FSL version *)
  Lemma adequacy_post_hold gs σs σs' Φs (σ: ob_st) :
    let gr := gs.(GlobalState.gs_graph) in
    AAConsistent.t gr ->
    AACandExec.NMSWF.wf gr ->
    "#Htpstep" ∷ tpsteps gs σs σs' -∗
    "Htpinit" ∷ tpstate_init gr σs -∗
    "Htpdone" ∷ tpstate_done σs' -∗
    "Hgs" ∷ □ gconst_interp gs -∗
    "Hannot_interp" ∷ annot_interp ∅ -∗
    "#Hnum_thd" ∷ ⌜S (length σs) = Candidate.num_of_thd gr⌝ -∗
    "Htpwp" ∷ tpwp gs σs Φs ==∗
    ∃ (node_annot : mea Σ) (edge_annot : sra Σ),
      ea_local_wf gr edge_annot node_annot ∗
      ⌜dom node_annot = Candidate.non_initial_eids gr⌝ ∗
      tppost_hold node_annot σs' Φs.
  Proof.
    iIntros (???). repeat iNamed 1.
    iDestruct (adequacy_po with "Htpstep Htpinit Htpdone Hgs Hannot_interp Hnum_thd Htpwp")
      as ">(% &%&H1)";[assumption|assumption|].
    iNamed "H1".
    rewrite big_sepL2_alt. iDestruct "Htpstep" as "[-> _]".
    iDestruct (tppost_lifting_hold with "Hnum_thd Hannot_interp Hlifting") as "Hpost_hold";[assumption|].
    iModIntro. iFrame "Hea". iFrame.
    iPureIntro;assumption.
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
    let gr := gs.(GlobalState.gs_graph) in
    AAConsistent.t gr ->
    AACandExec.NMSWF.wf gr ->
    S (length σs) = Candidate.num_of_thd gr ->
    (length σs = length σs' ∧
       ∀ idx σ σ', σs !! idx = Some σ → σs' !! idx = Some σ' → (∃ n, nsteps (LThreadStep.t gs (idx_to_tid idx)) (S n) σ σ')) ->
    (∀ idx σ, σs !! idx = Some σ → (∃ pg, LThreadState.at_progress σ pg ∧
                                          ThreadState.progress_is_init gr (idx_to_tid idx) pg)) ->
    (∀ (k:nat) σ, σs' !! k = Some σ → Terminated σ) ->
    (* WPs + initial interpretations *)
    ⊢ ((∃ (σ: ob_st), |==>
               "Hgs" ∷ □ gconst_interp gs
             ∗ "Hob_st" ∷ ob_st_interp gr σ (Candidate.initials gr)
             ∗ "Hannot_interp" ∷ annot_interp ∅
             ∗ "Htpwp" ∷ tpwp gs σs Φs)
        -∗ |={⊤}[∅]▷=>^ (size (Candidate.non_initial_eids gr)) |==> ▷ |==>
         tppost σs' Φs ∗ ∃ (σ': ob_st), "Hob_st" ∷ ob_st_interp gr σ' (Candidate.valid_eid gr))%I.
  Proof.
    iIntros (??? Hnum_thd Htpstep Htpinit Htpdone). iIntros "[% H]".
    iApply bupd_step_fupdN_bupd. iMod "H". iNamed "H".
    iMod (adequacy_post_hold gs σs σs' Φs with "[] [] [] Hgs Hannot_interp [] Htpwp")
      as "(%&%&Hea&%Hdom&Hpost_hold)" ;try assumption.
    iApply (big_sepL2_impl (λ idx σ σ', ⌜∃ n, nsteps (LThreadStep.t gs (idx_to_tid idx)) (S n) σ σ'⌝%I)).
    rewrite big_sepL2_pure. iPureIntro. assumption. iModIntro. iIntros (? ? ? ? ? [? ?]). iExists _. iPureIntro; eassumption.
    iApply (big_sepL_impl (λ idx σ , ⌜∃ pg, LThreadState.at_progress σ pg ∧
                                          ThreadState.progress_is_init gs.(GlobalState.gs_graph) (idx_to_tid idx) pg⌝%I)).
    rewrite big_sepL_pure. iPureIntro;assumption. iModIntro. iIntros (? ? ? [? ?]). iExists _. iPureIntro;eassumption.
    iPureIntro; assumption. iPureIntro; assumption.
    iModIntro.
    iNamed "Hea".
    iDestruct (adequacy_ob with "[$Hob_st] [Hea_fe]") as "Hna";try eassumption.
    rewrite -Hea_dom_eq in Hdom. exact Hdom.
    iSplit;first iPureIntro. eassumption. iFrame. iPureIntro;assumption.
    iApply (step_fupdN_mono with "[-Hna] Hna"). iIntros "[Hna Hob_st]".
    iMod ("Hpost_hold" with "Hna"). iFrame. clear;done.
  Qed.

  (* Iris version with pure post conditions *)
  Lemma adequacy_post_pure gs σs σs' (Φps : list (_ -> Prop)) :
    let gr := gs.(GlobalState.gs_graph) in
    AAConsistent.t gr ->
    AACandExec.NMSWF.wf gr ->
    S (length σs) = Candidate.num_of_thd gr ->
    (length σs = length σs' ∧
       ∀ idx σ σ', σs !! idx = Some σ → σs' !! idx = Some σ' → (∃ n, nsteps (LThreadStep.t gs (idx_to_tid idx)) (S n) σ σ')) ->
    (∀ idx σ, σs !! idx = Some σ → (∃ pg, LThreadState.at_progress σ pg ∧
                                          ThreadState.progress_is_init gr (idx_to_tid idx) pg)) ->
    (∀ (k:nat) σ, σs' !! k = Some σ → Terminated σ) ->
    (* WPs + initial interpretations *)
    ⊢ ((∃ (σ: ob_st), |==>
         "Hgs" ∷ □ gconst_interp gs
       ∗ "Hob_st" ∷ ob_st_interp gr σ (Candidate.initials gr)
       ∗ "Hannot_interp" ∷ annot_interp ∅
       ∗ "Htpwp" ∷ ([∗ list] idx ↦ σ;Φp ∈ σs;Φps,
                          ∃ `(_ : !irisGL) lσ, local_interp gs (idx_to_tid idx) (LThreadState.get_progress σ) lσ ∗
                            WP σ @ (idx_to_tid idx) {{ σ', ⌜Φp σ'⌝ }}))
       -∗ |={⊤}[∅]▷=>^ (size (Candidate.non_initial_eids gr)) |==> ▷ |==>
          ⌜length σs' = length Φps ∧ ∀ (idx: nat) σ' (Φ: _ -> Prop), σs' !! idx = Some σ' → Φps !! idx = Some Φ
                                                                   → Φ σ'⌝).
  Proof.
    iIntros (??? Hnum_thd Htpstep Htpinit Htpdone). iIntros "[% H]".
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
      iExists _,_. iFrame.
    }
    iDestruct (adequacy_post with "[-]") as "H";try eassumption.
    iFrame. clear;done.
    iApply (step_fupdN_mono with "[] H").
    iIntros ">H". iModIntro. iNext. iMod "H" as "[H _]". iModIntro.
    rewrite big_sepL2_fmap_r. rewrite big_sepL2_pure. iFrame.
  Qed.

End adequacy.

(* Final Coq level adequacy *)
Lemma adequacy_pure `{CMRA Σ} `{!invGpreS Σ} gs σs σs' (Φps : list (_ -> Prop)) :
  let gr := gs.(GlobalState.gs_graph) in
  AAConsistent.t gr ->
  AACandExec.NMSWF.wf gr ->
  S (length σs) = AACandExec.Candidate.num_of_thd gr ->
  (length σs = length σs' ∧
   ∀ idx σ σ', σs !! idx = Some σ → σs' !! idx = Some σ' → (∃ n, nsteps (LThreadStep.t gs (idx_to_tid idx)) (S n) σ σ')) ->
  (∀ idx σ, σs !! idx = Some σ → (∃ pg, LThreadState.at_progress σ pg ∧
                                        ThreadState.progress_is_init gr (idx_to_tid idx) pg)) ->
  (∀ (k:nat) σ, σs' !! k = Some σ → Terminated σ) ->
  (forall `{Hinv : !invGS_gen HasNoLc Σ},
      ⊢@{iProp Σ} |==> ∃ `(!irisG) (σ: ob_st),
       ("Hgs" ∷ □ gconst_interp gs
       ∗ "Hob_st" ∷ ob_st_interp gr σ (AACandExec.Candidate.initials gr)
       ∗ "Hannot_interp" ∷ annot_interp ∅
       ∗ "Htpwp" ∷ ([∗ list] idx ↦ σ;Φp ∈ σs;Φps, ∃ `(_ : !irisGL) lσ, local_interp gs (idx_to_tid idx) (LThreadState.get_progress σ) lσ
                                                                       ∗ WP σ @ (idx_to_tid idx) {{ σ', ⌜Φp σ'⌝ }}))) ->
  length σs' = length Φps ∧ forall (idx: nat) σ' (Φ: _ -> Prop), σs' !! idx = Some σ' → Φps !! idx = Some Φ → Φ σ'.
Proof.
  intros ??????? HH.
  eapply pure_soundness.
  eapply (step_fupdN_soundness_no_lc' _
            (size (AACandExec.Candidate.non_initial_eids gs.(GlobalState.gs_graph)) + 1)
            (size (AACandExec.Candidate.non_initial_eids gs.(GlobalState.gs_graph)) + 1)).
  intros. specialize (HH Hinv).

  iIntros "_".
  rewrite comm. rewrite (step_fupdN_add 1) /=. iMod HH as "(%Hiris & %prot & H)".

  iDestruct (@adequacy_post_pure Σ H Hinv Hiris gs σs σs' Φps with "[$H]") as "H";try assumption.
  clear;done.

  assert (Hfold:∀ P, (|={⊤}[∅]▷=>^1 P) ⊢@{iProp Σ} |={⊤}[∅]▷=> P) by done. iApply Hfold.
  rewrite -step_fupdN_add. rewrite Nat.add_comm /=. rewrite step_fupdN_add.
  iApply (step_fupdN_mono with "[] H").

  iIntros "H'". iMod "H'".
  iApply fupd_mask_intro. set_solver +.
  iIntros "Hclose". iNext. iMod "Hclose" as "_". iMod "H'" as "$". clear;done.
Qed.
