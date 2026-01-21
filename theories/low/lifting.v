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

From iris.proofmode Require Import tactics.

From self.low Require Export weakestpre.
From self Require Export iris_extra stdpp_extra.
Import uPred.

Section lifting.
  Context `{CMRA Σ}.
  Context `{!invGS_gen HasNoLc Σ}.
  Context `{!irisG}.
  Context `{!irisGL}.
  Implicit Types s : LThreadState.t.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : LThreadState.t → iProp Σ.
  Implicit Types Φs : list (LThreadState.t → iProp Σ).

  Lemma step_fupd_mono P Q E1 E2:
    (P -∗ Q) ⊢ (|={E1}[E2]▷=> P) -∗ |={E1}[E2]▷=> Q.
  Proof. iIntros "Himp >P". iModIntro. iNext. by iApply "Himp". Qed.

  (* [flow_eq], but has flow_out specified by [ea] *)
  Definition flow_eq_ea (gr: Graph.t) (e : Eid) (flow_in: mea Σ) (ea: sra Σ) (R: iProp Σ) : iProp Σ :=
    let d_lob := (Graph.lob_succ_of gr e) in
    flow_eq_dyn gr e flow_in (R ∗ ([∗ set] e_out ∈ d_lob, from_option (λ gm, from_option id emp (gm !! e)) emp (ea !! e_out)))%I.

  Definition ea_local_wf (gr: Graph.t) (ea : sra Σ) (na : mea Σ) : iProp Σ:=
      (* the map for each node is complete *)
      "%Hea_dom_eq" ∷ ⌜dom ea = dom na⌝ ∗
      (* WF of EA domain: for each node [e] in [ea],
         [gm] only remembers annotation on incoming edges of [e] *)
      "%Hea_lob_wf" ∷ ([∗ map] e ↦ gm ∈ ea, ⌜dom gm ⊆ (Graph.lob_pred_of gr e)⌝) ∗
      (* For each [e] in [ea], the edge annotations around it satisfy flow eq *)
      "Hea_fe" ∷ ([∗ map] e ↦ R ∈ na,
                    from_option (λ flow_in, flow_eq_ea gr e flow_in ea R) emp (ea !! e)).

  Lemma sswp_step gs tid s s' pg ls Φ :
    let gr := gs.(GlobalState.gs_graph) in
    AAConsistent.t gr ->
    AACand.NMSWF.wf gr ->
    LThreadStep.t gs tid s s' →
    LThreadState.at_progress s pg ->
    local_interp gs tid pg ls -∗
    (□ gconst_interp gs) -∗
    SSWP s @ tid {{ Φ }} -∗
    if (bool_decide (ThreadState.progress_is_valid gr tid pg)) then
      let e := (ThreadState.progress_to_node pg tid) in
        ∀ (na : mea Σ) (ea : sra Σ),
        "#Hannot_at_prog" ∷ na_at_progress gr tid pg na ∗
        "Hea_wf" ∷ ea_local_wf gr ea na ∗
        "Hinterp_annot" ∷ annot_interp na -∗
        |==> ▷ |==>
        let s_lob := (Graph.lob_pred_of gr e) in
        ∃ (R: iProp Σ) (na_used na_unused : mea Σ) (ls' : log_ts_t),
          "#Hna_split" ∷ na_splitting_wf s_lob na na_used na_unused ∗
          "Hinterp_annot" ∷ annot_interp ({[e := R]} ∪ na_unused ∪ na) ∗
          "Hea_wf" ∷ ea_local_wf gr ({[e := na_used]} ∪ ea) ({[e := R]} ∪ na_unused ∪ na) ∗
          "Hinterp_local" ∷  local_interp gs tid (LThreadState.get_progress s') ls' ∗
          "Hwp" ∷ Φ s'
    else
        ∀ (na : mea Σ) ,
        "Hinterp_annot" ∷ annot_interp na -∗
        |==> ▷ |==>
          ("Hinterp_annot" ∷ annot_interp na ∗
           "Hinterp_local" ∷  local_interp gs tid (LThreadState.get_progress s') ls ∗
           "Hwp" ∷ Φ s').
  Proof.
    iIntros (? Hgr_consist Hgr_wf Hstep Hpg) "Hls Hgs H". rewrite sswp_eq /sswp_def.
    rewrite (LThreadStep.step_not_terminated gs tid s s');[|assumption].

    iDestruct ("H" $! gs pg s' ls with "[$Hgs $Hls]") as "H". iPureIntro. repeat (split;try assumption).
    rewrite /gr.
    case_bool_decide as Hv.
    2:{
      iIntros (?) "H'". iNamed "H'".
      iDestruct ("H" $! na with "Hinterp_annot") as ">H".
      iModIntro. iNext. iMod "H" as "(?&?&?)".
      by iFrame.
    }
    iIntros (??) "H'". iNamed "H'".
    iDestruct ("H" $! na with "[$Hinterp_annot $Hannot_at_prog]") as ">H".
    iModIntro. iNext. iMod "H" as "(%&%&%&%&#Hna_split&FE&?&?&?)".
    (* iMod ("H" $! na with "[$Hinterp_annot $Hannot_at_prog]") as ">(%&%&%&%&#Hna_split&FE&?&?&?)". *)
    iModIntro. iExists R, na_used, na_unused, ls'. iFrame "Hna_split". iFrame.
    iNamed "Hna_split". iNamed "Hea_wf". iDestruct "Hannot_at_prog" as %Hna_dom_eq.
    rewrite /ea_local_wf.
    iDestruct (big_sepM2_alt with "Hnau_wf") as "[%Hnau_dom_eq _]".
    assert (dom na_used ⊆ dom na) as Hna_dom_sub.
    {
      assert (dom na_used ⊆ Graph.po_pred_of (GlobalState.gs_graph gs) (ThreadState.progress_to_node pg tid)) as Hsub.
      { etransitivity;try eassumption. apply Graph.lob_pred_of_subseteq_po;assumption. }
      rewrite LThreadStep.eids_from_init_po_pred_of in Hsub; [|assumption| assumption ].
      rewrite -Hna_dom_eq in Hsub. etransitivity;try eassumption. set_solver +.
    }
    iSplit;[|iSplit].
    - iPureIntro. rewrite !dom_union_L. rewrite Hea_dom_eq -Hnau_dom_eq. set_solver + Hna_dom_sub.
    - iPureIntro. apply map_Forall_union_2;[|assumption].
      apply map_Forall_singleton;assumption.
    - opose proof* (map_difference_union_exists na_unused na) as Hna_split.
      rewrite -Hnau_dom_eq. assumption.
      destruct Hna_split as [na_lob (Hnal_sub & Hnal_dom_eq & Hna_split)].
      rewrite -{2}Hna_split.
      rewrite big_sepM_union.
      2: { apply map_disjoint_dom. rewrite Hnal_dom_eq. set_solver +. }
      iDestruct "Hea_fe" as "[Hea_fe_upd Hea_fe_same]".
      rewrite -assoc. assert (na_unused ∪ na = na_unused ∪ (na ∖ na_unused)) as ->.
      {
        rewrite -{1}Hna_split. rewrite assoc.
        assert (na_unused ∪ na_lob = na_unused) as ->.
        {
          apply map_eq. intros. destruct (na_unused !! i) eqn:Hlk.
          rewrite lookup_union_l'. assumption. eexists;eassumption.
          apply lookup_union_None. split;first assumption. apply not_elem_of_dom. rewrite Hnal_dom_eq.
          apply not_elem_of_dom;assumption.
        }
        done.
      }
      assert (ThreadState.progress_to_node pg tid ∉ dom na) as Hcurr_nin.
      {
        intro Hin.
        assert (ThreadState.progress_to_node pg tid ∈ filter (Graph.is_local_node_of tid) (dom na)) as Hin'.
        rewrite elem_of_filter. split;done.
        rewrite Hna_dom_eq in Hin'.
        rewrite elem_of_filter in Hin'. destruct Hin' as [Hin' _].
        rewrite /= ThreadState.progress_of_node_to_node in Hin'.
        eapply ThreadState.progress_lt_refl_False;eassumption.
      }
      rewrite assoc. rewrite (big_sepM_union _ _ (na ∖ na_unused)).
      2: { apply map_disjoint_dom. set_solver + Hcurr_nin. }
      iSplitR "Hea_fe_same".
      + (* the interesting case *)
        rewrite big_sepM_union. rewrite big_sepM_singleton.
        2: {
          apply map_disjoint_dom.
          epose proof (Graph.not_elem_of_lob_pred_of _
                         (ThreadState.progress_to_node pg tid) Hgr_consist) as Hnin_lob.
          set_solver + Hnin_lob Hnau_dom_sub Hnau_dom_eq.
        }
        iSplitL "FE".
        * (* supply FE of the new node *)
          rewrite lookup_union_l';[|rewrite lookup_singleton;eexists;reflexivity].
          rewrite lookup_singleton /=.
          rewrite /flow_eq_ea /=.
          iApply (flow_eq_dyn_proper with "[] FE").
          {
            iModIntro. iNext. iIntros "$".
            epose proof (Graph.not_elem_of_lob_succ_of _
                          (ThreadState.progress_to_node pg tid) Hgr_consist) as Hnin_lob. rewrite /gr in Hnin_lob.
            iInduction (Graph.lob_succ_of (GlobalState.gs_graph gs) (ThreadState.progress_to_node pg tid))
              as [|e s_lob Hnin] "IH" using set_ind_L.
            - rewrite big_sepS_empty. clear;done.
            - rewrite big_sepS_union;last set_solver + Hnin.
              rewrite big_sepS_singleton.
              rewrite lookup_union_r.
              2: { apply lookup_singleton_None. set_solver + Hnin_lob. }
              destruct (ea !! e) eqn:Hlk.
              + (* We show contradiction by showing e1 -[po]> e2 and e2 -[po]> e1 *)
                pose proof Hlk as Hea_lk. apply Hea_lob_wf in Hlk.
                destruct (g !! (ThreadState.progress_to_node pg tid)) eqn:Hlk'.
                exfalso.
                assert ((ThreadState.progress_to_node pg tid) ∈ Graph.lob_pred_of (GlobalState.gs_graph gs) e) as Helem.
                { apply mk_is_Some in Hlk'. apply elem_of_dom in Hlk'.  set_solver + Hlk' Hlk. }
                apply Graph.elem_of_lob_pred_of_po in Helem. pose proof Helem as Hpo1. apply Graph.po_valid_eids in Helem. 2: assumption.
                destruct Helem as [Hvalid' Htid].
                assert (ThreadState.progress_to_node pg tid ∈ Graph.local_eids (GlobalState.gs_graph gs) tid) as Hvalid
                  by set_solver + Hvalid'.
                assert (e ∈ filter (Graph.is_local_node_of tid) (dom na)) as Hin.
                {
                  apply elem_of_filter. split. simpl in Htid. done. rewrite -Hea_dom_eq.
                  apply mk_is_Some in Hea_lk. apply elem_of_dom in Hea_lk.
                  set_solver + Hvalid' Hea_lk.
                }
                pose proof (ThreadState.progress_lt_po gr tid (ThreadState.progress_of_node e) pg) as Hpo2.
                ospecialize* Hpo2. assumption. destruct Hpo2 as [Hpo2 _].
                rewrite Hna_dom_eq in Hin. apply elem_of_filter in Hin. destruct Hin.
                ospecialize* Hpo2. split;[assumption|]. split.
                rewrite /ThreadState.progress_is_valid ThreadState.progress_to_node_of_node. set_solver + Hvalid'.
                done. done.
                rewrite ThreadState.progress_to_node_of_node in Hpo2.
                eapply Graph.po_irreflexive. eassumption. eassumption. assumption. done. assumption. assumption.
                iDestruct ("IH" with "[]") as "$". iPureIntro. set_solver + Hnin_lob.
                rewrite /= Hlk'. clear;done.
              + iDestruct ("IH" with "[]") as "$". iPureIntro. set_solver + Hnin_lob. clear;done.
          }
        * iInduction na_unused as [|e R_e_uu na_unused Hnin] "IH" using map_ind
                                    forall (na_lob Hnal_sub Hnal_dom_eq Hna_split na_used Hnau_dom_sub Hnau_dom_eq Hna_dom_sub).
          rewrite big_sepM_empty. clear;done.
          assert (is_Some (na_lob !! e)) as [R_e Hna_lob_lk].
          { apply elem_of_dom. rewrite Hnal_dom_eq. set_solver + Hnal_dom_eq. }
          assert (<[e := R_e]> (delete e na_lob) = na_lob) as <-. by apply insert_delete.
          rewrite big_sepM_insert. 2:{ apply lookup_delete_None. left;done. }
          rewrite big_sepM_insert;[|assumption].
          iDestruct ("Hea_fe_upd") as "[Hfe_e Hea_fe]".
          iSplitL "Hfe_e".
          {
            rewrite lookup_union_r.
            2: {
              rewrite lookup_singleton_None. intros <-.
              eapply (Graph.not_elem_of_lob_pred_of _ (ThreadState.progress_to_node pg tid));try eassumption.
              rewrite Hnau_dom_eq in Hnau_dom_sub. set_solver + Hnau_dom_sub.
            }
            destruct (decide (is_Some (ea !! e))) as [[gm ->]|Hn];simpl.
            2: {
              assert (ea !! e = None) as ->.
              apply not_elem_of_dom. intro. apply Hn. by apply elem_of_dom.
              iFrame.
            }
            iClear "IH".
            rewrite /flow_eq_ea.
            iApply (flow_eq_dyn_proper with "[] Hfe_e").
            {
              iModIntro. iNext.
              iIntros "[R_na R_out]".
              assert (is_Some (na_used !! e)) as [R_e_u Hnau_lob_lk].
              { apply elem_of_dom. set_solver + Hnau_dom_eq. }
              iDestruct (big_sepM2_lookup _ _ _ e R_e_u R_e_uu with "Hnau_wf") as "#Hnau_wf_k".
              done. apply lookup_insert_Some;left;clear;done.
              assert (na !! e = Some R_e) as Hna_lk.
              { rewrite map_subseteq_spec in Hnal_sub. apply Hnal_sub. assumption. }
              rewrite Hna_lk /=.
              iDestruct ("Hnau_wf_k" with "R_na") as "[R_na $]".
              iInduction (Graph.lob_succ_of (GlobalState.gs_graph gs) e)
                as [|e_succ s_lob_succ H_e_succ_nin] "IH" using set_ind_L.
              rewrite 2!big_sepS_empty. iFrame.
              rewrite big_sepS_union;last set_solver + H_e_succ_nin. rewrite big_sepS_singleton.
              rewrite big_sepS_union;last set_solver + H_e_succ_nin. rewrite big_sepS_singleton.
              iDestruct "R_out" as "[R_e_succ R_lob_out]".
              destruct (decide (ThreadState.progress_to_node pg tid = e_succ )) as [-> |Hneq].
              - rewrite lookup_union_l'. rewrite lookup_singleton /=. rewrite Hnau_lob_lk /=. iFrame.
                iApply (big_sepS_impl with "R_lob_out").
                iModIntro. iIntros (? Hin) "?".
                rewrite lookup_union_r. iFrame. rewrite lookup_singleton_None. set_solver + Hin H_e_succ_nin.
                eexists; apply lookup_singleton_Some;split; reflexivity.
              - rewrite lookup_union_r. 2:{ apply lookup_singleton_None. assumption. }
                iFrame "R_e_succ". iApply ("IH" with "R_lob_out R_na").
            }
          }
          iSpecialize ("IH" $! (delete e na_lob) with "[] [] []").
          { iPureIntro. etransitivity;[|eassumption]. apply delete_subseteq. }
          { iPureIntro. rewrite dom_delete. rewrite Hnal_dom_eq. rewrite -not_elem_of_dom in Hnin. set_solver + Hnin. }
          { iPureIntro. rewrite -{2}Hna_split.
            apply map_eq. intros.
            destruct (decide (i=e)) as [->|Hneq].
            rewrite lookup_union_r. rewrite lookup_union_l. rewrite Hna_lob_lk. rewrite lookup_difference_Some.
            split;try assumption. rewrite map_subseteq_spec in Hnal_sub. by apply Hnal_sub.
            apply lookup_difference_None. right;apply lookup_insert_is_Some. left;done.
            apply lookup_delete_None. left;done.
            destruct (decide(i ∈ dom na_lob)).
            - rewrite lookup_union_l'. rewrite lookup_delete_ne;try assumption.
              rewrite lookup_union_l';try assumption. reflexivity. by apply elem_of_dom.
              symmetry. assumption.
              rewrite lookup_delete_ne. by apply elem_of_dom.
              symmetry. assumption.
            - rewrite lookup_union_r. rewrite lookup_union_r.
              destruct ((na ∖ na_unused) !! i) eqn:Hlk; symmetry.
              apply lookup_difference_Some. apply lookup_difference_Some in Hlk.
              rewrite lookup_insert_ne;try assumption. symmetry;assumption.
              apply lookup_difference_None. apply lookup_difference_None in Hlk.
              rewrite lookup_insert_ne. assumption. symmetry;assumption. by apply not_elem_of_dom.
              rewrite lookup_delete_ne. by apply not_elem_of_dom.
              symmetry;assumption.
          }
          iSpecialize ("IH" $! (delete e na_used) with "[] [] [] []").
          { iPureIntro. etransitivity;[|eassumption]. apply subseteq_dom. apply delete_subseteq. }
          {
            iPureIntro. rewrite dom_delete_L. rewrite Hnau_dom_eq.
            apply not_elem_of_dom in Hnin. set_solver + Hnin.
          }
          {
            iPureIntro. rewrite dom_delete. set_solver + Hna_dom_sub.
          }
          {
            iModIntro.
            iDestruct (big_sepM2_alt with "Hnau_wf") as "[%Hna_u_dom _]".
            rewrite set_eq in Hna_u_dom. pose proof (Hna_u_dom e) as [_ Hna_u_dom'].
            ospecialize* Hna_u_dom'. rewrite dom_insert_L. set_solver +.
            rewrite elem_of_dom in Hna_u_dom'. destruct Hna_u_dom' as [? Hnau_lk].
            iDestruct (big_sepM2_delete _ _ _ e with "Hnau_wf") as "[_ Hnau_wf']";first eassumption.
            rewrite lookup_insert. reflexivity.
            rewrite delete_insert_delete.
            iClear "Hnau_wf".
            assert (delete e na_unused = na_unused) as <-. rewrite delete_notin //.
            rewrite delete_idemp.
            iApply (big_sepM2_proper with "Hnau_wf'").
            intros k?? Hlk1 Hlk2.
            assert (k ≠ e) as Hneq. { intros ->. rewrite lookup_delete_Some in Hlk1. destruct Hlk1. contradiction. }
            ospecialize* (Hna_u_dom k).
            rewrite lookup_delete_ne in Hlk1. reflexivity. symmetry;assumption.
          }
          iSpecialize ("IH" with "Hea_fe"). iApply (big_sepM_impl with "IH").
          {
            iModIntro. iIntros (?? Hlk) "H".
            assert (ThreadState.progress_to_node pg tid ≠ k) as Hneq.
            {
              intros <-.
              assert (ThreadState.progress_to_node pg tid ∈ dom na_unused) as Hin. apply elem_of_dom. eexists;eassumption.
              rewrite dom_insert_L in Hnau_dom_eq. rewrite dom_insert in Hnal_dom_eq.
              apply Hcurr_nin. apply subseteq_dom in Hnal_sub.
              rewrite Hnal_dom_eq in Hnal_sub. set_solver + Hin Hnal_sub.
            }
            rewrite lookup_union_r. 2:{ apply lookup_singleton_None. assumption. }
            rewrite lookup_union_r. 2:{ apply lookup_singleton_None. assumption. }

            destruct (decide (is_Some (ea !! k))) as [[gm Hlk_gm]|Hn].
            2: {
              assert (ea !! k = None) as ->.
              apply not_elem_of_dom. intro. apply Hn. by apply elem_of_dom.
              iFrame.
            }
            rewrite Hlk_gm /=.
            rewrite /flow_eq_ea.
            iApply (flow_eq_dyn_proper with "[] H").
            {
              iModIntro. iNext. iIntros "[$ H]". iApply (big_sepS_impl with "H"). iIntros (e_succ Hin). iModIntro.
              destruct (decide (ThreadState.progress_to_node pg tid = e_succ )) as [-> |Hneq'].
              - rewrite lookup_union_l'. rewrite lookup_singleton /=.
                rewrite lookup_union_l'. rewrite lookup_singleton /=.
                rewrite lookup_delete_ne. iIntros "$".
                intros ->. rewrite Hlk in Hnin. inversion Hnin. rewrite lookup_singleton. eexists;reflexivity. rewrite lookup_singleton. eexists;reflexivity.
              - rewrite lookup_union_r. rewrite lookup_union_r.
                iIntros "$".
                apply lookup_singleton_None. assumption. apply lookup_singleton_None. assumption.
            }
          }
      + (* the boring case *)
        iApply (big_sepM_impl with "Hea_fe_same").
        iModIntro. iIntros (?? Hlk) "H".
        rewrite lookup_union_r.
        2:{
          apply lookup_singleton_None.
          rewrite lookup_difference_Some in Hlk.
          destruct Hlk as [Hlk _].
          intros <-. apply Hcurr_nin. apply elem_of_dom. eexists;eassumption.
        }
        destruct (decide (is_Some (ea !! k))) as [[gm Hlk_gm]|Hn].
        2: {
          assert (ea !! k = None) as ->.
          apply not_elem_of_dom. intro. apply Hn. by apply elem_of_dom.
          iFrame.
        }
        rewrite Hlk_gm /=. rewrite /flow_eq_ea.
        iApply (flow_eq_dyn_proper with "[] H").
        {
          iModIntro. iNext. iIntros "[$ H]". iApply (big_sepS_impl with "H"). iIntros (e_succ Hin). iModIntro.
          destruct (decide (ThreadState.progress_to_node pg tid = e_succ )) as [-> |Hneq'].
          * rewrite lookup_union_l'. rewrite lookup_singleton /=.
            rewrite lookup_difference_Some in Hlk. destruct Hlk as [_ Hlk].
            apply not_elem_of_dom in Hlk. rewrite -Hnau_dom_eq in Hlk. apply not_elem_of_dom in Hlk. rewrite Hlk.
            iIntros "_". clear;done.
            rewrite lookup_singleton. eexists;reflexivity.
          * rewrite lookup_union_r.
            iIntros "$". apply lookup_singleton_None. assumption.
        }
  Qed.

  Lemma wp_step gs tid s s' pg ls Φ :
    let gr := gs.(GlobalState.gs_graph) in
    AAConsistent.t gr ->
    AACand.NMSWF.wf gr ->
    LThreadStep.t gs tid s s' →
    LThreadState.at_progress s pg ->
    local_interp gs tid pg ls -∗
    (□ gconst_interp gs) -∗
    WP s @ tid {{ Φ }} -∗
    if (bool_decide (ThreadState.progress_is_valid (gs.(GlobalState.gs_graph)) tid pg)) then
      let e := (ThreadState.progress_to_node pg tid) in
        ∀ (na : mea Σ) (ea : sra Σ),
        "#Hannot_at_prog" ∷ na_at_progress gr tid pg na ∗
        "Hea_wf" ∷ ea_local_wf gr ea na ∗
        "Hinterp_annot" ∷ annot_interp na -∗
        |==> ▷ |==>
        let s_lob := (Graph.lob_pred_of gr e) in
        ∃ (R: iProp Σ) (na_used na_unused : mea Σ) (ls' : log_ts_t),
          "#Hna_split" ∷ na_splitting_wf s_lob na na_used na_unused ∗
          "Hinterp_annot" ∷ annot_interp ({[e := R]} ∪ na_unused ∪ na) ∗
          "Hea_wf" ∷ ea_local_wf gr ({[e := na_used]} ∪ ea) ({[e := R]} ∪ na_unused ∪ na) ∗
          "Hinterp_local" ∷  local_interp gs tid (LThreadState.get_progress s') ls' ∗
          "Hwp" ∷ WP s' @ tid {{ Φ }}
    else
        ∀ (na : mea Σ) ,
        "Hinterp_annot" ∷ annot_interp na -∗
        |==> ▷ |==>
          ("Hinterp_annot" ∷ annot_interp na ∗
             "Hinterp_local" ∷  local_interp gs tid (LThreadState.get_progress s') ls ∗
            "Hwp" ∷ WP s' @ tid {{ Φ }}).
  Proof.
    iIntros (? Hgr_consist Hgr_wf Hstep Hpg) "Hls Hgs H".
    rewrite wp_sswp. iApply (sswp_step with "Hls Hgs H");assumption.
  Qed.

  Lemma step_bupdN_mono n P Q:
    (P -∗ Q) ⊢ (Nat.iter n (λ P, |==> ▷ |==> P) P) -∗ Nat.iter n (λ P, |==> ▷ |==> P) Q.
  Proof.
    iIntros "Himp P".
    iInduction n as [|] "IH" . by iApply "Himp".
    rewrite 2!Nat.iter_succ.
    iMod "P". iModIntro. iNext. iMod "P". iModIntro.
    iApply ("IH" with "Himp"). done.
  Qed.

  Lemma wp_steps (n : nat) gs (tid : Tid) s pg s' ls Φ :
    let gr := gs.(GlobalState.gs_graph) in
    AAConsistent.t gr ->
    AACand.NMSWF.wf gr ->
    nsteps (LThreadStep.t gs tid) n s s' →
    Terminated s' →
    LThreadState.at_progress s pg ->
    local_interp gs tid pg ls -∗
    (□ gconst_interp gs) -∗
    WP s @ tid {{ Φ }} -∗
    ∀ (na : mea Σ) (ea : sra Σ),
    "#Hannot_at_prog" ∷ na_at_progress gr tid pg na ∗
    "Hea_wf" ∷ ea_local_wf gr ea na ∗
    ("Hinterp_annot" ∷ annot_interp na) -∗
    Nat.iter n (λ P, |==> ▷ |==> P)
    (∃ na' ea' ls',
      annot_interp na' ∗
      ea_local_wf gr ea' na' ∗
      "Hinterp_local" ∷ local_interp gs tid (LThreadState.get_progress s') ls' ∗
      (* FEs hold for nodes in the middle, [s,s') *)
      ⌜LThreadStep.eids_between gr tid s s' ∪ dom na = dom na'⌝ ∗
      post_lifting Φ tid s').
  Proof.
    revert s s' pg ls Φ.
    induction n as [|n IH]=> s s' pg ls Φ /=.
    {
      inversion_clear 3. intros Hterm Hpg.
      iIntros "? ? WP". iIntros (??) "H".
      iExists na,ea,ls. rewrite Hpg /=. iNamed "H". iFrame.
      rewrite LThreadStep.traversed_eids_empty.
      iSplit;first (iPureIntro;set_solver+).
      iDestruct (wp_terminated_inv' with "WP") as "$"; done.
    }
    (* Induction case *)
    (* preparation *)
    iIntros (Hgr_cs Hgr_wf Hsteps Hterm Hpg) "Hls #Hgs Hwp".
    inversion_clear Hsteps as [|? ? ?s'' ? Hstep Hsteps'].
    iIntros (??) "H". iNamed "H".
    iDestruct (wp_step with "Hls Hgs Hwp") as "Step";try eassumption.
    erewrite LThreadStep.steps_traversed_eids_union;try eassumption.
    (* Case on the validity of [pg] *)
    case_bool_decide as Hv.
    (* case_bool_decide as Hpg_valid. *)
    { (* Case valid: update [na] *)
      iMod ("Step" $! na ea with "[$Hannot_at_prog $Hea_wf $Hinterp_annot]") as "Step".
      iModIntro. iNext. iMod "Step" as "(%&%&%&%&H)".
      iNamed "H". iNamed "Hna_split".
      iDestruct "Hannot_at_prog" as %Hannot_at_prog.
      iDestruct (big_sepM2_alt with "Hnau_wf") as "[%Hnauu_dom _]".
      assert (dom (na_unused ∪ na) = dom na) as Hnau_dom_eq.
      {
        erewrite <-(LThreadStep.eids_from_init_po_pred_of _ tid pg) in Hannot_at_prog;try eassumption.
        rewrite dom_union_L.
        assert (dom na_used ⊆ dom na) as Hsub.
        {
          etransitivity. exact Hnau_dom_sub. etransitivity. apply Graph.lob_pred_of_subseteq_po;first assumption. assumption.
          rewrite -Hannot_at_prog.
          intros ? Hin. rewrite elem_of_filter in Hin. destruct Hin;assumption.
        }
        set_solver + Hsub Hnauu_dom.
      }
      specialize (IH s'' s' (LThreadState.get_progress s'') ls' Φ Hgr_cs Hgr_wf Hsteps' Hterm).
      iDestruct (IH with "Hinterp_local Hgs Hwp") as "IH";first done.
      iSpecialize ("IH" $! ({[ThreadState.progress_to_node pg tid := R]} ∪ na_unused ∪ na) ({[ThreadState.progress_to_node pg tid := na_used]} ∪ ea)).
      iDestruct ("IH" with "[$Hea_wf $Hinterp_annot]") as "IH".
      {
        iPureIntro.
        rewrite -assoc. rewrite dom_union_L dom_singleton_L. rewrite filter_union_L filter_singleton_L;last reflexivity.
        rewrite Hnau_dom_eq Hannot_at_prog.
        rewrite (LThreadStep.step_traversed_eids_from_init_union s s'' Hstep).
        case_bool_decide;subst pg. reflexivity. contradiction.
      }

      iModIntro.
      iApply (step_bupdN_mono with "[] IH").
      iIntros "(%&%&%ls''&Hinterp_annot&Hea_wf&Hls&Hdom&Hpost)".
      iExists na',ea', ls''. iFrame.
      rewrite -assoc. rewrite dom_union_L. rewrite dom_singleton_L.
      rewrite Hnau_dom_eq. iDestruct "Hdom" as %Hdom.
      iPureIntro. subst pg. case_bool_decide;last contradiction. set_solver + Hdom.
    }
    { (* Case invalid: keep [na] unchanged *)
      specialize (IH s'' s' (LThreadState.get_progress s'') ls Φ Hgr_cs Hgr_wf Hsteps' Hterm).
      (* rewrite {1}interp_mod_eq /interp_mod_def. *)
      iMod ("Step" with "Hinterp_annot") as "Step".
      iModIntro. iNext. iMod "Step" as "[Hinterp_annot Hwp]".
      iNamed "Hwp".
      iDestruct (IH with "Hinterp_local Hgs Hwp") as "IH";first done.
      iModIntro.

      iDestruct ("IH" with "[$Hea_wf $Hinterp_annot]") as "IH".
      {
        iDestruct "Hannot_at_prog" as %Hannot_at_prog. iPureIntro.
        rewrite Hannot_at_prog.
        rewrite (LThreadStep.step_traversed_eids_from_init_union s s'' Hstep).
        subst pg.

        case_bool_decide; first contradiction.
        rewrite union_empty_l_L. reflexivity.
      }

      iApply (step_bupdN_mono with "[] IH").
      iIntros "(%&%&%&?&?&?&?&?)".
      subst pg;case_bool_decide;first contradiction.
      rewrite union_empty_l_L. iFrame.
    }
  Qed.

End lifting.
