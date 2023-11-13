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

Notation mea Σ := (gmap Eid (iProp Σ)).
Notation sra Σ := (gmap Eid (mea Σ)).

Section definition.
Import Graph.

(** Node Annotation *)
(* resources that avaliable on each node *)
Class NodeAnnot `{CMRA Σ} :=
  {
    na_local_wf tid (na : mea Σ) := set_Forall (fun e => is_local_node_of tid e) (dom na);
    (* for all local nodes in [dom(na)], their progresses < current progress [ρ] *)
    na_at_progress (gr : Graph.t) (tid : Tid) (pg : ThreadState.progress) (na : mea Σ) : iProp Σ :=
      (* all local nodes in the domain of na are po pred of current node *)
      "%Hna_dom_eq" ∷ ⌜filter (λ e : Eid, Graph.is_local_node_of tid e) (dom na) = LThreadStep.eids_from_init gr tid pg⌝;
    na_splitting_wf (s_lob : gset Eid) (na na_used na_unused : mea Σ) : iProp Σ :=
      "%Hnau_dom_sub" ∷ ⌜dom na_used ⊆ s_lob⌝ ∗
      "#Hnau_wf" ∷ [∗ map] e ↦ Pu;Puu ∈ na_used;na_unused,
          (* it is a almost pure equiv (by the plain modality),
             so that nothing in the spatial ctxt (nor non-plain persistent ctxt) can be used *)
          ▷ ■ (Pu ∗ Puu ∗-∗ from_option (λ P, P) emp (na !! e));
    na_full (gr : Graph.t) (na : mea Σ) : iProp Σ :=
      "%Hna_dom_full" ∷ ⌜dom na = Candidate.non_initial_eids gr⌝;
  }.

#[global] Instance na_instance `{CMRA Σ}: NodeAnnot := {}.

(** Protocols *)
Definition prot_t Σ := Addr -> Val -> (Eid -> iProp Σ).

Class Protocol `{CMRA Σ} := {
    prot_node : (Eid -> iProp Σ);
  }.

(** Flow Equations *)

Class FlowEq `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!Protocol} := {
    flow_eq (s_lob s_obs : gset Eid) (e : Eid) (na: mea Σ) (R: iProp Σ) : iProp Σ :=
        "R_lob_in" ∷ ([∗ set] e_in ∈ s_lob, from_option id True%I (na !! e_in)) ∗
        "#R_obs_in" ∷ □([∗ set] e_in ∈ s_obs, prot_node e_in)
        ={⊤,∅}=∗ ▷ |={∅,⊤}=>
        "R_obs_out" ∷ □(prot_node e) ∗
        "R_na" ∷ R;
    flow_eq_ea (s_lob s_obs : gset Eid) (e : Eid) (gm: mea Σ) (ea: sra Σ) (R: iProp Σ) : iProp Σ :=
        "R_lob_in" ∷ ([∗ map] _ ↦ R_in ∈ gm, R_in) ∗
        "#R_obs_in" ∷ □([∗ set] e_in ∈ s_obs, prot_node e_in)
        ={⊤,∅}=∗ ▷ |={∅,⊤}=>
        "#R_obs_out" ∷ □(prot_node e) ∗
        "R_na" ∷ R ∗
        "R_lob_out" ∷ ([∗ set] e_out ∈ s_lob,
           from_option (λ gm, from_option id emp (gm !! e)) emp (ea !! e_out));
  }.

#[global] Instance flow_eq_instance `{CMRA Σ} `{!invGS_gen HasNoLc Σ} `{!Protocol} : FlowEq := {}.

Class FlowEqWOProt `{CMRA Σ} `{!invGS_gen HasNoLc Σ} := {
    (* the version without mentioning protocols *)
    flow_eq_ea_wo_prot (s_ob : gset Eid)
      (e : Eid) (gm : mea Σ) (ea: sra Σ) (R: iProp Σ) : iProp Σ :=
        "R_in" ∷ ([∗ map] _ ↦ R_in ∈ gm, R_in)
        ={⊤,∅}=∗ ▷ |={∅,⊤}=>
        "R" ∷ R ∗
        "R_out" ∷ ([∗ set] e_out ∈ s_ob,
           from_option (λ gm, from_option id emp (gm !! e)) emp (ea !! e_out))
  }.

#[global] Instance flow_eq_final_instance `{CMRA Σ} `{!invGS_gen HasNoLc Σ} : FlowEqWOProt := {}.

(** Ob-edge Annotation *)

Class EdgeAnnot `{FlowEq} :=
  {
    ea_lob_wf (gr :  Graph.t) (ea : sra Σ) (na : mea Σ) : iProp Σ:=
      (* the map for each node is complete *)
      "%Hea_dom_eq" ∷ ⌜dom ea = dom na⌝ ∗
      "%Hea_lob_wf" ∷ ([∗ map] e ↦ gm ∈ ea, ⌜dom gm ⊆ (Graph.lob_pred_of gr e)⌝) ∗
      "Hea_fe" ∷ ([∗ map] e ↦ R ∈ na,
                    from_option
                      (λ gm,
                         let s_obs := (Graph.obs_pred_of gr e) in
                         let s_lob := (Graph.lob_succ_of gr e) in
                         flow_eq_ea s_lob s_obs e gm ea R) emp (ea !! e) );
    (* This version is used for ob induction *)
    ea_lob_wf_ind (gr :  Graph.t) (ea : sra Σ) (na : mea Σ) : iProp Σ:=
      (* the map for each node is complete *)
      "%Hea_lob_wf" ∷ ([∗ map] e ↦ gm ∈ ea, ⌜dom gm ⊆ (Graph.lob_pred_of gr e)⌝) ∗
      "Hea_fe" ∷ ([∗ map] e ↦ gm ∈ ea,
                 from_option
                      (λ R, let s_obs := (Graph.obs_pred_of gr e) in
                            let s_lob := (Graph.lob_succ_of gr e) in
                            flow_eq_ea s_lob s_obs e gm ea R) emp (na !! e));
  }.

#[global] Instance ea_instance `{FlowEq}: EdgeAnnot := {}.

Class EdgeAnnotWOProt `{FlowEqWOProt}:=
  {
    ea_ob_wf (gr :  Graph.t) (ea : sra Σ) (na : mea Σ) : iProp Σ :=
      "%Hea_dom_eq" ∷ ⌜dom ea = dom na⌝ ∗
      "%Hea_ob_wf" ∷ ([∗ map] e ↦ gm ∈ ea, ⌜dom gm ⊆ (Graph.ob_pred_of gr e)⌝) ∗
      "Hea_fe" ∷ ([∗ map] e ↦ R;gm ∈ na;ea,
          let s_ob := (Graph.ob_succ_of gr e) in
          flow_eq_ea_wo_prot s_ob e gm ea R);
    ea_ob_wf_ind (gr :  Graph.t) (ea : sra Σ) (na : mea Σ) : iProp Σ :=
      "%Hea_ob_wf" ∷ ([∗ map] e ↦ gm ∈ ea, ⌜dom gm ⊆ (Graph.ob_pred_of gr e)⌝) ∗
      "Hea_fe" ∷ ([∗ map] e ↦ gm ∈ ea,
                    from_option
                      (λ R, let s_ob := (Graph.ob_succ_of gr e) in
                            flow_eq_ea_wo_prot s_ob e gm ea R) emp (na !! e));
  }.

#[global] Instance eawo_instance `{FlowEqWOProt}: EdgeAnnotWOProt := {}.

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

  (* the version used in the induction proof is equivalent with the one used in the conclusion *)
  Lemma ea_ob_wf_ind_equiv gr node_annot edge_annot:
    ⌜dom edge_annot = dom node_annot ⌝ ∗ ea_ob_wf_ind gr edge_annot node_annot ⊣⊢
    ea_ob_wf gr edge_annot node_annot.
  Proof.
    iSplit. iIntros "[% H]". iNamed "H". iSplit. iPureIntro;done.
    iSplit. iPureIntro;done.
    rewrite big_sepM_sepM2_zip // big_sepM2_flip //.
    iNamed 1. iSplit. iPureIntro;done.
    iSplit. iPureIntro;done.
    rewrite big_sepM_sepM2_zip // big_sepM2_flip //.
  Qed.

  Context `{!Protocol}.

  (* the induction proof of FSL style phase two *)
  Lemma ea_obs_saturation_aux gr node_annot edge_annot:
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    dom edge_annot = Candidate.valid_eid gr ->
    dom edge_annot = dom node_annot ->
    forall edge_annot_last,
    ob_semi_last_set gr (dom edge_annot_last) (dom edge_annot) ->
    edge_annot_last ⊆ edge_annot ->
      ea_lob_wf_ind gr edge_annot_last node_annot -∗
      (ea_ob_wf_ind gr
        (map_imap (λ e gm, Some ((set_fold (λ e' acc, <[e' := (□(prot_node e'))%I]>acc) ∅
                              (obs_pred_of gr e)) ∪ gm)) edge_annot_last) node_annot).
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
      iIntros "Hea". iNamed "Hea".
      iSplit; apply dom_empty_inv_L in Heal_dom; subst eal; rewrite map_imap_empty;
      rewrite big_sepM_empty //. rewrite big_sepM_empty //.
    }
    {
      clear eal Heal_last Heal_sub.
      intros ef sl Hef_nv Hef_elem Hsl_last Hef_first IHsl. rewrite /P in IHsl.
      rewrite /P /=.
      intros eal Heal_dom Heal_last Heal_sub. iIntros "Hea". iNamed "Hea".

      (* split FEs into current FE and the rest *)
      assert (is_Some (eal !! ef)) as [gmf Heal_lk].
      { apply elem_of_dom. rewrite Heal_dom. set_solver +. }
      assert (<[ef := gmf]> eal = eal) as Heal_ins by rewrite insert_id //.
      rewrite -{2}Heal_ins. clear Heal_ins.
      rewrite big_sepM_insert_delete. iDestruct "Hea_fe" as "[FE Hea_fe]".
      assert (is_Some (node_annot !! ef)) as [R Hna_lk].
      { apply elem_of_dom. rewrite -Hea_dom_eq. set_solver + Hef_elem. }
      rewrite Hna_lk /=.

      (* apply IH *)
      assert (dom (delete ef eal) = sl) as Hsl_dom.
      { rewrite dom_delete_L Heal_dom. set_solver + Hef_nv. }

      specialize (IHsl (delete ef eal)). feed specialize IHsl.
      exact Hsl_dom.
      rewrite Hsl_dom. destruct Hsl_last;done.
      etransitivity;last exact Heal_sub. apply delete_subseteq.
      iDestruct (IHsl with "[Hea_fe]") as "IH".
      {
        iSplit. { iPureIntro. by apply map_Forall_delete. }
        iApply (big_sepM_impl with "Hea_fe").
        iModIntro. iIntros (e gm Hea_lk_e).
        iIntros "FE". destruct (decide (is_Some (node_annot !! e))) as [[R_e ->]|Hn];simpl.
        2:{
          assert (node_annot !! e = None) as ->;auto.
          apply not_elem_of_dom. intro. apply Hn. by apply elem_of_dom.
        }
        iIntros "R_in". iDestruct ("FE" with "[R_in]") as ">R_e". done.
        iModIntro. iNext. iMod "R_e".
        iNamed "R_e". iModIntro. iFrame "R_na R_obs_out".
        iApply (big_sepS_impl with "R_lob_out").
        iModIntro. iIntros (? Hx_lob).
        {
         (* x ≠ ef *)
          rewrite lookup_delete_ne;auto.
          destruct (decide (x ∈ sl)) as [Hx_in | Hx_nin]. set_solver + Hx_in Hsl_dom.
          assert (x ∈ dom edge_annot) as Hx_in_all.
          { rewrite Hea_full.  pose proof (elem_of_lob_succ_of_valid _ _ _ Hwf Hx_lob) as Hsub. set_solver + Hsub. }
          destruct Hsl_last as [_ Hsl_last].
          specialize (Hsl_last e). feed specialize Hsl_last.
          apply elem_of_dom_2 in Hea_lk_e. rewrite Hsl_dom // in Hea_lk_e.
          simpl in Hsl_last. exfalso. eapply (Hsl_last x). set_solver + Hx_nin Hx_in_all.
          apply elem_of_ob_pred_of.
          rewrite elem_of_ob_pred_of_succ. eapply lob_succ_of_subseteq_ob;eauto.
        }
      }
      iSplit.
      {
        iPureIntro. intros x gm Hlk. specialize (Hea_lob_wf x).
        rewrite map_lookup_imap in Hlk. destruct (eal !! x);inversion Hlk.
        specialize (Hea_lob_wf g). feed specialize Hea_lob_wf. done.
        rewrite dom_union_L. rewrite (set_fold_to_gmap_dom (obs_pred_of gr x) (λ e, (□ prot_node e)%I)).
        pose proof (ob_pred_of_disj_union gr x Hwf Hcs) as [Hsub _].
        etrans. 2:exact Hsub.
        apply union_subseteq.
        split. apply union_subseteq_r'. set_solver +. apply union_subseteq_l'. set_solver + Hea_lob_wf.
      }
      (* split FE of ef from the goal *)
      rewrite -{4}(insert_delete eal ef gmf);auto.
      rewrite map_imap_insert. rewrite map_imap_delete.
      rewrite big_sepM_insert_delete. rewrite delete_idemp.
      (* show FE of ef and the rest separately *)
      iSplitL "FE".
      { (* FE *)
        rewrite Hna_lk /=. iIntros "R_in".
        iDestruct ("FE" with "[R_in]") as ">R_out".
        { (* show we have all R_in (sth. about set_fold)*)
          rewrite big_sepM_union. iDestruct "R_in" as "[R_obs_in $]".
          2:{
            apply map_disjoint_dom. rewrite set_fold_to_gmap_dom.
            specialize (Hea_lob_wf ef gmf Heal_lk).
            pose proof (ob_pred_of_disj_union gr ef Hwf Hcs) as [_ Hdisj_lob_obs].
            set_solver + Hdisj_lob_obs Hea_lob_wf.
          }
          rewrite big_sepS_fold_to_gmap.
          iDestruct "R_obs_in" as "#R_obs_in".
          iModIntro.
          iApply (big_sepS_impl with "R_obs_in").
          iModIntro. iIntros (??) "#R". iFrame "R".
        }
        iModIntro. iNext. iMod "R_out". iModIntro.
        iNamed "R_out". iFrame.

        (* split the goal into lob and obs preds *)

        pose proof (ob_succ_of_disj_union gr ef Hwf Hcs) as [Hob_succ_sub Hdisj_lob_obs].
        pose proof (union_split_difference_intersection_subseteq_L (ob_succ_of gr ef) (lob_succ_of gr ef ∪ obs_succ_of gr ef)) as [-> Hdisj_lob_obs'].
        set_solver + Hob_succ_sub.
        (* pose proof (ob_succ_of_disj_union gr ef Hwf) as [-> Hdisj_lob_obs]. *)
        rewrite big_sepS_union;auto.
        iSplitR.
        {
          iApply big_sepS_impl.
          iApply big_sepS_emp. auto.
          iModIntro. iIntros (x Hlk) "_".
          rewrite  map_lookup_imap.
          destruct (eal !! x) eqn:Hlk_eal. simpl.
          2:{ simpl. auto. }
          rewrite lookup_union_r;auto.
          apply Hea_lob_wf in Hlk_eal.
          destruct (g !! ef) eqn:Hg.
          apply elem_of_dom_2 in Hg.
          assert (x ∉ lob_succ_of gr ef). apply elem_of_difference in Hlk. destruct Hlk as [_ Hnotin].
          apply not_elem_of_union in Hnotin. destruct Hnotin;assumption.
          assert (ef ∈ lob_pred_of gr x). set_solver + Hg Hlk_eal.
          apply elem_of_lob_pred_of_succ in H2. contradiction.
          rewrite Hg. auto.
          apply not_elem_of_dom.
          rewrite (set_fold_to_gmap_dom (obs_pred_of gr x) (λ e, (□ prot_node e)%I)).
          intro Hlk'. apply elem_of_obs_pred_of_succ in Hlk'.
          apply elem_of_difference in Hlk.
          destruct Hlk as [_ Hnotin].
          apply not_elem_of_union in Hnotin. destruct Hnotin;contradiction.
        }
        rewrite big_sepS_union;auto.
        iSplitL.
        { (* lob *)
          iApply (big_sepS_impl with "R_lob_out").
          iModIntro. iIntros (x Hlk) "R".
          rewrite  map_lookup_imap.
          destruct (eal !! x);last done.
          simpl. rewrite lookup_union_r;auto.
          apply not_elem_of_dom.
          rewrite (set_fold_to_gmap_dom (obs_pred_of gr x) (λ e, (□ prot_node e)%I)).
          intro Hlk'. apply elem_of_obs_pred_of_succ in Hlk'.
          apply (Hdisj_lob_obs x Hlk Hlk').
        }
        { (* obs: use prot_node ef *)
          iApply (big_sepS_impl). iApply big_sepS_emp. done.
          iModIntro. iIntros (x Hlk) "_".
          rewrite map_lookup_imap.
          destruct (eal !! x) eqn:Hlk';simpl;last done.
          rewrite lookup_union_l;auto.
          rewrite set_fold_to_gmap_lookup. done.
          by apply elem_of_obs_pred_of_succ.
          apply not_elem_of_dom.
          specialize (Hea_lob_wf x g Hlk'). intro Hin. simpl in Hea_lob_wf. specialize (Hea_lob_wf ef Hin).
          rewrite elem_of_lob_pred_of_succ in Hea_lob_wf.
          apply (Hdisj_lob_obs x Hea_lob_wf Hlk).
        }
        symmetry. apply disjoint_difference_r1. reflexivity.
      }
      { (* rest *)
        iNamed "IH".
        iApply (big_sepM_impl with "Hea_fe").
        iModIntro. iIntros (e gm Hlk) "FE".

        destruct (decide (is_Some (node_annot !! e))) as [[R_e ->]|Hn];simpl.
        2:{
          assert (node_annot !! e = None) as ->;auto.
          apply not_elem_of_dom. intro. apply Hn. by apply elem_of_dom.
        }

        iIntros "R_in_e". iMod ("FE" with "R_in_e") as "R_out_e".
        iModIntro. iNext. iMod "R_out_e". iModIntro.
        iNamed "R_out_e". iFrame.
        iApply (big_sepS_impl with "R_out").
        iModIntro. iIntros (x Hx_ob) "R_out".
        rewrite lookup_delete_ne. done.
        {
          (* x ≠ ef *)
          destruct (decide (x ∈ sl)) as [Hx_in | Hx_nin]. set_solver + Hx_in Hsl_dom.
          assert (x ∈ dom edge_annot) as Hx_in_all.
          { rewrite Hea_full.  pose proof (elem_of_ob_succ_of_valid _ _ _ Hwf Hx_ob) as Hsub. set_solver + Hsub. }
          destruct Hsl_last as [_ Hsl_last].
          specialize (Hsl_last e). feed specialize Hsl_last.
          rewrite lookup_delete_Some in Hlk. destruct Hlk as [Hneq Hlk].
          rewrite map_lookup_imap in Hlk.
          destruct (eal !! e) eqn:Heal_lk_e;inversion Hlk.
          apply elem_of_dom_2 in Heal_lk_e.
          set_solver + Heal_lk_e Hneq Hsl_dom.
          simpl in Hsl_last. exfalso. eapply (Hsl_last x). set_solver + Hx_nin Hx_in_all.
          apply elem_of_ob_pred_of.
          rewrite elem_of_ob_pred_of_succ //.
        }
      }
    }
    2:{ exact Heal_last. }
    { by apply subseteq_dom. }
    { reflexivity. }
    { done. }
    { done. }
  Qed.

  (* instantiate the induction proof above with [edge_annot] *)
  Lemma ea_obs_saturation_aux2 gr node_annot edge_annot:
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    dom edge_annot = Candidate.valid_eid gr ->
    dom edge_annot = dom node_annot ->
    ea_lob_wf_ind gr edge_annot node_annot -∗
     (ea_ob_wf_ind gr
        (map_imap (λ e gm, Some ((set_fold (λ e' acc, <[e' := (□(prot_node e'))%I]>acc) ∅
                              (obs_pred_of gr e)) ∪ gm)) edge_annot) node_annot).
  Proof.
    intros. eapply ea_obs_saturation_aux;eauto.
    intros ? ?. rewrite difference_diag_L //.
  Qed.

  (* convert to the induction version *)
  Lemma ea_lob_wf_impl_ind gr node_annot edge_annot:
    ea_lob_wf gr edge_annot node_annot -∗
    ea_lob_wf_ind gr edge_annot node_annot ∗ ⌜dom edge_annot = dom node_annot ⌝.
  Proof.
    iNamed 1. iSplit;[|done]. iSplit. iPureIntro;done.
    rewrite big_sepM_sepM2_zip // big_sepM_sepM2_zip //.
    rewrite big_sepM2_flip //.
  Qed.

  (* extend [node_annot] and [edge_annot] with initial nodes, first thing to do in phase-2 *)
  Lemma ea_init_extend gr node_annot edge_annot:
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    "%Hna_full" ∷ na_full gr node_annot -∗
    "Hea" ∷ ea_lob_wf gr edge_annot node_annot -∗
    "#R_init" ∷ ([∗ set] e ∈ Candidate.initials gr, □ prot_node e) -∗
    let node_annot' := (gset_to_gmap True%I (Candidate.initials gr) ∪ node_annot) in
    "%Hna_full" ∷ ⌜dom node_annot' = Candidate.valid_eid gr ⌝ ∗
    "Hea" ∷ ea_lob_wf gr (gset_to_gmap ∅ (Candidate.initials gr) ∪ edge_annot) node_annot'.
  Proof.
    iIntros (Hwf Hcs). repeat iNamed 1.
    iSplit.
    {
      rewrite dom_union_L Hna_full. rewrite dom_gset_to_gmap.
      iPureIntro. pose proof (Candidate.valid_eid_disjoint_union gr) as [? _];done.
    }
    {
      iNamed "Hea". iSplit.
      { iPureIntro. rewrite 2!dom_union_L. rewrite 2!dom_gset_to_gmap. rewrite Hea_dom_eq //. }
      iSplit.
      {
        iPureIntro. intros e gm Hlk.
        rewrite lookup_union_Some in Hlk. destruct Hlk as [Hlk|Hlk].
        rewrite lookup_gset_to_gmap_Some in Hlk. destruct Hlk as [_ <-]. set_solver +.
        specialize (Hea_lob_wf e gm Hlk). set_solver + Hea_lob_wf.
        apply map_disjoint_dom. rewrite dom_gset_to_gmap. rewrite Hea_dom_eq Hna_full.
        pose proof (Candidate.valid_eid_disjoint_union gr) as [_ ?];done.
      }
      rewrite big_sepM_union.
      2: {
        apply map_disjoint_dom. rewrite dom_gset_to_gmap. rewrite Hna_full.
        pose proof (Candidate.valid_eid_disjoint_union gr) as [_ ?];done.
      }
      iSplitR.
      {
        rewrite big_sepM_gset_to_gmap.
        iApply (big_sepS_impl with "R_init").
        iModIntro. iIntros (??) "R".
        rewrite lookup_union_l. rewrite lookup_gset_to_gmap. case_option_guard;last done;simpl.
        iIntros "[_ _]".
        iApply step_fupd_intro;auto. iFrame "R".
        iSplitL;first done.
        rewrite no_lob_succ_initial //. by rewrite big_sepS_empty.
        apply not_elem_of_dom. rewrite Hea_dom_eq Hna_full.
        pose proof (Candidate.valid_eid_disjoint_union gr) as [_ Hdisj]. set_solver.
      }
      {
        iApply (big_sepM_impl with "Hea_fe").
        iModIntro. iIntros (x R Hna_lk_x) "R".
        rewrite lookup_union_r.
        2:{
          apply not_elem_of_dom. rewrite dom_gset_to_gmap.
          apply elem_of_dom_2 in Hna_lk_x. rewrite Hna_full in Hna_lk_x.
          pose proof (Candidate.valid_eid_disjoint_union gr) as [_ Hdisj]. set_solver + Hdisj Hna_lk_x.
        }
        destruct (decide (is_Some (edge_annot !! x))) as [[gm ->]|Hn];simpl.
        2:{
          assert (edge_annot !! x = None) as ->;auto.
          apply not_elem_of_dom. intro. apply Hn. by apply elem_of_dom.
        }

        iNamed 1. iDestruct ("R" with "[$R_lob_in $R_obs_in]") as ">R_out".
        iModIntro. iNext. iMod "R_out".  iModIntro. iNamed "R_out".
        iFrame "R_na R_obs_out".
        iApply (big_sepS_impl with "R_lob_out").
        iModIntro. iIntros (? Hin_x').
        rewrite lookup_union_r. iIntros "$".
        apply not_elem_of_dom. rewrite dom_gset_to_gmap.
        apply elem_of_dom_2 in Hna_lk_x. rewrite Hna_full in Hna_lk_x.
        pose proof (Candidate.valid_eid_disjoint_union gr) as [_ Hdisj].
        apply (lob_same_thd) in Hin_x';auto.
        set_solver + Hin_x' Hdisj.
      }
    }
  Qed.

End lemma.
