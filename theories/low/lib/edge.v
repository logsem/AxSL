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

(* This file contains the resource construction for edges *)
From SSCCommon Require Import Common.
From iris.base_logic Require Import iprop.

From self Require Import stdpp_extra.

From self.algebra Require Import base.

Module Edge.
  (* Edge *)

  Inductive bn := W (ks : AccessStrength) (kv : AccessVariety) | R (ks : AccessStrength) (kv : AccessVariety) | B ( bκ : BarrierKind).
  Inductive t := Po | Addr | Data | Ctrl |Rf | Co | Rmw | Fr | Node (bn : bn) |
              Obs | Lob | Ob.

  Import AACandExec.

  Definition ef_node_interp (gr : Graph.t) (bn : bn) (e : Eid) : Prop :=
    ∃ E, gr !! e = Some E
           ∧ match bn with
    | W ks kv => AAConsistent.event_is_write_with_kind E ks kv
    | R ks kv => AAConsistent.event_is_read_with_kind E ks kv
    | B (AAArch.DMB κ) => AAConsistent.event_is_dmb κ E
    | B AAArch.ISB => AAConsistent.event_is_isb E
  end.

  #[global] Hint Unfold ef_node_interp : core.

  Definition ef_edge_interp (gr : Graph.t) (be : t) (e e' : Eid) : Prop :=
    match be with
    | Po => (e,e') ∈ (Candidate.po gr)
    | Addr => (e,e') ∈ (Candidate.addr gr)
    | Data => (e,e') ∈ (Candidate.data gr)
    | Ctrl => (e,e') ∈ (Candidate.ctrl gr)
    | Rf => (e,e') ∈ (Candidate.rf gr)
    | Co => (e,e') ∈ (Candidate.co gr)
    | Rmw => (e,e') ∈ (Candidate.rmw gr)
    | Fr => (e, e') ∈ (Candidate.fr gr)
    | Node bn =>  e = e' ∧ ef_node_interp gr bn e
    | Lob => (e,e') ∈ (AAConsistent.lob gr)
    | Obs => (e,e') ∈ (AAConsistent.obs gr)
    | Ob => (e,e') ∈ (AAConsistent.ob gr)
  end.

  #[global] Hint Unfold ef_node_interp : core.
  #[global] Hint Unfold ef_edge_interp : core.

  (** Some pure lemmas about [ef_edge_interp]*)
  Lemma subseteq_lob {gr s e} :
    set_Forall (λ x : Eid, ef_edge_interp gr Edge.Lob x e) s ->
    s ⊆ Graph.lob_pred_of gr e.
  Proof.
    intro Hlob.
    rewrite /Graph.lob_pred_of.
    assert (Hsub : GRel.grel_dom (CSets.gset_product s {[e]})
                     ⊆ GRel.grel_dom (filter (λ '(_, et), et = e) (AAConsistent.lob gr))).
    {
      assert (Hsub : (CSets.gset_product s {[e]})
                       ⊆ (filter (λ '(_, et), et = e) (AAConsistent.lob gr))).
      {
        transitivity (filter (λ '(_, et), et = e) (CSets.gset_product s {[e]})).
        intros ? Hin. rewrite elem_of_filter. split.
        apply CSets.gset_product_spec in Hin.
        destruct Hin as [Hin1 Hin2]. destruct x. set_solver + Hin2. done.
        apply stdpp_extra.set_filter_subseteq.
        intros ? Hin. apply CSets.gset_product_spec in Hin. destruct Hin as [Hin1 Hin2].
        specialize (Hlob x.1 Hin1). simpl in Hlob.
        apply elem_of_singleton in Hin2. destruct x. subst. simpl in Hlob. done.
      }
      rewrite /GRel.grel_dom. apply set_map_mono. done. set_solver + Hsub.
    }
    etransitivity;last exact Hsub. set_solver +.
  Qed.

End Edge.

Section def.
  Context `{AABaseG Σ}.

  Import AACandExec.

  Definition edge_def (ef : Edge.t) (e e' : Eid) : iProp Σ :=
    ∃ gr,  "Hgr_interp_e" ∷ graph_agree gr ∗
           "%Hgr_wf_e" ∷ ⌜ AAConsistent.t gr ⌝ ∗
           "%Hgr_cs_e" ∷ ⌜ AACandExec.NMSWF.wf gr ⌝ ∗
           "%Hedge_interp" ∷ ⌜Edge.ef_edge_interp gr ef e e'⌝.

  Definition edge_def_aux : seal (@edge_def). Proof. by eexists. Qed.
  Definition edge := edge_def_aux.(unseal).
  Definition edge_eq : @edge = @edge_def := edge_def_aux.(seal_eq).

  Definition node_def e (n : Edge.bn): iProp Σ := edge ((Edge.Node n)) e e.
  Definition node_def_aux : seal (@node_def). Proof. by eexists. Qed.
  Definition node := node_def_aux.(unseal).
  Definition node_eq : @node = @node_def := node_def_aux.(seal_eq).
End def.

Notation "n1 -{ r }> n2" :=
  (edge r n1 n2) (at level 21,  r at level 50, format "n1  -{ r }>  n2") : bi_scope.

Notation "n '-{N}>' e " :=
  (node n e) (at level 21,  e at level 50, format "n  '-{N}>'  e") : bi_scope.

Section lemmas.
  Context `{CMRA Σ} `{!AABaseG}.

  #[global] Instance edge_def_persist r n1 n2 : Persistent(edge r n1 n2).
  Proof. rewrite edge_eq. rewrite /edge_def. apply _. Qed.

  #[global] Instance node_def_persist e n : Persistent(node e n).
  Proof. rewrite node_eq. rewrite /node_def. apply _. Qed.

  (* edge prompte/demote lemmas *)
  Lemma acq_po_is_lob a b :
    a -{N}> Edge.R AS_rel_or_acq AV_plain -∗
    a -{Edge.Po}> b -∗
    a -{Edge.Lob}> b.
  Proof.
    rewrite node_eq /node_def edge_eq /edge_def.
    iIntros "[% (Hg1&%&%&%)]".
    iIntros "[% (Hg2&%&%&%)]".
    iDestruct (graph_agree_agree with "Hg1 Hg2") as %->.
    iExists _. iFrame. iSplit;first done. iSplit;first done.
    iPureIntro. simpl.
    apply Graph.acq_po_subseteq_lob.
    2:{ assumption. }
    rewrite /AAConsistent.acq_reads.
    destruct H3 as [_ [? [Hlk He]]].
    set_unfold. eexists;eauto. split;first eassumption.
    eapply AAConsistent.event_is_read_with_P_impl;last eassumption.
    intros. naive_solver.
  Qed.

  Lemma po_rel_is_lob a b kind_s:
    a -{Edge.Po}> b -∗
    b -{N}> Edge.W AS_rel_or_acq kind_s -∗
    a -{Edge.Lob}> b.
  Proof.
    rewrite node_eq /node_def edge_eq /edge_def.
    iIntros "[% (Hg1&%&%&%)]".
    iIntros "[% (Hg2&%&%&%)]".
    iDestruct (graph_agree_agree with "Hg1 Hg2") as %->.
    iExists _. iFrame. iSplit;first done. iSplit;first done.
    iPureIntro. simpl.
    apply Graph.po_rel_subseteq_lob. done.
    rewrite /AAConsistent.acq_reads.
    destruct H6 as [_ [?  [Hlk He]]].
    set_unfold. eexists.
    split;first eassumption.
    rewrite /AAConsistent.event_is_rel.
    rewrite /AAConsistent.event_is_write_with_kind in He.
    eapply AAConsistent.event_is_write_with_P_impl;[|eassumption].
    simpl. intros.
    rewrite /AACandExec.Candidate.kind_of_wreq_P.
    rewrite /AACandExec.Candidate.kind_of_wreq_P in H6.
    destruct (AAInter.WriteReq.access_kind wreq );try contradiction.
    case_bool_decide.
    rewrite H7. simpl. done.
    contradiction.
  Qed.

  Lemma addr_is_lob a b :
    a -{Edge.Addr}> b -∗
    a -{Edge.Lob}> b.
  Proof.
    rewrite edge_eq /edge_def.
    iIntros "[% (Hg1&%&%&%)]".
    iExists _. iFrame. iSplit;first done. iSplit;first done.
    iPureIntro. simpl.
    simpl in H3. apply Graph.addr_subseteq_lob;done.
  Qed.

  Lemma data_is_lob a b :
    a -{Edge.Data}> b -∗
    a -{Edge.Lob}> b.
  Proof.
    rewrite edge_eq /edge_def.
    iIntros "[% (Hg1&%&%&%)]".
    iExists _. iFrame. iSplit;first done. iSplit;first done.
    iPureIntro. simpl.
    simpl in H3. apply Graph.data_subseteq_lob;done.
  Qed.

  Lemma lob_is_ob a b:
    a -{Edge.Lob}> b -∗
    a -{Edge.Ob}> b.
  Proof.
    rewrite edge_eq /edge_def.
    iIntros "[% (Hg1&%&%&%)]".
    iExists _. iFrame. iSplit;first done. iSplit;first done.
    iPureIntro. simpl.
    simpl in H3. apply Graph.lob_subseteq_ob;done.
  Qed.

  Lemma rf_co_to_fr a b c :
    a -{Edge.Rf}> b -∗
    a -{Edge.Co}> c -∗
    b -{Edge.Fr}> c.
  Proof.
    rewrite edge_eq /edge_def.
    iIntros "[% (Hg1&%&%&%)]".
    iIntros "[% (Hg2&%&%&%)]".
    iDestruct (graph_agree_agree with "Hg1 Hg2") as %->.
    iExists _. iFrame. iSplit;first done. iSplit;first done.
    iPureIntro. simpl. set_solver + H3 H6.
  Qed.

  Lemma fre_is_ob a b:
    EID.tid a ≠ EID.tid b ->
    a -{Edge.Fr}> b -∗
    a -{Edge.Ob}> b.
  Proof.
    rewrite edge_eq /edge_def.
    iIntros (?) "[% (Hg1&%&%&%)]".
    iExists _. iFrame. iSplit;first done. iSplit;first done.
    iPureIntro. simpl. apply Graph.fre_subseteq_ob;done.
  Qed.

  Lemma rfe_is_ob a b:
    EID.tid a ≠ EID.tid b ->
    a -{Edge.Rf}> b -∗
    a -{Edge.Ob}> b.
  Proof.
    rewrite edge_eq /edge_def.
    iIntros (?) "[% (Hg1&%&%&%)]".
    iExists _. iFrame. iSplit;first done. iSplit;first done.
    iPureIntro. simpl. apply Graph.rfe_subseteq_ob;done.
  Qed.

  Lemma po_dmbsy_po_is_lob a b c:
    a -{Edge.Po}> b -∗
    b -{N}> (Edge.B (AAArch.DMB AAArch.Sy)) -∗
    b -{Edge.Po}> c -∗
    a -{Edge.Lob}> c.
  Proof.
    rewrite node_eq /node_def. rewrite edge_eq /edge_def.
    iIntros "[% (Hg1&%&%&%)] [% (Hg2&%&%&_&%)] [% (Hg3&%&%&%)]".
    iDestruct (graph_agree_agree with "Hg1 Hg2") as %->.
    iDestruct (graph_agree_agree with "Hg1 Hg3") as %->.
    iExists _. iFrame. iSplit;first done. iSplit;first done.
    iPureIntro. simpl in *. apply (Graph.po_dmbsy_po_subseteq_lob _ a b c).
    done.
    rewrite /Edge.ef_node_interp in H6.
    rewrite /AAConsistent.dmbs. destruct H6 as [?  [Hlk He]].
    set_unfold. eexists;eauto.
    done.
  Qed.

  Lemma ctrl_w_is_lob a b ak av:
    b -{N}> Edge.W ak av -∗
    a -{Edge.Ctrl}> b -∗
    a -{Edge.Lob}> b.
  Proof.
    rewrite node_eq /node_def edge_eq /edge_def.
    iIntros "[% (Hg1&%&%&_&%)] [% (Hg2&%&%&%)]".
    iDestruct (graph_agree_agree with "Hg1 Hg2") as %->.
    iExists _. iFrame. iSplit; first (iPureIntro;assumption). iSplit; first (iPureIntro;assumption).
    iPureIntro. simpl in H3,H6. simpl. apply (Graph.ctrl_w_subseteq_lob _ a b).
    + done.
    + destruct H3 as [? [Hlk He]].
      unfold AAConsistent.event_is_write_with_kind, AAConsistent.event_is_write_with_P in He.
      destruct x. destruct o; try (exfalso; assumption).
      clear -Hlk. set_unfold. repeat eexists. rewrite Hlk. reflexivity.
  Qed.

  Lemma ctrl_isb_po_is_lob a b c ak1 av1 ak2 av2:
    a -{N}> Edge.R ak1 av1 -∗
    b -{N}> Edge.B AAArch.ISB -∗
    c -{N}> Edge.R ak2 av2 -∗
    a -{Edge.Ctrl}> b -∗
    b -{Edge.Po}> c -∗
    a -{Edge.Lob}> c. 
  Proof.
    rewrite node_eq /node_def edge_eq /edge_def.
    iIntros "[% (Hg1&%&%&_&%)] [% (Hg2&%&%&_&%)] [% (Hg3&%&%&%)] [% (Hg4&%&%&%)] [% (Hg5&%&%&%)]".
    iDestruct (graph_agree_agree with "Hg1 Hg2") as %->.
    iDestruct (graph_agree_agree with "Hg1 Hg3") as %->.
    iDestruct (graph_agree_agree with "Hg1 Hg4") as %->.
    iDestruct (graph_agree_agree with "Hg1 Hg5") as %->.
    iExists _. iFrame. iSplit; first done. iSplit; first done.
    iPureIntro. simpl in *. apply (Graph.ctrl_isb_po_subseteq_lob _ a b c).
    + done.
    + unfold AAConsistent.isbs. destruct H6 as [? [Hlk He]].
      set_unfold. hauto lq: on rew: off.
    + done.
    + destruct H9 as [_ [? [Hlk He]]].
      unfold AAConsistent.event_is_read_with_kind, AAConsistent.event_is_read_with_P in He.
      destruct x.
      destruct o; try (exfalso; assumption).
      set_unfold. repeat eexists. rewrite Hlk. reflexivity.
  Qed.

  Lemma ob_trans a b c:
    a -{Edge.Ob}> b -∗
    b -{Edge.Ob}> c -∗
    a -{Edge.Ob}> c.
  Proof.
    rewrite edge_eq /edge_def.
    iIntros "[% (Hg1&%&%&%)]".
    iIntros "[% (Hg2&%&%&%)]".
    iDestruct (graph_agree_agree with "Hg1 Hg2") as %->.
    iExists _. iFrame. iSplit;first done. iSplit;first done.
    iPureIntro. simpl.
    rewrite /AAConsistent.ob.
    eapply GRel.grel_plus_trans;done.
  Qed.

  Lemma ob_acyclic a:
    a -{Edge.Ob}> a -∗ False.
  Proof.
    rewrite edge_eq /edge_def.
    iIntros "[% (Hg1&%&%&%)]".
    iPureIntro. eapply Graph.ob_acyclic;done.
  Qed.

  Lemma po_trans a b c:
    a -{Edge.Po}> b -∗
    b -{Edge.Po}> c -∗
    a -{Edge.Po}> c.
  Proof.
    rewrite edge_eq /edge_def.
    iIntros "[% (Hg1&%&%&%)]".
    iIntros "[% (Hg2&%&%&%)]".
    iDestruct (graph_agree_agree with "Hg1 Hg2") as %->.
    iExists _. iFrame. iSplit;first done. iSplit;first done.
    iPureIntro. simpl. eapply Graph.po_transitive;done.
  Qed.

  Lemma po_irrefl a:
    a -{Edge.Po}> a -∗ False.
  Proof.
    rewrite edge_eq /edge_def.
    iIntros "[% (Hg1&%&%&%)]".
    iPureIntro. eapply Graph.po_irreflexive;done.
  Qed.

End lemmas.
