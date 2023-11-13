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

(* This file contains the low-level proof rules for memory reads *)
From self.low.rules Require Import prelude.

Import uPred.

Section rules.
  Context `{AAIrisG} `{Htg: !ThreadGNL}.
  Import ThreadState.

  Lemma mem_read_external `{!UserProt} {tid : Tid} {o_po_src ts ctxt dep addr kind_s kind_v} R po_srcs lob_annot:
    ThreadState.ts_reqs ts = AAInter.Next (AAInter.MemRead 8 (readreq_of_store kind_s kind_v addr dep)) ctxt ->
    let eid := progress_to_node (get_progress ts) tid in
    let R_graph_facts := (λ val eid_w,
                            eid -{E}> (Event.R kind_s kind_v addr val) ∗
                            (* Po *)
                            ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{(Edge.Po)}> eid) ∗
                            (* Ctrl *)
                            ([∗ set] eid_ctrl_src ∈ ts.(ts_ctrl_srcs), eid_ctrl_src -{(Edge.Ctrl)}> eid) ∗
                            (* Addr *)
                            ([∗ set] eid_addr_src ∈ LThreadStep.deps_of_depon tid ts (Some dep), eid_addr_src -{(Edge.Addr)}> eid) ∗
                            (* There must be a write with same addr and val *)
                            (∃ kind_s_w kind_v_w, eid_w -{E}> (Event.W kind_s_w kind_v_w addr val)) ∗
                            (* [optional] rf from write to read *)
                            eid_w -{(Edge.Rf)}> eid ∗
                            (* eid_w is an external write *)
                            ⌜EID.tid eid_w ≠ tid⌝)%I in
    o_po_src -{LPo}> -∗
    ([∗ set] e_po_src ∈ po_srcs, e_po_src -{Po}>) -∗
    last_local_write tid addr None -∗
    (* node annotations *)
    ([∗ map] node ↦ annot ∈ lob_annot, node ↦ₐ annot) -∗
    (* Lob edge formers *)
    (eid -{N}> (Edge.R kind_s kind_v) -∗
     ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{Edge.Po}> eid) -∗
     ([∗ set] eid_ctrl_src ∈ ts.(ts_ctrl_srcs), eid_ctrl_src -{(Edge.Ctrl)}> eid) -∗
     ([∗ set] eid_addr_src ∈ LThreadStep.deps_of_depon tid ts (Some dep), eid_addr_src -{(Edge.Addr)}> eid) -∗
     [∗ set] eid_pre ∈ dom lob_annot, eid_pre -{Edge.Lob}> eid) -∗
    (* FE *)
    (∀ val eid_w,
       R_graph_facts val eid_w ∗
       ([∗ map] _ ↦ annot ∈ lob_annot, annot) ∗
       □(prot addr val eid_w)
       ={⊤}[∅]▷=∗
       R addr val eid_w) -∗
    SSWP (LThreadState.LTSNormal ts) @ tid {{ λ lts',
      (* exists a val, a write kind, and a write eid_w *)
      ∃ val eid_w,
      (* update lts' accordingly *)
      ⌜lts' = LThreadState.LTSNormal ((ThreadState.incr_cntr (ts <| ts_iis := (ts.(ts_iis)
                                    <| iis_mem_reads := ((ts.(ts_iis).(iis_mem_reads)) ++ [ts.(ts_iis).(iis_cntr)])%list|>)|>))
                                    <| ts_reqs := ctxt (inl(val, None)) |>
                                    <| ts_rmw_pred := if bool_decide (kind_v = AV_exclusive) ||
                                                           bool_decide (kind_v = AV_atomic_rmw)
                                                      then Some eid else ts.(ts_rmw_pred) |>)⌝ ∗
      R_graph_facts val eid_w ∗
      (Some eid) -{LPo}> ∗
      (* node annotation *)
      (eid ↦ₐ R addr val eid_w) ∗
      (* ([∗ map] node ↦ annot ∈ lob_annot_uu, node ↦ₐ annot) ∗ *)
      (* local writes at addr is unchanged *)
      last_local_write tid addr None
    }}.
  Proof.
    iIntros (Hreqs ??) "Hpo_src Hpo_srcs Hlocal Hannot Hef Hfe".
    rewrite sswp_eq /sswp_def /=.
    iIntros (????) "H". iNamed "H".
    inversion Hat_prog as [Hpg]. clear Hat_prog.
    case_bool_decide as Hv.
    2:{
      rewrite (LThreadStep.step_progress_valid_is_reqs_nonempty _ _ _ ts) in Hv;[|done|done].
      rewrite Hreqs /EmptyInterp /= in Hv. exfalso. by apply Hv.
    }
    iIntros (?). iNamed 1.
    (* Hstep gives that a read event is happening *)
    inversion_step Hstep.

    (* get the write *)
    feed pose proof (Graph.wf_read_inv _ _ _ addr kind_s kind_v mv Hgraph_wf Hgr_lk) as Hrf;simpl;
      [rewrite /AACandExec.Candidate.kind_of_rreq_P /=; repeat (case_bool_decide;[|contradiction]);done| destruct Hrf as (eid_w & kind_s_w & kind_v_w & E_w &Hgr_lk_w&HE_w&?)].

    iNamed "Hinterp_local".
    iDestruct (last_write_interp_agree_None with "Hinterp_local_lws Hlocal") as %Hlw.
    efeed specialize Hlw; [done|eauto|]. eapply AAConsistent.event_is_write_with_impl_addr;done.

    iDestruct (po_pred_interp_agree_big' with "Hinterp_po_src Hpo_srcs") as %Hpo_srcs.
    iDestruct (po_pred_interp_agree with "Hinterp_po_src Hpo_src") as %Hpo.

    epose proof (AAConsistent.event_is_write_with_elem_of_mem_writes eid_w _ _ _ _ _ Hgr_lk_w HE_w) as Heid_w.

    subst eid. set (eid := (mk_eid_ii ts tid)).
    destruct Hlw as [Hne_tid | [Htid Hlw]].
    2:{(* reading from later writes *)
      exfalso.
      pose proof (Graph.wf_rfi_inv eid_w eid Hgraph_wf Hgraph_co H2 Htid) as Hpo'.
      erewrite <-(progress_to_node_of_node tid eid_w Htid) in Hpo'.
      erewrite <-(progress_to_node_of_node tid eid) in Hpo';[|done].
      rewrite -progress_lt_po in Hpo';[|done]. destruct Hpo'.
      rewrite /eid. by apply progress_le_gt_False in Hlw.
    }

    assert (Hobs : (eid_w, eid) ∈ AAConsistent.obs (gs.(GlobalState.gs_graph))).
    { apply elem_of_union_l. apply elem_of_union_l. apply elem_of_filter. split. rewrite /= //. done. }

    (** allocate resources *)
    iAssert (eid -{E}> Event.R kind_s kind_v addr mv ∗
             ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{Edge.Po}> progress_to_node (get_progress ts) tid) ∗
             ([∗ set] eid_ctrl_src ∈ ts_ctrl_srcs ts, eid_ctrl_src -{Edge.Ctrl}> eid) ∗
             ([∗ set] eid_addr_src ∈ LThreadStep.deps_of_depon tid ts (Some dep), eid_addr_src -{(Edge.Addr)}> eid) ∗
             eid_w -{E}> Event.W kind_s_w kind_v_w addr mv ∗
             eid_w -{Edge.Rf}> eid)%I as "(E_R & Ed_po & Ed_ctrl & Ed_addr & E_W & Ed_rf)".
    {
      rewrite edge_eq /edge_def. rewrite event_eq /event_def. iNamed "Hinterp_global".

      iSplitL. alloc_graph_res.
      { rewrite /AACandExec.Candidate.kind_of_rreq_P /=; repeat case_bool_decide;try contradiction;auto. }

      iSplitL. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.
      destruct (Hpo_srcs x) as [? [? ?]];auto. rewrite -(progress_to_node_of_node tid x);auto.
      rewrite /eid. apply progress_lt_po;auto.

      iSplitL. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.

      iSplitL. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.

      iSplitL;alloc_graph_res;done.
    }

    (** get lob *)
    iDestruct ("Hef" with "[E_R] Ed_po Ed_ctrl Ed_addr") as "#E_lob".
    { iApply (event_node with "E_R"). }

    (** agree on lob *)
    iDestruct (graph_edge_agree_big_pred with "Hinterp_global E_lob") as %Hlob.

    (** agree on lob_annot *)
    iNamed "Hinterp_annot".
    iDestruct (annot_agree_big with "Hinterp_annot Hannot") as "[%Hlob_annot_dom_sub #_]".

    (** update na *)
    iDestruct (na_at_progress_not_elem_of with "Hannot_at_prog") as %Hpg_not_in.
    iDestruct "Hannot_at_prog" as "#Hannot_at_prog".
    iMod (annot_alloc _ (get_progress ts) tid gs (R addr mv eid_w)
           with "[$Hinterp_annot //]") as "(Hinterp_annot & Hannot_curr)".
    iMod (token_alloc with "[$Hinterp_token $Hannot_at_prog]") as "(Hinterp_token & Htok)".
    iDestruct "Hannot_at_prog" as %Hannot_at_prog.

    iDestruct (annot_update_big with "Hinterp_annot Hannot") as ">(%lob_annot_uu&%Hannot_dom & Hinterp_annot & #Hannot_split)".

    iMod (po_pred_interp_update _ ts ((ts <| ts_iis := ts_iis ts <| iis_mem_reads := (iis_mem_reads (ts_iis ts) ++ [iis_cntr (ts_iis ts)])%list |> |>)
                                          <| ts_reqs := ctxt (inl (mv, None)) |>
                                          <| ts_rmw_pred := if bool_decide (kind_v = AV_exclusive) ||
                                                           bool_decide (kind_v = AV_atomic_rmw) then Some eid else ts.(ts_rmw_pred) |>
            ) with "Hinterp_po_src Hpo_src") as "(Hinterp_po_src & Hpo_src)";auto.

    iExists (R addr mv eid_w), lob_annot, lob_annot_uu, (ls <|lls_pop := Some eid|>).

    iSplitL "Hfe". iSplitR.
    (* show well-splittedness *)
    iModIntro. iSplitR.
    { iPureIntro. by apply Edge.subseteq_lob. }
    {
      iApply (big_sepM2_impl with "Hannot_split"). iModIntro. iIntros (k P1 P2 Hlk1 Hlk2) "Heqv".
      assert (is_Some (lob_annot !! k)) as [P Hlob_annot_lk].
      {
        apply elem_of_dom. apply elem_of_dom_2 in Hlk1. done.
      }
      (* iDestruct (big_sepM_lookup _ _ k P with "Hannot_ag") as "Heqv'". done. *)
      assert (is_Some (na !! k)) as [P' Hna_lk].
      {
        apply elem_of_dom. apply elem_of_dom_2 in Hlk1.
        set_solver+ Hlk1 Hlob_annot_dom_sub.
      }
      rewrite lookup_insert_ne. 2:{ apply elem_of_dom_2 in Hna_lk. set_solver+ Hna_lk Hpg_not_in. }
      rewrite Hna_lk /=. iNext. rewrite wand_iff_sym //.
    }

    (** getting out resources from FE *)
    {
      iModIntro. repeat iNamed 1. iSpecialize ("Hfe" $! mv eid_w).

      rewrite /prot_node /=. erewrite progress_to_node_mk_eid_ii;last reflexivity.
      iDestruct (big_sepS_elem_of _ _ eid_w with "R_obs_in") as "R_in".
      rewrite /Graph.obs_pred_of. set_solver+ Hobs.
      iSpecialize ("R_in" with "E_W").
      rewrite iris_extra.big_sepS_to_map.
      iDestruct ("Hfe" with "[R_lob_in $R_in]") as "Hfe".
      {
        iFrame "#". iSplitR. iSplit;[|done]. iExists _, _. iFrame "E_W".
        iApply (big_sepM_proper with "R_lob_in");auto. }
      iApply step_fupd_frame_l.
      iSplitR "Hfe";last done.
      { iModIntro. iIntros (????) "E_W'". iDestruct (event_agree with "E_R E_W'") as %Heq. exfalso. done. }
      { set_solver+ Hlob. }
    }

    iDestruct (na_at_progress_not_elem_of with "[]") as %Hna_not_in.
    iPureIntro. exact Hannot_at_prog.
    iSplitL "Hinterp_annot Hinterp_token".
    {
      rewrite -insert_union_r. rewrite -assoc_L. rewrite insert_union_singleton_l.
      rewrite insert_union_singleton_l. iFrame "Hinterp_annot".
      rewrite !dom_union_L dom_singleton_L.
      assert ((dom lob_annot_uu ∪ dom na) = dom na) as ->.
      { rewrite Hannot_dom. set_solver+ Hlob_annot_dom_sub. }
      by iFrame.
      apply not_elem_of_dom. rewrite Hannot_dom. set_solver+ Hna_not_in Hlob_annot_dom_sub.
    }

    iSplitL "Hinterp_local_lws Hinterp_po_src".
    {
      iSplitL "Hinterp_local_lws".

      iApply (last_write_interp_progress_non_write with "Hinterp_local_lws");auto.
      intro Hin. erewrite progress_to_node_mk_eid_ii in Hin;last done.
      pose proof (AAConsistent.event_is_write_elem_of_mem_writes2 _ Hgraph_wf Hin) as [? [Hlk' HW]].
      rewrite Hgr_lk in Hlk'. inversion Hlk'. subst x. done.
      erewrite progress_to_node_mk_eid_ii;done.
    }

    iExists mv, eid_w. iModIntro. iSplit.

    erewrite progress_to_node_mk_eid_ii;last reflexivity.
    rewrite /readreq_of_store /AACandExec.Candidate.kind_of_rreq_is_atomic /AACandExec.Candidate.kind_of_rreq_P //.
    iFrame "E_R Ed_po Ed_ctrl Ed_rf Ed_addr Hpo_src". iSplitR. iSplit;[|done]. iExists _, _. iFrame "E_W".
    iFrame.
  Qed.

  Lemma mem_read_external_with_local `{!UserProt} {tid : Tid} {o_po_src ts ctxt dep addr kind_s kind_v kind_s' kind_v' leid lval}
        R po_srcs lob_annot
    :
    ThreadState.ts_reqs ts = AAInter.Next (AAInter.MemRead 8 (readreq_of_store kind_s kind_v addr dep)) ctxt ->
    let eid := progress_to_node (get_progress ts) tid in
    let R_graph_facts := (λ val eid_w,
                            eid -{E}> (Event.R kind_s kind_v addr val) ∗
                            (* Po *)
                            ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{(Edge.Po)}> eid) ∗
                            (* Ctrl *)
                            ([∗ set] eid_ctrl_src ∈ ts.(ts_ctrl_srcs), eid_ctrl_src -{(Edge.Ctrl)}> eid) ∗
                            (* Addr *)
                            ([∗ set] eid_addr_src ∈ LThreadStep.deps_of_depon tid ts (Some dep), eid_addr_src -{(Edge.Addr)}> eid) ∗
                            (* There must be a write with same addr and val *)
                            (∃ kind_s_w kind_v_w, eid_w -{E}> (Event.W kind_s_w kind_v_w addr val)) ∗
                            (* [optional] rf from write to read *)
                            eid_w -{(Edge.Rf)}> eid)%I in
    o_po_src -{LPo}> -∗
    ([∗ set] e_po_src ∈ po_srcs, e_po_src -{Po}>) -∗
    last_local_write tid addr (Some leid) -∗
    leid -{E}> (Event.W kind_s' kind_v' addr lval) -∗
    (* node annotations *)
    ([∗ map] node ↦ annot ∈ lob_annot, node ↦ₐ annot) -∗
    (* Lob edge formers *)
    (eid -{N}> (Edge.R kind_s kind_v) -∗
     ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{Edge.Po}> eid) -∗
     ([∗ set] eid_ctrl_src ∈ ts.(ts_ctrl_srcs), eid_ctrl_src -{(Edge.Ctrl)}> eid) -∗
     ([∗ set] eid_addr_src ∈ LThreadStep.deps_of_depon tid ts (Some dep), eid_addr_src -{(Edge.Addr)}> eid) -∗
     [∗ set] eid_pre ∈ dom lob_annot, eid_pre -{Edge.Lob}> eid) -∗
    (* FE *)
    (∀ val eid_w,
       R_graph_facts val eid_w ∗
       ⌜EID.tid eid_w ≠ tid⌝ ∗
       ([∗ map] _ ↦ annot ∈ lob_annot, annot) ∗
       □(prot addr val eid_w)
       ={⊤}[∅]▷=∗
       R addr val eid_w) -∗
    SSWP (LThreadState.LTSNormal ts) @ tid {{ λ lts',
      (* exists a val, a write kind, and a write eid_w *)
      ∃ val eid_w,
      (* update lts' accordingly *)
      ⌜lts' = LThreadState.LTSNormal ((ThreadState.incr_cntr (ts <| ts_iis := (ts.(ts_iis)
                                    <| iis_mem_reads := ((ts.(ts_iis).(iis_mem_reads)) ++ [ts.(ts_iis).(iis_cntr)])%list|>)|>))
                                    <| ts_reqs := ctxt (inl(val, None)) |>
                                    <| ts_rmw_pred := if bool_decide (kind_v = AV_exclusive) ||
                                                           bool_decide (kind_v = AV_atomic_rmw)
                                                      then Some eid else ts.(ts_rmw_pred) |>)⌝ ∗
      R_graph_facts val eid_w ∗
      (Some eid) -{LPo}> ∗
      (* node annotation *)
      (((eid ↦ₐ R addr val eid_w) ∗ ⌜EID.tid eid_w ≠ tid⌝) ∨ ⌜val = lval⌝) ∗
      (* ([∗ map] node ↦ annot ∈ lob_annot_uu, node ↦ₐ annot) ∗ *)
      (* local writes at addr is unchanged *)
      last_local_write tid addr (Some leid)
    }}.
  Proof.
    iIntros (Hreqs ??) "Hpo_src Hpo_srcs Hlocal Hlnode Hannot Hef Hfe".
    rewrite sswp_eq /sswp_def /=.
    iIntros (????) "H". iNamed "H".
    inversion Hat_prog as [Hpg]. clear Hat_prog.
    case_bool_decide as Hv.
    2:{
      rewrite (LThreadStep.step_progress_valid_is_reqs_nonempty _ _ _ ts) in Hv;[|done|done].
      rewrite Hreqs /EmptyInterp /= in Hv. exfalso. by apply Hv.
    }
    iIntros (?). iNamed 1.
    (* Hstep gives that a read event is happening *)
    inversion_step Hstep.

    (* get the write *)
    feed pose proof (Graph.wf_read_inv _ _ _ addr kind_s kind_v mv Hgraph_wf Hgr_lk) as Hrf;simpl;
      [rewrite /AACandExec.Candidate.kind_of_rreq_P /=; repeat (case_bool_decide;[|contradiction]);done| destruct Hrf as (eid_w & kind_s_w & kind_v_w & E_w &Hgr_lk_w&HE_w&?)].

    iNamed "Hinterp_local".
    iDestruct (last_write_interp_agree_Some with "Hinterp_local_lws Hlocal") as "(%Elw & %Hleid & %Hw & %Hltid & %Hlpg & %Hlw)".
    efeed specialize Hlw; [exact Hgr_lk_w|eauto|]. eapply AAConsistent.event_is_write_with_impl_addr;done.

    iDestruct (po_pred_interp_agree_big' with "Hinterp_po_src Hpo_srcs") as %Hpo_srcs.
    iDestruct (po_pred_interp_agree with "Hinterp_po_src Hpo_src") as %Hpo.

    epose proof (AAConsistent.event_is_write_with_elem_of_mem_writes eid_w _ _ _ _ _ Hgr_lk_w HE_w) as Heid_w.

    subst eid. set (eid := (mk_eid_ii ts tid)).

    destruct Hlw as [Hne_tid | [[Hlw Htid] | [Hlw Htid]]].
    2:{(* reading from later writes *)
      exfalso.
      pose proof (Graph.wf_rfi_inv eid_w eid Hgraph_wf Hgraph_co H2 Htid) as Hpo'.
      erewrite <-(progress_to_node_of_node tid eid_w Htid) in Hpo'.
      erewrite <-(progress_to_node_of_node tid eid) in Hpo';[|done].
      rewrite -progress_lt_po in Hpo';[|done]. destruct Hpo'.
      rewrite /eid. by apply progress_le_gt_False in Hlw.
    }
    {
  
      assert (Hobs : (eid_w, eid) ∈ AAConsistent.obs (gs.(GlobalState.gs_graph))).
      { apply elem_of_union_l. apply elem_of_union_l. apply elem_of_filter. split. rewrite /= //. done. }
  
      (** allocate resources *)
      iAssert (eid -{E}> Event.R kind_s kind_v addr mv ∗
               ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{Edge.Po}> progress_to_node (get_progress ts) tid) ∗
               ([∗ set] eid_ctrl_src ∈ ts_ctrl_srcs ts, eid_ctrl_src -{Edge.Ctrl}> eid) ∗
               ([∗ set] eid_addr_src ∈ LThreadStep.deps_of_depon tid ts (Some dep), eid_addr_src -{(Edge.Addr)}> eid) ∗
               eid_w -{E}> Event.W kind_s_w kind_v_w addr mv ∗
               eid_w -{Edge.Rf}> eid)%I as "(E_R & Ed_po & Ed_ctrl & Ed_addr & E_W & Ed_rf)".
      {
        rewrite edge_eq /edge_def. rewrite event_eq /event_def. iNamed "Hinterp_global".
  
        iSplitL. alloc_graph_res.
        { rewrite /AACandExec.Candidate.kind_of_rreq_P /=; repeat case_bool_decide;try contradiction;auto. }
  
        iSplitL. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.
        destruct (Hpo_srcs x) as [? [? ?]];auto. rewrite -(progress_to_node_of_node tid x);auto.
        rewrite /eid. apply progress_lt_po;auto.
  
        iSplitL. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.
  
        iSplitL. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.
  
        iSplitL;alloc_graph_res;done.
      }
  
      (** get lob *)
      iDestruct ("Hef" with "[E_R] Ed_po Ed_ctrl Ed_addr") as "#E_lob".
      { iApply (event_node with "E_R"). }
  
      (** agree on lob *)
      iDestruct (graph_edge_agree_big_pred with "Hinterp_global E_lob") as %Hlob.
  
      (** agree on lob_annot *)
      iNamed "Hinterp_annot".
      iDestruct (annot_agree_big with "Hinterp_annot Hannot") as "[%Hlob_annot_dom_sub #_]".
  
      (** update na *)
      iDestruct (na_at_progress_not_elem_of with "Hannot_at_prog") as %Hpg_not_in.
      iDestruct "Hannot_at_prog" as "#Hannot_at_prog".
      iMod (annot_alloc _ (get_progress ts) tid gs (R addr mv eid_w)
             with "[$Hinterp_annot //]") as "(Hinterp_annot & Hannot_curr)".
      iMod (token_alloc with "[$Hinterp_token $Hannot_at_prog]") as "(Hinterp_token & Htok)".
      iDestruct "Hannot_at_prog" as %Hannot_at_prog.
  
      iDestruct (annot_update_big with "Hinterp_annot Hannot") as ">(%lob_annot_uu&%Hannot_dom & Hinterp_annot & #Hannot_split)".
  
      iMod (po_pred_interp_update _ ts ((ts <| ts_iis := ts_iis ts <| iis_mem_reads := (iis_mem_reads (ts_iis ts) ++ [iis_cntr (ts_iis ts)])%list |> |>)
                                            <| ts_reqs := ctxt (inl (mv, None)) |>
                                            <| ts_rmw_pred := if bool_decide (kind_v = AV_exclusive) ||
                                                             bool_decide (kind_v = AV_atomic_rmw) then Some eid else ts.(ts_rmw_pred) |>
              ) with "Hinterp_po_src Hpo_src") as "(Hinterp_po_src & Hpo_src)";auto.
  
      iExists (R addr mv eid_w), lob_annot, lob_annot_uu, (ls <|lls_pop := Some eid|>).
  
      iSplitL "Hfe". iSplitR.
      (* show well-splittedness *)
      iModIntro. iSplitR.
      { iPureIntro. by apply Edge.subseteq_lob. }
      {
        iApply (big_sepM2_impl with "Hannot_split"). iModIntro. iIntros (k P1 P2 Hlk1 Hlk2) "Heqv".
        assert (is_Some (lob_annot !! k)) as [P Hlob_annot_lk].
        {
          apply elem_of_dom. apply elem_of_dom_2 in Hlk1. done.
        }
        (* iDestruct (big_sepM_lookup _ _ k P with "Hannot_ag") as "Heqv'". done. *)
        assert (is_Some (na !! k)) as [P' Hna_lk].
        {
          apply elem_of_dom. apply elem_of_dom_2 in Hlk1.
          set_solver+ Hlk1 Hlob_annot_dom_sub.
        }
        rewrite lookup_insert_ne. 2:{ apply elem_of_dom_2 in Hna_lk. set_solver+ Hna_lk Hpg_not_in. }
        rewrite Hna_lk /=. iNext. rewrite wand_iff_sym //.
      }
  
      (** getting out resources from FE *)
      {
        iModIntro. repeat iNamed 1. iSpecialize ("Hfe" $! mv eid_w).
  
        rewrite /prot_node /=. erewrite progress_to_node_mk_eid_ii;last reflexivity.
        iDestruct (big_sepS_elem_of _ _ eid_w with "R_obs_in") as "R_in".
        rewrite /Graph.obs_pred_of. set_solver + Hobs.
        iSpecialize ("R_in" with "E_W").
        rewrite iris_extra.big_sepS_to_map.
        iDestruct ("Hfe" with "[R_lob_in $R_in]") as "Hfe".
        {
          iFrame "#". iSplitR. iExists _, _. iFrame "E_W". iSplit; [done|].
          iApply (big_sepM_proper with "R_lob_in");auto. }
        iApply step_fupd_frame_l.
        iSplitR "Hfe";last done.
        { iModIntro. iIntros (????) "E_W'". iDestruct (event_agree with "E_R E_W'") as %Heq. exfalso. done. }
        { set_solver + Hlob. }
      }
  
      iDestruct (na_at_progress_not_elem_of with "[]") as %Hna_not_in.
      iPureIntro. exact Hannot_at_prog.
      iSplitL "Hinterp_annot Hinterp_token".
      {
        rewrite -insert_union_r. rewrite -assoc_L. rewrite insert_union_singleton_l.
        rewrite insert_union_singleton_l. iFrame "Hinterp_annot".
        rewrite !dom_union_L dom_singleton_L.
        assert ((dom lob_annot_uu ∪ dom na) = dom na) as ->.
        { rewrite Hannot_dom. set_solver + Hlob_annot_dom_sub. }
        by iFrame.
        apply not_elem_of_dom. rewrite Hannot_dom. set_solver + Hna_not_in Hlob_annot_dom_sub.
      }
  
      iSplitL "Hinterp_local_lws Hinterp_po_src".
      {
        iSplitL "Hinterp_local_lws".
  
        iApply (last_write_interp_progress_non_write with "Hinterp_local_lws");auto.
        intro Hin. erewrite progress_to_node_mk_eid_ii in Hin;last done.
        pose proof (AAConsistent.event_is_write_elem_of_mem_writes2 _ Hgraph_wf Hin) as [? [Hlk' HW]].
        rewrite Hgr_lk in Hlk'. inversion Hlk'. subst x. done.
        erewrite progress_to_node_mk_eid_ii;done.
      }
  
      iExists mv, eid_w. iModIntro. iSplit.
  
      erewrite progress_to_node_mk_eid_ii;last reflexivity.
      rewrite /readreq_of_store /AACandExec.Candidate.kind_of_rreq_is_atomic /AACandExec.Candidate.kind_of_rreq_P //.
      iFrame "E_R Ed_po Ed_ctrl Ed_rf Ed_addr Hpo_src". iSplitR. iExists _, _. iFrame "E_W".
      iFrame.
      iLeft.
      iFrame.
      done.
    }
  
    (** allocate resources *)
    iAssert (eid -{E}> Event.R kind_s kind_v addr mv ∗
             ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{Edge.Po}> progress_to_node (get_progress ts) tid) ∗
             ([∗ set] eid_ctrl_src ∈ ts_ctrl_srcs ts, eid_ctrl_src -{Edge.Ctrl}> eid) ∗
             ([∗ set] eid_addr_src ∈ LThreadStep.deps_of_depon tid ts (Some dep), eid_addr_src -{(Edge.Addr)}> eid) ∗
             eid_w -{E}> Event.W kind_s_w kind_v_w addr mv ∗
             eid_w -{Edge.Rf}> eid)%I as "(E_R & Ed_po & Ed_ctrl & Ed_addr & E_W & Ed_rf)".
    {
      rewrite edge_eq /edge_def. rewrite event_eq /event_def. iNamed "Hinterp_global".
  
      iSplitL. alloc_graph_res.
      { rewrite /AACandExec.Candidate.kind_of_rreq_P /=; repeat case_bool_decide;try contradiction;auto. }
  
      iSplitL. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.
      destruct (Hpo_srcs x) as [? [? ?]];auto. rewrite -(progress_to_node_of_node tid x);auto.
      rewrite /eid. apply progress_lt_po;auto.
  
      iSplitL. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.
  
      iSplitL. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.
  
      iSplitL;alloc_graph_res;done.
    }

    iNamed "Hinterp_annot".
    (** update na *)
    iDestruct (na_at_progress_not_elem_of with "Hannot_at_prog") as %Hpg_not_in.
    iDestruct "Hannot_at_prog" as "#Hannot_at_prog".
    iMod (annot_alloc _ (get_progress ts) tid gs True
           with "[$Hinterp_annot //]") as "(Hinterp_annot & Hannot_curr)".
    iMod (token_alloc with "[$Hinterp_token $Hannot_at_prog]") as "(Hinterp_token & Htok)".
    iDestruct "Hannot_at_prog" as %Hannot_at_prog.
    (* iDestruct (annot_update_big with "Hinterp_annot Hannot") as ">(%lob_annot_uu&%Hannot_dom & Hinterp_annot & #Hannot_split)". *)
    iMod (po_pred_interp_update _ ts ((ts <| ts_iis := ts_iis ts <| iis_mem_reads := (iis_mem_reads (ts_iis ts) ++ [iis_cntr (ts_iis ts)])%list |> |>)
                                            <| ts_reqs := ctxt (inl (mv, None)) |>
                                            <| ts_rmw_pred := if bool_decide (kind_v = AV_exclusive) ||
                                                             bool_decide (kind_v = AV_atomic_rmw) then Some eid else ts.(ts_rmw_pred) |>
              ) with "Hinterp_po_src Hpo_src") as "(Hinterp_po_src & Hpo_src)";auto.

    iExists (True)%I, ∅, ∅, (ls <|lls_pop := Some eid|>).
    iSplitL "". iSplitR.
    iModIntro. iSplitR.
    { iPureIntro. set_solver +. }
    { by iApply big_sepM2_empty. }
    { iModIntro. iNamed 1. 
      rewrite /prot_node /=. erewrite progress_to_node_mk_eid_ii;last reflexivity.
      iApply step_fupd_frame_l.
      iSplitR "". 
      { iModIntro. iIntros (????) "E_W'". iDestruct (event_agree with "E_R E_W'") as %Heq. exfalso. done. }
      iApply fupd_mask_intro; set_solver+.
    }
    iDestruct (na_at_progress_not_elem_of with "[]") as %Hna_not_in.
    iPureIntro. exact Hannot_at_prog.
    iSplitL "Hinterp_annot Hinterp_token".
    {
      unfold my_annot_interp.
      rewrite insert_union_singleton_l.
      rewrite map_union_empty. iFrame.
      rewrite dom_union_L.
      rewrite dom_singleton_L.
      by iFrame.
    }

    iSplitL "Hinterp_local_lws Hinterp_po_src".
    {
      iSplitL "Hinterp_local_lws".
  
      iApply (last_write_interp_progress_non_write with "Hinterp_local_lws");auto.
      intro Hin. erewrite progress_to_node_mk_eid_ii in Hin;last done.
      pose proof (AAConsistent.event_is_write_elem_of_mem_writes2 _ Hgraph_wf Hin) as [? [Hlk' HW]].
      rewrite Hgr_lk in Hlk'. inversion Hlk'. subst x. done.
      erewrite progress_to_node_mk_eid_ii; done.
    }
  
    iExists mv, eid_w. iModIntro. iSplit.
  
    erewrite progress_to_node_mk_eid_ii;last reflexivity.
    rewrite /readreq_of_store /AACandExec.Candidate.kind_of_rreq_is_atomic /AACandExec.Candidate.kind_of_rreq_P //.
    iFrame "E_R Ed_po Ed_ctrl Ed_rf Ed_addr Hpo_src". iSplitR. iExists _, _. iFrame "E_W".
    iFrame.
    iRight.
    destruct (decide (leid = eid_w)).
    { 
      rewrite e.
      iDestruct(event_agree with "Hlnode E_W") as "%Heq".
      iPureIntro.
      congruence.
    }
    assert(Hlw' : progress_of_node eid_w <p progress_of_node leid).
    {
      rewrite ThreadState.progress_le_inv in Hlw.
      destruct Hlw as [Hlw | Hlw] ; [assumption|].
      contradict n.
      destruct leid.
      destruct eid_w.
      simpl in Hltid.
      simpl in Htid.
      f_equal.
      + by rewrite Hltid Htid.
      + by injection Hlw.
      + by injection Hlw.
    }
    assert(Hpo' : (eid_w, leid) ∈ AACandExec.Candidate.po (GlobalState.gs_graph gs)).
    {
      rewrite -(progress_to_node_of_node tid leid).
      rewrite -(progress_to_node_of_node tid eid_w).
      apply progress_lt_po.
      + assumption.
      + split. { assumption. }
        rewrite /progress_is_valid. rewrite !progress_to_node_of_node; [|assumption|assumption].
        set_solver+ Hgr_lk_w Hleid.
      + assumption.
      + assumption.
    }
    assert(Hco : (eid_w, leid) ∈ AACandExec.Candidate.co (GlobalState.gs_graph gs)).    
    {
      apply Graph.wf_coi_inv.
      + assumption.
      + assumption.
      + eapply Graph.wf_loc_inv_writes2. repeat eexists; eauto.
        apply (AAConsistent.event_is_write_with_impl_addr _ kind_s_w kind_v_w _ mv); assumption.
      + eapply AAConsistent.event_is_write_with_addr_elem_of_mem_writes in Hw; [|eassumption].
        eapply AAConsistent.event_is_write_with_elem_of_mem_writes in HE_w; [|eassumption].
        set_solver+ Hw HE_w.
      + assumption.
    }
    iAssert(⌜(eid_w, eid) ∈ AACandExec.Candidate.rf (GlobalState.gs_graph gs)⌝)%I as "%Hrf".
    {
      iEval (rewrite edge_eq /edge_def) in "Ed_rf".
      iDestruct "Ed_rf" as "[%gr (Hgr_ag & _ & _ & %Hedge)]".
      iDestruct "Hinterp_global" as "[Hgr_ag' _]".
      iDestruct (graph_agree_agree with "Hgr_ag Hgr_ag'") as %->.
      simpl in Hedge.
      iPureIntro.
      set_solver+ Hedge.
    }
    assert(Hfr : (eid, leid) ∈ AACandExec.Candidate.fr (GlobalState.gs_graph gs)).
    {
      set_solver+ Hco Hrf.
    }
    unfold eid0 in Hgr_lk.
    fold eid in Hgr_lk.
    assert(Hpo'' : (leid, eid) ∈ AACandExec.Candidate.po (GlobalState.gs_graph gs)).
    {
      rewrite -(progress_to_node_of_node tid leid).
      rewrite -(progress_to_node_of_node tid eid).
      apply progress_lt_po.
      + assumption.
      + split. { assumption. }
        rewrite /progress_is_valid. rewrite !progress_to_node_of_node; [|by unfold eid|assumption].
        set_solver+ Hleid Hgr_lk.
      + by unfold eid.
      + assumption.
    }
    assert(Hloc : (leid, eid) ∈ AACandExec.Candidate.loc (GlobalState.gs_graph gs)).
    {
      unfold AAConsistent.event_is_write_with_addr in Hw.
      unfold AAConsistent.event_is_write_with_P in Hw.
      set_unfold.
      exists Elw, (AAInter.IEvent req resp), addr.
      split; [assumption|].
      split. { destruct Elw. destruct o; try contradiction. rewrite CBool.bool_unfold in Hw. subst. simpl.
               unfold AAConsistent.addr_of_wreq in Hw. by destruct Hw as [_ ->]. }
      split; [assumption|].
      reflexivity.
    }
    destruct Hgraph_co as [Hinternal _ _].
    set(internal := (AACandExec.Candidate.po (GlobalState.gs_graph gs) ∩ AACandExec.Candidate.loc (GlobalState.gs_graph gs)
        ∪ AAConsistent.ca (GlobalState.gs_graph gs) ∪ AACandExec.Candidate.rf (GlobalState.gs_graph gs))).
    assert(Hpo_int : (leid, eid) ∈ internal). { set_solver+ internal Hpo'' Hloc. }
    assert(Hfr_int : (eid, leid) ∈ internal). { set_solver+ internal Hfr. }
    assert(Hcyc : (leid, leid) ∈ GRel.grel_plus internal).
    { apply (GRel.grel_plus_trans _ leid eid leid); apply GRel.grel_plus_once; assumption. }
    rewrite GRel.grel_irreflexive_spec in Hinternal.
    exfalso.
    specialize (Hinternal (leid, leid)). simpl in Hinternal.
    by apply Hinternal.
  Qed.
End rules.
