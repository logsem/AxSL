(* This file contains the low-level proof rules for memory barriers *)
From self.low.rules Require Import prelude.

Import uPred.

Section rules.
  Context `{AAIrisG} `{Htg: !ThreadGNL}.
  Import ThreadState.

  Lemma dmb `{!UserProt} {tid : Tid} {o_po_src ts ctxt kind}:
    ThreadState.ts_reqs ts = AAInter.Next (AAInter.Barrier (AAArch.DMB kind)) ctxt ->
    let eid := progress_to_node (get_progress ts) tid in
    o_po_src -{LPo}> -∗
    SSWP (LThreadState.LTSNormal ts) @ tid {{ λ lts',
      (* update lts' accordingly *)
      ⌜lts' =(LThreadState.LTSNormal ((incr_cntr ts) <| ts_reqs := (ctxt tt) |>)) ⌝ ∗
      (* Current event is a read *)
      eid -{E}> (Event.B (AAArch.DMB kind)) ∗
      from_option (λ eid_po_src,  eid_po_src -{(Edge.Po)}> eid) emp o_po_src ∗
      Some eid -{LPo}>
    }}.
  Proof.
    iIntros (Hreqs ?) "Hpo_src".
    rewrite sswp_eq /sswp_def /=.
    iIntros (????) "H". iNamed "H".
    inversion Hat_prog as [Hpg]. clear Hat_prog.
    case_bool_decide as Hv.
    2:{
      rewrite (LThreadStep.step_progress_valid_is_reqs_nonempty _ _ _ ts) in Hv;[|done|done].
      rewrite Hreqs /EmptyInterp /= in Hv. exfalso. by apply Hv.
    }
    iIntros (?). iNamed 1.

    (* Hstep gives that a dmb event is happening *)
    inversion_step Hstep.

    subst eid. set (eid := (mk_eid_ii ts tid)).
    iNamed "Hinterp_local". iDestruct (po_pred_interp_agree with "Hinterp_po_src Hpo_src") as %Hpo.

    (** allocate resources *)
    iAssert (
      eid -{E}> (Event.B (AAArch.DMB dκ)) ∗
      (* Po *)
      from_option (λ eid_po_src,  eid_po_src -{(Edge.Po)}> eid) emp o_po_src)%I
      as "(E_B & Ed_po)".
    {
      rewrite edge_eq /edge_def. rewrite event_eq /event_def. iNamed "Hinterp_global".

      iSplitL;first alloc_graph_res. { repeat case_bool_decide;try contradiction;auto. }

      destruct o_po_src as [po_src|];last done. alloc_graph_res.
      destruct Hpo as [? [? ?]]. rewrite -(progress_to_node_of_node tid po_src);auto.
      rewrite /eid. erewrite <-progress_to_node_mk_eid_ii;last done.
      apply progress_lt_po;[done|repeat (split;[done|]);done].
    }

    (* update na *)
    iNamed "Hinterp_annot". iDestruct "Hannot_at_prog" as "#Hannot_at_prog".
    iMod (annot_alloc na (get_progress ts) tid gs emp%I with "[$Hinterp_annot $Hannot_at_prog //]") as "(Hinterp_annot & _)".
    iMod (token_alloc with "[$Hinterp_token $Hannot_at_prog //]") as "(Hinterp_token & _)".

    (* update ls *)
    iMod (po_pred_interp_update _ ts (ts <| ts_reqs := ctxt tt |>) with "Hinterp_po_src Hpo_src") as "(Hinterp_po_src & Hpo_src)";auto.

    iExists emp%I, ∅, ∅, (ls <|lls_pop := Some eid|>).
    iModIntro. iSplitR; [iSplitR |]. { by iApply empty_na_splitting_wf. }

    (** getting out resources from FE *)
    {
      repeat iNamed 1. iApply step_fupd_intro;auto.
      rewrite /prot_node /=. erewrite progress_to_node_mk_eid_ii;last reflexivity. iNext.

      iSplitL. iModIntro. iIntros (????) "E_W'".
      iDestruct (graph_event_agree with "Hinterp_global E_W'") as %Heq.
      destruct Heq as [? [Hlk ?]].
      rewrite Hlk in Hgr_lk. inversion Hgr_lk. subst x. contradiction. done.
    }

    iSplitL "Hinterp_annot Hinterp_token".
    { rewrite -map_union_assoc. rewrite map_empty_union. rewrite insert_union_singleton_l.
      iFrame. rewrite dom_union_L dom_singleton_L. by iFrame. }

    iSplitL "Hinterp_local_lws Hinterp_po_src".
    {
      iSplitL "Hinterp_local_lws".
      iApply (last_write_interp_progress_non_write with "Hinterp_local_lws");auto.
      intro Hin. erewrite progress_to_node_mk_eid_ii in Hin;last done.
      pose proof (AAConsistent.event_is_write_elem_of_mem_writes2 _ Hgraph_wf Hin) as [? [Hlk' HW]].
      rewrite Hgr_lk in Hlk'. inversion Hlk'. subst x. done.
      erewrite progress_to_node_mk_eid_ii;last reflexivity. done.
    }

    iFrame "E_B Ed_po Hpo_src". done.
  Qed.

  Lemma isb `{!UserProt} {tid : Tid} {o_po_src ts ctxt}:
    ThreadState.ts_reqs ts = AAInter.Next (AAInter.Barrier AAArch.ISB) ctxt ->
    let eid := progress_to_node (get_progress ts) tid in
    o_po_src -{LPo}> -∗
    SSWP (LThreadState.LTSNormal ts) @ tid {{ λ lts',
      (* update lts' accordingly *)
      ⌜lts' =(LThreadState.LTSNormal ((incr_cntr ts) <| ts_reqs := (ctxt tt) |>)) ⌝ ∗
      (* Current event is a read *)
      eid -{E}> (Event.B AAArch.ISB) ∗
      (* Po *)
      from_option (λ eid_po_src,  eid_po_src -{(Edge.Po)}> eid) emp o_po_src ∗
      (Some eid) -{LPo}> ∗
      (* Ctrl *)
      ([∗ set] eid_ctrl_src ∈ ts.(ts_ctrl_srcs), eid_ctrl_src -{(Edge.Ctrl)}> eid)
    }}.
  Proof.
    iIntros (Hreqs ?) "Hpo_src".
    rewrite sswp_eq /sswp_def /=.
    iIntros (????) "H". iNamed "H".
    inversion Hat_prog as [Hpg]. clear Hat_prog.
    case_bool_decide as Hv.
    2:{
      rewrite (LThreadStep.step_progress_valid_is_reqs_nonempty _ _ _ ts) in Hv;[|done|done].
      rewrite Hreqs /EmptyInterp /= in Hv. exfalso. by apply Hv.
    }
    iIntros (?). iNamed 1.

    (* Hstep gives that an isb event is happening *)
    inversion_step Hstep.

    subst eid. set (eid := (mk_eid_ii ts tid)).
    iNamed "Hinterp_local". iDestruct (po_pred_interp_agree with "Hinterp_po_src Hpo_src") as %Hpo.

    (** allocate resources *)
    iAssert (
      eid -{E}> (Event.B AAArch.ISB) ∗
      (* Po *)
      from_option (λ eid_po_src,  eid_po_src -{(Edge.Po)}> eid) emp o_po_src ∗
      (* Ctrl *)
      ([∗ set] eid_ctrl_src ∈ ts.(ts_ctrl_srcs), eid_ctrl_src -{(Edge.Ctrl)}> eid)
      )%I as "(E_B & Ed_po & Ed_ctrl)".
    {
      rewrite edge_eq /edge_def. rewrite event_eq /event_def. iNamed "Hinterp_global".

      iSplitL;first alloc_graph_res. done.

      iSplitL. destruct o_po_src as [po_src|];last done. alloc_graph_res.
      destruct Hpo as [? [? ?]]. rewrite -(progress_to_node_of_node tid po_src);last done.
      rewrite /eid. erewrite <-progress_to_node_mk_eid_ii;last done.
      apply progress_lt_po;first done. repeat(split;[done|]);done.

      rewrite big_sepS_forall. iIntros (??). alloc_graph_res.
    }

    (* update na *)
    iNamed "Hinterp_annot".
    iDestruct "Hannot_at_prog" as "#Hannot_at_prog".
    iMod (annot_alloc na (get_progress ts) tid gs emp%I with "[$Hinterp_annot $Hannot_at_prog //]") as "(Hinterp_annot & _)".
    iMod (token_alloc with "[$Hinterp_token $Hannot_at_prog //]") as "(Hinterp_token & _)".

    (* update ls *)
    iMod (po_pred_interp_update _ ts (ts <| ts_reqs := ctxt tt |>) with "Hinterp_po_src Hpo_src") as "(Hinterp_po_src & Hpo_src)";auto.

    iExists emp%I, ∅, ∅, (ls <|lls_pop := Some eid|>).
    iModIntro. iSplitR; [iSplitR |]. { by iApply empty_na_splitting_wf. }

    (** getting out resources from FE *)
    {
      repeat iNamed 1. iApply step_fupd_intro;first auto.
      rewrite /prot_node /=. erewrite progress_to_node_mk_eid_ii;last reflexivity. iNext.

      iSplitL. iModIntro. iIntros (????) "E_W'".
      iDestruct (graph_event_agree with "Hinterp_global E_W'") as %Heq.
      destruct Heq as [? [Hlk ?]].
      rewrite Hlk in Hgr_lk. inversion Hgr_lk. subst x. contradiction. done.
    }

    iSplitL "Hinterp_annot Hinterp_token".
    { rewrite -map_union_assoc. rewrite map_empty_union. rewrite insert_union_singleton_l.
      iFrame. rewrite dom_union_L dom_singleton_L. by iFrame. }
    iSplitL "Hinterp_local_lws Hinterp_po_src".
    {
      iSplitL "Hinterp_local_lws". iApply (last_write_interp_progress_non_write with "Hinterp_local_lws");auto.
      intro Hin. erewrite progress_to_node_mk_eid_ii in Hin;last done.
      pose proof (AAConsistent.event_is_write_elem_of_mem_writes2 _ Hgraph_wf Hin) as [? [Hlk' HW]].
      rewrite Hgr_lk in Hlk'. inversion Hlk'. subst x. contradiction.
      erewrite progress_to_node_mk_eid_ii;last reflexivity. done.
    }
    iFrame "E_B Ed_po Ed_ctrl". by iFrame.
  Qed.
End rules.


