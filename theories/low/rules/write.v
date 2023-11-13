(* This file contains the low-level proof rules for (non-exclusive) memory writes *)
From self.low.rules Require Import prelude.

Import uPred.

Section rules.
  Context `{AAIrisG} `{Htg: !ThreadGNL}.
  Import ThreadState.

  Lemma mem_write_non_xcl `{!UserProt} {tid : Tid} {o_po_src ts ctxt addr kind_s kind_v val ot_coi_pred dep_addr dep_data} R po_srcs lob_annot:
    ThreadState.ts_reqs ts = AAInter.Next (AAInter.MemWrite 8 (writereq_of_store kind_s kind_v val addr dep_addr dep_data)) ctxt ->
    kind_v = AV_plain ->
    let eid := progress_to_node (get_progress ts) tid in
    let R_graph_facts := (eid -{E}> (Event.W kind_s kind_v addr val) ∗
      (* Po *)
      ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{(Edge.Po)}> eid) ∗
      (* Ctrl *)
      ([∗ set] eid_ctrl_src ∈ ts.(ts_ctrl_srcs), eid_ctrl_src -{(Edge.Ctrl)}> eid) ∗
      (* Data *)
      ([∗ set] eid_addr_src ∈ LThreadStep.deps_of_depon tid ts (Some dep_addr), eid_addr_src -{(Edge.Addr)}> eid) ∗
      (* Addr *)
      ([∗ set] eid_data_src ∈ LThreadStep.deps_of_depon tid ts (Some dep_data), eid_data_src -{(Edge.Data)}> eid) ∗
      (* There must be a write with same addr and val *)
      from_option (λ eid_coi_pred, ⌜EID.tid eid_coi_pred = tid⌝ ∗ eid_coi_pred -{(Edge.Co)}> eid) emp ot_coi_pred)%I in
    o_po_src -{LPo}> -∗
    ([∗ set] e_po_src ∈ po_srcs, e_po_src -{Po}>) -∗
    last_local_write tid addr ot_coi_pred -∗
    (* node annotations *)
    ([∗ map] node ↦ annot ∈ lob_annot, node ↦ₐ annot) -∗
    (* Lob edge formers *)
    (eid -{N}> (Edge.W kind_s kind_v) -∗
     ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{(Edge.Po)}> eid) -∗
     ([∗ set] eid_ctrl_src ∈ ts.(ts_ctrl_srcs), eid_ctrl_src -{(Edge.Ctrl)}> eid) -∗
     ([∗ set] eid_addr_src ∈ LThreadStep.deps_of_depon tid ts (Some dep_addr), eid_addr_src -{(Edge.Addr)}> eid) -∗
     ([∗ set] eid_data_src ∈ LThreadStep.deps_of_depon tid ts (Some dep_data), eid_data_src -{(Edge.Data)}> eid) -∗
     [∗ set] eid_pre ∈ dom lob_annot, eid_pre -{Edge.Lob}> eid) -∗
    (* FE *)
    (R_graph_facts ∗ ([∗ map] _ ↦ annot ∈ lob_annot, annot)
       ={⊤}[∅]▷=∗
       R eid ∗ □(prot addr val eid)) -∗
    SSWP (LThreadState.LTSNormal ts) @ tid {{ λ lts',
      (* exists a bool (indicating if the (atomic) write succeeded) *)
      (* update lts' accordingly *)
      ⌜lts' = LThreadState.LTSNormal ((ThreadState.incr_cntr ts)
                                        <| ts_reqs := ctxt (inl None) |>)⌝ ∗
      R_graph_facts ∗
      (* R flowing in via lob *)
      (eid ↦ₐ R eid) ∗
      (* eid is the latest po pred *)
      (Some eid) -{LPo}> ∗
      (* local writes at addr is updated *)
      last_local_write tid addr (Some eid)
    }}.
  Proof.
    iIntros (Hreqs -> ? ?) "Hpo_src Hpo_srcs Hlocal Hannot Hef Hfe".
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
    inversion_step Hstep; resolve_atomic.

    subst eid. set (eid := (mk_eid_ii ts tid)).
    iNamed "Hinterp_local".
    iDestruct (po_pred_interp_agree with "Hinterp_po_src Hpo_src") as %Hpo.
    iDestruct (po_pred_interp_agree_big' with "Hinterp_po_src Hpo_srcs") as %Hpo_src.

    (** allocate resources *)
    iDestruct (last_local_write_co with "Hinterp_global Hinterp_local_lws Hlocal") as "#Ed_co";[done|done|done| |].
    simpl;case_bool_decide;done.

    iAssert R_graph_facts as "#(E_W & Ed_po & Ed_ctrl & Ed_addr & Ed_data & _)".
    {
      rewrite /R_graph_facts edge_eq /edge_def. rewrite event_eq /event_def. iNamed "Hinterp_global".

      iSplitR;first alloc_graph_res.
      { rewrite /AACandExec.Candidate.kind_of_wreq_P /=. repeat case_bool_decide;try contradiction;auto. }

      iSplitL. iApply big_sepS_forall. iIntros (??). alloc_graph_res.
      destruct (Hpo_src x) as [? [? ?]];auto. rewrite -(progress_to_node_of_node tid x);auto.
      rewrite /eid. apply progress_lt_po;auto.

      iSplitR. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.

      iSplitR. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.

      iSplitR. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.

      iFrame "Ed_co".
    }

    (** get lob *)
    iDestruct ("Hef" with "[E_W] Ed_po Ed_ctrl Ed_addr Ed_data") as "#E_lob".
    { iApply (event_node with "E_W"). }

    (** agree on lob *)
    iDestruct (graph_edge_agree_big_pred with "Hinterp_global E_lob") as %Hlob.

    (** agree on lob_annot *)
    iNamed "Hinterp_annot".
    iDestruct (annot_agree_big with "Hinterp_annot Hannot") as "[%Hlob_annot_dom_sub #_]".

    (** update na *)
    iDestruct (na_at_progress_not_elem_of with "Hannot_at_prog") as %Hpg_not_in.
    iDestruct "Hannot_at_prog" as "#Hannot_at_prog".
    iMod (annot_alloc _ (get_progress ts) tid gs (R eid) with "[$Hinterp_annot //]") as "(Hinterp_annot & Hannot_curr)".
    iMod (token_alloc with "[$Hinterp_token $Hannot_at_prog]") as "(Hinterp_token & Htok)".
    iDestruct "Hannot_at_prog" as %Hannot_at_prog.

    iDestruct (annot_update_big with "Hinterp_annot Hannot") as ">(%lob_annot_uu&%Hannot_dom & Hinterp_annot & #Hannot_split)".

    (** update ls*)
    iMod (po_pred_interp_update _ ts (ts <| ts_reqs := ctxt (inl None) |>) with "Hinterp_po_src Hpo_src") as "(Hinterp_po_src & Hpo_src)";auto.

    iExists (R eid), lob_annot, lob_annot_uu, (ls <|lls_lws := <[addr := (Some (progress_to_node (get_progress ts) tid))]>ls.(lls_lws)|>
                                          <| lls_pop := Some eid|>).
    iSplitL "Hfe". iSplitR.
    (* show well-splittedness *)
    iModIntro. iSplit.
    { iPureIntro. by apply Edge.subseteq_lob. }
    {
      iApply (big_sepM2_impl with "Hannot_split"). iModIntro. iIntros (k P1 P2 Hlk1 Hlk2) "Heqv".
      assert (is_Some (lob_annot !! k)) as [P Hlob_annot_lk].
      {
        apply elem_of_dom. apply elem_of_dom_2 in Hlk1. done.
      }
      assert (is_Some (na !! k)) as [P' Hna_lk].
      {
        apply elem_of_dom. apply elem_of_dom_2 in Hlk1.
        set_solver + Hlk1 Hlob_annot_dom_sub.
      }
      rewrite lookup_insert_ne. 2:{ apply elem_of_dom_2 in Hna_lk. set_solver + Hna_lk Hpg_not_in. }
      rewrite Hna_lk /=. iNext. rewrite wand_iff_sym //.
    }

    (** pushing resources into FE *)
    {
      iModIntro. repeat iNamed 1.

      rewrite /prot_node /=. erewrite progress_to_node_mk_eid_ii;last reflexivity.
      rewrite iris_extra.big_sepS_to_map.
      2:{ set_solver + Hlob. }
      iDestruct ("Hfe" with "[R_lob_in]") as ">Hfe".
      { iFrame "E_W Ed_po Ed_ctrl Ed_addr Ed_data Ed_co". iApply (big_sepM_proper with "R_lob_in");auto. }

      iModIntro. iNext.
      iDestruct (fupd_frame_l with "[E_W Hfe]") as "Hfe". iSplitR. iExact "E_W". iExact "Hfe".
      iApply (fupd_mono with "Hfe"). iIntros "[#E_W [$ #R_prot]]".
      iModIntro. iIntros (????) "E_W'". iDestruct (event_agree with "E_W E_W'") as %Heq.
      inversion Heq;subst. iFrame "R_prot".
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

    (* update and frame [my_local_interp] *)
    iDestruct (last_write_interp_progress_write _ (ts <| ts_reqs := ctxt (inl None) |>) with "Hinterp_local_lws Hlocal") as ">[$ $]".
    done. done. eexists. erewrite progress_to_node_mk_eid_ii;last reflexivity. split. exact Hgr_lk.
    simpl. case_bool_decide;done.
    iFrame "Hinterp_po_src".

    iModIntro. iSplit. iPureIntro. done.
    iFrame "E_W Ed_po Ed_ctrl Ed_addr Ed_data Ed_co".  by iFrame "Hannot_curr Hpo_src".
  Qed.

End rules.
