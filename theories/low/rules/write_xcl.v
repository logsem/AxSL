(* This file contains the low-level proof rules for exclusive memory writes *)
From self.low.rules Require Import prelude.

Import uPred.

Section rules.
  Context `{AAIrisG} `{Htg: !ThreadGNL}.
  Import ThreadState.
  (** rules *)
  Lemma mem_write_xcl_None `{!UserProt} {tid : Tid} {ts ctxt addr kind_s kind_v val dep_addr dep_data}:
    ThreadState.ts_reqs ts = AAInter.Next (AAInter.MemWrite 8 (writereq_of_store kind_s kind_v val addr dep_addr dep_data)) ctxt ->
    ThreadState.ts_rmw_pred ts = None ->
    kind_v = AV_atomic_rmw ∨ kind_v = AV_exclusive ->
    let eid := progress_to_node (get_progress ts) tid in
    ⊢ SSWP (LThreadState.LTSNormal ts) @ tid {{ λ lts',
      (* update lts' accordingly *)
      ⌜lts' = LThreadState.LTSNormal ((ThreadState.incr_cntr ts)
                                        <| ts_reqs := ctxt (inl (Some false)) |>)⌝
    }}.
  Proof.
    iIntros (Hreqs Hrmw_src Hatomic ?).
    rewrite sswp_eq /sswp_def /=.
    iIntros (????) "H". iNamed "H".
    inversion Hat_prog as [Hpg].  clear Hat_prog.
    case_bool_decide as Hv.
    2:{
      rewrite (LThreadStep.step_progress_valid_is_reqs_nonempty _ _ _ ts) in Hv;[|done|done].
      rewrite Hreqs /EmptyInterp /= in Hv. exfalso. by apply Hv.
    }
    iIntros (?). iNamed 1.

    inversion_step Hstep.
    destruct Hatomic;subst kind_v;resolve_atomic. inversion H3. inversion H3.
    rewrite Hrmw_src in H4. inversion H4.

    subst eid. set (eid := (mk_eid_ii ts tid)).

    (* update na *)
    iNamed "Hinterp_annot".
    iDestruct "Hannot_at_prog" as "#Hannot_at_prog".
    iMod (annot_alloc na (get_progress ts) tid gs emp%I with "[$Hinterp_annot $Hannot_at_prog //]") as "(Hinterp_annot & _)".
    iMod (token_alloc with "[$Hinterp_token $Hannot_at_prog //]") as "(Hinterp_token & _)".

    iExists emp%I, ∅, ∅, ls.
    iModIntro. iSplitR; [iSplitR |]. { by iApply empty_na_splitting_wf. }

    (** getting out resources from FE *)
    {
      repeat iNamed 1. iApply step_fupd_intro;first auto.
      rewrite /prot_node /=. erewrite progress_to_node_mk_eid_ii;last reflexivity. iNext.

      iSplitL. iModIntro. iIntros (????) "E_W'".
      iDestruct (graph_event_agree with "Hinterp_global E_W'") as %Heq.
      destruct Heq as [? [Hlk ?]].
      rewrite Hlk in Hgr_lk. inversion Hgr_lk. subst x.
      rewrite /AAConsistent.event_is_write_with //= in H2.

      done.
    }

    iSplitL "Hinterp_annot Hinterp_token".
    { rewrite -map_union_assoc. rewrite map_empty_union. rewrite insert_union_singleton_l.
      iFrame. rewrite dom_union_L dom_singleton_L //. }
    iSplitL "Hinterp_local";last done.
    {
      iNamed "Hinterp_local". iSplitL "Hinterp_local_lws".
      iApply (last_write_interp_progress_non_write with "Hinterp_local_lws");auto.
      intro Hin. erewrite progress_to_node_mk_eid_ii in Hin;eauto.
      pose proof (AAConsistent.event_is_write_elem_of_mem_writes2 _ Hgraph_wf Hin) as [? [Hlk' HW]].
      rewrite Hgr_lk in Hlk'. inversion Hlk'. subst x. done.
      iApply (po_pred_interp_skip with "Hinterp_po_src");auto.
    }
  Qed.

  Lemma mem_write_xcl_Some `{!UserProt} {tid : Tid} {o_po_src ts ctxt addr kind_s kind_v val ot_coi_pred dep_addr dep_data R_loc_in rmw_src} R po_srcs lob_annot:
    ThreadState.ts_reqs ts = AAInter.Next (AAInter.MemWrite 8 (writereq_of_store kind_s kind_v val addr dep_addr dep_data)) ctxt ->
    ThreadState.ts_rmw_pred ts = Some rmw_src ->
    kind_v = AV_atomic_rmw ∨ kind_v = AV_exclusive ->
    let eid := progress_to_node (get_progress ts) tid in
    let R_graph_facts :=
        (eid -{E}> (Event.W kind_s kind_v addr val) ∗
        (* Po *)
        ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{(Edge.Po)}> eid) ∗
        (* Ctrl *)
        ([∗ set] eid_ctrl_src ∈ ts.(ts_ctrl_srcs), eid_ctrl_src -{(Edge.Ctrl)}> eid) ∗
        (* Data *)
        ([∗ set] eid_addr_src ∈ LThreadStep.deps_of_depon tid ts (Some dep_addr), eid_addr_src -{(Edge.Addr)}> eid) ∗
        (* Addr *)
        ([∗ set] eid_data_src ∈ LThreadStep.deps_of_depon tid ts (Some dep_data), eid_data_src -{(Edge.Data)}> eid) ∗
        (* There must be a write with same addr and val *)
        from_option (λ eid_coi_pred, ⌜EID.tid eid_coi_pred = tid⌝ ∗ eid_coi_pred -{(Edge.Co)}> eid) emp ot_coi_pred ∗
        (* Rmw *)
        rmw_src -{(Edge.Rmw)}> eid)%I in
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
     rmw_src -{(Edge.Rmw)}> eid -∗
     [∗ set] eid_pre ∈ dom lob_annot, eid_pre -{Edge.Lob}> eid) -∗
    (* local resources that might flow into FE *)
    R_loc_in -∗
    (* FE *)
    (R_loc_in ∗ R_graph_facts ∗ Tok{ eid } ∗ ([∗ map] _ ↦ annot ∈ lob_annot, annot)
       ={⊤}[∅]▷=∗
       R ∗ □(prot addr val eid)) -∗
    SSWP (LThreadState.LTSNormal ts) @ tid {{ λ lts',
      (* exists a bool (indicating if the (atomic) write succeeded) *)
      ∃ b_succ,
      (* update lts' accordingly *)
      ⌜lts' = LThreadState.LTSNormal ((ThreadState.incr_cntr ts)
                                        <| ts_reqs := ctxt (inl (Some b_succ)) |>)⌝ ∗
      if b_succ then
        (* success *)
        R_graph_facts ∗
        (* R flowing in via lob *)
        (eid ↦ₐ R) ∗
        (Some eid) -{LPo}> ∗
        (* local writes at addr is updated *)
        last_local_write tid addr (Some eid)
      else
        (* failure, things stay unchanged *)
        o_po_src -{LPo}> ∗
        last_local_write tid addr ot_coi_pred ∗
        ([∗ map] node ↦ annot ∈ lob_annot, node ↦ₐ annot) ∗
        R_loc_in
    }}.
  Proof.
    iIntros (Hreqs Hrmw_src Hatomic ??) "Hpo_src Hpo_srcs Hlocal Hannot Hef R_loc_in Hfe".
    rewrite sswp_eq /sswp_def /=.
    iIntros (????) "H". iNamed "H".
    inversion Hat_prog as [Hpg]. clear Hat_prog.
    case_bool_decide as Hv.
    2:{
      rewrite (LThreadStep.step_progress_valid_is_reqs_nonempty _ _ _ ts) in Hv;[|done|done].
      rewrite Hreqs /EmptyInterp /= in Hv. exfalso. by apply Hv.
    }
    iIntros (?). iNamed 1.

    (* Hstep gives that a write event is happening *)
    inversion_step Hstep.
    destruct Hatomic;subst kind_v;resolve_atomic.
    { (* successful case *)
      iNamed "Hinterp_local".
      iDestruct (po_pred_interp_agree with "Hinterp_po_src Hpo_src") as %Hpo.
      iDestruct (po_pred_interp_agree_big' with "Hinterp_po_src Hpo_srcs") as %Hpo_src.

      subst eid;set (eid := (mk_eid_ii ts tid)).

      iDestruct (last_local_write_co with "Hinterp_global Hinterp_local_lws Hlocal") as "#Ed_co"; [done|done|done| |].
      simpl;case_bool_decide;done.

      (** allocate resources *)
      iAssert R_graph_facts as "#(E_W & Ed_po & Ed_ctrl & Ed_addr & Ed_data & _ & Ed_rmw)".
      {
        rewrite /R_graph_facts edge_eq /edge_def. rewrite event_eq /event_def. iNamed "Hinterp_global".

        iSplitL;first alloc_graph_res. {
          rewrite /AACandExec.Candidate.kind_of_wreq_P /=.
          repeat case_bool_decide;try contradiction;auto. }

        iSplitL. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.
        destruct (Hpo_src x) as [? [? ?]];auto. rewrite -(progress_to_node_of_node tid x);auto.
        rewrite /eid. apply progress_lt_po;auto.

        iSplitL. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.

        iSplitL. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.

        iSplitL. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.

        iFrame "Ed_co".

        rewrite Hrmw_src in H4;inversion H4;subst. alloc_graph_res. done.
      }

      (** get lob *)
      iDestruct ("Hef" with "[E_W] Ed_po Ed_ctrl Ed_addr Ed_data Ed_rmw") as "#E_lob".
      { iApply (event_node with "E_W"). }

      (** agree on lob *)
      iDestruct (graph_edge_agree_big_pred with "Hinterp_global E_lob") as %Hlob.

      iNamed "Hinterp_annot".
      (** agree on lob_annot *)
      iDestruct (annot_agree_big with "Hinterp_annot Hannot") as "[%Hlob_annot_dom_sub #_]".

      (** update na *)
      iDestruct (na_at_progress_not_elem_of with "Hannot_at_prog") as %Hpg_not_in;auto.
      iDestruct "Hannot_at_prog" as "#Hannot_at_prog".
      iMod (annot_alloc _ (get_progress ts) tid gs R with "[$Hinterp_annot //]") as "(Hinterp_annot & Hannot_curr)".
      iMod (token_alloc with "[$Hinterp_token $Hannot_at_prog]") as "(Hinterp_token & Htok)".
      iDestruct "Hannot_at_prog" as %Hannot_at_prog.

      iDestruct (annot_update_big with "Hinterp_annot Hannot") as ">(%lob_annot_uu&%Hannot_dom & Hinterp_annot & #Hannot_split)".

      (** update ls*)
      iMod (po_pred_interp_update _ ts (ts <| ts_reqs := ctxt (inl (Some true)) |>) with "Hinterp_po_src Hpo_src") as "(Hinterp_po_src & Hpo_src)";auto.

      iExists R, lob_annot, lob_annot_uu, (ls <|lls_lws := <[addr := (Some (progress_to_node (get_progress ts) tid))]>ls.(lls_lws)|>
                                              <| lls_pop := Some eid|>).
      iSplitL "Hfe R_loc_in Htok". iSplitR.
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
        iDestruct ("Hfe" with "[$R_loc_in $R_lob_in $Htok]") as ">Hfe".
        { iFrame "E_W Ed_po Ed_ctrl Ed_addr Ed_data Ed_co Ed_rmw". }

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
      rewrite /resp /=.
      iDestruct (last_write_interp_progress_write _
                   (ts <| ts_reqs := ctxt (inl (Some true)) |>) with "Hinterp_local_lws Hlocal") as ">[$ ?]".
      done. eexists. erewrite progress_to_node_mk_eid_ii;last reflexivity. eexists. split. exact Hgr_lk.
      simpl. case_bool_decide;done.
      iFrame "Hinterp_po_src".

      iModIntro. iExists true. iSplit. iPureIntro; done.
      iFrame "E_W Ed_po Ed_ctrl Ed_addr Ed_data Ed_co Ed_rmw".  by iFrame "Hannot_curr Hpo_src".
    }
    { (* failing case *)
      iNamed "Hinterp_annot". iDestruct "Hannot_at_prog" as "#Hannot_at_prog".
      (* update na *)
      iMod (annot_alloc na (get_progress ts) tid gs emp%I with "[$Hinterp_annot $Hannot_at_prog //]") as "(Hinterp_annot & _)".
      iMod (token_alloc with "[$Hinterp_token //]") as "(Hinterp_token & Htok)".

      iExists emp%I, ∅, ∅, ls.
      iModIntro. iSplitR; [iSplitR |]. { by iApply empty_na_splitting_wf. }

      (** getting out resources from FE *)
      {
        repeat iNamed 1. iApply step_fupd_intro;first auto.
        rewrite /prot_node /=. erewrite progress_to_node_mk_eid_ii;last reflexivity. iNext.

        iSplitL. iModIntro. iIntros (????) "E_W'".
        iDestruct (graph_event_agree with "Hinterp_global E_W'") as %Heq.
        destruct Heq as [? [Hlk ?]].
        rewrite Hlk in Hgr_lk. inversion Hgr_lk. subst x.
        rewrite /AAConsistent.event_is_write_with //= in H2.

        done.
      }

      iSplitL "Hinterp_annot Hinterp_token".
      { rewrite -map_union_assoc. rewrite map_empty_union. rewrite insert_union_singleton_l. iFrame.
        rewrite dom_union_L dom_singleton_L. iFrame. }
      iSplitL "Hinterp_local".
      {
        iNamed "Hinterp_local". iSplitL "Hinterp_local_lws".
        iApply (last_write_interp_progress_non_write with "Hinterp_local_lws");auto.
        intro Hin. erewrite progress_to_node_mk_eid_ii in Hin;eauto.
        pose proof (AAConsistent.event_is_write_elem_of_mem_writes2 _ Hgraph_wf Hin) as [? [Hlk' HW]].
        rewrite Hgr_lk in Hlk'. inversion Hlk'. subst x. done.
        iApply (po_pred_interp_skip with "Hinterp_po_src");auto.
      }
      iExists false. iSplit;first done.
      iFrame.
    }
  Qed.

End rules.
