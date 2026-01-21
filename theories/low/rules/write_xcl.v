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

(* This file contains the low-level proof rules for exclusive memory writes *)
From self.low.rules Require Import prelude.

Import uPred.

Section rules.
  Context `{AAIrisG} `{Htg: !ThreadGNL}.
  Import ThreadState.
  Import AACand.

  (** rules *)
  (* No exclusive read to pair with *)
  Lemma mem_write_xcl_None {tid : Tid} {ts ctxt addr kind_v kind_s val dep_addr dep_data}:
    ThreadState.ts_reqs ts = AAInter.Next (AAInter.MemWrite 8 (writereq_of_store kind_v kind_s val addr dep_addr dep_data)) ctxt ->
    ThreadState.ts_rmw_pred ts = None ->
    kind_v = AV_exclusive ->
    let eid := progress_to_node (get_progress ts) tid in
    {SS{{
           True
    }}}
    (LThreadState.LTSNormal ts) @ tid
    {{{ RET LThreadState.LTSNormal ((ThreadState.incr_cntr ts) <| ts_reqs := ctxt (inl false) |>);
        True
    }}}.
  Proof.
    iIntros (Hreqs Hrmw_src Hatomic ?).
    iIntros (Φ) "_ HΦ".
    rewrite sswp_eq /sswp_def /=.
    iIntros (????) "H". iNamed "H".
    inversion Hat_prog as [Hpg].  clear Hat_prog.
    case_bool_decide as Hv.
    2:{
      rewrite (LThreadStep.step_progress_valid_is_reqs_nonempty _ _ _ ts) in Hv; [|reflexivity|eassumption].
      rewrite Hreqs /EmptyInterp /= in Hv. exfalso. apply Hv. congruence.
    }
    iIntros (?). iNamed 1.

    inversion_step Hstep.
    inversion H3. subst. cdestruct H8. subst wreq. clear H3.
    simpl in H2. inversion H2.

    rewrite Hrmw_src in H3. inversion H3.

    subst eid. set (eid := (mk_eid_ii ts tid)).
    (* update na *)
    iNamed "Hinterp_annot".
    iDestruct "Hannot_at_prog" as "#Hannot_at_prog".
    iMod (annot_alloc na (get_progress ts) tid gs emp%I with "[$Hinterp_annot $Hannot_at_prog //]") as "(Hinterp_annot & _)".
    iMod (token_alloc with "[$Hinterp_token $Hannot_at_prog //]") as "(Hinterp_token & _)".

    iExists emp%I, ∅, ∅, ls.
    iModIntro. Local Opaque annot_res.annot_interp.
    iNext. iModIntro.
    iSplitR. { iApply empty_na_splitting_wf. }
    iSplitR.

    (** getting out resources from FE *)
    {
      rewrite flow_eq_dyn_unseal /flow_eq_dyn_def.
      iIntros (??). repeat iNamed 1.

      pose proof (prot_inv_unchanged _ σ s_ob eid Hgraph_wf) as Hprot_inv.
      iDestruct "Hob_pred_sub" as %Hob_pred_sub.
      iDestruct "Hob_pred_nin" as %Hob_pred_nin.
      ospecialize* Hprot_inv.
      { set_solver + Hv. }
      { set_solver + Hob_pred_nin. }
      { set_solver + Hob_pred_sub. }
      rewrite Hgr_lk /= in Hprot_inv.

      iDestruct (Hprot_inv with "Hob_st") as ">Hob_st".

      iApply step_fupd_intro;first set_solver +.
      iNext. iExists σ.
      iFrame.
    }

    iSplitL "Hinterp_annot Hinterp_token".
    { rewrite -map_union_assoc. rewrite map_empty_union. rewrite insert_union_singleton_l.
      iFrame. rewrite dom_union_L dom_singleton_L. iFrame. }
    iSplitL "Hinterp_local".
    {
      iNamed "Hinterp_local". iSplitL "Hinterp_local_lws".
      iApply (last_write_interp_progress_non_write with "Hinterp_local_lws");[reflexivity|].
      intro Hin. erewrite progress_to_node_mk_eid_ii in Hin;[|reflexivity].
      set_unfold in Hin. cdestruct Hin as ? ? Hlk'. rewrite Hgr_lk in Hlk'. unfold resp in Hlk'.
      cdestruct Hlk'.
      iApply (po_pred_interp_skip with "Hinterp_po_src"). reflexivity.
    }
    iApply "HΦ". done.
  Qed.

  (* there is a read to pair, the operation can be successful or failed *)
  Lemma mem_write_xcl_Some {tid : Tid} {o_po_src ts ctxt addr kind_v kind_s val ot_coi_pred dep_addr dep_data R_loc_in rmw_src} R po_srcs lob_annot:
    ThreadState.ts_reqs ts = AAInter.Next (AAInter.MemWrite 8 (writereq_of_store kind_v kind_s val addr dep_addr dep_data)) ctxt ->
    ThreadState.ts_rmw_pred ts = Some rmw_src ->
    kind_v = AV_exclusive ->
    let eid := progress_to_node (get_progress ts) tid in
    let R_graph_facts :=
        (eid -{E}> (Event.W kind_v kind_s addr val) ∗
        (* Po *)
        ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{(Edge.Po)}> eid) ∗
        (* Ctrl *)
        ([∗ set] eid_ctrl_src ∈ ts.(ts_ctrl_srcs), eid_ctrl_src -{(Edge.Ctrl)}> eid) ∗
        (* Data *)
        ([∗ set] eid_addr_src ∈ LThreadStep.deps_of_depon tid ts dep_addr, eid_addr_src -{(Edge.Addr)}> eid) ∗
        (* Addr *)
        ([∗ set] eid_data_src ∈ LThreadStep.deps_of_depon tid ts dep_data, eid_data_src -{(Edge.Data)}> eid) ∗
        (* There must be a write with same addr and val *)
        from_option (λ eid_coi_pred, ⌜EID.tid eid_coi_pred = tid⌝ ∗ eid_coi_pred -{(Edge.Co)}> eid) emp ot_coi_pred ∗
        (* Rmw *)
        rmw_src -{(Edge.Lxsx)}> eid)%I in
    {SS{{
           o_po_src -{LPo}> ∗
           ([∗ set] e_po_src ∈ po_srcs, e_po_src -{Po}>) ∗
           last_local_write tid addr ot_coi_pred ∗
           (* node annotations *)
           ([∗ map] node ↦ annot ∈ lob_annot, node ↦ₐ annot) ∗
           (* Lob edge formers *)
           (eid -{N}> (Edge.W kind_v kind_s) -∗
            ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{(Edge.Po)}> eid) -∗
            ([∗ set] eid_ctrl_src ∈ ts.(ts_ctrl_srcs), eid_ctrl_src -{(Edge.Ctrl)}> eid) -∗
            ([∗ set] eid_addr_src ∈ LThreadStep.deps_of_depon tid ts dep_addr, eid_addr_src -{(Edge.Addr)}> eid) -∗
            ([∗ set] eid_data_src ∈ LThreadStep.deps_of_depon tid ts dep_data, eid_data_src -{(Edge.Data)}> eid) -∗
            rmw_src -{(Edge.Lxsx)}> eid -∗
            [∗ set] eid_pre ∈ dom lob_annot, eid_pre -{Edge.Lob}> eid) ∗
           (* local resources that might flow into FE *)
           R_loc_in ∗
           (* FE *)
           (∃ prot q Q,
               (([∗ map] _ ↦ annot ∈ lob_annot, annot) -∗
                『addr, q | prot』 ∗ Q) ∗
               (R_loc_in ∗ 『addr, q | prot』 ∗ Q ∗ R_graph_facts
                ={⊤}[∅]▷=∗
                R ∗ (prot val eid)))
    }}}
    (LThreadState.LTSNormal ts) @ tid
    {{{ (b_succ: bool), RET LThreadState.LTSNormal ((ThreadState.incr_cntr ts) <| ts_reqs := ctxt (inl b_succ) |>);
      (* exists a bool (indicating if the (atomic) write succeeded) *)
      if b_succ then
        (* success *)
        R_graph_facts ∗
        (* R flowing in via lob *)
        (eid ↦ₐ R) ∗
        (Some eid) -{LPo}> ∗
        (* local writes at addr is updated *)
        last_local_write tid addr (Some eid) ∗
        Tok{ eid }
      else
        (* failure, things stay unchanged *)
        o_po_src -{LPo}> ∗
        last_local_write tid addr ot_coi_pred ∗
        ([∗ map] node ↦ annot ∈ lob_annot, node ↦ₐ annot) ∗
        R_loc_in
    }}}.
  Proof.
    iIntros (Hreqs Hrmw_src Hatomic ??).
    iIntros (Φ) "(Hpo_src & Hpo_srcs & Hlocal & Hannot & Hef & R_loc_in & Hfe) HΦ".
    rewrite sswp_eq /sswp_def /=.
    iIntros (????) "H". iNamed "H".
    inversion Hat_prog as [Hpg]. clear Hat_prog.
    case_bool_decide as Hv.
    2:{
      rewrite (LThreadStep.step_progress_valid_is_reqs_nonempty _ _ _ ts) in Hv; [|reflexivity|eassumption].
      rewrite Hreqs /EmptyInterp /= in Hv. exfalso. apply Hv. congruence.
    }
    iIntros (?). iNamed 1.

    (* Hstep gives that a write event is happening *)
    inversion_step Hstep.

    inversion H3. subst. cdestruct H8. subst wreq.
    simpl in H2.  done.

    inversion H4. subst. cdestruct H10. subst wreq. cbn in *. clear H4 H2.
    rewrite Hrmw_src in H3; inversion H3;clear H3; subst.

    { (* successful case *)
      iNamed "Hinterp_local".
      iDestruct (po_pred_interp_agree with "Hinterp_po_src Hpo_src") as %Hpo.
      iDestruct (po_pred_interp_agree_big' with "Hinterp_po_src Hpo_srcs") as %Hpo_src.

      subst eid;set (eid := (mk_eid_ii ts tid)).

      iDestruct (last_local_write_co with "Hinterp_global Hinterp_local_lws Hlocal") as "#Ed_co"; [assumption|assumption|eassumption| done | done |].

      (** allocate resources *)
      iAssert R_graph_facts as "#(E_W & Ed_po & Ed_ctrl & Ed_addr & Ed_data & _ & Ed_rmw)".
      {
        rewrite /R_graph_facts edge_eq /edge_def. rewrite event_eq /event_def. iNamed "Hinterp_global".

        iSplitL;first alloc_graph_res. done.

        iSplitL. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.
        destruct (Hpo_src x) as [? [? ?]]; try assumption. rewrite -(progress_to_node_of_node tid x);try assumption.
        rewrite /eid. apply progress_lt_po. assumption. repeat (split;try assumption).

        iSplitL. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.

        iSplitL. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.

        iSplitL. rewrite big_sepS_forall. iIntros (??). alloc_graph_res.

        iFrame "Ed_co".

        alloc_graph_res. done.
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
      iDestruct (na_at_progress_not_elem_of with "Hannot_at_prog") as %Hpg_not_in.
      iDestruct "Hannot_at_prog" as "#Hannot_at_prog".
      iMod (annot_alloc _ (get_progress ts) tid gs R with "[$Hinterp_annot //]") as "(Hinterp_annot & Hannot_curr)".
      iMod (token_alloc with "[$Hinterp_token $Hannot_at_prog]") as "(Hinterp_token & Htok)".
      iDestruct "Hannot_at_prog" as %Hannot_at_prog.

      iDestruct (annot_detach_big with "Hinterp_annot Hannot") as ">(%lob_annot_uu&%Hannot_dom & Hinterp_annot & #Hannot_split)".

      (** update ls*)
      iMod (po_pred_interp_update _ ts (ts <| ts_reqs := ctxt (inl true) |>) with "Hinterp_po_src Hpo_src") as "(Hinterp_po_src & Hpo_src)";try assumption.
      cbv;reflexivity.

      iExists R, lob_annot, lob_annot_uu, (ls <|lls_lws := <[addr := (Some (progress_to_node (get_progress ts) tid))]>ls.(lls_lws)|>
                                              <| lls_pop := Some eid|>).
      iSplitR. iModIntro. iModIntro. iModIntro.
      iSplit.
      (* show well-splittedness *)
      { iPureIntro. by apply Edge.subseteq_lob. }
      {
        iApply (big_sepM2_impl with "Hannot_split"). iModIntro. iIntros (k P1 P2 Hlk1 Hlk2) "Heqv".
        assert (is_Some (lob_annot !! k)) as [P Hlob_annot_lk].
        {
          apply elem_of_dom. apply elem_of_dom_2 in Hlk1. assumption.
        }
        assert (is_Some (na !! k)) as [P' Hna_lk].
        {
          apply elem_of_dom. apply elem_of_dom_2 in Hlk1.
          set_solver + Hlk1 Hlob_annot_dom_sub.
        }
        rewrite lookup_insert_ne. 2:{ apply elem_of_dom_2 in Hna_lk. set_solver + Hna_lk Hpg_not_in. }
        rewrite Hna_lk /=. iNext. iFrame.
      }

      (** pushing resources into FE *)
      iSplitL "Hfe R_loc_in".
      {
        iModIntro. iModIntro. iModIntro.
        rewrite flow_eq_dyn_unseal /flow_eq_dyn_def.
        iIntros (??). repeat iNamed 1.

        iDestruct "Hfe" as "(% & % & % & Hprot & Hfe)".

        iDestruct ("Hprot" with "R_lob_in") as "[Hp R_lob_in]".
        iNamed "Hob_st".

        iDestruct (prot_loc_agree with "Hprot Hp") as "[% [%Hprot_map_lk #Heql]]".

        pose proof (prot_inv_unchanged _ σ s_ob eid Hgraph_wf) as Hprot_inv.
        iDestruct "Hob_pred_sub" as %Hob_pred_sub.
        iDestruct "Hob_pred_nin" as %Hob_pred_nin.
        ospecialize* Hprot_inv.
        { set_solver + Hv. }
        { set_solver + Hob_pred_nin. }
        { set_solver + Hob_pred_sub. }
        rewrite Hgr_lk /= in Hprot_inv.
        rewrite Hprot_map_lk /= in Hprot_inv.

        iDestruct ("Hfe" with "[$R_loc_in $R_lob_in $Hp]") as ">Hfe".
        { iFrame "E_W Ed_po Ed_ctrl Ed_addr Ed_data Ed_co Ed_rmw". }

        iModIntro. iNext.
        iMod "Hfe" as "[$ Hp]".


        iDestruct (Hprot_inv with "[Hp $Hprot $Hprot_res]") as ">Hprot".
        iSpecialize ("Heql" $! val(progress_to_node (get_progress ts) tid)).
        iRewrite "Heql" in "Hp".
        iFrame.
        iFrame. clear;done.
      }

      iDestruct (na_at_progress_not_elem_of with "[]") as %Hna_not_in.
      iPureIntro. exact Hannot_at_prog.
      iSplitL "Hinterp_annot Hinterp_token".
      {
        rewrite -insert_union_r. rewrite -assoc_L. rewrite insert_union_singleton_l.
        rewrite insert_union_singleton_l. iFrame "Hinterp_annot".
        rewrite !dom_union_L. rewrite dom_insert_L. rewrite dom_empty_L.
        assert ((dom lob_annot_uu ∪ dom na) = dom na) as ->.
        { rewrite Hannot_dom. set_solver + Hlob_annot_dom_sub. }
        assert ({[{| EID.tid := tid; EID.iid := iis_iid (ts_iis ts); EID.ieid := iis_cntr (ts_iis ts) |}]} ∪ ∅ ∪ dom na = {[progress_to_node (get_progress ts) tid]} ∪ dom na) as -> by set_solver +.
        iFrame. clear;done.
        apply not_elem_of_dom. rewrite Hannot_dom. set_solver + Hna_not_in Hlob_annot_dom_sub.
      }

      (* update and frame [my_local_interp] *)
      rewrite /resp /=.
      iDestruct (last_write_interp_progress_write _
                   (ts <| ts_reqs := ctxt (inl true) |>) with "Hinterp_local_lws Hlocal") as ">[$ ?]".
      done. eexists. erewrite progress_to_node_mk_eid_ii;last reflexivity. eexists. split. exact Hgr_lk.
      simpl. done.
      iFrame "Hinterp_po_src".

      iModIntro. iNext. iModIntro.

      iApply ("HΦ" $! true).
      iFrame. iFrame "#".
    }
    { (* failing case *)
      iNamed "Hinterp_annot". iDestruct "Hannot_at_prog" as "#Hannot_at_prog".
      (* update na *)
      iMod (annot_alloc na (get_progress ts) tid gs emp%I with "[$Hinterp_annot $Hannot_at_prog //]") as "(Hinterp_annot & _)".
      iMod (token_alloc with "[$Hinterp_token]") as "(Hinterp_token & Htok)". iFrame "#".

      iExists emp%I, ∅, ∅, ls.
      iModIntro.
      Local Opaque annot_res.annot_interp.
      iNext. iModIntro.

      iSplitR. { iApply empty_na_splitting_wf. }

      iSplitR.
      (** getting out resources from FE *)
      {
        rewrite flow_eq_dyn_unseal /flow_eq_dyn_def.
        iIntros (??). repeat iNamed 1.

        pose proof (prot_inv_unchanged _ σ s_ob eid Hgraph_wf) as Hprot_inv.
        iDestruct "Hob_pred_sub" as %Hob_pred_sub.
        iDestruct "Hob_pred_nin" as %Hob_pred_nin.
        ospecialize* Hprot_inv.
        { set_solver + Hv. }
        { set_solver + Hob_pred_nin. }
        { set_solver + Hob_pred_sub. }
        rewrite Hgr_lk /= in Hprot_inv.

        iDestruct (Hprot_inv with "Hob_st") as ">Hob_st".

        iApply step_fupd_intro;first set_solver +.
        iNext. iExists σ.
        iFrame.
      }

      iSplitL "Hinterp_annot Hinterp_token".
      { rewrite -map_union_assoc. rewrite map_empty_union. rewrite insert_union_singleton_l. iFrame.
        rewrite dom_union_L dom_singleton_L. iFrame. }
      iSplitL "Hinterp_local".
      {
        iNamed "Hinterp_local". iSplitL "Hinterp_local_lws".
        iApply (last_write_interp_progress_non_write with "Hinterp_local_lws");[reflexivity|].
        intro Hin. erewrite progress_to_node_mk_eid_ii in Hin;[|reflexivity].
        set_unfold in Hin. cdestruct Hin as ? ? Hlk'.
        rewrite Hgr_lk in Hlk'. cdestruct Hlk'.
        iApply (po_pred_interp_skip with "Hinterp_po_src"). reflexivity.
      }

      iApply ("HΦ" $! false).
      iFrame.
    }
  Qed.

End rules.
