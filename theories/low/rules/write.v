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

(* This file contains the low-level proof rules for (non-exclusive) memory writes *)
From self.low.rules Require Import prelude.

Import uPred.

Section rules.
  Context `{AAIrisG} `{Htg: !ThreadGNL}.
  Import ThreadState.
  Import AACand.

  Lemma mem_write_non_xcl {tid : Tid} {o_po_src ts ctxt addr kind_s kind_v val ot_coi_pred dep_addr dep_data} R po_srcs lob_annot:
    ThreadState.ts_reqs ts = AAInter.Next (AAInter.MemWrite 8 (writereq_of_store kind_v kind_s val addr dep_addr dep_data)) ctxt ->
    kind_v = AV_plain ->
    let eid := progress_to_node (get_progress ts) tid in
    let R_graph_facts := (eid -{E}> (Event.W kind_v kind_s addr val) ∗
      (* Po *)
      ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{(Edge.Po)}> eid) ∗
      (* Ctrl *)
      ([∗ set] eid_ctrl_src ∈ ts.(ts_ctrl_srcs), eid_ctrl_src -{(Edge.Ctrl)}> eid) ∗
      (* Data *)
      ([∗ set] eid_addr_src ∈ LThreadStep.deps_of_depon tid ts dep_addr, eid_addr_src -{(Edge.Addr)}> eid) ∗
      (* Addr *)
      ([∗ set] eid_data_src ∈ LThreadStep.deps_of_depon tid ts dep_data, eid_data_src -{(Edge.Data)}> eid) ∗
      (* There must be a write with same addr and val *)
      from_option (λ eid_coi_pred, ⌜EID.tid eid_coi_pred = tid⌝ ∗ eid_coi_pred -{(Edge.Co)}> eid) emp ot_coi_pred)%I in
    {SS{{
           o_po_src -{LPo}> ∗
           ([∗ set] e_po_src ∈ po_srcs, e_po_src -{Po}>) ∗
           last_local_write tid addr ot_coi_pred ∗
           (* node annotations *)
           ([∗ map] node ↦ annot ∈ lob_annot, node ↦ₐ annot) ∗
           (* Lob edge formers *)
           (eid -{N}> (Edge.W kind_v kind_s ) -∗
            ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{(Edge.Po)}> eid) -∗
            ([∗ set] eid_ctrl_src ∈ ts.(ts_ctrl_srcs), eid_ctrl_src -{(Edge.Ctrl)}> eid) -∗
            ([∗ set] eid_addr_src ∈ LThreadStep.deps_of_depon tid ts dep_addr, eid_addr_src -{(Edge.Addr)}> eid) -∗
            ([∗ set] eid_data_src ∈ LThreadStep.deps_of_depon tid ts dep_data, eid_data_src -{(Edge.Data)}> eid) -∗
            [∗ set] eid_pre ∈ dom lob_annot, eid_pre -{Edge.Lob}> eid) ∗
           (* FE *)
           (∃ prot q Q,
               (([∗ map] _ ↦ annot ∈ lob_annot, annot) -∗
                『addr, q | prot』 ∗ Q) ∗
               (『addr, q | prot』 ∗ Q ∗
                R_graph_facts
                ={⊤}[∅]▷=∗
                R eid ∗ (prot val eid)))
    }}}
    (LThreadState.LTSNormal ts) @ tid
    {{{ RET LThreadState.LTSNormal ((ThreadState.incr_cntr ts) <| ts_reqs := ctxt (inl true) |>);
      (* exists a bool (indicating if the (atomic) write succeeded) *)
      R_graph_facts ∗
      (* R flowing in via lob *)
      (eid ↦ₐ R eid) ∗
      (* eid is the latest po pred *)
      (Some eid) -{LPo}> ∗
      (* local writes at addr is updated *)
      last_local_write tid addr (Some eid)
    }}}.
  Proof.
    iIntros (Hreqs -> ? ?).
    iIntros (Φ) "(Hpo_src & Hpo_srcs & Hlocal & Hannot & Hef & Hfe) HΦ".
    rewrite sswp_eq /sswp_def /=.
    iIntros (????) "H". iNamed "H".
    inversion Hat_prog as [Hpg]. clear Hat_prog.

    unfold eid.
    inversion_step Hstep.
    (* resolve_atomic. *)
    2:{
      inversion H4. subst. cdestruct H10. subst wreq. cbn in *.
      case_bool_decide; inversion H2. inversion H1.
    }
    2:{
      inversion H3. subst. cdestruct H5. subst wreq. cbn in *.
      case_bool_decide; inversion H2. inversion H1.
    }

    inversion H3. subst. cdestruct H8. subst wreq. cbn in *. clear H2 H3.

    (* Hstep gives that a write event is happening *)
    (* go to valid case *)
    unfold eid0 in Hgr_lk.
    rewrite -(progress_to_node_mk_eid_ii _ _ (get_progress ts)) in Hgr_lk;last done.
    case_bool_decide as Hv.
    2:{
      rewrite (LThreadStep.step_progress_valid_is_reqs_nonempty _ _ _ ts) in Hv; [|reflexivity|eassumption].
      rewrite Hreqs /EmptyInterp /= in Hv. exfalso. apply Hv. congruence.
    }

    iIntros (?). iNamed 1.

    subst eid. set (eid := (mk_eid_ii ts tid)).
    iNamed "Hinterp_local".
    iDestruct (po_pred_interp_agree with "Hinterp_po_src Hpo_src") as %Hpo.
    iDestruct (po_pred_interp_agree_big' with "Hinterp_po_src Hpo_srcs") as %Hpo_src.

    (** allocate resources *)
    iDestruct (last_local_write_co with "Hinterp_global Hinterp_local_lws Hlocal") as "#Ed_co";[assumption|assumption|eassumption| done | done | ].

    iAssert R_graph_facts as "#(E_W & Ed_po & Ed_ctrl & Ed_addr & Ed_data & _)".
    {
      rewrite /R_graph_facts edge_eq /edge_def. rewrite event_eq /event_def. iNamed "Hinterp_global".

      iSplitR;first alloc_graph_res. done.

      iSplitL. iApply big_sepS_forall. iIntros (??). alloc_graph_res.
      destruct (Hpo_src x) as [? [? ?]];first assumption. rewrite -(progress_to_node_of_node tid x);[|assumption].
      rewrite /eid. apply progress_lt_po;first assumption. repeat (split;try assumption).

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

    iDestruct (annot_detach_big with "Hinterp_annot Hannot") as ">(%lob_annot_uu&%Hannot_dom & Hinterp_annot & #Hannot_split)".

    (** update ls*)
    iMod (po_pred_interp_update _ ts (ts <| ts_reqs := ctxt (inl true) |>) with "Hinterp_po_src Hpo_src") as "(Hinterp_po_src & Hpo_src)";[clear;auto|assumption|].

    iExists (R eid), lob_annot, lob_annot_uu, (ls <|lls_lws := <[addr := (Some (progress_to_node (get_progress ts) tid))]>ls.(lls_lws)|>
                                          <| lls_pop := Some eid|>).
    iModIntro.
    Local Opaque annot_res.annot_interp.
    iNext.
    iSplitR.
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
      rewrite Hna_lk /=. iNext. iFrame.
    }

    iSplitL "Hfe".
    (** pushing resources into FE *)
    {
      iModIntro.
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
     
      iDestruct ("Hfe" with "[R_lob_in Hp]") as ">Hfe".
      { iFrame. iFrame "#". }

      iModIntro. iNext. iMod "Hfe" as "[R Hp]".

      rewrite Hprot_map_lk /= in Hprot_inv.

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
      assert ({[{| EID.tid := tid; EID.iid := iis_iid (ts_iis ts); EID.ieid := iis_cntr (ts_iis ts) |}]} ∪ ∅ ∪ dom na = {[progress_to_node (get_progress ts) tid]} ∪ dom na) as ->.
      clear;set_solver.
      iFrame. clear;done.
      apply not_elem_of_dom. rewrite Hannot_dom. set_solver + Hna_not_in Hlob_annot_dom_sub.
    }

    (* update and frame [my_local_interp] *)
    iDestruct (last_write_interp_progress_write _ (ts <| ts_reqs := ctxt (inl true) |>) with "Hinterp_local_lws Hlocal") as ">[? ?]".
    done. done. eexists. erewrite progress_to_node_mk_eid_ii;last reflexivity. split. exact Hgr_lk.
    simpl. naive_solver.
    iFrame.

    iApply "HΦ".
    iFrame "#". iFrame. done.
  Qed.

End rules.
