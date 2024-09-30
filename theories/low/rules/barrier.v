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

(* This file contains the low-level proof rules for memory barriers *)
From self.low.rules Require Import prelude.

Import uPred.

Section rules.
  Context `{AAIrisG} `{Htg: !ThreadGNL}.
  Import ThreadState.

  Lemma dmb {tid : Tid} {o_po_src ts ctxt kind}:
    ThreadState.ts_reqs ts = AAInter.Next (AAInter.Barrier (AAArch.DMB kind)) ctxt ->
    let eid := progress_to_node (get_progress ts) tid in
    o_po_src -{LPo}> -∗
    SSWP (LThreadState.LTSNormal ts) @ tid {{ λ lts',
      (* update lts' accordingly *)
      ⌜lts' = (LThreadState.LTSNormal ((incr_cntr ts) <| ts_reqs := (ctxt tt) |>)) ⌝ ∗
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
      rewrite (LThreadStep.step_progress_valid_is_reqs_nonempty _ _ _ ts) in Hv; [|reflexivity|eassumption].
      rewrite Hreqs /EmptyInterp /= in Hv. exfalso. apply Hv. congruence.
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

      iSplitL;first alloc_graph_res. { repeat case_bool_decide;try contradiction; clear; auto. }

      destruct o_po_src as [po_src|];last (clear;done). alloc_graph_res.
      destruct Hpo as [? [? ?]]. rewrite -(progress_to_node_of_node tid po_src);last assumption.
      rewrite /eid. erewrite <-progress_to_node_mk_eid_ii;last done.
      apply progress_lt_po;[done|repeat (split;[done|]);done].
    }

    (* update na *)
    iNamed "Hinterp_annot". iDestruct "Hannot_at_prog" as "#Hannot_at_prog".
    iMod (annot_alloc na (get_progress ts) tid gs emp%I with "[$Hinterp_annot $Hannot_at_prog //]") as "(Hinterp_annot & _)".
    iMod (token_alloc with "[$Hinterp_token $Hannot_at_prog //]") as "(Hinterp_token & _)".

    (* update ls *)
    iMod (po_pred_interp_update _ ts (ts <| ts_reqs := ctxt tt |>) with "Hinterp_po_src Hpo_src") as "(Hinterp_po_src & Hpo_src)";[clear;auto| assumption|].
    iExists emp%I, ∅, ∅, (ls <|lls_pop := Some eid|>).
    iModIntro. iSplitR. { iApply empty_na_splitting_wf. }
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

    iSplitL "Hinterp_local_lws Hinterp_po_src".
    {
      iSplitL "Hinterp_local_lws".
      iApply (last_write_interp_progress_non_write with "Hinterp_local_lws");[reflexivity|].
      intro Hin. erewrite progress_to_node_mk_eid_ii in Hin;[|reflexivity].
      pose proof (AAConsistent.event_is_write_elem_of_mem_writes2 _ Hgraph_wf Hin) as [? [Hlk' HW]].
      rewrite Hgr_lk in Hlk'. inversion Hlk'. subst x. done.
      erewrite progress_to_node_mk_eid_ii;last reflexivity. iFrame.
    }

    iFrame "E_B Ed_po Hpo_src". clear;done.
  Qed.

  Lemma isb {tid : Tid} {o_po_src ts ctxt}:
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
      rewrite Hreqs /EmptyInterp /= in Hv. exfalso. apply Hv. congruence.
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

      iSplitL. destruct o_po_src as [po_src|];[|clear;done]. alloc_graph_res.
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
    iMod (po_pred_interp_update _ ts (ts <| ts_reqs := ctxt tt |>) with "Hinterp_po_src Hpo_src") as "(Hinterp_po_src & Hpo_src)";[clear;auto| assumption|].

    iExists emp%I, ∅, ∅, (ls <|lls_pop := Some eid|>).
    iModIntro. iSplitR. { iApply empty_na_splitting_wf. }
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
      iFrame. rewrite dom_union_L dom_singleton_L. by iFrame. }
    iSplitL "Hinterp_local_lws Hinterp_po_src".
    {
      iSplitL "Hinterp_local_lws". iApply (last_write_interp_progress_non_write with "Hinterp_local_lws"). reflexivity.
      intro Hin. erewrite progress_to_node_mk_eid_ii in Hin;[|reflexivity].
      pose proof (AAConsistent.event_is_write_elem_of_mem_writes2 _ Hgraph_wf Hin) as [? [Hlk' HW]].
      rewrite Hgr_lk in Hlk'. inversion Hlk'. subst x. contradiction.
      erewrite progress_to_node_mk_eid_ii;last reflexivity. iFrame.
    }
    iFrame "E_B Ed_po Ed_ctrl". iFrame. clear;done.
  Qed.
End rules.
