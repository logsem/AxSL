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

(* This file contains the low-level proof rules for register operations *)
From self.low.rules Require Import prelude.

Import uPred.

Section rules.
  Context `{AAIrisG} `{Htg: !ThreadGNL}.
  Import ThreadState.

  Lemma reg_write {tid : Tid} {ts ctxt b reg o_dep val}:
    ThreadState.ts_reqs ts = AAInter.Next (AAInter.RegWrite reg b o_dep val) ctxt ->
    ⊢
    SSWP (LThreadState.LTSNormal ts) @ tid {{ λ lts',
      (* update lts' accordingly *)
      ⌜lts' = LThreadState.LTSNormal ((incr_cntr ts) <| ts_regs := <[reg := mk_regval val (LThreadStep.deps_of_depon tid ts o_dep)]>(ts.(ts_regs)) |>
                                                     <| ts_reqs := (ctxt tt) |>) ⌝
    }}.
  Proof.
    iIntros (Hreqs).
    rewrite sswp_eq /sswp_def /=.
    iIntros (????) "H". iNamed "H".
    inversion Hat_prog as [Hpg].  clear Hat_prog.
    case_bool_decide as Hv.
    2:{
      rewrite (LThreadStep.step_progress_valid_is_reqs_nonempty _ _ _ ts) in Hv; [|reflexivity|eassumption].
      rewrite Hreqs /EmptyInterp /= in Hv. exfalso. apply Hv. congruence.
    }
    iIntros (?). iNamed 1.

    (* Hstep gives that a reg-write event is happening *)
    inversion_step Hstep.

    set (eid := (mk_eid_ii ts tid)).

    (* update na *)
    iNamed "Hinterp_annot". iDestruct "Hannot_at_prog" as "#Hannot_at_prog".
    iMod (annot_alloc na (get_progress ts) tid gs emp%I with "[$Hinterp_annot $Hannot_at_prog //]") as "(Hinterp_annot & _)".
    iMod (token_alloc with "[$Hinterp_token $Hannot_at_prog //]") as "(Hinterp_token & _)".

    iExists emp%I, ∅, ∅, ls.
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
    iSplitL "Hinterp_local";last (clear;done).
    {
      iNamed "Hinterp_local". iSplitL "Hinterp_local_lws".
      iApply (last_write_interp_progress_non_write with "Hinterp_local_lws");first reflexivity.
      intro Hin. erewrite progress_to_node_mk_eid_ii in Hin;[|reflexivity].
      pose proof (AAConsistent.event_is_write_elem_of_mem_writes2 _ Hgraph_wf Hin) as [? [Hlk' HW]].
      rewrite Hgr_lk in Hlk'. inversion Hlk'. subst x. contradiction.
      iApply (po_pred_interp_skip with "Hinterp_po_src"). reflexivity.
    }
  Qed.

  Lemma reg_read {tid : Tid} {ts ctxt b reg val}:
    ThreadState.ts_reqs ts = AAInter.Next (AAInter.RegRead reg b) ctxt ->
    ts.(ts_regs) !! reg = Some (val : RegVal) ->
    ⊢
    SSWP (LThreadState.LTSNormal ts) @ tid {{ λ lts',
      (* update lts' accordingly *)
      ⌜lts' = LThreadState.LTSNormal ((incr_cntr ts) <| ts_reqs := (ctxt (val.(reg_val))) |>) ⌝
    }}.
  Proof.
    iIntros (Hreqs Hreg).
    rewrite sswp_eq /sswp_def /=.
    iIntros (????) "H". iNamed "H".
    inversion Hat_prog as [Hpg]. clear Hat_prog.
    case_bool_decide as Hv.
    2:{
      rewrite (LThreadStep.step_progress_valid_is_reqs_nonempty _ _ _ ts) in Hv; [|reflexivity|eassumption].
      rewrite Hreqs /EmptyInterp /= in Hv. exfalso. apply Hv. congruence.
    }
    iIntros (?). iNamed 1.

    (* Hstep gives that a reg-write event is happening *)
    inversion_step Hstep.

    set (eid := (mk_eid_ii ts tid)).

    (* update na *)
    iNamed "Hinterp_annot". iDestruct "Hannot_at_prog" as "#Hannot_at_prog".
    iMod (annot_alloc na (get_progress ts) tid gs emp%I with "[$Hinterp_annot $Hannot_at_prog //]") as "(Hinterp_annot & _)".
    iMod (token_alloc with "[$Hinterp_token $Hannot_at_prog //]") as "(Hinterp_token & _)".

    iExists emp%I, ∅, ∅, ls.
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
    iSplitL "Hinterp_local".
    {
      iNamed "Hinterp_local". iSplitL "Hinterp_local_lws".
      iApply (last_write_interp_progress_non_write with "Hinterp_local_lws"). reflexivity.
      intro Hin. erewrite progress_to_node_mk_eid_ii in Hin;[|reflexivity].
      pose proof (AAConsistent.event_is_write_elem_of_mem_writes2 _ Hgraph_wf Hin) as [? [Hlk' HW]].
      rewrite Hgr_lk in Hlk'. inversion Hlk'. subst x. contradiction.
      iApply (po_pred_interp_skip with "Hinterp_po_src"). reflexivity.
    }

    destruct H4 as [? [Hlk <-]]. rewrite Hreg in Hlk. inversion Hlk. clear;done.
  Qed.

End rules.
