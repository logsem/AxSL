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

(* This file contains the low-level proof rules for auxiliary operations *)
From self.low.rules Require Import prelude.

Import uPred.

Section rules.
  Context `{AAIrisG} `{Htg: !ThreadGNL}.

  Import ThreadState.

  Lemma reload {tid : Tid} {ts instr val}:
    ThreadState.ts_reqs ts = EmptyInterp ->
    ts.(ts_regs) !! RNPC = Some (val : RegVal) ->
    {SS{{
           (val.(reg_val)) ↦ᵢ instr
    }}}
    (LThreadState.LTSNormal ts) @ tid
    {{{ RET (LThreadState.LTSNormal ((reset_cntr ts) <| ts_reqs := (InstrInterp instr) |>));
        True
    }}}.
  Proof.
    iIntros (Hreqs Hreg).
    iIntros (Φ) "Hinstr HΦ".
    rewrite sswp_eq /sswp_def /=.
    iIntros (????) "H". iNamed "H".
    inversion Hat_prog as [Hpg]. clear Hat_prog.
    case_bool_decide as Hv.
    {
      rewrite (LThreadStep.step_progress_valid_is_reqs_nonempty _ _ _ ts) in Hv;[|done|done].
      contradiction.
    }

    iDestruct (instr_agree_Some with "Hinterp_global Hinstr") as %Hinstr_lk.
    (* Hstep gives that a reload/terminating event is happening *)
    inversion_step Hstep.
    2:{ (* not terminating *) rewrite Hreg in H3. inversion H3. subst val. rewrite Hinstr_lk in H4. inversion H4. }
    rewrite Hreg in H4. inversion H4. subst val. rewrite Hinstr_lk in H5. inversion H5.
    iIntros (?) "$".
    iModIntro. iNext. iModIntro.
    iSplitL "Hinterp_local".
    { iNamed "Hinterp_local". iSplitL "Hinterp_local_lws".
      iApply (last_write_interp_progress_non_write' with "Hinterp_local_lws");first reflexivity.
      assumption.
      iApply (po_pred_interp_skip' with "Hinterp_po_src"). reflexivity.
    }
    iApply "HΦ". done.
  Qed.

  Lemma terminate {tid : Tid} {ts val}:
    ThreadState.ts_reqs ts = EmptyInterp ->
    ts.(ts_regs) !! RNPC = Some (val : RegVal) ->
    {SS{{
           (val.(reg_val)) ↦ᵢ -
    }}}
    (LThreadState.LTSNormal ts) @ tid
    {{{ RET LThreadState.LTSDone ts;
        True
    }}}.
  Proof.
    iIntros (Hreqs Hreg).
    iIntros (Φ) "Hinstr HΦ".
    rewrite sswp_eq /sswp_def /=.
    iIntros (????) "H". iNamed "H".
    inversion Hat_prog as [Hpg]. clear Hat_prog.
    case_bool_decide as Hv.
    {
      rewrite (LThreadStep.step_progress_valid_is_reqs_nonempty _ _ _ ts) in Hv;[|done|done].
      contradiction.
    }

    iDestruct (instr_agree_None with "Hinterp_global Hinstr") as %Hinstr_lk.

    (* Hstep gives that a reload/terminating event is happening *)
    inversion_step Hstep.
    { (* not reload *) rewrite Hreg in H4. inversion H4. subst val. rewrite Hinstr_lk in H5. inversion H5. }
    iIntros (?) "$".
    iModIntro. iNext. iModIntro. iSplitL "Hinterp_local". iFrame.
    iApply "HΦ". done.
  Qed.

End rules.
