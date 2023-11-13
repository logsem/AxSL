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

(* This file contains an application of adequacy theorem on the [data_data1] example *)
From iris.proofmode Require Import tactics.

From self.low Require Import adequacy.
From self.middle Require Import weakestpre.

From self.lang Require Import mm opsem.
From self.examples.lb Require Import data_data1.

Require Import ISASem.SailArmInstTypes.

Lemma progress_zero_is_init gr tid:
  ThreadState.progress_is_init gr tid (0%nat, 0%nat).
Proof.
  intros ??. destruct (ThreadState.progress_of_node x).
  destruct n. right;simpl;lia. left;simpl;lia.
Qed.

Section adequacy.
  Context (g : Graph.t).

  Definition global_state :=
    GlobalState.make g
    {[
      (BV 64 0x1000) := read "r1" addr_x;
      (BV 64 0x1004) := write "r1" addr_y;
      (BV 64 0x2000) := read "r2" addr_y;
      (BV 64 0x2004) := write "r2" addr_x
    ]}.

  Notation ts1 := (ThreadState.mk_ts
           {["pc" := mk_regval (BV 64 0x1000) ∅; "r1" := mk_regval (BV 64 0) ∅]}
           instrs.EmptyInterp).

  Notation ts2 := (ThreadState.mk_ts
           {["pc" := mk_regval (BV 64 0x2000) ∅; "r2" := mk_regval (BV 64 0) ∅]}
           instrs.EmptyInterp).

  Definition lts :=
    [LThreadState.LTSNormal ts1 ; LThreadState.LTSNormal ts2].

  Definition Φs :=
    [
      (λ lts, ∃ ts, lts = LThreadState.LTSDone ts ∧ ∃ rv, ts.(ThreadState.ts_regs)!! "r1" = Some rv ∧ rv.(reg_val) = (BV 64 0))
      ;
      (λ lts, ∃ ts, lts = LThreadState.LTSDone ts ∧ ∃ rv, ts.(ThreadState.ts_regs)!! "r2" = Some rv ∧ rv.(reg_val) = (BV 64 0))
    ].

  Lemma application `{CMRA Σ} `{!invGpreS Σ} `{!base.AABaseInG} `{!instantiation.AAThreadInG} lts':
    AAConsistent.t g ->
    AACandExec.NMSWF.wf g ->
    S (length lts) = AACandExec.Candidate.num_of_thd g ->
    (length lts = length lts'
     ∧ ∀ idx σ σ', lts !! idx = Some σ → lts' !! idx = Some σ' → (∃ n, nsteps (LThreadStep.t global_state (idx_to_tid idx)) (S n) σ σ')) ->
    (∀ (k:nat) σ, lts' !! k = Some σ → Terminated σ) ->
    (forall (idx: nat) σ' (Φ: _ -> Prop), lts' !! idx = Some σ' → Φs !! idx = Some Φ → Φ σ').
  Proof.
    intros Hcons Hwf Hnum Htsteps Hterm.
    apply (adequacy_pure global_state lts lts' Φs Hcons Hwf Hnum Htsteps).
    {
      intros ?? Hlk. eexists. split;eauto. simpl. destruct idx;simpl in Hlk.
      { inversion Hlk;subst. rewrite /ThreadState.mk_ts /ThreadState.get_progress /=. apply progress_zero_is_init. }
      { apply list_lookup_singleton_Some in Hlk. destruct Hlk as [-> <-].
        rewrite /ThreadState.mk_ts /ThreadState.get_progress /=. apply progress_zero_is_init. }
    }
    { done. }
    {
      intros.
      (* allocate all resources *)
      iMod (instantiation.interp_alloc global_state) as "(%Hbase & ?&#Hgs &#Hgr&#Hinst)".
      iDestruct (instantiation.my_local_interp_alloc global_state (0,0)%nat (Pos.of_nat 1) {[addr_x;addr_y]} with "Hgr") as ">[%Htgl1 Hinterp_ll1]".
      { apply progress_zero_is_init. }
      iDestruct (instantiation.my_local_interp_alloc global_state (0,0)%nat (Pos.of_nat 2) {[addr_x;addr_y]} with "Hgr") as ">[%Htgl2 Hinterp_ll2]".
      { apply progress_zero_is_init. }
      pose (instantiation.GenAALThreadG Σ H _) as HaathreadG.

      iDestruct (@instantiation.thread_local_interp_alloc Σ H HaathreadG Htgl1 ts1) as ">[%Htgn1 Hinterp_tl1]".
      { eexists. simpl. simplify_map_eq /=. done. }
      iDestruct (@instantiation.thread_local_interp_alloc Σ H HaathreadG Htgl2 ts2) as ">[%Htgn2 Hinterp_tl2]".
      { eexists. simpl. simplify_map_eq /=. done. }

      iModIntro.
      pose (instantiation.Build_AAIrisG Σ _ Hinv Hbase) as HaairisG.
      pose (@instantiation.instantiation_irisG Σ _ Hinv Hbase HaairisG) as HirisG.
      pose ((@instantiation.user_prot_to_prot Σ _ Hbase data_data1.protocol)) as Hprot.
      iExists HirisG, Hprot.
      iFrame. iFrame "Hgs".
      iSplitR.
      { (* show the protocol holds on initials *)
        iApply big_sepS_forall.
        iIntros (e Hin). iModIntro. iIntros (ks kv a v) "Hinit". simpl.
        case_bool_decide; simpl. rewrite /lb_prot.
        iDestruct (instantiation.graph_event_agree with "Hgs Hinit") as "%Hinit".
        iPureIntro. rewrite /event.Event.event_interp in Hinit. destruct Hinit as (? &?&?).
        set_unfold in Hin. destruct Hin as [Hvalid Hzero].
        feed pose proof (Graph.init_zero g e Hwf Hzero v) as Heq.
        repeat eexists. eauto. eauto. rewrite Heq //.
        case_bool_decide; simpl. rewrite /lb_prot.
        iDestruct (instantiation.graph_event_agree with "Hgs Hinit") as "%Hinit".
        iPureIntro. rewrite /event.Event.event_interp in Hinit. destruct Hinit as (? &?&?).
        set_unfold in Hin. destruct Hin as [Hvalid Hzero].
        feed pose proof (Graph.init_zero g e Hwf Hzero v) as Heq.
        repeat eexists. eassumption. eassumption. rewrite Heq //.
        auto.
      }
      iSplitL "Hinterp_ll1 Hinterp_tl1".
      { (* instantiate WP1 *)
        pose (@instantiation.instantiation_irisGL Σ H Hinv Hbase HaairisG Htgl1) as HirisGL.
        iExists HirisGL, _.
        simpl. rewrite /ThreadState.get_progress /= /idx_to_tid.
        iDestruct "Hinterp_ll1" as "[$ [Hlocs Hpo]]".
        iDestruct "Hinterp_tl1" as "(Hinterp_thd & Hregs & Hctrl & Hrmw)".
        iApply (@wp_strong_mono Σ H Hinv HirisG HirisGL Hprot (Pos.of_nat 1) (LThreadState.LTSNormal ts1) _
                               (λ σ', ⌜∃ ts : ThreadState.t,
                            σ' = LThreadState.LTSDone ts
                            ∧ (∃ rv : RegVal, ThreadState.ts_regs ts !! "r1" = Some rv ∧ reg_val rv = BV 64 0)⌝)%I

                 with "[-] []").
        rewrite /instrs.RNPC. rewrite delete_insert //.
        rewrite big_sepM_singleton. rewrite big_sepS_union.
        2:{ assert (addr_x ≠ addr_y) as Hneq. bitvector_tactics.bv_solve. set_solver + Hneq. }

        rewrite 2!big_sepS_singleton. iDestruct "Hlocs" as "[Hx Hy]".

        iDestruct (@write_reg_thread_1 Σ H Hinv Hbase HaairisG HaathreadG Htgl1 Htgn1 with "Hpo Hctrl Hrmw [Hregs] Hx Hy []") as "WP".
        { iExists _. done. }
        { rewrite /instrs instantiation.instr_eq /instantiation.instr_def.
          repeat (iSplit;first (iExists _;iFrame "Hinst";done)).
          iExists _;iFrame "Hinst";done.
        }
        rewrite wpi_eq /wpi_def.
        iDestruct ("WP" with "[] Hinterp_thd") as "WP".
        {
          simpl. iPureIntro;split. done.
          simplify_map_eq /=. done.
        }
        iExact "WP".
        iIntros (?) "Hpost".
        rewrite /to_lts_Phi /=.
        destruct k; iDestruct "Hpost" as "(Hinterp&(% &%&%Hinv'&[% [Hr1 %]]))";inversion Hinv';subst.
        iNamed "Hinterp".
        iDestruct (instantiation.reg_interp_agree with "Hinterp_reg Hr1") as %Hr1.
        iModIntro. iPureIntro.
        exists ts. split;auto. eexists. split;eauto.
      }
      { (* instantiate WP2 *)
        simpl. iSplitL;last done.
        pose (@instantiation.instantiation_irisGL Σ H Hinv Hbase HaairisG Htgl2) as HirisGL.
        iExists HirisGL, _.
        simpl. rewrite /ThreadState.get_progress /= /idx_to_tid.
        iDestruct "Hinterp_ll2" as "[$ [Hlocs Hpo]]".
        iDestruct "Hinterp_tl2" as "(Hinterp_thd & Hregs & Hctrl & Hrmw)".
        iApply (@wp_strong_mono Σ H Hinv HirisG HirisGL Hprot (Pos.of_nat 2) (LThreadState.LTSNormal ts2) _
                               (λ σ', ⌜∃ ts : ThreadState.t,
                            σ' = LThreadState.LTSDone ts
                            ∧ (∃ rv : RegVal, ThreadState.ts_regs ts !! "r2" = Some rv ∧ reg_val rv = BV 64 0)⌝)%I

                 with "[-] []").
        rewrite /instrs.RNPC. rewrite delete_insert //.
        rewrite big_sepM_singleton. rewrite big_sepS_union.
        2:{ assert (addr_x ≠ addr_y) as Hneq. bitvector_tactics.bv_solve. set_solver + Hneq. }

        rewrite 2!big_sepS_singleton. iDestruct "Hlocs" as "[Hx Hy]".

        iDestruct (@write_reg_thread_2 Σ H Hinv Hbase HaairisG HaathreadG Htgl2 Htgn2 with "Hpo Hctrl Hrmw [Hregs] Hx Hy []") as "WP".
        { iExists _. done. }
        { rewrite /instrs instantiation.instr_eq /instantiation.instr_def.
          repeat (iSplit;first (iExists _;iFrame "Hinst";done)).
          iExists _;iFrame "Hinst";done.
        }
        rewrite wpi_eq /wpi_def.
        iDestruct ("WP" with "[] Hinterp_thd") as "WP".
        {
          simpl. iPureIntro;split. done.
          simplify_map_eq /=. done.
        }
        iExact "WP".
        iIntros (?) "Hpost".
        rewrite /to_lts_Phi /=.
        destruct k; iDestruct "Hpost" as "(Hinterp&(% &%&%Hinv'&[% [Hr1 %]]))";inversion Hinv';subst.
        iNamed "Hinterp".
        iDestruct (instantiation.reg_interp_agree with "Hinterp_reg Hr1") as %Hr1.
        iModIntro. iPureIntro.
        exists ts. split;auto. eexists. split;eauto.
      }
    }
  Qed.

End adequacy.
