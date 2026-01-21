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

(* This file contains an application of adequacy theorem on the [data_data1] example *)
From stdpp.bitvector Require Import definitions.
From iris.proofmode Require Import tactics.

From self.low Require Import adequacy.
From self.mid Require Import weakestpre.

From self.lang Require Import mm opsem.
From self.examples.lb Require Import data_data1.

Require Import ISASem.SailArmInstTypes.
Require Import SSCCommon.CDestruct.

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
    AACand.NMSWF.wf g ->
    S (length lts) = AACand.Candidate.num_of_thd g ->
    (∃ ns, length ns = length lts ∧ length lts = length lts'
     ∧ ∀ idx σ σ', lts !! idx = Some σ → lts' !! idx = Some σ' → (∃ n, ns !! idx = Some n ∧ nsteps (LThreadStep.t global_state (idx_to_tid idx)) (S n) σ σ')) ->
    (∀ (k:nat) σ, lts' !! k = Some σ → Terminated σ) ->
    (forall (idx: nat) σ' (Φ: _ -> Prop), lts' !! idx = Some σ' → Φs !! idx = Some Φ → Φ σ').
  Proof.
    intros Hcons Hwf Hnum [ns Htsteps] Hterm.
    apply (adequacy_pure global_state ns lts lts' Φs Hcons Hwf Hnum Htsteps).
    {
      intros ?? Hlk. eexists. split;[eauto|]. simpl. destruct idx;simpl in Hlk.
      { inversion Hlk;subst. rewrite /ThreadState.mk_ts /ThreadState.get_progress /=. apply progress_zero_is_init. }
      { apply list_lookup_singleton_Some in Hlk. destruct Hlk as [-> <-].
        rewrite /ThreadState.mk_ts /ThreadState.get_progress /=. apply progress_zero_is_init. }
    }
    { done. }
    {
      intros.
      (* allocate all resources *)
      iMod (instantiation.interp_alloc global_state {[addr_x := @lb_prot Σ; addr_y := @lb_prot Σ]}) as "(%Hbase & ?&#Hgs &#Hgr&#Hinst&Hprot&Hpt)".
      rewrite big_sepM_insert. rewrite big_sepM_singleton.
      iDestruct "Hpt" as "[Hpt1 Hpt2]".
      2:{ apply lookup_singleton_ne. clear. done. }

      iMod (prot_loc_persist with "Hpt1") as "#Hpt_x".
      iMod (prot_loc_persist with "Hpt2") as "#Hpt_y".

      iDestruct (instantiation_local.my_local_interp_alloc global_state (0,0)%nat (Pos.of_nat 1) {[addr_x;addr_y]} with "Hgr") as ">[%Htgl1 Hinterp_ll1]".
      { apply progress_zero_is_init. }
      iDestruct (instantiation_local.my_local_interp_alloc global_state (0,0)%nat (Pos.of_nat 2) {[addr_x;addr_y]} with "Hgr") as ">[%Htgl2 Hinterp_ll2]".
      { apply progress_zero_is_init. }
      pose (instantiation.GenAALThreadG Σ H _) as HaathreadG.

      iDestruct (@instantiation.thread_local_interp_alloc Σ H HaathreadG Htgl1 ts1) as ">[%Htgn1 Hinterp_tl1]".
      { eexists. simpl. clear;simplify_map_eq. reflexivity. }
      iDestruct (@instantiation.thread_local_interp_alloc Σ H HaathreadG Htgl2 ts2) as ">[%Htgn2 Hinterp_tl2]".
      { eexists. simpl. clear;simplify_map_eq. reflexivity. }

      iModIntro.
      pose (instantiation.Build_AAIrisG Σ _ Hinv Hbase) as HaairisG.
      pose (@instantiation.instantiation_irisG Σ _ Hinv Hbase HaairisG) as HirisG.
      pose ({[addr_x := @lb_prot Σ; addr_y := @lb_prot Σ]} : gmap Addr _) as Hprot.
      iExists HirisG, Hprot.
      iFrame. iFrame "Hgs".
      iSplitR.
      { (* show the protocol holds on initials. repetitive proof, but works *)
        iApply (big_sepS_mono (λ _, emp)%I);[|iApply big_sepS_emp;clear;done].
        iIntros (e Hin) "_".
        unfold prot_res.prot_res.

        assert (AACand.NMSWF.initial_wf g) as Hinit_wf by (rewrite /AACand.NMSWF.wf in Hwf;naive_solver).
        rewrite /AACand.NMSWF.initial_wf in Hinit_wf. destruct_and ? Hinit_wf.
        assert (e ∈ AACand.NMSWF.initial_writes g) as Hin_w.
        {
          rewrite -H5;set_solver + Hin.
        }
        apply H4 in Hin.
        rewrite /global_state /=.
        unfold AACand.Candidate.is_valid_init_mem_write in Hin.
        cdestruct Hin.
        set_unfold in Hin_w.
        cdestruct Hin_w.
        rewrite H10 /=.
        rewrite H10 in H6.
        cdestruct H6.
        assert (x0 = 8)%N as ->.
        {
          destruct (decide (x0 = 8)%N);first assumption.
          assert (AACand.NMSWF.size8_wf g) as Hsz_wf by (rewrite /AACand.NMSWF.wf in Hwf;naive_solver).
          rewrite /AACand.NMSWF.size8_wf in Hsz_wf.
          set_unfold in Hsz_wf.
          specialize (Hsz_wf e).
          exfalso.
          cdestruct Hsz_wf. apply Hsz_wf. eexists. split;[eassumption| simpl].
          destruct x0;[done|destruct p;[done| destruct p;[done| destruct p;[done| destruct p;[done|done|contradiction] |done] |done] |done]].
        }

        case_decide.
        2:{ clear - H11 H6. exfalso. naive_solver. }
        case_decide;last lia.
        simpl.
        destruct (Hprot !! AAInter.WriteReq.pa x1) eqn:HH;rewrite HH /=; last (clear;done).
          unfold Hprot in HH.
          assert (AAInter.WriteReq.pa x1 = addr_x ∨ AAInter.WriteReq.pa x1 = addr_y) as [Ha | Ha].
          { apply elem_of_dom_2 in HH. set_solver + HH. }
          all:
          rewrite Ha in HH;
          rewrite lookup_insert_Some in HH; destruct HH;
          try cdestruct H13;try contradiction;try subst u.
          {
            unfold lb_prot.
            iPureIntro.
            clear - H11.
            rewrite -Classical_Prop.Eq_rect_eq.eq_rect_eq.
            apply bv_eq.
            rewrite bvn_eq in H11. destruct H11.
            rewrite bv_unsigned_BV. bv_simplify_arith. done.
          }
          {
            rewrite lookup_insert in H14. inversion H14;subst u.
            unfold lb_prot.
            iPureIntro.
            clear - H11.
            rewrite -Classical_Prop.Eq_rect_eq.eq_rect_eq.
            apply bv_eq.
            rewrite bvn_eq in H11. destruct H11.
            rewrite bv_unsigned_BV. bv_simplify_arith. done.
          }
        }
      iSplitL "Hinterp_ll1 Hinterp_tl1".
      { (* instantiate WP1 *)
        pose (@instantiation_local.instantiation_irisGL Σ H Hbase Htgl1) as HirisGL.
        iExists HirisGL, _.
        simpl. rewrite /ThreadState.get_progress /= /idx_to_tid.
        iDestruct "Hinterp_ll1" as "[$ [Hlocs Hpo]]".
        iDestruct "Hinterp_tl1" as "(Hinterp_thd & Hregs & Hctrl & Hrmw)".
        iApply (@wp_strong_mono Σ H Hinv HirisG HirisGL (Pos.of_nat 1) (LThreadState.LTSNormal ts1) _
                               (λ σ', ⌜∃ ts : ThreadState.t,
                            σ' = LThreadState.LTSDone ts
                            ∧ (∃ rv : RegVal, ThreadState.ts_regs ts !! "r1" = Some rv ∧ reg_val rv = BV 64 0)⌝)%I

                 with "[-] []").
        rewrite /instrs.RNPC. rewrite delete_insert.
        rewrite big_sepM_singleton. rewrite big_sepS_union.
        2:{ assert (addr_x ≠ addr_y) as Hneq. bv_solve. set_solver + Hneq. }

        rewrite 2!big_sepS_singleton. iDestruct "Hlocs" as "[Hx Hy]".

        iDestruct (@write_reg_thread_1 Σ H Hinv Hbase HaairisG HaathreadG Htgl1 Htgn1 with "Hpo Hctrl Hrmw [Hregs] Hx Hy Hpt_x Hpt_y []") as "WP".
        { iExists _. iFrame. }
        { rewrite /instrs base.instr_eq /base.instr_def.
          repeat (iSplit;first (iExists _;iFrame "Hinst");clear;auto).
        }
        rewrite wpi_eq /wpi_def.
        iDestruct ("WP" with "[] Hinterp_thd") as "WP".
        {
          simpl. iPureIntro;split. clear;done.
          clear;simplify_map_eq. done.
        }
        iExact "WP".
        clear;done.
        iIntros (?) "Hpost".
        rewrite /to_lts_Phi /=.
        destruct k; iDestruct "Hpost" as "(Hinterp&(% &%&%Hinv'&[% [Hr1 %]]))";inversion Hinv';subst.
        iNamed "Hinterp".
        iDestruct (instantiation.reg_interp_agree with "Hinterp_reg Hr1") as %Hr1.
        iModIntro. iPureIntro.
        exists ts. split. reflexivity. eexists. split;eassumption.
      }
      { (* instantiate WP2 *)
        simpl. iSplitL;[|clear;done].
        pose (@instantiation_local.instantiation_irisGL Σ H Hbase Htgl2) as HirisGL.
        iExists HirisGL, _.
        simpl. rewrite /ThreadState.get_progress /= /idx_to_tid.
        iDestruct "Hinterp_ll2" as "[$ [Hlocs Hpo]]".
        iDestruct "Hinterp_tl2" as "(Hinterp_thd & Hregs & Hctrl & Hrmw)".
        iApply (@wp_strong_mono Σ H Hinv HirisG HirisGL (Pos.of_nat 2) (LThreadState.LTSNormal ts2) _
                               (λ σ', ⌜∃ ts : ThreadState.t,
                            σ' = LThreadState.LTSDone ts
                            ∧ (∃ rv : RegVal, ThreadState.ts_regs ts !! "r2" = Some rv ∧ reg_val rv = BV 64 0)⌝)%I

                 with "[-] []").
        rewrite /instrs.RNPC. rewrite delete_insert.
        rewrite big_sepM_singleton. rewrite big_sepS_union.
        2:{ assert (addr_x ≠ addr_y) as Hneq. bv_solve. set_solver + Hneq. }

        rewrite 2!big_sepS_singleton. iDestruct "Hlocs" as "[Hx Hy]".

        iDestruct (@write_reg_thread_2 Σ H Hinv Hbase HaairisG HaathreadG Htgl2 Htgn2 with "Hpo Hctrl Hrmw [Hregs] Hx Hy Hpt_x Hpt_y []") as "WP".
        { iExists _. iFrame. }
        { rewrite /instrs base.instr_eq /base.instr_def.
          repeat (iSplit;first (iExists _;iFrame "Hinst";clear;auto)).
          iExists _;iFrame "Hinst". iPureIntro;clear;done.
        }
        rewrite wpi_eq /wpi_def.
        iDestruct ("WP" with "[] Hinterp_thd") as "WP".
        {
          simpl. iPureIntro;split. clear;done.
          clear;simplify_map_eq /=. done.
        }
        iExact "WP".
        clear;done.
        iIntros (?) "Hpost".
        rewrite /to_lts_Phi /=.
        destruct k; iDestruct "Hpost" as "(Hinterp&(% &%&%Hinv'&[% [Hr1 %]]))";inversion Hinv';subst.
        iNamed "Hinterp".
        iDestruct (instantiation.reg_interp_agree with "Hinterp_reg Hr1") as %Hr1.
        iModIntro. iPureIntro.
        exists ts. split. reflexivity. eexists. split;eassumption.
      }
    }
  Qed.

End adequacy.
