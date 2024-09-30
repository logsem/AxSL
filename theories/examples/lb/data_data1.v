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

From stdpp.bitvector Require Export definitions tactics.

From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.

From self.mid Require Import rules specialised_rules.
Require Import ISASem.SailArmInstTypes.

Import uPred.

Definition data := (BV 64 1).
Definition addr_x := (BV 64 0x11).
Definition addr_y := (BV 64 0x10).

Notation write reg addr := (IStore AS_normal AV_plain "r0" (AEreg reg) (AEval addr)).
Notation read reg addr := (ILoad AS_normal AV_plain reg (AEval addr)).

Ltac fold_continuation :=
    match goal with | |- context [AAInter.Next _ ?cont] => set(ctx:=cont) end.

Section write_reg.
  Context `{AAIrisG} `{!AAThreadG} `{ThreadGN}.

  (* for this thin-air version we can only show that the outcome must be [00] *)
  Definition instrs : iProp Σ :=
    (BV 64 0x1000) ↦ᵢ read "r1" addr_x ∗
    (BV 64 0x1004) ↦ᵢ write "r1" addr_y ∗
    (BV 64 0x1008) ↦ᵢ - ∗
    (BV 64 0x2000) ↦ᵢ read "r2" addr_y ∗
    (BV 64 0x2004) ↦ᵢ write "r2" addr_x ∗
    (BV 64 0x2008) ↦ᵢ -.

  Definition lb_prot (v : Val) (e: Eid) : iProp Σ :=
    ⌜v = BV 64 0⌝.

  Definition write_reg_thread_1 tid :
    None -{LPo}> -∗
    ∅ -{Ctrl}> -∗
    None -{Rmw}> -∗
    (∃ rv, "r1" ↦ᵣ rv) -∗
    last_local_write tid addr_x None -∗
    last_local_write tid addr_y None -∗
    Prot[ addr_x, (1/2)%Qp | lb_prot ] -∗
    Prot[ addr_y, (1/2)%Qp | lb_prot ] -∗
    instrs -∗
    WPi (LTSI.Normal, (BV 64 0x1000)) @ tid
      {{ λ lts',
           ⌜lts' = (LTSI.Done, (BV 64 0x1008))⌝ ∗
           ∃ rv, "r1" ↦ᵣ rv ∗ ⌜rv.(reg_val) = BV 64 0⌝
      }}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hrmw [% Hreg] Hlocalw_x Hlocalw_y Hprot_x Hprot_y Hinstrs".
    iDestruct "Hinstrs" as "(#? & #? & #? & _ & _)".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hpo_src Hctrl_src Hlocalw_x Hprot_x Hrmw Hreg]").
    {
      iApply (iload_pln (λ e v, lb_prot v e ∗ lb_prot v e)%I ∅ ∅ with "[-Hprot_x] [Hprot_x]").
      iFrame "#∗".  rewrite big_sepM_empty big_sepS_empty //.

      iIntros. iSplitR.
      - iIntros "_ _". rewrite big_sepM_empty //.
      - iExists _,_,emp%I. iSplitL.
        iIntros "_". iFrame.
        iIntros (??) "_ _ _ _ _ _ %". iPureIntro. done.
    }
    iIntros (?) "(->&(%&%&%&(#Hwrite&%&Hreg&Hna&_&Hrfe&Hpo&_&Hctrl&Hrmw&_)))".
    assert (G: ((BV 64 4096) `+Z` 4 = (BV 64 4100))%bv); [bv_solve|]. rewrite G.

    iDestruct (annot_split_iupd with "Hna") as ">[Hna1 Hna2]".
    iApply sswpi_wpi. iApply (sswpi_mono with "[Hlocalw_y Hprot_y Hwrite Hpo Hctrl Hrmw Hreg Hna1]").
    {
      iApply (istore_pln_single_data). iFrame "#∗".
      iExists (lb_prot v eid').
      iSplitR. iIntros "$".
      iIntros (eid'') "#Hwrite' _ #Hpo #Hdata Hp Hprot".
      iFrame.
    }
    iIntros (?) "(%&[? (%&?&?&?&?)])".
    subst. clear G. assert (G: ((BV 64 4100) `+Z` 4 = (BV 64 4104))%bv); [bv_solve|].
    rewrite G.

    iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 4104)⌝)%I).
    { by iApply idone. }
    iIntros (? ->). iApply wpi_terminated.
    iApply (inst_post_lifting_lifting _ _ _ {[eid:= (lb_prot v eid')]} with "[Hna2]").
    rewrite dom_singleton_L set_Forall_singleton //.
    rewrite big_sepM_singleton //.
    rewrite big_sepM_singleton //. iIntros. iModIntro.
    iSplit;first done. iExists _. iFrame. simpl. done.
  Qed.

  Definition write_reg_thread_2 tid :
    None -{LPo}> -∗
    ∅ -{Ctrl}> -∗
    None -{Rmw}> -∗
    (∃ rv, "r2" ↦ᵣ rv) -∗
    last_local_write tid addr_x None -∗
    last_local_write tid addr_y None -∗
    Prot[ addr_x, (1/2)%Qp | lb_prot ] -∗
    Prot[ addr_y, (1/2)%Qp | lb_prot ] -∗
    instrs -∗
    WPi (LTSI.Normal, (BV 64 0x2000)) @ tid
      {{ λ lts',
           ⌜lts' = (LTSI.Done, (BV 64 0x2008))⌝ ∗
           ∃ rv, "r2" ↦ᵣ rv ∗ ⌜rv.(reg_val) = BV 64 0⌝
      }}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hrmw [% Hreg] Hlocalw_x Hlocalw_y Hprot_x Hprot_y Hinstrs".
    iDestruct "Hinstrs" as "(_ & _ & _ & #? & #? & #?)".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hpo_src Hctrl_src Hlocalw_y Hprot_y Hrmw Hreg]").
    {
      iApply (iload_pln (λ e v, lb_prot v e ∗ lb_prot v e)%I ∅ ∅ with "[-Hprot_y] [Hprot_y]").
      iFrame "#∗".  rewrite big_sepM_empty big_sepS_empty //.

      iIntros. iSplitR.
      - iIntros "_ _". rewrite big_sepM_empty //.
      - iExists _,_,emp%I.
        iSplitL. iIntros "_";iFrame.
        iIntros (??) "_ _ _ _ _ _ %". iPureIntro. done.
    }
    iIntros (?) "(->&(%&%&%&(#Hwrite&%&Hreg&Hna&_&Hrfe&Hpo&_&Hctrl&Hrmw&_)))".
    assert (G: ((BV 64 8192) `+Z` 4 = (BV 64 8196))%bv); [bv_solve|]. rewrite G.
    iDestruct (annot_split_iupd with "Hna") as ">[Hna1 Hna2]".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hlocalw_x Hprot_x Hwrite Hpo Hctrl Hreg Hna1]").
    {
      iApply istore_pln_single_data. iFrame "#∗".
      iExists (lb_prot v eid'). iSplit. iIntros "$".
      iIntros (eid'') "#Hwrite' _ #Hpo #Hdata Hp Hprot".
      iFrame.
    }
    iIntros (?) "(%&[? (%&?&?&?&?)])".
    subst. clear G. assert (G: ((BV 64 8196) `+Z` 4 = (BV 64 8200))%bv); [bv_solve|]. rewrite G.

    iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 8200)⌝)%I).
    { by iApply idone. }
    iIntros (? ->). iApply wpi_terminated.
    iApply (inst_post_lifting_lifting _ _ _ {[eid:= (lb_prot v eid')]} with "[Hna2]").
    rewrite dom_singleton_L set_Forall_singleton //.
    rewrite big_sepM_singleton //.
    rewrite big_sepM_singleton //. iIntros. iModIntro.
    iSplit;first done. iExists _. iFrame. simpl. done.
  Qed.

End write_reg.
