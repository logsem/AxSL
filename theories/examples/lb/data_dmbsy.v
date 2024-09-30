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

From stdpp.bitvector Require Import definitions tactics.

From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.

From self.mid Require Import rules specialised_rules.
Require Import ISASem.SailArmInstTypes.

Import uPred.

Definition data := (BV 64 1).
Definition addr_x := (BV 64 0x11).
Definition addr_y := (BV 64 0x10).

Notation read reg addr := (ILoad AS_normal AV_plain reg (AEval addr)).
Notation write reg addr := (IStore AS_normal AV_plain "r0" (AEreg reg) (AEval addr)).
Notation write_val addr := (IStore AS_normal AV_plain "r1" (AEval data) (AEval addr)).
Notation dmb_sy := (IDmb AAArch.Sy).

(* the token ghost state *)
Class LbInPreG `{CMRA Σ} := {
    LbDatasOneShot :: inG Σ (csumR (exclO unitO)
                             (agreeR (leibnizO Val)));
  }.

Class LbInG `{CMRA Σ} := {
    LbIn :: LbInPreG;
    LbOneShotN : gname;
  }.

#[global] Arguments LbOneShotN {Σ _ _}.

Definition LbΣ : gFunctors :=
  #[ GFunctor (csumR (exclO unitO)
                             (agreeR (leibnizO Val)))].

#[global] Instance subG_LbInPreG `{CMRA Σ}: subG LbΣ Σ -> LbInPreG.
Proof. solve_inG. Qed.

Section one_shot.
  Context `{CMRA Σ} `{!LbInG}.

  Definition pending := own LbOneShotN (Cinl (Excl ())).

  Definition shot v := own LbOneShotN (Cinr (to_agree v)).

  Lemma pending_shot v: pending -∗ shot v -∗ False.
  Proof.
    rewrite /pending /shot. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as "Hvalid".
    rewrite csum_validI //=.
  Qed.

  Lemma shoot v: pending ==∗ shot v.
  Proof.
    rewrite /pending /shot. iIntros "H".
    iApply (own_update with "H").
    apply cmra_update_exclusive.
    rewrite Cinr_valid. done.
  Qed.

  #[global] Instance shot_persist v: Persistent (shot v).
  Proof.
    rewrite /shot. apply _.
  Qed.

End one_shot.

Section write_val.
  Context `{AAIrisG} `{!AAThreadG} `{ThreadGN}.
  Context `{!LbInG}.

  (* for this thin-air version we can only show that the outcome must be [00] *)
  Definition instrs_val : iProp Σ :=
    (BV 64 0x1000) ↦ᵢ read "r1" addr_x ∗
    (BV 64 0x1004) ↦ᵢ dmb_sy ∗
    (BV 64 0x1008) ↦ᵢ write_val addr_y ∗
    (BV 64 0x100C) ↦ᵢ - ∗
    (BV 64 0x2000) ↦ᵢ read "r2" addr_y ∗
    (BV 64 0x2004) ↦ᵢ write "r2" addr_x ∗
    (BV 64 0x2008) ↦ᵢ -.

  Definition lb_prot (v : Val) (e: Eid) : iProp Σ :=
    ⌜v = bv_0 _⌝ ∨ (⌜ v = data ⌝ ∗ shot v).

  Definition write_val_thread_1 tid :
    None -{LPo}> -∗
    ∅ -{Ctrl}> -∗
    None -{Rmw}> -∗
    pending -∗
    (∃ rv, "r1" ↦ᵣ rv) -∗
    last_local_write tid addr_x None -∗
    last_local_write tid addr_y None -∗
    Prot[ addr_x, (1/2)%Qp | lb_prot ] -∗
    Prot[ addr_y, (1/2)%Qp | lb_prot ] -∗
    instrs_val -∗
    WPi (LTSI.Normal, (BV 64 0x1000)) @ tid
      {{ λ lts',
           ⌜lts' = (LTSI.Done, (BV 64 0x100C))⌝ ∗
           ∃ rv, "r1" ↦ᵣ rv ∗ ⌜rv.(reg_val) = bv_0 _⌝
      }}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hrmw Hpending [% Hreg] Hlocalw_x Hlocalw_y Hprot_x Hprot_y Hinstrs".
    iDestruct "Hinstrs" as "(#? & #? & #? & #? & _)".
    iApply sswpi_wpi. iApply (sswpi_mono with "[Hpo_src Hctrl_src Hlocalw_x Hprot_x Hrmw Hreg Hpending]").
    {
      iApply (iload_pln (λ _ v, ⌜v = bv_0 _⌝ ∗  (⌜v = bv_0 _⌝ ∗ pending))%I ∅ ∅ with "[-Hpending Hprot_x] [Hpending Hprot_x]").
      iFrame "#∗". rewrite big_sepS_empty big_sepM_empty //.

      iIntros (?). iSplitR.
      iIntros "_ _". done.
      iExists _,_,_. iSplitL. iIntros "_";iFrame. iExact "Hpending".
      iIntros (??) "_ _ _ _ _ _ Hpending [#H1|#[H2 Hshot]]".
      iFrame "Hpending". by iFrame "H1".
      iExFalso. iApply (pending_shot with "Hpending Hshot").
    }
    iIntros (?) "(-> &(%&%&%&(#Hwrite&%&Hreg&Hna&_&Hrfe&Hlpo&_&Hctrl&Hrmw&_)))".
    assert (G: ((BV 64 4096) `+Z` 4 = (BV 64 4100))%bv); [bv_solve|]. rewrite G.
    iDestruct (annot_split_iupd with "Hna") as ">[Hna1 Hna2]".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hlpo]").
    {
      iApply idmb;eauto.
    }
    iIntros (?) "(-> & %& #Hdmb & #Hpo & Hlpo)".
    subst. clear G. assert (G: ((BV 64 4100) `+Z` 4 = (BV 64 4104))%bv); [bv_solve|]. rewrite G.

    iDestruct (lpo_to_po with "Hlpo") as "[Hlpo #Hpo']".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hlocalw_y Hprot_y Hwrite Hlpo Hctrl Hna2]").
    {
      iApply (istore_pln (λ _, emp)%I {[eid0]} {[eid := _]} with "[Hlpo Hctrl Hlocalw_y Hna2]"). iFrame "#∗".
      rewrite big_sepS_singleton. rewrite big_sepM_singleton. iFrame "# Hna2".
      iExists _,_,_. iSplitL. iFrame. rewrite big_sepM_singleton. iIntros "HH";iExact "HH".
      iIntros (eid'').
      iSplitR.
      - iIntros "HE Hpo'' _". rewrite big_sepS_singleton. rewrite big_sepM_singleton /=.
        iApply (po_dmbsy_po_is_lob with "Hpo [Hdmb] Hpo''").
        { iDestruct (event_node with "Hdmb") as "$". }
      - iIntros "#Hwrite' % #Hpo''' Hp P".
        iDestruct "P" as "[% Hpending]".
        iDestruct (shoot data with "Hpending") as ">#Hshot".
        iModIntro. iSplitR;first done. iRight. iFrame "Hshot". done.
    }
    iIntros (?) "(->& (% &?&?&?&?&?&?&?))".
    subst. clear G. assert (G: ((BV 64 4104) `+Z` 4 = (BV 64 4108))%bv); [bv_solve|]. rewrite G.

    iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 4108)⌝)%I).
    { by iApply idone. }
    iIntros (? ->). iApply wpi_terminated.
    iApply (inst_post_lifting_lifting _ _ _ {[eid:= ⌜v = bv_0 _⌝%I]} with "[Hna1]").
    rewrite dom_singleton_L set_Forall_singleton //.
    rewrite big_sepM_singleton //.
    rewrite big_sepM_singleton //. iIntros. iModIntro.
    iSplit;first done. iExists _. iFrame. simpl. done.
  Qed.

  Definition write_val_thread_2 tid :
    None -{LPo}> -∗
    ∅ -{Ctrl}> -∗
    None -{Rmw}> -∗
    (∃ rv, "r2" ↦ᵣ rv) -∗
    last_local_write tid addr_x None -∗
    last_local_write tid addr_y None -∗
    Prot[ addr_x, (1/2)%Qp | lb_prot ] -∗
    Prot[ addr_y, (1/2)%Qp | lb_prot ] -∗
    instrs_val -∗
    WPi (LTSI.Normal, (BV 64 0x2000)) @ tid
      {{ λ lts',
           ⌜lts' = (LTSI.Done, (BV 64 0x2008))⌝ ∗
           ∃ rv, "r2" ↦ᵣ rv ∗ ⌜rv.(reg_val) = bv_0 _ ∨ rv.(reg_val) = data ⌝
      }}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hrmw [% Hreg] Hlocalw_x Hlocalw_y Hprot_x Hprot_y Hinstrs".
    iDestruct "Hinstrs" as "(_ & _ & _ & _ & #? & #? & #?)".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hpo_src Hctrl_src Hlocalw_y Hprot_y Hrmw Hreg]").
    {
      iApply (iload_pln (λ e v, lb_prot v e ∗ lb_prot v e)%I ∅ ∅ with "[- Hprot_y] [Hprot_y]").
      iFrame "#∗". rewrite big_sepM_empty big_sepS_empty //.

      iIntros (?). iSplitR.
      - iIntros "_ _". done.
      - iExists _,_,emp%I.
        iSplitL. iIntros "_". iFrame.
        iIntros (??) "_ _ _ _ _ _ _ #?". by iFrame "#".
    }
    iIntros (?) "(->&(%&%&%&(#Hwrite&%&Hreg&Hna&_&Hrfe&Hpo&_&Hctrl&Hrmw&_)))".
    assert (G: ((BV 64 8192) `+Z` 4 = (BV 64 8196))%bv); [bv_solve|]. rewrite G.
    iDestruct (annot_split_iupd with "Hna") as ">[Hna1 Hna2]".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hlocalw_x Hprot_x Hwrite Hpo Hctrl Hreg Hna1]").
    {
      iApply istore_pln_single_data. iFrame "#∗".
      iExists _. iSplitR. iIntros "HH";iExact "HH".
      iIntros (eid'') "#Hwrite' _ #Hpo #Hdata ? #Hprot".
      iFrame. unfold lb_prot. iFrame "#".
    }
    iIntros (?) "(->&[? (%&?&?&?&?)])".
    clear G. assert (G: ((BV 64 8196) `+Z` 4 = (BV 64 8200))%bv); [bv_solve|]. rewrite G.

    iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 8200)⌝)%I).
    { by iApply idone. }
    iIntros (? ->). iApply wpi_terminated.
    iApply (inst_post_lifting_lifting _ _ _ {[eid:= (lb_prot v eid')]} with "[Hna2]").
    rewrite dom_singleton_L set_Forall_singleton //.
    rewrite big_sepM_singleton //.
    rewrite big_sepM_singleton //. iIntros "#Hprot". iModIntro.
    iSplit;first done. iExists _. iFrame. simpl. iDestruct "Hprot" as "[#? | [#? _]]".
    iLeft. done. iRight. done.
  Qed.

End write_val.
