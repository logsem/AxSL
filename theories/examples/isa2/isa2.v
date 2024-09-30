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

From self.low Require Export instantiation.
From self.mid Require Import rules specialised_rules.
Require Import ISASem.SailArmInstTypes.

Import uPred.

Definition data := (BV 64 0x10).
Definition flag1 := (BV 64 0x18).
Definition flag2 := (BV 64 0x20).

Definition data_write : Instruction := 
  (IStore AS_normal AV_plain "r0" (AEval (BV 64 42)) (AEval data)).
Definition flag1_write : Instruction :=
  (IStore AS_rel_or_acq AV_plain "r0" (AEval (BV 64 1)) (AEval flag1)).

Definition flag1_read kind :=
  (ILoad kind AV_plain "r1" (AEval flag1)).
Definition flag2_write :=
  (IStore AS_normal AV_plain "r0" (AEreg "r1") (AEval flag2)).

Definition flag2_read kind :=
  (ILoad kind AV_plain "r1" (AEval flag2)).
Definition data_read :=
  (ILoad AS_normal AV_plain "r2" (AEval data)).

Section proof.
  Context `{AAIrisG}.

  Context (tid1 tid2 tid3 : Tid).
  Context (Htid_ne12 : tid1 ≠ tid2).
  Context (Htid_ne13 : tid1 ≠ tid3).
  Context (Htid_ne23 : tid2 ≠ tid3).

  Definition data_prot (v : Val) (e : Eid) : iProp Σ :=
    (⌜v = (BV 64 42)⌝ ∗ ⌜EID.tid e = tid1⌝) ∨ ⌜EID.tid e = 0%nat⌝.

  Definition t1_prop w_data w_flag : iProp Σ :=
    ⌜EID.tid w_data = tid1⌝ ∗ ⌜EID.tid w_flag = tid1⌝ ∗
    w_data -{Edge.Po}> w_flag ∗
    w_data -{E}> (Event.W AS_normal AV_plain data (BV 64 42)) ∗
    w_flag -{E}> (Event.W AS_rel_or_acq AV_plain flag1 (BV 64 1)).

  Definition flag1_prot (v : Val) (e : Eid) : iProp Σ :=
    ⌜EID.tid e = 0%nat⌝ ∨ ∃ d, t1_prop d e.

  (* Need to constrain both thread 2 events to tid2 *)
  Definition t2_prop w_data w_flag1 r_flag1 w_flag2 : iProp Σ :=
    t1_prop w_data w_flag1 ∗
    ⌜EID.tid r_flag1 = tid2⌝ ∗ ⌜EID.tid w_flag2 = tid2⌝ ∗
    w_flag1 -{Edge.Rf}> r_flag1 ∗
    r_flag1 -{Edge.Data}> w_flag2 ∗
    w_flag2 -{E}> (Event.W AS_normal AV_plain flag2 (BV 64 1)). 

  Definition flag2_prot (v : Val) (e : Eid) : iProp Σ :=
    ⌜EID.tid e = 0%nat⌝ ∨
    ⌜ v = (BV 64 0) ⌝ ∨
    ∃ wd wf1 rf1,
      t2_prop wd wf1 rf1 e.
      
  Definition t1_instrs : iProp Σ :=
    (BV 64 0x1000 ↦ᵢ data_write) ∗
    (BV 64 0x1004 ↦ᵢ flag1_write) ∗
    (BV 64 0x1008 ↦ᵢ -).

  Definition t2_instrs : iProp Σ :=
    (BV 64 0x2000 ↦ᵢ flag1_read AS_normal) ∗
    (BV 64 0x2004 ↦ᵢ flag2_write) ∗
    (BV 64 0x2008 ↦ᵢ -).

  Definition t3_instrs : iProp Σ :=
    (BV 64 0x3000 ↦ᵢ flag2_read AS_rel_or_acq) ∗
    (BV 64 0x3004 ↦ᵢ data_read) ∗
    (BV 64 0x3008 ↦ᵢ -).

  (* Definition protocol : UserProt := *)
  (*   Build_UserProt _ _ (λ a v e, *)
  (*                        if bool_decide (a = data) then data_prot v e *)
  (*                        else if bool_decide (a = flag1) then flag1_prot e *)
  (*                        else if bool_decide (a = flag2) then flag2_prot v e *)
  (*                        else (⌜EID.tid e = 0%nat⌝))%I. *)

  Context `{!AAThreadG} `{ThreadGN}.

  Lemma t1 ctrl:
    None -{LPo}> -∗
    ctrl -{Ctrl}> -∗
    last_local_write tid1 data None -∗
    last_local_write tid1 flag1 None -∗
    Prot[ data , (1/2)%Qp | data_prot ] -∗
    Prot[ flag1 , (1/2)%Qp | flag1_prot ] -∗
    t1_instrs -∗
    WPi (LTSI.Normal, (BV 64 0x1000)) @ tid1 {{ λ lts', ⌜lts' = (LTSI.Done, (BV 64 0x1008)) ⌝}}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hlocalw_data Hlocalw_flag Hprot_data Hprot_flag Hinstrs".
    iDestruct "Hinstrs" as "(#? & #? & #?)".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hpo_src Hctrl_src Hlocalw_data Hprot_data]").
    {
      iApply (istore_pln (λ _, emp)%I ∅ ∅ with "[Hpo_src Hctrl_src Hlocalw_data]"). iFrame "#∗".
      { rewrite big_sepS_empty big_sepM_empty //. }

      iExists _,_,emp%I. iSplitL. iIntros "_";iFrame.
      iIntros (?). iSplitL.
      - by iIntros "_ _ _".
      - iIntros "#HE % #Hpo _ _". iModIntro. iSplit; [done|]. simpl. unfold data_prot. by iLeft.
    }

    iIntros (?) "(-> & [% (#Hwrite & %Htid1 & Hpo & _ & Hlocalw_data & Hctrl & HeidP)])".
    assert (G: ((BV 64 4096) `+Z` 4 = (BV 64 4100))%bv) by bv_solve. rewrite G. clear G.

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hlocalw_flag Hprot_flag Hwrite Hpo Hctrl HeidP]").
    {
      iDestruct (lpo_to_po with "Hpo") as "[Hlpo #Hpo]".
      iApply (istore_rel emp {[eid := emp%I]}). iFrame "#∗".

      iSplit; [by rewrite big_sepM_singleton|].
      iSplitL; [by rewrite big_sepM_singleton|].

      iExists emp%I. iSplitL. iIntros "_";iFrame. done.
      iIntros (eid') "#Hfwrite %Htid1' #Hpo' HeidP' _".
      iModIntro. iSplit; [done|].

      simpl. unfold flag1_prot.
      iRight. iExists eid. unfold t1_prop. iFrame "#%".
      by iEval (rewrite big_sepM_singleton) in "Hpo'".
    }
    iIntros (?) "(-> & [%  (? & ? & ?)])".
    assert (G: ((BV 64 4100) `+Z` 4 = (BV 64 4104))%bv); [bv_solve|]. rewrite G. clear G.

    iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 4104)⌝)%I).
    {
      by iApply idone.
    }
    iIntros (? ->). iApply wpi_terminated. iApply (inst_post_lifting_lifting _ _ _ ∅); auto.
    rewrite dom_empty_L //.
  Qed.

  Lemma t2 ctrl:
    None -{LPo}> -∗
    ctrl -{Ctrl}> -∗
    None -{Rmw}> -∗
    last_local_write tid2 flag1 None -∗
    last_local_write tid2 flag2 None -∗
    Prot[ flag1 , (1/2)%Qp | flag1_prot ] -∗
    Prot[ flag2 , (1/2)%Qp | flag2_prot ] -∗
    (∃ rv, "r1" ↦ᵣ rv) -∗
    t2_instrs -∗
    WPi (LTSI.Normal, (BV 64 0x2000)) @ tid2 {{ λ lts', ⌜lts' = (LTSI.Done, (BV 64 0x2008)) ⌝}}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hrmw Hlocalw_flag1 Hlocalw_flag2 Hprot_flag1 Hprot_flag2 [% Hr1] Hinstrs".
    iDestruct "Hinstrs" as "(#? & #? & #?)".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hr1 Hpo_src Hctrl_src Hrmw Hlocalw_flag1 Hprot_flag1]").
    {
      iApply (iload_pln _ ∅ ∅ with "[$Hr1 $Hpo_src $Hctrl_src $Hrmw Hlocalw_flag1]").
      {
        iFrame "#∗".
        rewrite big_sepS_empty big_sepM_empty //.
      }

      iIntros (?). iSplitR.
      - iIntros "_ _". done.
      - iExists _,_,emp%I. iSplitL. iIntros "_";iFrame.
        iIntros (??) "_ _ _ _ _ _ _ #Hprot". iFrame "Hprot". iExact "Hprot".
    }

    iIntros (?) "(-> & % & % & % & #Hf1read & %Hfread_tid & Hr1 & Hannot & (% & % & #Hwrite) & #Hrf & Hpo_src & _ & Hctrl_src & Hrmw & _)". 
    assert (G: ((BV 64 8192) `+Z` 4 = (BV 64 8196))%bv) by bv_solve. rewrite G. clear G.

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hlocalw_flag2 Hprot_flag2 Hr1 Hannot Hwrite Hrf Hpo_src Hctrl_src]").
    {
      iApply (istore_pln_single_data with "[$Hpo_src $Hctrl_src $Hlocalw_flag2 $Hr1 $Hannot Hprot_flag2]").
      iFrame "#".

      iExists _,_,_. iSplitL. iIntros "H";iFrame;iExact "H".
      iIntros (eidf2) "#Hf2write %Hfwrite_tid #Ht2po #Ht2data Hp #Hflag1_prot".
      unfold flag2_prot. iRight.
      destruct (decide (v = (BV 64 0))); [iLeft; done|].
      iRight. unfold flag1_prot.
      iDestruct "Hflag1_prot" as "[%Htid_eid' | [%wd Hflag1_prot]]".
      {
        by iDestruct (initial_write_zero _ _ _ _ _ Htid_eid' with "Hwrite") as "<-".
      }
      iExists wd, eid', eid.
      unfold t2_prop.
      iAssert(⌜v = (BV 64 1)⌝)%I as "->".
      {
        unfold t1_prop.
        iDestruct "Hflag1_prot" as "(_ & _ & _ & _ & Hwrite')".
        iDestruct (event_agree with "Hwrite Hwrite'") as "%Heq".
        iPureIntro.
        by injection Heq.
      }
        
      iFrame "#%".
    }

    iIntros (?) "(-> & _ & [% (_ & _ & _ & _)])".
    assert (G: ((BV 64 8196) `+Z` 4 = (BV 64 8200))%bv) by bv_solve. rewrite G. clear G. 
    
    iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, (BV 64 8200))⌝)%I).
    { by iApply idone. }

    iIntros (? ->). iApply wpi_terminated. iApply (inst_post_lifting_lifting _ _ _ ∅); auto.
    rewrite dom_empty_L //.
  Qed.

  Lemma t3 ctrl:
    None -{LPo}> -∗
    ctrl -{Ctrl}> -∗
    None -{Rmw}> -∗
    last_local_write tid3 flag2 None -∗
    last_local_write tid3 data None -∗
    Prot[ flag2 , (1/2)%Qp | flag2_prot ] -∗
    Prot[ data , (1/2)%Qp | data_prot ] -∗
    (∃ rv, "r1" ↦ᵣ rv) -∗
    (∃ rv, "r2" ↦ᵣ rv) -∗
    t3_instrs -∗
    WPi (LTSI.Normal, (BV 64 0x3000)) @ tid3 {{ λ lts',
                                                  ⌜lts' = (LTSI.Done, (BV 64 0x3008)) ⌝ ∗
                                                  ∃ r1 r2, "r1" ↦ᵣ r1 ∗ "r2" ↦ᵣ r2 ∗
                                                    (⌜r1.(reg_val) = (BV 64 1)⌝ -∗ ⌜r2.(reg_val) = (BV 64 42)⌝)
        }}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hrmw Hlastw_flag2 Hlastw_data Hprot_flag Hprot_data [% Hr1] [% Hr2] Hinstrs".
    iDestruct "Hinstrs" as "(#? & #? & #?)".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hr1 Hpo_src Hctrl_src Hrmw Hlastw_flag2 Hprot_flag]").
    {
      iApply (iload_pln _ ∅ ∅ with "[$Hr1 $Hpo_src $Hctrl_src $Hrmw $Hlastw_flag2]").
      {
        iFrame "∗#".
        rewrite big_sepM_empty big_sepS_empty //.
      }

      iIntros (?). iSplitR.
      - iIntros "_ _"; done.
      - iExists _,_,emp%I. iSplitL. iIntros "_";iFrame.
        iIntros (??) "_ _ _ _ _ _ _ #Hprot". iModIntro. iFrame "Hprot". iExact "Hprot".
    }

    iIntros (?) "(-> & % & % & % & #Hf2read & %Hf2read_tid & Hr1 & Hannot & (% & % & #Hf2write) & #Hrf & Hpo_src & _ & Hctrl_src & Hrmw & _)".

    assert (G: ((BV 64 12288) `+Z` 4 = (BV 64 12292))%bv) by bv_solve. rewrite G. clear G.

    iDestruct (lpo_to_po with "Hpo_src") as "[Hpo_src #Hpo]".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hr2 Hpo_src Hannot Hctrl_src Hrmw Hlastw_data Hprot_data]").
    {
      iApply (iload_pln (λ e v', ⌜v = (BV 64 1)⌝ -∗ ⌜v' = (BV 64 42)⌝)%I {[eid]} {[eid := flag2_prot v eid']} with "[$Hr2 $Hpo_src $Hctrl_src $Hrmw $Hlastw_data Hannot]").
      {
        iFrame "#∗".
        rewrite big_sepM_singleton big_sepS_singleton. iFrame "#∗".
      }
      iIntros (data_read). iSplitR.
      - iIntros "Hdata_read HPo". rewrite  big_sepM_singleton big_sepS_singleton.
        iApply (acq_po_is_lob with "[Hf2read] HPo"). iDestruct (event_node with "Hf2read") as "$".
      - iExists _,_,_. iSplitL. rewrite big_sepM_singleton. iIntros "H";iFrame;iExact "H".
        iIntros (data_write v') "#Hdata_read %Hdata_read_tid #HPo (% & % & #Hdata_write) #Hdata_rf Hp Hannot".
        rewrite big_sepS_singleton.
        iIntros "#Hdata_prot". iModIntro. iFrame "Hdata_prot". iIntros (->).
        simpl.

        iDestruct "Hdata_prot" as "[(% & %)|%Hdata_prot]"; [done|].
        unfold flag2_prot.
        iDestruct "Hannot" as "[%Hannot|[%Hannot|Hannot]]".
        {
          iDestruct (initial_write_zero _ _ _ _ _ Hannot with "Hf2write") as "%F".
          contradict F. bv_solve.
        }
        {
          contradict Hannot. 
          (* Unfold some hidden constructors that seem to trip up bv_solve *)
          unfold Val, AAArch.val, AAval, AAArch.val_size.
          bv_solve.
        }

        iDestruct "Hannot" as "(%data_write' & %flag1_write & %flag1_read & #Ht1 & #Ht2)". 
        remember eid' as flag2_write.
        remember eid as flag2_read.

        iDestruct "Ht1" as "(% & % & Ht1_po & Hdata_write' & Hflag1_write)".
        iDestruct "Ht2" as "(% & % & Hflag1_rf & Ht2_data & Hflag2_write)".

        iDestruct (initial_write_co with "Hdata_write Hdata_write'") as "Hco"; [ done | | ].
        { subst. pose proof tid_nz_nz. lia. }
        iDestruct (rf_co_to_fr with "Hdata_rf Hco") as "Hfr".
        iDestruct (fre_is_ob with "Hfr") as "Hob1"; [lia|].
        iDestruct (po_rel_is_lob with "Ht1_po [Hflag1_write]") as "Hlob2".
        { iDestruct (event_node with "Hflag1_write") as "$". }
        iDestruct (lob_is_ob with "Hlob2") as "Hob2".
        iDestruct (rfe_is_ob with "Hflag1_rf") as "Hob3"; [lia|].
        iDestruct (data_is_lob with "Ht2_data") as "Hlob4".
        iDestruct (lob_is_ob with "Hlob4") as "Hob4".
        iDestruct (rfe_is_ob with "Hrf") as "Hob5"; [lia|].
        iDestruct (acq_po_is_lob with "[Hf2read] HPo") as "Hlob6".
        { iDestruct (event_node with "Hf2read") as "$". }
        iDestruct (lob_is_ob with "Hlob6") as "Hob6".


        iDestruct (ob_trans with "Hob1 Hob2") as "Hob".
        iDestruct (ob_trans with "Hob Hob3") as "{Hob} Hob".
        iDestruct (ob_trans with "Hob Hob4") as "{Hob} Hob".
        iDestruct (ob_trans with "Hob Hob5") as "{Hob} Hob".
        iDestruct (ob_trans with "Hob Hob6") as "{Hob} Hob".
        iDestruct (ob_acyclic with "Hob") as "[]".
    }
    iIntros (?) "(-> & % & % & % & Hdread & % & Hr2 & Hdannot & _ & _ & Hlpo & _ & Hctrl & Hrmw & _)".
    subst. assert (G: ((BV 64 12292) `+Z` 4 = (BV 64 12296))%bv); [bv_solve|]. rewrite G.

    iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 12296)⌝)%I).
    { by iApply idone. }
    iIntros (? ->). iApply wpi_terminated. iApply (inst_post_lifting_lifting _ _ _ {[eid0 := _]} with "[Hdannot]"); auto.
    { simpl. rewrite dom_singleton_L. set_solver. }
    { rewrite big_sepM_singleton. iExact "Hdannot". }
    rewrite big_sepM_singleton.
    iIntros "% !>". iSplit;first done.
    iExists _, _.  iFrame. auto.
  Qed.

End proof.
