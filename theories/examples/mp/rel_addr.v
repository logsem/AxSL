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
Definition flag := (BV 64 0x18).

Definition data_write : Instruction :=
  (IStore AS_normal AV_plain "r0" (AEval (BV 64 42)) (AEval data)).
Definition flag_write : Instruction :=
  (IStore AS_rel_or_acq AV_plain "r0" (AEval (BV 64 1)) (AEval flag)).

Definition flag_read kind:=
  (ILoad kind AV_plain "r1" (AEval flag)).
Definition dep_data_read :=
  (ILoad AS_normal AV_plain "r2" (AEbinop AOplus (AEval data) (AEbinop AOminus (AEreg "r1") (AEreg "r1")))).

Section proof.
  Context `{AAIrisG}.

  Context (tid1 tid2: Tid).
  Context (Htid_ne :tid1 ≠ tid2).

  Definition data_prot (v : Val) (e : Eid) : iProp Σ :=
    (⌜v= (BV 64 42)⌝ ∗ ⌜EID.tid e = tid1⌝) ∨ ⌜EID.tid e = 0%nat⌝.

  Definition flag_prot (v: Val) (e : Eid) : iProp Σ :=
    ⌜EID.tid e = 0%nat⌝
    ∨ ∃ d,
        ⌜EID.tid e = tid1 ⌝ ∗ ⌜EID.tid d = tid1⌝ ∗
        d -{Edge.Po}> e ∗
        d -{E}> (Event.W AS_normal AV_plain data (BV 64 42)) ∗
        e -{E}> (Event.W AS_rel_or_acq AV_plain flag (BV 64 1)).

  Definition send_instrs : iProp Σ :=
    (BV 64 0x1000) ↦ᵢ data_write ∗
    (BV 64 0x1004) ↦ᵢ flag_write ∗
    (BV 64 0x1008) ↦ᵢ -.

  Definition dep_receive_instrs : iProp Σ :=
    (BV 64 0x2000) ↦ᵢ flag_read AS_normal ∗
    (BV 64 0x2004) ↦ᵢ dep_data_read ∗
    (BV 64 0x2008) ↦ᵢ -.

  Context `{!AAThreadG} `{ThreadGN}.

  (* NOTE: the sender proof is identical to that in [rel_acq.v] *)
  Lemma send ctrl:
    None -{LPo}> -∗
    ctrl -{Ctrl}> -∗
    last_local_write tid1 data None -∗
    last_local_write tid1 flag None -∗
    Prot[ data, (1/2)%Qp | data_prot ] -∗
    Prot[ flag, (1/2)%Qp | flag_prot ] -∗
    send_instrs -∗
    WPi (LTSI.Normal, (BV 64 0x1000)) @ tid1 {{ λ lts', ⌜lts' = (LTSI.Done, (BV 64 0x1008))⌝}}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hlocalw_data Hlocalw_flag Hprot_data Hprot_flag Hinstrs".
    iDestruct "Hinstrs" as "(#? & #? & #?)".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hpo_src Hctrl_src Hlocalw_data Hprot_data]").
    {
      iApply (istore_pln (λ _, emp)%I ∅ ∅ with "[$Hpo_src $Hctrl_src $Hlocalw_data]"). iFrame "#∗".
      rewrite big_sepS_empty big_sepM_empty //.

      iExists _,_,emp%I.
      iSplitL. iIntros "_". iFrame.

      iIntros (?). iSplitL.
      - iIntros "_ _ _". done.
      - iIntros "#HE % #Hpo _ Hp". iModIntro. iSplit;first done. simpl. rewrite /data_prot. iLeft;done.
    }
    iIntros (?) "(-> &[% (#Hwrite&%Htid1&Hpo&_&Hlocal&Hctrl&HeidP)])".
    assert (G: ((BV 64 4096) `+Z` 4 = (BV 64 4100))%bv) by bv_solve. rewrite G.

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hlocalw_flag Hprot_flag Hwrite Hpo Hctrl HeidP]").
    {
      iDestruct (lpo_to_po with "Hpo") as "[Hlpo #Hpo]".
      iApply (istore_rel emp {[eid := emp%I]}). iFrame "#∗".

      iSplit;first rewrite big_sepM_singleton //.
      iSplitL;first rewrite big_sepM_singleton //.

      iExists _. iSplitR. rewrite big_sepM_singleton. iIntros "H";iExact "H".

      iIntros (eid') "#Hwrite' %Htid2 #Hpo' HeidP' _".
      iModIntro. iSplit;first done.
      iRight. iExists eid. rewrite big_sepM_singleton. by iFrame "#".
    }
    iIntros (?) "(-> &[% (?&?&?)])".
    clear G. assert (G: ((BV 64 4100) `+Z` 4 = (BV 64 4104))%bv); [bv_solve|]. rewrite G.

    iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 4104)⌝)%I).
    { by iApply idone. }
    iIntros (? ->). iApply wpi_terminated. iApply (inst_post_lifting_lifting _ _ _ ∅); auto. rewrite dom_empty_L //.
  Qed.

  Lemma receive_addr ctrl :
    None -{LPo}> -∗
    ctrl -{Ctrl}> -∗
    None -{Rmw}> -∗
    last_local_write tid2 data None -∗
    last_local_write tid2 flag None -∗
    Prot[ data, (1/2)%Qp | data_prot ] -∗
    Prot[ flag, (1/2)%Qp | flag_prot ] -∗
    (∃ rv, "r1" ↦ᵣ rv) -∗
    (∃ rv, "r2" ↦ᵣ rv) -∗
    dep_receive_instrs -∗
    WPi (LTSI.Normal, (BV 64 0x2000)) @ tid2 {{ λ lts',
                                                  ⌜lts' = (LTSI.Done, (BV 64 0x2008))⌝ ∗
                                                  ∃ r1 r2, "r1" ↦ᵣ r1 ∗ "r2" ↦ᵣ r2 ∗
                                                    (⌜r1.(reg_val) = (BV 64 1)⌝ -∗ ⌜r2.(reg_val) = (BV 64 42)⌝)
      }}.
  Proof.
    iIntros "Hlpo Hctrl Hrmw Hllwd Hllwf Hprot_d Hprot_f [% Hr1] [% Hr2] Hinstrs".
    iDestruct "Hinstrs" as "(#? & #? & #?)".
    iApply sswpi_wpi. iApply (sswpi_mono with "[Hr1 Hlpo Hctrl Hrmw Hllwf Hprot_f]").
    {
      iApply (iload_pln _ ∅ ∅ with "[$Hr1 $Hlpo $Hctrl $Hrmw $Hllwf]"). iFrame "∗#".
      rewrite big_sepM_empty big_sepS_empty //.

      iIntros (?). iSplitR.
      - iIntros "_ _";done.
      - iExists _,_,emp%I. iSplitL. iIntros "_";iFrame.
        iIntros (??) "_ _ _ _ _ _ _ #Hprot". iModIntro. iFrame "Hprot". iExact "Hprot".
    }
    iIntros (?) "(-> & %&%&%& #Hfread & %Hfread_tid & Hr1 & Hannot & (% & % & #Hwrite) & #Hrf & Hlpo & _ & Hctrl & Hrmw & _)".
    assert (G: ((BV 64 8192) `+Z` 4 = (BV 64 8196))%bv); [bv_solve|]. rewrite G.

    iDestruct (lpo_to_po with "Hlpo") as "[Hlpo #Hpo]".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hr1 Hr2 Hlpo Hannot Hctrl Hrmw Hllwd Hprot_d]").
    {
      iApply (iload_pln_fake_addr (λ e v', ⌜v = (BV 64 1)⌝ -∗ ⌜v' = (BV 64 42)⌝)%I with "[$Hr2 Hr1 $Hlpo $Hctrl $Hrmw $Hllwd Hannot]"). iFrame "∗#".
      iExists _,_,_. iSplitL. iIntros "HH";iFrame;iExact "HH".
      iIntros (???) "#Hdread % (% &% &#Hwrite') #Hrf' #Haddr Hp Hannot #Hdata". iModIntro. iFrame "Hdata". iIntros (->).
      rewrite /data_prot /flag_prot.
      iDestruct "Hdata" as "[(% & %)|%Hdata]"; [done|].
      iDestruct (write_of_read with "Hfread Hrf") as "(% & % & Hfw)".
      iDestruct "Hannot" as "[%Hannot|Hannot]".
      { iDestruct (initial_write_zero _ _ _ _ _ Hannot with "Hfw") as "%F". contradict F. bv_solve. }
      iClear "Hfw".
      iDestruct "Hannot" as "(%d & %Hfwrite_tid & %Hd_tid & #Hsendpo & #Hd & #Hfw)".
      iDestruct (initial_write_co with "Hwrite' Hd") as "Hco"; [done| |].
      { rewrite Hd_tid.  pose proof tid_nz_nz. lia. }
      iDestruct (po_rel_is_lob with "Hsendpo [Hfw]") as "Hsendob".
      { iDestruct (event_node with "Hfw") as "$". }
      iDestruct (addr_is_lob with "Haddr") as "Hreadob".
      iDestruct (rf_co_to_fr with "Hrf' Hco") as "Hfr".
      iDestruct (rfe_is_ob with "Hrf") as "Hob2"; [lia|].
      iDestruct (fre_is_ob with "Hfr") as "Hob4"; [lia|].
      iDestruct (lob_is_ob with "Hsendob") as "Hob1".
      iDestruct (lob_is_ob with "Hreadob") as "Hob3".
      iDestruct (ob_trans with "Hob1 Hob2") as "Hob".
      iDestruct (ob_trans with "Hob Hob3") as "Hob'".
      iDestruct (ob_trans with "Hob' Hob4") as "Hob''".
      iDestruct (ob_acyclic with "Hob''") as "[]".
    }
    iIntros (?) "(-> & Hr1 & % & % & % & Hdread & % & Hr2 & Hdannot & _ & _ & Hlpo & Hctrl & Hrmw)".
    subst. clear G. assert (G: ((BV 64 8196) `+Z` 4 = (BV 64 8200))%bv); [bv_solve|]. rewrite G.

    iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 8200)⌝)%I).
    { by iApply idone. }
    iIntros (? ->). iApply wpi_terminated. iApply (inst_post_lifting_lifting _ _ _ {[eid0 := _ ]} with "[Hdannot]"); auto.
    { rewrite dom_singleton_L //. set_solver. }
    { rewrite big_sepM_singleton. iFrame. }
    iIntros "? !>". rewrite big_sepM_singleton.
    iSplit;first done.
    iExists _, _. iFrame. done.
  Qed.

End proof.
