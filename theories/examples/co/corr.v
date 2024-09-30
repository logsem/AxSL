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

From self.low Require Import instantiation.
From self.low.lib Require Import edge event.
From self.mid Require Import rules specialised_rules.
Require Import ISASem.SailArmInstTypes.

Import uPred.

Definition addr := (BV 64 0x10).
Definition data := (BV 64 0x11).

Definition write : Instruction :=
  (IStore AS_normal AV_plain "r0" (AEval data) (AEval addr)).
Definition read reg : Instruction :=
  (ILoad AS_normal AV_plain reg (AEval addr)).

Section proof.
  Context `{AAIrisG}.

  Definition addr_prot (v : Val) (e : Eid) : iProp Σ :=
    (⌜v= data⌝ ∗ ⌜EID.tid e = 1%nat⌝) ∨ ⌜EID.tid e = 0%nat⌝.

  Definition instrs_writer : iProp Σ :=
    (BV 64 0x1000) ↦ᵢ write ∗
    (BV 64 0x1004) ↦ᵢ -.

  Definition instrs_reader : iProp Σ :=
    (BV 64 0x2000) ↦ᵢ read "r1" ∗
    (BV 64 0x2004) ↦ᵢ read "r2" ∗
    (BV 64 0x2008) ↦ᵢ -.

  Context `{!AAThreadG} `{ThreadGN}.

  Lemma writer ctrl:
    None -{LPo}> -∗
    ctrl -{Ctrl}> -∗
    last_local_write 1 addr None -∗
    Prot[ addr, (1/2)%Qp | addr_prot ] -∗
    instrs_writer -∗
    WPi (LTSI.Normal, (BV 64 0x1000)) @ 1 {{ λ lts', ⌜lts' = (LTSI.Done, (BV 64 0x1004))⌝}}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hlocalw Hprot Hinstrs".
    iDestruct "Hinstrs" as "(#? & #?)".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hpo_src Hctrl_src Hlocalw Hprot]").
    {
      iApply (istore_pln (λ _, emp)%I ∅ ∅ with "[$Hpo_src $Hctrl_src $Hlocalw]"). iFrame "#∗".
      rewrite big_sepS_empty big_sepM_empty //.

      iExists _,_,emp%I. iSplitL. iIntros "_";iFrame.
      iIntros (?). iSplitL.
      - iIntros "_ _ _". done.
      - iIntros "#HE % #Hpo _ _". iModIntro. iSplit;first done. simpl. rewrite /addr_prot. iLeft;done.
    }
    iIntros (?) "(-> &[% (#Hwrite&%Htid1&Hpo&_&Hlocal&Hctrl&HeidP)])".
    assert (G: ((BV 64 4096) `+Z` 4 = (BV 64 4100))%bv) by bv_solve. rewrite G.

    iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 4100)⌝)%I).
    { by iApply idone. }
    iIntros (? ->). iApply wpi_terminated. iApply (inst_post_lifting_lifting _ _ _ ∅); auto. rewrite dom_empty_L //.
  Qed.

  (* Ad-hoc internal lemma for CoRR *)
  Lemma po_loc_fr_rf_acyclic addr eid eid' eid'' :
    eid -{Edge.Po}> eid' -∗
    eid' -{Edge.Fr}> eid'' -∗
    eid'' -{Edge.Rf}> eid -∗
    (∃ kinds kindv val, eid -{E}> (Event.R kinds kindv addr val)) -∗
    (∃ kinds kindv val, eid' -{E}> (Event.R kinds kindv addr val)) -∗
    False%I.
  Proof.
    rewrite event_eq /event_def. rewrite edge_eq /edge_def.
    iIntros "[% (Hg1&%&%&%)] [% (Hg2&_&_&%)] [% (Hg3&_&_&%)]
    (%&%&%&[% (Hg4&_&_&%HE1)]) (%&%&%&[% (Hg5&_&_&%HE2)])".
    iDestruct (graph_agree_agree with "Hg1 Hg2") as %->.
    iDestruct (graph_agree_agree with "Hg1 Hg3") as %->.
    iDestruct (graph_agree_agree with "Hg1 Hg4") as %->.
    iDestruct (graph_agree_agree with "Hg1 Hg5") as %->.
    exfalso.
    simpl in *.
    assert ((eid,eid') ∈ AACandExec.Candidate.loc gr3).
    {
      rewrite /Event.event_interp in HE1.
      rewrite /Event.event_interp in HE2.
      clear -HE1 HE2.
      set_unfold.
      destruct HE1 as (?&Hlk1&HE1).
      destruct HE2 as (?&Hlk2&HE2).
      exists x, x0, addr. split;first assumption.
      split.
      {
        rewrite /AAConsistent.event_is_read_with in HE1.
        set_unfold.
        clear HE2 Hlk2 Hlk1.
        destruct x;destruct o;simpl in *;try contradiction.
        f_equal.
        rewrite CBool.bool_unfold in HE1.
        destruct HE1 as [_ [[_ Haddr1] _]].
        destruct t0. simpl in *. done.
      }
      split;first assumption.
      {
        rewrite /AAConsistent.event_is_read_with in HE2.
        set_unfold.
        clear HE1 Hlk2 Hlk1.
        destruct x0;destruct o;simpl in *;try contradiction.
        f_equal.
        rewrite CBool.bool_unfold in HE2.
        destruct HE2 as [_ [[_ Haddr2] _]].
        destruct t0. simpl in *. done.
      }
    }
    destruct H3.
    rewrite GRel.grel_irreflexive_spec in internal.
    specialize (internal (eid, eid)).
    apply internal.
    eapply (GRel.grel_plus_trans _ _ eid').
    apply GRel.grel_plus_once. { set_solver + H8 H5. }
    eapply (GRel.grel_plus_trans _ _ eid'').
    apply GRel.grel_plus_once. { set_solver + H6. }
    apply GRel.grel_plus_once. { set_solver + H7. }
    done.
  Qed.

  Definition reader ctrl :
    None -{LPo}> -∗
    ctrl -{Ctrl}> -∗
    None -{Rmw}> -∗
    last_local_write 2 addr None -∗
    Prot[ addr, (1/2)%Qp | addr_prot ] -∗
    (∃ rv, "r1" ↦ᵣ rv) -∗
    (∃ rv, "r2" ↦ᵣ rv) -∗
    instrs_reader -∗
    WPi (LTSI.Normal, (BV 64 0x2000)) @ 2 {{ λ lts',
                                               ⌜lts' = (LTSI.Done, (BV 64 0x2008))⌝ ∗
                                               ∃ r1 r2, "r1" ↦ᵣ r1 ∗ "r2" ↦ᵣ r2 ∗
                                                        (⌜r1.(reg_val)  = (BV 64 0) ∧ (r2.(reg_val) = (BV 64 0) ∨ r2.(reg_val) = data)⌝
                                                        ∨ ⌜r1.(reg_val)  = data ∧ r2.(reg_val) = data⌝)
      }}.
  Proof.
    iIntros "Hlpo Hctrl Hrmw Hlocalw Hprot [% Hr1] [% Hr2] Hinstrs".
    iDestruct "Hinstrs" as "(#? & #? & #?)".
    iDestruct "Hprot" as "[Hprot1 Hprot2]".
    iApply sswpi_wpi. iApply (sswpi_mono with "[Hr1 Hlpo Hctrl Hrmw Hlocalw Hprot1]").
    {
      iApply (iload_pln _ ∅ ∅ with "[$Hr1 $Hlpo $Hctrl $Hrmw $Hlocalw]"). iFrame "∗#".
      rewrite big_sepM_empty big_sepS_empty //.

      iIntros (?). iSplitR.
      - iIntros "_ _". rewrite big_sepM_empty //.
      - iExists _,_,emp%I. iSplitL. iIntros "_";iFrame.
        iIntros (??) "_ _ _ _ _ _ _ #Hprot". iModIntro. iFrame "Hprot". iExact "Hprot".
    }
    iIntros (?) "(-> & %&%&%& #He_r1 & %Htid_r1 & Hr1 & Hannot & (% & % & #He_w1) & #Hrf1 & Hlpo & _ & Hctrl & Hrmw & Hlocalw)".
    assert (G: ((BV 64 8192) `+Z` 4 = (BV 64 8196))%bv); [bv_solve|]. rewrite G.

    iDestruct (lpo_to_po with "Hlpo") as "[Hlpo #Hpo_r1]".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hr2 Hlpo Hctrl Hrmw Hlocalw Hprot2]").
    {
      iApply (iload_pln _ {[eid]} ∅ with "[$Hr2 $Hlpo $Hctrl $Hrmw $Hlocalw]"). iFrame "∗#".
      { rewrite big_sepM_empty big_sepS_singleton. by iFrame "#". }
      iIntros (?). iSplitR.
      - iIntros "_ _". rewrite big_sepM_empty //.
      - iExists _,_,emp%I. iSplitL. iIntros "_";iFrame.
        iIntros (??) "_ _ _ _ _ _ _ #Hprot". iModIntro. iFrame "Hprot". iExact "Hprot".
    }
    iIntros (?) "(-> & % & % & % & #He_r2 & %Htid_r2 & Hr2 & Hannot2 & (%&%&#He_w2) & #Hrf2 & Hlpo & #Hpo_r1_r2 & Hctrl & Hrmw & _)".
    subst. clear G. assert (G: ((BV 64 8196) `+Z` 4 = (BV 64 8200))%bv); [bv_solve|]. rewrite G.
    rewrite big_sepS_singleton.
    iAssert (⌜eid ≠ eid0⌝%I) as "%Hneq".
    { iIntros (->). iApply (po_irrefl with "Hpo_r1_r2"). }

    iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 8200)⌝)%I).
    { by iApply idone. }
    iIntros (? ->). iApply wpi_terminated.
    iApply (inst_post_lifting_lifting _ _ _ {[eid0 := _;eid := _]} with "[Hannot Hannot2]"); auto.
    {
      simpl. rewrite 2!dom_insert_L. rewrite dom_empty_L union_empty_r_L.
      apply set_Forall_union;rewrite set_Forall_singleton;lia.
    }
    {
      rewrite big_sepM_insert. iFrame.
      rewrite big_sepM_singleton. iFrame.
      rewrite lookup_singleton_None //.
    }
    iIntros "HP".
    rewrite big_sepM_insert. rewrite big_sepM_singleton.
    2:{ rewrite lookup_singleton_None //. }
    iModIntro.
    iSplit;first done.
    iExists _, _. iFrame "Hr1 Hr2".
    rewrite /addr_prot.
    iDestruct "HP" as "[[[-> %]|%] [[-> %]|%]]".
    { iRight;done. }
    {
      iDestruct (initial_write_zero with "He_w1") as %->;first lia.
      iLeft. iSplit;[done|iRight;done].
    }
    {
      (* impossible, by coh *)
      iExFalso.
      iApply po_loc_fr_rf_acyclic;iFrame "#".
      iDestruct (initial_write_co with "He_w2 He_w1") as "#Hco";first lia.
      rewrite H4. lia.
      iApply (rf_co_to_fr with "Hrf2 Hco").
    }
    {
      iDestruct (initial_write_zero with "He_w1") as %<-;first lia.
      iDestruct (initial_write_zero with "He_w2") as %<-;first lia.
      iLeft. iSplit;[done|iLeft;done].
    }
  Qed.

End proof.
