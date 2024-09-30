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

Definition write addr data : Instruction :=
  (IStore AS_normal AV_plain "r0" (AEval data) (AEval addr)).

Section Proof.
  Context `{AAIrisG}.
  Context `{!AAThreadG} `{ThreadGN}.

  Context (addr data data' : bv 64).

  Definition instrs : iProp Σ :=
    (BV 64 0x1000) ↦ᵢ (write addr data) ∗
    (BV 64 0x1004) ↦ᵢ (write addr data') ∗
    (BV 64 0x1008) ↦ᵢ -.

  Lemma loc_of_writes {gr ks kv ks' kv' a v v'} eid eid' :
   Event.event_interp gr (Event.W ks kv a v) eid ->
   Event.event_interp gr (Event.W ks' kv' a v') eid' ->
   (eid, eid') ∈ AACandExec.Candidate.loc gr.
  Proof.
    intros HE1 HE2.
    unfold Event.event_interp in *.
    clear -HE1 HE2.
    destruct HE1 as (E1&HE1gr&HE1).
    destruct HE2 as (E2&HE2gr&HE2).
    set_unfold.
    unfold AAConsistent.event_is_write_with, AAConsistent.event_is_write_with_P in HE1.
    exists E1, E2, a.
    split; [assumption|].
    split.
    {
      destruct E1. destruct o; try contradiction. rewrite CBool.bool_unfold in HE1. simpl.
      f_equal.
      destruct HE1 as (_&_&HE1).
      unfold AAConsistent.addr_and_value_of_wreq in HE1.
      destruct (decide (n = AAArch.val_size)); [| destruct t0; congruence].
      destruct t0. unfold eq_rec_r, eq_rec in HE1. subst. simpl. inversion HE1. reflexivity. 
    }
    split; [assumption|].
    destruct E2. destruct o; try contradiction. rewrite CBool.bool_unfold in HE2. simpl.
    f_equal.
    destruct HE2 as (_&_&HE2).
    unfold AAConsistent.addr_and_value_of_wreq in HE2.
    destruct (decide (n = AAArch.val_size)); [| destruct t0; congruence].
    destruct t0. unfold eq_rec_r, eq_rec in HE2. subst. simpl. inversion HE2. reflexivity. 
  Qed.

  (* Instead of these ad hoc lemmas we should just expose the notion
     of "internal" edges in the ghost state and give a lemma that it's
     acyclic *)
  Lemma po_loc_co_acyclic eid eid' :
    eid -{Edge.Po}> eid' -∗
    eid' -{Edge.Co}> eid -∗
    (∃ ks kv v, eid -{E}> (Event.W ks kv addr v)) -∗
    (∃ ks kv v, eid' -{E}> (Event.W ks kv addr v)) -∗
    False%I.
  Proof.
    rewrite event_eq /event_def. rewrite edge_eq /edge_def.
    iIntros "(%gr & Hgr1 & %Hgraph_co & % & %Hpo) (% & Hgr2 & _ & _ & %Hco)
             (% & % & % & % & Hgr3 & _ & _ & %HE1) (% & % & % & % & Hgr4 & _ & _ & %HE2)".
    iDestruct (graph_agree_agree with "Hgr2 Hgr1") as %->.
    iDestruct (graph_agree_agree with "Hgr3 Hgr1") as %->.
    iDestruct (graph_agree_agree with "Hgr4 Hgr1") as %->.
    exfalso.
    assert(Hloc : (eid, eid') ∈ AACandExec.Candidate.loc gr).
    { apply (loc_of_writes _ _ HE1 HE2). }
    destruct Hgraph_co as [Hinternal _ _].
    unfold Edge.ef_edge_interp in Hpo, Hco.
    set(internal := AACandExec.Candidate.po gr ∩ AACandExec.Candidate.loc gr ∪ AAConsistent.ca gr ∪ AACandExec.Candidate.rf gr).
    assert (Hint1 : (eid, eid') ∈ internal). { set_solver + internal Hpo Hloc. }
    assert (Hint2 : (eid', eid) ∈ internal). { set_solver + internal Hco. }
    assert (Hcyc : (eid, eid) ∈ GRel.grel_plus internal).
    { eapply GRel.grel_plus_trans; apply GRel.grel_plus_once; eassumption. }
    rewrite GRel.grel_irreflexive_spec in Hinternal.
    specialize (Hinternal (eid, eid)).
    by apply Hinternal.
  Qed.

  Lemma po_to_co eid eid' :
    eid -{Edge.Po}> eid' -∗
    (∃ ks kv v, eid -{E}> (Event.W ks kv addr v)) -∗
    (∃ ks kv v, eid' -{E}> (Event.W ks kv addr v)) -∗
    eid -{Edge.Co}> eid'.
  Proof.
    rewrite event_eq /event_def. rewrite edge_eq /edge_def.
    iIntros "(%gr & Hgr1 & %Hgraph_co & % & %Hpo)
             (%ks & %kv & %v & % & Hgr2 & _ & _ & %HE1) (%ks' & %kv' & %v' & % & Hgr3 & _ & _ & %HE2)".
    iDestruct (graph_agree_agree with "Hgr2 Hgr1") as %->.
    iDestruct (graph_agree_agree with "Hgr3 Hgr1") as %->.
    iExists gr.
    iFrame "%∗".
    iPureIntro.
    unfold Edge.ef_edge_interp.
    apply Graph.wf_coi_inv; try assumption.
    + apply (loc_of_writes _ _ HE1 HE2).
    + assert (G : eid ∈ AACandExec.Candidate.mem_writes gr).
      {
        unfold Event.event_interp in HE1. 
        destruct HE1 as (E1 & HE1gr & HE1).
        apply (AAConsistent.event_is_write_with_elem_of_mem_writes eid E1 ks kv addr v); assumption.
      }
      assert (G' : eid' ∈ AACandExec.Candidate.mem_writes gr).
      {
        unfold Event.event_interp in HE2. 
        destruct HE2 as (E2 & HE2gr & HE2).
        apply (AAConsistent.event_is_write_with_elem_of_mem_writes eid' E2 ks' kv' addr v'); assumption.
      }
      set_solver + G G'.
  Qed.

  Lemma prog ctrl:
    None -{LPo}> -∗
    ctrl -{Ctrl}> -∗
    last_local_write 1 addr None -∗
    Prot[ addr | (λ _ _, True%I) ] -∗
    instrs -∗
    WPi (LTSI.Normal,  (BV 64 0x1000)) @ 1 {{ λ lts', ⌜lts' = (LTSI.Done, (BV 64 0x1008))⌝ ∗
                                                      ∃ eid eid',
                                                        eid -{E}> Event.W AS_normal AV_plain addr data ∗
                                                        eid' -{E}> Event.W AS_normal AV_plain addr data' ∗
                                                        eid -{Edge.Co}> eid'}}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hlast_write Hprot Hinstrs".
    iDestruct "Hinstrs" as "(#? & #? & #?)".
    iDestruct "Hprot" as "[Hprot1 Hprot2]".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hpo_src Hctrl_src Hlast_write Hprot1]").
    {
      iApply (istore_pln (λ _, emp)%I ∅ ∅ with "[$Hpo_src $Hctrl_src $Hlast_write]").
      { iFrame "#". by rewrite big_sepS_empty big_sepM_empty. }

      iExists _,_,emp%I. iSplitL. iIntros "_";iFrame.
      iIntros (?). iSplitL.
      - by iIntros "_ _ _".
      - iIntros "#HE %Htid #Hpo _ _". by iModIntro.
    }
      
    iIntros (?) "(-> & %eid1 & #Heid1 & %Htid1 & Hpo_src & _ & Hlast_write & Hctrl_src & _)".

    assert(G: ((BV 64 4096) `+Z` 4 = (BV 64 4100))%bv) by bv_solve. rewrite G. clear G.

    iDestruct (lpo_to_po with "Hpo_src") as "[Hpo_src #Hpo]".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hpo_src Hctrl_src Hlast_write Hpo Hprot2]").
    {
      iApply (istore_pln (λ _, emp)%I {[eid1]} ∅ with "[$Hpo_src $Hctrl_src $Hlast_write]").
      { iFrame "#". rewrite big_sepS_singleton big_sepM_empty. by iFrame "#". }

      iExists _,_,emp%I. iSplitL. iIntros "_";iFrame.
      iIntros (?). iSplitL.
      - by iIntros "_ _ _".
      - iIntros "#HE %Htid #Hpo' _ _". by iModIntro.
    }

    iIntros (?) "{Hpo} (-> & %eid2 & #Heid2 & %Htid2 & Hpo_src & #Hpo & Hlast_write & Hctrl_src & _)".
    iEval (rewrite big_sepS_singleton) in "Hpo".

    assert(G: ((BV 64 4100) `+Z` 4 = (BV 64 4104))%bv) by bv_solve. rewrite G. clear G.

    iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 4104)⌝))%I.
    { by iApply idone. }

    iIntros (? ->).
    iApply wpi_terminated.
    iApply (inst_post_lifting_lifting _ _ _ ∅); [done|done|].
    iIntros "_ !>".
    iSplitL; [done|].
    iExists eid1, eid2.
    iFrame "#".

    iApply po_to_co; [done| |].
    + by iExists AS_normal, AV_plain, data.
    + by iExists AS_normal, AV_plain, data'.
  Qed.
                           
End Proof.
