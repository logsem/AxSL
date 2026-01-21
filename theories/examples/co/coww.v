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

From stdpp.bitvector Require Import definitions tactics.

From iris.proofmode Require Import tactics.

From self.low Require Import instantiation.
From self.low.lib Require Import edge event.
From self.mid Require Import rules specialised_rules.
Require Import ISASem.SailArmInstTypes.

Import uPred.

Definition write addr data : Instruction :=
  (IStore AV_plain AS_normal "r0" (AEval data) (AEval addr)).

Section proof.
  Context `{AAIrisG}.
  Context `{!AAThreadG} `{ThreadGN}.

  Context (addr data data' : bv 64).

  Import AACand.

  Definition instrs : iProp Σ :=
    (BV 64 0x1000) ↦ᵢ (write addr data) ∗
    (BV 64 0x1004) ↦ᵢ (write addr data') ∗
    (BV 64 0x1008) ↦ᵢ -.

  Lemma loc_of_writes {gr ks kv ks' kv' a v v'} eid eid' :
   Event.event_interp gr (Event.W ks kv a v) eid ->
   Event.event_interp gr (Event.W ks' kv' a v') eid' ->
   (eid, eid') ∈ Candidate.same_pa gr.
  Proof.
    intros HE1 HE2.
    unfold Event.event_interp in *.
    clear -HE1 HE2.
    destruct HE1 as (E1&HE1gr&HE1).
    destruct HE2 as (E2&HE2gr&HE2).
    set_unfold.
    naive_solver.
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
    assert(Hloc : (eid, eid') ∈ Candidate.same_pa gr).
    { apply (loc_of_writes _ _ HE1 HE2). }
    destruct Hgraph_co as [Hinternal _ _].
    unfold Edge.ef_edge_interp in Hpo, Hco.
    set(internal := Candidate.po gr ∩ Candidate.same_pa gr ∪ AAConsistent.ca gr ∪ Candidate.rf gr).
    assert (Hint1 : (eid, eid') ∈ internal). { set_solver + internal Hpo Hloc. }
    assert (Hint2 : (eid', eid) ∈ internal). { set_solver + internal Hco. }
    assert (Hcyc : (eid, eid) ∈ GRel.grel_plus internal).
    { eapply GRel.grel_plus_trans; apply GRel.grel_plus_once; eassumption. }
    unfold GRel.grel_acyclic in Hinternal.
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
    + clear - HE1 HE2.
      subst.
      set_unfold.
      intros ? [-> | ->].
      unfold Event.event_interp in HE1.  cdestruct HE1. subst.
      eexists. split;first eassumption. done.
      unfold Event.event_interp in HE2.  cdestruct HE2. subst.
      eexists. split;first eassumption. done.
  Qed.

  Lemma prog ctrl:
    None -{LPo}> -∗
    ctrl -{Ctrl}> -∗
    last_local_write 1 addr None -∗
    『 addr, □ | (λ _ _, True%I)』 -∗
    instrs -∗
    WPi (LTSI.Normal,  (BV 64 0x1000)) @ 1 {{ λ lts', ⌜lts' = (LTSI.Done, (BV 64 0x1008))⌝ ∗
                                                      ∃ eid eid',
                                                        eid -{E}> Event.W AV_plain AS_normal addr data ∗
                                                        eid' -{E}> Event.W AV_plain AS_normal addr data' ∗
                                                        eid -{Edge.Co}> eid'}}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hlast_write #Hprot Hinstrs".
    iDestruct "Hinstrs" as "(#? & #? & #?)".

    iApply sswpi_wpi.
    (* iApply (sswpi_mono with "[Hpo_src Hctrl_src Hlast_write Hprot]"). *)
    (* { *)
      iApply (istore_pln (λ _, emp)%I ∅ ∅ with "[$Hpo_src $Hctrl_src $Hlast_write]").
      iFrame "#". rewrite big_sepS_empty big_sepM_empty.
        iSplit;first done.
        iSplit;first done.

      iExists emp%I. iSplitL. iIntros "_";iFrame.  done.
      iIntros (?). iSplitL.
      { by iIntros "_ _ _". }
      { iIntros "#HE %Htid #Hpo _ _". by iModIntro. }
      
      iNext.
    iIntros (eid1) "(#Heid1 & %Htid1 & Hpo_src & _ & Hlast_write & Hctrl_src & _)".

    assert(G: ((BV 64 4096) `+Z` 4 = (BV 64 4100))%bv) by bv_solve. rewrite G. clear G.

    iDestruct (lpo_to_po with "Hpo_src") as "[Hpo_src #Hpo]".

    iApply sswpi_wpi.
    iApply (istore_pln (λ _, emp)%I {[eid1]} ∅ with "[$Hpo_src $Hctrl_src $Hlast_write]").
    { iFrame "#". rewrite big_sepS_singleton big_sepM_empty. iFrame "#". iSplit;first done. 

      iExists emp%I. iSplitL. iIntros "_";iFrame. done.
      iIntros (?). iSplitL.
      { by iIntros "_ _ _". }
      { iIntros "#HE %Htid #Hpo' _ _". by iModIntro. }
    }

    iNext.
    iIntros (eid2) "(#Heid2 & %Htid2 & Hpo_src & #Hpo' & Hlast_write & Hctrl_src & _)".
    iEval (rewrite big_sepS_singleton) in "Hpo'".

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
    + by iExists AV_plain, AS_normal, data.
    + by iExists AV_plain, AS_normal, data'.
  Qed.
                           
End proof.
