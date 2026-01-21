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

(* This file includes the exclusive invariant and specialised rules *)
(* From stdpp Require Import unstable.bitvector. *)

From iris.proofmode Require Import tactics.

From iris.base_logic.lib Require Export invariants.

From self Require Import stdpp_extra.
From self.low.lib Require Import edge event.

Import uPred.

Import AACand.
Section definition.
  Context `{CMRA Σ} `{!AABaseG} `{invGS_gen HasNoLc Σ}.


  Definition excl_inv_name (eid_w : EID.t) := (nroot .@ (encode eid_w)).

  Definition excl_inv eid_w P : iProp Σ :=
   inv (excl_inv_name eid_w) (P eid_w ∨ ∃ eid_xr eid_xw, eid_w -{(Edge.Rf)}> eid_xr ∗ eid_xr -{(Edge.Lxsx)}> eid_xw ∗ Tok{ eid_xw }).

End definition.

Section rules.
  Context `{CMRA Σ} `{!AABaseG}.

  Lemma rmw_is_bij a b c:
    b ≠ c ->
    a -{Edge.Lxsx}> b -∗
    a -{Edge.Lxsx}> c -∗
    False.
  Proof.
    rewrite edge_eq /edge_def.
    iIntros (?) "[% (Hgr1&_&%Hwf&%)] [% (Hgr2&_&_&%)]".
    iDestruct (graph_agree_agree with "Hgr1 Hgr2") as %<-.
    simpl in *.
    rewrite /AACand.NMSWF.wf in Hwf.
    assert (AACand.NMSWF.lxsx_wf gr) as Hrmw_wf by naive_solver.
    clear Hwf.
    unfold NMSWF.lxsx_wf in Hrmw_wf.
    destruct_and ? Hrmw_wf.
    exfalso.
    specialize (H4 _ _ _ H2 H3). done.
  Qed.

  Lemma rmw_rmw eid_w eid_xw eid_xw' eid_xr eid_xr' :
    eid_xr ≠ eid_xr' ->
    eid_w -{Edge.Rf}> eid_xr -∗
    eid_xr -{Edge.Lxsx}> eid_xw -∗
    eid_w -{Edge.Rf}> eid_xr' -∗
    eid_xr' -{Edge.Lxsx}> eid_xw' -∗
    False.
  Proof.
    rewrite edge_eq /edge_def.
    iIntros (?) "[% (Hgr1&%Hcs&%Hwf&%)] [% (Hgr2&_&_&%)] [% (Hgr3&_&_&%)] [% (Hgr4&_&_&%)]".
    iDestruct (graph_agree_agree with "Hgr1 Hgr2") as %<-.
    iDestruct (graph_agree_agree with "Hgr1 Hgr3") as %<-.
    iDestruct (graph_agree_agree with "Hgr1 Hgr4") as %<-.
    simpl in *.
    iPureIntro.
    apply (Graph.rmw_rmw gr eid_w eid_xr eid_xr' eid_xw eid_xw'); assumption.
  Qed.

  Lemma excl_inv_open_succ `{!invGS_gen HasNoLc Σ} eid_w eid_xr eid_xw E P :
    ↑(excl_inv_name eid_w) ⊆ E ->
    (* FIXME: external rf or lob *)
    (Tok{ eid_xw } ∗ eid_w -{Edge.Rf}> eid_xr ∧ ⌜EID.tid eid_w ≠ EID.tid eid_xr⌝ ∗ eid_xr -{(Edge.Lxsx)}> eid_xw ∗
     excl_inv eid_w P)
       ={E, E ∖ ↑(excl_inv_name eid_w)}=∗ ▷ (P eid_w ∗ |={E ∖ ↑(excl_inv_name eid_w),E}=> emp).
  Proof.
    iIntros (Hsub) "(Htok & Hrf & %Hext & Hrwm & Hinv)".
    iInv "Hinv" as "P" "Hclose".
    iModIntro. iNext.
    iDestruct "P" as "[$ | (%eid_xr'&%eid_xw'&Hrf'&Hrmw&Htok')]".
    iApply ("Hclose" with "[-]").
    { iNext. iRight. iExists _,_. iFrame. }
    iDestruct (token_excl with "Htok Htok'") as %Hneq.
    destruct (decide (eid_xr = eid_xr')) as [<-|].
    {
      iExFalso. by iApply (rmw_is_bij with "Hrwm Hrmw").
    }
    {
      iExFalso. iApply (rmw_rmw with "Hrf Hrwm Hrf' Hrmw");done.
    }
  Qed.

  Lemma excl_inv_alloc `{!invGS_gen HasNoLc Σ} {E} eid_w P:
    P eid_w ={E}=∗ excl_inv eid_w P.
  Proof.
    iIntros "P".
    iDestruct (inv_alloc (nroot .@ (encode eid_w)) with "[P]") as ">Inv".
    2:{ iModIntro. rewrite /excl_inv. iFrame "Inv". }
    iNext. iLeft;done.
  Qed.

End rules.
