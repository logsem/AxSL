(* This file includes the exclusive invariant and specialised rules *)
(* From stdpp Require Import unstable.bitvector. *)

From iris.proofmode Require Import tactics.

From iris.base_logic.lib Require Export invariants.

From self Require Import stdpp_extra.
From self.low Require Import instantiation.
From self.lang Require Export mm.

Import uPred.

Section definition.
  Context `{AAIrisG}.

  Definition excl_inv_name (eid_w : EID.t) := (nroot .@ (encode eid_w)).

  Definition excl_inv eid_w P : iProp Σ :=
   inv (excl_inv_name eid_w) (P eid_w ∨ ∃ eid_xr eid_xw, eid_w -{(Edge.Rf)}> eid_xr ∗ eid_xr -{(Edge.Rmw)}> eid_xw ∗ Tok{ eid_xw }).

End definition.

Section rules.
  Context `{AABaseG Σ}.

  Lemma rmw_is_bij a b c:
    b ≠ c ->
    a -{Edge.Rmw}> b -∗
    a -{Edge.Rmw}> c -∗
    False.
  Proof.
    rewrite edge_eq /edge_def.
    iIntros (?) "[% (Hgr1&_&%Hwf&%)] [% (Hgr2&_&_&%)]".
    iDestruct (graph_agree_agree with "Hgr1 Hgr2") as %<-.
    simpl in *.
    rewrite /AACandExec.NMSWF.wf in Hwf.
    assert (AACandExec.NMSWF.rmw_wf gr) as Hrmw_wf by naive_solver.
    clear Hwf.
    rewrite CBool.bool_unfold in Hrmw_wf.
    destruct_and ? Hrmw_wf.
    exfalso.
    rewrite GRel.grel_functional_spec in H4.
    specialize (H4 _ _ _ H2 H3). done.
  Qed.

  Lemma rmw_rmw eid_w eid_xw eid_xw' eid_xr eid_xr' :
    eid_xr ≠ eid_xr' ->
    eid_w -{Edge.Rf}> eid_xr -∗
    eid_xr -{Edge.Rmw}> eid_xw -∗
    eid_w -{Edge.Rf}> eid_xr' -∗
    eid_xr' -{Edge.Rmw}> eid_xw' -∗
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
    (Tok{ eid_xw } ∗ eid_w -{Edge.Rf}> eid_xr ∧ ⌜EID.tid eid_w ≠ EID.tid eid_xr⌝ ∗ eid_xr -{(Edge.Rmw)}> eid_xw ∗
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
