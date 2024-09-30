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

From iris.bi Require Import derived_laws.

From self.lang Require Import mm opsem.
From self.algebra Require Export base.
From self.low Require Export edge event.

Section def.
  Context `{CMRA Σ} `{!AABaseG}.

  (** Graph *)
  Import AACandExec.

  Definition global_interp (gs : GlobalState.t) :=
    (* agree RA for the graph, we simply put it in every graph assertion *)
    ("Hgr_ag" ∷ graph_agree gs.(GlobalState.gs_graph) ∗
    (* agree RA for the instruction table, similar as above *)
    "Hinstr_ag" ∷ instr_table_agree gs.(GlobalState.gs_gimem))%I.

End def.

Lemma graph_agree_alloc `{CMRA Σ} `{!AABaseInG} gr:
  ⊢ |==> ∃ GN, own GN ((to_agree gr) : (agreeR (leibnizO Graph.t))).
Proof.
  iDestruct (own_alloc (to_agree gr)) as ">[% ?]". done.
  iModIntro. iExists _. iFrame.
Qed.

Lemma instr_table_agree_alloc `{CMRA Σ} `{!AABaseInG} gi:
  ⊢ |==> ∃ GN, own GN (to_agree (gi: gmapO Addr (leibnizO Instruction))).
Proof.
  iDestruct (own_alloc (to_agree gi)) as ">[% ?]". done.
  iModIntro. iExists _. iFrame.
Qed.

Section lemma.
  Context `{CMRA Σ}.
  Context `{!AABaseG}.

  Lemma instr_agree_Some gs a i:
    global_interp gs -∗
    a ↦ᵢ i -∗
    ⌜gs.(GlobalState.gs_gimem) !! a = Some i⌝.
  Proof.
    iIntros "[_ Hinstr] Hi". rewrite instr_eq /instr_def.
    iDestruct "Hi" as "[% [Hag %Hlk]]".
    iDestruct (instr_table_agree_agree with "Hinstr Hag") as %->.
    done.
  Qed.

  Lemma instr_agree_None gs a:
    global_interp gs -∗
    a ↦ᵢ - -∗
    ⌜gs.(GlobalState.gs_gimem) !! a = None⌝.
  Proof.
    iIntros "[_ Hinstr] Hi". rewrite instr_eq /instr_def.
    iDestruct "Hi" as "[% [Hag %Hlk]]".
    iDestruct (instr_table_agree_agree with "Hinstr Hag") as %->.
    done.
  Qed.

  Lemma graph_edge_agree gs e1 e2 E:
    global_interp gs -∗
    e1 -{ E }> e2 -∗
    ⌜Edge.ef_edge_interp gs.(GlobalState.gs_graph) E e1 e2 ⌝.
  Proof.
    iIntros "[Hgr _] He". rewrite edge_eq /edge_def.
    iNamed "He". iDestruct (graph_agree_agree with "Hgr Hgr_interp_e") as %->.
    done.
  Qed.

  Lemma graph_event_agree gs e E:
    global_interp gs -∗
    e -{E}> E -∗
    ⌜ Event.event_interp gs.(GlobalState.gs_graph) E e⌝.
  Proof.
    iIntros "[Hgr _] He". rewrite event_eq /event_def.
    iNamed "He". iDestruct (graph_agree_agree with "Hgr Hgr_interp_e") as %->.
    done.
  Qed.

  Lemma graph_edge_agree_big_pred gs s e E:
    global_interp gs -∗
    ([∗ set] e1 ∈ s, e1 -{ E }> e) -∗
    [∗ set] e1 ∈ s, ⌜Edge.ef_edge_interp gs.(GlobalState.gs_graph) E e1 e⌝.
  Proof.
    iInduction s as [|??] "IH" using set_ind_L.
    iIntros. rewrite big_sepS_empty //.
    iIntros "Hgr Hs".
    rewrite !big_sepS_union; try set_solver.
    iDestruct "Hs" as "[He Hs]".
    rewrite !big_sepS_singleton.
    iDestruct (graph_edge_agree with "Hgr He") as %?.
    iSplit. done. iApply ("IH" with "Hgr Hs").
  Qed.

End lemma.
