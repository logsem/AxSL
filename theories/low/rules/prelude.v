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

(* This file contains the helper tactics and lemmas that are useful for showing proof rules *)
From stdpp.bitvector Require Export definitions.
From SSCCommon Require Export COption CDestruct.

From iris.proofmode Require Export tactics.

Require Export ISASem.SailArmInstTypes.

From self.lang Require Export opsem.
From self.algebra Require Export base.
From self.low Require Export weakestpre instantiation instantiation_local.
From self.low.lib Require Export edge event.

(* NOTE: all modules are exported, so that other rule files only need to import this prelude module *)

Import uPred.

Section helpers.
  Context `{AAIrisG} `{Htg: !ThreadGNL}.

  (* spliting and merging node_annots *)
  Lemma annot_split_iupd n P Q:
    n ↦ₐ (P ∗ Q) -∗ |=i=> (n ↦ₐ P ∗ n ↦ₐ Q).
  Proof.
    rewrite interp_mod_eq /interp_mod_def.
    rewrite /iris.annot_interp /=. iIntros "H %". iNamed 1.
    iFrame "Hinterp_token". by iApply (annot_split with "H").
  Qed.

  Lemma annot_merge_iupd n P Q:
    n ↦ₐ P -∗ n ↦ₐ Q -∗ |=i=> (n ↦ₐ (P ∗ Q)).
  Proof.
    rewrite interp_mod_eq /interp_mod_def.
    rewrite /iris.annot_interp /=. iIntros "H1 H2 %". iNamed 1.
    iFrame "Hinterp_token". by iApply (annot_merge with "H1 H2").
  Qed.

  Lemma annot_wand_iupd n P Q:
    □(P -∗ Q) -∗ n ↦ₐ P -∗ |=i=> (n ↦ₐ Q).
  Proof.
    rewrite interp_mod_eq /interp_mod_def.
    rewrite /iris.annot_interp /=. iIntros "H1 H2 %". iNamed 1.
    iFrame "Hinterp_token". by iApply (annot_wand with "H1 H2").
  Qed.

  Import ThreadState.

  (** Helpers *)

  Lemma empty_na_splitting_wf lob_pred na :
    ⊢ (na_splitting_wf lob_pred na ∅ ∅ : iProp Σ).
  Proof.
    iStartProof. iSplit. rewrite dom_empty //. rewrite big_sepM2_empty //.
  Qed.

  Ltac alloc_graph_res :=
    iExists _;iFrame "Hgr_ag";iPureIntro; repeat (split;[done|]); try (eexists;split;[done|]);simpl;
    try (match goal with
         | [ HH : _ ⊆ (?f (GlobalState.gs_graph _)) |- _ ∈ (?f (GlobalState.gs_graph _))] =>
             apply HH; rewrite elem_of_gset_cprod; split; [done| set_solver +]
         end).
  Import AACand.

  Lemma last_local_write_co {gs} {tid : Tid} {pg ls addr ot_coi_pred} W:
    AACand.NMSWF.wf (GlobalState.gs_graph gs) ->
    AAConsistent.t (GlobalState.gs_graph gs) ->
    GlobalState.gs_graph gs !! (progress_to_node pg tid) = Some W ->
    AAInter.is_mem_write_req W ->
    AAInter.get_pa W = Some addr ->
    "Hinterp_global" ∷ global_interp gs -∗
    "Hinterp_local_lws" ∷ last_write_interp gs tid pg ls -∗
    "Hlocal"  ∷ last_local_write tid addr ot_coi_pred -∗
    from_option (λ eid_coi_pred : Eid, ⌜EID.tid eid_coi_pred = tid⌝ ∗ eid_coi_pred -{Edge.Co}> progress_to_node pg tid)
       emp ot_coi_pred.
  Proof.
    iIntros (?? Hgr_lk HWw HWa). repeat iNamed 1.
    destruct ot_coi_pred; last (simpl;iFrame;clear;done).
    iDestruct(last_write_interp_agree_Some with "Hinterp_local_lws Hlocal") as %(W' & Hlk_w'&?&?&Hco&?&_).
    simpl. iSplitR;first (iPureIntro;assumption). rewrite edge_eq /edge_def.
    iNamed "Hinterp_global". alloc_graph_res.
    apply Graph.wf_coi_inv;try assumption.
    eapply Graph.wf_loc_inv_writes2. repeat eexists;(try eassumption).

    clear -Hlk_w' H3 Hgr_lk HWw.
    set_unfold. naive_solver.
    rewrite -(progress_to_node_of_node tid t0);last done.
    rewrite -progress_lt_po; last done. repeat (split;try assumption).
    rewrite /progress_is_valid. rewrite progress_to_node_of_node;last done.
    set_solver + Hlk_w'.
    set_solver + Hgr_lk.
  Qed.

End helpers.

(** tactics *)
Ltac alloc_graph_res :=
  iExists _;iFrame "Hgr_ag";iPureIntro; repeat (split;[done|]); try (eexists;split;[done|]);simpl;
  try (match goal with
       | [ HH : _ ⊆ (?f (GlobalState.gs_graph _)) |- _ ∈ (?f (GlobalState.gs_graph _))] =>
           apply HH; rewrite elem_of_gset_cprod; split; [done| set_solver +]
       end).

Ltac inversion_step Hstep :=
  inversion Hstep;
  match goal with
  | [ Hreq_eq : ThreadState.reqs_done ?ts , Hreqs : ThreadState.ts_reqs ?ts = AAInter.Next _ _ |- _ ] =>
      rewrite /ThreadState.reqs_done in Hreq_eq; rewrite Hreqs in Hreq_eq; symmetry in Hreq_eq; inversion Hreq_eq
  | [ Hreq_eq : ThreadState.next_req_is ?ts ?req ?ctxt, Hreqs : ThreadState.ts_reqs ?ts = EmptyInterp |- _ ] =>
      rewrite /ThreadState.next_req_is in Hreq_eq; rewrite Hreqs in Hreq_eq; symmetry in Hreq_eq; inversion Hreq_eq
  | [ Hreq_eq : ThreadState.reqs_done ?ts , Hreqs : ThreadState.ts_reqs ?ts = EmptyInterp |- _ ] =>
      repeat match goal with
        | [ Hts : ?ts' = ts |- _ ] => subst ts'
        | [ Heq : ?x = ?x |- _] => clear Heq
        | [ Hlk : GlobalState.gs_graph ?gs !! ?e = Some ?E |- _] => rename Hlk into Hgr_lk
        end
  | [ Hreq_eq : ThreadState.next_req_is ?ts ?req ?ctxt, Hreqs : ThreadState.ts_reqs ?ts = AAInter.Next _ _ |- _ ] =>
      rewrite /ThreadState.next_req_is in Hreq_eq; rewrite Hreqs in Hreq_eq; cdestruct Hreq_eq;
      repeat match goal with
        | [ Hts : ?ts' = ts |- _ ] => subst ts'
        | [ Hts : _ = ?y |- _ ] => subst y
        | [ Hts : ?x = ?y |- _ ] => subst x
        | [ Hlk : GlobalState.gs_graph ?gs !! ?e = Some ?E |- _] => rename Hlk into Hgr_lk
        end
  end.

(* Ltac resolve_atomic := *)
(*       repeat (match goal with *)
(*           | [ HH : AACandExec.Candidate.kind_of_wreq_is_atomic (?f _ ?v _ _ _) = ?b |- _] => *)
(*               rewrite /f /AACandExec.Candidate.kind_of_wreq_is_atomic /AACandExec.Candidate.kind_of_wreq_P /= in HH *)
(*           | [ HH : bool_decide (?f _ = _) || bool_decide (?g _ = _) = _ |- _ ] => try (rewrite /f /g orb_false_iff /= in HH; destruct HH as [? ?]); *)
(*                                                                                  try (rewrite /f /g orb_true_iff /= in HH; destruct HH as [? | ?]) *)
(*           | [ HH : bool_decide (_ = _) = _ |- _ ] => case_bool_decide; try inversion HH; clear HH *)
(*           | [ HH : false = true |- _ ] => inversion HH *)
(*           | [ HH : true = false |- _ ] => inversion HH *)
(*           end). *)
