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

(** This file contains the instantiation of the low-level logic,
 this is the file that all helper files import*)
From iris_named_props Require Export named_props.
From iris.bi Require Import derived_laws.

From self.lang Require Import mm opsem.
From self.algebra Require Export base.
From self.low Require Export edge event iris interp_mod annotations
  annot_res token_res global_res prot_res.

Section interp.
  Context `{CMRA Σ} `{!AABaseG}.

  Definition my_annot_interp (m : gmap Eid (iProp Σ)) : iProp Σ :=
    "Hinterp_annot" ∷ annot_interp m ∗
    "Hinterp_token" ∷ token_interp (dom m).

End interp.

Lemma interp_alloc `{CMRA Σ} `{!AABaseInG} gs prot_map:
  ⊢  |==> ∃ `(!AABaseG), my_annot_interp ∅ ∗
                         global_interp gs ∗
                         graph_agree (gs.(GlobalState.gs_graph)) ∗
                         instr_table_agree (gs.(GlobalState.gs_gimem)) ∗
                         prot_interp prot_map ∗ ([∗ map] x ↦ Φ ∈ prot_map, Prot[ x | Φ]).
Proof.
  iStartProof.
  rewrite /my_annot_interp.
  iDestruct (annot_interp_alloc) as ">[%g1 H1]".
  iDestruct (token_interp_alloc) as ">[%g2 H2]".
  iDestruct (graph_agree_alloc (GlobalState.gs_graph gs)) as ">[%g3 #H3]".
  iDestruct (instr_table_agree_alloc (GlobalState.gs_gimem gs)) as ">[%g4 #H4]".
  rewrite /prot_interp. rewrite prot_loc_eq /prot_loc_def.
  iDestruct (prot_interp_alloc prot_map) as ">[%g5 [% [H5 H6]]]".
  iDestruct (big_sepM2_impl _
               (λ x gn Φ, saved_prot_own gn Φ ∗ ∃ gn : gname, ghost_map_elem g5 x (DfracOwn 1) gn ∗ saved_prot_own gn Φ)%I
              with "H6 []") as "Himpl".
  { iModIntro. iIntros "%%%%% [H1 #H2]". iFrame "H2". iFrame. }
  iDestruct (big_sepM2_sep with "Himpl") as "[H6 Himpl]".
  iDestruct (big_sepM2_lookup_iff with "Himpl") as "%HH".
  iDestruct (big_sepM2_sepM (λ _ _, emp)%I) as "[HH _]". exact HH.
  iDestruct ("HH" with "[Himpl]") as "[_ H7]".
  iApply (big_sepM2_impl with "Himpl").
  { iModIntro. iIntros "%%%%% H". iSplitR;first done. iExact "H". }
  iModIntro.
  iExists (GenAABaseG Σ _ _ g3 g1 g4 g2 g5).
  iFrame. rewrite /global_interp.
  rewrite graph_agree_eq;iFrame.
  rewrite instr_table_agree_eq;iFrame.
  iFrame "#".
  iApply (big_sepM_impl with "H7").
  { iModIntro. iIntros "%%% H".
    rewrite prot_loc_gn_eq /prot_loc_gn_def. iFrame. }
Qed.

(* The final CMRA typeclass to be assumed *)
Class AAIrisG `{CMRA Σ} `{aairis_inv : !invGS_gen HasNoLc Σ} `{aairis_base : !AABaseG}:= {}.

(* Instantiation of low-level logic *)
#[global] Instance instantiation_irisG `{AAIrisG} : irisG := {
    annot_interp := my_annot_interp;
    gconst_interp := global_interp;
    ob_st := gmap Addr (ProtLoc Σ);
    ob_st_interp := prot_inv;
  }.
