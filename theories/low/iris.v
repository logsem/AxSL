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

(* This file contains the typeclasses which are the parameter of the low-level logic,
  the weakest precondition and adequacy can be instantiated by any instance of the typeclasses *)
From iris.base_logic.lib Require Export fancy_updates.

From self.lang Require Import opsem.
(* From self.low.lib Require Export annotations. *)
From self.algebra Require Export base.
Import uPred.

Notation mea Σ := (gmap Eid (iProp Σ)).
Notation sra Σ := (gmap Eid (mea Σ)).

Class irisG `{CMRA Σ} `{!invGS_gen HasNoLc Σ} := IrisG {
  (* Interpretation for tied assertions *)
  annot_interp : mea Σ -> iProp Σ;
  (* Interpretation for global instruction memory and graph *)
  gconst_interp : GlobalState.t -> iProp Σ;
  (* Logical state updated in ob *)
  ob_st : Type;
  (* Interpretation for [ob_st] *)
  (* NOTE: just handy to have access to graph in the implementation,
     but not necessary, can use [graph_agree] RA to hide it*)
  ob_st_interp : Graph.t -> ob_st -> gset Eid -> iProp Σ;
  (* (* we can split the interpretation for [e] from overall interpretation if [e] is not ob-ordered with the rest *) *)
  (* (* NOTE: used to establish FE for initial nodes in the adequacy proof *) *)
  (* ob_st_interp_split: (∀ gr σ e s, e ∉ s -> Graph.ob_pred_of gr e ## s -> Graph.ob_succ_of gr e ## s -> *)
  (*                                  ob_st_interp gr σ ({[e]} ∪ s) ⊣⊢ ob_st_interp gr σ {[e]} ∗ ob_st_interp gr σ s) *)
}.

Class irisGL `{CMRA Σ} := IrisGL {
  (* logical thread state *)
  log_ts_t : Type;
  (* local interpretation (for both 'physical' and logical ts), parametrised by tid *)
  local_interp : GlobalState.t -> Tid -> ThreadState.progress -> log_ts_t ->iProp Σ;
}.
