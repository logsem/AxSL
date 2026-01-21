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

From iris.bi Require Import derived_laws.

From self.lang Require Import mm opsem.
From self.algebra Require Import base.
From self.low Require Import edge event annotations.


Section def.
  Context `{CMRA Σ} `{!AABaseG}.

  (** Graph *)
  Import AACand.
  (* Token for RMWs *)
  Definition token_interp (s : gset Eid) : iProp Σ :=
    own AARmwTokenN (● (GSet s)).

End def.

Lemma token_interp_alloc `{CMRA Σ} `{!AABaseInG}:
  ⊢ |==> ∃ GN, (own GN (● (GSet (∅ : gset Eid)))).
Proof.
  iDestruct (own_alloc (● (GSet (∅ : gset Eid)))) as ">[% ?]".
  apply auth_auth_valid. done.
  iModIntro. iExists _. iFrame.
Qed.

Section lemma.
  Context `{CMRA Σ}.
  Context `{!AABaseG}.

  Lemma token_alloc {gs tid pg na}:
    na_at_progress (GlobalState.gs_graph gs) tid pg na ∗
    token_interp (dom na) ==∗
    let eid := ThreadState.progress_to_node pg tid in
    token_interp ({[eid]} ∪ (dom na)) ∗ Tok{ eid }.
  Proof.
    iIntros "[Hnin Hint]".
    iDestruct (na_at_progress_not_elem_of with "Hnin") as %Hnin.
    rewrite rmw_token_eq /rmw_token_def /token_interp.
    rewrite -own_op. iApply (own_update with "Hint").
    apply auth_update_alloc.
    apply gset_disj_alloc_empty_local_update.
    set_solver + Hnin.
  Qed.

End lemma.
