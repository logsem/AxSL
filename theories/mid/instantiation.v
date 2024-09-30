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

(** This file contains the instantiation of the middle-level logic,
 this is the file that all helper files import*)
From iris_named_props Require Export named_props.
From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Export agree gset lib.dfrac_agree.
From iris.base_logic.lib Require Export ghost_map.

From self.lang Require Import opsem.
From self.low Require Export instantiation instantiation_local.
From self.mid Require Export weakestpre.


Class AAThreadInG `{CMRA Σ} := {
  AAInGRegs :: ghost_mapG Σ RegName RegVal;
  AAInGCtrlSrc :: inG Σ (dfrac_agreeR (gsetO Eid));
  AAInGRmwPred :: inG Σ (dfrac_agreeR (optionO (leibnizO Eid)));
}.

Class ThreadGN `{AALocGNs : !ThreadGNL} := {
    AARegN : gname;
    AACtrlSrcN : gname;
    AARmwPredN : gname;
  }.

#[global] Arguments AARegN {_ _}.
#[global] Arguments AACtrlSrcN {_ _}.
#[global] Arguments AARmwPredN {_ _}.

Section genAAThreadG.
  Class AAThreadG `{CMRA Σ} :=
    GenAALThreadG{
        AAIn :: AAThreadInG;
      }.

  Definition AAThreadΣ : gFunctors :=
    #[
       ghost_mapΣ RegName RegVal;
       GFunctor (dfrac_agreeR (gsetO Eid));
       GFunctor (dfrac_agreeR (optionO (leibnizO Eid)))
      ].

  #[global] Instance subG_AAThreadpreG `{CMRA Σ}: subG AAThreadΣ Σ -> AAThreadInG.
  Proof. solve_inG. Qed.

End genAAThreadG.

Definition reg_mapsto_def `{CMRA Σ} `{!AAThreadG} `{ThreadGN} (r : RegName) (v: RegVal) : iProp Σ :=
   r ↪[AARegN] v.
Definition reg_mapsto_aux : seal (@reg_mapsto_def). by eexists. Qed.
Definition reg_mapsto := unseal reg_mapsto_aux.
Arguments reg_mapsto {Σ _ _ _ _}.
Definition reg_mapsto_eq : @reg_mapsto = @reg_mapsto_def :=
  seal_eq reg_mapsto_aux.
Notation "r ↦ᵣ v" := (reg_mapsto r v) (at level 20) : bi_scope.

Definition ctrl_src_half_def `{CMRA Σ} `{!AAThreadG} `{ThreadGN} (s: gset Eid) : iProp Σ :=
  ∃ s', ⌜s ⊆ s'⌝ ∗ own AACtrlSrcN (to_dfrac_agree (DfracOwn (1/2)%Qp) (s' : (gsetO Eid))).
Definition ctrl_src_half_aux : seal (@ctrl_src_half_def). by eexists. Qed.
Definition ctrl_src_half := unseal ctrl_src_half_aux.
Arguments ctrl_src_half {Σ _ _ _ _}.
Definition ctrl_src_half_eq : @ctrl_src_half = @ctrl_src_half_def :=
  seal_eq ctrl_src_half_aux.
Notation "s -{Ctrl}>" := (ctrl_src_half s) (at level 20) : bi_scope.

Definition rmw_pred_half_def `{CMRA Σ} `{!AAThreadG} `{ThreadGN} (me : option Eid) : iProp Σ :=
  own AARmwPredN (to_dfrac_agree (DfracOwn (1/2)%Qp) (me : (optionO (leibnizO Eid)))).

Definition rmw_pred_half_aux : seal (@rmw_pred_half_def). by eexists. Qed.
Definition rmw_pred_half := unseal rmw_pred_half_aux.
Arguments rmw_pred_half {Σ _ _ _ _}.
Definition rmw_pred_half_eq : @rmw_pred_half = @rmw_pred_half_def :=
  seal_eq rmw_pred_half_aux.

Notation "m -{Rmw}>" := (rmw_pred_half m) (at level 20) : bi_scope.

Section instantiation.
  Context `{CMRA Σ} `{!AAThreadG} `{ThreadGN}.

  Definition reg_interp regs := ghost_map_auth AARegN 1%Qp regs.

  Lemma reg_mapsto_ne {r r' v v'} :
    r ↦ᵣ v -∗
    r' ↦ᵣ v' -∗
    ⌜r ≠ r'⌝.
  Proof.
    rewrite reg_mapsto_eq /reg_mapsto_def.
    apply ghost_map_elem_ne.
  Qed.

  Lemma reg_interp_agree {regs r v} :
    reg_interp regs -∗
    r ↦ᵣ v -∗
    ⌜regs !! r = Some v⌝.
  Proof.
    rewrite reg_mapsto_eq /reg_mapsto_def.
    apply ghost_map_lookup.
  Qed.

  Lemma reg_interp_agree_big {regs regs'} :
    reg_interp regs -∗
    ([∗ map] r ↦ v∈ regs', r ↦ᵣ v) -∗
    ⌜regs' ⊆ regs⌝.
  Proof.
    rewrite reg_mapsto_eq /reg_mapsto_def.
    apply ghost_map_lookup_big.
  Qed.

  Lemma reg_interp_update {regs r v} v' :
    reg_interp regs -∗
    r ↦ᵣ v ==∗
    reg_interp (<[r := v']> regs) ∗ r ↦ᵣ v'.
  Proof.
    rewrite reg_mapsto_eq /reg_mapsto_def.
    apply ghost_map_update.
  Qed.

  Definition ctrl_srcs_interp (s: gsetO Eid) := own AACtrlSrcN (to_dfrac_agree (DfracOwn (1/2)%Qp) s).

  Lemma ctrl_srcs_interp_agree {s s'} :
    ctrl_srcs_interp s -∗
    s' -{Ctrl}> -∗
    ⌜s' ⊆ s⌝.
  Proof.
    rewrite ctrl_src_half_eq /ctrl_src_half_def.
    iIntros "H1 [% [%Hsub H2]]".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    rewrite dfrac_agree_op_valid_L in Hvalid.
    destruct Hvalid as [_ ->]. done.
  Qed.

  Lemma ctrl_srcs_interp_union {s s'} s'' :
    ctrl_srcs_interp s -∗
    s' -{Ctrl}> ==∗
    ctrl_srcs_interp (s'' ∪ s) ∗ (s'' ∪ s') -{Ctrl}>.
  Proof.
    iIntros "H1 H2".
    iDestruct (ctrl_srcs_interp_agree with "H1 H2") as %Hsub.
    rewrite ctrl_src_half_eq /ctrl_src_half_def.
    iDestruct "H2" as "[% [%Hsub' H2]]".
    iDestruct (own_update with "[H1 H2]") as ">H".
    2:{ iCombine "H1 H2" as "H". iFrame. }
    apply (dfrac_agree_update_2 _ _ _ _ (s'' ∪ s)). rewrite dfrac_op_own.
    f_equal. apply (bool_decide_unpack _). by compute.
    rewrite own_op. iDestruct "H" as "[? ?]".
    iModIntro. iFrame.
    iPureIntro. set_solver + Hsub.
  Qed.

  Definition rmw_pred_interp (m : optionO (leibnizO Eid)) := own AARmwPredN (to_dfrac_agree (DfracOwn (1/2)%Qp) m).

  Lemma rmw_pred_interp_agree {m m'} :
    rmw_pred_interp m -∗
    m' -{Rmw}> -∗
    ⌜m = m'⌝.
  Proof.
    rewrite rmw_pred_half_eq /rmw_pred_half_def.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    rewrite dfrac_agree_op_valid_L in Hvalid.
    destruct Hvalid as [_ ->]. done.
  Qed.

  Lemma rmw_pred_interp_update {m m'} m'' :
    rmw_pred_interp m -∗
    m' -{Rmw}> ==∗
    rmw_pred_interp m'' ∗ m'' -{Rmw}>.
  Proof.
    iIntros "H1 H2".
    iDestruct (rmw_pred_interp_agree with "H1 H2") as %->.
    rewrite rmw_pred_half_eq /rmw_pred_half_def.
    iDestruct (own_update with "[H1 H2]") as ">H".
    2:{ iCombine "H1 H2" as "H". iFrame. }
    apply (dfrac_agree_update_2 _ _ _ _ m''). rewrite dfrac_op_own.
    f_equal. apply (bool_decide_unpack _). by compute.
    rewrite own_op. iDestruct "H" as "[? ?]".
    iModIntro. iFrame.
  Qed.

  Definition thread_local_interp (ts : ThreadState.t) : iProp Σ :=
    "Hinterp_reg" ∷ reg_interp ts.(ThreadState.ts_regs) ∗
    "[% Hinterp_pc]" ∷ (∃ w, RNPC ↦ᵣ (mk_regval w ∅)) ∗
    "Hinterp_ctrl" ∷ ctrl_srcs_interp ts.(ThreadState.ts_ctrl_srcs) ∗
    "Hinterp_rmw" ∷ rmw_pred_interp ts.(ThreadState.ts_rmw_pred).

  Definition ready_for_next_ins_at (w : Addr) (ts : ThreadState.t) : Prop :=
    ts.(ThreadState.ts_reqs) = EmptyInterp ∧
    ts.(ThreadState.ts_regs) !! RNPC = Some (mk_regval w ∅).

End instantiation.


Lemma thread_local_interp_alloc `{CMRA Σ} `{!AAThreadG} (HGNL: ThreadGNL) (ts : ThreadState.t):
  (∃ w, ts.(ThreadState.ts_regs) !! RNPC  = Some (mk_regval w ∅)) ->
  ⊢ |==> ∃ `(!ThreadGN), thread_local_interp ts ∗
                        ([∗ map] r ↦ rv ∈ (delete (RNPC) ts.(ThreadState.ts_regs)), r ↦ᵣ rv) ∗
                        ts.(ThreadState.ts_ctrl_srcs) -{Ctrl}> ∗
                        ts.(ThreadState.ts_rmw_pred) -{Rmw}>.
Proof.
  iIntros ([? Hpc]).
  iMod (ghost_map_alloc ts.(ThreadState.ts_regs)) as "[%RN [Hinterp_reg Hregs]]".
  iMod (own_alloc ((to_dfrac_agree ((DfracOwn (1/2)%Qp) ⋅ (DfracOwn (1/2))%Qp) ts.(ThreadState.ts_ctrl_srcs)))) as "[%CN Hinterp_ctrl]". done.
  rewrite dfrac_agree_op. rewrite own_op. iDestruct "Hinterp_ctrl" as "[Hinterp_ctrl Hinterp_ctrl']".
  iMod (own_alloc ((to_dfrac_agree ((DfracOwn (1/2)%Qp) ⋅ (DfracOwn (1/2))%Qp) (ts.(ThreadState.ts_rmw_pred) : optionO (leibnizO Eid))))) as "[%WN Hinterp_rmw]". done.
  rewrite dfrac_agree_op. rewrite own_op. iDestruct "Hinterp_rmw" as "[Hinterp_rmw Hinterp_rmw']".
  iModIntro.
  iExists (Build_ThreadGN HGNL RN CN WN).
  iFrame. rewrite rmw_pred_half_eq ctrl_src_half_eq. iFrame.
  rewrite big_sepM_delete;last exact Hpc. iDestruct "Hregs" as "[Hpc Hregs]".
  rewrite reg_mapsto_eq. iFrame. done.
Qed.

(* Instantiation of mid-level logic *)
#[global] Instance instantiation_irisGInst `{AAThreadG} `{ThreadGN}
    : irisGInst := {
    inst_thread_interp := thread_local_interp;
    inst_addr_is := ready_for_next_ins_at;
  }.

Lemma inst_post_lifting_lifting `{AAIrisG} tid Φ (addr: Addr) annot :
  set_Forall (λ e, (EID.tid e) = tid) (dom annot) ->
  ([∗ map] e ↦ P ∈ annot, e ↦ₐ P) -∗
  (([∗ map] _ ↦ P ∈ annot, P) ==∗ Φ (LTSI.Done, addr)) -∗
  inst_post_lifting tid addr Φ.
Proof.
  iIntros (Hdom) "Hannot Himp". iIntros (?) "[Hinterp ?]".
  iDestruct (annot_agree_big with "Hinterp Hannot") as "[%Hsub #Hag]".
  iModIntro. iSplitR "Himp Hannot". iFrame.
  iIntros "All".
  iApply "Himp". iApply big_sepM_later_2.
  iClear "Hannot".
  iInduction annot as [|i x Hlkm H' ] "IH" using map_ind forall (na Hsub). done.
  rewrite big_sepM_insert;last done.
  rewrite dom_insert_L in Hdom. assert (is_Some(na !! i)) as [? Hlk].
  apply elem_of_dom. set_solver.
  (* iDestruct (big_sepM2_dom with "Hag") as %Hdom'. *)
  (* assert (is_Some(m'' !! i) ) as [? Hlk'']. *)
  (* apply elem_of_dom. set_solver + Hdom'. *)
  (* rewrite -(insert_delete m'' i x1);last done. *)
  rewrite big_sepM_insert. 2:done.
  rewrite Hlk /=.
  rewrite -(insert_delete na i x0);last done.
  iDestruct (big_sepM_insert with "All") as "[H All]".
  apply lookup_delete_None;left;done.
  case_bool_decide.
  2:{ specialize (Hdom i). ospecialize (Hdom _). set_solver +. done. }
  iDestruct "Hag" as "[Hag1 Hag]".
  iSplitL "H".
  iNext. iApply "Hag1". done. (* ("Hag1" with "H") as "[$ _]". *)
  iApply ("IH" with "[] [] [Hag] All").
  iPureIntro. apply set_Forall_union_inv_2 in Hdom. done.
  iPureIntro. rewrite dom_delete_L. apply elem_of_dom_2 in Hlk. apply not_elem_of_dom_2 in H'. set_solver.
  iModIntro.
  iApply (big_sepM_impl with "Hag").
  iModIntro. iIntros (?? Hlkm').
  destruct (decide (i = k)). subst k.
  (* rewrite lookup_delete_Some in Hlkdm. destruct Hlkdm;done. *)
  rewrite lookup_delete /=. iIntros "_";done.
  rewrite lookup_delete_ne //.
  rewrite insert_delete //.
  iApply bi.wand_refl.
Qed.
