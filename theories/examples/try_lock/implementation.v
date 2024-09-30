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
From iris.algebra Require Import excl.

From self.mid Require Import rules specialised_rules.
Require Import ISASem.SailArmInstTypes.

Import uPred.

Definition locked := (BV 64 1).
Definition unlocked := (BV 64 0).

Notation read_xcl reg addr := (ILoad AS_normal AV_exclusive reg (AEval addr)).
Notation write_xcl reg_res addr := (IStore AS_rel_or_acq AV_exclusive reg_res (AEval locked) (AEval addr)).
Notation write_rel reg_res addr := (IStore AS_rel_or_acq AV_plain reg_res (AEval unlocked) (AEval addr)).
Notation dmb_sy := (IDmb AAArch.Sy).
Notation bne reg addr:= (IBne (AEreg reg) addr).

(* (* The protocol at the given location is used to implement a try-lock *) *)
(* Class IsLockAt `{CMRA Σ} `{!AABaseG} `{!invGS_gen HasNoLc Σ} (a : Addr) (P : Eid -> iProp Σ) := *)
(*   { *)
(*     lock_prot_def val eid := (if bool_decide (val = unlocked) then excl_inv eid P *)
(*                               else *)
(*                                 if bool_decide (val = locked) then True *)
(*                                 else False)%I; *)
(*     (* lock_prot_spec : forall (val:Val) eid, prot a val eid ⊣⊢ lock_prot_def val eid ; *) *)
(*   }. *)

Definition lock_prot `{CMRA Σ} `{!AABaseG} `{!invGS_gen HasNoLc Σ} P val eid := (if bool_decide (val = unlocked) then excl_inv eid P
                              else
                                if bool_decide (val = locked) then True
                                else False)%I.

Local Instance lock_prot_persist `{CMRA Σ} `{!AABaseG} `{!invGS_gen HasNoLc Σ} P val eid: Persistent (lock_prot P val eid).
Proof.
  unfold lock_prot.
  case_bool_decide. apply _.
  case_bool_decide; apply _.
Qed.

Section implementation.
  Context `{AAIrisG} `{!AAThreadG} `{ThreadGN}.
  Context (lock_addr : Addr).
  Context `{P: Eid -> iProp Σ}.

  Context (inst_addr_start : Addr).
  Context (r1 r2 : RegName).

  (* the aquaire implmentation *)
  (* XXX: do we need release? *)
  Definition instrs_aquire : iProp Σ :=
    (inst_addr_start) ↦ᵢ read_xcl r1 lock_addr ∗
    (inst_addr_start `+Z` 4)%bv ↦ᵢ bne r1 (inst_addr_start `+Z` 16)%bv ∗
    (inst_addr_start `+Z` 8)%bv ↦ᵢ write_xcl r2 lock_addr ∗
    (inst_addr_start `+Z` 12)%bv ↦ᵢ dmb_sy.

  Definition acquire {tid Φ} P' q:
    None -{LPo}> -∗
    ∅ -{Ctrl}> -∗
    None -{Rmw}> -∗
    (∃ rv, r1 ↦ᵣ rv) -∗
    (∃ rv, r2 ↦ᵣ rv) -∗
    last_local_write tid lock_addr None -∗
    Prot[ lock_addr , q | lock_prot P ] -∗
    instrs_aquire -∗
    (∀ eid, P eid ==∗ P' eid) -∗
    (* continuation *)
    (
      (
        ∃ eid_xr,
        ∃ v1 v2 d, r1 ↦ᵣ (mk_regval v1 {[eid_xr]}) ∗ r2 ↦ᵣ (mk_regval v2 d) ∗
        ∃ po_src ctrl_src rmw_src, po_src -{LPo}> ∗ ctrl_src -{Ctrl}> ∗ rmw_src -{Rmw}> ∗
                   (
                     (⌜v1 = unlocked ∧ v2 = locked⌝) -∗
                     (
                       ⌜d = ∅⌝ ∗
                       ∃ eid_lw eid_xw eid_b,
                         ⌜po_src = (Some eid_b)⌝ ∗
                         ⌜ctrl_src = {[eid_xr]}⌝ ∗
                         ⌜rmw_src = Some eid_xr⌝ ∗
                         last_local_write tid lock_addr (Some eid_xw) ∗
                         eid_xw ↦ₐ (P' eid_lw ∗ Prot[ lock_addr , q | lock_prot P ]) ∗
                         eid_lw -{Edge.Ob}> eid_xw ∗
                         eid_b -{E}> (Event.B (AAArch.DMB AAArch.Sy)) ∗
                         eid_xw -{Edge.Po}> eid_b
                     )
                   )
      ) -∗
      WPi (LTSI.Normal , (inst_addr_start `+Z` 16)%bv) @ tid  {{ lts, Φ lts }}
    )-∗
    WPi (LTSI.Normal, inst_addr_start) @ tid
      {{ λ lts', Φ lts'}}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hrmw [% Hr1] [% Hr2] Hlocal Hprot Hinstrs Himpl Hcont".
    iDestruct "Hinstrs" as "(#? & #? & #? & #?)".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hpo_src Hctrl_src Hlocal Hprot Hrmw Hr1]").
    {
      iApply (iload_excl (λ eid_w v, lock_prot P v eid_w ∗ Prot[ lock_addr , q | lock_prot P ])%I ∅ ∅ with "[- Hprot]").
      iFrame "#∗".  rewrite big_sepM_empty big_sepS_empty //.

      iIntros. iSplitR.
      - iIntros "_ _". rewrite big_sepM_empty //.
      - iExists _,_,emp%I. iSplitL. iIntros "_";iFrame.
        iIntros (??) "_ _ _ _ _ Hp _ #H !>".
        iFrame "H Hp".
    }
    iIntros (?) "(->&(%&%&%&(#HRX&%&Hr1&Hna&_&#Hrfe&#Hext&Hpo_src&Hctrl_src&Hrmw&Hlocal)))".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hctrl_src Hr1]").
    {
      iApply (ibne {[r1 := {| reg_val := v; reg_dep := {[eid]} |}]} with "[] Hctrl_src [Hr1]");auto.
      - simpl. rewrite dom_singleton_L. set_solver +.
      - simpl. rewrite lookup_singleton /=. reflexivity.
      - rewrite big_sepM_singleton. done.
    }
    iIntros (?) "(Hr1&Hctrl_src&Hcases)".
    rewrite union_empty_r_L. rewrite map_fold_singleton /=. rewrite union_empty_r_L.
    rewrite big_sepM_singleton.

    (* two cases *)
    iDestruct "Hcases" as "[[-> ->]|[-> %Hlocked]]".
    {
      (* interesting case *)
      assert ((((inst_addr_start `+Z` 4) `+Z` 4)%bv) =((inst_addr_start `+Z` 8)%bv)) as ->; [bv_solve|].

      iApply sswpi_wpi. iApply (sswpi_mono with "[Hpo_src Hctrl_src Hlocal Hrmw Hr2 Hna Himpl]").
      {
        iDestruct (lpo_to_po with "Hpo_src") as "[Hpo_src #Hpo]".
        iApply (istore_rel_excl P P' (Prot[ lock_addr , q | lock_prot P ]) {[eid := (lock_prot P 0 eid' ∗ Prot[ lock_addr , q | lock_prot P ])%I]} _ _ r2 with "[- ]").
        {
          iFrame "#∗". rewrite !big_sepM_singleton. iFrame "#". iFrame.
          (* iIntros "Hlock". rewrite /lock_prot_def. *)
          (* case_bool_decide. done. case_bool_decide. rewrite /locked in H6. inversion H6. *)
          (* iExFalso. done. *)
        }
        {
          iExists _,_,emp%I. rewrite big_sepM_singleton. iSplitL. iIntros "[Hprot Hp]". iFrame.
          iIntros (?) "_ _ Hp".
          iApply fupd_mask_intro. set_solver +.
          iIntros "Hmod". iNext. iMod "Hmod". iModIntro. iFrame "Hp".
        }
      }
      simpl. iIntros (?) "(->&(%&Hr2&Hctrl&Hrmw&Hpost))".

      assert ((((inst_addr_start `+Z` 8) `+Z` 4)%bv) =((inst_addr_start `+Z` 12)%bv)) as ->; [bv_solve|].
      destruct b_succ.
      {
        iDestruct "Hpost" as "(%&HXW&%Htid&#Hpo&Hpo_src&Hlocal&Hna)".
        (* iMod (annot_split_iupd with "Hna") as "Hna Hna_p]". *)
        rewrite dom_singleton_L. rewrite big_sepS_singleton.

        iApply sswpi_wpi. iApply (sswpi_mono with "[Hpo_src]").
        {
          iApply idmb; [iFrame "#" | iExact "Hpo_src"].
        }

        iIntros (?) "(-> & %eid_dmb & #Hdmb & #Hpo' & Hpo_src)".
        simpl.
        assert ((((inst_addr_start `+Z` 12) `+Z` 4)%bv) =((inst_addr_start `+Z` 16)%bv)) as ->; [bv_solve|].

        iApply "Hcont".
        iExists eid, (BV 64 0), (bool_to_bv 64 true),∅. iFrame.
        iIntros "_". iSplit;first done.
        iExists eid', eid0, eid_dmb. iFrame. iFrame "#".
        do 3 (iSplit;first done).
        iDestruct "Hext" as "%".
        iDestruct (rfe_is_ob with "Hrfe") as "Hob"; [lia|].
        iDestruct (po_rel_is_lob with "Hpo [HXW]") as "Hob'".
        { iDestruct (event_node with "HXW") as "$". }
        iDestruct (lob_is_ob with "Hob'") as "Hob'".
        iApply (ob_trans with "Hob Hob'").
      }
      {
        iDestruct "Hpost" as "(Hpo_src&Hlocal&Hna)".

        iApply sswpi_wpi. iApply (sswpi_mono with "[Hpo_src]").
        {
          iApply idmb; [iFrame "#" | iExact "Hpo_src"].
        }

        iIntros (?) "(-> & %eid_dmb & #Hdmb & #Hpo & Hpo_src)".
        simpl.
        assert ((((inst_addr_start `+Z` 12) `+Z` 4)%bv) =((inst_addr_start `+Z` 16)%bv)) as ->; [bv_solve|].

        iApply "Hcont".
        iExists eid, (BV 64 0), (bool_to_bv 64 false), ∅.
        iFrame.
        iIntros "[_ %HH]".
        exfalso. simpl in HH. rewrite /locked in HH. simpl.
        destruct (bool_decide ((bv_unsigned (bool_to_bv 64 false)) = 0)) eqn:Heqn;rewrite HH /= in Heqn;done.
      }
    }

    iApply "Hcont". destruct rv0. iExists eid, v, _, _. iFrame.
    iIntros "[%HH _]". exfalso. simpl in HH. rewrite HH in Hlocked. rewrite /unlocked in Hlocked. contradiction.
  Qed.

  (* the release implmentation *)
  Definition instrs_release : iProp Σ :=
    (inst_addr_start) ↦ᵢ write_rel "r0" lock_addr.

  Definition release {tid o_po_src o_lw o_rmw ctrl_src Φ} po_priors lob_priors R q:
    po_priors ⊆ dom lob_priors ->
    o_po_src -{LPo}> -∗
    ([∗ set] po_src ∈ po_priors, po_src -{Po}>) -∗
    ctrl_src -{Ctrl}> -∗
    o_rmw -{Rmw}> -∗
    last_local_write tid lock_addr o_lw -∗
    instrs_release -∗
    ([∗ map] lob_pred ↦ P ∈ lob_priors, lob_pred ↦ₐ P) -∗
    (∃ Q, (([∗ map] _ ↦ P ∈ lob_priors, P) -∗ Prot[ lock_addr ,q | lock_prot P ] ∗ Q) ∗
      ∀ eid,
        (eid -{N}> Edge.W AS_rel_or_acq AV_plain -∗
         ([∗ set] po_prior ∈ po_priors, po_prior -{Edge.Po}> eid) -∗
         [∗ set] lob_pred ∈ (dom lob_priors ∖ po_priors), lob_pred -{Edge.Lob}> eid) ∗
        ((eid -{E}> (Event.W AS_rel_or_acq AV_plain lock_addr unlocked) ∗
             ([∗ set] po_src ∈ po_priors, po_src -{Edge.Po}> eid) ∗
             Q) ==∗ P eid ∗ R)
    ) -∗
    (* continuation *)
    (
      (
        ∃ eid, eid -{E}> (Event.W AS_rel_or_acq AV_plain lock_addr unlocked) ∗
               ⌜(EID.tid eid) = tid⌝ ∗
               Some eid -{LPo}> ∗
               ctrl_src -{Ctrl}> ∗
               last_local_write tid lock_addr (Some eid) ∗
               eid ↦ₐ (R ∗ Prot[ lock_addr ,q | lock_prot P ])
      ) -∗
      WPi (LTSI.Normal , (inst_addr_start `+Z` 4)%bv) @ tid  {{ lts, Φ lts }}
    )-∗
    WPi (LTSI.Normal, inst_addr_start) @ tid {{ λ lts, Φ lts}}.
  Proof.
    iIntros (Hsub) "Hpo_src Hpo_srcs Hctrl_src Hrmw Hlocal Hinstrs Hannot Himpl Hcont".
    iDestruct "Hinstrs" as "#?".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hpo_src Hpo_srcs Hctrl_src Hlocal Hrmw Hannot Himpl]").
    {
      iApply (istore_rel_raw (R ∗ Prot[ lock_addr ,q | lock_prot P ]) po_priors lob_priors _ _ Hsub with "[-]").
      iFrame "#∗".
      iDestruct "Himpl" as "[%[Hprot Himpl]]".
      iExists _,_,_. iFrame.

      iIntros (?).
      iDestruct ("Himpl" $! eid) as "[$ Himpl]".
      iIntros "HW _ Hpo Hp HP".
      iSpecialize ("Himpl" with "[$HW $Hpo $HP]").
      iMod "Himpl" as "[HP HR]".
      iDestruct (excl_inv_alloc eid P with "HP") as ">#Hexcl_inv".
      iModIntro. iFrame.
      rewrite /lock_prot. case_bool_decide; done.
    }
    iIntros (?) "(->&(%&#HE&?&?&?&?&?))".

    iApply "Hcont". iExists _. iFrame. iFrame "#".
  Qed.

End implementation.
