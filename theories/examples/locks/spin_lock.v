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
From iris.algebra Require Import excl.

From self.mid Require Import rules specialised_rules.
Require Import ISASem.SailArmInstTypes.

Import uPred.

Definition locked := (BV 64 1).
Definition unlocked := (BV 64 0).

Notation ldaxr reg addr := (ILoad AV_exclusive AS_rel_or_acq reg (AEval addr)).
Notation stxr reg_res addr val := (IStore AV_exclusive AS_normal reg_res (AEval val) (AEval addr)).
Notation stlr reg_res addr val := (IStore AV_plain AS_rel_or_acq reg_res (AEval val) (AEval addr)).
(* Notation write_xcl reg_res addr := (IStore AV_exclusive AS_rel_or_acq reg_res (AEval locked) (AEval addr)). *)
Notation dmb_sy := (IBarrier BKsy).
Notation bnz reg addr:= (IBne (AEreg reg) addr).
Notation bz reg addr:= (IBne (AEbinop AOminus (AEreg reg)  (AEval (BV _ 1))) addr).

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

(* https://github.com/ARM-software/arm-trusted-firmware/blob/master/lib/locks/exclusive/aarch64/spinlock.S#L52C1-L60C5 *)
  (* l1:	ldaxr	w1, [x0] *)
  (* 	cbnz	w1, l1 *)
  (* 	stxr	w1, w2, [x0] *)
  (* 	cbnz	w1, l1 *)

  (* XXX: do we need release? *)
  Definition instrs_aquire : iProp Σ :=
    (inst_addr_start) ↦ᵢ ldaxr r1 lock_addr ∗
    (inst_addr_start `+Z` 4)%bv ↦ᵢ bnz r1 (inst_addr_start)%bv ∗
    (inst_addr_start `+Z` 8)%bv ↦ᵢ stxr r2 lock_addr locked ∗
    (inst_addr_start `+Z` 12)%bv ↦ᵢ bz r2 (inst_addr_start)%bv.

  Definition acquired P : iProp Σ :=
    (∃ eid_unlock eid_lx eid_sx, eid_lx -{Po}> ∗
                                 eid_unlock -{Edge.Rf}> eid_lx ∗ eid_lx -{Edge.Lxsx}> eid_sx ∗ Tok{ eid_sx } ∗
                           eid_lx ↦ₐ (lock_prot P unlocked eid_unlock))%I.

  Definition acquire {tid Φ} ctrl_src rmw_src po_src:
    po_src -{LPo}> -∗
    ctrl_src -{Ctrl}> -∗
    rmw_src -{Rmw}> -∗
    (∃ rv, r1 ↦ᵣ rv) -∗
    (∃ rv, r2 ↦ᵣ rv) -∗
    last_local_write tid lock_addr None -∗
    『lock_addr , □ | lock_prot P』 -∗
    instrs_aquire -∗
    (* continuation *)
    (
      (
        ∃ v1 v2 , r1 ↦ᵣ v1 ∗ r2 ↦ᵣ v2 ∗
        ∃ eid_sx,
          (Some eid_sx) -{LPo}> ∗ (∃ rmw_src, rmw_src -{Rmw}>) ∗ (∃ ctrl_src,  ctrl_src -{Ctrl}>) ∗
          last_local_write tid lock_addr (Some eid_sx) ∗
          acquired P
      ) -∗
      WPi (LTSI.Normal , (inst_addr_start `+Z` 16)%bv) @ tid  {{ lts, Φ lts }}
    )-∗
    WPi (LTSI.Normal, inst_addr_start) @ tid
      {{ λ lts', Φ lts'}}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hrmw [% Hr1] [% Hr2] Hlocal #Hprot Hinstrs Hcont".
    iDestruct "Hinstrs" as "(#? & #? & #? & #?)".
    iLöb as "IH" forall (rv rv0 rmw_src ctrl_src po_src).

    (** * LDAXR *)
    iApply sswpi_wpi.
    iApply (iload_excl (λ eid_w v, lock_prot P v eid_w)%I ∅ ∅ with "[$Hpo_src $Hctrl_src $Hlocal Hprot $Hrmw $Hr1]").
    iFrame "#". rewrite big_sepM_empty big_sepS_empty.
    iSplit;first done. iSplit;first done.
    iIntros. iSplitR.
    iIntros "_ _". rewrite big_sepM_empty //.
    iExists _,_,emp%I. iSplitL. iIntros "_";iFrame "#".
    iIntros (??) "_ _ _ _ _ Hp _ #H !>".
    iFrame "H Hp".

    iNext. iIntros (???) "(#HRX&%&Hr1&Hna&_&#Hrfe&#Hext&Hpo_src&Hctrl_src&Hrmw&Hlocal)".

    (** * BNZ *)
    iApply sswpi_wpi.
    iApply (ibne {[r1 := {| reg_val := v; reg_dep := {[eid]} |}]} with "[$Hctrl_src Hr1]");auto.
    3: iFrame "#".
    simpl. rewrite dom_singleton_L. set_solver +.
    simpl. rewrite lookup_singleton /=. reflexivity.
    rewrite big_sepM_singleton. done.

    iNext. iIntros (?) "(Hr1&Hctrl_src&Hcases)".
    rewrite map_fold_singleton /=. rewrite union_empty_r_L. rewrite big_sepM_singleton.

    (* two cases *)
    iDestruct "Hcases" as "[[-> ->]|[-> %Hlocked]]".
    2:{
      (* the lock is still locked, loop back *)
      iApply ("IH" with "Hpo_src Hctrl_src Hrmw Hr1 Hr2 Hlocal").
      done.
    }

    (* the lock is unlocked, try to acquire it *)
    assert ((((inst_addr_start `+Z` 4) `+Z` 4)%bv) =((inst_addr_start `+Z` 8)%bv)) as ->.
    { apply pa_addZ_assoc. }

    (** * STXR *)
    iApply sswpi_wpi.
    iDestruct (lpo_to_po with "Hpo_src") as "[Hpo_src #Hpo]".

    iDestruct (annot_wand_iupd _ _ ( lock_prot P 0 eid' ∗ emp)%I with "[] Hna") as ">Hna".
    { iModIntro. iIntros "$". }
    iDestruct (annot_split_iupd with "Hna") as ">[Hna Hna_emp]".

    iApply (istore_excl (λ _, emp%I) emp _ _ r2 with "[Hpo_src Hctrl_src Hlocal Hrmw Hr2 Hna_emp]").
    (* rewrite !big_sepM_singleton. *)
    iFrame "#". iFrame.

    iExists emp%I.
    iSplitL. iIntros "$Hp".
    iIntros (?) "_ _ _ _".
    iApply fupd_mask_intro. set_solver +.
    iIntros "Hmod". iNext. iMod "Hmod". iModIntro. done.

    simpl. iNext. iIntros (?) "(Hr2&Hctrl&Hrmw&Hpost)".

    assert ((((inst_addr_start `+Z` 8) `+Z` 4)%bv) =((inst_addr_start `+Z` 12)%bv)) as ->.
    { apply pa_addZ_assoc. }

    iApply sswpi_wpi.
    iApply (ibne {[r2 := {| reg_val := bool_to_bv 64 b_succ; reg_dep := ∅ |}]} with "[$Hctrl Hr2]");auto.
    3: iFrame "#".
    simpl. rewrite dom_singleton_L. set_solver +.
    simpl. rewrite lookup_singleton /=. reflexivity.
    rewrite big_sepM_singleton. done.

    iNext. iIntros (?) "(Hr2&Hctrl_src&%Hcases)".
    rewrite map_fold_singleton /=.
    rewrite (big_sepM_singleton _ r2).
    rewrite 2!union_empty_l_L.

    (* two cases *)
    destruct b_succ.
    2:{
      (* store exclusive failed *)
      iDestruct "Hpost" as "(Hpo_src&Hlocal&_)".

        destruct Hcases as [[-> HFalse] | [-> Hbv]].
        {
          exfalso.
          apply bv_eq in HFalse.
          rewrite bv_sub_unsigned in HFalse.
          rewrite bool_to_bv_unsigned // in HFalse.
        }

      (* loop back *)
      iApply ("IH" with "Hpo_src Hctrl_src Hrmw Hr1 Hr2 Hlocal").
      done.
    }
    {
      (* store exclusive is successful *)
      iDestruct "Hpost" as "(%&HXW&#Hlxsx&Hpo_src&Hlocal&_&Htok)".

      (* iMod (annot_split_iupd with "Hna") as "[Hna _]". *)
      (*   rewrite dom_singleton_L. rewrite big_sepS_singleton. *)

      destruct Hcases as [[-> Hbv] | [-> HFalse]].
      2:{
        exfalso.
        apply HFalse. apply bv_eq.
        rewrite bv_sub_unsigned.
        rewrite bool_to_bv_unsigned //.
      }

        assert ((((inst_addr_start `+Z` 12) `+Z` 4)%bv) =((inst_addr_start `+Z` 16)%bv)) as ->.
        { apply pa_addZ_assoc. }

        (* iApply sswpi_wpi. *)
        (* iApply (ibarrier with "[$Hpo_src $Hctrl_src]"). iFrame "#". *)

        (* iNext. iIntros "(%eid_dmb & #Hdmb & #Hpo'' & Hpo_src & _ & Hctrl)". simpl. *)

        (* assert ((((inst_addr_start `+Z` 16) `+Z` 4)%bv) =((inst_addr_start `+Z` 20)%bv)) as ->. *)
        (* { apply pa_addZ_assoc. } *)

        iApply "Hcont".
        (* iExists eid, (BV 64 0), (bool_to_bv 64 true),∅. *)
        iFrame. iFrame "#".
        (* iSplit;first done. *)
        (* iExists eid', eid0, eid_dmb. iFrame. iFrame "#". *)
        (* do 2 (iSplit;first done). *)

        (* iDestruct "Hext" as "%". *)
        (* iDestruct (rfe_is_ob with "Hrfe") as "Hob"; [lia|]. *)
        (* iDestruct (po_rel_is_lob with "Hpo' [HXW]") as "Hob'". *)
        (* { iDestruct (event_node with "HXW") as "$". } *)
        (* iDestruct (lob_is_ob with "Hob'") as "Hob'". *)
        (* iApply (ob_trans with "Hob Hob'"). *)
      }
  Qed.

  (* the release implmentation *)
  Definition instrs_release : iProp Σ :=
    (inst_addr_start) ↦ᵢ stlr "r0" lock_addr unlocked.

  Definition release {tid o_po_src o_lw o_rmw ctrl_src Φ} po_priors lob_priors R :
    po_priors ⊆ dom lob_priors ->
    o_po_src -{LPo}> -∗
    ([∗ set] po_src ∈ po_priors, po_src -{Po}>) -∗
    ctrl_src -{Ctrl}> -∗
    o_rmw -{Rmw}> -∗
    last_local_write tid lock_addr o_lw -∗
    instrs_release -∗
    ([∗ map] lob_pred ↦ P ∈ lob_priors, lob_pred ↦ₐ P) -∗
    (∃ Q, (([∗ map] _ ↦ P ∈ lob_priors, P) -∗ 『 lock_addr, □| lock_prot P 』 ∗ Q) ∗
      ∀ eid,
        (eid -{N}> Edge.W AV_plain AS_rel_or_acq -∗
         ([∗ set] po_prior ∈ po_priors, po_prior -{Edge.Po}> eid) -∗
         [∗ set] lob_pred ∈ (dom lob_priors ∖ po_priors), lob_pred -{Edge.Lob}> eid) ∗
        ((eid -{E}> (Event.W AV_plain AS_rel_or_acq lock_addr unlocked) ∗
             ([∗ set] po_src ∈ po_priors, po_src -{Edge.Po}> eid) ∗
             Q) ==∗ P eid ∗ R)
    ) -∗
    (* continuation *)
    (
      (
        ∃ eid, eid -{E}> (Event.W AV_plain AS_rel_or_acq lock_addr unlocked) ∗
               ⌜(AACand.EID.tid eid) = tid⌝ ∗
               Some eid -{LPo}> ∗
               ctrl_src -{Ctrl}> ∗
               last_local_write tid lock_addr (Some eid) ∗
               eid ↦ₐ R
      ) -∗
      WPi (LTSI.Normal , (inst_addr_start `+Z` 4)%bv) @ tid  {{ lts, Φ lts }}
    )-∗
    WPi (LTSI.Normal, inst_addr_start) @ tid {{ λ lts, Φ lts}}.
  Proof.
    iIntros (Hsub) "Hpo_src Hpo_srcs Hctrl_src Hrmw Hlocal Hinstrs Hannot Himpl Hcont".
    iDestruct "Hinstrs" as "#?".

    iApply sswpi_wpi.
    (* iApply (sswpi_mono with "[Hpo_src Hpo_srcs Hctrl_src Hlocal Hrmw Hannot Himpl]"). *)
    (* { *)
      iApply (istore_rel_raw R po_priors lob_priors _ _ Hsub with "[Hpo_src Hpo_srcs Hctrl_src Hlocal Hrmw Hannot Himpl]").
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

      iNext. iIntros (?) "(#HE&?&?&?&?&?)".

    iApply "Hcont". iExists _. iFrame. iFrame "#".
  Qed.

End implementation.
