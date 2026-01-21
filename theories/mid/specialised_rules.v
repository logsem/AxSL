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

(* This file contains some highly specialised mid-level proof rules (mostly for loads and stores) *)
From stdpp.bitvector Require Import definitions tactics.

From iris.proofmode Require Import tactics.

Require Import ISASem.SailArmInstTypes.

From self Require Import stdpp_extra.
From self.mid Require Export rules.

Import uPred.


Section rules.
  Context `{AAIrisG} `{!AAThreadG} `{ThreadGN}.
  Import ThreadState.
  Import AACand.

  Ltac load_ins :=
    rewrite sswpi_eq /sswpi_def;
    iIntros (?); iNamed 1; rewrite wpi_eq /wpi_def;
    iIntros (? [? ?]); repeat iNamed 1;
    iApply wp_sswp; iApply (sswp_strong_mono with "[Hinst]");
    first (iApply (reload with "[Hinst]");eauto); iIntros (? ->); simpl.

  (** specialised rules *)
  Lemma iload_excl {tid inst_addr kind_s ctrl rmw rv ot} R po_priors lob_priors addr reg:
    {SSi{{
           inst_addr ↦ᵢ (ILoad AV_exclusive kind_s reg (AEval addr)) ∗
           reg ↦ᵣ rv ∗
           ot -{LPo}> ∗
           ([∗ set] po_prior ∈ po_priors, po_prior -{Po}>) ∗
           ctrl -{Ctrl}> ∗
           rmw -{Rmw}> ∗
           last_local_write tid addr None ∗
           ([∗ map] lob_pred ↦ P ∈ lob_priors, lob_pred ↦ₐ P) ∗
           (∀ eid,
              (eid -{N}> (Edge.R AV_exclusive kind_s ) -∗
               ([∗ set] po_prior ∈ po_priors, po_prior -{(Edge.Po)}> eid) -∗
               [∗ map] lob_prior ↦ _ ∈ lob_priors, lob_prior -{Edge.Lob}> eid) ∗
              (∃ prot q Q,
                  (([∗ map] _ ↦ P ∈ lob_priors, P) -∗ 『addr, q | prot』 ∗ Q) ∗
                  ∀ eid' v,
                 eid -{E}> (Event.R AV_exclusive kind_s addr v) -∗
                 ⌜(EID.tid eid) = tid⌝ -∗
                 ([∗ set] po_prior ∈ po_priors, po_prior -{Edge.Po}> eid) -∗
                 (∃ kind_s_w kind_v_w, eid' -{E}> (Event.W kind_s_w kind_v_w addr v)) -∗
                 eid' -{Edge.Rf}> eid -∗
                 (『addr, q | prot』 -∗ Q -∗ prot v eid' ==∗ R eid' v ∗ (prot v eid'))
           ))
    }}}
     (LTSI.Normal,inst_addr) @ tid
    {{{ eid eid' v, RET (LTSI.Normal, (inst_addr `+Z` 4)%bv);
           eid -{E}> (Event.R AV_exclusive kind_s addr v) ∗
                           ⌜(EID.tid eid) = tid⌝ ∗
                           reg ↦ᵣ mk_regval v {[eid]} ∗
                           eid ↦ₐ (R eid' v) ∗
                           (∃ kind_s_w kind_v_w, eid' -{E}> (Event.W kind_s_w kind_v_w addr v)) ∗
                           eid' -{Edge.Rf}> eid ∗ ⌜EID.tid eid' ≠ EID.tid eid⌝ ∗
                           Some eid -{LPo}> ∗
                           ctrl -{Ctrl}> ∗
                           Some eid -{Rmw}> ∗
                           last_local_write tid addr None
      }}}.
  Proof.

    iIntros (Φ) "(Hinst & Hr & Hlpo & Hpo & Hctrl & Hrmw & Hlast_write &HP & Hfe) HΦ".

    rewrite sswpi_eq /sswpi_def;
    iIntros (?); iNamed 1; rewrite wpi_eq /wpi_def;
    iIntros (? [? ?]); repeat iNamed 1;
    iApply wp_sswp;
    iApply (reload with "[Hinst]");eauto;iNext;iIntros "_".

    iApply (mem_read_external _ (dom po_priors) lob_priors with "Hlpo Hctrl Hlast_write Hrmw [Hpo] [] HP [Hfe] [-Hinterp]") => //=.
    + set_solver.
    + iIntros (?). iDestruct ("Hfe" $! eid) as "[Hf He]". iSplitL "Hf".
    - iIntros "HN Hpo _ _". rewrite big_sepM_dom. iApply ("Hf" with "HN Hpo").
    - iDestruct "He" as "(%&%&%&?&He)". iFrame.
      iIntros (? eid_w) "(Hp & Q & (HE & [%Htid _] & Hpo & _ & _ & Hwrite & Hrf & _) & Hprot)".
      iApply (fupd_mask_intro _ ∅). { set_solver. }
      iIntros "M !>".
      iDestruct ("He" $! eid_w val with "HE [//] Hpo Hwrite Hrf Hp Q Hprot") as ">R".
      iMod "M" as "_". iModIntro. iExact "R".
    + simpl.
      iNext.
      iIntros (?) "Hinterp %Hpc_eq (% & % & % & [% %] & (Hread & [% %] & _ & _ & _ & Hwrite & Hrf & %Hext) & Hannot & Hpo & Hctrl & Hlast_local_write & Hrmw & ?)".

      iNamed "Hinterp".
      iApply wp_sswp.
      iApply reg_write;eauto.
      iNext. iIntros "_".
      iNamed "Hinterp". iDestruct (reg_interp_update with "Hinterp_reg Hr") as ">[Hinterp_reg Hr]".
      iDestruct (reg_mapsto_ne with "Hr Hinterp_pc") as %Hneq.

      iApply (inc_pc with "[-Hinterp_reg Hinterp_pc Hinterp_ctrl Hinterp_rmw]");auto.
      simpl. rewrite lookup_insert_ne //. rewrite Hpc_eq //.
      iIntros (? -> ? ?) "Hinterp". iApply ("Hcont" with "[-Hinterp]");auto.
      iApply ("HΦ" $!  eid eid_w val).
      iFrame.
      iPureIntro. split;lia.
      rewrite /= union_empty_l_L. rewrite H5 /=.
      rewrite union_empty_r_L. destruct eid;simpl in *;subst. iFrame.
  Qed.

  Lemma istore_excl {tid inst_addr ctrl kind_s po_src eid_w eid_xr res_ov} R_tied P_lx addr data reg_res:
    {SSi{{
    inst_addr ↦ᵢ (IStore AV_exclusive kind_s reg_res (AEval data) (AEval addr)) ∗
    reg_res ↦ᵣ res_ov ∗
    Some po_src -{LPo}> ∗
    (* ([∗ map] po_prior ↦ _ ∈ po_priors, po_prior -{Po}>) ∗ *)
    ctrl -{Ctrl}> ∗
    last_local_write tid addr None ∗
    Some eid_xr -{Rmw}> ∗
    (eid_w -{Edge.Rf}> eid_xr ∗ ⌜EID.tid eid_w ≠ EID.tid eid_xr⌝) ∗
    (eid_xr ↦ₐ P_lx) ∗
    (* (∀ eid, *)
    (*   (eid -{N}> (Edge.W AV_exclusive kind_s) -∗ eid_xr -{(Edge.Lxsx)}> eid -∗ *)
    (*  eid_xr -{Edge.Lob}> eid)) ∗ *)
    (
      ∃ prot q Q, (P_lx -∗ (『addr, q | prot』 ∗ Q)) ∗
      ∀ eid,
        (eid -{E}> (Event.W AV_exclusive kind_s addr data) -∗
             ⌜(EID.tid eid) = tid⌝ -∗
             『addr, q | prot』-∗
             Q
             ={⊤}[∅]▷=∗
             (R_tied eid) ∗ (prot data eid)))
    }}}
    (LTSI.Normal,inst_addr) @ tid
    {{{ b_succ, RET (LTSI.Normal, (inst_addr `+Z` 4)%bv);
             reg_res ↦ᵣ mk_regval (bool_to_bv 64 b_succ) ∅ ∗
             ctrl -{Ctrl}> ∗
             (Some eid_xr) -{Rmw}> ∗
             (* update lts' accordingly *)
             if b_succ then
               (* success *)
               ∃ eid, eid -{E}> (Event.W AV_exclusive kind_s addr data) ∗
                      (* ⌜(EID.tid eid) = tid⌝ ∗ *)
                      eid_xr -{(Edge.Lxsx)}> eid ∗
                      (* ([∗ set] po_prior ∈ dom lob_priors, po_prior -{Edge.Po}> eid) ∗ *)
                      Some eid -{LPo}> ∗
                      last_local_write tid addr (Some eid) ∗
                      eid ↦ₐ (R_tied eid) ∗
                      Tok{eid}
             else
               (* failure, things stay unchanged *)
               Some po_src -{LPo}> ∗
               last_local_write tid addr None ∗
               eid_xr ↦ₐ P_lx
      }}}.
  Proof.
    iIntros (Φ) "(Hinst & Hreg_res & Hlpo & Hctrl & Hlast_write & Hrmw & #Hw_rfe_xr & Hannot & Hfe) HΦ".

    rewrite sswpi_eq /sswpi_def;
    iIntros (?); iNamed 1; rewrite wpi_eq /wpi_def;
    iIntros (? [? ?]); repeat iNamed 1;
    iApply wp_sswp;
    iApply (reload with "[Hinst]");eauto;iNext;iIntros "_".

    iDestruct (lpo_to_po with "Hlpo") as "[Hlpo Hpo]".

    iApply (mem_write_xcl_Some R_tied emp%I {[po_src]} _ {[eid_xr := P_lx]} ∅ ∅ with
                "Hlpo [Hpo] Hctrl Hlast_write Hrmw [] [Hannot] [Hfe] [-Hinterp]");auto.
    + rewrite big_sepS_singleton //.
    + rewrite map_union_empty. rewrite big_sepM_empty //.
    + rewrite big_sepM_singleton //.
    + simpl. iIntros (?). iSplitR.
      - iIntros "#HE Hpo _ _ _ Hrmw".
        rewrite dom_singleton_L.
        rewrite !big_sepS_singleton.
        iApply (lxsx_is_lob);done.
      - iFrame.

        iSplit;first done.
        (* iSplitR; first done. *)
        iDestruct "Hfe" as "(%&%&%&HPexcl&Hfe)".

        iExists prot,q, Q.
        rewrite big_sepM_singleton.
        iFrame.
        (* iExists eid_w, *)
        (*           ((eid -{E}> Event.W AV_exclusive AS_rel_or_acq addr data ∗ *)
        (*             ⌜EID.tid eid = tid ∧ EID.iid eid = (iis_iid (ts_iis ts) + 1)%nat⌝ ∗ *)
        (*             ([∗ set] eid_po_src ∈ dom po_priors, eid_po_src -{Edge.Po}> eid) ∗ *)
        (*             ([∗ set] eid_ctrl_src ∈ ctrl, eid_ctrl_src -{Edge.Ctrl}> eid) ∗ *)
        (*             ([∗ set] eid_addr_src ∈ (map_fold (λ (_ : RegName) (dv : RegVal) (acc : gset Eid), reg_dep dv ∪ acc) ∅ ∅ ∪ ∅), eid_addr_src -{Edge.Addr}> eid) ∗ *)
        (*             ([∗ set] eid_data_src ∈ (map_fold (λ (_ : RegName) (dv : RegVal) (acc : gset Eid), reg_dep dv ∪ acc) ∅ ∅ ∪ ∅), eid_data_src -{Edge.Data}> eid) ∗ *)
        (*             emp  ∗ eid_xr -{Edge.Lxsx}> eid) ∗ 『addr, q | prot』 ∗ Q ∗ (∀ eid0 : Eid, R eid0 ==∗ R' eid0))%I, R. *)
        (* iSplitR "Hfe". *)

        iIntros "(_&Hprot&Q&HE&[%Htid _] &?&?&?&?&?&?)".
        iDestruct ("Hfe" with "HE [//] Hprot Q") as ">M".
        iModIntro.
        iModIntro. iMod "M" as "[Q $]".
        iModIntro.
        iExact "Q".
    + iNext.
      iIntros (?) "Hinterp %Hpc_eq (% & %Heq & HPost)";simpl. simpl in Hpc_eq.
      iNamed "Hinterp".
      iApply wp_sswp.
      iApply reg_write;eauto. rewrite Heq. done.
      iNamed "Hinterp".
      iNext. iIntros "_".
      iDestruct (reg_interp_update with "Hinterp_reg Hreg_res") as ">[Hinterp_reg Hreg_res]".
      iDestruct (reg_mapsto_ne with "Hreg_res Hinterp_pc") as %Hneq. simpl in Heq.

      iApply (inc_pc with "[-Hinterp_reg Hinterp_pc Hinterp_ctrl Hinterp_rmw]");auto.
      simpl. rewrite lookup_insert_ne //. rewrite Hpc_eq //.
      iIntros (? -> ? ?) "Hinterp". iApply ("Hcont" with "[-Hinterp]");auto.
      iApply ("HΦ" $! b_succ).
      iDestruct "HPost" as "($&$&HPost)".
      iSplitL "Hreg_res". iExact "Hreg_res".
      destruct b_succ.
      - iDestruct "HPost" as "[% ((?&[[? ?] (? & ? &?&?&?&?)])&HP&?&?&?)]".
      iExists eid. iFrame.
      - rewrite big_sepM_singleton.
        iDestruct "HPost" as "($&$&$&$)".
      - simpl. iFrame.
  Qed.

  (* Lemma istore_rel_excl {tid inst_addr ctrl ot eid_w eid_xr res_ov} R R' R'' po_priors addr data reg_res: *)
  (*   {SSi{{ *)
  (*   inst_addr ↦ᵢ (IStore AV_exclusive AS_rel_or_acq reg_res (AEval data) (AEval addr)) ∗ *)
  (*   reg_res ↦ᵣ res_ov ∗ *)
  (*   ot -{LPo}> ∗ *)
  (*   ([∗ map] po_prior ↦ _ ∈ po_priors, po_prior -{Po}>) ∗ *)
  (*   ctrl -{Ctrl}> ∗ *)
  (*   last_local_write tid addr None ∗ *)
  (*   Some eid_xr -{Rmw}> ∗ *)
  (*   (eid_w -{Edge.Rf}> eid_xr ∗ ⌜EID.tid eid_w ≠ EID.tid eid_xr⌝) ∗ *)
  (*   (∀ eid, R eid ==∗ R' eid) ∗ *)
  (*   ([∗ map] po_pred ↦ P ∈ po_priors, po_pred ↦ₐ P) ∗ *)
  (*   ( *)
  (*     ∃ prot q Q, *)
  (*                  (([∗ map] _ ↦ P ∈ po_priors, P) -∗ (『addr, q | prot』 ∗ Q ∗ excl_inv eid_w R)) ∗ *)
  (*     ∀ eid, *)
  (*       (eid -{E}> (Event.W AV_exclusive AS_rel_or_acq addr data) -∗ *)
  (*            ⌜(EID.tid eid) = tid⌝ -∗ *)
  (*            (* ([∗ map] po_prior ↦ _ ∈ po_priors, po_prior -{Edge.Po}> eid) -∗ *) *)
  (*            (* ([∗ map] _ ↦ P ∈ po_priors, P) -∗ *) *)
  (*            『addr, q | prot』-∗ *)
  (*            Q *)
  (*            ={⊤∖ ↑(excl_inv_name eid_w)}[∅]▷=∗ *)
  (*            R'' ∗ (prot data eid))) *)
  (*   }}} *)
  (*   (LTSI.Normal,inst_addr) @ tid *)
  (*   {{{ b_succ, RET (LTSI.Normal, (inst_addr `+Z` 4)%bv); *)
  (*            reg_res ↦ᵣ mk_regval (bool_to_bv 64 b_succ) ∅ ∗ *)
  (*            ctrl -{Ctrl}> ∗ *)
  (*            (Some eid_xr) -{Rmw}> ∗ *)
  (*            (* update lts' accordingly *) *)
  (*            if b_succ then *)
  (*              (* success *) *)
  (*              ∃ eid, eid -{E}> (Event.W AV_exclusive AS_rel_or_acq addr data) ∗ *)
  (*                     ⌜(EID.tid eid) = tid⌝ ∗ *)
  (*                     ([∗ set] po_prior ∈ dom po_priors, po_prior -{Edge.Po}> eid) ∗ *)
  (*                     Some eid -{LPo}> ∗ *)
  (*                     last_local_write tid addr (Some eid) ∗ *)
  (*                     eid ↦ₐ (R' eid_w ∗ R'') *)
  (*            else *)
  (*              (* failure, things stay unchanged *) *)
  (*              ot -{LPo}> ∗ *)
  (*              last_local_write tid addr None ∗ *)
  (*              ([∗ map] node ↦ annot ∈ po_priors, node ↦ₐ annot) ∗ *)
  (*              (∀ eid, R eid ==∗ R' eid) *)
  (*     }}}. *)
  (* Proof. *)
  (*   iIntros (Φ) "(Hinst & Hreg_res & Hlpo & Hpos & Hctrl & Hlast_write & Hrmw & #Hw_rfe_xr *)
  (*   & Himpl & Hannot & Hfe) HΦ". *)

  (*   rewrite sswpi_eq /sswpi_def; *)
  (*   iIntros (?); iNamed 1; rewrite wpi_eq /wpi_def; *)
  (*   iIntros (? [? ?]); repeat iNamed 1; *)
  (*   iApply wp_sswp; *)
  (*   iApply (reload with "[Hinst]");eauto;iNext;iIntros "_". *)

  (*   iApply (mem_write_xcl_Some_inv (∀ eid : Eid, R eid ==∗ R' eid)%I _ (dom po_priors) _ (po_priors) ∅ ∅ with *)
  (*               "Hlpo [Hpos] Hctrl Hlast_write Hrmw [] Hannot [Hfe Himpl] [-Hinterp]");auto. *)
  (*   + rewrite big_sepM_dom //. *)
  (*   + rewrite map_union_empty. rewrite big_sepM_empty //. *)
  (*   + simpl. iIntros (?). iSplitR. *)
  (*     - iIntros "#HE Hpo _ _ _ Hrmw". *)
  (*       iApply (big_sepS_impl with "Hpo"). *)
  (*       iModIntro. iIntros (? Hin) "Hpo". *)
  (*       iApply (po_rel_is_lob with "Hpo");auto. *)
  (*     - iFrame. *)
  (*       (* iSplitR; first done. *) *)
  (*       iDestruct "Hfe" as "(%&%&%&HPexcl&Hfe)". *)

  (*       iExists eid_w, *)
  (*                 ((eid -{E}> Event.W AV_exclusive AS_rel_or_acq addr data ∗ *)
  (*                   ⌜EID.tid eid = tid ∧ EID.iid eid = (iis_iid (ts_iis ts) + 1)%nat⌝ ∗ *)
  (*                   ([∗ set] eid_po_src ∈ dom po_priors, eid_po_src -{Edge.Po}> eid) ∗ *)
  (*                   ([∗ set] eid_ctrl_src ∈ ctrl, eid_ctrl_src -{Edge.Ctrl}> eid) ∗ *)
  (*                   ([∗ set] eid_addr_src ∈ (map_fold (λ (_ : RegName) (dv : RegVal) (acc : gset Eid), reg_dep dv ∪ acc) ∅ ∅ ∪ ∅), eid_addr_src -{Edge.Addr}> eid) ∗ *)
  (*                   ([∗ set] eid_data_src ∈ (map_fold (λ (_ : RegName) (dv : RegVal) (acc : gset Eid), reg_dep dv ∪ acc) ∅ ∅ ∪ ∅), eid_data_src -{Edge.Data}> eid) ∗ *)
  (*                   emp  ∗ eid_xr -{Edge.Lxsx}> eid) ∗ 『addr, q | prot』 ∗ Q ∗ (∀ eid0 : Eid, R eid0 ==∗ R' eid0))%I, R. *)
  (*       iExists prot,q. iFrame. *)
  (*       iSplitR "Hfe". *)

  (*       (* iSplitR "Hfe Himpl". *) *)
  (*       iIntros "[Himpl (#HG & [Q $]&Hp)]". *)
  (*       (* iDestruct ("HPexcl" with "Hannot") as "#Hexcl_inv". *) *)
  (*       iFrame. iFrame "#". *)
  (*       iIntros "([(#HE & [%Htid _] & (#Hpos & _)) [Hp [Q Himpl]]]& R)". *)
  (*       iDestruct ("Hfe" with "HE [//] Hp Q") as ">M". *)
  (*       iModIntro. iNext. iMod "M" as "[Q $]". *)
  (*       iDestruct ("Himpl" with "R") as ">R". iModIntro. *)
  (*       iCombine "R Q" as "R". iExact "R". *)
  (*   + iNext. *)
  (*     iIntros (?) "Hinterp %Hpc_eq (% & %Heq & HPost)";simpl. simpl in Hpc_eq. *)
  (*     iNamed "Hinterp". *)
  (*     iApply wp_sswp. *)
  (*     iApply reg_write;eauto. rewrite Heq. done. *)
  (*     iNamed "Hinterp". *)
  (*     iNext. iIntros "_". *)
  (*     iDestruct (reg_interp_update with "Hinterp_reg Hreg_res") as ">[Hinterp_reg Hreg_res]". *)
  (*     iDestruct (reg_mapsto_ne with "Hreg_res Hinterp_pc") as %Hneq. simpl in Heq. *)

  (*     iApply (inc_pc with "[-Hinterp_reg Hinterp_pc Hinterp_ctrl Hinterp_rmw]");auto. *)
  (*     simpl. rewrite lookup_insert_ne //. rewrite Hpc_eq //. *)
  (*     iIntros (? -> ? ?) "Hinterp". iApply ("Hcont" with "[-Hinterp]");auto. *)
  (*     iApply ("HΦ" $! b_succ). *)
  (*     iDestruct "HPost" as "($&$&HPost)". *)
  (*     iSplitL "Hreg_res". iExact "Hreg_res". *)
  (*     destruct b_succ. *)
  (*     - iDestruct "HPost" as "[% ((?&[[? ?] [? ?]])&HP&?&?)]". *)
  (*     iExists eid. iFrame. *)
  (*     - iDestruct "HPost" as "($&$&$&$)". *)
  (*     - simpl. iFrame. *)
  (* Qed. *)

  Lemma istore_pln_single_data {tid inst_addr ctrl po_prior} reg_data reg_res addr val addr_pred P:
    {SSi{{
           inst_addr ↦ᵢ (IStore AV_plain AS_normal reg_res (AEreg reg_data) (AEval addr)) ∗
           Some po_prior -{LPo}> ∗
           ctrl -{Ctrl}> ∗
           last_local_write tid addr None ∗
           reg_data ↦ᵣ (mk_regval val {[addr_pred]}) ∗
           addr_pred ↦ₐ P ∗
           (
             ∃ prot q Q,
               (P -∗ (『addr, q | prot』 ∗ Q)) ∗
               ∀ eid, eid -{E}> (Event.W AV_plain AS_normal addr val) -∗
                      ⌜EID.tid eid = tid⌝ -∗
                      po_prior -{Edge.Po}> eid -∗
                      addr_pred -{Edge.Data}> eid -∗
                      『addr, q | prot』 -∗
                      Q -∗
                      (prot val eid)
           )
    }}}
    (* Need to know about the data write here, or write the implication *)
    (LTSI.Normal,inst_addr) @ tid
    {{{ eid, RET (LTSI.Normal, (inst_addr `+Z` 4)%bv);
           reg_data ↦ᵣ (mk_regval val {[addr_pred]}) ∗
            eid -{E}> (Event.W AV_plain AS_normal addr val) ∗
                  ⌜EID.tid eid = tid ⌝ ∗
                  Some eid -{LPo}> ∗
                  last_local_write tid addr (Some eid) ∗
                  ctrl -{Ctrl}>
     }}}.
  Proof.
    iIntros (Φ) "(Hinst & Hpo & Hctrl & Hlast_write & Hreg & Hna & Hprot) HΦ".

    rewrite sswpi_eq /sswpi_def;
    iIntros (?); iNamed 1; rewrite wpi_eq /wpi_def;
    iIntros (? [? ?]); repeat iNamed 1;
    iApply wp_sswp;
    iApply (reload with "[Hinst]");eauto;iNext;iIntros "_".

    iDestruct (lpo_to_po with "Hpo") as "[Hlpo #Hpo]".

    iApply wp_sswp.
    iNamed "Hinterp". iDestruct (reg_interp_agree with "Hinterp_reg Hreg") as %Hreg.
    iApply (reg_read);eauto. simpl.
    iNext. iIntros "_".

    iApply (mem_write_non_xcl _ {[po_prior]} {[addr_pred := P]} {[reg_data := _]} ∅
             with "Hlpo Hctrl Hlast_write [] [Hreg] [Hna] [Hprot] [-Hinterp_reg Hinterp_ctrl Hinterp_rmw Hinterp_pc]").
    + simpl. reflexivity.
    + done.
    + rewrite map_subseteq_spec.
      intros ?? Hlk. rewrite lookup_intersection in Hlk.
      rewrite lookup_empty in Hlk. inversion Hlk.
    + simpl. set_solver +.
    + rewrite dom_singleton_L. simpl. set_solver +.
    + by iApply big_sepS_singleton.
    + rewrite map_empty_union.
      by iApply big_sepM_singleton.
    + by iApply big_sepM_singleton.
    + iIntros (?).
      iSplitR.
    - iIntros "_ _ _ _ ?".
      simpl. rewrite map_fold_singleton /=. rewrite 2!union_empty_r_L.
      rewrite dom_singleton_L. rewrite 2!big_sepS_singleton.
      by iApply data_is_lob.
    - iDestruct "Hprot" as "(%&%&%&Himpl&Hprot)".
      iExists prot, q, Q.
      rewrite big_sepM_singleton. iFrame.
      iIntros "(Hp & Q & Hev&[Htid _]&Hpos&_&Hdata&_&_)". simpl.
      rewrite map_fold_singleton /=. rewrite 2!union_empty_r_L.
      rewrite 2!big_sepS_singleton.
      iDestruct ("Hprot" $! eid with "Hev Htid Hpos Hdata Hp Q") as "Hprot".
      iApply (fupd_mask_intro _ ∅). {set_solver. }
      iIntros "M !>". iMod "M". iModIntro. iFrame. iExact "M".
      + simpl. iNext.
        iIntros (?) "Hinterp [%Hpc_eq %] [% ((?&[Htid _]&?)&_&_&?&?&?&?)]";simpl.
        iApply (inc_pc with "[-Hinterp]");eauto. rewrite Hpc_eq //.
        iIntros (? -> ? ?) "Hinterp". iApply ("Hcont" with "[-Hinterp]");auto.
        rewrite map_empty_union. rewrite big_sepM_singleton.
        iApply "HΦ".
        iFrame.
      + iFrame.
  Qed.

  Definition iload_pln {tid inst_addr kind_s ctrl rmw rv ot} R po_priors lob_priors addr reg:
    {SSi{{
           inst_addr ↦ᵢ (ILoad AV_plain kind_s reg (AEval addr)) ∗
           reg ↦ᵣ rv ∗
           ot -{LPo}> ∗
           ([∗ set] po_prior ∈ po_priors, po_prior -{Po}>) ∗
           ctrl -{Ctrl}> ∗
           rmw -{Rmw}> ∗
           last_local_write tid addr None ∗
           ([∗ map] lob_pred ↦ P ∈ lob_priors, lob_pred ↦ₐ P) ∗
           (∀ eid,
              (eid -{N}> (Edge.R AV_plain kind_s) -∗
               ([∗ set] po_prior ∈ po_priors, po_prior -{(Edge.Po)}> eid) -∗
               [∗ map] lob_prior ↦ _ ∈ lob_priors, lob_prior -{Edge.Lob}> eid) ∗
              (∃ prot q Q,
                  (([∗ map] _ ↦ P ∈ lob_priors, P) -∗ 『addr, q | prot』 ∗ Q) ∗
                  ∀ eid' v, eid -{E}> (Event.R AV_plain kind_s addr v) -∗
                            ⌜(EID.tid eid) = tid⌝ -∗
                            ([∗ set] po_prior ∈ po_priors, po_prior -{Edge.Po}> eid) -∗
                            (∃ kind_s_w kind_v_w, eid' -{E}> (Event.W kind_s_w kind_v_w addr v)) -∗
                            eid' -{Edge.Rf}> eid -∗
                            『addr, q | prot』 -∗ Q -∗
                            prot v eid' ==∗
                            R eid' v ∗ prot v eid'
           ))
    }}}
    (LTSI.Normal,inst_addr) @ tid
    {{{ eid eid' v, RET (LTSI.Normal, (inst_addr `+Z` 4)%bv);
           eid -{E}> (Event.R AV_plain kind_s addr v) ∗
                           ⌜(EID.tid eid) = tid⌝ ∗
                           reg ↦ᵣ mk_regval v {[eid]} ∗
                           eid ↦ₐ (R eid' v) ∗
                           (∃ kind_s_w kind_v_w, eid' -{E}> (Event.W kind_s_w kind_v_w addr v)) ∗
                           eid' -{Edge.Rf}> eid ∗
                           Some eid -{LPo}> ∗
                           ([∗ set] po_prior ∈ po_priors, po_prior -{Edge.Po}> eid) ∗
                           ctrl -{Ctrl}> ∗
                           rmw -{Rmw}> ∗
                           last_local_write tid addr None
      }}}.
  Proof.
    iIntros (Φ) "(Hinst & Hr & Hlpo & Hpo & Hctrl & Hrmw & Hlast_write &HP & Hfe) HΦ".

    rewrite sswpi_eq /sswpi_def;
    iIntros (?); iNamed 1; rewrite wpi_eq /wpi_def;
    iIntros (? [? ?]); repeat iNamed 1;
    iApply wp_sswp;
    iApply (reload with "[Hinst]");eauto;iNext;iIntros "_".

    iApply (mem_read_external _ (dom po_priors) lob_priors with "Hlpo Hctrl Hlast_write Hrmw [Hpo] [] HP [Hfe] [-Hinterp]") => //=.
    + set_solver.
    + iIntros (?). iDestruct ("Hfe" $! eid) as "[Hf He]". iSplitL "Hf".
    - iIntros "HN Hpo _ _". rewrite big_sepM_dom. iApply ("Hf" with "HN Hpo").
    - iDestruct "He" as "(%&%&%&?&He)". iFrame.
      iIntros (? eid_w) "(Hp & Q & (HE & [%Htid _] & Hpo & _ & _ & Hwrite & Hrf & _) & Hprot)".
      iApply (fupd_mask_intro _ ∅). { set_solver. }
      iIntros "M !>".
      iDestruct ("He" $! eid_w val with "HE [//] Hpo Hwrite Hrf Hp Q Hprot") as ">R".
      iMod "M" as "_". iModIntro. iExact "R".
    + simpl. iNext.
    iIntros (?) "Hinterp %Hpc_eq (% & % & % & [% %] & (Hread & [% %] & Hpos & _ & _ & Hwrite & Hrf & Hext) & Hannot & Hpo & Hctrl & Hlast_local_write & Hrmw & _)".

    iNamed "Hinterp".
    iApply wp_sswp.
    iApply reg_write;eauto.
    iNext. iIntros "_".
    iNamed "Hinterp". iDestruct (reg_interp_update with "Hinterp_reg Hr") as ">[Hinterp_reg Hr]".
    iDestruct (reg_mapsto_ne with "Hr Hinterp_pc") as %Hneq.

    iApply (inc_pc with "[-Hinterp_reg Hinterp_pc Hinterp_ctrl Hinterp_rmw]");auto.
    simpl. rewrite lookup_insert_ne //. rewrite Hpc_eq //.
    iIntros (? -> ? ?) "Hinterp". iApply ("Hcont" with "[-Hinterp]");auto.
    iApply ("HΦ" $! eid eid_w val).
    iFrame. done. iFrame. simpl. rewrite union_empty_l_L. rewrite H5 /=.
    rewrite union_empty_r_L. destruct eid;simpl in *;subst. iFrame.
  Qed.

  Lemma iload_pln_fake_addr {tid inst_addr kind_s ctrl rmw val addr_pred ot} R addr reg rv reg_dep P:
    {SSi{{
           inst_addr ↦ᵢ ILoad AV_plain kind_s reg (AEbinop AOplus (AEval addr) (AEbinop AOminus (AEreg reg_dep) (AEreg reg_dep))) ∗
           reg_dep ↦ᵣ mk_regval val {[addr_pred]} ∗
           addr_pred ↦ₐ P ∗
           reg ↦ᵣ rv ∗
           ot -{LPo}> ∗
           ctrl -{Ctrl}> ∗
           rmw -{Rmw}> ∗
           last_local_write tid addr None ∗
           (∃ prot q Q,
               (P -∗ 『addr, q | prot』 ∗ Q) ∗
               ∀ eid eid' v, eid -{E}> (Event.R AV_plain kind_s addr v) -∗
                             ⌜(EID.tid eid) = tid⌝ -∗
                             (∃ kind_s_w kind_v_w, eid' -{E}> (Event.W kind_s_w kind_v_w addr v)) -∗
                             eid' -{Edge.Rf}> eid -∗
                             addr_pred -{Edge.Addr}> eid -∗
                             『addr, q | prot』 -∗
                             Q -∗
                             prot v eid' ==∗
                             R eid' v ∗ prot v eid'
           )
    }}}
    (LTSI.Normal, inst_addr) @ tid
    {{{ eid eid' v, RET (LTSI.Normal, (inst_addr `+Z` 4)%bv);
        reg_dep ↦ᵣ mk_regval val {[addr_pred]} ∗
        eid -{E}> (Event.R AV_plain kind_s addr v) ∗
        ⌜(EID.tid eid) = tid⌝ ∗
        reg ↦ᵣ mk_regval v {[eid]} ∗
        eid ↦ₐ (R eid' v) ∗
        (∃ kind_s_w kind_v_w, eid' -{E}> (Event.W kind_s_w kind_v_w addr v)) ∗
        eid' -{Edge.Rf}> eid ∗
        Some eid -{LPo}> ∗
        ctrl -{Ctrl}> ∗
        rmw -{Rmw}>
      }}}.
  Proof.
    iIntros (Φ) "(Hinst & Hreg & HP & Hr & Hlpo & Hctrl & Hrmw & Hlast_write & Hfe) HΦ".
    rewrite sswpi_eq /sswpi_def;
    iIntros (?); iNamed 1; rewrite wpi_eq /wpi_def;
    iIntros (? [? ?]); repeat iNamed 1;
    iApply wp_sswp;
    iApply (reload with "[Hinst]");eauto;iNext;iIntros "_".

    iApply wp_sswp. iNamed "Hinterp". iDestruct (reg_interp_agree with "Hinterp_reg Hreg") as %Hreg.
    iApply reg_read;eauto.
    iNext. iIntros "_".

    iApply wp_sswp.
    iApply reg_read;eauto.
    iNext. iIntros "_".

    iApply (mem_read_external _ ∅ {[addr_pred := P]} {[reg_dep := _]} with "Hlpo Hctrl Hlast_write Hrmw [] [Hreg] [HP] [Hfe] [-Hinterp_reg Hinterp_pc Hinterp_ctrl Hinterp_rmw]");auto.
    + simpl.
      assert (addr + (val - val) = addr)%bv as ->.
      { unfold Val in *; unfold dw_size in *; bv_solve. }
      reflexivity.
    + rewrite dom_singleton_L /=. set_solver +.
    + rewrite big_sepM_singleton /=. iFrame.
    + rewrite big_sepM_singleton /=. iFrame.
    + iIntros (?). iSplitR "Hfe".
    - iIntros "HN _ _ Haddr". simpl.
      rewrite map_fold_singleton /=. rewrite 2!union_empty_r_L.
      rewrite dom_singleton_L. rewrite 2!big_sepS_singleton.
      by iApply addr_is_lob.
    - iDestruct "Hfe" as "(%&%&%&?&He)".
      iExists _,_,_.
      rewrite big_sepM_singleton. iFrame.
      iIntros (? eid_w) "(Hp & Q & (HE & [%Htid _] & Hpo & _ & Haddr & Hwrite & Hrf & _) & Hprot)".
      iApply (fupd_mask_intro _ ∅). { set_solver. }
      iIntros "M !>".
      iMod ("He" $! eid eid_w val0 with "HE [//] Hwrite Hrf [Haddr] Hp Q [$Hprot]") as "R".
      { simpl. rewrite map_fold_singleton /=. rewrite 2!union_empty_r_L. rewrite big_sepS_singleton //. }
      iMod "M" as "_". iModIntro. iExact "R".
    + simpl. iNext.
      iIntros (?) "Hinterp %Hpc_eq (% & % & % & [% %] & (Hread & [% %] & _ & _ & _ & Hwrite & Hrf & Hext) & Hannot & Hpo & Hctrl & Hlast_local_write & Hrmw & Hreg_dep)".
      subst.

      iNamed "Hinterp".
      iApply wp_sswp.
      iApply reg_write;eauto.
      iNext. iIntros "_".

      iNamed "Hinterp". iDestruct (reg_interp_update with "Hinterp_reg Hr") as ">[Hinterp_reg Hr]".
      iDestruct (reg_mapsto_ne with "Hr Hinterp_pc") as %Hneq.

      iApply (inc_pc with "[-Hinterp_reg Hinterp_pc Hinterp_ctrl Hinterp_rmw]");auto.
      simpl. rewrite lookup_insert_ne //. rewrite Hpc_eq //.
      iIntros (? -> ? ?) "Hinterp". iApply ("Hcont" with "[-Hinterp]");auto.
      iApply ("HΦ").
      rewrite big_sepM_singleton. iFrame.
      done.
      iFrame. rewrite /= union_empty_l_L. rewrite H5 /=.
      rewrite union_empty_r_L. destruct eid;simpl in *;subst. iFrame.
    + iFrame. 
  Qed.

  Lemma istore_pln {tid inst_addr ctrl ot lastw} R po_priors lob_priors addr data reg_res:
    {SSi{{
    inst_addr ↦ᵢ (IStore AV_plain AS_normal reg_res (AEval data) (AEval addr)) ∗
    ot -{LPo}> ∗
    ([∗ set] po_prior ∈ po_priors, po_prior -{Po}>) ∗
    ctrl -{Ctrl}> ∗
    last_local_write tid addr lastw ∗
    ([∗ map] lob_pred ↦ P ∈ lob_priors, lob_pred ↦ₐ P) ∗
    (∃ prot q Q, (([∗ map] _ ↦ P ∈ lob_priors, P) -∗ (『addr, q | prot』 ∗ Q)) ∗
      ∀ eid,
        (eid -{N}> (Edge.W AV_plain AS_normal) -∗
         ([∗ set] po_prior ∈ po_priors, po_prior -{(Edge.Po)}> eid) -∗
         ([∗ set] ctrl_prior ∈ ctrl, ctrl_prior -{(Edge.Ctrl)}> eid) -∗
         [∗ map] lob_prior ↦ _ ∈ lob_priors, lob_prior -{Edge.Lob}> eid) ∗
        (eid -{E}> (Event.W AV_plain AS_normal addr data) -∗
             ⌜(EID.tid eid) = tid⌝ -∗
             ([∗ set] po_prior ∈ po_priors, po_prior -{Edge.Po}> eid) -∗
             『addr, q | prot』 -∗
             Q ==∗
             R eid ∗ (prot data eid))
    )
    }}}
    (LTSI.Normal,inst_addr) @ tid
    {{{ eid, RET (LTSI.Normal, (inst_addr `+Z` 4)%bv);
        eid -{E}> (Event.W AV_plain AS_normal addr data) ∗
        ⌜(EID.tid eid) = tid⌝ ∗
        Some eid -{LPo}> ∗
        ([∗ set] po_prior ∈ po_priors, po_prior -{Edge.Po}> eid) ∗
        last_local_write tid addr (Some eid) ∗
        ctrl -{Ctrl}> ∗
        eid ↦ₐ R eid
      }}}.
  Proof.
    iIntros (Φ) "(Hinst & Hlpo & Hpos & Hctrl & Hlast_write & Hannot & Hfe) HΦ".

    rewrite sswpi_eq /sswpi_def;
    iIntros (?); iNamed 1; rewrite wpi_eq /wpi_def;
    iIntros (? [? ?]); repeat iNamed 1;
    iApply wp_sswp;
    iApply (reload with "[Hinst]");eauto;iNext;iIntros "_".

    iApply (mem_write_non_xcl _ po_priors lob_priors with "Hlpo Hctrl Hlast_write [Hpos] [] [Hannot] [Hfe] [-Hinterp]");auto.
    + assert (G: (∅ : gmap RegName RegVal) ∩ ∅ ⊆ ∅) => //.
    + set_solver.
    + set_solver.
    + rewrite map_union_empty. rewrite big_sepM_empty //.
    + simpl. iIntros (?).
      iDestruct "Hfe" as "(%&%&%&?&Hfe)". iFrame.
      iDestruct ("Hfe" $! eid) as "[Hf He]". iSplitL "Hf".
    - iIntros "HE Hpos Hctrl _ _". rewrite big_sepM_dom. iApply ("Hf" with "HE Hpos Hctrl").
    - iIntros "(Hp & Q & (HE & [%Htid _] & (Hpos & _)))".
      iApply (fupd_mask_intro _ ∅). { set_solver. }
      iIntros "M !>". iMod "M".
      iDestruct ("He" with "HE [//] Hpos Hp Q") as ">[HQ Hprot]".
      iModIntro. iFrame. iExact "HQ".
    + iNext. iIntros (?) "Hinterp [%Hpc_eq %] [% ((?&[? ?]&?&?&?)&HP&_&?&?&?&?)]";simpl.
      iApply (inc_pc with "[-Hinterp]");eauto. rewrite Hpc_eq //.
      iIntros (? -> ? ?) "Hinterp". iApply ("Hcont" with "[-Hinterp]");auto.
      iApply "HΦ".
      iFrame.
  Qed.

  Lemma istore_rel_raw {tid inst_addr reg_res ctrl ot o_lw} R po_priors lob_priors addr data:
    po_priors ⊆ dom lob_priors ->
    {SSi{{
           inst_addr ↦ᵢ (IStore AV_plain AS_rel_or_acq reg_res (AEval data) (AEval addr)) ∗
           ot -{LPo}> ∗
           ([∗ set] po_prior ∈ po_priors, po_prior -{Po}>) ∗
           ctrl -{Ctrl}> ∗
           last_local_write tid addr o_lw ∗
           ([∗ map] lob_pred ↦ P ∈ lob_priors, lob_pred ↦ₐ P) ∗
           (∃ prot q Q, (([∗ map] _ ↦ P ∈ lob_priors, P) -∗ (『addr, q | prot』 ∗ Q)) ∗
                        ∀ eid,
              (eid -{N}> Edge.W AV_plain AS_rel_or_acq -∗
               ([∗ set] po_prior ∈ po_priors, po_prior -{Edge.Po}> eid) -∗
               ([∗ set] lob_pred ∈ dom lob_priors ∖ po_priors, lob_pred -{Edge.Lob}> eid)) ∗
              (eid -{E}> (Event.W AV_plain AS_rel_or_acq addr data) -∗
               ⌜(EID.tid eid) = tid⌝ -∗
               ([∗ set] po_prior ∈ po_priors, po_prior -{Edge.Po}> eid) -∗
               (* ([∗ set] lob_pred ∈ dom lob_priors, lob_pred -{Edge.Lob}> eid) -∗ *)
               『addr, q | prot』 -∗
               Q ={⊤}=∗
               R ∗ (prot data eid))
           )
    }}}
     (LTSI.Normal, inst_addr) @ tid
    {{{ eid, RET (LTSI.Normal, (inst_addr `+Z` 4)%bv);
        eid -{E}> (Event.W AV_plain AS_rel_or_acq addr data) ∗
        ⌜(EID.tid eid) = tid⌝ ∗
        Some eid -{LPo}> ∗
        ctrl -{Ctrl}> ∗
        last_local_write tid addr (Some eid) ∗
        eid ↦ₐ R
     }}}.
  Proof.
    iIntros (Hsub Φ) "(Hinst & Hlpo & Hpo & Hctrl & Hlast_write & HP & Hprot) HΦ".

    rewrite sswpi_eq /sswpi_def;
    iIntros (?); iNamed 1; rewrite wpi_eq /wpi_def;
    iIntros (? [? ?]); repeat iNamed 1;
    iApply wp_sswp;
    iApply (reload with "[Hinst]");eauto;iNext;iIntros "_".

    iApply (mem_write_non_xcl _ po_priors lob_priors with "Hlpo Hctrl Hlast_write [Hpo] [] HP [Hprot] [-Hinterp]") => //=.
    + assert (G: (∅ : gmap RegName RegVal) ∩ ∅ ⊆ ∅) => //.
    + set_solver.
    + set_solver.
    + rewrite map_union_empty. rewrite big_sepM_empty //.
    + simpl. iIntros (?).
      iDestruct "Hprot" as "(%&%&%&?&Hprot)".
      iDestruct ("Hprot" $! eid) as "[Hef Hprot]".
      iSplitL "Hef".
      - iIntros "#HE #Hpo _ _ _".
        iSpecialize ("Hef" with "HE Hpo").
        iDestruct (big_sepS_impl with "Hpo") as "#Hlob".
        iSpecialize ("Hlob" with "[]").
        iModIntro. iIntros (? Hin) "Hpo'".
        iApply (po_rel_is_lob with "Hpo' HE");auto.
        iDestruct (big_sepS_union_2 with "Hef Hlob") as "Hlob'".
        assert ((dom lob_priors ∖ po_priors ∪ po_priors) = dom lob_priors) as ->.
        rewrite union_comm_L. rewrite -union_difference_L //.
        done.
      - iFrame.
        iIntros "(Hp & Q & (Hev&[%Htid _]&Hpos&?&?&?&_))".
        iDestruct ("Hprot" with "Hev [//] Hpos Hp Q") as ">[HQ Hprot]".
        iApply (fupd_mask_intro _ ∅). {set_solver. }
        iIntros "M !>". iMod "M".
        iModIntro. iFrame. iExact "HQ".
    + iNext. iIntros (?) "Hinterp [%Hpc_eq %] [% ((?&[[? ?] ?])&HP&_&?&?&?&?)]";simpl.
       iApply (inc_pc with "[-Hinterp]");eauto. rewrite Hpc_eq //.
       iIntros (? -> ? ?) "Hinterp". iApply ("Hcont" with "[-Hinterp]");auto.
       iApply "HΦ".
       iFrame.
  Qed.

  Lemma istore_rel {tid inst_addr reg_res ctrl ot o_lw} R po_priors addr data:
    {SSi{{
           inst_addr ↦ᵢ (IStore AV_plain AS_rel_or_acq reg_res (AEval data) (AEval addr)) ∗
           ot -{LPo}> ∗
           ([∗ map] po_prior ↦ _ ∈ po_priors, po_prior -{Po}>) ∗
           ctrl -{Ctrl}> ∗
           last_local_write tid addr o_lw ∗
           ([∗ map] po_pred ↦ P ∈ po_priors, po_pred ↦ₐ P) ∗
           (∃ prot q Q, (([∗ map] _ ↦ P ∈ po_priors, P) -∗ (『addr, q | prot』 ∗ Q)) ∗
                        ∀ eid, eid -{E}> (Event.W AV_plain AS_rel_or_acq addr data) -∗
                               ⌜(EID.tid eid) = tid⌝ -∗
                               ([∗ map] po_prior ↦ _ ∈ po_priors, po_prior -{Edge.Po}> eid) -∗
                               『addr, q | prot』 -∗
                               Q ={⊤}=∗
                               R ∗ (prot data eid)
           )
    }}}
    (LTSI.Normal, inst_addr) @ tid
     {{{ eid, RET (LTSI.Normal, (inst_addr `+Z` 4)%bv);
            eid -{E}> (Event.W AV_plain AS_rel_or_acq addr data) ∗
                  ⌜(EID.tid eid) = tid⌝ ∗
                  Some eid -{LPo}> ∗
                  ctrl -{Ctrl}> ∗
                  last_local_write tid addr (Some eid) ∗
                  eid ↦ₐ R
      }}}.
  Proof.
    iIntros (Φ) "(Hinst & Hlpo & Hpo & Hctrl & Hlast_write & HP & Hprot) HΦ".

    iApply (istore_rel_raw R (dom po_priors) po_priors with "[$Hinst $Hlpo Hpo $Hctrl $Hlast_write $HP Hprot]");auto.
    rewrite big_sepM_dom. iFrame "Hpo".
    iDestruct "Hprot" as "(%&%&%&$&Hprot)".
    iIntros (?).
    iSplitR. { rewrite difference_diag_L. iIntros "? ?". done. }
    iIntros "HE Htid Hpo HP".
    iApply ("Hprot" with "HE Htid [Hpo] HP").
    rewrite big_sepM_dom. iFrame "Hpo".
  Qed.

  Lemma istore_pln_fake_data {tid inst_addr ctrl po_prior} reg_dep val reg_res addr data addr_pred P:
    {SSi{{
    inst_addr ↦ᵢ (IStore AV_plain AS_normal
                    reg_res (AEbinop AOplus (AEval data) (AEbinop AOminus (AEreg reg_dep) (AEreg reg_dep))) (AEval addr)) ∗
    Some po_prior -{LPo}> ∗
    ctrl -{Ctrl}> ∗
    last_local_write tid addr None ∗
    reg_dep ↦ᵣ (mk_regval val {[addr_pred]}) ∗
    addr_pred ↦ₐ P ∗
    (∃ prot q Q, (P -∗ (『addr, q | prot』 ∗ Q)) ∗
      ∀ eid, eid -{E}> (Event.W AV_plain AS_normal addr data) -∗
             po_prior -{Edge.Po}> eid -∗
             addr_pred -{Edge.Data}> eid -∗
             『addr, q | prot』 -∗
             Q ==∗
             (prot data eid)
    )
    }}}
    (* Need to know about the data write here, or write the implication *)
    (LTSI.Normal, inst_addr) @ tid
      {{{  eid, RET (LTSI.Normal, (inst_addr `+Z` 4)%bv);
           reg_dep ↦ᵣ (mk_regval val {[addr_pred]}) ∗
           eid -{E}> (Event.W AV_plain AS_normal addr data) ∗
                  Some eid -{LPo}> ∗
                  last_local_write tid addr (Some eid) ∗
                  ctrl -{Ctrl}>
      }}}.
  Proof.
    iIntros (Φ) "(Hinst & Hpo & Hctrl & Hlast_write & Hreg & Hna & Hprot) HΦ".

    rewrite sswpi_eq /sswpi_def;
    iIntros (?); iNamed 1; rewrite wpi_eq /wpi_def;
    iIntros (? [? ?]); repeat iNamed 1;
    iApply wp_sswp;
    iApply (reload with "[Hinst]");eauto;iNext;iIntros "_".

    iDestruct (lpo_to_po with "Hpo") as "[Hlpo #Hpo]".

    iApply wp_sswp. iNamed "Hinterp". iDestruct (reg_interp_agree with "Hinterp_reg Hreg") as %Hreg.
    iApply reg_read;eauto.
    iNext. iIntros "_".

    iApply wp_sswp.
    iApply reg_read;eauto.
    iNext. iIntros "_".

    iApply (mem_write_non_xcl _ {[po_prior]} {[addr_pred := P]} {[reg_dep := _]} ∅ with "Hlpo Hctrl Hlast_write [] [Hreg] [Hna] [Hprot] [-Hinterp_reg Hinterp_ctrl Hinterp_rmw Hinterp_pc]").
    + simpl. reflexivity.
    + done.
    + rewrite map_subseteq_spec.
      intros ?? Hlk. rewrite lookup_intersection in Hlk.
      rewrite lookup_empty in Hlk. inversion Hlk.
    + simpl. set_solver +.
    + rewrite dom_singleton_L. simpl. set_solver +.
    + by iApply big_sepS_singleton.
    + rewrite map_empty_union.
      by iApply big_sepM_singleton.
    + by iApply big_sepM_singleton.
    + iIntros (?). iSplitR.
      - iIntros "_ _ _ _ ?".
        simpl. rewrite map_fold_singleton /=. rewrite 2!union_empty_r_L.
        rewrite dom_singleton_L. rewrite 2!big_sepS_singleton.
        by iApply data_is_lob.
      - iDestruct "Hprot" as "(%&%&%&?&Hprot)".
        iExists _,_,_. rewrite big_sepM_singleton. iFrame.
        iIntros "(Hp & Q & (Hev&_&Hpos&_&Hdata&_&_))". simpl.
        rewrite map_fold_singleton /=. rewrite 2!union_empty_r_L.
        rewrite 2!big_sepS_singleton.
        assert ((data + (val - val)) = data)%bv as ->.
        { unfold Val in *. bv_solve. }
        iDestruct ("Hprot" $! eid with "Hev Hpos Hdata Hp Q") as "Hprot".
        iApply (fupd_mask_intro _ ∅). {set_solver. }
        iIntros "M !>". iMod "M". iMod "Hprot". iModIntro. iFrame. iExact "M".
    + iNext. iIntros (?) "Hinterp [%Hpc_eq %] [% ((?&?)&_&_&?&?&?&?)]";simpl.
      iApply (inc_pc with "[-Hinterp]");eauto. rewrite Hpc_eq //.
      iIntros (? -> ? ?) "Hinterp". iApply ("Hcont" with "[-Hinterp]");auto.
      rewrite map_empty_union. rewrite big_sepM_singleton.
      iApply "HΦ".
      iFrame.
      assert ((data + (val - val)) = data)%bv as ->.
      { unfold Val in *. bv_solve. } done.
    + iFrame. 
  Qed.

End rules.
