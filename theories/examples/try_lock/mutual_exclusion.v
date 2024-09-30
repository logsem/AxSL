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

From self.examples.try_lock Require Import implementation.

Import uPred.

(* ghost states *)
Class MeInPreG `{CMRA Σ} := {
    MeOneShot :: inG Σ (csumR (dfrac_agreeR unitO)
                             (agreeR (leibnizO Eid)));
    MeOneShot' :: inG Σ (csumR (exclR unitO)
                             (agreeR unitO));
  }.

Class MeInG `{CMRA Σ} := {
    MeIn :: MeInPreG;
    MeOneShotNx : gname;
    MeOneShotNy : gname;
    MeOneShotNl : gname;
  }.

#[global] Arguments MeOneShotNx {Σ _ _}.
#[global] Arguments MeOneShotNy {Σ _ _}.
#[global] Arguments MeOneShotNl {Σ _ _}.

Definition MeΣ : gFunctors :=
  #[ GFunctor (csumR (dfrac_agreeR unitO) (agreeR (leibnizO Eid)));
     GFunctor (csumR (exclR unitO) (agreeR unitO))].

#[global] Instance subG_MeInPreG `{CMRA Σ}: subG MeΣ Σ -> MeInPreG.
Proof. solve_inG. Qed.

Section one_shot.
  Context `{CMRA Σ} `{!MeInG}.

  Definition pending_l := own MeOneShotNl (Cinl (Excl ())).

  Definition pending γ q := own γ (Cinl (to_dfrac_agree (DfracOwn q) ())).

  Lemma pending_split γ q:
    pending γ q ⊣⊢
    pending γ (q/2) ∗ pending γ (q/2).
  Proof.
    rewrite /pending.
    rewrite -own_op.
    rewrite -Cinl_op.
    rewrite -dfrac_agree_op.
    rewrite dfrac_op_own.
    rewrite Qp.div_2. done.
  Qed.

  Definition shot γ (v: Eid) := own γ (Cinr (to_agree (v :(leibnizO Eid)))).

  Lemma pending_shot γ q v: pending γ q -∗ shot γ v -∗ False.
  Proof.
    rewrite /pending /shot. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as "Hvalid".
    rewrite csum_validI //=.
  Qed.

  Definition shot_l := own MeOneShotNl (Cinr (to_agree ())).

  Lemma pending_l_shot : pending_l -∗ shot_l -∗ False.
  Proof.
    rewrite /pending_l /shot_l. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as "Hvalid".
    rewrite csum_validI //=.
  Qed.

  Lemma shot_shot γ v v': shot γ v -∗ shot γ v' -∗ ⌜v = v'⌝.
  Proof.
    rewrite /shot. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as "Hvalid".
    rewrite csum_validI //=.
    iDestruct "Hvalid" as %Hvalid.
    rewrite to_agree_op_valid_L in Hvalid.
    done.
  Qed.

  Lemma shoot γ v: pending γ 1%Qp ==∗ shot γ v.
  Proof.
    rewrite /pending /shot. iIntros "H".
    iApply (own_update with "H").
    apply cmra_update_exclusive.
    rewrite Cinr_valid. done.
  Qed.

  Lemma shoot_l : pending_l ==∗ shot_l.
  Proof.
    rewrite /pending_l /shot_l. iIntros "H".
    iApply (own_update with "H").
    apply cmra_update_exclusive.
    rewrite Cinr_valid. done.
  Qed.

  #[global] Instance shot_persist γ v: Persistent (shot γ v).
  Proof.
    rewrite /shot. apply _.
  Qed.

  #[global] Instance shot_l_persist : Persistent (shot_l).
  Proof.
    rewrite /shot_l. apply _.
  Qed.

  Definition pending_x q := pending MeOneShotNx q.
  Definition shot_x v := shot MeOneShotNx v.
  Definition pending_y q := pending MeOneShotNy q.
  Definition shot_y v := shot MeOneShotNy v.

End one_shot.

Definition addr_x := (BV 64 0x10).
Definition addr_y := (BV 64 0x11).
Definition addr_lock := (BV 64 0x12).
Definition data_flag := (BV 64 0x01).
Definition data_init := (BV 64 0).

Section mutual_exclusion.
  Context `{AAIrisG} `{!AAThreadG} `{ThreadGN}.
  Context `{!MeInG}.

  Definition me_x_prot (v : Val) (eid : Eid) : iProp Σ :=
    if (bool_decide (v = data_init)) then
      (⌜eid.(EID.tid) = 0%nat⌝)%I
    else if (bool_decide (v = data_flag)) then
           (shot_x eid)%I
         else False%I.

  Local Instance me_x_prot_persist v eid : Persistent (me_x_prot v eid).
  Proof.
    rewrite /me_x_prot. case_bool_decide. apply _.
    case_bool_decide; apply _.
  Qed.

  Definition me_y_prot (v : Val) (eid : Eid): iProp Σ :=
    if (bool_decide (v = data_init)) then
      (⌜eid.(EID.tid) = 0%nat⌝)%I
    else if (bool_decide (v = data_flag)) then
           (shot_y eid)%I
         else False%I.

  Local Instance me_y_prot_persist v eid : Persistent (me_y_prot v eid).
  Proof.
    rewrite /me_y_prot. case_bool_decide. apply _.
    case_bool_decide; apply _.
  Qed.

  Definition protected q (eid : Eid) : iProp Σ :=
    ((pending_x q ∗ pending_y q)
     ∨ (shot_l
        ∗ ∃ eid_x eid_y, (shot_x eid_x) ∗ ⌜eid_x.(EID.tid) = 1%nat⌝
                         ∗ (shot_y eid_y)∗ ⌜eid_y.(EID.tid) = 1%nat⌝
                         ∗ eid_x -{E}> (Event.W AS_normal AV_plain addr_x data_flag)
                         ∗ eid_y -{E}> (Event.W AS_normal AV_plain addr_y data_flag)
                         ∗ eid_x -{Edge.Ob}> eid
                         ∗ eid_y -{Edge.Ob}> eid)).

  Definition me_lock_prot (v: Val) (eid : Eid) :=
    if bool_decide (v = unlocked) then excl_inv eid (protected 1%Qp)
     else
       if bool_decide (v = locked) then True%I
       else False%I.

  Local Instance me_lock_prot_persist v eid : Persistent (me_lock_prot v eid).
  Proof.
    rewrite /me_lock_prot. case_bool_decide. apply _.
    case_bool_decide; apply _.
  Qed.

  (* Definition protocol : UserProt := *)
  (*   Build_UserProt _ _(λ a v e, *)
  (*                        if (bool_decide (a = addr_x)) then *)
  (*                          me_prot_x e v *)
  (*                        else if (bool_decide (a = addr_y)) then *)
  (*                          me_prot_y e v *)
  (*                        else if (bool_decide (a = addr_lock)) then *)
  (*                               me_prot_lock e v *)
  (*                        else True%I *)
  (*     ). *)

  (* Local Instance userprot : UserProt := protocol. *)

  (* Local Instance lock_is_lock : IsLockAt addr_lock (protected 1%Qp). *)
  (* Proof. *)
  (*   split. intros. simpl. done. *)
  (* Qed. *)

  Notation bne reg addr:= (IBne (AEreg reg) addr).
  Notation bne_neg reg addr:= (IBne (AEbinop AOminus (AEreg reg) (AEval (BV 64 1))) addr).
  Notation read reg addr := (ILoad AS_normal AV_plain reg (AEval addr)).
  Notation write val addr := (IStore AS_normal AV_plain "r0" (AEval val) (AEval addr)).

  Definition instrs_reader : iProp Σ :=
    instrs_aquire addr_lock (BV 64 0x2000) "r1" "r2" ∗
    (BV 64 0x2010) ↦ᵢ bne "r1" (BV 64 0x2024) ∗
    (BV 64 0x2014) ↦ᵢ bne_neg "r2" (BV 64 0x2024) ∗
    (* obtained the lock *)
    (BV 64 0x2018) ↦ᵢ read "r3" addr_x ∗
    (BV 64 0x201C) ↦ᵢ read "r4" addr_y ∗
    instrs_release addr_lock (BV 64 0x2020) ∗
    (BV 64 0x2024) ↦ᵢ -.

  Lemma reader :
    None -{LPo}> -∗
    ∅ -{Ctrl}> -∗
    None -{Rmw}> -∗
    (∃ rv, "r1" ↦ᵣ rv) -∗
    (∃ rv, "r2" ↦ᵣ rv) -∗
    (∃ rv, "r3" ↦ᵣ rv) -∗
    (∃ rv, "r4" ↦ᵣ rv) -∗
    last_local_write 2 addr_x None -∗
    last_local_write 2 addr_y None -∗
    last_local_write 2 addr_lock None -∗
    Prot[ addr_x, (1/2)%Qp | me_x_prot ] -∗
    Prot[ addr_y, (1/2)%Qp | me_y_prot ] -∗
    Prot[ addr_lock, (1/2)%Qp | me_lock_prot ] -∗
    instrs_reader -∗
    WPi (LTSI.Normal, (BV 64 0x2000)) @ 2
      {{ λ lts',
           ⌜lts' = (LTSI.Done, (BV 64 0x2024))⌝ ∗
           ∃ rv1 rv2 rv3 rv4, ("r1" ↦ᵣ rv1 ∗ "r2" ↦ᵣ rv2 ∗ "r3" ↦ᵣ rv3 ∗ "r4" ↦ᵣ rv4) ∗
           (⌜rv1.(reg_val) = unlocked ∧ rv2.(reg_val) = (BV 64 1)⌝ -∗
            ⌜(rv3.(reg_val) = data_init ∧ rv4.(reg_val) = data_init)
            ∨ (rv3.(reg_val) = data_flag ∧ rv4.(reg_val) = data_flag)⌝
            )
      }}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hrmw Hreg1 Hreg2 Hreg3 Hreg4 Hlocalw_x Hlocalw_y Hlocalw_l Hprot_x Hprot_y Hprot_l Hinstrs".
    iDestruct "Hinstrs" as "(#? & #? & #? & #? & #? & #? & #?)".

    iApply (acquire _ _ _ _ (λ eid, (protected (1/2)%Qp eid ∗ protected (1/2)%Qp eid))%I
             with "Hpo_src Hctrl_src Hrmw Hreg1 Hreg2 Hlocalw_l Hprot_l [#$]").
    {
      iIntros (?) "[Hl|#Hr]".
      {
        iModIntro.
        iFrame. rewrite /pending_x /pending_y.
        rewrite (pending_split MeOneShotNx).
        rewrite (pending_split MeOneShotNy).
        iDestruct "Hl" as "([Hpending_x1 Hpending_x2] & Hpending_y1 & Hpending_y2)".
        iSplitL "Hpending_x1 Hpending_y1"; iLeft; iFrame.
      }
      {
        iModIntro.
        iSplitL;iRight;iFrame "Hr".
      }
    }

    iIntros "(%eid_lxr & %v1 & %v2 & %d2 & Hreg1 & Hreg2 & %po_src & %ctrl_src & %rmw_src & Hpo_src
    & Hctrl_src & Hrmw_src & Hpost)".

    iDestruct "Hreg3" as "[%rv3 Hreg3]". iDestruct "Hreg4" as "[%rv4 Hreg4]".

    assert (G: (BV 64 8192 `+Z` 16)%bv = (BV 64 8208)%bv); [bv_solve|]. rewrite G;clear G.

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hctrl_src Hreg1]").
    {
      iApply (ibne {["r1" := _]} with "[#] Hctrl_src [Hreg1]").
      4:{ rewrite big_sepM_singleton. iExact "Hreg1". }
      3:{ iFrame "#". }
      - rewrite dom_singleton_L. set_solver +.
      - simpl. rewrite lookup_singleton /=. reflexivity.
    }
    iIntros (?) "(Hreg1 & Hctrl_src & %Hbranch)".
    rewrite map_fold_singleton /=. rewrite union_empty_r_L.
    rewrite big_sepM_singleton.

    (* Obtained the lock or not, first branching *)
    destruct Hbranch as [[-> ->]|[-> ?]].
    2:{
      iApply sswpi_wpi.
      iApply idone. iFrame "#".
      iApply wpi_terminated.
      iApply (inst_post_lifting_lifting _ _ _ ∅).
      rewrite dom_empty_L //.
      rewrite big_sepM_empty //.
      iIntros "_ !>".
      iSplit;first done.
      iExists _,_,_,_. iFrame. simpl.
      iIntros "[-> ->]". rewrite /unlocked in H4. done.
    }

    assert (G: (BV 64 8208 `+Z` 4)%bv = (BV 64 8212)%bv); [bv_solve|]. rewrite G;clear G.

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hctrl_src Hreg2]").
    {
      iApply (ibne {["r2" := _]} with "[#] Hctrl_src [Hreg2]").
      4:{ rewrite big_sepM_singleton. iExact "Hreg2". }
      3:{ iFrame "#". }
      - rewrite dom_singleton_L. set_solver +.
      - simpl. rewrite lookup_singleton /=. reflexivity.
    }
    iIntros (?) "(Hreg2 & Hctrl_src & %Hbranch)".
    rewrite map_fold_singleton /=. rewrite union_empty_r_L.
    rewrite big_sepM_singleton.

    (* Obtained the lock or not, second branching *)
    destruct Hbranch as [[-> Heq_v2]|[-> ?]].
    2:{
      iApply sswpi_wpi.
      iApply idone. iFrame "#".
      iApply wpi_terminated.
      iApply (inst_post_lifting_lifting _ _ _ ∅).
      rewrite dom_empty_L //.
      rewrite big_sepM_empty //.
      iIntros "_ !>".
      iSplit;first done.
      iExists _,_,_,_. iFrame. simpl.
      iIntros "[-> ->]".
      exfalso.
      assert ((BV 64 1 - BV 64 1) = BV 64 0)%bv. bv_solve.
      rewrite H5 in H4. done.
    }

    (* Obtained the lock *)
    assert (v2 = locked) as ->.
    {
      (* XXX: bv_solve is not working - unfolding is not smart enough! *)
      rewrite /locked.
      destruct (bool_decide (v2 = BV 64 1)) eqn:Heqn.
      rewrite bool_decide_eq_true in Heqn. done.
      rewrite bool_decide_eq_false in Heqn.
      clear -Heq_v2 Heqn.
      unfold AAInter.reg_type in v2. unfold AAArch.val in v2. unfold AAval in v2. unfold AAArch.val_size in v2.
      assert ((v2 - BV 64 1)%bv = (v2 `-Z` 1)%bv). bv_solve.
      rewrite H in Heq_v2. clear H.
      assert (bv_unsigned v2 ≠ 1).
      { intro Heq. apply Heqn. apply bv_eq. rewrite Heq. done. }
      apply bv_eq in Heq_v2.
      rewrite bv_sub_Z_unsigned  /= in Heq_v2.
      rewrite bv_unsigned_BV in Heq_v2.
      bv_simplify_arith. bv_saturate_unsigned; bv_solve_unfold_tac.
      unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, bv_unsigned in *.
      simpl in *. destruct v2. simpl. lia.
    }
    iDestruct ("Hpost" with "[//]") as "(-> & %eid_lw & %eid_lw' & %eid_b & -> & -> & -> & Hlocalw_l
    & Hna_lw' & #Hob_lwlw' & #He_b & #Hpo_lw'b)".
    rewrite union_empty_l_L.

    iDestruct (annot_split_iupd with "Hna_lw'") as ">[Hna_lw' Hna_lw'_lw]".
    iDestruct (annot_split_iupd with "Hna_lw'") as ">[Hna_lw'_x Hna_lw'_y]".
    assert (G: (BV 64 8212 `+Z` 4)%bv = (BV 64 8216)%bv); [bv_solve|]. rewrite G;clear G.
    iDestruct (lpo_to_po with "Hpo_src") as "[Hpo_src #Hpo_src_b]".

    (* Read x *)
    iApply sswpi_wpi. iApply (sswpi_mono with "[Hlocalw_x Hprot_x Hpo_src Hctrl_src Hna_lw'_x Hreg3 Hrmw_src]").
    {
      iApply (iload_pln (λ eid_x v,
                           ((⌜v = data_init⌝ ∗ ⌜eid_x.(EID.tid) = 0%nat⌝ ∗ protected (1/2)%Qp eid_lw)
                            ∨ (⌜v = data_flag⌝  ∗ shot_x eid_x ∗ shot_l ∗ eid_x -{Edge.Ob}> eid_lw
                               ∗ (∃ (kind_s_w : AccessStrength) (kind_v_w : AccessVariety), eid_x -{E}> Event.W kind_s_w kind_v_w addr_x v)
                               ∗ ∃ eid_y, (shot_y eid_y) ∗ ⌜eid_y.(EID.tid) = 1%nat⌝ ∗ eid_y -{Edge.Ob}> eid_lw
                                          ∗ eid_y -{E}> (Event.W AS_normal AV_plain addr_y data_flag))))%I
                {[eid_b]} {[eid_lw' := protected (1/2)%Qp eid_lw]}
               with "[$Hpo_src $Hctrl_src $Hlocalw_x Hna_lw'_x $Hreg3 $Hrmw_src]").
      { iFrame "#∗". rewrite big_sepS_singleton big_sepM_singleton. iFrame "#∗". }
      iIntros (eid_r_x). iSplitR.
      {
        iIntros "HE Hpo_b".
        rewrite big_sepS_singleton big_sepM_singleton.
        iApply po_dmbsy_po_is_lob;iFrame "#∗".
        iDestruct (event_node with "He_b") as "$".
      }
      {
        iExists _,_,_. iSplitL. iIntros "H";iFrame. iExact "H".
        iIntros (eid_w_x v_x) "He_r_x Htid_r_x Hpo_r_x He_w_x Hrf_x Hp HP #Hprot".
        rewrite big_sepM_singleton.
        rewrite /me_x_prot.
        iModIntro.
        case_bool_decide.
        { iFrame "#". iLeft. iFrame. done. }
        {
          case_bool_decide;last done.
          {
            iFrame "#". iRight. iSplit;first done.
            iDestruct "HP" as "[[Hx _]|(?& %&%&Hshot_x &?& Hshot_y & ?&?&?&?&?)]".
            {
              iExFalso.
              iApply (pending_shot with "Hx Hprot").
            }
            {
              iDestruct (shot_shot with "Hprot Hshot_x") as %->.
              iFrame "#∗".
            }
          }
        }
      }
    }

    iIntros (?) "(-> & (%eid_r_x & %eid_w_x & %val_x & He_r_x & #Htid_w_x & Hreg3 & Hna_r_x & #He_w_x & #Hrf_x
     & Hpo_src & #Hpo_b_r_x & Hctrl_src & Hrmw_src & _))".
    rewrite big_sepS_singleton.
    iAssert (⌜eid_b ≠ eid_r_x⌝%I) as "%Hneq_eid_r_x".
    { iIntros (->). iApply (po_irrefl with "Hpo_b_r_x"). }

    assert (G: (BV 64 8216 `+Z` 4)%bv = (BV 64 8220)%bv); [bv_solve|]. rewrite G;clear G.
    iDestruct (lpo_to_po with "Hpo_src") as "[Hpo_src #Hpo_src_r_x]".

    (* Read y *)
    iApply sswpi_wpi. iApply (sswpi_mono with "[Hlocalw_y Hprot_y Hpo_src Hctrl_src Hna_lw'_y Hreg4 Hrmw_src]").
    {
      iApply (iload_pln (λ eid_y v,
                           ((⌜v = data_init⌝ ∗ ⌜eid_y.(EID.tid) = 0%nat⌝ ∗ protected (1/2)%Qp eid_lw)
                            ∨ (⌜v = data_flag⌝ ∗ shot_y eid_y ∗ shot_l ∗ eid_y -{Edge.Ob}> eid_lw
                               ∗ eid_y -{E}> (Event.W AS_normal AV_plain addr_y data_flag)
                               ∗ ∃ eid_x, (shot_x eid_x) ∗ ⌜eid_x.(EID.tid) = 1%nat⌝  ∗ eid_x -{Edge.Ob}> eid_lw
                                          ∗ eid_x -{E}> (Event.W AS_normal AV_plain addr_x data_flag))))%I
                {[eid_b;eid_r_x]} {[eid_lw' := protected (1/2)%Qp eid_lw]}
               with "[$Hpo_src $Hctrl_src $Hlocalw_y Hna_lw'_y $Hreg4 $Hrmw_src]").
      {
        iFrame "#∗". rewrite big_sepS_union. rewrite 2!big_sepS_singleton big_sepM_singleton. iFrame "#∗".
        set_solver + Hneq_eid_r_x.
      }
      iIntros (eid_r_y). iSplitR.
      {
        iIntros "HE Hpo_b".
        rewrite big_sepS_union. rewrite 2!big_sepS_singleton big_sepM_singleton.
        iDestruct "Hpo_b" as "[Hpo_b _]".
        iApply po_dmbsy_po_is_lob;iFrame "#∗".
        iDestruct (event_node with "He_b") as "$".
        set_solver + Hneq_eid_r_x.
      }
      {
        iExists _,_,_. iSplitL. iIntros "H";iFrame;iExact "H".
        iIntros (eid_w_y v_y) "He_r_y Htid_r_y Hpo_r_y He_w_y Hrf_y Hp HP #Hprot".
        rewrite big_sepM_singleton.
        rewrite /me_y_prot.
        iModIntro.
        case_bool_decide.
        { iFrame "#". iLeft; iFrame. done. }
        {
          case_bool_decide;last done.
          {
            iFrame "#". iRight. iSplit;first done.
            iDestruct "HP" as "[[_ Hy]|(?& %&%&Hshot_x&? & Hshot_y &?& ?&?&?&?)]".
            {
              iExFalso. iApply (pending_shot with "Hy Hprot").
            }
            {
              iDestruct (shot_shot with "Hprot Hshot_y") as %->.
              iFrame "#∗".
            }
          }
        }
      }
    }

    iIntros (?) "(-> & (%eid_r_y & %eid_w_y & %val_y & He_r_y & #Htid_w_y & Hreg4 & Hna_r_y & #He_w_y & #Hrf_y
     & Hpo_src & Hpos & Hctrl_src & Hrmw_src & _))".
    iDestruct (lpo_to_po with "Hpo_src") as "[Hpo_src #Hpo_src_r_y]".

    assert (G: (BV 64 8220 `+Z` 4)%bv = (BV 64 8224)%bv); [bv_solve|]. rewrite G;clear G.

    rewrite big_sepS_union. rewrite 2!big_sepS_singleton. iDestruct "Hpos" as "[#Hpo_b_r_y #Hpo_r_x_r_y]".
    iAssert (⌜eid_r_x ≠ eid_r_y⌝%I) as "%Hneq_eid_r_x_y".
    { iIntros (->). iApply (po_irrefl with "Hpo_r_x_r_y"). }

    iApply (release _ _ {[eid_r_x; eid_r_y]} {[eid_r_x := _; eid_r_y := _; eid_lw' := _]}
                    (⌜val_x = data_init ∧ val_y = data_init⌝ ∨ ⌜val_x = data_flag ∧ val_y = data_flag⌝)%I
             with "Hpo_src [] Hctrl_src Hrmw_src Hlocalw_l [#$] [Hna_r_x Hna_r_y Hna_lw'_lw]").
    {
      rewrite 3!dom_insert_L. set_solver +.
    }
    {
      rewrite big_sepS_union. rewrite 2!big_sepS_singleton. iFrame "#".
      set_solver + Hneq_eid_r_x_y.
    }
    {
      iApply (big_sepM_insert_2 with "Hna_r_x").
      iApply (big_sepM_insert_2 with "Hna_r_y").
      by iApply (big_sepM_insert_2 with "Hna_lw'_lw").
    }
    {
      iExists _.
      iAssert (⌜eid_lw' ≠ eid_r_x⌝%I) as "%Hneq_eid_lw'_x".
      {
        iIntros (->).
        iDestruct (po_trans with "Hpo_lw'b Hpo_b_r_x" ) as "HH".
        iApply (po_irrefl with "HH").
      }

      iAssert (⌜eid_lw' ≠ eid_r_y⌝%I) as "%Hneq_eid_lw'_y".
      {
        iIntros (->).
        iDestruct (po_trans with "Hpo_lw'b Hpo_b_r_y" ) as "HH".
        iApply (po_irrefl with "HH").
      }

      iSplitL.
      rewrite big_sepM_insert.
      2:{
        simplify_map_eq /=. done.
      }
      rewrite big_sepM_insert.
      2:{
        simplify_map_eq /=. done.
      }
      rewrite big_sepM_singleton.

      iIntros "(H & H' & $)". iCombine "H H'" as "H". iExact "H".

      iIntros (eid_r).
      iSplitR.
      {
        iIntros "_ #Hpoo". rewrite 3!dom_insert_L. rewrite dom_empty_L. rewrite union_empty_r_L.
        assert ((({[eid_r_x]} ∪ {[eid_r_y; eid_lw']})
                      ∖ {[eid_r_x; eid_r_y]}) = {[eid_lw']}) as ->.
        { set_solver. }
        rewrite big_sepS_singleton.
        iApply (po_dmbsy_po_is_lob with "Hpo_lw'b [] ").
        iApply (event_node with "He_b").
        rewrite big_sepS_union. 2: set_solver.
        rewrite big_sepS_singleton. iDestruct "Hpoo" as "[Hpoo _]".
        iApply (po_trans with "[] Hpoo"). iFrame "#".
      }
      {
        iIntros "(#He_r&Hpos&HP)".
        rewrite big_sepS_union. 2: set_solver + Hneq_eid_r_x_y.
        rewrite 2!big_sepS_singleton.
        iModIntro.
        iDestruct "HP" as "[[Hz_x | Hf_x] [Hz_y | Hf_y]]".
        {
          (* case x=0, y=0 *)
          iDestruct "Hz_x" as "(-> & %Hinit_x & Hz_x)". iDestruct "Hz_y" as "(-> & %Hinit_y & Hz_y)".
          iSplit;last (iLeft;done).

          iDestruct "Hpos" as "[#Hpo_r_x_r #Hpo_r_y_r]".
          iDestruct (po_trans with "Hpo_lw'b Hpo_b_r_x") as "Hpo_x_1".
          iDestruct (po_trans with "Hpo_x_1 Hpo_r_x_r") as "Hpo_x_2".
          iAssert (eid_lw' -{Edge.Ob}> eid_r)%I as "Hob_r".
          {
            iApply lob_is_ob.
            iApply (po_rel_is_lob with "Hpo_x_2 []").
            iApply (event_node with "He_r").
          }

          iDestruct "Hz_x" as "[[HN_x HN_y] | (#Hshot_l& %&%&HS_x & HS_y & #(Hx1&Hx2&Hx3&Hx4&Hx5&Hx6))]";
          iDestruct "Hz_y" as "[[HN_x' HN_y'] | (#Hshot_l'& %&%&HS_x' & HS_y' & #(Hy1&Hy2&Hy3&Hy4&Hy5&Hy6))]".
          {
            iLeft. iDestruct (pending_split with "[$HN_x $HN_x']") as "$".
            iDestruct (pending_split with "[$HN_y $HN_y']") as "$".
          }
          { iExFalso. iApply (pending_shot with "HN_x HS_x'"). }
          { iExFalso. iApply (pending_shot with "HN_x' HS_x"). }
          {
            iRight. iFrame "Hshot_l".
            iDestruct (shot_shot with "HS_x HS_x'") as %->.
            iExists _,_. iFrame "#∗".
            iDestruct (ob_trans with "Hy5 Hob_lwlw'") as "Hob_x".
            iDestruct (ob_trans with "Hy6 Hob_lwlw'") as "Hob_y".
            iSplit.
            { iApply (ob_trans with "Hob_x Hob_r"). }
            { iApply (ob_trans with "Hob_y Hob_r"). }
          }
        }
        {
          (* case x = 0, y = 1, impossible *)
          iDestruct "Hz_x" as "(-> & % & _)".
          iDestruct "He_w_x" as "(%&%&He_w_x)".
          iDestruct "Hf_y" as "(_ &_&_&_&_&%eid_w_x'&_&%Htid_x&#Hob_x&#He_w')".
          iDestruct (initial_write_co with "He_w_x He_w'") as "Hco_x". done.
          { rewrite Htid_x. lia. }
          iDestruct (rf_co_to_fr with "Hrf_x Hco_x") as "Hfr_x".
          iDestruct "Htid_w_x" as %Htid_r_x.
          iDestruct (fre_is_ob with "Hfr_x") as "Hob_x'".  lia.
          iDestruct (ob_trans with "Hob_x' Hob_x") as "Hob_x''".
          iDestruct (ob_trans with "Hob_x'' Hob_lwlw'") as "Hob_x'''".
          iDestruct (po_dmbsy_po_is_lob with "Hpo_lw'b [] Hpo_b_r_x") as "Hlob_x".
          { iApply (event_node with "He_b"). }
          iDestruct (lob_is_ob with "Hlob_x") as "Hob_x''''".
          iDestruct (ob_trans with "Hob_x''' Hob_x''''") as "Hob_cycle".
          iExFalso. iApply (ob_acyclic with "Hob_cycle").
        }
        {
          (* case x = 1, y = 0, impossible *)
          iDestruct "Hz_y" as "(-> & % & _)".
          iDestruct "He_w_y" as "(%&%&He_w_y)".
          iDestruct "Hf_x" as "(_ &_&_&_&_&%eid_w_y'&_&%Htid_y&#Hob_y&#He_w')".
          iDestruct (initial_write_co with "He_w_y He_w'") as "Hco_y". done.
          { rewrite Htid_y. lia. }
          iDestruct (rf_co_to_fr with "Hrf_y Hco_y") as "Hfr_y".
          iDestruct "Htid_w_y" as %Htid_r_y.
          iDestruct (fre_is_ob with "Hfr_y") as "Hob_y'".  lia.
          iDestruct (ob_trans with "Hob_y' Hob_y") as "Hob_y''".
          iDestruct (ob_trans with "Hob_y'' Hob_lwlw'") as "Hob_y'''".
          iDestruct (po_dmbsy_po_is_lob with "Hpo_lw'b [] Hpo_b_r_y") as "Hlob_y".
          { iApply (event_node with "He_b"). }
          iDestruct (lob_is_ob with "Hlob_y") as "Hob_y''''".
          iDestruct (ob_trans with "Hob_y''' Hob_y''''") as "Hob_cycle".
          iExFalso. iApply (ob_acyclic with "Hob_cycle").
        }
        {
          (* case x = 1, y = 1 *)
          iDestruct "Hf_y" as "(%v_y & #shot_y & #shot_l & #Hob_w_y_l &#He_w_y'&%eid_w_x'
          &shot_x'&%Htid_x&#Hob_x&#He_w')".
          iDestruct "Hf_x" as "(%v_x & #shot_x & _ & #Hob_w_x_l &#He_w_x'&%eid_w_y'&shot_y'
          &%Htid_y&#Hob_y&#He_w'')".
          iSplit.
          iRight. iFrame "shot_l".
          iDestruct (shot_shot with "shot_x shot_x'") as %->.
          iDestruct (shot_shot with "shot_y shot_y'") as %->.
          iExists _,_. iFrame "#". iSplit;first done. iSplit;first done.

          iDestruct (ob_trans with "Hob_w_x_l Hob_lwlw'") as "Hob_x'".
          iDestruct (ob_trans with "Hob_w_y_l Hob_lwlw'") as "Hob_y'".
          iDestruct "Hpos" as "[#Hpo_r_x_r #Hpo_r_y_r]".
          iDestruct (po_trans with "Hpo_lw'b Hpo_b_r_x") as "Hpo_x_1".
          iDestruct (po_trans with "Hpo_x_1 Hpo_r_x_r") as "Hpo_x_2".
          iAssert (eid_lw' -{Edge.Ob}> eid_r)%I as "Hob_r".
          {
            iApply lob_is_ob.
            iApply (po_rel_is_lob with "Hpo_x_2 []").
            iApply (event_node with "He_r").
          }
          iSplit.
          { iApply (ob_trans with "Hob_x' Hob_r"). }
          { iApply (ob_trans with "Hob_y' Hob_r"). }
          iRight;done.
        }
      }
    }
    iIntros "(%&?&%HHH&?&?&?&Hna)".

    assert (G: ((BV 64 8224) `+Z` 4 = (BV 64 8228))%bv); [bv_solve|]. rewrite G. clear G.
    iApply sswpi_wpi. iApply idone;auto.
    iApply wpi_terminated.
    iApply (inst_post_lifting_lifting _ _ _ {[eid := _]} with "[Hna]");auto.
    rewrite dom_singleton_L. apply set_Forall_singleton. done.
    rewrite big_sepM_singleton. iFrame.
    rewrite big_sepM_singleton.
    iIntros "[%HH Hp]". iModIntro. iSplit;first done.
    iExists _,_,_,_. iFrame. simpl. iIntros "_". iPureIntro. done.
    set_solver + Hneq_eid_r_x.
  Qed.

  Definition instrs_writer : iProp Σ :=
    instrs_aquire addr_lock (BV 64 0x1000) "r1" "r2" ∗
    (BV 64 0x1010) ↦ᵢ bne "r1" (BV 64 0x1024) ∗
    (BV 64 0x1014) ↦ᵢ bne_neg "r2" (BV 64 0x1024) ∗
    (* obtained the lock *)
    (BV 64 0x1018) ↦ᵢ write data_flag addr_x ∗
    (BV 64 0x101C) ↦ᵢ write data_flag addr_y ∗
    instrs_release addr_lock (BV 64 0x1020) ∗
    (BV 64 0x1024) ↦ᵢ -.

  Lemma writer :
    None -{LPo}> -∗
    ∅ -{Ctrl}> -∗
    None -{Rmw}> -∗
    (∃ rv, "r1" ↦ᵣ rv) -∗
    (∃ rv, "r2" ↦ᵣ rv) -∗
    last_local_write 1 addr_x None -∗
    last_local_write 1 addr_y None -∗
    last_local_write 1 addr_lock None -∗
    Prot[ addr_x, (1/2)%Qp | me_x_prot ] -∗
    Prot[ addr_y, (1/2)%Qp | me_y_prot ] -∗
    Prot[ addr_lock, (1/2)%Qp | me_lock_prot ] -∗
    instrs_writer -∗
    pending_l -∗
    WPi (LTSI.Normal, (BV 64 0x1000)) @ 1
      {{ λ lts',
           ⌜lts' = (LTSI.Done, (BV 64 0x1024))⌝
      }}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hrmw Hreg1 Hreg2 Hlocalw_x Hlocalw_y Hlocalw_l Hprot_x Hprot_y Hprot_lock Hinstrs Hpending_l".
    iDestruct "Hinstrs" as "(#? & #? & #? & #? & #? & #? & #?)".

    iApply (acquire _ _ _ _ (λ _,  pending_l ∗ pending_x 1%Qp ∗ pending_y 1%Qp)%I
             with "Hpo_src Hctrl_src Hrmw Hreg1 Hreg2 Hlocalw_l Hprot_lock [#$] [Hpending_l]").
    {
      iIntros (?) "[Hl|[Hshot_l Hr]]".
      { iModIntro. iDestruct "Hl" as "[$ $]". iFrame. }
      { iExFalso. iApply (pending_l_shot with "Hpending_l Hshot_l"). }
    }

    iIntros "(%eid_lxr & %v1 & %v2 & %d2 & Hreg1 & Hreg2 & %po_src & %ctrl_src & %rmw_src & Hpo_src
    & Hctrl_src & Hrmw_src & Hpost)".

    assert (G: (BV 64 4096 `+Z` 16)%bv = (BV 64 4112)%bv); [bv_solve|]. rewrite G;clear G.

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hctrl_src Hreg1]").
    {
      iApply (ibne {["r1" := _]} with "[#] Hctrl_src [Hreg1]").
      4:{ rewrite big_sepM_singleton. iExact "Hreg1". }
      3:{ iFrame "#". }
      - rewrite dom_singleton_L. set_solver +.
      - simpl. rewrite lookup_singleton /=. reflexivity.
    }
    iIntros (?) "(Hreg1 & Hctrl_src & %Hbranch)".
    rewrite map_fold_singleton /=. rewrite union_empty_r_L. rewrite big_sepM_singleton.

    (* Obtained the lock or not, first branching *)
    destruct Hbranch as [[-> ->]|[-> ?]].
    2:{
      iApply sswpi_wpi. iApply idone. iFrame "#".
      iApply wpi_terminated.
      iApply (inst_post_lifting_lifting _ _ _ ∅).
      rewrite dom_empty_L //.
      rewrite big_sepM_empty //.
      iIntros "_ !>". done.
    }

    assert (G: (BV 64 4112 `+Z` 4)%bv = (BV 64 4116)%bv); [bv_solve|]. rewrite G;clear G.

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hctrl_src Hreg2]").
    {
      iApply (ibne {["r2" := _]} with "[#] Hctrl_src [Hreg2]").
      4:{ rewrite big_sepM_singleton. iExact "Hreg2". }
      3:{ iFrame "#". }
      - rewrite dom_singleton_L. set_solver +.
      - simpl. rewrite lookup_singleton /=. reflexivity.
    }
    iIntros (?) "(Hreg2 & Hctrl_src & %Hbranch)".
    rewrite map_fold_singleton /=. rewrite union_empty_r_L. rewrite big_sepM_singleton.

    (* Obtained the lock or not, second branching *)
    destruct Hbranch as [[-> Heq_v2]|[-> ?]].
    2:{
      iApply sswpi_wpi. iApply idone. iFrame "#".
      iApply wpi_terminated.
      iApply (inst_post_lifting_lifting _ _ _ ∅).
      rewrite dom_empty_L //.
      rewrite big_sepM_empty //.
      iIntros "_ !>". done.
    }

    (* Obtained the lock *)
    assert (v2 = locked) as ->.
    {
      (* XXX: bv_solve is not working - unfolding is not smart enough! *)
      rewrite /locked.
      destruct (bool_decide (v2 = BV 64 1)) eqn:Heqn.
      rewrite bool_decide_eq_true in Heqn. done.
      rewrite bool_decide_eq_false in Heqn.
      clear -Heq_v2 Heqn.
      unfold AAInter.reg_type in v2. unfold AAArch.val in v2. unfold AAval in v2. unfold AAArch.val_size in v2.
      assert ((v2 - BV 64 1)%bv = (v2 `-Z` 1)%bv). bv_solve.
      rewrite H in Heq_v2. clear H.
      assert (bv_unsigned v2 ≠ 1).
      { intro Heq. apply Heqn. apply bv_eq. rewrite Heq. done. }
      apply bv_eq in Heq_v2.
      rewrite bv_sub_Z_unsigned  /= in Heq_v2.
      rewrite bv_unsigned_BV in Heq_v2.
      bv_simplify_arith. bv_saturate_unsigned; bv_solve_unfold_tac.
      unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, bv_unsigned in *.
      simpl in *. destruct v2. simpl. lia.
    }
    iDestruct ("Hpost" with "[//]") as "(-> & %eid_lw & %eid_lw' & %eid_b & -> & -> & -> & Hlocalw_l
    & Hna_lw' & #Hob_lwlw' & #He_b & #Hpo_lw'b)".
    rewrite union_empty_l_L.

    iDestruct (annot_split_iupd with "Hna_lw'") as ">[Hna_lw' Hna_lw'_p]".
    iDestruct (annot_split_iupd with "Hna_lw'") as ">[Hna_lw'_l Hna_lw']".
    iDestruct (annot_split_iupd with "Hna_lw'") as ">[Hna_lw'_x Hna_lw'_y]".
    assert (G: (BV 64 4116 `+Z` 4)%bv = (BV 64 4120)%bv); [bv_solve|]. rewrite G;clear G.
    iDestruct (lpo_to_po with "Hpo_src") as "[Hpo_src #Hpo_src_b]".

    (* Write x *)
    iApply sswpi_wpi. iApply (sswpi_mono with "[Hlocalw_x Hprot_x Hpo_src Hctrl_src Hna_lw'_x]").
    {
      iApply (istore_pln (λ eid, shot_x eid) {[eid_b]} {[eid_lw' := pending_x 1]} with "[$Hpo_src $Hctrl_src $Hlocalw_x Hna_lw'_x]").
      { iFrame "#∗". rewrite big_sepS_singleton big_sepM_singleton. iFrame "#∗". }

      iExists _,_,_. iSplitL. iIntros "H";iFrame. iExact "H".
      iIntros (eid_w_x). iSplitR.
      {
        iIntros "HE Hpo_b _".
        rewrite big_sepS_singleton big_sepM_singleton.
        iApply po_dmbsy_po_is_lob;iFrame "#∗".
        iDestruct (event_node with "He_b") as "$".
      }
      {
        rewrite big_sepS_singleton big_sepM_singleton.
        iIntros "HE Htid_w_x Hpo_w_x Hp Hpending_x".
        iDestruct (shoot _ eid_w_x with "Hpending_x") as ">#Hshot_x".
        iModIntro. iSplit;first done.
        rewrite /me_x_prot.
        case_bool_decide. inversion H4.
        case_bool_decide;last done. iFrame "Hshot_x".
      }
    }
    iIntros (?) "(-> & (%eid_w_x & #He_w_x& #Htid_w_x & Hpo_src & #Hpo_b_w_x & Hlocalw_x & Hctrl_src & Hna_w_x))".
    rewrite big_sepS_singleton.
    iAssert (⌜eid_b ≠ eid_w_x⌝%I) as "%Hneq_eid_w_x".
    {
      iIntros (->). iApply (po_irrefl with "Hpo_b_w_x").
    }

    assert (G: ((BV 64 4120) `+Z` 4 = (BV 64 4124))%bv); [bv_solve|]. rewrite G. clear G.
    iDestruct (lpo_to_po with "Hpo_src") as "[Hpo_src #Hpo_src_w_x]".

    (* Write y *)
    iApply sswpi_wpi. iApply (sswpi_mono with "[Hlocalw_y Hprot_y Hpo_src Hctrl_src Hna_lw'_y]").
    {
      iApply (istore_pln (λ eid, shot_y eid) {[eid_b;eid_w_x]}
                {[eid_lw' := pending_y 1]} with "[$Hpo_src $Hctrl_src $Hlocalw_y Hna_lw'_y]").
      {
        iFrame "#∗". rewrite big_sepM_singleton. iFrame "#∗".
        rewrite big_sepS_union. rewrite 2!big_sepS_singleton. iFrame "#". set_solver + Hneq_eid_w_x.
      }
      iExists _,_,_. iSplitL. iIntros "H";iFrame;iExact "H".
      iIntros (eid_w_y). iSplitR.
      {
        rewrite big_sepS_union; last set_solver + Hneq_eid_w_x.
        iIntros "HE [Hpo_b _] _".
        rewrite big_sepM_singleton.
        iApply po_dmbsy_po_is_lob;iFrame "#∗".
        iDestruct (event_node with "He_b") as "$".
        rewrite big_sepS_singleton. iFrame "Hpo_b".
      }
      {
        rewrite big_sepM_singleton.
        iIntros "HE Htid_w_y Hpos Hp Hpending_y".
        iDestruct (shoot _ eid_w_y with "Hpending_y") as ">#Hshot_y".
        iModIntro. iFrame "#∗".
      }
    }
    iIntros (?) "(-> & (%eid_w_y & #He_w_y & #Htid_w_y & Hpo_src & Hpos & Hlocalw_y & Hctrl_src & Hna_w_y))".

    rewrite big_sepS_union; last set_solver + Hneq_eid_w_x.
    rewrite 2!big_sepS_singleton.
    iDestruct "Hpos" as "[#Hpo_b_w_y #Hpo_w_x_w_y]".

    iAssert (⌜eid_w_x ≠ eid_w_y⌝%I) as "%Hneq_eid_w_y".
    {
      iIntros (->). iApply (po_irrefl with "Hpo_w_x_w_y").
    }

    assert (G: ((BV 64 4124) `+Z` 4 = (BV 64 4128))%bv); [bv_solve|]. rewrite G. clear G.
    iDestruct (lpo_to_po with "Hpo_src") as "[Hpo_src #Hpo_src_w_y]".

    iDestruct (annot_merge_iupd with "Hna_lw'_p Hna_lw'_l") as ">Hna_lw'_l".

    iApply (release _ _ {[eid_w_x; eid_w_y]}
                    {[eid_w_x := shot_x eid_w_x; eid_w_y := shot_y eid_w_y ; eid_lw' := _]} emp
             with "Hpo_src [] Hctrl_src Hrmw_src Hlocalw_l [#$] [Hna_w_x Hna_w_y Hna_lw'_l]").
    {
      rewrite 3!dom_insert_L. set_solver +.
    }
    {
      rewrite big_sepS_union. rewrite 2!big_sepS_singleton.  iFrame "#".
      set_solver + Hneq_eid_w_y.
    }
    {
      iApply (big_sepM_insert_2 with "Hna_w_x").
      iApply (big_sepM_insert_2 with "Hna_w_y").
      iApply (big_sepM_singleton with "Hna_lw'_l").
    }
    {
      iExists _. iSplitL.
      iAssert (⌜eid_lw' ≠ eid_w_x⌝%I) as "%Hneq_eid_lw'_x".
      {
        iIntros (->).
        iDestruct (po_trans with "Hpo_lw'b Hpo_b_w_x" ) as "HH".
        iApply (po_irrefl with "HH").
      }

      iAssert (⌜eid_lw' ≠ eid_w_y⌝%I) as "%Hneq_eid_lw'_y".
      {
        iIntros (->).
        iDestruct (po_trans with "Hpo_lw'b Hpo_b_w_y" ) as "HH".
        iApply (po_irrefl with "HH").
      }

      rewrite big_sepM_insert.
      2: { simplify_map_eq /=. done. }
      rewrite big_sepM_insert.
      2: { simplify_map_eq /=. done. }
      rewrite big_sepM_singleton.

      iIntros "(H1 & H2 & $ & H3)".
      iCombine "H1 H2 H3" as "HH". iExact "HH".

      iIntros (?).

      iDestruct (po_trans with "Hpo_lw'b Hpo_b_w_y") as "#Hpo_lw'_w_y".
      iDestruct (po_trans with "Hpo_lw'b Hpo_b_w_x") as "#Hpo_lw'_w_x".
      iAssert (⌜eid_lw' ≠ eid_w_x⌝%I) as "%Hneq_eid_w_x'".
      { iIntros (->). iApply (po_irrefl with "Hpo_lw'_w_x"). }
      iAssert (⌜eid_lw' ≠ eid_w_y⌝%I) as "%Hneq_eid_w_y'".
      { iIntros (->). iApply (po_irrefl with "Hpo_lw'_w_y"). }
      iSplitL.
      {
        (* graph reasoning *)
        rewrite 3!dom_insert_L.
        iIntros "_ Hpo".
        rewrite big_sepS_union;last set_solver + Hneq_eid_w_y.
        rewrite 2!big_sepS_singleton.
        iDestruct "Hpo" as "[#Hpo_w_x_r #Hpo_w_y_r]".
        rewrite dom_empty_L. rewrite union_empty_r_L.
        assert ((({[eid_w_x]} ∪ {[eid_w_y; eid_lw']})
                      ∖ {[eid_w_x; eid_w_y]}) = ({[eid_lw']}: gset Eid)) as ->.
        { set_solver + Hneq_eid_w_x' Hneq_eid_w_y'. }
        rewrite big_sepS_singleton.
        iApply (po_dmbsy_po_is_lob with "Hpo_lw'b [] []").
        { iApply (event_node with "He_b"). }
        { iApply (po_trans with "Hpo_b_w_y Hpo_w_y_r"). }
      }
      iIntros "(#He_r&Hpos&HP)".
      iDestruct "HP" as "(Hshot_x & Hshot_y & Hpending_l)".
      iMod (shoot_l with "Hpending_l") as "Hshot_l".
      iModIntro. iSplit;last done. iRight. iFrame "Hshot_l".
      iExists eid_w_x, eid_w_y. iFrame.
      rewrite big_sepS_union;last set_solver.
      rewrite 2!big_sepS_singleton.
      iDestruct "Hpos" as "[Hpo1 Hpo2]".
      iDestruct "Htid_w_x" as %Htid_x. iDestruct "Htid_w_y" as %Htid_y.
      iSplit; first (iPureIntro;lia). iSplit; first (iPureIntro;lia).
      iFrame "#". iSplitL "Hpo1".
      iApply lob_is_ob.
      iApply (po_rel_is_lob with "Hpo1").
      { iApply (event_node with "He_r"). }
      iApply lob_is_ob.
      iApply (po_rel_is_lob with "Hpo2").
      { iApply (event_node with "He_r"). }
    }
    iIntros "_".

    assert (G: ((BV 64 4128) `+Z` 4 = (BV 64 4132))%bv); [bv_solve|]. rewrite G. clear G.

    iApply sswpi_wpi. iApply idone;auto.
    iApply wpi_terminated.
    iApply (inst_post_lifting_lifting _ _ ∅ ∅);auto. set_solver.
  Qed.

End mutual_exclusion.
