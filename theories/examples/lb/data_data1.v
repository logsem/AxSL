From stdpp.unstable Require Export bitvector.
From stdpp.unstable Require Import bitvector_tactics.

From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.

From self.middle Require Import rules specialised_rules.
Require Import ISASem.SailArmInstTypes.

Import uPred.

Definition data := (BV 64 1).
Definition addr_x := (BV 64 0x11).
Definition addr_y := (BV 64 0x10).

Notation write reg addr := (IStore AS_normal AV_plain "r0" (AEreg reg) (AEval addr)).
Notation read reg addr := (ILoad AS_normal AV_plain reg (AEval addr)).

Ltac fold_continuation :=
    match goal with | |- context [AAInter.Next _ ?cont] => set(ctx:=cont) end.

Section write_reg.
  Context `{AAIrisG} `{!AAThreadG} `{ThreadGN}.

  (* for this thin-air version we can only show that the outcome must be [00] *)
  Definition instrs : iProp Σ :=
    (BV 64 0x1000) ↦ᵢ read "r1" addr_x ∗
    (BV 64 0x1004) ↦ᵢ write "r1" addr_y ∗
    (BV 64 0x1008) ↦ᵢ - ∗
    (BV 64 0x2000) ↦ᵢ read "r2" addr_y ∗
    (BV 64 0x2004) ↦ᵢ write "r2" addr_x ∗
    (BV 64 0x2008) ↦ᵢ -.

  Definition lb_prot (v : Val) : iProp Σ :=
    ⌜v = BV 64 0⌝.

  Definition protocol : UserProt :=
    Build_UserProt _ _(λ a v e,
                         if (bool_decide (a = addr_x)) || (bool_decide (a = addr_y))
                         then lb_prot v
                         else True%I
      ).

  Local Instance userprot : UserProt := protocol.

  Definition write_reg_thread_1 tid :
    None -{LPo}> -∗
    ∅ -{Ctrl}> -∗
    None -{Rmw}> -∗
    (∃ rv, "r1" ↦ᵣ rv) -∗
    last_local_write tid addr_x None -∗
    last_local_write tid addr_y None -∗
    instrs -∗
    WPi (LTSI.Normal, (BV 64 0x1000)) @ tid
      {{ λ lts',
           ⌜lts' = (LTSI.Done, (BV 64 0x1008))⌝ ∗
           ∃ rv, "r1" ↦ᵣ rv ∗ ⌜rv.(reg_val) = BV 64 0⌝
      }}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hrmw [% Hreg] Hlocalw_x Hlocalw_y Hinstrs".
    iDestruct "Hinstrs" as "(#? & #? & #? & _ & _)".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hpo_src Hctrl_src Hlocalw_x Hrmw Hreg]").
    {
      iApply (iload_pln (λ _ v, lb_prot v ∗ lb_prot v)%I ∅ ∅ with "[-] []").
      iFrame "#∗".  rewrite big_sepM_empty big_sepS_empty //.

      iIntros. iSplitL.
      - iIntros "_ _". rewrite big_sepM_empty //.
      - iIntros (??) "_ _ _ _ _ _ %". iPureIntro. done.
    }
    iIntros (?) "(->&(%&%&%&(#Hwrite&%&Hreg&Hna&_&Hrfe&Hpo&_&Hctrl&Hrmw&_)))".
    assert (G: ((BV 64 4096) `+Z` 4 = (BV 64 4100))%bv); [bv_solve|]. rewrite G.

    iDestruct (annot_split_iupd with "Hna") as ">[Hna1 Hna2]".
    iApply sswpi_wpi. iApply (sswpi_mono with "[Hlocalw_y Hwrite Hpo Hctrl Hrmw Hreg Hna1]").
    {
      iApply istore_pln_single_data. iFrame "#∗".
      iIntros (eid'') "#Hwrite' _ #Hpo #Hdata %Hprot".
      iModIntro. simpl. done.
    }
    iIntros (?) "(%&[? (%&?&?&?&?)])".
    subst. clear G. assert (G: ((BV 64 4100) `+Z` 4 = (BV 64 4104))%bv); [bv_solve|].
    rewrite G.

    iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 4104)⌝)%I).
    { by iApply idone. }
    iIntros (? ->). iApply wpi_terminated.
    iApply (inst_post_lifting_lifting _ _ _ {[eid:= (lb_prot v)]} with "[Hna2]").
    rewrite dom_singleton_L set_Forall_singleton //.
    rewrite big_sepM_singleton //.
    rewrite big_sepM_singleton //. iIntros. iModIntro.
    iSplit;first done. iExists _. iFrame. simpl. done.
  Qed.

  Definition write_reg_thread_2 tid :
    None -{LPo}> -∗
    ∅ -{Ctrl}> -∗
    None -{Rmw}> -∗
    (∃ rv, "r2" ↦ᵣ rv) -∗
    last_local_write tid addr_x None -∗
    last_local_write tid addr_y None -∗
    instrs -∗
    WPi (LTSI.Normal, (BV 64 0x2000)) @ tid
      {{ λ lts',
           ⌜lts' = (LTSI.Done, (BV 64 0x2008))⌝ ∗
           ∃ rv, "r2" ↦ᵣ rv ∗ ⌜rv.(reg_val) = BV 64 0⌝
      }}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hrmw [% Hreg] Hlocalw_x Hlocalw_y Hinstrs".
    iDestruct "Hinstrs" as "(_ & _ & _ & #? & #? & #?)".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hpo_src Hctrl_src Hlocalw_y Hrmw Hreg]").
    {
      iApply (iload_pln (λ _ v, lb_prot v ∗ lb_prot v)%I ∅ ∅ with "[-] []").
      iFrame "#∗".  rewrite big_sepM_empty big_sepS_empty //.

      iIntros. iSplitL.
      - iIntros "_ _". rewrite big_sepM_empty //.
      - iIntros (??) "_ _ _ _ _ _ %". iPureIntro. done.
    }
    iIntros (?) "(->&(%&%&%&(#Hwrite&%&Hreg&Hna&_&Hrfe&Hpo&_&Hctrl&Hrmw&_)))".
    assert (G: ((BV 64 8192) `+Z` 4 = (BV 64 8196))%bv); [bv_solve|]. rewrite G.
    iDestruct (annot_split_iupd with "Hna") as ">[Hna1 Hna2]".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hlocalw_x Hwrite Hpo Hctrl Hreg Hna1]").
    {
      iApply istore_pln_single_data. iFrame "#∗".
      iIntros (eid'') "#Hwrite' _ #Hpo #Hdata %Hprot".
      iModIntro. simpl. done.
    }
    iIntros (?) "(%&[? (%&?&?&?&?)])".
    subst. clear G. assert (G: ((BV 64 8196) `+Z` 4 = (BV 64 8200))%bv); [bv_solve|]. rewrite G.

    iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 8200)⌝)%I).
    { by iApply idone. }
    iIntros (? ->). iApply wpi_terminated.
    iApply (inst_post_lifting_lifting _ _ _ {[eid:= (lb_prot v)]} with "[Hna2]").
    rewrite dom_singleton_L set_Forall_singleton //.
    rewrite big_sepM_singleton //.
    rewrite big_sepM_singleton //. iIntros. iModIntro.
    iSplit;first done. iExists _. iFrame. simpl. done.
  Qed.

End write_reg.
