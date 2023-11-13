From stdpp.unstable Require Import bitvector bitvector_tactics.

From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.

From self.middle Require Import rules specialised_rules.
Require Import ISASem.SailArmInstTypes.

Import uPred.

Definition data := (BV 64 1).
Definition addr_x := (BV 64 0x11).
Definition addr_y := (BV 64 0x10).

Notation read reg addr := (ILoad AS_normal AV_plain reg (AEval addr)).
Notation write_val addr := (IStore AS_normal AV_plain "r1" (AEval data) (AEval addr)).
Notation branch reg val addr := (IBne (AEbinop AOminus (AEreg reg) (AEval val)) addr).

(* the token ghost state *)
Class LbInPreG `{CMRA Σ} := {
    LbDatasOneShot :> inG Σ (csumR (exclO unitO)
                             (agreeR (leibnizO Val)));
  }.

Class LbInG `{CMRA Σ} := {
    LbIn :> LbInPreG;
    LbOneShotN : gname;
  }.

#[global] Arguments LbOneShotN {Σ _ _}.

Definition LbΣ : gFunctors :=
  #[ GFunctor (csumR (exclO unitO)
                             (agreeR (leibnizO Val)))].

#[global] Instance subG_LbInPreG `{CMRA Σ}: subG LbΣ Σ -> LbInPreG.
Proof. solve_inG. Qed.

Section one_shot.
  Context `{CMRA Σ} `{!LbInG}.

  Definition pending := own LbOneShotN (Cinl (Excl ())).

  Definition shot v := own LbOneShotN (Cinr (to_agree v)).

  Lemma pending_shot v: pending -∗ shot v -∗ False.
  Proof.
    rewrite /pending /shot. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as "Hvalid".
    rewrite csum_validI //=.
  Qed.

  Lemma shoot v: pending ==∗ shot v.
  Proof.
    rewrite /pending /shot. iIntros "H".
    iApply (own_update with "H").
    apply cmra_update_exclusive.
    rewrite Cinr_valid. done.
  Qed.

  #[global] Instance shot_persist v: Persistent (shot v).
  Proof.
    rewrite /shot. apply _.
  Qed.

End one_shot.

Section ctrls.
  Context `{AAIrisG} `{!AAThreadG} `{ThreadGN}.
  Context `{!LbInG}.

  Definition instrs : iProp Σ :=
    (BV 64 0x1000) ↦ᵢ read "r1" addr_x ∗
    (BV 64 0x1004) ↦ᵢ branch "r1" (BV 64 0) (BV 64 0x1008) ∗
    (BV 64 0x1008) ↦ᵢ write_val addr_y ∗
    (BV 64 0x100C) ↦ᵢ - ∗
    (BV 64 0x2000) ↦ᵢ read "r2" addr_y ∗
    (BV 64 0x2004) ↦ᵢ branch "r2" data (BV 64 0x200C) ∗
    (BV 64 0x2008) ↦ᵢ write_val addr_x ∗
    (BV 64 0x200C) ↦ᵢ -.

  Definition lb_prot_val (v : Val) : iProp Σ :=
    ⌜v = bv_0 _⌝ ∨ (⌜ v = data ⌝ ∗ shot v).

  #[local] Instance userprot_val : UserProt :=
    Build_UserProt _ _(λ a v e,
                         if (bool_decide (a = addr_x)) || (bool_decide (a = addr_y))
                         then lb_prot_val v
                         else False%I
      ).

  Definition thread_1 tid :
    None -{LPo}> -∗
    ∅ -{Ctrl}> -∗
    None -{Rmw}> -∗
    pending -∗
    (∃ rv, "r1" ↦ᵣ rv) -∗
    last_local_write tid addr_x None -∗
    last_local_write tid addr_y None -∗
    instrs -∗
    WPi (LTSI.Normal, (BV 64 0x1000)) @ tid
      {{ λ lts',
           (⌜lts' = (LTSI.Done, (BV 64 0x100C))⌝ ∗
           ∃ rv, "r1" ↦ᵣ rv ∗ ⌜rv.(reg_val) = bv_0 _⌝)
      }}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hrmw Hpending [% Hreg] Hlocalw_x Hlocalw_y Hinstrs".
    iDestruct "Hinstrs" as "(#? & #? & #? & #? & _)".
    iApply sswpi_wpi. iApply (sswpi_mono with "[Hpo_src Hctrl_src Hlocalw_x Hrmw Hreg Hpending]").
    {
      iApply (iload_pln (λ _ v, ⌜v = bv_0 _⌝ ∗  (⌜v = bv_0 _⌝ ∗ pending))%I ∅ ∅ with "[-Hpending] [Hpending]").
      iFrame "#∗". rewrite big_sepS_empty big_sepM_empty //.

      iIntros (?). iSplitR.
      iIntros "_ _". done.
      iIntros (??) "_ _ _ _ _ _ [#H1|#[H2 Hshot]]".
      iFrame "Hpending". by iFrame "H1".
      iExFalso. iApply (pending_shot with "Hpending Hshot").
    }
    iIntros (?) "(-> &(%&%&%&(#Hwrite&%&Hreg&Hna&_&Hrfe&Hlpo&_&Hctrl&Hrmw&_)))".
    assert (G: ((BV 64 4096) `+Z` 4 = (BV 64 4100))%bv); [bv_solve|]. rewrite G;clear G.
    iDestruct (annot_split_iupd with "Hna") as ">[Hna1 Hna2]".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hreg Hctrl]").
    {
      iApply (ibne {["r1" := _ ]} with "[] [Hctrl]" ); [ | | iFrame "#" | iFrame | ].
      set_solver.
      2: { by rewrite big_sepM_singleton. }
      + simpl. rewrite lookup_insert /=. reflexivity.
    }
    iIntros (?) "(Hreg & Hctrl & [[-> _]|[-> %]])".
    {
      assert (G: ((BV 64 4100) `+Z` 4 = (BV 64 4104))%bv); [bv_solve|]. rewrite G.

      rewrite big_sepM_singleton.
      rewrite (@map_fold_singleton _ _ _ _ _ _ _ _ _ _ _ RegVal) /=.
      rewrite union_empty_r_L. rewrite union_empty_r_L.

      iApply sswpi_wpi. iApply (sswpi_mono with "[Hlocalw_y Hwrite Hlpo Hctrl Hna2]").
      {
        iApply (istore_pln (λ _, emp)%I ∅ {[eid := _]} with "[Hlpo Hctrl Hlocalw_y Hna2]"). iFrame "#∗".
        iSplitR;first done. rewrite big_sepM_singleton. iFrame "Hna2".
        iIntros (eid'').
        iSplitR.
        - iIntros "HE _ Hctrls". rewrite big_sepM_singleton /=. rewrite big_sepS_singleton.
          iApply (ctrl_w_is_lob with "HE Hctrls").
        - iIntros "#Hwrite' % #Hpo''' P".
          rewrite big_sepM_singleton. iDestruct "P" as "[% Hpending]".
          iDestruct (shoot data with "Hpending") as ">#Hshot".
          iModIntro. iSplitR;first done. iModIntro. iRight. iFrame "Hshot". done.
      }
      iIntros (?) "(->& (% &?&?&?&?&?&?&?))".
      subst. clear G. assert (G: ((BV 64 4104) `+Z` 4 = (BV 64 4108))%bv); [bv_solve|]. rewrite G.

      iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 4108)⌝)%I).
      { by iApply idone. }
      iIntros (? ->). iApply wpi_terminated.
      iApply (inst_post_lifting_lifting _ _ _ {[eid:= ⌜v = bv_0 _⌝%I]} with "[Hna1]").
      rewrite dom_singleton_L set_Forall_singleton //.
      rewrite big_sepM_singleton //.
      rewrite big_sepM_singleton //. iIntros. iModIntro.
      iSplit;first done. iExists _. iFrame. simpl. done.
    }
    {
      rewrite big_sepM_singleton.
      rewrite (@map_fold_singleton _ _ _ _ _ _ _ _ _ _ _ RegVal) /=.
      rewrite union_empty_r_L. rewrite union_empty_r_L.

      iApply sswpi_wpi. iApply (sswpi_mono with "[Hlocalw_y Hwrite Hlpo Hctrl Hna2]").
      {
        iApply (istore_pln (λ _, emp)%I ∅ {[eid := _]} with "[Hlpo Hctrl Hlocalw_y Hna2]"). iFrame "#∗".
        iSplitR;first done. rewrite big_sepM_singleton. iFrame "Hna2".
        iIntros (eid'').
        iSplitR.
        - iIntros "HE _ Hctrls". rewrite big_sepM_singleton /=. rewrite big_sepS_singleton.
          iApply (ctrl_w_is_lob with "HE Hctrls").
        - iIntros "#Hwrite' % #Hpo''' P".
          rewrite big_sepM_singleton. iDestruct "P" as "[% Hpending]".
          iDestruct (shoot data with "Hpending") as ">#Hshot".
          iModIntro. iSplitR;first done. iModIntro. iRight. iFrame "Hshot". done.
      }
      iIntros (?) "(->& (% &?&?&?&?&?&?&?))".
      subst. assert (G: ((BV 64 4104) `+Z` 4 = (BV 64 4108))%bv); [bv_solve|]. rewrite G.

      iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 4108)⌝)%I).
      { by iApply idone. }
      iIntros (? ->). iApply wpi_terminated.
      iApply (inst_post_lifting_lifting _ _ _ {[eid:= ⌜v = bv_0 _⌝%I]} with "[Hna1]").
      rewrite dom_singleton_L set_Forall_singleton //.
      rewrite big_sepM_singleton //.
      rewrite big_sepM_singleton //. iIntros. iModIntro.
      iSplit;first done. iExists _. iFrame. simpl. done.
    }
  Qed.

  Definition thread_2 tid :
    None -{LPo}> -∗
    ∅ -{Ctrl}> -∗
    None -{Rmw}> -∗
    (∃ rv, "r2" ↦ᵣ rv) -∗
    last_local_write tid addr_x None -∗
    last_local_write tid addr_y None -∗
    instrs -∗
    WPi (LTSI.Normal, (BV 64 0x2000)) @ tid
      {{ λ lts',
           ⌜lts' = (LTSI.Done, (BV 64 0x200C))⌝ ∗
           ∃ rv, "r2" ↦ᵣ rv ∗ ⌜rv.(reg_val) = bv_0 _ ∨ rv.(reg_val) = data ⌝
      }}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hrmw [% Hreg] Hlocalw_x Hlocalw_y Hinstrs".
    iDestruct "Hinstrs" as "(_ & _ & _ & _ & #? & #? & #? & #?)".
    iApply sswpi_wpi.
    iApply (sswpi_mono with "[Hpo_src Hctrl_src Hlocalw_y Hrmw Hreg]").
    {
      iApply (iload_pln (λ _ v, lb_prot_val v ∗ lb_prot_val v)%I ∅ ∅ with "[-] []").
      iFrame "#∗". rewrite big_sepM_empty big_sepS_empty //.

      iIntros (?). iSplitR.
      - iIntros "_ _". done.
      - iIntros (??) "_ _ _ _ _ _ #?". by iFrame "#".
    }
    iIntros (?) "(->&(%&%&%&(#Hwrite&%&Hreg&Hna&_&Hrfe&Hpo&_&Hctrl&Hrmw&_)))".
    assert (G: ((BV 64 8192) `+Z` 4 = (BV 64 8196))%bv); [bv_solve|]. rewrite G.
    iDestruct (annot_split_iupd with "Hna") as ">[Hna1 Hna2]".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hreg Hctrl]").
    {
      iApply (ibne {["r2" := _ ]} with "[] [Hctrl]" ); [ | | iFrame "#" | iFrame | ].
      set_solver.
      2: { by rewrite big_sepM_singleton. }
      + simpl. rewrite lookup_insert /=. reflexivity.
    }
    iIntros (?) "(Hreg & Hctrl & [[-> %]|[-> %]])".
    {
      clear G. assert (G: ((BV 64 8196) `+Z` 4 = (BV 64 8200))%bv); [bv_solve|]. rewrite G.

      rewrite big_sepM_singleton.
      rewrite (@map_fold_singleton _ _ _ _ _ _ _ _ _ _ _ RegVal) /=.
      rewrite union_empty_r_L. rewrite union_empty_r_L.

      iApply sswpi_wpi. iApply (sswpi_mono with "[Hlocalw_x Hwrite Hpo Hctrl Hna1]").
      {
        iApply (istore_pln (λ _, emp)%I ∅ {[eid := _]} with "[Hpo Hctrl Hlocalw_x Hna1]"). iFrame "#∗".
        iSplitR;first done. rewrite big_sepM_singleton. iFrame "Hna1".
        iIntros (eid'').
        iSplitR.
        - iIntros "HE _ Hctrls". rewrite big_sepM_singleton /=. rewrite big_sepS_singleton.
          iApply (ctrl_w_is_lob with "HE Hctrls").
        - iIntros "#Hwrite' % #Hpo''' P".
          rewrite big_sepM_singleton.
          iDestruct "P" as "#P".
          iModIntro. iSplitR;first done. iModIntro. simpl.
          rewrite /lb_prot_val.
          assert (v = data)%bv as Heq.
          {
            clear -H5.
            rewrite /data in H5. rewrite /data.
            destruct (bool_decide (v = BV 64 1)) eqn:Heqn.
            rewrite bool_decide_eq_true in Heqn. done.
            rewrite bool_decide_eq_false in Heqn.
            unfold Val in v. unfold AAArch.val in v. unfold AAval in v. unfold AAArch.val_size in v.
            assert ((v - BV 64 1)%bv = (v `-Z` 1)%bv). bv_solve.
            rewrite H in H5. clear H.
            assert (bv_unsigned v ≠ 1).
            { intro Heq. apply Heqn. apply bv_eq. rewrite Heq. done. }
            apply bv_eq in H5.
            rewrite bv_sub_Z_unsigned /= in H5.
            rewrite bv_unsigned_BV in H5.
            bv_simplify_arith. bv_saturate_unsigned; bv_solve_unfold_tac.
            unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, bv_unsigned in *.
            simpl in *. destruct v. lia.
          }
          iDestruct "P" as "[-> | [-> Hshot]]".
          {
            rewrite /data in Heq.
            assert (bv_0 64 = BV 64 0)%bv. bv_solve.
            rewrite H7 in Heq. inversion Heq.
          }
          {
            iRight. iFrame "Hshot". done.
          }
      }
      iIntros (?) "(->& (% &?&?&?&?&?&?&?))".
      subst. clear G. assert (G: ((BV 64 8200) `+Z` 4 = (BV 64 8204))%bv); [bv_solve|]. rewrite G.

      iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 8204)⌝)%I).
      { by iApply idone. }
      iIntros (? ->). iApply wpi_terminated.
      iApply (inst_post_lifting_lifting _ _ _ {[eid:= (lb_prot_val v)]} with "[Hna2]").
      rewrite dom_singleton_L set_Forall_singleton //.
      rewrite big_sepM_singleton //.
      rewrite big_sepM_singleton //. iIntros "#Hprot". iModIntro.
      iSplit;first done. iExists _. iFrame. simpl. iDestruct "Hprot" as "[#? | [#? _]]".

      iLeft. done. iRight. done.
    }
    {
      rewrite big_sepM_singleton.
      rewrite (@map_fold_singleton _ _ _ _ _ _ _ _ _ _ _ RegVal) /=.
      rewrite union_empty_r_L. rewrite union_empty_r_L.

      iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 8204)⌝)%I).
      { by iApply idone. }
      iIntros (? ->). iApply wpi_terminated.
      iApply (inst_post_lifting_lifting _ _ _ {[eid:= (lb_prot_val v)]} with "[Hna2]").
      rewrite dom_singleton_L set_Forall_singleton //.
      rewrite big_sepM_singleton //.
      rewrite big_sepM_singleton //. iIntros "#Hprot". iModIntro.
      iSplit;first done. iExists _. iFrame. simpl. iDestruct "Hprot" as "[#? | [#? _]]".

      iLeft. done. iRight. done.
    }
  Qed.

End ctrls.
