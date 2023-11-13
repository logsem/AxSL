From stdpp.unstable Require Import bitvector bitvector_tactics.

From iris.proofmode Require Import tactics.

From self.low Require Export instantiation.
From self.middle Require Import rules specialised_rules.
Require Import ISASem.SailArmInstTypes.

Import uPred.

Definition data := (BV 64 0x10).
Definition flag := (BV 64 0x18).

Definition data_write : Instruction := 
  (IStore AS_normal AV_plain "r0" (AEval (BV 64 42)) (AEval data)).
Definition flag_write : Instruction :=
  (IStore AS_rel_or_acq AV_plain "r0" (AEval (BV 64 1)) (AEval flag)).

Definition flag_read kind:=
  (ILoad kind AV_plain "r1" (AEval flag)).
Definition receive_barrier:=
  (IDmb AAArch.Sy). 
Definition data_read :=
  (ILoad AS_normal AV_plain "r2" (AEval data)).

Section proof.
  Context `{AAIrisG}.

  Context (tid1 tid2: Tid).
  Context (Htid_ne :tid1 ≠ tid2).

  Definition data_prot (v : Val) (e : Eid) : iProp Σ :=
    (⌜v= (BV 64 42)⌝ ∗ ⌜EID.tid e = tid1⌝) ∨ ⌜EID.tid e = 0%nat⌝.

  Definition flag_prot (e : Eid) : iProp Σ :=
    ⌜EID.tid e = 0%nat⌝
    ∨ ∃ d,
        ⌜EID.tid e = tid1 ⌝ ∗ ⌜EID.tid d = tid1⌝ ∗
        d -{Edge.Po}> e ∗
        d -{E}> (Event.W AS_normal AV_plain data (BV 64 42)) ∗
        e -{E}> (Event.W AS_rel_or_acq AV_plain flag (BV 64 1)).

  Definition send_instrs : iProp Σ :=
    (BV 64 0x1000) ↦ᵢ data_write ∗
    (BV 64 0x1004) ↦ᵢ flag_write ∗
    (BV 64 0x1008) ↦ᵢ -.

  Definition receive_instrs : iProp Σ :=
    (BV 64 0x2000) ↦ᵢ flag_read AS_rel_or_acq ∗
    (BV 64 0x2004) ↦ᵢ receive_barrier ∗
    (BV 64 0x2008) ↦ᵢ data_read ∗
    (BV 64 0x200c) ↦ᵢ -.

  Definition protocol : UserProt :=
    Build_UserProt _ _(λ a v e,
                         if bool_decide (a = data) then data_prot v e
                         else if bool_decide (a = flag) then flag_prot e
                              else (⌜EID.tid e = 0%nat⌝)%I
      ).

  #[local] Instance userprot : UserProt := protocol.

  Context `{!AAThreadG} `{ThreadGN}.

  (* Note this is the same proof as in rel_acq *)
  Lemma send ctrl:
    None -{LPo}> -∗
    ctrl -{Ctrl}> -∗
    last_local_write tid1 data None -∗
    last_local_write tid1 flag None -∗
    send_instrs -∗
    WPi (LTSI.Normal, (BV 64 0x1000)) @ tid1 {{ λ lts', ⌜lts' = (LTSI.Done, (BV 64 0x1008))⌝}}.
  Proof.
    iIntros "Hpo_src Hctrl_src Hlocalw_data Hlocalw_flag Hinstrs".
    iDestruct "Hinstrs" as "(#? & #? & #?)".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hpo_src Hctrl_src Hlocalw_data]").
    {
      iApply (istore_pln (λ _, emp)%I ∅ ∅ with "[$Hpo_src $Hctrl_src $Hlocalw_data]"). iFrame "#∗".
      rewrite big_sepS_empty big_sepM_empty //.

      iIntros (?). iSplitL.
      - iIntros "_ _ _". done.
      - iIntros "#HE % #Hpo _". iModIntro. iSplit;first done. simpl. rewrite /data_prot. iLeft;done.
    }
    iIntros (?) "(-> &[% (#Hwrite&%Htid1&Hpo&_&Hlocal&Hctrl&HeidP)])".
    assert (G: ((BV 64 4096) `+Z` 4 = (BV 64 4100))%bv) by bv_solve. rewrite G.

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hlocalw_flag Hwrite Hpo Hctrl HeidP]").
    {
      iDestruct (lpo_to_po with "Hpo") as "[Hlpo #Hpo]".
      iApply (istore_rel emp {[eid := emp%I]}). iFrame "#∗".

      iSplit;first rewrite big_sepM_singleton //.
      iSplitL;first rewrite big_sepM_singleton //.

      iIntros (eid') "#Hwrite' %Htid2 #Hpo' HeidP'".
      iModIntro. iSplit;first done. iModIntro.
      iRight. iExists eid.  rewrite big_sepM_singleton. by iFrame "#".
    }
    iIntros (?) "(-> &[% (?&?&?)])".
    clear G. assert (G: ((BV 64 4100) `+Z` 4 = (BV 64 4104))%bv); [bv_solve|]. rewrite G.

    iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 4104)⌝)%I).
    { by iApply idone. }
    iIntros (? ->). iApply wpi_terminated. iApply (inst_post_lifting_lifting _ _ _ ∅); auto. rewrite dom_empty_L //.
  Qed.

  Definition receive ctrl :
    None -{LPo}> -∗
    ctrl -{Ctrl}> -∗
    None -{Rmw}> -∗
    last_local_write tid2 data None -∗
    last_local_write tid2 flag None -∗
    (∃ rv, "r1" ↦ᵣ rv) -∗
    (∃ rv, "r2" ↦ᵣ rv) -∗
    receive_instrs -∗
    WPi (LTSI.Normal, (BV 64 0x2000)) @ tid2 {{ λ lts',
                                                  ⌜lts' = (LTSI.Done, (BV 64 0x200c))⌝ ∗
                                                  ∃ r1 r2, "r1" ↦ᵣ r1 ∗ "r2" ↦ᵣ r2 ∗
                                                    (⌜r1.(reg_val)  = (BV 64 1)⌝ -∗ ⌜r2.(reg_val) = (BV 64 42)⌝)
      }}.
  Proof.
    iIntros "Hlpo Hctrl Hrmw Hllwd Hllwf [% Hr1] [% Hr2] Hinstrs".
    iDestruct "Hinstrs" as "(#? & #? & #? & #?)".
    iApply sswpi_wpi. iApply (sswpi_mono with "[Hr1 Hlpo Hctrl Hrmw Hllwf]").
    {
      iApply (iload_pln _ ∅ ∅ with "[$Hr1 $Hlpo $Hctrl $Hrmw $Hllwf]"). iFrame "∗#".
      rewrite big_sepM_empty big_sepS_empty //.

      iIntros (?). iSplitR.
      - iIntros "_ _". rewrite big_sepM_empty //.
      - iIntros (??) "_ _ _ _ _ _ #Hprot". iModIntro. iExact "Hprot".
    }
    iIntros (?) "(-> & %eid_fr & %eid_fw & % & #Hfread & %Hfread_tid & Hr1 & Hannot & (% & % & #Hfwrite) & #Hrf & Hlpo & _ & Hctrl & Hrmw & _)".
    assert (G: ((BV 64 8192) `+Z` 4 = (BV 64 8196))%bv); [bv_solve|]. rewrite G.

    iDestruct (lpo_to_po with "Hlpo") as "[Hlpo #Hpo]".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hlpo]").
    {
      iApply idmb; [iFrame "#" | iExact "Hlpo"].
    }

    iIntros (?) "(-> & %eid_dmb & #Hdmb & #Hpo1 & Hlpo)".
    simpl.
    assert (G' : ((BV 64 8196) `+Z` 4 = (BV 64 8200))%bv); [bv_solve |]. rewrite G'.

    iClear "Hpo".
    iDestruct (lpo_to_po with "Hlpo") as "[Hlpo #Hpo]".

    iApply sswpi_wpi. iApply (sswpi_mono with "[Hr2 Hlpo Hannot Hctrl Hrmw Hllwd]").
    {
      iApply (iload_pln (λ e v', ⌜v = (BV 64 1)⌝ -∗ ⌜v' = (BV 64 42)⌝)%I {[eid_dmb]} {[eid_fr := prot flag v eid_fw]} with "[$Hr2 $Hlpo $Hctrl $Hrmw $Hllwd Hannot]"). iFrame "∗#".
      { rewrite big_sepM_singleton big_sepS_singleton. iFrame "#∗". }
      iIntros (?). iSplitR.
      - iIntros "HN HPo". rewrite big_sepM_singleton big_sepS_singleton.
        iApply (po_dmbsy_po_is_lob with "Hpo1 [Hdmb] HPo").
        { iDestruct (event_node with "Hdmb") as "$". }
      - iIntros (??) "#Hdread % #HPo (% &% &#Hwrite') #Hrf' Hannot". rewrite big_sepM_singleton big_sepS_singleton.
        iIntros "#Hdata". iModIntro. iIntros (->).
        rewrite /prot /= /data_prot /flag_prot.
        iDestruct "Hdata" as "[(% & %)|%Hdata]"; [done|].
        iDestruct (write_of_read with "Hfread Hrf") as "(% & % & Hfw)".
        iDestruct "Hannot" as "[%Hannot|Hannot]".
        { iDestruct (initial_write_zero _ _ _ _ _ Hannot with "Hfw") as "%F". contradict F. bv_solve. }
        iClear "Hfw".
        iDestruct "Hannot" as "(%d & %Hfwrite_tid & %Hd_tid & #Hsendpo & #Hd & #Hfw)".
        iDestruct (initial_write_co with "Hwrite' Hd") as "Hco"; [done| |].
        { rewrite Hd_tid.  pose proof tid_nz_nz. lia. }
        iDestruct (po_rel_is_lob with "Hsendpo [Hfw]") as "Hsendob".
        { iDestruct (event_node with "Hfw") as "$". }
        iDestruct (po_dmbsy_po_is_lob with "Hpo1 [Hdmb] HPo") as "Hreadob".
        { iDestruct (event_node with "Hdmb") as "$". }
        iDestruct (rf_co_to_fr with "Hrf' Hco") as "Hfr".
        iDestruct (rfe_is_ob with "Hrf") as "Hob2"; [lia|].
        iDestruct (fre_is_ob with "Hfr") as "Hob4"; [lia|].
        iDestruct (lob_is_ob with "Hsendob") as "Hob1".
        iDestruct (lob_is_ob with "Hreadob") as "Hob3".
        iDestruct (ob_trans with "Hob1 Hob2") as "Hob".
        iDestruct (ob_trans with "Hob Hob3") as "Hob'".   
        iDestruct (ob_trans with "Hob' Hob4") as "Hob''".
        iDestruct (ob_acyclic with "Hob''") as "[]".
    }
    iIntros (?) "(-> & % & % & % & Hdread & % & Hr2 & Hdannot & _ & _ & Hlpo & _ & Hctrl & Hrmw & _)".
    subst. assert (G'': ((BV 64 8200) `+Z` 4 = (BV 64 8204))%bv); [bv_solve|]. rewrite G''.
    
    iApply sswpi_wpi. iApply (sswpi_mono _ _ _ (λ s', ⌜s' = (LTSI.Done, BV 64 8204)⌝)%I).
    { by iApply idone. }
    iIntros (? ->). iApply wpi_terminated. iApply (inst_post_lifting_lifting _ _ _ {[eid := _]} with "[Hdannot]"); auto.
    { simpl. rewrite dom_singleton_L. set_solver. }
    { rewrite big_sepM_singleton. iExact "Hdannot". }
    rewrite big_sepM_singleton.
    iIntros "% !>". iSplit;first done.
    iExists _, _.  iFrame. auto.
  Qed.
End proof.
