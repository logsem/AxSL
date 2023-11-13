(* This file contains some highly specialised mid-level proof rules (mostly for loads and stores) *)
From stdpp.unstable Require Import bitvector bitvector_tactics.

From iris.proofmode Require Import tactics.

Require Import ISASem.SailArmInstTypes.

From self Require Import stdpp_extra.
From self.middle Require Export rules.

Import uPred.

Section rules.
  Context `{AAIrisG} `{!AAThreadG} `{ThreadGN} `{!UserProt}.
  Import ThreadState.

  Ltac load_ins :=
    rewrite sswpi_eq /sswpi_def;
    iIntros (?); iNamed 1; rewrite wpi_eq /wpi_def;
    iIntros (? [? ?]); repeat iNamed 1;
    iApply wp_sswp; iApply (sswp_strong_mono with "[Hinst]");
    first (iApply (reload with "[Hinst]");eauto); iIntros (? ->); simpl.

  (** specialised rules *)
  Lemma iload_excl `{!UserProt} {tid inst_addr kind_s ctrl rmw rv ot} R po_priors lob_priors addr reg:
    inst_addr ↦ᵢ (ILoad kind_s AV_exclusive reg (AEval addr)) ∗
    reg ↦ᵣ rv ∗
    ot -{LPo}> ∗
    ([∗ set] po_prior ∈ po_priors, po_prior -{Po}>) ∗
    ctrl -{Ctrl}> ∗
    rmw -{Rmw}> ∗
    last_local_write tid addr None ∗
    ([∗ map] lob_pred ↦ P ∈ lob_priors, lob_pred ↦ₐ P) -∗
    (∀ eid,
        (eid -{N}> (Edge.R kind_s AV_exclusive) -∗
         ([∗ set] po_prior ∈ po_priors, po_prior -{(Edge.Po)}> eid) -∗
         [∗ map] lob_prior ↦ _ ∈ lob_priors, lob_prior -{Edge.Lob}> eid) ∗
        ∀ eid' v, eid -{E}> (Event.R kind_s AV_exclusive addr v) -∗
             ⌜(EID.tid eid) = tid⌝ -∗
             ([∗ set] po_prior ∈ po_priors, po_prior -{Edge.Po}> eid) -∗
             (∃ kind_s_w kind_v_w, eid' -{E}> (Event.W kind_s_w kind_v_w addr v)) -∗
             eid' -{Edge.Rf}> eid -∗
             ([∗ map] _ ↦ P ∈ lob_priors, P) -∗
             □prot addr v eid' ==∗
             R eid' v
    ) -∗
    SSWPi (LTSI.Normal,inst_addr) @ tid
      {{ λ ltsi,
           ⌜ltsi = (LTSI.Normal, (inst_addr `+Z` 4)%bv)⌝ ∗
           ∃ eid eid' v, eid -{E}> (Event.R kind_s AV_exclusive addr v) ∗
                           ⌜(EID.tid eid) = tid⌝ ∗
                           reg ↦ᵣ mk_regval v {[eid]} ∗
                           eid ↦ₐ (R eid' v) ∗
                           (∃ kind_s_w kind_v_w, eid' -{E}> (Event.W kind_s_w kind_v_w addr v)) ∗
                           eid' -{Edge.Rf}> eid ∗ ⌜EID.tid eid' ≠ EID.tid eid⌝ ∗
                           Some eid -{LPo}> ∗
                           ctrl -{Ctrl}> ∗
                           Some eid -{Rmw}> ∗
                           last_local_write tid addr None
      }}.
  Proof.
    iIntros "(Hinst & Hr & Hlpo & Hpo & Hctrl & Hrmw & Hlast_write &HP) Hfe". load_ins.
    iApply (mem_read_external _ (dom po_priors) lob_priors with "Hlpo Hctrl Hlast_write Hrmw [Hpo] [] HP [Hfe] [-Hinterp]") => //=.
    + set_solver.
    + iIntros (?). iDestruct ("Hfe" $! eid) as "[Hf He]". iSplitL "Hf".
    - iIntros "HN Hpo _ _". rewrite big_sepM_dom. iApply ("Hf" with "HN Hpo").
    - iIntros (? eid_w) "((HE & [%Htid _] & Hpo & _ & _ & Hwrite & Hrf & _) & HP & #Hprot)".
      iApply (fupd_mask_intro _ ∅). { set_solver. }
      iIntros "M !>".
      iMod ("He" $! eid_w val with "HE [//] Hpo Hwrite Hrf HP Hprot") as "R".
      iMod "M" as "_". iModIntro. iExact "R".
    + simpl.
    iIntros (?) "Hinterp %Hpc_eq (% & % & % & [% %] & (Hread & [% %] & _ & _ & _ & Hwrite & Hrf & %Hext) & Hannot & Hpo & Hctrl & Hlast_local_write & Hrmw & ?)".

    iNamed "Hinterp".
    iApply wp_sswp. iApply (sswp_strong_mono with "[]").
    iApply reg_write;eauto.
    iIntros (? ->);simpl.
    iNamed "Hinterp". iDestruct (reg_interp_update with "Hinterp_reg Hr") as ">[Hinterp_reg Hr]".
    iDestruct (reg_mapsto_ne with "Hr Hinterp_pc") as %Hneq.

    iApply (inc_pc with "[-Hinterp_reg Hinterp_pc Hinterp_ctrl Hinterp_rmw]");auto.
    simpl. rewrite lookup_insert_ne //. rewrite Hpc_eq //.
    iIntros (? -> ? ?) "Hinterp". iApply ("Hcont" with "[-Hinterp]");auto.
    iSplit;first done.
    iExists eid, eid_w, val.
    iFrame. iPureIntro. split;lia. iFrame. simpl. rewrite union_empty_l_L. rewrite H7 /=.
    rewrite union_empty_r_L. destruct eid;simpl in *;subst. iFrame.
    iExists _;done.
  Qed.

  Lemma istore_rel_excl `{!UserProt} {tid inst_addr ctrl ot eid_w eid_xr res_ov} R R' Q po_priors
    addr data reg_res:
    inst_addr ↦ᵢ (IStore AS_rel_or_acq AV_exclusive reg_res (AEval data) (AEval addr)) ∗
    reg_res ↦ᵣ res_ov ∗
    ot -{LPo}> ∗
    ([∗ map] po_prior ↦ _ ∈ po_priors, po_prior -{Po}>) ∗
    ctrl -{Ctrl}> ∗
    last_local_write tid addr None ∗
    Some eid_xr -{Rmw}> ∗
    ((([∗ map] _ ↦ P ∈ po_priors, P) -∗ excl_inv eid_w R) ∗
    eid_w -{Edge.Rf}> eid_xr ∗ ⌜EID.tid eid_w ≠ EID.tid eid_xr⌝) ∗
    (∀ eid, R eid ==∗ R' eid) ∗
    ([∗ map] po_pred ↦ P ∈ po_priors, po_pred ↦ₐ P) -∗
    (
      ∀ eid,
        (eid -{E}> (Event.W AS_rel_or_acq AV_exclusive addr data) -∗
             ⌜(EID.tid eid) = tid⌝ -∗
             (* ([∗ map] po_prior ↦ _ ∈ po_priors, po_prior -{Edge.Po}> eid) -∗ *)
             ([∗ map] _ ↦ P ∈ po_priors, P) ={⊤∖ ↑(excl_inv_name eid_w)}[∅]▷=∗
             Q ∗ □ (prot addr data eid))
    ) -∗
    SSWPi (LTSI.Normal,inst_addr) @ tid
      {{ λ ltsi,
           ⌜ltsi = (LTSI.Normal, (inst_addr `+Z` 4)%bv) ⌝ ∗
           ∃ b_succ,
             reg_res ↦ᵣ mk_regval (bool_to_bv 64 b_succ) ∅ ∗
             ctrl -{Ctrl}> ∗
             (Some eid_xr) -{Rmw}> ∗
             (* update lts' accordingly *)
             if b_succ then
               (* success *)
               ∃ eid, eid -{E}> (Event.W AS_rel_or_acq AV_exclusive addr data) ∗
                      ⌜(EID.tid eid) = tid⌝ ∗
                      ([∗ set] po_prior ∈ dom po_priors, po_prior -{Edge.Po}> eid) ∗
                      Some eid -{LPo}> ∗
                      last_local_write tid addr (Some eid) ∗
                      eid ↦ₐ (R' eid_w ∗ Q)
             else
               (* failure, things stay unchanged *)
               ot -{LPo}> ∗
               last_local_write tid addr None ∗
               ([∗ map] node ↦ annot ∈ po_priors, node ↦ₐ annot)
      }}.
  Proof.
    iIntros "(Hinst & Hreg_res & Hlpo & Hpos & Hctrl & Hlast_write & Hrmw & (HPexcl & #Hw_rfe_xr)
    & Himpl & Hannot) Hfe". load_ins.

    iApply (mem_write_xcl_Some_inv emp _ (dom po_priors) _ (po_priors) ∅ ∅ with
                "Hlpo [Hpos] Hctrl Hlast_write Hrmw [] Hannot [Hfe HPexcl Himpl] [-Hinterp]");auto.
    + rewrite big_sepM_dom //.
    + rewrite map_union_empty. rewrite big_sepM_empty //.
    + simpl. iIntros (?). iSplitR.
      - iIntros "#HE Hpo _ _ _ Hrmw".
        iApply (big_sepS_impl with "Hpo").
        iModIntro. iIntros (? Hin) "Hpo".
        iApply (po_rel_is_lob with "Hpo");auto.
      - iSplitR; first done.
        iExists eid_w,
                  ((eid -{E}> Event.W AS_rel_or_acq AV_exclusive addr data ∗
                    ⌜EID.tid eid = tid ∧ EID.iid eid = (iis_iid (ts_iis ts) + 1)%nat⌝ ∗
                    ([∗ set] eid_po_src ∈ dom po_priors, eid_po_src -{Edge.Po}> eid) ∗
                    ([∗ set] eid_ctrl_src ∈ ctrl, eid_ctrl_src -{Edge.Ctrl}> eid) ∗
                    ([∗ set] eid_addr_src ∈ (map_fold (λ (_ : RegName) (dv : RegVal) (acc : gset Eid), reg_dep dv ∪ acc) ∅ ∅ ∪ ∅), eid_addr_src -{Edge.Addr}> eid) ∗
                    ([∗ set] eid_data_src ∈ (map_fold (λ (_ : RegName) (dv : RegVal) (acc : gset Eid), reg_dep dv ∪ acc) ∅ ∅ ∪ ∅), eid_data_src -{Edge.Data}> eid) ∗
                    emp ∗ eid_xr -{Edge.Rmw}> eid) ∗ [∗ map] annot ∈ po_priors, annot)%I, R.
        iSplitL "HPexcl".
        iIntros "[_ (#HG & Hannot)]".
        iDestruct ("HPexcl" with "Hannot") as "#Hexcl_inv".
        iFrame. iFrame "#".
        iIntros "([(#HE & [%Htid _] & (#Hpos & _)) Hannot] & R)".
        iDestruct ("Hfe" with "HE [//] Hannot") as ">M".
        iModIntro. iNext. iMod "M" as "[Q $]".
        iDestruct ("Himpl" with "R") as ">R". iModIntro.
        iCombine "R Q" as "R". iExact "R".
    + iIntros (?) "Hinterp %Hpc_eq (% & %Heq & HPost)";simpl. simpl in Hpc_eq.
      iNamed "Hinterp".
      iApply wp_sswp. iApply (sswp_strong_mono with "[]").
      iApply reg_write;eauto.
      iIntros (? ->);simpl.
      iNamed "Hinterp". iDestruct (reg_interp_update with "Hinterp_reg Hreg_res") as ">[Hinterp_reg Hreg_res]".
      iDestruct (reg_mapsto_ne with "Hreg_res Hinterp_pc") as %Hneq.
      simpl in Heq.

      iApply (inc_pc with "[-Hinterp_reg Hinterp_pc Hinterp_ctrl Hinterp_rmw]");auto.
      simpl. rewrite lookup_insert_ne //. rewrite Hpc_eq //.
      iIntros (? -> ? ?) "Hinterp". iApply ("Hcont" with "[-Hinterp]");auto.
      iSplit;first done.
      iDestruct "HPost" as "($&$&HPost)".
      iExists b_succ.
      iSplitL "Hreg_res". iExact "Hreg_res".
      destruct b_succ.
      - iDestruct "HPost" as "[% ((?&[[? ?] [? ?]])&HP&?&?)]".
      iExists eid. iFrame.
      - iDestruct "HPost" as "($&$&$&_)".
      - simpl. rewrite union_empty_l_L. iFrame. iExists _;done.
  Qed.

  Lemma istore_pln_single_data `{!UserProt} {tid inst_addr ctrl po_prior} reg_data reg_res addr val addr_pred P:
    inst_addr ↦ᵢ (IStore AS_normal AV_plain reg_res (AEreg reg_data) (AEval addr)) ∗
    Some po_prior -{LPo}> ∗
    ctrl -{Ctrl}> ∗
    last_local_write tid addr None ∗
    reg_data ↦ᵣ (mk_regval val {[addr_pred]}) ∗
    addr_pred ↦ₐ P ∗
    (
      ∀ eid, eid -{E}> (Event.W AS_normal AV_plain addr val) -∗
             ⌜EID.tid eid = tid⌝ -∗
             po_prior -{Edge.Po}> eid -∗
             addr_pred -{Edge.Data}> eid -∗
             P -∗
             □ (prot addr val eid)
    ) -∗
    (* Need to know about the data write here, or write the implication *)
    SSWPi (LTSI.Normal,inst_addr) @ tid
      {{ λ ltsi,
           ⌜ltsi = (LTSI.Normal, (inst_addr `+Z` 4)%bv) ⌝ ∗
           reg_data ↦ᵣ (mk_regval val {[addr_pred]}) ∗
           ∃ eid, eid -{E}> (Event.W AS_normal AV_plain addr val) ∗
                  ⌜EID.tid eid = tid ⌝ ∗
                  Some eid -{LPo}> ∗
                  last_local_write tid addr (Some eid) ∗
                  ctrl -{Ctrl}>
      }}.
  Proof.
    iIntros "(Hinst & Hpo & Hctrl & Hlast_write & Hreg & Hna & Hprot)". load_ins.

    iDestruct (lpo_to_po with "Hpo") as "[Hlpo #Hpo]".

    iApply wp_sswp.
    iNamed "Hinterp". iDestruct (reg_interp_agree with "Hinterp_reg Hreg") as %Hreg.
    iApply (sswp_strong_mono with "[]").
    iApply (reg_read);eauto. simpl.
    iIntros (? ->);simpl.

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
    - iIntros "((Hev&[Htid _]&Hpos&_&Hdata&_&_)&Hna)". simpl.
      rewrite map_fold_singleton /=. rewrite 2!union_empty_r_L.
      rewrite 2!big_sepS_singleton. rewrite big_sepM_singleton.
      iDestruct ("Hprot" $! eid with "Hev Htid Hpos Hdata Hna") as "Hprot".
      iApply (fupd_mask_intro _ ∅). {set_solver. }
      iIntros "M !>". iMod "M". iModIntro. iSplit. { iExact "M". }
      iFrame.
      + iIntros (?) "Hinterp [%Hpc_eq %] [% ((?&[Htid _]&?)&_&_&?&?&?&?)]";simpl.
        iApply (inc_pc with "[-Hinterp]");eauto. rewrite Hpc_eq //.
        iIntros (? -> ? ?) "Hinterp". iApply ("Hcont" with "[-Hinterp]");auto.
        rewrite map_empty_union. rewrite big_sepM_singleton. iFrame.
        iSplit;first done.
        iExists _;iFrame.
      + iFrame. iExists _;iFrame.
  Qed.

  Definition iload_pln `{!UserProt} {tid inst_addr kind_s ctrl rmw rv ot} R po_priors lob_priors addr reg:
    inst_addr ↦ᵢ (ILoad kind_s AV_plain reg (AEval addr)) ∗
    reg ↦ᵣ rv ∗
    ot -{LPo}> ∗
    ([∗ set] po_prior ∈ po_priors, po_prior -{Po}>) ∗
    ctrl -{Ctrl}> ∗
    rmw -{Rmw}> ∗
    last_local_write tid addr None ∗
    ([∗ map] lob_pred ↦ P ∈ lob_priors, lob_pred ↦ₐ P) -∗
    (∀ eid,
        (eid -{N}> (Edge.R kind_s AV_plain) -∗
         ([∗ set] po_prior ∈ po_priors, po_prior -{(Edge.Po)}> eid) -∗
         [∗ map] lob_prior ↦ _ ∈ lob_priors, lob_prior -{Edge.Lob}> eid) ∗
        ∀ eid' v, eid -{E}> (Event.R kind_s AV_plain addr v) -∗
             ⌜(EID.tid eid) = tid⌝ -∗
             ([∗ set] po_prior ∈ po_priors, po_prior -{Edge.Po}> eid) -∗
             (∃ kind_s_w kind_v_w, eid' -{E}> (Event.W kind_s_w kind_v_w addr v)) -∗
             eid' -{Edge.Rf}> eid -∗
             ([∗ map] _ ↦ P ∈ lob_priors, P) -∗
             □prot addr v eid' ==∗
             R eid' v
    ) -∗
    SSWPi (LTSI.Normal,inst_addr) @ tid
      {{ λ ltsi,
           ⌜ltsi = (LTSI.Normal, (inst_addr `+Z` 4)%bv)⌝ ∗
           ∃ eid eid' v, eid -{E}> (Event.R kind_s AV_plain addr v) ∗
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
      }}.
  Proof.
    iIntros "(Hinst & Hr & Hlpo & Hpo & Hctrl & Hrmw & Hlast_write &HP) Hfe". load_ins.
    iApply (mem_read_external _ (dom po_priors) lob_priors with "Hlpo Hctrl Hlast_write Hrmw [Hpo] [] HP [Hfe] [-Hinterp]") => //=.
    + set_solver.
    + iIntros (?). iDestruct ("Hfe" $! eid) as "[Hf He]". iSplitL "Hf".
    - iIntros "HN Hpo _ _". rewrite big_sepM_dom. iApply ("Hf" with "HN Hpo").
    - iIntros (? eid_w) "((HE & [%Htid _] & Hpo & _ & _ & Hwrite & Hrf & _) & HP & #Hprot)".
      iApply (fupd_mask_intro _ ∅). { set_solver. }
      iIntros "M !>".
      iMod ("He" $! eid_w val with "HE [//] Hpo Hwrite Hrf HP Hprot") as "R".
      iMod "M" as "_". iModIntro. iExact "R".
    + simpl.
    iIntros (?) "Hinterp %Hpc_eq (% & % & % & [% %] & (Hread & [% %] & Hpos & _ & _ & Hwrite & Hrf & Hext) & Hannot & Hpo & Hctrl & Hlast_local_write & Hrmw & _)".

    iNamed "Hinterp".
    iApply wp_sswp. iApply (sswp_strong_mono with "[]").
    iApply reg_write;eauto.
    iIntros (? ->);simpl.
    iNamed "Hinterp". iDestruct (reg_interp_update with "Hinterp_reg Hr") as ">[Hinterp_reg Hr]".
    iDestruct (reg_mapsto_ne with "Hr Hinterp_pc") as %Hneq.

    iApply (inc_pc with "[-Hinterp_reg Hinterp_pc Hinterp_ctrl Hinterp_rmw]");auto.
    simpl. rewrite lookup_insert_ne //. rewrite Hpc_eq //.
    iIntros (? -> ? ?) "Hinterp". iApply ("Hcont" with "[-Hinterp]");auto.
    iSplit;first done.
    iExists eid, eid_w, val.
    iFrame. done. iFrame. simpl. rewrite union_empty_l_L. rewrite H7 /=.
    rewrite union_empty_r_L. destruct eid;simpl in *;subst. iFrame.
    iExists _;done.
  Qed.

  Lemma iload_pln_fake_addr`{!UserProt} {tid inst_addr kind_s ctrl rmw val addr_pred ot} R addr reg rv reg_dep P:
    inst_addr ↦ᵢ ILoad kind_s AV_plain reg (AEbinop AOplus (AEval addr) (AEbinop AOminus (AEreg reg_dep) (AEreg reg_dep)))∗
    reg_dep ↦ᵣ mk_regval val {[addr_pred]} ∗
    addr_pred ↦ₐ P ∗
    reg ↦ᵣ rv ∗
    ot -{LPo}> ∗
    ctrl -{Ctrl}> ∗
    rmw -{Rmw}> ∗
    last_local_write tid addr None -∗
    (∀ eid eid' v, eid -{E}> (Event.R kind_s AV_plain addr v) -∗
                   ⌜(EID.tid eid) = tid⌝ -∗
                   (∃ kind_s_w kind_v_w, eid' -{E}> (Event.W kind_s_w kind_v_w addr v)) -∗
                   eid' -{Edge.Rf}> eid -∗
                   addr_pred -{Edge.Addr}> eid -∗
                   P -∗
                   □prot addr v eid' ==∗
                   R eid' v
    ) -∗

    SSWPi (LTSI.Normal, inst_addr) @ tid {{ λ ltsi,
                                              ⌜ltsi = (LTSI.Normal, (inst_addr `+Z` 4)%bv) ⌝ ∗
                                              reg_dep ↦ᵣ mk_regval val {[addr_pred]} ∗
                                              ∃ eid eid' v, eid -{E}> (Event.R kind_s AV_plain addr v) ∗
                                                            ⌜(EID.tid eid) = tid⌝ ∗
                                                            reg ↦ᵣ mk_regval v {[eid]} ∗
                                                            eid ↦ₐ (R eid' v) ∗
                                                            (∃ kind_s_w kind_v_w, eid' -{E}> (Event.W kind_s_w kind_v_w addr v)) ∗
                                                            eid' -{Edge.Rf}> eid ∗
                                                            Some eid -{LPo}> ∗
                                                            ctrl -{Ctrl}> ∗
                                                            rmw -{Rmw}>
      }}.
  Proof.
    iIntros "(Hinst & Hreg & HP & Hr & Hlpo & Hctrl & Hrmw & Hlast_write) Hfe". load_ins.

    iApply wp_sswp. iNamed "Hinterp". iDestruct (reg_interp_agree with "Hinterp_reg Hreg") as %Hreg.
    iApply (sswp_strong_mono with "[]").
    iApply reg_read;eauto.
    iIntros (? ->);simpl.

    iApply wp_sswp. iApply (sswp_strong_mono with "[]").
    iApply reg_read;eauto.
    iIntros (? ->);simpl.


    iApply (mem_read_external _ ∅ {[addr_pred := P]} {[reg_dep := _]} with "Hlpo Hctrl Hlast_write Hrmw [] [Hreg] [HP] [Hfe] [-Hinterp_reg Hinterp_pc Hinterp_ctrl Hinterp_rmw]");auto.
    + simpl. assert (addr + (val - val) = addr)%bv as -> by bv_solve. reflexivity.
    + rewrite dom_singleton_L /=. set_solver +.
    + rewrite big_sepM_singleton /=. iFrame.
    + rewrite big_sepM_singleton /=. iFrame.
    + iIntros (?). iSplitR "Hfe".
    - iIntros "HN _ _ Haddr". simpl.
      rewrite map_fold_singleton /=. rewrite 2!union_empty_r_L.
      rewrite dom_singleton_L. rewrite 2!big_sepS_singleton.
      by iApply addr_is_lob.
    - iIntros (? eid_w) "((HE & [%Htid _] & Hpo & _ & Haddr & Hwrite & Hrf & _) & HP & #Hprot)".
      iApply (fupd_mask_intro _ ∅). { set_solver. }
      iIntros "M !>".
      iMod ("Hfe" $! eid eid_w val0 with "HE [//] Hwrite Hrf [Haddr] [HP] [$Hprot]") as "R".
      { simpl. rewrite map_fold_singleton /=. rewrite 2!union_empty_r_L. rewrite big_sepS_singleton //. }
      { rewrite big_sepM_singleton //. }
      iMod "M" as "_". iModIntro. iExact "R".
    + simpl. iIntros (?) "Hinterp %Hpc_eq (% & % & % & [% %] & (Hread & [% %] & _ & _ & _ & Hwrite & Hrf & Hext) & Hannot & Hpo & Hctrl & Hlast_local_write & Hrmw & Hreg_dep)".
      subst.

      iNamed "Hinterp".
      iApply wp_sswp. iApply (sswp_strong_mono with "[]").
      iApply reg_write;eauto.
      iIntros (? ->);simpl.
      iNamed "Hinterp". iDestruct (reg_interp_update with "Hinterp_reg Hr") as ">[Hinterp_reg Hr]".
      iDestruct (reg_mapsto_ne with "Hr Hinterp_pc") as %Hneq.

      iApply (inc_pc with "[-Hinterp_reg Hinterp_pc Hinterp_ctrl Hinterp_rmw]");auto.
      simpl. rewrite lookup_insert_ne //. rewrite Hpc_eq //.
      iIntros (? -> ? ?) "Hinterp". iApply ("Hcont" with "[-Hinterp]");auto.
      iSplit;first done. rewrite big_sepM_singleton. iFrame.
      iExists eid, eid_w, val0.
      iFrame. done. iSplitL "Hinterp_reg". simpl. rewrite union_empty_l_L. rewrite H7 /=.
      rewrite union_empty_r_L. destruct eid;simpl in *;subst. iFrame.
      iFrame. iExists _;done.
    + iFrame. iExists _;done.
  Qed.

  Lemma istore_pln `{!UserProt} {tid inst_addr ctrl ot lastw} Q po_priors lob_priors addr data reg_res:
    inst_addr ↦ᵢ (IStore AS_normal AV_plain reg_res (AEval data) (AEval addr)) ∗
    ot -{LPo}> ∗
    ([∗ set] po_prior ∈ po_priors, po_prior -{Po}>) ∗
    ctrl -{Ctrl}> ∗
    last_local_write tid addr lastw ∗
    ([∗ map] lob_pred ↦ P ∈ lob_priors, lob_pred ↦ₐ P) -∗
    (
      ∀ eid,
        (eid -{N}> (Edge.W AS_normal AV_plain) -∗
         ([∗ set] po_prior ∈ po_priors, po_prior -{(Edge.Po)}> eid) -∗
         ([∗ set] ctrl_prior ∈ ctrl, ctrl_prior -{(Edge.Ctrl)}> eid) -∗
         [∗ map] lob_prior ↦ _ ∈ lob_priors, lob_prior -{Edge.Lob}> eid) ∗
        (eid -{E}> (Event.W AS_normal AV_plain addr data) -∗
             ⌜(EID.tid eid) = tid⌝ -∗
             ([∗ set] po_prior ∈ po_priors, po_prior -{Edge.Po}> eid) -∗
             ([∗ map] _ ↦ P ∈ lob_priors, P) ==∗
             Q eid ∗ □ (prot addr data eid))
    ) -∗
    SSWPi (LTSI.Normal,inst_addr) @ tid
      {{ λ ltsi,
           ⌜ltsi = (LTSI.Normal, (inst_addr `+Z` 4)%bv) ⌝ ∗
           ∃ eid, eid -{E}> (Event.W AS_normal AV_plain addr data) ∗
                   ⌜(EID.tid eid) = tid⌝ ∗
                   Some eid -{LPo}> ∗
                   ([∗ set] po_prior ∈ po_priors, po_prior -{Edge.Po}> eid) ∗
                   last_local_write tid addr (Some eid) ∗
                   ctrl -{Ctrl}> ∗
                   eid ↦ₐ Q eid
      }}.
  Proof.
    iIntros "(Hinst & Hlpo & Hpos & Hctrl & Hlast_write & Hannot) Hfe". load_ins.

    iApply (mem_write_non_xcl _ po_priors lob_priors with "Hlpo Hctrl Hlast_write [Hpos] [] [Hannot] [Hfe] [-Hinterp]");auto.
    + assert (G: (∅ : gmap RegName RegVal) ∩ ∅ ⊆ ∅) => //.
    + set_solver.
    + set_solver.
    + rewrite map_union_empty. rewrite big_sepM_empty //.
    + simpl. iIntros (?). iDestruct ("Hfe" $! eid) as "[Hf He]". iSplitL "Hf".
    - iIntros "HE Hpos Hctrl _ _". rewrite big_sepM_dom. iApply ("Hf" with "HE Hpos Hctrl").
    - iIntros "((HE & [%Htid _] & (Hpos & _)) & Hannot)".
      iApply (fupd_mask_intro _ ∅). { set_solver. }
      iIntros "M !>". iMod "M".
      iDestruct ("He" with "HE [//] Hpos Hannot") as ">[HQ Hprot]".
      iModIntro. iSplit. { iExact "HQ". } done.
    + iIntros (?) "Hinterp [%Hpc_eq %] [% ((?&[? ?]&?&?&?)&HP&_&?&?&?&?)]";simpl.
      iApply (inc_pc with "[-Hinterp]");eauto. rewrite Hpc_eq //.
      iIntros (? -> ? ?) "Hinterp". iApply ("Hcont" with "[-Hinterp]");auto.
      iFrame. iSplit;first done.
      iExists _;iFrame "#∗".
  Qed.

  Lemma istore_rel_raw `{!UserProt} {tid inst_addr reg_res ctrl ot o_lw} Q po_priors lob_priors addr data:
    po_priors ⊆ dom lob_priors ->
    inst_addr ↦ᵢ (IStore AS_rel_or_acq AV_plain reg_res (AEval data) (AEval addr)) ∗
    ot -{LPo}> ∗
    ([∗ set] po_prior ∈ po_priors, po_prior -{Po}>) ∗
    ctrl -{Ctrl}> ∗
    last_local_write tid addr o_lw ∗
    ([∗ map] lob_pred ↦ P ∈ lob_priors, lob_pred ↦ₐ P) ∗
    (
      ∀ eid,
        (eid -{N}> Edge.W AS_rel_or_acq AV_plain -∗
         ([∗ set] po_prior ∈ po_priors, po_prior -{Edge.Po}> eid) -∗
         ([∗ set] lob_pred ∈ dom lob_priors ∖ po_priors, lob_pred -{Edge.Lob}> eid)) ∗
        (eid -{E}> (Event.W AS_rel_or_acq AV_plain addr data) -∗
         ⌜(EID.tid eid) = tid⌝ -∗
         ([∗ set] po_prior ∈ po_priors, po_prior -{Edge.Po}> eid) -∗
         (* ([∗ set] lob_pred ∈ dom lob_priors, lob_pred -{Edge.Lob}> eid) -∗ *)
         ([∗ map] _ ↦ P ∈ lob_priors, P) ={⊤}=∗
         Q ∗ □ (prot addr data eid))
    ) -∗
    SSWPi (LTSI.Normal, inst_addr) @ tid {{ λ ltsi,
                                              ⌜ltsi = (LTSI.Normal, (inst_addr `+Z` 4)%bv) ⌝ ∗
                                              ∃ eid, eid -{E}> (Event.W AS_rel_or_acq AV_plain addr data) ∗
                                                     ⌜(EID.tid eid) = tid⌝ ∗
                                                     Some eid -{LPo}> ∗
                                                     ctrl -{Ctrl}> ∗
                                                     last_local_write tid addr (Some eid) ∗
                                                     eid ↦ₐ Q
      }}.
  Proof.
    iIntros (Hsub) "(Hinst & Hlpo & Hpo & Hctrl & Hlast_write & HP & Hprot)". load_ins.

    iApply (mem_write_non_xcl _ po_priors lob_priors with "Hlpo Hctrl Hlast_write [Hpo] [] HP [Hprot] [-Hinterp]") => //=.
    + assert (G: (∅ : gmap RegName RegVal) ∩ ∅ ⊆ ∅) => //.
    + set_solver.
    + set_solver.
    + rewrite map_union_empty. rewrite big_sepM_empty //.
    + simpl. iIntros (?). iDestruct ("Hprot" $! eid) as "[Hef Hprot]".
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
      - iIntros "((Hev&[%Htid _]&Hpos&?&?&?&_)&HP)".
        iDestruct ("Hprot" with "Hev [//] Hpos HP") as ">[HQ Hprot]".
        iApply (fupd_mask_intro _ ∅). {set_solver. }
        iIntros "M !>". iMod "M".
        iModIntro. iSplit. { iExact "HQ". }
        iFrame.
    + iIntros (?) "Hinterp [%Hpc_eq %] [% ((?&[[? ?] ?])&HP&_&?&?&?&?)]";simpl.
       iApply (inc_pc with "[-Hinterp]");eauto. rewrite Hpc_eq //.
       iIntros (? -> ? ?) "Hinterp". iApply ("Hcont" with "[-Hinterp]");auto.
       iFrame. iSplit;first done. iExists _;iFrame.
  Qed.

  Lemma istore_rel `{!UserProt} {tid inst_addr reg_res ctrl ot o_lw} Q po_priors addr data:
    inst_addr ↦ᵢ (IStore AS_rel_or_acq AV_plain reg_res (AEval data) (AEval addr)) ∗
    ot -{LPo}> ∗
    ([∗ map] po_prior ↦ _ ∈ po_priors, po_prior -{Po}>) ∗
    ctrl -{Ctrl}> ∗
    last_local_write tid addr o_lw ∗
    ([∗ map] po_pred ↦ P ∈ po_priors, po_pred ↦ₐ P) ∗
    (
      ∀ eid, eid -{E}> (Event.W AS_rel_or_acq AV_plain addr data) -∗
             ⌜(EID.tid eid) = tid⌝ -∗
             ([∗ map] po_prior ↦ _ ∈ po_priors, po_prior -{Edge.Po}> eid) -∗
             ([∗ map] _ ↦ P ∈ po_priors, P) ={⊤}=∗
             Q ∗ □ (prot addr data eid)
    ) -∗
    SSWPi (LTSI.Normal, inst_addr) @ tid {{ λ ltsi,
                                              ⌜ltsi = (LTSI.Normal, (inst_addr `+Z` 4)%bv) ⌝ ∗
                                              ∃ eid, eid -{E}> (Event.W AS_rel_or_acq AV_plain addr data) ∗
                                                     ⌜(EID.tid eid) = tid⌝ ∗
                                                     Some eid -{LPo}> ∗
                                                     ctrl -{Ctrl}> ∗
                                                     last_local_write tid addr (Some eid) ∗
                                                     eid ↦ₐ Q
      }}.
  Proof.
    iIntros "(Hinst & Hlpo & Hpo & Hctrl & Hlast_write & HP & Hprot)".

    iApply (istore_rel_raw Q (dom po_priors) po_priors with "[$Hinst $Hlpo Hpo $Hctrl $Hlast_write $HP Hprot]");auto.
    rewrite big_sepM_dom. iFrame "Hpo".
    iIntros (?).
    iSplitR. { rewrite difference_diag_L. iIntros "? ?". done. }
    iIntros "HE Htid Hpo HP".
    iApply ("Hprot" with "HE Htid [Hpo] HP").
    rewrite big_sepM_dom. iFrame "Hpo".
  Qed.

  Lemma istore_pln_fake_data `{!UserProt} {tid inst_addr ctrl po_prior} reg_dep val reg_res addr data addr_pred P:
    inst_addr ↦ᵢ (IStore AS_normal AV_plain
                    reg_res (AEbinop AOplus (AEval data) (AEbinop AOminus (AEreg reg_dep) (AEreg reg_dep))) (AEval addr)) ∗
    Some po_prior -{LPo}> ∗
    ctrl -{Ctrl}> ∗
    last_local_write tid addr None ∗
    reg_dep ↦ᵣ (mk_regval val {[addr_pred]}) ∗
    addr_pred ↦ₐ P ∗
    (
      ∀ eid, eid -{E}> (Event.W AS_normal AV_plain addr data) -∗
             po_prior -{Edge.Po}> eid -∗
             addr_pred -{Edge.Data}> eid -∗
             P ==∗
             □ (prot addr data eid)
    ) -∗
    (* Need to know about the data write here, or write the implication *)
    SSWPi (LTSI.Normal, inst_addr) @ tid
      {{ λ ltsi,
           ⌜ltsi = (LTSI.Normal, (inst_addr `+Z` 4)%bv) ⌝ ∗
           reg_dep ↦ᵣ (mk_regval val {[addr_pred]}) ∗
           ∃ eid, eid -{E}> (Event.W AS_normal AV_plain addr data) ∗
                  Some eid -{LPo}> ∗
                  last_local_write tid addr (Some eid) ∗
                  ctrl -{Ctrl}>
      }}.
  Proof.
    iIntros "(Hinst & Hpo & Hctrl & Hlast_write & Hreg & Hna & Hprot)". load_ins.

    iDestruct (lpo_to_po with "Hpo") as "[Hlpo #Hpo]".

    iApply wp_sswp. iNamed "Hinterp". iDestruct (reg_interp_agree with "Hinterp_reg Hreg") as %Hreg.
    iApply (sswp_strong_mono with "[]").
    iApply reg_read;eauto.
    iIntros (? ->);simpl.

    iApply wp_sswp. iApply (sswp_strong_mono with "[]").
    iApply reg_read;eauto.
    iIntros (? ->);simpl.

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
      - iIntros "((Hev&_&Hpos&_&Hdata&_&_)&Hna)". simpl.
        rewrite map_fold_singleton /=. rewrite 2!union_empty_r_L.
        rewrite 2!big_sepS_singleton. rewrite big_sepM_singleton.
        assert ((data + (val - val)) = data)%bv as ->. bv_solve.
        iDestruct ("Hprot" $! eid with "Hev Hpos Hdata Hna") as "Hprot".
        iApply (fupd_mask_intro _ ∅). {set_solver. }
        iIntros "M !>". iMod "M". iMod "Hprot". iModIntro. iSplit. { iExact "M". }
        iFrame.
    + iIntros (?) "Hinterp [%Hpc_eq %] [% ((?&?)&_&_&?&?&?&?)]";simpl.
      iApply (inc_pc with "[-Hinterp]");eauto. rewrite Hpc_eq //.
      iIntros (? -> ? ?) "Hinterp". iApply ("Hcont" with "[-Hinterp]");auto.
      rewrite map_empty_union. rewrite big_sepM_singleton. iFrame.
      iSplit;first done.
      iExists _;iFrame.
      assert ((data + (val - val)) = data)%bv as ->. bv_solve. done.
    + iFrame. iExists _;iFrame.
  Qed.

End rules.
