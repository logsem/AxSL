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

From iris_named_props Require Import named_props.
From iris.bi Require Import derived_laws.

From self.lang Require Import mm opsem.
From self.algebra Require Import base.
From self.low Require Import edge event interp_mod annotations.

Section def.
  Context `{CMRA Σ} `{!AABaseG}.

  (** Graph *)
  Import AACand.

  Definition global_interp (gs : GlobalState.t) :=
    (* agree RA for the graph, we simply put it in every graph assertion *)
    ("Hgr_ag" ∷ graph_agree gs.(GlobalState.gs_graph) ∗
    (* agree RA for the instruction table, similar as above *)
    "Hinstr_ag" ∷ instr_table_agree gs.(GlobalState.gs_gimem))%I.

  Definition annot_interp (m : gmap Eid (iProp Σ)) : iProp Σ :=
    ∃ (annot : gmap Eid gname),
      (* auth gmap [annot] for Eid -> gname *)
      ("Hannot_gn_map_auth" ∷ ghost_map_ag_auth AANodeAnnotN annot) ∗
      (* this map has same domain as the global [m] Eid -> iProp *)
      (* XXX do we need this? *)
      ("%Hannot_gn_map_dom" ∷ ⌜dom annot = dom m⌝) ∗
      (* for every event [eid], [P] is tied *)
      "Hannot_res_eqv" ∷
        [∗ map] eid ↦ gn;P ∈ annot;m,
        (* a resource gmap gn -> iProp tracks all resources tied to the event *)
          ∃ (res : gmap gname (iProp Σ)),
            (* all the ghost names of the tied resources*)
            own gn (● (GSet (dom res))) ∗
            (* tied iProps with saved_prop *)
            ([∗ map] gnp ↦ R ∈ res, saved_prop_own gnp (DfracOwn (1/2)) R) ∗
            (* NOTE: we only require [-∗] here, which implicitly allows us to
             attach resources from persistent context, in po! *)
            (* This is not a problem since the source of the persistent resources has to be
             the currect thread (e.g. some local graph facts), i.e cannot attach something from external*)
            ▷ □ (P -∗ ([∗ map] _ ↦ R ∈ res, R)).
End def.


Section lemma.
  Context `{CMRA Σ}.
  Context `{!AABaseG}.

  Lemma annot_merge n P Q :
    n ↦ₐ P -∗ n ↦ₐ Q -∗ (∀ na, annot_interp na ==∗ (n ↦ₐ (P ∗ Q)) ∗ annot_interp na).
  Proof.
    iIntros "Heid Heid'". rewrite annot_own_eq /annot_interp /annot_own_def.
    iDestruct "Heid" as "[%name [%gn (Hname_mapped & Hset & Hprop)]]".
    iDestruct "Heid'" as "[%name' [%gn' (Hname_mapped' & Hset' & Hprop')]]".
    iDestruct (ghost_map_ag_elem_agree with "Hname_mapped Hname_mapped'") as %->.
    iClear "Hname_mapped'".
    iIntros (?) "[%name_map (map_auth & %Hdom & Hmap)]".
    iDestruct (ghost_map_ag_lookup with "map_auth Hname_mapped") as "%Hlk_nm".
    assert (is_Some (na !! n)) as [? Hlk_na].
    { apply elem_of_dom. rewrite -Hdom. eapply elem_of_dom_2;eauto. }
    iDestruct (big_sepM2_delete with "Hmap") as "[(%&Hset_a &Hres_map& Hsep) Hmap]";eauto.
    iDestruct (own_valid_2 with "Hset_a Hset") as %Hset_v.
    rewrite auth_both_valid_discrete in Hset_v. destruct Hset_v as [Hset_v _].
    assert (is_Some (res !! gn)) as [R Hlk_res].
    { apply elem_of_dom. rewrite gset_disj_included in Hset_v. set_solver. }
    iDestruct (own_valid_2 with "Hset_a Hset'") as %Hset_v'.
    rewrite auth_both_valid_discrete in Hset_v'. destruct Hset_v' as [Hset_v' _].
    assert (is_Some (res !! gn')) as [R' Hlk_res'].
    { apply elem_of_dom. rewrite gset_disj_included in Hset_v'. set_solver. }
    iDestruct (own_valid_2 with "Hset Hset'") as %Hset_vv.
    rewrite auth_frag_op_valid in Hset_vv. rewrite gset_disj_valid_op in Hset_vv.

    iDestruct (big_sepM_delete with "Hres_map") as "[Hsp' Hres_map]";eauto.
    iDestruct (saved_prop_agree with "Hprop' Hsp'") as "#Hequiv'".
    iDestruct (big_sepM_delete with "Hres_map") as "[Hsp Hres_map]";eauto.
    { rewrite (lookup_delete_ne _ gn'). exact Hlk_res. set_solver + Hset_vv. }
    iDestruct (saved_prop_agree with "Hprop Hsp") as "#Hequiv".

    iMod (saved_prop_update_halves (P ∗ Q) gn with "Hprop Hsp") as "[Hprop1 Hprop2]".
    iMod (saved_prop_update_halves emp gn' with "Hprop' Hsp'") as "[Hprop1' Hprop2']".

    iModIntro.
    iSplitR "map_auth Hsep Hset_a Hprop1 Hprop1' Hmap Hres_map".
    { iExists name',gn. iFrame. }
    iExists name_map. iFrame. iSplit;first done.
    iApply big_sepM2_delete;eauto. iFrame "Hmap".
    iExists (<[gn' := emp%I]>(<[gn := (P ∗ Q)%I]> res)).
    assert (dom (<[gn' := emp%I]>(<[gn := (P ∗ Q)%I]> res)) = dom res) as ->.
    { apply elem_of_dom_2 in Hlk_res,Hlk_res'. rewrite !dom_insert_L. set_solver + Hlk_res Hlk_res'. }
    iFrame. rewrite 2!big_sepM_insert_delete. iFrame.
    rewrite delete_insert_ne. 2:{ apply elem_of_dom_2 in Hlk_res.  set_solver + Hset_vv. }
    rewrite 2!big_sepM_insert_delete. iFrame.
    iNext. rewrite (bi.sep_comm P Q).
    rewrite -bi.sep_assoc. iRewrite "Hequiv". iRewrite "Hequiv'".
    rewrite -!big_sepM_delete //. rewrite bi.emp_sep //.
    rewrite lookup_delete_ne //. set_solver + Hset_vv.
  Qed.

  Definition annot_agree m eid P :
    annot_interp m -∗ eid ↦ₐ P -∗
    ⌜eid ∈ dom m⌝ ∗ from_option (λ P', ▷ □ (P' -∗ P)) emp (m !! eid).
  Proof.
    iIntros "Hint Heid".
    rewrite annot_own_eq /annot_interp /annot_own_def.
    iDestruct "Hint" as "[%name_map (map_auth & %Hdom & Hmap)]".
    iDestruct "Heid" as "[%name [%gn (Hname_mapped & Hset & Hprop)]]".
    iDestruct (ghost_map_ag_lookup with "map_auth Hname_mapped") as "%H'".
    assert (is_Some (m !! eid)) as [? Hlk].
    { apply elem_of_dom. rewrite -Hdom. eapply elem_of_dom_2;eauto. }
    iDestruct (big_sepM2_lookup with "Hmap") as "(%&Hset_a & Hmap & #Hsep)";eauto.
    iDestruct (own_valid_2 with "Hset_a Hset") as %Hset_v.
    rewrite auth_both_valid_discrete in Hset_v. destruct Hset_v as [Hset_v _].
    assert (is_Some (res !! gn)) as [R Hlk_res].
    { apply elem_of_dom. rewrite gset_disj_included in Hset_v. set_solver. }
    iDestruct (big_sepM_lookup with "Hmap") as "Hsp";eauto.
    iDestruct (saved_prop_agree with "Hprop Hsp") as "Hequiv".
    iSplit. iPureIntro. apply elem_of_dom. eexists;eauto.
    rewrite Hlk /=. rewrite big_sepM_delete //.
    (* iExists _.  *)iNext. iRewrite "Hequiv".
    iModIntro. iIntros "?".  iDestruct ("Hsep" with "[$]") as "[$ _]".
  Qed.

  Definition annot_agree_big m m':
    annot_interp m -∗
    ([∗ map] eid ↦ P ∈ m', eid ↦ₐ P) -∗
    ⌜dom m' ⊆ dom m ⌝ ∗
    [∗ map] eid ↦ R ∈ m', from_option (λ P', ▷ □ (P' -∗ R)) emp (m !! eid).
  Proof.
    iIntros "Hannot Hm".
    iInduction m' as [|] "IH" using map_ind.
    iSplit. iPureIntro. rewrite dom_empty_L //. (*  iExists ∅. *) done.
    rewrite !big_sepM_insert //. iDestruct "Hm" as "[H Hm]".
    iDestruct (annot_agree with "Hannot H") as "[% #Hequiv]".
    iDestruct ("IH" with "Hannot Hm") as "[%Hdom IH']".
    iSplit. iPureIntro. rewrite dom_insert_L. set_solver.
    iFrame "#". iFrame.
  Qed.

  (* detach [P] from [eid] *)
  Definition annot_detach m eid P :
    annot_interp m -∗
    eid ↦ₐ P ==∗
    (* [R] is the remaining after detaching *)
    ∃R, annot_interp (<[eid:=R]>m) ∗ from_option(λ P', ▷ □ (P' -∗ P ∗ R)) emp (m !! eid).
  Proof.
    iIntros "Hint Heid".
    iDestruct (annot_agree with "Hint Heid") as "[%Hdom #_]".
    rewrite elem_of_dom in Hdom. destruct Hdom as [? Hlk]. rewrite Hlk /=.
    rewrite annot_own_eq /annot_interp /annot_own_def.
    iDestruct "Hint" as "[%name_map (map_auth & %Hdom & Hmap)]".
    iDestruct "Heid" as "[%name [%gn (Hname_mapped & Hset & Hprop)]]".
    iDestruct (ghost_map_ag_lookup with "map_auth Hname_mapped") as "%H'".
    iDestruct (big_sepM2_delete with "Hmap") as "[(%&Hset_a &Hmap'&#Hsep) Hmap]";eauto.
    iDestruct (own_valid_2 with "Hset_a Hset") as %Hset_v.
    rewrite auth_both_valid_discrete in Hset_v. destruct Hset_v as [Hset_v _].
    assert (is_Some (res !! gn)) as [R' Hlk_res].
    { apply elem_of_dom. rewrite gset_disj_included in Hset_v. set_solver. }
    iDestruct (big_sepM_delete with "Hmap'") as "[Hsp Hmap']";eauto.
    iDestruct (saved_prop_agree with "Hprop Hsp") as "#Hequiv".
    iMod (saved_prop_update_halves emp%I gn _ _ with "Hprop Hsp") as "(Hprop1 & Hprop2)".
    iModIntro.
    rewrite big_sepM_delete //.
    iExists ([∗ map] y ∈ delete gn res, y)%I.
    iSplitL. 2:{ iNext. iRewrite "Hequiv". done. }
    iExists _. iFrame.
    iSplitR. rewrite dom_insert_L. iPureIntro.
    assert (eid ∈ dom m). apply elem_of_dom. eexists;done.
    set_solver + H1 Hdom.
    iApply big_sepM2_delete;eauto.
    rewrite lookup_insert_Some. left;split;eauto.
    rewrite delete_insert_delete. iFrame "Hmap".
    iExists (<[gn := emp%I]>res).
    rewrite dom_insert_L.
    assert (({[gn]} ∪ dom res) = dom res) as ->.
    { assert (gn ∈ dom res). apply elem_of_dom. eexists;done.
      set_solver + H1. }
    rewrite big_sepM_insert_delete //. iFrame.
    iNext. iModIntro. rewrite big_sepM_insert_delete //. iIntros "$".
  Qed.

  Definition annot_detach_big {m m'}:
    annot_interp m -∗
    ([∗ map] eid ↦ P ∈ m', eid ↦ₐ P) ==∗
    ∃m'', ⌜dom m'' = dom m'⌝ ∗
      annot_interp (m'' ∪ m) ∗
          ([∗ map] eid ↦ R; R' ∈ m'; m'', from_option(λ P',▷ □ (P' -∗ R ∗ R')) emp (m !! eid)).
  Proof.
    iIntros "Hannot Hm".
    iInduction m' as [|] "IH" using map_ind.
    iModIntro. iExists ∅. iSplitR;first done. rewrite map_empty_union. iFrame. done.
    rewrite big_sepM_insert //. iDestruct "Hm" as "[Hi Hm]".
    iDestruct ("IH" with "Hannot Hm") as ">[% (%Hdom & Hannot & Hequiv)]".
    iDestruct (annot_detach _ _ x with "Hannot Hi") as ">[% [Hannot Hi]]".
    iModIntro. iExists (<[i := R]> m'').
    iSplitR. { iPureIntro. rewrite !dom_insert_L. rewrite Hdom //. }
    rewrite !insert_union_l. iFrame.
    iApply (big_sepM2_insert_2 with "[Hi]").
    { rewrite lookup_union_r //.
      apply not_elem_of_dom. rewrite Hdom. by apply not_elem_of_dom. }
    done.
  Qed.

  Definition annot_alloc na pg tid gs P :
    annot_interp na ∗ na_at_progress (GlobalState.gs_graph gs) tid pg na
    ==∗
    let eid := ThreadState.progress_to_node pg tid in
    annot_interp (<[eid:=P]>na) ∗
    eid ↦ₐ P.
  Proof.
    iIntros "(Hannot & Hpg)". unfold na_at_progress.
    iDestruct (na_at_progress_not_elem_of with "Hpg") as %H'.
    unfold annot_interp. iDestruct "Hannot" as "[%name_map (map_auth & %Hdom & Hmap)]".
    iMod (saved_prop_alloc P (DfracOwn 1)) as "[%γ new_prop]". { done. }
    iMod (own_alloc ((● GSet {[γ]}) ⋅ ◯ (GSet {[γ]}))) as "[%gn Hset]".
    { rewrite auth_both_valid_discrete.
      split;last done. apply gset_disj_included. set_solver +. }
    rewrite own_op. iDestruct "Hset" as "[Hset_a Hset_f]".
    iMod (ghost_map_ag_insert (ThreadState.progress_to_node pg tid) gn with "map_auth")
      as "(map_auth & Hname_mapped)".
    { rewrite -not_elem_of_dom Hdom //. }
    iModIntro.
    iDestruct "new_prop" as "(new_prop1 & new_prop2)".
    iSplitR "Hname_mapped Hset_f new_prop2".
    - iExists _. iFrame. iSplitR. { iPureIntro. set_solver + Hdom. }
      rewrite big_sepM2_insert;eauto.
      2: { apply not_elem_of_dom. rewrite Hdom //. }
      2: { by apply not_elem_of_dom. }
      iSplitL "Hset_a new_prop1".
      { iExists {[γ := P]}. rewrite dom_singleton_L. rewrite !big_sepM_singleton. iFrame.
        iNext. iModIntro. iIntros "$". }
      done.
    - rewrite annot_own_eq /annot_own_def.
      iExists gn, γ. iFrame.
  Qed.

  Lemma annot_split n P Q:
    n ↦ₐ (P ∗ Q) -∗ (∀ na, annot_interp na ==∗ (n ↦ₐ P ∗ n ↦ₐ Q) ∗ annot_interp na).
  Proof.
    iIntros "Heid". rewrite annot_own_eq /annot_own_def.
    rewrite /annot_interp. iIntros (?) "Hint".
    iDestruct "Heid" as "[%name [%gn (#Hname_mapped & Hset & Hprop)]]".
    iDestruct "Hint" as "[%name_map (map_auth & %Hdom & Hmap)]".
    iDestruct (ghost_map_ag_lookup with "map_auth Hname_mapped") as "%H'".
    assert (is_Some (na !! n)) as [? Hlk].
    { apply elem_of_dom. rewrite -Hdom. eapply elem_of_dom_2;eauto. }
    iDestruct (big_sepM2_delete with "Hmap") as "[(%&Hset_a &Hres_map&#Hsep) Hmap]";eauto.
    iDestruct (own_valid_2 with "Hset_a Hset") as %Hset_v.
    rewrite auth_both_valid_discrete in Hset_v. destruct Hset_v as [Hset_v _].
    assert (is_Some (res !! gn)) as [R Hlk_res].
    { apply elem_of_dom. rewrite gset_disj_included in Hset_v. set_solver. }
    iDestruct (big_sepM_delete with "Hres_map") as "[Hsp Hres_map]";eauto.
    iDestruct (saved_prop_agree with "Hprop Hsp") as "#Hequiv".
    iMod (saved_prop_alloc_cofinite (dom res) P (DfracOwn 1)) as "[%gnp [%Hnin new_prop]]". { done. }
    iMod (saved_prop_update_halves Q gn with "Hprop Hsp") as "[Hprop1 Hprop2]".
    iDestruct "new_prop" as "[Hprop1' Hprop2']".
    iMod (own_update _ _ (● GSet ({[gnp]}∪ (dom res)) ⋅ (◯ GSet {[gnp]})) with "Hset_a") as "Hset_a".
    apply auth_update_alloc. apply gset_disj_alloc_empty_local_update. set_solver + Hnin.
    iDestruct (own_op with "Hset_a") as "[Hset_a Hset']".
    iModIntro.
    iSplitR "map_auth Hset_a Hprop1 Hprop1' Hmap Hres_map".
    { iSplitL "Hset' Hprop2'". iExists name,gnp. by iFrame.  iExists name, gn. by iFrame. }
    iExists name_map. iFrame. iSplit;first done.
    iApply big_sepM2_delete;eauto. iFrame "Hmap".
    iExists (<[gnp := P]>(<[gn := Q]> res)).
    assert (dom (<[gnp:=P]> (<[gn:=Q]> res)) = {[gnp]}∪ dom res) as ->.
    { apply elem_of_dom_2 in Hlk_res. rewrite !dom_insert_L. set_solver + Hlk_res. }
    iFrame. rewrite 2!big_sepM_insert_delete. iFrame.
    rewrite delete_insert_ne. 2:{ apply elem_of_dom_2 in Hlk_res.  set_solver + Hlk_res Hnin. }
    assert ((delete gnp res) = res) as ->. rewrite delete_notin //. by apply not_elem_of_dom.
    rewrite 2!big_sepM_insert_delete. iFrame.
    iNext. iClear "Hname_mapped". iModIntro.
    rewrite bi.sep_assoc. iRewrite "Hequiv".
    rewrite -big_sepM_delete //.
  Qed.

  Lemma annot_wand n P Q:
    (* NOTE: this is a strong version. When applying it,
       the wand can be proved with other persistent resources *)
    □ (P -∗ Q)
    ⊢
    n ↦ₐ P -∗ (∀ na, annot_interp na ==∗ (n ↦ₐ Q) ∗ annot_interp na).
  Proof.
    iIntros "#Heq_PQ Heid". rewrite annot_own_eq /annot_own_def.
    rewrite /annot_interp. iIntros (?) "Hint".
    iDestruct "Heid" as "[%name [%gn (#Hname_mapped & Hset & Hprop)]]".
    iDestruct "Hint" as "[%name_map (map_auth & %Hdom & Hmap)]".
    iDestruct (ghost_map_ag_lookup with "map_auth Hname_mapped") as "%H'".
    assert (is_Some (na !! n)) as [? Hlk].
    { apply elem_of_dom. rewrite -Hdom. eapply elem_of_dom_2;eauto. }
    iDestruct (big_sepM2_delete with "Hmap") as "[(%&Hset_a &Hres_map&#Hsep) Hmap]";eauto.
    iDestruct (own_valid_2 with "Hset_a Hset") as %Hset_v.
    rewrite auth_both_valid_discrete in Hset_v. destruct Hset_v as [Hset_v _].
    assert (is_Some (res !! gn)) as [R Hlk_res].
    { apply elem_of_dom. rewrite gset_disj_included in Hset_v. set_solver. }
    iDestruct (big_sepM_delete with "Hres_map") as "[Hsp Hres_map]";eauto.
    iDestruct (saved_prop_agree with "Hprop Hsp") as "#Hequiv".
    iMod (saved_prop_update_halves Q gn with "Hprop Hsp") as "[Hprop1 Hprop2]".
    iModIntro.
    iSplitR "map_auth Hset_a Hprop1 Hmap Hres_map".
    { iExists name,gn. by iFrame. }
    iExists name_map. iFrame. iSplit;first done.
    iApply big_sepM2_delete;eauto. iFrame "Hmap".
    iExists (<[gn := Q]>(delete gn res)).
    assert (dom (<[gn:=Q]> (delete gn res)) = dom res) as ->.
    { apply elem_of_dom_2 in Hlk_res. rewrite insert_delete_insert //.
      rewrite dom_insert_L. set_solver + Hlk_res. }
    iFrame.
    rewrite big_sepM_insert_delete. rewrite delete_idemp. iFrame.
    iNext. iModIntro. iClear "Hname_mapped".
    rewrite (big_sepM_delete _ _ _ _ Hlk_res).
    rewrite big_sepM_insert_delete. rewrite delete_idemp.
    iRewrite - "Hequiv" in "Hsep".
    { iIntros "x". iDestruct ("Hsep" with "x") as "[? $]". iApply "Heq_PQ". done. }
  Qed.

  (* This lemma is a bit limiting since the entailment has to be proved with empty spatial context *)
  Lemma annot_entail n P Q:
    (P ⊢ Q) ->
    ⊢
    n ↦ₐ P -∗ (∀ na, annot_interp na ==∗ (n ↦ₐ Q) ∗ annot_interp na).
  Proof.
    iIntros "%Heq_PQ Heid". rewrite annot_own_eq /annot_own_def.
    rewrite /annot_interp. iIntros (?) "Hint".
    iDestruct "Heid" as "[%name [%gn (#Hname_mapped & Hset & Hprop)]]".
    iDestruct "Hint" as "[%name_map (map_auth & %Hdom & Hmap)]".
    iDestruct (ghost_map_ag_lookup with "map_auth Hname_mapped") as "%H'".
    assert (is_Some (na !! n)) as [? Hlk].
    { apply elem_of_dom. rewrite -Hdom. eapply elem_of_dom_2;eauto. }
    iDestruct (big_sepM2_delete with "Hmap") as "[(%&Hset_a &Hres_map&#Hsep) Hmap]";eauto.
    iDestruct (own_valid_2 with "Hset_a Hset") as %Hset_v.
    rewrite auth_both_valid_discrete in Hset_v. destruct Hset_v as [Hset_v _].
    assert (is_Some (res !! gn)) as [R Hlk_res].
    { apply elem_of_dom. rewrite gset_disj_included in Hset_v. set_solver. }
    iDestruct (big_sepM_delete with "Hres_map") as "[Hsp Hres_map]";eauto.
    iDestruct (saved_prop_agree with "Hprop Hsp") as "#Hequiv".
    iMod (saved_prop_update_halves Q gn with "Hprop Hsp") as "[Hprop1 Hprop2]".
    iModIntro.
    iSplitR "map_auth Hset_a Hprop1 Hmap Hres_map".
    { iExists name,gn. by iFrame. }
    iExists name_map. iFrame. iSplit;first done.
    iApply big_sepM2_delete;eauto. iFrame "Hmap".
    iExists (<[gn := Q]>(delete gn res)).
    assert (dom (<[gn:=Q]> (delete gn res)) = dom res) as ->.
    { apply elem_of_dom_2 in Hlk_res. rewrite insert_delete_insert //.
      rewrite dom_insert_L. set_solver + Hlk_res. }
    iFrame.
    rewrite big_sepM_insert_delete. rewrite delete_idemp. iFrame.
    iNext. iModIntro. iClear "Hname_mapped".
    rewrite (big_sepM_delete _ _ _ _ Hlk_res).
    rewrite big_sepM_insert_delete. rewrite delete_idemp.
    iRewrite - "Hequiv" in "Hsep".
    iIntros "x". iDestruct ("Hsep" with "x") as "[? $]". by iApply Heq_PQ.
  Qed.

  (* This lemma is not working: we have to make the choice earlier than we can get [P] *)
  (* XXX: can later credit help?? *)
  (* Lemma annot_or n P Q Q': *)
  (*   (P ⊢ Q ∨ Q') -> *)
  (*   ⊢ *)
  (*   n ↦ₐ P -∗ (∀ na, annot_interp na ==∗ ((n ↦ₐ Q) ∨ n ↦ₐ Q') ∗ annot_interp na). *)
  (* Proof. *)
  (*   iIntros "%Heq_PQ Heid". iIntros (?) "Hint". *)
  (*   rewrite annot_own_eq /annot_own_def. rewrite /annot_interp. *)

  (*   iDestruct "Heid" as "[%name [%gn (#Hname_mapped & Hset & Hprop)]]". *)
  (*   iDestruct "Hint" as "[%name_map (map_auth & %Hdom & Hmap)]". *)
  (*   iDestruct (ghost_map_ag_lookup with "map_auth Hname_mapped") as "%H'". *)
  (*   assert (is_Some (na !! n)) as [? Hlk]. *)
  (*   { apply elem_of_dom. rewrite -Hdom. eapply elem_of_dom_2;eauto. } *)
  (*   iDestruct (big_sepM2_delete with "Hmap") as "[(%&Hset_a &Hres_map&#Hsep) Hmap]";eauto. *)
  (*   iDestruct (own_valid_2 with "Hset_a Hset") as %Hset_v. *)
  (*   rewrite auth_both_valid_discrete in Hset_v. destruct Hset_v as [Hset_v _]. *)
  (*   assert (is_Some (res !! gn)) as [R Hlk_res]. *)
  (*   { apply elem_of_dom. rewrite gset_disj_included in Hset_v. set_solver. } *)
  (*   iDestruct (big_sepM_delete with "Hres_map") as "[Hsp Hres_map]";eauto. *)
  (*   iDestruct (saved_prop_agree with "Hprop Hsp") as "#Hequiv". *)
  (*   rewrite bi.sep_exist_l. *)

    (* iModIntro. *)
    (* iExists name_map. iFrame. rewrite bi.sep_comm. rewrite -bi.sep_assoc. iSplit;first done. *)

    (* rewrite (big_sepM2_delete _ name_map na n). 2-3: eassumption. *)
    (* iFrame "Hmap". rewrite bi.sep_exist_r. iExists res. iFrame. *)
    (* rewrite (big_sepM_delete _ _ _ _ Hlk_res). iFrame. *)
  (* Admitted. *)

End lemma.

Lemma annot_interp_alloc `{CMRA Σ} `{!AABaseInG}:
  ⊢ |==> ∃ GN, (∃ (annot : gmap Eid gname),
                    ghost_map_ag_auth GN annot ∗
                    ⌜dom annot = dom (∅ : gmap Eid (iProp Σ))⌝ ∗
                    ([∗ map] eid ↦ gn;P ∈ annot;(∅ : gmap Eid (iProp _)),
                       ∃ (res : gmap gname (iProp Σ)),
                         own gn (● (GSet (dom res))) ∗
                         ([∗ map] gnp ↦ R ∈ res, saved_prop_own gnp (DfracOwn (1/2)) R) ∗
                         ▷ □ (P -∗ ([∗ map] _ ↦ R ∈ res, R)))).
Proof.
  iDestruct (ghost_map_ag_alloc_empty) as ">[% ?]".
  iModIntro. iExists _. iExists ∅. iFrame.
  iSplit;first done.
  done.
Qed.
