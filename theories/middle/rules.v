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

(* This file lifts rules of the low-level logic to mid-level *)
From stdpp.unstable Require Import bitvector bitvector_tactics.

From iris.proofmode Require Import tactics.

Require Import ISASem.SailArmInstTypes.

From self Require Import stdpp_extra.
From self.lang Require Export opsem.
From self.low.rules Require Export prelude write_xcl write read barrier util reg announce.
From self.middle Require Export instantiation excl.

Import uPred.

Lemma reg_dep_fold_eq (dep : list _) (ts_regs dep_regs : gmap _ _):
  dep_regs ⊆ ts_regs ->
  dom dep_regs = list_to_set dep ->
  (foldr (λ (r : AAInter.reg) (acc : gset Eid), from_option (λ rd : RegVal, reg_dep rd ∪ acc) acc (ts_regs !! r)) ∅
     dep = (map_fold (λ _ dv acc, reg_dep dv ∪ acc) ∅ dep_regs)).
Proof.
  revert dep_regs ts_regs.
  induction dep using list_subset_ind;intros dep_regs ts_regs Hsub Hdom.
  {
    rewrite list_to_set_nil in Hdom.
    apply dom_empty_inv_L in Hdom.
    subst. done.
  }
  {
    destruct dep.
    rewrite list_to_set_nil in Hdom.
    apply dom_empty_inv_L in Hdom.
    subst. done.
    rewrite list_to_set_cons in Hdom. simpl.
    assert (Hin: r ∈ dom dep_regs) by set_solver + Hdom.
    rewrite elem_of_dom in Hin. destruct Hin as [b Hlk].
    rewrite -(insert_delete dep_regs r b Hlk).
    pose proof Hsub as Hsub'.
    rewrite map_subseteq_spec in Hsub.
    apply (Hsub r b) in Hlk. rewrite Hlk /=.
    rewrite map_fold_insert_L.
    pose proof (list_filter_split dep (λ x, x = r)) as Hsplit.
    rewrite (foldr_permutation (=) _ _ dep _ _ Hsplit).
    2:{
      intros. destruct (ts_regs !! a1), (ts_regs !! a2);simpl;auto. set_solver +.
    }
    pose proof (list_foldr_absorb (filter (λ x : AAInter.reg, x = r) dep) (filter (λ x : AAInter.reg, x ≠ r) dep)
                  (λ (r0 : AAInter.reg) (acc : gset Eid), from_option (λ rd : RegVal, reg_dep rd ∪ acc) acc (ts_regs !! r0))
      ∅ r ) as Heq.
    feed specialize Heq.
    {
      clear Heq Hsplit Hdom H.
      induction dep. by apply Forall_nil.
      rewrite filter_cons.
      case_decide.
      rewrite Forall_cons.
      split;done.
      done.
    }
    { intros. rewrite Hlk /=. set_solver +. }
    rewrite Hlk /=in Heq. rewrite Heq.
    specialize (H (filter (λ x : AAInter.reg, x ≠ r) dep)).
    feed specialize H.
    exists r. exists (filter (λ x : AAInter.reg, x = r) dep).
    rewrite -Permutation_cons_app. reflexivity.
    rewrite Permutation_app_comm. done.
    specialize (H (delete r dep_regs) ts_regs).
    feed specialize H.
    etransitivity;[|exact Hsub']. apply delete_subseteq.
    rewrite dom_delete_L. rewrite Hdom.
    rewrite difference_union_distr_l_L.
    rewrite difference_diag_L. rewrite union_empty_l_L.
    {
      clear Heq Hsplit Hdom H.
      induction dep.
      rewrite filter_nil. set_solver +.
      rewrite filter_cons.
      case_decide.
      rewrite 2!list_to_set_cons.
      rewrite -IHdep. set_solver + H.
      set_solver + H IHdep.
    }
    rewrite H //.
    intros. set_solver +.
    apply lookup_delete_None;left;done.
  }
Qed.


Require Import ISASem.Interface.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma iMon_bind_assoc {a b c: Type}
  (h : AACandExec.iMon a)
  (f : a -> AACandExec.iMon b)
  (g : b -> AACandExec.iMon c) :
  (h ≫= (λ x, f x ≫= g)) = ((h ≫= f) ≫= g).
Proof.
  rewrite /mbind.
  rewrite /AAInter.iMon_mbind_inst.
  induction h ;simpl. done.
  f_equal.
  extensionality x.
  specialize (H x). done.
Qed.

Section rules.
  Context `{AAIrisG} `{!AAThreadG} `{ThreadGN} `{!UserProt}.
  Import ThreadState.

  Lemma idone {addr tid Φ}:
    addr ↦ᵢ - -∗
    Φ (LTSI.Done, addr) -∗
    SSWPi (LTSI.Normal, addr) @ tid {{ Φ }}.
  Proof.
    iIntros "Hinst Hpost". rewrite sswpi_eq /sswpi_def.
    iIntros (?). iNamed 1. rewrite wpi_eq /wpi_def.
    iIntros (? [? ?]). repeat iNamed 1.
    iApply wp_sswp.
    iApply (sswp_strong_mono with "[Hinst]").
    { iApply (terminate with "[Hinst]") => //=.  }
    iIntros (? ->). simpl.
    iApply ("Hcont" with "Hpost");done.
  Qed.

  Ltac load_ins :=
    rewrite sswpi_eq /sswpi_def;
    iIntros (?); iNamed 1; rewrite wpi_eq /wpi_def;
    iIntros (? [? ?]); repeat iNamed 1;
    iApply wp_sswp; iApply (sswp_strong_mono with "[Hinst]");
    first (iApply (reload with "[Hinst]");eauto); iIntros (? ->); simpl.

  Lemma ibr {tid : Tid} {ins_addr addr} :
    ins_addr ↦ᵢ (IBr addr)
    ⊢
    SSWPi (LTSI.Normal, ins_addr) @ tid
        {{ λ ltsi, ⌜ltsi = (LTSI.Normal, addr)⌝ }}.
  Proof.
    iIntros "Hinst". load_ins.

    iApply wp_sswp. iApply (sswp_strong_mono with "[]").
    iApply (reg_write);eauto.
    simpl. iIntros (? ->). rewrite union_empty_l_L.
    iNamed "Hinterp". iMod (reg_interp_update with "Hinterp_reg Hinterp_pc") as "[Hinterp_reg Hinterp_pc]".

    iApply ("Hcont" $! (LTSI.Normal, addr) with "[//]").
    iPureIntro. split;auto. apply lookup_insert_Some;naive_solver.
    iFrame;simpl. iExists _;iFrame.
  Qed.

  Lemma inc_pc {tid : Tid} {ins_addr ts Ψ}:
    ts.(ThreadState.ts_reqs) = IncPCInterp ->
    ts_regs ts !! RNPC = Some {| reg_val := ins_addr; reg_dep := ∅ |} ->
    (∀ ltsi' : LTSI.t,
              ⌜ltsi' = (LTSI.Normal, (ins_addr `+Z` 4)%bv)⌝ -∗
              ∀ ts0 : ThreadState.t,
                "%PC" ∷ ⌜ready_for_next_ins_at ltsi'.2 ts0⌝ -∗
                "Hinterp" ∷ thread_local_interp ts0 -∗
                WP LTSI.to_lts ltsi'.1 ts0 @ tid  {{ lts, to_lts_Phi (λ ltsi0 : LTSI.t, Ψ ltsi0) lts }})-∗
    thread_local_interp ts -∗
    WP LThreadState.LTSNormal ts @ tid  {{ lts, to_lts_Phi Ψ lts }}.
  Proof.
    iIntros (Hreqs PC) "Hcont Hinterp".

    iApply wp_sswp. iApply (sswp_strong_mono with "[]").
    iApply reg_read;eauto.
    simpl. iIntros (? ->).

    iApply wp_sswp. iApply (sswp_strong_mono with "[]").
    iApply reg_write;eauto.
    simpl. iIntros (? ->).

    iNamed "Hinterp". iMod (reg_interp_update with "Hinterp_reg Hinterp_pc") as "[Hinterp_reg Hinterp_pc]".

    iApply ("Hcont" with "[//]").
    iPureIntro. split;auto. apply lookup_insert_Some;naive_solver.
    iFrame;simpl. iExists _;iFrame.
  Qed.

  Lemma inop {tid : Tid} {ins_addr} :
    ins_addr ↦ᵢ (INop)
    ⊢
    SSWPi (LTSI.Normal, ins_addr) @ tid
        {{ λ ltsi, ⌜ltsi = (LTSI.Normal, (ins_addr `+Z` 4)%bv)⌝}}.
  Proof.
    iIntros "Hinst". load_ins.

    iApply (inc_pc with "[Hcont]");eauto.
  Qed.

  Lemma idmb {tid : Tid} {ins_addr kind o_po_src} :
    ins_addr ↦ᵢ (IDmb kind) -∗
    o_po_src -{LPo}> -∗
    SSWPi (LTSI.Normal, ins_addr) @ tid
        {{ λ ltsi, ⌜ltsi = (LTSI.Normal,(ins_addr `+Z` 4)%bv)⌝ ∗
                   ∃ eid, eid -{E}> (Event.B (AAArch.DMB kind)) ∗
                   (* Po *)
                   from_option (λ eid_po_src,  eid_po_src -{(Edge.Po)}> eid) emp o_po_src ∗
                   (Some eid) -{LPo}>
        }}.
  Proof.
    iIntros "Hinst Hpo". load_ins.

    iApply wp_sswp. iApply (sswp_strong_mono with "[Hpo]").
    { iApply (dmb with "Hpo"). reflexivity. }
    iIntros (k) "[% (?&?&?)]";simpl;subst k.

    iApply (wp_strong_mono with "[-]"). 2: { iIntros (?) "H". iModIntro. iExact "H". }
    iApply (inc_pc with "[-Hinterp]");eauto.
    iIntros (?) "Hpost". iApply "Hcont". iFrame. iExists _;iFrame.
  Qed.

  Lemma iisb {tid : Tid} {ins_addr o_po_src ctrl_srcs} :
    ins_addr ↦ᵢ IIsb -∗
    o_po_src -{LPo}> -∗
    ctrl_srcs -{Ctrl}> -∗
    SSWPi (LTSI.Normal, ins_addr) @ tid
        {{ λ ltsi, ⌜ltsi = (LTSI.Normal, (ins_addr `+Z` 4)%bv) ⌝ ∗
                   ∃ eid, eid -{E}> (Event.B AAArch.ISB) ∗
                   (* Po *)
                   from_option (λ eid_po_src,  eid_po_src -{(Edge.Po)}> eid) emp o_po_src ∗
                   (Some eid) -{LPo}> ∗
                   (* Ctrl *)
                   ([∗ set] eid_ctrl_src ∈ ctrl_srcs, eid_ctrl_src -{(Edge.Ctrl)}> eid) ∗
                   ctrl_srcs -{Ctrl}>
        }}.
  Proof.
    iIntros "Hinst Hpo Hctrl". load_ins.

    iApply wp_sswp. iApply (sswp_strong_mono with "[Hpo]").
    iApply (isb with "Hpo"). reflexivity.
    iIntros (?) "[-> (?&?&?&?)]";simpl.
    rewrite /get_progress /=.

    iAssert (⌜ctrl_srcs ⊆ ts_ctrl_srcs ts⌝)%I with "[Hinterp Hctrl]" as %Hsub.
    iNamed "Hinterp". iApply (ctrl_srcs_interp_agree with "Hinterp_ctrl Hctrl").

    iApply (wp_strong_mono with "[-]"). 2: { iIntros (?) "H". iModIntro. iExact "H". }
    iApply (inc_pc with "[-Hinterp]"); eauto.
    iIntros (?) "Hpost". iApply "Hcont". iFrame.

    iExists _;iFrame. iApply big_sepS_subseteq;eauto.
  Qed.


  Fixpoint eval_ae_val ae (regs : RegFile) :=
    match ae with
    | AEval w => Some w
    | AEreg r =>  (λ rv, rv.(reg_val)) <$> regs !! r
    | AEbinop op ae1 ae2 =>
        eval_ae_val ae1 regs
          ≫= (λ w1 : bv (8 * AAArch.val_size),
                eval_ae_val ae2 regs
                  ≫= (λ w2 : bv (8 * AAArch.val_size),
                        Some match op with
                          | AOplus => (w1 + w2)%bv
                          | AOminus => (w1 - w2)%bv
                          | AOtimes => (w1 * w2)%bv
                          end))
    end.

  Lemma eval_ae_val_subseteq ae regs regs' v:
    eval_ae_val ae regs = Some v ->
    regs ⊆ regs' ->
    eval_ae_val ae regs' = Some v.
  Proof.
    revert regs regs' v.
    induction ae.
    - simpl. done.
    - simpl. intros.
      rewrite fmap_Some.
      rewrite fmap_Some in H4.
      destruct H4 as (?&?&?).
      eexists. split;eauto.
      specialize (H5 r). rewrite H4 /= in H5.
      destruct (regs' !! r) eqn:Heqn. subst x;done. done.
    - simpl. intros ??? Hae_val ?.
      destruct (eval_ae_val ae1 regs) eqn:Hae_val1. 2:{ inversion Hae_val. }
      destruct (eval_ae_val ae2 regs) eqn:Hae_val2. 2:{ inversion Hae_val. }
      simpl in Hae_val.
      erewrite IHae1;eauto.
      erewrite IHae2;eauto.
  Qed.

  Lemma eval_ae_val_Some_unique ae regs v:
    eval_ae_val ae regs = Some v ->
    eval_ae_val ae (filter (λ '(r,_) , r ∈@{gset _} list_to_set (dep_of_AE_aux ae)) regs) = Some v.
  Proof.
    revert v. induction ae;simpl;first done.
    - intros. rewrite map_filter_lookup.
      rewrite fmap_Some.
      rewrite fmap_Some in H4.
      destruct H4 as (?&?&?).
      eexists. rewrite H4 /=. rewrite option_guard_True.
      split;eauto.
      set_solver +.
    - intros ? Hae_val.
      destruct (eval_ae_val ae1 regs) eqn:Hae_val1. 2:{ inversion Hae_val. }
      destruct (eval_ae_val ae2 regs) eqn:Hae_val2. 2:{ inversion Hae_val. }
      simpl in Hae_val.
      rewrite list_to_set_app_L.
      specialize (IHae1 v0). feed specialize IHae1;auto. rewrite (eval_ae_val_subseteq _ _ _ _ IHae1).
      2: { apply map_filter_strong_subseteq_ext. intros ? ? [].  split;[set_solver|done]. }
      specialize (IHae2 v1). feed specialize IHae2;auto. rewrite (eval_ae_val_subseteq _ _ _ _ IHae2).
      2: { apply map_filter_strong_subseteq_ext. intros ? ? [].  split;[set_solver|done]. }
      done.
  Qed.

  Fixpoint count_ae_reg ae : nat :=
    match ae with
    | AEval w => 0
    | AEreg r => 1
    | AEbinop op ae1 ae2 =>
        count_ae_reg ae1 + count_ae_reg ae2
    end.

  Lemma ts_iis_incr_cntr_inversion ts ts' n:
    ts_iis ts' = ts_iis ts ->
    ts_iis (Nat.iter n incr_cntr ts') = ts_iis (PeanoNat.Nat.iter n incr_cntr ts).
  Proof.
    revert ts ts'. induction n;first done.
    intros. rewrite /= (IHn ts ts') //.
  Qed.

  Lemma ae_eval {tid : Tid} {ins_addr ts ae ctxt val Ψ} dep_regs:
    ts.(ThreadState.ts_reqs) = AEInterp ae ≫= ctxt ->
    ts_regs ts !! RNPC = Some {| reg_val := ins_addr; reg_dep := ∅ |} ->
    dom dep_regs = list_to_set (dep_of_AE_aux ae) ->
    eval_ae_val ae dep_regs = Some val ->
    ( ∀ ts' : ThreadState.t,
        ⌜ts_regs ts' !! RNPC = Some {| reg_val := ins_addr; reg_dep := ∅ |} ⌝ -∗
        ⌜ts'.(ThreadState.ts_reqs) = ctxt val ∧
        ts'.(ThreadState.ts_iis) = (Nat.iter (count_ae_reg ae) incr_cntr ts).(ThreadState.ts_iis)⌝ -∗
        ([∗ map] dr ↦ dv ∈ dep_regs, dr ↦ᵣ dv) -∗
        thread_local_interp ts' -∗
        WP LThreadState.LTSNormal ts' @ tid  {{ ltsi, to_lts_Phi Ψ ltsi }}) -∗
    ([∗ map] dr ↦ dv ∈ dep_regs, dr ↦ᵣ dv) -∗
    thread_local_interp ts -∗
    WP LThreadState.LTSNormal ts @ tid  {{ ltsi, to_lts_Phi Ψ ltsi }}.
  Proof.
    intros Hreqs Hpc Hreg_dom Hae_val. revert ctxt dep_regs val ts Hreqs Hpc Hreg_dom Hae_val.
    induction ae; iIntros (????????) "Hcont HDR Hinterp";simpl in *.
    {
      inversion Hae_val;subst w.
      iApply ("Hcont" with "[//] [//] HDR Hinterp").
    }
    {
      rewrite union_empty_r_L in Hreg_dom. apply dom_singleton_inv_L in Hreg_dom.
      destruct Hreg_dom as [? ->]. simplify_map_eq /=. rewrite {2}big_sepM_singleton.

      iAssert (⌜ ts_regs ts !! r = Some x⌝)%I with "[Hinterp HDR]" as %Hreg_val.
      iNamed "Hinterp". iDestruct (reg_interp_agree with "Hinterp_reg HDR") as %Hlk;done.

      iApply wp_sswp. iApply (sswp_strong_mono with "[]").
      iApply reg_read;eauto.
      iIntros (? ->); simpl.

      iApply ("Hcont" with "[] [] [HDR]");auto.
      rewrite big_sepM_singleton //.
    }
      assert (filter (λ '(k, _), k ∈@{gset _} list_to_set (dep_of_AE_aux ae1)) dep_regs ##ₘ filter (λ '(k, _), k ∉@{gset _} list_to_set (dep_of_AE_aux ae1)) dep_regs) as Hdomdisj.
      {
        pose proof (filter_dom_L (λ k: RegName, k ∈@{gset _} (list_to_set (dep_of_AE_aux ae1))) dep_regs) as Hdomeq2; simpl in Hdomeq2.
        pose proof (filter_dom_L (λ k: RegName, k ∉@{gset _} (list_to_set (dep_of_AE_aux ae1))) dep_regs) as Hdomeq2'; simpl in Hdomeq2'.
        apply map_disjoint_dom. rewrite -Hdomeq2 -Hdomeq2'.
        pose proof (set_filter_split (dom dep_regs) (λ (k : RegName), k ∈@{gset _} list_to_set (dep_of_AE_aux ae1))) as [_ ?]. done.
      }
    {
      pose proof (map_filter_split dep_regs (λ (k : RegName), k ∈@{gset _} list_to_set (dep_of_AE_aux ae1))) as <-.
      iDestruct (big_sepM_union with "HDR") as "[HDR1 HDR2]";auto.

      destruct (eval_ae_val ae1 dep_regs) eqn:Hae_val1. 2:{ inversion Hae_val. }
      destruct (eval_ae_val ae2 dep_regs) eqn:Hae_val2. 2:{ inversion Hae_val. }
      simpl in Hae_val.

      iApply (IHae1 with "[Hcont HDR2] HDR1").
      { rewrite Hreqs. rewrite -iMon_bind_assoc. reflexivity. }
      done.
      rewrite (dom_filter_L _ dep_regs (filter (λ k, k ∈@{gset _} list_to_set (dep_of_AE_aux ae1)) ((dom dep_regs): gset RegName) )).
      2:{ intros. rewrite elem_of_filter. rewrite elem_of_dom. split;[intros [? []];eexists;done|intros [? []];split;eauto]. }
      assert (list_to_set (dep_of_AE_aux ae1) ⊆ dom dep_regs).
      { rewrite Hreg_dom. rewrite list_to_set_app_L. set_solver +. }
      apply set_eq. intros. rewrite elem_of_filter. set_solver + H4.

      eapply eval_ae_val_Some_unique;eauto.
      assert (filter (λ '(k, _), k ∈@{gset _} list_to_set (dep_of_AE_aux ae2)) dep_regs ##ₘ filter (λ '(k, _), k ∉@{gset _} list_to_set (dep_of_AE_aux ae2)) dep_regs) as Hdomdisj2.
      {
        pose proof (filter_dom_L (λ k: RegName, k ∈@{gset _} (list_to_set (dep_of_AE_aux ae2))) dep_regs) as Hdomeq2; simpl in Hdomeq2.
        pose proof (filter_dom_L (λ k: RegName, k ∉@{gset _} (list_to_set (dep_of_AE_aux ae2))) dep_regs) as Hdomeq2'; simpl in Hdomeq2'.
        apply map_disjoint_dom. rewrite -Hdomeq2 -Hdomeq2'.
        pose proof (set_filter_split (dom dep_regs) (λ (k : RegName), k ∈@{gset _} list_to_set (dep_of_AE_aux ae2))) as [_ ?]. done.
      }
      {
        iIntros (?) "%Hpc' %Hreqs'". iIntros "HDR".
        iDestruct (big_sepM_union with "[$HDR $HDR2]") as "HDR";auto.
        pose proof (map_filter_split dep_regs (λ (k : RegName), k ∈@{gset _} list_to_set (dep_of_AE_aux ae1))) as ->.
        pose proof (map_filter_split dep_regs (λ (k : RegName), k ∈@{gset _} list_to_set (dep_of_AE_aux ae2))) as <-.

        iDestruct (big_sepM_union with "HDR") as "[HDR1 HDR2]";auto.
        destruct Hreqs' as [Hreqs' Hpg'].

        iApply (IHae2 with "[Hcont HDR2] HDR1").
        rewrite Hreqs'. rewrite -iMon_bind_assoc. reflexivity.
        done.

        rewrite (dom_filter_L _ dep_regs (filter (λ k, k ∈@{gset _} list_to_set (dep_of_AE_aux ae2)) ((dom dep_regs): gset RegName) )).
        2:{ intros. rewrite elem_of_filter. rewrite elem_of_dom. split;[intros [? []];eexists;done|intros [? []];split;eauto]. }
        assert (list_to_set (dep_of_AE_aux ae2) ⊆ dom dep_regs).
        { rewrite Hreg_dom. rewrite list_to_set_app_L. set_solver +. }
        apply set_eq. intros. rewrite elem_of_filter. set_solver + H4.

        eapply eval_ae_val_Some_unique;eauto.

        iIntros (?) "%Hpc'' %Hreqs''". iIntros "HDR".
        iDestruct (big_sepM_union with "[$HDR $HDR2]") as "HDR";auto.
        pose proof (map_filter_split dep_regs (λ (k : RegName), k ∈@{gset _} list_to_set (dep_of_AE_aux ae2))) as ->.

        iApply ("Hcont" with "[//] [] [HDR]").
        { iPureIntro.
          destruct Hreqs'' as [? ?].
          split;auto. simpl in H4. inversion Hae_val;subst val. done.
          rewrite H5. rewrite (comm Nat.add) Nat.iter_add. by apply ts_iis_incr_cntr_inversion.
        }
        done.
      }
      done.
    }
    Qed.

  Lemma ibne {tid : Tid} {ins_addr addr ae val ctrl_srcs} dep_regs:
    dom dep_regs = list_to_set (dep_of_AE_aux ae) ->
    eval_ae_val ae dep_regs = Some val ->
    ins_addr ↦ᵢ (IBne ae addr) -∗
    ctrl_srcs -{Ctrl}> -∗
    ([∗ map] dr ↦ dv ∈ dep_regs, dr ↦ᵣ dv) -∗
    SSWPi (LTSI.Normal, ins_addr) @ tid
    {{ λ ltsi,
        ([∗ map] dr ↦ dv ∈ dep_regs, dr ↦ᵣ dv) ∗
        ((map_fold (λ _ dv acc, reg_dep dv ∪ acc) ∅ dep_regs) ∪ ctrl_srcs) -{Ctrl}> ∗
        ((⌜ltsi = (LTSI.Normal, (ins_addr `+Z` 4)%bv)⌝ ∗ ⌜val = (BV 64 0)⌝)
        ∨
        (⌜ltsi = (LTSI.Normal, addr)⌝ ∗ ⌜val ≠ (BV 64 0)⌝))
    }}.
  Proof.
    iIntros (Hdom Heval) "Hinst Hctrl Hrs". load_ins.
    iApply (wp_strong_mono with "[-]"). 2: { iIntros (?) "H". iModIntro. iExact "H". }
    iApply (ae_eval with "[- Hinterp Hrs] Hrs"); eauto.
    iIntros (?) "%PC [% %] Hrs Hinterp".
    
    iApply wp_sswp. iApply (sswp_strong_mono with "[]").
    {
      iApply branch_announce; eauto.
    }
    iIntros (? ->) "/=".
    iNamed "Hinterp".
    iDestruct (ctrl_srcs_interp_union (map_fold (λ _ dv acc, reg_dep dv ∪ acc) ∅ dep_regs) with "Hinterp_ctrl Hctrl") as ">(Hinterp_ctrl & Hctrl)".

    iDestruct (reg_interp_agree_big with "Hinterp_reg Hrs") as "%Hrs_sub".
    case_bool_decide as Hpred.
    + iApply (wp_strong_mono with "[-]"). 2: { iIntros (?) "H". iModIntro. iExact "H". }
      iApply (inc_pc with "[-Hinterp_reg Hinterp_ctrl Hinterp_rmw Hinterp_pc]"); eauto.
      { iIntros (?) "Hpost". iApply "Hcont". iFrame.
        iLeft.
        iFrame.
        rewrite Hpred. iPureIntro. bv_unfold. bv_simplify. cbv. bv_solve.
      }

      iFrame.
      iSplitL "Hinterp_pc". { iExists w. iFrame. }
      simpl.
      rewrite (reg_dep_fold_eq _ _ dep_regs).
      { rewrite union_empty_r_L. iFrame. }
      { exact Hrs_sub. }
      { exact Hdom. }
    + iApply wp_sswp. iApply (sswp_strong_mono with "[]"). 
      iApply (reg_write); eauto. 
      simpl. iIntros (? ->). rewrite union_empty_l_L.
      iMod (reg_interp_update with "Hinterp_reg Hinterp_pc") as "[Hinterp_reg Hinterp_pc]".
      simpl.
      
      iApply ("Hcont" $! (LTSI.Normal, addr) with "[Hctrl Hrs]").
      {
        iFrame. iRight. iSplit; [done|]. 
        iPureIntro. intro Heq. rewrite Heq in Hpred. contradict Hpred. cbv. bv_solve.
      }
      {
        unfold ready_for_next_ins_at.
        iPureIntro; split; [done | by rewrite lookup_insert].
      }
      iFrame.
      iSplitL "Hinterp_pc". { iExists addr. iFrame. }
      simpl.
      rewrite (reg_dep_fold_eq _ _ dep_regs).
      { rewrite union_empty_r_L. iFrame. }
      { exact Hrs_sub. }
      { exact Hdom. }
  Qed.
  
  Lemma iassign {tid : Tid} {ins_addr r rv ae val} dep_regs:
    dom dep_regs = list_to_set (dep_of_AE_aux ae) ->
    eval_ae_val ae dep_regs = Some val ->
    ins_addr ↦ᵢ (IAssign r ae) -∗
    r ↦ᵣ rv -∗
    ([∗ map] dr ↦ dv ∈ dep_regs, dr ↦ᵣ dv) -∗
    SSWPi (LTSI.Normal, ins_addr) @ tid
        {{ λ ltsi, ⌜ltsi = (LTSI.Normal, (ins_addr `+Z` 4)%bv)⌝ ∗
                   r ↦ᵣ (mk_regval val (map_fold (λ _ dv acc, reg_dep dv ∪ acc) ∅ dep_regs)) ∗
                   ([∗ map] dr ↦ dv ∈ dep_regs, dr ↦ᵣ dv)
        }}.
  Proof.
    iIntros (Hdom Heval) "Hinst HR HDR". load_ins.

    iApply (wp_strong_mono with "[-]"). 2: { iIntros (?) "H". iModIntro. iExact "H". }
    iApply (ae_eval with "[- Hinterp HDR] HDR");eauto.
    iIntros (?) "%PC [% %] HDR Hinterp".

    iApply wp_sswp. iApply (sswp_strong_mono with "[]").
    iApply reg_write;eauto.
    iIntros (? ->); simpl.

    iNamed "Hinterp".
    iDestruct (reg_interp_agree_big with "Hinterp_reg HDR") as %Hsub.
    iDestruct (reg_interp_update with "Hinterp_reg HR") as ">[Hinterp_reg HR]".
    iDestruct (reg_mapsto_ne with "HR Hinterp_pc") as %Hneq.

    iApply (wp_strong_mono with "[-]"). 2: { iIntros (?) "H". iModIntro. iExact "H". }
    iApply (inc_pc with "[-Hinterp_reg Hinterp_ctrl Hinterp_rmw Hinterp_pc]");auto.
    { simpl. rewrite lookup_insert_ne //. }

    iIntros (?) "Hpost". iApply "Hcont". iFrame. iFrame.

    rewrite union_empty_r_L. rewrite /incr_cntr /=. rewrite (reg_dep_fold_eq _ _ dep_regs) //.
    iFrame. iExists _;iFrame.
  Qed.

  (** helper lemmas *)
  Lemma mem_read_external `{!UserProt} {tid : Tid} {o_po_src ctrl_srcs ts ctxt dep addr kind_s kind_v mrmw Ψ}
    R po_srcs lob_annot dep_regs:
    ThreadState.ts_reqs ts = AAInter.Next (AAInter.MemRead 8 (readreq_of_store kind_s kind_v addr dep)) ctxt ->
    dom dep_regs = list_to_set (AAInter.DepOn.regs dep) ->
    let reg_deps := map_fold (λ _ dv acc, reg_dep dv ∪ acc) ∅ dep_regs in
    let mem_deps :=
      foldr (λ (idx : N) (acc : gset Eid),
               from_option (λ md : nat, {[{| EID.tid := tid; EID.iid := ts.(ts_iis).(iis_iid); EID.num := md |}]} ∪ acc) acc
                 (ts.(ts_iis).(iis_mem_reads) !! idx)) ∅ (AAInter.DepOn.mem_reads dep) in
    let R_graph_facts := (λ eid val eid_w,
                            eid -{E}> (Event.R kind_s kind_v addr val) ∗
                            ⌜(EID.tid eid) = tid ∧ (EID.iid eid) = ts.(ts_iis).(iis_iid)⌝ ∗
                            (* Po *)
                            ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{(Edge.Po)}> eid) ∗
                            (* Ctrl *)
                            ([∗ set] eid_ctrl_src ∈ ctrl_srcs, eid_ctrl_src -{(Edge.Ctrl)}> eid) ∗
                            (* Addr *)
                            ([∗ set] eid_addr_src ∈ reg_deps ∪ mem_deps, eid_addr_src -{(Edge.Addr)}> eid) ∗
                            (* There must be a write with same addr and val *)
                            (∃ kind_s_w kind_v_w, eid_w -{E}> (Event.W kind_s_w kind_v_w addr val)) ∗
                            (* [optional] rf from write to read *)
                            eid_w -{(Edge.Rf)}> eid ∗
                            (* eid_w is an external write *)
                            ⌜EID.tid eid_w ≠ tid⌝)%I in
    o_po_src -{LPo}> -∗
    ctrl_srcs -{Ctrl}> -∗
    last_local_write tid addr None -∗
    mrmw -{Rmw}> -∗
    ([∗ set] e_po_src ∈ po_srcs, e_po_src -{Po}>) -∗
    ([∗ map] dr ↦ dv ∈ dep_regs, dr ↦ᵣ dv) -∗
    (* node annotations *)
    ([∗ map] node ↦ annot ∈ lob_annot, node ↦ₐ annot) -∗
    (∀ eid,
       (* Lob edge formers *)
       (eid -{N}> (Edge.R kind_s kind_v) -∗
        ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{(Edge.Po)}> eid) -∗
        ([∗ set] eid_ctrl_src ∈ ctrl_srcs, eid_ctrl_src -{(Edge.Ctrl)}> eid) -∗
        ([∗ set] eid_addr_src ∈ reg_deps ∪ mem_deps, eid_addr_src -{(Edge.Addr)}> eid) -∗
        [∗ set] eid_pre ∈ dom lob_annot, eid_pre -{Edge.Lob}> eid) ∗
       (* FE *)
       (∀ val eid_w,
          R_graph_facts eid val eid_w ∗
          ([∗ map] _ ↦ annot ∈ lob_annot, annot) ∗
          □(prot addr val eid_w)
          ={⊤}[∅]▷=∗
          R addr val eid_w)) -∗
    (* continuation *)
    (
      ∀ ts' : ThreadState.t,
        "Hinterp" ∷ thread_local_interp ts' -∗
        ⌜ts'.(ts_regs) !! RNPC = ts.(ts_regs) !! RNPC⌝ -∗
        (
          (* exists a val, and a write eid_w *)
          ∃ val eid_w,
          (* update lts' accordingly *)
          ∃ eid,
            ⌜ts'.(ts_iis)= (incr_cntr ts).(ts_iis)<|iis_mem_reads := ((ts.(ts_iis).(iis_mem_reads)) ++ [eid.(EID.num)])%list|>
            ∧ ts'.(ts_reqs) = ctxt (inl(val, None)) ⌝ ∗
            R_graph_facts eid val eid_w ∗
            (* node annotation *)
            (eid ↦ₐ R addr val eid_w) ∗
            (Some eid) -{LPo}> ∗
            ctrl_srcs -{Ctrl}> ∗
            (* local writes at addr is unchanged *)
            last_local_write tid addr None ∗
            (* Update this read as the rmw pred if atomic *)
            (if bool_decide (kind_v = AV_exclusive) || bool_decide (kind_v = AV_atomic_rmw)
             then Some eid else mrmw) -{Rmw}> ∗
            ([∗ map] dr ↦ dv ∈ dep_regs, dr ↦ᵣ dv)
        ) -∗
      WP LThreadState.LTSNormal ts' @ tid  {{ lts, to_lts_Phi Ψ lts }}
    )-∗
    thread_local_interp ts -∗
    WP LThreadState.LTSNormal ts @ tid {{  λ lts', to_lts_Phi Ψ lts' }}.
  Proof.
    iIntros (? Hdom ???) "Hpo_src Hctrl Hlw Hrmw Hpo_srcs HDRs Hna Hef_fe Hcont Hinterp".
    iNamed "Hinterp".
    iDestruct (reg_interp_agree_big with "Hinterp_reg HDRs") as %Hdr_sub.
    iDestruct (ctrl_srcs_interp_agree with "Hinterp_ctrl Hctrl") as %Hctrl_sub.
    iDestruct (rmw_pred_interp_agree with "Hinterp_rmw Hrmw") as %Hrmw_ag.
    iApply wp_sswp.
    iApply (sswp_strong_mono' with "[-Hinterp_reg Hinterp_ctrl Hinterp_rmw Hinterp_pc HDRs Hctrl Hrmw Hcont]").
    iDestruct ("Hef_fe" $! (progress_to_node (get_progress ts) tid)) as "[Hef Hfe]".

    iApply (mem_read_external with "Hpo_src Hpo_srcs Hlw Hna [Hef] [Hfe]"). eauto.
    {
      iIntros "E_R Hpo Hctrl Haddr".
      iApply ("Hef" with "E_R Hpo [Hctrl] [Haddr]").
      iApply big_sepS_subseteq;eauto.
      simpl. erewrite reg_dep_fold_eq;eauto.
    }
    {
      rewrite /R_graph_facts /=. iIntros (??) "H".
      set (pg := (get_progress ts)).
      erewrite (reg_dep_fold_eq _ (ts_regs ts) dep_regs);eauto. rewrite /reg_deps.
      iSpecialize ("Hfe" with "[-]").
      iDestruct "H" as "[(?&?&?&?&?&?) H]".
      iSplitR "H". 2:{ iExact "H". } iFrame.
      iSplit;first done.
      iApply big_sepS_subseteq;eauto.
      iExact "Hfe".
    }
    iIntros (k) "(%&%&%&(?&?&Hctrl'&?&?&?&?)&Hlpo&Hna&Hlw)". subst k.
    iApply interp_mod_bupd'.
    iMod (rmw_pred_interp_update (if bool_decide (kind_v = AV_exclusive) || bool_decide (kind_v = AV_atomic_rmw)
      then Some _ else mrmw) with "Hinterp_rmw Hrmw") as "[Hinterp_rmw Hrmw]".
    simpl.
    iFrame. simpl. iModIntro.

    iApply ("Hcont" with "[Hinterp_reg Hinterp_ctrl Hinterp_pc Hinterp_rmw] [] [-]").
    iFrame. rewrite Hrmw_ag. iFrame. iExists _;done.
    done.
    iExists val,eid_w,_. iSplit.
    2:{
      iFrame. simpl. erewrite reg_dep_fold_eq;eauto.
      iSplit;first done.
      iSplitL "Hctrl'";last done. iApply big_sepS_subseteq;eauto.
    }
    done.
  Qed.

  Lemma mem_write_non_xcl `{!UserProt} {tid : Tid} {o_po_src ctrl_srcs ts ctxt addr kind_s kind_v val
                              ot_coi_pred dep_addr dep_data Ψ} R po_srcs lob_annot dep_regs_data dep_regs_addr:
    ThreadState.ts_reqs ts = AAInter.Next (AAInter.MemWrite 8 (writereq_of_store kind_s kind_v val addr dep_addr dep_data)) ctxt ->
    kind_v = AV_plain ->
    dep_regs_addr ∩ dep_regs_data ⊆ dep_regs_data ->
    dom dep_regs_addr = list_to_set (AAInter.DepOn.regs dep_addr) ->
    let reg_deps_addr := map_fold (λ _ dv acc, reg_dep dv ∪ acc) ∅ dep_regs_addr in
    let mem_deps_addr :=
      foldr (λ (idx : N) (acc : gset Eid),
               from_option (λ md : nat, {[{| EID.tid := tid; EID.iid := ts.(ts_iis).(iis_iid); EID.num := md |}]} ∪ acc) acc
                 (ts.(ts_iis).(iis_mem_reads) !! idx)) ∅ (AAInter.DepOn.mem_reads dep_addr) in
    dom dep_regs_data = list_to_set (AAInter.DepOn.regs dep_data) ->
    let reg_deps_data := map_fold (λ _ dv acc, reg_dep dv ∪ acc) ∅ dep_regs_data in
    let mem_deps_data :=
      foldr (λ (idx : N) (acc : gset Eid),
               from_option (λ md : nat, {[{| EID.tid := tid; EID.iid := ts.(ts_iis).(iis_iid); EID.num := md |}]} ∪ acc) acc
                 (ts.(ts_iis).(iis_mem_reads) !! idx)) ∅ (AAInter.DepOn.mem_reads dep_data) in
    let R_graph_facts := (λ eid,
      eid -{E}> (Event.W kind_s kind_v addr val) ∗
      ⌜(EID.tid eid) = tid ∧ (EID.iid eid) = ts.(ts_iis).(iis_iid) ⌝ ∗
      (* Po *)
      ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{(Edge.Po)}> eid) ∗
      (* Ctrl *)
      ([∗ set] eid_ctrl_src ∈ ctrl_srcs, eid_ctrl_src -{(Edge.Ctrl)}> eid) ∗
      (* Data *)
      ([∗ set] eid_data_src ∈ reg_deps_data ∪ mem_deps_data, eid_data_src -{(Edge.Data)}> eid) ∗
      (* Addr *)
      ([∗ set] eid_addr_src ∈ reg_deps_addr ∪ mem_deps_addr, eid_addr_src -{(Edge.Addr)}> eid) ∗
      (* There must be a write with same addr and val *)
      from_option (λ eid_coi_pred, ⌜EID.tid eid_coi_pred = tid⌝ ∗ eid_coi_pred -{(Edge.Co)}> eid) emp ot_coi_pred )%I in
    o_po_src -{LPo}> -∗
    ctrl_srcs -{Ctrl}> -∗
    last_local_write tid addr ot_coi_pred -∗
    ([∗ set] e_po_src ∈ po_srcs, e_po_src -{Po}>) -∗
    ([∗ map] dr ↦ dv ∈ dep_regs_addr ∪ dep_regs_data, dr ↦ᵣ dv) -∗
    (* node annotations *)
    ([∗ map] node ↦ annot ∈ lob_annot, node ↦ₐ annot) -∗
    (* Lob edge formers *)
    (∀ eid, (eid -{N}> (Edge.W kind_s kind_v) -∗
     ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{(Edge.Po)}> eid) -∗
     ([∗ set] eid_ctrl_src ∈ ctrl_srcs, eid_ctrl_src -{(Edge.Ctrl)}> eid) -∗
     ([∗ set] eid_addr_src ∈ reg_deps_addr ∪ mem_deps_addr, eid_addr_src -{(Edge.Addr)}> eid) -∗
     ([∗ set] eid_data_src ∈ reg_deps_data ∪ mem_deps_data, eid_data_src -{(Edge.Data)}> eid) -∗
     [∗ set] eid_pre ∈ dom lob_annot, eid_pre -{Edge.Lob}> eid) ∗
    (* FE *)
    ((R_graph_facts eid) ∗ ([∗ map] _ ↦ annot ∈ lob_annot, annot)
       ={⊤}[∅]▷=∗
       R eid ∗ □(prot addr val eid))
    ) -∗
    (* continuation *)
    (
      ∀ ts' : ThreadState.t,
        "Hinterp" ∷ thread_local_interp ts' -∗
        ⌜ts'.(ts_regs) !! RNPC = ts.(ts_regs) !! RNPC
        ∧ ts'.(ts_reqs) = ctxt (inl None)⌝ -∗
        ((* exists a bool (indicating if the (atomic) write succeeded) *)
          (* update lts' accordingly *)
          (* Current event is a write *)
          ∃ eid, (R_graph_facts eid) ∗
                 (* R flowing in via lob *)
                 (eid ↦ₐ R eid) ∗
                 ⌜EID.tid eid = tid⌝ ∗
                 (Some eid) -{LPo}> ∗
                 (* local writes at addr is updated *)
                 last_local_write tid addr (Some eid) ∗
                 ctrl_srcs -{Ctrl}> ∗
                 ([∗ map] dr ↦ dv ∈ dep_regs_addr ∪ dep_regs_data, dr ↦ᵣ dv)) -∗
      WP LThreadState.LTSNormal ts' @ tid  {{ lts, to_lts_Phi Ψ lts }}
    )-∗
    thread_local_interp ts -∗
    WP LThreadState.LTSNormal ts @ tid {{ λ lts', to_lts_Phi Ψ lts' }}.
  Proof.
    iIntros (?? Hintersec ???????) "Hpo_src Hctrl Hlw Hpo_srcs HDRs Hna Hef_fe Hcont Hinterp".

    iNamed "Hinterp".
    iDestruct (reg_interp_agree_big with "Hinterp_reg HDRs") as %Hdr_sub.
    iDestruct (ctrl_srcs_interp_agree with "Hinterp_ctrl Hctrl") as %Hctrl_sub.
    assert (dep_regs_data ⊆ ts_regs ts) as Hsub'.
    {
      etrans. 2:exact Hdr_sub.
      rewrite map_intersection_filter in Hintersec.
      apply map_subseteq_spec. intros ?? Hlk.
      destruct (decide (is_Some (dep_regs_addr !! i))).
      destruct i0 as [x' Hlk'].
      rewrite map_subseteq_spec in Hintersec.
      specialize (Hintersec i x').
      feed specialize Hintersec.
      apply map_filter_lookup_Some.
      split. apply lookup_union_Some_l. done.
      split; eexists;done.
      apply lookup_union_Some_l.
      rewrite Hlk in Hintersec. inversion Hintersec. subst x';done.
      rewrite lookup_union_r //. rewrite -elem_of_dom in n. apply not_elem_of_dom. done.
    }

    iApply wp_sswp. iApply (sswp_strong_mono with "[-Hinterp_reg Hinterp_ctrl Hinterp_rmw Hinterp_pc HDRs Hctrl Hcont]").

    iDestruct ("Hef_fe" $! (progress_to_node (get_progress ts) tid)) as "[Hef Hfe]".
    iApply (mem_write_non_xcl with "Hpo_src Hpo_srcs Hlw Hna [Hef] [Hfe]");eauto.
    {
      iIntros "E_R Hpo Hctrl Haddr Hdata".
      iApply ("Hef" with "E_R Hpo [Hctrl] [Haddr] [Hdata]").
      iApply big_sepS_subseteq;eauto.
      simpl. erewrite reg_dep_fold_eq;eauto.
      { etrans. 2:exact Hdr_sub. apply map_union_subseteq_l. }
      simpl. erewrite reg_dep_fold_eq;eauto.
    }
    {
      rewrite /R_graph_facts /=. iIntros "H".
      set (pg := (get_progress ts)).
      erewrite (reg_dep_fold_eq _ (ts_regs ts) dep_regs_addr);eauto. erewrite (reg_dep_fold_eq _ (ts_regs ts) dep_regs_data);eauto.
      rewrite /reg_deps_addr.
      iSpecialize ("Hfe" with "[-]").
      iDestruct "H" as "[(?&?&?&?&?&?) H]".
      iSplitR "H";last done. iFrame.
      iSplit;first done.
      iApply big_sepS_subseteq;eauto.
      iExact "Hfe".
      { etrans. 2:exact Hdr_sub. apply map_union_subseteq_l. }
    }
    iIntros (k) "(%&(?&?&?&?&?&?)&?&Hctrl'&?)"; subst k. simpl.
    iApply ("Hcont" with "[Hinterp_reg Hinterp_ctrl Hinterp_pc Hinterp_rmw] [] [-]").
    iFrame. iExists _;done.
    done.

    iFrame. iExists (progress_to_node (get_progress ts) tid). iFrame.
    iSplit; last done. iSplit; first done.
    simpl. erewrite (reg_dep_fold_eq _ (ts_regs ts) dep_regs_addr);eauto. erewrite (reg_dep_fold_eq _ (ts_regs ts) dep_regs_data);eauto.
    iFrame. iApply big_sepS_subseteq;eauto.
    { etrans. 2:exact Hdr_sub. apply map_union_subseteq_l. }
  Qed.


  Lemma mem_write_xcl_None `{!UserProt} {tid : Tid} {ts ctxt addr kind_s kind_v val dep_addr dep_data Ψ}:
    ThreadState.ts_reqs ts = AAInter.Next (AAInter.MemWrite 8 (writereq_of_store kind_s kind_v val addr dep_addr dep_data)) ctxt ->
    kind_v = AV_atomic_rmw ∨ kind_v = AV_exclusive ->
    None -{Rmw}> -∗
    (* continuation *)
    (
      ∀ ts' : ThreadState.t,
        "Hinterp" ∷ thread_local_interp ts' -∗
        ⌜ts'.(ts_regs) !! RNPC = ts.(ts_regs) !! RNPC
        ∧ ts'.(ts_reqs) = ctxt (inl (Some false))⌝ -∗
        None -{Rmw}> -∗
        WP LThreadState.LTSNormal ts' @ tid  {{ lts, to_lts_Phi Ψ lts }}
    ) -∗
    thread_local_interp ts -∗
    WP LThreadState.LTSNormal ts @ tid {{ λ lts', to_lts_Phi Ψ lts' }}.
  Proof.
    iIntros (??) "Hrmw_src Hcont Hinterp".
    iNamed "Hinterp".

    iDestruct (rmw_pred_interp_agree with "Hinterp_rmw Hrmw_src") as %?.
    iApply wp_sswp. iApply (sswp_strong_mono with "[-Hinterp_rmw Hinterp_reg Hinterp_ctrl Hinterp_pc Hrmw_src Hcont]").
    iApply mem_write_xcl_None;eauto.
    iIntros (k) "%";subst k.
    iApply ("Hcont" with "[Hinterp_reg Hinterp_ctrl Hinterp_pc Hinterp_rmw] [] [-]").
    iFrame. iExists _;done. auto. done.
  Qed.

  Lemma mem_write_xcl_Some `{!UserProt} {tid : Tid} {o_po_src ts ctxt addr kind_s kind_v val ot_coi_pred dep_addr dep_data rmw_src Ψ} R R_loc_in po_srcs ctrl_srcs lob_annot (dep_regs_addr: gmap _ _) dep_regs_data:
    ThreadState.ts_reqs ts = AAInter.Next (AAInter.MemWrite 8 (writereq_of_store kind_s kind_v val addr dep_addr dep_data)) ctxt ->
    kind_v = AV_atomic_rmw ∨ kind_v = AV_exclusive ->
    dep_regs_addr ∩ dep_regs_data ⊆ dep_regs_data ->
    dom dep_regs_addr = list_to_set (AAInter.DepOn.regs dep_addr) ->
    let reg_deps_addr := map_fold (λ _ dv acc, reg_dep dv ∪ acc) ∅ dep_regs_addr in
    let mem_deps_addr :=
      foldr (λ (idx : N) (acc : gset Eid),
               from_option (λ md : nat, {[{| EID.tid := tid; EID.iid := ts.(ts_iis).(iis_iid); EID.num := md |}]} ∪ acc) acc
                 (ts.(ts_iis).(iis_mem_reads) !! idx)) ∅ (AAInter.DepOn.mem_reads dep_addr) in
    dom dep_regs_data = list_to_set (AAInter.DepOn.regs dep_data) ->
    let reg_deps_data := map_fold (λ _ dv acc, reg_dep dv ∪ acc) ∅ dep_regs_data in
    let mem_deps_data :=
      foldr (λ (idx : N) (acc : gset Eid),
               from_option (λ md : nat, {[{| EID.tid := tid; EID.iid := ts.(ts_iis).(iis_iid); EID.num := md |}]} ∪ acc) acc
                 (ts.(ts_iis).(iis_mem_reads) !! idx)) ∅ (AAInter.DepOn.mem_reads dep_data) in
    let R_graph_facts := (λ eid,
        eid -{E}> (Event.W kind_s kind_v addr val) ∗
        ⌜(EID.tid eid) = tid ∧ (EID.iid eid) = ts.(ts_iis).(iis_iid)⌝ ∗
        (* Po *)
        ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{(Edge.Po)}> eid) ∗
        (* Ctrl *)
        ([∗ set] eid_ctrl_src ∈ ctrl_srcs, eid_ctrl_src -{(Edge.Ctrl)}> eid) ∗
        (* Data *)
        ([∗ set] eid_addr_src ∈ reg_deps_addr ∪ mem_deps_addr, eid_addr_src -{(Edge.Addr)}> eid) ∗
        (* Addr *)
        ([∗ set] eid_data_src ∈ reg_deps_data ∪ mem_deps_data, eid_data_src -{(Edge.Data)}> eid) ∗
        (* There must be a write with same addr and val *)
        (from_option (λ eid_coi_pred, ⌜EID.tid eid_coi_pred = tid⌝ ∗ eid_coi_pred -{(Edge.Co)}> eid) emp ot_coi_pred) ∗
        (* Rmw *)
        rmw_src -{(Edge.Rmw)}> eid)%I in
    o_po_src -{LPo}> -∗
    ([∗ set] e_po_src ∈ po_srcs, e_po_src -{Po}>) -∗
    ctrl_srcs -{Ctrl}> -∗
    last_local_write tid addr ot_coi_pred -∗
    Some rmw_src -{Rmw}> -∗
    ([∗ map] dr ↦ dv ∈ dep_regs_addr ∪ dep_regs_data, dr ↦ᵣ dv) -∗
    (* node annotations *)
    ([∗ map] node ↦ annot ∈ lob_annot, node ↦ₐ annot) -∗
    (* Lob edge formers *)
    (∀ eid,
      (eid -{N}> (Edge.W kind_s kind_v) -∗
     ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{(Edge.Po)}> eid) -∗
     ([∗ set] eid_ctrl_src ∈ ctrl_srcs, eid_ctrl_src -{(Edge.Ctrl)}> eid) -∗
     ([∗ set] eid_addr_src ∈ reg_deps_addr ∪ mem_deps_addr, eid_addr_src -{(Edge.Addr)}> eid) -∗
     ([∗ set] eid_data_src ∈ reg_deps_data ∪ mem_deps_data, eid_data_src -{(Edge.Data)}> eid) -∗
     rmw_src -{(Edge.Rmw)}> eid -∗
     ([∗ set] eid_pre ∈ dom lob_annot, eid_pre -{Edge.Lob}> eid)) ∗
    (* local resources that might flow into FE *)
    R_loc_in ∗
    (* FE *)
    (R_loc_in ∗ R_graph_facts eid ∗ Tok{ eid } ∗ ([∗ map] _ ↦ annot ∈ lob_annot, annot)
       ={⊤}[∅]▷=∗
       R ∗ □(prot addr val eid))) -∗
    (* continuationh *)
    (
      ∀ ts' : ThreadState.t,
        "Hinterp" ∷ thread_local_interp ts' -∗
        ⌜ts'.(ts_regs) !! RNPC = ts.(ts_regs) !! RNPC⌝ -∗
      (* exists a bool (indicating if the (atomic) write succeeded) *)
      (∃ b_succ,
          ⌜ts'.(ts_reqs) = ctxt (inl (Some b_succ))⌝ ∗
          ctrl_srcs -{Ctrl}> ∗
          Some rmw_src -{Rmw}> ∗
          (* update lts' accordingly *)
          if b_succ then
            (* success *)
            ∃ eid,
              R_graph_facts eid ∗
              (* R flowing in via lob *)
              (eid ↦ₐ R) ∗
              (Some eid) -{LPo}> ∗
              (* local writes at addr is updated *)
              last_local_write tid addr (Some eid)
          else
            (* failure, things stay unchanged *)
            o_po_src -{LPo}> ∗
            last_local_write tid addr ot_coi_pred ∗
            ([∗ map] node ↦ annot ∈ lob_annot, node ↦ₐ annot) ∗
            R_loc_in) -∗
      WP LThreadState.LTSNormal ts' @ tid  {{ lts, to_lts_Phi Ψ lts }}
    ) -∗
    thread_local_interp ts -∗
    WP LThreadState.LTSNormal ts @ tid {{ λ lts', to_lts_Phi Ψ lts' }}.
  Proof.
    iIntros (?? Hintersec ???????) "Hpo_src Hpo_srcs Hctrl Hlw Hrmw_src HDRs Hna Hef_fe Hcont Hinterp".
    iNamed "Hinterp".
    iDestruct (reg_interp_agree_big with "Hinterp_reg HDRs") as %Hdr_sub.
    iDestruct (ctrl_srcs_interp_agree with "Hinterp_ctrl Hctrl") as %Hctrl_sub.
    iDestruct (rmw_pred_interp_agree with "Hinterp_rmw Hrmw_src") as %Hrmw.

    assert (dep_regs_data ⊆ ts_regs ts) as Hsub'.
    {
      etrans. 2:exact Hdr_sub.
      rewrite map_intersection_filter in Hintersec.
      apply map_subseteq_spec. intros ?? Hlk.
      destruct (decide (is_Some (dep_regs_addr !! i))).
      destruct i0 as [x' Hlk'].
      rewrite map_subseteq_spec in Hintersec.
      specialize (Hintersec i x').
      feed specialize Hintersec.
      apply map_filter_lookup_Some.
      split. apply lookup_union_Some_l. done.
      split; eexists;done.
      apply lookup_union_Some_l.
      rewrite Hlk in Hintersec. inversion Hintersec. subst x';done.
      rewrite lookup_union_r //. rewrite -elem_of_dom in n. apply not_elem_of_dom. done.
    }

    iApply wp_sswp. iApply (sswp_strong_mono with "[-Hinterp_reg Hinterp_ctrl Hinterp_rmw Hinterp_pc HDRs Hctrl Hrmw_src Hcont]").

    iDestruct ("Hef_fe" $! (progress_to_node (get_progress ts) tid)) as "[Hef [R_in Hfe]]".

    iApply (mem_write_xcl_Some with "Hpo_src Hpo_srcs Hlw Hna [Hef] R_in [Hfe]"). eauto. eauto. auto.
    {
      iIntros "E_R Hpo Hctrl Haddr Hdata Hrmw".
      iApply ("Hef" with "E_R Hpo [Hctrl] [Haddr] [Hdata] Hrmw").
      iApply big_sepS_subseteq;eauto.
      simpl. erewrite reg_dep_fold_eq;eauto.
      { etrans. 2:exact Hdr_sub. apply map_union_subseteq_l. }
      simpl. erewrite reg_dep_fold_eq;eauto.
    }
    {
      rewrite /R_graph_facts /=. iIntros "[R_in H]".
      set (pg := (get_progress ts)).
      erewrite (reg_dep_fold_eq _ (ts_regs ts) dep_regs_addr);eauto. erewrite (reg_dep_fold_eq _ (ts_regs ts) dep_regs_data);eauto.
      rewrite /reg_deps_addr.
      iSpecialize ("Hfe" with "[-]").
      iDestruct "H" as "[(?&?&?&?&?&?) H]". iFrame "R_in".
      iSplitR "H";last done. iFrame.
      iSplit;first done.
      iApply big_sepS_subseteq;eauto.
      iExact "Hfe".
      { etrans. 2:exact Hdr_sub. apply map_union_subseteq_l. }
    }
    iIntros (k) "[% [% H]]";subst k.
    simpl. iApply ("Hcont" with "[Hinterp_reg Hinterp_ctrl Hinterp_pc Hinterp_rmw] [] [-]").
    iFrame. iExists _;done. auto.

    iExists b_succ. iSplitR;first done. iFrame.
    simpl. erewrite (reg_dep_fold_eq _ (ts_regs ts) dep_regs_addr);eauto. erewrite (reg_dep_fold_eq _ (ts_regs ts) dep_regs_data);eauto.
    destruct b_succ.
    {
      iExists (progress_to_node (get_progress ts) tid). iDestruct "H" as "((?&?&?&?&?&?&?)&(?&?&?))".
      iFrame.
      iSplit;first done.
      iApply big_sepS_subseteq;eauto.
    }
    { iFrame. }
    { etrans. 2:exact Hdr_sub. apply map_union_subseteq_l. }
  Qed.

  Lemma mem_write_xcl_Some_inv `{!UserProt} {tid : Tid} {o_po_src ts ctxt addr kind_s kind_v val ot_coi_pred dep_addr dep_data rmw_src Ψ} R_loc_in R po_srcs ctrl_srcs lob_annot (dep_regs_addr: gmap _ _) dep_regs_data:
    ThreadState.ts_reqs ts = AAInter.Next (AAInter.MemWrite 8 (writereq_of_store kind_s kind_v val addr dep_addr dep_data)) ctxt ->
    kind_v = AV_atomic_rmw ∨ kind_v = AV_exclusive ->
    dep_regs_addr ∩ dep_regs_data ⊆ dep_regs_data ->
    dom dep_regs_addr = list_to_set (AAInter.DepOn.regs dep_addr) ->
    let reg_deps_addr := map_fold (λ _ dv acc, reg_dep dv ∪ acc) ∅ dep_regs_addr in
    let mem_deps_addr :=
      foldr (λ (idx : N) (acc : gset Eid),
               from_option (λ md : nat, {[{| EID.tid := tid; EID.iid := ts.(ts_iis).(iis_iid); EID.num := md |}]} ∪ acc) acc
                 (ts.(ts_iis).(iis_mem_reads) !! idx)) ∅ (AAInter.DepOn.mem_reads dep_addr) in
    dom dep_regs_data = list_to_set (AAInter.DepOn.regs dep_data) ->
    let reg_deps_data := map_fold (λ _ dv acc, reg_dep dv ∪ acc) ∅ dep_regs_data in
    let mem_deps_data :=
      foldr (λ (idx : N) (acc : gset Eid),
               from_option (λ md : nat, {[{| EID.tid := tid; EID.iid := ts.(ts_iis).(iis_iid); EID.num := md |}]} ∪ acc) acc
                 (ts.(ts_iis).(iis_mem_reads) !! idx)) ∅ (AAInter.DepOn.mem_reads dep_data) in
    let R_graph_facts := (λ eid,
        eid -{E}> (Event.W kind_s kind_v addr val) ∗
        ⌜(EID.tid eid) = tid ∧ (EID.iid eid) = ts.(ts_iis).(iis_iid)⌝ ∗
        (* Po *)
        ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{(Edge.Po)}> eid) ∗
        (* Ctrl *)
        ([∗ set] eid_ctrl_src ∈ ctrl_srcs, eid_ctrl_src -{(Edge.Ctrl)}> eid) ∗
        (* Data *)
        ([∗ set] eid_addr_src ∈ reg_deps_addr ∪ mem_deps_addr, eid_addr_src -{(Edge.Addr)}> eid) ∗
        (* Addr *)
        ([∗ set] eid_data_src ∈ reg_deps_data ∪ mem_deps_data, eid_data_src -{(Edge.Data)}> eid) ∗
        (* There must be a write with same addr and val *)
        (from_option (λ eid_coi_pred, ⌜EID.tid eid_coi_pred = tid⌝ ∗ eid_coi_pred -{(Edge.Co)}> eid) emp ot_coi_pred) ∗
        (* Rmw *)
        rmw_src -{(Edge.Rmw)}> eid)%I in
    o_po_src -{LPo}> -∗
    ([∗ set] e_po_src ∈ po_srcs, e_po_src -{Po}>) -∗
    ctrl_srcs -{Ctrl}> -∗
    last_local_write tid addr ot_coi_pred -∗
    Some rmw_src -{Rmw}> -∗
    ([∗ map] dr ↦ dv ∈ dep_regs_addr ∪ dep_regs_data, dr ↦ᵣ dv) -∗
    (* node annotations *)
    ([∗ map] node ↦ annot ∈ lob_annot, node ↦ₐ annot) -∗
    (* Lob edge formers *)
    (∀ eid,
      (eid -{N}> (Edge.W kind_s kind_v) -∗
     ([∗ set] eid_po_src ∈ po_srcs, eid_po_src -{(Edge.Po)}> eid) -∗
     ([∗ set] eid_ctrl_src ∈ ctrl_srcs, eid_ctrl_src -{(Edge.Ctrl)}> eid) -∗
     ([∗ set] eid_addr_src ∈ reg_deps_addr ∪ mem_deps_addr, eid_addr_src -{(Edge.Addr)}> eid) -∗
     ([∗ set] eid_data_src ∈ reg_deps_data ∪ mem_deps_data, eid_data_src -{(Edge.Data)}> eid) -∗
     rmw_src -{(Edge.Rmw)}> eid -∗
     ([∗ set] eid_pre ∈ dom lob_annot, eid_pre -{Edge.Lob}> eid)) ∗
    (* local resources that might flow into FE *)
    R_loc_in ∗
    (* FE, with excl invariant *)
    (∃ eid_w R_in P,
      (* excl invariant flows in *)
      (R_loc_in ∗ R_graph_facts eid ∗ ([∗ map] _ ↦ annot ∈ lob_annot, annot) -∗
       R_in ∗ eid_w -{Edge.Rf}> rmw_src ∗ ⌜EID.tid eid_w ≠ EID.tid rmw_src⌝ ∗ excl_inv eid_w P) ∗
      (* FE *)
      (R_in ∗ ▷ P eid_w ={⊤∖ ↑(excl_inv_name eid_w)}[∅]▷=∗ R ∗ □(prot addr val eid)))) -∗
    (* continuation *)
    (
      ∀ ts' : ThreadState.t,
        "Hinterp" ∷ thread_local_interp ts' -∗
        ⌜ts'.(ts_regs) !! RNPC = ts.(ts_regs) !! RNPC⌝ -∗
        (* exists a bool (indicating if the (atomic) write succeeded) *)
        (∃ b_succ,
          ⌜ts'.(ts_reqs) = ctxt (inl (Some b_succ))⌝ ∗
          ctrl_srcs -{Ctrl}> ∗
          Some rmw_src -{Rmw}> ∗
          if b_succ then
            (* success *)
            ∃ eid,
              R_graph_facts eid ∗
              (* R flowing in via lob *)
              (eid ↦ₐ R) ∗
              (Some eid) -{LPo}> ∗
              (* local writes at addr is updated *)
              last_local_write tid addr (Some eid)
          else
            (* failure, things stay unchanged *)
            o_po_src -{LPo}> ∗
            last_local_write tid addr ot_coi_pred ∗
            ([∗ map] node ↦ annot ∈ lob_annot, node ↦ₐ annot) ∗
            R_loc_in
      ) -∗
      WP LThreadState.LTSNormal ts' @ tid  {{ lts, to_lts_Phi Ψ lts }}
    ) -∗
    thread_local_interp ts -∗
    WP LThreadState.LTSNormal ts @ tid {{ λ lts', to_lts_Phi Ψ lts' }}.
  Proof.
    iIntros (?? Hintersec ???????) "Hpo_src Hpo_srcs Hctrl Hlw Hrmw_src HDRs Hna Hef_fe".
    iApply (mem_write_xcl_Some with "Hpo_src Hpo_srcs Hctrl Hlw Hrmw_src HDRs Hna [Hef_fe]");auto.
    iIntros (?). iDestruct ("Hef_fe" $! eid) as "[$ [$ (%&%&%&Himpl&Hfe)]]".
    iIntros "(R_loc_in & #R_gr &Htok&Hna)".
    iDestruct ("Himpl" with "[$R_loc_in $R_gr $Hna]") as "(R_in & Ed_rf & Hext & Hinv)".
    iDestruct (excl_inv_open_succ with "[$Htok $Ed_rf $Hinv $Hext]") as ">P". done.
    { iDestruct "R_gr" as "(_&_&_&_&_&_&_&$)". }
    rewrite later_sep. iDestruct "P" as "[P Hclo]".
    iDestruct ("Hfe" with "[$R_in $P]") as ">R".
    iModIntro. iNext. iMod "R". iMod "Hclo". by iFrame.
  Qed.

End rules.
