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

From iris_named_props Require Export named_props.
From iris.bi Require Import derived_laws.
From iris.base_logic.lib Require Import fancy_updates.

From self.lang Require Import mm opsem.
From self.algebra Require Import base.
From self.low Require Import edge event.

Section def.
  Context `{CMRA Σ} `{!AABaseG}.

  (** Protocols *)
  Definition ProtNode Σ := Eid -> iProp Σ.
  Definition ProtLoc Σ := Val -> (ProtNode Σ).

  (** Graph *)
  Import AACandExec.

  Definition prot_interp (m : gmap Addr (ProtLoc Σ)) : iProp Σ :=
    ∃ (gns : gmap Addr gname),
      (* auth gmap for Addr -> gname *)
      ("Hprot_loc_gn_auth" ∷ ghost_map_auth AAProtN 1 gns) ∗
      (* ("%Hannot_gn_map_dom" ∷ ⌜dom gns ⊆ dom m⌝) ∗ *)
      (* for every addr [x], [Φ] is the protocol *)
      "Hprot_loc_saved" ∷
        [∗ map] x ↦ gn;Φ ∈ gns;m,
            (* protocol with saved_prot *)
            saved_prot_own gn Φ.

  (* The predicate asserting resources for [e] given [prot_map] *)
  Definition prot_res (gr: Graph.t) (prot_map: gmap Addr (ProtLoc Σ)) (e: EID.t): iProp Σ :=
    match gr !! e with
    | Some (AAInter.IEvent (AAInter.MemWrite 8 wr) (inl (Some true)))
    | Some (AAInter.IEvent (AAInter.MemWrite 8 wr) (inl None)) =>
        let loc := AAConsistent.addr_of_wreq wr in
        let val := AAConsistent.value_of_wreq wr in
        (from_option (λ prot_loc, prot_loc val e) True%I (prot_map !! loc))
    | _ => emp%I
    end.

  Definition prot_inv (gr: Graph.t) (m: gmap Addr (ProtLoc Σ)) (s: gset Eid) : iProp Σ :=
    "Hprot" ∷ prot_interp m ∗
    "Hprot_res" ∷ ([∗ set] e ∈ s, prot_res gr m e).

End def.

Lemma prot_interp_alloc_aux `{CMRA Σ} `{!AABaseInG} gm:
  ⊢ |==> ∃ (gns : gmap Addr gname), ([∗ map] _ ↦ gn;Φ∈ gns ;(gm : gmap Addr (Val -> Eid -> iProp Σ)), saved_prot_own gn Φ).
Proof.
  induction gm using map_ind.
  - iModIntro. iExists ∅. done.
  - iDestruct IHgm as ">[% H]".
    iDestruct (saved_prot_alloc x) as ">[%gn Halloc]".
    iExists (<[i := gn]> gns).
    iModIntro.
    iDestruct (big_sepM2_alt with "H") as "[% H]".
    rewrite big_sepM2_insert. iFrame. rewrite big_sepM2_alt. iSplit;[iPureIntro;assumption|iFrame].
    apply not_elem_of_dom. rewrite H2. apply not_elem_of_dom;assumption.
    assumption.
Qed.

Lemma prot_interp_alloc `{CMRA Σ} `{!AABaseInG} gm:
  ⊢ |==> ∃ GN, (∃ (gns : gmap Addr gname),
                    ghost_map_auth GN 1 gns ∗
                    ([∗ map] x ↦ gn;Φ∈ gns;(gm : gmap Addr (Val -> Eid -> iProp Σ)),
                         ghost_map_elem GN x (DfracOwn 1) gn ∗ saved_prot_own gn Φ)).
Proof.
  iIntros.
  iDestruct (prot_interp_alloc_aux gm) as ">[% Hsaved]".
  iDestruct (ghost_map_alloc gns) as ">[%GN [Hauth Hfrag]]".
  iFrame.
  rewrite big_sepM2_sep.
  iDestruct (big_sepM2_dom with "Hsaved") as %Hdom.
  iFrame. iModIntro.
  iApply (big_sepM2_mono (λ k v _, k ↪[GN] v ∗ emp)%I). iIntros (?????) "[$ _]".
  iApply (big_sepM2_sepM_2 (λ k v, k ↪[GN] v)%I (λ _ _, emp%I) with "[$Hfrag]").
  intro. rewrite -!elem_of_dom.
  rewrite set_eq in Hdom. apply Hdom;done.
  done.
Qed.

Section lemma.
  Context `{CMRA Σ}.
  Context `{!AABaseG}.

  Import Graph.

  (** protocol *)
  Lemma prot_loc_agree x q Φ prot_map:
    prot_interp prot_map -∗ Prot[x , q | Φ] -∗
      ∃ ψ, ⌜prot_map !! x = Some ψ⌝ ∗ ▷ (∀ x y, Φ x y ≡ ψ x y).
  Proof.
    rewrite /prot_interp prot_loc_eq /prot_loc_def.
    iIntros "[%gns H] [%gn [Hgn Hsv]]". iNamed "H".
    iDestruct (prot_loc_gn_both_agree with "Hgn Hprot_loc_gn_auth") as %?.
    iDestruct (big_sepM2_lookup_l  with "Hprot_loc_saved") as "[% [%Hlk Hsvv]]". exact H1.
    rewrite Hlk.
    iExists x2. iSplitR;first done.
    rewrite bi.later_forall. iIntros. rewrite bi.later_forall. iIntros.
    iApply (saved_prot_agree with "Hsv Hsvv").
  Qed.

  (* NOTE: the modalities have to be these to make things work *)
  Lemma prot_inv_unchanged `{!invGS_gen HasNoLc Σ} gr prot_map s e :
    AACandExec.NMSWF.wf gr ->
    e ∈ (AACandExec.Candidate.valid_eid gr) ->
    e ∉ s ->
    (Graph.obs_pred_of gr e) ⊆ s ->
    ⊢
      match gr !! e with
      | Some (AAInter.IEvent (AAInter.MemWrite 8 wr) (inl (Some true)))
      | Some (AAInter.IEvent (AAInter.MemWrite 8 wr) (inl None)) =>
          let loc := AAConsistent.addr_of_wreq wr in
          let val := AAConsistent.value_of_wreq wr in
          (((from_option (λ prot_loc, prot_loc val e) True%I (prot_map !! loc)) ∗ prot_inv gr prot_map s) ==∗ prot_inv gr prot_map ({[e]} ∪ s))%I
      | Some (AAInter.IEvent (AAInter.MemRead 8 rr) (inl (val, _))) =>
          (∀ e_rf E_w R addr_w val_w kind_s_w kind_s_v, ⌜is_rfe gr e_rf e ∧ gr !! e_rf = Some E_w ∧
                                 AAConsistent.event_is_write_with E_w kind_s_w kind_s_v addr_w val_w⌝ -∗
                     ((from_option (λ prot_loc, prot_loc val_w e_rf) True%I (prot_map !! addr_w))
                      ={⊤}[∅]▷=∗ (from_option (λ prot_loc, prot_loc val_w e_rf) True%I (prot_map !! addr_w)) ∗ R) -∗
                     (prot_inv gr prot_map s) ={⊤}[∅]▷=∗ prot_inv gr prot_map ({[e]} ∪ s) ∗ R)%I
      | _ =>
          (prot_inv gr prot_map s ==∗ prot_inv gr prot_map ({[e]} ∪ s))%I
      end.
  Proof.
    intros Hwf Hvalid Hnin Hsub.
    destruct (gr !! e) as [E|] eqn:HE.
    2:{ set_unfold in Hvalid. set_solver + Hvalid HE. }
    destruct E;destruct o.
    1,2,5-15:
      (iNamed 1; iFrame; rewrite big_sepS_union;last set_solver + Hnin; iFrame;
       rewrite big_sepS_singleton;
       rewrite /prot_res HE;clear;done).
    all: destruct (decide (n = 8)%N) as [H8|Hn8].
    { (* read *)
      subst n.
      destruct t0. destruct p.
      iIntros (??????? [?[? ?]]) "Hpers". iNamed 1.
      rewrite (big_sepS_delete _ _ e_rf).
      iDestruct "Hprot_res" as "[Hres_rf Hprot_res]".
      iApply (step_fupd_wand with "[Hpers Hres_rf] [Hprot Hprot_res]").
      iApply ("Hpers" with "[Hres_rf]").
      { unfold prot_res. rewrite H2. destruct E_w;destruct o0;try contradiction.
        assert (n = 8)%N as ->.
        {
          destruct (decide (n = 8))%N;first assumption.
          exfalso.
          rewrite /wf in Hwf. assert (size8_wf gr) as Hwf_size by naive_solver;clear Hwf.
          rewrite CBool.bool_unfold in Hwf_size.
          set_unfold in Hwf_size.
          specialize (Hwf_size e_rf). simpl in Hwf_size.
          apply Hwf_size.
          eexists. split;[eassumption|].
          simpl.
          destruct n;repeat (try destruct p;auto).
        }
        simpl in H3.
        rewrite CBool.bool_unfold in H3.
        destruct H3 as [[_ ?] [_ Hva]].
        unfold addr_and_value_of_wreq in Hva.
        destruct t2.
        case_match;[|inversion Hva].
        unfold eq_rec_r, eq_rec in Hva. subst.
        rewrite <-Classical_Prop.Eq_rect_eq.eq_rect_eq in Hva.
        inversion Hva. subst.
        destruct t0;[destruct o0;[destruct b0;[| contradiction] | ] |contradiction].
        simpl. iFrame.
        simpl. iFrame.
      }
      iIntros "[Hres_rf $]".
      iDestruct (big_sepS_delete _ _ e_rf with "[$Hprot_res Hres_rf]") as "Hprot_res".
      1,4:set_solver + H1 Hsub.
      { unfold prot_res. rewrite H2. destruct E_w;destruct o0;try contradiction.
        assert (n = 8)%N as ->.
        {
          destruct (decide (n = 8))%N;first assumption.
          exfalso.
          rewrite /wf in Hwf. assert (size8_wf gr) as Hwf_size by naive_solver;clear Hwf.
          rewrite CBool.bool_unfold in Hwf_size.
          set_unfold in Hwf_size.
          specialize (Hwf_size e_rf). simpl in Hwf_size.
          apply Hwf_size.
          eexists. split;[eassumption|].
          simpl.
          destruct n;repeat (try destruct p;auto).
        }
        simpl in H3.
        rewrite CBool.bool_unfold in H3.
        destruct H3 as [[_ ?] [_ Hva]].
        unfold addr_and_value_of_wreq in Hva.
        destruct t2.
        case_match;[|inversion Hva].
        unfold eq_rec_r, eq_rec in Hva. subst.
        rewrite <-Classical_Prop.Eq_rect_eq.eq_rect_eq in Hva.
        inversion Hva. subst.
        destruct t0;[destruct o0;[destruct b0;[| contradiction] | ] |contradiction].
        simpl. iFrame.
        simpl. iFrame.
      }
      iFrame; rewrite big_sepS_union;last set_solver + Hnin; iFrame; rewrite big_sepS_singleton;
       rewrite /prot_res HE.
      clear;done.
      {
        (* contradict with [mem_wf] *)
        exfalso.
        rewrite /wf in Hwf. assert (mem_wf gr) as Hwf_mem by naive_solver;clear Hwf.
        rewrite CBool.bool_unfold in Hwf_mem.
        set_unfold in Hwf_mem.
        specialize (Hwf_mem e). simpl in Hwf_mem.
        rewrite HE /= in Hwf_mem.
        apply Hwf_mem.
        eexists.
        split;[reflexivity|].
        simpl. rewrite andb_comm. auto.
      }
    }
    {
      (* contradict with [size8_wf] *)
        exfalso.
        rewrite /wf in Hwf. assert (size8_wf gr) as Hwf_size by naive_solver;clear Hwf.
        rewrite CBool.bool_unfold in Hwf_size.
        set_unfold in Hwf_size.
        specialize (Hwf_size e). simpl in Hwf_size.
        apply Hwf_size.
        eexists. split;[eassumption|].
        simpl.
        destruct n;repeat (try destruct p;auto).
    }
    { (* write *)
      subst n.
      rewrite /wf in Hwf. assert (mem_wf gr) as Hwf_mem by naive_solver;clear Hwf.
      rewrite CBool.bool_unfold in Hwf_mem.
      set_unfold in Hwf_mem.
      specialize (Hwf_mem e). simpl in Hwf_mem.
      rewrite HE /= in Hwf_mem.

      destruct t0. destruct o. destruct b.
      {
      iIntros "[Hres Hinv]". iNamed "Hinv".
      iFrame; rewrite big_sepS_union;last set_solver + Hnin; iFrame; rewrite big_sepS_singleton.
      unfold prot_res.
      rewrite HE. iFrame.
      clear;done.
      }
      2:{
      iIntros "[Hres Hinv]". iNamed "Hinv".
      iFrame; rewrite big_sepS_union;last set_solver + Hnin; iFrame; rewrite big_sepS_singleton.
      unfold prot_res.
      rewrite HE. iFrame.
      clear;done.
      }

      all: (exfalso;apply Hwf_mem;eexists;split;[reflexivity|simpl;rewrite andb_comm;auto]).
    }
    {
      (* contradict with [size8_wf] *)
        exfalso.
        rewrite /wf in Hwf. assert (size8_wf gr) as Hwf_size by naive_solver;clear Hwf.
        rewrite CBool.bool_unfold in Hwf_size.
        set_unfold in Hwf_size.
        specialize (Hwf_size e). simpl in Hwf_size.
        apply Hwf_size.
        eexists. split;[eassumption|].
        simpl.
        destruct n;repeat (try destruct p;auto).
    }
    Qed.

End lemma.
