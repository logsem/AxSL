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

From SSCCommon Require Import CBase COption CDestruct.

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
  Import AACand.

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

  Definition default {T} P (o : option T) :=
    match o with
     | Some k => k
     | None => P
    end.

  Definition prot_res (gr: Graph.t) (prot_map: gmap Addr (ProtLoc Σ)) (e: EID.t): iProp Σ :=
    default emp%I $
        write ← gr !! e;
        guard (AAInter.is_mem_write_req (write : iEvent));;
        addr ← AAInter.get_pa write;
        bval ← AAInter.get_mem_value write;
        val ← definitions.bvn_to_bv 64 bval;
        prot ← prot_map !! addr;
        mret (prot val e).


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
    prot_interp prot_map -∗ 『x , q | Φ 』-∗
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
    AACand.NMSWF.wf gr ->
    e ∈ (Candidate.valid_eid gr) ->
    e ∉ s ->
    (Graph.obs_pred_of gr e) ⊆ s ->
    ⊢
      (* default ()%I $ *)
      (*   event ← gr !! e; *)
      (*   addr ← AAInter.get_pa write; *)
      (*   bval ← AAInter.get_mem_value event; *)
      (*   val <- definitions.bvn_to_bv 64 bval; *)
      (*   prot ← prot_map !! addr; *)
      (*   mret ((guard is_mem_read event;;  ) ∗ (⌜is_mem_write event⌝ -∗ )). *)
      match gr !! e with
      | Some (AAInter.IEvent (AAInter.MemWrite _ wr) (inl true)) =>
          let write := AAInter.IEvent (AAInter.MemWrite _ wr) (inl true) in
        default (prot_inv gr prot_map s ==∗ prot_inv gr prot_map ({[e]} ∪ s)) $
        addr ← AAInter.get_pa write;
        bval ← AAInter.get_mem_value write;
        val ← definitions.bvn_to_bv 64 bval;
        prot_loc ← prot_map !! addr;
        mret (((prot_loc val e) ∗ prot_inv gr prot_map s) ==∗ prot_inv gr prot_map ({[e]} ∪ s))%I
      | Some (AAInter.IEvent (AAInter.MemRead _ rr) (inl r)) =>
          let read := AAInter.IEvent (AAInter.MemRead _ rr) (inl r) in
        default (prot_inv gr prot_map s ={⊤}[∅]▷=∗ prot_inv gr prot_map ({[e]} ∪ s)) $
        addr ← AAInter.get_pa read;
        bval ← AAInter.get_mem_value read;
        val ← definitions.bvn_to_bv 64 bval;
        prot_loc ← prot_map !! addr;
        mret ((∀ e_w R,
                 ⌜is_rfe gr e_w e⌝ -∗
                 (prot_loc val e_w ={⊤}[∅]▷=∗ prot_loc val e_w ∗ R) -∗
                 (prot_inv gr prot_map s) ={⊤}[∅]▷=∗ prot_inv gr prot_map ({[e]} ∪ s) ∗ R)%I)
      | _ =>
          prot_inv gr prot_map s ==∗ prot_inv gr prot_map ({[e]} ∪ s)
      end.
  Proof.
    intros Hwf Hvalid Hnin Hsub.
    destruct (gr !! e) as [E|] eqn:HE.
    2:{ set_unfold in Hvalid. set_solver + Hvalid HE. }
    destruct E;destruct o.
    1,2,5-12: (iNamed 1; iFrame;
       rewrite big_sepS_union;last set_solver + Hnin; iFrame; rewrite big_sepS_singleton; rewrite /prot_res HE; simpl;try done).

    all: destruct (decide (n = 8)%N) as [H8|Hn8].
    { (* read *)
      subst n.
      destruct t0. destruct p eqn: Hp.

      simpl.

      destruct (prot_map !! AAInter.ReadReq.pa t1) eqn:Hprot_lk.
      simpl.

      iIntros (???) "Hpers". iNamed 1.
      rewrite (big_sepS_delete _ _ e_w).
      iDestruct "Hprot_res" as "[Hres_rf Hprot_res]".
      iApply (step_fupd_wand with "[Hpers Hres_rf] [Hprot Hprot_res]").
      iApply ("Hpers" with "[Hres_rf]").
      { unfold prot_res.
        opose proof * (wf_read_inv _ e _ (AAInter.ReadReq.pa t1) (definitions.bv_to_bvn b) Hwf HE);try done.
        cdestruct H2.
        pose proof (wf_read_single _ _ _ _ Hwf H5) as <-.
        2:{ set_solver + H1. }
        rewrite H2 /=.
        inversion H4.
        rewrite definitions.bvn_eq in H4. destruct H4.
        assert (x1 = 8)%N as ->.
        {
          simpl in H4.
          lia.
        }
        case_decide;last lia.
        simpl.
        rewrite H3. rewrite Hprot_lk /=.

        rewrite <-Classical_Prop.Eq_rect_eq.eq_rect_eq.
        cdestruct H8.
        rewrite H8. iFrame.
      }

      iIntros "[Hres_rf $]".

      iDestruct (big_sepS_delete _ _ e_w with "[$Hprot_res Hres_rf]") as "Hprot_res".
      1,4:set_solver + H1 Hsub.
      { unfold prot_res.
        opose proof * (wf_read_inv _ e _ (AAInter.ReadReq.pa t1) (definitions.bv_to_bvn b) Hwf HE);try done.
        cdestruct H2.
        pose proof (wf_read_single _ _ _ _ Hwf H5) as <-.
        2:{ set_solver + H1. }
        rewrite H2 /=.
        inversion H4.
        rewrite definitions.bvn_eq in H4. destruct H4.
        assert (x1 = 8)%N as ->.
        {
          simpl in H4.
          lia.
        }
        case_decide;last lia.
        simpl.
        rewrite H3. rewrite Hprot_lk /=.

        rewrite <-Classical_Prop.Eq_rect_eq.eq_rect_eq.
        cdestruct H8.
        rewrite H8. iFrame.
        }

      iFrame; rewrite big_sepS_union;last set_solver + Hnin; iFrame; rewrite big_sepS_singleton;
       rewrite /prot_res HE.
      simpl. done.
      {
        simpl.
        iNamed 1.
        iApply fupd_mask_intro. done.
        iIntros "HH". iNext.
        iMod "HH" as "_".
        iModIntro.

        iFrame; rewrite big_sepS_union;last set_solver + Hnin; iFrame; rewrite big_sepS_singleton;
          rewrite /prot_res HE.
        simpl. done.
      }

      iNamed 1. iFrame.

        iFrame; rewrite big_sepS_union;last set_solver + Hnin; iFrame; rewrite big_sepS_singleton;
          rewrite /prot_res HE.
        simpl. done.
      }
    {
      (* contradict with [size8_wf] *)
        exfalso.
        rewrite /wf in Hwf. assert (size8_wf gr) as Hwf_size by naive_solver;clear Hwf.
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
      opose proof * (mem_wf_spec_write _ Hwf_mem _ _ HE).
      done.
      cdestruct H1. destruct t0;last done. destruct b;last done.
      simpl.
      destruct (prot_map !! AAInter.WriteReq.pa t1) eqn:Hprot_lk.
      {
        simpl.

        iIntros "[Hres Hinv]". iNamed "Hinv".
        iFrame; rewrite big_sepS_union;last set_solver + Hnin; iFrame; rewrite big_sepS_singleton.
        unfold prot_res.
        rewrite HE /=. rewrite Hprot_lk /=.
        iFrame. done.
      }
      simpl.
      iNamed 1.
      iFrame.
      iFrame; rewrite big_sepS_union;last set_solver + Hnin; iFrame; rewrite big_sepS_singleton.
      unfold prot_res.
      rewrite HE /=. rewrite Hprot_lk /=.
      done.
    }
    {
      (* contradict with [size8_wf] *)
        exfalso.
        rewrite /wf in Hwf. assert (size8_wf gr) as Hwf_size by naive_solver;clear Hwf.
        set_unfold in Hwf_size.
        specialize (Hwf_size e). simpl in Hwf_size.
        apply Hwf_size.
        eexists. split;[eassumption|].
        simpl.
        destruct n;repeat (try destruct p;auto).
    }
    Qed.

End lemma.
