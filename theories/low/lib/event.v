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

Require Import stdpp.bitvector.definitions.

From SSCCommon Require Import Common.
From iris.base_logic Require Import iprop.

From self Require Import stdpp_extra.

From self.low.lib Require Import edge.

Module Event.
  (* Event *)

  Inductive t := W (kv : AccessVariety) (ks : AccessStrength) (a : Addr) (v : Val) | R (kv : AccessVariety) (ks : AccessStrength) (a : Addr) (v : Val) |
              B (bk : BarKind).

  Import AACand.

  Definition event_interp (gr : Graph.t) (ev : t) (e : Eid) : Prop :=
    ∃ E, gr !! e = Some E
           ∧ match ev with
    | W kv ks a v =>
        AAInter.is_mem_write_kindP (λ ak', ak' = access_kind_of_AK kv ks) E ∧ AAInter.get_pa E = Some a ∧ AAInter.get_mem_value E = Some (bv_to_bvn v)
    | R kv ks a v =>
        AAInter.is_mem_read_kindP (λ ak', ak' = access_kind_of_AK kv ks) E ∧ AAInter.get_pa E = Some a ∧ AAInter.get_mem_value E = Some (bv_to_bvn v)
    | B bk =>
        AAInter.is_barrierP (λ bk', bk' = barrier_of bk) E
  end.

End Event.

Section def.
  Context `{AABaseG Σ}.

  Import AACand.

  Definition event_def (e : Eid) (ev : Event.t): iProp Σ :=
    ∃ gr,  "Hgr_interp_e" ∷ graph_agree gr ∗
           "%Hgr_wf_e" ∷ ⌜ AAConsistent.t gr ⌝ ∗
           "%Hgr_cs_e" ∷ ⌜ NMSWF.wf gr ⌝ ∗
           "%Hedge_interp" ∷ ⌜Event.event_interp gr ev e⌝.

  Definition event_def_aux : seal (@event_def). Proof. by eexists. Qed.
  Definition event := event_def_aux.(unseal).
  Definition event_eq : @event = @event_def := event_def_aux.(seal_eq).

End def.

Notation "e '-{E}>' E" :=
  (event e E) (at level 21,  E at level 50, format "e  '-{E}>'  E") : bi_scope.

Section lemmas.
  Context `{CMRA Σ} `{!AABaseG}.

  #[global] Instance event_def_persist e E : Persistent(event e E).
  Proof. rewrite event_eq. rewrite /event_def. apply _. Qed.

  Import AACand.

  Lemma initial_write_zero a addr v kv ks:
    EID.tid a = 0%nat ->
    a -{E}> Event.W kv ks addr v -∗
    (⌜(BV 64 0) = v⌝).
  Proof.
    rewrite event_eq /event_def.
    iIntros (?) "[% (_&%Hcons&%Hwf&%He)] !%".
    symmetry.
    unfold Event.event_interp in He.
    destruct He as [e [G1 G2]].

    opose proof * (Graph.init_zero gr a Hwf H1 v).
    naive_solver.
    clear -H2.
    rewrite bvn_eq in H2.
    destruct H2.
    apply bv_eq.

    simpl in H0.
    unfold definitions.bvn_unsigned in H0.
    rewrite H0.
    done.
  Qed.

  Lemma initial_write_co a b addr v v' kv ks kv' ks':
    EID.tid a = 0%nat ->
    EID.tid b ≠ 0%nat ->
    a -{E}> Event.W kv ks addr v -∗
    b -{E}> Event.W kv' ks' addr v' -∗
    a -{Edge.Co}> b.
  Proof.
    rewrite event_eq /event_def.
    rewrite edge_eq /edge_def.
    iIntros (??) "[% (Hag1&%Hcons&%Hwf&%He)] [% (Hag2&_&_&%He')]".
    iDestruct (graph_agree_agree with "Hag1 Hag2") as %<-.
    iExists gr. iFrame "∗%".
    iPureIntro.
    simpl.
    apply (Graph.init_co _ _ _ addr) => //.
    { 
      unfold Event.event_interp in *.
      cdestruct He, He'. subst.
      eexists. split;first eassumption.
      simpl. done.
    }
      unfold Event.event_interp in *.
      cdestruct He, He'. subst.
      eexists. split;first eassumption.
      simpl. rewrite H9. done.
  Qed.

  Lemma write_of_read a b addr v kv ks:
    a -{E}> Event.R kv ks addr v -∗
    b -{Edge.Rf}> a -∗
    ∃ kv' ks', b -{E}> Event.W kv' ks' addr v.
  Proof.
    rewrite event_eq /event_def.
    rewrite edge_eq /edge_def.
    iIntros "[% (Hag1&%Hcons&%Hwf&%Hread)] [% (Hag2&_&_&%Hrf)]".
    iDestruct (graph_agree_agree with "Hag1 Hag2") as %<-.
    assert (∃ kv' ks', Event.event_interp gr (Event.W kv' ks' addr v) b) as [k' [x' Hwrite]].
    {
      unfold Event.event_interp.
      cdestruct Hread.
      opose proof * (Graph.wf_read_inv gr a _ addr v);try eassumption.
      done.
      simpl. rewrite H3 //.
      simpl. rewrite H4 //.
      cdestruct H5.
    assert (NMSWF.rf_wf gr) as Hwf_rf.
    clear -Hwf. rewrite /NMSWF.wf in Hwf. naive_solver.
    unfold NMSWF.rf_wf in Hwf_rf.
     cdestruct Hwf_rf. clear H9 H10 H12.
     unfold GRel.grel_functional in H11.
     ospecialize * (H11 a x b).
     set_solver + H8.
     set_solver + Hrf.
     subst x.


    assert (NMSWF.mem_wf gr) as Hwf_mem.
    clear -Hwf. rewrite /NMSWF.wf in Hwf. naive_solver.
    unfold NMSWF.mem_wf in Hwf_mem.
    assert (b ∈ Candidate.mem_writes gr ∩ Candidate.mem_explicit gr).
    {
      clear - H5 Hwf_mem.
      set_unfold.
      hauto lq:on.
    }
    unfold Candidate.mem_explicit in H9.
    unfold Candidate.mem_by_kind in H9.
    set_unfold in H9.
    destruct H9 as ((?&?&?)&?&?&?).
    rewrite H11 in H9. inversion H9;subst x4.
    rewrite H11 in H5. inversion H5;subst x. clear H9.
    cbn in *.

    destruct x6;simpl in H12;try contradiction. simpl.
    destruct access_kind;try contradiction.
    destruct e.
     exists Explicit_access_kind_variety, Explicit_access_kind_strength.
     eexists.
     split;first eassumption.
     simpl.

    destruct x7;try contradiction. destruct b0;try contradiction.
    unfold access_kind_of_AK.

    cbn in *.
    split;first done.
    clear H11 H5.
    subst.
    rewrite H7.
    done.
    }

    simpl in Hrf.

    iExists k', x', gr.
    iFrame "∗%".
  Qed.

  Lemma event_node eid E :
    eid -{E}> E -∗ eid -{N}> (match E with
                              | Event.W ks kv _ _ => Edge.W ks kv
                              | Event.R ks kv _ _ => Edge.R ks kv
                              | Event.B bκ => Edge.B bκ
                              end).
  Proof.
    rewrite event_eq. rewrite /event_def.
    rewrite node_eq. rewrite /node_def.
    rewrite edge_eq. rewrite /edge_def.
    iIntros "[% [Hag [% [% %HE]]]]".
    iExists _. iFrame. iSplit; first done. iSplit; first done.
    iPureIntro. simpl. split;first done. rewrite /Edge.ef_node_interp.
    rewrite /Event.event_interp in HE.
    destruct HE as [? [? ?]].
    eexists. split;first eauto. destruct E;
    naive_solver.
  Qed.

  Import AAConsistent.

  Lemma event_agree eid E E' :
    eid -{E}> E -∗ eid -{E}> E' -∗ ⌜E = E'⌝.
  Proof.
    rewrite event_eq. rewrite /event_def.
    iIntros "[% H1] [% [Hag [_ [_ %HE']]]]". iNamed "H1".
    iDestruct (graph_agree_agree with "Hgr_interp_e Hag") as %->. iPureIntro.

    destruct HE' as [? [Hlk' HE']]. destruct Hedge_interp as [? [Hlk HE]]. rewrite Hlk in Hlk'. inversion Hlk'. subst x0.
    clear Hgr_wf_e Hgr_cs_e.

    destruct E, E';
    cdestruct HE, HE';
    subst;

     repeat (match goal with
                 | [H1 : (@eq _ (?f ?x) _), H2 : (@eq _ (?f ?x) _) |- _ ] => rewrite H1 in H2;inversion H2
            end);  subst;try done.

    cdestruct H5.
    inversion H1. subst x2.
    cdestruct H11. subst x1.
    rewrite H2 in H6.
    cdestruct H6.
    subst.
    cdestruct H10.
    subst. done.

    cdestruct H5.
    cbn in *.
    inversion H5. subst x4.
    cdestruct H12. subst x1.
    rewrite H2 in H6.
    cdestruct H6.
    subst.
    cdestruct H10.
    subst. done.

    rewrite AAInter.is_barrierP_spec in HE.
    rewrite AAInter.is_barrierP_spec in HE'.
    cdestruct HE, HE'.
    subst.
    inversion H2.
    unfold barrier_of in H3.
    destruct bk,bk0;
    cdestruct H3;
    done.

  Qed.

End lemmas.
