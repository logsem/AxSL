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

Require Import stdpp.unstable.bitvector.

From SSCCommon Require Import Common.
From iris.base_logic Require Import iprop.

From self Require Import stdpp_extra.

From self.algebra Require Import base.
From self.low.lib Require Import edge.

Module Event.
  (* Event *)

  Inductive t := W (ks : AccessStrength) (ks : AccessVariety) (a : Addr) (v : Val) | R (ks : AccessStrength) (ks : AccessVariety) (a : Addr) (v : Val) |
              B (bκ : BarrierKind).

  Import AACandExec.

  Definition event_interp (gr : Graph.t) (ev : t) (e : Eid) : Prop :=
    ∃ E, gr !! e = Some E
           ∧ match ev with
    | W ks kv a v => AAConsistent.event_is_write_with E ks kv a v
    | R ks kv a v => AAConsistent.event_is_read_with E ks kv a v
    | B (AAArch.DMB κ) => AAConsistent.event_is_dmb κ E
    | B AAArch.ISB => AAConsistent.event_is_isb E
  end.

End Event.

Section def.
  Context `{AABaseG Σ}.

  Import AACandExec.

  Definition event_def (e : Eid) (ev : Event.t): iProp Σ :=
    ∃ gr,  "Hgr_interp_e" ∷ graph_agree gr ∗
           "%Hgr_wf_e" ∷ ⌜ AAConsistent.t gr ⌝ ∗
           "%Hgr_cs_e" ∷ ⌜ AACandExec.NMSWF.wf gr ⌝ ∗
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

  Lemma initial_write_zero a addr v k x:
    EID.tid a = 0%nat ->
    a -{E}> Event.W k x addr v -∗
    (⌜(BV 64 0) = v⌝).
  Proof.
    rewrite event_eq /event_def.
    iIntros (?) "[% (_&%Hcons&%Hwf&%He)] !%".
    symmetry.
    unfold Event.event_interp in He.
    destruct He as [e [G1 G2]].
    apply (Graph.init_zero gr a) => //.
    exists e, addr, k, x => //.
  Qed.

  Lemma initial_write_co a b addr v v' k k' x x':
    EID.tid a = 0%nat ->
    EID.tid b ≠ 0%nat ->
    a -{E}> Event.W k x addr v -∗
    b -{E}> Event.W k' x' addr v' -∗
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
      unfold Event.event_interp in *. unfold AAConsistent.event_is_write_with_addr. destruct He as [e [G1 G2]]. exists e. split; [assumption|].
      apply AAConsistent.event_is_write_with_impl_addr in G2. exact G2.
    }
    unfold Event.event_interp in *. unfold AAConsistent.event_is_write_with_addr. destruct He' as [e [G1 G2]]. exists e. split; [assumption|].
    apply AAConsistent.event_is_write_with_impl_addr in G2. exact G2.
  Qed.

  Lemma write_of_read a b addr v k x:
    a -{E}> Event.R k x addr v -∗
    b -{Edge.Rf}> a -∗
    ∃ k' x', b -{E}> Event.W k' x' addr v.
  Proof.
    rewrite event_eq /event_def.
    rewrite edge_eq /edge_def.
    iIntros "[% (Hag1&%Hcons&%Hwf&%Hread)] [% (Hag2&_&_&%Hrf)]".
    iDestruct (graph_agree_agree with "Hag1 Hag2") as %<-.
    iAssert(∃k' x', ⌜Event.event_interp gr (Event.W k' x' addr v) b⌝)%I as "[%k' [%x' %Hwrite]]".
    { iPureIntro. simpl.
      unfold Event.event_interp.
      destruct Hread as [e [G1 G2]].
      destruct (Graph.wf_read_inv gr a e addr k x v) as [e' [k' [x' [Ew [Hew [His_write Hrf']]]]]] => //.
      assert(e'=b) as ->. 
      {
        apply (Graph.wf_read_single gr _ _ a).
        - assumption.
        - assumption.
        - unfold Edge.ef_edge_interp in Hrf. simpl. assumption.  
      }
      exists k', x', Ew.
      done.
    }
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
    eexists. split;first eauto. destruct E.
    eapply AAConsistent.event_is_write_with_impl_kind;eauto.
    eapply AAConsistent.event_is_read_with_impl_kind;eauto.
    done.
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

     repeat (match goal with
             | [ HE: Is_true _ |- _ ] => rewrite -> bool_unfold in HE;destruct_and ? HE
             | [HE : context [match ?x with _ => _ end] |- _ ] => destruct x eqn:?;try (by inversion HE)
             | [ |- _ ] =>  unfold event_is_write_with in *;
                           unfold event_is_read_with in *;
                           unfold event_is_write_with_P in *;
                           unfold event_is_read_with_P in *;
                           unfold event_is_dmb in *;
                           unfold event_is_isb in *;simpl in *
              end);unfold AACandExec.Candidate.kind_of_wreq_P in *; unfold AACandExec.Candidate.kind_of_rreq_P in *.

    all: repeat (match goal with
                 | [ HE: Is_true _ |- _ ] => rewrite -> bool_unfold in HE;destruct_and ? HE
                 | [HE : context [match ?x with _ => _ end] |- _ ] => destruct x eqn:?;try (by inversion HE)
                 | [HE : match ?x with _ => _ end = _|- _ ] => destruct x;try (by inversion HE)
                 | [HE : match (decide ?x) with _ => _ end = _  |- _ ] => destruct (decide ?x)
                 | [HE : context[let _ := ?X in _] |- _ ] => destruct X
                 | [H1 : (@eq _ (?f ?x) _), H2 : (@eq _ (?f ?x) _) |- _ ] => rewrite H1 in H2;inversion H2
            end);  subst;try done.

    inversion H1;done.
    inversion H2;done.
  Qed.

End lemmas.
