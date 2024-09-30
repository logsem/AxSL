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

(* Simplified version of [CandidateExecutions.v] of [system-semantics-coq]. *)

(** This file provide a common type for representing candidate executions
    for all memory models to use *)

Require Import Ensembles.

Require Import Strings.String.

From stdpp Require Export listset.
From stdpp Require Export gmap.

Require Import SSCCommon.Common.
Require Import SSCCommon.Exec.
Require Import SSCCommon.GRel.

Require Import ISASem.Interface.
Require Import ISASem.SailArmInstTypes.


Open Scope Z_scope.
Open Scope stdpp_scope.

(* event ID *)
Module EID.
  Record t :=
    make {
        (* thread ID *)
        tid : nat;
        (* Instruction ID *)
        iid : nat;
        (* event number *)
        num : nat
      }.

  #[global] Instance eta : Settable _ :=
    settable! make <tid; iid; num>.

  #[global] Instance eq_dec : EqDecision t.
  Proof. solve_decision. Defined.

  #[global] Instance countable : Countable t.
  Proof.
    eapply (inj_countable' (fun eid => (tid eid, iid eid, num eid))
              (fun x => make x.1.1 x.1.2 x.2)).
    sauto.
  Qed.
End EID.

Module CandidateExecutions (Arch : Arch) (IA : InterfaceT Arch). (* to be imported *)
  Import Arch.
  Import IA.
  Notation outcome := (IA.outcome empOutcome).
  Notation iMon := (IA.iMon empOutcome).
  Notation iSem := (IA.iSem empOutcome).
  Notation iEvent := (IA.iEvent empOutcome).
  Notation iTrace := (IA.iTrace empOutcome).


  Module Candidate.

    Record t :=
      make {
         (** Each thread is a list of instruction, which each have a trace.
              We force the return type to be unit, but it just means we
              forget the actual value. *)
          events : list (list (iTrace ()));
          (** Program order. The per-thread order of all events in the trace
             po can be deduced by the order of events in the trace *)
          po : grel EID.t;
          (** Memory read-from *)
          rf : grel EID.t;
          (** Memory coherence: for each pa, list of writes in order *)
          co : grel EID.t;
          (** Register read from (needed because of potentially relaxed register) *)
          rrf : grel EID.t;
          (** rmw *)
          rmw : grel EID.t;
          (** Same instruction, should be an equivalence relation.
           can be deduced from trace structure *)
          si : grel EID.t;
          (** intra-instruction address dependencies (to memory events) *)
          iio_addr : grel EID.t;
          (** intra-instruction data dependencies (to memory and register writes) *)
          iio_data : grel EID.t;
          (** intra-instruction control dependencies (to branches) *)
          iio_ctrl : grel EID.t;
        }.

    (** NOTE: we assume initial writes are in the traces of thread 0, one trace contains only one such write*)

    (** Get an event at a given event ID in a candidate *)
    Global Instance lookup_eid : Lookup EID.t iEvent t :=
      fun eid cd =>
        traces ← cd.(events) !! eid.(EID.tid);
    '(trace, result) ← traces !! eid.(EID.iid);
    trace !! eid.(EID.num).

    (** This is true if one of the thread had an ISA model failure
        like a Sail assertion or an Isla assumption that failed *)
    Definition failed (cd : t) : bool :=
      existsb (fun traces =>
                 let '(trace, trace_end) := List.last traces ([], inl ()) in
                 match trace_end with | inr _ => true | inl _ => false end)
        cd.(events).

    Definition event_list (cd : t) : list (EID.t*iEvent) :=
      '(tid, traces) ← enumerate cd.(events);
    '(iid, (trace, trace_end)) ← enumerate traces;
    '(num, event) ← enumerate trace;
    [(EID.make tid iid num, event)].

  Global Typeclasses Opaque event_list.

  Import SetUnfoldPair.

  Lemma event_list_match cd eid ev :
    cd !! eid = Some ev ↔ (eid, ev) ∈ event_list cd.
  Proof.
    (* Unfold everything properly on both side, and naive_solver does it. *)
    unfold lookup at 1.
    unfold lookup_eid.
    repeat setoid_rewrite bind_Some.
    unfold event_list.
    destruct eid.
    set_unfold.
    repeat setoid_rewrite exists_pair.
    naive_solver.
  Qed.

  Global Instance set_unfold_elem_of_event_list cd x :
    SetUnfoldElemOf x (event_list cd) (cd !! x.1 = Some x.2).
  Proof. tcclean. destruct x. symmetry. apply event_list_match. Qed.

  Lemma event_list_NoDup1 cd : NoDup (event_list cd).*1.
  Proof.
    unfold event_list.
    rewrite fmap_unfold.
    cbn.
    apply NoDup_bind;
      [set_unfold; hauto lq:on rew:off | idtac | apply NoDup_enumerate].
    intros [? ?] ?.
    apply NoDup_bind;
      [set_unfold; hauto lq:on rew:off | idtac | apply NoDup_enumerate].
    intros [? [? ?]] ?.
    apply NoDup_bind;
      [set_unfold; hauto lq:on rew:off | idtac | apply NoDup_enumerate].
    intros [? [? ?]] ?.
    auto with nodup.
  Qed.

  Lemma event_list_NoDup cd : NoDup (event_list cd).
  Proof. eapply NoDup_fmap_1. apply event_list_NoDup1. Qed.

  Definition event_map (cd : t) : gmap EID.t iEvent :=
    event_list cd |> list_to_map.

  Lemma event_map_match cd eid : (event_map cd) !! eid = cd !! eid.
  Proof.
    unfold event_map.
    destruct (cd !! eid) eqn: Heq.
    - apply elem_of_list_to_map.
      + apply event_list_NoDup1.
      + set_solver.
    - apply not_elem_of_list_to_map_1.
      set_solver.
  Qed.

  Global Instance lookup_unfold_event_map x cd R :
    LookupUnfold x cd R → LookupUnfold x (event_map cd) R.
  Proof. tcclean. apply event_map_match. Qed.

    (** Accessors *)

  Definition collect_all (P : iEvent -> bool) (cd : t) : gset EID.t :=
    filter (fun '(eid, event) => P event) (event_list cd)
      |> map fst |> list_to_set.

  Global Instance set_unfold_elem_of_filter `{FinSet A B}
    `{∀ x : A, Decision (P x)} x (a : B) Q:
    SetUnfoldElemOf x a Q ->
    SetUnfoldElemOf x (filter P a) (P x ∧ Q).
  Proof. tcclean. apply elem_of_filter. Qed.

  Global Instance set_unfold_elem_of_filter_list A
    `{∀ x : A, Decision (P x)} x (a : list A) Q:
    SetUnfoldElemOf x a Q ->
    SetUnfoldElemOf x (filter P a) (P x ∧ Q).
  Proof. tcclean. apply elem_of_list_filter. Qed.

  Global Instance set_elem_of_collect_all eid P cd :
    SetUnfoldElemOf eid (collect_all P cd) (∃x, cd !! eid = Some x ∧ P x).
  Proof. tcclean. set_unfold. hauto db:core. Qed.
  Global Typeclasses Opaque collect_all.

  (** Get the set of all valid EID for that candidate *)
  Definition valid_eid (cd : t) :=
    collect_all (fun event => true) cd.

  (** Get the set of all register reads *)
    Definition reg_reads (cd : t) :=
      collect_all
        (fun event =>
           match event with
           | IEvent (RegRead _ _) _ => true
           | _ => false end)
        cd.

    Global Instance set_elem_of_reg_read eid cd :
      SetUnfoldElemOf eid (reg_reads cd)
        (∃ reg reg_acc res,
            cd !! eid = Some (IEvent (RegRead reg reg_acc) res)).
    Proof. tcclean. set_unfold. hauto l:on. Qed.
    Global Typeclasses Opaque reg_reads.

    (** Get the set of all register writes *)
    Definition reg_writes (cd : t) :=
      collect_all
        (fun event =>
           match event with
           | IEvent (RegWrite _ _ _ _) _ => true
           | _ => false end)
        cd.

    Global Instance set_elem_of_reg_writes eid cd :
      SetUnfoldElemOf eid (reg_writes cd)
        (∃ reg reg_acc dep val,
            cd !! eid = Some (IEvent (RegWrite reg reg_acc dep val) ())).
    Proof. tcclean. set_unfold. sauto dep:on. Qed.
    Global Typeclasses Opaque reg_writes.

    Definition wreq_is_valid {n} (r: WriteReq.t n) :=
      match r.(WriteReq.access_kind) with
        | AK_explicit _ => true
        | _ => false
      end.

    (* valid means the write has real effects *)
    Definition wresp_is_valid (o : option bool + abort) :=
      match o with
      (* either a write without response (i.e. normal write).
       or is a successful exclusive write *)
      | inl None | inl (Some true) => true
      | _ => false
      end.

    Definition rresp_is_valid {n} (o : bv (8 * n) * option bool + abort) :=
      match o with
      | inl _ => true
      | _ => false
      end.

    Definition rreq_is_valid {n} (r : ReadReq.t n) :=
      match r.(ReadReq.access_kind) with
        | AK_explicit _ => true
        | _ => false
      end.

    (** Get the set of all memory reads *)
    Definition mem_reads (cd : t) :=
      collect_all
        (fun event =>
           match event with
           (* | IEvent (MemRead _ rreq) rresp => rreq_is_valid rreq && rresp_is_valid rresp *)
           | IEvent (MemRead _ _) _ => true
           | _ => false end)
        cd.

    Global Instance set_elem_of_mem_reads eid cd :
      SetUnfoldElemOf eid (mem_reads cd)
        (* (∃ n rr res, cd !! eid = Some (IEvent (MemRead n rr) res) ∧ (rreq_is_valid rr && rresp_is_valid res)). *)
        (∃ n rr res, cd !! eid = Some (IEvent (MemRead n rr) res)).
    Proof. tcclean. set_unfold. hauto l:on. Qed.
    Global Typeclasses Opaque mem_reads.

    (** Get the set of all memory writes *)
    Definition mem_writes (cd : t) :=
      collect_all
        (fun event =>
           match event with
           (* | IEvent (MemWrite _ wreq) wresp => wreq_is_valid wreq && wresp_is_valid wresp *)
           | IEvent (MemWrite _ _) _ => true
           | _ => false end)
        cd.

    Global Instance set_elem_of_mem_writes eid cd :
      SetUnfoldElemOf eid (mem_writes cd)
        (* (∃ n wr res, cd !! eid = Some (IEvent (MemWrite n wr) res) ∧ (wreq_is_valid wr && wresp_is_valid res)). *)
        (∃ n wr res, cd !! eid = Some (IEvent (MemWrite n wr) res)).
    Proof. tcclean. set_unfold. hauto l:on. Qed.
    Global Typeclasses Opaque mem_writes.

    (** Get the set of all memory writes *)
    Definition mem_events (cd : t) :=
      collect_all
        (fun event =>
           match event with
           (* | IEvent (MemRead _ rreq) rresp => rreq_is_valid rreq && rresp_is_valid rresp *)
           (* | IEvent (MemWrite _ wreq) wresp => wreq_is_valid wreq && wresp_is_valid wresp *)
           | IEvent (MemRead _ _) _ => true
           | IEvent (MemWrite _ _) _ => true
           | _ => false end)
        cd.

    (** Get the set of all barriers *)
    Definition branches (cd : t) :=
      collect_all
        (fun event =>
           match event with
           | IEvent (BranchAnnounce _ _) _ => true
           | _ => false end)
        cd.

    (** Get the set of all barriers *)
    Definition barriers (cd : t) :=
      collect_all
        (fun event =>
           match event with
           | IEvent (Barrier _) _ => true
           | _ => false end)
        cd.


    #[global] Instance access_strength_eqdec : (EqDecision Access_strength).
    Proof. intros ??. destruct x, y; try (left;done);right;done. Qed.
    #[global] Instance access_variety_eqdec : (EqDecision Access_variety).
    Proof. intros ??. destruct x, y; try (left;done);right;done. Qed.
    #[global] Instance explicit_access_kind_eqdec : (EqDecision Explicit_access_kind).
    Proof.
      intros ??. destruct x as [x1 x2], y as [y1 y2].
      unfold Decision. decide equality;decide equality.
    Qed.


    (** Get the content of a barrier, returns none if not a barrier (or is an
        invalid EID) *)
    Definition get_barrier (cd : t) (eid : EID.t) : option barrier:=
      match cd !! eid with
      | Some (IEvent (Barrier b) ()) => Some b
      | _ => None
      end.

    Definition kind_of_wreq_P{n} (req: WriteReq.t n) (P: Explicit_access_kind -> bool) :=
      match req.(WriteReq.access_kind) with
      | AK_explicit eaκ=> P eaκ
      | _ => false
      end.

    Definition kind_of_wreq{n} (req: WriteReq.t n) :=
      kind_of_wreq_P req (λ _, true).

    Definition kind_of_rreq_P {n} (req: ReadReq.t n) (P: Explicit_access_kind -> bool):=
      match req.(ReadReq.access_kind) with
      | AK_explicit eaκ=> P eaκ
      | _ => false
      end.

    Definition kind_of_rreq {n} (req: ReadReq.t n) :=
      kind_of_rreq_P req (λ _, true).

    Definition kind_of_rreq_is_atomic {n} (rreq : ReadReq.t n) :=
       kind_of_rreq_P rreq (λ eaκ, bool_decide (eaκ.(Explicit_access_kind_variety) = AV_exclusive) ||
                                 bool_decide (eaκ.(Explicit_access_kind_variety) = AV_atomic_rmw)).

    Definition kind_of_wreq_is_atomic {n} (wreq : WriteReq.t n) :=
       kind_of_wreq_P wreq (λ eaκ, bool_decide (eaκ.(Explicit_access_kind_variety) = AV_exclusive) ||
                                 bool_decide (eaκ.(Explicit_access_kind_variety) = AV_atomic_rmw)).

    Definition mem_writes_pln_zero (cd : t) : gset EID.t :=
      collect_all
        (fun event =>
           match event : iEvent with
           | IEvent (MemWrite _ wr) wresp =>
               (bool_decide (wr.(WriteReq.value) = (bv_0 _)))
               && (negb (kind_of_wreq_is_atomic wr))
               && wreq_is_valid wr
               && wresp_is_valid wresp
           | _ => false
           end)
        cd.

    Definition mem_writes_atomic (cd : t) : gset EID.t :=
      collect_all
        (fun event =>
           match event : iEvent with
           | IEvent (MemWrite _ wr) wresp =>
               kind_of_wreq_is_atomic wr && wresp_is_valid wresp
           | _ => false
           end)
        cd.

    Definition mem_reads_atomic (cd : t) : gset EID.t :=
      collect_all
        (fun event =>
           match event : iEvent with
           | IEvent (MemRead _ rr) rresp =>
               kind_of_rreq_is_atomic rr && rresp_is_valid rresp
           | _ => false
           end)
        cd.

    (** Utility relations *)
    Definition addr (cd : t) :=
      ⦗mem_reads cd⦘⨾
        (⦗mem_reads cd⦘ ∪ (iio_data cd ⨾ (rrf cd ∪ ⦗reg_writes cd⦘))⁺)⨾
        iio_addr cd⨾
        ⦗mem_events cd⦘.

    Definition data (cd : t) :=
      ⦗mem_reads cd⦘⨾
        (⦗mem_reads cd⦘ ∪ (iio_data cd ⨾ (rrf cd ∪ ⦗reg_writes cd⦘))⁺)⨾
        iio_data cd⨾
        ⦗mem_events cd⦘.

    Definition ctrl (cd : t) :=
      ⦗mem_reads cd⦘⨾
        (⦗mem_reads cd⦘ ∪ (iio_data cd ⨾ (rrf cd ∪ ⦗reg_writes cd⦘))⁺)⨾
        iio_ctrl cd⨾
        ⦗branches cd⦘⨾
        (po cd ∖ si cd).


    Definition incoming_of (r : grel EID.t) (e : EID.t) :=
      filter (fun '(_, e_tgt) => e_tgt = e) r.

    Definition outgoing_of (r : grel EID.t) (e : EID.t) :=
      filter (fun '(e_src, _) => e_src = e) r.

    Definition external_of (r: grel EID.t) :=
      filter (fun '(e_src,e_tgt) =>  e_src.(EID.tid) ≠ e_tgt.(EID.tid)) r.

    Definition internal_of (r: grel EID.t) :=
      filter (fun '(e_src,e_tgt) =>  e_src.(EID.tid) = e_tgt.(EID.tid)) r.


    (* In this version,  [P] takes an extra [EID.t] which makes this definition more useful for stating some lemmas *)
    Definition collect_all' (P : EID.t -> iEvent -> bool) (cd : t) : gset EID.t :=
      filter (fun '(eid, event) => P eid event) (event_list cd)
        |> map fst |> list_to_set.
    Global Instance set_elem_of_collect_all' eid P cd :
      SetUnfoldElemOf eid (collect_all' P cd) (∃x, cd !! eid = Some x ∧ P eid x).
    Proof. tcclean. set_unfold. hauto db:core. Qed.
    Global Typeclasses Opaque collect_all'.

    (** A folding and filtering helper that returns a gmap from some [K] to sets of EIDs *)
    Definition event_list_fold `{Countable K} (cd : t) (b : gmap K (gset EID.t)) (P : EID.t -> iEvent -> option K) :=
      fold_left (λ acc '(eid, event), (match (P eid event) with
                                       | Some k => {[ k := {[eid]}]}
                                       | None =>  ∅
                                      end) ∪ₘ acc) (event_list cd) b.

    Lemma lookup_total_unfold_event_list_fold `{Countable K} (cd : t) (P : EID.t -> iEvent -> option K) (b : gmap K (gset EID.t)) (k: K):
      (forall k, b !!! k ## collect_all' (λ _ _, true) cd) ->
      LookupTotalUnfold k (event_list_fold cd b P) (b !!! k ∪ collect_all' (λ eid event, match (P eid event) with
                                                                                     | Some k' =>  k' =? k
                                                                                     | None => false
                                                                                     end) cd).
    Proof.
      unfold event_list_fold, valid_eid, collect_all'.
      tcclean.
      revert b H0.
      pose proof (event_list_NoDup1 cd) as Hdup.
      induction (event_list cd).
      set_solver.
      assert (map fst (filter (λ '(_, _), True) l) = l.*1) as Heql.
      { clear. induction l;first done. rewrite filter_cons_True. rewrite map_cons. hauto. hauto. }

      destruct a as [eid event].
      rewrite fmap_cons in Hdup.
      specialize (IHl (NoDup_cons_1_2 _ _ Hdup)).
      apply NoDup_cons_1_1 in Hdup.
      rewrite filter_cons. simpl.
      rewrite filter_cons. simpl. case_decide as HP.
      - destruct (P eid event);[|contradiction].
        rewrite bool_unfold in HP;subst;intros;simpl.
        rewrite IHl.
        assert ( ({[k := {[eid]}]} ∪ₘ b) !!! k = {[eid]} ∪ b !!! k) as ->.
        apply lookup_total_unfold_pointwise_union; apply _.
        set_solver + H0.
        intros. destruct (decide (k = k0)).
        subst k0. assert ( ({[k := {[eid]}]} ∪ₘ b) !!! k = {[eid]} ∪ b !!! k) as ->.
        apply lookup_total_unfold_pointwise_union; apply _.
        rewrite Heql. rewrite Heql in H0. set_solver + H0 Hdup.
        assert ( ({[k := {[eid]}]} ∪ₘ b) !!! k0 = ∅ ∪ b !!! k0) as ->.
        apply lookup_total_unfold_pointwise_union; apply _.
        set_solver + H0.
      - destruct (P eid event); rewrite bool_unfold in HP;subst;intros;simpl.
        + rewrite IHl.
          assert ( (({[k0 := {[eid]}]}) ∪ₘ b) !!! k = ∅ ∪ b !!! k) as ->.
          apply lookup_total_unfold_pointwise_union; apply _.
          set_solver + H0.
          intros.
          destruct (decide (k0 = k1)).
          * assert ( (({[k0 := {[eid]}]}) ∪ₘ b) !!! k1 = {[eid]} ∪ b !!! k1) as ->.
            apply lookup_total_unfold_pointwise_union.
            rewrite e. apply _. apply _.
            rewrite Heql. rewrite Heql in H0. set_solver + H0 Hdup.
          * assert ( (({[k0 := {[eid]}]}) ∪ₘ b) !!! k1 = ∅ ∪ b !!! k1) as ->.
            apply lookup_total_unfold_pointwise_union.
            apply _. apply _.
            set_solver + H0.
        + rewrite IHl.
          assert ( (∅ ∪ₘ b) !!! k = ∅ ∪ b !!! k) as ->.
          apply lookup_total_unfold_pointwise_union; apply _.
          set_solver +.
          intros. assert ( (∅ ∪ₘ b) !!! k0 = ∅ ∪ b !!! k0) as ->.
          apply lookup_total_unfold_pointwise_union; apply _.
          set_solver + H0.
    Qed.

    Lemma event_list_fold_is_Some `{Countable K} (cd : t) (P : EID.t -> iEvent -> option K) (k: K) b:
      (is_Some (b !! k) ∨ ∃ eid event, (eid, event) ∈ event_list cd ∧ P eid event = Some k) ->
       is_Some((event_list_fold cd b P) !! k).
    Proof.
      unfold event_list_fold. revert b.
      induction (event_list cd) ;intros ; first set_solver.
      simpl. destruct a as [eid event]. destruct H0.
      apply IHl. destruct H0. left. case_match. destruct (decide (k = k0)).
      subst k0. exists ({[eid]} ∪ x). assert (Some {[eid]} ∪ₒ Some x = Some ({[eid]} ∪ x)) as <-. done.
      apply lookup_unfold_pointwise_union. tcclean. rewrite lookup_singleton_Some;hauto. done.
     + exists x. assert (None ∪ₒ Some x = Some x) as <-. done.
       apply lookup_unfold_pointwise_union. tcclean. rewrite lookup_singleton_None;hauto. done.
     + exists x. assert (None ∪ₒ Some x = Some x) as <-. done.
       apply lookup_unfold_pointwise_union. tcclean. rewrite lookup_empty;hauto. done.
     + destruct H0 as (?&?&?&?).
       rewrite elem_of_cons in H0.
       destruct H0 as [H0 | Hin]. inversion H0;subst.
       * rewrite H1. apply IHl. left.
         destruct (b !! k) eqn:Hb.
         exists ({[eid]} ∪ g). assert (Some {[eid]} ∪ₒ Some g = Some ({[eid]} ∪ g)) as <-. done.
         apply lookup_unfold_pointwise_union. tcclean. rewrite lookup_singleton_Some;hauto. done.
         exists {[eid]}. assert (Some {[eid]} ∪ₒ None = Some {[eid]}) as <-. done.
         apply lookup_unfold_pointwise_union. tcclean. rewrite lookup_singleton_Some;hauto. done.
       * apply IHl. right. do 2 eexists. naive_solver.
    Qed.

    Definition get_pa (e : iEvent) : option (Arch.pa):=
      match e with
      | IEvent (MemRead _ rr) _ => Some (rr.(ReadReq.pa))
      | IEvent (MemWrite n rr) _ => Some (rr.(WriteReq.pa))
      | _ => None
      end.

    (** Symmetry relation referring to events having the same address.
        Might need to be updated for mixed-size *)
    Definition loc (cd : t) : grel EID.t :=
      let pa_map : gmap pa (gset EID.t) :=
        event_list_fold cd ∅ (λ _ event, get_pa event)in
      map_fold (fun (k : pa) (s : gset EID.t) (r : grel EID.t) => r ∪ (s × s))
        ∅ pa_map.

    #[export] Instance set_elem_of_map_fold_set_union `{Countable K, Countable K'} {V} (m : gmap K V) b e (f : K -> V -> gset K') :
      SetUnfoldElemOf (e) (map_fold (fun (k: K) (v : V) (r : gset K') => r ∪ (f k v)) b m)
        (e ∈ b ∨ ∃ k v, m !! k = Some v ∧ e ∈ (f k v)).
    Proof.
      tcclean. cinduction m using map_fold_cind.
      hauto lq:on use:lookup_empty_Some.
      set_unfold. setoid_rewrite H2; clear H2.
      split.
      - intros [[| (?&?&?&?)]|];first hauto lq:on;
          (destruct (decide (e ∈ b));[hauto lq:on | right; do 2 eexists; rewrite lookup_insert_Some; sauto lq:on]).
      - intros [|(?&?&Hlk&?)];first hauto lq:on;
          rewrite lookup_insert_Some in Hlk; hauto lq:on.
    Qed.

    Global Instance set_elem_of_loc eid1 eid2 cd :
      SetUnfoldElemOf (eid1, eid2) (loc cd)
        (∃ E1 E2 l, cd !! eid1 = Some E1 ∧ get_pa E1 = Some l ∧
                  cd !! eid2 = Some E2 ∧ get_pa E2 = Some l).
    Proof.
      tcclean. unfold loc. set_unfold.
      split.
      - intros [|(?&?&Hfold&?)];first done.
        pose proof (lookup_total_unfold_event_list_fold cd (λ _ event, get_pa event) ∅ x).
        ospecialize* H0.
        intros. rewrite lookup_total_empty.
        set_solver +.
        rewrite lookup_total_empty, union_empty_l_L in H0.
        tcclean_hyp H0.
        rewrite lookup_total_alt in H0.
        rewrite Hfold in H0. simpl in H0.
        set_unfold.
        pose proof (H0 eid1) as [(E1 & Hlk1 & Heq1) _];first set_solver.
        pose proof (H0 eid2) as [(E2 & Hlk2 & Heq2) _];first set_solver.
        case_match;last done. case_match;last done;simplify_map_eq /=.
        repeat rewrite bool_unfold in *.
        hauto lq:on.
      - intros (?&?&?&?&Hloc1&?&Hloc2);right.
        exists x1. eexists.
        split.
        + pose proof (lookup_total_unfold_event_list_fold cd (λ _ event, get_pa event) ∅ x1).
          ospecialize* H1.
          intros. rewrite lookup_total_empty.
          set_solver +.
          rewrite lookup_total_empty, union_empty_l_L in H1.
          tcclean_hyp H1.
          rewrite lookup_total_alt in H1.
          pose proof (event_list_fold_is_Some cd (λ _ event, get_pa event) x1 ∅) as [? HSome].
          right. do 2 eexists. rewrite event_list_match in H. hauto.
          hauto.
        + set_unfold.
          split;eexists;(split;first eassumption;hauto).
    Qed.
    Global Typeclasses Opaque loc.

    (* same thread, excluding thread 0 (initial writes) *)
    Definition sthd (cd : t) : grel EID.t :=
      let tid_map : gmap nat (gset EID.t) :=
        event_list_fold cd ∅ (λ eid _, Some (eid.(EID.tid))) in
      map_fold (fun _ (s : gset EID.t) (r : grel EID.t) => r ∪ (s × s))
        ∅ tid_map.

    Global Instance set_elem_of_sthd eid1 eid2 cd :
      SetUnfoldElemOf (eid1, eid2) (sthd cd)
        (∃ E1 E2 tid, cd !! eid1 = Some E1 ∧ eid1.(EID.tid) = tid ∧
                  cd !! eid2 = Some E2 ∧ eid2.(EID.tid) = tid).
    Proof.
      tcclean. unfold sthd. set_unfold.
      split.
      - intros [|(?&?&Hfold&?)];first done.
        pose proof (lookup_total_unfold_event_list_fold cd (λ eid _, Some (eid.(EID.tid))) ∅ x).
        ospecialize* H0.
        intros. rewrite lookup_total_empty.
        set_solver +.
        rewrite lookup_total_empty, union_empty_l_L in H0.
        tcclean_hyp H0.
        rewrite lookup_total_alt in H0.
        rewrite Hfold in H0. simpl in H0.
        set_unfold.
        pose proof (H0 eid1) as [(E1 & Hlk1 & Heq1) _];first set_solver.
        pose proof (H0 eid2) as [(E2 & Hlk2 & Heq2) _];first set_solver.
        repeat rewrite bool_unfold in *.
        hauto lq:on.
      - intros (?&?&?&Hlk1&?&Hlk2&?);right.
        exists x1. eexists.
        split.
        + pose proof (lookup_total_unfold_event_list_fold cd (λ eid _, Some (eid.(EID.tid))) ∅ x1).
          ospecialize* H1.
          intros. rewrite lookup_total_empty.
          set_solver +.
          rewrite lookup_total_empty, union_empty_l_L in H1.
          tcclean_hyp H1.
          rewrite lookup_total_alt in H1.
          pose proof (event_list_fold_is_Some cd (λ eid _, Some (eid.(EID.tid))) x1 ∅) as [? HSome].
          right. do 2 eexists. rewrite event_list_match in Hlk1. hauto.
          hauto.
        + set_unfold.
          split;eexists;(split;first eassumption;hauto).
    Qed.
    Global Typeclasses Opaque sthd.

    Definition fr (cd : t) : grel EID.t :=
      (rf cd)⁻¹⨾ (co cd).

    (* including initials *)
    Definition num_of_thd (cd : t) :=
      length (events cd).

    Lemma num_of_thd_spec gr eid:
      eid ∈ valid_eid gr ->
      ((EID.tid eid) < num_of_thd gr)%nat.
    Proof.
      intros.
      set_unfold.
      destruct H as [? [? _]].
      rewrite event_list_match in H.
      unfold event_list in H.
      destruct eid.
      set_unfold.
      repeat setoid_rewrite exists_pair in H.
      destruct H as  (?&?&(?&?&?&((?&?&?&?)&?))&?).
      destruct H;last contradiction.
      simpl in H. inversion H. subst.
      simpl in H2.
      apply list_lookup_alt in H2.
      destruct H2;done.
    Qed.

    Definition non_initial_eids (gr : Candidate.t) :=
      Candidate.collect_all' (λ eid _, bool_decide (eid.(EID.tid) ≠ 0))%nat gr.

    (* the union of events in non-zero threads is equal to the set all of non-initial events,
   given the well-formedness which assumes thread 0 contains and only contains initial writes of all locations *)
    Lemma non_initial_eids_fold' {gr : Candidate.t} (k b n : nat) x:
      (b <= n)%nat ->
      x = Candidate.collect_all' (λ eid _, bool_decide (eid.(EID.tid) ∈ (seq k b)))%nat gr ->
      foldl (λ (s : gset _) (idx : nat),
               filter (λ eid, eid.(EID.tid) = idx) (Candidate.valid_eid gr) ∪ s) x (seq (b+k) (n-b))
      = Candidate.collect_all' (λ eid _, bool_decide (eid.(EID.tid) ∈ (seq k n)))%nat gr.
    Proof.
      unfold collect_all'.
      revert b x.
      induction n.
      - simpl.
        intros.
        destruct b.
        simpl in H0. done.
        lia.
      - intros.
        simpl.
        rewrite Nat.le_lteq in H.
        destruct H.
        + assert (S n - b = S (n - b))%nat as ->. lia.
          rewrite seq_end. rewrite foldl_snoc.
          rewrite IHn.
          2:lia.  2: done.
          set_unfold.
          intros.
          assert (b + k + (n - b)= k + n)%nat as ->. lia.
          clear IHn H0.
          assert (k%nat :: seq (S k) n = seq k n ++ [(k+n)%nat])%list as ->.
          rewrite <-seq_end. simpl. done.
          split.
          intros [[? [? ?]]| (?&?&?&?)].
          exists (x0,x1).  rewrite bool_unfold. sauto use:elem_of_app.
          exists x1. destruct x1. rewrite bool_unfold in H1. rewrite bool_unfold. sauto use:elem_of_app.
          intros (?&?&?&?). destruct x1.
          rewrite bool_unfold in H1. apply elem_of_app in H1.
          destruct H1.
          right. exists (t0,i). rewrite bool_unfold.  sauto.
          left. sauto.
        + subst b.
          assert (S n - S n = 0)%nat as ->. lia.
          simpl.
          rewrite H0.
          done.
    Qed.

    Lemma non_initial_eids_fold_aux (gr : Candidate.t) (n : nat):
      foldl (λ (s : gset _) (idx : nat),
               filter (λ eid, eid.(EID.tid) = idx) (Candidate.valid_eid gr) ∪ s) ∅ (seq (0+1) (n-0))
      = Candidate.collect_all' (λ eid _, bool_decide (eid.(EID.tid) ∈ (seq 1 n)))%nat gr.
    Proof.
      eapply non_initial_eids_fold'.
      lia.
      simpl. unfold collect_all'. set_unfold. sauto.
    Qed.

    Lemma non_initial_eids_fold {gr : Candidate.t} (n : nat):
      S n = num_of_thd gr ->
      foldl (λ (s : gset _) (idx : nat),
               filter (λ eid, eid.(EID.tid) = S idx) (Candidate.valid_eid gr) ∪ s) ∅ (seq 0 n)
      = non_initial_eids gr.
    Proof.
      pose proof (non_initial_eids_fold_aux gr n).
      assert (S <$> (seq 0 n) = seq (0+1) (n-0)) as Heq.
      {
        rewrite fmap_S_seq. assert (0 + 1 =1)%nat as -> by lia.
        assert (n - 0 = n)%nat as -> by lia. done.
      }
      rewrite <-Heq in H.

      rewrite foldl_fmap in H.
      rewrite H.
      unfold non_initial_eids.
      unfold collect_all'.
      set_unfold.
      intros Hsz.
      intros.
      split.
      intros (?&?&?&?).
      eexists x0.
      destruct x0. rewrite bool_unfold in H1.
      rewrite bool_unfold. set_unfold.
      rewrite elem_of_seq in H1.
      assert (EID.tid t0 ≠ 0%nat) by lia.
      sauto.
      intros (?&?&?&?).
      eexists x0.
      destruct x0. rewrite bool_unfold in H1.
      rewrite bool_unfold. set_unfold.
      split;first done.
      split;last done.
      rewrite elem_of_seq.
      pose proof (num_of_thd_spec gr t0).
      ospecialize* H3.
      set_unfold. hauto.
      rewrite <- Hsz in H3.
      lia.
    Qed.

    Global Instance set_unfold_non_initial_eids e gr:
      SetUnfoldElemOf (e) (non_initial_eids gr) (e ∈ valid_eid gr ∧ (EID.tid e) ≠ 0%nat).
    Proof. tcclean. unfold non_initial_eids.
           set_unfold. hauto. Qed.

    (* tid of any non-initial event is greater than 0, and smaller than the number of normal threads plus thread 0 *)
    Lemma non_initial_tid_inv gr e:
      e ∈ non_initial_eids gr ->
      (0 < e.(EID.tid) ∧ e.(EID.tid) < Candidate.num_of_thd gr)%nat.
    Proof.
      intros. set_unfold. destruct H.
      apply num_of_thd_spec in H.
      lia.
    Qed.

    (* tid 0 is reserved for initial writes *)
    Definition initials (cd : t) : gset EID.t :=
      collect_all'  (fun e _=> e.(EID.tid) =? 0%nat) cd.

    Global Instance set_unfold_initial_eids e gr:
      SetUnfoldElemOf (e) (initials gr) (e ∈ valid_eid gr ∧ (EID.tid e) = 0%nat).
    Proof. tcclean. unfold initials.
           set_unfold.
           split;intros [? ?].
           rewrite bool_unfold in H. hauto.
           destruct H. eexists. rewrite bool_unfold. hauto.
    Qed.

    Lemma valid_eid_disjoint_union gr :
      initials gr ∪ non_initial_eids gr = valid_eid gr
      ∧ initials gr ## non_initial_eids gr.
    Proof.
      unfold initials. unfold non_initial_eids.
      split.
      apply set_eq. intros. repeat rewrite elem_of_filter.
      set_unfold. set_unfold.
      split. intros [?|?];hauto.
      intros. destruct (decide (EID.tid x = 0%nat));hauto.
      set_unfold.
      intros. hauto.
    Qed.

    Global Opaque non_initial_eids.
    Global Opaque initials.

  End Candidate.

  (** Non-mixed size well-formedness *)
  Module NMSWF.
    Import Candidate.

    (** This is only correct for 8 bytes values*)
    Definition get_val (event : iEvent) :=
      match event : iEvent with
      | IEvent (MemRead 8 rr) (inl (val, _)) =>
          Some val
      | IEvent (MemWrite 8 rr) _ =>
          Some (rr.(WriteReq.value))
      | _ => None
      end.

    (** This relation only make sense for 8-bytes non-mixed-size models.
        It relates events with the same values *)
    Definition val (cd : t) : grel EID.t :=
      let val_map : gmap (bv 64) (gset EID.t) :=
        event_list_fold cd ∅ (λ _ event, get_val event) in
      map_fold
        (fun (_ : bv 64) (s : gset EID.t) (r : grel EID.t) => r ∪ (s × s))
        ∅ val_map.

    Global Instance set_elem_of_val eid1 eid2 cd :
      SetUnfoldElemOf (eid1, eid2) (val cd)
        (∃ E1 E2 val, cd !! eid1 = Some E1 ∧ get_val E1 = Some val ∧
                      cd !! eid2 = Some E2 ∧ get_val E2 = Some val).
    Proof.
      tcclean. unfold val. set_unfold.
      split.
      - intros [|(?&?&Hfold&?)];first done.
        pose proof (lookup_total_unfold_event_list_fold cd (λ _ event, get_val event) ∅ x).
        ospecialize* H0.
        intros. rewrite lookup_total_empty.
        set_solver +.
        rewrite lookup_total_empty, union_empty_l_L in H0.
        tcclean_hyp H0.
        rewrite lookup_total_alt in H0.
        rewrite Hfold in H0. simpl in H0.
        set_unfold.
        pose proof (H0 eid1) as [(E1 & Hlk1 & Heq1) _];first set_solver.
        pose proof (H0 eid2) as [(E2 & Hlk2 & Heq2) _];first set_solver.
        case_match;last done. case_match;last done;simplify_map_eq /=.
        repeat rewrite bool_unfold in *.
        hauto lq:on.
      - intros (?&?&?&Hlk1&?&Hlk2&?);right.
        exists x1. eexists.
        split.
        + pose proof (lookup_total_unfold_event_list_fold cd (λ _ event, get_val event) ∅ x1).
          ospecialize* H1.
          intros. rewrite lookup_total_empty.
          set_solver +.
          rewrite lookup_total_empty, union_empty_l_L in H1.
          tcclean_hyp H1.
          rewrite lookup_total_alt in H1.
          pose proof (event_list_fold_is_Some cd (λ _ event, get_val event) x1 ∅) as [? HSome].
          right. do 2 eexists. rewrite event_list_match in Hlk1. hauto.
          hauto.
        + set_unfold.
          split;eexists;(split;first eassumption;hauto).
    Qed.
    Global Typeclasses Opaque val.

    (** Check that all memory accesses have size 8. Alignment checking need to
        know how pa work and thus need to be architecture specific*)
    Definition size8_wf (cd : t) : bool :=
      collect_all
        (fun event =>
           match event with
           | IEvent (MemRead 8 _) _ => false
           | IEvent (MemRead _ _) _ => true
           | IEvent (MemWrite 8 _) _ => false
           | IEvent (MemWrite _ _) _ => true
           | _ => false
           end) cd =? ∅.

    Definition co_wf (cd : t) : bool :=
      let co := co cd in
      let loc := loc cd in
      let writes := mem_writes cd in
      grel_irreflexive co &&
        grel_transitive co &&
        bool_decide (co ⊆ loc) &&
        bool_decide (grel_dom co ⊆ writes) &&
        bool_decide (grel_rng co ⊆ writes) &&
        (loc ∩ (writes × writes) =? co ∪ co⁻¹ ∪ ⦗writes⦘)
      (* initials are the minimum elements *)
      && bool_decide(co⨾⦗initials cd⦘= ∅).

    Definition rf_wf (cd : t) : bool :=
      let rf := rf cd in
      let loc := loc cd in
      let val := val cd in
      let reads := mem_reads cd in
      let writes := mem_writes cd in
      bool_decide (grel_dom rf ⊆ writes) &&
        bool_decide (grel_rng rf = reads) &&
        grel_functional (rf⁻¹) &&
        bool_decide (rf ⊆ loc ∩ val).
    (* NOTE: It is only complete for user Arm *)

    Definition po_wf (cd : t) : bool :=
      let po := po cd in
      let init := initials cd in
      let lt := (λ '(e, e'), ((EID.iid e)= (EID.iid e') ∧ (EID.num e) < (EID.num e'))
                                             ∨ ((EID.iid e)< (EID.iid e')))%nat in
      grel_irreflexive po &&
        grel_transitive po &&
        (* only between nodes of same threads, but not between initial writes even if they reside in thread 0 *)
        bool_decide (po ∪ po⁻¹ ∪ (init × init) = (sthd cd)) &&
        bool_decide (po ∩ (init × init) = ∅) &&
        bool_decide (set_Forall lt po) &&
        bool_decide (set_Forall (λ (r : EID.t * EID.t), ((lt r) ∧ r ∉ (init × init)) -> r ∈ po) (sthd cd))
    .

    Definition addr_wf (cd : t) : bool :=
      let addr := addr cd in
      let po := po cd in
      let reads := mem_reads cd in
      let mem := mem_events cd in
      bool_decide (grel_dom addr ⊆ reads) &&
        bool_decide (grel_rng addr ⊆ mem) &&
        bool_decide (addr ⊆ po).

    Definition data_wf (cd : t) : bool :=
      let data := data cd in
      let po := po cd in
      let reads := mem_reads cd in
      let writes := mem_writes cd in
      bool_decide (grel_dom data ⊆ reads) &&
        bool_decide (grel_rng data ⊆ writes) &&
        bool_decide (data ⊆ po).

    Definition ctrl_wf (cd : t) : bool :=
      let ctrl := ctrl cd in
      let po := po cd in
      let reads := mem_reads cd in
      bool_decide (grel_dom ctrl ⊆ reads) &&
        bool_decide (ctrl ⊆ po) &&
        bool_decide (ctrl⨾po ⊆ ctrl).

    Definition rmw_wf (cd : t) :  bool :=
      let rmw := rmw cd in
      let loc := loc cd in
      let po := po cd in
      let writes := mem_writes_atomic cd in
      let reads := mem_reads_atomic cd in
      grel_functional rmw &&
        grel_functional (rmw⁻¹) &&
        bool_decide (rmw ⊆ loc) &&
        bool_decide (rmw ⊆ po) &&
        bool_decide (grel_dom rmw ⊆ reads) &&
        bool_decide (grel_rng rmw ⊆ writes) &&
        bool_decide (rmw ∩ (⦗reads⦘⨾po ⨾⦗writes⦘⨾ po ⨾⦗writes⦘)  =? ∅) &&
        bool_decide (rmw ∩ (⦗reads⦘⨾po ⨾⦗reads⦘⨾ po ⨾⦗writes⦘)  =? ∅).

    Definition initial_writes (cd : t) :=
      filter (λ e, ¬ ∃ e', e' ∈ (mem_writes cd) ∧ (e', e) ∈ (co cd) ) (mem_writes cd).

    Definition initial_wf (cd : t) : bool :=
      let pa_set :=
        fold_left
          (fun pa_set '(eid, event) =>
             if (bool_decide (eid.(EID.tid) = 0%nat)) && (bool_decide (eid.(EID.num) = 0%nat)) then
               pa_set
             else
               match event : iEvent with
               | IEvent (MemRead _ rr) _ => {[rr.(ReadReq.pa)]} ∪ pa_set
               | IEvent (MemWrite n rr) _ => {[rr.(WriteReq.pa)]} ∪ pa_set
               | _ => pa_set
               end) (event_list cd) (∅:gset pa) in
      let pa_init_set :=
        fold_left
          (fun pa_init_set '(eid, event) =>
             if (bool_decide (eid.(EID.tid) = 0%nat)) && (bool_decide (eid.(EID.num) = 0%nat)) then
               match event : iEvent with
               | IEvent (MemWrite n rr) _ => {[rr.(WriteReq.pa)]} ∪ pa_init_set
               | _ => pa_init_set
               end
             else pa_init_set) (event_list cd) (∅:gset pa) in
      (* number of locations = number of initial nodes, i.e. one node per location *)
      (* and they are all the only event in a trace *)
      bool_decide ((size pa_init_set) = size (initials cd))
      (* initial nodes are all write 0 *)
      && bool_decide ((initials cd) ⊆ (mem_writes_pln_zero cd))
      (* locations appear in the program = locations for with an initial write exists *)
      && bool_decide (pa_set = pa_init_set)
      && bool_decide ((initials cd) = (initial_writes cd))
      && bool_decide (set_Forall (λ e, e.(EID.num) = 0%nat) (initials cd))
    .

    (* Check if all memory events have explicit access strength, variaty, and their responds are valid *)
    Definition mem_wf (cd : t) : bool :=
      collect_all
        (fun event =>
           match event with
           | IEvent (MemRead _ rreq) rresp => negb (rreq_is_valid rreq && rresp_is_valid rresp)
           | IEvent (MemWrite _ wreq) wresp => negb (wreq_is_valid wreq && wresp_is_valid wresp)
           | _ => false
           end) cd =? ∅.

    (* Check that a candidate is self consistent *)
    Definition wf (cd : t) : bool :=
      size8_wf cd && rf_wf cd && co_wf cd && po_wf cd && addr_wf cd && data_wf cd && ctrl_wf cd && rmw_wf cd && initial_wf cd && mem_wf cd.

  End NMSWF.

End CandidateExecutions.
