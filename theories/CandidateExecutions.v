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

(* Simplified version of [CandidateExecutions.v] of [system-semantics-coq]. *)

(** This file provide a common type for representing candidate executions
    for all memory models to use *)

Require Import Ensembles.

Require Import Strings.String.

From stdpp Require Export listset.
From stdpp Require Export gmap.

(* Require Import SSCCommon.Options. *)
Require Import SSCCommon.Common.
Require Import SSCCommon.Exec.
Require Import SSCCommon.GRel.

Require Import ISASem.Interface.


Open Scope Z_scope.
Open Scope stdpp_scope.

Module CandidateExecutions (IWA : InterfaceWithArch). (* to be imported *)
  Import IWA.Arch.
  Import IWA.Interface.
  Notation outcome := (outcome ()).
  Notation iMon := (iMon ()).
  Notation iSem := (iSem ()).
  Notation iEvent := (iEvent).
  Notation iTrace := (iTrace ()).

  (* event ID *)
  Module EID.
    Record t :=
      make {
          (* thread ID *)
          tid : nat;
          (* Instruction ID *)
          iid : nat;
          (* event number *)
          ieid : nat
        }.

    #[global] Instance eta : Settable _ :=
      settable! make <tid; iid; ieid>.

    #[global] Instance eq_dec : EqDecision t.
    Proof. solve_decision. Defined.

    #[global] Instance countable : Countable t.
    Proof.
      eapply (inj_countable' (fun eid => (tid eid, iid eid, ieid eid))
                (fun x => make x.1.1 x.1.2 x.2)).
      sauto.
    Qed.
  End EID.



  Module Candidate.

    Record t :=
      make {
          (** Each thread is a list of instruction, which each have a trace.
              We force the return type to be unit, but it just means we
              forget the actual value. *)
          events : list (list (iTrace));
          (** Program order. The per-thread order of all events in the trace
             po can be deduced by the order of events in the trace *)
          po : grel EID.t;
          (** Memory read-from *)
          rf : grel EID.t;
          (** Memory coherence: for each pa, list of writes in order *)
          co : grel EID.t;
          (** Load-reserve/store conditional pair (exclusives in Arm speak) *)
          lxsx : grel EID.t;
          addr : grel EID.t;
          data : grel EID.t;
          ctrl : grel EID.t;
        }.

    (** NOTE: we assume initial writes are in the traces of thread 0, one trace contains only one such write*)

    (** Get an event at a given event ID in a candidate *)
    #[global] Instance lookup_eid : Lookup EID.t iEvent t :=
      fun eid cd =>
        traces ← cd.(events) !! eid.(EID.tid);
        '(trace, result) ← traces !! eid.(EID.iid);
        trace !! eid.(EID.ieid).

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

    #[global] Typeclasses Opaque event_list.

    Import SetUnfoldPair.

    (** Gives the list of valid EIDs for a event at a specific position in a
        candidate *)
    Definition EID_list_from_iEvent (tid iid ieid : nat)
      (event : iEvent) : list EID.t :=
      [EID.make tid iid ieid].

    Definition lookup_instruction pe (tid iid : nat) :
      option iTrace :=
      traces ← pe.(events) !! tid;
    traces !! iid.

    Definition lookup_iEvent pe (tid iid ieid : nat) :
      option iEvent :=
      '(trace, result) ← lookup_instruction pe tid iid;
    trace !! ieid.


    Definition instruction_list pe : list (nat * nat * iTrace) :=
      '(tid, traces) ← enumerate pe.(events);
    '(iid, trace) ← enumerate traces;
    [(tid, iid, (trace : iTrace))].


    (** Allow [set_unfold] to unfold through [match] constructs *)
    #[local] Existing Instance set_unfold_match.

    Lemma instruction_list_match pe tid iid ev :
      lookup_instruction pe tid iid = Some ev ↔
      (tid, iid, ev) ∈ instruction_list pe.
    Proof using.
      destruct ev.
      unfold lookup_instruction.
      unfold instruction_list.
      set_unfold.
      (* setoid_rewrite lookup_unfold. *)
      setoid_rewrite eq_some_unfold.
      repeat setoid_rewrite exists_pair.
      naive_solver.
    Qed.
    #[global] Typeclasses Opaque lookup_instruction.
    Opaque lookup_instruction.
    #[global] Typeclasses Opaque instruction_list.



    Definition iEvent_list pe : list (nat * nat * nat * iEvent) :=
      '(tid, iid, (trace, trace_end)) ← instruction_list pe;
    '(ieid, event) ← enumerate trace;
    mret (tid, iid, ieid, event).

    Lemma iEvent_list_match cd tid iid ieid ev :
      lookup_iEvent cd tid iid ieid = Some ev ↔
      (tid, iid, ieid, ev) ∈ iEvent_list cd.
    Proof using.
      unfold lookup_iEvent.
      unfold iEvent_list.
      set_unfold.
      setoid_rewrite eq_some_unfold.
      setoid_rewrite instruction_list_match.
      repeat setoid_rewrite exists_pair.
      set_solver.
    Qed.
    #[global] Typeclasses Opaque lookup_iEvent.
    Opaque lookup_iEvent.
    #[global] Typeclasses Opaque iEvent_list.

    Lemma event_list_match cd eid ev :
      cd !! eid = Some ev ↔ (eid, ev) ∈ event_list cd.
    Proof using.
      unfold lookup at 1.
      unfold lookup_eid.
      unfold event_list.
      unfold EID_list_from_iEvent.
      destruct eid.
      set_unfold.
      setoid_rewrite eq_some_unfold.
      (* setoid_rewrite iEvent_list_match. *)
      repeat setoid_rewrite exists_pair.
      naive_solver.
    Qed.

    #[global] Instance set_unfold_elem_of_event_list cd x :
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


Import SSCCommon.CBase.FunctionPipeNotations.

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

    #[global] Instance lookup_unfold_event_map x cd R :
      LookupUnfold x cd R → LookupUnfold x (event_map cd) R.
    Proof. tcclean. apply event_map_match. Qed.

    (** * Accessors ***)

    Definition collect_all (P : EID.t -> iEvent -> Prop)
      `{∀ eid event, Decision (P eid event)}
      pe : gset EID.t :=
      filter (fun '(eid, event) => P eid event) (event_list pe)
        |> map fst |> list_to_set.
    #[global] Instance set_elem_of_collect_all eid P
      `{∀ eid event, Decision (P eid event)} pe :
      SetUnfoldElemOf eid (collect_all P pe) (∃x, pe !! eid = Some x ∧ P eid x).
    Proof using. tcclean. unfold collect_all. set_unfold. hauto db:pair. Qed.
    #[global] Typeclasses Opaque collect_all.

    #[global] Instance set_unfold_elem_of_filter `{FinSet A B}
      `{∀ x : A, Decision (P x)} x (a : B) Q:
      SetUnfoldElemOf x a Q ->
      SetUnfoldElemOf x (filter P a) (P x ∧ Q).
    Proof. tcclean. apply elem_of_filter. Qed.

    #[global] Instance set_unfold_elem_of_filter_list A
      `{∀ x : A, Decision (P x)} x (a : list A) Q:
      SetUnfoldElemOf x a Q ->
      SetUnfoldElemOf x (filter P a) (P x ∧ Q).
    Proof. tcclean. apply elem_of_list_filter. Qed.

    (* Global Instance set_elem_of_collect_all eid P cd : *)
    (*   SetUnfoldElemOf eid (collect_all P cd) (∃x, cd !! eid = Some x ∧ P x). *)
    (* Proof. tcclean. set_unfold. *)
    (*        split. *)
    (*        hauto db:core. *)
    (*        intros. *)
    (*        destruct H. *)
    (*        exists (eid, x). *)
    (*        hauto db:core. Qed. *)
    (* Global Typeclasses Opaque collect_all. *)

    (** Get the set of all valid EID for that candidate *)
    Definition valid_eid (cd : t) :=
      collect_all (fun _ _ => True) cd.


    (** Get the set of all register reads *)
    Definition reg_reads := collect_all (λ _, is_reg_read).

    (** Get the set of all register writes *)
    Definition reg_writes := collect_all (λ _, is_reg_write).

    (** Get the set of all memory reads *)
    Definition mem_reads_req := collect_all (λ _ , is_mem_read_req).
    Definition mem_reads := collect_all (λ _ , is_mem_read).

    (** Get the set of all memory writes *)

    Definition mem_writes_req := collect_all (λ _ , is_mem_write_req).
    Definition mem_writes := collect_all (λ _ , is_mem_write).

    (** Get the set of all memory writes *)
    Definition mem_events_req := collect_all (λ _, is_mem_event_req).
    Definition mem_events cd := mem_reads cd ∪ mem_writes cd.
    #[global] Typeclasses Opaque mem_events_req.

    Lemma mem_events_union pe : mem_events_req pe = mem_reads_req pe ∪ mem_writes_req pe.
    Proof. unfold mem_events_req, mem_reads_req, mem_writes_req, is_mem_event_req. set_solver. Qed.

    (** Get the set of all barriers *)
    Definition barriers pe :=
      collect_all (λ _ event, is_Some (get_barrier event)) pe.
    #[global] Typeclasses Opaque barriers.

    (* WARNING: intense boilerplate *)
    Section ByKind.
      Context (P : accessKind → Prop).
      Context {Pdec : ∀ acc, Decision (P acc)}.
      Definition mem_by_kind := collect_all (λ _, is_mem_event_kindP P).
      #[global] Typeclasses Opaque mem_by_kind.
      Definition reads_by_kind := collect_all (λ _, is_mem_read_kindP P).
      #[global] Typeclasses Opaque reads_by_kind.
      Definition writes_by_kind := collect_all (λ _, is_mem_write_kindP P).
      #[global] Typeclasses Opaque writes_by_kind.
    End ByKind.
    Definition mem_explicit := (mem_by_kind is_explicit).
    Definition explicit_reads := (reads_by_kind is_explicit).
    Definition explicit_writes := (writes_by_kind is_explicit).
    Definition mem_ifetch := (mem_by_kind is_ifetch).
    Definition ifetch_reads := (reads_by_kind is_ifetch).
    Definition ifetch_writes := (writes_by_kind is_ifetch). (* empty *)
    Definition mem_ttw := (mem_by_kind is_ttw).
    Definition ttw_reads := (reads_by_kind is_ttw).
    Definition ttw_writes := (writes_by_kind is_ttw).
    Definition mem_relaxed := (mem_by_kind is_relaxed).
    Definition relaxed_reads := (reads_by_kind is_relaxed).
    Definition relaxed_writes := (writes_by_kind is_relaxed).
    Definition mem_rel_acq := (mem_by_kind is_rel_acq).
    Definition rel_acq_reads := (reads_by_kind is_rel_acq).
    Definition rel_acq_writes := (writes_by_kind is_rel_acq).
    Definition mem_acq_rcpc := (mem_by_kind is_acq_rcpc).
    Definition acq_rcpc_reads := (reads_by_kind is_acq_rcpc).
    Definition acq_rcpc_writes := (writes_by_kind is_acq_rcpc).
    Definition mem_standalone := (mem_by_kind is_standalone).
    Definition standalone_reads := (reads_by_kind is_standalone).
    Definition standalone_writes := (writes_by_kind is_standalone).
    Definition mem_exclusive := (mem_by_kind is_exclusive).
    Definition exclusive_reads := (reads_by_kind is_exclusive).
    Definition exclusive_writes := (writes_by_kind is_exclusive).
    Definition mem_atomic_rmw := (mem_by_kind is_atomic_rmw).
    Definition atomic_rmw_reads := (reads_by_kind is_atomic_rmw).
    Definition atomic_rmw_writes := (writes_by_kind is_atomic_rmw).

    Definition is_valid_init_mem_write (cd : t) (eid : EID.t) :=
      (is_Some $
        write ← cd !! eid;
        val ← get_mem_value write;
        guard' (val = (bv_0 (val.(bvn_n)))))
      ∧
      eid ∈ mem_standalone cd ∩ mem_relaxed cd
    .

    Definition mem_writes_atomic (cd : t) : gset EID.t :=
      collect_all (λ _, is_mem_write) cd ∩ mem_exclusive cd.

    Definition mem_reads_atomic (cd : t) : gset EID.t :=
      collect_all (λ _, is_mem_read) cd ∩ mem_exclusive cd.

    (** Utility relations *)

    Definition incoming_of (r : grel EID.t) (e : EID.t) :=
      filter (fun '(_, e_tgt) => e_tgt = e) r.

    Definition outgoing_of (r : grel EID.t) (e : EID.t) :=
      filter (fun '(e_src, _) => e_src = e) r.

    Definition external_of (r: grel EID.t) :=
      filter (fun '(e_src,e_tgt) =>  e_src.(EID.tid) ≠ e_tgt.(EID.tid)) r.

    Definition internal_of (r: grel EID.t) :=
      filter (fun '(e_src,e_tgt) =>  e_src.(EID.tid) = e_tgt.(EID.tid)) r.

    (** * Utility relations **)


    (** ** Relation building helpers *)

    (** This helper computes an optional key from each eid and event pair of a
          candidate using [get_key], and gathers all eids with the same key
          together into a set. It returns a map from keys to sets of eids *)
    Definition gather_by_key `{Countable K} pe
      (get_key : EID.t -> iEvent -> option K) : gmap K (gset EID.t) :=
      fold_left (λ acc '(eid, event), match get_key eid event with
                                      | Some k => {[ k := {[eid]}]}
                                      | None => ∅
                                      end ∪ₘ acc) (event_list pe) ∅.
    #[global] Typeclasses Opaque gather_by_key.

    #[global] Instance set_elem_of_gather_by_key_lookup `{Countable K} pe
      (get_key : EID.t → iEvent → option K) (k: K) (eid : EID.t):
      SetUnfoldElemOf eid (gather_by_key pe get_key !!! k)
        (∃ E, pe !! eid = Some E ∧ get_key eid E = Some k).
    Proof.
      tcclean.
      unfold gather_by_key.
      orewrite* (fold_left_inv_ND
                   (λ map tl, ∀ eid k,
                      eid ∈ map !!! k ↔
                      ∃ ev, pe !! eid = Some ev
                            ∧ (eid, ev) ∉ tl
                            ∧ get_key eid ev = Some k)).
      - apply event_list_NoDup.
      - clear eid k. intros eid k.
        rewrite lookup_total_unfold.
        setoid_rewrite event_list_match.
        set_solver.
      - clear eid k. intros map [eid ev] tl Hel Hntl Hinv eid' k.
        rewrite <- event_list_match in Hel.
        destruct (get_key eid ev) as [k' |] eqn:Hgk.
        1: destruct decide subst k k'.
        all: destruct decide subst eid eid'.
        all: rewrite lookup_total_unfold.
        all: set_unfold.
        all: rewrite Hinv.
        all: set_solver - Hinv.
      - set_solver.
    Qed.

    #[global] Instance lookup_total_unfold_gather_by_key `{Countable K} pe
      (get_key : EID.t → iEvent → option K) (k: K):
      LookupTotalUnfold k (gather_by_key pe get_key)
        (collect_all (λ eid event, get_key eid event = Some k) pe).
    Proof. tcclean. set_solver. Qed.

    Lemma gather_by_key_None `{Countable K} pe
      (get_key : EID.t → iEvent → option K) (k : K):
      gather_by_key pe get_key !! k = None ↔
      ∀ eid ev, (eid, ev) ∈ event_list pe → get_key eid ev ≠ Some k.
    Proof.
      unfold gather_by_key.
      orewrite* (fold_left_inv_ND
                   (λ map tl, ∀ k,
                      map !! k = None ↔
                      ∀ eid ev, (eid, ev) ∈ event_list pe →
                                (eid, ev) ∈ tl ∨ get_key eid ev ≠ Some k)).
      - apply event_list_NoDup.
      - clear k.
        intro k.
        rewrite lookup_unfold.
        hauto lq:on.
      - clear k. intros map [eid ev] tl Hel Hntl Hinv k.
        destruct (get_key eid ev) as [k' |] eqn:Hgk.
        1: destruct decide subst k k'.
        all: rewrite lookup_unfold.
        all: rewrite option_union_None.
        all: rewrite Hinv; clear Hinv.
        all: set_solver.
      - set_solver.
    Qed.

    (** If there is an event with key [k], then [k] must in the gathered map *)
    Lemma lookup_is_Some_gather_by_key `{Countable K} pe
      (get_key : EID.t → iEvent → option K) (k: K):
      (∃ eid event, (eid, event) ∈ event_list pe ∧ get_key eid event = Some k) →
      is_Some (gather_by_key pe get_key !! k).
    Proof.
      destruct (gather_by_key pe get_key !! k) eqn:Heqn.
      - done.
      - rewrite gather_by_key_None in Heqn.
        naive_solver.
    Qed.

    (** Returns an equivalence relation, such that two events are in the relation
          iff they have the same key computed with [get_key] *)
    Definition same_key `{Countable K} (get_key : EID.t -> iEvent -> option K)
      pe :=
      finmap_reduce_union (λ k s, s × s) (gather_by_key pe get_key).

    (** An unfold instance for [same_key] *)
    #[global] Instance set_elem_of_same_key `{Countable K} pe
      get_key eids :
      SetUnfoldElemOf eids
        (same_key get_key pe)
        (∃ E1 E2 (k: K), pe !! eids.1 = Some E1 ∧ pe !! eids.2 = Some E2
                         ∧ get_key eids.1 E1 = Some k ∧ get_key eids.2 E2 = Some k).
    Proof.
      tcclean. destruct eids. unfold same_key.
      set_unfold.
      split.
      - intros (?&?&?&?).
        lookup_lookup_total; set_solver.
      - intros (?&?&k&?). destruct_and!.
        opose proof* (lookup_is_Some_gather_by_key pe get_key k) as [? HSome].
        { set_solver. }
        do 2 eexists.
        repeat split_and; first eassumption.
        all: lookup_lookup_total; set_solver.
    Qed.
    #[global] Typeclasses Opaque same_key.


    (** ** Thread and instruction based orders and relations *)

    Class UnfoldEidRels := {}.

    (** Equivalence relation relating events from the same thread *)
    Definition same_thread : (t) → grel EID.t :=
      same_key (λ eid _, Some (eid.(EID.tid))).
    #[global] Typeclasses Opaque same_thread.
    #[global] Instance set_elem_of_same_thread `{UnfoldEidRels} pe eids:
      SetUnfoldElemOf eids (same_thread pe)
        (is_Some (pe !! eids.1) ∧ is_Some (pe !! eids.2) ∧
         eids.1.(EID.tid) = eids.2.(EID.tid)).
    Proof.
      tcclean.
      destruct eids.
      unfold same_thread.
      set_unfold #UnfoldEidRels.
      hauto q:on.
    Qed.

    (** Equivalence relation relating events from the same instruction instance *)
    Definition same_instruction_instance : t → grel EID.t :=
      same_key (λ eid _, Some (eid.(EID.tid), eid.(EID.iid))).
    #[global] Typeclasses Opaque same_instruction_instance.
    #[global] Instance set_elem_of_same_instruction_instance `{UnfoldEidRels} pe eids:
      SetUnfoldElemOf eids (same_instruction_instance pe)
        (is_Some (pe !! eids.1) ∧ is_Some (pe !! eids.2) ∧
         eids.1.(EID.tid) = eids.2.(EID.tid) ∧
         eids.1.(EID.iid) = eids.2.(EID.iid)).
    Proof.
      tcclean.
      destruct eids.
      unfold same_instruction_instance.
      set_unfold #UnfoldEidRels.
      hauto q:on.
    Qed.


    (** Intra Instruction Order: The order in which events ran inside an
          instruction

          This is intended to disappear in future versions,
          try not to depend on it *)
    Definition iio pe :=
      same_instruction_instance pe
        |> filter (λ eids, eids.1.(EID.ieid) < eids.2.(EID.ieid))%nat.
    #[global] Typeclasses Opaque iio.
    #[global] Instance set_elem_of_iio`{UnfoldEidRels} pe eids:
      SetUnfoldElemOf eids (iio pe)
        (is_Some (pe !! eids.1) ∧ is_Some (pe !! eids.2) ∧
         eids.1.(EID.tid) = eids.2.(EID.tid) ∧
         eids.1.(EID.iid) = eids.2.(EID.iid) ∧
         eids.1.(EID.ieid) < eids.2.(EID.ieid))%nat. (* Should use <ᵢ *)
    Proof.
      tcclean.
      destruct eids.
      unfold iio.
      set_unfold #UnfoldEidRels.
      naive_solver lia.
    Qed.

    (** Order in which the instructions architecturally ran. This does not mean
          they micro-architecturally run in that specific order. This is an inter
          instruction order, it does not order the events inside an instructions
          (see [iio] for that) *)
    Definition instruction_order pe :=
      same_thread pe
        |> filter (λ eids, eids.1.(EID.iid) < eids.2.(EID.iid))%nat.
    #[global] Typeclasses Opaque instruction_order.
    #[global] Instance set_elem_of_instruction_order`{UnfoldEidRels} pe eids:
      SetUnfoldElemOf eids (instruction_order pe)
        (is_Some (pe !! eids.1) ∧ is_Some (pe !! eids.2) ∧
         eids.1.(EID.tid) = eids.2.(EID.tid) ∧
         eids.1.(EID.iid) < eids.2.(EID.iid))%nat.
    Proof.
      tcclean.
      destruct eids.
      unfold instruction_order.
      set_unfold #UnfoldEidRels.
      naive_solver lia.
    Qed.

    (** Complete thread order. This is a strict partial order on each thread
          events denoting event that happened sequentially before other according
          to the program and instruction semantics. This does NOT means that this
          order implies any kind of weak memory ordering *)
    Definition full_instruction_order pe := instruction_order pe ∪ iio pe.
    #[global] Typeclasses Transparent full_instruction_order.


    (** ** Memory based relations *)

    Implicit Type ev : iEvent.

    (** Equivalence relation relating memory events that have the same physical
          address. In an [MixedSize] model which splits reads but not write, this
          is based on the pa of the whole read *)
    Definition same_pa : t → grel EID.t :=
      same_key (λ _, get_pa).
    #[export] Typeclasses Transparent same_pa.

    (** Equivalence relation relating memory event that have the same size and value *)
    Definition same_mem_value : t → grel EID.t :=
      same_key (λ _, get_mem_value).
    #[export] Typeclasses Transparent same_mem_value.

    Definition fr (cd : t) : grel EID.t :=
      (rf cd)⁻¹⨾ (co cd).
    #[export] Typeclasses Transparent fr.

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
      cdestruct H.
      apply list_lookup_alt in H1.
      cdestruct H1.
      done.
    Qed.

    Definition non_initial_eids (gr : Candidate.t) :=
      collect_all (λ eid _, eid.(EID.tid) ≠ 0)%nat gr.

    (* the union of events in non-zero threads is equal to the set all of non-initial events,
   given the well-formedness which assumes thread 0 contains and only contains initial writes of all locations *)
    Lemma non_initial_eids_fold' {gr : Candidate.t} (k b n : nat) x:
      (b <= n)%nat ->
      x = collect_all (λ eid _, eid.(EID.tid) ∈ (seq k b))%nat gr ->
      foldl (λ (s : gset _) (idx : nat),
               filter (λ eid, eid.(EID.tid) = idx) (valid_eid gr) ∪ s) x (seq (b+k) (n-b))
      = collect_all (λ eid _, eid.(EID.tid) ∈ (seq k n))%nat gr.
    Proof.
      unfold collect_all.
      revert b x.
      induction n.
      - cdestruct |- ***.
        destruct b;last lia.
        simpl. done.
      - cdestruct |- ***.
        rewrite Nat.le_lteq in H.
        destruct H.
        + assert (S n - b = S (n - b))%nat as -> by lia.
          rewrite seq_end. rewrite foldl_snoc.
          rewrite IHn.
          2:lia.  2: done.
          set_unfold.
          intros.
          assert (b + k + (n - b)= k + n)%nat as -> by lia.
          clear IHn H.
          assert (k%nat :: seq (S k) n = seq k n ++ [(k+n)%nat])%list as ->.
          { rewrite <-seq_end. simpl. done. }
          split; cdestruct |- ***.
          * destruct H;cdestruct H.
            -- exists (x,x0). sauto use:elem_of_app.
            -- exists (x,i). sauto use:elem_of_app.
          * apply elem_of_app in H.
            destruct H.
            -- right. exists (x,i).  sauto.
            -- left. sauto.
        + subst b.
          assert (S n - S n = 0)%nat as -> by lia.
          simpl. done.
    Qed.

    Lemma non_initial_eids_fold_aux (gr : Candidate.t) (n : nat):
      foldl (λ (s : gset _) (idx : nat),
               filter (λ eid, eid.(EID.tid) = idx) (valid_eid gr) ∪ s) ∅ (seq (0+1) (n-0))
      = collect_all (λ eid _, eid.(EID.tid) ∈ (seq 1 n))%nat gr.
    Proof.
      eapply non_initial_eids_fold'.
      - lia.
      - simpl. unfold collect_all. set_unfold. sauto.
    Qed.

    Lemma non_initial_eids_fold {gr : Candidate.t} (n : nat):
      S n = num_of_thd gr ->
      foldl (λ (s : gset _) (idx : nat), filter (λ eid, eid.(EID.tid) = S idx) (valid_eid gr) ∪ s) ∅ (seq 0 n)
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
      unfold collect_all.
      set_unfold.
      intros Hsz.
      intros.
      split;cdestruct |- ***.
      - exists (x,i). set_unfold.
        assert (EID.tid x ≠ 0%nat) by lia.
        sauto.
      - exists (x,i). set_unfold.
        split;first done.
        split;last done.
        opose proof * (num_of_thd_spec gr x).
        + set_unfold. hauto.
        + rewrite <- Hsz in H2. lia.
    Qed.

    #[global] Instance set_unfold_non_initial_eids e gr:
      SetUnfoldElemOf (e) (non_initial_eids gr) (e ∈ valid_eid gr ∧ (EID.tid e) ≠ 0%nat).
    Proof. tcclean. unfold non_initial_eids. set_unfold. hauto. Qed.

    (* tid of any non-initial event is greater than 0, and smaller than the number of normal threads plus thread 0 *)
    Lemma non_initial_tid_inv gr e:
      e ∈ non_initial_eids gr ->
      (0 < e.(EID.tid) ∧ e.(EID.tid) < num_of_thd gr)%nat.
    Proof.
      intros. set_unfold. destruct H.
      apply num_of_thd_spec in H.
      lia.
    Qed.

    (* tid 0 is reserved for initial writes *)
    Definition initials (cd : t) : gset EID.t :=
      collect_all  (fun e _=> e.(EID.tid) = 0%nat) cd.

    #[global] Instance set_unfold_initial_eids e gr:
      SetUnfoldElemOf (e) (initials gr) (e ∈ valid_eid gr ∧ (EID.tid e) = 0%nat).
    Proof. tcclean. unfold initials. set_unfold. split; naive_solver. Qed.

    Lemma valid_eid_disjoint_union gr :
      initials gr ∪ non_initial_eids gr = valid_eid gr
      ∧ initials gr ## non_initial_eids gr.
    Proof.
      unfold initials. unfold non_initial_eids.
      split.
      - apply set_eq. intros.
        set_unfold. set_unfold.
        destruct (decide (EID.tid x = 0%nat));hauto.
      - set_unfold. intros. hauto.
    Qed.

    #[global] Opaque non_initial_eids.
    #[global] Opaque initials.

  End Candidate.

  (** Non-mixed size well-formedness *)
  Module NMSWF.
    Import Candidate.

    (** Check that all memory accesses have size 8. Alignment checking need to
        know how pa work and thus need to be architecture specific*)
    Definition size8_wf (cd : t) : Prop :=
      collect_all
        (fun _ event =>
           match event with
           | IEvent (MemRead 8 _) _ => false
           | IEvent (MemRead _ _) _ => true
           | IEvent (MemWrite 8 _) _ => false
           | IEvent (MemWrite _ _) _ => true
           | _ => false
           end) cd = ∅.

    Definition co_wf (cd : t) : Prop :=
      let co := co cd in
      let loc := same_pa cd in
      let writes := mem_writes_req cd in
      grel_irreflexive co ∧
      grel_transitive co ∧
      (co ⊆ loc) ∧
      (grel_dom co ⊆ writes) ∧
      (grel_rng co ⊆ writes) ∧
      (loc ∩ (writes × writes) = co ∪ co⁻¹ ∪ ⦗writes⦘)
      (* initials are the minimum elements *)
      ∧ (co⨾⦗initials cd⦘ = ∅).

    Definition rf_wf (cd : t) : Prop :=
      let rf := rf cd in
      let loc := same_pa cd in
      let val := same_mem_value cd in
      let reads := mem_reads_req cd in
      let writes := mem_writes_req cd in
      (grel_dom rf ⊆ writes) ∧
      (grel_rng rf = reads) ∧
      grel_functional (rf⁻¹) ∧
      (rf ⊆ loc ∩ val).
    (* NOTE: It is only complete for user Arm *)

    Definition po_wf (cd : t) : Prop :=
      let po := po cd in
      let init := initials cd in
      let lt := (λ '(e, e'), (EID.tid e) = (EID.tid e') ∧ (((EID.iid e)= (EID.iid e') ∧ (EID.ieid e) < (EID.ieid e'))
                             ∨ ((EID.iid e) < (EID.iid e'))))%nat in
      grel_irreflexive po ∧
      grel_transitive po ∧
      (* only between nodes of same threads, but not between initial writes even if they reside in thread 0 *)
      (po ∪ po⁻¹ ∪ (init × init) = (same_thread cd)) ∧
      (po ∩ (init × init) = ∅) ∧
      (set_Forall lt po) ∧
      (set_Forall (λ (r : EID.t * EID.t), ((lt r) ∧ r ∉ (init × init)) -> r ∈ po) (same_thread cd))
    .

    Definition addr_wf (cd : t) : Prop :=
      let addr := addr cd in
      let po := po cd in
      let reads := mem_reads_req cd in
      let mem := mem_events_req cd in
      (grel_dom addr ⊆ reads) ∧
      (grel_rng addr ⊆ mem) ∧
      (addr ⊆ po).

    Definition data_wf (cd : t) : Prop :=
      let data := data cd in
      let po := po cd in
      let reads := mem_reads_req cd in
      let writes := mem_writes_req cd in
      (grel_dom data ⊆ reads) ∧
      (grel_rng data ⊆ writes) ∧
      (data ⊆ po).

    Definition ctrl_wf (cd : t) : Prop :=
      let ctrl := ctrl cd in
      let po := po cd in
      let reads := mem_reads_req cd in
      (grel_dom ctrl ⊆ reads) ∧
      (ctrl ⊆ po) ∧
      (ctrl⨾po ⊆ ctrl).

    Definition lxsx_wf (cd : t) :  Prop :=
      let rmw := lxsx cd in
      let loc := same_pa cd in
      let po := po cd in
      let writes := mem_writes_atomic cd in
      let reads := mem_reads_atomic cd in
      grel_functional rmw ∧
      grel_functional (rmw⁻¹) ∧
      (rmw ⊆ loc) ∧
      (rmw ⊆ po) ∧
      (grel_dom rmw ⊆ reads) ∧
      (grel_rng rmw ⊆ writes) ∧
      (rmw ∩ (⦗reads⦘⨾po ⨾⦗writes⦘⨾ po ⨾⦗writes⦘)  = ∅) ∧
      (rmw ∩ (⦗reads⦘⨾po ⨾⦗reads⦘⨾ po ⨾⦗writes⦘)  = ∅).

    Definition initial_writes (cd : t) :=
      filter (λ e, ¬ ∃ e', e' ∈ (mem_writes_req cd) ∧ (e', e) ∈ (co cd)) (mem_writes_req cd).

    Definition initial_wf (cd : t) : Prop :=
      let pa_set :=
        fold_left
          (fun pa_set '(eid, event) =>
             if (bool_decide ((eid.(EID.tid) = 0%nat) ∧ (eid.(EID.ieid) = 0%nat))) then
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
             if (bool_decide (eid.(EID.tid) = 0%nat)) && (bool_decide (eid.(EID.ieid) = 0%nat)) then
               match event : iEvent with
               | IEvent (MemWrite n rr) _ => {[rr.(WriteReq.pa)]} ∪ pa_init_set
               | _ => pa_init_set
               end
             else pa_init_set) (event_list cd) (∅:gset pa) in
      (* number of locations = number of initial nodes, i.e. one node per location *)
      (* and they are all the only event in a trace *)
      ((size pa_init_set) = size (initials cd))
      (* initial nodes are all write 0 *)
      ∧ (∀ e ∈ (initials cd), is_valid_init_mem_write cd e)
      (* locations appear in the program = locations for with an initial write exists *)
      ∧ (pa_set = pa_init_set)
      ∧ ((initials cd) = (initial_writes cd))
      ∧ (set_Forall (λ e, e.(EID.ieid) = 0%nat) (initials cd))
    .

    (* Check if all memory events have explicit access strength, variaty, and their responds are valid *)
    Definition mem_wf (cd : t) : Prop :=
      mem_reads_req cd ⊆ mem_reads cd ∩ mem_explicit cd ∧
      mem_writes_req cd ⊆ mem_writes cd ∩ mem_explicit cd.

    (* Check that a candidate is self consistent *)
    Definition wf (cd : t) : Prop :=
      size8_wf cd
      ∧ rf_wf cd
      ∧ co_wf cd
      ∧ po_wf cd
      ∧ addr_wf cd
      ∧ data_wf cd
      ∧ ctrl_wf cd
      ∧ lxsx_wf cd
      ∧ initial_wf cd
      ∧ mem_wf cd.

  End NMSWF.

End CandidateExecutions.
