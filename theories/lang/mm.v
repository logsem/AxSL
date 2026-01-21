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

(* This file contains the memory model *)
(* TODO: compilation of this file is slow, move lemmas to a separate file *)
From SSCCommon Require Import Common CSets GRel.


Require Import ISASem.SailArmInstTypes.
Require Import stdpp.prelude.
Require Import stdpp.bitvector.definitions.

Require Export self.lang.machine.

Require Import ssreflect.

Open Scope stdpp_scope.

Module AAConsistent.

  Import AACand.
  Import Candidate.
  Import AAInter.
  Export ISASem.SailArmInstTypes.


(** * Definition of barriers categories and barrier sets

      This section defines the event sets of Arm barrier and the corresponding
      classification. For now only dmbs, dsbs and isbs are supported.

      This development assumes that all hardware threads are in the same inner
      shareability domain, therefore we identify barriers that are:
      - Full system
      - Outer shareable
      - Inner shareable
      This might need to change when considering device interaction later *)
Section Barriers.
  Implicit Type cd : t.
  Implicit Type b : barrier.
  #[local] Hint Extern 10 (Decision (?x _)) => unfold x : typeclass_instances.
  #[local] Hint Extern 10 (Decision (?x _ _)) => unfold x : typeclass_instances.
  #[local] Hint Extern 10 (Decision (?x _ _ _)) => unfold x : typeclass_instances.


  Definition is_isb b := if b is Barrier_ISB _ then True else False.
  Definition isb cd := collect_all (λ _, is_barrierP is_isb) cd.

  Definition is_dsbP (P : MBReqTypes → Prop) b :=
    if b is Barrier_DSB dxb
    then dxb.(DxB_domain) ≠ MBReqDomain_Nonshareable ∧ P dxb.(DxB_types)
    else False.
  Definition is_dsb := is_dsbP (λ _, True).
  Definition is_dsbT t := is_dsbP (.=t).

  Definition is_dsbnshP (P : MBReqTypes → Prop) b :=
    if b is Barrier_DSB dxb
    then dxb.(DxB_domain) = MBReqDomain_Nonshareable ∧ P dxb.(DxB_types)
    else False.
  Definition is_dsbnsh := is_dsbnshP (λ _, True).
  Definition is_dsbnshT t := is_dsbnshP (.=t).

  Definition dsbsy cd :=
    collect_all (λ _, is_barrierP (is_dsbT MBReqTypes_All)) cd.
  Definition dsbst cd :=
    collect_all (λ _, is_barrierP (is_dsbT MBReqTypes_Writes)) cd.
  Definition dsbld cd :=
    collect_all (λ _, is_barrierP (is_dsbT MBReqTypes_Reads)) cd.
  Definition dsb cd := collect_all (λ _, is_barrierP is_dsb) cd.
  Definition dsbnshsy cd :=
    collect_all (λ _, is_barrierP (is_dsbnshT MBReqTypes_All)) cd.
  Definition dsbnshst cd :=
    collect_all (λ _, is_barrierP (is_dsbnshT MBReqTypes_Writes)) cd.
  Definition dsbnshld cd :=
    collect_all (λ _, is_barrierP (is_dsbnshT MBReqTypes_Reads)) cd.
  Definition dsbnsh cd := collect_all (λ _, is_barrierP is_dsbnsh) cd.

  Definition is_dmbP (P : MBReqTypes → Prop) b :=
    if b is Barrier_DMB dxb
    then dxb.(DxB_domain) ≠ MBReqDomain_Nonshareable ∧ P dxb.(DxB_types)
    else False.
  Definition is_dmb := is_dmbP (λ _, True).
  Definition is_dmbT t := is_dmbP (.=t).

  Definition is_dmbnshP (P : MBReqTypes → Prop) b :=
    if b is Barrier_DMB dxb
    then dxb.(DxB_domain) = MBReqDomain_Nonshareable ∧ P dxb.(DxB_types)
    else False.
  Definition is_dmbnsh := is_dmbnshP (λ _, True).
  Definition is_dmbnshT t := is_dmbnshP (.=t).

  Definition dmbsy cd :=
    collect_all (λ _, is_barrierP (is_dmbT MBReqTypes_All)) cd.
  Definition dmbst cd :=
    collect_all (λ _, is_barrierP (is_dmbT MBReqTypes_Writes)) cd.
  Definition dmbld cd :=
    collect_all (λ _, is_barrierP (is_dmbT MBReqTypes_Reads)) cd.
  Definition dmb cd := collect_all (λ _, is_barrierP is_dmb) cd.
  Definition dmbnshsy cd :=
    collect_all (λ _, is_barrierP (is_dmbnshT MBReqTypes_All)) cd.
  Definition dmbnshst cd :=
    collect_all (λ _, is_barrierP (is_dmbnshT MBReqTypes_Writes)) cd.
  Definition dmbnshld cd :=
    collect_all (λ _, is_barrierP (is_dmbnshT MBReqTypes_Reads)) cd.
  Definition dmbnsh cd := collect_all (λ _, is_barrierP is_dmbnsh) cd.

  (** ** Cumulated barriers

      Each of those set collect all barrier that are stronger than the set name *)

  Definition dsb_full cd := dsbsy cd.
  Definition dsb_load cd := dsbld cd ∪ dsbsy cd.
  Definition dsb_store cd := dsbst cd ∪ dsbsy cd.
  Definition dmb_full cd := dmbsy cd ∪ dsbsy cd.
  Definition dmb_load cd := dmbld cd ∪ dmbsy cd ∪ dsb_load cd.
  Definition dmb_store cd := dmbst cd ∪ dmbsy cd ∪ dsb_store cd.

  Definition dmb_sy cd := dmbsy cd.
  Definition dmb_ld cd := dmbld cd.
  Definition dmb_st cd := dmbst cd.

End Barriers.


  (* Definition value_of_wreq {n} (req: AAInter.WriteReq.t n) := *)
  (*  req.(AAInter.WriteReq.value). *)

  (* Definition addr_of_wreq {n} (req: AAInter.WriteReq.t n) := *)
  (*  req.(AAInter.WriteReq.pa). *)

  (* (* This is annoying since the interface allows writing arbitraty bytes to memory, we have *)
  (*  to make sure the number of bytes is [AAArch.val_size]*) *)
  (* Program Definition addr_and_value_of_wreq {n} (req: AAInter.WriteReq.t n) : *)
  (*   option (Addr * Val). *)
  (* destruct req as []. *)
  (* destruct (decide (n = AAArch.val_size)). *)
  (* { *)
  (*   subst n. *)
  (*   exact (Some (pa,value)). *)
  (* } *)
  (* exact None. *)
  (* Defined. *)

  (* Definition addr_of_rreq {n} (req: AAInter.ReadReq.t n) : Addr := req.(AAInter.ReadReq.pa). *)

  (* Program Definition value_of_read (event : Event) : option Val. *)
  (* destruct event as [? []]. *)
  (* exact None. *)
  (* exact None. *)
  (* destruct t1; last exact None. *)
  (* destruct p. *)
  (* destruct (decide (n = AAArch.val_size)). *)
  (* { *)
  (*   subst n. *)
  (*   exact (Some b). *)
  (* } *)
  (* all : exact None. *)
  (* Defined. *)

  (* (** write *) *)
  (* Definition event_is_write_with_P (event : Event) (P : ∀ n : N, AAInter.WriteReq.t n -> bool) := *)
  (*   match event with *)
  (*   | AAInter.IEvent (AAInter.MemWrite n wreq) wresp => wreq_is_valid wreq && wresp_is_valid wresp && P n wreq *)
  (*   | _ => false end. *)
  (* #[global] Hint Unfold event_is_write_with_P : all. *)

  (* Definition event_is_pln_write (event : Event) := *)
  (*  event_is_write_with_P event (λ _ wreq, kind_of_wreq_P wreq *)
  (*                                           (λ κ, bool_decide (κ = (Build_Explicit_access_kind AV_plain AS_normal)))). *)
  (* #[global] Hint Unfold event_is_pln_write : all. *)

  (* Definition event_is_rel (event : Event) := *)
  (*  event_is_write_with_P event (λ _ wreq, kind_of_wreq_P wreq *)
  (*                (λ κ, bool_decide (κ.(Explicit_access_kind_strength) = AS_rel_or_acq))). *)
  (* #[global] Hint Unfold event_is_rel : all. *)

  (* Definition event_is_xcl_write (event : Event) := *)
  (*   event_is_write_with_P event (λ _ wreq, *)
  (*                                  (* kind_of_wreq_P wreq *) *)
  (*                                  (*          (λ κ, bool_decide (Explicit_access_kind_strength κ= AS_normal)) *) *)
  (*                                  (* && *) *)
  (*                                  kind_of_wreq_is_atomic wreq). *)
  (* #[global] Hint Unfold event_is_xcl_write : all. *)

  (* Definition event_is_write_with (event : Event) (ks : Access_strength) (kv : Access_variety) (a : Addr) (v : Val) := *)
  (*  event_is_write_with_P event (λ _ wreq, kind_of_wreq_P wreq *)
  (*                                           (λ κ, bool_decide (κ = (Build_Explicit_access_kind kv ks))) && *)
  (*                                  bool_decide (addr_and_value_of_wreq wreq = Some (a,v))). *)
  (* #[global] Hint Unfold event_is_write_with : all. *)

  (* Definition event_is_write_with_addr (event : Event) (a : Addr) := *)
  (*   event_is_write_with_P event (λ _ wreq, bool_decide (addr_of_wreq wreq = a)). *)

  (* Definition event_is_write_with_kind (event : Event) (ks : Access_strength) (kv : Access_variety) := *)
  (*   event_is_write_with_P event (λ _ wreq, *)
  (*                                  kind_of_wreq_P wreq (λ κ, bool_decide (κ = (Build_Explicit_access_kind kv ks)))). *)
  (* #[global] Hint Unfold event_is_write_with_kind : all. *)

  (* Definition event_is_write (event : Event) := *)
  (*   event_is_write_with_P event (λ _ _, true). *)
  (* #[global] Hint Unfold event_is_write : all. *)

  Lemma event_is_mem_write_elem_of_mem_writes {gr} (e : Eid) (event : Event) :
    gr !! e = Some event ->
    is_mem_write event ->
    (* event_is_write_with event ks kv a v -> *)
    e ∈ mem_writes gr.
  Proof.
    intros Hlk Hw. set_unfold.
    cdestruct Hw. subst.
    naive_solver.
  Qed.

  Lemma mem_wf_spec_write gr:
    NMSWF.mem_wf gr ->
    forall eid event,
    gr !! eid = Some event ->
    is_mem_write_req event ->
    is_mem_write event.
  Proof.
    intros Hwf ?? Hlk Hw.
    set_unfold.
    cdestruct Hw.
    set_unfold.
    destruct Hwf as [_ Hwf].
    ospecialize* (Hwf eid).
    set_unfold. naive_solver.
    set_unfold in Hwf.
    cdestruct Hwf.
    rewrite H0 in Hlk; inversion Hlk;subst.
    done.
  Qed.

  Lemma event_is_write_elem_of_mem_writes2 {gr} (e : Eid) :
    NMSWF.wf gr ->
    e ∈ mem_writes_req gr ->
    ∃  (event : Event), gr !! e = Some event ∧ is_mem_write event.
  Proof.
    intros Hwf Hin. set_unfold.
    assert (NMSWF.mem_wf gr). { rewrite /NMSWF.wf in Hwf. naive_solver. }

    cdestruct Hin.
    opose proof * (mem_wf_spec_write gr H e);try eassumption.
    set_unfold. naive_solver.
    naive_solver.
  Qed.

  (* Lemma event_is_write_with_addr_elem_of_mem_writes2 {gr} (e : Eid) : *)
  (*   NMSWF.wf gr -> *)
  (*   e ∈ AACandExec.Candidate.mem_writes gr -> *)
  (*   ∃  (event : Event) (a : Addr), gr !! e = Some event ∧ event_is_write_with_addr event a. *)
  (* Proof. *)
  (*   intros Hwf Hin. set_unfold. *)
  (*   assert (NMSWF.mem_wf gr). *)
  (*   { rewrite /NMSWF.wf in Hwf. naive_solver. } *)
  (*   destruct Hin as [? [? [? HE]]]. *)
  (*   pose proof (mem_wf_spec_write gr H e _ HE). ospecialize* H0. set_unfold. do 3 eexists. eassumption. *)
  (*   eexists. exists (addr_of_wreq x0). split;eauto. *)
  (*   simpl. rewrite bool_unfold. simpl in H0. rewrite bool_unfold in H0. clear H HE. *)
  (*   naive_solver. *)
  (* Qed. *)

  (* Lemma event_is_write_with_P_impl (event : Event) (P Q : ∀ n : N, AAInter.WriteReq.t n -> bool) : *)
  (*   (forall n wreq, P n wreq -> Q n wreq) -> *)
  (*   event_is_write_with_P event P -> event_is_write_with_P event Q. *)
  (* Proof. *)
  (*  intros Himp HP. destruct event;auto;destruct o;auto. simpl in *. *)
  (*  rewrite ->bool_unfold in *; split; naive_solver. *)
  (* Qed. *)

  (* Lemma event_is_write_with_impl_addr (event : Event) (ks : Access_strength) (kv : Access_variety) *)
  (*   (a : Addr) (v : Val) : *)
  (*   event_is_write_with event ks kv a v -> event_is_write_with_addr event a. *)
  (* Proof. *)
  (*   apply event_is_write_with_P_impl. *)
  (*   intros. *)
  (*   repeat rewrite ->bool_unfold in *. *)
  (*   simpl. unfold addr_and_value_of_wreq in H. destruct H as [_ H]. *)
  (*   case_match;auto. *)
  (*   case_match;auto. *)
  (*   unfold eq_rec_r, eq_rec in H. subst n. *)
  (*   rewrite <-Classical_Prop.Eq_rect_eq.eq_rect_eq in H. *)
  (*   inversion H. done. done. *)
  (* Qed. *)

  (* Lemma event_is_write_with_impl_kind (e : Eid) (event : Event) (ks : Access_strength) (kv : Access_variety) (a : Addr) (v : Val) : *)
  (*   event_is_write_with event ks kv a v -> event_is_write_with_kind event ks kv. *)
  (* Proof. *)
  (*   apply event_is_write_with_P_impl. *)
  (*   intros. unfold kind_of_wreq_P in *. *)
  (*   rewrite -> bool_unfold in *. *)
  (*   hauto lq:on. *)
  (* Qed. *)

  (* (** read *) *)
  (* Definition event_is_read_with_P (event : Event) (P : ∀ n : N, AAInter.ReadReq.t n -> bool) := *)
  (*   match event with *)
  (*   | AAInter.IEvent (AAInter.MemRead n rreq) rresp => rreq_is_valid rreq && rresp_is_valid rresp && P n rreq *)
  (*   | _ => false end. *)
  (* #[global] Hint Transparent event_is_read_with_P : all. *)

  (* Definition event_is_read (event : Event) := *)
  (*   event_is_read_with_P event (λ _ _, true). *)

  (* Definition event_is_pln_read (event : Event) := *)
  (*   event_is_read_with_P event (λ _ rreq, kind_of_rreq_P rreq (λ κ, bool_decide (κ = (Build_Explicit_access_kind AV_plain AS_normal)))). *)

  (* Definition event_is_acq (event : Event) := *)
  (*   event_is_read_with_P event (λ _ rreq, kind_of_rreq_P rreq (λ κ, bool_decide (κ = (Build_Explicit_access_kind AV_plain AS_rel_or_acq)))). *)

  (* Definition event_is_xcl_read (event : Event) := *)
  (*   event_is_read_with_P event (λ _ rreq, kind_of_rreq_P rreq (λ κ, bool_decide ((Explicit_access_kind_strength κ = AS_normal))) *)
  (*                                         && kind_of_rreq_is_atomic rreq). *)

  (* Definition event_is_wacq (event : Event) := *)
  (*   event_is_read_with_P event (λ _ rreq, kind_of_rreq_P rreq (λ κ, bool_decide (κ = (Build_Explicit_access_kind AV_plain AS_acq_rcpc)))). *)

  (* Definition event_is_read_with (event : Event) (ks : Access_strength) (kv : Access_variety) (a : Addr) (v : Val) := *)
  (*   event_is_read_with_P event (λ _ rreq, *)
  (*                                 kind_of_rreq_P rreq (λ κ, bool_decide (κ = (Build_Explicit_access_kind kv ks))) && *)
  (*                                   bool_decide (addr_of_rreq rreq = a) && *)
  (*                                   bool_decide (value_of_read event = Some v) *)
  (*     ). *)

  (* Definition event_is_read_with_kind (event : Event) (ks : Access_strength) (kv : Access_variety) := *)
  (*   event_is_read_with_P event (λ _ rreq, *)
  (*       bool_decide(kind_of_rreq_P rreq (λ κ, bool_decide (κ = Build_Explicit_access_kind kv ks)))). *)

  (* Definition event_is_read_with_addr (event : Event) (a : Addr) := *)
  (*   event_is_read_with_P event (λ _ rreq, bool_decide (addr_of_rreq rreq = a)). *)

  Lemma mem_wf_spec_read gr:
    NMSWF.mem_wf gr ->
    forall eid event,
    gr !! eid = Some event ->
    is_mem_read_req event ->
    is_mem_read event.
  Proof.
    intros Hwf ?? Hlk Hw.
    set_unfold. cdestruct Hw.
    destruct Hwf as [Hwf _].
    ospecialize * (Hwf eid).
    set_unfold;naive_solver.
    set_unfold in Hwf.
    cdestruct Hwf.
    rewrite H0 in Hlk;inversion Hlk;subst.
    done.
  Qed.

  (* Lemma event_is_read_with_P_impl (event : Event) (P Q : ∀ n : N, AAInter.ReadReq.t n -> bool) : *)
  (*   (forall n rreq, P n rreq -> Q n rreq) -> *)
  (*   event_is_read_with_P event P -> event_is_read_with_P event Q. *)
  (* Proof. *)
  (*  intros Himp HP. destruct event;auto;destruct o;auto. simpl in *. *)
  (*  rewrite ->bool_unfold in *; split; naive_solver. *)
  (* Qed. *)

  (* Lemma event_is_read_with_impl_addr (e : Eid) (event : Event) (ks : Access_strength) (kv : Access_variety) (a : Addr) (v : Val) : *)
  (*   event_is_read_with event ks kv a v -> event_is_read_with_addr event a. *)
  (* Proof. *)
  (*   apply event_is_read_with_P_impl. *)
  (*   intros. unfold kind_of_wreq_P in *. *)
  (*   repeat rewrite -> bool_unfold in *. *)
  (*   hauto lq:on. *)
  (* Qed. *)

  (* Lemma event_is_read_with_impl_kind (e : Eid) (event : Event) (ks : Access_strength) (kv : Access_variety) (a : Addr) (v : Val) : *)
  (*   event_is_read_with event ks kv a v -> event_is_read_with_kind event ks kv. *)
  (* Proof. *)
  (*   apply event_is_read_with_P_impl. *)
  (*   intros. unfold kind_of_wreq_P in *. *)
  (*   repeat rewrite ->bool_unfold in *. *)
  (*   hauto lq:on. *)
  (* Qed. *)

  (* Definition get_pa_val_of_read_or_write (event : Event) := *)
  (*   match event with *)
  (*   | AAInter.IEvent (AAInter.MemRead 8 rr) (inl (val, _)) => *)
  (*       Some (addr_of_rreq rr, val) *)
  (*   | AAInter.IEvent (AAInter.MemWrite 8 wr) _ => *)
  (*       Some (addr_of_wreq wr, value_of_wreq wr) *)
  (*   | _ => None *)
  (*   end. *)

  Definition rel_writes (cd : t) := mem_writes cd ∩ mem_rel_acq cd.

  Definition acq_reads (cd : t) := mem_reads cd ∩ mem_rel_acq cd.

  Definition wacq_reads (cd : t) := mem_reads cd ∩ mem_acq_rcpc cd.

  Definition pln_writes (cd : t) := mem_writes cd ∩ mem_standalone cd.

  Definition pln_reads (cd : t) := mem_reads cd ∩ mem_standalone cd.

  Definition xcl_writes (cd : t) := mem_writes cd ∩ mem_exclusive cd.

  Definition xcl_reads (cd : t) := mem_reads cd ∩ mem_exclusive cd.

  Definition dob (cd : t) : Rel :=
    let writes := mem_writes cd in
    let reads := mem_reads cd in
    let isb := isb cd in
    let addr := addr cd in
    let data := data cd in
    let ctrl := ctrl cd in
    let po := cd.(po) in
    let coi := internal_of cd.(co) in
    let rfi := internal_of cd.(rf) in
    data
      ∪ addr
      ∪ (ctrl⨾⦗writes⦘)
      ∪ ((ctrl ∪ (addr ⨾ po))⨾⦗isb⦘⨾po⨾⦗reads⦘)
      ∪ (addr⨾po⨾⦗writes⦘)
      ∪ ((ctrl ∪ data)⨾ coi)
      ∪ ((addr ∪ data)⨾ rfi).

  #[global] Typeclasses Opaque dob.
  #[global] Instance set_elem_of_dob `{UnfoldEidRels} pe eids:
    SetUnfoldElemOf eids (dob pe)
      (((((((eids.1, eids.2) ∈ data pe ∨ (eids.1, eids.2) ∈ addr pe)
      ∨ (eids.1, eids.2) ∈ ctrl pe
        ∧ ∃ x : AACand.iEvent,
            pe !! eids.2 = Some x ∧ Arm.Interface.is_mem_writeP (λ (n : N) (_ : Arm.Interface.WriteReq.t n), True) x)
     ∨ (∃ z : Eid,
          (((eids.1, z) ∈ ctrl pe ∨ ∃ z0 : Eid, (eids.1, z0) ∈ addr pe ∧ (z0, z) ∈ po pe)
           ∧ ∃ x : AACand.iEvent, pe !! z = Some x ∧ is_barrierP is_isb x) ∧ (z, eids.2) ∈ po pe)
       ∧ ∃ x : AACand.iEvent,
           pe !! eids.2 = Some x
           ∧ Arm.Interface.is_mem_readP
               (λ (n : N) (_ : Arm.Interface.ReadReq.t n) (_ : bv (8 * n)) (_ : option bool), True) x)
    ∨ (∃ z : Eid, (eids.1, z) ∈ addr pe ∧ (z, eids.2) ∈ po pe)
      ∧ ∃ x : AACand.iEvent,
          pe !! eids.2 = Some x ∧ Arm.Interface.is_mem_writeP (λ (n : N) (_ : Arm.Interface.WriteReq.t n), True) x)
   ∨ ∃ z : Eid, ((eids.1, z) ∈ ctrl pe ∨ (eids.1, z) ∈ data pe) ∧ EID.tid z = EID.tid eids.2 ∧ (z, eids.2) ∈ co pe)
  ∨ (∃ z : Eid, ((eids.1, z) ∈ addr pe ∨ (eids.1, z) ∈ data pe) ∧ EID.tid z = EID.tid eids.2 ∧ (z, eids.2) ∈ rf pe)).
  Proof.
    tcclean.
    destruct eids.
    unfold dob.
    set_unfold #UnfoldEidRels.
    hauto q:on.
  Qed.

  Definition bob (cd : t) : Rel :=
    let po := cd.(po) in
    let dmb_sy := dmb_sy cd in
    let dmb_ld := dmb_ld cd in
    let dmb_st := dmb_st cd in
    let rel := rel_writes cd in
    let acq := acq_reads cd in
    let wacq := wacq_reads cd in
    let writes := mem_writes cd in
    let reads := mem_reads cd in
    let coi := internal_of cd.(co) in
    (po⨾⦗dmb_sy⦘⨾po)
      ∪ (⦗rel⦘⨾po⨾⦗acq⦘)
      ∪ (⦗reads⦘⨾po⨾⦗dmb_ld⦘⨾po)
      ∪ ((⦗wacq⦘∪⦗acq⦘)⨾ po)
      ∪ (⦗writes⦘⨾po⨾⦗dmb_st⦘⨾po⨾⦗writes⦘)
      ∪ (po⨾⦗rel⦘)
      ∪ (po⨾⦗rel⦘⨾coi).

  Definition obs (cd : t) : Rel :=
    external_of (cd.(rf)) ∪ external_of (cd.(co)) ∪ external_of (fr cd).

  Definition aob (cd : t) : Rel :=
    let rfi := internal_of cd.(rf) in
    let rmw := (cd.(lxsx)) in
    let acq := acq_reads cd in
    let wacq := wacq_reads cd in
    rmw ∪ (⦗grel_rng rmw⦘⨾ rfi⨾ (⦗wacq⦘∪⦗acq⦘)).

  Definition lob (cd : t) : Rel := (dob cd) ∪ (aob cd) ∪ (bob cd).

  Definition ob (cd : t) : Rel := ((obs cd) ∪ (lob cd))⁺.

  Definition ind_lob (cd : t) : Rel := (internal_of (ob cd)).

  Definition ca (cd : t) : Rel := (fr cd) ∪ (co cd).

  Record t cd := {
      internal : grel_acyclic (((po cd) ∩ (same_pa cd)) ∪ (ca cd) ∪ (rf cd));
      external : grel_irreflexive (ob cd);
      atomic : ((cd.(lxsx)) ∩ ((external_of (fr cd))⨾(external_of (co cd)))) = ∅;
    }.

End AAConsistent.

(* memory graph *)
Module Graph.
  Export AACand.
  Export AACand.Candidate.
  Export AAConsistent.
  Export NMSWF.

  (** helper notations and definitions *)
  Definition t := Candidate.t.

  Definition iids_of (eids : gset Eid) : gset nat :=
    set_map (fun eid => eid.(EID.iid)) eids.

  Definition is_po gr oe_src e_tgt :=
    from_option (λ e_src, (e_src, e_tgt) ∈ gr.(Candidate.po)) True oe_src.

  Notation is_local_edge_of tid := (fun '(es,et) => es.(EID.tid) = tid ∧ et.(EID.tid) = tid).
  Notation is_external_edge_of := (fun '(es,et) => es.(EID.tid) ≠ et.(EID.tid)).

  Notation is_local_node_of tid := (fun e => e.(EID.tid) = tid).
  Definition local_eids (gr : Candidate.t) (tid : nat) :=
    filter (is_local_node_of tid) (Candidate.valid_eid gr).

  Notation is_rf gr e_src e_tgt := ((e_src, e_tgt) ∈ gr.(Candidate.rf)).

  Definition lob_pred_of (gr : Candidate.t) (e : Eid) :=
    grel_dom (filter (fun '(es,et) => et = e) (lob gr)).

  Definition lob_succ_of (gr : Candidate.t) (e : Eid) :=
    grel_rng (filter (fun '(es,et) => es = e) (lob gr)).

  Definition ind_lob_pred_of (gr : Candidate.t) (e : Eid) :=
    grel_dom (filter (fun '(es,et) => et = e) (ind_lob gr)).

  Definition ind_lob_succ_of (gr : Candidate.t) (e : Eid) :=
    grel_rng (filter (fun '(es,et) => es = e) (ind_lob gr)).

  Definition is_rfe gr e_src e_tgt := ((e_src, e_tgt) ∈ (external_of (gr.(Candidate.rf)))).

  Definition obs_pred_of (gr : Candidate.t) (e : Eid) :=
    grel_dom (filter (fun '(es,et) => et = e) (obs gr)).

  Definition ob_pred_of (gr : Candidate.t) (e : Eid) :=
    grel_dom (filter (fun '(es,et) => et = e) (ob gr)).

  Definition obs_succ_of (gr : Candidate.t) (e : Eid) :=
    grel_rng (filter (fun '(es,et) => es = e) (obs gr)).

  Definition ob_succ_of (gr : Candidate.t) (e : Eid) :=
    grel_rng (filter (fun '(es,et) => es = e) (ob gr)).

  Definition po_pred_of (gr : Candidate.t) (e : Eid) :=
    grel_dom (filter (fun '(es,et) => et = e) (gr.(Candidate.po))).

  Ltac pattern_evar :=
    match goal with | |- context G [?x] => is_evar x; pattern x end.

  Ltac match_inversion :=
   repeat (match goal with
    | [ HH : Some _ = None |- _ ] => inversion HH
    | [ HH : None = Some _ |- _ ] => inversion HH
    | [ HH : false |- _ ] => inversion HH
    | [ HH : Some ?x = Some _ |- _ ] => inversion HH;subst x;clear HH
    | _  => case_match
    end).

  Import AAInter.

  (** Below are axiomised results about the consistency and well-formedness of execution graphs *)

  (** well-formedness *)
  (* if two events are related by the auxilary [loc] relation and one is a write on [addr],
     then the other must be a read or write on [addr] as well *)
  Lemma wf_loc_inv_writes {gr} eid_w eid addr:
    NMSWF.wf gr ->
    (exists E1, gr !! eid_w = Some E1 ∧ get_pa E1 = Some addr) ->
    (eid_w, eid) ∈ same_pa gr ->
    (exists E2, gr !! eid = Some E2 ∧ get_pa E2 = Some addr).
  Proof.
    intros Hwf Hlk Hloc.
    assert (mem_wf gr) as Hmwf. unfold wf in Hwf. naive_solver. clear Hwf.

    cdestruct Hlk.
    set_unfold in Hloc.
    cdestruct Hloc.
    naive_solver.
  Qed.

  (* two writes on the same address are ordered by [loc] *)
  Lemma wf_loc_inv_writes2 {gr} eid_w eid:
    (exists addr E1 E2, gr !! eid_w = Some E1 ∧ get_pa E1 = Some addr ∧ gr !! eid = Some E2 ∧ get_pa E2 = Some addr) ->
    (eid_w, eid) ∈ same_pa gr.
  Proof.
    cdestruct |- ***.
    set_unfold.
    naive_solver.
  Qed.

  Ltac inversion' :=
    (match goal with
     | [ HH : Some _ = None |- _ ] => inversion HH
     | [ HH : None = Some _ |- _ ] => inversion HH
     | [ HH : false |- _ ] => inversion HH
     | [ HH : Some _ = Some _ |- _ ] =>
         inversion HH;clear HH;subst
     | [ HH : ?x = Some _, HH' : ?x = Some _ |- _] =>
         rewrite HH in HH';inversion HH';clear HH'; subst
     | [ HH : (?f ?x) = Some ?s, HH' : (?f ?x) = Some _ |- _] =>
         rewrite HH in HH';inversion HH';clear HH'; subst s
     | [ HH : (?f ?x ?y) = Some ?s, HH' : (?f ?x ?y) = Some _ |- _] =>
         rewrite HH in HH';inversion HH';clear HH'; subst s
     | [ HH : (?f ?x ?y ?z) = Some ?s, HH' : (?f ?x ?y ?z) = Some _ |- _] =>
         rewrite HH in HH';inversion HH';clear HH'; subst s
     | _  => fail
     end).

  (* in a well-formed graph, a read event [e] must read the value [val] from a write event on the same address [addr],
    (is ordered by [rf]) *)
  Lemma wf_read_inv gr e E addr val:
    wf gr ->
    gr !! e = Some E ->
    is_mem_read_req E ->
    get_pa E = Some addr ->
    get_mem_value E = Some val ->
    ∃ eid_w E_w,
      gr !! eid_w = Some E_w ∧
      is_mem_write_req E_w ∧
      get_pa E_w = Some addr ∧
      get_mem_value E_w = Some val ∧
      (eid_w, e) ∈ rf gr.
  Proof.
    rewrite /wf.
    intros Hwf Hlk Hread.
    assert (rf_wf gr) as Hwf_rf by naive_solver;rewrite /rf_wf in Hwf_rf.
    assert (mem_wf gr) as Hwf_mem by naive_solver;clear Hwf.
    destruct_and ? Hwf_rf.


    assert (Hin : e ∈ grel_rng (rf gr)).
    { rewrite H1. clear - Hread Hlk. cdestruct Hread. set_unfold. naive_solver. }

    set_unfold in Hin. destruct Hin as [e_w Hrf].
    exists e_w. specialize (H e_w). ospecialize* H. set_solver + Hrf.
    set_unfold in H. cdestruct H.
    specialize (H3 (e_w,e) Hrf).
    set_unfold in H3.

    cdestruct H3.
    repeat inversion'.
    opose proof * (mem_wf_spec_write _ Hwf_mem e_w);try naive_solver.
  Qed.

  (* in a well formed graph, a read reads from only one write *)
  Lemma wf_read_single gr w w' r:
    wf gr ->
    is_rf gr w r ->
    is_rf gr w' r ->
    w = w'.
  Proof.
    intros Hwf Hrf1 Hrf2.
    rewrite /wf in Hwf.
    assert (rf_wf gr) as Hwf_rf by naive_solver;rewrite /rf_wf in Hwf_rf.

    destruct_and ? Hwf_rf.
    clear - H0 Hrf1 Hrf2.

    eapply H0.
    rewrite grel_inv_spec. eassumption.
    rewrite grel_inv_spec. eassumption.
  Qed.

  (* well-formed [rfi] is included in [po] *)
  Lemma wf_rfi_inv {gr} eid_w eid:
    wf gr ->
    AAConsistent.t gr ->
    is_rf gr eid_w eid ->
    EID.tid eid_w = EID.tid eid ->
    (eid_w, eid) ∈ gr.(po).
  Proof.
    intros Hwf Hcs Hrf Hsth.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf. destruct_and ? Hpo_wf.
    assert (rf_wf gr) as Hrf_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /rf_wf in Hrf_wf. destruct_and ? Hrf_wf.

    assert (eid_w ∈ mem_writes_req gr) as Hw. set_solver + Hrf H4.
    assert (eid ∈ non_initial_eids gr).
    {
      (* clear H11 H13 H10 H2 H8. *)
      assert (eid ∈ mem_reads_req gr). rewrite -H7. set_solver + Hrf.
    assert (initial_wf gr) as Hinitial_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /initial_wf in Hinitial_wf. destruct_and ? Hinitial_wf.
    clear - H8 H13.
    assert (eid ∉ initials gr).
    rewrite H13. clear H13.
    set_unfold.
    cdestruct H8 |- ***.
    intro.
    cdestruct H0 |- ***.
    rewrite H in H1.
    inversion H1.
    pose proof (valid_eid_disjoint_union gr).
    set_solver - H13.
    }

    assert ((eid_w,eid) ∈ same_thread gr).
   {
     clear -Hsth H8 Hw.
     set_unfold #UnfoldEidRels.
     unfold valid_eid in H8.
     set_unfold.
     cdestruct Hw, H8.
     naive_solver.
   }

    rewrite -H0 in H10.
    apply elem_of_union in H10. destruct H10.
    2:{
      clear - H8 H10. exfalso. set_unfold. hauto lq:on.
    }
    apply elem_of_union in H10. destruct H10. assumption.
    exfalso.
    assert ((eid,eid_w) ∈ same_pa gr). apply H9 in Hrf. set_solver + Hrf.
    assert ((eid,eid_w) ∈ po gr ∩ same_pa gr). set_solver + H10 H11.
    destruct Hcs.

    unfold grel_acyclic in internal0.
    rewrite grel_irreflexive_spec in internal0.
    clear - H12 Hrf internal0.
    specialize (internal0 (eid, eid)).
    apply internal0;last reflexivity.
    apply (grel_plus_trans _ _ eid_w);
    apply grel_plus_once; set_solver.
  Qed.

  Lemma wf_coi_inv' {gr} eid_w eid:
    wf gr ->
    AAConsistent.t gr ->
    (eid_w, eid) ∈ Candidate.co gr ->
    (EID.tid eid_w) = (EID.tid eid) ->
    (eid_w, eid) ∈ Candidate.po gr.
  Proof.
    intros Hwf Hcs Hco Hsth.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf. destruct_and ? Hpo_wf.
    assert (co_wf gr) as Hco_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /co_wf in Hco_wf. destruct_and ? Hco_wf.
    assert (initial_wf gr) as Hinitial_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /initial_wf in Hinitial_wf. destruct_and ? Hinitial_wf.
    assert (eid_w ∈ mem_writes_req gr) as Hw. set_solver + Hco H10.

    assert (eid ∈ non_initial_eids gr).
    {
      clear -Hco H6 H9 H12.
      assert (eid ∈ mem_writes_req gr). set_solver + Hco H9.
      assert (eid ∉ initials gr).
      intro. clear - H12 Hco H0.
      set_unfold.
      eapply H12.
      naive_solver.

      pose proof (valid_eid_disjoint_union gr).
      set_solver - H0.
    }
    assert ((eid_w, eid) ∈ same_thread gr).
    { clear - Hsth H16 Hw. unfold same_thread. set_unfold. unfold valid_eid. set_unfold. sauto. }
    rewrite -H0 in H18.
    apply elem_of_union in H18. destruct H18.
    2:{
      clear - H16 H18. exfalso. set_unfold. hauto lq:on.
    }
    apply elem_of_union in H18. destruct H18. assumption.
    exfalso.
    assert ((eid_w,eid) ∈ co gr ∪ (co gr) ⁻¹ ∪ ⦗mem_writes_req gr⦘).
    set_solver + Hco.
    rewrite -H10 in H19.
    assert ((eid_w,eid) ∈ same_pa gr). set_solver + H19.
    assert ((eid,eid_w) ∈ same_pa gr). set_solver + H20.
    assert ((eid,eid_w) ∈ po gr ∩ same_pa gr).
    set_solver + H18 H20.

    destruct Hcs.
    unfold grel_acyclic in internal0.
    rewrite grel_irreflexive_spec in internal0.
    clear - H22 Hco internal0.
    specialize (internal0 (eid, eid)). simpl in internal0.
    apply internal0;last reflexivity.
    apply (grel_plus_trans _ _ eid_w);
    apply grel_plus_once;set_solver.
  Qed.


  (* two writes on the same location are ordered by [coi] if ordered by [po] *)
  Lemma wf_coi_inv {gr} eid_w eid:
    wf gr ->
    AAConsistent.t gr ->
    (eid_w, eid) ∈ same_pa gr ->
    {[eid_w; eid]} ⊆ mem_writes_req gr ->
    (eid_w, eid) ∈ po gr ->
    (eid_w, eid) ∈ co gr.
  Proof.
    intros Hwf Hcs Hloc Hw Hpo.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf. destruct_and ? Hpo_wf.
    assert (co_wf gr) as Hco_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /co_wf in Hco_wf. destruct_and ? Hco_wf.
    assert ((eid_w, eid) ∈ same_pa gr ∩ (mem_writes_req gr × mem_writes_req gr)).
    set_solver + Hw Hloc.
    rewrite H10 in H11.
    apply elem_of_union in H11.
    destruct H11.
    2:{
      exfalso. apply H3 in Hpo. clear - H11 Hpo. set_unfold.
      cdestruct H11. subst.
      lia.
    }
    apply elem_of_union in H11.
    destruct H11;first assumption.
    assert ((eid_w,eid) ∈ po gr ∩ same_pa gr). set_solver + Hpo Hloc.

    destruct Hcs. exfalso.
    unfold grel_acyclic in internal0.
    rewrite grel_irreflexive_spec in internal0.
    clear - H13 H11 internal0.
    specialize (internal0 (eid_w, eid_w)). simpl in internal0.
    apply internal0;last reflexivity.
    apply (grel_plus_trans _ _ eid);
    apply grel_plus_once;set_solver.
  Qed.

  Lemma rfi_subseteq_po gr:
    wf gr ->
    AAConsistent.t gr ->
    internal_of (Candidate.rf gr) ⊆ po gr.
  Proof.
    intros Hwf Hcs. intros r Hin.
    pose proof (wf_rfi_inv r.1 r.2 Hwf Hcs).
    apply H;
    set_unfold #UnfoldEidRels.

    hauto lq:on.
    set_unfold.

    hauto lq:on.
  Qed.

  Lemma aob_subseteq_po (gr : Candidate.t):
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    aob gr ⊆ po gr.
  Proof.
    intros Hwf Hcs.
    rewrite /aob.
    assert (lxsx_wf gr) as Hrmw_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /lxsx_wf in Hrmw_wf.
    destruct_and ? Hrmw_wf.

    apply union_subseteq.
    split. assumption.
    pose proof (rfi_subseteq_po _ Hwf Hcs).
    clear - H6.
    intros ??.
    assert (x ∈ internal_of (rf gr)).
    {
      clear H6.
      apply grel_seq_spec in H.
      destruct H as (?&?&?). destruct x. assert (x0 = t1) as ->. set_solver + H0.
      apply grel_seq_spec in H.
      destruct H as (?&?&?). assert (t0 = x) as ->. set_solver + H.
      done.
    }
    set_solver.
  Qed.

  Lemma lxsx_subseteq_aob (gr : Candidate.t):
    lxsx gr ⊆ aob gr.
  Proof.
    intros. set_solver.
  Qed.

  Lemma aob_subseteq_lob (gr : Candidate.t):
    aob gr ⊆ lob gr.
  Proof.
    intros. set_solver.
  Qed.

  Lemma coi_subseteq_po gr:
    wf gr ->
    AAConsistent.t gr ->
    Candidate.internal_of (Candidate.co gr) ⊆ Candidate.po gr.
  Proof.
    intros Hwf Hcs. intros r Hin.
    pose proof (wf_coi_inv' r.1 r.2 Hwf Hcs).
    set_unfold in Hin.
    apply H;hauto lq:on.
  Qed.

  Lemma bob_subseteq_po (gr : Candidate.t):
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    bob gr ⊆ po gr.
  Proof.
    intros Hwf Hcs.
    rewrite /bob.

    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf. destruct_and ? Hpo_wf.
    clear -H1 Hwf Hcs.
    rewrite grel_transitive_spec in H1.
    rewrite !union_subseteq.
    repeat split.
    - set_unfold. intros ? H. sauto lq:on.
    - set_unfold. intros ? H ;sauto lq:on.
    - set_unfold. intros ? H. sauto lq:on.
    - set_unfold. intros ? H. destruct H as (?&[|]&?);sauto lq:on.
    - set_unfold. intros ? H. sauto lq:on.
    - set_unfold. intros ? H. sauto lq:on.
    - pose proof (coi_subseteq_po _ Hwf Hcs).
      set_unfold. intros ? ?. sauto lq:on.
  Qed.

  Lemma addr_subseteq_po (gr : Candidate.t):
    NMSWF.wf gr ->
    Candidate.addr gr ⊆ Candidate.po gr.
  Proof.
    intros Hwf.
    assert (addr_wf gr) as Haddr_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /addr_wf in Haddr_wf. destruct_and ? Haddr_wf.
    assumption.
  Qed.

  Lemma data_subseteq_po (gr : Candidate.t):
    NMSWF.wf gr ->
    Candidate.data gr ⊆ Candidate.po gr.
  Proof.
    intros Hwf.
    assert (data_wf gr) as Hdata_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /data_wf in Hdata_wf. destruct_and ? Hdata_wf.
    assumption.
  Qed.

  Lemma ctrl_subseteq_po (gr : Candidate.t):
    NMSWF.wf gr ->
    Candidate.ctrl gr ⊆ Candidate.po gr.
  Proof.
    intros Hwf.
    assert (ctrl_wf gr) as Hctrl_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /ctrl_wf in Hctrl_wf. destruct_and ? Hctrl_wf.
    assumption.
  Qed.

  Opaque Candidate.addr Candidate.data Candidate.ctrl.

  Lemma dob_subseteq_po (gr : Candidate.t):
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    dob gr ⊆ Candidate.po gr.
  Proof.
    intros Hwf Hcs.
    rewrite /dob.

    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf. destruct_and ? Hpo_wf.
    clear - H1 Hcs Hwf.
    rewrite grel_transitive_spec in H1.
    rewrite !union_subseteq.
    pose proof (addr_subseteq_po _ Hwf) as Haddr.
    pose proof (data_subseteq_po _ Hwf) as Hdata.
    pose proof (ctrl_subseteq_po _ Hwf) as Hctrl.
    pose proof (coi_subseteq_po _ Hwf Hcs) as Hcoi.
    pose proof (rfi_subseteq_po _ Hwf Hcs) as Hrfi.
    clear Hwf Hcs.

    repeat split.
    - assumption.
    - assumption.
    - set_unfold. intros ? H. sauto lq:on.
    - clear Hdata.

      intros ? H.
      set_unfold.
      cdestruct H.
      destruct H as [|].
      sauto lq: on rew: off l: on q: on.
      cdestruct H.
      (* SLOW *)
      qblast l: on q: on.
    - set_unfold. intros ? H. sauto lq:on.
    - set_unfold. intros ? H. destruct H as (?&[|]&?);sauto lq:on.
    - set_unfold. intros ? H. destruct H as (?&[|]&?);sauto lq:on.
  Qed.

  (* [lob] is in [po] *)
  Lemma lob_subseteq_po gr :
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    lob gr ⊆ po gr.
  Proof.
    intros Hwf Hcs.
    rewrite /lob.
    pose proof (aob_subseteq_po _ Hwf Hcs).
    pose proof (dob_subseteq_po _ Hwf Hcs).
    pose proof (bob_subseteq_po _ Hwf Hcs).
    rewrite 2!union_subseteq.
    repeat split; assumption.
  Qed.

  (* if two events are ordered by [po], then they are in the same (normal) thread *)
  Lemma po_valid_eids gr e1 e2:
    NMSWF.wf gr ->
    (e1, e2) ∈ gr.(Candidate.po) ->
    ({[e1; e2]} ⊆ local_eids gr e1.(EID.tid) ∧ e1.(EID.tid) = e2.(EID.tid) )%nat.
  Proof.
    intros Hwf Hpo.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf.
    destruct_and ? Hpo_wf.
    assert ((e1, e2)∈ same_thread gr).
    { rewrite -H0. set_solver + Hpo. }
    clear - H4.
    set_unfold #UnfoldEidRels.
    split;last sauto.
    intros. destruct H as [<-|<-]; hauto.
  Qed.

  Lemma po_valid_eids' gr e1 e2:
    NMSWF.wf gr ->
    (e1, e2) ∈ gr.(po) ->
    e1 ∈ valid_eid gr ∧ e2 ∈ valid_eid gr.
  Proof.
    intros Hwf Hpo.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf.
    destruct_and ? Hpo_wf.
    assert ((e1, e2)∈ same_thread gr).
    { rewrite -H0. set_solver + Hpo. }

    clear -H4.
    set_unfold #UnfoldEidRels.
    split;last sauto.
    sauto.
  Qed.

  (* if two events are ordered by po, the po earlier has a lower event id *)
  Lemma po_to_pg_lt gr e1 e2:
    NMSWF.wf gr ->
    (e1, e2) ∈ gr.(Candidate.po) ->
    (e1.(EID.iid) < e2.(EID.iid))%nat ∨  (e1.(EID.iid) = e2.(EID.iid) ∧ e1.(EID.ieid) < e2.(EID.ieid))%nat.
  Proof.
    intros Hwf Hpo.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf.
    destruct_and ? Hpo_wf.
    assert ((e1, e2)∈ same_thread gr).
    { rewrite -H0. set_solver + Hpo. }
    specialize (H3 _ Hpo).
    clear -H3.
    destruct H3; hauto.
  Qed.

  (* for two events on the same thread, the one with the lower event id is po before the other *)
  Lemma pg_lt_to_po gr e1 e2:
    NMSWF.wf gr ->
    e1 ∈ Candidate.valid_eid gr ->
    e2 ∈ Candidate.valid_eid gr ->
    e1.(EID.tid) ≠ 0%nat ->
    e1.(EID.tid) = e2.(EID.tid) ->
    (e1.(EID.iid) < e2.(EID.iid))%nat ∨ (e1.(EID.iid) = e2.(EID.iid) ∧ e1.(EID.ieid) < e2.(EID.ieid))%nat ->
    (e1, e2) ∈ gr.(po).
  Proof.
    intros Hwf He1 He2 Hnz Hsth Hpo.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf.
    destruct_and ? Hpo_wf.
    assert ((e1, e2)∈ same_thread gr).
    { set_unfold #UnfoldEidRels. hauto lq:on. }
    apply H5 in H4.
    eapply H4.
    split. naive_solver.
    clear - Hnz. set_unfold. naive_solver lia.
  Qed.

  (* [po] is irreflexive *)
  Lemma po_irreflexive gr e1 e2:
    NMSWF.wf gr ->
    (e1, e2) ∈ gr.(Candidate.po) ->
    (e2, e1) ∈ gr.(Candidate.po) -> False.
  Proof.
    intros Hwf Hpo1 Hpo2.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf.
    destruct_and ? Hpo_wf.
    apply H3 in Hpo1.
    apply H3 in Hpo2.
    destruct Hpo1, Hpo2;
    lia.
  Qed.

  (* [po] is transitive *)
  Lemma po_transitive gr e1 e2 e3:
    NMSWF.wf gr ->
    (e1, e2) ∈ gr.(Candidate.po) ->
    (e2, e3) ∈ gr.(Candidate.po) ->
    (e1, e3) ∈ gr.(Candidate.po).
  Proof.
    intros Hwf Hpo1 Hpo2.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf.
    destruct_and ? Hpo_wf.
    rewrite -H1.
    eapply grel_plus_trans.
    apply grel_plus_once. eassumption.
    apply grel_plus_once. eassumption.
  Qed.

  Lemma rf_dom_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_dom (Candidate.rf gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    assert (rf_wf gr) as Hrf_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /rf_wf in Hrf_wf.
    destruct_and ? Hrf_wf.
    etransitivity. eassumption.
    set_solver +.
  Qed.

  Lemma rf_rng_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_rng (Candidate.rf gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    assert (rf_wf gr) as Hrf_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /rf_wf in Hrf_wf.
    destruct_and ? Hrf_wf.
    etransitivity. rewrite H1. reflexivity.
    set_solver +.
  Qed.

  Lemma co_dom_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_dom (Candidate.co gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    assert (co_wf gr) as Hco_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /co_wf in Hco_wf.
    destruct_and ? Hco_wf.
    etransitivity. eassumption.
    set_solver +.
  Qed.

  Lemma co_rng_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_rng (Candidate.co gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    assert (co_wf gr) as Hco_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /co_wf in Hco_wf.
    destruct_and ? Hco_wf.
    etransitivity. eassumption.
    set_solver +.
  Qed.

  Lemma fr_dom_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_dom (Candidate.fr gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    rewrite /Candidate.fr.
    pose proof (rf_rng_valid gr Hwf).
    set_solver + H.
  Qed.

  Lemma fr_rng_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_rng (Candidate.fr gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    rewrite /Candidate.fr.
    pose proof (co_rng_valid gr Hwf).
    set_solver + H.
  Qed.

  Lemma obs_dom_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_dom (obs gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    pose proof (rf_dom_valid gr Hwf).
    pose proof (fr_dom_valid gr Hwf).
    pose proof (co_dom_valid gr Hwf).
    rewrite /obs.
    set_solver - Hwf.
  Qed.

  Lemma obs_rng_valid gr:
    NMSWF.wf gr ->
    grel_rng (obs gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    pose proof (rf_rng_valid gr Hwf).
    pose proof (fr_rng_valid gr Hwf).
    pose proof (co_rng_valid gr Hwf).
    rewrite /obs.
    set_solver - Hwf.
  Qed.

  Lemma rmw_dom_valid gr:
    NMSWF.wf gr ->
    grel_dom (lxsx gr) ⊆ (valid_eid gr).
  Proof.
    intros Hwf.
    assert (lxsx_wf gr) as Hrmw_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /lxsx_wf in Hrmw_wf.
    destruct_and ? Hrmw_wf.
    etransitivity. eassumption.
    set_solver +.
  Qed.

  Lemma rmw_rng_valid gr:
    NMSWF.wf gr ->
    grel_rng (lxsx gr) ⊆ (valid_eid gr).
  Proof.
    intros Hwf.
    assert (lxsx_wf gr) as Hrmw_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /lxsx_wf in Hrmw_wf.
    destruct_and ? Hrmw_wf.
    etransitivity. eassumption.
    set_solver +.
  Qed.

  Lemma aob_dom_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_dom (aob gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    rewrite /aob.
    pose proof (rmw_rng_valid gr Hwf).
    pose proof (rmw_dom_valid gr Hwf).
    set_solver - Hwf.
  Qed.

  Lemma aob_rng_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_rng (aob gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    rewrite /aob.
    pose proof (rmw_rng_valid gr Hwf).
    pose proof (rmw_dom_valid gr Hwf).
    set_solver - Hwf.
  Qed.

  Lemma data_dom_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_dom (Candidate.data gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    assert (data_wf gr) as Hdata_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /data_wf in Hdata_wf.
    destruct_and ? Hdata_wf.
    etransitivity. eassumption.
    set_solver +.
  Qed.

  Lemma data_rng_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_rng (Candidate.data gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    assert (data_wf gr) as Hdata_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /data_wf in Hdata_wf.
    destruct_and ? Hdata_wf.
    etransitivity. eassumption.
    set_solver +.
  Qed.

  Lemma addr_dom_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_dom (Candidate.addr gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    assert (addr_wf gr) as Haddr_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /addr_wf in Haddr_wf.
    destruct_and ? Haddr_wf.
    etransitivity. eassumption.
    set_solver +.
  Qed.

  Lemma addr_rng_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_rng (Candidate.addr gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    assert (addr_wf gr) as Haddr_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /addr_wf in Haddr_wf.
    destruct_and ? Haddr_wf.
    etransitivity. eassumption.
    unfold mem_events_req.
    set_solver +.
  Qed.

  Lemma ctrl_dom_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_dom (Candidate.ctrl gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    assert (ctrl_wf gr) as Hctrl_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /ctrl_wf in Hctrl_wf.
    destruct_and ? Hctrl_wf.
    etransitivity. eassumption.
    set_solver +.
  Qed.

  Lemma po_dom_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_dom (Candidate.po gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf.
    destruct_and ? Hpo_wf.
    trans (grel_rng (same_thread gr)). rewrite -H0. set_solver +.
    unfold same_thread.
    set_solver +.
  Qed.

  Lemma po_rng_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_rng (Candidate.po gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf.
    destruct_and ? Hpo_wf.
    trans (grel_rng (same_thread gr)). rewrite -H0. set_solver +.
    unfold same_thread.
    set_solver +.
  Qed.

  Lemma ctrl_rng_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_rng (Candidate.ctrl gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    assert (ctrl_wf gr) as Hctrl_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /ctrl_wf in Hctrl_wf.
    destruct_and ? Hctrl_wf.
    pose proof (po_rng_valid gr Hwf).
    etransitivity.
    2: eassumption.
    intro. clear -H1.
    set_unfold;hauto.
  Qed.

  Lemma dob_dom_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_dom (dob gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    rewrite /dob.
    pose proof (data_dom_valid gr Hwf).
    pose proof (ctrl_dom_valid gr Hwf).
    pose proof (addr_dom_valid gr Hwf).
    set_unfold.
    hauto lq: on rew: off.
  Qed.

  Lemma dob_rng_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_rng (dob gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    rewrite /dob.
    pose proof (co_rng_valid gr Hwf).
    pose proof (rf_rng_valid gr Hwf).
    pose proof (data_rng_valid gr Hwf).
    pose proof (addr_rng_valid gr Hwf).
    clear Hwf.

    set_unfold.
    scrush l: on q: on rew: off e: off.
  Qed.

  Lemma bob_dom_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_dom (bob gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    rewrite /bob.
    pose proof (po_dom_valid gr Hwf).
    clear Hwf.

    set_unfold.
    scrush l: on q: on rew: off e: off.
  Qed.

  Lemma bob_rng_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_rng (bob gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    rewrite /bob.
    pose proof (co_rng_valid gr Hwf).
    pose proof (po_rng_valid gr Hwf).
    clear Hwf.
    set_unfold.
    scrush l: on q: on rew: off e: off.
  Qed.


  (* [acq ; po] is in [lob] *)
  Lemma acq_po_subseteq_lob (gr : Candidate.t) e e':
    e ∈ acq_reads gr ->
    (e, e') ∈ po gr ->
    (e, e') ∈ lob gr.
  Proof. set_unfold. hauto lq:on rew:off. Qed.


  (* [ctrl; [w]] is in [lob] *)
  Lemma ctrl_w_subseteq_lob gr e e':
    (e, e') ∈ ctrl gr ->
    e' ∈ mem_writes gr ->
    (e, e') ∈ lob gr.
  Proof.
    intros.
    unfold lob.
    do 2 apply elem_of_union_l.
    unfold dob.
    do 4 apply elem_of_union_l.
    apply elem_of_union_r.
    set_unfold.
    hauto lq: on.
  Qed.

  (* [ctrl; [isb]; po] is in [lob] *)
  Lemma ctrl_isb_po_subseteq_lob (gr : Candidate.t) e e' e'':
    (e, e') ∈ Candidate.ctrl gr ->
    e' ∈ isb gr ->
    (e', e'') ∈ Candidate.po gr ->
    e'' ∈ Candidate.mem_reads gr ->
    (e, e'') ∈ lob gr.
  Proof.
    intros.
    unfold lob.
    do 2 apply elem_of_union_l.
    unfold dob.
    do 3 apply elem_of_union_l.
    apply elem_of_union_r.
    set_unfold.
    hauto lq: on.
  Qed.

  (* [addr] is in [lob] *)
  Lemma addr_subseteq_lob (gr : Candidate.t):
     Candidate.addr gr ⊆ lob gr.
  Proof.
    intros ??.
    rewrite /lob.
    apply elem_of_union_l.
    apply elem_of_union_l.
    rewrite /dob.
    apply elem_of_union_l.
    apply elem_of_union_l.
    apply elem_of_union_l.
    apply elem_of_union_l.
    apply elem_of_union_l.
    apply elem_of_union_r.
    done.
  Qed.

  (* [data] is in [lob] *)
  Lemma data_subseteq_lob (gr : Candidate.t):
    Candidate.data gr ⊆ lob gr.
  Proof.
    intros ??.
    rewrite /lob.
    apply elem_of_union_l.
    apply elem_of_union_l.
    rewrite /dob.
    apply elem_of_union_l.
    apply elem_of_union_l.
    apply elem_of_union_l.
    apply elem_of_union_l.
    apply elem_of_union_l.
    apply elem_of_union_l.
    done.
  Qed.

  Opaque dob.

  (* [po ; rel] is in [lob] *)
  Lemma po_rel_subseteq_lob gr e e':
    (e, e') ∈ po gr ->
    e' ∈ rel_writes gr ->
    (e, e') ∈ lob gr.
  Proof. set_unfold. hauto lq:on rew:off. Qed.

  (* [po ; [dmb_sy]; po] is in [lob] *)
  Lemma po_dmbsy_po_subseteq_lob gr e e' e'':
    (e, e') ∈ po gr ->
    e' ∈ dmb_sy gr ->
    (e', e'') ∈ po gr ->
    (e, e'') ∈ lob gr.
  Proof. set_unfold. hauto lq:on rew:off. Qed.

  Opaque aob bob.

  (* domain of [lob] are valid nodes of the graph *)
  Lemma lob_dom_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_dom (lob gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    rewrite /lob.
    intros Hwf.
    pose proof (dob_dom_valid gr Hwf).
    pose proof (aob_dom_valid gr Hwf).
    pose proof (bob_dom_valid gr Hwf).
    clear Hwf.
    set_unfold.
    scrush l: on q: on rew: off e: off.
  Qed.

  (* range of [lob] are valid nodes of the graph *)
  Lemma lob_rng_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_rng (lob gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    rewrite /lob.
    intros Hwf.
    pose proof (dob_rng_valid gr Hwf).
    pose proof (aob_rng_valid gr Hwf).
    pose proof (bob_rng_valid gr Hwf).

    clear Hwf.
    set_unfold.
    scrush l: on q: on rew: off e: off.
  Qed.

  Opaque lob.

  (* [fre] is in [ob] *)
  Lemma fre_subseteq_ob (gr : Candidate.t) (e e': Eid):
    EID.tid e ≠ EID.tid e' ->
    (e, e') ∈ Candidate.fr gr->
    (e, e') ∈ ob gr.
  Proof.
    intros ??.
    rewrite /ob.
    apply grel_plus_once.
    apply elem_of_union_l.
    rewrite /obs.
    apply elem_of_union_r.
    set_solver.
  Qed.

  (* [rfe] is in [ob] *)
  Lemma rfe_subseteq_ob (gr : Candidate.t) (e e': Eid):
    EID.tid e ≠ EID.tid e' ->
    (e, e') ∈ Candidate.rf gr->
    (e, e') ∈ ob gr.
  Proof.
    intros ??.
    rewrite /ob.
    apply grel_plus_once.
    apply elem_of_union_l.
    rewrite /obs.
    apply elem_of_union_l.
    apply elem_of_union_l.
    set_solver.
  Qed.

  Lemma obs_valid gr e e':
    (e, e') ∈ obs gr ->
    (EID.tid e) ≠ (EID.tid e').
  Proof. set_unfold. sauto. Qed.

  Opaque obs.

  (* domain of [ob] are valid nodes of the graph *)
  Lemma ob_dom_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_dom (ob gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    rewrite /ob.
    rewrite grel_dom_plus.
    intros Hwf.
    pose proof (obs_dom_valid gr Hwf).
    pose proof (lob_dom_valid gr Hwf).
    set_unfold.
    scrush l: on q: on rew: off e: off.
  Qed.

  (* range of [ob] are valid nodes of the graph *)
  Lemma ob_rng_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_rng (ob gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    rewrite /ob.
    rewrite grel_rng_plus.
    intros Hwf.
    pose proof (obs_rng_valid gr Hwf).
    pose proof (lob_rng_valid gr Hwf).

    set_unfold.
    scrush l: on q: on rew: off e: off.
  Qed.

  (* initial writes has no [lob] successors *)
  Lemma no_lob_succ_initial gr e:
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    e ∈ initials gr -> lob_succ_of gr e = ∅.
  Proof.
    intros Hwf Hcs ?.
    assert (initial_wf gr) as Hinit by (rewrite /wf in Hwf;naive_solver).
    rewrite /initial_wf in Hinit.
    destruct_and ? Hinit.
    rewrite /lob_succ_of.
    assert (po_wf gr) as Hpo by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo.
    destruct_and ? Hpo.

    (* clear H8 H11 H0 H1 H3 H4 H5 H6 H2. *)

    assert (grel_rng (filter (λ '(es, _), es = e) (po gr)) = ∅).
    {
      clear -H6 H8 H.
      set_unfold.
      intros. apply Classical_Pred_Type.all_not_not_ex.
      intros. intro.
      destruct H0 as [<- ?].
      assert ((n, x) ∈ same_thread gr).
      {
        apply H6. simpl. left. left;done.
      }
      set_unfold #UnfoldEidRels.
      qauto lq: on.
    }

    pose proof (lob_subseteq_po _ Hwf Hcs).
    set_solver.
  Qed.

  (* initial writes has no [lob] predecessors *)
  Lemma no_lob_pred_initial gr e:
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    e ∈ initials gr -> lob_pred_of gr e = ∅.
  Proof.
    intros Hwf Hcs ?.
    assert (initial_wf gr) as Hinit by (rewrite /wf in Hwf;naive_solver).
    rewrite /initial_wf in Hinit.
    destruct_and ? Hinit.
    rewrite /lob_succ_of.
    assert (po_wf gr) as Hpo by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo.
    destruct_and ? Hpo.
    (* clear Hwf. *)
    (* clear H8 H11 H0 H1 H3 H4 H5 H6 H2. *)

    assert (grel_dom (filter (λ '(_,es), es = e) (po gr)) = ∅).
    {
      clear -H6 H8 H.
      set_unfold.
      intros. apply Classical_Pred_Type.all_not_not_ex.
      intros. intro.
      destruct H0 as [<- ?].
      assert ((n, x) ∈ same_thread gr).
      {
        apply H6. simpl. left. right;done.
      }
      set_unfold #UnfoldEidRels.
      qauto lq: on.
    }

    pose proof (lob_subseteq_po _ Hwf Hcs).
    Local Opaque lob.
    set_solver.
  Qed.

  (* initial writes has no [ob] predecessors *)
  Lemma no_ob_pred_initial_aux gr e:
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    e ∈ Candidate.initials gr -> grel_dom (filter (λ '(_, et), et = e) (obs gr ∪ lob gr)) = ∅ .
  Proof.
    intros Hwf Hcs ?.
    assert (initial_wf gr) as Hinit by (rewrite /wf in Hwf;naive_solver).
    rewrite /initial_wf in Hinit.
    destruct_and ? Hinit.

    pose proof (no_lob_pred_initial gr e Hwf Hcs H) as Hnlob.
    clear H0 H1 H5.
    Transparent obs.

    unfold obs.
    assert (grel_dom (filter (λ '(_, es), es = e) (rf gr)) = ∅).
    {
    rewrite H3 in H.
      assert (rf_wf gr) as Hrf by (rewrite /wf in Hwf;naive_solver).
      rewrite /rf_wf in Hrf. clear Hwf.
      cdestruct Hrf.
      clear -H1 H.
      set_unfold.
      specialize (H1 e).
      intros ? [? [-> ?]].
      destruct H1 as [Hrf_rng _].
      ospecialize* Hrf_rng. eexists;eassumption.
      cdestruct Hrf_rng, H.
      inversion'.
    }

    assert (grel_dom (filter (λ '(_, es), es = e) (co gr)) = ∅).
    {
      assert (co_wf gr) as Hco by (rewrite /wf in Hwf;naive_solver).
      rewrite /co_wf in Hco. clear Hwf.
      cdestruct Hco.
      clear -H H9.
      set_unfold.
      intros ? [? [-> Hco]].
      eapply H9.
      split;[eassumption|].
      done.
    }

    rewrite 3!filter_union_L.
    Local Opaque lob.
    clear H3 H2 H.
    set_solver.
  Qed.


  Lemma no_ob_pred_initial gr e:
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    e ∈ Candidate.initials gr -> grel_dom (filter (λ '(_, et), et = e) (ob gr)) = ∅ .
  Proof.
    intros Hwf Hcs Hi.
    Local Opaque lob obs.
    unfold ob. set_unfold. intros.
    intros [? [<- Hin]].
    revert Hi.
    cinduction Hin using grel_plus_cind_r.
    {
      intros.
      pose proof (no_ob_pred_initial_aux gr y Hwf Hcs).
      set_unfold in H0.
      ospecialize * H0. assumption.
      eexists. split;[reflexivity|].
      set_unfold in H. eassumption. assumption.
    }
    {
      intros.
      pose proof (no_ob_pred_initial_aux gr z Hwf Hcs).
      set_unfold in H2.
      ospecialize * H2. assumption.
      eexists. split;[reflexivity|].
      set_unfold in H0. eassumption. assumption.
    }
  Qed.

  (* [ob] predecessors of [e] is its [lob] predecessors disjoint union its [obs] predecessors *)
  Lemma ob_pred_of_disj_union (gr : Candidate.t) (e : Eid):
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    lob_pred_of gr e ∪ obs_pred_of gr e ⊆ ob_pred_of gr e
    ∧ lob_pred_of gr e ## obs_pred_of gr e.
  Proof.
    intros Hwf Hcs.
    rewrite /ob_pred_of /lob_pred_of /obs_pred_of.
    Local Opaque obs.
    set_unfold.
    split.
    - intros ? [];
      eexists; (split;first reflexivity);
      apply grel_plus_once;set_solver.
    - intros ? [? [-> ?]] [? [-> ?]].
      apply (lob_subseteq_po _ Hwf Hcs) in H.
      apply (po_valid_eids _ _ _ Hwf) in H.
      destruct H.
      apply obs_valid in H0.
      contradiction.
  Qed.


  (* [ob] successors of [e] is its [lob] successors disjoint union its [obs] successors *)
  Lemma ob_succ_of_disj_union (gr : Candidate.t) (e : Eid):
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    lob_succ_of gr e ∪ obs_succ_of gr e ⊆ ob_succ_of gr e
    ∧ lob_succ_of gr e ## obs_succ_of gr e.
  Proof.
    intros Hwf Hcs.
    rewrite /ob_succ_of /lob_succ_of /obs_succ_of.
    rewrite /ob. set_unfold.
    split.
    - intros ? [];
      eexists; (split;first reflexivity);
      apply grel_plus_once;set_solver.
    - intros ? [? [-> ?]] [? [-> ?]].
      apply (lob_subseteq_po _ Hwf Hcs) in H.
      apply (po_valid_eids _ _ _ Hwf) in H.
      destruct H.
      apply obs_valid in H0.
      contradiction.
  Qed.

  (* [ob] is acyclic *)
  Lemma ob_acyclic (gr : Candidate.t) (e : Eid):
    AAConsistent.t gr -> (e, e) ∉ ob gr.
  Proof. intros [_ ?]. set_solver. Qed.

  (* initial events are writes with value 0 *)
  Lemma init_zero (gr : Candidate.t) (e : Eid):
    NMSWF.wf gr ->
    e.(EID.tid) = 0%nat ->
    ∀ v, (exists E, gr !! e = Some E ∧ get_mem_value E = Some v) -> v = (BV 64 0).
  Proof.
    intros Hwf ???.
    assert (initial_wf gr) as Hinit_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /initial_wf in Hinit_wf.
    destruct_and ? Hinit_wf.
    clear - H H3 H0 H4 Hwf.
    assert (size8_wf gr) as Hsize_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /size8_wf in Hsize_wf.
    clear Hwf.
    assert (e ∈ initials gr). set_unfold. set_solver.
    assert (e ∈ initial_writes gr). set_solver.
    apply H3 in H1.
    unfold is_valid_init_mem_write in H1.
    cdestruct H0.
    rewrite H0 /= in H1.
    set_unfold in H2.
    cdestruct H2.
    inversion'.
    rewrite H5 /= in H1.
    cdestruct H1 #CDestrEqOpt.
    rewrite H1.
    simpl in H5.
    inversion'.
    simpl.

    set_unfold in Hsize_wf.
    specialize (Hsize_wf e).
    simpl in H1.
    destruct (decide (x1 = 8)%N).
    subst x1.
    assert (8*8 = 64)%N as -> by lia.
    clear.
    rewrite bvn_eq.
    split.
    simpl. lia.
    unfold bvn_unsigned.
    unfold CBitvector.bvn_unsigned.
    simpl.
    rewrite <-(@bv_0_unsigned 64).
    done.

    exfalso.
    apply Hsize_wf.
    eexists;split;first eassumption.
    simpl.
    clear -n.

    repeat destruct x1 as [|x1];[try done|].
    destruct x1;try done.
    destruct x1;try done.
    destruct x1;try done.
    destruct x1;try done.
  Qed.

  (* initial writes are [co] initial *)
  Lemma init_co (gr : Candidate.t) (e e': Eid) (a : Addr):
    NMSWF.wf gr ->
    e.(EID.tid) = 0%nat ->
    e'.(EID.tid) ≠ 0%nat ->
    (exists E, gr !! e = Some E ∧ is_mem_write_req E ∧ get_pa E = Some a) ->
    (exists E, gr !! e' = Some E ∧ is_mem_write_req E ∧ get_pa E = Some a) ->
    (e, e') ∈ co gr.
  Proof.
    intros Hwf ? Hnz [?[]] [?[]].
    assert (initial_wf gr) as Hinit_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /initial_wf in Hinit_wf.
    destruct_and ? Hinit_wf.

    assert (e ∈ initials gr). set_unfold. set_solver + H0 H.
    cdestruct H1, H3.

    assert ((e, e') ∈ same_pa gr) as Hloc.
      {
        clear H7 H8 H6 H4 H9 H5. set_unfold.
        subst.
        hauto lq:on.
      }
      assert (co_wf gr) as Hco_wf by (rewrite /wf in Hwf;naive_solver).
      rewrite /co_wf in Hco_wf.
      destruct_and ? Hco_wf.
      assert ((e, e') ∈ same_pa gr ∩ (mem_writes_req gr × mem_writes_req gr)).
      {
        clear H13 H14 H15 H16 H17 H19 H11 H4 H6 H7 H8 H9.
        apply elem_of_intersection.
        split;first assumption.
        set_unfold. subst.
        naive_solver.
      }
      rewrite H17 in H18.

      apply elem_of_union in H18.
      destruct H18.
      2:{ set_unfold in H18. set_solver + H18 H Hnz. }
      apply elem_of_union in H18.
      destruct H18. assumption.
      set_unfold in H18.
      set_solver + H19 H18 H8.
  Qed.

  Lemma rf_rmw_co gr (eid_w eid_xr eid_xw : EID.t):
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    (eid_w, eid_xr) ∈ rf gr ->
    (eid_xr, eid_xw) ∈ lxsx gr ->
    (eid_w, eid_xw) ∈ co gr.
  Proof.
    intros Hwf Hcs Hrf Hrmw.
    assert (co_wf gr) as Hco_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /co_wf in Hco_wf.
    destruct_and ? Hco_wf.
    assert (rf_wf gr) as Hrf_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /rf_wf in Hrf_wf.
    destruct_and ? Hrf_wf.
    assert (lxsx_wf gr) as Hrmw_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /lxsx_wf in Hrmw_wf.
    destruct_and ? Hrmw_wf.
    assert ((eid_w, eid_xr) ∈ same_pa gr). apply H10 in Hrf. set_solver + Hrf.
    assert ((eid_xr, eid_xw) ∈ same_pa gr). apply H11 in Hrmw. set_solver + Hrmw.
    assert ((eid_w, eid_xw) ∈ same_pa gr). set_solver + H17 H19.
    assert (eid_w ∈ mem_writes_req gr).
    {
      (* assert (mem_wf gr) as Hmem_wf by (rewrite /wf in Hwf;naive_solver). *)
      (* rewrite /mem_wf in Hmem_wf. *)
      set_solver + Hrf H5.
    }
    assert (eid_xw ∈ mem_writes_atomic gr). apply H15. set_solver + Hrmw.
    assert (eid_xw ∈ mem_writes_req gr). {
      clear - H22. set_unfold.
      cdestruct H22.
      naive_solver.
      }
    assert ((eid_w, eid_xw) ∈ same_pa gr ∩ (mem_writes_req gr × mem_writes_req gr)).
    { clear - H20 H21 H23. set_unfold. hauto. }

    rewrite H4 in H24. apply elem_of_union in H24.
    assert ((eid_xr, eid_xw) ∈ po gr ∩ same_pa gr).
    {
      apply elem_of_intersection.
      split. apply H13. assumption. assumption.
    }
    destruct Hcs.
    unfold grel_acyclic in internal0.
    rewrite grel_irreflexive_spec in internal0.
    destruct H24.
    {
      apply elem_of_union in H24. destruct H24. assumption.
      exfalso.
      clear - H25 Hrf H24 internal0.
      specialize (internal0 (eid_w, eid_w)). simpl in internal0.
      apply internal0;last reflexivity.
      apply (grel_plus_trans _ _ eid_xr).
      apply grel_plus_once. set_solver + Hrf.
      apply (grel_plus_trans _ _ eid_xw).
      apply grel_plus_once. set_solver + H25.
      apply grel_plus_once. set_solver + H24.
    }
    {
      exfalso.
      clear - H25 Hrf H24 internal0.
      specialize (internal0 (eid_w, eid_w)). simpl in internal0.
      apply internal0;last reflexivity.
      apply (grel_plus_trans _ _ eid_xr).
      apply grel_plus_once. set_solver + Hrf.
      apply grel_plus_once. set_solver + H24 H25.
    }
  Qed.

  (* There can only be a single successful rmw read from any write *)
  Lemma rmw_rmw gr (eid_w eid_xr eid_xr' eid_xw eid_xw' : Eid):
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    eid_xr ≠ eid_xr' ->
    (eid_w, eid_xr) ∈ rf gr ->
    (eid_xr, eid_xw) ∈ lxsx gr ->
    (eid_w, eid_xr') ∈ rf gr ->
    (eid_xr', eid_xw') ∈ lxsx gr ->
    False.
  Proof.
    intros Hwf Hcs Hnst Hrf Hrmw Hrf' Hrmw'.
    assert (co_wf gr) as Hco_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /co_wf in Hco_wf.
    destruct_and ? Hco_wf.
    assert (rf_wf gr) as Hrf_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /rf_wf in Hrf_wf.
    destruct_and ? Hrf_wf.
    assert (lxsx_wf gr) as Hrmw_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /lxsx_wf in Hrmw_wf.
    destruct_and ? Hrmw_wf.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf.
    destruct_and ? Hpo_wf.
    assert ((eid_w, eid_xw) ∈ co gr) as Hco.
    {
      eapply (rf_rmw_co _ eid_w eid_xr); eassumption.
    }
    assert ((eid_w, eid_xw') ∈ co gr) as Hco'.
    {
      eapply (rf_rmw_co _ eid_w eid_xr'); eassumption.
    }
    assert (EID.tid eid_xr ≠ EID.tid eid_xr').
    {
      intros Hst.
      assert ((eid_xr', eid_xw') ∈ po gr). apply H13. assumption.
      assert ((eid_xr, eid_xw) ∈ po gr). apply H13. assumption.
      assert (eid_xr ∈ mem_reads_atomic gr) as Hxr. apply H14. set_solver + Hrmw.
      assert (eid_xr' ∈ mem_reads_atomic gr) as Hxr'. apply H14. set_solver + Hrmw'.
      assert ((eid_xr, eid_xr') ∈ same_thread gr). clear - Hst Hxr Hxr'. set_unfold #UnfoldEidRels. cdestruct Hxr, Hxr'. hauto lq:on.

      assert (eid_xw ∈ mem_writes_atomic gr) as Hxw. apply H15. set_solver + Hrmw.
      assert (eid_xw' ∈ mem_writes_atomic gr) as Hxw'. apply H15. set_solver + Hrmw'.
      assert ((eid_xw, eid_xr') ∈ same_thread gr).
      {
        assert ((eid_xr, eid_xw) ∈ same_thread gr). rewrite -H19. set_solver + H25.
        clear - H27 H26. set_unfold #UnfoldEidRels. sauto.
      }
      assert ((eid_xw', eid_xr) ∈ same_thread gr).
      {
        assert ((eid_xr', eid_xw') ∈ same_thread gr). rewrite -H19. set_solver + H23.
        clear - H26 H28. set_unfold #UnfoldEidRels. sauto.
      }
      rewrite -H19 in H26. rewrite -H19 in H27. rewrite -H19 in H28.
      (* set_solver + Hst Hxr Hxr'. *)
      apply elem_of_union in H26. destruct H26.
      2:{
        assert (eid_xr ∈ initials gr). set_solver + H26.
        assert (initial_wf gr) as Hinitial_wf by (rewrite /wf in Hwf;naive_solver).
        rewrite /initial_wf in Hinitial_wf.
        destruct_and ? Hinitial_wf.
        rewrite H33 in H29.
        clear -H29 Hxr.
        set_unfold. cdestruct Hxr, H29. inversion'.
      }
      apply elem_of_union in H27. destruct H27.
      2:{
        assert (eid_xw ∈ Candidate.initials gr). set_solver + H27.
        assert (initial_wf gr) as Hinitial_wf by (rewrite /wf in Hwf;naive_solver).
        rewrite /initial_wf in Hinitial_wf.
        destruct_and ? Hinitial_wf.
        specialize (H32 _ H29).
        rewrite H33 in H29.

        clear -H29 Hxw H32.
        set_unfold. cdestruct Hxw, H29, H32.
        unfold mem_standalone, mem_relaxed in H4.
        set_unfold in H4.
        unfold mem_exclusive in H0.
        unfold mem_by_kind in H0, H4.

        set_unfold in H4. set_unfold in H0.
        cdestruct H0. cdestruct H4.
        inversion'. inversion'.
        simpl in H5, H6.
        unfold is_mem_event_kindP in H5, H6.
        cdestruct H5, H6 #CDestrMatch;try done.
        destruct m. destruct e. simpl in H5, H6.
        all: naive_solver.
      }
      apply elem_of_union in H28. destruct H28.
      2:{
        assert (eid_xr ∈ initials gr). set_solver + H28.
        assert (initial_wf gr) as Hinitial_wf by (rewrite /wf in Hwf;naive_solver).
        rewrite /initial_wf in Hinitial_wf.
        destruct_and ? Hinitial_wf.
        rewrite H33 in H29.
        clear -H29 Hxr.

        set_unfold. cdestruct Hxr, H29. inversion'.
      }
      apply elem_of_union in H26. destruct H26.
      {
        apply elem_of_union in H27. destruct H27.
        {
          (* internal *)
          assert ((eid_xr', eid_xw) ∈ fr gr).
          set_solver + Hrf' Hco.
          assert ((eid_xw, eid_xr') ∈ po gr ∩ same_pa gr).
          apply elem_of_intersection.  split. assumption.
          apply H10 in Hrf'.
          apply H0 in Hco.
          set_solver + Hrf' Hco.
          destruct Hcs.
          unfold grel_acyclic in internal0.
          rewrite grel_irreflexive_spec in internal0.
          clear - H30 H29 internal0.
          specialize (internal0 (eid_xw, eid_xw)). simpl in internal0.
          apply internal0;last reflexivity.
          apply (grel_plus_trans _ _ eid_xr').
          apply grel_plus_once. set_solver + H30.
          apply grel_plus_once. set_solver + H29.
        }
        {
          assert ((eid_xr, eid_xw) ∈ ⦗mem_reads_atomic gr⦘ ⨾ po gr ⨾ ⦗mem_reads_atomic gr⦘ ⨾ po gr
           ⨾ ⦗mem_writes_atomic gr⦘).
          clear - H26 H27 Hxr Hxr' Hxw.
          set_unfold. sauto lq:on.
          set_solver + H29 Hrmw H18.
        }
      }
      {
        apply elem_of_union in H28. destruct H28.
        {
          (* internal *)
          assert ((eid_xr, eid_xw') ∈ fr gr).
          set_solver + Hrf Hco'.
          assert ((eid_xw', eid_xr) ∈ po gr ∩ same_pa gr).
          apply elem_of_intersection.  split. assumption.
          apply H10 in Hrf.
          apply H0 in Hco'.
          set_solver + Hrf Hco'.
          destruct Hcs.
          unfold grel_acyclic in internal0.
          rewrite grel_irreflexive_spec in internal0.
          clear - H30 H29 internal0.
          specialize (internal0 (eid_xw', eid_xw')). simpl in internal0.
          apply internal0;last reflexivity.
          apply (grel_plus_trans _ _ eid_xr).
          apply grel_plus_once. set_solver + H30.
          apply grel_plus_once. set_solver + H29.
        }
        {
          assert ((eid_xr', eid_xw') ∈ ⦗mem_reads_atomic gr⦘ ⨾ Candidate.po gr ⨾ ⦗mem_reads_atomic gr⦘ ⨾ po gr
           ⨾ ⦗mem_writes_atomic gr⦘).
          clear - H26 H28 Hxr Hxr' Hxw'.
          set_unfold. sauto lq:on.
          set_solver + H29 Hrmw' H18.
        }
      }
    }

    assert ((eid_xr', eid_xw) ∈ external_of (fr gr)) as Hfr.
    {
      assert ((eid_xr, eid_xw) ∈ po gr). apply H13. assumption.
      assert ((eid_xr, eid_xw) ∈ same_thread gr). rewrite -H19. set_solver + H25.
      clear - Hco Hrf' H26 H23.
      set_unfold #UnfoldEidRels. sauto.
    }
    assert ((eid_xr, eid_xw') ∈ external_of (fr gr)) as Hfr'.
    {
      assert ((eid_xr', eid_xw') ∈ po gr). apply H13. assumption.
      assert ((eid_xr', eid_xw') ∈ same_thread gr). rewrite -H19. set_solver + H25.
      clear - Hco' Hrf H26 H23.
      set_unfold #UnfoldEidRels. sauto.
    }
    assert ((eid_xw, eid_xw') ∈ same_pa gr) as Hloc.
    {
      apply H11 in Hrmw'.
      apply H10 in Hrf'.
      assert ((eid_w, eid_xw) ∈ same_pa gr).
      {
        assert ((eid_w, eid_xw) ∈ co gr ∪ (co gr) ⁻¹ ∪ ⦗mem_writes_req gr⦘). set_solver + Hco.
        rewrite -H4 in H25.
        set_solver + H25.
      }
      set_solver + H25 Hrmw' Hrf'.
    }
    assert ((eid_xw, eid_xw') ∈ co gr ∪ (co gr) ⁻¹ ∪ ⦗mem_writes_req gr⦘).
    {
      rewrite -H4.
      apply elem_of_intersection.
      split. set_solver + Hloc.
      clear - Hco Hco' H3.
      set_unfold. pose proof (H3 eid_xw).
      pose proof (H3 eid_xw'). clear H3.
      hauto lq:on.
    }
    assert (EID.tid (eid_xw) ≠ EID.tid (eid_xw')).
    {
      intros Heq.
      assert ((eid_xr, eid_xw) ∈ po gr). apply H13. assumption.
      assert ((eid_xr, eid_xw) ∈ same_thread gr). rewrite -H19. set_solver + H26.
      assert ((eid_xr', eid_xw') ∈ po gr). apply H13. assumption.
      assert ((eid_xr', eid_xw') ∈ same_thread gr). rewrite -H19. set_solver + H28.
      clear - H27 H29 H23 Heq.
      set_unfold #UnfoldEidRels. sauto lq:on.
    }
    apply elem_of_union in H25.
    destruct H25.
    2:{
      set_solver + H25 H26.
    }
    apply elem_of_union in H25.
    destruct Hcs.
    destruct H25.
    {
      assert ((eid_xw, eid_xw') ∈ Candidate.external_of (Candidate.co gr)). set_solver + H26 H25.
      assert ((eid_xr', eid_xw') ∈ (Candidate.external_of (Candidate.fr gr))⨾(Candidate.external_of (Candidate.co gr))). set_solver + H27 Hfr.
      set_solver + atomic0 H28 Hrmw'.
    }
    {
      assert ((eid_xw', eid_xw) ∈ Candidate.external_of (Candidate.co gr)).
      set_solver + H25 H26.
      assert ((eid_xr, eid_xw) ∈ (Candidate.external_of (Candidate.fr gr))⨾(Candidate.external_of (Candidate.co gr))).
      {
        set_solver + H27 Hfr'.
      }
      set_solver + atomic0 H28 Hrmw.
    }
  Qed.

  (** End of axioms *)

  Lemma lob_acyclic (gr : Candidate.t) (e : Eid):
    AAConsistent.t gr -> (e, e) ∉ lob gr.
  Proof.
    intros Hcs. pose proof (ob_acyclic _ e Hcs).
    clear Hcs.
    rewrite /ob in H.
    intro.
    apply H.
    apply grel_plus_once.
    set_solver.
  Qed.

  Lemma lob_subseteq_ob(gr : Candidate.t):
    lob gr ⊆ ob gr.
  Proof.
    intros.
    rewrite /ob.
    set_unfold.
    intros.
    apply grel_plus_once.
    destruct x.
    set_solver.
  Qed.

  Lemma lob_pred_of_subseteq_po (gr : Candidate.t) (e : Eid) :
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    lob_pred_of gr e ⊆ po_pred_of gr e.
  Proof.
   rewrite /lob_pred_of /po_pred_of.
   intros Hwf Hcs e' Hin.
   pose proof (lob_subseteq_po _ Hwf Hcs).
   set_solver - Hwf Hcs.
  Qed.

  Lemma collect_all_subseteq gr P Q:
    (∀ e ev, P e ev = true -> Q e ev = true) ->
      Candidate.collect_all P gr ⊆ Candidate.collect_all Q gr.
  Proof.
    intros Himpl e Hin. set_unfold.
    destruct Hin as [? [? ?]].
    eexists. split;eauto.
    rewrite Is_true_true. apply Himpl.
    rewrite -Is_true_true //.
  Qed.

  Lemma not_elem_of_lob_pred_of (gr : Candidate.t) (e : Eid):
    AAConsistent.t gr -> e ∉ lob_pred_of gr e.
  Proof.
    intro Hcs. pose proof (lob_acyclic _ e Hcs). set_solver.
  Qed.

  Lemma not_elem_of_lob_succ_of (gr : Candidate.t) (e : Eid) :
    AAConsistent.t gr ->
    e ∉ lob_succ_of gr e.
  Proof.
    intro Hcs. pose proof (lob_acyclic _ e Hcs). set_solver.
  Qed.

  Lemma elem_of_lob_pred_of_po (gr : Candidate.t) (e1 e2 : Eid) :
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    e2 ∈ lob_pred_of gr e1 ->
    (e2, e1) ∈ gr.(Candidate.po).
  Proof.
    intros Hwf Hcs Hpred. epose proof (lob_pred_of_subseteq_po _ e1 Hwf Hcs). set_solver - Hwf Hcs.
  Qed.

  (** Some helpers *)
  Lemma elem_of_lob_pred_of_lob (gr : Candidate.t) (e1 e2 : Eid) :
    e2 ∈ lob_pred_of gr e1 ->
    (e2, e1) ∈ (lob gr).
  Proof.
    intros. rewrite /lob_pred_of in H. set_solver.
  Qed.

  Lemma elem_of_ob_pred_of (gr : Candidate.t) (e e': Eid) :
    e' ∈ ob_pred_of gr e -> (e', e) ∈ (ob gr).
  Proof. set_solver. Qed.

  Lemma ob_pred_of_valid (gr : Candidate.t) (e : Eid) :
    NMSWF.wf gr ->
    ob_pred_of gr e ⊆ Candidate.valid_eid gr.
  Proof.
    intros Hwf.
    rewrite /ob_pred_of. pose proof (ob_dom_valid _ Hwf).
    set_solver - Hwf.
  Qed.

  Lemma elem_of_obs_pred_of_succ (gr : Candidate.t) (e e': Eid) :
    e' ∈ obs_pred_of gr e <-> e ∈ obs_succ_of gr e'.
  Proof. set_solver. Qed.

  Lemma elem_of_lob_pred_of_succ (gr : Candidate.t) (e e': Eid) :
    e' ∈ lob_pred_of gr e <-> e ∈ lob_succ_of gr e'.
  Proof. set_solver. Qed.

  Lemma elem_of_ob_pred_of_succ (gr : Candidate.t) (e e': Eid) :
    e' ∈ ob_pred_of gr e <-> e ∈ ob_succ_of gr e'.
  Proof. set_solver. Qed.

  Lemma lob_succ_of_subseteq_ob (gr : Candidate.t) (e : Eid):
    lob_succ_of gr e ⊆ ob_succ_of gr e.
  Proof.
    intros. pose proof lob_subseteq_ob. set_solver.
  Qed.

  Lemma elem_of_ob_succ_of_valid (gr : Candidate.t) (e e': Eid) :
    NMSWF.wf gr ->
    e' ∈ ob_succ_of gr e -> {[e'; e]} ⊆ Candidate.valid_eid gr.
  Proof.
    intros Hwf.
    pose proof (ob_dom_valid _ Hwf). pose proof (ob_rng_valid _ Hwf).
    rewrite -elem_of_ob_pred_of_succ.
    intro. assert ((e,e') ∈ ob gr). set_solver - Hwf.
    set_solver - Hwf.
  Qed.

  Lemma elem_of_lob_succ_of_valid (gr : Candidate.t) (e e': Eid) :
    NMSWF.wf gr ->
    e' ∈ lob_succ_of gr e -> {[e'; e]} ⊆ Candidate.valid_eid gr.
  Proof.
    intros Hwf.
    pose proof lob_subseteq_ob.
    intro. assert ((e,e') ∈ ob gr). set_solver - Hwf.
    pose proof (ob_dom_valid _ Hwf). pose proof (ob_rng_valid _ Hwf).
    set_solver - Hwf.
  Qed.

  Lemma elem_of_ob_succ_of_ne gr e e':
    AAConsistent.t gr ->
    e' ∈ ob_succ_of gr e -> e ≠ e'.
  Proof.
    pose proof ob_acyclic. set_solver.
  Qed.

  Lemma elem_of_ob_pred_of_ne gr e e':
    AAConsistent.t gr ->
    e' ∈ ob_pred_of gr e -> e ≠ e'.
  Proof.
    pose proof ob_acyclic. set_solver.
  Qed.

  Lemma lob_same_thd gr e e':
    AAConsistent.t gr →
    wf gr ->
    e' ∈ lob_succ_of gr e -> e' ∈ Candidate.non_initial_eids gr.
  Proof.
    rewrite -elem_of_lob_pred_of_succ.
    intros Hc Hwf ?.
    assert ((e,e') ∈ lob gr). set_solver - Hwf.
    assert ((e,e') ∈ Candidate.po gr).
    pose proof (lob_subseteq_po _ Hwf). set_solver - Hwf.
    assert (po_wf gr) as Hpo by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo.
    destruct_and ? Hpo.
    assert ((e, e')∈ same_thread gr).
    { rewrite -H3. set_solver + H1. }
    clear Hwf.

    set_unfold. specialize (H5 (e,e')).
    set_unfold in H7  #UnfoldEidRels .
    cdestruct H7.

    unfold valid_eid.
    set_unfold.

    split;first naive_solver.
    intro.
    rewrite -H10 in H11.
    apply H5.
    split;first assumption.
    rewrite -H10.
    naive_solver.
  Qed.

End Graph.
