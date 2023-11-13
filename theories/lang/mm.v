(* This file contains the memory model *)


From SSCCommon Require Import Common CSets GRel.

Require Import ISASem.SailArmInstTypes.

Require Import stdpp.prelude.
Require Import stdpp.unstable.bitvector.

Require Export self.lang.machine.

Require Import ssreflect.

Open Scope stdpp_scope.


Ltac match_inversion :=
  repeat (match goal with
          | [ HH : Some _ = None |- _ ] => inversion HH
          | [ HH : None = Some _ |- _ ] => inversion HH
          | [ HH : false |- _ ] => inversion HH
          | [ HH : Some ?x = Some _ |- _ ] => inversion HH;subst x;clear HH
          | _  => case_match
          end).

Module AAConsistent.

  Import AACandExec.
  Import AACandExec.Candidate.
  Export ISASem.SailArmInstTypes.

  Definition event_is_isb (event: Event) :=
    match event with
    | AAInter.IEvent (AAInter.Barrier AAArch.ISB) _ => true
    | _ => false end.

  Definition isbs (cd : t) :=
    collect_all event_is_isb cd.

  #[local] Instance dmb_kind_eqdec : (EqDecision AAArch.dmb_kind).
  Proof. intros ??. destruct x, y; try (left;done);right;done. Qed.

  Definition event_is_dmb (κ: AAArch.dmb_kind) (event: Event) :=
    match event with
    | AAInter.IEvent (AAInter.Barrier (AAArch.DMB κ')) _ => (bool_decide (κ=κ'))
    | _ => false end.

  Definition dmbs (cd : t) (κ: AAArch.dmb_kind) :=
    collect_all (event_is_dmb κ) cd.

  Definition value_of_wreq {n} (req: AAInter.WriteReq.t n) :=
   req.(AAInter.WriteReq.value).

  Definition addr_of_wreq {n} (req: AAInter.WriteReq.t n) :=
   req.(AAInter.WriteReq.pa).

  (* This is annoying since the interface allows writing arbitraty bytes to memory, we have
   to make sure the number of bytes is [AAArch.val_size]*)
  Program Definition addr_and_value_of_wreq {n} (req: AAInter.WriteReq.t n) :
    option (Addr * Val).
  destruct req as [].
  destruct (decide (n = AAArch.val_size)).
  {
    subst n.
    exact (Some (pa,value)).
  }
  exact None.
  Defined.

  Definition addr_of_rreq {n} (req: AAInter.ReadReq.t n) : Addr := req.(AAInter.ReadReq.pa).

  Program Definition value_of_read (event : Event) : option Val.
  destruct event as [? []].
  exact None.
  exact None.
  destruct t1; last exact None.
  destruct p.
  destruct (decide (n = AAArch.val_size)).
  {
    subst n.
    exact (Some b).
  }
  all : exact None.
  Defined.

  (** write *)
  Definition event_is_write_with_P (event : Event) (P : ∀ n : N, AAInter.WriteReq.t n -> bool) :=
    match event with
    | AAInter.IEvent (AAInter.MemWrite n wreq) wresp => wreq_is_valid wreq && wresp_is_valid wresp && P n wreq
    | _ => false end.
  #[global] Hint Unfold event_is_write_with_P : all.

  Definition event_is_pln_write (event : Event) :=
   event_is_write_with_P event (λ _ wreq, kind_of_wreq_P wreq
                                            (λ κ, bool_decide (κ = (Build_Explicit_access_kind AV_plain AS_normal)))).
  #[global] Hint Unfold event_is_pln_write : all.

  Definition event_is_rel (event : Event) :=
   event_is_write_with_P event (λ _ wreq, kind_of_wreq_P wreq
                 (λ κ, bool_decide (κ.(Explicit_access_kind_strength) = AS_rel_or_acq))).
  #[global] Hint Unfold event_is_rel : all.

  Definition event_is_xcl_write (event : Event) :=
    event_is_write_with_P event (λ _ wreq,
                                   (* kind_of_wreq_P wreq *)
                                   (*          (λ κ, bool_decide (Explicit_access_kind_strength κ= AS_normal)) *)
                                   (* && *)
                                   kind_of_wreq_is_atomic wreq).
  #[global] Hint Unfold event_is_xcl_write : all.

  Definition event_is_write_with (event : Event) (ks : Access_strength) (kv : Access_variety) (a : Addr) (v : Val) :=
   event_is_write_with_P event (λ _ wreq, kind_of_wreq_P wreq
                                            (λ κ, bool_decide (κ = (Build_Explicit_access_kind kv ks))) &&
                                   bool_decide (addr_and_value_of_wreq wreq = Some (a,v))).
  #[global] Hint Unfold event_is_write_with : all.

  Definition event_is_write_with_addr (event : Event) (a : Addr) :=
    event_is_write_with_P event (λ _ wreq, bool_decide (addr_of_wreq wreq = a)).
  #[global] Hint Unfold event_is_write_with_addr : all.

  Definition event_is_write_with_kind (event : Event) (ks : Access_strength) (kv : Access_variety) :=
    event_is_write_with_P event (λ _ wreq,
                                   kind_of_wreq_P wreq (λ κ, bool_decide (κ = (Build_Explicit_access_kind kv ks)))).
  #[global] Hint Unfold event_is_write_with_kind : all.

  Definition event_is_write (event : Event) :=
    event_is_write_with_P event (λ _ _, true).
  #[global] Hint Unfold event_is_write : all.

  Lemma event_is_write_with_elem_of_mem_writes {gr} (e : Eid) (event : Event) (ks : Access_strength)
    (kv : Access_variety) (a : Addr) (v : Val) :
    gr !! e = Some event ->
    event_is_write_with event ks kv a v ->
    e ∈ AACandExec.Candidate.mem_writes gr.
  Proof.
    intros Hlk Hw. set_unfold. unfold event_is_write_with in Hw.
    unfold event_is_write_with_P in Hw.
    case_match;case_match; try contradiction.
    rewrite bool_unfold in Hw.
    destruct_and? Hw.
    unfold wreq_is_valid. unfold kind_of_wreq_P in H1.
    sauto.
  Qed.

  Lemma event_is_write_elem_of_mem_writes {gr} (e : Eid) (event : Event) (a : Addr) :
    gr !! e = Some event ->
    event_is_write_with_addr event a ->
    e ∈ AACandExec.Candidate.mem_writes gr.
  Proof.
    intros Hlk Hw. set_unfold. unfold event_is_write_with in Hw.
    unfold event_is_write_with_addr, event_is_write_with_P in Hw.
    case_match;case_match; try contradiction.
    rewrite bool_unfold in Hw.
    destruct_and? Hw.
    unfold wreq_is_valid.
    sauto.
  Qed.

  Lemma mem_wf_spec_write gr:
    NMSWF.mem_wf gr ->
    forall eid event,
    gr !! eid = Some event ->
    eid ∈ mem_writes gr ->
    event_is_write event.
  Proof.
    intros Hwf ?? Hlk Hw.
    unfold event_is_write, event_is_write_with_P.
    set_unfold. destruct Hw as (?&?&?&?).
    rewrite Hlk in H.
    match_inversion;subst.
    rewrite /NMSWF.mem_wf in Hwf.
    rewrite bool_unfold in Hwf.
    set_unfold.
    specialize (Hwf eid).
    rewrite bool_unfold. left.
    eapply (Classical_Pred_Type.not_ex_all_not _ _ ) in Hwf.
    Unshelve. 2: exact ((AAInter.IEvent (AAInter.MemWrite x x0) x1)).
    eapply not_and_l in Hwf.
    Unshelve. 2:{ left. done. }
    destruct Hwf. done.
    rewrite bool_unfold in H.
    destruct (decide ((wreq_is_valid x0 ∧ wresp_is_valid x1))).
    done. apply H in n. done.
  Qed.


  Lemma event_is_write_elem_of_mem_writes2 {gr} (e : Eid) :
    NMSWF.wf gr ->
    e ∈ AACandExec.Candidate.mem_writes gr ->
    ∃  (event : Event), gr !! e = Some event ∧ event_is_write event.
  Proof.
    intros Hwf Hin. set_unfold.
    assert (NMSWF.mem_wf gr).
    { rewrite /NMSWF.wf in Hwf. naive_solver. }

    destruct Hin as [? [? [? HE]]].

    pose proof (mem_wf_spec_write gr H e _ HE).
    feed specialize H0.
    set_unfold. do 3 eexists. eassumption.
    eexists. split;eauto.
  Qed.

  Lemma event_is_write_with_addr_elem_of_mem_writes {gr} (e : Eid) (event : Event) (a : Addr) :
    gr !! e = Some event ->
    event_is_write_with_addr event a ->
    e ∈ AACandExec.Candidate.mem_writes gr.
  Proof.
    intros Hlk Hw. set_unfold.
    destruct event;auto;destruct o;auto;try inversion Hw.
    simpl in Hw. repeat eexists;eauto.
  Qed.

  Lemma event_is_write_with_addr_elem_of_mem_writes2 {gr} (e : Eid) :
    NMSWF.wf gr ->
    e ∈ AACandExec.Candidate.mem_writes gr ->
    ∃  (event : Event) (a : Addr), gr !! e = Some event ∧ event_is_write_with_addr event a.
  Proof.
    intros Hwf Hin. set_unfold.
    assert (NMSWF.mem_wf gr).
    { rewrite /NMSWF.wf in Hwf. naive_solver. }
    destruct Hin as [? [? [? HE]]].
    pose proof (mem_wf_spec_write gr H e _ HE). feed specialize H0. set_unfold. do 3 eexists. eassumption.
    eexists. exists (addr_of_wreq x0). split;eauto.
    simpl. rewrite bool_unfold. simpl in H0. rewrite bool_unfold in H0. clear H HE.
    naive_solver.
  Qed.

  Lemma event_is_write_with_P_impl (event : Event) (P Q : ∀ n : N, AAInter.WriteReq.t n -> bool) :
    (forall n wreq, P n wreq -> Q n wreq) ->
    event_is_write_with_P event P -> event_is_write_with_P event Q.
  Proof.
   intros Himp HP. destruct event;auto;destruct o;auto. simpl in *.
   rewrite ->bool_unfold in *; split; naive_solver.
  Qed.

  Lemma event_is_write_with_impl_addr (event : Event) (ks : Access_strength) (kv : Access_variety)
    (a : Addr) (v : Val) :
    event_is_write_with event ks kv a v -> event_is_write_with_addr event a.
  Proof.
    apply event_is_write_with_P_impl.
    intros.
    repeat rewrite ->bool_unfold in *.
    simpl. unfold addr_and_value_of_wreq in H. destruct H as [_ H].
    case_match;auto.
    case_match;auto.
    unfold eq_rec_r, eq_rec in H. subst n.
    rewrite <-Classical_Prop.Eq_rect_eq.eq_rect_eq in H.
    inversion H. done. done.
  Qed.

  Lemma event_is_write_with_impl_kind (e : Eid) (event : Event) (ks : Access_strength) (kv : Access_variety) (a : Addr) (v : Val) :
    event_is_write_with event ks kv a v -> event_is_write_with_kind event ks kv.
  Proof.
    apply event_is_write_with_P_impl.
    intros. unfold kind_of_wreq_P in *.
    rewrite -> bool_unfold in *.
    hauto lq:on.
  Qed.

  (** read *)
  Definition event_is_read_with_P (event : Event) (P : ∀ n : N, AAInter.ReadReq.t n -> bool) :=
    match event with
    | AAInter.IEvent (AAInter.MemRead n rreq) rresp => rreq_is_valid rreq && rresp_is_valid rresp && P n rreq
    | _ => false end.
  #[global] Hint Transparent event_is_read_with_P : all.

  Definition event_is_read (event : Event) :=
    event_is_read_with_P event (λ _ _, true).

  Definition event_is_pln_read (event : Event) :=
    event_is_read_with_P event (λ _ rreq, kind_of_rreq_P rreq (λ κ, bool_decide (κ = (Build_Explicit_access_kind AV_plain AS_normal)))).

  Definition event_is_acq (event : Event) :=
    event_is_read_with_P event (λ _ rreq, kind_of_rreq_P rreq (λ κ, bool_decide (κ = (Build_Explicit_access_kind AV_plain AS_rel_or_acq)))).

  Definition event_is_xcl_read (event : Event) :=
    event_is_read_with_P event (λ _ rreq, kind_of_rreq_P rreq (λ κ, bool_decide ((Explicit_access_kind_strength κ = AS_normal)))
                                          && kind_of_rreq_is_atomic rreq).

  Definition event_is_wacq (event : Event) :=
    event_is_read_with_P event (λ _ rreq, kind_of_rreq_P rreq (λ κ, bool_decide (κ = (Build_Explicit_access_kind AV_plain AS_acq_rcpc)))).

  Definition event_is_read_with (event : Event) (ks : Access_strength) (kv : Access_variety) (a : Addr) (v : Val) :=
    event_is_read_with_P event (λ _ rreq,
                                  kind_of_rreq_P rreq (λ κ, bool_decide (κ = (Build_Explicit_access_kind kv ks))) &&
                                    bool_decide (addr_of_rreq rreq = a) &&
                                    bool_decide (value_of_read event = Some v)
      ).

  Definition event_is_read_with_kind (event : Event) (ks : Access_strength) (kv : Access_variety) :=
    event_is_read_with_P event (λ _ rreq,
        bool_decide(kind_of_rreq_P rreq (λ κ, bool_decide (κ = Build_Explicit_access_kind kv ks)))).

  Definition event_is_read_with_addr (event : Event) (a : Addr) :=
    event_is_read_with_P event (λ _ rreq, bool_decide (addr_of_rreq rreq = a)).

  Lemma mem_wf_spec_read gr:
    NMSWF.mem_wf gr ->
    forall eid event,
    gr !! eid = Some event ->
    eid ∈ mem_reads gr ->
    event_is_read event.
  Proof.
    intros Hwf ?? Hlk Hw.
    unfold event_is_read, event_is_read_with_P.
    set_unfold. destruct Hw as (?&?&?&?).
    rewrite Hlk in H.
    match_inversion;subst.
    rewrite /NMSWF.mem_wf in Hwf.
    rewrite bool_unfold in Hwf.
    set_unfold.
    specialize (Hwf eid).
    rewrite bool_unfold. left.
    eapply (Classical_Pred_Type.not_ex_all_not _ _ ) in Hwf.
    Unshelve. 2: exact ((AAInter.IEvent (AAInter.MemRead x x0) x1)).
    eapply not_and_l in Hwf.
    Unshelve. 2:{ left. done. }
    destruct Hwf. done.
    rewrite bool_unfold in H.
    destruct (decide ((rreq_is_valid x0 ∧ rresp_is_valid x1))).
    done. apply H in n. done.
  Qed.

  Lemma event_is_read_with_P_impl (event : Event) (P Q : ∀ n : N, AAInter.ReadReq.t n -> bool) :
    (forall n rreq, P n rreq -> Q n rreq) ->
    event_is_read_with_P event P -> event_is_read_with_P event Q.
  Proof.
   intros Himp HP. destruct event;auto;destruct o;auto. simpl in *.
   rewrite ->bool_unfold in *; split; naive_solver.
  Qed.

  Lemma event_is_read_with_impl_addr (e : Eid) (event : Event) (ks : Access_strength) (kv : Access_variety) (a : Addr) (v : Val) :
    event_is_read_with event ks kv a v -> event_is_read_with_addr event a.
  Proof.
    apply event_is_read_with_P_impl.
    intros. unfold kind_of_wreq_P in *.
    repeat rewrite -> bool_unfold in *.
    hauto lq:on.
  Qed.


  Lemma event_is_read_with_impl_kind (e : Eid) (event : Event) (ks : Access_strength) (kv : Access_variety) (a : Addr) (v : Val) :
    event_is_read_with event ks kv a v -> event_is_read_with_kind event ks kv.
  Proof.
    apply event_is_read_with_P_impl.
    intros. unfold kind_of_wreq_P in *.
    repeat rewrite ->bool_unfold in *.
    hauto lq:on.
  Qed.

  Definition rel_writes (cd : t) :=
    collect_all event_is_rel cd.

  Definition acq_reads (cd : t) :=
    collect_all event_is_acq cd.

  Definition wacq_reads (cd : t) :=
    collect_all event_is_wacq cd.

  Definition pln_writes (cd : t) :=
    collect_all event_is_pln_write cd.

  Definition pln_reads (cd : t) :=
    collect_all event_is_pln_read cd.

  Definition xcl_reads (cd : t) :=
    collect_all event_is_xcl_read cd.

  Definition xcl_writes (cd : t) :=
    collect_all event_is_xcl_write cd.

  Definition dob (cd : t) : Rel :=
    let writes := mem_writes cd in
    let reads := mem_reads cd in
    let isb := isbs cd in
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

  Definition bob (cd : t) : Rel :=
    let po := cd.(po) in
    let dmb_sy := dmbs cd (AAArch.Sy) in
    let dmb_ld := dmbs cd (AAArch.Ld) in
    let dmb_st := dmbs cd (AAArch.St) in
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
    let rmw := (rmw cd) in
    let acq := acq_reads cd in
    let wacq := wacq_reads cd in
    rmw ∪ (⦗grel_rng rmw⦘⨾ rfi⨾ (⦗wacq⦘∪⦗acq⦘)).

  Definition lob (cd : t) : Rel := (dob cd) ∪ (aob cd) ∪ (bob cd).

  Definition ob (cd : t) : Rel := ((obs cd) ∪ (lob cd))⁺.

  Definition ind_lob (cd : t) : Rel := (internal_of (ob cd)).

  Definition ca (cd : t) : Rel := (fr cd) ∪ (co cd).

  Record t cd := {
      internal : grel_acyclic (((po cd) ∩ (loc cd)) ∪ (ca cd) ∪ (rf cd));
      external : grel_irreflexive (ob cd);
      atomic : bool_decide (((rmw cd) ∩ ((external_of (fr cd))⨾(external_of (co cd)))) = ∅);
    }.

End AAConsistent.

(* memory graph *)
Module Graph.
  Export AACandExec.
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
  (** Below are axiomised results about the consistency and well-formedness of execution graphs *)

  (** well-formedness *)
  (* if two events are related by the auxilary [loc] relation and one is a write on [addr],
     then the other must be a read or write on [addr] as well *)
  Lemma wf_loc_inv_writes {gr} eid_w eid addr:
    NMSWF.wf gr ->
    (exists E1, gr !! eid_w = Some E1 ∧ event_is_write_with_addr E1 addr) ->
    (eid_w, eid) ∈ AACandExec.Candidate.loc gr ->
    (exists E2, gr !! eid = Some E2 ∧ (event_is_write_with_addr E2 addr ∨ event_is_read_with_addr E2 addr)).
  Proof.
    rewrite /event_is_write_with_addr /event_is_read_with_addr /wf.
    intros Hwf Hlk Hloc.
    assert (NMSWF.mem_wf gr) as Hmwf by naive_solver. clear Hwf.

    destruct Hlk as (?&Hlk&?).
    set_unfold.
    destruct Hloc as (?&?&?&Hlk'&?&?&?).
    rewrite Hlk in Hlk'. inversion Hlk';subst;clear Hlk'.
    eexists. split;first eassumption.

    rewrite /event_is_write_with_P in H.
    match_inversion;try contradiction;rewrite bool_unfold in H;subst;simpl in H2;match_inversion.

    destruct_and ? H.
    simpl in H0. inversion H0;subst x2. rewrite /addr_of_wreq in H4. rewrite H4 in H2. clear H4 H5 H Hlk H0.

    rewrite /Candidate.get_pa in H2.
    match_inversion;try contradiction;subst;simpl.
    pose proof (mem_wf_spec_read _ Hmwf eid _ H1).
    feed specialize H. set_unfold. do 3 eexists. eassumption.
    right. rewrite bool_unfold. inversion H2;subst addr.
    simpl in H. rewrite bool_unfold in H. naive_solver.

    left. rewrite bool_unfold. inversion H2;subst addr.
    pose proof (mem_wf_spec_write _ Hmwf eid _ H1).
    feed specialize H. set_unfold. do 3 eexists. eassumption.
    simpl in H. rewrite bool_unfold in H. naive_solver.
  Qed.

  (* two writes on the same address are ordered by [loc] *)
  Lemma wf_loc_inv_writes2 {gr} eid_w eid:
    (exists addr E1 E2, gr !! eid_w = Some E1 ∧ event_is_write_with_addr E1 addr ∧ gr !! eid = Some E2 ∧ event_is_write_with_addr E2 addr) ->
    (eid_w, eid) ∈ AACandExec.Candidate.loc gr.
  Proof.
    rewrite /event_is_write_with_addr /event_is_write_with_P.
    intros (?&?&?&?&?&?&?).
    set_unfold.
    match_inversion;try contradiction;rewrite bool_unfold in H0;subst;simpl in H2;match_inversion.
    rewrite bool_unfold in H2. destruct H0,H2.
    do 2 eexists. exists x.
    rewrite /Candidate.get_pa.
    rewrite /addr_of_wreq in H3. rewrite /addr_of_wreq in H4.
    split;first eassumption.
    simpl. split. f_equal. done. split;first eassumption.
    simpl. f_equal. done.
  Qed.

  (* in a well-formed graph, a read event [e] must read the value [val] from a write event on the same address [addr],
    (is ordered by [rf]) *)
  Lemma wf_read_inv gr e E addr kind_s kind_v val:
    wf gr ->
    gr !! e = Some E ->
    AAConsistent.event_is_read_with E kind_s kind_v addr val ->
    ∃ eid_w kind_s_w kind_s_v E_w,
      gr !! eid_w = Some E_w ∧
      AAConsistent.event_is_write_with E_w kind_s_w kind_s_v addr val ∧
      (eid_w, e) ∈ AACandExec.Candidate.rf gr.
  Proof.
    rewrite /event_is_read_with /event_is_read_with_P /wf.
    intros Hwf Hlk Hread.
    assert (rf_wf gr) as Hwf_rf by naive_solver;rewrite /rf_wf in Hwf_rf.
    assert (mem_wf gr) as Hwf_mem by naive_solver;clear Hwf.
    rewrite bool_unfold in Hwf_rf.
    destruct_and ? Hwf_rf.

    repeat case_match;try contradiction.
    destruct_and ? Hread.
    assert (Hin : e ∈ grel_rng (Candidate.rf gr)).
    { rewrite H3. set_unfold. repeat eexists. eassumption. }
    set_unfold in Hin. destruct Hin as [e_w Hrf].
    exists e_w. specialize (H e_w). feed specialize H. set_solver + Hrf.
    set_unfold in H. destruct H as (?&?&?&?).
    (* rewrite bool_unfold in H5. destruct H5 as [? ?]. rewrite /Candidate.wreq_is_valid in H5. *)
    (* case_match; try contradiction. destruct e0. *)
    specialize (H0 (e_w,e) Hrf).
    set_unfold in H0.


    destruct H0 as [(?&?&?&Hlk1&?&Hlk2&?) (?&?&?&Hlk1'&?&Hlk2'&?)].
    rewrite Hlk1 in Hlk1'. rewrite Hlk2 in Hlk2'.
    inversion Hlk1';subst x5;clear Hlk1'.
    inversion Hlk2';subst x6;clear Hlk2'.
    rewrite Hlk1 in H. rewrite Hlk2 in Hlk.
    inversion H;subst x2;clear H. inversion Hlk;subst x3;clear Hlk.

    pose proof (mem_wf_spec_write _ Hwf_mem _ _ Hlk1).
    feed specialize H.
    set_unfold. do 3 eexists. eassumption. simpl in H. rewrite bool_unfold in H. destruct H as [[ ? ?] |];last done.
    rewrite /Candidate.wreq_is_valid in H.
    match_inversion;[| contradiction | contradiction | contradiction ].
    destruct e0.


    repeat eexists. eassumption. rewrite /event_is_write_with /event_is_write_with_P.
    do 2 pattern_evar. setoid_rewrite bool_unfold.
    split;auto. split;auto. rewrite /Candidate.wreq_is_valid. hauto lq:on.
    split. rewrite /Candidate.kind_of_wreq_P. rewrite H14.
    do 2 pattern_evar. setoid_rewrite bool_unfold. reflexivity.
    rewrite /addr_and_value_of_wreq.

    case_match eqn:HE.

    2:assumption.

    (* reasoning about val_size is painful, also there seems to be redundant conditions  *)
    destruct (decide (x = AAArch.val_size)).
    {
      rewrite /eq_rec_r. rewrite /eq_rec. subst. simpl.
      f_equal.

      destruct t0. destruct p. simpl in H9.
      simpl in H12.
      simpl in H5. simpl in H0.


      match_inversion.
      inversion H5;subst x4.
      apply pair_eq.
      rewrite /addr_of_rreq.
      split;first reflexivity.

      rewrite /eq_rect_r in H9.
      rewrite <-Classical_Prop.Eq_rect_eq.eq_rect_eq in H9.
      match_inversion.
      simpl in H11.
      inversion H11;done.
      simpl in H9.
      match_inversion.
    }
    {
      destruct t0. destruct p. simpl in H11.
      match_inversion.
      rewrite /AAArch.val_size in n0. lia.
      simpl in H11.
      match_inversion.
      rewrite /AAArch.val_size in n0. lia.
    }
  Qed.

  (* in a well formed graph, a read reads from only one write *)
  Lemma wf_read_single gr w w' r:
    wf gr ->
    Graph.is_rf gr w r ->
    Graph.is_rf gr w' r ->
    w = w'.
  Proof.
    intros Hwf Hrf1 Hrf2.
    rewrite /wf in Hwf.
    assert (rf_wf gr) as Hwf_rf by naive_solver;rewrite /rf_wf in Hwf_rf.
    rewrite bool_unfold in Hwf_rf.
    destruct_and ? Hwf_rf.
    set_unfold.
    rewrite grel_functional_spec in H2.
    eapply H2.
    rewrite grel_inv_spec. eassumption.
    rewrite grel_inv_spec. eassumption.
  Qed.


  (* well-formed [rfi] is included in [po] *)
  Lemma wf_rfi_inv {gr} eid_w eid:
    wf gr ->
    AAConsistent.t gr ->
    Graph.is_rf gr eid_w eid ->
    (EID.tid eid_w) = (EID.tid eid) ->
    (eid_w, eid) ∈ AACandExec.Candidate.po gr.
  Proof.
    intros Hwf Hcs Hrf Hsth.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf. destruct_and ? Hpo_wf.
    assert (rf_wf gr) as Hrf_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /rf_wf in Hrf_wf. destruct_and ? Hrf_wf.
    assert (initial_wf gr) as Hinitial_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /initial_wf in Hinitial_wf. destruct_and ? Hinitial_wf.
    assert (eid_w ∈ Candidate.mem_writes gr) as Hw. set_solver + Hrf H1.
    assert (eid ∈ Candidate.non_initial_eids gr).
    {
      clear H11 H13 H10 H2 H8.
      assert (eid ∈ Candidate.mem_reads gr). rewrite -H9. set_solver + Hrf.
      assert (eid ∉ Candidate.mem_writes_pln_zero gr).
      clear -H2. set_unfold. destruct H2 as (?&?&?&?).
      apply Classical_Pred_Type.all_not_not_ex.
      intros. intros [].
      rewrite H in H0;inversion H0;subst n. contradiction.
      clear - H7 H14 H2.
      set_unfold.
      split. set_unfold. sauto lq:on.
      intros Heq.
      set_unfold.
      specialize (H14 eid). feed specialize H14. sauto lq:on.
      clear H2.
      sauto.
    }
    assert ((eid_w, eid) ∈ Candidate.sthd gr).
    { clear - Hsth H7 Hw. set_unfold. set_unfold. sauto. }
    rewrite -H4 in H15.
    apply elem_of_union in H15. destruct H15.
    2:{
      clear - H7 H15. exfalso. set_unfold. hauto lq:on.
    }
    apply elem_of_union in H15. destruct H15. assumption.
    exfalso.
    assert ((eid_w,eid) ∈ Candidate.loc gr). apply H6 in Hrf. set_solver + Hrf.
    assert ((eid,eid_w) ∈ Candidate.loc gr). set_solver + H16.
    assert ((eid,eid_w) ∈ Candidate.po gr ∩ Candidate.loc gr). set_solver + H15 H17.
    destruct Hcs.
    exfalso.
    rewrite grel_irreflexive_spec in internal0.
    clear - H18 Hrf internal0.
    specialize (internal0 (eid, eid)). simpl in internal0.
    apply internal0;last reflexivity.
    apply (grel_plus_trans _ _ eid_w);
    apply grel_plus_once.

    set_solver + H18.
    set_solver + Hrf.
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
    assert (eid_w ∈ Candidate.mem_writes gr) as Hw. set_solver + Hco H10.
    assert (eid ∈ Candidate.non_initial_eids gr).
    {
      clear -Hco H6 H9.
      assert (eid ∈ Candidate.mem_writes gr). set_solver + Hco H9.
      set_unfold.
      split.
      set_unfold. sauto lq:on.
      intros Heq.
      set_unfold.
      specialize (H6 (eid_w,eid)).
      sauto lq:on.
    }
    assert ((eid_w, eid) ∈ Candidate.sthd gr).
    { clear - Hsth H1 Hw. set_unfold. set_unfold. sauto. }
    rewrite -H4 in H18.
    apply elem_of_union in H18. destruct H18.
    2:{
      clear - H1 H18. exfalso. set_unfold. hauto lq:on.
    }
    apply elem_of_union in H18. destruct H18. assumption.
    exfalso.
    assert ((eid_w,eid) ∈ Candidate.co gr ∪ (Candidate.co gr) ⁻¹ ∪ ⦗Candidate.mem_writes gr⦘).
    set_solver + Hco.
    rewrite -H8 in H19.
    assert ((eid_w,eid) ∈ Candidate.loc gr). set_solver + H19.
    assert ((eid,eid_w) ∈ Candidate.loc gr). set_solver + H20.
    assert ((eid,eid_w) ∈ Candidate.po gr ∩ Candidate.loc gr). set_solver + H18 H21.
    destruct Hcs.
    exfalso.
    rewrite grel_irreflexive_spec in internal0.
    clear - H22 Hco internal0.
    specialize (internal0 (eid, eid)). simpl in internal0.
    apply internal0;last reflexivity.
    apply (grel_plus_trans _ _ eid_w);
    apply grel_plus_once.

    set_solver + H22.
    set_solver + Hco.
  Qed.


  (* two writes on the same location are ordered by [coi] if ordered by [po] *)
  Lemma wf_coi_inv {gr} eid_w eid:
    wf gr ->
    AAConsistent.t gr ->
    (eid_w, eid) ∈ AACandExec.Candidate.loc gr ->
    {[eid_w; eid]} ⊆ AACandExec.Candidate.mem_writes gr ->
    (eid_w, eid) ∈ AACandExec.Candidate.po gr ->
    (eid_w, eid) ∈ AACandExec.Candidate.co gr.
  Proof.
    intros Hwf Hcs Hloc Hw Hpo.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf. destruct_and ? Hpo_wf.
    assert (co_wf gr) as Hco_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /co_wf in Hco_wf. destruct_and ? Hco_wf.
    assert ((eid_w, eid) ∈ Candidate.loc gr ∩ (Candidate.mem_writes gr × Candidate.mem_writes gr)).
    set_solver + Hw Hloc.
    rewrite H8 in H1.
    apply elem_of_union in H1.
    destruct H1.
    2:{
      exfalso. apply H2 in Hpo. clear - H1 Hpo. set_unfold. destruct H1 as [_ ?].
      destruct eid_w, eid. simpl in *. inversion H. subst. lia.
    }
    apply elem_of_union in H1.
    destruct H1;first assumption.
    assert ((eid_w,eid) ∈ Candidate.po gr ∩ Candidate.loc gr). set_solver + Hpo Hloc.
    destruct Hcs. exfalso.
    rewrite grel_irreflexive_spec in internal0.
    clear - H13 H1 internal0.
    specialize (internal0 (eid_w, eid_w)). simpl in internal0.
    apply internal0;last reflexivity.
    apply (grel_plus_trans _ _ eid);
    apply grel_plus_once.

    set_solver + H13.
    set_solver + H1.
  Qed.

  Lemma rfi_subseteq_po gr:
    wf gr ->
    AAConsistent.t gr ->
    Candidate.internal_of (Candidate.rf gr) ⊆ Candidate.po gr.
  Proof.
    intros Hwf Hcs. intros r Hin.
    pose proof (wf_rfi_inv r.1 r.2 Hwf Hcs).
    set_unfold in Hin.
    apply H;hauto lq:on.
  Qed.

  Lemma aob_subseteq_po (gr : Candidate.t):
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    aob gr ⊆ Candidate.po gr.
  Proof.
    intros Hwf Hcs.
    rewrite /aob.
    assert (rmw_wf gr) as Hrmw_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /rmw_wf in Hrmw_wf.
    destruct_and ? Hrmw_wf.

    apply union_subseteq.
    split. assumption.
    pose proof (rfi_subseteq_po _ Hwf Hcs).
    clear - H1.
    intros ??.
    assert (x ∈ Candidate.internal_of (Candidate.rf gr)).
    clear H1.
    apply grel_seq_spec in H.
    destruct H as (?&?&?). destruct x. assert (x0 = t1) as ->. set_solver + H0.
    apply grel_seq_spec in H.
    destruct H as (?&?&?). assert (t0 = x) as ->. set_solver + H.
    done.
    set_solver + H0 H1.
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
    bob gr ⊆ Candidate.po gr.
  Proof.
    intros Hwf Hcs.
    rewrite /bob.

    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf. destruct_and ? Hpo_wf.
    clear H0 H2 H3 H4 H.
    rewrite grel_transitive_spec in H5.
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
    clear H0 H2 H3 H4 H.
    rewrite grel_transitive_spec in H5.
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
    - clear Hdata. set_unfold. intros ? H. destruct H as (?&(?&(?&[|]&?)&?)&?). sauto lq: on rew: off l: on q: on. qblast l: on q: on.
    - set_unfold. intros ? H. sauto lq:on.
    - set_unfold. intros ? H. destruct H as (?&[|]&?);sauto lq:on.
    - set_unfold. intros ? H. destruct H as (?&[|]&?);sauto lq:on.
  Qed.


  (* [lob] is in [po] *)
  Lemma lob_subseteq_po (gr : Candidate.t):
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    lob gr ⊆ Candidate.po gr.
  Proof.
    intros Hwf Hcs.
    rewrite /lob.

    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf. destruct_and ? Hpo_wf.
    clear H0 H2 H3 H4 H.
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
    rewrite bool_unfold in Hpo_wf.
    destruct_and ? Hpo_wf.
    assert ((e1, e2)∈ Candidate.sthd gr).
    { rewrite -H4. set_solver + Hpo. }
    set_unfold in H1.
    clear H H2 H3 H4 H5 Hwf.
    set_unfold.
    destruct H1 as (?&?&?&?&?&?&?).
    split;last sauto.
    intros. destruct H4 as [<-|<-]; hauto.
  Qed.

  Lemma po_valid_eids' gr e1 e2:
    NMSWF.wf gr ->
    (e1, e2) ∈ gr.(Candidate.po) ->
    e1 ∈ Candidate.valid_eid gr ∧ e2 ∈ Candidate.valid_eid gr.
  Proof.
    intros Hwf Hpo.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf.
    rewrite bool_unfold in Hpo_wf.
    destruct_and ? Hpo_wf.
    assert ((e1, e2)∈ Candidate.sthd gr).
    { rewrite -H4. set_solver + Hpo. }
    set_unfold in H1.
    clear H H2 H3 H4 H5 Hwf.
    set_unfold.
    destruct H1 as (?&?&?&?&?&?&?).
    sauto.
  Qed.

  (* if two events are ordered by po, the po earlier has a lower event id *)
  Lemma po_to_pg_lt gr e1 e2:
    NMSWF.wf gr ->
    (e1, e2) ∈ gr.(Candidate.po) ->
    (e1.(EID.iid) < e2.(EID.iid))%nat ∨  (e1.(EID.iid) = e2.(EID.iid) ∧ e1.(EID.num) < e2.(EID.num))%nat.
  Proof.
    intros Hwf Hpo.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf.
    rewrite bool_unfold in Hpo_wf.
    destruct_and ? Hpo_wf.
    assert ((e1, e2)∈ Candidate.sthd gr).
    { rewrite -H4. set_solver + Hpo. }
    set_unfold in H1.
    specialize (H2 _ Hpo).
    clear H0 H H3 H4 H1 Hwf.
    destruct H2; hauto.
  Qed.

  (* for two events on the same thread, the one with the lower event id is po before the other *)
  Lemma pg_lt_to_po gr e1 e2:
    NMSWF.wf gr ->
    e1 ∈ Candidate.valid_eid gr ->
    e2 ∈ Candidate.valid_eid gr ->
    e1.(EID.tid) ≠ 0%nat ->
    e1.(EID.tid) = e2.(EID.tid) ->
    (e1.(EID.iid) < e2.(EID.iid))%nat ∨ (e1.(EID.iid) = e2.(EID.iid) ∧ e1.(EID.num) < e2.(EID.num))%nat ->
    (e1, e2) ∈ gr.(Candidate.po).
  Proof.
    intros Hwf He1 He2 Hnz Hsth Hpo.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf.
    rewrite bool_unfold in Hpo_wf.
    destruct_and ? Hpo_wf.
    assert ((e1, e2)∈ Candidate.sthd gr).
    { set_unfold. hauto lq:on. }
    rewrite -H4 in H1.
    set_unfold in H1.
    destruct H1.
    destruct H1. assumption.
    apply H2 in H1. simpl in H1. lia.
    simpl in H1. destruct H1 as (?&?&?). lia.
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
    rewrite bool_unfold in Hpo_wf.
    destruct_and ? Hpo_wf.
    apply H2 in Hpo1.
    apply H2 in Hpo2.
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
    rewrite bool_unfold in Hpo_wf.
    destruct_and ? Hpo_wf.
    rewrite H5.
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
    rewrite bool_unfold in Hrf_wf.
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
    rewrite bool_unfold in Hrf_wf.
    destruct_and ? Hrf_wf.
    etransitivity. rewrite H3. reflexivity.
    set_solver +.
  Qed.

  Lemma co_dom_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_dom (Candidate.co gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    assert (co_wf gr) as Hco_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /co_wf in Hco_wf.
    rewrite bool_unfold in Hco_wf.
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
    rewrite bool_unfold in Hco_wf.
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

  Lemma obs_rng_valid (gr : Candidate.t):
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

  Lemma rmw_dom_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_dom (Candidate.rmw gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    assert (rmw_wf gr) as Hrmw_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /rmw_wf in Hrmw_wf.
    rewrite bool_unfold in Hrmw_wf.
    destruct_and ? Hrmw_wf.
    etransitivity. eassumption.
    set_solver +.
  Qed.

  Lemma rmw_rng_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_rng (Candidate.rmw gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    assert (rmw_wf gr) as Hrmw_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /rmw_wf in Hrmw_wf.
    rewrite bool_unfold in Hrmw_wf.
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
    rewrite bool_unfold in Hdata_wf.
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
    rewrite bool_unfold in Hdata_wf.
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
    rewrite bool_unfold in Haddr_wf.
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
    rewrite bool_unfold in Haddr_wf.
    destruct_and ? Haddr_wf.
    etransitivity. eassumption.
    set_solver +.
  Qed.

  Lemma ctrl_dom_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_dom (Candidate.ctrl gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    assert (ctrl_wf gr) as Hctrl_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /ctrl_wf in Hctrl_wf.
    rewrite bool_unfold in Hctrl_wf.
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
    rewrite bool_unfold in Hpo_wf.
    destruct_and ? Hpo_wf.
    trans (grel_rng (Candidate.sthd gr)). rewrite -H4. set_solver +.
    set_solver +.
  Qed.

  Lemma po_rng_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_rng (Candidate.po gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf.
    rewrite bool_unfold in Hpo_wf.
    destruct_and ? Hpo_wf.
    trans (grel_rng (Candidate.sthd gr)). rewrite -H4. set_solver +.
    set_solver +.
  Qed.

  Lemma ctrl_rng_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_rng (Candidate.ctrl gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    assert (ctrl_wf gr) as Hctrl_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /ctrl_wf in Hctrl_wf.
    rewrite bool_unfold in Hctrl_wf.
    destruct_and ? Hctrl_wf.
    pose proof (po_rng_valid gr Hwf).
    etransitivity.
    2: eassumption.
    intro. clear Hwf H1 H0 H.
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
    rewrite !grel_dom_union.
    rewrite !union_subseteq.
    split. 2: etrans;[apply grel_seq_dom|].
    split. 2: etrans;[apply grel_seq_dom|].
    split. 2: etrans;[apply grel_seq_dom|etrans;[apply grel_seq_dom|]].
    split. 2: etrans;[apply grel_seq_dom|etrans;[apply grel_seq_dom|etrans;[apply grel_seq_dom|]]].
    split. 2: etrans;[apply grel_seq_dom|].
    split. all: rewrite ?grel_dom_union.
    all: try assumption.
    rewrite !union_subseteq.
    split. 2: etrans;[apply grel_seq_dom|].
    all: try assumption; rewrite !union_subseteq;split;try assumption.
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
    rewrite !grel_rng_union.
    rewrite !union_subseteq.
    split. 2: etrans;[apply grel_seq_rng|].
    split. 2: etrans;[apply grel_seq_rng|].
    split. 2: etrans;[apply grel_seq_rng|].
    split. 2: etrans;[apply grel_seq_rng|].
    split. 2: etrans;[apply grel_seq_rng|].
    split. all: set_solver - Hwf.
  Qed.

  Lemma bob_dom_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_dom (bob gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    rewrite /bob.
    pose proof (po_dom_valid gr Hwf).
    rewrite !grel_dom_union.
    rewrite !union_subseteq.
    split. 2: etrans;[apply grel_seq_dom|etrans;[apply grel_seq_dom|]].
    split. 2: etrans;[apply grel_seq_dom|].
    split. 2: etrans;[apply grel_seq_dom|etrans;[apply grel_seq_dom|etrans;[apply grel_seq_dom|etrans;[apply grel_seq_dom|]]]].
    split. 2: etrans;[apply grel_seq_dom|].
    split. 2: etrans;[apply grel_seq_dom|etrans;[apply grel_seq_dom|etrans;[apply grel_seq_dom|]]].
    split. 2: etrans;[apply grel_seq_dom|etrans;[apply grel_seq_dom|]].
    etrans;[apply grel_seq_dom|etrans;[apply grel_seq_dom|]].

    all: rewrite ?grel_dom_union.
    all: try assumption.
    all: rewrite ?union_subseteq;try split.
    all: set_solver - Hwf.
  Qed.

  Lemma bob_rng_valid (gr : Candidate.t):
    NMSWF.wf gr ->
    grel_rng (bob gr) ⊆ (Candidate.valid_eid gr).
  Proof.
    intros Hwf.
    rewrite /bob.
    pose proof (co_rng_valid gr Hwf).
    pose proof (po_rng_valid gr Hwf).
    rewrite !grel_rng_union.
    rewrite !union_subseteq.
    split. 2: etrans;[apply grel_seq_rng|].
    split. 2: etrans;[apply grel_seq_rng|].
    split. 2: etrans;[apply grel_seq_rng|].
    split. 2: etrans;[apply grel_seq_rng|].
    split. 2: etrans;[apply grel_seq_rng|].
    split. 2: etrans;[apply grel_seq_rng|].
    etrans;[apply grel_seq_rng|].
    all: set_solver - Hwf.
  Qed.

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
    rewrite 2!grel_dom_union.
    rewrite !union_subseteq.
    set_solver - Hwf.
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

    rewrite 2!grel_rng_union.
    rewrite !union_subseteq.
    set_solver - Hwf.
  Qed.

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
    rewrite grel_dom_union.
    rewrite union_subseteq.
    set_solver - Hwf.
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

    rewrite grel_rng_union.
    rewrite union_subseteq.
    set_solver - Hwf.
  Qed.

  (* [acq ; po] is in [lob] *)
  Lemma acq_po_subseteq_lob (gr : Candidate.t) e e':
    e ∈ acq_reads gr ->
    (e, e') ∈ Candidate.po gr ->
    (e, e') ∈ lob gr.
  Proof.
    intros.
    rewrite /lob.
    apply elem_of_union_r.
    rewrite /bob.
    apply elem_of_union_l.
    apply elem_of_union_l.
    apply elem_of_union_l.
    apply elem_of_union_r.
    set_unfold.
    hauto.
  Qed.


  (* [po ; rel] is in [lob] *)
  Lemma po_rel_subseteq_lob (gr : Candidate.t) e e':
    (e, e') ∈ Candidate.po gr ->
    e' ∈ rel_writes gr ->
    (e, e') ∈ lob gr.
  Proof.
    intros.
    rewrite /lob.
    apply elem_of_union_r.
    rewrite /bob.
    apply elem_of_union_l.
    apply elem_of_union_r.
    set_unfold.
    hauto.
  Qed.


  (* [po ; [dmb_sy]; po] is in [lob] *)
  Lemma po_dmbsy_po_subseteq_lob (gr : Candidate.t) e e' e'':
    (e, e') ∈ Candidate.po gr ->
    e' ∈ dmbs gr AAArch.Sy ->
    (e', e'') ∈ Candidate.po gr ->
    (e, e'') ∈ lob gr.
  Proof.
    intros.
    rewrite /lob.
    apply elem_of_union_r.
    rewrite /bob.
    apply elem_of_union_l.
    apply elem_of_union_l.
    apply elem_of_union_l.
    apply elem_of_union_l.
    apply elem_of_union_l.
    apply elem_of_union_l.
    set_unfold.
    hauto.
  Qed.

  (* [ctrl; [w]] is in [lob] *)
  Lemma ctrl_w_subseteq_lob (gr : Candidate.t) e e':
    (e, e') ∈ Candidate.ctrl gr ->
    e' ∈ AACandExec.Candidate.mem_writes gr ->
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
    e' ∈ isbs gr ->
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

  (* initial writes has no [lob] successors *)
  Lemma no_lob_succ_initial gr e:
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    e ∈ Candidate.initials gr -> lob_succ_of gr e = ∅.
  Proof.
    intros Hwf Hcs ?.
    assert (initial_wf gr) as Hinit by (rewrite /wf in Hwf;naive_solver).
    rewrite /initial_wf in Hinit.
    destruct_and ? Hinit.
    rewrite /lob_succ_of.
    assert (po_wf gr) as Hpo by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo.
    destruct_and ? Hpo.
    clear H8 H11 H0 H1 H3 H4 H5 H6 H2.


    assert (grel_rng (filter (λ '(es, _), es = e) (Candidate.po gr)) = ∅).
    {
      clear Hwf.
      set_unfold.
      intros. apply Classical_Pred_Type.all_not_not_ex.
      intros. intro.
      destruct H0 as [<- ?].
      assert ((n, x) ∈ Candidate.sthd gr).
      {
        apply H10. simpl. left. left;done.
      }
      set_unfold.
      sauto lq:on.
    }

    pose proof (lob_subseteq_po _ Hwf Hcs).
    Local Opaque lob.
    set_unfold.
    set_solver + H0 H1.
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
    rewrite -grel_dom_union. rewrite -filter_union_L.
    Local Opaque obs.
    rewrite /ob. rewrite union_comm_L. set_unfold.
    split.
    - intros ? [].
      eexists. split;first reflexivity.
      apply grel_plus_once.
      clear Hwf.
      set_unfold. hauto.
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
    rewrite -grel_rng_union. rewrite -filter_union_L.
    rewrite /ob. rewrite union_comm_L. set_unfold.
    split.
    - intros ? [].
      eexists. split;first reflexivity.
      apply grel_plus_once.
      clear Hwf.
      set_unfold. hauto.
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
    ∀ v, (exists E addr ks kv , gr !! e = Some E ∧ event_is_write_with E ks kv addr v) -> v = (BV _ 0).
  Proof.
    intros Hwf ???.
    assert (initial_wf gr) as Hinit_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /initial_wf in Hinit_wf.
    rewrite bool_unfold in Hinit_wf.
    destruct_and ? Hinit_wf.
    clear H3 H5.
    assert (e ∈ Candidate.initials gr). set_unfold. set_solver + H0 H.
    apply H6 in H1. set_unfold in H1.
    destruct H1 as [? [? ?]].
    destruct H0 as (?&?&?&?&?&?).
    rewrite H1 in H0. match_inversion;try contradiction.
    rewrite bool_unfold in H3.
    destruct_and ? H3.
    simpl in H5.
    rewrite bool_unfold in H5.
    destruct_and ? H5.
    rewrite /addr_and_value_of_wreq in H14.
    (* clear H6 H7 H10 H11 H12 H14. *)
    match_inversion;try contradiction.
    subst n.
    unfold eq_rec_r, eq_rec in H14.
    rewrite <-Classical_Prop.Eq_rect_eq.eq_rect_eq in H14.
    inversion H14. subst. simpl in H8.
    rewrite H8.
    unfold Val. unfold AAArch.val. unfold AAval. bv_solve.
  Qed.

  (* initial writes are [co] initial *)
  Lemma init_co (gr : Candidate.t) (e e': Eid) (a : Addr):
    NMSWF.wf gr ->
    e.(EID.tid) = 0%nat ->
    e'.(EID.tid) ≠ 0%nat ->
    (exists E, gr !! e = Some E ∧ event_is_write_with_addr E a) ->
    (exists E, gr !! e' = Some E ∧ event_is_write_with_addr E a) ->
    (e, e') ∈ Candidate.co gr.
  Proof.
    intros Hwf ? Hnz [?[]] [?[]].
    assert (initial_wf gr) as Hinit_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /initial_wf in Hinit_wf.
    rewrite bool_unfold in Hinit_wf.
    destruct_and ? Hinit_wf.
    assert (e ∈ Candidate.initials gr). set_unfold. set_solver + H0 H.
    rewrite H7 in H4. set_unfold in H4.
    destruct H4 as [? (?&?&?&?)].

    pose proof (Classical_Pred_Type.not_ex_all_not _ _ H4 e'). simpl in H11.
    apply not_and_l in H11.
    destruct H11.
    - exfalso. clear H5 H6 H9 H7 H8 H0 H1 H10 H.
      set_unfold in H11.
      rewrite /event_is_write_with_addr in H3. rewrite /event_is_write_with_P in H3.
      match_inversion;try contradiction.
      eapply (Classical_Pred_Type.not_ex_all_not) in H11.
      eapply (Classical_Pred_Type.not_ex_all_not) in H11.
      eapply (Classical_Pred_Type.not_ex_all_not) in H11.
      rewrite H2 in H11.
      contradiction.
    - assert ((e, e') ∈ Candidate.loc gr) as Hloc.
      {
        clear H8 H6 H4 H9 H5. set_unfold.
        exists x. exists x0. exists a.  rewrite /Candidate.get_pa.
        split;first assumption.
        rewrite /event_is_write_with_addr /event_is_write_with_P in H1.
        rewrite /event_is_write_with_addr /event_is_write_with_P in H3.
        match_inversion;try contradiction.
        rewrite bool_unfold in H1.
        rewrite bool_unfold in H3.
        destruct_and ? H1.
        destruct_and ? H3.
        rewrite /addr_of_wreq in H12. rewrite /addr_of_wreq in H14.
        rewrite H12. rewrite H14.
        hauto lq:on.
      }
      assert (co_wf gr) as Hco_wf by (rewrite /wf in Hwf;naive_solver).
      rewrite /co_wf in Hco_wf. rewrite bool_unfold in Hco_wf.
      destruct_and ? Hco_wf.
      assert ((e, e') ∈ Candidate.loc gr ∩ (Candidate.mem_writes gr × Candidate.mem_writes gr)).
      {
        clear H13 H14 H15 H16 H17 H18 H19 H11 H4 H6 H7 H8 H9.
        apply elem_of_intersection.
        split;first assumption.
        eapply event_is_write_elem_of_mem_writes in H3;last eassumption.
        set_unfold.
        sauto lq:on.
      }
      rewrite H15 in H12.
      apply elem_of_union in H12.
      destruct H12.
      2:{ set_unfold in H12. set_solver + H12 H Hnz. }
      apply elem_of_union in H12.
      destruct H12. assumption.
      set_unfold in H12. set_solver + H12 H11.
  Qed.

  Lemma rf_rmw_co (gr : Candidate.t) (eid_w eid_xr eid_xw : EID.t):
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    (eid_w, eid_xr) ∈ Candidate.rf gr ->
    (eid_xr, eid_xw) ∈ Candidate.rmw gr ->
    (eid_w, eid_xw) ∈ Candidate.co gr.
  Proof.
    intros Hwf Hcs Hrf Hrmw.
    assert (co_wf gr) as Hco_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /co_wf in Hco_wf.
    destruct_and ? Hco_wf.
    assert (rf_wf gr) as Hrf_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /rf_wf in Hrf_wf.
    destruct_and ? Hrf_wf.
    assert (rmw_wf gr) as Hrmw_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /rmw_wf in Hrmw_wf.
    destruct_and ? Hrmw_wf.
    assert ((eid_w, eid_xr) ∈ Candidate.loc gr). apply H7 in Hrf. set_solver + Hrf.
    assert ((eid_xr, eid_xw) ∈ Candidate.loc gr). apply H17 in Hrmw. set_solver + Hrmw.
    assert ((eid_w, eid_xw) ∈ Candidate.loc gr). set_solver + H12 H19.
    assert (eid_w ∈ Candidate.mem_writes gr). apply H. set_solver + Hrf.
    assert (eid_xw ∈ Candidate.mem_writes_atomic gr). apply H14. set_solver + Hrmw.
    assert (eid_xw ∈ Candidate.mem_writes gr). clear - H22.
    set_unfold. destruct H22 as (?&?&?). match_inversion;try contradiction. hauto.
    assert ((eid_w, eid_xw) ∈ Candidate.loc gr
              ∩ (Candidate.mem_writes gr × Candidate.mem_writes gr)).
    clear - H20 H21 H23. set_unfold. hauto.
    rewrite H2 in H24. apply elem_of_union in H24.
    assert ((eid_xr, eid_xw) ∈ Candidate.po gr ∩ Candidate.loc gr).
    {
      apply elem_of_intersection.
      split. apply H16. assumption. apply H17. assumption.
    }
    destruct Hcs.
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
  Lemma rmw_rmw (gr : Candidate.t) (eid_w eid_xr eid_xr' eid_xw eid_xw' : Eid):
    NMSWF.wf gr ->
    AAConsistent.t gr ->
    eid_xr ≠ eid_xr' ->
    (eid_w, eid_xr) ∈ Candidate.rf gr ->
    (eid_xr, eid_xw) ∈ Candidate.rmw gr ->
    (eid_w, eid_xr') ∈ Candidate.rf gr ->
    (eid_xr', eid_xw') ∈ Candidate.rmw gr ->
    False.
  Proof.
    intros Hwf Hcs Hnst Hrf Hrmw Hrf' Hrmw'.
    assert (co_wf gr) as Hco_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /co_wf in Hco_wf.
    destruct_and ? Hco_wf.
    assert (rf_wf gr) as Hrf_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /rf_wf in Hrf_wf.
    destruct_and ? Hrf_wf.
    assert (rmw_wf gr) as Hrmw_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /rmw_wf in Hrmw_wf.
    destruct_and ? Hrmw_wf.
    assert (po_wf gr) as Hpo_wf by (rewrite /wf in Hwf;naive_solver).
    rewrite /po_wf in Hpo_wf.
    destruct_and ? Hpo_wf.
    assert ((eid_w, eid_xw) ∈ Candidate.co gr) as Hco.
    {
      eapply (rf_rmw_co _ eid_w eid_xr); eassumption.
    }
    assert ((eid_w, eid_xw') ∈ Candidate.co gr) as Hco'.
    {
      eapply (rf_rmw_co _ eid_w eid_xr'); eassumption.
    }
    assert (EID.tid eid_xr ≠ EID.tid eid_xr').
    {
      intros Hst.
      assert ((eid_xr', eid_xw') ∈ Candidate.po gr). apply H16. assumption.
      assert ((eid_xr, eid_xw) ∈ Candidate.po gr). apply H16. assumption.
      assert (eid_xr ∈ Candidate.mem_reads_atomic gr) as Hxr. apply H15. set_solver + Hrmw.
      assert (eid_xr' ∈ Candidate.mem_reads_atomic gr) as Hxr'. apply H15. set_solver + Hrmw'.
      assert ((eid_xr, eid_xr') ∈ Candidate.sthd gr). set_solver + Hst Hxr Hxr'.

      assert (eid_xw ∈ Candidate.mem_writes_atomic gr) as Hxw. apply H14. set_solver + Hrmw.
      assert (eid_xw' ∈ Candidate.mem_writes_atomic gr) as Hxw'. apply H14. set_solver + Hrmw'.
      assert ((eid_xw, eid_xr') ∈ Candidate.sthd gr).
      {
        assert ((eid_xr, eid_xw) ∈ Candidate.sthd gr). rewrite -H23. set_solver + H25.
        clear - H27 H26. set_unfold. sauto.
      }
      assert ((eid_xw', eid_xr) ∈ Candidate.sthd gr).
      {
        assert ((eid_xr', eid_xw') ∈ Candidate.sthd gr). rewrite -H23. set_solver + H20.
        clear - H26 H28. set_unfold. sauto.
      }
      rewrite -H23 in H26.
      rewrite -H23 in H27.
      rewrite -H23 in H28.
      (* set_solver + Hst Hxr Hxr'. *)
      apply elem_of_union in H26. destruct H26.
      2:{
        assert (eid_xr ∈ Candidate.initials gr). set_solver + H26.
        assert (initial_wf gr) as Hinitial_wf by (rewrite /wf in Hwf;naive_solver).
        rewrite /initial_wf in Hinitial_wf.
        destruct_and ? Hinitial_wf.
        apply H35 in H29.
        clear -H29 Hxr.
        set_unfold. destruct H29 as (?&?&?). destruct Hxr as (?&?&?). rewrite H in H1. inversion H1;subst x0.
        match_inversion;try contradiction.
      }
      apply elem_of_union in H27. destruct H27.
      2:{
        assert (eid_xw ∈ Candidate.initials gr). set_solver + H27.
        assert (initial_wf gr) as Hinitial_wf by (rewrite /wf in Hwf;naive_solver).
        rewrite /initial_wf in Hinitial_wf.
        destruct_and ? Hinitial_wf.
        apply H35 in H29.
        clear -H29 Hxw.
        set_unfold. destruct H29 as (?&?&?). destruct Hxw as (?&?&?). rewrite H in H1. inversion H1;subst x0.
        match_inversion;try contradiction.
        destruct_and ? H2.
        destruct_and ? H0.
        rewrite bool_unfold in H5.
        rewrite bool_unfold in H9.
        contradiction.
      }
      apply elem_of_union in H28. destruct H28.
      2:{
        assert (eid_xr ∈ Candidate.initials gr). set_solver + H28.
        assert (initial_wf gr) as Hinitial_wf by (rewrite /wf in Hwf;naive_solver).
        rewrite /initial_wf in Hinitial_wf.
        destruct_and ? Hinitial_wf.
        apply H35 in H29.
        clear -H29 Hxr.
        set_unfold. destruct H29 as (?&?&?). destruct Hxr as (?&?&?). rewrite H in H1. inversion H1;subst x0.
        match_inversion;try contradiction.
      }
      apply elem_of_union in H26. destruct H26.
      {
        apply elem_of_union in H27. destruct H27.
        {
          (* internal *)
          assert ((eid_xr', eid_xw) ∈ Candidate.fr gr).
          set_solver + Hrf' Hco.
          assert ((eid_xw, eid_xr') ∈ Candidate.po gr ∩ Candidate.loc gr).
          apply elem_of_intersection.  split. assumption.
          apply H7 in Hrf'.
          apply H5 in Hco.
          set_solver + Hrf' Hco.
          destruct Hcs.
          rewrite grel_irreflexive_spec in internal0.
          clear - H30 H29 internal0.
          specialize (internal0 (eid_xw, eid_xw)). simpl in internal0.
          apply internal0;last reflexivity.
          apply (grel_plus_trans _ _ eid_xr').
          apply grel_plus_once. set_solver + H30.
          apply grel_plus_once. set_solver + H29.
        }
        {
          assert ((eid_xr, eid_xw) ∈ ⦗Candidate.mem_reads_atomic gr⦘ ⨾ Candidate.po gr ⨾ ⦗Candidate.mem_reads_atomic gr⦘ ⨾ Candidate.po gr
           ⨾ ⦗Candidate.mem_writes_atomic gr⦘).
          clear - H26 H27 Hxr Hxr' Hxw.
          set_unfold. sauto lq:on.
          set_solver + H29 Hrmw H11.
        }
      }
      {
        apply elem_of_union in H28. destruct H28.
        {
          (* internal *)
          assert ((eid_xr, eid_xw') ∈ Candidate.fr gr).
          set_solver + Hrf Hco'.
          assert ((eid_xw', eid_xr) ∈ Candidate.po gr ∩ Candidate.loc gr).
          apply elem_of_intersection.  split. assumption.
          apply H7 in Hrf.
          apply H5 in Hco'.
          set_solver + Hrf Hco'.
          destruct Hcs.
          rewrite grel_irreflexive_spec in internal0.
          clear - H30 H29 internal0.
          specialize (internal0 (eid_xw', eid_xw')). simpl in internal0.
          apply internal0;last reflexivity.
          apply (grel_plus_trans _ _ eid_xr).
          apply grel_plus_once. set_solver + H30.
          apply grel_plus_once. set_solver + H29.
        }
        {
          assert ((eid_xr', eid_xw') ∈ ⦗Candidate.mem_reads_atomic gr⦘ ⨾ Candidate.po gr ⨾ ⦗Candidate.mem_reads_atomic gr⦘ ⨾ Candidate.po gr
           ⨾ ⦗Candidate.mem_writes_atomic gr⦘).
          clear - H26 H28 Hxr Hxr' Hxw'.
          set_unfold. sauto lq:on.
          set_solver + H29 Hrmw' H11.
        }
      }
    }

    assert ((eid_xr', eid_xw) ∈ Candidate.external_of (Candidate.fr gr)) as Hfr.
    {
      assert ((eid_xr, eid_xw) ∈ Candidate.po gr). apply H16. assumption.
      assert ((eid_xr, eid_xw) ∈ Candidate.sthd gr). rewrite -H23. set_solver + H25.
      clear - Hco Hrf' H26 H20.
      set_unfold. sauto.
    }
    assert ((eid_xr, eid_xw') ∈ Candidate.external_of (Candidate.fr gr)) as Hfr'.
    {
      assert ((eid_xr', eid_xw') ∈ Candidate.po gr). apply H16. assumption.
      assert ((eid_xr', eid_xw') ∈ Candidate.sthd gr). rewrite -H23. set_solver + H25.
      clear - Hco' Hrf H26 H20.
      set_unfold. sauto.
    }
    assert ((eid_xw, eid_xw') ∈ Candidate.loc gr) as Hloc.
    {
      apply H17 in Hrmw'.
      apply H7 in Hrf'.
      assert ((eid_w, eid_xw) ∈ Candidate.loc gr).
      {
        assert ((eid_w, eid_xw) ∈ Candidate.co gr ∪ (Candidate.co gr) ⁻¹ ∪ ⦗Candidate.mem_writes gr⦘). set_solver + Hco.
        rewrite -H2 in H25.
        set_solver + H25.
      }
      set_solver + H25 Hrmw' Hrf'.
    }
    assert ((eid_xw, eid_xw') ∈ Candidate.co gr ∪ (Candidate.co gr) ⁻¹ ∪ ⦗Candidate.mem_writes gr⦘).
    {
      rewrite -H2.
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
      assert ((eid_xr, eid_xw) ∈ Candidate.po gr). apply H16. assumption.
      assert ((eid_xr, eid_xw) ∈ Candidate.sthd gr). rewrite -H23. set_solver + H26.
      assert ((eid_xr', eid_xw') ∈ Candidate.po gr). apply H16. assumption.
      assert ((eid_xr', eid_xw') ∈ Candidate.sthd gr). rewrite -H23. set_solver + H28.
      clear - H27 H29 H20 Heq.
      set_unfold. sauto lq:on.
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
      rewrite bool_unfold in atomic0.
      set_solver + atomic0 H28 Hrmw'.
    }
    {
      assert ((eid_xw', eid_xw) ∈ Candidate.external_of (Candidate.co gr)).
      set_solver + H25 H26.
      assert ((eid_xr, eid_xw) ∈ (Candidate.external_of (Candidate.fr gr))⨾(Candidate.external_of (Candidate.co gr))).
      {
        set_solver + H27 Hfr'.
      }
      rewrite bool_unfold in atomic0.
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
    (∀ e, P e = true -> Q e = true) ->
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
    assert ((e, e')∈ Candidate.sthd gr).
    { rewrite -H7. set_solver + H1. }
    clear H3 H5 H7 Hwf.

    set_unfold. specialize (H6 (e,e')).
    destruct H4 as (?&?&?&?&?&?&?).
    set_unfold.
    split;first sauto lq:on.
    intro.
    subst.
    clear H8 H0 H Hc.
    apply not_and_l in H6. destruct H6;first contradiction.
    rewrite -H7 in H. rewrite H9 in H.
    hauto lq:on.
  Qed.

  (** Induction scheme*)
  (* This is weaker in the sense that nodes in [s] can be ordered *)
  Definition ob_semi_last_set gr (s s' : gset Eid) :=
    set_Forall (λ e_last, set_Forall (λ e, (e_last, e) ∉ (AAConsistent.ob gr)) (s' ∖ s)) s.

  Definition ob_subset gr (s' s : gset Eid) : Prop := s' ⊂ s ∧ ob_semi_last_set gr s' s.

  Lemma ob_semi_last_set_mono gr (s s' s'' : gset Eid) :
    s ⊂ s' -> s' ⊆ s'' ->
    ob_semi_last_set gr s s'  -> ob_semi_last_set gr s' s'' -> ob_semi_last_set gr s s''.
  Proof.
    intros Hsub Hsub' Hob Hob'.
    apply set_subseteq_inv_L in Hsub'.
    destruct Hsub' as [Hsub'| ->];last done.
    intros x Hin.
    specialize (Hob x Hin). simpl in Hob.
    intros x'' Hin''.
    destruct (decide (x'' ∈ s')).
    - intro.
      specialize (Hob x'').
      feed specialize Hob. set_solver + e Hin'' Hsub Hsub'.
      done. done.
    - rewrite /ob_semi_last_set in Hob'.
      destruct (decide (x ∈ s')).
    + specialize (Hob' x).
      feed specialize Hob'. set_solver + e.
      simpl in Hob'.
      apply Hob'.
      set_solver + Hin'' n.
    + set_solver + Hsub n0 Hin.
  Qed.

  Lemma ob_subset_wf gr : well_founded.wf (ob_subset gr).
  Proof.
    apply (wf_projected (<)%nat size).
    - intros ?? (? & _).
      by apply subset_size.
    - apply lt_wf.
  Qed.

  Definition get_ob_first gr (s : gset Eid) :=
    filter (λ e, set_Forall (λ e', (e', e) ∉ (AAConsistent.ob gr)) s) s.

  Lemma get_ob_first_subseteq gr s :
    get_ob_first gr s ⊆ s.
  Proof.
    intros ? Hin.
    apply elem_of_filter in Hin.
    destruct Hin;done.
  Qed.

  Lemma get_ob_first_non_empty gr s :
    AAConsistent.t gr ->
    s ⊆ Candidate.valid_eid gr ->
    (exists x, x ∈ s) ->
    exists x, x ∈ get_ob_first gr s.
  Proof.
    intros Hcs.
    eapply (well_founded_induction _
              (λ s, s ⊆ Candidate.valid_eid gr → (∃ x : Eid, x ∈ s) → ∃ x : Eid, x ∈ get_ob_first gr s)).
    Unshelve.
    2: { exact (⊂). }
    2 : {
      eapply (wf_projected (<)%nat size).
      - intros ??. apply subset_size.
      - apply lt_wf.
    }
    clear s. intros s IH Hsub Hnem.
    destruct Hnem as [x Hin].
    destruct (decide (x ∈ get_ob_first gr s));[exists x;done|].
    rewrite /get_ob_first elem_of_filter in n. rewrite not_and_l in n.
    destruct n; last set_solver + H Hin Hsub.
    apply not_set_Forall_Exists in H. 2: apply _.
    destruct H as [x0 [Hin' Hob]].
    assert (x0 ≠ x).
    {
      intros ->. destruct Hcs as [_ Hac].
      rewrite grel_irreflexive_spec in Hac.
      simpl in Hob. apply Hob.
      intro Hxx. specialize (Hac (x, x) Hxx). done.
    }
    specialize (IH (s∖ {[x]})). feed specialize IH.
    set_solver + Hin.
    set_solver + Hsub.
    exists x0. set_solver + H Hin Hin'.
    destruct IH as [x2 ?].
    destruct (decide ((x, x2) ∈ (ob gr))).
    {
      apply elem_of_filter in H0.
      destruct H0.
      assert (x0 ∈ s ∖ {[x]}) by set_solver + H Hin'.
      specialize (H0 x0 H2).
      simpl in H0. simpl in Hob.
      assert ((x0, x) ∈ ob gr).
      destruct (decide ((x0, x) ∈ ob gr)). done.
      exfalso. apply Hob. done.
      exfalso. apply H0.
      pose proof (grel_transitive_spec (ob gr)) as [Htran _].
      feed specialize Htran.
      apply grel_transitive_plus. eapply Htran;eauto.
    }
    {
      exists x2. apply elem_of_filter.
      split. 2:{ apply elem_of_filter in H0. destruct H0. set_solver + H1. }
      rewrite (union_difference_L {[x]} s); first set_solver + Hin.
      apply set_Forall_union.
      apply set_Forall_singleton. done.
      apply elem_of_filter in H0. destruct H0. done.
    }
  Qed.

  Lemma ob_semi_last_set_choose_or_empty gr s:
    AAConsistent.t gr ->
    s ⊆ Candidate.valid_eid gr ->
    (∃ x, x ∈ s ∧ ob_semi_last_set gr (s ∖ {[x]}) s) ∨ s ≡ ∅.
  Proof.
    intros Hcs Hsub.
    destruct (set_choose_or_empty (get_ob_first gr s)) as [[x Hx_in]|HX].
    - left. exists x.
      apply elem_of_filter in Hx_in.
      destruct Hx_in as (Hlast & Hin ).
      split;first done.
      intros y Hy_in.
      assert (Hy_in' : y ∈ s) by set_solver + Hy_in.
      specialize (Hlast y Hy_in').
      assert ((s ∖ (s ∖ {[x]})) = {[x]}) as ->.
      rewrite difference_difference_r_L.
      set_solver + Hin.
      apply set_Forall_singleton. done.
    - destruct (set_choose_or_empty s) as [[y Hy_in]|HY].
      + exfalso.
        pose proof (get_ob_first_non_empty gr s Hcs Hsub) as Hnem.
        feed specialize Hnem. exists y;done.
        set_solver + Hnem HX.
      + right;done.
  Qed.

  Lemma ob_set_ind (gr : Graph.t) (s_all : gset Eid) (P : gset Eid → Prop) :
    Proper ((≡) ==> iff) P →
    AAConsistent.t gr ->
    s_all ⊆ (Candidate.valid_eid gr) ->
    P ∅ →
    (∀ (x : Eid) (X : gset Eid), x ∉ X -> x ∈ s_all ->
                                 ob_subset gr X s_all ->
                                 set_Forall (λ x', (x', x) ∉ (AAConsistent.ob gr)) ({[x]} ∪ X) →
                                 P X → P ({[ x ]} ∪ X)) →
    ∀ X, X ⊆ s_all -> ob_semi_last_set gr X s_all -> P X.
  Proof.
    intros ? Hcs Hall_valid Hemp Hadd.
    eapply (well_founded_induction _ (λ X, X ⊆ s_all -> ob_semi_last_set gr X s_all → P X)).
    Unshelve.
    2:{ exact (ob_subset gr). }
    2:{ apply ob_subset_wf. }
    intros X IH HX_subeq HX_semi_first.
    assert (HX_valid: X ⊆ Candidate.valid_eid gr) by set_solver + HX_subeq Hall_valid.
    destruct (ob_semi_last_set_choose_or_empty gr X Hcs HX_valid) as [[x [Hx_in HX_x_semi_first]]|HX].
    - rewrite (union_difference {[x]} X);[set_solver + Hx_in|].
      apply Hadd;[set_solver + | set_solver + Hx_in  HX_subeq | | |].
      {
        split. set_solver + Hx_in HX_subeq.
        eapply ob_semi_last_set_mono;eauto.
        set_solver + Hx_in HX_subeq.
      }
      {
        apply set_Forall_union.
        {
          rewrite set_Forall_singleton.
          destruct Hcs as [_ Hac].
          rewrite grel_irreflexive_spec in Hac.
          intro Hxx. specialize (Hac (x, x) Hxx). done.
        }
        {
          intros x0 Hx0_in.
          apply (HX_x_semi_first x0 Hx0_in).
          set_solver + Hx_in.
        }
      }
      apply IH.
      split. set_solver + Hx_in. done.
      set_solver + HX_subeq.
        eapply ob_semi_last_set_mono;eauto.
        set_solver + Hx_in.
    - by rewrite HX.
  Qed.

  Lemma ob_set_ind_L (gr : Graph.t) (s_all : gset Eid) (P : gset Eid → Prop) :
    AAConsistent.t gr ->
    s_all ⊆ (Candidate.valid_eid gr) ->
    P ∅ → (∀ (x : Eid) (X : gset Eid), x ∉ X -> x ∈ s_all ->
                                       ob_subset gr X s_all ->
                                       set_Forall (λ x', (x', x) ∉ (AAConsistent.ob gr)) ({[x]} ∪ X) →
                  P X → P ({[ x ]} ∪ X)) → ∀ X, X ⊆ s_all -> ob_semi_last_set gr X s_all -> P X.
  Proof. apply ob_set_ind. by intros ?? ->%leibniz_equiv_iff. Qed.

End Graph.
