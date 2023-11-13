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

(** This file contains the definition of the operational semantics *)
From Coq Require Import ssreflect.
From stdpp Require Import numbers unstable.bitvector.

From RecordUpdate Require Export RecordSet.
Export RecordSetNotations.

From SSCCommon Require Import CSets GRel.

From self Require Import stdpp_extra.
From self.lang Require Export mm.
From self.lang Require Import instrs.

Record RegVal := mk_regval {
    reg_val : AAInter.reg_type; (* Val *)
    reg_dep : gset Eid;
}.

Notation RegFile := (gmap RegName RegVal) (only parsing).
Notation Tid := positive.

(* nodes whose eids start with tid 0 are initial writes *)
Definition tid0 := 0.
Coercion Pos.to_nat : Tid >-> nat.

Lemma iter_op_plus_mono t (n n': nat):
  (n <= n')%nat ->
  (Pos.iter_op plus t n <= Pos.iter_op plus t n')%nat.
Proof.
  revert n n'.
  induction t ;simpl;try lia.
  intros. specialize  (IHt (n+n) (n' + n'))%nat.
  feed specialize IHt. lia.
  lia.
  intros. specialize  (IHt (n+n) (n' + n'))%nat.
  feed specialize IHt. lia.
  lia.
Qed.

Lemma tid_nz_aux (t : Tid) : (0%nat < t)%nat.
Proof.
  rewrite /Pos.to_nat.
  induction t ;simpl.
  lia.
  pose proof (iter_op_plus_mono t 1 2). feed specialize H;first lia.
  lia.
  lia.
Qed.

Lemma tid_nz_nz (t : Tid) : (0%nat ≠ t)%nat.
Proof. pose proof (tid_nz_aux t). lia. Qed.


(* instruction memory of all threads *)
Module GInstrMem.

  Definition t := gmap Addr Instruction.

End GInstrMem.


(* thread state *)
Module ThreadState.
  Import AACandExec.
  Definition progress : Type := (nat * nat).

  Module IntraInstrState.

    Record t := mk_l {
                    iis_iid : nat;
                    iis_cntr : nat;
                    iis_mem_reads : list nat;
                  }.

    #[global] Instance eta : Settable _ := settable! mk_l <iis_iid; iis_cntr; iis_mem_reads>.

    Definition mk_iis iid := {| iis_iid := iid; iis_cntr := 0; iis_mem_reads := [] |}.
  End IntraInstrState.

  Record t := mk_l {
      ts_regs : RegFile;
      ts_reqs : InstSem;
      ts_ctrl_srcs : gset Eid;
      ts_iis : IntraInstrState.t;
      ts_rmw_pred : option Eid;
    }.

  (* instance for record update *)
  #[global] Instance eta : Settable _ := settable! mk_l <ts_regs; ts_reqs; ts_ctrl_srcs; ts_iis; ts_rmw_pred>.

  Export IntraInstrState.
  Definition mk_ts regs fst_instr_sem :=
     {|
      ts_regs := regs;
      ts_reqs := fst_instr_sem;
      ts_ctrl_srcs := ∅;
      ts_iis := mk_iis 0;
      ts_rmw_pred := None;
    |}.

  Definition reqs_done ts := ts.(ts_reqs) = EmptyInterp.
  Definition next_req_is{T} ts (req: outcome T) k := ts.(ts_reqs) = (AAInter.Next req k).

  Definition mk_eid_ii ts tid :=
    EID.make tid ts.(ts_iis).(iis_iid) ts.(ts_iis).(iis_cntr).

  Definition mk_iis_ni ts := mk_iis (ts.(ts_iis).(iis_iid) + 1).

  Definition incr_cntr ts : ThreadState.t :=
    ts <| ts_iis := (ts.(ts_iis) <|iis_cntr := ((ts.(ts_iis).(iis_cntr)) + 1)%nat |>) |>.
  Definition reset_cntr ts : ThreadState.t :=
    ts <| ts_iis := mk_iis_ni ts |>.

  (* A local progress is (iid, num), it returns the latest one *)
  Definition get_progress ts : progress :=
   (ts.(ThreadState.ts_iis).(iis_iid), ts.(ThreadState.ts_iis).(iis_cntr)).

  Definition progress_of_node e : progress := (e.(EID.iid), e.(EID.num)).
  Definition progress_to_node ρ tid : Eid := (EID.make tid ρ.1 ρ.2).

  Lemma progress_to_node_of_node tid e :
    e.(EID.tid) = tid ->
    progress_to_node (progress_of_node e) tid = e.
  Proof.
    rewrite /progress_to_node /progress_of_node /=.
    intros <-. destruct e;cbn; done.
  Qed.

  Lemma progress_of_node_to_node tid pg:
    progress_of_node (progress_to_node pg tid) = pg.
  Proof.
    rewrite /progress_to_node /progress_of_node /=.
    destruct pg; done.
  Qed.

  Definition progress_is_valid gr (tid : Tid) pg :=
    progress_to_node pg tid ∈ Candidate.valid_eid gr.

  #[global] Instance progress_is_valid_dec gr tid pg : Decision (progress_is_valid gr tid pg).
  Proof. rewrite /progress_is_valid. apply _. Qed.

  Definition progress_lt (pg1 pg2 : progress) := (pg1.1 < pg2.1 ∨ (pg1.1 = pg2.1 ∧ pg1.2 < pg2.2))%nat.

  #[global] Instance progress_lt_dec pg1 pg2 : Decision (progress_lt pg1 pg2).
  Proof. rewrite /progress_lt. apply _. Qed.

  Lemma progress_lt_gt_False pg1 pg2 : progress_lt pg1 pg2 ∧ progress_lt pg2 pg1 -> False.
  Proof. intros [[|] [|]];lia. Qed.

  Lemma progress_lt_refl_False pg : progress_lt pg pg -> False.
  Proof. intros [|];lia. Qed.

  Lemma progress_lt_trans pg1 pg2 pg3 :
    progress_lt pg1 pg2 ->
    progress_lt pg2 pg3 -> progress_lt pg1 pg3.
  Proof.
    destruct pg1, pg2, pg3;intros [];intros [];simpl in *;[left|left|left|right];simpl;lia.
  Qed.

  Lemma progress_lt_neq pg pg': progress_lt pg pg' -> pg ≠ pg'.
  Proof. intros [|] ->;lia. Qed.

  (* It is used in the lifting proofs *)
  (* Maybe we can get rid of this by proving a similar property
     (but without WF) for [step] *)
  Lemma progress_lt_po gr (tid : Tid) (pg pg' : progress):
    (* not true for initial writes *)
    AACandExec.NMSWF.wf gr ->
    (ThreadState.progress_lt pg pg'
     ∧ ThreadState.progress_is_valid gr tid pg
     ∧ ThreadState.progress_is_valid gr tid pg')
     <-> ((ThreadState.progress_to_node pg tid),
          (ThreadState.progress_to_node pg' tid)) ∈ gr.(AACandExec.Candidate.po).
  Proof.
    intros Hwf.
    split.
    + intros.
      unfold progress_is_valid, progress_lt in *.
      destruct H as [Hlt [Hvalid1 Hvalid2]].
      apply Graph.pg_lt_to_po.
      - assumption.
      - by simpl.
      - by simpl.
      - pose proof (tid_nz_nz tid). simpl. lia.
      - by simpl.
      - by simpl.   
    + intros.
      split.
      - unfold progress_lt.
        set (e1 := progress_to_node pg tid).
        set (e2 := progress_to_node pg' tid).
        apply (Graph.po_to_pg_lt gr e1 e2); assumption.
      - by apply Graph.po_valid_eids'.
  Qed.

  Definition progress_le (pg1 pg2 : progress) := (pg1.1 < pg2.1 ∨ (pg1.1 = pg2.1 ∧ pg1.2 <= pg2.2))%nat.

  #[global] Instance progress_le_dec p1 p2 : Decision (progress_le p1 p2).
  Proof. rewrite /progress_le. apply _. Qed.

  Lemma progress_lt_le pg1 pg2 :
    progress_lt pg1 pg2 -> progress_le pg1 pg2.
  Proof.
    destruct pg1,pg2. intros [];simpl in *.
    left;simpl;lia.
    right;simpl;lia.
  Qed.

  Lemma progress_le_inv pg1 pg2 : progress_le pg1 pg2 <-> progress_lt pg1 pg2 ∨ pg1 = pg2.
  Proof.
    destruct pg1,pg2. split;intros [];simpl in *.
    left;left;simpl; lia.
    destruct (decide (n0 < n2)%nat).
    left;right;simpl;lia.
    right;simpl. destruct H as [-> ?]. f_equal. lia.
    by apply progress_lt_le.
    right;simpl. inversion H. lia.
  Qed.

  Lemma progress_le_gt_False pg1 pg2 : progress_le pg1 pg2 ->
                  progress_lt pg2 pg1 -> False.
  Proof. intros [Hlt | Heq] [H1| H2];try lia. Qed.

  Lemma progress_le_ge_eq pg1 pg2 :
    progress_le pg1 pg2 -> progress_le pg2 pg1 -> pg1 = pg2.
  Proof.
    intros Hle Hle'. rewrite progress_le_inv in Hle.
    destruct Hle;last done. exfalso;eapply progress_le_gt_False;eauto.
  Qed.

  Lemma progress_le_refl pg : progress_le pg pg.
  Proof. right;split;lia. Qed.

  Lemma progress_lt_trans'1 pg1 pg2 pg3 :
    progress_lt pg1 pg2 ->
    progress_le pg2 pg3 -> progress_lt pg1 pg3.
  Proof.
    intros Hlt Hle. rewrite progress_le_inv in Hle.
    destruct Hle as [Hlt'|[]].
    eapply progress_lt_trans;eauto.
    done.
  Qed.

  Lemma progress_lt_trans'2 pg1 pg2 pg3 :
    progress_le pg1 pg2 ->
    progress_lt pg2 pg3 -> progress_lt pg1 pg3.
  Proof.
    intros Hle Hlt. rewrite progress_le_inv in Hle.
    destruct Hle as [Hlt'| ->].
    eapply progress_lt_trans;eauto.
    done.
  Qed.

  Lemma progress_le_trans pg1 pg2 pg3 :
    progress_le pg1 pg2 ->
    progress_le pg2 pg3 -> progress_le pg1 pg3.
  Proof.
    intros Hle Hlt. rewrite progress_le_inv in Hle.
    destruct Hle as [Hlt'| ->]. rewrite progress_le_inv.
    left. eapply progress_lt_trans'1;eauto.
    done.
  Qed.

  Lemma progress_nle_gt pg1 pg2 : (progress_le pg1 pg2 -> False) ->
                  progress_lt pg2 pg1.
  Proof.
    intros Hnle. destruct pg1; destruct pg2;subst;simpl in *.
    destruct n1.
    intros. destruct (decide (n = 0)%nat). right;simpl.
    destruct (decide (n2 < n0)%nat). lia. exfalso. apply Hnle.
    right;simpl;lia.
    left;simpl;lia.
    intros. destruct n. exfalso. apply Hnle. left;simpl;lia.
    destruct (decide (n < n1)%nat). exfalso. apply Hnle. left;simpl;lia.
    destruct (decide (n1 < n)%nat). left;simpl;lia.
    assert (n1 = n) as -> by lia. right;simpl. split;first done.
    destruct (decide (n2 < n0)%nat). done.
    exfalso. apply Hnle. right;simpl. split;lia.
  Qed.

  Lemma progress_nlt_ge pg1 pg2 : (progress_lt pg1 pg2 -> False) ->
                  progress_le pg2 pg1.
  Proof.
    intros Hnlt. destruct pg1; destruct pg2;subst;simpl in *.
    destruct n1.
    intros. destruct (decide (n = 0)%nat). right;simpl.
    destruct (decide (n2 <= n0)%nat). lia. exfalso. apply Hnlt.
    right;simpl;lia.
    left;simpl;lia.
    intros. destruct n. exfalso. apply Hnlt. left;simpl;lia.
    destruct (decide (n < n1)%nat). exfalso. apply Hnlt. left;simpl; lia.
    destruct (decide (n1 < n)%nat). left;simpl;lia.
    assert (n1 = n) as -> by lia. right;simpl. split;first done.
    destruct (decide (n2 <= n0)%nat). done.
    exfalso. apply Hnlt. right;simpl. split;lia.
  Qed.

  Lemma progress_iid_le_next_instr ts:
    let iis := (mk_iis_ni ts) in
    forall pg, progress_lt pg (iis_iid iis, iis_cntr iis) ->
          (pg.1 <= (get_progress ts).1)%nat.
  Proof.
    intros iis pg Hlt.
    rewrite /iis /= /mk_iis_ni /= in Hlt.
    destruct pg as [iid eid];rewrite /get_progress /=.
    destruct (decide ((iis_iid (ts_iis ts)) < iid)%nat);[|lia].
    destruct Hlt as [Hlt | [Heq Hlt ]];simpl in *;lia.
  Qed.

  Lemma progress_iid_le_same_instr ts:
    let pg' := (iis_iid (ts_iis ts), iis_cntr (ts_iis ts) + 1)%nat in
    forall pg, progress_lt pg pg' ->
          (pg.1 <= (get_progress ts).1)%nat.
  Proof.
    intros iis pg Hlt.
    rewrite /iis /= in Hlt.
    destruct pg as [iid eid];rewrite /=.
    destruct (decide ((iis_iid (ts_iis ts)) < iid)%nat);[|lia].
    destruct Hlt as [Hlt | [Heq Hlt ]];simpl in *;lia.
  Qed.

  Lemma progress_adjacent_incr_cntr ts pg' pg'':
    progress_le (get_progress ts) pg'' ->
    progress_lt pg'' pg' ->
    pg' = (get_progress (incr_cntr ts)) ->
    (get_progress ts) = pg''.
  Proof.
    rewrite /incr_cntr /get_progress /=.
    intros Hle Hlt ->.
    efeed pose proof (progress_iid_le_same_instr ts) as Hiid_le;eauto.
    rewrite Nat.le_lteq in Hiid_le; destruct Hiid_le as [Hiid_lt | Hiid_eq].
    - exfalso. rewrite progress_le_inv in Hle. destruct pg'';simpl in *. destruct Hle as [Hlt' | Heq].
      destruct Hlt' as [H1|H1];simpl in H1;try lia. inversion Heq;lia.
    - destruct pg'';simpl in *.
      subst n. destruct Hlt as [?|[_ Hlt]];simpl in *; [lia|].
      destruct Hle as [?|[_ Hle]];simpl in *; [lia|].
      by assert (n0 = iis_cntr (ts_iis ts)) as -> by lia.
  Qed.

  Definition ts_is_done_instr gr (tid : Tid) ts :=
    let instr_pg := get_progress ts in
    let instr_eids :=
      (filter (fun e => bool_decide (e.(EID.tid) = tid) && bool_decide (e.(EID.iid) = instr_pg.1 )) (Candidate.valid_eid gr)) in
    set_Forall (λ e, progress_lt (progress_of_node e) instr_pg) instr_eids.

  Lemma ts_is_done_instr_inv gr (tid : Tid) ts:
    let instr_pg := get_progress ts in
    ts_is_done_instr gr tid ts ->
    forall pg,
    progress_is_valid gr tid pg ->
    instr_pg.1 = pg.1 ->
    progress_lt pg instr_pg.
  Proof.
    rewrite /ts_is_done_instr /=.
    intros Hdone pg Hvalid Hiid_eq.
    specialize (Hdone (EID.make tid pg.1 pg.2)).
    rewrite /progress_of_node /= in Hdone.
    apply Hdone.
    rewrite elem_of_filter /=.
    split. case_bool_decide;[case_bool_decide;done|done].
    apply Hvalid.
  Qed.

  Lemma ts_is_done_instr_progress_invalid gr (tid : Tid) ts:
    let instr_pg := get_progress ts in
    ts_is_done_instr gr tid ts ->
    ¬ progress_is_valid gr tid instr_pg.
  Proof.
    intros ? Hdone Hvalid.
    eapply progress_lt_refl_False.
    eapply ts_is_done_instr_inv;eauto.
  Qed.

  (* progress of any local event is behind the latest progress *)
  Definition ts_is_done_thd gr (tid : Tid) ts :=
    set_Forall (λ e, progress_lt (progress_of_node e) (get_progress ts)) (Graph.local_eids gr tid).

  Lemma ts_is_done_thd_inv gr (tid : Tid) ts:
    let last_pg := get_progress ts in
    ts_is_done_thd gr tid ts ->
    forall pg,
    progress_is_valid gr tid pg ->
    progress_lt pg last_pg.
  Proof.
    rewrite /ts_is_done_thd /=.
    intros Hdone pg Hvalid.
    specialize (Hdone (EID.make tid pg.1 pg.2)).
    rewrite /progress_of_node /= in Hdone.
    apply Hdone.
    rewrite elem_of_filter /=.
    split; [done|apply Hvalid].
  Qed.

  Lemma ts_is_done_thd_progress_invalid gr (tid : Tid) ts:
    let last_pg := get_progress ts in
    ts_is_done_thd gr tid ts ->
    ¬ progress_is_valid gr tid last_pg.
  Proof.
    intros ? Hdone Hvalid.
    eapply progress_lt_refl_False.
    eapply ts_is_done_thd_inv;eauto.
  Qed.

  Lemma progress_to_node_mk_eid_ii tid ts pg:
    get_progress ts = pg ->
    progress_to_node pg tid = mk_eid_ii ts tid.
  Proof.
    intros Hpg. rewrite /progress_to_node /mk_eid_ii.
    rewrite -Hpg. destruct pg;done.
  Qed.

  Lemma progress_adjacent_incr_cntr' ts pg:
    progress_lt pg (get_progress (incr_cntr ts)) <->
    progress_le pg (get_progress ts).
  Proof.
    rewrite /incr_cntr /get_progress /=.
    split.
    {
      intros Hlt.
      efeed pose proof (progress_iid_le_same_instr ts) as Hiid_le;eauto.
      rewrite Nat.le_lteq in Hiid_le; destruct Hiid_le as [Hiid_lt | Hiid_eq].
      - left;done.
      - destruct pg;simpl in *.
        subst n. destruct Hlt as [?|[_ Hlt]];simpl in *; [lia|].
        right;split. done. simpl;lia.
    }
    {
      intros Hle. rewrite progress_le_inv in Hle.
      destruct Hle as [Hlt | ->].
      eapply progress_lt_trans;eauto.
      right. split; simpl;lia.
      right. split; simpl;lia.
    }
  Qed.

  (* progress of any local event is after or equal to the initial progress,
   this combined with above and some others can give us that all thread local events are checked if we have a complete local execution *)
  Definition progress_is_init gr (tid : Tid) pg :=
    set_Forall (λ e, progress_le pg (progress_of_node e)) (Graph.local_eids gr tid).

End ThreadState.

Notation "p1 '<p' p2" := (ThreadState.progress_lt p1 p2) (at level 50).
Notation "p1 '<=p' p2" := (ThreadState.progress_le p1 p2) (at level 50).

Module GlobalState.

  Export Graph.

  Record t :=
    make {
        gs_graph : Graph.t;
        gs_gimem : GInstrMem.t;
      }.

End GlobalState.


Module LThreadState.
  Export ThreadState.

  Inductive t :=
  | LTSNormal (ts : ThreadState.t)
  | LTSDone (ts : ThreadState.t).

  Definition is_done lts :=
    match lts with
    | LTSDone _ => true
    | LTSNormal _ => false
    end.

  Notation is_terminated := is_done.

  Definition get_progress lts :=
    match lts with
    | LTSNormal ts => get_progress ts
    | LTSDone ts => get_progress ts
    end.

  (* Prop version *)
  Notation at_progress lts pg := (LThreadState.get_progress lts = pg).

  Lemma progress_unique s pg pg':
    at_progress s pg ->
    at_progress s pg' -> pg = pg'.
  Proof.
    intros H1 H2. destruct s;try done;
      rewrite H1 in H2; inversion_clear H2; done.
  Qed.

End LThreadState.

Section machine_mixin.
  Context {local_state global_const id : Type}.
  Context (terminated : local_state → bool).

  Context (prim_step : global_const -> id → local_state → local_state → Prop).

  Record MachineMixin := {
    mixin_terminated_stuck g i σ σ' :
      prim_step g i σ σ' → terminated σ = false;
  }.
End machine_mixin.

Module LThreadStep.
  Import GInstrMem.
  Import AAInter.
  Import GlobalState.
  Export LThreadState.

  (* union of all register dependencies + memory dependencies *)
  Definition deps_of_depon tid ts dep :=
    match dep with
    (* None is not reachable, but we might need to fix it. Since [None] is interpreted as
            "depending on all previous registers and memory values that were read" in the Interface *)
    | None => ∅
    | Some depon =>
        (* union of all register dependencies + memory dependencies *)
        fold_right (fun r acc => from_option (λ rd, rd.(reg_dep) ∪ acc) acc (ts.(ts_regs) !! r)) ∅ depon.(DepOn.regs)
        ∪
        fold_right (fun idx acc => from_option (λ md, {[EID.make tid ts.(ts_iis).(iis_iid) md]} ∪ acc) acc (ts.(ts_iis).(iis_mem_reads) !! idx)) ∅ depon.(DepOn.mem_reads)
    end.

  Inductive t (gs: GlobalState.t) (tid: Tid) : LThreadState.t -> LThreadState.t -> Prop :=
  | TStepReload ts rv instr:
    (* current instruction is done *)
    reqs_done ts ->
    (* all events of current instructions are checked *)
    ts_is_done_instr gs.(gs_graph) tid ts ->
    (* val of PC is [rv] *)
    ts.(ts_regs) !! RNPC = Some rv ->
    (* next instruction is [instr] *)
    gs.(gs_gimem) !! rv.(reg_val) = Some instr ->
    (* update [ts] with new trace *)
    t gs tid (LTSNormal ts) (LTSNormal ((reset_cntr ts) <| ts_reqs := (InstrInterp instr) |>))
  | TStepTerm ts rv :
    (* current instruction is done, address of the next instruction is [iaddr] *)
    reqs_done ts ->
    (* val of PC is [rv] *)
    ts.(ts_regs) !! RNPC = Some rv ->
    (* no more instructions to run *)
    gs.(gs_gimem) !! rv.(reg_val) = None ->
    (* fulfillment check *)
    ts_is_done_thd gs.(gs_graph) tid ts ->
    (* this thread is done *)
    t gs tid (LTSNormal ts) (LTSDone ts)
  | TStepRegRead ts r v ctxt :
    let req := (RegRead r true) in
    (* current request is RegRead, [ctxt] is the continuation *)
    next_req_is ts req ctxt ->
    (* we can find an event with same request in graph, the response is [v] *)
    gs.(gs_graph) !! (mk_eid_ii ts tid) = Some (IEvent req v) ->
    (* local reg has same value *)
    (∃ rv, ts.(ts_regs) !! r = Some rv ∧ rv.(reg_val) = v) ->
    (* increment [iis_cntr] and set [ctxt] as the new [ts_reqs] *)
    t gs tid (LTSNormal ts) (LTSNormal ((incr_cntr ts)
                                          <| ts_reqs := (ctxt v) |>))
  | TStepRegWrite ts r dep v ctxt :
    let req := (RegWrite r true dep v) in
    (* current request is RegWrite, [ctxt] is the continuation *)
    next_req_is ts req ctxt ->
    (* we can find an event with same request in graph, no response is expected*)
    gs.(gs_graph) !! (mk_eid_ii ts tid) = Some (IEvent req tt) ->
    (* computing the dependencies *)
    let reg_dep := deps_of_depon tid ts dep in
    (* incrementing [iis_cntr], updating register, setting [ctxt] as the new [ts_reqs] *)
    t gs tid (LTSNormal ts) (LTSNormal ((incr_cntr ts)
                                          <| ts_regs := <[r := mk_regval v reg_dep]>(ts.(ts_regs)) |>
                                          <| ts_reqs := (ctxt tt) |>))
  | TStepBranch ts baddr dep ctxt:
    let req := (BranchAnnounce baddr dep) in
    (* current request is RegWrite, [ctxt] is the continuation *)
    next_req_is ts req ctxt ->
    let eid := (mk_eid_ii ts tid) in
    (* we can find an event with same request in graph, no response is expected*)
    gs.(gs_graph) !! (mk_eid_ii ts tid) = Some (IEvent req tt) ->
    (* computing the dependencies *)
    let cond_dep := deps_of_depon tid ts dep in
    (* incrementing [iis_cntr], updating [ts_ctrl_srcs], setting [ctxt] as the new [ts_reqs] *)
    t gs tid (LTSNormal ts) (LTSNormal ((incr_cntr ts) <| ts_ctrl_srcs := cond_dep ∪ ts.(ts_ctrl_srcs) |>
                                                       <| ts_reqs := (ctxt tt) |>))
  | TStepBarrierDmb ts dκ ctxt:
    let req := (AAInter.Barrier (AAArch.DMB dκ)) in
    (* current request is RegWrite, [ctxt] is the continuation *)
    next_req_is ts req ctxt ->
    let eid := (mk_eid_ii ts tid) in
    (* we can find an event with same request in graph, no response is expected*)
    gs.(gs_graph) !! eid = Some (IEvent req tt) ->
    (* there are e_ctrl_src -ctrl-> eid *)
    ((ts.(ts_ctrl_srcs)) × ({[eid]})) ⊆ (Candidate.ctrl gs.(gs_graph)) ->
    (* incrementing [iis_cntr], updating [ts_po_src], setting [ctxt] as the new [ts_reqs] *)
    t gs tid (LTSNormal ts) (LTSNormal ((incr_cntr ts) <| ts_reqs := (ctxt tt) |>))
  | TStepBarrierIsb ts ctxt:
    let req := (AAInter.Barrier AAArch.ISB) in
    (* current request is RegWrite, [ctxt] is the continuation *)
    next_req_is ts req ctxt ->
    let eid := (mk_eid_ii ts tid) in
    (* we can find an event with same request in graph, no response is expected*)
    gs.(gs_graph) !! eid = Some (IEvent req tt) ->
    (* there are e_ctrl_src -ctrl-> eid *)
    ((ts.(ts_ctrl_srcs)) × ({[eid]})) ⊆ (Candidate.ctrl gs.(gs_graph)) ->
    (* incrementing [iis_cntr], updating [ts_po_src], setting [ctxt] as the new [ts_reqs] *)
    t gs tid (LTSNormal ts) (LTSNormal ((incr_cntr ts) <| ts_reqs := (ctxt tt) |>))
  | TStepReadMem ts sz rreq mv ctxt:
    let req := (MemRead sz rreq) in
    (* current request is RegWrite, [ctxt] is the continuation *)
    next_req_is ts req ctxt ->
    let eid := (mk_eid_ii ts tid) in
    let resp := (inl (mv, None)) in
    (* we can find an event with same request in graph *)
    gs.(gs_graph) !! eid = Some (IEvent req resp) ->
    (* there are e_addr_src -addr-> eid *)
    ((deps_of_depon tid ts rreq.(ReadReq.addr_dep_on)) × ({[eid]})) ⊆ (Candidate.addr gs.(gs_graph)) ->
    (* there are e_ctrl_src -ctrl-> eid *)
    ((ts.(ts_ctrl_srcs)) × ({[eid]})) ⊆ (Candidate.ctrl gs.(gs_graph)) ->
    (* incrementing [iis_cntr], updating [ts_po_src], setting [ctxt] as the new [ts_reqs] *)
    t gs tid (LTSNormal ts) (LTSNormal ((incr_cntr (ts <| ts_iis := (ts.(ts_iis) <| iis_mem_reads := ((ts.(ts_iis).(iis_mem_reads)) ++ [ts.(ts_iis).(iis_cntr)] )|>)|>))
                                                       <| ts_reqs := (ctxt resp) |>
                                                       <| ts_rmw_pred := if AACandExec.Candidate.kind_of_rreq_is_atomic rreq then Some eid else ts.(ts_rmw_pred) |>))
  | TStepWriteMem ts sz wreq ctxt:
    AACandExec.Candidate.kind_of_wreq_is_atomic wreq = false ->
    let req := (MemWrite sz wreq) in
    (* current request is MemWrite, [ctxt] is the continuation *)
    next_req_is ts req ctxt ->
    let eid := (mk_eid_ii ts tid) in
    let resp := (inl None) in
    (* we can find an event with same request in graph, no response is expected*)
    gs.(gs_graph) !! eid = Some (IEvent req resp) ->
    (* there are e_addr_src -addr-> eid *)
    ((deps_of_depon tid ts wreq.(WriteReq.addr_dep_on)) × ({[eid]})) ⊆ (Candidate.addr gs.(gs_graph)) ->
    (* there are e_data_src -data-> eid *)
    ((deps_of_depon tid ts wreq.(WriteReq.data_dep_on)) × ({[eid]})) ⊆ (Candidate.data gs.(gs_graph)) ->
    (* there are e_ctrl_src -ctrl-> eid *)
    ((ts.(ts_ctrl_srcs)) × ({[eid]})) ⊆ (Candidate.ctrl gs.(gs_graph)) ->
    (* incrementing [iis_cntr], updating [ts_po_src], setting [ctxt] as the new [ts_reqs] *)
    t gs tid (LTSNormal ts) (LTSNormal ((incr_cntr ts) <| ts_reqs := (ctxt resp) |>))
  | TStepWriteMemAtomicSucc ts sz wreq ctxt rmw_pred:
    AACandExec.Candidate.kind_of_wreq_is_atomic wreq = true ->
    ts.(ts_rmw_pred) = Some rmw_pred ->
    let req := (MemWrite sz wreq) in
    (* current request is MemWrite, [ctxt] is the continuation *)
    next_req_is ts req ctxt ->
    let eid := (mk_eid_ii ts tid) in
    let resp := (inl (Some true)) in
    (* we can find an event with same request in graph, respond with succuss*)
    gs.(gs_graph) !! eid = Some (IEvent req resp) ->
    (rmw_pred, eid) ∈ (Candidate.rmw gs.(gs_graph)) ->
    (* there are e_addr_src -addr-> eid *)
    ((deps_of_depon tid ts wreq.(WriteReq.addr_dep_on)) × ({[eid]})) ⊆ (Candidate.addr gs.(gs_graph)) ->
    (* there are e_data_src -data-> eid *)
    ((deps_of_depon tid ts wreq.(WriteReq.data_dep_on)) × ({[eid]})) ⊆ (Candidate.data gs.(gs_graph)) ->
    (* there are e_ctrl_src -ctrl-> eid *)
    ((ts.(ts_ctrl_srcs)) × ({[eid]})) ⊆ (Candidate.ctrl gs.(gs_graph)) ->
    (* incrementing [iis_cntr], updating [ts_po_src], setting [ctxt] as the new [ts_reqs] *)
    t gs tid (LTSNormal ts) (LTSNormal ((incr_cntr ts) <| ts_reqs := (ctxt resp) |>))
  | TStepWriteMemAtomicFail ts sz wreq ctxt:
    AACandExec.Candidate.kind_of_wreq_is_atomic wreq = true ->
    let req := (MemWrite sz wreq) in
    next_req_is ts req ctxt ->
    let eid := (mk_eid_ii ts tid) in
    let resp := (inl (Some false)) in
    (* we can find an event with same request in graph, respond with failure*)
    gs.(gs_graph) !! eid = Some (IEvent req resp) ->
    (* incrementing [iis_cntr], updating [ts_po_src], setting [ctxt] as the new [ts_reqs] *)
    t gs tid (LTSNormal ts) (LTSNormal ((incr_cntr ts) <| ts_reqs := (ctxt resp) |>))
  .

  Lemma step_not_terminated gs tid lts lts' :
    t gs tid lts lts' → is_terminated lts = false.
  Proof. intros [];reflexivity. Qed.

  Lemma steps_not_terminated {gs tid lts} lts' n :
    nsteps (t gs tid) (S n) lts lts' ->
    is_terminated lts = false.
  Proof. inversion 1. by eapply step_not_terminated. Qed.

  Lemma machine_mixin : MachineMixin is_terminated t.
  Proof.
    refine {| mixin_terminated_stuck := step_not_terminated |}.
  Qed.

  Lemma step_progress_mono {gs tid lts lts'} :
    t gs tid lts lts' ->
    is_terminated lts' = false ->
    (get_progress lts) <p (get_progress lts').
  Proof.
    inversion 1;inversion 1;
      subst;rewrite /reset_cntr /incr_cntr /ThreadState.get_progress /=;try (right;simpl;split;lia).
    left. simpl;lia.
  Qed.

  Lemma step_progress_mono' {gs tid lts lts'} :
    t gs tid lts lts' ->
    (get_progress lts) <=p (get_progress lts').
  Proof.
    inversion 1;
      subst;rewrite /reset_cntr /incr_cntr /ThreadState.get_progress /=;try (right;simpl;split;lia).
    left. simpl;lia.
  Qed.

  Lemma steps_progress_mono {gs tid lts lts'} n :
    nsteps (t gs tid) (S n) lts lts' ->
    is_terminated lts' = false ->
    (get_progress lts) <p (get_progress lts').
  Proof.
    revert lts lts'. induction n; intros ?? Hsteps Hterm.
    - inversion Hsteps as [|???lts''??Hstep?Hsteps'];subst.
      inversion Hsteps';subst.
      eapply step_progress_mono;eauto.
    - inversion Hsteps as [|???lts''??Hstep?Hsteps'];subst.
      set pg'' := (get_progress lts'').
      eapply (progress_lt_trans). eapply step_progress_mono;eauto.
      inversion Hsteps';subst. eapply step_not_terminated;eauto.
      eapply IHn;eauto.
  Qed.

  Lemma steps_progress_mono' {gs tid lts lts'} n :
    nsteps (t gs tid) n lts lts' ->
    (get_progress lts) <=p (get_progress lts').
  Proof.
    revert lts lts'. induction n; intros ?? Hsteps.
    - inversion Hsteps;subst.
      apply progress_le_refl.
    - inversion Hsteps as [|???lts''??Hstep?Hsteps'];subst.
      set pg'' := (get_progress lts'').
      eapply (progress_le_trans).
      eapply step_progress_mono';eauto.
      eapply IHn;eauto.
  Qed.

  Lemma step_progress_ne {gs tid} lts lts':
    t gs tid lts lts' ->
    is_terminated lts' = false ->
    (get_progress lts) ≠ (get_progress lts').
  Proof. intros. apply progress_lt_neq. eapply LThreadStep.step_progress_mono;eauto. Qed.

  Lemma step_progress_done_invalid {gs tid lts lts'} pg:
    t gs tid lts lts' ->
    is_done lts' ->
    at_progress lts pg ->
    ¬ progress_is_valid (gs_graph gs) tid pg.
  Proof.
    inversion 1 as [ |??????Hdone| | | | | | | | |];inversion 1;subst.
    inversion 1. intros ?.
    specialize (Hdone (progress_to_node pg tid)).
    subst pg. feed specialize Hdone.
    apply elem_of_filter. split;done.
    rewrite /progress_of_node /progress_to_node /= in Hdone.
    eapply progress_lt_refl_False. apply Hdone.
  Qed.

  (* NOTE it is not true! *)
  (* Lemma step_progress_valid {gs tid} s s' pg: *)
  (*   t gs tid s s' -> *)
  (*   at_progress s pg -> *)
  (*   progress_is_valid gs.(GlobalState.gs_graph) tid pg. *)

  (* This is the key helper for showing that we don't skip events *)
  Lemma step_progress_adjacent {gs tid} s s':
    t gs tid s s' ->
    (* if there is another valid event between the two, it has to be pg *)
    forall pg'', progress_is_valid gs.(GlobalState.gs_graph) tid pg'' ->
            (get_progress s) <=p pg'' -> pg'' <p (get_progress s') ->
    (get_progress s) = pg''.
  Proof.
    intros Hstep pg'' Hvalid Hge Hlt.
    inversion Hstep;subst.
    - epose proof ts_is_done_instr_inv as Hinv.
      feed specialize Hinv. eauto.
      epose proof (progress_iid_le_next_instr _ _ Hlt) as Hiid_le.
      rewrite Nat.le_lteq in Hiid_le; destruct Hiid_le as [Hiid_lt | Hiid_eq]
      + exfalso. rewrite progress_le_inv in Hge. destruct pg'';simpl in *. destruct Hge as [Hlt' | Hlt'];try lia.
        destruct Hlt' as [Hlt' | Hlt']; simpl in Hlt';lia. inversion Hlt';lia.
      + efeed specialize Hinv;eauto. exfalso. eapply progress_le_gt_False;eauto.
    - exfalso. epose proof ts_is_done_thd_inv as Hinv.
      efeed specialize Hinv; eauto. eapply progress_le_gt_False;eauto.
    - eapply progress_adjacent_incr_cntr;eauto.
    - eapply progress_adjacent_incr_cntr;eauto.
    - eapply progress_adjacent_incr_cntr;eauto.
    - eapply progress_adjacent_incr_cntr;eauto.
    - eapply progress_adjacent_incr_cntr;eauto.
    - eapply progress_adjacent_incr_cntr;eauto.
    - eapply progress_adjacent_incr_cntr;eauto.
    - eapply progress_adjacent_incr_cntr;eauto.
    - eapply progress_adjacent_incr_cntr;eauto.
  Qed.

  Lemma step_progress_valid_is_reqs_nonempty gs tid s' ts pg:
    ThreadState.get_progress ts = pg ->
    t gs tid (LTSNormal ts) s' ->
    (ThreadState.progress_is_valid (GlobalState.gs_graph gs) tid pg)
    <->
    (ThreadState.ts_reqs ts ≠ EmptyInterp).
  Proof.
    intros Hpg Hstep.
    inversion Hstep;subst;
      match goal with
      | [ Hreq_eq : ThreadState.reqs_done ?ts |- _ ] => rewrite /ThreadState.reqs_done in Hreq_eq;
                                                       rewrite Hreq_eq;split;last done;intros
      | [ Hreq_eq : next_req_is ?ts ?req ?ctxt |- _ ] =>
          rewrite /next_req_is in Hreq_eq;
          rewrite Hreq_eq;split;first done;intros _;
          rewrite /progress_is_valid;
          (erewrite progress_to_node_mk_eid_ii;eauto);
          set_unfold;eauto
      | _ => idtac
      end.
    eapply ts_is_done_instr_inv in H1;eauto; exfalso;eapply ThreadState.progress_lt_refl_False;eauto.
    eapply ts_is_done_thd_inv in H3;eauto; exfalso;eapply ThreadState.progress_lt_refl_False;eauto.
  Qed.

  Lemma steps_traverse_all_eids {gs tid} n lts lts' :
    nsteps (t gs tid) n lts lts' →
    is_terminated lts' = false ->
    ∀ pg'', progress_is_valid (gs.(gs_graph)) tid pg'' ->
    (exists n1 n2 lts'', n1 + n2 = n ∧ n2 > 0 ∧
                    get_progress lts'' = pg'' ∧
                    nsteps (t gs tid) n1 lts lts'' ∧
                    nsteps (t gs tid) n2 lts'' lts')%nat
    <-> (get_progress lts  <=p pg'' ∧ pg'' <p  get_progress lts').
  Proof.
    revert n lts lts'.
    induction n as [|n IH]=> lts lts' /=.
    - inversion_clear 1.
      intros Hnotgs ? Hvalid. split.
      + intros (n1 & n2 & lts'' & Heqn & Hgtz & Hpg'' & Hsteps1 & Hsteps2). lia.
      + intros (Hge & Hlt'); exfalso. by eapply progress_le_gt_False.
    - intros Hsteps Hngs ? Hvalid. split.
      + intros (n1 & n2 & lts'' & Hsum & Hgtz& Hpg'' & Hsteps1 & Hsteps2).
        destruct n1.
        * inversion Hsteps1;subst.
          split; first apply progress_le_refl. eapply steps_progress_mono;eauto.
        * inversion_clear Hsteps1 as [|? ? lts''' ? Hfststep Hsteps1'].
        assert (n1 + n2 = n)%nat as Hsum' by lia.
        specialize (IH lts''' lts').
        feed specialize IH. rewrite -Hsum'. by eapply nsteps_trans. done.
        specialize (IH pg'' Hvalid). destruct IH as [IH _]. feed specialize IH.
        exists n1, n2, lts''. repeat (split;first done). done.
        destruct IH as (Hge & Hlt). split;last done.
        epose proof (step_progress_mono Hfststep) as Hlts. efeed specialize Hlts;eauto.
        destruct n;first lia. eapply (steps_not_terminated lts' n);eauto.
        rewrite -Hsum'. eapply nsteps_trans;eauto.
        epose proof (steps_progress_mono' _ Hsteps1') as Hle';auto.
        efeed specialize Hle';eauto. eapply progress_le_trans;eauto. apply progress_lt_le;auto.
      + intros (Hge & Hlt).
        inversion_clear Hsteps as [|? ? lts''' ? Hfststep Hsteps'].
        destruct n.
        * specialize (IH lts''' lts').
          feed specialize IH; auto.
          inversion Hsteps';subst.
          epose proof (step_progress_adjacent _ _) as Hpgeq;eauto.
          feed specialize Hpgeq;eauto.
          efeed specialize Hpgeq;eauto. subst pg''.
          exists 0%nat,1%nat, lts. split;[lia|split;[lia|]]. repeat (split;first done).
          split. constructor. by apply nsteps_once.
        * inversion_clear Hsteps'.
          destruct (decide ((get_progress lts''') = pg'')).
          -- specialize (IH lts''' lts').
             feed specialize IH;auto. eapply nsteps_l;eauto.
             specialize (IH _ Hvalid). destruct IH as [_ IH]. feed specialize IH.
             split;auto. subst pg''. apply progress_le_refl.
             exists 1%nat, (S n), lts'''. split;first lia.
             split;first lia. repeat (split;first done).
             split. econstructor;eauto. constructor. eapply nsteps_l;eauto.
          -- destruct (decide (pg'' <=p (get_progress lts'''))) as [Hle'|Hnle'].
             rewrite progress_le_inv in Hle'.
             destruct Hle';last done.
             efeed pose proof (step_progress_adjacent lts lts''' Hfststep);eauto.
             subst pg''.
             exists 0%nat, (S (S n)), lts.
             split;first done. split;first lia. split;first done.
             split. constructor. econstructor;eauto. eapply nsteps_l;eauto.
             specialize (IH lts''' lts').
             feed specialize IH; auto.  eapply nsteps_l;eauto.
             specialize (IH _ Hvalid). destruct IH as [_ IH]. feed specialize IH.
             split;last done. apply progress_nle_gt in Hnle'. rewrite progress_le_inv. left;done.
             destruct IH as (n1 & n2 & lts'' & Hsum & Hnz & ? & ? & ?). destruct n1.
             inversion H2. subst. done.
             exists (S (S n1)), n2, lts''. split;first lia.
             split;first lia. repeat (split;first done).
             split. econstructor. exact Hfststep. done. done.
  Qed.

  Definition eids_between gr tid lts lts' :=
    let (pg, pg') := (get_progress lts, get_progress lts') in
    let all_po_pre := filter (λ e : Eid, (progress_of_node e) <p pg') (local_eids gr tid) in
    let lt_po_pre := filter (λ e : Eid, (progress_of_node e) <p pg) (local_eids gr tid) in
    (all_po_pre ∖ lt_po_pre).

  Lemma elem_of_eids_between_in_thd gr tid lts lts' e:
    e ∈ eids_between gr tid lts lts' ->
    e.(EID.tid) = tid.
  Proof.
    rewrite /eids_between. destruct (get_progress lts);destruct (get_progress lts');intro;set_solver.
  Qed.

  Lemma eids_between_inv gr tid lts lts' :
    forall pg'',
    ( progress_is_valid gr tid pg'' ∧ get_progress lts <=p pg'' ∧ pg'' <pget_progress lts')
    <-> (progress_to_node pg'' tid) ∈ (eids_between gr tid lts lts').
  Proof.
    intros ?. split.
    - intros (Hvalid & Hge & Hlt).
      rewrite /eids_between /=.
      rewrite elem_of_difference;rewrite /progress_of_node /=;split.
      + apply elem_of_filter. split;first done.
        rewrite /local_eids /=. apply elem_of_filter. split;done.
      + intro Hf. rewrite elem_of_filter /= in Hf. destruct Hf as [Hlt' _].
        eapply progress_le_gt_False;eauto.
    - intros Helem.
      destruct (decide (eids_between gr tid lts lts' = ∅)) as [|Hnept];first set_solver.
      rewrite /eids_between in Helem.
      rewrite elem_of_difference elem_of_filter /progress_of_node /= in Helem.
      destruct Helem as [[Hlt Hvalid] Hnelem];split.
      + rewrite /local_eids elem_of_filter /= in Hvalid. destruct Hvalid as [_ ?];done.
      + split;last done. destruct (decide ((get_progress lts) <p pg'')) as [|Hlt'].
        by apply progress_lt_le.
        destruct (decide ((get_progress lts) = pg'')); [rewrite progress_le_inv;right;done|].
        destruct (decide ((get_progress lts) <=p pg'')) as [|Hnle];first done.
        apply progress_nle_gt in Hnle. exfalso.
        apply Hnelem;rewrite elem_of_filter /=;split;done.
  Qed.

  Lemma eids_between_inv_pg_valid gr (tid : Tid) lts lts' pg:
    (progress_to_node pg tid) ∈ eids_between gr tid lts lts' ->
    (progress_is_valid gr tid pg).
  Proof.
    rewrite /eids_between. destruct (get_progress lts);destruct (get_progress lts');intro;set_solver.
  Qed.

  Lemma steps_traversed_eids {gs tid} n lts lts' :
    nsteps (t gs tid) n lts lts' →
    is_terminated lts' = false ->
    ∀ pg'', progress_is_valid (gs.(gs_graph)) tid pg'' ->
    (exists n1 n2 lts'', n1 + n2 = n ∧ n2 > 0 ∧
                    get_progress lts'' = pg'' ∧
                    nsteps (t gs tid) n1 lts lts'' ∧
                    nsteps (t gs tid) n2 lts'' lts')%nat
    <-> (progress_to_node pg'' tid) ∈ (eids_between (gs.(gs_graph)) tid lts lts').
  Proof.
    intros. rewrite -eids_between_inv. epose proof steps_traverse_all_eids as Heq.
    efeed specialize Heq;eauto. rewrite Heq.
    split;intros (?&?);repeat destruct Hpg as [? Hpg];eauto.
  Qed.

  Lemma traversed_eids_empty {gs tid} lts :
    (eids_between (gs.(GlobalState.gs_graph)) tid lts lts) = ∅.
  Proof. rewrite /eids_between /=. rewrite difference_diag_L //. Qed.

  Lemma step_traversed_eids_valid_singleton {gs tid} lts lts' :
    t gs tid lts lts' →
    progress_is_valid (gs.(gs_graph)) tid (get_progress lts) ->
    (eids_between (gs.(GlobalState.gs_graph)) tid lts lts') = {[progress_to_node (get_progress lts) tid]}.
  Proof.
    intros Hstep Hvalid.
    destruct lts'.
    - apply set_eq. intros e. rewrite elem_of_singleton.
      split.
      + intro Hin.
        assert (e = (progress_to_node (progress_of_node e) tid)) as Heqe.
        {
          rewrite /progress_to_node /progress_of_node /=.
          destruct e eqn:Heqn. simpl.
          efeed pose proof elem_of_eids_between_in_thd as Htid;eauto.
          rewrite -Htid //.
        }
        rewrite Heqe in Hin.
        eapply (steps_traversed_eids 1) in Hin;eauto.
        destruct Hin as (n1 & n2 & lts'' & Hsum & Hgt & Hpg'' & Hstep1 & _).
        assert (n1 = 0)%nat as -> by lia.
        inversion Hstep1. subst. inversion Hpg''. rewrite Heqe. f_equal. eapply progress_unique;eauto.
        by apply nsteps_once.
        eapply eids_between_inv_pg_valid;eauto.
      + intros ->.
        eapply eids_between_inv.
        repeat split;try done. eapply progress_le_refl.
        eapply step_progress_mono;eauto.
    - exfalso. eapply step_progress_done_invalid;eauto.
  Qed.

  Lemma step_traversed_eids_done_empty {gs tid} lts lts' :
    t gs tid lts lts' →
    is_done lts' = true ->
    (eids_between (gs.(GlobalState.gs_graph)) tid lts lts') = ∅.
  Proof.
    inversion 1; inversion 1.
    rewrite /eids_between /=. set_solver +.
  Qed.

  Lemma step_traversed_eids_invalid_empty {gs tid} lts lts' :
    t gs tid lts lts' →
    forall pg, at_progress lts pg ->
          ¬ progress_is_valid (gs.(gs_graph)) tid pg ->
          (eids_between (gs.(GlobalState.gs_graph)) tid lts lts') = ∅.
  Proof.
    intros Hstep ? Hpg Hnvalid.
    destruct lts'.
    - apply set_eq. intros e. rewrite elem_of_empty.
      split;[|intro;exfalso;auto].
      intro Hin.
      assert (e = (progress_to_node (progress_of_node e) tid)) as Heqe.
      {
        rewrite /progress_to_node /progress_of_node /=.
        destruct e eqn:Heqn. simpl.
        efeed pose proof elem_of_eids_between_in_thd as Htid;eauto.
        rewrite -Htid //.
      }
      rewrite Heqe in Hin. pose proof Hin.
      eapply (steps_traversed_eids 1) in Hin;eauto.
      destruct Hin as (n1 & n2 & lts'' & Hsum & Hgt & Hpg'' & Hstep1 & _).
      assert (n1 = 0)%nat as -> by lia.
      inversion Hstep1. subst.
      subst. apply Hnvalid.
      eapply eids_between_inv_pg_valid;eauto. rewrite Hpg'' //.
      by apply nsteps_once.
      eapply eids_between_inv_pg_valid;eauto.
    - apply step_traversed_eids_done_empty;auto.
  Qed.

  Lemma progress_le_eids_subseteq gr tid pg pg' :
    pg <=p pg' ->
    filter (λ e : Eid, (progress_of_node e) <p pg) (local_eids gr tid) ⊆
      filter (λ e : Eid, (progress_of_node e) <p pg') (local_eids gr tid).
  Proof.
    intro Hle. rewrite elem_of_subseteq.
    intros ?. rewrite 2!elem_of_filter. intros [Hlt Hin].
    split;last done.
    rewrite progress_le_inv in Hle.
    destruct Hle as [Hlt'| ->];last done.
    eapply progress_lt_trans;eauto.
  Qed.

  (* This is the key lemma used in the induction case of the nsteps lifting lemma. *)
  Lemma steps_traversed_eids_union {gs tid} n lts lts'' lts' :
    t gs tid lts lts'' →
    nsteps (t gs tid) n lts'' lts' →
    (eids_between (gs.(gs_graph)) tid lts lts')
    = (if (bool_decide (progress_is_valid (gs.(gs_graph)) tid (get_progress lts)))
       then {[progress_to_node (get_progress lts) tid]} else ∅) ∪ (eids_between (gs.(gs_graph)) tid lts'' lts').
  Proof.
    intros Hstep Hsteps. rewrite /eids_between.
    destruct n.
    - inversion Hsteps. subst.
      rewrite difference_diag_L union_empty_r_L.
      case_bool_decide.
      erewrite <-(step_traversed_eids_valid_singleton lts lts');eauto. rewrite /eids_between //.
      erewrite <-(step_traversed_eids_invalid_empty lts lts');eauto.
    - inversion Hsteps as [|???? Hstep']. subst.
    set (B := filter (λ e : Eid, progress_of_node e <p (get_progress lts)) _).
    set (C := filter (λ e : Eid, progress_of_node e <p (get_progress lts')) _).
    set (D := filter (λ e : Eid, progress_of_node e <p (get_progress lts'')) _).
    assert (D ⊆ C). rewrite /C /D. apply progress_le_eids_subseteq.
    eapply (steps_progress_mono' _ Hsteps);eauto.
    assert (B ⊆ D). rewrite /B /D. apply progress_le_eids_subseteq.
    eapply (steps_progress_mono' 1). apply nsteps_once. apply Hstep.
    erewrite difference_split_subseteq_L;eauto.
    case_bool_decide.
    erewrite <-(step_traversed_eids_valid_singleton lts lts'');eauto. rewrite /eids_between //.
    rewrite /C /D /B. set_solver+.
    erewrite <-(step_traversed_eids_invalid_empty lts lts'');eauto. rewrite /eids_between //.
    rewrite /C /D /B. set_solver+.
  Qed.

  Definition eids_from_init gr tid pg := filter (λ e : Eid, (progress_of_node e) <p pg) (local_eids gr tid).

  Lemma eids_from_init_empty {gr tid} pg :
    ThreadState.progress_is_init gr tid pg ->
    eids_from_init gr tid pg = ∅.
  Proof.
    intro Hinit. rewrite /eids_from_init.
    apply set_eq. split;last done.
    rewrite elem_of_filter.
    intros [Hlt Hin]. exfalso.
    specialize (Hinit _ Hin).
    eapply ThreadState.progress_le_gt_False;eauto. exact Hinit.
  Qed.

  Lemma eids_from_init_po_pred_of gr (tid : Tid) pg:
    AACandExec.NMSWF.wf gr ->
    progress_is_valid gr tid pg ->
    po_pred_of gr (ThreadState.progress_to_node pg tid) = eids_from_init gr tid pg.
  Proof.
    intros Hwf Hvalid. apply set_eq.
    intros e. rewrite elem_of_filter. rewrite /po_pred_of.
    split.
    - intro Hpo.
      set_unfold in Hpo.
      destruct Hpo as [e' [-> Hpo]].
      assert(Heid : EID.tid e = tid). { pose (G:= Graph.po_valid_eids gr e (progress_to_node pg tid) Hwf Hpo). destruct G as [_ ->]. by simpl. }
      pose proof (progress_lt_po _ tid (progress_of_node e) pg Hwf) as [_ Himp].
      feed specialize Himp. rewrite progress_to_node_of_node //.
      destruct Himp as [Hlt [Hvalide Hvalid']].
      split;first auto.
      apply elem_of_filter. split;first assumption.
      by rewrite /progress_is_valid progress_to_node_of_node in Hvalide.
    - intros [Hlt Hlc].
      rewrite elem_of_filter in Hlc.
      destruct Hlc as [Htid Hvalid'].
      pose proof (progress_lt_po _ tid (progress_of_node e) pg Hwf) as [Himp _].
      feed specialize Himp.
      split;auto. split;auto. rewrite /progress_is_valid.
      rewrite progress_to_node_of_node //.
      set_unfold. exists (progress_to_node pg tid).
      split;auto. rewrite progress_to_node_of_node // in Himp.
  Qed.

  Lemma step_traversed_eids_from_init_union {gs tid} lts lts' :
    t gs tid lts lts' →
    (eids_from_init (gs.(gs_graph)) tid (get_progress lts'))
    = (if (bool_decide (progress_is_valid (gs.(gs_graph)) tid (get_progress lts)))
       then {[progress_to_node (get_progress lts) tid]} else ∅) ∪ (eids_from_init (gs.(gs_graph)) tid (get_progress lts)).
  Proof.
    intros Hstep.
    rewrite /eids_from_init.
    efeed pose proof (LThreadStep.step_progress_mono' Hstep) as Hle;eauto.
    case_bool_decide as Hpg_valid.
    - erewrite <-(step_traversed_eids_valid_singleton lts lts');eauto. rewrite /eids_between //.
      epose proof (progress_le_eids_subseteq (gs_graph gs) tid (get_progress lts) (get_progress lts') Hle) as Hsub.
      rewrite difference_union_L. set_solver + Hsub.
    - rewrite union_empty_l_L. symmetry.
      pose proof (LThreadStep.step_progress_mono' Hstep).
      apply set_eq. intros x. rewrite 2!elem_of_filter. split.
      intros [Hlt Hvalid]. split;last auto.
      eapply ThreadState.progress_lt_trans'1;eauto.
      intros [Hlt Hvalid]. split;last auto.
      destruct (decide (ThreadState.progress_of_node x <p (get_progress lts))) as [|Hnlt]. done.
      apply ThreadState.progress_nlt_ge in Hnlt.
      rewrite elem_of_filter in Hvalid. destruct Hvalid as [Hvalid Htid].
      efeed pose proof (LThreadStep.step_progress_adjacent _ _ Hstep (ThreadState.progress_of_node x))as Heq;auto.
      rewrite /ThreadState.progress_is_valid. rewrite ThreadState.progress_to_node_of_node //.
      exfalso. apply Hpg_valid.
      rewrite /ThreadState.progress_is_valid Heq. rewrite ThreadState.progress_to_node_of_node //.
  Qed.

  Lemma eids_between_inv_tid_eq gr (tid : Tid) lts lts' e:
    e ∈ eids_between gr tid lts lts' ->
    e.(EID.tid) = tid.
  Proof.
    rewrite /eids_between.
    destruct (LThreadState.get_progress lts);destruct (LThreadState.get_progress lts');intro;set_solver.
  Qed.

  Lemma eids_between_full gs tid lts lts':
    ThreadState.progress_is_init (gs.(GlobalState.gs_graph)) tid (LThreadState.get_progress lts) ->
    is_terminated lts' = true ->
    (* NOTE: the equality holds only if we take at least a step to Done, it proprogate to [tpsteps] *)
    (∃ n, nsteps (LThreadStep.t gs tid) (S n) lts lts') ->
         filter (Graph.is_local_node_of tid) (Candidate.valid_eid (gs.(GlobalState.gs_graph)))
         = LThreadStep.eids_between (gs.(GlobalState.gs_graph)) tid lts lts'.
  Proof.
    intros Hinit Hterm [n Hstep].
    rewrite /eids_between.
    epose proof (eids_from_init_empty (LThreadState.get_progress lts)) as Hept.
    feed specialize Hept; eauto.
    rewrite /eids_from_init in Hept. rewrite Hept.
    rewrite difference_empty_L.
    apply nsteps_inv_r in Hstep. destruct Hstep as [? [? Hstep]].
    inversion Hstep as [ | ? ? ? ? ? Hdone | | | | | | | | | ];subst;try inversion Hterm.
    apply set_eq. intro. rewrite /local_eids 3!elem_of_filter.
    split.
    - intros [Htid Hin]. split;last done.
      specialize (Hdone x); feed specialize Hdone.
      rewrite /local_eids elem_of_filter //. done.
    - intros [? ?]. done.
  Qed.

End LThreadStep.
