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

(** This file contains construction of basic RAs *)
(* From stdpp Require Export namespaces. *)

From iris.algebra Require Export agree gmap gset csum lib.dfrac_agree.
From iris.base_logic.lib Require Export ghost_map saved_prop.
From iris.proofmode Require Export tactics.
From iris_named_props Require Export named_props.
From iris.base_logic.lib Require Export iprop.
From iris.bi.lib Require Import fractional.

(* need physical states from these files *)
From self.lang Require Import mm instrs.
From self.algebra Require Export ghost_map_ag mono_pg.
From self.algebra.lib Require Export saved_prot.

(* Make Coq aware of Σ with type class search *)
Class CMRA `{Σ: !gFunctors} := {}.

Class AABaseInG `{CMRA Σ} := {
  AAInGBaseEdge :: inG Σ (agreeR (leibnizO Graph.t));
  (* node_annotation *)
  AAInGNodeAnnot :: ghost_map_agG Σ Eid gname;
  AAInGNodeAnnotGnames :: inG Σ (authR (gset_disjUR gname));
  AAInGSavedProp :: savedPropG Σ;
  AAInGInstrMem :: inG Σ (agreeR (gmapO Addr (leibnizO Instruction)));
  AAInGLocalWriteMap :: ghost_mapG Σ Addr (option Eid);
  AAInGPoSrcMono :: inG Σ (mono_pgR);
  AAInGPoSrcOneShot :: inG Σ (csumR (dfrac_agreeR unitO) (agreeR (prodO gnameO natO)));
  AAInGRmwSrc :: inG Σ (authR (gset_disjUR Eid));
  AAInGProtGNMap :: ghost_mapG Σ Addr gname;
  AAInGProtPred :: savedProtG Σ Val Eid;
}.

Section genAABaseG.
  Class AABaseG `{CMRA Σ} :=
    GenAABaseG{
        AAIn :: AABaseInG;
        AAGraphN : gname;
        AANodeAnnotN: gname;
        AAInstrN : gname;
        AARmwTokenN : gname;
        AAProtN : gname;
      }.

  #[global] Arguments AAGraphN {Σ _ _}.
  #[global] Arguments AANodeAnnotN {Σ _ _}.
  #[global] Arguments AAInstrN {Σ _ _}.
  #[global] Arguments AARmwTokenN {Σ _ _}.
  #[global] Arguments AAProtN {Σ _ _}.

  Definition AABaseΣ : gFunctors :=
    #[ GFunctor (agreeR (leibnizO Graph.t));
       savedPropΣ;
       ghost_map_agΣ Eid gname;
       GFunctor (authR (gset_disjUR gname));
       GFunctor (agreeR (gmapO Addr (leibnizO Instruction)));
       ghost_mapΣ Addr (option Eid);
       GFunctor mono_pgR;
       GFunctor (csumR (dfrac_agreeR unitO) (agreeR (prodO gnameO natO)));
       GFunctor (authR (gset_disjUR Eid));
       ghost_mapΣ Addr gname;
       savedProtΣ Val Eid
      ].

  #[global] Instance subG_AABasepreG `{CMRA Σ}: subG AABaseΣ Σ -> AABaseInG.
  Proof. solve_inG. Qed.

End genAABaseG.

Section definition.
  Context `{CMRA Σ} `{!AABaseG}.

  (** Graph facts, including edges and nodes *)
  Definition graph_agree_def (gr : Graph.t) : iProp Σ :=
    own AAGraphN ((to_agree gr) : (agreeR (leibnizO Graph.t))).
  Definition graph_agree_aux : seal (@graph_agree_def). Proof. by eexists. Qed.
  Definition graph_agree := graph_agree_aux.(unseal).
  Definition graph_agree_eq : @graph_agree = @graph_agree_def := graph_agree_aux.(seal_eq).

  #[global] Instance graph_agree_persist gr: Persistent(graph_agree gr).
  Proof. rewrite graph_agree_eq /graph_agree_def. apply _. Qed.

  Lemma graph_agree_agree gr gr':
    graph_agree gr -∗ graph_agree gr' -∗ ⌜gr = gr'⌝.
  Proof.
    iIntros "He Hξ". rewrite graph_agree_eq /graph_agree_def.
    iDestruct (own.own_valid_2 with "He Hξ") as "%Hvalid".
    rewrite to_agree_op_valid_L in Hvalid. done.
  Qed.

  (** node anotation *)
  Definition node_annot_agmap_def (eid : Eid) (N : gname) : iProp Σ :=
    ghost_map_ag_elem AANodeAnnotN eid N.
  Definition node_annot_agmap_aux : seal (@node_annot_agmap_def). Proof. by eexists. Qed.
  Definition node_annot_agmap := node_annot_agmap_aux.(unseal).
  Definition node_annot_agmap_eq : @node_annot_agmap = @node_annot_agmap_def := node_annot_agmap_aux.(seal_eq).

  #[global] Instance node_annot_agmap_persist eid e: Persistent(node_annot_agmap eid e).
  Proof. rewrite node_annot_agmap_eq /node_annot_agmap_def. apply _. Qed.

  Lemma node_annot_agmap_both_agree n E m:
    node_annot_agmap n E -∗ ghost_map_ag_auth AANodeAnnotN m -∗ ⌜m !! n = Some E⌝.
  Proof.
    iIntros "He Hauth". rewrite node_annot_agmap_eq /node_annot_agmap_def.
    iApply (ghost_map_ag.ghost_map_ag_lookup with "Hauth He").
  Qed.

  (** instructions *)
  Definition instr_table_agree_def (gi : gmap Addr Instruction) : iProp Σ :=
      own AAInstrN (to_agree (gi: gmapO Addr (leibnizO Instruction))).
  Definition instr_table_agree_aux : seal (@instr_table_agree_def). Proof. by eexists. Qed.
  Definition instr_table_agree := instr_table_agree_aux.(unseal).
  Definition instr_table_agree_eq : @instr_table_agree = @instr_table_agree_def := instr_table_agree_aux.(seal_eq).

  #[global] Instance instr_table_persist gi: Persistent (instr_table_agree gi).
  Proof.
    rewrite instr_table_agree_eq /instr_table_agree_def. apply _.
  Qed.

  Lemma instr_table_agree_agree tb tb':
    instr_table_agree tb -∗ instr_table_agree tb' -∗ ⌜tb = tb'⌝.
  Proof.
    iIntros "He Hξ". rewrite instr_table_agree_eq /instr_table_agree_def.
    iDestruct (own.own_valid_2 with "He Hξ") as "%Hvalid".
    rewrite to_agree_op_valid_L in Hvalid. done.
  Qed.

  (** protocol *)
  Definition prot_loc_gn_def (addr: Addr) (dq: dfrac) (N: gname) :=
    ghost_map_elem AAProtN addr dq N.

  Definition prot_loc_gn_aux : seal (@prot_loc_gn_def). Proof. by eexists. Qed.
  Definition prot_loc_gn := prot_loc_gn_aux.(unseal).
  Definition prot_loc_gn_eq : @prot_loc_gn = @prot_loc_gn_def := prot_loc_gn_aux.(seal_eq).

  Lemma prot_loc_gn_combine l dq1 dq2 N1 N2:
    prot_loc_gn l dq1 N1 -∗ prot_loc_gn l dq2 N2 -∗ prot_loc_gn l (dq1 ⋅ dq2) N1.
  Proof.
    iIntros "H1 H2". rewrite prot_loc_gn_eq /prot_loc_gn_def.
    by iCombine "H1 H2" as "$".
  Qed.

  Lemma prot_loc_gn_split l q1 q2 N:
    prot_loc_gn l (DfracOwn (q1 + q2)) N -∗ prot_loc_gn l (DfracOwn q1) N ∗ prot_loc_gn l (DfracOwn q2) N.
  Proof.
    iIntros "H". rewrite prot_loc_gn_eq /prot_loc_gn_def.
    iDestruct "H" as "[$ $]".
  Qed.

  Lemma prot_loc_gn_both_agree l q N m:
    prot_loc_gn l q N -∗ ghost_map_auth AAProtN 1 m -∗ ⌜m !! l = Some N⌝.
  Proof.
    iIntros "He Hauth". rewrite prot_loc_gn_eq /prot_loc_gn_def.
    iApply (ghost_map.ghost_map_lookup with "Hauth He").
  Qed.

  Lemma prot_loc_gn_both_update l N N' m:
    prot_loc_gn l (DfracOwn 1) N -∗ ghost_map_auth AAProtN 1 m ==∗
    ghost_map_auth AAProtN 1 (<[ l := N' ]>m) ∗ prot_loc_gn l (DfracOwn 1) N'.
  Proof.
    iIntros "He Hauth". rewrite prot_loc_gn_eq /prot_loc_gn_def.
    by iDestruct (ghost_map.ghost_map_update with "Hauth He") as ">[$ $]".
  Qed.

  Lemma prot_loc_gn_persist l q N:
    prot_loc_gn l (DfracOwn q) N ==∗ prot_loc_gn l (DfracDiscarded) N.
  Proof.
    iIntros "H". rewrite prot_loc_gn_eq /prot_loc_gn_def.
    iApply ghost_map_elem_persist.
    done.
  Qed.

End definition.

Definition instr_def `{CMRA Σ} `{!AABaseG} (a : Addr) (oi : option Instruction) : iProp Σ :=
  ∃ gi, instr_table_agree gi ∗ ⌜gi !! a = oi⌝.
Definition instr_aux : seal (@instr_def). Proof. by eexists. Qed.
Definition instr := instr_aux.(unseal).
Arguments instr {Σ _ _}.
Definition instr_eq : @instr = @instr_def := instr_aux.(seal_eq).
Notation "a ↦ᵢ i" := (instr a (Some i)) (at level 20) : bi_scope.
Notation "a ↦ᵢ -" := (instr a None) (at level 20) : bi_scope.

Definition annot_own_def `{CMRA Σ} `{!AABaseG} eid (P : iProp Σ) :iProp Σ :=
  ∃ n n', ghost_map_ag_elem AANodeAnnotN eid n ∗ own n (◯ (GSet {[n']})) ∗
          saved_prop_own n' (DfracOwn (1/2)) P.
Definition annot_own_aux : seal(@annot_own_def). Proof. by eexists. Qed.
Definition annot_own := annot_own_aux.(unseal).
Arguments annot_own {Σ _ _}.
Definition annot_own_eq : @annot_own = @annot_own_def := annot_own_aux.(seal_eq).
Notation "n ↦ₐ P" := (annot_own n P) (at level 20) : bi_scope.

Definition rmw_token_def `{CMRA Σ} `{!AABaseG} (e : Eid) :=
  own AARmwTokenN (◯ (GSet {[e]})).
Definition rmw_token_aux : seal(@rmw_token_def). Proof. by eexists. Qed.
Definition rmw_token := rmw_token_aux.(unseal).
Arguments rmw_token {Σ _ _}.
Definition rmw_token_eq : @rmw_token = @rmw_token_def := rmw_token_aux.(seal_eq).
Notation "Tok{ n }" := (rmw_token n) (at level 20,
                         format "'Tok{' n  '}'") : bi_scope.

Definition prot_loc_def `{CMRA Σ} `{!AABaseG} (l: Addr) (q: dfrac) (prot: Val -> Eid -> iProp Σ) : iProp Σ:=
  ∃ gn, prot_loc_gn l q gn ∗ saved_prot_own gn prot.
Definition prot_loc_aux : seal(@prot_loc_def). Proof. by eexists. Qed.
Definition prot_loc := prot_loc_aux.(unseal).
Arguments prot_loc {Σ _ _}.
Definition prot_loc_eq : @prot_loc = @prot_loc_def := prot_loc_aux.(seal_eq).
Notation "『 x , dq | Φ 』" := (prot_loc x dq Φ) (at level 20,
                         format "『 x ,  dq  |  Φ 』") : bi_scope.
Notation "『 x , # q | Φ 』" := (prot_loc x (DfracOwn q) Φ) (at level 20,
                         format "『 x ,  # q  |  Φ 』") : bi_scope.
Notation "『 x | Φ 』" := (prot_loc x (DfracOwn 1) Φ) (at level 20,
                         format "『 x  |  Φ 』") : bi_scope.
Notation "『 x , □ | Φ 』" := (prot_loc x (DfracDiscarded) Φ) (at level 20,
                         format "『 x ,  □ |  Φ 』") : bi_scope.

Section lemma.
  Context `{CMRA Σ} `{!AABaseG}.
  #[global] Instance instr_persis a i: Persistent (a ↦ᵢ i).
  Proof.
    rewrite instr_eq /instr_def. apply _.
  Qed.

  #[global] Instance instr_persis' a: Persistent (a ↦ᵢ -).
  Proof.
    rewrite instr_eq /instr_def. apply _.
  Qed.

  Lemma token_excl a b:
    Tok{a} -∗ Tok{b} -∗ ⌜a ≠ b⌝.
  Proof.
    rewrite rmw_token_eq /rmw_token_def.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    iPureIntro. rewrite auth_frag_op_valid in Hvalid.
    rewrite gset_disj_valid_op in Hvalid.
    set_solver + Hvalid.
  Qed.

  Lemma prot_loc_combine x q1 q2 Φ1 Φ2 :
    『 x , #q1 |  Φ1 』 -∗ 『 x, #q2 | Φ2  』-∗
    『 x , #((q1+q2)%Qp) | Φ1 』.
  Proof.
    rewrite prot_loc_eq /prot_loc_def.
    iIntros "[% [Hgn1 Hsp1]] [% [Hgn2 Hsp2]]".
    iDestruct (prot_loc_gn_combine with "Hgn1 Hgn2") as "Hgn".
    by iFrame.
  Qed.

  Global Instance prot_loc_combine_as l q1 q2 Φ1 Φ2:
    CombineSepAs (『 l , #q1 | Φ1 』) ( 『l , #q2 | Φ2 』) (『 l, #(q1 + q2) | Φ1 』) | 60.
  Proof.
    rewrite /CombineSepAs. iIntros "[H1 H2]".
    iDestruct (prot_loc_combine with "H1 H2") as "$".
  Qed.

  Global Instance prot_loc_fractional l Φ :
    Fractional (λ q, 『l, #q | Φ 』)%I.
  Proof.
    iIntros (??). iSplit.
    {
      rewrite prot_loc_eq /prot_loc_def.
      iIntros "[% [Hgn #Hsp]]". iFrame "#".
      iDestruct (prot_loc_gn_split with "Hgn") as "[$ $]".
    }
    iIntros "[H1 H2]".
    iApply (prot_loc_combine with "H1 H2").
  Qed.


  Global Instance prot_loc_as_fractional l q Φ :
    AsFractional (『 l, #q | Φ 』) (λ q, 『 l, #q |  Φ 』)%I q.
  Proof.
      split. reflexivity.
      apply _.
  Qed.

  Lemma prot_loc_persist l q Φ:
    『 l , #q | Φ 』 ==∗ 『 l , □ | Φ 』.
  Proof.
    rewrite prot_loc_eq /prot_loc_def.
    iIntros "[% [H $]]".
    by iApply prot_loc_gn_persist.
  Qed.


  Global Instance prot_loc_pers l Φ:
   Persistent (『 l , □ | Φ 』).
  Proof.
    rewrite prot_loc_eq /prot_loc_def.
    rewrite prot_loc_gn_eq.
    apply _.
  Qed.

End lemma.
