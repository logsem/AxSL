(** This file contains construction of basic RAs *)
(* From stdpp Require Export namespaces. *)

From iris.algebra Require Export agree gmap gset csum lib.dfrac_agree.
From iris.base_logic.lib Require Export ghost_map saved_prop.
From iris.proofmode Require Export tactics.
From iris_named_props Require Export named_props.

From self Require Export cmra.
From self.lang Require Export mm instrs.
From self.algebra Require Export ghost_map_ag mono_pg.

Class AABaseInG `{CMRA Σ} := {
  AAInGBaseEdge :> inG Σ (agreeR (leibnizO Graph.t));
  (* node_annotation *)
  AAInGNodeAnnot :> ghost_map_agG Σ Eid gname;
  AAInGNodeAnnotGnames :> inG Σ (authR (gset_disjUR gname));
  AAInGSavedProp :> savedPropG Σ;
  AAInGInstrMem :> inG Σ (agreeR (gmapO Addr (leibnizO Instruction)));
  AAInGLocalWriteMap :> ghost_mapG Σ Addr (option Eid);
  AAInGPoSrcMono :> inG Σ (mono_pgR);
  AAInGPoSrcOneShot :> inG Σ (csumR (dfrac_agreeR unitO) (agreeR (prodO gnameO natO)));
  AAInGRmwSrc :> inG Σ (authR (gset_disjUR Eid));
}.

Section genAABaseG.
  Class AABaseG `{CMRA Σ} :=
    GenAABaseG{
        AAIn :> AABaseInG;
        AAGraphN : gname;
        AANodeAnnotN: gname;
        AAInstrN : gname;
        AARmwTokenN : gname;
      }.

  #[global] Arguments AAGraphN {Σ _ _}.
  #[global] Arguments AANodeAnnotN {Σ _ _}.
  #[global] Arguments AAInstrN {Σ _ _}.
  #[global] Arguments AARmwTokenN {Σ _ _}.

  Definition AABaseΣ : gFunctors :=
    #[ GFunctor (agreeR (leibnizO Graph.t));
       savedPropΣ;
       ghost_map_agΣ Eid gname;
       GFunctor (authR (gset_disjUR gname));
       GFunctor (agreeR (gmapO Addr (leibnizO Instruction)));
       ghost_mapΣ Addr (option Eid);
       GFunctor mono_pgR;
       GFunctor (csumR (dfrac_agreeR unitO) (agreeR (prodO gnameO natO)));
       GFunctor (authR (gset_disjUR Eid))
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

End definition.
