(** This file contains the RA of construction gmap K (agree V)*)
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import tactics.

Require Export self.algebra.lib.gmap_view_ag.

Class ghost_map_agG Σ (K V : Type) `{Countable K} := GhostMapAgG {
  ghost_map_ag_inG : inG Σ (gmap_view_agR K (leibnizO V));
}.

Local Existing Instance ghost_map_ag_inG.

Definition ghost_map_agΣ (K V : Type) `{Countable K} : gFunctors :=
  #[ GFunctor (gmap_view_agR K (leibnizO V)) ].

Global Instance subG_ghost_map_agΣ Σ (K V : Type) `{Countable K} :
  subG (ghost_map_agΣ K V) Σ → ghost_map_agG Σ K V.
Proof. solve_inG. Qed.

Section definitions.
  Context `{ghost_map_agG Σ K V}.

  Local Definition ghost_map_ag_auth_def
      (γ : gname) (m : gmap K V) : iProp Σ :=
    own γ (gmap_view_ag_auth (V:=leibnizO V) m).
  Local Definition ghost_map_ag_auth_aux : seal (@ghost_map_ag_auth_def).
  Proof. by eexists. Qed.
  Definition ghost_map_ag_auth := ghost_map_ag_auth_aux.(unseal).
  Local Definition ghost_map_ag_auth_unseal :
    @ghost_map_ag_auth = @ghost_map_ag_auth_def := ghost_map_ag_auth_aux.(seal_eq).

  Local Definition ghost_map_ag_elem_def
      (γ : gname) (k : K) (v : V) : iProp Σ :=
    own γ (gmap_view_ag_frag (V:=leibnizO V) k v).
  Local Definition ghost_map_ag_elem_aux : seal (@ghost_map_ag_elem_def).
  Proof. by eexists. Qed.
  Definition ghost_map_ag_elem := ghost_map_ag_elem_aux.(unseal).
  Local Definition ghost_map_ag_elem_unseal :
    @ghost_map_ag_elem = @ghost_map_ag_elem_def := ghost_map_ag_elem_aux.(seal_eq).
End definitions.

Notation "k ↪[ γ ]ag v" := (ghost_map_ag_elem γ k v)
  (at level 20, γ at level 50, format "k  ↪[ γ ]ag  v") : bi_scope.

Local Ltac unseal := rewrite
  ?ghost_map_ag_auth_unseal /ghost_map_ag_auth_def
  ?ghost_map_ag_elem_unseal /ghost_map_ag_elem_def.

Section lemmas.
  Context `{ghost_map_agG Σ K V}.
  Implicit Types (m : gmap K V) (k : K) (q : Qp) (v : V).

  Global Instance ghost_map_ag_elem_timeless k γ v : Timeless (k ↪[γ]ag v).
  Proof. unseal. apply _. Qed.
  Global Instance ghost_map_ag_elem_persistent k γ v : Persistent (k ↪[γ]ag v).
  Proof. unseal. apply _. Qed.

  Lemma ghost_map_ag_elem_agree k γ v1 v2 :
    k ↪[γ]ag v1 -∗ k ↪[γ]ag v2 -∗ ⌜v1 = v2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %?%gmap_view_ag_frag_op_valid_L.
    done.
  Qed.

  Lemma ghost_map_ag_alloc_strong P m :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ ghost_map_ag_auth γ m ∗ [∗ map] k ↦ v ∈ m, k ↪[γ]ag v.
  Proof.
    unseal. intros.
    iMod (own_alloc_strong (gmap_view_ag_auth (V:=leibnizO V) m) P)
      as (γ) "[% Hauth]"; first done.
    { apply gmap_view_ag_auth_valid. }
    iExists γ. iSplitR; first done.
    iDestruct (own_update with "Hauth") as ">Hauth".
    apply gmap_view_ag_alloc_lookup_big.
    reflexivity.
    rewrite -big_opM_own_1 -own_op //.
  Qed.
  Lemma ghost_map_ag_alloc_strong_empty P :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ ghost_map_ag_auth γ (∅ : gmap K V).
  Proof.
    intros. iMod (ghost_map_ag_alloc_strong P ∅) as (γ) "(% & Hauth & _)"; eauto.
  Qed.
  Lemma ghost_map_ag_alloc m :
    ⊢ |==> ∃ γ, ghost_map_ag_auth γ m ∗ [∗ map] k ↦ v ∈ m, k ↪[γ]ag v.
  Proof.
    iMod (ghost_map_ag_alloc_strong (λ _, True) m) as (γ) "[_ Hmap]".
    - by apply pred_infinite_True.
    - eauto.
  Qed.
  Lemma ghost_map_ag_alloc_empty :
    ⊢ |==> ∃ γ, ghost_map_ag_auth γ (∅ : gmap K V).
  Proof.
    intros. iMod (ghost_map_ag_alloc ∅) as (γ) "(Hauth & _)"; eauto.
  Qed.

  Global Instance ghost_map_ag_auth_timeless γ m : Timeless (ghost_map_ag_auth γ m).
  Proof. unseal. apply _. Qed.

 (* Lemmas about the interaction of [ghost_map_auth] with the elements *)
  Lemma ghost_map_ag_lookup {γ m k v} :
    ghost_map_ag_auth γ m -∗ k ↪[γ]ag v -∗ ⌜m !! k = Some v⌝.
  Proof.
    unseal. iIntros "Hauth Hel".
    iDestruct (own_valid_2 with "Hauth Hel") as %?%gmap_view_ag_both_valid_L.
    eauto.
  Qed.

  Lemma ghost_map_ag_insert {γ m} k v :
    m !! k = None →
    ghost_map_ag_auth γ m ==∗ ghost_map_ag_auth γ (<[k := v]> m) ∗ k ↪[γ]ag v.
  Proof. unseal. intros ?. rewrite -own_op.
    iApply own_update. apply: gmap_view_ag_alloc; done.
  Qed.

  Lemma ghost_map_extract {γ m} k v :
    m !! k = Some v →
    ghost_map_ag_auth γ m ==∗ ghost_map_ag_auth γ m ∗ k ↪[γ]ag v.
  Proof.
    unseal. intros ?. rewrite -own_op.
    iApply own_update. apply: gmap_view_ag_alloc_lookup; done.
  Qed.

  (* Big-op versions of above lemmas *)
  Lemma ghost_map_ag_lookup_big {γ m} m0 :
    ghost_map_ag_auth γ m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ]ag v) -∗
    ⌜m0 ⊆ m⌝.
  Proof.
    iIntros "Hauth Hfrag". rewrite map_subseteq_spec. iIntros (k v Hm0).
    iDestruct (ghost_map_ag_lookup with "Hauth [Hfrag]") as %->.
    { rewrite big_sepM_lookup; done. }
    done.
  Qed.

  Lemma ghost_map_ag_insert_big {γ m} m' :
    m' ##ₘ m →
    ghost_map_ag_auth γ m ==∗
    ghost_map_ag_auth γ (m' ∪ m) ∗ ([∗ map] k ↦ v ∈ m', k ↪[γ]ag v).
  Proof.
    unseal. intros ?. rewrite -big_opM_own_1 -own_op.
    iApply own_update. apply: gmap_view_ag_alloc_big; done.
  Qed.

  Lemma ghost_map_ag_extract_big {γ m} m' :
    m' ⊆ m →
    ghost_map_ag_auth γ m ==∗
    ghost_map_ag_auth γ m ∗ ([∗ map] k ↦ v ∈ m', k ↪[γ]ag v).
  Proof.
    unseal. intros ?. rewrite -big_opM_own_1 -own_op.
    iApply own_update. apply: gmap_view_ag_alloc_lookup_big; done.
  Qed.

End lemmas.
