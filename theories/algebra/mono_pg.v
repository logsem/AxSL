From iris.algebra Require Export auth.
From iris.algebra Require Import numbers updates.
From iris.prelude Require Import options.

(** ** Progresses with [max] as the operation. *)
Record max_pg := MaxPg { max_pg_car : nat * nat}.
Add Printing Constructor max_pg.

Definition pg_max := λ (n m : nat * nat),
                      (if bool_decide (n.1 < m.1) then m
                       else if bool_decide (n.1 =  m.1)
                            then (n.1, (n.2 `max` m.2))
                            else n).

Definition pg_le := λ (n m : nat * nat), n.1 < m.1 ∨ n.1 = m.1 ∧ n.2 <= m.2.
#[global] Hint Unfold pg_le : core.

Lemma pg_le_max_r x y : pg_le x (pg_max x y).
Proof.
  unfold pg_le, pg_max. destruct x,y;simpl.
  case_bool_decide.
  { left; simpl;lia. }
  { case_bool_decide; right;simpl;lia. }
Qed.

Lemma pg_max_le x y : pg_le x y -> y = pg_max x y.
Proof.
  unfold pg_max. intros [| [? ?]];case_bool_decide;try done.
  case_bool_decide;try lia. destruct x,y;simpl in *. subst.
  rewrite Nat.max_r;auto.
Qed.

Lemma pg_max_assoc x y z: pg_max x (pg_max y z) = pg_max (pg_max x y) z.
Proof.
  unfold pg_max. destruct x,y,z. repeat case_bool_decide;simpl in *; subst;try done;try lia.
  rewrite Nat.max_assoc. done.
Qed.

Lemma pg_max_comm x y : pg_max x y = pg_max y x.
Proof.
  unfold pg_max. destruct x,y. repeat case_bool_decide;simpl in *; subst;try done;try lia.
  rewrite Nat.max_comm. done.
Qed.

Lemma pg_max_id x : pg_max x x = x.
Proof.
  unfold pg_max. destruct x. repeat case_bool_decide;simpl in *; subst;try done;try lia.
  rewrite Nat.max_id. done.
Qed.

Canonical Structure max_pgO := leibnizO max_pg.


Section max_pg.
  Local Instance max_pg_unit_instance : Unit max_pg := MaxPg (0,0).
  Local Instance max_pg_valid_instance : Valid max_pg := λ x, True.
  Local Instance max_pg_validN_instance : ValidN max_pg := λ n x, True.
  Local Instance max_pg_pcore_instance : PCore max_pg := Some.
  Local Instance max_pg_op_instance : Op max_pg := λ n m, MaxPg (pg_max (max_pg_car n) (max_pg_car m)).
  Definition max_pg_op x y : MaxPg x ⋅ MaxPg y = MaxPg (pg_max x y) := eq_refl.

  Lemma max_pg_included x y : x ≼ y ↔ pg_le (max_pg_car x) (max_pg_car y).
  Proof.
    split.
    - intros [z ->]. simpl. apply pg_le_max_r.
    - exists y. rewrite /op /max_pg_op_instance. rewrite -pg_max_le;auto. by destruct y.
  Qed.
  Lemma max_pg_ra_mixin : RAMixin max_pg.
  Proof.
    apply ra_total_mixin; apply _ || eauto.
    - intros [x] [y] [z]. repeat rewrite max_pg_op. by rewrite pg_max_assoc.
    - intros [x] [y]. by rewrite max_pg_op pg_max_comm.
    - intros [x]. by rewrite max_pg_op pg_max_id.
  Qed.
  Canonical Structure max_pgR : cmra := discreteR max_pg max_pg_ra_mixin.

  Global Instance max_pg_cmra_discrete : CmraDiscrete max_pgR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma max_pg_ucmra_mixin : UcmraMixin max_pg.
  Proof. split; try apply _ || done. intros [x].
         rewrite /op /max_pg_op_instance /max_pg_unit_instance /=.
         f_equiv. rewrite /pg_max /=. destruct x; repeat case_bool_decide;simpl in *; subst;try done;try lia.
  Qed.
  Canonical Structure max_pgUR : ucmra := Ucmra max_pg max_pg_ucmra_mixin.

  Global Instance max_pg_core_id (x : max_pg) : CoreId x.
  Proof. by constructor. Qed.

  Lemma max_pg_local_update (x y x' : max_pg) :
    pg_le (max_pg_car x) (max_pg_car x') → (x,y) ~l~> (x',x').
  Proof.
    move: x y x' => [x] [y] [y'] /= H.
    rewrite local_update_unital_discrete=> [[z]] _.
    rewrite 2!max_pg_op. intros [= ?].
    split; first done. apply f_equal. subst.
    rewrite /pg_max /pg_le.
    rewrite /pg_max /pg_le in H.
    destruct y',y,z. simpl in *.
    destruct H as [|[? ?]]; repeat case_bool_decide;simpl in *; subst;try lia;try done;f_equal; lia.
  Qed.

  Global Instance : IdemP (=@{max_pg}) (⋅).
  Proof. intros [x]. rewrite max_pg_op. apply f_equal. rewrite pg_max_id //. Qed.

  Global Instance max_pg_is_op (x y : (nat * nat)) :
    IsOp (MaxPg (pg_max x y)) (MaxPg x) (MaxPg y).
  Proof. done. Qed.
End max_pg.

(** Authoritative CMRA over [max_pg]. The authoritative element is a
monotonically increasing [pg], while a fragment is a lower bound. *)

Definition mono_pg   := auth max_pgUR.
Definition mono_pgR  := authR max_pgUR.
Definition mono_pgUR := authUR max_pgUR.

(** [mono_pg_auth] is the authoritative element. The definition includes the
fragment at the same value so that lemma [mono_pg_included], which states that
[mono_pg_lb n ≼ mono_pg_auth dq n], holds. Without this trick, a
frame-preserving update lemma would be required instead. *)
Notation pg := (nat * nat)%type.

Definition mono_pg_auth (dq : dfrac) (n : pg) : mono_pg :=
  ●{dq} MaxPg n ⋅ ◯ MaxPg n.
Definition mono_pg_lb (n : pg) : mono_pg := ◯ MaxPg n.

Notation "●MN dq a" := (mono_pg_auth dq a)
  (at level 20, dq custom dfrac at level 1, format "●MN dq  a").
Notation "◯MN a" := (mono_pg_lb a) (at level 20).

Section mono_pg.
  Implicit Types (n : pg).

  Global Instance mono_pg_lb_core_id n : CoreId (◯MN n).
  Proof. apply _. Qed.
  Global Instance mono_pg_auth_core_id l : CoreId (●MN□ l).
  Proof. apply _. Qed.

  Lemma mono_pg_auth_dfrac_op dq1 dq2 n :
    ●MN{dq1 ⋅ dq2} n ≡ ●MN{dq1} n ⋅ ●MN{dq2} n.
  Proof.
    rewrite /mono_pg_auth auth_auth_dfrac_op.
    rewrite (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
    by rewrite -core_id_dup (comm _ (◯ _)).
  Qed.

  Lemma mono_pg_lb_op n1 n2 :
    ◯MN (pg_max n1 n2) = ◯MN n1 ⋅ ◯MN n2.
  Proof. rewrite -auth_frag_op max_pg_op //. Qed.

  Lemma mono_pg_auth_lb_op dq n :
    ●MN{dq} n ≡ ●MN{dq} n ⋅ ◯MN n.
  Proof.
    rewrite /mono_pg_auth /mono_pg_lb.
    rewrite -!assoc -auth_frag_op max_pg_op.
    rewrite pg_max_id //.
  Qed.

  Global Instance mono_pg_auth_dfrac_is_op dq dq1 dq2 n :
    IsOp dq dq1 dq2 → IsOp' (●MN{dq} n) (●MN{dq1} n) (●MN{dq2} n).
  Proof. rewrite /IsOp' /IsOp=> ->. rewrite mono_pg_auth_dfrac_op //. Qed.
  Global Instance mono_pg_lb_max_is_op n n1 n2 :
    IsOp (MaxPg n) (MaxPg n1) (MaxPg n2) → IsOp' (◯MN n) (◯MN n1) (◯MN n2).
  Proof. rewrite /IsOp' /IsOp /mono_pg_lb=> ->. done. Qed.

  (** rephrasing of [mono_pg_lb_op] useful for weakening a fragment to a
  smaller lower-bound *)
  Lemma mono_pg_lb_op_le_l n n' :
    pg_le n' n →
    ◯MN n = ◯MN n' ⋅ ◯MN n.
  Proof. intros. rewrite -mono_pg_lb_op -pg_max_le //. Qed.

  Lemma mono_pg_auth_dfrac_valid dq n : (✓ ●MN{dq} n) ↔ ✓ dq.
  Proof.
    rewrite /mono_pg_auth auth_both_dfrac_valid_discrete /=. naive_solver.
  Qed.
  Lemma mono_pg_auth_valid n : ✓ ●MN n.
  Proof. by apply auth_both_valid. Qed.

  Lemma mono_pg_auth_dfrac_op_valid dq1 dq2 n1 n2 :
    ✓ (●MN{dq1} n1 ⋅ ●MN{dq2} n2) ↔ ✓ (dq1 ⋅ dq2) ∧ n1 = n2.
  Proof.
    rewrite /mono_pg_auth (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
    rewrite -auth_frag_op (comm _ (◯ _)) assoc. split.
    - move=> /cmra_valid_op_l /auth_auth_dfrac_op_valid. naive_solver.
    - intros [? ->]. rewrite -core_id_dup -auth_auth_dfrac_op.
      by apply auth_both_dfrac_valid_discrete.
  Qed.
  Lemma mono_pg_auth_op_valid n1 n2 :
    ✓ (●MN n1 ⋅ ●MN n2) ↔ False.
  Proof. rewrite mono_pg_auth_dfrac_op_valid. naive_solver. Qed.

  Lemma mono_pg_both_dfrac_valid dq n m :
    ✓ (●MN{dq} n ⋅ ◯MN m) ↔ ✓ dq ∧ pg_le m n.
  Proof.
    rewrite /mono_pg_auth /mono_pg_lb -assoc -auth_frag_op.
    rewrite auth_both_dfrac_valid_discrete max_pg_included /=.
    split;[intros [? [? ?]]| intros [? ?]];split;auto.
    - rewrite /pg_le. rewrite /pg_le /pg_max in H0.
      destruct m,n. simpl in *. destruct H0 as [|[? ?]]; repeat case_bool_decide;simpl in *; subst;try lia;try done;f_equal.
    -  split;auto.
       + rewrite /pg_le /pg_max. rewrite /pg_le /pg_max in H0.
         destruct m,n. simpl in *. destruct H0 as [|[? ?]]; repeat case_bool_decide;simpl in *; subst;try lia;try done;f_equal.
       + naive_solver.
  Qed.
  Lemma mono_pg_both_valid n m :
    ✓ (●MN n ⋅ ◯MN m) ↔ pg_le m n.
  Proof. rewrite mono_pg_both_dfrac_valid dfrac_valid_own. naive_solver. Qed.

  Lemma mono_pg_lb_mono n1 n2 : pg_le n1 n2 → ◯MN n1 ≼ ◯MN n2.
  Proof. intros. by apply auth_frag_mono, max_pg_included. Qed.

  Lemma mono_pg_included dq n : ◯MN n ≼ ●MN{dq} n.
  Proof. apply cmra_included_r. Qed.

  Lemma mono_pg_update {n} n' :
    pg_le n n' → ●MN n ~~> ●MN n'.
  Proof.
    intros. rewrite /mono_pg_auth /mono_pg_lb.
    by apply auth_update, max_pg_local_update.
  Qed.

  Lemma mono_pg_auth_persist n dq :
    ●MN{dq} n ~~> ●MN□ n.
  Proof.
    intros. rewrite /mono_pg_auth /mono_pg_lb.
    eapply cmra_update_op_proper; last done.
    eapply auth_update_auth_persist.
  Qed.
End mono_pg.

Global Typeclasses Opaque mono_pg_auth mono_pg_lb.
