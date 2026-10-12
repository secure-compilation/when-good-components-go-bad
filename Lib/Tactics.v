Require Import Common.Maps.
Require Import Common.Memory.

Require Import Coq.Arith.Arith.

Ltac inv H :=
  inversion H; subst; clear H.

Ltac simplify_option :=
  match goal with
  | H: Some ?x1 = Some ?x2 |- _ => inv H
  | |- match ?V with _ => _ end = Some _ =>
    destruct V eqn:?; subst; try discriminate
  | H: match ?V with _ => _ end = Some _ |- _ =>
    destruct V eqn:?; inv H
  end.

Ltac simplify_bools :=
  match goal with
  | H: match ?V with _ => _ end = true |- _ =>
    destruct V eqn:?; subst; try discriminate
  | H: match ?V with _ => _ end = false |- _ =>
    destruct V eqn:?; subst; try discriminate
  end.

Ltac simplify_nat_equalities :=
  try rewrite Nat.eqb_refl;
  try rewrite <- Nat.eqb_refl;
  try match goal with
      | H: (_ =? _) = true |- _ =>
        apply Nat.eqb_eq in H; rewrite H
      end.