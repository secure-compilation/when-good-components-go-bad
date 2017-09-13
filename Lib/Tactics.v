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
  try rewrite <- beq_nat_refl;
  try rewrite beq_nat_refl;
  try match goal with
      | H: (_ =? _) = true |- _ =>
        apply beq_nat_true_iff in H; rewrite H
      end.

Ltac rewrite_memory_operations :=
  unfold Memory.alloc, Memory.load, Memory.store;
  match goal with
  | H: ZMap.find (elt:=ComponentMemory.t) _ _ = Some _ |- _ => rewrite H
  | H: ZMap.find (elt:=ComponentMemory.t) _ _ = None |- _ => rewrite H
  | H: ComponentMemory.store _ _ _ _ = Some _ |- _ => rewrite H
  | H: ComponentMemory.store _ _ _ _ = None |- _ => rewrite H
  | H: ComponentMemory.load _ _ _ = Some _ |- _ => rewrite H
  | H: ComponentMemory.load _ _ _ = None |- _ => rewrite H
  end.

Ltac rewrite_map_operations :=
  match goal with
  | H: ZMap.find _ _ _ = Some _ |- _ => rewrite H
  | H: ZMap.find _ _ _ = None |- _ => rewrite H
  end.