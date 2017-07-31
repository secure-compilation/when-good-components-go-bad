Require Import Common.Maps.
Require Import Common.Memory.

Ltac inv H :=
  inversion H; clear H; subst.

Ltac simplify_options :=
  match goal with
  | H: Some ?x1 = Some ?x2 |- _ => inv H
  | |- match ?V with _ => _ end = Some _ =>
    destruct V eqn:?; subst; try discriminate
  | H: match ?V with _ => _ end = Some _ |- _ =>
    destruct V eqn:?; inv H
  end.

Ltac rewrite_memory_operations :=
  unfold Memory.alloc, Memory.load, Memory.store;
  match goal with
  | H: NMap.find (elt:=ComponentMemory.t) _ _ = Some _ |- _ => rewrite H
  | H: ComponentMemory.store _ _ _ _ = Some _ |- _ => rewrite H
  | H: ComponentMemory.load _ _ _ = Some _ |- _ => rewrite H
  end.