Require Import Common.

Inductive event :=
  | ECall : Component.id -> Procedure.id -> nat -> Component.id -> event
  | ERet : Component.id -> nat -> Component.id -> event.

Definition trace := list event.
Definition E0 : trace := [].
