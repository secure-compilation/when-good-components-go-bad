Require Import Common.

(* from CompCert events *)
Inductive event :=
  | ECall : Component.id -> Procedure.id -> nat -> Component.id -> event
  | ERet : Component.id -> nat -> Component.id -> event
  | EInput : Component.id -> nat -> event
  | EOutput : Component.id -> nat -> event.

(* Finite traces *)
Definition trace := list event.
Definition E0 : trace := [].
Definition Eapp (t1 t2: trace) : trace := t1 ++ t2.

(* Infinite traces *)
CoInductive traceinf : Type :=
| Econsinf: event -> traceinf -> traceinf.

Fixpoint Eappinf (t: trace) (T: traceinf) {struct t} : traceinf :=
  match t with
  | nil => T
  | ev :: t' => Econsinf ev (Eappinf t' T)
  end.

Infix "**" := Eapp (at level 60, right associativity).
Infix "***" := Eappinf (at level 60, right associativity).


