Require Import Coq.Strings.String.

Inductive Either {A:Type} {E:Type} : Type :=
| Right : A  -> Either
| Left : string -> E -> Either.
