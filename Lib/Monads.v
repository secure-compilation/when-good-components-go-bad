Class Monad (M: Type -> Type) := {
  ret : forall {A}, A -> M A;
  bind : forall {A B}, M A -> (A -> M B) -> M B
}.

Instance option_monad : Monad option := {
  ret A x := Some x;
  bind A B x f :=
    match x with
    | Some y => f y
    | None => None
    end
}.

Module MonadNotations.
  Notation "m >>= f" := (bind m f) (at level 60, right associativity).
  Notation "' x <- m ; y " := (m >>= (fun x:_ => y))
    (at level 65, x ident, only parsing, right associativity).
  Notation "' ( x1 , x2 ) <- m ; y" := (m >>= (fun x => let '(x1,x2) := x in y))
    (at level 65, x1 ident, x2 ident, only parsing, right associativity).
End MonadNotations.