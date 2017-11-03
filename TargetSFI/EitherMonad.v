Require Export Lib.Monads.
Require Import Coq.Strings.String.

Require Import FunctionalExtensionality.

Set Implicit Arguments.
                  
Inductive Either {A:Type} : Type :=
| Right : A -> Either
| Left : string -> Either.

Instance either_monad : Monad (@Either)
  := {
      
      ret := fun {A:Type} (x:A) => @Right A x;
      
      bind := fun {A B:Type} (x : @Either A) (f : A -> @Either B) => 
        match x with
        | Right y => f y
        | Left m => Left m
        end
    }.


(* Definition lift {A} (x: option A) (msg : string) : (@Either A) := *)
(*   match x with *)
(*   | None => Left msg *)
(*   | Some x' => Right x' *)
(*   end. *)
           

Lemma either_monad_left_id:
  forall A B (a: A) (f: A -> @Either B),
    bind (ret a) f = f a.
Proof.
  auto.
Qed.

Lemma either_monad_right_id:
  forall A (m: @Either A),
    bind m ret = m.
Proof.
  intros.
  destruct m; auto.
Qed.

Lemma either_monad_associativity:
  forall A B C (m: @Either A) (f: A -> @Either B) (g: B -> @Either C),
    bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof.
  intros.
  destruct m; auto.
Qed.