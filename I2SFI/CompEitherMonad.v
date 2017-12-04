Require Export Lib.Monads.
Require Import Coq.Strings.String.

Require Import FunctionalExtensionality.
Require Import AbstractMachine.
Require Import Common.Maps.
Require Import Coq.NArith.BinNat.

Set Implicit Arguments.

Inductive CompilerError : Type :=
| NoInfo : CompilerError
| DuplicatedLabels :  (PMap.t (PMap.t AbstractMachine.lcode)) -> CompilerError
| ExportedProcsLabelsC : positive ->  (PMap.t (PMap.t  AbstractMachine.label)) -> CompilerError
| ExportedProcsLabelsP : positive -> positive ->
                         (PMap.t (PMap.t  AbstractMachine.label)) -> CompilerError
| PosArg : positive -> CompilerError
| TwoPosArg : positive -> positive -> CompilerError
.

Inductive CompEither {A:Type} : Type :=
| Right : A -> CompEither
| Left : string -> CompilerError -> CompEither.

Instance comp_either_monad : Monad (@CompEither)
  := {
      
      ret := fun {A:Type} (x:A) => @Right A x;
      
      bind := fun {A B:Type} (x : @CompEither A) (f : A -> @CompEither B) => 
        match x with
        | Right y => f y
        | Left m err => Left m err
        end
    }.

Lemma either_monad_left_id:
  forall A B (a: A) (f: A -> @CompEither B),
    bind (ret a) f = f a.
Proof.
  auto.
Qed.

Lemma either_monad_right_id:
  forall A (m: @CompEither A),
    bind m ret = m.
Proof.
  intros.
  destruct m; auto.
Qed.

Lemma either_monad_associativity:
  forall A B C (m: @CompEither A) (f: A -> @CompEither B) (g: B -> @CompEither C),
    bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof.
  intros.
  destruct m; auto.
Qed.