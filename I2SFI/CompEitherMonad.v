Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNat.

Require Import FunctionalExtensionality.

Require Import Common.Definitions.
Require Import Common.Maps.

Require Export Lib.Monads.

Require Import AbstractMachine.
Require Import SFIUtil.

Set Implicit Arguments.

Inductive CompilerError : Type :=
| NoInfo : CompilerError
| DuplicatedLabels :  (BinNatMap.t (BinNatMap.t AbstractMachine.lcode)) -> CompilerError
| ExportedProcsLabelsC : N ->  (BinNatMap.t (BinNatMap.t  AbstractMachine.label)) -> CompilerError
| ExportedProcsLabelsP : N -> N ->
                         (BinNatMap.t (BinNatMap.t AbstractMachine.label)) -> CompilerError
| NArg : N -> CompilerError
| ProcNotImported : N -> N -> list (N*N) -> CompilerError
| TwoNArg : N -> N -> CompilerError
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