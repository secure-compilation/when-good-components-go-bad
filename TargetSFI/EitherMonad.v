Require Export Lib.Monads.
Require Import Coq.Strings.String.

Require Import FunctionalExtensionality.
Require Import TargetSFI.Machine.

Set Implicit Arguments.

Inductive ExecutionError :=
| RegisterNotFound : MachineState.t -> RiscMachine.Register.t -> ExecutionError
| NoInfo : ExecutionError
| UninitializedMemory : MachineState.t -> RiscMachine.address -> ExecutionError
| CodeMemoryException : MachineState.t -> RiscMachine.address
                        -> RiscMachine.ISA.instr  -> ExecutionError
| DataMemoryException : MachineState.t -> RiscMachine.address
                        -> RiscMachine.value  -> ExecutionError
| MissingComponentId : MachineState.t -> SFIComponent.id -> Env.CN -> ExecutionError
| CallEventError : MachineState.t -> SFIComponent.id -> SFIComponent.id
                   -> Env.CN -> Env.E -> ExecutionError
| RetEventError : MachineState.t -> SFIComponent.id -> SFIComponent.id
                  -> Env.CN -> ExecutionError
| IllegalJalToZeroComponent : MachineState.t -> ExecutionError
| IllegalJumpFromZeroComponent : MachineState.t -> ExecutionError
.

Inductive Either {A:Type} : Type :=
| Right : A  -> Either
| Left : string -> ExecutionError -> Either.

Instance either_monad : Monad (@Either)
  := {
      
      ret := fun {A:Type} (x:A) => @Right A x;
      
      bind := fun {A B:Type} (x : @Either A) (f : A -> @Either B) => 
        match x with
        | Right y => f y
        | Left m err => Left m err
        end
    }.

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