(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.NArith.BinNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import CompCert.Events.

Require Import Source.Language.
Require Import Source.Examples.Factorial.
Require Import Source.Examples.Identity.
Require Import Source.Examples.Increment.
Require Import S2I.Compiler.
Require Import I2SFI.Compiler.
Require Import TargetSFI.EitherMonad.
Require Import TargetSFI.Machine.
Require Import TargetSFI.CS.
Require Import Intermediate.Machine.
Require Import Common.Definitions.
Require Import Common.Maps.

Import MonadNotations.
Open Scope monad_scope.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.
(* Suppress some annoying warnings: *)

Open Scope positive_scope.
Definition increment : Source.program := {|
  Source.prog_interface :=
    PMapExtra.of_list [(1, {| Component.import := [(2, 1)];
                              Component.export := [1] |});
                       (2, {| Component.import := [];
                              Component.export := [1] |})];
  Source.prog_buffers := PMapExtra.of_list [(1, (inl 1%nat)); (2, (inl 1%nat))];
  Source.prog_procedures := PMapExtra.of_list [
    (* NOTE the version with E_exit is the right one, but unfortunately it is difficult
            to debug with extraction. Hence, the second version without E_exit *)
    (*(1, NMapExtra.of_list [(0, E_seq (E_call 2 0 (E_val (Int 6))) E_exit)]);*)
    (1, PMapExtra.of_list [(1, E_call 2 1 (E_val (Int 6)))]);
    (2, PMapExtra.of_list [(1,     
        (E_binop Add
                 (E_deref E_local)
                 (E_val (Int 1))))])];
  Source.prog_main := (1, 1)
|}.
Close Scope positive_scope.

Definition test (sp : Source.program) : @Either sfi_program :=
  match S2I.Compiler.compile_program sp with
  | None => TargetSFI.EitherMonad.Left "S2I compiler failed"
  | Some ip => compile_program ip
  end.


Example test_increment :
  exists (tp : sfi_program),
    test increment = TargetSFI.EitherMonad.Right tp.
Proof.
  compute. eauto. Qed.

(* (* this doesn't end Need to figure out TODO *) *)
(* Example test_identity : *)
(*   exists (ip : Intermediate.program) (tp : sfi_program), *)
(*     S2I.Compiler.compile_program identity = Some ip /\ *)
(*     I2SFI.Compiler.compile_program ip = Right tp. *)
(* Proof. *)
(*   compute. eauto. Qed. *)


(* (* this doesn't end Need to figure out TODO *) *)
(* Example test_factorial : *)
(*   exists (ip : Intermediate.program) (tp : sfi_program), *)
(*     S2I.Compiler.compile_program Examples.factorial = Some ip /\ *)
(*     I2SFI.Compiler.compile_program ip = Right tp. *)
(* Proof. *)
(*   compute. eauto. Qed. *)

Instance show_sp : Show Source.program :=
  {|
    show := fun _ => Coq.Strings.String.EmptyString
  |}.

Definition genSourceProgram : G  Source.program :=
  elements identity [identity; factorial;
                       Source.Examples.Increment.increment].


Definition integration_pbt : Checker :=
  forAll genSourceProgram
         ( fun sp =>
             match S2I.Compiler.compile_program sp with
             | None => whenFail "Source program does not compile" false
             | Some ip =>
               match I2SFI.Compiler.compile_program ip with
               | TargetSFI.EitherMonad.Left msg =>
                  whenFail ("Compilation error: " ++ msg) false
               | TargetSFI.EitherMonad.Right p =>
                 match CS.eval_program (5000%nat) p (RiscMachine.RegisterFile.reset_all) with
                 | TargetSFI.EitherMonad.Left msg => whenFail msg false
                 | TargetSFI.EitherMonad.Right (t,(mem,_,regs)) => checker true
                 end
               end
             end
         ).

QuickChick integration_pbt.