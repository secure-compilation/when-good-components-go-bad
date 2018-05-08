(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.NArith.BinNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import Common.Either.

Require Import CompCert.Events.

Require Import Source.Language.

Require Import S2I.Compiler.
Require Import I2SFI.Compiler.
Require Import TargetSFI.Machine.
Require Import TargetSFI.CS.
Require Import Intermediate.Machine.
Require Import Common.Definitions.
Require Import Common.Maps.

Require Export Extraction.Definitions.

Require Import Source.Examples.Factorial.
Require Import Source.Examples.DefaultInitBuffer.
Require Import Source.Examples.NestedCalls.
Require Import Source.Examples.Identity.
Require Import Source.Examples.Increment.

Require Import I2SFI.AbstractMachine.
Require Import I2SFI.CompStateMonad.

Require Import Tests.TargetSFI.SFITestUtil.
Require Import Tests.CompTestUtil.
Require Import Tests.I2SFI.I2SFICompUtil.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.

Definition newline := String "010" ""%string.

Definition compile_and_run (sp : Source.program) (fuel : nat) :=
  match S2I.Compiler.compile_program sp with
  | None => print_error ocaml_int_0
  | Some ip =>
    match I2SFI.Compiler.compile_program ip with
    | Common.Either.Left msg err => print_string_error (msg ++ " " ++ (show err)
                                                              ++ newline
                                                              ++ (show ip))
    | Common.Either.Right p =>
      match CS.eval_program fuel p (RiscMachine.RegisterFile.reset_all) with
      | Common.Either.Left msg err => print_error ocaml_int_1
      | Common.Either.Right (t,(mem,_,regs),_) =>
        match  (RiscMachine.RegisterFile.get_register
                  RiscMachine.Register.R_COM regs) with
        | Some z =>
          print_ocaml_int (z2int z)
        | None => print_error ocaml_int_2
        end
      end
    end
  end.

Definition run_fact := (compile_and_run factorial 10000%nat).
Extraction "/tmp/run_target_compiled_factorial.ml" run_fact.

Definition run_buffer := (compile_and_run default_init_buffer fuel).
Extraction "/tmp/run_target_compiled_default_init_buffer.ml" run_buffer.

Definition run_id := (compile_and_run identity fuel).
Extraction "/tmp/run_target_compiled_identityt.ml" run_id.

Definition run_inc := (compile_and_run increment fuel).
Extraction "/tmp/run_target_compiled_increment.ml" run_inc.

Definition run_nested := (compile_and_run nested_calls fuel).
Extraction "/tmp/run_target_compiled_nested_calls.ml" run_nested.