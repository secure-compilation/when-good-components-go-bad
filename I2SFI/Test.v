Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import ZArith.

Require Import CompilerPBTests.
Require Import I2SFI.StoreTest.
Require Import I2SFI.JumpTest.
Require Import I2SFI.StackTest.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.


Extract Constant Test.defNumTests => "1000".
Extract Constant newRandomSeed => "(Random.State.make [| int_of_string (Sys.getenv ""RAND_SEED"") |] )".

(* number of target machine instructions to simulate *)
Definition FUEL := 100%nat. 

Definition run_store_test :=
  show (quickCheck (store_correct FUEL)).

Definition run_jump_test :=
  show (quickCheck (jump_correct FUEL)).

Definition run_stack_test :=
  show (quickCheck (stack_correct FUEL)).

(* Extraction "/tmp/run_store_test.ml" run_store_test. *)
(* Extraction "/tmp/run_jump_test.ml" run_jump_test. *)
(* Extraction "/tmp/run_stack_test.ml" run_stack_test. *)

(****************** QUICK CHECKS ***************************)
Extract Constant Test.defNumTests => "10".
QuickChick (store_correct 100%nat).
QuickChick (jump_correct 100%nat).
QuickChick (stack_correct 100%nat).
