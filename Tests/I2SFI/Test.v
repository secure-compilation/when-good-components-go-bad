Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import ZArith.

Require Import Tests.CompilerPBTests.
Require Import Tests.I2SFI.StoreTest.
Require Import Tests.I2SFI.JumpTest.
Require Import Tests.I2SFI.StackTest.
Require Import Tests.I2SFI.SFI_RSC_Test.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Extract Constant Test.defNumTests => "100".
(* number of target machine instructions to simulate *)
Definition FUEL := 100%nat. 

Definition run_store_test :=
  show (quickCheck (store_correct FUEL)). 

Definition run_jump_test :=
  show (quickCheck (jump_correct FUEL)).

Definition run_stack_test :=
  show (quickCheck (stack_correct FUEL)).

Definition run_rsc_test :=
  show (quickCheck (sfi_rsc_correct FUEL)).

Extraction "/tmp/run_test.ml" run_store_test run_jump_test  run_stack_test run_rsc_test.

