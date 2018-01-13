Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import ZArith.

Require Import I2SFI.CompilerFlags.
Require Import CompilerPBTests.
Require Import RCPBTests.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Require Import TestsOptions.

Extract Constant newRandomSeed => "(Random.State.make [| 42 |] )".
Extract Constant Test.defNumTests => "60000". 

Definition run_store_test (ig : instr_gen) (f : flag) :=
  match ig with
  | EqualUndefAllowed =>    
    show (quickCheck (store_correct TInstrEqualUndef (get_comp_flag f)))
  | EqualNoUndef =>
    show (quickCheck (store_correct TInstrEqual (get_comp_flag f)))
  | TestSpecific =>
    show (quickCheck (store_correct TStore (get_comp_flag f)))
  end.

Extraction "run_store_test.ml" run_store_test.