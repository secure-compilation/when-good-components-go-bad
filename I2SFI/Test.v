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


Extract Constant Test.defNumTests => "100".
Extract Constant newRandomSeed => "(Random.State.make [| int_of_string (Sys.getenv ""RAND_SEED"") |] )".

Definition run_test (ct : checker_type) (ig : instr_gen) (f : flag) :=
  match ct with
  | CStore =>
      show (quickCheck (store_correct ig (get_comp_flag f)))
  | CJump =>
      show (quickCheck (jump_correct ig (get_comp_flag f)))
  | CStack =>
      show (quickCheck (cs_correct ig (get_comp_flag f)))
  | CCompCorrect =>
      show (quickCheck (compiler_correct ig FUEL (get_comp_flag f)))
  end.

Extraction "run_test.ml" run_test.