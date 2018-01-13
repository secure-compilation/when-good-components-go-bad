Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import ZArith.

Require Import CompilerPBTests.
Require Import RCPBTests.
Require Import I2SFI.CompilerFlags.

Require Import TestsOptions.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.

Require Import ExtrOcamlBasic.

Extract Constant Test.defNumTests => "60000". 

  
Definition run_injection_test (ct : checker_type) (f : flag) :=
  match ct with
  | CStore => show (quickCheck (store_correct TStore (get_comp_flag f)))
  | CJump => show (quickCheck (jump_correct TJump (get_comp_flag f)))
  | CStack => show (quickCheck (cs_correct TStack (get_comp_flag f)))
  | CCompCorrect => show (quickCheck (compiler_correct TCompilerCorrect FUEL
                                                      (get_comp_flag f)))
  end.

Extraction "run_injection_test.ml" run_injection_test.