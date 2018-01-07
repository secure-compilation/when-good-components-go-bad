Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import ZArith.

Require Import CompilerPBTests.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Extract Constant Test.defNumTests => "10". 

Inductive checker_type : Type :=
| CStore : checker_type
| CJump : checker_type
| CStack : checker_type
| CCompCorrect : checker_type.

Inductive instr_gen : Type :=
| EqualUndefAllowed : instr_gen
| EqualNoUndef : instr_gen
| TestSpecific : instr_gen.
                         

Definition run_test (ct : checker_type) (ig : instr_gen) :=
  match ct with
  | CStore =>
    match ig with
    | EqualUndefAllowed =>    
      show (quickCheck (store_correct TInstrEqualUndef))
    | EqualNoUndef =>
      show (quickCheck (store_correct TInstrEqual))
    | TestSpecific =>
      show (quickCheck (store_correct TStore))
    end
  | _ => "Error"
  end.

Extraction "run_test.ml" run_test.