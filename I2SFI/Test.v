Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import ZArith.

Require Import CompilerPBTests.
Require Import RCPBTests.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Extract Constant Test.defNumTests => "10000". 

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
  | CJump =>
    match ig with
    | EqualUndefAllowed =>    
      show (quickCheck (jump_correct TInstrEqualUndef))
    | EqualNoUndef =>
      show (quickCheck (jump_correct TInstrEqual))
    | TestSpecific =>
      show (quickCheck (jump_correct TJump))
    end
  | CStack =>
    match ig with
    | EqualUndefAllowed =>    
      show (quickCheck (cs_correct TInstrEqualUndef))
    | EqualNoUndef =>
      show (quickCheck (cs_correct TInstrEqual))
    | TestSpecific =>
      show (quickCheck (cs_correct TStack))
    end
  | CCompCorrect =>
    match ig with
    | EqualUndefAllowed =>    
      show (quickCheck (compiler_correct TInstrEqualUndef FUEL))
    | EqualNoUndef =>
      show (quickCheck (compiler_correct TInstrEqual FUEL))
    | TestSpecific =>
      show (quickCheck (compiler_correct TCompilerCorrect FUEL))
    end
  end.

Extraction "run_test.ml" run_test.