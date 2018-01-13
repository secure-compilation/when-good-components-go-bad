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

Extract Constant Test.defNumTests => "10000". 
                         

Definition run_test (ct : checker_type) (ig : instr_gen) :=
  match ct with
  | CStore =>
    match ig with
    | EqualUndefAllowed =>    
      show (quickCheck (store_correct TInstrEqualUndef all_flags_off))
    | EqualNoUndef =>
      show (quickCheck (store_correct TInstrEqual all_flags_off))
    | TestSpecific =>
      show (quickCheck (store_correct TStore all_flags_off))
    end
  | CJump =>
    match ig with
    | EqualUndefAllowed =>    
      show (quickCheck (jump_correct TInstrEqualUndef all_flags_off))
    | EqualNoUndef =>
      show (quickCheck (jump_correct TInstrEqual all_flags_off))
    | TestSpecific =>
      show (quickCheck (jump_correct TJump all_flags_off))
    end
  | CStack =>
    match ig with
    | EqualUndefAllowed =>    
      show (quickCheck (cs_correct TInstrEqualUndef all_flags_off))
    | EqualNoUndef =>
      show (quickCheck (cs_correct TInstrEqual all_flags_off))
    | TestSpecific =>
      show (quickCheck (cs_correct TStack all_flags_off))
    end
  | CCompCorrect =>
    match ig with
    | EqualUndefAllowed =>    
      show (quickCheck (compiler_correct TInstrEqualUndef FUEL all_flags_off))
    | EqualNoUndef =>
      show (quickCheck (compiler_correct TInstrEqual FUEL all_flags_off))
    | TestSpecific =>
      show (quickCheck (compiler_correct TCompilerCorrect FUEL all_flags_off))
    end
  end.

Extraction "run_test.ml" run_test.