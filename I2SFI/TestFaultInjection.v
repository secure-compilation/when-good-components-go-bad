Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import ZArith.

Require Import CompilerPBTests.
Require Import RCPBTests.
Require Import I2SFI.CompilerFlags.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.

Require Import ExtrOcamlBasic.

Extract Constant Test.defNumTests => "60000". 


Inductive checker_type : Type :=
| CStore : checker_type
| CJump : checker_type
| CStack : checker_type
| CCompCorrect : checker_type.

Inductive flag : Type :=
| TStoreInstrOff : flag
| TStoreInstr1Off : flag
| TStoreInstr2Off : flag

| TJumpInstrOff : flag
| TJumpInstr1Off : flag
| TJumpInstr2Off : flag

| TPushSfiHaltNotPresent : flag

| TPopSfiNotAligned : flag
                        
| TSetSfiRegistersMissing : flag

| TAfterCallLabelMissing : flag

| TTargetsNotAligned : flag

| TAllOff : flag.
  
Definition get_comp_flag (f : flag) : comp_flags :=
  match f with
  | TStoreInstrOff => set_store_instr_off
  | TStoreInstr1Off => set_store_instr1_off
  | TStoreInstr2Off => set_store_instr2_off
                        
  | TJumpInstrOff => set_jump_instr_off
  | TJumpInstr1Off => set_jump_instr1_off
  | TJumpInstr2Off => set_jump_instr2_off
                       
  | TPushSfiHaltNotPresent => set_push_sfi_halt_not_present
                               
  | TPopSfiNotAligned => set_pop_sfi_not_aligned
                          
  | TSetSfiRegistersMissing => set_set_sfi_registers_missing
                                
  | TAfterCallLabelMissing => set_after_call_label_missing
                               
  | TTargetsNotAligned => set_targets_not_aligned
                           
  | TAllOff => all_flags_off
  end.

Definition run_injection_test (ct : checker_type) (f : flag) :=
  match ct with
  | CStore => show (quickCheck (store_correct TStore (get_comp_flag f)))
  | CJump => show (quickCheck (jump_correct TJump (get_comp_flag f)))
  | CStack => show (quickCheck (cs_correct TStack (get_comp_flag f)))
  | CCompCorrect => show (quickCheck (compiler_correct TCompilerCorrect FUEL
                                                      (get_comp_flag f)))
  end.

Extraction "run_injection_test.ml" run_injection_test.