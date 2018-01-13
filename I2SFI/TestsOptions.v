Require Import CompilerFlags.

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


Inductive instr_gen : Type :=
| EqualUndefAllowed : instr_gen
| EqualNoUndef : instr_gen
| TestSpecific : instr_gen.


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
