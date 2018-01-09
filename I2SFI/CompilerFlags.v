Record comp_flags : Type :=
  {
    store_instr_off : bool;
    store_instr1_off : bool;
    store_instr2_off : bool;

    jump_instr_off : bool;
    jump_instr1_off : bool;
    jump_instr2_off : bool;

    push_sfi_halt_not_present : bool;
    
    pop_sfi_not_aligned : bool;

    set_sfi_registers_missing : bool;

    after_call_label_missing : bool;

    targets_not_aligned : bool;
    
  }.

Definition set_store_instr_off : comp_flags :=
  {|
    store_instr_off := true;
    store_instr1_off := false;
    store_instr2_off := false;

    jump_instr_off := false;
    jump_instr1_off := false;
    jump_instr2_off := false;

    push_sfi_halt_not_present := false;
    
    pop_sfi_not_aligned := false;

    set_sfi_registers_missing := false;

    after_call_label_missing := false;

    targets_not_aligned := false;

  |}.


Definition set_store_instr1_off : comp_flags :=
  {|
    store_instr_off := false;
    store_instr1_off := true;
    store_instr2_off := false;

    jump_instr_off := false;
    jump_instr1_off := false;
    jump_instr2_off := false;

    push_sfi_halt_not_present := false;
    
    pop_sfi_not_aligned := false;

    set_sfi_registers_missing := false;

    after_call_label_missing := false;

    targets_not_aligned := false;

  |}.

Definition set_store_instr2_off : comp_flags :=
  {|
    store_instr_off := false;
    store_instr1_off := false;
    store_instr2_off := true;

    jump_instr_off := false;
    jump_instr1_off := false;
    jump_instr2_off := false;

    push_sfi_halt_not_present := false;
    
    pop_sfi_not_aligned := false;

    set_sfi_registers_missing := false;

    after_call_label_missing := false;

    targets_not_aligned := false;

  |}.


Definition set_jump_instr_off : comp_flags :=
  {|
    store_instr_off := false;
    store_instr1_off := false;
    store_instr2_off := false;

    jump_instr_off := true;
    jump_instr1_off := false;
    jump_instr2_off := false;

    push_sfi_halt_not_present := false;
    
    pop_sfi_not_aligned := false;

    set_sfi_registers_missing := false;

    after_call_label_missing := false;

    targets_not_aligned := false;

  |}.

Definition set_jump_instr1_off : comp_flags :=
  {|
    store_instr_off := false;
    store_instr1_off := false;
    store_instr2_off := false;

    jump_instr_off := false;
    jump_instr1_off := true;
    jump_instr2_off := false;

    push_sfi_halt_not_present := false;
    
    pop_sfi_not_aligned := false;

    set_sfi_registers_missing := false;

    after_call_label_missing := false;

    targets_not_aligned := false;

  |}.

Definition set_jump_instr2_off : comp_flags :=
  {|
    store_instr_off := false;
    store_instr1_off := false;
    store_instr2_off := false;

    jump_instr_off := false;
    jump_instr1_off := false;
    jump_instr2_off := true;

    push_sfi_halt_not_present := false;
    
    pop_sfi_not_aligned := false;

    set_sfi_registers_missing := false;

    after_call_label_missing := false;

    targets_not_aligned := false;

  |}.

Definition set_push_sfi_halt_not_present : comp_flags :=
  {|
    store_instr_off := false;
    store_instr1_off := false;
    store_instr2_off := false;

    jump_instr_off := false;
    jump_instr1_off := false;
    jump_instr2_off := false;

    push_sfi_halt_not_present := true;
    
    pop_sfi_not_aligned := false;

    set_sfi_registers_missing := false;

    after_call_label_missing := false;

    targets_not_aligned := false;

  |}.

Definition set_pop_sfi_not_aligned : comp_flags :=
  {|
    store_instr_off := false;
    store_instr1_off := false;
    store_instr2_off := false;

    jump_instr_off := false;
    jump_instr1_off := false;
    jump_instr2_off := false;

    push_sfi_halt_not_present := false;
    
    pop_sfi_not_aligned := true;

    set_sfi_registers_missing := false;

    after_call_label_missing := false;

    targets_not_aligned := false;

  |}.

Definition set_set_sfi_registers_missing : comp_flags :=
  {|
    store_instr_off := false;
    store_instr1_off := false;
    store_instr2_off := false;

    jump_instr_off := false;
    jump_instr1_off := false;
    jump_instr2_off := false;

    push_sfi_halt_not_present := false;
    
    pop_sfi_not_aligned := false;

    set_sfi_registers_missing := true;

    after_call_label_missing := false;

    targets_not_aligned := false;

  |}.

Definition set_after_call_label_missing : comp_flags :=
  {|
    store_instr_off := false;
    store_instr1_off := false;
    store_instr2_off := false;

    jump_instr_off := false;
    jump_instr1_off := false;
    jump_instr2_off := false;

    push_sfi_halt_not_present := false;
    
    pop_sfi_not_aligned := false;

    set_sfi_registers_missing := false;

    after_call_label_missing := true;

    targets_not_aligned := false;

  |}.

Definition set_targets_not_aligned : comp_flags :=
  {|
    store_instr_off := false;
    store_instr1_off := false;
    store_instr2_off := false;

    jump_instr_off := false;
    jump_instr1_off := false;
    jump_instr2_off := false;

    push_sfi_halt_not_present := false;
    
    pop_sfi_not_aligned := false;

    set_sfi_registers_missing := false;

    after_call_label_missing := false;

    targets_not_aligned := true;

  |}.


Definition all_flags_off : comp_flags :=
  {|
    store_instr_off := false;
    store_instr1_off := false;
    store_instr2_off := false;

    jump_instr_off := false;
    jump_instr1_off := false;
    jump_instr2_off := false;

    push_sfi_halt_not_present := false;
    
    pop_sfi_not_aligned := false;

    set_sfi_registers_missing := false;

    after_call_label_missing := false;

    targets_not_aligned := false;

  |}.
