Require Import ZArith.

Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Maps.

(******************************************
 * Instruction Set Definition
 *******************************************)

(* Register Type *)
Definition register := N.

Open Scope N_scope.

Definition R_ONE: register := 1.
Definition R_COM : register := 2.
Definition R_AUX1 : register := 3.
Definition R_AUX2 : register := 4.
Definition R_RA : register := 5.
Definition R_SP : register := 6. 

Definition IS_NOT_SFI_REGISTER (reg:N) := reg < 26.
Definition IS_SFI_REGISTER (reg:N) := reg > 25.

Definition is_not_sfi_reg_bool (reg:N) := reg <? 26.

Definition  IS_SFI_SP_REGISTER (reg:N) := reg = 26.

Definition is_sfi_sp_register_bool (reg:N) := reg =? 26.

Definition R_SFI_SP: register := 26.
Definition R_AND_CODE_MASK : register := 27.
Definition R_AND_DATA_MASK : register := 28.
Definition R_OR_CODE_MASK : register := 29.
Definition R_OR_DATA_MASK : register := 30.
Definition R_T : register := 31.
Definition R_D : register := 32.

Close Scope N_scope.

Definition NO_REGISTERS : nat := 33.

Definition value := Z.

Definition ZERO_VALUE : value := Z0.

Definition is_zero_value (v:value) : Prop := (v = Z0).

Definition immediate := Z.

Definition address := N.

Inductive binop : Set :=
  Addition
| Subtraction
| Multiplication
| Equality
| Leq
| BitwiseAnd
| BitwiseOr
| ShiftLeft. 

Open Scope Z_scope.

Definition executing_binop (operation : binop) (op1 : value) (op2 : value) : value :=
  match operation with
    Addition => op1 + op2
  | Subtraction => op1 - op2
  | Multiplication => op1 * op2
  | Equality => if Zeq_bool op1 op2 then 1 else 0
  | Leq => if Zle_bool op1 op2 then 1 else 0
  | BitwiseAnd => Z.land op1 op2
  | BitwiseOr => Z.lor op1 op2
  | ShiftLeft => Z.shiftl op1 op2
  end.

Inductive instr :=
| INop : instr
(* register operations *)
| IConst : value -> register -> instr
| IMov : register -> register -> instr
| IBinOp : binop -> register -> register -> register -> instr
(* memory operations *)
| ILoad : register -> register -> instr
| IStore : register -> register -> instr
(* conditional and unconditional jumps *)
| IBnz : register -> immediate -> instr
| IJump : register -> instr
| IJal : address -> instr
(* termination *)
| IHalt : instr.

Inductive word := 
| Data : value -> word
| Instruction : instr -> word.


(******************************************
 * Program Definition
 *******************************************)

Module SFIComponent.
  
  Definition id := N.
  
End SFIComponent.

(* CN is a map from component numerical identifier to component
identifier used in the labeled transitions from the intermediate
language semantics. *)
Definition CN := SFIComponent.id -> Component.id.

(* Maximum number of components *)
Definition COMP_SIZE:N := 3.

(* Number of bits used for offset within slot *)
Definition OFFSET_SIZE:N := 12.

(* Let C be a map address -> component numerical identifier.
For SFI, C is just the value stored at bits S+1 to S+N. *)
Definition C := address ->  SFIComponent.id.

Definition COMPONENT_MASK : N := 2^COMP_SIZE - 1. 

(* Definition C_SFI  (addr : address) : SFIComponent.id := *)
Definition C_SFI : C := (fun addr =>
                           N.land (N.shiftl addr OFFSET_SIZE) COMPONENT_MASK).

(* E is a partial map from addresses to procedure names.*)
Definition E := address -> Procedure.id.

Definition memory := N -> word.

Module SFI.

  Module RegisterFile.

    Definition pc : Set := address.
    
    Definition general_registers : Set := list value.

    Fixpoint is_zero (gen_regs:general_registers)  : Prop :=
      match gen_regs with
      | [] => True
      | r :: l' => (is_zero_value r)/\ is_zero l'
      end.

    Definition zero : general_registers := repeat Z0 NO_REGISTERS.

    Definition set_register (reg : register) (val : value)
               (gen_regs  : general_registers) : general_registers :=
      (* TODO fix this *)
      Util.Lists.update gen_regs (N.to_nat reg) val.


    Definition get_register (reg : register) (gen_regs : general_registers) : value :=
      (* TODO fix this *)
      nth (N.to_nat reg) gen_regs Z0.

  End RegisterFile.
  
  Module Memory.

    Definition t := BinNatMap.t word.

    Definition get_word (mem : t) (ptr : address) : option word :=
      BinNatMap.find ptr mem.

    Definition get_value (mem : t) (ptr : address) : value :=
      match get_word mem ptr with
      | Some (Data val) => val
      | _ => ZERO_VALUE (* might need to deal with an instruction here*) 
      end.

    Definition set_value (mem : t) (ptr : address) (val : value) : t :=
      BinNatMap.add ptr (Data val) mem.

    Definition to_address (ptr:value) : address :=
      (* negatives are converted to zero *)
      Z.to_N ptr.

    Definition is_same_component (addr1: address) (addr2: address) : Prop :=
      (C_SFI addr1) = (C_SFI addr2).

    Open Scope N_scope.
    
    Definition is_same_component_bool (addr1: address) (addr2: address) :=
      (C_SFI addr1) =? (C_SFI addr2).

    Close Scope N_scope.
    
  End Memory.
  
  Record program :=
    {
      cn : CN;
      e : E;
      mem : Memory.t;
      prog_interface : Program.interface
    }.

  Definition executing (mem : Memory.t) (pc : address) ( i : instr) : Prop :=
    match (Memory.get_word mem pc) with
    | Some (Instruction i') => i = i'
    |  _ => False
    end.

End SFI.

Close Scope Z_scope.