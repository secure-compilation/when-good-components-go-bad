Require Import ZArith.

Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Maps.

(******************************************
 * Basic Risc Machine Definition
 *******************************************)
Module RiscMachine.

  Definition value := Z.

  Definition immediate := Z.

  Definition address := N.


  
  Module Register.
    
    Definition t := N.
    Open Scope N_scope.
    Definition R_ONE: t := 1.
    Definition R_COM : t := 2.
    Definition R_AUX1 : t := 3.
    Definition R_AUX2 : t := 4.
    Definition R_RA : t := 5.
    Definition R_SP : t := 6. 
    (* reserved SFI registers *)
    Definition R_SFI_SP: t := 26.
    Definition R_AND_CODE_MASK : t := 27.
    Definition R_AND_DATA_MASK : t := 28.
    Definition R_OR_CODE_MASK : t := 29.
    Definition R_OR_DATA_MASK : t := 30.
    Definition R_T : t := 31.
    Definition R_D : t := 32.
    Close Scope N_scope.

    Definition NO_REGISTERS : nat := 33.

    
    (* Definition IS_NOT_SFI_REGISTER (reg:N) := reg < 26. *)
    (* Definition IS_SFI_REGISTER (reg:N) := reg > 25. *)
    (* Definition is_not_sfi_reg_bool (reg:N) := reg <? 26.     *)
    (* Definition  IS_SFI_SP_REGISTER (reg:N) := reg = 26.     *)
    (* Definition is_sfi_sp_register_bool (reg:N) := reg =? 26. *)

  End Register.

  Definition pc : Set := address.
  
  Module RegisterFile.
    
    Definition t : Set := list value.

    Fixpoint is_zero (gen_regs:t)  : Prop :=
      match gen_regs with
      | [] => True
      | r :: l' => (r = Z0 )/\ is_zero l'
      end.

    Definition zero : t := repeat Z0 Register.NO_REGISTERS.

    Definition set_register (reg : Register.t) (val : value)
               (gen_regs  : t) : t :=
      (* TODO fix this *)
      Util.Lists.update gen_regs (N.to_nat reg) val.


    Definition get_register (reg : Register.t) (gen_regs : t) : value :=
      (* TODO fix this *)
      nth (N.to_nat reg) gen_regs Z0.

  End RegisterFile.


  Module ISA.
    
    Inductive binop :=
    | Addition
    | Subtraction
    | Multiplication
    | Equality
    | Leq
    | BitwiseAnd
    | BitwiseOr
    | ShiftLeft. 
  
    Inductive instr :=
    | INop : instr
    (* register operations *)
    | IConst : value -> Register.t -> instr
    | IMov : Register.t -> Register.t -> instr
    | IBinOp : binop -> Register.t -> Register.t -> Register.t -> instr
    (* memory operations *)
    | ILoad : Register.t -> Register.t -> instr
    | IStore : Register.t -> Register.t -> instr
    (* conditional and unconditional jumps *)
    | IBnz : Register.t -> immediate -> instr
    | IJump : Register.t -> instr
    | IJal : address -> instr
    (* termination *)
    | IHalt : instr.
    
  End ISA.

  
  Inductive word := 
  | Data : value -> word
  | Instruction : ISA.instr -> word.

  
  Module Memory.

    Definition t := BinNatMap.t word.

    Definition get_word (mem : t) (ptr : address) : option word :=
      BinNatMap.find ptr mem.

    Definition get_value (mem : t) (ptr : address) : value :=
      match get_word mem ptr with
      | Some (Data val) => val
      | _ => Z0 (* might need to deal with an instruction here*) 
      end.

    Definition set_value (mem : t) (ptr : address) (val : value) : t :=
      BinNatMap.add ptr (Data val) mem.

    Definition to_address (ptr:value) : address :=
      (* negatives are converted to zero *)
      Z.to_N ptr.
    Close Scope N_scope.
    
  End Memory.

  (* Open Scope Z_scope. *)
  (* Definition executing_binop (operation : ISA.binop) (op1 : value) (op2 : value) : value := *)
  (* match operation with *)
  (* | Addition => op1 + op2 *)
  (* | Subtraction => op1 - op2 *)
  (* | Multiplication => op1 * op2 *)
  (* | Equality => if Zeq_bool op1 op2 then 1 else 0 *)
  (* | Leq => if Zle_bool op1 op2 then 1 else 0 *)
  (* | BitwiseAnd => Z.land op1 op2 *)
  (* | BitwiseOr => Z.lor op1 op2 *)
  (* | ShiftLeft => Z.shiftl op1 op2 *)
  (* end. *)
  (* Close Scope Z_scope. *)

  
  Definition executing (mem : Memory.t) (pc : address) ( i : ISA.instr) : Prop :=
    match (Memory.get_word mem pc) with
    | Some (Instruction i') => i = i'
    |  _ => False
    end.

  
End RiscMachine.


(******************************************
 * Program Definition
 *******************************************)

Module SFIComponent.
  
  Definition id := N.
  
End SFIComponent.


Module Env.

  (* CN is a map from component numerical identifier to component
     identifier used in the labeled transitions from the intermediate
     language semantics. *)
  Definition CN := SFIComponent.id -> Component.id.

  (* E is a partial map from addresses to procedure names.*)
  Definition E := list (RiscMachine.address, Procedure.id).

End Env.

Module SFI.

  (* Maximum number of components *)
  Definition COMP_MAX:N := 3.

  (* Number of bits used for offset within slot *)
  Definition OFFSET_SIZE:N := 12.

  Definition COMPONENT_MASK : N := 2^COMP_SIZE - 1. 

  Definition C_SFI (addr : RiscMachine.address) : SFIComponent.id  := 
    N.land (N.shiftl addr OFFSET_SIZE) COMPONENT_MASK.


  Record program :=
    {
      cn : Env.CN;
      e : Env.E;
      mem : RiscMachine.Memory.t;
      prog_interface : Program.interface
    }.


  (* Definition is_same_component (addr1: address) (addr2: address) : Prop := *)
  (*   (C_SFI addr1) = (C_SFI addr2). *)

  
  (* Definition is_same_component_bool (addr1: address) (addr2: address) := *)
  (*       (C_SFI addr1) =? (C_SFI addr2). *)

End SFI.