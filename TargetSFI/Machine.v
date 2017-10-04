Require Import Coq.ZArith.ZArith.
Require Import Coq.Structures.Equalities.

Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Maps.
Require Import SFIUtil.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.

From mathcomp.ssreflect Require Import ssreflect ssrbool eqtype.

(******************************************
 * Basic Risc Machine Definition
 *******************************************)
Module RiscMachine.

  Definition value := Z.

  Definition immediate := Z.

  Definition address := N.


  Module Register.
    
    Open Scope N_scope.
    Definition t := N.
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

    Definition reset_all : t := repeat Z0 Register.NO_REGISTERS.

    Definition set_register (reg : Register.t) (val : value)
               (gen_regs  : t) : t :=
      Util.Lists.update gen_regs (N.to_nat reg) val.


    Definition get_register (reg : Register.t) (gen_regs : t) : option value :=
      ListUtil.get (N.to_nat reg) gen_regs.

  End RegisterFile.


  Module ISA.
    
    Inductive binop : Type :=
    | Addition : binop
    | Subtraction : binop
    | Multiplication : binop
    | Equality : binop
    | Leq : binop
    | BitwiseOr : binop
    | BitwiseAnd : binop
    | ShiftLeft : binop. 
  
    Inductive instr : Set :=
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

    Definition get_value (mem : t) (ptr : address) : option value :=
      match get_word mem ptr with
      | Some (Data val) => Some val
      | _ => None (* might need to deal with an instruction here*) 
      end.

    Definition set_value (mem : t) (ptr : address) (val : value) : t :=
      BinNatMap.add ptr (Data val) mem.

    Definition to_address (ptr:value) : address :=
      (* negatives are converted to zero *)
      Z.to_N ptr.
    
  End Memory.


  Definition executing_binop (op : ISA.binop)
             (op1 : value) (op2 : value) : value :=
    match op with
    | ISA.Addition => op1 + op2
    | ISA.Subtraction => op1 - op2
    | ISA.Multiplication => op1 * op2
    | ISA.Equality => if Zeq_bool op1 op2 then 1 else 0
    | ISA.Leq => if Zle_bool op1 op2 then 1 else 0
    | ISA.BitwiseAnd => Z.land op1 op2
    | ISA.BitwiseOr => Z.lor op1 op2
    | ISA.ShiftLeft => Z.shiftl op1 op2
  end.
  
  Definition executing (mem : Memory.t) (pc : address) ( i : ISA.instr) : Prop :=
    match (Memory.get_word mem pc) with
    | Some (Instruction i') => i = i'
    |  _ => False
    end.


  Definition inc_pc (a : pc) : pc := N.add a 1.

  
End RiscMachine.


Close Scope Z_scope.

(******************************************
 * Program Definition
 *******************************************)
Module SFIComponent.

  Definition id := N.

    (* Maximum number of components *)
  Definition COMP_MAX:N := 3.

End SFIComponent.

Module Env  <: UsualDecidableType.

  (* list of dimension COMP_MAX + 1 *)
  Definition CN := list Component.id.

  (* E is a partial map from addresses to procedure names.*)
  Definition E := list (RiscMachine.address*Procedure.id).

  Definition t := CN * E.

  Definition get_component_name_from_id (id : SFIComponent.id)
             (G : t): option Component.id :=
    ListUtil.get (N.to_nat id) (fst G).

  Definition get_procedure (addr : RiscMachine.address)
             (G : Env.t) : option Procedure.id :=
    ListUtil.get_by_key (N.eqb) addr (snd G).

  Definition eq_dec:
    forall g1 g2 : t,  {g1 = g2} + {g1 <> g2}.
  Proof.
    repeat decide equality. Defined.

  Include HasUsualEq <+ UsualIsEq.
  
End Env.


Module SFI.

  (* Number of bits used for offset within slot *)
  Definition OFFSET_SIZE:N := 12.

  Definition COMPONENT_MASK : N := 2^SFIComponent.COMP_MAX - 1. 

  Definition C_SFI (addr : RiscMachine.address) : SFIComponent.id  := 
    N.land (N.shiftl addr OFFSET_SIZE) COMPONENT_MASK.


  Record program :=
    {
      cn : Env.CN;
      e : Env.E;
      mem : RiscMachine.Memory.t;
      prog_interface : Program.interface
    }.


  Definition is_same_component (addr1: RiscMachine.address)
             (addr2: RiscMachine.address) : Prop :=
    (C_SFI addr1) = (C_SFI addr2).

  
  Definition is_same_component_bool (addr1: RiscMachine.address)
             (addr2: RiscMachine.address) :=
    N.eqb (C_SFI addr1) (C_SFI addr2).

End SFI.

Module MachineState.

  Definition t := RiscMachine.Memory.t * RiscMachine.pc * RiscMachine.RegisterFile.t.

End MachineState.


