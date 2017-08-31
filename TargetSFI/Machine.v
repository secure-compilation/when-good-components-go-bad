Require Import ZArith.

Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Maps.


(******************************************
 * Instruction Set Definition
 *******************************************)

(* Registers *)
Definition register := nat.

Definition R_ONE: register := 1.
Definition R_COM : register := 2.
Definition R_AUX1 : register := 3.
Definition R_AUX2 : register := 4.
Definition R_RA : register := 5.
Definition R_SP : register := 6. 
Definition R_SP_SFI : register := 7. 
Definition R_AND_CODE : register := 8.
Definition R_AND_DATA : register := 9.
Definition R_OR_DATA : register := 10. (* TODO add all SFI registers *)

Definition value := Z.

Definition ZERO_VALUE : value := Z.of_nat 0.

Definition is_zero_value (v:value) : Prop := (v = Z.of_nat 0).

Definition immediate := Z.

Definition address := nat.

Inductive binop : Set :=
  Plus | ShiftLeft. (* TODO add all *)

Open Scope Z_scope.

Definition executing_binop (operation : binop) (op1 : value) (op2 : value) : value :=
  match operation with
  | Plus => op1 + op2
  | _ => ZERO_VALUE (* TODO finish this *)
  end.

Close Scope Z_scope.

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

(******************************************
 * Program Definition
 *******************************************)

Inductive word := 
| Data : Z -> word
| Instruction : instr -> word.


Module SFIComponent.
  
  Definition id := nat.
  
End SFIComponent.

(* CN is a map from component numerical identifier to component
identifier used in the labeled transitions from the intermediate
language semantics. *)
Definition CN := SFIComponent.id -> Component.id.

(* Let C be a map address -> component numerical identifier.
For SFI, C is just the value stored at bits S+1 to S+N. *)
Definition C := address -> nat. 

(* E is a partial map from addresses to procedure names.*)
Definition E := address -> Procedure.id.

Definition memory := nat -> word.

Module SFI.

  Module RegisterFile.

    Definition t : Set := list value.

    Fixpoint is_zero (gen_regs:t)  : Prop :=
      match gen_regs with
      | [] => True
      | r :: l' => (is_zero_value r)/\ is_zero l'
      end.

    Definition set_register (reg : register) (val : value) (gen_regs  : t) : t :=
      Util.Lists.update gen_regs reg val.


    Definition get_register (reg : register) (gen_regs : t) : value :=
      nth reg gen_regs (Z.of_nat 0).

  End RegisterFile.
  
  Module Memory.

    Definition t := NMap.t word.

    Definition get_word (mem : t) (ptr : address) : option word :=
      NMap.find ptr mem.

    Definition get_value (mem : t) (ptr : address) : value :=
      match get_word mem ptr with
      | Some (Data val) => val
      | _ => ZERO_VALUE (* might need to deal with an istruction here*)
      end.

    Definition to_address (ptr:value) : address :=
      (* todo *) 0.
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