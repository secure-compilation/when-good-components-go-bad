Require Import ZArith.

Require Import Common.Definitions.


(******************************************
 * Instruction Set Definition
 *******************************************)

(* Register File *)
Inductive register : Set :=
  R_ONE : register
| R_COM : register
| R_AUX1 : register
| R_AUX2 : register
| R_RA : register
| R_SP : register
| R_SP_SFI : register
| R_AND_CODE : register
| R_AND_DATA : register
| R_OR_DATA : register. (* TODO add all SFI registers *)

Definition value := Z.

Definition is_zero_value (v:value) : Prop := (v = Z.of_nat 0).

Definition immediate := Z.

Definition address := nat.

Inductive binop : Type :=
  Plus | ShiftLeft. (* TODO add all *)

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

Definition Memory := nat -> word.

Module SFI.

  Module RegisterFile.

    Definition t : Set := list value.

    Fixpoint is_zero (gen_regs:t)  : Prop :=
      match gen_regs with
      | [] => True
      | r :: l' => (is_zero_value r)/\ is_zero l'
      end.

  End RegisterFile.

  Record program :=
    {
      cn : CN;
      e : E;
      mem : Memory;
      prog_interface : Program.interface
    }.

End SFI.