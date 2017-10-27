(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.PArith.BinPos.

Require Import Common.Definitions.

Require Import Intermediate.Machine.
Require Import TargetSFI.Machine.

Definition label :Set := Component.id*N.

Definition register := RiscMachine.Register.t.

Inductive ainstr :=
| INop : ainstr
| ILabel : label -> ainstr
(* register operations *)
| IConst : RiscMachine.value -> register -> ainstr
| IMov : register -> register -> ainstr
| IBinOp : RiscMachine.ISA.binop -> register -> register -> register -> ainstr
(* memory operations *)
| ILoad : register -> register -> ainstr
| IStore : register -> register -> ainstr
(* conditional and unconditional jumps *)
| IBnz : register -> label -> ainstr
| IJump : register -> ainstr
| IJal : label -> ainstr
(* termination *)
| IHalt : ainstr.

Definition code := list ainstr.

Definition lcode : Set := list ((option (list AbstractMachine.label)) *
                                AbstractMachine.ainstr).

Definition map_register (reg : Intermediate.Machine.register) : RiscMachine.Register.t :=
  match reg with
  | Intermediate.Machine.R_ONE => RiscMachine.Register.R_ONE
  | Intermediate.Machine.R_COM => RiscMachine.Register.R_COM
  | Intermediate.Machine.R_AUX1 => RiscMachine.Register.R_AUX1
  | Intermediate.Machine.R_AUX2 => RiscMachine.Register.R_AUX2
  | Intermediate.Machine.R_RA => RiscMachine.Register.R_RA
  | Intermediate.Machine.R_SP => RiscMachine.Register.R_SP
  end.

Definition map_binop (op : Common.Values.binop) : RiscMachine.ISA.binop :=
  match op with
  | Add => RiscMachine.ISA.Addition
  | Minus => RiscMachine.ISA.Subtraction
  | Mul => RiscMachine.ISA.Multiplication
  | Eq => RiscMachine.ISA.Equality
  | Leq => RiscMachine.ISA.Leq
  end.

Definition label_eqb (l1 l2 : label) :=
  let '(c1,i1) := l1 in
  let '(c2,i2) := l2 in
  (Pos.eqb c1 c2) && (N.eqb i1 i2).
