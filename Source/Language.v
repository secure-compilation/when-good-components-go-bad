Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.

Inductive expr : Type :=
| E_val : value -> expr
| E_local : expr
| E_binop : binop -> expr -> expr -> expr
| E_seq : expr -> expr -> expr
| E_if : expr -> expr -> expr -> expr
| E_alloc : expr -> expr
| E_deref : expr -> expr
| E_assign : expr -> expr -> expr
| E_call : Component.id -> Procedure.id -> expr -> expr
| E_exit : expr.

Record program : Type := mkProg {
  prog_interface : Program.interface;
  prog_procedures : NMap.t (NMap.t expr);
  prog_buffers : NMap.t nat
}.