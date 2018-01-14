Require Import Common.Definitions.
(* TL TODO: Ariths Export is a pain *)

From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint.
From CoqUtils Require Import fmap fset.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.LRC.

Require Import Lib.Monads.
Import MonadNotations.
Open Scope monad_scope.


(** Encode: resolve labels, encode instructions, allocate buffers, concretize pointers **)

Require Import MicroPolicies.Types.

Definition encode_instr (x : Machine.instr * mem_tag) : matom :=
     {| vala := match fst x with
             | ICall _ _      => word.as_word 0 (* TL TODO: monadic error? *)
             | IReturn        => word.as_word 0 (* TL TODO: monadic error? *)
             | INop           => encode_instr (Nop Symbolic.mt)
             | ILabel _       => encode_instr (Nop Symbolic.mt)
             | IConst _ _     => encode_instr (Nop Symbolic.mt)
             | IMov _ _       => encode_instr (Nop Symbolic.mt)
             | IBinOp _ _ _ _ => encode_instr (Nop Symbolic.mt)
             | ILoad _ _      => encode_instr (Nop Symbolic.mt)
             | IStore _ _     => encode_instr (Nop Symbolic.mt)
             | IAlloc _ _     => encode_instr (Nop Symbolic.mt)
             | IBnz _ _       => encode_instr (Nop Symbolic.mt)
             | IJump _        => encode_instr (Nop Symbolic.mt)
             | IJal _         => encode_instr (Nop Symbolic.mt)
             | IHalt          => encode_instr (Nop Symbolic.mt)
                end ;
        taga := snd x |}.
