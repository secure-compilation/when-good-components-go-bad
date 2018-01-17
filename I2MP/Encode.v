Require Import Common.Definitions.
(* TL TODO: Ariths Export is a pain *)

From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint.
From CoqUtils Require Import fmap fset.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.LRC.
Require Precompile.

Require Import Lib.Monads.
Import MonadNotations.
Open Scope monad_scope.


(** Encode: resolve labels, encode instructions, allocate buffers, concretize pointers **)

Require Import MicroPolicies.Types.

Local Notation mt := Symbolic.mt.

Definition encode_value (v : imvalue) : imm mt :=
  match v with
  | IInt z => word.as_word 0 (* TODO: convert integer? *)
  | _ => word.as_word 0
  end.

SearchPattern (Z -> int).


Definition encode_reg (r : register) : reg mt :=
  match r with
  (* TL TODO: this is a totally arbitrary mapping *)
  | R_ONE => word.as_word 1
  | R_COM => word.as_word 2
  | R_AUX1 => word.as_word 3
  | R_AUX2 => word.as_word 4
  | R_RA => word.as_word 5
  | R_SP => word.as_word 6
  end.

Definition encode_binop (b : Values.binop) : binop :=
  match b with
  | Add => ADD
  | Minus => SUB
  | Mul => MUL
  | Eq => EQ
  | Leq => LEQ
  end.

Definition encode_instr (x : Machine.instr * mem_tag) : matom :=
  (* TL TODO: are binop arguments in the same order, etc.*)
  {| vala := match fst x with
             | ICall _ _         => word.as_word 0 (* TL TODO: monadic error? *)
             | IReturn           => word.as_word 0 (* TL TODO: monadic error? *)
             | INop              => encode_instr (Nop mt)
             | ILabel _          => encode_instr (Nop mt)
             | IConst _ _        => word.as_word 0 (* TL TODO: concretize pointers *)
             | IMov r1 r2        => encode_instr (Mov (encode_reg r1) (encode_reg r2))
             | IBinOp o r1 r2 r3 => encode_instr (Binop (encode_binop o) (encode_reg r1)
                                                       (encode_reg r2) (encode_reg r3))
             | ILoad r1 r2       => encode_instr (Load (encode_reg r1) (encode_reg r2))
             | IStore r1 r2      => encode_instr (Store (encode_reg r1) (encode_reg r2))
             | IAlloc _ _        => word.as_word 0 (* TL TODO: memory allocation *)
             | IBnz _ _          => word.as_word 0 (* TL TODO: label resolution *)
             | IJump r           => encode_instr (Jump (encode_reg r))
             | IJal _            => word.as_word 0 (* TL TODO: label resolution *)
             | IHalt             => encode_instr (Halt mt)
             end ;
     taga := snd x |}.

(*  fmap_of_seq s *)
(*         invm m *)

(* Definition encode_code (code : seq (Machine.instr * mem_tag)). *)



(* Definition alloc_buffers  : seq matom. *)
(* Admitted. *)