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

Record compiler_env :=
  { concretize_pointer : Pointer.t -> int ;
    solve_label : label -> int ;
  }.

Definition encode_val (cenv : compiler_env) (v : imvalue) : imm mt :=
  match v with
  | IInt z => word.as_word 0 (* TODO: convert integer? *)
  | IPtr p => word.as_word (concretize_pointer cenv p)
  end.

Definition encode_reg (cenv : compiler_env) (r : register) : reg mt :=
  match r with
  (* TL TODO: this is a totally arbitrary mapping *)
  | R_ONE => word.as_word 1
  | R_COM => word.as_word 2
  | R_AUX1 => word.as_word 3
  | R_AUX2 => word.as_word 4
  | R_RA => word.as_word 5
  | R_SP => word.as_word 6
  end.

Definition encode_binop (cenv : compiler_env) (b : Values.binop) : binop :=
  match b with
  | Add => ADD
  | Minus => SUB
  | Mul => MUL
  | Eq => EQ
  | Leq => LEQ
  end.

Definition encode_instr  (cenv : compiler_env)(x : Machine.instr * mem_tag) : matom :=
  (* TL TODO: are binop arguments in the same order, etc.*)
  {| vala := match fst x with
             | ICall _ _         => word.as_word 0 (* TL TODO: monadic error? *)
             | IReturn           => word.as_word 0 (* TL TODO: monadic error? *)
             | INop              => encode_instr (Nop mt)
             | ILabel _          => encode_instr (Nop mt)
             | IConst i r        => encode_instr (Const (encode_val cenv i) (encode_reg cenv r))
             | IMov r1 r2        => encode_instr (Mov (encode_reg cenv r1) (encode_reg cenv r2))
             | IBinOp o r1 r2 r3 => encode_instr (Binop (encode_binop cenv o) (encode_reg cenv r1)
                                                       (encode_reg cenv r2) (encode_reg cenv r3))
             | ILoad r1 r2       => encode_instr (Load (encode_reg cenv r1) (encode_reg cenv r2))
             | IStore r1 r2      => encode_instr (Store (encode_reg cenv r1) (encode_reg cenv r2))
             | IAlloc _ _        => word.as_word 0 (* TL TODO: memory allocation *)
             | IBnz r l          => encode_instr (Bnz (encode_reg cenv r)
                                                     (word.as_word (solve_label cenv l)))
             | IJump r           => encode_instr (Jump (encode_reg cenv r))
             | IJal l            => encode_instr (Jal (word.as_word (solve_label cenv l)))
             | IHalt             => encode_instr (Halt mt)
             end ;
     taga := snd x |}.


(* Definition encode_code (code : seq (Machine.instr * mem_tag)) : {fmap atom unit unit -> matom}. *)
(*  fmap_of_seq s *)

(* Definition alloc_buffers  : seq matom. *)
(* Admitted. *)

Definition encode (prog : Precompile.prog) :=
  (* Solve labels *)
  let labels : seq int := (* TL TODO: int is an ugly hack to get an eqType for free       *)
                          (*          switch to eqTypes for Intermediate.instr eventually *)
      map (fun x => match fst x with ILabel l => Posz l | _ => Negz 1 end) (Precompile.procedures prog) in
  let solve (l : label) := index (Posz l) labels in
  (* Concretize pointers *)
  let concretize := (fun _ => 0) in (* TL TODO! *)
  {| solve_label := solve ;
     concretize_pointer := concretize |}.
