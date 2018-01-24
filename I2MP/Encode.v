Require Import Common.Definitions.
(* TL TODO: Ariths Export is a pain *)

From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint.
From CoqUtils Require Import fmap fset word.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.LRC.
Require Precompile.
Require Tmp.

Require Import Lib.Monads.
Import MonadNotations.
Open Scope monad_scope.


(** Encode: resolve labels, encode instructions, allocate buffers, concretize pointers **)

Require Import MicroPolicies.Types.

Local Notation mt := Symbolic.mt.
Local Notation memory := {fmap mword mt -> matom }.

Record encoder_env :=
  { concretize_pointer : Pointer.t -> int ;
    solve_label : label -> int ;
  }.

Definition encode_imval (eenv : encoder_env) (v : imvalue) : imm mt :=
  match v with
  | IInt z => word.as_word 0 (* TODO: convert integer? *)
  | IPtr p => word.as_word (concretize_pointer eenv p)
  end.


Definition encode_memval (eenv : encoder_env) (x : value * mem_tag) : matom :=
  {| vala := match fst x with
             | Int z => word.as_word 0 (* TODO: convert integer? *)
             | Ptr p => word.as_word (concretize_pointer eenv p)
             | Undef =>  word.as_word 0 (* TODO: convert integer? *)
             end ;
     taga := snd x |}.

Definition encode_reg (eenv : encoder_env) (r : register) : reg mt :=
  match r with
  (* TL TODO: this is a totally arbitrary mapping *)
  | R_ONE => word.as_word 1
  | R_COM => word.as_word 2
  | R_AUX1 => word.as_word 3
  | R_AUX2 => word.as_word 4
  | R_RA => word.as_word 5
  | R_SP => word.as_word 6
  end.

Definition encode_binop (eenv : encoder_env) (b : Values.binop) : binop :=
  match b with
  | Add => ADD
  | Minus => SUB
  | Mul => MUL
  | Eq => EQ
  | Leq => LEQ
  end.

Definition encode_instr  (eenv : encoder_env) (x : Machine.instr * mem_tag) : matom :=
  (* TL TODO: are binop arguments in the same order, etc.*)
  {| vala := match fst x with
             | ICall _ _         => word.as_word 0
             | IReturn           => word.as_word 0
             | INop              => encode_instr (Nop mt)
             | ILabel _          => encode_instr (Nop mt)
             | IConst i r        => encode_instr (Const (encode_imval eenv i) (encode_reg eenv r))
             | IMov r1 r2        => encode_instr (Mov (encode_reg eenv r1) (encode_reg eenv r2))
             | IBinOp o r1 r2 r3 => encode_instr (Binop (encode_binop eenv o) (encode_reg eenv r1)
                                                       (encode_reg eenv r2) (encode_reg eenv r3))
             | ILoad r1 r2       => encode_instr (Load (encode_reg eenv r1) (encode_reg eenv r2))
             | IStore r1 r2      => encode_instr (Store (encode_reg eenv r1) (encode_reg eenv r2))
             | IAlloc _ _        => word.as_word 0 (* TL TODO: memory allocation *)
             | IBnz r l          => encode_instr (Bnz (encode_reg eenv r)
                                                     (word.as_word (solve_label eenv l)))
             | IJump r           => encode_instr (Jump (encode_reg eenv r))
             | IJal l            => encode_instr (Jal (word.as_word (solve_label eenv l)))
             | IHalt             => encode_instr (Halt mt)
             end ;
     taga := snd x |}.


Definition encode_code (eenv : encoder_env) (code : Precompile.code) : memory :=
  let f : nat -> mword mt := word.as_word in
  Tmp.mapk f (fmap_of_seq (map (encode_instr eenv) code)).

Definition alloc_buffers (eenv : encoder_env) (bufs : Precompile.bufs) (* : memory. *) :=
  mapm (fun map : NMap (value * mem_tag) => tt) bufs.

  (* mkfmap (map (fun p => (word.as_word (concretize_pointer eenv p), encode_memval eenv (get_val p))) all_pointers). *)

Admitted.

Definition block_size (bufs : Precompile.bufs) (c : Component.id) (b : Block.id) : nat :=
  (* TL TODO: the fact that the size of the block is the lenght of the map is not obvious, it is a translation invariant... ; should take the max index *)
  Option.default 0 (do m <- getm bufs c;
                    do b <- getm m b;
                    Some (length b)).

Definition encode (prog : Precompile.prog) : {fmap mword mt -> matom}:=
  (* Solve labels *)
  let labels : seq int := (* TL TODO: int is an ugly hack to get an eqType for free;      *)
                          (*          switch to eqTypes for Intermediate.instr eventually *)
      map (fun x => match fst x with ILabel l => Posz l | _ => Negz 1 end)
          (Precompile.procedures prog) in
  let solve (l : label) := index (Posz l) labels in
  (* Concretize pointers *)
  let concretize := (fun _ => 0) in (* TL TODO! *)
  let eenv := {| solve_label := solve ;
                 concretize_pointer := concretize |}
  in unionm (encode_code eenv (Precompile.procedures prog))
            (alloc_buffers eenv (Precompile.buffers prog)).
