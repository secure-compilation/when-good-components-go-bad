Require Import Common.Definitions.
(* TL TODO: Ariths Export is a pain *)

From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint ssrnat.
From CoqUtils Require Import fmap fset word.

Require Import Intermediate.Machine.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Instance.
Require Linearize.
Require Tmp.

Require Import Lib.Monads.
Import MonadNotations.
Open Scope monad_scope.


(** Encode: resolve labels, encode instructions, allocate static buffers, concretize pointers to static buffers **)

Require Import MicroPolicies.Types.

Local Notation memory := {fmap mword mt -> matom }.

Record encoder_env :=
  { concretize_pointer : Pointer.t -> int ;
    solve_label : label -> int ;
  }.

Definition encode_int (z : Z) : int :=
  match z with
  | Z0 => 0
  | Z.pos n => Posz (ssrnat.nat_of_pos n)
  | Z.neg n => Negz (ssrnat.nat_of_pos n)
  end.

Definition encode_imval (eenv : encoder_env) (v : imvalue) : imm mt :=
  match v with
  | IInt z => word.as_word (encode_int z)
  | IPtr p => word.as_word (concretize_pointer eenv p)
  end.


Definition encode_memval (eenv : encoder_env) (x : value * mem_tag) : matom :=
  {| vala := match fst x with
             | Int z => word.as_word (encode_int z)
             | Ptr p => word.as_word (concretize_pointer eenv p)
             | Undef =>  word.as_word 0 (* Invariant: should not be present *)
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

Definition encode_instr  (eenv : encoder_env) (x : sum Linearize.sp_instr Machine.instr * mem_tag) : matom :=
  (* TL TODO: are binop arguments in the same order, etc.*)
  {| vala := match fst x with
             | inr i => match i with
               | ICall _ _         => word.as_word 0 (* Invariant: should not be present *)
               | IReturn           => word.as_word 0 (* Invariant: should not be present *)
               | INop              => encode_instr (Nop mt)
               | ILabel _          => encode_instr (Nop mt)
               | IConst i r        => encode_instr (Const (encode_imval eenv i) (encode_reg eenv r))
               | IMov r1 r2        => encode_instr (Mov (encode_reg eenv r1) (encode_reg eenv r2))
               | IBinOp o r1 r2 r3 => encode_instr (Binop (encode_binop eenv o) (encode_reg eenv r1)
                                                          (encode_reg eenv r2) (encode_reg eenv r3))
               | ILoad r1 r2       => encode_instr (Load (encode_reg eenv r1) (encode_reg eenv r2))
               | IStore r1 r2      => encode_instr (Store (encode_reg eenv r1) (encode_reg eenv r2))
               | IAlloc _ _        => word.as_word 0 (* Invariant: should not be present *)
               | IBnz r l          => encode_instr (Bnz (encode_reg eenv r)
                                                        (word.as_word (solve_label eenv l)))
               | IJump r           => encode_instr (Jump (encode_reg eenv r))
               | IJal l            => encode_instr (Jal (word.as_word (solve_label eenv l)))
               | IHalt             => encode_instr (Halt mt)
               end
             | inl i => match i with
                        | Linearize.SJalAlloc => encode_instr (Jal (swcast alloc_addr))
                        | Linearize.SSyscallSetArg1 r => encode_instr (Mov (encode_reg eenv r) syscall_arg1)
                        | Linearize.SSyscallSetArg3 r => encode_instr (Mov (encode_reg eenv r) syscall_arg3)
                        | Linearize.SSyscallGetArg3 r => encode_instr (Mov syscall_arg3 (encode_reg eenv r))
                        | Linearize.SSyscallGetRet  r => encode_instr (Mov syscall_ret (encode_reg eenv r))
                        end
             end ;
     taga := snd x |}.


Definition encode_code (eenv : encoder_env) (code : Linearize.code) : memory :=
  let f : nat -> mword mt := word.as_word in
  Tmp.mapk f (fmap_of_seq (map (encode_instr eenv) code)).

Definition alloc_buffers (eenv : encoder_env) (bufs : Linearize.bufs) : memory :=
  let f (x : nat * nat * nat) : mword mt :=
      match x with (c, b, o) => word.as_word (concretize_pointer eenv (c, b, Z.of_nat o)) end
  in Tmp.mapk f (mapm (encode_memval eenv) bufs).

Definition encode (prog : Linearize.prog) : {fmap mword mt -> matom}:=
  (* Solve labels *)
  let labels : seq int := (* TL TODO: int is an ugly hack to get an eqType for free;      *)
                          (*          switch to eqTypes for Intermediate.instr eventually *)
      map (fun x => match fst x with inr (ILabel l) => Posz l | _ => Negz 1 end)
          (Linearize.procedures prog) in
  let solve (l : label) : int := index (Posz l) labels in
  (* Concretize pointers *)
  let base_adress c b :=
      length (Linearize.procedures prog) + 1 +
      length (filter (fun x => match x with (c', b', _) => (c' < c) || ((c' == c) && (b' < b)) end)
                     (* TL TODO codomm doesn't typecheck... *)
                     (* Invariant: Linearize.buffers is "continuous" *)
                     (unzip1 (Linearize.buffers prog)))
  in
  let concretize := (fun p => match p with
                              | (c, b, o) =>
                                (* TL TODO: I have add notation issues, hence intZmod.addz... *)
                                intZmod.addz (encode_int o) (base_adress c b)
                              end)
  in
  let eenv := {| solve_label := solve ;
                 concretize_pointer := concretize |}
  in unionm (encode_code eenv (Linearize.procedures prog))
            (alloc_buffers eenv (Linearize.buffers prog)).
