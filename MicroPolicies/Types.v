From mathcomp Require Import
  ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype div order ssrint ssralg intdiv.
From extructures Require Import ord.
From CoqUtils Require Import word.
From HB Require Import structures.

Require Import MicroPolicies.Utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Warning: extending binop here requires to add corresponding ground rules *)
Inductive binop : predArgType :=
| ADD
| SUB
| MUL
| EQ
| LEQ
| LEQU
| AND
| OR
| XOR
| SHRU
| SHL.

Scheme Equality for binop.

Lemma binop_eqP : Equality.axiom binop_beq.
Proof. by do !case; constructor. Qed.

HB.instance Definition _ := hasDecEq.Build binop binop_eqP.

Definition pickle_binop b :=
  match b with
  | ADD  => 0
  | SUB  => 1
  | MUL  => 2
  | EQ   => 3
  | LEQ  => 4
  | LEQU => 5
  | AND  => 6
  | OR   => 7
  | XOR  => 8
  | SHRU => 9
  | SHL  => 10
  end.

Definition unpickle_binop n :=
  match n with
  | 0  => Some ADD
  | 1  => Some SUB
  | 2  => Some MUL
  | 3  => Some EQ
  | 4  => Some LEQ
  | 5  => Some LEQU
  | 6  => Some AND
  | 7  => Some OR
  | 8  => Some XOR
  | 9  => Some SHRU
  | 10 => Some SHL
  | _  => None
  end.

Lemma pickle_binopK : pcancel pickle_binop unpickle_binop.
Proof. by case. Qed.

HB.instance Definition _ := PCanHasChoice pickle_binopK.
HB.instance Definition _ := PCanIsCountable pickle_binopK.

Definition binop_enum := [::
  ADD;
  SUB;
  MUL;
  EQ;
  LEQ;
  LEQU;
  AND;
  OR;
  XOR;
  SHRU;
  SHL
  ].

Lemma binop_enumP : Finite.axiom binop_enum.
Proof. by case. Qed.

HB.instance Definition _ := isFinite.Build binop binop_enumP.

Inductive opcode : predArgType :=
| NOP
| CONST
| MOV
| BINOP of binop
| LOAD
| STORE
| JUMP
| BNZ
| JAL
| JUMPEPC
| ADDRULE
| GETTAG
| PUTTAG
| HALT.

Scheme Equality for opcode.

Lemma opcode_eqP : Equality.axiom opcode_beq.
Proof. by do !case; constructor. Qed.

HB.instance Definition _ := hasDecEq.Build opcode opcode_eqP.

Definition pickle_opcode (o : opcode) : nat :=
  match o with
  | NOP        =>  1
  | CONST      =>  2
  | MOV        =>  3
  | LOAD       =>  4
  | STORE      =>  5
  | JUMP       =>  6
  | BNZ        =>  7
  | JAL        =>  8
  | JUMPEPC    =>  9
  | ADDRULE    => 10
  | GETTAG     => 11
  | PUTTAG     => 12
  | BINOP ADD  => 13
  | BINOP SUB  => 14
  | BINOP MUL  => 15
  | BINOP EQ   => 16
  | BINOP LEQ  => 17
  | BINOP LEQU => 18
  | BINOP AND  => 19
  | BINOP OR   => 20
  | BINOP XOR  => 21
  | BINOP SHRU => 22
  | BINOP SHL  => 23
  | HALT       => 24
  end.

Definition unpickle_opcode (n : nat) : option opcode :=
  match n with
  |  1 => Some NOP
  |  2 => Some CONST
  |  3 => Some MOV
  |  4 => Some LOAD
  |  5 => Some STORE
  |  6 => Some JUMP
  |  7 => Some BNZ
  |  8 => Some JAL
  |  9 => Some JUMPEPC
  | 10 => Some ADDRULE
  | 11 => Some GETTAG
  | 12 => Some PUTTAG
  | 13 => Some (BINOP ADD)
  | 14 => Some (BINOP SUB)
  | 15 => Some (BINOP MUL)
  | 16 => Some (BINOP EQ)
  | 17 => Some (BINOP LEQ)
  | 18 => Some (BINOP LEQU)
  | 19 => Some (BINOP AND)
  | 20 => Some (BINOP OR)
  | 21 => Some (BINOP XOR)
  | 22 => Some (BINOP SHRU)
  | 23 => Some (BINOP SHL)
  | 24 => Some HALT
  | _  => None
  end.

Lemma pickle_opcodeK : pcancel pickle_opcode unpickle_opcode.
Proof. by do !case. Qed.

HB.instance Definition _ := PCanHasChoice pickle_opcodeK.
HB.instance Definition _ := PCanIsCountable pickle_opcodeK.
HB.instance Definition _ := PcanHasOrd pickle_opcodeK.

Definition max_opcode := 24.

Definition opcode_enum :=
  [::
   NOP;
   CONST;
   MOV;
   BINOP ADD;
   BINOP SUB;
   BINOP MUL;
   BINOP EQ;
   BINOP LEQ;
   BINOP LEQU;
   BINOP AND;
   BINOP OR;
   BINOP XOR;
   BINOP SHRU;
   BINOP SHL;
   LOAD;
   STORE;
   JUMP;
   BNZ;
   JAL;
   JUMPEPC;
   ADDRULE;
   GETTAG;
   PUTTAG;
   HALT].

Lemma opcode_enumP : Finite.axiom opcode_enum.
Proof. by do !case. Qed.

HB.instance Definition _ := isFinite.Build opcode opcode_enumP.

Inductive vopcode : predArgType :=
| OP : opcode -> vopcode
(* "Virtual" opcode used for describing handlers for system services *)
| SERVICE.

Coercion OP : opcode >-> vopcode.

Definition vopcode_eq (x1 x2 : vopcode) : bool :=
  match x1, x2 with
  | OP x1, OP x2 => x1 == x2
  | SERVICE, SERVICE => true
  | _, _ => false
  end.

Lemma vopcode_eqP : Equality.axiom vopcode_eq.
Proof.
  move=> [x1|] [x2|] /=; try by constructor.
  by apply/(iffP idP); [move /eqP ->| move=> [->]].
Qed.

HB.instance Definition _ := hasDecEq.Build vopcode vopcode_eqP.

Definition pickle_vopcode (vo : vopcode) : nat :=
  match vo with
  | OP op => pickle op
  | SERVICE => max_opcode + 1
  end.

Definition unpickle_vopcode n :=
  if n == max_opcode + 1 then Some SERVICE
  else omap OP (unpickle n).

Lemma pickle_vopcodeK : pcancel pickle_vopcode unpickle_vopcode.
Proof. by do !case. Qed.

HB.instance Definition _ := PCanHasChoice pickle_vopcodeK.
HB.instance Definition _ := PCanIsCountable pickle_vopcodeK.

Definition vopcode_enum := SERVICE :: [seq OP x | x <- enum opcode].

Record machine_types := {
  word_size : nat;
  word_size_lb : 7 <= word_size;
  reg_field_size : nat;
  imm_size : nat
}.

Definition mword (mt : machine_types) : Type :=
  word (word_size mt).
Arguments mword mt : simpl never.
HB.instance Definition _ mt := Equality.copy (mword mt) (word (word_size mt)).

Definition reg (mt : machine_types) : Type :=
  word (reg_field_size mt).
Arguments reg mt : simpl never.

Definition imm (mt : machine_types) : Type :=
  word (imm_size mt).
Arguments imm mt : simpl never.

Section instr.

Variable mt : machine_types.

Inductive instr : Type :=
| Nop : instr
| Const : imm mt -> reg mt -> instr
| Mov : reg mt -> reg mt -> instr
| Binop : binop -> reg mt -> reg mt -> reg mt -> instr
| Load : reg mt -> reg mt -> instr
| Store : reg mt -> reg mt -> instr
| Jump : reg mt -> instr
| Bnz : reg mt -> imm mt -> instr
| Jal : imm mt -> instr
(* only for the concrete machine: *)
| JumpEpc : instr
| AddRule : instr
| GetTag : reg mt -> reg mt -> instr
| PutTag : reg mt -> reg mt -> reg mt -> instr
| Halt : instr.

Definition instr_eq (i1 i2 : instr) : bool :=
  match i1, i2 with
  | Nop, Nop => true
  | Const x1 y1, Const x2 y2 => eq_op x1 x2 && eq_op y1 y2
  | Mov x1 y1, Mov x2 y2 => eq_op x1 x2 && eq_op y1 y2
  | Binop o1 x1 y1 z1, Binop o2 x2 y2 z2 =>
    eq_op o1 o2 && eq_op x1 x2 && eq_op y1 y2 && eq_op z1 z2
  | Load x1 y1, Load x2 y2 => eq_op x1 x2 && eq_op y1 y2
  | Store x1 y1, Store x2 y2 => eq_op x1 x2 && eq_op y1 y2
  | Jump x1, Jump x2 => eq_op x1 x2
  | Bnz x1 y1, Bnz x2 y2 => eq_op x1 x2 && eq_op y1 y2
  | Jal x1, Jal x2 => eq_op x1 x2
  | JumpEpc, JumpEpc => true
  | AddRule, AddRule => true
  | GetTag x1 y1, GetTag x2 y2 => eq_op x1 x2 && eq_op y1 y2
  | PutTag x1 y1 z1, PutTag x2 y2 z2 =>
    eq_op x1 x2 && eq_op y1 y2 && eq_op z1 z2
  | Halt, Halt => true
  | _, _ => false
  end.

Lemma instr_eqP : Equality.axiom instr_eq.
Proof.
  move => i1 i2.
  case: i1; case: i2 => /= *; try (by constructor);
  repeat match goal with
  | |- context[?x == ?y] =>
    have [->|/eqP ?] := altP (x =P y); simpl; try constructor; try congruence
  end.
Qed.

HB.instance Definition _ := hasDecEq.Build instr instr_eqP.

Definition opcode_of (i : instr) : opcode :=
  match i with
  | Nop => NOP
  | Const _ _ => CONST
  | Mov _ _ => MOV
  | Binop op _ _ _ => BINOP op
  | Load _ _ => LOAD
  | Store _ _ => STORE
  | Jump _ => JUMP
  | Bnz _ _ => BNZ
  | Jal _ => JAL
  | JumpEpc => JUMPEPC
  | AddRule => ADDRULE
  | GetTag _ _ => GETTAG
  | PutTag _ _ _ => PUTTAG
  | Halt => HALT
  end.

End instr.

Class machine_ops (mt : machine_types) := {
  encode_instr : instr mt -> mword mt;
  decode_instr : mword mt -> option (instr mt);

  ra : reg mt;
  rcom : reg mt;
}.

Class machine_ops_spec mt (ops : machine_ops mt) := {

  encodeK : forall i, decode_instr (encode_instr i) = Some i

}.

Section Ops.

Local Open Scope word_scope.

Context {mt : machine_types}
        {op : machine_ops mt}
        {ops : machine_ops_spec op}.

Definition binop_denote (f : binop) : mword mt -> mword mt -> mword mt :=
  match f with
  | ADD => addw
  | SUB => subw
  | MUL => mulw
  | EQ  => fun w1 w2 => as_word (w1 == w2)
  | LEQ => fun w1 w2 => as_word ((int_of_word w1 <= int_of_word w2)%O)
      (* signed comparison via two's-complement [int_of_word]
         (was an unsigned stub; LEQU is the unsigned opcode) *)
  | LEQU => fun w1 w2 => as_word (w1 <= w2)%ord
  | AND => andw
  | OR => orw
  | XOR => xorw
  | SHRU => addw (* FIXME: we don't have shifts right now *)
  | SHL => shlw
  end.

End Ops.

Section Coding.

Section FixK.

Variable k : nat.
Hypothesis k_ge_5 : 5 <= k.

Definition op_of_word (w : word k) : option opcode :=
  unpickle (val w).

Definition word_of_op (o : opcode) : word k :=
  as_word (pickle o).

Lemma word_of_opK : pcancel word_of_op op_of_word.
Proof.
have lb : 2 ^ 5 <= 2 ^ k by rewrite leq_exp2l //.
do !case=> //=;
by rewrite /word_of_op /op_of_word as_wordK //;
apply: leq_ltn_trans lb.
Qed.

End FixK.

Lemma mword_of_opK mt :
  pcancel (@word_of_op (word_size mt)) (@op_of_word (word_size mt)).
Proof.
by apply: word_of_opK; rewrite (leq_trans _ (word_size_lb mt)).
Qed.

Definition mword_of_op_inj mt := pcan_inj (mword_of_opK mt).

End Coding.

Arguments word_of_op {k} _.
Arguments op_of_word {k} _.

Record atom V T := Atom { vala : V; taga : T }.

Arguments vala {V T} _.
Arguments taga {V T} _.

Definition atom_eqb (V T : eqType) : rel (atom V T) :=
  [rel a1 a2 | [&& vala a1 == vala a2 & taga a1 == taga a2] ].

Lemma atom_eqbP V T : Equality.axiom (@atom_eqb V T).
Proof.
  move => [v1 t1] [v2 t2] /=.
  apply (iffP andP); simpl.
  - by move => [/eqP -> /eqP ->].
  - move => [-> ->]. by rewrite !eqxx.
Qed.

HB.instance Definition _ (V T : eqType) := hasDecEq.Build (atom V T) (@atom_eqbP V T).

Notation "x @ t" := (Atom x t) (at level 5, format "x '@' t").

Section SyscallRegs.

Context (mt : machine_types).

Class syscall_regs := {
  syscall_ret  : reg mt;
  syscall_arg1 : reg mt;
  syscall_arg2 : reg mt;
  syscall_arg3 : reg mt
}.

End SyscallRegs.

Arguments syscall_ret  {_ _}.
Arguments syscall_arg1 {_ _}.
Arguments syscall_arg2 {_ _}.
Arguments syscall_arg3 {_ _}.

Ltac current_instr_opcode :=
  match goal with
  | H : decode_instr _ = Some ?instr |- _ =>
    let op := (eval compute in (opcode_of instr)) in
    op
  end.

Ltac failwith m :=
  let op := current_instr_opcode in
  fail 1000 m op.
