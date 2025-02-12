Require Import Common.Definitions.

From CoqUtils Require Import hseq word.
From extructures Require Import fmap.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Require Import Types.
Require Import Transitional.
Require Import MicroPolicies.Utils MicroPolicies.LRC MicroPolicies.Symbolic Intermediate.Machine.
Require Import CompCert.Events.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DoNotation.

Variant instr :=
| MrNop : instr
| MrLabel : plabel -> instr
| MrConst : imvalue -> register -> instr
| MrMov : register  -> register -> instr
| MrBinop : binop -> register -> register -> register -> instr
| MrLoad : register -> register -> instr
| MrStore : register -> register -> instr
| MrJump : register -> instr
| MrBnz : register -> plabel -> instr
| MrJal : imvalue -> instr
| MrHalt : instr.

Context {mt : machine_types}
  {ops : machine_ops mt}.


(* Memory model and definition are the same as defined in LRC.v *)
(* TODO : this must be rewritten explicitely as sym_lrc contains transfer *)
(*
Notation state := (@Symbolic.state mt sym_lrc).
Notation State := (@Symbolic.State mt sym_lrc).
 *)

Local Notation word := (mword mt).
Let atom := (atom word).

Local Notation memory := {fmap word -> atom (Symbolic.tag_type lrc_tags Symbolic.M)}.
Local Notation registers := {fmap register -> atom (Symbolic.tag_type lrc_tags Symbolic.R)}.

Record state := State {
  mem : memory;
  regs : registers;
  pc : atom (Symbolic.tag_type lrc_tags Symbolic.P)
}.

Notation instr_rules := LRC.instr_rules.
Notation state_ev := (state * option event)%type.

Notation update := (@Symbolic.update mt).
(*
Inductive update :=
  | RegWrite : register -> word -> update
  | RegRead  : register -> update
  | MemWrite : word -> word -> update
  | MemRead : word -> update
.*)

(*
Definition vovec (op : opcode) : Type := Symbolic.ovec lrc_tags op.
Notation vovec_ev op := ((vovec op) * option event)%type.

Record ivec : Type := IVec {
  op  : opcode;
  tpc : Symbolic.tag_type lrc_tags Symbolic.P;
  ti  : Symbolic.instr_tag op;
  ts  : hseq Symbolic.tag_type (vinputs op);
  tni : option (Symbolic.tag_type Symbolic.M)
}.*)


Definition code := (seq (instr * mem_tag *  Component.id)).


(* TODO: is this sufficiently expressive as a global environment? *)
Definition global_env := NMap nat. (* label -> start of procedure (expressed as offset in code) *)


Definition executing (cde : code) (pc : mword mt) (i : instr) (tg : mem_tag) (c : Component.id) : Prop :=
  let off := Symbolic.convert (word.int_of_word pc) in
  (off >= 0) % Z /\ nth_error cde (Z.to_nat off) = Some (i,tg,c).

Definition next_state_updates (st : state) (op : opcode) (updts : seq update) : option state_ev :=
  None. (*next_state_updates_and_pc st iv updts (vala (pc st)).+1.*)

Inductive step (cde : code) (G : global_env) (st st' : state) (ev : option event) : Prop :=
| step_nop : forall mem reg pc tpc i ti tg c
               (ST   : st = State mem reg pc@tpc)
               (PC   : mem pc = Some i@ti)
               (INST : executing cde pc MrNop tg c), forall
        (NEXT : next_state_updates st NOP [:: ] = Some (st', ev)),    step cde G st st' ev
| step_nop' : forall pc tg c 
               (INST : executing cde pc MrNop tg c)
               (NO_EVENT : ev = None),
    step cde G st st' ev.



(* Definition eval_step (cde : code) (G : global_env) (st : state) : option (event * state) := *)

