Require Import Common.Definitions.

From CoqUtils Require Import hseq word.
From extructures Require Import fmap.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Symbolic Types.
Export Symbolic.
Require MicroPolicies.Merged.
Require Import MicroPolicies.Utils MicroPolicies.LRC Intermediate.Machine.
Require Import  MicroPolicies.Int32.
Require Import CompCert.Events.


Require Import Source.Language S2I.Compiler.
Require Export Extraction.Definitions.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DoNotation.


Context {mt : machine_types} {ops : machine_ops mt} {sregs : syscall_regs mt}.

Definition step_eval_mp := (@Exec.stepf mt ops sym_lrc Merged.table_lrc).
Definition step_eval_me := (@Exec.stepf mt ops Merged.sym_lrc_merged Merged.table).
Definition step_mp := (@Symbolic.step mt ops sym_lrc Merged.table_lrc).
Definition step_me := (@Symbolic.step mt ops Merged.sym_lrc_merged Merged.table).

Notation state := (state sym_lrc).

Definition id (s:state) : @Symbolic.state mt Merged.sym_lrc_merged :=
  Symbolic.State Merged.sym_lrc_merged (Symbolic.mem s) (Symbolic.regs s) (Symbolic.pc s) (Symbolic.internal s) (Symbolic.comp_num s).

Inductive trace_prod : state -> state -> trace -> Type :=
| trace_refl : forall s, trace_prod s s nil
| trace_step_nil : forall s1 s2 s3 t,
    step_mp s2 s3 None ->
    trace_prod s1 s2 t ->
    trace_prod s1 s3 t
| trace_step_ev : forall s1 s2 s3 t ev,
    step_mp s2 s3 (Some ev) ->
    trace_prod s1 s2 t ->
    trace_prod s1 s3 (ev :: t).

Definition undefined_behavior s : Prop :=
  exists out, (step_eval_mp s = Some out) /\ (step_eval_me (id s) = None).

Definition undefined_behavior_in_P c s : Prop :=
  exists v,
  (undefined_behavior s) /\ (mem s (vala (pc s)) = Some v) /\ (color (taga v) = c).

Fixpoint trace_prod_satisfy {s s' t} (tp : trace_prod s s' t) P : Prop :=
  match tp with
  | trace_refl s => P s
  | trace_step_nil _ _ s3 _ _ tp'
  | trace_step_ev  _ _ s3 _ _ _ tp' => (P s3) /\ (trace_prod_satisfy tp' P)
  end.
