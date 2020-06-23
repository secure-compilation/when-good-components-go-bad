Require Import Common.Definitions.
Require Import CompCert.Events.
Require Import CompCert.Behaviors.
From mathcomp Require Import ssreflect seq.

Definition extract_finite_trace {Ev: Type} (beh: program_behavior) : option (trace Ev) :=
  match beh with
  | Terminates t => Some t
  | Diverges t => Some t
  | Reacts T => None
  | Goes_wrong t => Some t
  end.

Definition last_comp {Ev} {evInst : EventClass Ev} (t: trace Ev) :=
  last Component.main [seq next_comp_of_event e | e <- t].

Definition undef_in {Ev} {evInst : EventClass Ev} (t: trace Ev) (iface: Program.interface) :=
  last_comp t \in domm iface.
