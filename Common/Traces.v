Require Import Lib.Extra.
Require Import CompCert.Events.
Require Import Common.Definitions.
Require Import Common.Linking.

Inductive stack_state := StackState {
  (* The current running component.  *)
  cur_comp : Component.id;

  (* Other running components further down the stack. *)
  callers  : list Component.id
}.

Fixpoint well_bracketed_trace (s: stack_state) (t: trace) : Prop :=
  match t with
  | [] => True
  | e :: t' =>
    cur_comp s = cur_comp_of_event e /\
    match e with
    | ECall C _ _ C' =>
      well_bracketed_trace (StackState C' (C :: callers s)) t'
    | ERet C _ C' =>
      match callers s with
      | [] => False
      | head :: tail =>
        head = C' /\
        well_bracketed_trace (StackState C' tail) t'
      end
    end
  end.

Definition well_formed_event intf (e: event) : Prop :=
  match e with
  | ECall C P _ C' => C <> C' /\ imported_procedure intf C C' P
  | ERet  C _   C' => C <> C'
  end.

Definition well_formed_trace intf (t: trace) : Prop :=
  well_bracketed_trace (StackState Component.main []) t /\
  All (well_formed_event intf) t.
