Require Import Common.Definitions.
Require Import CompCert.Events.
Require Import CompCert.Behaviors.

Definition extract_finite_trace (beh: program_behavior) : option trace :=
  match beh with
  | Terminates t => Some t
  | Diverges t => Some t
  | Reacts T => None
  | Goes_wrong t => Some t
  end.

Fixpoint last_event (t: trace) : option event :=
  match t with
  | [] => None
  | [e] => Some e
  | _::t' => last_event t'
  end.

Definition who_is_in_control_after (e: event) : Component.id :=
  match e with
  | ECall _ _ _ C => C
  | ERet _ _ C => C
  end.

Definition undef_in
           (mainComp: Component.id)
           (t: trace) (iface: Program.interface) : Prop :=
  match last_event t with
  | None =>
    (* the trace is empty
       the main component is the only one that we can blame *)
    mainComp \in (domm iface)
  | Some e =>
    (* the last event gives us the component to blame *)
    (who_is_in_control_after e) \in (domm iface)
  end.