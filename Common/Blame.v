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
           (t: trace) (iface: Program.interface) : Prop :=
  match last_event t with
  | None =>
    (* the trace is empty
       the main component is the only one that we can blame *)
    Component.main \in (domm iface)
  | Some e =>
    (* the last event gives us the component to blame *)
    (who_is_in_control_after e) \in (domm iface)
  end.

Lemma no_last_event_implies_empty_trace:
  forall t,
    last_event t = None -> t = [].
Proof.
  intros t Hlast_event.
  induction t as [|? t' IH].
  - reflexivity.
  - destruct t'; simpl in *.
    + discriminate.
    + specialize (IH Hlast_event).
      discriminate.
Qed.

Lemma last_event_is_in_trace:
  forall t e,
    last_event t = Some e -> In e t.
Proof.
  intros t e H.
  induction t.
  - discriminate.
  - destruct t; simpl in H.
    + inversion H. subst. intuition.
    + apply in_cons. apply IHt. auto.
Qed.