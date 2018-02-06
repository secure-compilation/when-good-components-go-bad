Require Import Common.Definitions.
Require Import CompCert.Events.
Require Import CompCert.Behaviors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma help : forall m1 m2 T,
    trace_prefix m1 T -> trace_prefix m2 T ->
    (trace_prefix m1 m2 \/ trace_prefix m2 m1).
Proof.
  intros m1. induction m1 as [| e m1]; intros m2 T [x1 H1] [x2 H2].
  - left. now exists m2.
  - assert (foo : (exists s, m2 = e :: s) \/ m2 = []).
   { destruct m2. right. reflexivity. subst T. inversion H2.
     left. now exists m2. }
    destruct foo as [[s k0] | k1].
     + subst m2. subst T. inversion H2. specialize (IHm1 s (m1 ** x1)).
       assert (use1 : trace_prefix m1 (m1 ** x1)) by now exists x1.
       assert (use2 : trace_prefix s (m1 ** x1)) by (rewrite H0; now exists x2).
       destruct (IHm1 use1 use2) as [K | K]. clear IHm1.
       left. destruct K as [m K]. exists m. simpl. now rewrite K.
     + right. destruct K as [m K]. exists m. simpl. now rewrite K.
     + right. rewrite k1. now exists (e :: m1).
Qed.

Lemma help_inf : forall m1 m2 T,
    traceinf_prefix m1 T -> traceinf_prefix m2 T ->
    (trace_prefix m1 m2 \/ trace_prefix m2 m1).
Proof.
   intros m1. induction m1 as [| e m1]; intros m2 T [x1 H1] [x2 H2].
  - left. now exists m2.
  - assert (foo : (exists s, m2 = e :: s) \/ m2 = []).
   { destruct m2. right. reflexivity. subst T. inversion H2.
     left. now exists m2. }
    destruct foo as [[s k0] | k1].
     + subst m2. subst T. inversion H2. specialize (IHm1 s (m1 *** x1)).
       assert (use1 : traceinf_prefix m1 (m1 *** x1)) by now exists x1.
       assert (use2 : traceinf_prefix s (m1 *** x1)) by (rewrite H0; now exists x2).
       destruct (IHm1 use1 use2) as [K | K]. clear IHm1.
       left. destruct K as [m K]. exists m. simpl. now rewrite K.
     + right. destruct K as [m K]. exists m. simpl. now rewrite K.
     + right. rewrite k1. now exists (e :: m1).
Qed.


(* How to simplify this proof ? *)
Lemma behavior_prefix_comp : forall m1 m2 b,
    behavior_prefix m1 b ->
    behavior_prefix m2 b ->
    (trace_prefix m1 m2 \/ trace_prefix m2 m1).
Proof.
  intros m1 m2 b [beh1 H1] [beh2 H2].
  destruct b.

  destruct beh1; inversion H1;
  destruct beh2; inversion H2;
  inversion H1; inversion H2.
  assert (K1 : trace_prefix m1 t) by now exists t0.
  assert (K2 : trace_prefix m2 t) by now exists t1.
  apply (help K1 K2).

  destruct beh1; inversion H1.
  destruct beh2; inversion H2.
  assert (K1 : trace_prefix m1 t ) by now exists t0.
  assert (K2 : trace_prefix m2 t) by now exists t1.
  apply (help K1 K2).

  destruct beh1; inversion H1.
  destruct beh2; inversion H2.
  assert (K1 : traceinf_prefix m1 t) by now exists t0.
  assert (K2 : traceinf_prefix m2 t) by now exists t1.
  apply (help_inf K1 K2).

  destruct beh1; inversion H1.
  destruct beh2; inversion H2.
  assert (K1 : trace_prefix m1 t) by now exists t0.
  assert (K2 : trace_prefix m2 t) by now exists t1.
  apply (help K1 K2).
Qed.


Lemma trace_behavior_prefix_trans : forall m1 m2 b,
    trace_prefix m1 m2 ->
    behavior_prefix m2 b ->
    behavior_prefix m1 b.
Proof.
  unfold trace_prefix, behavior_prefix.
  intros m1 m2 b [m3 Hm3] [b' Hb].
  subst m2 b.
  exists (behavior_app m3 b').
  now rewrite <- behavior_app_assoc.
Qed.

Lemma behavior_prefix_goes_wrong_trans : forall t b m,
  behavior_prefix t b ->
  behavior_prefix m (Goes_wrong t) ->
  behavior_prefix m b.
Proof.
  unfold behavior_prefix.
  destruct t as [| e t']; intros b m [b1 H1] [b2 H2]; subst b.
  - destruct m; destruct b2; simpl in H2; try discriminate.
    injection H2; intro H. subst. now eauto.
  - destruct m; destruct b2 as [| | | t'']; simpl in *; try discriminate.
    + exists (behavior_app (e :: t') b1). now rewrite behavior_app_E0.
    + injection H2; intros E1 E2; subst e t'.
      exists (behavior_app t'' b1). rewrite <- behavior_app_assoc.
      reflexivity.
Qed.

Lemma behavior_prefix_improves_trans : forall t b m,
    behavior_prefix m t ->
    behavior_improves t b ->
    behavior_prefix m b.
Proof.
  intros t b m H0 H1.
  destruct H1 as  [H1 | [t' [H11 H12]]].
  + subst. assumption.
  + subst. eapply  behavior_prefix_goes_wrong_trans; eassumption.
Qed.

Inductive finpref_behavior : Type :=
  | FTerminates: trace -> finpref_behavior
  | FGoes_wrong: trace -> finpref_behavior
  | FTbc : trace -> finpref_behavior.

Definition prefix (m:finpref_behavior) (b:program_behavior) : Prop :=
  match m, b with
  | FTerminates t1, Terminates t2
  | FGoes_wrong t1, Goes_wrong t2 => t1 = t2
  | FTbc t1, b => behavior_prefix t1 b
  | _, _ => False
  end.
