Require Import Common.Definitions.
Require Import CompCert.Events.
Require Import CompCert.Behaviors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Finite prefixes and behaviors. *)

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

Definition trace_finpref_prefix (t : trace) (m : finpref_behavior) : Prop :=
  match m with
  | FTerminates t' | FGoes_wrong t' | FTbc t' => trace_prefix t t'
  end.

Definition finpref_trace_prefix (m : finpref_behavior) (t : trace) : Prop :=
  match m with
  | FTerminates t' | FGoes_wrong t' => False
  | FTbc t' => trace_prefix t' t
  end.

(* Properties of prefixes. *)

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
    prefix m1 b ->
    behavior_prefix m2 b ->
    (finpref_trace_prefix m1 m2 \/ trace_finpref_prefix m2 m1).
Proof.
(* RB: TODO: New prefix model.
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
*) Admitted.


Lemma trace_behavior_prefix_trans : forall m1 m2 b,
    finpref_trace_prefix m1 m2 ->
    behavior_prefix m2 b ->
    prefix m1 b.
Proof.
  unfold finpref_trace_prefix, behavior_prefix, prefix.
  intros f m b Hf [b' Hb'].
  subst b.
  destruct f as [| | f].
  - inversion Hf.
  - inversion Hf.
  - unfold trace_prefix in Hf. destruct Hf as [t Ht]. subst m.
    exists (behavior_app t b'). now rewrite <- behavior_app_assoc.
Qed.

Lemma trace_behavior_prefix_trans' : forall m1 m2 b,
  trace_finpref_prefix m1 m2 ->
  prefix m2 b ->
  behavior_prefix m1 b.
Proof.
  unfold trace_finpref_prefix, prefix, behavior_prefix.
  intros t f b Hf Hfb.
  destruct f as [t1 | t1 | t1];
    destruct Hf as [t2 Ht2]; subst t1.
  - destruct b as [t3 | t3 | t3 | t3]; try (inversion Hfb; fail).
    + subst t3. exists (Terminates t2). reflexivity.
  - destruct b as [t3 | t3 | t3 | t3]; try (inversion Hfb; fail).
    + subst t3. exists (Goes_wrong t2). reflexivity.
  - destruct Hfb as [b1 Hb1]. subst b.
    exists (behavior_app t2 b1). now rewrite <- behavior_app_assoc.
Qed.

Lemma behavior_prefix_goes_wrong_trans : forall t1 t2 b,
  behavior_prefix t1 (Goes_wrong t2) ->
  behavior_prefix t2 b ->
  behavior_prefix t1 b.
Proof.
  unfold behavior_prefix.
  intros t1 t2 b [b1 Hprefix1] [b2 ?]; subst b.
  unfold behavior_app in Hprefix1.
  destruct b1; try (inversion Hprefix1).
  - subst t2. exists (behavior_app t b2). now rewrite <- behavior_app_assoc.
Qed.

Lemma behavior_prefix_improves_trans' : forall t b m,
  behavior_prefix m t ->
  behavior_improves t b ->
  behavior_prefix m b.
Proof.
  unfold behavior_prefix, behavior_improves.
  intros b1 b2 t1 [b3 Happb1] [Heqb1 | [t2 [Hwrongb1 [b4 Happb2]]]].
  - subst. eauto.
  - subst.
    unfold behavior_app in Hwrongb1. destruct b3; try (inversion Hwrongb1; fail).
    + inversion Hwrongb1 as [Heqt2].
      exists (behavior_app t b4). now rewrite <- behavior_app_assoc.
Qed.
