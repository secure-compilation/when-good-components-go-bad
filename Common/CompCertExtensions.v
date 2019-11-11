Require Import Common.Definitions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

(* Define a canonical structure on event equality. If needed, richer event types
   can extend the encoding by using nested sums. *)
Definition sum_of_event (e : event) :=
  match e with
  | ERet C v C' => inl (C, v, C')
  | ECall C P v C' => inr (C, P, v, C')
  end.

Lemma sum_of_event_inj : injective sum_of_event.
Proof.
by case=> [????|???] [????|???] //= => [[-> -> -> ->]|[-> -> ->]].
Qed.

Definition event_eqMixin := InjEqMixin sum_of_event_inj.
Canonical event_eqType := Eval hnf in EqType event event_eqMixin.

Definition empty_behavior (beh : program_behavior) :=
  match beh with
  | Terminates t | Diverges t | Goes_wrong t => t == E0
  | Reacts _ => false
  end.

Lemma empty_behaviorPn beh :
  reflect (exists e beh', beh = behavior_app [:: e] beh')
          (~~ empty_behavior beh).
Proof.
case: beh=> [[|e t]|[|e t]|[e t]|[|e t]] /=; constructor;
try by case=> [e [[|||]]].
- eexists e, (Terminates _); rewrite /=; eauto.
- eexists e, (Diverges _); rewrite /=; eauto.
- eexists e, (Reacts _); rewrite /=; eauto.
- eexists e, (Goes_wrong _); rewrite /=; eauto.
Qed.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Smallstep semantics: alternative star. *)

Section CLOSURES.

Variable genv: Type.
Variable state: Type.

Variable step: genv -> state -> trace -> state -> Prop.

Inductive starR (ge: genv): state -> trace -> state -> Prop :=
  | starR_refl: forall s,
      starR ge s E0 s
  | starR_step: forall s1 t1 s2 t2 s3 t,
      starR ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
      starR ge s1 t s3.

Lemma starR_one:
  forall ge s1 t s2, step ge s1 t s2 -> starR ge s1 t s2.
Proof.
  intros. eapply starR_step; eauto. apply starR_refl. traceEq.
Qed.

Lemma starR_trans:
  forall ge s1 t1 s2, starR ge s1 t1 s2 ->
  forall t2 s3 t, starR ge s2 t2 s3 -> t = t1 ** t2 -> starR ge s1 t s3.
Proof.
  intros ge s1 t1 s2 HstarR1 t2 s3 t HstarR2 Ht.
  generalize dependent t.
  generalize dependent t1.
  generalize dependent s1.
  induction HstarR2 as [| s1 t1 s2 t2 s3 t HstarR1 IHHstarR2 Hstep2 Ht].
  - intros s1 t1 HstarR1 t Ht.
    rewrite E0_right in Ht.
    subst.
    assumption.
  - intros s0 t0 HstarR0 t3 Ht3.
    eapply starR_step.
    + apply (IHHstarR2 _ _ HstarR0 _ (erefl (t0 ** t1))).
    + apply Hstep2.
    + subst.
      rewrite Eapp_assoc.
      reflexivity.
Qed.

Lemma star_iff_starR : forall ge s1 t s2, star step ge s1 t s2 <-> starR ge s1 t s2.
Proof.
  split.
  - intros H.
    induction H.
    + apply starR_refl.
    + apply starR_one in H.
      apply (starR_trans H IHstar H1).
  - intros H.
    induction H.
    + apply star_refl.
    + apply star_one in H0.
      apply (star_trans IHstarR H0 H1).
Qed.

Lemma star_E0_ind' ge (P : state -> state -> Prop) :
  (forall s, P s s) ->
  (forall s1 s2 s3, step ge s1 E0 s2 -> star step ge s2 E0 s3 -> P s2 s3 -> P s1 s3) ->
  forall s1 s2, star step ge s1 E0 s2 -> P s1 s2.
Proof.
move=> H0 H1 s1 s2; move e_t: E0 => t Hstar.
elim: s1 t s2 / Hstar e_t => // s1 t1 s2 t2 s3 t Hstep Hstar IH ->.
move=> /(@esym _ _ _)/Eapp_E0_inv [??]; subst t1 t2.
by apply: H1; eauto.
Qed.

End CLOSURES.

Section Inversion.

Variables (L : semantics) (Hsingle : single_events L).

Lemma star_cons_inv s1 e t s2 :
  Star L s1 (e :: t) s2 ->
  exists s1' s2', Star L s1 E0 s1' /\ Step L s1' [e] s2' /\ Star L s2' t s2.
Proof.
rewrite -[e :: t]/([e] ** t).
case/(star_app_inv Hsingle)=> s2'' [Hstar1 Hstar2].
case/star_non_E0_split: Hstar1=> // [s1' [s2' [A [B C]]]].
by exists s1', s2'; do !split=> //; apply: star_trans; eauto.
Qed.

Lemma star_middle1_inv s1 t1 e t2 s2 :
  Star L s1 (t1 ** e :: t2) s2 ->
  exists s1' s2', Star L s1 t1 s1' /\ Step L s1' [e] s2' /\ Star L s2' t2 s2.
Proof.
case/(star_app_inv Hsingle)=> s0 [Hstar0].
case/star_cons_inv=> s1' [s2' [Hstar1 [Hstep2 Hstar3]]].
exists s1', s2'; do !split=> //; apply: star_trans; eauto.
by rewrite E0_right.
Qed.

End Inversion.

(* Finite prefixes and behaviors. *)

Inductive finpref_behavior : Type :=
  | FTerminates: trace -> finpref_behavior
  | FGoes_wrong: trace -> finpref_behavior
  | FTbc : trace -> finpref_behavior.

Definition not_wrong_finpref (m:finpref_behavior) : Prop :=
  match m with
  | FGoes_wrong _ => False
  | _             => True
  end.

Definition prefix (m:finpref_behavior) (b:program_behavior) : Prop :=
  match m, b with
  | FTerminates t1, Terminates t2
  | FGoes_wrong t1, Goes_wrong t2 => t1 = t2
  | FTbc t1, b => behavior_prefix t1 b
  | _, _ => False
  end.

Definition finpref_trace (m : finpref_behavior) : trace :=
  match m with
  | FTerminates t | FGoes_wrong t | FTbc t => t
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

Definition behavior_improves_finpref (b:program_behavior) (m:finpref_behavior) :=
  exists t, b = Goes_wrong t /\ trace_finpref_prefix t m.

(* CH: Introduce a definition for
       does_prefix and use it everywhere where it's
       possible, instead of unfolding it everywhere. *)
Definition does_prefix x m := exists b, program_behaves x b /\ prefix m b.
(* CH: Alternatively could define this in terms of Star and prove the
       predicate above as an alternative characterization. *)

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

Lemma behavior_prefix_comp' : forall m1 m2 b,
    prefix m1 b ->
    behavior_prefix m2 b ->
    (finpref_trace_prefix m1 m2 \/ trace_finpref_prefix m2 m1).
Proof.
  unfold prefix, finpref_trace_prefix, trace_finpref_prefix.
  intros m1 m2 b Hbp1 Hbp2.
  (* Destruct behaviors. *)
  destruct m1 as [m1'|m1'|m1'];
    destruct b as [b'|b'|b'|b'];
    (* Non-matching cases are discarded by a simple inversion. *)
    try (inversion Hbp1; fail);
    (* Matching cases are proved by the lemma on standard behaviors. *)
    try (apply (behavior_prefix_comp Hbp1 Hbp2));
    (* The remaining cases are trivial. *)
    subst m1'; destruct Hbp2 as [b'' Happ]; destruct b''; inversion Happ as [Hb'];
      right; now exists t.
Qed.

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

Lemma behavior_prefix_app_inv : forall t1 t2 b,
  behavior_prefix (t1 ++ t2) b ->
  behavior_prefix t1 b.
Proof.
  intros t1 t2 ? [b ?]; subst.
  exists (behavior_app t2 b).
  rewrite behavior_app_assoc.
  reflexivity.
Qed.

Lemma program_behaves_finpref_exists :
  forall L s t s',
    initial_state L s ->
    Star L s t s' ->
  exists beh,
    program_behaves L beh /\
    prefix (FTbc t) beh.
Proof.
  intros L s t s' Hini HStar.
  destruct (state_behaves_exists L s') as [beh_s' Hbeh_s'].
  pose proof program_runs Hini (state_behaves_app HStar Hbeh_s') as Hbeh.
  eexists. split.
  - exact Hbeh.
  - simpl. exists beh_s'. reflexivity.
Qed.
