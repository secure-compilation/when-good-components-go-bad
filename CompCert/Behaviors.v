Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Coqlib.

Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalEpsilon.

Set Implicit Arguments.

Inductive program_behavior: Type :=
  | Terminates: trace -> program_behavior
  | Diverges: trace -> program_behavior
  | Reacts: traceinf -> program_behavior
  | Goes_wrong: trace -> program_behavior.

(** Operations and relations on behaviors *)

Definition not_wrong (beh: program_behavior) : Prop :=
  match beh with
  | Terminates _ => True
  | Diverges _ => True
  | Reacts _ => True
  | Goes_wrong _ => False
  end.

Definition behavior_app (t: trace) (beh: program_behavior): program_behavior :=
  match beh with
  | Terminates t1 => Terminates (t ** t1)
  | Diverges t1 => Diverges (t ** t1)
  | Reacts T => Reacts (t *** T)
  | Goes_wrong t1 => Goes_wrong (t ** t1)
  end.

Lemma behavior_app_assoc:
  forall t1 t2 beh,
  behavior_app (t1 ** t2) beh = behavior_app t1 (behavior_app t2 beh).
Proof.
  intros. destruct beh; simpl; f_equal; traceEq.
Qed.

Lemma behavior_app_E0:
  forall beh, behavior_app E0 beh = beh.
Proof.
  destruct beh; auto.
Qed.

Definition behavior_prefix (t: trace) (beh: program_behavior) : Prop :=
  exists beh', beh = behavior_app t beh'.

Definition behavior_improves (beh1 beh2: program_behavior) : Prop :=
  beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.

Lemma behavior_improves_refl:
  forall beh, behavior_improves beh beh.
Proof.
  intros; red; auto.
Qed.

Lemma behavior_improves_trans:
  forall beh1 beh2 beh3,
  behavior_improves beh1 beh2 -> behavior_improves beh2 beh3 ->
  behavior_improves beh1 beh3.
Proof.
  intros. red. destruct H; destruct H0; subst; auto.
  destruct H as [t1 [EQ1 [beh2' EQ1']]].
  destruct H0 as [t2 [EQ2 [beh3' EQ2']]].
  subst. destruct beh2'; simpl in EQ2; try discriminate. inv EQ2.
  right. exists t1; split; auto. exists (behavior_app t beh3'). apply behavior_app_assoc.
Qed.

Lemma behavior_improves_bot:
  forall beh, behavior_improves (Goes_wrong E0) beh.
Proof.
  intros. right. exists E0; split; auto. exists beh. rewrite behavior_app_E0; auto.
Qed.

Lemma behavior_improves_app:
  forall t beh1 beh2,
  behavior_improves beh1 beh2 ->
  behavior_improves (behavior_app t beh1) (behavior_app t beh2).
Proof.
  intros. red; destruct H. left; congruence.
  destruct H as [t' [A [beh' B]]]. subst.
  right; exists (t ** t'); split; auto. exists beh'. rewrite behavior_app_assoc; auto.
Qed.

(** Associating behaviors to programs. *)

Section PROGRAM_BEHAVIORS.

Variable L: semantics.

Inductive state_behaves (s: state L): program_behavior -> Prop :=
  | state_terminates: forall t s',
      Star L s t s' ->
      final_state L s' ->
      state_behaves s (Terminates t)
  | state_diverges: forall t s',
      Star L s t s' -> Forever_silent L s' ->
      state_behaves s (Diverges t)
  | state_reacts: forall T,
      Forever_reactive L s T ->
      state_behaves s (Reacts T)
  | state_goes_wrong: forall t s',
      Star L s t s' ->
      Nostep L s' ->
      ~final_state L s' ->
      state_behaves s (Goes_wrong t).

Inductive program_behaves: program_behavior -> Prop :=
  | program_runs: forall s beh,
      initial_state L s -> state_behaves s beh ->
      program_behaves beh
  | program_goes_initially_wrong:
      (forall s, ~initial_state L s) ->
      program_behaves (Goes_wrong E0).

Lemma state_behaves_app:
  forall s1 t s2 beh,
  Star L s1 t s2 -> state_behaves s2 beh -> state_behaves s1 (behavior_app t beh).
Proof.
  intros. inv H0; simpl; econstructor; eauto; try (eapply star_trans; eauto).
  eapply star_forever_reactive; eauto.
Qed.

Lemma state_behaves_app_inv:
  single_events L ->
  forall s1 t beh,
    state_behaves s1 (behavior_app t beh) ->
  exists s2, Star L s1 t s2 /\ state_behaves s2 beh.
Proof.
  intros HL s1 t beh H.
  remember (behavior_app t beh) as beh' eqn:E.
  destruct H as [t' s s1_s final_s|t' s s1_s silent|t' reacts|t' s Hstar Hstuck1 Hstuck2].
  - destruct beh as [t''| | |]; simpl in E; try discriminate.
    inv E.
    apply star_app_inv in s1_s; trivial.
    destruct s1_s as [s2 [s1_s2 s2_s]].
    exists s2; split; trivial.
    now econstructor; eauto.
  - destruct beh as [|t''| |]; simpl in E; try discriminate.
    inv E.
    apply star_app_inv in s1_s; trivial.
    destruct s1_s as [s2 [s1_s2 s2_s]].
    exists s2; split; trivial.
    now econstructor; eauto.
  - destruct beh as [| |t''|]; simpl in E; try discriminate.
    inv E.
    apply forever_reactive_app_inv in reacts; trivial.
    destruct reacts as [s2 [Hstar Hforever]].
    exists s2; split; trivial.
    now econstructor.
  - destruct beh as [| | |t'']; simpl in E; try discriminate.
    inv E.
    apply star_app_inv in Hstar; trivial.
    destruct Hstar as [s2 [Hstar1 Hstar2]].
    exists s2; split; trivial.
    now econstructor; eauto.
Qed.

(** * Existence of behaviors *)

Section TRACEINF_REACTS.

Variable s0: state L.

Hypothesis reacts:
  forall s1 t1, Star L s0 t1 s1 ->
  exists s2, exists t2, Star L s1 t2 s2 /\ t2 <> E0.

Lemma reacts':
  forall s1 t1, Star L s0 t1 s1 ->
  { s2 : state L & { t2 : trace | Star L s1 t2 s2 /\ t2 <> E0 } }.
Proof.
  intros.
  destruct (constructive_indefinite_description _ (reacts H)) as [s2 A].
  destruct (constructive_indefinite_description _ A) as [t2 [B C]].
  exists s2; exists t2; auto.
Qed.

CoFixpoint build_traceinf' (s1: state L) (t1: trace) (ST: Star L s0 t1 s1) : traceinf' :=
  match reacts' ST with
  | existT s2 (exist t2 (conj A B)) =>
      Econsinf' t2
                (build_traceinf' (star_trans ST A (refl_equal _)))
                B
  end.

Lemma reacts_forever_reactive_rec:
  forall s1 t1 (ST: Star L s0 t1 s1),
  Forever_reactive L s1 (traceinf_of_traceinf' (build_traceinf' ST)).
Proof.
  cofix COINDHYP; intros.
  rewrite (unroll_traceinf' (build_traceinf' ST)). simpl.
  destruct (reacts' ST) as [s2 [t2 [A B]]].
  rewrite traceinf_traceinf'_app.
  econstructor. eexact A. auto. apply COINDHYP.
Qed.

Lemma reacts_forever_reactive:
  exists T, Forever_reactive L s0 T.
Proof.
  exists (traceinf_of_traceinf' (build_traceinf' (star_refl (step L) (globalenv L) s0))).
  apply reacts_forever_reactive_rec.
Qed.

End TRACEINF_REACTS.

Lemma diverges_forever_silent:
  forall s0,
  (forall s1 t1, Star L s0 t1 s1 -> exists s2, Step L s1 E0 s2) ->
  Forever_silent L s0.
Proof.
  cofix COINDHYP; intros.
  destruct (H s0 E0) as [s1 ST]. constructor.
  econstructor. eexact ST. apply COINDHYP.
  intros. eapply H. eapply star_left; eauto.
Qed.

Lemma state_behaves_exists:
  forall s, exists beh, state_behaves s beh.
Proof.
  intros s0.
  destruct (classic (forall s1 t1, Star L s0 t1 s1 -> exists s2, exists t2, Step L s1 t2 s2)).
(* 1 Divergence (silent or reactive) *)
  destruct (classic (exists s1, exists t1, Star L s0 t1 s1 /\
                       (forall s2 t2, Star L s1 t2 s2 ->
                        exists s3, Step L s2 E0 s3))).
(* 1.1 Silent divergence *)
  destruct H0 as [s1 [t1 [A B]]].
  exists (Diverges t1); econstructor; eauto.
  apply diverges_forever_silent; auto.
(* 1.2 Reactive divergence *)
  destruct (@reacts_forever_reactive s0) as [T FR].
  intros.
  generalize (not_ex_all_not _ _ H0 s1). intro A; clear H0.
  generalize (not_ex_all_not _ _ A t1). intro B; clear A.
  destruct (not_and_or _ _ B). contradiction.
  destruct (not_all_ex_not _ _ H0) as [s2 C]; clear H0.
  destruct (not_all_ex_not _ _ C) as [t2 D]; clear C.
  destruct (imply_to_and _ _ D) as [E F]; clear D.
  destruct (H s2 (t1 ** t2)) as [s3 [t3 G]]. eapply star_trans; eauto.
  exists s3; exists (t2 ** t3); split.
  eapply star_right; eauto.
  red; intros. destruct (app_eq_nil t2 t3 H0). subst. elim F. exists s3; auto.
  exists (Reacts T); econstructor; eauto.
(* 2 Termination (normal or by going wrong) *)
  destruct (not_all_ex_not _ _ H) as [s1 A]; clear H.
  destruct (not_all_ex_not _ _ A) as [t1 B]; clear A.
  destruct (imply_to_and _ _ B) as [C D]; clear B.
  destruct (classic (final_state L s1)) as [FINAL | NOTFINAL].
(* 2.1 Normal termination *)
  exists (Terminates t1); econstructor; eauto.
(* 2.2 Going wrong *)
  exists (Goes_wrong t1); econstructor; eauto. red. intros.
  generalize (not_ex_all_not _ _ D s'); intros.
  generalize (not_ex_all_not _ _ H t); intros.
  auto.
Qed.

Theorem program_behaves_exists:
  exists beh, program_behaves beh.
Proof.
  destruct (classic (exists s, initial_state L s)) as [[s0 INIT] | NOTINIT].
(* 1. Initial state is defined. *)
  destruct (state_behaves_exists s0) as [beh SB].
  exists beh; econstructor; eauto.
(* 2. Initial state is undefined *)
  exists (Goes_wrong E0). apply program_goes_initially_wrong.
  intros. eapply not_ex_all_not; eauto.
Qed.

End PROGRAM_BEHAVIORS.

(** * Forward simulations and program behaviors *)

Section FORWARD_SIMULATIONS.

Context L1 L2 index order match_states (S: fsim_properties L1 L2 index order match_states).

Lemma forward_simulation_state_behaves:
  forall i s1 s2 beh1,
  match_states i s1 s2 -> state_behaves L1 s1 beh1 ->
  exists beh2, state_behaves L2 s2 beh2 /\ behavior_improves beh1 beh2.
Proof.
  intros. inv H0.
- (* termination *)
  exploit simulation_star; eauto. intros [i' [s2' [A B]]].
  exists (Terminates t); split.
  econstructor; eauto. eapply fsim_match_final_states; eauto.
  apply behavior_improves_refl.
- (* silent divergence *)
  exploit simulation_star; eauto. intros [i' [s2' [A B]]].
  exists (Diverges t); split.
  econstructor; eauto. eapply simulation_forever_silent; eauto.
  apply behavior_improves_refl.
- (* reactive divergence *)
  exists (Reacts T); split.
  econstructor. eapply simulation_forever_reactive; eauto.
  apply behavior_improves_refl.
- (* going wrong *)
  exploit simulation_star; eauto. intros [i' [s2' [A B]]].
  destruct (state_behaves_exists L2 s2') as [beh' SB].
  exists (behavior_app t beh'); split.
  eapply state_behaves_app; eauto.
  replace (Goes_wrong t) with (behavior_app t (Goes_wrong E0)).
  apply behavior_improves_app. apply behavior_improves_bot.
  simpl. decEq. traceEq.
Qed.

End FORWARD_SIMULATIONS.

Theorem forward_simulation_behavior_improves:
  forall L1 L2, forward_simulation L1 L2 ->
  forall beh1, program_behaves L1 beh1 ->
  exists beh2, program_behaves L2 beh2 /\ behavior_improves beh1 beh2.
Proof.
  intros L1 L2 FS. destruct FS as [init order match_states S]. intros. inv H.
- (* initial state defined *)
  exploit (fsim_match_initial_states S); eauto. intros [i [s' [INIT MATCH]]].
  exploit forward_simulation_state_behaves; eauto. intros [beh2 [A B]].
  exists beh2; split; auto. econstructor; eauto.
- (* initial state undefined *)
  destruct (classic (exists s', initial_state L2 s')).
  destruct H as [s' INIT].
  destruct (state_behaves_exists L2 s') as [beh' SB].
  exists beh'; split. econstructor; eauto. apply behavior_improves_bot.
  exists (Goes_wrong E0); split.
  apply program_goes_initially_wrong.
  intros; red; intros. elim H; exists s; auto.
  apply behavior_improves_refl.
Qed.

Corollary forward_simulation_same_safe_behavior:
  forall L1 L2, forward_simulation L1 L2 ->
  forall beh,
  program_behaves L1 beh -> not_wrong beh ->
  program_behaves L2 beh.
Proof.
  intros. exploit forward_simulation_behavior_improves; eauto.
  intros [beh' [A B]]. destruct B.
  congruence.
  destruct H1 as [t [C D]]. subst. contradiction.
Qed.

(** * Backward simulations and program behaviors *)

Section BACKWARD_SIMULATIONS.

Context L1 L2 index order match_states (S: bsim_properties L1 L2 index order match_states).

Definition safe_along_behavior (s: state L1) (b: program_behavior) : Prop :=
  forall t1 s' b2, Star L1 s t1 s' -> b = behavior_app t1 b2 ->
     final_state L1 s'
  \/ (exists t2, exists s'', Step L1 s' t2 s'').

Remark safe_along_safe:
  forall s b, safe_along_behavior s b -> safe L1 s.
Proof.
  intros; red; intros. eapply H; eauto. symmetry; apply behavior_app_E0.
Qed.

Remark star_safe_along:
  forall s b t1 s' b2,
  safe_along_behavior s b ->
  Star L1 s t1 s' -> b = behavior_app t1 b2 ->
  safe_along_behavior s' b2.
Proof.
  intros; red; intros. eapply H. eapply star_trans; eauto.
  subst. rewrite behavior_app_assoc. eauto.
Qed.

Remark not_safe_along_behavior:
  forall s b,
  ~ safe_along_behavior s b ->
  exists t, exists s',
     behavior_prefix t b
  /\ Star L1 s t s'
  /\ Nostep L1 s'
  /\ ~(final_state L1 s').
Proof.
  intros.
  destruct (not_all_ex_not _ _ H) as [t1 A]; clear H.
  destruct (not_all_ex_not _ _ A) as [s' B]; clear A.
  destruct (not_all_ex_not _ _ B) as [b2 C]; clear B.
  destruct (imply_to_and _ _ C) as [D E]; clear C.
  destruct (imply_to_and _ _ E) as [F G]; clear E.
  destruct (not_or_and _ _ G) as [P Q]; clear G.
  exists t1; exists s'.
  split. exists b2; auto.
  split. auto.
  split. red; intros; red; intros. elim Q. exists t; exists s'0; auto.
  intros; red; intros. elim P. auto.
Qed.

Lemma backward_simulation_star:
  forall s2 t s2', Star L2 s2 t s2' ->
  forall i s1 b, match_states i s1 s2 -> safe_along_behavior s1 (behavior_app t b) ->
  exists i', exists s1', Star L1 s1 t s1' /\ match_states i' s1' s2'.
Proof.
  induction 1; intros.
  exists i; exists s1; split; auto. apply star_refl.
  exploit (bsim_simulation S); eauto. eapply safe_along_safe; eauto.
  intros [i' [s1' [A B]]].
  assert (Star L1 s0 t1 s1'). intuition. apply plus_star; auto.
  exploit IHstar; eauto. eapply star_safe_along; eauto.
  subst t; apply behavior_app_assoc.
  intros [i'' [s2'' [C D]]].
  exists i''; exists s2''; split; auto. eapply star_trans; eauto.
Qed.

Lemma backward_simulation_forever_silent:
  forall i s1 s2,
  Forever_silent L2 s2 -> match_states i s1 s2 -> safe L1 s1 ->
  Forever_silent L1 s1.
Proof.
  assert (forall i s1 s2,
         Forever_silent L2 s2 -> match_states i s1 s2 -> safe L1 s1 ->
         forever_silent_N (step L1) order (globalenv L1) i s1).
    cofix COINDHYP; intros.
    inv H.  destruct (bsim_simulation S _ _ _ H2 _ H0 H1) as [i' [s2' [A B]]].
    destruct A as [C | [C D]].
    eapply forever_silent_N_plus; eauto. eapply COINDHYP; eauto.
      eapply star_safe; eauto. apply plus_star; auto.
    eapply forever_silent_N_star; eauto. eapply COINDHYP; eauto.
      eapply star_safe; eauto.
  intros. eapply forever_silent_N_forever; eauto. eapply bsim_order_wf; eauto.
Qed.

Lemma backward_simulation_forever_reactive:
  forall i s1 s2 T,
  Forever_reactive L2 s2 T -> match_states i s1 s2 -> safe_along_behavior s1 (Reacts T) ->
  Forever_reactive L1 s1 T.
Proof.
  cofix COINDHYP; intros. inv H.
  destruct (backward_simulation_star H2 (Reacts T0) H0) as [i' [s1' [A B]]]; eauto.
  econstructor; eauto. eapply COINDHYP; eauto. eapply star_safe_along; eauto.
Qed.

Lemma backward_simulation_state_behaves:
  forall i s1 s2 beh2,
  match_states i s1 s2 -> state_behaves L2 s2 beh2 ->
  exists beh1, state_behaves L1 s1 beh1 /\ behavior_improves beh1 beh2.
Proof.
  intros. destruct (classic (safe_along_behavior s1 beh2)).
- (* 1. Safe along *)
  exists beh2; split; [idtac|apply behavior_improves_refl].
  inv H0.
+ (* termination *)
  assert (Terminates t = behavior_app t (Terminates E0)).
    simpl. rewrite E0_right; auto.
  rewrite H0 in H1.
  exploit backward_simulation_star; eauto.
  intros [i' [s1' [A B]]].
  exploit (bsim_match_final_states S); eauto.
    eapply safe_along_safe. eapply star_safe_along; eauto.
  intros [s1'' [C D]].
  econstructor. eapply star_trans; eauto. traceEq. auto.
+ (* silent divergence *)
  assert (Diverges t = behavior_app t (Diverges E0)).
    simpl. rewrite E0_right; auto.
  rewrite H0 in H1.
  exploit backward_simulation_star; eauto.
  intros [i' [s1' [A B]]].
  econstructor. eauto. eapply backward_simulation_forever_silent; eauto.
  eapply safe_along_safe. eapply star_safe_along; eauto.
+ (* reactive divergence *)
  econstructor. eapply backward_simulation_forever_reactive; eauto.
+ (* goes wrong *)
  assert (Goes_wrong t = behavior_app t (Goes_wrong E0)).
    simpl. rewrite E0_right; auto.
  rewrite H0 in H1.
  exploit backward_simulation_star; eauto.
  intros [i' [s1' [A B]]].
  exploit (bsim_progress S); eauto. eapply safe_along_safe. eapply star_safe_along; eauto.
  intros [FIN | [t' [s2' STEP2]]].
  elim (H4 FIN).
  elim (H3 _ _ STEP2).

- (* 2. Not safe along *)
  exploit not_safe_along_behavior; eauto.
  intros [t [s1' [PREF [STEPS [NOSTEP NOFIN]]]]].
  exists (Goes_wrong t); split.
  econstructor; eauto.
  right. exists t; auto.
Qed.

End BACKWARD_SIMULATIONS.

Theorem backward_simulation_behavior_improves:
  forall L1 L2, backward_simulation L1 L2 ->
  forall beh2, program_behaves L2 beh2 ->
  exists beh1, program_behaves L1 beh1 /\ behavior_improves beh1 beh2.
Proof.
  intros L1 L2 S beh2 H. destruct S as [index order match_states S]. inv H.
- (* L2's initial state is defined. *)
  destruct (classic (exists s1, initial_state L1 s1)) as [[s1 INIT] | NOINIT].
+ (* L1's initial state is defined too. *)
  exploit (bsim_match_initial_states S); eauto. intros [i [s1' [INIT1' MATCH]]].
  exploit backward_simulation_state_behaves; eauto. intros [beh1 [A B]].
  exists beh1; split; auto. econstructor; eauto.
+ (* L1 has no initial state *)
  exists (Goes_wrong E0); split.
  apply program_goes_initially_wrong.
  intros; red; intros. elim NOINIT; exists s0; auto.
  apply behavior_improves_bot.
- (* L2 has no initial state *)
  exists (Goes_wrong E0); split.
  apply program_goes_initially_wrong.
  intros; red; intros.
  exploit (bsim_initial_states_exist S); eauto. intros [s2 INIT2].
  elim (H0 s2); auto.
  apply behavior_improves_refl.
Qed.

Corollary backward_simulation_same_safe_behavior:
  forall L1 L2, backward_simulation L1 L2 ->
  (forall beh, program_behaves L1 beh -> not_wrong beh) ->
  (forall beh, program_behaves L2 beh -> program_behaves L1 beh).
Proof.
  intros. exploit backward_simulation_behavior_improves; eauto.
  intros [beh' [A B]]. destruct B.
  congruence.
  destruct H2 as [t [C D]]. subst. elim (H0 (Goes_wrong t)). auto.
Qed.
