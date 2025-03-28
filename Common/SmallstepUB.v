Require Import CompCert.Events.
Require Import CompCert.Coqlib.

Require Import Coq.Relations.Relations.
Require Import Coq.Wellfounded.Wellfounded.

Require Import CompCert.Smallstep.

Set Implicit Arguments.


Section STEP.

Variable genv: Type.
Variable state: Type.

Variable stepS: genv -> state -> trace -> state -> Prop.
Variable stepT: genv -> state -> trace -> state -> Prop.

Variable allowed_UB: state -> Prop.

Variant step_restricted_UB (ge: genv): state -> trace -> state -> Prop :=
  | step_UB_allowed: forall s t s',
      stepT ge s t s' ->
      allowed_UB s ->
      step_restricted_UB ge s t s'
  | step_UB_disallowed: forall s t s',
      stepS ge s t s' ->
      stepT ge s t s' ->
      step_restricted_UB ge s t s'
.

End STEP.

Section SEMANTICS.

  Context {state genvtype: Type}.
  Variable step1: genvtype -> state -> trace -> state -> Prop.
  Variable step2: genvtype -> state -> trace -> state -> Prop.
  Variable initial_state: state -> Prop.
  Variable final_state: state -> Prop.
  Variable globalenv: genvtype.


  Variable allowed_UB: state -> Prop.

  Let L1: semantics :=
    {| Smallstep.state := state;
       Smallstep.genvtype := genvtype;
       step := step1;
       Smallstep.initial_state := initial_state;
       Smallstep.final_state := final_state;
       Smallstep.globalenv := globalenv |}.

  Let L2: semantics :=
    {| Smallstep.state := state;
       Smallstep.genvtype := genvtype;
       step := step2;
       Smallstep.initial_state := initial_state;
       Smallstep.final_state := final_state;
       Smallstep.globalenv := globalenv |}.

  Definition L_restricted_UB: semantics :=
    {| Smallstep.state := state;
       Smallstep.genvtype := genvtype;
       step := step_restricted_UB step1 step2 allowed_UB;
       Smallstep.initial_state := initial_state;
       Smallstep.final_state := final_state;
       Smallstep.globalenv := globalenv |}.

  Hypothesis extends_step: forall ge s t s',
      step L1 ge s t s' ->
      step L2 ge s t s'.

End SEMANTICS.




(** * The following code was taken from the following git:
    https://github.com/secure-compilation/SECOMP
    file common/Smallstep.v
*)

(** * Three-way simulations used in recomposition. *)


Require Import Coq.micromega.Lia.

Record tsim_properties (L1 L2 L3: semantics)
                       {single_L1: single_events L1} {single_L2: single_events L2} {single_L3: single_events L3}
                       (* (index: Type) *)
                       (* (order: index -> index -> Prop) *)
                       (match_states: (* index ->  *)state L1 -> state L2 -> state L3 -> Prop) : Prop := {
    (* tsim_order_wf: well_founded order; *)
    tsim_match_initial_states:
      forall s1 s2, initial_state L1 s1 ->
               initial_state L2 s2 ->
      exists s3, initial_state L3 s3 /\ match_states s1 s2 s3;
    (* tsim_match_final_states: *)
    (*   forall i s1 s2 s3 r, *)
    (*   match_states i s1 s2 s3 -> final_state L1 s1 r -> final_state L2 s2 r -> final_state L3 s3 r; *)
    tsim_simulation_simultaneous:
    forall s1 e s1',
      Step L1 s1 (e :: nil) s1' ->
    forall s2 s2', Step L2 s2 (e :: nil) s2' ->
      forall s3, match_states s1 s2 s3 ->
      exists s3',
         (Plus L3 s3 (e :: nil) s3')
         /\ match_states s1' s2' s3';
    tsim_simulation1:
      forall s1 s1', Step L1 s1 E0 s1' ->
      forall s2 s3, match_states s1 s2 s3 ->
      exists s3',
         Star L3 s3 E0 s3'
      /\ match_states s1' s2 s3';
    tsim_simulation2:
      forall s2 s2', Step L2 s2 E0 s2' ->
      forall s1 s3, match_states s1 s2 s3 ->
       exists s3',
         Star L3 s3 E0 s3'
      /\ match_states s1 s2' s3' }
  .

Arguments tsim_properties: clear implicits.

Inductive threeway_simulation (L1 L2 L3: semantics)
  {single_L1: single_events L1} {single_L2: single_events L2} {single_L3: single_events L3} : Prop :=
  Threeway_simulation (match_states: state L1 -> state L2 -> state L3 -> Prop)
                      (props: tsim_properties L1 L2 L3 single_L1 single_L2 single_L3
                                match_states).

Arguments Threeway_simulation {L1 L2 L3 single_L1 single_L2 single_L3 }
  match_states props.
(** ** Three-way simulation of transition sequences *)

Section TSIMULATION_SEQUENCES.

Context L1 L2 L3
  {single_L1: single_events L1} {single_L2: single_events L2} {single_L3: single_events L3}
   match_states
  (S: tsim_properties L1 L2 L3 single_L1 single_L2 single_L3 match_states).

Lemma tsimulation_star:
  forall s1 t s1',
    Star L1 s1 t s1' ->
  forall s2 s2',
    Star L2 s2 t s2' ->
  forall s3, match_states s1 s2 s3 ->
  exists s3', Star L3 s3 t s3' /\ match_states s1' s2' s3'.
Proof.
  induction 1; intros until s2'.
  - intros H; remember E0 as t; revert H Heqt.
    induction 1; intros.
    + exists s3; split; auto. apply star_refl.
    + subst t.
      assert (t1 = E0) by now destruct t1. subst t1.
      assert (t2 = E0) by now destruct t2. subst t2.
      exploit tsim_simulation2; eauto.
      intros [s3' [A B]].
      exploit IHstar; eauto.
      intros [s3'' [C D]].
      eexists; split; auto. eapply star_trans; eauto. eauto.
  - induction 1; intros.
    + assert (t1 = E0) by now destruct t1. subst t1.
      assert (t2 = E0) by now destruct t2. subst t2.
      exploit tsim_simulation1; eauto.
      intros [s3' [A B]].
      exploit IHstar; eauto. eapply star_refl.
      intros [s3'' [C D]].
      exists s3''; split; auto. eapply star_trans; eauto.
    + destruct t1, t0; eauto.
      * simpl in *; subst t2; subst t3.
        exploit tsim_simulation1; eauto.
        intros [s3' [A B]].
        pose proof (tsim_simulation2 S _ _ H2 _ _ B).
        destruct H1 as [s3'' [D E]].
        specialize (IHstar _ _ H3 _ E) as [s3''' [F G]].
        exists s3'''; split; auto. eapply star_trans; eauto. eapply star_trans; eauto.
        traceEq.
      * assert (t0 = nil) by now apply single_L2 in H2; destruct t0; eauto; simpl in H2; lia.
        subst t0; simpl in *; subst t2; subst t.
        exploit tsim_simulation1; eauto.
        intros [s3' [A B]].
        exploit IHstar. eapply star_step; eauto. eauto.
        intros [s3'' [C D]].
        exists s3''; split; auto. eapply star_trans; eauto.
      * assert (t1 = nil) by now apply single_L1 in H; destruct t1; eauto; simpl in H; lia.
        subst t1; simpl in *; subst t3; subst t.
        exploit tsim_simulation2; eauto.
        intros [s3' [A B]].
        exploit IHstar0. reflexivity. eauto.
        intros [s3'' [C D]].
        exists s3''; split; auto. eapply star_trans; eauto.
      * assert (t1 = nil) by now apply single_L1 in H; destruct t1; eauto; simpl in H; lia.
        assert (t0 = nil) by now apply single_L2 in H2; destruct t0; eauto; simpl in H2; lia.
        subst. simpl in H4. inv H4.
        exploit tsim_simulation_simultaneous; eauto.
        intros [s3' [A B]].
        exploit IHstar; eauto.
        intros [s3'' [C D]].
        exists s3''; split; auto. eapply star_trans; eauto. apply plus_star; eauto.
Qed.


End TSIMULATION_SEQUENCES.

Section THREEWAY_SIMU_DIAGRAM.

Variable L1: semantics.
Variable L2: semantics.
Variable L3: semantics.
Context {single_L1: single_events L1}
  {single_L2: single_events L2}
  {single_L3: single_events L3}.

Variable metadata: Type.


Variable common_equivalence: metadata -> state L1 -> state L2 -> state L3 -> Prop.
Variable strong_equivalence1: metadata -> state L1 -> state L3 -> Prop.
Variable strong_equivalence2: metadata -> state L2 -> state L3 -> Prop.
Variable weak_equivalence1: metadata -> state L1 -> state L3 -> Prop.
Variable weak_equivalence2: metadata -> state L2 -> state L3 -> Prop.

Variant match_states: metadata -> state L1 -> state L2 -> state L3 -> Prop :=
  | match_states_left: forall M s1 s2 s3,
      common_equivalence M s1 s2 s3 ->
      strong_equivalence1 M s1 s3 ->
      weak_equivalence2 M s2 s3 ->
      match_states M s1 s2 s3
  | match_states_right: forall M s1 s2 s3,
      common_equivalence M s1 s2 s3 ->
      weak_equivalence1 M s1 s3 ->
      strong_equivalence2 M s2 s3 ->
      match_states M s1 s2 s3.

Hypothesis match_initial_states:
  forall s1, initial_state L1 s1 ->
  forall s2, initial_state L2 s2 ->
  exists s3 M, initial_state L3 s3 /\ match_states M s1 s2 s3.

(* Variable order: (metadata * state L1 * state L2) -> (metadata * state L1 * state L2) -> Prop. *)
(* Hypothesis order_wf: well_founded order. *)


(* The strongly-related states take a silent step at the same time *)
Hypothesis step_silent_strong1:
  forall s1 s1', Step L1 s1 E0 s1' ->
  forall s2 s3 M, strong_equivalence1 M s1 s3 ->
           weak_equivalence2 M s2 s3 ->
      common_equivalence M s1 s2 s3 ->
  exists s3' M', Plus L3 s3 E0 s3' /\ (* Using Plus to ensure the strongly related states take a step *)
           strong_equivalence1 M' s1' s3' /\
           weak_equivalence2 M' s2 s3' /\
              common_equivalence M' s1' s2 s3'.

Hypothesis step_silent_strong2:
  forall s2 s2', Step L2 s2 E0 s2' ->
  forall s1 s3 M, strong_equivalence2 M s2 s3 ->
           weak_equivalence1 M s1 s3 ->
      common_equivalence M s1 s2 s3 ->
  exists s3' M', Plus L3 s3 E0 s3' /\ (* idem *)
           strong_equivalence2 M' s2' s3' /\
           weak_equivalence1 M' s1 s3' /\
      common_equivalence M' s1 s2' s3'.

(* The weakly-related state takes a step, not the strongly-related states *)
Hypothesis step_silent_weak1:
  forall s1 s1', Step L1 s1 E0 s1' ->
  forall s2 s3 M, strong_equivalence2 M s2 s3 ->
           weak_equivalence1 M s1 s3 ->
           common_equivalence M s1 s2 s3 ->
  exists M', strong_equivalence2 M' s2 s3 /\
        weak_equivalence1 M' s1' s3 /\
        common_equivalence M' s1' s2 s3.
        (* order (M', s1', s2) (M, s1, s2). *)

Hypothesis step_silent_weak2:
  forall s2 s2', Step L2 s2 E0 s2' ->
  forall s1 s3 M, strong_equivalence1 M s1 s3 ->
           weak_equivalence2 M s2 s3 ->
           common_equivalence M s1 s2 s3 ->
   exists M', strong_equivalence1 M' s1 s3 /\
           weak_equivalence2 M' s2' s3 /\
           common_equivalence M' s1 s2' s3.

(* NOTE: should we add a lemma about internal steps that generate an event? *)

(* The three states take a step at the same time, generating an event *)
(* NOTE: is this lemma enough or should we enforce that the weak and strong relations
   get swapped? -> i think no, but that's just an intuition that comes from the fact
   we could imagine having two executions where private events are synchronized but
   do not lead to a control swap *)
Hypothesis step_event:
  forall s1 e s1', Step L1 s1 (e :: nil) s1' ->
  forall s2 s2',   Step L2 s2 (e :: nil) s2' ->
  forall s3 M, match_states M s1 s2 s3    ->
  exists s3' M', Plus L3 s3 (e :: nil) s3' /\ (* using Plus here because we know if an event is emitted then we've done at least one step *)
            match_states M' s1' s2' s3'.

Lemma threeway_simulation_diagram:
  @threeway_simulation L1 L2 L3 single_L1 single_L2 single_L3.
Proof.
  eapply Threeway_simulation with
    (match_states := fun s1 s2 s3 => exists M, match_states M s1 s2 s3).
  econstructor; eauto.
  - intros.
    exploit match_initial_states; eauto.
    intros [? [? [? ?]]]. eexists; split; eauto.
  - intros s1 e s1' H s2 s2' H0 s3 [? ?].
    exploit step_event; try now intuition eauto.
    intros [? [? [? ?]]].
    eexists; intuition eauto.
  - intros ? ? step1 ? ? [M H].
    inv H.
    + exploit step_silent_strong1; eauto.
      intros [? [? [? [? [? ?]]]]].
      eexists; split; eauto using plus_star.
      eexists; eauto using match_states_left.
    + exploit step_silent_weak1; eauto.
      intros [? [? [? ?]]].
      eexists; split; eauto using star_refl.
      eexists; eauto using match_states_right.
  - intros ? ? step2 ? ? [M H].
    inv H.
    + exploit step_silent_weak2; eauto.
      intros [? [? [? ?]]].
      eexists; split; eauto using star_refl.
      eexists; eauto using match_states_left.
    + exploit step_silent_strong2; eauto.
      intros [? [? [? [? [? ?]]]]].
      eexists; split; eauto using plus_star.
      eexists; eauto using match_states_right.
Qed.

End THREEWAY_SIMU_DIAGRAM.
