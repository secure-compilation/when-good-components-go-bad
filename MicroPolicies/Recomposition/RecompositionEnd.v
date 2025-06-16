Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.SmallstepUB.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From CoqUtils Require Import hseq word.
From extructures Require Import fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Equality.

Require Import MicroPolicies.Utils.
Import DoNotation.
Import Types.

Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.PreservationLemmas.
Require Import MicroPolicies.Recomposition.StepSilentStrong.
Require Import MicroPolicies.Recomposition.StepEventReturn.
Require Import MicroPolicies.Recomposition.StepEventCall.

Module RecEnd (S: RecompositionContext).

  Module Defs := RecompositionDefinitions S.
  Module Pres := Preservation S.
  Include Pres.
  (*** Diagrams ***)


  Lemma initial_memory_domm: forall b,
      domm (@initial_memory mt b) = fset (map word_of_nat (List.seq 0 (size (@initial_memory mt b)))).
  Proof.
    intros.
  Admitted.

  Lemma encode_code_domm: forall cd pc,
      domm (encode_code cd pc) = fset (map word_of_nat (List.seq pc (size cd))).
  Proof.
    intros.
  Admitted.


  Lemma match_initial_states:
  forall s1, Smallstep.initial_state sem s1 ->
  forall s2, Smallstep.initial_state sem' s2 ->
  exists s3 M, Smallstep.initial_state sem'' s3 /\ match_states M s1 s2 s3.
  Proof.
    intros s1 init1 s2 init2.
    unfold Smallstep.initial_state, sem, sem' in init1, init2. simpl in init1. unfold initial_state1, initial_state2 in *.
    remember (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'')) as s3.
    rename Heqs3 into init3.
    exists s3. exists [].
    split; try (simpl; unfold initial_state3; done).
    remember (prog_main p) as main. destruct main; [eapply match_states_left | eapply match_states_right]; try (eapply common_equiv_def || econstructor); simpl.
    - unfold initial_state in init1. simpl in init1. destruct s1. inv init1. simpl. done.
    - unfold initial_state in init2. simpl in init2. destruct s2. inv init2. simpl. done.
    - unfold initial_state in init3. simpl in init3. destruct s3. inv init3. simpl. done.
    - rewrite init3. simpl. econstructor.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - unfold combined_codes. intros. admit.
    - unfold combined_codes. intros. admit.
    - subst. unfold initial_state. simpl. rewrite Hifacep Hifacec. trivial.
    - assert (color_eq: color_of s1 = 0). subst. unfold initial_state, color_of. simpl. trivial.
  Admitted.






  (*** Final Proofs ***)

  Theorem tsim_properties_match_states:
    @tsim_properties sem sem' sem'' (sd_traces det_sem) (sd_traces det_sem') (sd_traces det_sem'')
      (fun s1 s2 s3 => exists M, match_states M s1 s2 s3).
  Proof.
    eapply threeway_simulation_properties.
    - eapply match_initial_states.
    - eapply step_silent_strong1.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Corollary recomposition_blame:
    forall m,
      does_prefix sem   m ->
      does_prefix sem'  m ->
      does_prefix sem'' m.
  Proof.
    setoid_rewrite (does_prefix_equiv det_sem).
    setoid_rewrite (does_prefix_equiv det_sem').
    setoid_rewrite (does_prefix_equiv det_sem'').
    intros m dp_sem dp_sem'.
    pose proof tsim_properties_match_states as props.
    inversion dp_sem; subst; inversion dp_sem'; subst;
      try (match goal with | H : (forall s : Smallstep.state _, ~ Smallstep.initial_state _ s) |- _ =>
                               exfalso; eapply H; simpl; unfold initial_state2; unfold initial_state1; eauto end);
      remember (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'')) as s3;
      try (assert (match_s3: exists M, match_states M s s0 s3) by
          (( match goal with | H : (Smallstep.initial_state sem _), H' : (Smallstep.initial_state sem' _) |- _ =>
                                 rename H into init_sem; rename H' into init_sem' end);
           destruct props as [a]; destruct (a _ _ init_sem init_sem') as [s3' [init match_init]];
           simpl in init; unfold initial_state3 in init;
           rewrite <- init in Heqs3; subst; try done));
      try ((match goal with | H : (Star sem' _ _ _) |- _ => rename H into star end));
      ((destruct (tsimulation_star props H0 star s3 match_s3) as [s3' [star_sem'' ?]]);
       assert (init: Smallstep.initial_state sem'' s3) by done).
    - apply (does_FTbc (init) star_sem'').
    - apply (does_FGoes_wrong (init) star_sem'').
      + admit.
      + admit. (* we should use properties of match_states and final_states here. *)
    - apply (does_FTerminates (init) star_sem'').
      admit. (* we should use properties of match_states and final_states here. *)
  Admitted.

  Corollary recomposition_blame':
    forall m,
      does_prefix sem   (FGoes_wrong m) ->
      does_prefix sem'  (FTbc m) ->
      Common.Blame.undef_in m ip ->
      does_prefix sem'' (FGoes_wrong m).
  Proof.
    setoid_rewrite (does_prefix_equiv det_sem).
    setoid_rewrite (does_prefix_equiv det_sem').
    setoid_rewrite (does_prefix_equiv det_sem'').
    intros m dp_sem dp_sem' undef_m_ip.
    pose proof tsim_properties_match_states as props.
    inversion dp_sem; inversion dp_sem';
      try (match goal with | H : (forall s : Smallstep.state _, ~ Smallstep.initial_state _ s) |- _ =>
                               exfalso; eapply H; simpl; unfold initial_state2; unfold initial_state1; eauto end).
    remember (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'')) as s3.
    assert (match_s3: exists M, match_states M s s0 s3).
    { destruct props as [a]. destruct (a _ _ H0 H5) as [s3' [init match_init]].
      simpl in init. unfold initial_state3 in init.
      rewrite <- init in Heqs3. subst. done. }
    destruct (tsimulation_star props H1 H6 s3 match_s3) as [s3' [star_sem'' ?]].
    econstructor.
    - simpl; unfold initial_state3; eauto.
    - eauto.
    - admit.
    - admit.
  Admitted.

End Recomposition.
