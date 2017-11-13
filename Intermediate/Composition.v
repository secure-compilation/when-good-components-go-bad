Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.
Require Import Intermediate.PS.
Require Import Intermediate.Decomposition.

Import GlobalEnv.
Import Intermediate.

Section PS2CS.
  Variable prog: program.

  Hypothesis prog_is_closed:
    closed_program prog.

  Let ctx := PMap.empty Component.interface.
  Let G := init_genv prog.

  Lemma match_initial_states:
    forall ips,
      PS.initial_state prog ctx ips ->
    exists ics,
      CS.initial_state prog ics /\ PS.partial_state ctx ics ips.
  Proof.
    intros ips Hips_init.
    inversion Hips_init; subst.
    exists ics. split; auto.
  Qed.

  Lemma match_final_states:
    forall ips ics,
      PS.partial_state ctx ics ips ->
      PS.final_state prog ctx ips ->
      CS.final_state G ics.
  Proof.
    intros ips ics Hics_partial Hips_final.
    inversion Hips_final; subst.
    (* program has control *)
    - inversion Hics_partial; subst;
        try (PS.simplify_turn; contradiction).
      inversion H0; subst; try (PS.simplify_turn; contradiction).
      inversion H11; subst; try (PS.simplify_turn; contradiction).
      auto.
    (* context has control *)
    (* (contra, context is empty) *)
    - PS.simplify_turn.
      destruct ips.
      + repeat destruct p.
        exfalso.
        eapply PMapFacts.empty_in_iff; eauto.
      + destruct c. destruct p.
        exfalso.
        eapply PMapFacts.empty_in_iff; eauto.
  Qed.

  Lemma lockstep_simulation:
    forall ips t ips',
      PS.step ctx G ips t ips' ->
    forall ics,
      PS.partial_state ctx ics ips ->
    exists ics',
      CS.step G ics t ics' /\ PS.partial_state ctx ics' ips'.
  Proof.
    intros ips t ips' Hstep ics Hics_partial.

    inversion Hics_partial; subst; PS.simplify_turn;
      try (eapply PMapFacts.empty_in_iff in H; inversion H).

    inversion Hstep; subst.

    inversion H2; subst; PS.simplify_turn;
      try contradiction.
    inversion H11; subst.

    assert (CS.state_eq (gps0, mem0, regs, pc) (gps, mem, regs, pc)). {
      constructor; try reflexivity.
      - rewrite (PS.to_partial_stack_with_empty_context gps gps0); auto.
      - rewrite H0 in H10.
        unfold PMap.Equal, PMapExtra.filter in *.
        intros C. specialize (H10 C).
        rewrite PMapExtra.fold_identity in H10.
        rewrite PMapExtra.fold_identity in H10.
        auto.
    }

    destruct (CS.equal_states_step G (gps0, mem0, regs, pc) t ics'
                                   (gps, mem, regs, pc) H4 H1) as [ics'' [Hstep' Heq']].
    eexists ics''.
    split; auto.
    eapply PS.equal_states_partialize; eauto.
  Qed.

  Lemma star_simulation:
    forall ips t ips',
      Star (PS.sem prog ctx) ips t ips' ->
    forall ics,
      PS.partial_state ctx ics ips ->
    exists ics',
      Star (CS.sem prog) ics t ics' /\ PS.partial_state ctx ics' ips'.
  Proof.
    intros ips t ips' Hstar.
    induction Hstar; subst.
    - eexists. split.
      + left.
      + auto.
    - intros ics Hics_partial.
      destruct (lockstep_simulation s1 t1 s2 H ics Hics_partial) as [ics' []].
      destruct (IHHstar ics' H1) as [ics'' []].
      exists ics''. split.
      + eapply star_left; eauto.
      + auto.
  Qed.

  Theorem CS_simulates_PS:
    forward_simulation (PS.sem prog ctx) (CS.sem prog).
  Proof.
    eapply forward_simulation_step.
    - apply match_initial_states.
    - apply match_final_states.
    - apply lockstep_simulation.
  Qed.

  Lemma context_validity:
    forall C CI,
      PMap.MapsTo C CI ctx -> PMap.MapsTo C CI (prog_interface prog).
  Proof.
    intros.
    apply PMapFacts.empty_mapsto_iff in H.
    contradiction.
  Qed.

  Corollary partial_semantics_implies_complete_semantics:
    forall beh,
      program_behaves (PS.sem prog ctx) beh ->
      program_behaves (CS.sem prog) beh.
  Proof.
    intros.

    (* manually prove that PS is going wrong *)
    
    destruct (forward_simulation_behavior_improves CS_simulates_PS H)
      as [beh' [Hbeh []]]; subst; auto.

    destruct H0 as [t []]; subst.

    inversion H; subst.
    - (* program has run *)
      inversion H0; subst.
      eapply program_runs.
      + eauto.
      + inversion H2; subst.
        destruct (star_simulation s t s' H6 ics H3) as [? []].
        econstructor.
        * eauto.
        * unfold nostep in *. intros.
          unfold not. intro.
          destruct (Decomposition.lockstep_simulation prog ctx x t0 s'0 H10 s' H9)
            as [s'' []].
          eapply H7. econstructor; eauto.
        * unfold not. intros.
          apply H8. econstructor; eauto.
          ** PS.simplify_turn. unfold not. intro.
             destruct s'. repeat destruct p. 
             eapply PMapFacts.empty_in_iff in H11; inversion H11.
             destruct c. destruct p.
             eapply PMapFacts.empty_in_iff in H11; inversion H11.
    - (* program went wrong immediately *)
      eapply program_goes_initially_wrong.
      intros. unfold not. intro.
      specialize (H2 (PS.partialize s ctx)).
      apply H2. econstructor.
      + apply PS.partialize_correct.
        reflexivity.
      + auto.
  Qed.
End PS2CS.

Section PartialComposition.
  Variable prog1 prog2: program.

  Hypothesis same_main:
    prog_main prog1 = prog_main prog2.

  Hypothesis disjointness:
    PMapExtra.Disjoint (prog_interface prog1) (prog_interface prog2).

  (* at some point we will have to use the fact that the link gives us a good program *)
  (*
  Hypothesis closedness:
    closed_program (program_link prog1 prog2 (fst (prog_main prog1)) (snd (prog_main prog1))).
*)

  Let prog := program_link prog1 prog2 (fst (prog_main prog1)) (snd (prog_main prog1)).
  Let empty_ctx := PMap.empty Component.interface.
  Let G := init_genv prog.

  Definition multi_state : Type := PS.state * PS.state.

  Inductive multi_initial_state: multi_state -> Prop :=
  | multi_initial_state_intro: forall ics ips1 ips2,
      PS.partial_state (prog_interface prog2) ics ips1 ->
      PS.partial_state (prog_interface prog1) ics ips2 ->
      PS.mergeable_states ips1 ips2 ->
      CS.initial_state prog ics ->
      multi_initial_state (ips1, ips2).

  Inductive multi_final_state : multi_state -> Prop :=
  | multi_final_state_intro: forall ics ips1 ips2,
      PS.partial_state (prog_interface prog2) ics ips1 ->
      PS.partial_state (prog_interface prog1) ics ips2 ->
      PS.mergeable_states ips1 ips2 ->
      CS.final_state G ics ->
      multi_final_state (ips1, ips2).

  Inductive multi_step (G: global_env)
    : multi_state -> trace -> multi_state -> Prop :=
  | mstep: forall ips1 t ips1' ips2 ips2',
      PS.step (prog_interface prog2) G ips1 t ips1' ->
      PS.step (prog_interface prog1) G ips2 t ips2' ->
      PS.mergeable_states ips1 ips2 ->
      multi_step G (ips1, ips2) t (ips1', ips2').

  Definition multisem :=
    @Semantics_gen multi_state global_env
                   multi_step multi_initial_state multi_final_state G.

  Inductive multi_match : multi_state -> PS.state -> Prop :=
  | mmatch_first: forall ips1 ips2,
      PS.is_program_component ips1 (prog_interface prog2) ->
      PS.is_context_component ips2 (prog_interface prog1) ->
      PS.mergeable_states ips1 ips2 ->
      multi_match (ips1, ips2) (PS.merge_partial_states ips1 ips2)
  | mmatch_second: forall ips1 ips2,
      PS.is_context_component ips1 (prog_interface prog2) ->
      PS.is_program_component ips2 (prog_interface prog1) ->
      PS.mergeable_states ips1 ips2 ->
      multi_match (ips1, ips2) (PS.merge_partial_states ips1 ips2).

  (* if ics is a partial state of ips1 and ips2 in, respectively, ctx1 and ctx2,
     it means that it is also a partial state of the merge of ips1 and ips2 in
     the empty context *)
  Lemma merged_state_preserves_partiality:
    forall ips1 ips2 ics,
      PS.partial_state (prog_interface prog2) ics ips1 ->
      PS.partial_state (prog_interface prog1) ics ips2 ->
      PS.partial_state empty_ctx ics (PS.merge_partial_states ips1 ips2).
  Proof.
  Admitted.

  Lemma partial_state_weakening:
    forall ips1 ips2 ics,
      PS.partial_state (prog_interface prog2) ics ips1 ->
      PS.partial_state empty_ctx ics (PS.merge_partial_states ips1 ips2).
  Proof.
  Admitted.

  (* after the merge, the context will never execute *)
  Lemma merged_state_always_executes_the_program:
    forall ips1 ips2,
      PS.mergeable_states ips1 ips2 ->
      PS.is_program_component (PS.merge_partial_states ips1 ips2) empty_ctx.
  Proof.
  Admitted.

  Lemma multi_match_initial_states:
    forall ms,
      multi_initial_state ms ->
    exists ips,
      PS.initial_state prog empty_ctx ips /\ multi_match ms ips.
  Proof.
    intros ms Hms_init.
    inversion Hms_init; subst.
    exists (PS.merge_partial_states ips1 ips2). split.
    - econstructor; eauto.
      + eapply merged_state_preserves_partiality; eauto.
    - (* case analysis how who has control *)
      CS.unfold_state.
      destruct (PMap.mem (Pointer.component pc) (prog_interface prog2)) eqn:Hcontrol;
        [ apply PMapFacts.mem_in_iff in Hcontrol |
          apply PMapFacts.not_mem_in_iff in Hcontrol ].
      + apply mmatch_second; auto.
        * inversion H; subst; inversion H; subst; PS.simplify_turn;
            try contradiction; auto.
        * inversion H0; subst; inversion H; subst; PS.simplify_turn; auto.
          inversion H; subst; inversion H0; subst; PS.simplify_turn; auto.
          exfalso.
          apply (disjointness (Pointer.component pc)). split; auto.
      + apply mmatch_first; auto.
        * inversion H; subst; inversion H; subst; PS.simplify_turn;
            try contradiction; auto.
        * inversion H0; subst; inversion H; subst; PS.simplify_turn; auto.
          inversion H; subst; inversion H0; subst; PS.simplify_turn; auto.
          (* Pointer.component pc isn't in ctx1, nor it is in ctx2, that should be
             impossible *)
          (* notice that we know Pointer.component pc to be equal to (fst (prog_main p)) *)
          destruct H2 as [? [? [? [Hpc []]]]].
          (*
          destruct closedness as [Hclosed_interface Hmain_existence].
          destruct Hmain_existence as [mainC_procs []].
          simpl in *.*)
          admit.
  Admitted.

  Lemma multi_match_final_states:
    forall ms ips,
      multi_match ms ips ->
      multi_final_state ms ->
      PS.final_state prog empty_ctx ips.
  Proof.
    intros ms ips Hmmatch Hms_final.
    inversion Hms_final; subst.
    inversion Hmmatch; subst.
    - eapply PS.final_state_program; eauto.
      + apply merged_state_always_executes_the_program; auto.
      + eapply merged_state_preserves_partiality; eauto.
    - eapply PS.final_state_program; eauto.
      + apply merged_state_always_executes_the_program; auto.
      + eapply merged_state_preserves_partiality; eauto.
  Qed.

  Lemma threeway_simulation:
    forall ms t ms',
      multi_step G ms t ms' ->
    forall ips,
      multi_match ms ips ->
    exists ips',
      PS.step empty_ctx G ips t ips' /\ multi_match ms' ips'.
  Proof.
    intros ms t ms' Hstep.
    intros ips Hmatch.

    inversion Hstep; subst.

    exists (PS.merge_partial_states ips1' ips2'). split.
    - inversion H; subst.
      inversion Hmatch; subst;
        econstructor; eauto; apply partial_state_weakening; auto.
    - (* case analysis how who has control *)
  Admitted.

  Theorem prog_simulates_prog1_and_prog2:
    forward_simulation multisem (PS.sem prog (PMap.empty Component.interface)).
  Proof.
    eapply forward_simulation_step.
    - apply multi_match_initial_states.
    - apply multi_match_final_states.
    - apply threeway_simulation.
  Qed.

  Corollary partial_programs_composition:
    forall beh,
      program_behaves (PS.sem prog1 (prog_interface prog2)) beh ->
      program_behaves (PS.sem prog2 (prog_interface prog1)) beh ->
      program_behaves (PS.sem prog empty_ctx) beh.
  Proof.
    (* this should be provable, but it might be tricky *)
  Admitted.
End PartialComposition.

Section Composition.
  Variable p c: program.

  Let mainC := fst (prog_main p).
  Let mainP := snd (prog_main p).

  Hypothesis same_main:
    prog_main p = prog_main c.

  Hypothesis disjointness:
    PMapExtra.Disjoint (prog_interface p) (prog_interface c).

  Hypothesis closedness:
    closed_program (program_link p c mainC mainP).

  Theorem composition:
    forall beh,
      program_behaves (PS.sem p (prog_interface c)) beh ->
      program_behaves (PS.sem c (prog_interface p)) beh ->
      program_behaves (CS.sem (program_link p c mainC mainP)) beh.
  Proof.
    intros beh Hbeh1 Hbeh2.
    destruct closedness.
    eapply partial_semantics_implies_complete_semantics.
    apply partial_programs_composition; auto.
  Qed.
End Composition.