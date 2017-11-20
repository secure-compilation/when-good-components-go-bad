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

    eapply CS.equal_states_step in H1.
    - eexists. split. apply H1. apply H3.
    - constructor; try reflexivity.
      + rewrite (PS.to_partial_stack_with_empty_context gps gps0); auto.
      + rewrite H0 in H10.
        unfold PMap.Equal, PMapExtra.filter in *.
        intros C. specialize (H10 C).
        rewrite PMapExtra.fold_identity in H10.
        rewrite PMapExtra.fold_identity in H10.
        auto.
    - reflexivity.
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

(*** experimental ***)

(*
   IDEA:
   - the context simulates the program, we change our point view on the simulation
     whenever the control changes
   - a star in the partial semantics is splitted into a mt_star, that is,
     a sequence of st_star (a star in which the turn remains the same) connected by
     single steps that change control
*)

Inductive same_turn: PS.state -> PS.state -> Prop :=
| same_turn_program: forall prog_st prog_st',
    same_turn (PS.PC prog_st) (PS.PC prog_st')
| same_turn_context: forall ctx_st ctx_st',
    same_turn (PS.CC ctx_st) (PS.CC ctx_st').

(* st_star represents a sequence of events performed by the same actor *)
(* st stands for same turn *)
Inductive st_star (G: global_env) (ctx: Program.interface)
  : PS.state -> trace -> PS.state -> Prop :=
| st_star_refl: forall ips,
    st_star G ctx ips E0 ips
| st_star_step: forall ips t1 ips' t2 ips'' t,
    PS.step ctx G ips t1 ips' ->
    same_turn ips ips' ->
    st_star G ctx ips' t2 ips'' ->
    same_turn ips' ips'' ->
    t = t1 ** t2 ->
    st_star G ctx ips t ips''.

Lemma st_star_same_turn:
  forall G ctx ips t ips',
    st_star G ctx ips t ips' ->
    same_turn ips ips'.
Proof.
  intros G ctx ips t ips' Hst_star.
  induction Hst_star; subst.
  - PS.unfold_states; constructor.
  - repeat PS.unfold_states;
      try constructor;
      match goal with
      | contra: same_turn (PS.CC _) (PS.PC _) |- _ =>
        inversion contra
      | contra: same_turn (PS.PC _) (PS.CC _) |- _ =>
        inversion contra
      end.
Qed.

(* mt_star is a sequence of st_star interleaved by steps that change control *)
(* mt stands for multi turn *)
Inductive mt_star (G: global_env) (ctx: Program.interface)
  : PS.state -> trace -> PS.state -> Prop :=
| mt_star_segment: forall ips t ips',
    st_star G ctx ips t ips' ->
    mt_star G ctx ips t ips'
| mt_star_control_change: forall ips t1 ips' t2 ips'' t3 ips''' t,
    st_star G ctx ips t1 ips' ->
    PS.step ctx G ips' t2 ips'' ->
    ~ same_turn ips' ips'' ->
    mt_star G ctx ips'' t3 ips''' ->
    t = t1 ** t2 ** t3 ->
    mt_star G ctx ips t ips'''.

Theorem star_if_st_star:
  forall G ctx ips t ips',
    st_star G ctx ips t ips' ->
    star (PS.step ctx) G ips t ips'.
Proof.
  intros G ctx ips t ips' Hst_star.
  induction Hst_star; subst.
  - constructor.
  - econstructor.
    + eassumption.
    + eassumption.
    + reflexivity.
Qed.

Theorem star_if_mt_star:
  forall G ctx ips t ips',
    mt_star G ctx ips t ips' ->
    star (PS.step ctx) G ips t ips'.
Proof.
  intros G ctx ips t ips' Hmt_star.
  induction Hmt_star; subst.

  (* st_star *)
  - apply star_if_st_star; auto.

  (* st_star + step that changes control + mt_star *)
  - eapply star_trans.
    + eapply star_right.
      * apply star_if_st_star. eassumption.
      * eassumption.
      * reflexivity.
    + eassumption.
    + apply app_assoc.
Qed.

(* We want to prove that a star is either a sequence of steps without change of control,
   or it can be decomposed in a star without change of control + a step with the change of control +
   another star doing the remaining trace *)
(* how can we prove this? *)
(* classically? *)
Lemma change_of_turn_in_star:
  forall G ctx ips t ips',
    star (PS.step ctx) G ips t ips' ->
  st_star G ctx ips t ips' \/
  (exists ips'' ips''' t1 t2 t3,
     st_star G ctx ips t1 ips'' /\
     PS.step ctx G ips'' t2 ips''' /\
     ~ same_turn ips'' ips''' /\
     star (PS.step ctx) G ips''' t3 ips' /\
     t = t1 ** t2 ** t3).
Proof.
Admitted.

Theorem mt_star_if_star:
  forall G ctx ips t ips',
    star (PS.step ctx) G ips t ips' ->
    mt_star G ctx ips t ips'.
Proof.
  intros G ctx ips t ips' Hstar.

  induction Hstar; subst.

  (* base case, no steps *)
  - apply mt_star_segment.
    apply st_star_refl.

  (* step + star *)
  - PS.unfold_state s1; PS.unfold_state s2.

    (* PC to PC *)
    + destruct (change_of_turn_in_star G ctx (PS.PC (pgps0, pmem0, regs0, pc0)) t2 s3 Hstar)
        as [ | [s2' [s2'' [t2' [t2'' [t2'''
               [Hfirst_st_star [Hstep [Hdiff_turn [Hremaining_star Htrace]]]]]]]]]].
      * apply mt_star_segment.
        eapply st_star_step.
        ** eassumption.
        ** constructor.
        ** eassumption.
        ** eapply st_star_same_turn; eassumption.
        ** reflexivity.
      * eapply mt_star_control_change.
        ** eapply st_star_step.
           *** eassumption.
           *** constructor.
           *** apply Hfirst_st_star.
           *** eapply st_star_same_turn; eassumption.
           *** reflexivity.
        ** apply Hstep.
        ** assumption.
        ** admit.
        ** admit.

    (* PC to CC *)
    + eapply mt_star_control_change.
      * apply st_star_refl.
      * eassumption.
      * intro contra. inversion contra.
      * eassumption.
      * reflexivity.

    (* CC to PC *)
    + eapply mt_star_control_change.
      * apply st_star_refl.
      * eassumption.
      * intro contra. inversion contra.
      * eassumption.
      * reflexivity.

    (* CC to CC *)
    + admit.
Admitted.

Theorem star_mt_star_equivalence:
  forall G ctx ips t ips',
    star (PS.step ctx) G ips t ips' <-> mt_star G ctx ips t ips'.
Proof.
  intros.
  split.
  - apply mt_star_if_star.
  - apply star_if_mt_star.
Qed.

(*** Internal simulation, context simulates program ***)

Module ProgramSem.
Section Semantics.
  Variable prog: program.
  Variable ctx: Program.interface.

  Inductive initial_state : PS.state -> Prop :=
  | initial_state_intro: forall ips,
      PS.is_program_component ips ctx ->
      initial_state ips.

  Inductive final_state : PS.state -> Prop :=
  | final_state_nostep: forall ips,
      PS.is_program_component ips ctx ->
      Nostep (PS.sem prog ctx) ips ->
      final_state ips
  | final_state_step_into_context: forall ips t ips',
      PS.is_program_component ips ctx ->
      PS.is_context_component ips' ctx ->
      Step (PS.sem prog ctx) ips t ips' ->
      final_state ips.

  Definition sem :=
    @Semantics_gen PS.state global_env (PS.step ctx)
                   initial_state final_state (init_genv prog).
End Semantics.
End ProgramSem.

Module ContextSem.
Section Semantics.
  Variable prog: program.
  Variable ctx: Program.interface.

  Inductive initial_state : PS.state -> Prop :=
  | initial_state_intro: forall ips,
      PS.is_context_component ips ctx ->
      initial_state ips.

  Inductive final_state : PS.state -> Prop :=
  | final_state_intro: forall ips,
      PS.is_context_component ips ctx ->
      final_state ips.

  Definition sem :=
    @Semantics_gen PS.state global_env (PS.step ctx)
                   initial_state final_state (init_genv prog).
End Semantics.
End ContextSem.

Module ProgCtxSim.
Section Simulation.
  Variable prog1 prog2: program.

  Hypothesis same_main:
    prog_main prog1 = prog_main prog2.

  Hypothesis disjointness:
    PMapExtra.Disjoint (prog_interface prog1) (prog_interface prog2).

  Lemma match_initial_states:
    forall ips1,
      ProgramSem.initial_state (prog_interface prog2) ips1 ->
    exists ips2,
      ContextSem.initial_state (prog_interface prog1) ips2 /\
      PS.mergeable_states (prog_interface prog1) (prog_interface prog2) ips1 ips2.
  Proof.
  Admitted.

  Lemma match_final_states:
    forall ips1 ips2,
      PS.mergeable_states (prog_interface prog1) (prog_interface prog2) ips1 ips2 ->
      ProgramSem.final_state prog1 (prog_interface prog2) ips1 ->
      ContextSem.final_state (prog_interface prog1) ips2.
  Proof.
  Admitted.

  Lemma lockstep_simulation:
    forall ips1 t ips1',
      Step (ProgramSem.sem prog1 (prog_interface prog2)) ips1 t ips1' ->
    forall ips2,
      PS.mergeable_states (prog_interface prog1) (prog_interface prog2) ips1 ips2 ->
    exists ips2',
      Step (ContextSem.sem prog2 (prog_interface prog1)) ips2 t ips2' /\
      PS.mergeable_states (prog_interface prog1) (prog_interface prog2) ips1' ips2'.
  Proof.
  Admitted.

  Theorem context_simulates_program:
    forward_simulation (ProgramSem.sem prog1 (prog_interface prog2))
                       (ContextSem.sem prog2 (prog_interface prog1)).
  Proof.
    eapply forward_simulation_step.
    - apply match_initial_states.
    - apply match_final_states.
    - apply lockstep_simulation.
  Qed.
End Simulation.
End ProgCtxSim.

Module MultiSem.
Section MultiSemantics.
  Variable prog1 prog2: program.

  Hypothesis same_main:
    prog_main prog1 = prog_main prog2.

  Hypothesis disjointness:
    PMapExtra.Disjoint (prog_interface prog1) (prog_interface prog2).

  Let prog := program_link prog1 prog2 (fst (prog_main prog1)) (snd (prog_main prog1)).
  Let empty_ctx := PMap.empty Component.interface.
  Let G := init_genv prog.

  Definition mstate : Type := PS.state * PS.state.

  Inductive minitial_state : mstate -> Prop :=
  | initial_state_intro: forall ips1 ips2,
      PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1 ips2 ->
      PS.initial_state prog1 (prog_interface prog2) ips1 ->
      PS.initial_state prog2 (prog_interface prog1) ips2 ->
      minitial_state (ips1, ips2).

  Inductive mfinal_state : mstate -> Prop :=
  | final_state_intro: forall ips1 ips2,
      PS.final_state prog1 (prog_interface prog2) ips1 ->
      PS.final_state prog2 (prog_interface prog1) ips2 ->
      mfinal_state (ips1, ips2).

  Inductive mstep (G: global_env)
    : mstate -> trace -> mstate -> Prop :=
  | multi_step: forall ips1 t ips1' ips2 ips2',
      PS.step (prog_interface prog2) G ips1 t ips1' ->
      PS.step (prog_interface prog1) G ips2 t ips2' ->
      mstep G (ips1, ips2) t (ips1', ips2').

  Definition msem :=
    @Semantics_gen mstate global_env
                   mstep minitial_state
                   mfinal_state G.

  Inductive multi_match : mstate -> PS.state -> Prop :=
  | multi_match_intro: forall ips1 ips2,
      PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1 ips2 ->
      multi_match (ips1, ips2) (PS.merge_partial_states ips1 ips2).

  Lemma multi_match_initial_states:
    forall ms,
      minitial_state ms ->
    exists ips,
      PS.initial_state prog empty_ctx ips /\ multi_match ms ips.
  Proof.
    intros ms Hms_init.
    inversion Hms_init; subst.
    exists (PS.merge_partial_states ips1 ips2).
    split.
    - apply PS.initial_state_intro
        with (ics:=PS.unpartialize (PS.merge_partial_states ips1 ips2)).
      + inversion H0; subst. inversion H1; subst.
        inversion H2; subst; inversion H4; subst; PS.simplify_turn.
        * (* contra *)
          inversion H.
        * econstructor.
          ** PS.simplify_turn.
             intro contra. eapply PMapFacts.empty_in_iff; eauto.
          ** simpl. rewrite Memory.filter_identity. reflexivity.
          ** simpl.
             rewrite PS.to_partial_stack_unpartialize_identity.
             *** reflexivity.
             *** apply PS.merged_stack_has_no_holes.
                 inversion H; subst. assumption.
        * econstructor.
          ** PS.simplify_turn.
             intro contra. eapply PMapFacts.empty_in_iff; eauto.
          ** simpl. rewrite Memory.filter_identity. reflexivity.
          ** simpl.
             rewrite PS.to_partial_stack_unpartialize_identity.
             *** reflexivity.
             *** apply PS.merged_stack_has_no_holes.
                 inversion H; subst. assumption.
        * (* contra *)
          inversion H.
      + (* unpartilizing the merge preserves the state information that make
           CS.initial_state true *)
        inversion H0; subst. inversion H1; subst.
        inversion H3; subst. inversion H5; subst.
        inversion H2; subst; inversion H4; subst; PS.simplify_turn.
        * (* contra *)
          inversion H.
        * constructor;
            try reflexivity.
          ** (* prove lemma about init_all with larger program *) admit.
          ** assumption.
          ** (* prove lemma about EntryPoint.get with larger program *) admit.
          ** assumption.
        * constructor;
            try reflexivity.
          ** (* prove lemma about init_all with larger program *) admit.
          ** rewrite H13. simpl.
             rewrite same_main. reflexivity.
          ** (* prove lemma about EntryPoint.get with larger program *) admit.
          ** assumption.
        * (* contra *)
          inversion H.
    - constructor.
      + assumption.
  Admitted.

  Lemma multi_match_final_states:
    forall ms ips,
      multi_match ms ips ->
      mfinal_state ms ->
      PS.final_state prog empty_ctx ips.
  Proof.
    intros ms ips Hmmatch Hms_final.
    inversion Hms_final; subst.
    inversion Hmmatch; subst.
    eapply PS.final_state_program
      with (ics:=PS.unpartialize (PS.merge_partial_states ips1 ips2));
      inversion H4; subst; PS.simplify_turn.
    - intro contra. eapply PMapFacts.empty_in_iff; eauto.
    - intro contra. eapply PMapFacts.empty_in_iff; eauto.
    - constructor.
      + PS.simplify_turn.
        intro contra. eapply PMapFacts.empty_in_iff; eauto.
      + simpl. rewrite Memory.filter_identity. reflexivity.
      + simpl.
        rewrite PS.to_partial_stack_unpartialize_identity.
        * reflexivity.
        * apply PS.merged_stack_has_no_holes.
          inversion H; subst; assumption.
    - constructor.
      + PS.simplify_turn.
        intro contra. eapply PMapFacts.empty_in_iff; eauto.
      + simpl. rewrite Memory.filter_identity. reflexivity.
      + simpl.
        rewrite PS.to_partial_stack_unpartialize_identity.
        * reflexivity.
        * apply PS.merged_stack_has_no_holes.
          inversion H; subst; assumption.
    - inversion H; subst.
      + unfold CS.final_state in H8. CS.unfold_states.
        inversion H7; subst.
        (* execution in a larger program *)
        admit.
      + PS.simplify_turn. contradiction.
    - inversion H0; subst.
      + unfold CS.final_state in H8. CS.unfold_states.
        inversion H7; subst.
        (* execution in a larger program *)
        admit.
      + PS.simplify_turn. contradiction.
  Admitted.

  Lemma lockstep_simulation:
    forall ms t ms',
      mstep G ms t ms' ->
    forall ips,
      multi_match ms ips ->
    exists ips',
      PS.step empty_ctx G ips t ips' /\ multi_match ms' ips'.
  Proof.
    intros ms t ms' Hstep.
    intros ips Hmatch.

    inversion Hmatch; subst.
    inversion Hstep; subst.

    exists (PS.merge_partial_states ips1' ips2'). split.
    - inversion H; subst; simpl.
      inversion H2; subst. inversion H5; subst.
      + eapply PS.partial_step with
            (ics:=PS.unpartialize (PS.PC (PS.merge_stacks pgps1 pgps2,
                                          PS.merge_memories pmem1 pmem2, regs, pc)))
            (ics':=PS.unpartialize (PS.merge_partial_states ips1' ips2')).
        * inversion H8; subst; inversion H11; subst;
            PS.simplify_turn; simpl in *.
          ** (* contra, executing component is outside of prog *)
             admit.
          ** (* program is in the first state *) admit.
          ** (* prgroam is in the second state *) admit.
          ** (* contra, executing component is in both prog1 and prog2 *)
             exfalso. eapply disjointness. split; eauto.
             admit.
        * simpl. constructor; simpl.
          ** PS.simplify_turn.
             intro contra.
             eapply PMapFacts.empty_in_iff; eauto.
          ** symmetry. apply Memory.filter_identity.
          ** rewrite PS.to_partial_stack_unpartialize_identity.
             *** reflexivity.
             *** apply PS.merged_stack_has_no_holes; auto.
        * inversion H8; subst; inversion H11; subst;
            PS.simplify_turn; simpl in *.
          ** (* contra, executing component is outside of prog *)
             admit.
          ** (* program is in the first state *) admit.
          ** (* prgroam is in the second state *) admit.
          ** (* contra, executing component is in both prog1 and prog2 *)
             exfalso. eapply disjointness. split; eauto.
             admit.

      + (* symmetric the previous case *)
        admit.

    - inversion H; subst.
      inversion H2; subst; inversion H5; subst.
      + inversion H8; subst; inversion H11; subst.
         ** admit.
         ** admit.
         ** admit.
         ** admit.
      + admit.
  Admitted.

  Theorem merged_prog_simulates_multisem:
    forward_simulation msem (PS.sem prog (PMap.empty Component.interface)).
  Proof.
    eapply forward_simulation_step.
    - apply multi_match_initial_states.
    - apply multi_match_final_states.
    - apply lockstep_simulation.
  Qed.
End MultiSemantics.
End MultiSem.

Section PartialComposition.
  Variable prog1 prog2: program.

  Hypothesis same_main:
    prog_main prog1 = prog_main prog2.

  Hypothesis disjointness:
    PMapExtra.Disjoint (prog_interface prog1) (prog_interface prog2).

  Let prog := program_link prog1 prog2 (fst (prog_main prog1)) (snd (prog_main prog1)).
  Let empty_ctx := PMap.empty Component.interface.
  Let G := init_genv prog.

  (* with multisem *)

  Lemma threeway_multisem_st_star_simulation:
    forall ips1 ips2 t ips1' ips2',
      PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1 ips2 ->
      st_star G (prog_interface prog2) ips1 t ips1' ->
      st_star G (prog_interface prog1) ips2 t ips2' ->
      star (MultiSem.mstep prog1 prog2) G (ips1, ips2) t (ips1', ips2') /\
      PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1' ips2'.
  Proof.
    intros ips1 ips2 t ips1' ips2'.
    intros Hmergeable Hst_star1 Hst_star2.

    induction Hmergeable; subst.

    (* the programs is in the first state *)
    (*
    - remember (PS.PC (pgps1, pmem1, regs, pc)) as ips1.
      remember (PS.CC (Pointer.component pc, pgps2, pmem2)) as ips2.
      induction Hst_star1; subst.
      + apply star_if_st_star in Hst_star2.
        eapply PS.context_epsilon_star_is_silent in Hst_star2.
        * split.
          ** admit.
          ** admit.
        * econstructor; try reflexivity.

      + discriminate.
     *)
    admit.

    (* the program is in the second state *)
    (* (should be symmetric w.r.t. the first part of the proof) *)
    - admit.
  Admitted.

  Theorem threeway_multisem_mt_star_simulation:
    forall ips1 ips2 t ips1' ips2',
      PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1 ips2 ->
      mt_star G (prog_interface prog2) ips1 t ips1' ->
      mt_star G (prog_interface prog1) ips2 t ips2' ->
      star (MultiSem.mstep prog1 prog2) G (ips1, ips2) t (ips1', ips2') /\
      PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1' ips2'.
  Proof.
    intros ips1 ips2 t ips1' ips2'.
    intros Hmergeable Hmt_star1 Hmt_star2.

    induction Hmergeable; subst.

    (*
    (* the programs is in the first state *)
    - remember (PS.PC (pgps1, pmem1, regs, pc)) as ips.
      induction Hmt_star1; subst.

      (* single segment *)
      + inversion Hmt_star2; subst.

        (* single segment with the same trace *)
        * apply threeway_multisem_st_star_simulation; auto.
          ** constructor; auto.

        (* segment + change of control (PC to CC) + mt_star *)
        (* contradiction, the segment is invalid *)
        * inversion H4.

        (* segment + change of control (CC to PC) + mt_star *)
        * (* this case is impossible:
             we have a segment made by the program with trace (t1 ** t2 ** t3) in
             which there is no change of control.
             we also a step from context to program with trace t2 that happens after
             segment made by the context with trace t1.
             this means that t2 is an event that changes control and we shouldn't be
             able to observe it inside the program segment. *)
          admit.

      (* segment + change of control (PC to CC) + mt_star *)
      + inversion Hmt_star2; subst.
        * (* this case is impossible for the same reason the case above it is impossible.
             t2 is an event that changes control, it cannot appear inside a segment *)
          admit.
        * destruct IHHmt_star1 as [Hstar Hmergeable].
          ** admit.
          ** admit.
          ** admit.
          ** split.
             *** eapply star_step.
                 **** econstructor.
                      ***** admit.
                      ***** admit.
                 **** apply Hstar.
                 **** admit.
             *** auto.
        * (* there are different cases to analyze, there interesting one t0 = t1, t2=t4 *)
          (* can we prove that it is indeed the only case? *)
          admit.

      (* segment + change of control (CC to PC) + mt_star *)
      (* contradiction, the segment is invalid *)
      + inversion H1.

    (* the program is in the second state *)
    (* (should be symmetric w.r.t. the first part of the proof) *)
    - admit.
     *)
  Admitted.

  Corollary threeway_multisem_star:
    forall ips1 ips2 t ips1' ips2',
      PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1 ips2 ->
      star (PS.step (prog_interface prog2)) G ips1 t ips1' ->
      star (PS.step (prog_interface prog1)) G ips2 t ips2' ->
      star (MultiSem.mstep prog1 prog2) G (ips1, ips2) t (ips1', ips2').
  Proof.
    intros ips1 ips2 t ips1' ips2'.
    intros Hmergeable Hstar1 Hstar2.
    apply threeway_multisem_mt_star_simulation.
    - assumption.
    - apply star_mt_star_equivalence; auto.
    - apply star_mt_star_equivalence; auto.
  Qed.

  Corollary partial_programs_composition:
    forall t,
      program_behaves (PS.sem prog1 (prog_interface prog2)) (Terminates t) ->
      program_behaves (PS.sem prog2 (prog_interface prog1)) (Terminates t) ->
      program_behaves (PS.sem prog empty_ctx) (Terminates t).
  Proof.
    intros t Hprog1_beh Hprog2_beh.
    inversion Hprog1_beh; subst. inversion H0; subst.
    inversion Hprog2_beh; subst. inversion H4; subst.

    eapply forward_simulation_same_safe_behavior.
    + apply MultiSem.merged_prog_simulates_multisem; auto.
    + eapply program_runs with (s:=(s,s0)).
      * constructor; auto.
        (* the states are mergeable *)
        admit.
      * eapply state_terminates with (s':=(s',s'0)); auto.
        ** apply threeway_multisem_star.
           *** (* the states are mergeable *) admit.
           *** (* star in a bigger environment *) admit.
           *** (* star in a bigger environment *) admit.
        ** simpl. constructor; auto.
    + simpl. constructor.
  Admitted.

  (* alternative without multisem *)

  Theorem threeway_mt_star_simulation:
    forall ips1 ips2 t ips1' ips2',
      PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1 ips2 ->
      mt_star G (prog_interface prog2) ips1 t ips1' ->
      mt_star G (prog_interface prog1) ips2 t ips2' ->
      mt_star G empty_ctx (PS.merge_partial_states ips1 ips2) t
                          (PS.merge_partial_states ips1' ips2').
  Proof.
  Admitted.

  Theorem threeway_simulation_star:
    forall ips1 ips2 t ips1' ips2',
      PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1 ips2 ->
      star (PS.step (prog_interface prog2)) G ips1 t ips1' ->
      star (PS.step (prog_interface prog1)) G ips2 t ips2' ->
      star (PS.step empty_ctx) G (PS.merge_partial_states ips1 ips2) t
                                 (PS.merge_partial_states ips1' ips2').
  Proof.
    intros ips1 ips2 t ips1' ips2'.
    intros Hmergeable Hstar1 Hstar2.
    apply star_mt_star_equivalence.
    apply threeway_mt_star_simulation.
    - assumption.
    - apply star_mt_star_equivalence; assumption.
    - apply star_mt_star_equivalence; assumption.
  Qed.

  Corollary partial_programs_composition':
    forall t,
      program_behaves (PS.sem prog1 (prog_interface prog2)) (Terminates t) ->
      program_behaves (PS.sem prog2 (prog_interface prog1)) (Terminates t) ->
      program_behaves (PS.sem prog empty_ctx) (Terminates t).
  Proof.
    intros t Hprog1_beh Hprog2_beh.
    inversion Hprog1_beh; subst. inversion H0; subst.
    inversion Hprog2_beh; subst. inversion H4; subst.

    eapply program_runs with (s:=PS.merge_partial_states s s0).
    - admit.
    - eapply state_terminates with (s':=PS.merge_partial_states s' s'0); auto.
      + apply threeway_simulation_star.
        * admit.
        * (* star in a bigger environment *) admit.
        * (* star in a bigger environment *) admit.
      + admit.
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

  Theorem composition_for_termination:
    forall t,
      program_behaves (PS.sem p (prog_interface c)) (Terminates t) ->
      program_behaves (PS.sem c (prog_interface p)) (Terminates t) ->
      program_behaves (CS.sem (program_link p c mainC mainP)) (Terminates t).
  Proof.
    intros t Hbeh1 Hbeh2.
    destruct closedness.
    eapply partial_semantics_implies_complete_semantics; auto.
    apply partial_programs_composition; auto.
  Qed.
End Composition.

(*
(* old stuff and thougths *)

  (* not sure if this is useful, but it makes sense *)
  Lemma step_after_merge_generic:
    forall ips1 ips2,
      PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1 ips2 ->
      (* the program is ips1 *)
      (forall t ips1',
         PS.step (prog_interface prog2) G ips1 t ips1' ->
       exists ips2',
         PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1' ips2' /\
         PS.step (prog_interface prog1) G ips2 t ips2' /\
         PS.step empty_ctx G (PS.merge_partial_states ips1 ips2) t
                             (PS.merge_partial_states ips1' ips2')) \/
      (* the program is ips2 *)
      (forall t ips2',
         PS.step (prog_interface prog1) G ips2 t ips2' ->
       exists ips1',
         PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1' ips2' /\
         PS.step (prog_interface prog2) G ips1 t ips1' /\
         PS.step empty_ctx G (PS.merge_partial_states ips1 ips2) t
                             (PS.merge_partial_states ips1' ips2')).
  Proof.
  Admitted.

  Lemma step_after_merge:
    forall ips1 ips2 t ips1' ips2',
      PS.step (prog_interface prog2) G ips1 t ips1' ->
      PS.step (prog_interface prog1) G ips2 t ips2' ->
      PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1 ips2 ->
      PS.step empty_ctx G (PS.merge_partial_states ips1 ips2) t
                          (PS.merge_partial_states ips1' ips2') /\
      PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1' ips2'.
  Proof.
  Admitted.

  Lemma decompose_visible_trace:
    forall L s s' a t,
      single_events L ->
      Star L s (a::t) s' ->
    exists s1 s2,
      Star L s E0 s1 /\
      Step L s1 [a] s2 /\
      Star L s2 t s'.
  Proof.
  Admitted.

  Lemma simulate_upto_visible_event:
    forall ips1 ips2 a t ips1' ips2',
      PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1 ips2 ->
      Star (PS.sem prog1 (prog_interface prog2)) ips1 (a::t) ips1' ->
      Star (PS.sem prog2 (prog_interface prog1)) ips2 (a::t) ips2' ->
    exists ips1'' ips2'',
      (*Star (PS.sem prog1 (prog_interface prog2)) ips1 [a] ips1'' /\
      Star (PS.sem prog2 (prog_interface prog1)) ips2 [a] ips2'' /\*)
      PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1'' ips2'' /\
      Star (PS.sem prog empty_ctx) (PS.merge_partial_states ips1 ips2) [a]
                                   (PS.merge_partial_states ips1'' ips2'') /\
      Star (PS.sem prog1 (prog_interface prog2)) ips1'' t ips1' /\
      Star (PS.sem prog2 (prog_interface prog1)) ips2'' t ips2'.
  Proof.
  Admitted.

  (* merged states star given two partial star *)
  Lemma star_after_merge:
    forall ips1 ips2 t ips1' ips2',
      PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1 ips2 ->
      Star (PS.sem prog1 (prog_interface prog2)) ips1 t ips1' ->
      Star (PS.sem prog2 (prog_interface prog1)) ips2 t ips2' ->
      PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1' ips2' /\
      Star (PS.sem prog empty_ctx) (PS.merge_partial_states ips1 ips2) t
                                   (PS.merge_partial_states ips1' ips2').
  Proof.
    intros ips1 ips2 t ips1' ips2'.
    intros Hmergeable Hstar1 Hstar2.

    inversion Hmergeable; subst.

    (* program has control in ips1 *)
    - induction Hstar1; subst.
      (* epsilon trace *)
      + admit.
      (* non-empty trace *)
      + admit.

    (* program has control in ips2 *)
    - admit.

  Admitted.

  (*
  Lemma sketch:
    forall ips1 ips2 t ips1' ips2',
      PS.mergeable_states (prog_interface prog2) (prog_interface prog1) ips1 ips2 ->
      Star (PS.sem prog1 (prog_interface prog2)) ips1 t ips1' ->
      Star (PS.sem prog2 (prog_interface prog1)) ips2 t ips2' ->
      Star multisem (ips1, ips2) t (ips1', ips2').
  Proof.
    intros ips1 ips2 t ips1' ips2'.
    intros Hmergeable Hstar1 Hstar2.
    inversion Hmergeable; subst.
    - induction Hstar1; subst.
      + inversion Hstar2; subst.
        * constructor.
        * admit.
      + inversion Hstar2; subst.
        * symmetry in H6. apply Eapp_E0_inv in H6. destruct H6. subst.
          exists s2.
          exists (PS.CC (Pointer.component pc, pgps2, pmem2)).
          apply star_step
           with (t1:=E0) (t2:=E0)
                (s2:=(s2, PS.CC (Pointer.component pc, pgps2, pmem2))).
          ** unfold step. simpl. unfold G.
             apply mstep.
             *** unfold step in H1. simpl in *.
                 (* this is our hypothesis, but with a bigger environment *) admit.
             *** inversion H1; subst. simpl in *.
                 apply PS.partial_step with ics ics'.
                 **** (* this is our hypothesis, but with a bigger environment *) admit.
                 **** do 2 CS.unfold_states.
                      (* this should be true because of partialization *) admit.
                 **** (* this should be true because of partialization *) admit.
          ** econstructor.
          ** reflexivity.
        * (* we show that t1 = t0 because our semantics has single events,
             then we use the inductive hypothesis *)
          inversion H1; subst.
          apply CS.singleton_traces in H7.
          inversion H4; subst.
          apply CS.singleton_traces in H10.
          admit.
    (* - symmetric to the first case *)
  Admitted.
       *)

    (* since we truncate to prefixes, the following cases might not be needed *)

    (*
    (* silent divergence *)
    - inversion H0; subst.
      inversion H2; subst.
      eapply forward_simulation_same_safe_behavior.
      + apply prog_simulates_prog1_and_prog2.
      + eapply program_runs with (s:=(s,s0)).
        * constructor; auto.
        * eapply state_diverges with (s':=(s',s'0)).
          ** (* multisem simulates prog1 and prog2 *) admit.
          ** econstructor; eauto.
             *** admit.
             *** admit.
      + simpl. constructor.

    (* reactive divergence *)
    - inversion H0; subst.
      inversion H2; subst.
      eapply forward_simulation_same_safe_behavior.
      + apply prog_simulates_prog1_and_prog2.
      + eapply program_runs with (s:=(s,s0)).
        * constructor; auto.
        * eapply state_reacts.
          ** (* multisem simulates prog1 and prog2 *) admit.
      + simpl. constructor.

    (* going wrong *)
    - (* manually prove it *) admit.
      *)
  Admitted.

*)