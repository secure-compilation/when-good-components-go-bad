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

Require Import Coq.Program.Equality.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import Intermediate.

(*
  P and C are two partial programs whose linking results in a whole program.
  We want to show that P and C do the same terminating behavior in the partial semantics
  iff their linking produces the very same behavior in the complete semantics.

    prog_behaves P[C] (Terminates t) <-> prog_behaves P (Terminates t) /\
                                         prog_behaves C (Terminates t)

  One direction is what we call decomposition (see Decomposition.v), that is, we can
  decompose the execution of a whole program (P[C]) in the complete semantics, in two
  executions of two partial programs (P and C) in the partial semantics. Note that
  currently our decomposition proof doens't cover the case of undefined behavior.
  At the intermediate level, this is not a problem since we are assuming to deal only
  with defined behaviors. If we were to prove the complete preservation of behaviors,
  we would have to introduce some changes that allow the context to go wrong in the
  partial semantics.

  The other direction is what we want to prove here and it guarantess that linking two
  partial programs producing the same terminating trace in the partial semantics,
  results in a whole-program producing such terminating trace in the complete semantics.

  NOTE: in general we would like to have this property for all possible behaviors.
        the terminating case with the exact trace is the simplest case, thus we focus on
        it as a starting point.

  The proof of this theorem relies on the following facts:
  - executing a whole-program in the complete semantics is equivalent to executing it
    in the partial semantics (see PS2CS section + Decomposition.v)
  - context-program simulation in partial semantics
    the context simulates the program in the partial semantics (see ProgCtxSim section).
  - context determinism with same trace in partial semantics
    when the context executes, the partial semantics is deterministic once we fix a given
    trace (e.g. s ->(t) s' /\ s ->(t) s'' => s' = s'')
    note that, in general, the context is non-deterministic (there can be multiple events
    starting from the same state)
    See context_same_trace_determinism in Intermediate/PS.v for more details.
  - star & mt_star equivalence
    a sequence of steps in the partial semantics can be split into a sequence of sequences
    of steps where the turn doesn't change (either program or the context executes for the
    whole sequence) and such single turn sequences are interleaved by single steps that
    change control (e.g. a call from the program to the context)
  - three-way simulation
    if two mergeable states (i.e. one complements the other) do the same step in the
    partial semantics, then their merge does the very same step in the partial semantics
    and the resulting state is equivalent to the merge of the resulting state in which
    the original steps were finishing in

  More formally, given the following facts
    initial_state s1 /\ initial_state s2 /\
    star s1 t s1' /\ star s2 t s2' /\
    final_state s1' /\ final_state s2'
  we want to prove that
    initial_state (merge s1 s2) /\
    star (merge s1 s2) t (merge s1' s2') /\
    final_state (merge s1' s2')

  The proof can be divided into four parts:
  1) showing that s1 and s2 are indeed mergeable
  2) proving that merging initial states produces an initial state
  3) proving that merging states of two stars with the same trace, produces a star with
     such trace
  4) proving that merging final states produces a final state

  Comments on each part:

  (1) consists in showing that
    - one of the two states is controlled by the program, the other by the context
    - th executing component of the context state is the executing component in the
      program state (the component tag in the program counter)
    - stacks are one the complement of the other (should be trivial because the states
      are intial, therefore the stacks are empty)
    - memories are disjoint

  (2) and (4) should be provable by showing that the unpartialization of the merge is an
  initial or, respectively, a final state in the complete semantics. This is a rather
  technical proof in which we have to show that the merge of two mergeable states can be
  unpartialized to a complete state. Then, it is a matter of showing that the information
  which made the original states being initial or final, are actually preserved by the
  merge and, therefore, make the initial of final state predicates hold even after the
  merge.

  (3) is harder and it's what we will concentrate on in these notes.

  In order to prove (3), we need to introduce some definitions:
  + st_star s t s'
    it's a sequence of 0 or more steps in which there are no changes of turn.
    the program or, respectively, the context has always control.
  + mt_star s t s'
    it's a concatenation of st_star
    either we have a single st_star, in which case the sequence might also be empty, or
    we have more than one st_star interleaved by single steps where the turn changes
    effectively happen.
    examples:
    * st_star (program or context)
    * st_star (program) -> control change step -> st_star (context) -> ....
  See Coq code later in the file for more details.

  We also need to prove some facts about these new definitions.
  We need at least the following facts:
  + equivalence beetween star sequences and mt_star sequences
  + a st_star doesn't contain turn changes by construction, hence the trace obtained
    from the concatenation of its single steps cannot contain events that make those
    turn changes happen

  Finally, we need to prove a simulation that allows us to move from two steps in the
  partial semantics to just one step made by the merge of the original stepping states.
  This is what we call a three-way simulation.

  Three-Way Simulation:
    forall s1 s2,
      s1 mergeable with s2 /\             s1' mergeable with s2' /\
      step s1 t s1' /\ step s2 t s2' =>   step (merge s1 s2) t (merge s1' s2')

  Three-Way st_star Simulation:
    st_star s1 t s1' /\ st_star s2 t s2' => star (merge s1 s2) t (mege s1' s2')
  Proof.
    we work on the equivalent st_star sequences
      st_star s1 t s1'
      st_star s2 t s2'
    by mergeability, without loss of generality
      s1 is executing the program, whereas s2 is executing the context
    by induction on the first st_star, we prove that
      star (merge s1 s2) t (merge s1' s2')
    * base case, trivial
        st_star s1 E0 s1
      we prove
        star (merge s1 s2) E0 (merge s1 s2)
    * step case
        step s1 t1 s1'' /\ st_star s1'' t2 s1' /\ t = t1 ** t2
      by context simulation, we can simulate the step and the rest of the star
        step s2 t1 s2'' /\ st_star s2'' t2 s2''' /\ t = t1 ** t2
      by three-way simulation, we can simulate the two steps
        step (merge s1 s2) t1 (merge s1'' s2'')
      by IH, we can simulate the rest of the stars
        star (merge s1'' s2'') t2 (merge s1' s2''')
      recall that we know
        st_star s2 t s2''' /\ st_star s2 t s2'
      since a st_star implies a star
        star s2 t s2''' /\ star s2 t s2'
      by determinism of context with same trace in the partial semantics
        s2''' = s2'
      therefore, we finally have
        step (merge s1 s2) t1 (merge s1'' s2'')
        star (merge s1'' s2'') t2 (merge s1' s2')
      which can be merged into the star we wanted to show
        star (merge s1 s2) (t1 ** t2) (merge s1' s2')

  *** Proof sketch for (3) ***
  We are given two sequences of steps producing the same trace t.
    star s1 t s1'
    star s2 t s2'
  Previously, we showed that s1 is mergeable with s2.
  We want to show that
    star (merge s1 s2) t (merge s1' s2')

  The two stars are equivalent to two multi-turn segmented stars:
    mt_star s1 t s1'
    mt_star s2 t s2'

  We do this in order to simulate segments one by one by using the right simulation.
  The context simulates the program, therefore, each time we have a change of turn, we
  have to invert the roles to continue the simulation.

  Now, we do an induction on the mt_star in which the program has control.
  Suppose, without loss of generality, that such state is s1, then we have two cases.

  - base case
      st_star s1 t s1'
      mt_star s2 t s2'
    by inversion on the second mt_star
    + st_star s2 t s2'
      we prove the star by Three-Way st_star Simulation

    + st_star s2 t1 s2'' /\ step s2'' t2 s2''' /\ mt_star s2''' t3 s2'
      t = t1 ** t2 ** t3
      we know that t is a trace obtained from a sequence of steps without changes of turn.
      This means that t cannot contain t2, this case cannot happen.

  - step case
      st_star s1 t1 s1'' /\ step s1'' t2 s1''' /\ mt_star s1''' t3 s1'
      t = t1 ** t2 ** t3
      mt_star s2 t s2'
    by inversion on the second mt_star
    + st_star s2 t s2'
      we know that t is a trace obtained from a sequence of steps without changes of turn.
      This means that t cannot contain t2, this case cannot happen.
    + st_star s2 t1' s2'' /\ step s2'' t2' s2''' /\ mt_star s2''' t3' s2'
      t = t1' ** t2' ** t3'
      We first show that t1=t1' /\ t2=t2' /\ t3=t3'
      First, notice that the following holds
        t1 ** t2 ** t3 = t1' ** t2' ** t3'
      Case analysis on t1 and t1':
      * t1 < t1'
        this cannot happen, because it would mean that t2 appears in t1'.
        But t1' cannot contain changes of turn
      * t1 = t1'
        But then t2 = t2', since our semantics is single event (at most an event is
        produced during a step) and, consequently, t3 = t3'
      * t1 > t1'
        this cannot happen, because it would mean that t2' appears in t1.
        But t1 cannot contain changes of turn

      We established the following
        st_star s1 t1 s1'' /\ step s1'' t2 s1''' /\ mt_star s1''' t3 s1'
        st_star s2 t1 s2'' /\ step s2'' t2 s2''' /\ mt_star s2''' t3 s2'
        t = t1 ** t2 ** t3
      by Three-Way st_star Simulation
        star (merge s1 s2) t1 (merge s1'' s2'')
      by Three-Way Simulation
        step (merge s1'' s2'') t2 (merge s1''' s2''')
      by IH
        star (merge s1''' s2''') t3 (merge s1' s2')
      by transitivity and the following facts
        star (merge s1 s2) t1 (merge s1'' s2'')
        step (merge s1'' s2'') t2 (merge s1''' s2''')
        star (merge s1''' s2''') t3 (merge s1' s2')
      we obtain
        star (merge s1 s2) (t1 ** t2 ** t3) (merge s1' s2')
      which is what we wanted to show.
*)

Section PS2CS.
  Variable prog: program.

  Hypothesis prog_is_well_formed:
    well_formed_program prog.

  Hypothesis prog_is_closed:
    closed_program prog.

  Lemma match_initial_states:
    forall ips,
      PS.initial_state prog emptym ips ->
    exists ics,
      CS.initial_state prog ics /\ PS.partial_state emptym ics ips.
  Proof.
    intros ips Hips_init.
    inversion Hips_init; subst.
    enough (p' = empty_prog) as Hempty_prog.
    subst. eexists. split; eauto.
    - rewrite linking_empty_program in H2. assumption.
    - apply empty_interface_implies_empty_program.
      + inversion H0; auto.
      + assumption.
  Qed.

  Lemma match_final_states:
    forall ips ics,
      PS.partial_state emptym ics ips ->
      PS.final_state prog emptym ips ->
      CS.final_state (prepare_global_env prog) ics.
  Proof.
    intros ips ics Hics_partial Hips_final.
    inversion Hips_final; subst.
    (* program has control *)
    - inversion Hics_partial; subst;
        try (PS.simplify_turn; contradiction).
      inversion H2; subst.
      PS.simplify_turn.
      enough (p' = empty_prog) as Hempty_prog. subst.
      + rewrite linking_empty_program in H3.
        assumption.
      + apply empty_interface_implies_empty_program.
        * inversion H0; auto.
        * assumption.
    (* context has control *)
    (* (contra, context is empty) *)
    - PS.simplify_turn.
      destruct ips.
      + repeat destruct p.
        exfalso.
        rewrite mem_domm in H. inversion H.
      + destruct c. destruct p.
        exfalso.
        rewrite mem_domm in H. inversion H.
  Qed.

  Lemma lockstep_simulation:
    forall ips t ips',
      PS.step prog emptym (prepare_global_env prog) ips t ips' ->
    forall ics,
      PS.partial_state emptym ics ips ->
    exists ics',
      CS.step (prepare_global_env prog) ics t ics' /\ PS.partial_state emptym ics' ips'.
  Proof.
    intros ips t ips' Hstep ics Hics_partial.

    inversion Hics_partial; subst; PS.simplify_turn;
      try (rewrite mem_domm in H; inversion H; clear H).

    inversion Hstep; subst.

    inversion H2; subst; PS.simplify_turn;
      try contradiction.

    (* show stacks are equal *)
    rewrite domm0 in H11.
    apply PS.to_partial_stack_with_empty_context in H11. subst.

    (* show mem0 = mem *)
    rewrite domm0 in H10. simpl in *.
    do 2 rewrite filterm_identity in H10.
    subst.

    (* use the fact that p' is empty *)
    enough (p' = empty_prog) as Hempty_prog. subst.
    - rewrite linking_empty_program in H1.
      eexists. split; eauto.
    - apply empty_interface_implies_empty_program.
      + inversion H0; auto.
      + assumption.
  Qed.

  Lemma star_simulation:
    forall ips t ips',
      Star (PS.sem prog emptym) ips t ips' ->
    forall ics,
      PS.partial_state emptym ics ips ->
    exists ics',
      Star (CS.sem prog) ics t ics' /\ PS.partial_state emptym ics' ips'.
  Proof.
    intros ips t ips' Hstar.
    induction Hstar; subst.
    - eexists. split.
      + left.
      + auto.
    - intros ics Hics_partial.
      destruct (lockstep_simulation H Hics_partial) as [ics' []].
      destruct (IHHstar ics' H1) as [ics'' []].
      exists ics''. split.
      + eapply star_left; eauto.
      + auto.
  Qed.

  Theorem CS_simulates_PS:
    forward_simulation (PS.sem prog emptym) (CS.sem prog).
  Proof.
    eapply forward_simulation_step.
    - apply match_initial_states.
    - apply match_final_states.
    - apply lockstep_simulation.
  Qed.

  Corollary partial_semantics_implies_complete_semantics:
    forall beh,
      program_behaves (PS.sem prog emptym) beh ->
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
      assert (p' = empty_prog) as Hempty_prog. {
        inversion H4.
        apply empty_interface_implies_empty_program; auto.
      }
      subst.
      eapply program_runs.
      + rewrite linking_empty_program in H6. eauto.
      + inversion H2; subst.
        destruct (star_simulation H8 H5) as [? []].
        econstructor.
        * eauto.
        * unfold nostep in *. intros.
          unfold not. intro.
          rewrite <- (linking_empty_program prog) in H12.
          destruct (Decomposition.lockstep_simulation H4 H12 H11)
            as [s'' []].
          eapply H9. econstructor; eauto.
        * unfold not. intros.
          apply H10. econstructor; eauto.
          ** PS.simplify_turn. unfold not. intro.
             destruct s'. repeat destruct p.
             rewrite mem_domm in H13. inversion H13.
             *** destruct c. destruct p.
                 rewrite mem_domm in H13. inversion H13.
          ** rewrite linking_empty_program. eauto.
    - (* program went wrong immediately *)
      eapply program_goes_initially_wrong.
      intros. unfold not. intro.
      specialize (H2 (PS.partialize s emptym)).
      apply H2.
      apply PS.initial_state_intro with (p':=empty_prog) (ics:=s).
      + reflexivity.
      + apply empty_prog_linkability; auto.
      + apply PS.partialize_correct.
        reflexivity.
      + destruct prog.
        unfold program_link. simpl.
        repeat rewrite unionm0.
        destruct prog_main0; simpl;
        assumption.
  Qed.
End PS2CS.

Inductive same_turn: PS.state -> PS.state -> Prop :=
| same_turn_program: forall prog_st prog_st',
    same_turn (PS.PC prog_st) (PS.PC prog_st')
| same_turn_context: forall ctx_st ctx_st',
    same_turn (PS.CC ctx_st) (PS.CC ctx_st').

(* st_star represents a sequence of events performed by the same actor *)
(* st stands for same turn *)
Inductive st_star (p: program) (ctx: Program.interface) (G: global_env)
  : PS.state -> trace -> PS.state -> Prop :=
| st_star_refl: forall ips,
    st_star p ctx G ips E0 ips
| st_star_step: forall ips t1 ips' t2 ips'' t,
    PS.step p ctx G ips t1 ips' ->
    same_turn ips ips' ->
    st_star p ctx G ips' t2 ips'' ->
    same_turn ips' ips'' -> (* TODO remove? *)
    t = t1 ** t2 ->
    st_star p ctx G ips t ips''.

Lemma st_star_same_turn:
  forall p ctx G ips t ips',
    st_star p ctx G ips t ips' ->
    same_turn ips ips'.
Proof.
  intros p ctx G ips t ips' Hst_star.
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
Inductive mt_star (p: program) (ctx: Program.interface) (G: global_env)
  : PS.state -> trace -> PS.state -> Prop :=
| mt_star_segment: forall ips t ips',
    st_star p ctx G ips t ips' ->
    mt_star p ctx G ips t ips'
| mt_star_control_change: forall ips t1 ips' t2 ips'' t3 ips''' t,
    st_star p ctx G ips t1 ips' ->
    PS.step p ctx G ips' t2 ips'' ->
    ~ same_turn ips' ips'' ->
    mt_star p ctx G ips'' t3 ips''' ->
    t = t1 ** t2 ** t3 ->
    mt_star p ctx G ips t ips'''.

Theorem star_if_st_star:
  forall p ctx G ips t ips',
    st_star p ctx G ips t ips' ->
    star (PS.step p ctx) G ips t ips'.
Proof.
  intros p ctx G ips t ips' Hst_star.
  induction Hst_star; subst.
  - constructor.
  - econstructor.
    + eassumption.
    + eassumption.
    + reflexivity.
Qed.

Theorem star_if_mt_star:
  forall p ctx G ips t ips',
    mt_star p ctx G ips t ips' ->
    star (PS.step p ctx) G ips t ips'.
Proof.
  intros p ctx G ips t ips' Hmt_star.
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
   or it can be decomposed in a star without change of control + a step with the change
   of control + another star doing the remaining trace *)
(* is this enough to prove the equivalence? *)
(* how can we prove this? classically? *)
Lemma change_of_turn_in_star:
  forall p ctx G ips t ips',
    star (PS.step p ctx) G ips t ips' ->
  st_star p ctx G ips t ips' \/
  (exists ips'' ips''' t1 t2 t3,
     st_star p ctx G ips t1 ips'' /\
     PS.step p ctx G ips'' t2 ips''' /\
     ~ same_turn ips'' ips''' /\
     star (PS.step p ctx) G ips''' t3 ips' /\
     t = t1 ** t2 ** t3).
Proof.
Admitted.

Theorem mt_star_if_star:
  forall p ctx G ips t ips',
    star (PS.step p ctx) G ips t ips' ->
    mt_star p ctx G ips t ips'.
Proof.
  intros p ctx G ips t ips' Hstar.

  induction Hstar; subst.

  (* base case, no steps *)
  - apply mt_star_segment.
    apply st_star_refl.

  (* step + star *)
  - PS.unfold_state s1; PS.unfold_state s2.

    (* PC to PC *)
    + destruct (change_of_turn_in_star Hstar)
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
        ** (* the inductive hypothesis is not enough *)
           admit.
        ** rewrite Htrace. apply app_assoc.

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
    + (* it should be almost the same as the PC to PC case *)
      admit.
Admitted.

Theorem star_mt_star_equivalence:
  forall p ctx G ips t ips',
    star (PS.step p ctx) G ips t ips' <-> mt_star p ctx G ips t ips'.
Proof.
  intros. split.
  - apply mt_star_if_star.
  - apply star_if_mt_star.
Qed.

(*
  Program-Context Simulation

  At any moment, we have two states which are mergeable; one of them has the program in
  control, while the other has the context.
  The argument is that the context always simulates the program, therefore, whenever the
  program state makes a step, the context state is able to make a step with the same
  event.

  To formalize this fact, we define two ad-hoc semantics and then prove a forward
  simulation between the two. One semantics represents the program, wheres the other
  represents the context.

  The program semantics is defined such that all those states in which the program has
  control are initial and final states, and a state steps only if the the state in which
  it finishes is still controlled by the program.
  The same is true for the context semantics, but with the roles swapped.
*)

Module ProgramSem.
Section Semantics.
  Variable prog: program.
  Variable ctx: Program.interface.

  Hypothesis valid_program:
    well_formed_program prog.

  Hypothesis merged_interface_is_closed:
    closed_interface (unionm (prog_interface prog) ctx).

  Inductive initial_state : PS.state -> Prop :=
  | initial_state_intro: forall ips,
      PS.is_program_component ips ctx ->
      initial_state ips.

  Inductive final_state : PS.state -> Prop :=
  | final_state_nostep: forall ips,
      PS.is_program_component ips ctx ->
      final_state ips.

  Inductive step (G: global_env): PS.state -> trace -> PS.state -> Prop :=
  | program_step: forall ips t ips',
      PS.is_program_component ips ctx ->
      PS.is_program_component ips' ctx ->
      PS.step prog ctx G ips t ips' ->
      step G ips t ips'.

  Definition sem :=
    @Semantics_gen PS.state global_env step
                   initial_state final_state (prepare_global_env prog).
End Semantics.
End ProgramSem.

Module ContextSem.
Section Semantics.
  Variable prog: program.
  Variable ctx: Program.interface.

  Hypothesis valid_program:
    well_formed_program prog.

  Hypothesis merged_interface_is_closed:
    closed_interface (unionm (prog_interface prog) ctx).

  Inductive initial_state : PS.state -> Prop :=
  | initial_state_intro: forall ips,
      PS.is_context_component ips ctx ->
      initial_state ips.

  Inductive final_state : PS.state -> Prop :=
  | final_state_intro: forall ips,
      PS.is_context_component ips ctx ->
      final_state ips.

  Inductive step (G: global_env): PS.state -> trace -> PS.state -> Prop :=
  | program_step: forall ips t ips',
      PS.is_context_component ips ctx ->
      PS.is_context_component ips' ctx ->
      PS.step prog ctx G ips t ips' ->
      step G ips t ips'.

  Definition sem :=
    @Semantics_gen PS.state global_env step
                   initial_state final_state (prepare_global_env prog).
End Semantics.
End ContextSem.

Module ProgCtxSim.
Section Simulation.
  Variables p c: program.

  Hypothesis linkability:
    linkable_programs p c.

  Lemma match_initial_states:
    forall ips1,
      ProgramSem.initial_state (prog_interface c) ips1 ->
    exists ips2,
      ContextSem.initial_state (prog_interface p) ips2 /\
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2.
  Proof.
  Admitted.

  Lemma match_final_states:
    forall ips1 ips2,
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      ProgramSem.final_state (prog_interface c) ips1 ->
      ContextSem.final_state (prog_interface p) ips2.
  Proof.
  Admitted.

  (* it might be that we just need this lemma and not the previous two *)
  Lemma lockstep_simulation:
    forall ips1 t ips1',
      Step (ProgramSem.sem p (prog_interface c)) ips1 t ips1' ->
    forall ips2,
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
    exists ips2',
      Step (ContextSem.sem c (prog_interface p)) ips2 t ips2' /\
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1' ips2'.
  Proof.
  Admitted.

  Theorem context_simulates_program:
    forward_simulation (ProgramSem.sem p (prog_interface c))
                       (ContextSem.sem c (prog_interface p)).
  Proof.
    eapply forward_simulation_step.
    - apply match_initial_states.
    - apply match_final_states.
    - apply lockstep_simulation.
  Qed.

  Corollary st_star_simulation:
    forall ips1 t ips1',
      st_star p (prog_interface c) (prepare_global_env p) ips1 t ips1' ->
    forall ips2,
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
    exists ips2',
      st_star c (prog_interface p) (prepare_global_env c) ips2 t ips2' /\
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1' ips2'.
  Proof.
  Admitted.
End Simulation.
End ProgCtxSim.

(*
  Three-way Simulation

  The main intuition is that whenever two mergeable states make the same step, then
  the state resulting from their merge makes the same step as well.
*)

Module MultiSem.
Section MultiSemantics.
  Variables p c: program.

  Hypothesis linkability:
    linkable_programs p c.

  Let prog := program_link p c.

  Definition state : Type := PS.state * PS.state.

  Inductive initial_state : state -> Prop :=
  | initial_state_intro: forall ips1 ips2,
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      PS.initial_state p (prog_interface c) ips1 ->
      PS.initial_state c (prog_interface p) ips2 ->
      initial_state (ips1, ips2).

  Inductive final_state : state -> Prop :=
  | final_state_intro: forall ips1 ips2,
      PS.final_state p (prog_interface c) ips1 ->
      PS.final_state c (prog_interface p) ips2 ->
      final_state (ips1, ips2).

  Inductive step (G: global_env)
    : state -> trace -> state -> Prop :=
  | multi_step: forall ips1 t ips1' ips2 ips2',
      PS.step p (prog_interface c) (prepare_global_env p) ips1 t ips1' ->
      PS.step c (prog_interface p) (prepare_global_env c) ips2 t ips2' ->
      step G (ips1, ips2) t (ips1', ips2').

  Definition msem :=
    @Semantics_gen state global_env
                   step initial_state
                   final_state (prepare_global_env prog).

  Inductive multi_match : state -> PS.state -> Prop :=
  | multi_match_intro: forall ips1 ips2,
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      multi_match (ips1, ips2) (PS.merge_partial_states ips1 ips2).

  Lemma multi_match_initial_states:
    forall ms,
      initial_state ms ->
    exists ips,
      PS.initial_state prog emptym ips /\ multi_match ms ips.
  Proof.
    intros ms Hms_init.
    inversion Hms_init; subst.
    exists (PS.merge_partial_states ips1 ips2).
    split.
    - apply PS.initial_state_intro
        with (ics:=PS.unpartialize (PS.merge_partial_states ips1 ips2))
             (p':=empty_prog).
      + reflexivity.
      + apply empty_prog_linkability.
        apply linking_well_formedness; auto.
      + inversion H0; subst. inversion H1; subst.
        inversion H4; subst; inversion H8; subst; PS.simplify_turn.
        * (* contra *)
          inversion H.
        * econstructor.
          ** PS.simplify_turn.
             rewrite mem_domm. auto.
          ** simpl.
             rewrite domm0. simpl. rewrite filterm_identity.
             reflexivity.
          ** simpl. rewrite domm0.
             rewrite PS.to_partial_stack_unpartialize_identity.
             *** reflexivity.
             *** apply PS.merged_stack_has_no_holes.
                 inversion H; subst; assumption.
        * econstructor.
          ** PS.simplify_turn.
             rewrite mem_domm. auto.
          ** simpl.
             rewrite domm0. simpl. rewrite filterm_identity.
             reflexivity.
          ** simpl. rewrite domm0.
             rewrite PS.to_partial_stack_unpartialize_identity.
             *** reflexivity.
             *** apply PS.merged_stack_has_no_holes.
                 inversion H; subst; assumption.
        * (* contra *)
          inversion H.
      + (* unpartilizing the merge preserves the state information that make
           CS.initial_state true *)
        rewrite linking_empty_program. subst. simpl.
        inversion H0; subst; inversion H1; subst.
        CS.unfold_state ics. CS.unfold_state ics0.
        * admit.
    - admit.
  Admitted.

  Lemma multi_match_final_states:
    forall ms ips,
      multi_match ms ips ->
      final_state ms ->
      PS.final_state prog emptym ips.
  Proof.
    intros ms ips Hmmatch Hms_final.
    inversion Hms_final; subst.
    inversion Hmmatch; subst.
    eapply PS.final_state_program
      with (ics:=PS.unpartialize (PS.merge_partial_states ips1 ips2))
           (p':=empty_prog);
      inversion H4; subst; PS.simplify_turn.
    - reflexivity.
    - reflexivity.
    - apply empty_prog_linkability.
      inversion linkability; auto.
      apply linking_well_formedness; auto.
    - apply empty_prog_linkability.
      inversion linkability; auto.
      apply linking_well_formedness; auto.
    - rewrite mem_domm. auto.
    - rewrite mem_domm. auto.
    - constructor.
      + PS.simplify_turn.
        rewrite mem_domm. auto.
      + simpl. rewrite domm0. simpl. rewrite filterm_identity.
        reflexivity.
      + simpl. rewrite domm0.
        rewrite PS.to_partial_stack_unpartialize_identity.
        * reflexivity.
        * apply PS.merged_stack_has_no_holes.
          inversion H; subst; assumption.
    - constructor.
      + PS.simplify_turn.
        rewrite mem_domm. auto.
      + simpl. rewrite domm0. simpl. rewrite filterm_identity.
        reflexivity.
      + simpl. rewrite domm0.
        rewrite PS.to_partial_stack_unpartialize_identity.
        * reflexivity.
        * apply PS.merged_stack_has_no_holes.
          inversion H; subst; assumption.
    - inversion H; subst.
      + unfold CS.final_state in H10. CS.unfold_states.
        inversion H9; subst.
        rewrite linking_empty_program.
        (* execution in a larger program *)
        admit.
      + PS.simplify_turn. rewrite H3 in H1. discriminate.
    - inversion H0; subst.
      + unfold CS.final_state in H10. CS.unfold_states.
        inversion H9; subst.
        rewrite linking_empty_program.
        (* execution in a larger program *)
        admit.
      + PS.simplify_turn. rewrite H3 in H2. discriminate.
  Admitted.

  Lemma lockstep_simulation:
    forall ms t ms',
      step (prepare_global_env prog) ms t ms' ->
    forall ips,
      multi_match ms ips ->
    exists ips',
      PS.step prog emptym (prepare_global_env prog) ips t ips' /\ multi_match ms' ips'.
  Proof.
    intros ms t ms' Hstep.
    intros ips Hmatch.

    inversion Hmatch; subst.
    inversion Hstep; subst.

    exists (PS.merge_partial_states ips1' ips2'). split.

    - inversion H; subst; simpl;
      inversion H2; subst; inversion H5; subst.

      (* program is in the first state *)
      + inversion H9; subst; inversion H14; subst;
        PS.simplify_turn; simpl in *.
        admit.
      + (* program is in the second state *)
        eapply PS.partial_step with
            (ics:=PS.unpartialize (PS.PC (PS.merge_stacks pgps1 pgps2,
                                          PS.merge_memories pmem1 pmem2, regs, pc)))
            (p':=empty_prog).
        * reflexivity.
        * apply empty_prog_linkability.
          apply linking_well_formedness; auto.
        * admit.
        * constructor.
          ** PS.simplify_turn.
             rewrite mem_domm. auto.
          ** rewrite domm0. simpl. rewrite filterm_identity. reflexivity.
          ** rewrite domm0.
             rewrite (PS.to_partial_stack_unpartialize_identity
                        (PS.merged_stack_has_no_holes H4)).
             reflexivity.
        * admit.

    - (* prove match *) admit.
  Admitted.

  Theorem merged_prog_simulates_multisem:
    forward_simulation msem (PS.sem prog emptym).
  Proof.
    eapply forward_simulation_step.
    - apply multi_match_initial_states.
    - apply multi_match_final_states.
    - apply lockstep_simulation.
  Qed.
End MultiSemantics.
End MultiSem.

(*
  Putting all together in the partial semantics

  Two partial programs doing the same behavior can be merged into another partial
  program that does such behavior.
  NOTE: here we are starting with the assumption that the program resulting from
        the merge is a whole-program. In our case this is enough, but in general
        it would be nice to prove a theorem which composes two partial program
        into another possibly partial program.
*)

Section PartialComposition.
  Variables p c: program.

  Hypothesis linkability:
    linkable_programs p c.

  Let prog := program_link p c.

  Lemma threeway_multisem_st_star_simulation:
    forall ips1 ips2 t ips1' ips2',
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      st_star p (prog_interface c) (prepare_global_env p) ips1 t ips1' ->
      st_star c (prog_interface p) (prepare_global_env c) ips2 t ips2' ->
      star (MultiSem.step p c) (prepare_global_env prog) (ips1, ips2) t (ips1', ips2') /\
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1' ips2'.
  Proof.
    intros ips1 ips2 t ips1' ips2'.
    intros Hmergeable Hst_star1 Hst_star2.

    generalize dependent ips2.
    induction Hst_star1; subst.

    (* empty trace *)
    - intros ips2 Hmergeable Hst_star2.
      inversion Hmergeable; subst.

      (* the program doesn't step, hence we stay still *)
      + apply star_if_st_star in Hst_star2.
        eapply PS.context_epsilon_star_is_silent in Hst_star2; subst.
        split.
        * constructor.
        * assumption.
      (* the program does a star with an epsilon trace.
         use the fact that the context simulates the program *)
      + assert (Hmergeable':
                  PS.mergeable_states (prog_interface p) (prog_interface c)
                                      (PS.PC (pgps2, pmem2, regs, pc))
                                      (PS.CC (Pointer.component pc, pgps1, pmem1))). {
          (* mergeability is symmetric *)
          admit.
        }
        destruct (ProgCtxSim.st_star_simulation
                    (linkable_sym p c linkability) Hst_star2 Hmergeable')
          as [ips1' [Hstar Hmergeable'']].
        admit.

    (* non-empty trace *)
    - intros ips2 Hmergeable Hst_star2.
      inversion Hmergeable; subst.

      (* the program is stepping *)
      + (* simulate the step *)
        (* use inductive hypothesis *)
        (* compose previous results *)
        admit.

      (* the context is stepping *)
      + admit.
  Admitted.

  Theorem threeway_multisem_mt_star_simulation:
    forall ips1 ips2 t ips1' ips2',
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      mt_star p (prog_interface c) (prepare_global_env p) ips1 t ips1' ->
      mt_star c (prog_interface p) (prepare_global_env c) ips2 t ips2' ->
      star (MultiSem.step p c) (prepare_global_env prog) (ips1, ips2) t (ips1', ips2') /\
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1' ips2'.
  Proof.
    intros ips1 ips2 t ips1' ips2'.
    intros Hmergeable Hmt_star1 Hmt_star2.

    generalize dependent ips2.
    induction Hmt_star1; subst.

    (* single segment *)
    - intros ips2 Hmergeable Hmt_star2.
      inversion Hmergeable; subst.

      (* the program has control in the first state of the first sequence *)
      + inversion Hmt_star2; subst.

        (* single segment with the same trace *)
        * apply threeway_multisem_st_star_simulation; auto.

        (* segment + change of control + mt_star *)
        (* this case cannot happen since t2 is an event that changes
           control and it appears in the st_star segment *)
        * (* contradiction *) admit.

      (* the context has control in the first state of the first sequence *)
      + inversion Hmt_star2; subst.

        (* single segment with the same trace *)
        * apply threeway_multisem_st_star_simulation; auto.

        (* segment + change of control + mt_star *)
        (* this case cannot happen since t2 is an event that changes
           control and it appears in the st_star segment *)
        * (* contradiction *) admit.

    (* segment + change of control + mt_star *)
    - intros ips2 Hmergeable Hmt_star2.
      inversion Hmergeable; subst.

      (* the program has control in the first state of the first sequence *)
      + inversion Hmt_star2; subst.

        (* single segment with the same trace *)
        (* this case cannot happen since t2 is an event that changes
           control and it appears in the st_star segment *)
        * (* contradiction *) admit.

        (* segment + change of control + mt_star *)
        * assert (t1=t0). { admit. }
          assert (t2=t4). { admit. }
          assert (t3=t5). { admit. }
          subst.

          (* simulate the first segment (trace t0) *)

          destruct (threeway_multisem_st_star_simulation Hmergeable H H4)
            as [Hfirst_segment Hmergeable'].

          (* build the step that changes control (trace t4) *)

          assert (MultiSem.step p c (prepare_global_env prog) (ips', ips'0) t4 (ips'', ips''0))
            as Hmultistep. {
            constructor; auto.
          }

          assert (MultiSem.multi_match p c
                                       (ips', ips'0) (PS.merge_partial_states ips' ips'0))
            as Hmultimatch. {
            constructor; auto.
          }

          (* use the multisem simulation to show that the states after the step are still
             mergeable *)
          destruct (MultiSem.lockstep_simulation linkability Hmultistep Hmultimatch)
            as [merged_state' [Hmiddle_step Hmergeable'']].
          inversion Hmergeable''; subst.

          (* simulate the rest of the sequence (trace t5) *)

          destruct (IHHmt_star1 ips''0 H14 H9)
            as [Hlast_star Hmergeable'''].

          (* compose first segment + step that changes control + last star *)

          split.
          ** eapply star_trans.
             *** eapply star_right.
                 **** apply Hfirst_segment.
                 **** apply Hmultistep.
                 **** reflexivity.
             *** apply Hlast_star.
             *** apply app_assoc.
          ** assumption.

      (* the context has control in the first state of the first sequence *)
      + inversion Hmt_star2; subst.

        (* single segment with the same trace *)
        (* this case cannot happen since t2 is an event that changes
           control and it appears in the st_star segment *)
        * (* contradiction *) admit.

        (* segment + change of control + mt_star *)
        * assert (t1=t0). { admit. }
          assert (t2=t4). { admit. }
          assert (t3=t5). { admit. }
          subst.

          (* simulate the first segment (trace t0) *)

          destruct (threeway_multisem_st_star_simulation Hmergeable H H4)
            as [Hfirst_segment Hmergeable'].

          (* build the step that changes control (trace t4) *)

          assert (MultiSem.step p c (prepare_global_env prog) (ips', ips'0) t4 (ips'', ips''0))
            as Hmultistep. {
            constructor; auto.
          }

          assert (MultiSem.multi_match p c
                                       (ips', ips'0) (PS.merge_partial_states ips' ips'0))
            as Hmultimatch. {
            constructor; auto.
          }

          (* use the multisem simulation to show that the states after the step are still
             mergeable *)
          destruct (MultiSem.lockstep_simulation linkability Hmultistep Hmultimatch)
            as [merged_state' [Hmiddle_step Hmergeable'']].
          inversion Hmergeable''; subst.

          (* simulate the rest of the sequence (trace t5) *)

          destruct (IHHmt_star1 ips''0 H14 H9)
            as [Hlast_star Hmergeable'''].

          (* compose first segment + step that changes control + last star *)

          split.
          ** eapply star_trans.
             *** eapply star_right.
                 **** apply Hfirst_segment.
                 **** apply Hmultistep.
                 **** reflexivity.
             *** apply Hlast_star.
             *** apply app_assoc.
          ** assumption.
  Admitted.

  Corollary threeway_multisem_star:
    forall ips1 ips2 t ips1' ips2',
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      star (PS.step p (prog_interface c)) (prepare_global_env p) ips1 t ips1' ->
      star (PS.step c (prog_interface p)) (prepare_global_env c) ips2 t ips2' ->
      star (MultiSem.step p c) (prepare_global_env prog) (ips1, ips2) t (ips1', ips2').
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
      program_behaves (PS.sem p (prog_interface c)) (Terminates t) ->
      program_behaves (PS.sem c (prog_interface p)) (Terminates t) ->
      program_behaves (PS.sem prog emptym) (Terminates t).
  Proof.
    intros t Hprog1_beh Hprog2_beh.
    inversion Hprog1_beh; subst. inversion H0; subst.
    inversion Hprog2_beh; subst. inversion H4; subst.

    eapply forward_simulation_same_safe_behavior.
    + apply MultiSem.merged_prog_simulates_multisem; auto.
    + assert (Hmergeable:
               PS.mergeable_states (prog_interface c) (prog_interface p) s s0). {
        inversion H; subst; inversion H1; subst.
        inversion H9; subst; inversion H13; subst;
        inversion H10; subst; inversion H14; subst; simpl in *.
        - (* contra, pc is neither in (prog_interface c), nor in (prog_interface p) *)
          PS.simplify_turn.
          (* show and use the fact that the main has an entrypoint, therefore
             (Pointer.component pc) must be in either (prog_interface c) or (prog_interface p) *)
          (* here it's probably where we need well-formed programs *)
          admit.
        - constructor; PS.simplify_turn;
            try assumption;
            try reflexivity.
          + inversion linkability.
            unfold linkable_mains in H21.
            destruct (prog_main p); destruct (prog_main c); subst; simpl in *;
              try (rewrite H22 in H25; inversion H25; reflexivity).
            * admit.
            * admit.
            * admit.
            * admit.
          + admit.
          + unfold PS.mergeable_memories. admit.
        - constructor; PS.simplify_turn;
            try assumption;
            try reflexivity.
          + inversion linkability.
            unfold linkable_mains in H21.
            destruct (prog_main p); destruct (prog_main c); subst; simpl in *;
              try (rewrite H22 in H25; inversion H25; reflexivity).
            * admit.
            * admit.
            * admit.
            * admit.
          + admit.
          + unfold PS.mergeable_memories.
            (* show use the fact that the initial memory contains just the memories
               for the components present in the program, therefore they are disjoint *)
            admit.
        - (* contra, pc is both in (prog_interface c) and in (prog_interface p) *)
          admit.
      }
      eapply program_runs with (s:=(s,s0)).
      * constructor; auto.
      * eapply state_terminates with (s':=(s',s'0)); auto.
        ** apply threeway_multisem_star; auto.
        ** simpl. constructor; auto.
    + simpl. constructor.
  Admitted.
End PartialComposition.

(*
  Composition Theorem

  From partial semantics to complete semantics
  This is the final theorem which is actually needed for our proof plan.
*)

Section Composition.
  Variables p c: program.

  Let prog := program_link p c.

  Hypothesis linkability:
    linkable_programs p c.

  Hypothesis prog_is_closed:
    closed_program prog.

  (* this should follow from linkability *)
  Hypothesis prog_is_well_formed:
    well_formed_program prog.

  Theorem composition_for_termination:
    forall t,
      program_behaves (PS.sem p (prog_interface c)) (Terminates t) ->
      program_behaves (PS.sem c (prog_interface p)) (Terminates t) ->
      program_behaves (CS.sem prog) (Terminates t).
  Proof.
    intros t Hbeh1 Hbeh2.
    eapply partial_semantics_implies_complete_semantics; auto.
    apply partial_programs_composition; auto.
  Qed.
End Composition.