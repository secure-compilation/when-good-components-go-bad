Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
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
  partial semantics. Actually, we preserve undefined behavior when it is caused by the
  concrete program that we keep in the partial semantics (however, we still haven't
  formally proved this result in Coq).

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
    See state_determinism in Intermediate/PS.v for more details.
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
  1) proving that s1 and s2 are indeed mergeable
  2) proving that merging initial states produces an initial state
  3) proving that merging states two stars with the same trace, produces a star with
     such trace
  4) proving that merging final states produces a final state

  Comments on each part:

  (1) consists in showing that
    - one of the two states is controlled by the program, the other by the context
    - th executing component of the context state is the executing component in the
      program state (the component tag in the program counter)
    - stacks are one the complement of the other (should be trivial because the states
      are intial, therefore the stacks are empty)
    - memories are disjoint (the init procedure should give this fact)

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
    - rewrite linking_empty_program in H4. assumption.
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
      inversion H4; subst.
      PS.simplify_turn.
      enough (p' = empty_prog) as Hempty_prog. subst.
      + rewrite linking_empty_program in H5.
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

    inversion H4; subst; PS.simplify_turn;
      try contradiction.

    (* show stacks are equal *)
    rewrite domm0 in H13.
    apply PS.to_partial_stack_with_empty_context in H13. subst.

    (* show mem0 = mem *)
    rewrite domm0 in H12. simpl in *.
    do 2 rewrite filterm_identity in H12.
    subst.

    (* use the fact that p' is empty *)
    enough (p' = empty_prog) as Hempty_prog. subst.
    - rewrite linking_empty_program in H3.
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
      + rewrite linking_empty_program in H8. eauto.
      + inversion H2; subst.
        destruct (star_simulation H10 H7) as [? []].
        econstructor.
        * eauto.
        * unfold nostep in *. intros.
          unfold not. intro.
          rewrite <- (linking_empty_program prog) in H14.
          destruct (Decomposition.lockstep_simulation H4 H5 H6 H14 H13)
            as [s'' []].
          eapply H11. econstructor; eauto.
        * unfold not. intros.
          apply H12. econstructor; eauto.
          ** PS.simplify_turn. unfold not. intro.
             destruct s'. repeat destruct p.
             rewrite mem_domm in H15. inversion H15.
             *** destruct c. destruct p.
                 rewrite mem_domm in H15. inversion H15.
          ** rewrite linking_empty_program. eauto.
    - (* program went wrong immediately *)
      eapply program_goes_initially_wrong.
      intros. unfold not. intro.
      specialize (H2 (PS.partialize s emptym)).
      apply H2.
      apply PS.initial_state_intro with (p':=empty_prog) (ics:=s).
      + reflexivity.
      + assumption.
      + apply empty_prog_is_well_formed.
      + destruct prog_is_well_formed as [Hsound_interface _ _ _ _ _].
        unfold linkable. simpl. split.
        * rewrite unionm0. assumption.
        * rewrite domm0. apply fdisjoints0.
      + apply PS.partialize_correct.
        reflexivity.
      + destruct prog.
        unfold program_link. simpl.
        repeat rewrite unionm0.
        destruct prog_main0; simpl;
        assumption.
  Qed.
End PS2CS.

(* Definition in terms of an interface (like everything else in the development).
   A disadvantage of the current definition is that tactics like [constructor]
   are ambiguous and cannot choose the obviously correct constructor. *)
Inductive same_turn (ctx : Program.interface) : PS.state -> PS.state -> Prop :=
| same_turn_program: forall st st',
    PS.is_program_component st ctx ->
    PS.is_program_component st' ctx ->
    same_turn ctx st st'
| same_turn_context: forall st st',
    PS.is_context_component st ctx ->
    PS.is_context_component st' ctx ->
    same_turn ctx st st'.

(* st_star represents a sequence of events performed by the same actor *)
(* st stands for same turn *)
Inductive st_starN (p: program) (ctx: Program.interface) (G: global_env)
  : nat -> PS.state -> trace -> PS.state -> Prop :=
| st_starN_refl: forall ips,
    st_starN p ctx G 0 ips E0 ips
| st_starN_step: forall n ips t1 ips' t2 ips'' t,
    PS.step p ctx G ips t1 ips' ->
    same_turn ctx ips ips' ->
    st_starN p ctx G n ips' t2 ips'' ->
    t = t1 ** t2 ->
    st_starN p ctx G (S n) ips t ips''.

Lemma st_starN_same_turn:
  forall p ctx G n ips t ips',
    st_starN p ctx G n ips t ips' ->
    same_turn ctx ips ips'.
Proof.
  intros p ctx G n ips t ips' Hst_star.
  induction Hst_star as [| n s1 t1 s2 t2 s3 ? Hstep12 Hturn12 IHHst_star Hturn23]; subst.
  - destruct (PS.is_context_component ips ctx) eqn:Hcomp.
    + apply same_turn_context;
        assumption.
    + apply same_turn_program;
        PS.simplify_turn;
        rewrite Hcomp;
        reflexivity.
  - inversion Hturn12 as [? ? Hcomp1 Hcomp2| ? ? Hcomp1 Hcomp2];
      inversion Hturn23 as [? ? Hcomp2' Hcomp3 | ? ? Hcomp2' Hcomp3];
      subst.
    + apply same_turn_program; assumption.
    + PS.simplify_turn.
      rewrite Hcomp2' in Hcomp2.
      discriminate.
    + PS.simplify_turn.
      rewrite Hcomp2 in Hcomp2'.
      discriminate.
    + apply same_turn_context; assumption.
Qed.

(* mt_star is a sequence of st_star interleaved by steps that change control *)
(* mt stands for multi turn *)
Inductive mt_starN (p: program) (ctx: Program.interface) (G: global_env)
  : nat -> PS.state -> trace -> PS.state -> Prop :=
| mt_starN_segment: forall n ips t ips',
    st_starN p ctx G n ips t ips' ->
    mt_starN p ctx G n ips t ips'
| mt_starN_control_change: forall n1 n2 n3 ips t1 ips' t2 ips'' t3 ips''' t,
    st_starN p ctx G n1 ips t1 ips' ->
    PS.step p ctx G ips' t2 ips'' ->
    ~ same_turn ctx ips' ips'' ->
    mt_starN p ctx G n2 ips'' t3 ips''' ->
    n3 = S (n1 + n2) ->
    t = t1 ** t2 ** t3 ->
    mt_starN p ctx G n3 ips t ips'''.

Theorem starN_if_st_starN:
  forall p ctx G n ips t ips',
    st_starN p ctx G n ips t ips' ->
    starN (PS.step p ctx) G n ips t ips'.
Proof.
  intros p ctx G n ips t ips' Hst_starN.
  induction Hst_starN; subst;
    econstructor; eauto.
Qed.

Theorem star_if_st_starN:
  forall p ctx G n ips t ips',
    st_starN p ctx G n ips t ips' ->
    star (PS.step p ctx) G ips t ips'.
Proof.
  intros p ctx G n ips t ips' Hst_star.
  apply starN_if_st_starN in Hst_star.
  eapply starN_star; eauto.
Qed.

Theorem starN_if_mt_starN:
  forall p ctx G n ips t ips',
    mt_starN p ctx G n ips t ips' ->
    starN (PS.step p ctx) G n ips t ips'.
Proof.
  intros p ctx G n ips t ips' Hmt_star.
  induction Hmt_star; subst.

  (* st_starN *)
  - eapply starN_if_st_starN; eauto.

  (* st_starN + step that changes control + mt_starN *)
  - eapply starN_trans.
    + eapply starN_right.
      * eapply starN_if_st_starN. eassumption.
      * eassumption.
      * reflexivity.
    + eassumption.
    + reflexivity.
    + apply app_assoc.
Qed.

Theorem star_if_mt_starN:
  forall p ctx G n ips t ips',
    mt_starN p ctx G n ips t ips' ->
    star (PS.step p ctx) G ips t ips'.
Proof.
  intros p ctx G n ips t ips' Hmt_star.

  apply starN_if_mt_starN in Hmt_star.
  apply starN_star in Hmt_star.
  assumption.
Qed.

(* We want to prove that a star is either a sequence of steps without change of control,
   or it can be decomposed in a star without change of control + a step with the change
   of control + another star doing the remaining trace *)

Theorem mt_starN_if_starN:
  forall p ctx G n ips t ips',
    starN (PS.step p ctx) G n ips t ips' ->
    mt_starN p ctx G n ips t ips'.
Proof.
  intros p ctx G n ips t ips' HstarN.
  induction HstarN as [| n s1 t t1 s2 t2 s3 Hstep HstarN IHHstarN Ht].
  - apply mt_starN_segment.
    apply st_starN_refl.
  - subst t.
    destruct (PS.is_context_component s1 ctx) eqn:Hcomp1;
      destruct (PS.is_context_component s2 ctx) eqn:Hcomp2.
    (* If the states belong to the same turn, if the turn is the same as the first turn
       in the star, it continues its first segment, otherwise it changes control.
       If the states belong to different turns, the star changes control.
       RB: TODO: Duplicated (2-3) and redundant (1-4) cases, simplifications and
       symmetries, more visible through the revised definition of same_turn, slightly
       less automatic. *)
    + inversion IHHstarN
        as [? ? ? ? Hst_starN |
            n1 n2 ? ? t'1 s'1 t'2 s'2 t'3 ? ? Hst_starN' Hstep' Hsame' Hmt_starN'];
        subst.
      * apply mt_starN_segment.
        eapply st_starN_step;
          try eassumption.
        -- apply same_turn_context; assumption.
        -- reflexivity.
      * eapply mt_starN_control_change;
          try eassumption.
        -- eapply st_starN_step;
             try eassumption.
           ++ apply same_turn_context; assumption.
           ++ reflexivity.
        -- reflexivity.
        -- rewrite Eapp_assoc.
           reflexivity.
    + eapply mt_starN_control_change.
      * apply st_starN_refl.
      * apply Hstep.
      * intros Hsame.
        inversion Hsame as [? ? Hcomp1' Hcomp2' | ? ? Hcomp1' Hcomp2']; subst.
        -- PS.simplify_turn.
           rewrite Hcomp1 in Hcomp1'.
           discriminate.
        -- PS.simplify_turn.
           rewrite Hcomp2 in Hcomp2'.
           discriminate.
      * apply IHHstarN.
      * reflexivity.
      * reflexivity.
    + eapply mt_starN_control_change.
      * apply st_starN_refl.
      * apply Hstep.
      * intros Hsame.
        inversion Hsame as [? ? Hcomp1' Hcomp2' | ? ? Hcomp1' Hcomp2']; subst.
        -- PS.simplify_turn.
           rewrite Hcomp2 in Hcomp2'.
           discriminate.
        -- PS.simplify_turn.
           rewrite Hcomp1 in Hcomp1'.
           discriminate.
      * apply IHHstarN.
      * reflexivity.
      * reflexivity.
    + inversion IHHstarN
        as [? ? ? ? Hst_starN |
            n1 n2 ? ? t'1 s'1 t'2 s'2 t'3 ? ? Hst_starN' Hstep' Hsame' Hmt_starN'];
        subst.
      * apply mt_starN_segment.
        eapply st_starN_step;
          try eassumption.
        -- apply same_turn_program;
             unfold PS.is_program_component.
           ++ rewrite Hcomp1.
              reflexivity.
           ++ rewrite Hcomp2.
              reflexivity.
        -- reflexivity.
      * eapply mt_starN_control_change;
          try eassumption.
        -- eapply st_starN_step;
             try eassumption.
           ++ apply same_turn_program;
                unfold PS.is_program_component.
              ** rewrite Hcomp1.
                 reflexivity.
              ** rewrite Hcomp2.
                 reflexivity.
           ++ reflexivity.
        -- reflexivity.
        -- rewrite Eapp_assoc.
           reflexivity.
Qed.

Theorem mt_starN_if_star:
  forall p ctx G ips t ips',
    star (PS.step p ctx) G ips t ips' ->
  exists n,
    mt_starN p ctx G n ips t ips'.
Proof.
  intros p ctx G ips t ips' Hstar.
  apply star_starN in Hstar.
  destruct Hstar as [n Hstar].
  exists n. apply mt_starN_if_starN; auto.
Qed.

Theorem starN_mt_starN_equivalence:
  forall p ctx G n ips t ips',
    starN (PS.step p ctx) G n ips t ips' <->
    mt_starN p ctx G n ips t ips'.
Proof.
  intros. split.
  - apply mt_starN_if_starN.
  - apply starN_if_mt_starN.
Qed.

Theorem star_mt_starN_equivalence:
  forall p ctx G ips t ips',
    star (PS.step p ctx) G ips t ips' <->
    exists n, mt_starN p ctx G n ips t ips'.
Proof.
  intros. split.
  - apply mt_starN_if_star.
  - intro. destruct H. eapply star_if_mt_starN. eauto.
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
  | initial_state_intro: forall ics ips,
      CS.comes_from_initial_state ics ->
      PS.partial_state ctx ics ips ->
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
  | initial_state_intro: forall ics ips,
      CS.comes_from_initial_state ics ->
      PS.partial_state ctx ics ips ->
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

  Hypothesis wf1 : well_formed_program p.
  Hypothesis wf2 : well_formed_program c.

  Hypothesis linkability: linkable (prog_interface p) (prog_interface c).

  Hypothesis prog_is_closed:
    closed_program (program_link p c).

  Hypothesis mergeable_interfaces:
    PS.mergeable_interfaces (prog_interface p) (prog_interface c).

  (* RB: TODO: The following two lemmas should live in PS, if useful. *)
  Lemma mergeable_stack_exists :
    forall pgps1,
    exists pgps2,
      PS.mergeable_stacks pgps1 pgps2.
  Proof.
    induction pgps1 as [| ptr pgps1 IH].
    - exists [].
      constructor.
    - destruct IH as [pgps2 IH].
      destruct ptr as [C [[b o] |]].
      + exists ((C, None) :: pgps2).
        constructor.
        * by apply IH.
        * by constructor.
      + exists ((C, Some (0, 0%Z)) :: pgps2).
        constructor.
        * by apply IH.
        * by econstructor.
  Qed.

  Lemma mergeable_memory_exists :
    forall mem1,
    exists mem2,
      PS.mergeable_memories mem1 mem2.
  Proof.
    intro mem1.
    exists emptym.
    unfold PS.mergeable_memories.
    rewrite domm0.
    apply fdisjoints0.
  Qed.

  (* RB: TODO: p and c are closed and disjoint, so by well-formedness of the state
    (to be defined), we must get that if a component is not in c, it must be in p,
    and so on. The existence of mergeable stacks and memories given one of the
    halves is used, but it is unclear how informative this is without appealing to
    well-formed states. The same applies to made up registers and pointers.
    Regardless, observe that there remains a troublesome case when matching the
    PC form against mergeable_states.

    Observe several goals repeat: pose, refactor, etc. *)
  Lemma match_initial_states:
    forall ips1,
      ProgramSem.initial_state (prog_interface c) ips1 ->
    exists ips2,
      ContextSem.initial_state (prog_interface p) ips2 /\
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2.
  Proof.
    intros ips1 Hini.
    inversion Hini as [ics ? Hcomes_from Hpartial1 Hpc1]; subst.
    inversion Hcomes_from as [p' [s' [t' [Hini' Hstar']]]].
    inversion Hpartial1 as [? ? ? ? ? ? _ | ? ? ? ? ? ? Hcc1]; subst;
      PS.simplify_turn;
      last by rewrite Hcc1 in Hpc1. (* Contra. *)
    exists
      (PS.CC
         (Pointer.component pc,
          PS.to_partial_stack gps (domm (prog_interface p)),
          filterm (fun (k : nat) (_ : ComponentMemory.t) => k \notin domm (prog_interface p)) mem)).
    split.
    - econstructor.
      + eassumption.
      + constructor.
        * PS.simplify_turn. eapply PS.domm_partition; eassumption.
        * reflexivity.
        * reflexivity.
      + PS.simplify_turn. eapply PS.domm_partition; eassumption.
    - econstructor.
      + eapply PS.mergeable_interfaces_sym; eassumption.
      + eassumption.
      + assumption.
      + constructor.
        * PS.simplify_turn. eapply PS.domm_partition; eassumption.
        * reflexivity.
        * reflexivity.
  Qed.

  Lemma match_final_states:
    forall ips1 ips2,
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      ProgramSem.final_state (prog_interface c) ips1 ->
      ContextSem.final_state (prog_interface p) ips2.
  Proof.
    intros ips1 ips2 Hmerge Hfinal1.
    constructor.
    inversion Hfinal1 as [? Hpc]; subst.
    inversion Hmerge
      as [ics ? ? Hmerge_ifaces Hini Hpartial1 Hpartial2]; subst.
    inversion Hpartial1; subst;
      inversion Hpartial2; subst;
      PS.simplify_turn.
    - eapply PS.domm_partition; eassumption.
    - assumption.
    - eapply PS.domm_partition; eassumption.
    - assumption.
  Qed.

  Lemma lockstep_simulation:
    forall ips1 t ips1',
      Step (ProgramSem.sem p (prog_interface c)) ips1 t ips1' ->
    forall ips2,
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
    exists ips2',
      Step (ContextSem.sem c (prog_interface p)) ips2 t ips2' /\
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1' ips2'.
  Proof.
    intros ips1 t ips1' HStep ips2 Hmerge.
    inversion HStep as [? ? ? Hpc1 Hpc1' Hstep_ps]; subst.
    inversion Hmerge as [ics ? ? Hmerge_iface Hfrom_initial Hpartial1 Hpartial2]; subst;
      inversion Hpartial1 as [? ? ? ? ? ? _ | ? ? ? ? ? ? Hcc1]; subst;
      inversion Hpartial2 as [? ? ? ? ? ? Hpc2 | ? ? ? ? ? ? Hcc2]; subst;
      PS.simplify_turn;
      [admit | | admit | admit]. (* Contra. *)
    inversion Hstep_ps
      as [p' ? ? ? ics1 ics1' Hsame_iface _ Hwf2' Hlinkable Hstep_cs Hpartial Hpartial'];
      subst.
    destruct ips1' as [[[[stk1' mem1'] regs1'] pc1'] | [[Cid1' stk1'] mem1']];
      (* RB: TODO: Ltac to discharge \in-\notin sequents, propagate and reuse; cf. PS. *)
      last by
        inversion Hpartial;
        inversion Hpartial' as [| ? ? ? ? ? ? Hcontra];
        subst;
        PS.simplify_turn;
        rewrite Hcontra in Hpc1'.
    inversion Hpartial as [? ? ? ? ? ? Hpc_partial Hmem Hstk |]; subst.
    inversion Hpartial' as [? ? ? ? ? ? Hpc_partial' |]; subst.
    PS.simplify_turn.
    inversion Hstep_cs; subst.
    - (* INop *)
      exists
        (PS.CC
           (Pointer.component pc,
            PS.to_partial_stack gps (domm (prog_interface p)),
            filterm (fun (k : nat) (_ : ComponentMemory.t) => k \notin domm (prog_interface p)) mem)).
      split.
      + constructor.
        * easy.
        * easy.
        * econstructor.
          -- reflexivity.
          -- assumption.
          -- assumption.
          -- eapply linkable_sym; eassumption.
          -- eapply CS.Nop.
             admit.
          -- admit.
          -- admit.
      + rewrite <- Hmem.
        rewrite <- Hstk.
        (* RB: TODO: Refer to ics symbolically, e.g. from goal via Ltac. *)
        eapply PS.mergeable_states_intro with
          (ics := (PS.unpartialize (PS.merge_partial_states
            (PS.PC
               (PS.to_partial_stack gps (domm (prog_interface c)),
               filterm (fun (k : nat) (_ : ComponentMemory.t) => k \notin domm (prog_interface c)) mem,
               regs1', Pointer.inc pc))
            (PS.CC
               (Pointer.component pc, PS.to_partial_stack gps (domm (prog_interface p)),
               filterm (fun (k : nat) (_ : ComponentMemory.t) => k \notin domm (prog_interface p)) mem))
          ))).
        * easy.
        * simpl.
          rewrite (PS.merge_stacks_partition Hmerge_iface).
          rewrite (PS.merge_memories_partition Hmerge_iface).
          admit.
        * constructor.
          -- assumption.
          -- by rewrite (PS.merge_memories_partition Hmerge_iface).
          -- by rewrite (PS.merge_stacks_partition Hmerge_iface).
        * simpl.
          rewrite (PS.merge_memories_partition Hmerge_iface).
          rewrite (PS.merge_stacks_partition Hmerge_iface).
          rewrite <- Pointer.inc_preserves_component.
          constructor.
          -- by rewrite Pointer.inc_preserves_component.
          -- reflexivity.
          -- reflexivity.
    (* RB: TODO: A couple of cases dealing with memories, etc.; then compose. *)
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

  Corollary st_starN_simulation:
    forall n ips1 t ips1',
      st_starN p (prog_interface c) (prepare_global_env p) n ips1 t ips1' ->
    forall ips2,
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
    exists ips2',
      st_starN c (prog_interface p) (prepare_global_env c) n ips2 t ips2' /\
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

  Hypothesis wf1 : well_formed_program p.
  Hypothesis wf2 : well_formed_program c.

  Hypothesis main_linkability: linkable_mains p c.
  Hypothesis linkability: linkable (prog_interface p) (prog_interface c).

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

  Lemma merged_initial_states:
    forall ips1 ips2,
      PS.initial_state p (prog_interface c) ips1 ->
      PS.initial_state c (prog_interface p) ips2 ->
      CS.initial_state (program_link p c)
                       (PS.unpartialize (PS.merge_partial_states ips1 ips2)).
  Proof.
  Admitted.

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
      + apply linking_well_formedness; now auto.
      + now apply empty_prog_is_well_formed.
      + simpl. apply linkable_emptym. now apply linkability.
      + inversion H0; subst. inversion H1; subst.
        inversion H6; subst; inversion H12; subst; PS.simplify_turn.
        * (* contra *)
          (* RB: TODO: Extract and simplify patterns if inversion of mergeable_states
             followed by the two partial_state: four standard cases, of which two are
             contradictory. More instances of this below. *)
          inversion H as [? ? ? Hmerge_ifaces ? Hpartial1 Hpartial2]; subst.
          inversion Hpartial1 as [? ? ? ? ? ? Hpc1 |]; subst.
          inversion Hpartial2 as [? ? ? ? ? ? Hpc2 |]; subst.
          PS.simplify_turn.
          apply (PS.domm_partition Hmerge_ifaces) in Hpc2.
          rewrite Hpc2 in Hpc1.
          discriminate.
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
                 apply (PS.mergeable_states_stacks H); reflexivity.
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
                 apply (PS.mergeable_states_stacks H); reflexivity.
        * (* contra *) (* Symmetric case of contra above. *)
          inversion H as [? ? ? Hmerge_ifaces ? Hpartial1 Hpartial2]; subst.
          inversion Hpartial1 as [| ? ? ? ? ? ? Hpc1]; subst.
          inversion Hpartial2 as [| ? ? ? ? ? ? Hpc2]; subst.
          PS.simplify_turn.
          apply (PS.domm_partition_notin Hmerge_ifaces) in Hpc2.
          rewrite Hpc1 in Hpc2.
          discriminate.
      + (* unpartilizing the merge preserves the state information that make
           CS.initial_state true *)
        rewrite linking_empty_program. subst. simpl.
        inversion H0; subst; inversion H1; subst.
        CS.unfold_state ics. CS.unfold_state ics0.
        * apply merged_initial_states; auto.
    - constructor; auto.
  Qed.

  Lemma multi_match_final_states:
    forall ms ips,
      multi_match ms ips ->
      final_state ms ->
      PS.final_state prog emptym ips.
  Proof.
    intros ms ips Hmmatch Hms_final.
    inversion Hms_final as [ips1 ips2 Hfinal1 Hfinal2]; subst.
    inversion Hmmatch as [? ? Hmergeable]; subst.
    inversion Hmergeable as [ics ? ? Hmergeable_ifaces Hcomes_from Hpartial1 Hpartial2]; subst.
    inversion Hpartial1 as [? ? ? ? ? ? Hpc1 | ? ? ? ? ? ? Hcc1]; subst;
      inversion Hpartial2 as [? ? ? ? ? ? Hpc2 | ? ? ? ? ? ? Hcc2]; subst;
      PS.simplify_turn;
      [ (* XXX: This relies on a false assumption *)
        now destruct (PS.domm_partition_in_neither Hmergeable_ifaces Hpc1 Hpc2)
      |
      |
      | ].
    - eapply PS.final_state_program with
        (ics := (PS.unpartialize_stack
                   (PS.merge_stacks (PS.to_partial_stack gps (domm (prog_interface c)))
                                    (PS.to_partial_stack gps (domm (prog_interface p)))),
                 PS.merge_memories
                   (filterm (fun (k : nat) (_ : ComponentMemory.t) => k \notin domm (prog_interface c)) mem)
                   (filterm (fun (k : nat) (_ : ComponentMemory.t) => k \notin domm (prog_interface p)) mem),
                 regs, pc))
        (p' := empty_prog).
      + reflexivity.
      + apply linking_well_formedness; assumption.
      + now apply empty_prog_is_well_formed.
      + apply linkable_emptym. now apply linkability.
      + PS.simplify_turn. now rewrite mem_domm.
      + constructor.
        * PS.simplify_turn.
          now rewrite mem_domm.
        * by rewrite domm0 filterm_predT.
        * rewrite domm0 (PS.merge_stacks_partition Hmergeable_ifaces).
          by rewrite (PS.merge_stacks_partition_emptym Hmergeable_ifaces).
      + rewrite linking_empty_program.
        inversion Hfinal1
          as [p' ics ? Hsame_iface' _ Hwf' Hlinkable' Hnotin' Hpartial' Hfinal' | ? Hcontra];
          subst;
          PS.simplify_turn;
          last by rewrite Hcontra in Hpc1.
        inversion Hpartial'; subst.
        inversion Hfinal'; subst.
        eapply (execution_invariant_to_linking _ _ _ _ _ Hlinkable'); assumption.
    - (* The second case is symmetric *)
      admit.
    - by move: (PS.domm_partition_notin Hmergeable_ifaces Hcc2); rewrite Hcc1.
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

    - inversion H as [ics ? ? Hmerge_ifaces Hfrom_initial Hpartial1 Hpartial2]; subst;
        inversion H2; subst;
        inversion H5; subst;
        inversion Hpartial1; subst;
        inversion Hpartial2; subst;
        simpl in *; PS.simplify_turn.
      + admit. (* contra *)
      + (* program is in the first state *)
(*
        inversion H8; subst; inversion H15; subst; (* RB: TODO: Name/review new offsets. *)
        PS.simplify_turn; simpl in *.
        eapply PS.partial_step with
            (ics:=PS.unpartialize (PS.PC (PS.merge_stacks pgps1 pgps2,
                                          PS.merge_memories pmem1 pmem2, regs, pc)))
            (p':=empty_prog).
        * reflexivity.
        * apply linking_well_formedness; assumption.
        * now apply empty_prog_is_well_formed.
        * apply linkable_emptym. now apply linkability.
        * admit.
        * constructor.
          ** PS.simplify_turn.
             by rewrite mem_domm.
          ** rewrite domm0. rewrite filterm_identity. reflexivity.
          ** rewrite domm0.
             rewrite (PS.to_partial_stack_unpartialize_identity
                        (PS.merged_stack_has_no_holes H4)).
             reflexivity.
        * admit.
*) admit.
      + admit. (* contra *)
      + (* program is in the second state *)
(*
        eapply PS.partial_step with
            (ics:=PS.unpartialize (PS.PC (PS.merge_stacks pgps1 pgps2,
                                          PS.merge_memories pmem1 pmem2, regs, pc)))
            (p':=empty_prog).
        * reflexivity.
        * apply linking_well_formedness; assumption.
        * now apply empty_prog_is_well_formed.
        * apply linkable_emptym. now apply linkability.
        * admit.
        * constructor.
          ** PS.simplify_turn.
             by rewrite mem_domm.
          ** rewrite domm0. rewrite filterm_identity. reflexivity.
          ** rewrite domm0.
             rewrite (PS.to_partial_stack_unpartialize_identity
                        (PS.merged_stack_has_no_holes H4)).
             reflexivity.
        * admit.
*) admit.

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

  Hypothesis wf1 : well_formed_program p.
  Hypothesis wf2 : well_formed_program c.

  Hypothesis main_linkability: linkable_mains p c.
  Hypothesis linkability: linkable (prog_interface p) (prog_interface c).

  Let prog := program_link p c.

  Hypothesis prog_is_closed:
    closed_program prog.

  Hypothesis mergeable_interfaces:
    PS.mergeable_interfaces (prog_interface p) (prog_interface c).

  Lemma threeway_multisem_st_starN_simulation:
    forall n ips1 ips2 t ips1' ips2',
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      st_starN p (prog_interface c) (prepare_global_env p) n ips1 t ips1' ->
      st_starN c (prog_interface p) (prepare_global_env c) n ips2 t ips2' ->
      starN (MultiSem.step p c) (prepare_global_env prog) n (ips1, ips2) t (ips1', ips2') /\
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1' ips2'.
  Proof.
    intros n ips1 ips2 t ips1' ips2'.
    intros Hmergeable Hst_star1 Hst_star2.

    generalize dependent ips2.
    induction Hst_star1; subst.

    (* empty trace *)
    - intros ips2 Hmergeable Hst_star2.
      inversion Hmergeable as [ics ? ? Hmergeable_ifaces Hcomes_from Hpartial1 Hpartial2];
        subst.
      inversion Hpartial1 as [? ? ? ? ? ? Hpc1 | ? ? ? ? ? ? Hcc1]; subst;
        inversion Hpartial2 as [? ? ? ? ? ? Hpc2 | ? ? ? ? ? ? Hcc2]; subst.

      + admit. (* Contra. *)

      (* the program doesn't step, hence we stay still *)
      + apply star_if_st_starN in Hst_star2.
        pose proof PS.context_epsilon_star_is_silent.
        eapply (PS.context_epsilon_star_is_silent Hcc2) in Hst_star2; subst.
        split.
        * constructor.
        * assumption.

      + admit. (* Contra. *)

      (* the program does a star with an epsilon trace.
         use the fact that the context simulates the program *)
      + assert (Hmergeable' := Hmergeable).
        apply PS.mergeable_states_sym in Hmergeable'; auto.
        assert (prog_is_closed' := prog_is_closed).
        rewrite (closed_program_link_sym wf1 wf2 linkability main_linkability)
          in prog_is_closed'.
        destruct (ProgCtxSim.st_starN_simulation wf2 wf1
                   (linkable_sym linkability) prog_is_closed'
                   Hmergeable_ifaces Hst_star2 Hmergeable')
          as [ips1' [Hstar Hmergeable'']].
        (* TODO *)
        admit.

    (* non-empty trace *)
    - intros ips2 Hmergeable Hst_star2.
      inversion Hmergeable as [ics ? ? Hmergeable_ifaces Hcomes_from Hpartial1 Hpartial2];
        subst.
      inversion Hpartial1 as [? ? ? ? ? ? Hpc1 | ? ? ? ? ? ? Hcc1]; subst;
        inversion Hpartial2 as [? ? ? ? ? ? Hpc2 | ? ? ? ? ? ? Hcc2]; subst.

      + admit. (* Contra. *)

      (* the program is stepping *)
      + (* simulate the step *)
        (* use inductive hypothesis *)
        (* compose previous results *)
        admit.

      + admit. (* Contra. *)

      (* the context is stepping *)
      + admit.
  Admitted.

  (* RB: TODO: Carefully check statement changes, esp. unproven and w.r.t.
     same_turn. Consider formulating the new premises in terms of same_turn. *)
  Lemma st_starN_with_turn_change_impossible_1:
    forall n1 ctx_st prog_st2 ctx_st' t1 prog_st1 t2 n2 t3 ips',
      PS.is_program_component prog_st2 (prog_interface c) ->
      PS.is_context_component ctx_st (prog_interface p) ->
      PS.mergeable_states (prog_interface c) (prog_interface p)
                          prog_st2 ctx_st ->
      st_starN c (prog_interface p) (prepare_global_env c)
               n1 ctx_st t1 ctx_st' ->
      PS.step c (prog_interface p) (prepare_global_env c) ctx_st' t2 prog_st1 ->
      ~ same_turn (prog_interface p) ctx_st' prog_st1 ->
      mt_starN c (prog_interface p) (prepare_global_env c) n2 prog_st1 t3 ips' ->
    forall n3 ips'',
      st_starN p (prog_interface c) (prepare_global_env p)
               n3 prog_st2 (t1 ** t2 ** t3) ips'' ->
      False.
  Proof.
  Admitted.

  Lemma st_starN_with_turn_change_impossible_1':
    forall n1 ctx_st prog_st2 ctx_st' t1 prog_st1 t2 n2 t3 ips',
      PS.is_context_component ctx_st (prog_interface c) ->
      PS.is_program_component prog_st2 (prog_interface p) ->
      PS.mergeable_states (prog_interface c) (prog_interface p)
                          ctx_st prog_st2 ->
      st_starN p (prog_interface c) (prepare_global_env p)
               n1 ctx_st t1 ctx_st' ->
      PS.step p (prog_interface c) (prepare_global_env p) ctx_st' t2 prog_st1 ->
      ~ same_turn (prog_interface c) ctx_st' prog_st1 ->
      mt_starN p (prog_interface c) (prepare_global_env p) n2 prog_st1 t3 ips' ->
    forall n3 ips'',
      st_starN c (prog_interface p) (prepare_global_env c)
               n3 prog_st2 (t1 ** t2 ** t3) ips'' ->
      False.
  Proof.
  Admitted.

  Lemma st_starN_with_turn_change_impossible_2:
    forall n1 prog_st ctx_st2 prog_st' t1 ctx_st1 t2 n2 t3 ips',
      PS.is_context_component ctx_st2 (prog_interface c) ->
      PS.is_program_component prog_st (prog_interface p) ->
      PS.mergeable_states (prog_interface c) (prog_interface p)
                          ctx_st2 prog_st ->
      st_starN c (prog_interface p) (prepare_global_env c)
               n1 prog_st t1 prog_st' ->
      PS.step c (prog_interface p) (prepare_global_env c) prog_st' t2 ctx_st1 ->
      ~ same_turn (prog_interface p) prog_st' ctx_st1 ->
      mt_starN c (prog_interface p) (prepare_global_env c) n2 ctx_st1 t3 ips' ->
    forall n3 ips'',
      st_starN p (prog_interface c) (prepare_global_env p)
               n3 ctx_st2 (t1 ** t2 ** t3) ips'' ->
      False.
  Proof.
  Admitted.

  Lemma st_starN_with_turn_change_impossible_3:
    forall n1 prog_st ctx_st2 prog_st' t1 ctx_st1 t2 n2 t3 ips',
      PS.is_program_component prog_st (prog_interface c) ->
      PS.is_context_component ctx_st2 (prog_interface p) ->
      PS.mergeable_states (prog_interface c) (prog_interface p)
                          prog_st ctx_st2 ->
      st_starN p (prog_interface c) (prepare_global_env p)
               n1 prog_st t1 prog_st' ->
      PS.step p (prog_interface c) (prepare_global_env p) prog_st' t2 ctx_st1 ->
      ~ same_turn (prog_interface c) prog_st' ctx_st1 ->
      mt_starN p (prog_interface c) (prepare_global_env p) n2 ctx_st1 t3 ips' ->
    forall n3 ips'',
      st_starN c (prog_interface p) (prepare_global_env c)
               n3 ctx_st2 (t1 ** t2 ** t3) ips'' ->
      False.
  Proof.
  Admitted.

  Lemma same_trace_and_steps:
    forall prog_st1 prog_st1' prog_st2 ctx_st1 ctx_st1'
           ctx_st2 ips' ips'' n1 n1' n2 n2' t1 t1' t2 t2' t3 t3',
      PS.is_program_component prog_st1 (prog_interface c) ->
      PS.is_context_component ctx_st1 (prog_interface p) ->
      PS.mergeable_states (prog_interface c) (prog_interface p)
                          prog_st1 ctx_st1 ->
      (* first side *)
      st_starN p (prog_interface c) (prepare_global_env p)
               n1 prog_st1 t1 prog_st1' ->
      PS.step p (prog_interface c) (prepare_global_env p) prog_st1' t2 ctx_st2 ->
      ~ same_turn (prog_interface c) prog_st1' ctx_st2 ->
      mt_starN p (prog_interface c) (prepare_global_env p) n2 ctx_st2 t3 ips' ->
      (* second side *)
      st_starN c (prog_interface p) (prepare_global_env c)
               n1' ctx_st1 t1' ctx_st1' ->
      PS.step c (prog_interface p) (prepare_global_env c) ctx_st1' t2' prog_st2 ->
      ~ same_turn (prog_interface p) ctx_st1' prog_st2 ->
      mt_starN c (prog_interface p) (prepare_global_env c) n2' prog_st2 t3' ips'' ->
      (* same steps and same trace *)
      t1 = t1' /\ t2 = t2' /\ t3 = t3' /\ n1 = n1' /\ n2 = n2'.
  Proof.
  Admitted.

  Lemma same_trace_and_steps':
    forall prog_st1 prog_st1' prog_st2 ctx_st1 ctx_st1'
           ctx_st2 ips' ips'' n1 n1' n2 n2' t1 t1' t2 t2' t3 t3',
      PS.is_context_component ctx_st1 (prog_interface c) ->
      PS.is_program_component prog_st1 (prog_interface p) ->
      PS.mergeable_states (prog_interface c) (prog_interface p)
                          ctx_st1 prog_st1 ->
      (* first side *)
      st_starN p (prog_interface c) (prepare_global_env p)
               n1 ctx_st1 t1 ctx_st1' ->
      PS.step p (prog_interface c) (prepare_global_env p) ctx_st1' t2 prog_st2 ->
      ~ same_turn (prog_interface c) ctx_st1' prog_st2 ->
      mt_starN p (prog_interface c) (prepare_global_env p) n2 prog_st2 t3 ips'' ->
      (* second side *)
      st_starN c (prog_interface p) (prepare_global_env c)
               n1' prog_st1 t1' prog_st1' ->
      PS.step c (prog_interface p) (prepare_global_env c) prog_st1' t2' ctx_st2 ->
      ~ same_turn (prog_interface p) prog_st1' ctx_st2 ->
      mt_starN c (prog_interface p) (prepare_global_env c) n2' ctx_st2 t3' ips' ->
      (* same steps and same trace *)
      t1 = t1' /\ t2 = t2' /\ t3 = t3' /\ n1 = n1' /\ n2 = n2'.
  Proof.
  Admitted.

  Theorem threeway_multisem_mt_starN_simulation:
    forall n ips1 ips2 t ips1' ips2',
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      mt_starN p (prog_interface c) (prepare_global_env p) n ips1 t ips1' ->
      mt_starN c (prog_interface p) (prepare_global_env c) n ips2 t ips2' ->
      starN (MultiSem.step p c) (prepare_global_env prog) n (ips1, ips2) t (ips1', ips2') /\
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1' ips2'.
  Proof.
    intros n ips1 ips2 t ips1' ips2'.
    intros Hmergeable Hmt_star1 Hmt_star2.

    generalize dependent ips2.
    induction Hmt_star1; subst.

    (* single segment *)
    - intros ips2 Hmergeable Hmt_star2.
      inversion Hmergeable as [ics ? ? Hsame_ifaces Hcomes_from Hpartial1 Hpartial2];
        subst.
      inversion Hpartial1 as [? ? ? ? ? ? Hpc1 | ? ? ? ? ? ? Hcc1]; subst;
        inversion Hpartial2 as [? ? ? ? ? ? Hpc2 | ? ? ? ? ? ? Hcc2]; subst.

      + (* Contra. *)
        PS.simplify_turn.
        apply (PS.domm_partition Hsame_ifaces) in Hpc2.
        rewrite Hpc2 in Hpc1.
        discriminate.

      (* the program has control in the first state of the first sequence *)
      + inversion Hmt_star2; subst.

        (* single segment with the same trace *)
        * eapply threeway_multisem_st_starN_simulation; eauto.

        (* segment + change of control + mt_star *)
        (* contradiction *)
        (* this case cannot happen since t2 is an event that changes
           control and it appears in the st_star segment *)
        * exfalso.
          eapply st_starN_with_turn_change_impossible_1; eauto.

      (* the context has control in the first state of the first sequence *)
      + inversion Hmt_star2; subst.

        (* single segment with the same trace *)
        * eapply threeway_multisem_st_starN_simulation; eauto.

        (* segment + change of control + mt_star *)
        (* contradiction *)
        (* this case cannot happen since t2 is an event that changes
           control and it appears in the st_star segment *)
        * exfalso.
          eapply st_starN_with_turn_change_impossible_2; eauto.

      + (* Contra. *)
        PS.simplify_turn.
        apply (PS.domm_partition_notin Hsame_ifaces) in Hcc2.
        rewrite Hcc1 in Hcc2.
        discriminate.

    (* segment + change of control + mt_star *)
    - intros ips2 Hmergeable Hmt_star2.
      inversion Hmergeable as [ics ? ? Hsame_ifaces Hcomes_from Hpartial1 Hpartial2];
        subst.
      inversion Hpartial1 as [? ? ? ? ? ? Hpc1 | ? ? ? ? ? ? Hcc1]; subst;
        inversion Hpartial2 as [? ? ? ? ? ? Hpc2 | ? ? ? ? ? ? Hcc2]; subst.

      + (* Contra. *)
        PS.simplify_turn.
        apply (PS.domm_partition Hsame_ifaces) in Hpc2.
        rewrite Hpc2 in Hpc1.
        discriminate.

      (* the program has control in the first state of the first sequence *)
      + inversion Hmt_star2; subst.

        (* single segment with the same trace *)
        (* contradiction *)
        (* this case cannot happen since t2 is an event that changes
           control and it appears in the st_star segment *)
        * exfalso.
          eapply st_starN_with_turn_change_impossible_3; eauto.

        (* segment + change of control + mt_star *)
        * destruct (same_trace_and_steps
                      Hpc1 Hcc2 Hmergeable H H0 H1 Hmt_star1 H2 H3 H4 H5)
            as [Ht1 [Ht2 [Ht3 [Hn1 Hn2]]]]. subst.
          (* simulate the first segment (trace t0) *)

          destruct (threeway_multisem_st_starN_simulation Hmergeable H H2)
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
          destruct (MultiSem.lockstep_simulation wf1 wf2 main_linkability linkability Hmultistep Hmultimatch)
            as [merged_state' [Hmiddle_step Hmergeable'']].
          inversion Hmergeable''; subst.

          (* simulate the rest of the sequence (trace t5) *)

          destruct (IHHmt_star1 ips''0 H11 H5)
            as [Hlast_star Hmergeable'''].

          (* compose first segment + step that changes control + last star *)

          split.
          ** eapply starN_trans.
             *** eapply starN_right.
                 **** apply Hfirst_segment.
                 **** apply Hmultistep.
                 **** reflexivity.
             *** apply Hlast_star.
             *** reflexivity.
             *** apply app_assoc.
          ** assumption.

      (* the context has control in the first state of the first sequence *)
      + inversion Hmt_star2; subst.

        (* single segment with the same trace *)
        (* contradiction *)
        (* this case cannot happen since t2 is an event that changes
           control and it appears in the st_star segment *)
        * exfalso.
          eapply st_starN_with_turn_change_impossible_1'; eauto.

        (* segment + change of control + mt_star *)
        * destruct (same_trace_and_steps'
                      Hcc1 Hpc2 Hmergeable H H0 H1 Hmt_star1 H2 H3 H4 H5)
            as [Ht1 [Ht2 [Ht3 [Hn1 Hn2]]]]. subst.

          (* simulate the first segment (trace t0) *)

          destruct (threeway_multisem_st_starN_simulation Hmergeable H H2)
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
          destruct (MultiSem.lockstep_simulation wf1 wf2 main_linkability linkability Hmultistep Hmultimatch)
            as [merged_state' [Hmiddle_step Hmergeable'']].
          inversion Hmergeable''; subst.

          (* simulate the rest of the sequence (trace t5) *)

          destruct (IHHmt_star1 ips''0 H11 H5)
            as [Hlast_star Hmergeable'''].

          (* compose first segment + step that changes control + last star *)

          split.
          ** eapply starN_trans.
             *** eapply starN_right.
                 **** apply Hfirst_segment.
                 **** apply Hmultistep.
                 **** reflexivity.
             *** apply Hlast_star.
             *** reflexivity.
             *** apply app_assoc.
          ** assumption.

      + (* Contra. *)
        PS.simplify_turn.
        apply (PS.domm_partition_notin Hsame_ifaces) in Hcc2.
        rewrite Hcc1 in Hcc2.
        discriminate.

  Qed.

  Corollary threeway_multisem_starN:
    forall n ips1 ips2 t ips1' ips2',
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      starN (PS.step p (prog_interface c)) (prepare_global_env p) n ips1 t ips1' ->
      starN (PS.step c (prog_interface p)) (prepare_global_env c) n ips2 t ips2' ->
      starN (MultiSem.step p c) (prepare_global_env prog) n (ips1, ips2) t (ips1', ips2').
  Proof.
    intros n ips1 ips2 t ips1' ips2'.
    intros Hmergeable Hstar1 Hstar2.
    eapply threeway_multisem_mt_starN_simulation.
    - assumption.
    - apply starN_mt_starN_equivalence; auto.
    - apply starN_mt_starN_equivalence; auto.
  Qed.

  Lemma initial_states_mergeability:
    forall s1 s2,
      initial_state (PS.sem p (prog_interface c)) s1 ->
      initial_state (PS.sem c (prog_interface p)) s2 ->
      PS.mergeable_states (prog_interface c) (prog_interface p) s1 s2.
  Proof.
    intros s1 s2 Hs1_init Hs2_init.
    inversion Hs1_init; subst; inversion Hs2_init; subst.
    inversion H3; subst; inversion H9; subst;
      inversion H4; subst; inversion H10; subst; simpl in *.

    (* contra, pc is neither in (prog_interface c), nor in (prog_interface p) *)
    - PS.simplify_turn.
      (* show and use the fact that the main has an entrypoint, therefore
         (Pointer.component pc) must be in either (prog_interface c) or (prog_interface p) *)
      (* here it's probably where we need well-formed programs *)
      admit.

    - econstructor.
      + apply PS.mergeable_interfaces_sym; assumption.
      + admit.
      + constructor.
        * assumption.
        * admit.
        * admit.
      + admit.
(*
      + inversion linkability.
        (* RB: With the changes to [linkability], the case analysis on programs
           does not follow naturally from its inversion. The admits on each
           resulting proof obligation are replaced by a single admit. Note that
           automatic hypothesis names have not been corrected as in the rest of
           the proof following changes to the notion of linkability to be based
           on interfaces, since they currently do not make sense.
           unfold linkable_mains in H21.
           destruct (prog_main p); destruct (prog_main c); subst; simpl in *;
           try (rewrite H22 in H25; inversion H25; reflexivity).
           * admit.
           * admit.
            * admit.
            * admit.
            *) admit.
          + admit.
          + unfold PS.mergeable_memories. admit.
*)

    - econstructor.
      + apply PS.mergeable_interfaces_sym; assumption.
      + admit.
      + admit.
      + admit.
(*
          + inversion linkability.
            (* RB: Same as above.
            unfold linkable_mains in H21.
            destruct (prog_main p); destruct (prog_main c); subst; simpl in *;
              try (rewrite H22 in H25; inversion H25; reflexivity).
            * admit.
            * admit.
            * admit.
            * admit.
            *) admit.
          + admit.
          + unfold PS.mergeable_memories.
            (* show use the fact that the initial memory contains just the memories
               for the components present in the program, therefore they are disjoint *)
            admit.
*)

    (* contra, pc is both in (prog_interface c) and in (prog_interface p) *)
    - admit.
  Admitted.

  Lemma termination_with_same_number_of_steps:
    forall t,
      program_behaves (PS.sem p (prog_interface c)) (Terminates t) ->
      program_behaves (PS.sem c (prog_interface p)) (Terminates t) ->
    exists n s1 s1' s2 s2',
      initial_state (PS.sem p (prog_interface c)) s1 /\
      starN (PS.step p (prog_interface c)) (prepare_global_env p) n s1 t s1' /\
      final_state (PS.sem p (prog_interface c)) s1' /\
      initial_state (PS.sem c (prog_interface p)) s2 /\
      starN (PS.step c (prog_interface p)) (prepare_global_env c) n s2 t s2' /\
      final_state (PS.sem c (prog_interface p)) s2'.
  Proof.
  Admitted.

  Corollary partial_programs_composition:
    forall t,
      program_behaves (PS.sem p (prog_interface c)) (Terminates t) ->
      program_behaves (PS.sem c (prog_interface p)) (Terminates t) ->
      program_behaves (PS.sem prog emptym) (Terminates t).
  Proof.
    intros t Hprog1_beh Hprog2_beh.

    destruct (termination_with_same_number_of_steps Hprog1_beh Hprog2_beh)
      as [n1 [s1 [s1' [s2 [s2' [Hinit1 [HstarN1 [Hfinal1 [Hinit2 [HstarN2 Hfinal2]]]]]]]]]].

    eapply forward_simulation_same_safe_behavior.
    + apply MultiSem.merged_prog_simulates_multisem; auto.
    + pose proof (initial_states_mergeability Hinit1 Hinit2) as Hmergeable.
      eapply program_runs with (s:=(s1,s2)).
      * constructor; auto.
      * eapply state_terminates with (s':=(s1',s2')); auto.
        ** eapply starN_star.
           eapply threeway_multisem_starN; eauto.
        ** simpl. constructor; auto.
    + simpl. constructor.
  Qed.

  Corollary partial_programs_composition_prefix :
    forall bp bc m,
      program_behaves (PS.sem p (prog_interface c)) bp ->
      program_behaves (PS.sem c (prog_interface p)) bc ->
      prefix m bp ->
      prefix m bc ->
    exists bprog,
      program_behaves (PS.sem prog emptym) bprog /\ prefix m bprog.
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

  Hypothesis wf1 : well_formed_program p.
  Hypothesis wf2 : well_formed_program c.

  Hypothesis main_linkability: linkable_mains p c.
  Hypothesis linkability: linkable (prog_interface p) (prog_interface c).

  Hypothesis prog_is_closed:
    closed_program (program_link p c).

  Hypothesis mergeable_interfaces:
    PS.mergeable_interfaces (prog_interface p) (prog_interface c).

  Theorem composition_for_termination:
    forall t,
      program_behaves (PS.sem p (prog_interface c)) (Terminates t) ->
      program_behaves (PS.sem c (prog_interface p)) (Terminates t) ->
      program_behaves (CS.sem (program_link p c)) (Terminates t).
  Proof.
    intros t Hbeh1 Hbeh2.
    eapply partial_semantics_implies_complete_semantics; auto.
    - apply linking_well_formedness; auto.
    - apply partial_programs_composition; auto.
  Qed.

  Theorem composition_prefix:
    forall b1 b2 m,
      program_behaves (PS.sem p (prog_interface c)) b1 ->
      program_behaves (PS.sem c (prog_interface p)) b2 ->
      prefix m b1 ->
      prefix m b2 ->
    exists b3,
      program_behaves (CS.sem (program_link p c)) b3 /\
      prefix m b3.
  Proof.
    intros b1 b2 m Hbeh1 Hbeh2 Hpref1 Hpref2.
    pose proof
      partial_programs_composition_prefix
        wf1 wf2 main_linkability linkability prog_is_closed mergeable_interfaces
        Hbeh1 Hbeh2 Hpref1 Hpref2
      as Hcomp.
    destruct Hcomp as [b3 [Hbeh3 Hpref3]].
    exists b3. split; auto.
    - apply partial_semantics_implies_complete_semantics; auto.
      + apply linking_well_formedness; auto.
  Qed.
End Composition.
