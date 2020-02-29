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
Require Import Old.Intermediate.MachineExtra.
Require Import Old.Intermediate.PS.
Require Import Old.Intermediate.Decomposition.
Require Import Intermediate.Machine.
Import MachineExtra.Intermediate.

Require Import Coq.Program.Equality.

From mathcomp Require Import ssreflect ssrfun ssrbool.

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

Module PS2CS.
Section Simulation.
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
    inversion Hips_init as [? ? ? ? ? ? ? Hmains]; subst.
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
    inversion Hips_final as [? ? ? ? ? ? ? Hmains |]; subst.
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

    inversion Hstep as [? ? ? ? ? ? ? ? ? ? Hmains]; subst.

    inversion H4; subst; PS.simplify_turn;
      try contradiction.

    (* show stacks are equal *)
    rewrite domm0 in H13.
    apply PS.to_partial_stack_with_empty_context in H13. subst.

    (* show mem0 = mem *)
    rewrite domm0 in H12. simpl in *.
    unfold to_partial_memory in *.
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
      inversion H0 as [? ? ? ? ? ? ? Hmains]; subst.
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
          destruct (Decomposition.lockstep_simulation H4 H5 H6 Hmains H14 H13)
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
      + unfold linkable_mains, empty_prog.
        destruct (prog_main prog); reflexivity.
      + apply PS.partialize_correct.
        reflexivity.
      + destruct prog.
        unfold program_link. simpl.
        repeat rewrite unionm0.
        destruct prog_main0; simpl;
        assumption.
  Qed.
End Simulation.
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

Lemma step_E0_same_turn:
  forall p ctx G s1 s2,
    PS.step p ctx G s1 E0 s2 ->
    same_turn ctx s1 s2.
  intros p ctx G s1 s2 Hstep.
  inversion Hstep
    as [p1 ? ? ? cs1 cs1' ? Hwfp Hwfp1 Hlink1 Hmains1 Hstep_cs1 Hpartial1 Hpartial1'];
    subst.
  inversion Hstep_cs1 ; subst ;
    inversion Hpartial1
    as [cstk1' ? cmem1' ? regs1' pc1' Hpc1' | cstk1' ? cmem1' ? regs1' pc1' Hcc1'];
    subst;
    inversion Hpartial1'
      as [cstk2' ? cmem2' ? regs2' pc2' Hpc2' | cstk2' ? cmem2' ? regs2' pc2' Hcc2'];
    subst ;
    PS.simplify_turn ;

    match goal with
    (* Obviously true cases *)
    | [ |- same_turn (prog_interface _) (PS.PC _) (PS.PC _)]
      => apply same_turn_program ; assumption
    | [ |- same_turn (prog_interface _) (PS.CC _) (PS.CC _)]
      => apply same_turn_context ; assumption

    (* Obviously wrong cases *)
    (* is_true coercion is not automatic in Ltac *)
    (* IJump *)
    | [ H__notin: is_true (Pointer.component _ \notin domm (prog_interface _)),
        H__in: is_true (Pointer.component  _  \in domm (prog_interface _)),
        H__pcEq: Pointer.component _ = Pointer.component _ |- _ ]
      => first [rewrite H__pcEq in H__notin | rewrite <- H__pcEq in H__notin] ;
        rewrite H__in in H__notin ; discriminate

    (* Pointer.inc (most of instructions) *)
    | [ H__notin: is_true (Pointer.component _ \notin domm (prog_interface _)),
        H__in: is_true (Pointer.component  (Pointer.inc _) \in domm (prog_interface _)) |- _ ]
      => rewrite Pointer.inc_preserves_component in H__in ;
        rewrite H__in in H__notin ; discriminate
    | [ H__notin: is_true (Pointer.component (Pointer.inc _) \notin domm (prog_interface _)),
        H__in: is_true (Pointer.component _ \in domm (prog_interface _)) |- _ ]
      => rewrite Pointer.inc_preserves_component in H__notin ;
        rewrite H__in in H__notin ;      discriminate

    (* IJal *)
    | [ H__notin: is_true (Pointer.component _ \notin domm (prog_interface _)),
        H__in: is_true (Pointer.component  _  \in domm (prog_interface _)),
        H__labelComp : find_label_in_component _ _ _ = Some _ |- _ ]
      => apply find_label_in_component_1 in H__labelComp;
        first [rewrite H__labelComp in H__notin | rewrite <- H__labelComp in H__notin];
        rewrite H__in in H__notin ; discriminate

    (* IBnz *)
    | [ H__notin: is_true (Pointer.component _ \notin domm (prog_interface _)),
        H__in: is_true (Pointer.component  _  \in domm (prog_interface _)),
        H__labelProc : find_label_in_procedure _ _ _ = Some _ |- _ ]
      => apply find_label_in_procedure_1 in H__labelProc;
        first [rewrite H__labelProc in H__notin | rewrite <- H__labelProc in H__notin];
        rewrite H__in in H__notin ; discriminate
    end.
Qed.

(* RB: TODO: Rename. *)
Ltac rewrite_if_then :=
  match goal with
  | H: is_true ?X
    |- context [ (if ?X then _ else _) ]
    =>
    rewrite H
  end.

Ltac rewrite_if_else_negb :=
  match goal with
  | H: is_true (negb ?X)
    |- context [ (if ?X then _ else _) ]
    =>
    apply negb_true_iff in H; setoid_rewrite H
  end.

(*
  Three-way Simulation

  The main intuition is that whenever two mergeable states make the same step, then
  the state resulting from their merge makes the same step as well.
*)

Module MultiSem.
Section MergeableStatesProgram.
  Variables p c: program.

  Hypothesis wf1 : well_formed_program p.
  Hypothesis wf2 : well_formed_program c.

  Hypothesis main_linkability: linkable_mains p c.
  Hypothesis linkability: linkable (prog_interface p) (prog_interface c).

  Hypothesis mergeable_interfaces:
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Let prog := program_link p c.

  Hypothesis prog_is_closed : closed_program prog.

  (* RB: TODO: Relocate, generalize existing tactic? *)
  Ltac CS_step_of_executing' PROG :=
    match goal with
    | H : executing (prepare_global_env PROG) _ ?INSTR |- _ =>
      match INSTR with
      | INop           => eapply CS.Nop
      | ILabel _       => eapply CS.Label
      | IConst _ _     => eapply CS.Const
      | IMov _ _       => eapply CS.Mov
      | IBinOp _ _ _ _ => eapply CS.BinOp
      | ILoad _ _      => eapply CS.Load
      | IStore _ _     => eapply CS.Store
      | IAlloc _ _     => eapply CS.Alloc
      | IBnz _ _       =>
        match goal with
        | H : Register.get _ _ = Int 0 |- _ => eapply CS.BnzZ
        | _                                 => eapply CS.BnzNZ
        end
      | IJump _        => eapply CS.Jump
      | IJal _         => eapply CS.Jal
      | ICall _ _      => eapply CS.Call
      | IReturn        => eapply CS.Return
      | IHalt          => fail
      end
    end.

  Ltac t_mergeable_states_step_intros :=
    intros s1 s1' s2 s2' t Hpcomp Hmergeable Hstep Hstep';
    (* Top-level case analysis. *)
    inversion Hmergeable
      as [ics ? ? Hmergeable_ifaces Hcomes_from Hpartial_ics1 Hpartial_ics1'];
      subst;
rename Hmergeable into _Hmergeable;
    inversion Hstep
      as [c' ? ? ? ics1 ics2
          Hsame_iface1 _ Hwf1 Hlinkable Hmains Hstep_cs Hpartial1 Hpartial2];
      subst;
rename Hstep into _Hstep;
    inversion Hstep'
      as [p' ? ? ? ics1' ics2'
          Hsame_iface2 _ Hwf2 Hlinkable' Hmains' Hstep_cs' Hpartial1' Hpartial2'];
      subst;
rename Hstep' into _Hstep';
    inversion Hpartial_ics1
      as [gps1 ? mem1 ? regs1 pc1 Hpc1 | gps1 ? mem1 ? ? pc1 Hcc1]; subst;
      [| exfalso; PS.simplify_turn; eapply PS.domm_partition_in_notin; eassumption];
rename Hpartial_ics1 into _Hpartial_ics1;
    (* p has control. *)
    inversion Hpartial_ics1'
      as [? | gps1' ? mem1' ? ? pc1' Hcc1']; subst;
      [exfalso; eapply PS.domm_partition_in_neither; eassumption |];
rename Hpartial_ics1' into _Hpartial_ics1';
      inversion Hpartial1
        as [ics_gps1 ? ics_mem1 ? ics_regs1 ics_pc1 Hics_pc1 Hmem1 Hstack1 |];
        subst;
rename Hpartial1 into _Hpartial1;
      inversion Hpartial1'
        as [| ics_gps1' ? ics_mem1' ? ics_regs1' ics_pc1' Hics_pc1' Hmem1' Hstack1' dummy Hcomp1'];
        subst;
rename Hpartial1' into _Hpartial1';
      PS.simplify_turn.

  (* RB: TODO: In this set of tactics, replace [try match goal] constructs by a
     [match goal] with an [idtac] default case, so that instructions are mandated
     for certain branches and failure to carry them out is detected
     immediately. More generally, document every [try] with the goals it is
     supposed to act on, either by white- or black-listing. *)
  Ltac t_mergeable_states_step_partial2 Hpartial2 _Hstep_cs :=
    inversion Hpartial2
      as [ ics_gps2 ? ics_mem2 ? ics_regs2 ics_pc2 Hics_pc2 Hmem2 Hstack2
         | ? ? ? ? ? ? Hics_pc2];
      subst;
    [ idtac
    | try (pose proof CS.silent_step_preserves_component _ _ _ _Hstep_cs as Heq;
           simpl in Heq; PS.simplify_turn; rewrite <- Heq in Hics_pc2;
           exfalso; eapply PS.domm_partition_in_notin; eassumption)
    ];
rename Hpartial2 into _Hpartial2.

  Ltac t_mergeable_states_step_partial2'
       Hpartial2' _Hstep_cs' Hsame_iface1 gps1 Hstack1 Hstack1' Hcomes_from Hics_pc2 Hics_pc2'
       Hstack1_hd Hcase1 gps1_hd (* Hack variables introduced by the tactic. *) :=
    inversion Hpartial2'
      as [ ics_gps2' ? ics_mem2' ? ics_regs2' ics_pc2' Hics_pc2'
         | ics_gps2' ? ics_mem2' ? ics_regs2' ics_pc2' Hics_pc2' Hmem2' Hstack2' dummy Hcomp2'];
      subst;
    [ try (pose proof CS.silent_step_preserves_component _ _ _ _Hstep_cs' as Heq;
           simpl in Heq; PS.simplify_turn; rewrite <- Heq in Hics_pc2';
           exfalso; eapply PS.domm_partition_in_notin; eassumption)
    | idtac
    ];
rename Hpartial2' into _Hpartial2';
    (* After this and the previous inversion, silent steps are in one-to-one
       correspondence. Calls and returns are not and present the usual four-case
       product, two of which cases are nonsensical and can be discharged. *)
    try (exfalso; PS.simplify_turn; eapply PS.domm_partition_in_both; eassumption);
    try match goal with
    | Heq : Pointer.component _ = Pointer.component _
      |- _ =>
      rewrite Heq in Hics_pc2';
      exfalso; PS.simplify_turn; eapply PS.domm_partition_in_both; eassumption
    end;
    try match goal with
    | Hentry : EntryPoint.get _ _ _ = Some _
      |- _ =>
      apply EntryPoint.get_some in Hentry;
      rewrite domm_genv_entrypoints in Hentry;
      simpl in Hentry; rewrite Hsame_iface1 in Hentry;
      exfalso; eapply PS.domm_partition_in_union_in_neither; eassumption
    end;
    try match goal with
    | Hop : CS.step _ _ [ERet _ _ (Pointer.component ?PC)] _,
      Heq : Pointer.component _ = Pointer.component ?PC
      |- _ =>
      (* RB: TODO: Decompose the stack up front, for all cases? *)
      destruct gps1 as [| gps1_hd gps1]; [now inversion Hstack1' | ];
      inversion Hstack1 as [[Hstack1_hd Htmp]]; clear Hstack1; rename Htmp into Hstack1;
      inversion Hstack1' as [[Hstack1'_hd Htmp]]; clear Hstack1'; rename Htmp into Hstack1';
      (* Back to business. *)
      exfalso; PS.simplify_turn;
      rewrite -> Heq in Hics_pc2';
      pose proof CS.comes_from_initial_state_stack_cons_domm _ _ _ _ _ _ Hcomes_from as Hdomm;
      destruct (Pointer.component PC \in domm (prog_interface c)) eqn:Hcase1;
        first (eapply PS.domm_partition_in_notin; eassumption);
      unfold PS.to_partial_frame in Hstack1_hd;
      rewrite -> Hcase1 in Hstack1_hd;
      destruct (Pointer.component gps1_hd \in domm (prog_interface c)) eqn:Hcase2;
        first discriminate;
      inversion Hstack1_hd as [[Hcomp Hblock Hoffset]]; rewrite <- Hcomp in Hics_pc2, Hics_pc2';
      eapply PS.domm_partition_in_union_in_neither; eassumption
    end.

  Ltac step_trans_solve_CC :=
    try rewrite -> Pointer.inc_preserves_component;
    try erewrite -> PS.to_partial_memory_merge_partial_memories_right;
    try erewrite -> PS.merge_stacks_partition_cons;
    (eassumption || reflexivity).

  Ltac step_trans_solve_partial_state :=
    constructor;
    try erewrite -> PS.to_partial_memory_merge_partial_memories_left;
    try erewrite -> PS.to_partial_memory_merge_partial_memories_right;
    (eassumption || reflexivity).

  (* RB: TODO: Infer parameters from context. *)
  Ltac mergeable_step_call_stack Hpc1 Hcc1' Hcomp1' pc1 :=
    rewrite PS.to_partial_stack_cons PS.merge_stacks_cons PS.unpartialize_stack_cons;
    assert (Hpc1c := Hpc1); rewrite <- Pointer.inc_preserves_component in Hpc1c;
    assert (Hpc1p := Hcc1'); rewrite <- Hcomp1' in Hpc1p; rewrite <- Pointer.inc_preserves_component in Hpc1p;
    assert (Hpc1c' : Pointer.component (Pointer.inc pc1) \in domm (prog_interface c) = false)
      by (destruct (Pointer.component (Pointer.inc pc1) \in domm (prog_interface c)) eqn:Hcase;
          now rewrite Hcase in Hpc1c);
    rewrite (PS.ptr_within_partial_frame_1 Hpc1p);
    rewrite (PS.ptr_within_partial_frame_2 Hpc1c');
    simpl; rewrite Pointer.compose.

  Ltac t_mergeable_states_step_trans_solve
       pc1 gps1 Hstack1 Hstack1' Hmem1 Hics_pc1' Hmem1' ics_pc1' Hcomp1'
       Hics_pc2' Hcomes_from Hmergeable_ifaces Hcc1' Hpc1 Hpc1c' Hpc1p
       HBnz1 HJal1 HJump1 (* Hack variables. *) :=
    (* Jump rewrite rule. This hypothesis will be used to rewrite, implicitly
       acting in the corresponding sub-case. Sometimes it will be necessary
       to re-detect the case we are in. Similarly for jumps. *)
    try match goal with
    | Hop : executing _ pc1 (IBnz _ _),
      Hlabel : find_label_in_procedure _ pc1 _ = Some _
      |- _ =>
      pose proof find_label_in_procedure_1 _ _ _ _ Hlabel as HBnz1
    end;
    try match goal with
    | Hop : executing _ pc1 (IJal _),
      Hlabel : find_label_in_component _ pc1 _ = Some _
      |- _ =>
      pose proof find_label_in_component_1 _ _ _ _ Hlabel as HJal1
    end;
    try match goal with
    | Hop : executing _ pc1 (IJump _),
      Hreg : Register.get ?REG _ = Ptr ?PTR,
      Hcomp : Pointer.component ?PTR = Pointer.component pc1
      |- _ =>
      rename Hcomp into HJump1
    end;
    (* Simplify cons'ed stack. *)
    try match goal with
    | Hop : executing _ _ IReturn
      |- _ =>
      destruct gps1 as [| gps1_hd gps1]; [now inversion Hstack1 | ];
      inversion Hstack1 as [[Hstack1_hd Htmp]]; clear Hstack1; rename Htmp into Hstack1;
      (* destruct ics_gps1' as [| ics_gps1'_hd ics_gps1']; [now inversion Hstack1' | ]; *)
      inversion Hstack1' as [[Hstack1'_hd Htmp]]; clear Hstack1'; rename Htmp into Hstack1'
    end;
    (* Stack and memory simplifications. *)
    try rewrite <- Hmem1;
    try rewrite <- Hstack1; (* (Returns rewrite the stack later.) *)
    (* (Case analysis on second CS step used to be here.) *)
    (* Specialized memory rewrites for store and alloc. *)
    try match goal with
    | Hop : executing _ ?PC (IStore _ _),
      Hcomp : Pointer.component ?PTR = Pointer.component ?PC,
      Hstore : Memory.store ?MEM1 ?PTR _ = Some ?MEM2
      |- _ =>
      rewrite <- Hcomp in Hics_pc1';
      rewrite -> (program_store_to_partialized_memory Hics_pc1' Hstore) in Hmem1'
    end;
    try match goal with
    | Hop : executing _ ?PC (IAlloc _ _),
      Halloc : Memory.alloc ?MEM1 (Pointer.component ?PTR) _ = Some (?MEM2, _)
      |- _ =>
      rewrite -> (program_allocation_to_partialized_memory Hics_pc1' Halloc) in Hmem1'
    end;
    (* Specialized memory rewrites for jumps. *)
    try match goal with
    | Hlabel : find_label_in_component _ ics_pc1' _ = Some _
      |- _ =>
      rewrite <- (find_label_in_component_1 _ _ _ _ Hlabel) in *
    end;
    try match goal with
    | Hop : executing _ ics_pc1' (IJump ?REG),
      Hreg : Register.get ?REG _ = Ptr ?PTR,
      Hcomp : Pointer.component ?PTR = Pointer.component ics_pc1'
      |- _ =>
      rewrite -> Hcomp in *
    end;
    try match goal with
    | Hlabel : find_label_in_procedure _ ics_pc1' _ = Some _
      |- _ =>
      rewrite <- (find_label_in_procedure_1 _ _ _ _ Hlabel) in *
    end;
    (* Stack and memory rewrites. *)
    rewrite <- Hmem1' in *;
    try rewrite <- Hstack1' in *; (* (Calls rewrite the stack later.) *)
    assert (Hcomp1'inc := Hcomp1');
    rewrite -Pointer.inc_preserves_component
            -[in RHS]Pointer.inc_preserves_component in Hcomp1'inc;
    try rewrite -> Hcomp1'inc in *;
    try rewrite -> Hcomp1' in *;
    (* Preprocess PC increments for jumps. *)
    try match goal with
    | Hcomp : is_true (Pointer.component pc1 \in _)
      |- PS.mergeable_states
           _ _
           (PS.PC (_, _, _, Pointer.inc ?PC))
           (PS.CC (Pointer.component ?PC, _, _))
      =>
      rewrite <- Pointer.inc_preserves_component;
      assert (Hinc := Hcomp); rewrite <- Pointer.inc_preserves_component in Hinc
    end;
    (* On calls, we cannot do too much work up front *and* reuse lemmas,
       but some useful facts can be established. *)
    unfold PS.is_context_component in Hics_pc2'; simpl in Hics_pc2';
    (* Solve goal. *)
    match goal with
    | |- PS.mergeable_states
           _ _
           (PS.PC (?GPS1, ?MEM1, ?REGS, ?PC))
           (PS.CC (_, ?GPS2, ?MEM2))
      =>
      remember (PS.unpartialize_stack (PS.merge_stacks GPS1 GPS2)) as gps12 eqn:Hgps12;
      remember (merge_memories MEM1 MEM2) as mem12 eqn:Hmem12;
      try rewrite (PS.merge_stacks_partition Hmergeable_ifaces Hcomes_from) in Hgps12;
      try rewrite (PS.merge_memories_partition Hmergeable_ifaces Hcomes_from) in Hmem12;
      apply PS.mergeable_states_intro
        with (ics := (gps12, mem12, REGS, PC))
    (* RB: TODO: In calls and returns from the context, same thing
       (refactoring target). Importantly, keeping the order of partial
       stacks and memories as in the goal, so that tactics work on both
       cases. *)
    | |- PS.mergeable_states
           _ _
           (PS.CC (_, ?GPS1, ?MEM1))
           (PS.PC (?GPS2, ?MEM2, ?REGS, ?PC))
      =>
      remember (PS.unpartialize_stack (PS.merge_stacks GPS1 GPS2)) as gps12 eqn:Hgps12;
      remember (merge_memories MEM1 MEM2) as mem12 eqn:Hmem12;
      try rewrite (PS.merge_stacks_partition Hmergeable_ifaces Hcomes_from) in Hgps12;
      try rewrite (PS.merge_memories_partition Hmergeable_ifaces Hcomes_from) in Hmem12;
      apply PS.mergeable_states_intro
        with (ics := (gps12, mem12, REGS, PC))
    end;
    subst;
    [ assumption
    | eapply PS.comes_from_initial_state_step_trans; try eassumption;
      [ simpl; now rewrite -> Hcc1'
      | (* Stack rewrites, before simplification. *)
        try match goal with
        | Hop : executing _ _ (ICall _ _)
          |- _ =>
          mergeable_step_call_stack Hpc1 Hcc1' Hcomp1' pc1;
          rewrite <- Hstack1'; (* This always follows mergeable_step_call_stack. *)
          erewrite PS.to_partial_stack_merge_stack_right; try eassumption;
          unfold PS.to_partial_frame;
          rewrite !Pointer.inc_preserves_component Hcc1' Hcomp1'
        end;
        try match goal with
        | Hop : CS.step _ _ [ERet _ _ (Pointer.component ?PC)] _,
          Heq : Pointer.component _ = Pointer.component ?PC
          |- _ =>
          rewrite -> Heq in Hics_pc2'; rewrite -> Heq
        end;
        simpl;
        try rewrite <- HBnz1;
        try rewrite <- HJal1;
        try rewrite -> HJump1;
        ( (* Usual case. *)
          rewrite_if_then
        || (* Calls and returns from context. *)
          (PS.simplify_turn; rewrite_if_else_negb)
        );
        now step_trans_solve_CC
      ]
    | match goal with
      | Hop : executing _ _ (ICall _ _)
        |- _ =>
        mergeable_step_call_stack Hpc1 Hcc1' Hcomp1' pc1;
        rewrite <- Hstack1';
        erewrite PS.merge_stacks_partition; try eassumption;
        constructor;
        [ assumption
        | reflexivity
        | simpl; unfold PS.to_partial_frame; rewrite Hpc1c'; reflexivity
        ]
      | Hop : executing _ _ IReturn
        |- _ =>
        erewrite -> PS.merge_stacks_partition_cons; try eassumption;
        constructor;
          PS.simplify_turn; congruence (* (Refined for context component return.) *)
      | |- _ =>
        now step_trans_solve_partial_state
      end
    | (* now step_trans_solve_partial_state. *)
      try match goal with
      | Hop : executing _ pc1 (IBnz _ _)
        |- _ =>
        try rewrite -> Pointer.inc_preserves_component;
        rewrite -> HBnz1
      end;
      try match goal with
      | Hop : executing _ pc1 (IJal _)
        |- _ =>
        try rewrite -> Pointer.inc_preserves_component;
        rewrite -> HJal1
      end;
      try match goal with
      | Hop : executing _ pc1 (IJump _)
        |- _ =>
        try rewrite -> Pointer.inc_preserves_component;
        rewrite <- HJump1
      end;
      match goal with
      | Hop : executing _ _ (ICall _ _)
        |- _ =>
        mergeable_step_call_stack Hpc1 Hcc1' Hcomp1' pc1;
        rewrite <- Hstack1';
        constructor;
        [ assumption
        | reflexivity
        | erewrite PS.merge_stacks_partition; try eassumption;
          simpl; unfold PS.to_partial_frame;
          rewrite Hcomp1'inc in Hpc1p; rewrite Hpc1p Hcomp1'inc; reflexivity
        ]
      | Hop : CS.step _ _ [ERet _ _ (Pointer.component ?PC)] _,
        Heq : Pointer.component _ = Pointer.component ?PC
        |- _ =>
        rewrite -> Heq; rewrite -> Heq in Hics_pc2';
        erewrite -> PS.merge_stacks_partition_cons; try eassumption;
        now constructor
      | |- _ =>
        constructor;
          try erewrite -> PS.to_partial_memory_merge_partial_memories_left;
          try erewrite -> PS.to_partial_memory_merge_partial_memories_right;
          try erewrite -> PS.merge_stacks_partition_cons;
          try rewrite <- HBnz1;
          try rewrite <- HJal1;
          try rewrite -> HJump1;
          eassumption || reflexivity
      end
        (* [ assumption *)
        (* | eapply PS.comes_from_initial_state_step_trans; try eassumption; *)
        (*   [ simpl; now rewrite -> Hcc1' *)
        (*   | simpl; rewrite_if_then; now step_trans_solve_CC ] *)
        (* | now step_trans_solve_partial_state *)
        (* | now step_trans_solve_partial_state ]. *)
    ].

  (* RB: TODO: This result very likely belongs in PS. I am reusing the hypotheses
     in this section, but these should be pared down. *)
  Lemma mergeable_states_step_trans_program : forall s1 s1' s2 s2' t,
    PS.is_program_component s1 (prog_interface c) ->
    PS.mergeable_states (prog_interface c) (prog_interface p) s1 s1' ->
    PS.step p (prog_interface c) (prepare_global_env p) s1 t s2 ->
    PS.step c (prog_interface p) (prepare_global_env c) s1' t s2' ->
    PS.mergeable_states (prog_interface c) (prog_interface p) s2 s2'.
  Proof.
    t_mergeable_states_step_intros.
    (* Case analysis on p's step. *)
    inversion Hstep_cs; subst;
rename Hstep_cs into _Hstep_cs;
      (* Invert first final partial step. *)
      t_mergeable_states_step_partial2 Hpartial2 _Hstep_cs;
      PS.simplify_turn;
      (* Synchronize with c's step. *)
      inversion Hstep_cs'; subst;
rename Hstep_cs' into _Hstep_cs';
      (* Invert second final partial step, remove contradictions. *)
      t_mergeable_states_step_partial2'
        Hpartial2' _Hstep_cs' Hsame_iface1 gps1 Hstack1 Hstack1' Hcomes_from Hics_pc2 Hics_pc2'
        Hstack1_hd Hcase1 gps1_hd; (* Hack variables introduced by the tactic. *)
      (* Solve legitimate goals. *)
      t_mergeable_states_step_trans_solve
        pc1 gps1 Hstack1 Hstack1' Hmem1 Hics_pc1' Hmem1' ics_pc1' Hcomp1'
        Hics_pc2' Hcomes_from Hmergeable_ifaces Hcc1' Hpc1 Hpc1c' Hpc1p
        HBnz1 HJal1 HJump1. (* Hack variables. *)
  Qed.

  Ltac t_mergeable_states_step_CS_solve
       Hmem1 Hstack1 Hcomes_from Hics_pc1' Hmem1' ics_pc1' pc1 Hpc1 Hcc1' Hcomp1'
       gps1 Hstack1' Hics_pc2' Hics_pc2 ics_regs1' regs1 c' Hsame_iface1 ics_mem1
       mem1 Hsame_iface2 :=
    (* Explicit unfolding. *)
    unfold PS.unpartialize;
    (* Stack and memory simplifications. *)
    try rewrite <- Hmem1;
    try rewrite <- Hstack1;
    erewrite (PS.merge_stacks_partition
                (mergeable_interfaces_sym _ _ mergeable_interfaces)
                Hcomes_from);
    erewrite (PS.merge_memories_partition
                (mergeable_interfaces_sym _ _ mergeable_interfaces)
                Hcomes_from);
    (* Specialized memory rewrites for store and alloc. *)
    try match goal with
    | Hop : executing _ ?PC (IStore _ _),
      Hcomp : Pointer.component ?PTR = Pointer.component ?PC,
      Hstore : Memory.store ?MEM1 ?PTR _ = Some ?MEM2
      |- _ =>
      rewrite <- Hcomp in Hics_pc1';
      rewrite -> (program_store_to_partialized_memory Hics_pc1' Hstore) in Hmem1'
    end;
    try match goal with
    | Hop : executing _ ?PC (IAlloc _ _),
      Halloc : Memory.alloc ?MEM1 (Pointer.component ?PTR) _ = Some (?MEM2, _)
      |- _ =>
      rewrite -> (program_allocation_to_partialized_memory Hics_pc1' Halloc) in Hmem1'
    end;
    (* Specialized stack rewrites for call and return. *)
    try match goal with
    | Hcomp : Pointer.component ics_pc1' = Pointer.component pc1
      |- CS.step _ _ [ECall _ _ _ _] _
      =>
      mergeable_step_call_stack Hpc1 Hcc1' Hcomp1' pc1;
      rewrite Hcomp
    end;
    try match goal with
    | Hcomp1 : Pointer.component ics_pc1' = Pointer.component pc1,
      Hcomp2 : Pointer.component ?ICS_PC2' = Pointer.component _
      |- CS.step _ _ [ERet _ _ _] _
      =>
      destruct gps1 as [| gps1_hd gps1]; [now inversion Hstack1' | ];
      inversion Hstack1 as [[Hstack1_hd Htmp]]; clear Hstack1; rename Htmp into Hstack1;
      inversion Hstack1' as [[Hstack1'_hd Htmp]]; clear Hstack1'; rename Htmp into Hstack1';
      rewrite Hcomp1;
      ( (* Return to program component. *)
        (rewrite Hcomp2;
         pose proof PS.ptr_within_partial_frame_inv_2 (eq_sym Hstack1_hd) Hics_pc2;
         subst gps1_hd)
      || (* Return to context component. *)
        (pose proof PS.ptr_within_partial_frame_inv_2 (eq_sym Hstack1'_hd) Hics_pc2';
         subst gps1_hd)
      );
      erewrite (PS.merge_stacks_partition_cons
                  (mergeable_interfaces_sym _ _ mergeable_interfaces)
                  Hcomes_from)
    end;
    (* Stack and memory rewrites, then solve goal. *)
    rewrite <- Hmem1';
    try rewrite <- Hstack1';
    try rewrite (PS.merge_stacks_partition
                   (mergeable_interfaces_sym _ _ mergeable_interfaces)
                   Hcomes_from);
    try erewrite (PS.merge_memories_partition
                    (mergeable_interfaces_sym _ _ mergeable_interfaces)
                    Hcomes_from);
    (* Register rewrites for context calls and returns. *)
    try match goal with
    | Hstep : CS.step _ _ [_] _
      |- _ =>
      assert (Register.invalidate ics_regs1' = Register.invalidate regs1)
        as Hregs
        by (apply Register.invalidate_eq; congruence);
      rewrite Hregs
    end;
    (* Apply CS lemma and prove special-case side conditions. *)
    CS_step_of_executing' (program_link p c');
    try eassumption;
    try reflexivity;
    try congruence; (* (Used for context component return.) *)
    try match goal with
    | Hlabel : find_label_in_component _ _ _ = _
      |- find_label_in_component _ _ _ = _
      =>
      rewrite find_label_in_component_program_link_left; try assumption;
      rewrite find_label_in_component_program_link_left in Hlabel; try assumption;
      try eassumption;
      now rewrite <- Hsame_iface1 in Hpc1
    end;
    try match goal with
    | Hlabel : find_label_in_procedure _ _ _ = _
      |- find_label_in_procedure _ _ _ = _
      =>
      rewrite find_label_in_procedure_program_link_left; try assumption;
      rewrite find_label_in_procedure_program_link_left in Hlabel; try assumption;
      try eassumption;
      now rewrite <- Hsame_iface1 in Hpc1
    end;
    try match goal with
    | Hload : Memory.load ics_mem1 ?PTR = Some ?V
      |- Memory.load mem1 ?PTR = Some ?V
      =>
      symmetry in Hmem1;
      destruct PTR as [[C b] o]; simpl in *; subst;
      eapply program_load_in_partialized_memory_strong;
      eassumption
    end;
    (* (Program component call.) *)
    try match goal with
    | Hentry : EntryPoint.get _ _ _ = _
      |- EntryPoint.get _ _ _ = _
      =>
      rewrite genv_entrypoints_program_link_left; try assumption;
      rewrite genv_entrypoints_program_link_left in Hentry; try assumption;
      now rewrite Hsame_iface1
    end;
    (* (Context component call.) *)
    try match goal with
    | Hentry : EntryPoint.get _ _ _ = Some ?B
      |- EntryPoint.get _ _ _ = Some ?B
      =>
      rewrite (program_linkC wf1 wf2 linkability);
      rewrite genv_entrypoints_program_link_left; try assumption;
        [| now apply linkable_sym | now apply linkable_mains_sym];
      rewrite genv_entrypoints_program_link_left in Hentry; try assumption;
      now rewrite Hsame_iface2
    end;
    try match goal with
    | Himport : imported_procedure _ ?C _ _
      |- imported_procedure _ ?C _ _
      =>
      rewrite imported_procedure_unionm_left; try assumption;
      rewrite imported_procedure_unionm_left in Himport; try assumption;
      now rewrite Hsame_iface1
    end;
    try match goal with
    | Hstore : Memory.store ics_mem1 _ _ = Some _,
      Hcomp : Pointer.component _ = Pointer.component pc1
      |- Memory.store _ _ _ = Some _
      =>
      rewrite <- (PS.merge_memories_partition
                    (mergeable_interfaces_sym _ _ mergeable_interfaces)
                    Hcomes_from)
              at 1;
      rewrite -> Hmem1;
      rewrite <- Hcomp in Hpc1;
      apply (partialize_program_store Hpc1) in Hstore;
      apply unpartialize_program_store;
      now apply Hstore
    end;
    try match goal with
    | Halloc : Memory.alloc ics_mem1 _ _ = Some (_, _)
      |- Memory.alloc mem1 _ _ = Some (_, _)
      =>
      rewrite <- (PS.merge_memories_partition
                    (mergeable_interfaces_sym _ _ mergeable_interfaces)
                    Hcomes_from)
              at 1;
      apply (partialize_program_alloc Hpc1) in Halloc;
      rewrite <- Hmem1 in Halloc;
      apply unpartialize_program_alloc;
      now apply Halloc
    end;
    (* Finish goal. *)
    apply execution_invariant_to_linking with (c1 := c'); eassumption.

  Lemma mergeable_states_step_CS_program : forall s1 s1' s2 s2' t,
    PS.is_program_component s1 (prog_interface c) ->
    PS.mergeable_states (prog_interface c) (prog_interface p) s1 s1' ->
    PS.step p (prog_interface c) (prepare_global_env p) s1 t s2 ->
    PS.step c (prog_interface p) (prepare_global_env c) s1' t s2'->
    CS.step (prepare_global_env (program_link p c))
            (PS.unpartialize (PS.merge_partial_states s1 s1')) t
            (PS.unpartialize (PS.merge_partial_states s2 s2')).
  Proof.
    t_mergeable_states_step_intros.
    (* Case analysis on p's step. *)
    inversion Hstep_cs; subst;
rename Hstep_cs into _Hstep_cs;
      (* Invert first final partial step. *)
      t_mergeable_states_step_partial2 Hpartial2 _Hstep_cs;
      PS.simplify_turn;
      (* Synchronize with c's step. *)
      inversion Hstep_cs'; subst;
rename Hstep_cs' into _Hstep_cs';
      (* Invert second final partial step, remove contradictions. *)
      t_mergeable_states_step_partial2'
        Hpartial2' _Hstep_cs' Hsame_iface1 gps1 Hstack1 Hstack1' Hcomes_from Hics_pc2 Hics_pc2'
        Hstack1_hd Hcase1 gps1_hd; (* Hack variables introduced by the tactic. *)
      (* Solve legitimate goals. *)
      t_mergeable_states_step_CS_solve
        Hmem1 Hstack1 Hcomes_from Hics_pc1' Hmem1' ics_pc1' pc1 Hpc1 Hcc1' Hcomp1'
        gps1 Hstack1' Hics_pc2' Hics_pc2 ics_regs1' regs1 c' Hsame_iface1 ics_mem1
        mem1 Hsame_iface2.
  Qed.
End MergeableStatesProgram.

Section MultiSemantics.
  Variables p c: program.

  Hypothesis wf1 : well_formed_program p.
  Hypothesis wf2 : well_formed_program c.

  Hypothesis main_linkability: linkable_mains p c.
  Hypothesis linkability: linkable (prog_interface p) (prog_interface c).

  Hypothesis mergeable_interfaces:
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Let prog := program_link p c.

  Hypothesis prog_is_closed : closed_program prog.

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
    intros ips1 ips2 HPSini1 HPSini2.
    inversion HPSini1
      as [p' ics1 ? Hiface1 _ Hwf1 Hlinkable1 Hmains1 Hpartial1 HCSini1];
      subst.
    inversion HPSini2
      as [c' ics2 ? Hiface2 _ Hwf2 Hlinkable2 Hmains2 Hpartial2 HCSini2];
      subst.
    unfold CS.initial_state in HCSini1, HCSini2.
    unfold CS.initial_state.
    (* Inline initial states in Hpartial hypotheses; work on those from there. *)
    subst ics1 ics2.
    simpl in Hpartial1, Hpartial2. simpl.
    (* Extract mains compatibility information before case analysis. *)
    inversion main_linkability as [Hmainpc];
      inversion Hmains1 as [Hmainpp'];
      inversion Hmains2 as [Hmaincc'].
    destruct (prog_main p) as [mainp |] eqn:Hmainp;
      destruct (prog_main c) as [mainc |] eqn:Hmainc;
      destruct (prog_main p') as [mainp' | ] eqn:Hmainp';
      destruct (prog_main c') as [mainc' | ] eqn:Hmainc';
      try discriminate;
      simpl in Hpartial1, Hpartial2; simpl.
    (* In the remaining cases:
        - The "correct" ones (in which one of p and c and their counterpart
          have mains) are solved by composability of initial states.
        - Cases where both p and c have no mains are ruled out by closedness
          of their linking.
        - Cases where the indirect "matching mains" condition on either p and its
          counterpart or c and its counterpart is not respected are ruled out by
          the strong well-formedness of programs.
       There is overlap among the two classes of contradictions.
       RB: NOTE: It is easy to use tactics to refactor contradictory cases, and
       symmetry to refactor the two proper cases. *)
    - rewrite (CS.initial_machine_state_after_linking
                 _ _ wf1 wf2 linkability prog_is_closed).
      assert (Hclosed1 : closed_program (program_link p p')).
      {
        (* RB: TODO: Refactor this (and instance below) into lemma. *)
        constructor.
        - simpl. rewrite Hiface1. now inversion prog_is_closed.
        - destruct (wfprog_main_existence wf1 Hmainp)
            as [main_procs [Hmain_procs Hinmain_procs]].
          exists mainp, main_procs. split; [| split].
          + simpl. now rewrite Hmainp.
          + simpl. now rewrite unionmE Hmain_procs.
          + assumption.
      }
      rewrite (CS.initial_machine_state_after_linking
                 _ _ wf1 Hwf1 Hlinkable1 Hclosed1) in Hpartial1.
      assert (Hclosed2 : closed_program (program_link c c')).
      {
        (* RB: TODO: Refactor this (and instance above) into lemma. *)
        constructor.
        - simpl. rewrite Hiface2.
          inversion linkability as [_ Hdisjoint].
          rewrite <- (unionmC Hdisjoint).
          now inversion prog_is_closed.
        - destruct (wfprog_main_existence Hwf2 Hmainc')
            as [main_procs [Hmain_procs Hinmain_procs]].
          exists mainc', main_procs. split; [| split].
          + simpl. now rewrite Hmainc Hmainc'.
          + simpl.
            (* Here, the easiest solution is to commute c' to the front. *)
            inversion Hlinkable2 as [_ Hdisjoint].
            rewrite (wfprog_defined_procedures wf2)
                    (wfprog_defined_procedures Hwf2) in Hdisjoint.
            rewrite (unionmC Hdisjoint).
            now rewrite unionmE Hmain_procs.
          + assumption.
      }
      rewrite (CS.initial_machine_state_after_linking
                 _ _ wf2 Hwf2 Hlinkable2 Hclosed2) in Hpartial2.
      inversion Hpartial1 as [? ? ? ? ? ? Hcomp1 | ? ? ? ? ? ? Hcomp1]; subst;
        inversion Hpartial2 as [? ? ? ? ? ? Hcomp2 | ? ? ? ? ? ? Hcomp2]; subst;
        PS.simplify_turn.
      (* RB: TODO: The structure revealed below is also subject to refactoring. *)
      + inversion wf1 as [_ _ _ _ _ _ [_ Hcontra]].
        rewrite Hmainp in Hcontra. specialize (Hcontra (eq_refl _)).
        rewrite Hcontra in Hcomp2.
        discriminate.
      + (* Expose memory structures and rewrite. *)
        unfold merge_memories, to_partial_memory.
        rewrite <- Hiface1,
                -> filterm_union (**), <- domm_prepare_procedures_memory,
                -> fdisjoint_filterm_full (**), -> (fdisjoint_filterm_empty (eq_refl _)),
                -> unionm0,
                <- Hiface2,
                -> filterm_union (**), <- domm_prepare_procedures_memory,
                -> fdisjoint_filterm_full (**), -> (fdisjoint_filterm_empty (eq_refl _)),
                -> unionm0.
        (* Expose main block arithmetic, simplify and close. *)
        unfold CS.prog_main_block.
        rewrite -> Hmainp, -> Hmainc, -> Hmainp'.
        reflexivity.
        (* Discharge disjointness goals generated by memory rewrites. *)
        * rewrite -> !domm_prepare_procedures_memory. now inversion Hlinkable2.
        * rewrite -> !domm_prepare_procedures_memory. now inversion Hlinkable2.
        * rewrite -> !domm_prepare_procedures_memory. now inversion Hlinkable1.
        * rewrite -> !domm_prepare_procedures_memory. now inversion Hlinkable1.
      + inversion wf2 as [_ _ _ _ _ _ [Hcontra _]].
        specialize (Hcontra Hcomp1). rewrite Hmainc in Hcontra.
        discriminate.
      + (* The usual funky mixture of SSR rewrites in what would normally be
           applications. *)
        pose proof domm_partition_notin _ _ mergeable_interfaces as Hcontra.
        specialize (Hcontra Component.main).
        rewrite Hcomp1 Hcomp2 in Hcontra.
        specialize (Hcontra (eq_refl _)).
        discriminate.
    - rewrite (prog_main_none_same_interface Hwf2 wf1 Hiface2 Hmainc')
        in Hmainp.
      discriminate.
    - (* By composability of [prepare_], like above.
         RB: TODO: Refactor. This is the symmetric of the above. *)
      rewrite (CS.initial_machine_state_after_linking
                 _ _ wf1 wf2 linkability prog_is_closed).
      assert (Hclosed1 : closed_program (program_link p p')).
      {
        (* RB: TODO: Refactor this (and instance below) into lemma. *)
        constructor.
        - simpl. rewrite Hiface1. now inversion prog_is_closed.
        - destruct (wfprog_main_existence Hwf1 Hmainp')
            as [main_procs [Hmain_procs Hinmain_procs]].
          exists mainp', main_procs. split; [| split].
          + simpl. now rewrite Hmainp Hmainp'.
          + simpl.
            (* Here, the easiest solution is to commute c' to the front. *)
            inversion Hlinkable1 as [_ Hdisjoint].
            rewrite (wfprog_defined_procedures wf1)
                    (wfprog_defined_procedures Hwf1) in Hdisjoint.
            rewrite (unionmC Hdisjoint).
            now rewrite unionmE Hmain_procs.
          + assumption.
      }
      rewrite (CS.initial_machine_state_after_linking
                 _ _ wf1 Hwf1 Hlinkable1 Hclosed1) in Hpartial1.
      assert (Hclosed2 : closed_program (program_link c c')).
      {
        (* RB: TODO: Refactor this (and instance above) into lemma. *)
        constructor.
        - simpl. rewrite Hiface2.
          inversion linkability as [_ Hdisjoint].
          rewrite <- (unionmC Hdisjoint).
          now inversion prog_is_closed.
        - destruct (wfprog_main_existence wf2 Hmainc)
            as [main_procs [Hmain_procs Hinmain_procs]].
          exists mainc, main_procs. split; [| split].
          + simpl. now rewrite Hmainc.
          + simpl. now rewrite unionmE Hmain_procs.
          + assumption.
      }
      rewrite (CS.initial_machine_state_after_linking
                 _ _ wf2 Hwf2 Hlinkable2 Hclosed2) in Hpartial2.
      inversion Hpartial1 as [? ? ? ? ? ? Hcomp1 | ? ? ? ? ? ? Hcomp1]; subst;
        inversion Hpartial2 as [? ? ? ? ? ? Hcomp2 | ? ? ? ? ? ? Hcomp2]; subst;
        PS.simplify_turn.
      (* RB: TODO: The structure revealed below is also subject to refactoring. *)
      + inversion wf2 as [_ _ _ _ _ _ [_ Hcontra]].
        rewrite Hmainc in Hcontra. specialize (Hcontra (eq_refl _)).
        rewrite Hcontra in Hcomp1.
        discriminate.
      + inversion wf1 as [_ _ _ _ _ _ [Hcontra _]].
        specialize (Hcontra Hcomp2). rewrite Hmainp in Hcontra.
        discriminate.
      + (* Expose memory structures and rewrite. *)
        unfold merge_memories, to_partial_memory.
        rewrite <- Hiface1,
                -> filterm_union (**), <- domm_prepare_procedures_memory,
                -> fdisjoint_filterm_full (**), -> (fdisjoint_filterm_empty (eq_refl _)),
                -> unionm0,
                <- Hiface2,
                -> filterm_union (**), <- domm_prepare_procedures_memory,
                -> fdisjoint_filterm_full (**), -> (fdisjoint_filterm_empty (eq_refl _)),
                -> unionm0.
        (* Expose main block arithmetic, simplify and close. *)
        unfold CS.prog_main_block.
        rewrite -> Hmainp, -> Hmainc, -> Hmainc'.
        rewrite Nat.add_0_r.
        reflexivity.
        (* Discharge disjointness goals generated by memory rewrites. *)
        * rewrite -> !domm_prepare_procedures_memory. now inversion Hlinkable2.
        * rewrite -> !domm_prepare_procedures_memory. now inversion Hlinkable2.
        * rewrite -> !domm_prepare_procedures_memory. now inversion Hlinkable1.
        * rewrite -> !domm_prepare_procedures_memory. now inversion Hlinkable1.
      + (* The usual funky mixture of SSR rewrites in what would normally be
           applications. *)
        pose proof domm_partition_notin _ _ mergeable_interfaces as Hcontra.
        specialize (Hcontra Component.main).
        rewrite Hcomp1 Hcomp2 in Hcontra.
        specialize (Hcontra (eq_refl _)).
        discriminate.
    - rewrite (prog_main_none_same_interface Hwf1 wf2 Hiface1 Hmainp')
        in Hmainc.
      discriminate.
    - rewrite (prog_main_none_same_interface wf1 Hwf2 (eq_sym Hiface2) Hmainp)
        in Hmainc'.
      discriminate.
    - rewrite (prog_main_none_same_interface wf2 Hwf1 (eq_sym Hiface1) Hmainc)
        in Hmainp'.
      discriminate.
    - rewrite (prog_main_none_same_interface wf1 Hwf2 (eq_sym Hiface2) Hmainp)
        in Hmainc'.
      discriminate.
    - (* Contra: by prog_is_closed, there should be a main. *)
      inversion prog_is_closed as [_ [mainP [_ [HmainP _]]]].
      simpl in HmainP. rewrite Hmainp Hmainc in HmainP.
      discriminate.
  Qed.

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
      + exact (linkable_mains_empty_prog prog).
      + inversion H0 as [? ? ? ? ? ? ? Hmains1]; subst.
        inversion H1 as [? ? ? ? ? ? ? Hmains2]; subst.
        inversion H6; subst; inversion H12; subst; PS.simplify_turn.
        * (* contra *)
          (* RB: TODO: Extract and simplify patterns if inversion of mergeable_states
             followed by the two partial_state: four standard cases, of which two are
             contradictory. More instances of this below. *)
          inversion H as [? ? ? Hmerge_ifaces Hfrom_initial Hpartial1 Hpartial2]; subst.
          inversion Hpartial1 as [? ? ? ? ? ? Hpc1 |]; subst.
          inversion Hpartial2 as [? ? ? ? ? ? Hpc2 |]; subst.
          PS.simplify_turn.
          apply (PS.domm_partition Hmerge_ifaces Hfrom_initial) in Hpc2.
          rewrite Hpc2 in Hpc1.
          discriminate.
        * econstructor.
          ** PS.simplify_turn.
             rewrite mem_domm. auto.
          ** simpl.
             rewrite domm0. simpl.
             unfold to_partial_memory. rewrite filterm_identity.
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
             rewrite domm0. simpl.
             unfold to_partial_memory. rewrite filterm_identity.
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
          apply (domm_partition_notin _ _ Hmerge_ifaces) in Hpc2.
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

  (* TODO: Compare with old definitions/proof, try to reproduce structure.
     Consider the use (as in the old proof: which, where) of partition lemmas. *)
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
      [ now destruct (PS.domm_partition_in_neither Hmergeable_ifaces Hcomes_from Hpc1 Hpc2)
      |
      |
      | now destruct (PS.domm_partition_in_both Hmergeable_ifaces Hcc1 Hcc2) ].
    - eapply PS.final_state_program with
        (ics := (PS.unpartialize_stack
                   (PS.merge_stacks (PS.to_partial_stack gps (domm (prog_interface c)))
                                    (PS.to_partial_stack gps (domm (prog_interface p)))),
                 merge_memories
                   (to_partial_memory mem (domm (prog_interface c)))
                   (to_partial_memory mem (domm (prog_interface p))),
                 regs, pc))
        (p' := empty_prog).
      + reflexivity.
      + apply linking_well_formedness; assumption.
      + now apply empty_prog_is_well_formed.
      + apply linkable_emptym. now apply linkability.
      + exact (linkable_mains_empty_prog prog).
      + PS.simplify_turn. now rewrite mem_domm.
      + constructor.
        * PS.simplify_turn.
          now rewrite mem_domm.
        * unfold to_partial_memory.
          by rewrite domm0 filterm_predT.
        * rewrite domm0 (PS.merge_stacks_partition Hmergeable_ifaces Hcomes_from).
          by rewrite (PS.merge_stacks_partition_emptym Hmergeable_ifaces Hcomes_from).
      + rewrite linking_empty_program.
        inversion Hfinal1
          as [p' ics ? Hsame_iface' _ Hwf' Hlinkable' Hmains' Hnotin' Hpartial' Hfinal' | ? Hcontra];
          subst;
          PS.simplify_turn;
          last by rewrite Hcontra in Hpc1.
        inversion Hpartial'; subst.
        inversion Hfinal'; subst.
        eapply (@execution_invariant_to_linking _ _ _ _ _ Hlinkable'); assumption.
    - (* The second case is symmetric *)
      eapply PS.final_state_program with
        (ics := (PS.unpartialize_stack
                   (PS.merge_stacks (PS.to_partial_stack gps (domm (prog_interface c)))
                                    (PS.to_partial_stack gps (domm (prog_interface p)))),
                 merge_memories
                   (to_partial_memory mem (domm (prog_interface c)))
                   (to_partial_memory mem (domm (prog_interface p))),
                 regs, pc))
        (p' := empty_prog).
      + reflexivity.
      + apply linking_well_formedness; assumption.
      + now apply empty_prog_is_well_formed.
      + apply linkable_emptym. now apply linkability.
      + exact (linkable_mains_empty_prog prog).
      + PS.simplify_turn. now rewrite mem_domm.
      + constructor.
        * PS.simplify_turn.
          now rewrite mem_domm.
        * rewrite domm0.
          unfold to_partial_memory. rewrite filterm_predT.
          reflexivity.
        * rewrite domm0.
          rewrite (PS.merge_stacks_partition Hmergeable_ifaces Hcomes_from).
          rewrite (PS.merge_stacks_partition_emptym Hmergeable_ifaces Hcomes_from).
          reflexivity.
      + rewrite linking_empty_program.
        inversion Hfinal2
          as [p' ics ? Hsame_iface' _ Hwf' Hlinkable' Hmains' Hnotin' Hpartial' Hfinal' | ? Hcontra];
          subst;
          PS.simplify_turn;
          last by destruct (PS.domm_partition_in_both Hmergeable_ifaces Hcc1 Hcontra).
        inversion Hpartial'; subst.
        inversion Hfinal'; subst.
        unfold prog. rewrite (program_linkC wf1 wf2 linkability).
        pose proof linkable_sym linkability as linkability'.
        assert (main_linkability_sym := main_linkability).
        apply linkable_mains_sym in main_linkability_sym.
        eapply (@execution_invariant_to_linking _ _ _ _ _ Hlinkable'); assumption.
  Qed.

  (* RB: TODO: Add side conditions (well-formed programs, linkable interfaces,
     etc. *)
  Lemma mergeable_states_merge :
    forall s s',
      PS.mergeable_states (prog_interface c) (prog_interface p) s s' ->
      PS.merge_partial_states s s' =
      PS.mergeable_states_state s s'.
  Proof.
    intros s1 s2 Hmerge.
    inversion Hmerge as [ics ? ? Hifaces Hcomes_from Hpartial1 Hpartial2];
      subst.
    unfold PS.merge_partial_states, PS.mergeable_states_state,
           PS.mergeable_states_stack, PS.mergeable_states_memory,
           PS.mergeable_states_regs, PS.mergeable_states_pc.
    inversion Hpartial1 as [gps1 ? mem1 ? regs1 pc1 Hcomp1 |
                            gps1 ? mem1 ? regs1 pc1 Hcomp1];
      subst;
      inversion Hpartial2 as [gps2 ? mem2 ? regs2 pc2 Hcomp2 |
                              gps2 ? mem2 ? regs2 pc2 Hcomp2];
      subst;
      PS.simplify_turn.
    - exfalso. eapply PS.domm_partition_in_neither; eassumption.
    - reflexivity.
    - reflexivity.
    - exfalso. eapply PS.domm_partition_in_both; eassumption.
  Qed.

  (* A special case of a more general property on [PS.partial_state emptym] that
     would relate a CS state to its injection to a PS state. *)
  Lemma mergeable_states_partial_state_emptym :
    forall s s',
      PS.mergeable_states (prog_interface c) (prog_interface p) s s' ->
      PS.partial_state emptym
                       (PS.unpartialize (PS.merge_partial_states s s'))
                       (PS.merge_partial_states s s').
  Proof.
    intros s1 s2 Hmerge.
    inversion Hmerge as [ics ? ? Hifaces Hcomes_from Hpartial1 Hpartial2];
      subst.
    rewrite (mergeable_states_merge Hmerge).
    apply PS.ProgramControl.
    - PS.simplify_turn. now rewrite domm0 in_fset0.
    - unfold PS.mergeable_states_memory, to_partial_memory.
      rewrite fdisjoint_filterm_full; first reflexivity.
      rewrite domm0. now apply fdisjoints0.
    - unfold PS.mergeable_states_stack.
      rewrite domm0.
      rewrite PS.to_partial_stack_unpartialize_identity; first reflexivity.
      apply PS.merged_stack_has_no_holes.
      now apply (PS.mergeable_states_stacks Hmerge).
  Qed.

  (* RB: TODO: This lemma is related to the ones below, on mergeable states, but
     should also be relocated once the sections are finished.
     Also, for the sake of findability, consistently use shorthand notation
     (involving PS.sem) or its extension into PS.step et al.). *)
  Ltac t_mergeable_states_step_E0
       HCSpartial2 HCSstep Hcomp1' Hmem1 Hstk1 Hcomp pc :=
    inversion HCSpartial2 as [? ? ? ? ? ? Hcomp2 | ? ? ? ? ? ? Hcomp2]; subst;
      [| (exfalso;
          PS.simplify_turn;
          rewrite (CS.silent_step_preserves_component _ _ _ HCSstep) in Hcomp1';
          exfalso; eapply PS.domm_partition_in_notin; eassumption)
      ];
    [rewrite <- Pointer.inc_preserves_component];
    [try rewrite <- Hmem1];
    [rewrite <- Hstk1];
    [match goal with
     | |- PS.mergeable_states
            _ _ (PS.CC (_, ?GPS1, ?MEM1)) (PS.PC (?GPS2, ?MEM2, ?REGS, ?PC))
       =>
       apply PS.mergeable_states_intro
         with (ics := (PS.unpartialize_stack (PS.merge_stacks GPS1 GPS2),
                       merge_memories MEM1 MEM2, REGS, PC))
     end];
    [ constructor; try easy;
      [ now apply linkable_sym
      | pose proof (cprog_closed_interface prog_is_closed) as Hclosed;
        rewrite unionmC; first assumption;
        rewrite fdisjointC; now inversion linkability
      ]
    | eapply PS.comes_from_initial_state_step_trans; try eassumption;
      [ simpl; PS.simplify_turn; now rewrite_if_else_negb
      | try rewrite <- Hmem1;
        [rewrite <- Hstk1];
        [simpl];
        [simpl]; [PS.simplify_turn]; [rewrite_if_else_negb];
        [erewrite PS.to_partial_stack_merge_stack_right]; [| easy | eassumption];
        (* RB: TODO: Here and in other instances, try distributing
           PS.partial_memory over appropriate instances of PS.merge_memories
           for a more uniform treatment of the cases. Note also this
           case-specific treatment of memories reoccurs in three sub-goals of
           this case analysis. *)
        [match goal with
         | Hop : executing _ pc (IAlloc _ _)
           |- _ =>
           erewrite PS.to_partial_memory_merge_partial_memories_right_2; try eassumption
         | Hop : executing _ pc (IStore _ _)
           |- _ =>
           erewrite PS.to_partial_memory_merge_partial_memories_right_2; try eassumption
         | |- _ =>
           erewrite PS.to_partial_memory_merge_memory_right; [| easy | eassumption]
         end];
        [reflexivity]
      ]
    | try match goal with
      | Hlabel : find_label_in_component _ pc _ = Some _
        |- _ =>
        rewrite -> Pointer.inc_preserves_component,
                -> (find_label_in_component_1 _ _ _ _ Hlabel);
        rewrite (find_label_in_component_1 _ _ _ _ Hlabel) in Hcomp
      | Hlabel : find_label_in_procedure _ pc _ = Some _
        |- _ =>
        rewrite -> Pointer.inc_preserves_component,
                -> (find_label_in_procedure_1 _ _ _ _ Hlabel);
        rewrite (find_label_in_procedure_1 _ _ _ _ Hlabel) in Hcomp
      | Hop : executing _ pc (IJump _),
        Heq : Pointer.component _ = Pointer.component pc
        |- _ =>
        rewrite -> Pointer.inc_preserves_component,
                <- Heq;
        rewrite <- Heq in Hcomp
      end;
      [constructor]; try reflexivity;
      [   assumption
        || now rewrite Pointer.inc_preserves_component
      | match goal with
        | Hop : executing _ pc (IAlloc _ _)
          |- _ =>
          erewrite PS.to_partial_memory_merge_partial_memories_left_2;
            try eassumption; reflexivity
        | Hop : executing _ pc (IStore _ _)
          |- _ =>
          erewrite PS.to_partial_memory_merge_partial_memories_left_2;
            try eassumption; reflexivity
        | |- _ =>
          erewrite PS.to_partial_memory_merge_memory_left; try easy; eassumption
        end
      | erewrite PS.to_partial_stack_merge_stack_left; try easy; eassumption
      ]
    | constructor; try easy;
      [ match goal with
        | Hop : executing _ pc (IAlloc _ _)
          |- _ =>
          erewrite PS.to_partial_memory_merge_partial_memories_right_2;
          try eassumption; reflexivity
        | Hop : executing _ pc (IStore _ _)
          |- _ =>
          erewrite PS.to_partial_memory_merge_partial_memories_right_2;
          try eassumption; reflexivity
        | |- _ =>
          erewrite PS.to_partial_memory_merge_memory_right; try easy; eassumption
        end
      | erewrite PS.to_partial_stack_merge_stack_right; try easy; eassumption
      ]
    ].

  Lemma mergeable_states_step_E0 :
    forall s s1 s2,
      PS.mergeable_states (prog_interface c) (prog_interface p) s s1 ->
      PS.step c (prog_interface p) (prepare_global_env c) s1 E0 s2 ->
      PS.mergeable_states (prog_interface c) (prog_interface p) s s2.
  Proof.
    intros s s1 s2 Hmerge Hstep.
    inversion Hmerge as [ics ? ? Hmerge_ifaces Hcomes_from Hpartial Hpartial1]; subst.
    inversion Hstep
      as [p' ? ? ? ics1 ics2
          Hsame_iface1 _ Hwf1 Hlinkable1 Hmains1 HCSstep HCSpartial1 HCSpartial2];
      subst.
    inversion Hpartial1 as [ ? ? ? ? ? ? Hcomp1' | ? ? ? ? ? ? Hcomp1']; subst;
      inversion Hpartial as [? ? ? ? ? ? Hcomp | ? ? ? ? ? ? Hcomp]; subst;
      PS.simplify_turn;
      [ exfalso; eapply PS.domm_partition_in_neither; eassumption | |
      | exfalso; eapply PS.domm_partition_in_both; eassumption].
    - (* On the program. *)
      inversion HCSpartial1 as [? ? ? ? ? ? Hcomp1 Hmem1 Hstk1 |]; subst.
      inversion HCSstep; subst;
        now t_mergeable_states_step_E0 HCSpartial2 HCSstep Hcomp1' Hmem1 Hstk1 Hcomp pc.
    - (* On the context, this is straightforward. *)
      match goal with
      | Hstep : PS.step _ _ _ ?S1 E0 s2
        |- _ =>
        assert (Hcc1 : PS.is_context_component S1 (prog_interface p))
          by assumption
      end.
      pose proof PS.context_epsilon_step_is_silent Hcc1 Hstep; subst s2.
      econstructor; try eassumption.
  Qed.

  Lemma mergeable_states_star_E0 :
    forall s s1 s2,
      PS.mergeable_states (prog_interface c) (prog_interface p) s s1 ->
      Star (PS.sem c (prog_interface p)) s1 E0 s2 ->
      PS.mergeable_states (prog_interface c) (prog_interface p) s s2.
  Proof.
    simpl.
    intros s s1 s2 Hmerge Hstar.
    apply star_iff_starR in Hstar.
    remember E0 as t eqn:Ht. revert Ht.
    induction Hstar as [| ? ? ? ? ? ? ? IHHstar Hstep];
      subst;
      intros Ht.
    - assumption.
    - apply Eapp_E0_inv in Ht. destruct Ht; subst t1 t2.
      specialize (IHHstar Hmerge (eq_refl _)).
      exact (mergeable_states_step_E0 IHHstar Hstep).
  Qed.

  Corollary mergeable_states_step_trans : forall s1 s1' s2 s2' t,
    PS.mergeable_states (prog_interface c) (prog_interface p) s1 s1' ->
    PS.step p (prog_interface c) (prepare_global_env p) s1 t s2 ->
    PS.step c (prog_interface p) (prepare_global_env c) s1' t s2' ->
    PS.mergeable_states (prog_interface c) (prog_interface p) s2 s2'.
  Proof.
    intros s1 s1' s2 s2' t Hmergeable Hstep Hstep'.
    destruct (PS.is_program_component s1 (prog_interface c)) eqn:Hpcomp.
    - eapply mergeable_states_step_trans_program; eassumption.
    - apply PS.mergeable_states_sym;
        [assumption | assumption | now apply linkable_sym |].
      eapply mergeable_states_step_trans_program.
      + now apply linkable_mains_sym.
      + eapply PS.mergeable_states_context_to_program;
          [eassumption |].
        unfold PS.is_program_component in Hpcomp.
        now apply negb_false_iff in Hpcomp.
      + eapply PS.mergeable_states_sym; eassumption.
      + eassumption.
      + eassumption.
  Qed.

  Corollary mergeable_states_step_CS : forall s1 s1' s2 s2' t,
    PS.mergeable_states (prog_interface c) (prog_interface p) s1 s1' ->
    PS.step p (prog_interface c) (prepare_global_env p) s1 t s2 ->
    PS.step c (prog_interface p) (prepare_global_env c) s1' t s2'->
    CS.step (prepare_global_env (program_link p c))
            (PS.unpartialize (PS.merge_partial_states s1 s1')) t
            (PS.unpartialize (PS.merge_partial_states s2 s2')).
  Proof.
    intros s1 s1' s2 s2' t Hmergeable1 Hstep Hstep'.
    destruct (PS.is_program_component s1 (prog_interface c)) eqn:Hpcomp.
    - eapply mergeable_states_step_CS_program; eassumption.
    - pose proof program_linkC wf1 wf2 linkability as HlinkC.
      assert (Hprog_is_closed := prog_is_closed);
        unfold prog in Hprog_is_closed; rewrite -> HlinkC in Hprog_is_closed.
      unfold PS.is_program_component in Hpcomp. apply negb_false_iff in Hpcomp.
      pose proof PS.mergeable_states_context_to_program Hmergeable1 Hpcomp
        as Hpcomp'.
      assert (Hmergeable1' := Hmergeable1);
        apply PS.mergeable_states_sym in Hmergeable1'; try assumption.
      pose proof mergeable_states_step_CS_program
           wf2 wf1
           (linkable_mains_sym main_linkability) (linkable_sym linkability)
           (mergeable_interfaces_sym _ _ mergeable_interfaces)
           Hpcomp' Hmergeable1' Hstep' Hstep
        as HCSstep.
      rewrite <- HlinkC in HCSstep.
      rewrite <- (PS.merge_partial_states_sym Hmergeable1) in HCSstep.
      pose proof mergeable_states_step_trans Hmergeable1 Hstep Hstep'
        as Hmergeable2.
      rewrite <- (PS.merge_partial_states_sym Hmergeable2) in HCSstep.
      exact HCSstep.
  Qed.

  (* RB: TODO: This result very likely belongs in PS. I am reusing the hypotheses
     in this section, but these should be pared down. *)
  Lemma mergeable_states_step : forall s1 s1' s2 s2' t,
    PS.mergeable_states (prog_interface c) (prog_interface p) s1 s1' ->
    PS.step p (prog_interface c) (prepare_global_env p) s1 t s2 ->
    PS.step c (prog_interface p) (prepare_global_env c) s1' t s2'->
    PS.step (program_link p c) emptym (prepare_global_env (program_link p c))
            (PS.merge_partial_states s1 s1') t
            (PS.merge_partial_states s2 s2').
  Proof.
    intros s1 s1' s2 s2' t Hmergeable1 Hstep Hstep'.
    pose proof mergeable_states_step_trans Hmergeable1 Hstep Hstep'
      as Hmergeable2.
    apply PS.partial_step
      with (p' := empty_prog)
           (ics := PS.unpartialize (PS.merge_partial_states s1 s1'))
           (ics' := PS.unpartialize (PS.merge_partial_states s2 s2')).
    - reflexivity.
    - now apply linking_well_formedness.
    - exact empty_prog_is_well_formed.
    - exact (linkable_emptym _ (proj1 linkability)).
    - now apply linkable_mains_empty_prog.
    - rewrite linking_empty_program. now apply mergeable_states_step_CS.
    - now apply mergeable_states_partial_state_emptym.
    - now apply mergeable_states_partial_state_emptym.
  Qed.

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

    inversion Hmatch as [ips1 ips2 Hmergeable]; subst.
    inversion Hstep as [? ? ips1' ? ips2' Hstep1 Hstep2]; subst.

    exists (PS.merge_partial_states ips1' ips2'). split.
    - exact (mergeable_states_step Hmergeable Hstep1 Hstep2).
    - constructor.
      exact (mergeable_states_step_trans Hmergeable Hstep1 Hstep2).
  Qed.

  Lemma star_simulation:
    forall ms t ms',
      Star msem ms t ms' ->
    forall ips,
      multi_match ms ips ->
    exists ips',
      Star (PS.sem prog emptym) ips t ips' /\ multi_match ms' ips'.
  Proof.
    intros ms t ms' Hstar.
    induction Hstar as [| ? ? ? ? ? ? H ? IHHstar]; subst.
    - eexists. split.
      + left.
      + auto.
    - intros ips Hmulti_match.
      destruct (lockstep_simulation H Hmulti_match) as [ips' [? H1]].
      destruct (IHHstar ips' H1) as [ips'' []].
      exists ips''. split.
      + eapply star_left; eauto.
      + auto.
  Qed.

  Theorem merged_prog_simulates_multisem:
    forward_simulation msem (PS.sem prog emptym).
  Proof.
    eapply forward_simulation_step.
    - apply multi_match_initial_states.
    - apply multi_match_final_states.
    - apply lockstep_simulation.
  Qed.

  (* RB: TODO: Move to CompCertExtensions, integrate in existing proofs. *)
  Lemma behavior_prefix_goes_initially_wrong_inv : forall t,
    behavior_prefix t (Goes_wrong E0) ->
    t = E0.
  Proof.
    intros t [beh Hbeh].
    destruct beh as [| | | tbeh];
      try discriminate.
    inversion Hbeh as [Happ].
    now destruct (Eapp_E0_inv _ _ (eq_sym Happ)).
  Qed.

  (* RB: TODO: To PS when done.
     A partial step, partialized on the empty interface (that is, a complete
     step in disguise) can be rearranged as two partial steps split along the
     lines of a pair of mergeable interfaces.
     Possible refactoring of CS.prog_main_block parts, see similar uses in
     initial_states_mergeability. Refactor symmetric sub-goals as well. *)
  Lemma initial_state_split :
    forall s1 s2,
      PS.initial_state p (prog_interface c) s1 ->
      PS.initial_state c (prog_interface p) s2 ->
      PS.mergeable_states (prog_interface c) (prog_interface p) s1 s2.
  Proof.
    intros s1 s2 Hini1 Hini2.
    apply PS.mergeable_states_intro with (ics := CS.initial_machine_state prog).
    - now apply mergeable_interfaces_sym.
    - unfold CS.comes_from_initial_state.
      destruct (cprog_main_existence prog_is_closed)
        as [main [main_procs [Hmain [Hprocs Hdomm]]]].
      exists prog, main, (CS.initial_machine_state prog), E0.
      split; [| split; [| split; [| split]]].
      + now apply linking_well_formedness.
      + assumption.
      + rewrite unionmC; first reflexivity.
        rewrite fdisjointC.
        now inversion linkability.
      + reflexivity.
      + now apply star_refl.
    - inversion Hini1
        as [p' ics ? Hiface _ Hwf1 Hlinkable1 Hmains1 Hpartial1 HCSini1];
        subst.
      assert (Hclosed : closed_program (program_link p p')).
      {
        (* Refactored for later sub-proofs. *)
        apply interface_preserves_closedness_r with (p2 := c); try easy.
        apply interface_implies_matching_mains; easy.
      }
      inversion Hpartial1 as [? ? ? ? ? ? Hcomp1 | ? ? ? ? ? ? Hcomp1]; subst;
        PS.simplify_turn.
      + rewrite CS.initial_machine_state_after_linking; try assumption.
        unfold CS.initial_state in HCSini1.
        rewrite CS.initial_machine_state_after_linking in HCSini1; try assumption.
        inversion HCSini1; subst.
        pose proof CS.prog_main_block_no_main _ wf2 Hcomp1 as Hmain1. rewrite Hmain1.
        rewrite <- Hiface in Hcomp1.
        pose proof CS.prog_main_block_no_main _ Hwf1 Hcomp1 as Hmain2. rewrite Hmain2.
        rewrite -> Hiface in Hcomp1. (* Restore for later sub-goal. *)
        apply PS.ProgramControl.
        * assumption.
        * apply PS.to_partial_memory_merge_prepare_procedures_memory_left; assumption.
        * reflexivity.
      + rewrite CS.initial_machine_state_after_linking; try assumption.
        unfold CS.initial_state in HCSini1.
        rewrite CS.initial_machine_state_after_linking in HCSini1; try assumption.
        inversion HCSini1; subst.
        assert (Hcomp2 : Component.main \notin domm (prog_interface p)).
        {
          destruct (Component.main \in domm (prog_interface p)) eqn:Hcase.
          - simpl in Hcomp1. exfalso. eapply PS.domm_partition_in_both; eassumption.
          - reflexivity.
        }
        pose proof CS.prog_main_block_no_main _ wf1 Hcomp2 as Hmain1. rewrite Hmain1.
        simpl.
        apply PS.ContextControl.
        * assumption.
        * apply PS.to_partial_memory_merge_prepare_procedures_memory_left; assumption.
        * reflexivity.
    - (* Symmetric case. *)
      inversion Hini2
        as [c' ics ? Hiface _ Hwf2 Hlinkable2 Hmains2 Hpartial2 HCSini2];
        subst.
      assert (Hclosed : closed_program (program_link c c')).
      {
        (* Refactored for later sub-proofs. *)
        apply interface_preserves_closedness_r with (p2 := p); try easy.
        - now apply linkable_sym.
        - rewrite closed_program_link_sym; try easy.
          now apply linkable_sym.
        - now apply linkable_mains_sym.
        - now apply interface_implies_matching_mains.
      }
      inversion Hpartial2 as [? ? ? ? ? ? Hcomp2 | ? ? ? ? ? ? Hcomp2]; subst;
        PS.simplify_turn.
      + rewrite CS.initial_machine_state_after_linking; try assumption.
        unfold CS.initial_state in HCSini2.
        rewrite CS.initial_machine_state_after_linking in HCSini2; try assumption.
        inversion HCSini2; subst.
        pose proof CS.prog_main_block_no_main _ wf1 Hcomp2 as Hmain1. rewrite Hmain1.
        rewrite <- Hiface in Hcomp2.
        pose proof CS.prog_main_block_no_main _ Hwf2 Hcomp2 as Hmain2. rewrite Hmain2.
        rewrite -> Hiface in Hcomp2. (* Restore for later sub-goal. *)
        assert (Heq : CS.prog_main_block c + 0 = CS.prog_main_block c) by omega.
        rewrite Heq.
        apply PS.ProgramControl.
        * assumption.
        * setoid_rewrite unionmC at 2;
            last (rewrite 2!domm_prepare_procedures_memory; now apply linkability).
          apply PS.to_partial_memory_merge_prepare_procedures_memory_left; try assumption.
          now apply linkable_sym.
        * reflexivity.
      + rewrite CS.initial_machine_state_after_linking; try assumption.
        unfold CS.initial_state in HCSini2.
        rewrite CS.initial_machine_state_after_linking in HCSini2; try assumption.
        inversion HCSini2; subst.
        assert (Hcomp1 : Component.main \notin domm (prog_interface c)).
        {
          destruct (Component.main \in domm (prog_interface c)) eqn:Hcase.
          - simpl in Hcomp2. exfalso. eapply PS.domm_partition_in_both; eassumption.
          - reflexivity.
        }
        pose proof CS.prog_main_block_no_main _ wf2 Hcomp1 as Hmain2. rewrite Hmain2.
        simpl.
        apply PS.ContextControl.
        * assumption.
        * setoid_rewrite unionmC at 2;
            last (rewrite 2!domm_prepare_procedures_memory; now apply linkability).
          apply PS.to_partial_memory_merge_prepare_procedures_memory_left; try assumption.
          now apply linkable_sym.
        * reflexivity.
  Qed.

  Lemma initial_state_exists : exists s, initial_state s.
  Proof.
    destruct (PS.initial_state_exists wf1 wf2 linkability main_linkability)
      as [s1 Hini1].
    destruct (PS.initial_state_exists
                wf2 wf1 (linkable_sym linkability)
                (linkable_mains_sym main_linkability))
      as [s2 Hini2].
    pose proof initial_state_split Hini1 Hini2 as Hmerge.
    pose proof initial_state_intro Hmerge Hini1 Hini2.
    now exists (s1, s2).
  Qed.

  (* RB: TODO: Move helper lemmas. *)
  Remark to_partial_memory_empty_prog :
    forall (mem : Memory.t),
      to_partial_memory mem (domm (prog_interface empty_prog)) = mem.
  Proof.
    intros mem.
    unfold to_partial_memory.
    rewrite fdisjoint_filterm_full; first reflexivity.
    rewrite domm0. now apply fdisjoints0.
  Qed.

  Remark to_partial_stack_empty_prog :
    forall gps,
      PS.unpartialize_stack
        (PS.to_partial_stack gps (domm (prog_interface empty_prog))) =
      gps.
  Proof.
    intros gps. induction gps as [| [[C b] o] gps IHgps].
    - reflexivity.
    - simpl. rewrite IHgps.
      unfold PS.unpartialize_stack_frame, PS.to_partial_frame.
      rewrite domm0. reflexivity.
  Qed.

  Remark in_domm_unionm :
    forall ptr (ctx1 ctx2 : Program.interface),
      ptr \in domm (unionm ctx1 ctx2) -> ptr \in domm ctx1 \/ ptr \in domm ctx2.
  Proof.
    intros ptr ctx1 ctx2 Hdomm.
    assert (exists v, (unionm ctx1 ctx2) ptr = Some v)
      as [v HSome]
      by now apply /dommP.
    rewrite unionmE in HSome.
    destruct (isSome (ctx1 ptr)) eqn:Hcase;
      simpl in HSome.
    - left. apply /dommP. now eauto.
    - right. apply /dommP. now eauto.
  Qed.

  (* RB: TODO: As usual, refactor symmetries. *)
  Lemma step_emptym_split :
    forall s t s',
      PS.step prog emptym (prepare_global_env prog) s t s' ->
      PS.step p (prog_interface c) (prepare_global_env p)
              (PS.partialize (PS.unpartialize s) (prog_interface c)) t
              (PS.partialize (PS.unpartialize s') (prog_interface c)) /\
      PS.step c (prog_interface p) (prepare_global_env c)
              (PS.partialize (PS.unpartialize s) (prog_interface p)) t
              (PS.partialize (PS.unpartialize s') (prog_interface p)).
  Proof.
    intros s1 t s2 Hstep12.
    inversion Hstep12
      as [p' ? ? ? ics1 ics2 Hiface Hwf Hwf' _ _ HCSstep Hpartial1 Hpartial2];
      subst.
    pose proof empty_interface_implies_empty_program Hwf' Hiface; subst p'.
    clear Hwf' Hiface.
    rewrite linking_empty_program in HCSstep.
    split.
    - apply PS.partial_step with (p' := c) (ics := ics1) (ics' := ics2);
        try easy.
      + inversion Hpartial1 as [gps ? mem ? regs pc Hcomp | ? ? ? ? ? ? Hcomp];
          subst;
          last (PS.simplify_turn; now rewrite domm0 in_fset0 in Hcomp).
        unfold PS.unpartialize.
        rewrite to_partial_memory_empty_prog to_partial_stack_empty_prog.
        unfold PS.partialize.
        destruct (Pointer.component pc \in domm (prog_interface c)) eqn:Hcase.
        * now constructor.
        * constructor; try easy.
          PS.simplify_turn. unfold negb. now rewrite Hcase.
      + (* Symmetric case. *)
        inversion Hpartial2 as [gps ? mem ? regs pc Hcomp | ? ? ? ? ? ? Hcomp];
          subst;
          last (PS.simplify_turn; now rewrite domm0 in_fset0 in Hcomp).
        unfold PS.unpartialize.
        rewrite to_partial_memory_empty_prog to_partial_stack_empty_prog.
        unfold PS.partialize.
        destruct (Pointer.component pc \in domm (prog_interface c)) eqn:Hcase.
        * now constructor.
        * constructor; try easy.
          PS.simplify_turn. unfold negb. now rewrite Hcase.
    - (* Symmetric case. *)
      apply PS.partial_step with (p' := p) (ics := ics1) (ics' := ics2);
        try easy.
      + now apply linkable_sym.
      + now apply linkable_mains_sym.
      + rewrite program_linkC; try assumption.
        now apply linkable_sym.
      (* The remaining two cases are as above, with p instead of c. *)
      + inversion Hpartial1 as [gps ? mem ? regs pc Hcomp | ? ? ? ? ? ? Hcomp];
          subst;
          last (PS.simplify_turn; now rewrite domm0 in_fset0 in Hcomp).
        unfold PS.unpartialize.
        rewrite to_partial_memory_empty_prog to_partial_stack_empty_prog.
        unfold PS.partialize.
        destruct (Pointer.component pc \in domm (prog_interface p)) eqn:Hcase.
        * now constructor.
        * constructor; try easy.
          PS.simplify_turn. unfold negb. now rewrite Hcase.
      + (* Symmetric case. *)
        inversion Hpartial2 as [gps ? mem ? regs pc Hcomp | ? ? ? ? ? ? Hcomp];
          subst;
          last (PS.simplify_turn; now rewrite domm0 in_fset0 in Hcomp).
        unfold PS.unpartialize.
        rewrite to_partial_memory_empty_prog to_partial_stack_empty_prog.
        unfold PS.partialize.
        destruct (Pointer.component pc \in domm (prog_interface p)) eqn:Hcase.
        * now constructor.
        * constructor; try easy.
          PS.simplify_turn. unfold negb. now rewrite Hcase.
  Qed.

  Lemma final_state_emptym_split :
    forall s,
      PS.final_state prog emptym s ->
      PS.final_state p (prog_interface c)
                     (PS.partialize (PS.unpartialize s) (prog_interface c)) /\
      PS.final_state c (prog_interface p)
                     (PS.partialize (PS.unpartialize s) (prog_interface p)).
  Proof.
    intros s Hfinal.
    inversion Hfinal as [p' ics ips Hiface Hwf Hwf' _ _ _ Hpartial HCSfinal | ? Hturn];
      subst;
      last (PS.simplify_turn;
            PS.unfold_state s; now rewrite domm0 in_fset0 in Hturn).
    pose proof empty_interface_implies_empty_program Hwf' Hiface; subst p'.
    clear Hwf' Hiface.
    rewrite linking_empty_program in HCSfinal.
    inversion Hpartial as [gps ? mem ? regs pc Hcomp | ? ? ? ? ? ? Hcomp]; subst;
      last (PS.simplify_turn; now rewrite domm0 in_fset0 in Hcomp).
    simpl.
    destruct (Pointer.component pc \in domm (prog_interface p)) eqn:Hcase1;
      destruct (Pointer.component pc \in domm (prog_interface c)) eqn:Hcase2;
      rewrite Hcase1 Hcase2.
    - exfalso. eapply PS.domm_partition_in_both; eassumption.
    - split.
      + apply PS.final_state_program with (p' := c) (ics := (gps, mem, regs, pc));
          try easy;
          first (PS.simplify_turn; congruence).
        apply PS.ProgramControl.
        * PS.simplify_turn. unfold negb. now rewrite Hcase2. (* Mini-lemma? *)
        * now rewrite to_partial_memory_empty_prog.
        * now rewrite to_partial_stack_empty_prog.
      + now apply PS.final_state_context.
    - (* Symmetric case. *)
      split.
      + now apply PS.final_state_context.
      + apply PS.final_state_program with (p' := p) (ics := (gps, mem, regs, pc));
          try easy.
        * now apply linkable_sym.
        * now apply linkable_mains_sym.
        * PS.simplify_turn. congruence.
        * apply PS.ProgramControl.
          -- PS.simplify_turn. unfold negb. now rewrite Hcase1.
          -- now rewrite to_partial_memory_empty_prog.
          -- now rewrite to_partial_stack_empty_prog.
        * now rewrite <- (program_linkC wf1 wf2 linkability).
    - (* Contra. *)
      destruct HCSfinal as [C_procs [_ [Hdomm _]]].
      assert (Pointer.component pc \in domm (genv_procedures (prepare_global_env prog)))
        as Hcase
        by (apply /dommP; now eauto).
      rewrite domm_genv_procedures in Hcase.
      destruct (in_domm_unionm Hcase) as [Hcontra | Hcontra].
      + rewrite Hcontra in Hcase1. discriminate.
      + rewrite Hcontra in Hcase2. discriminate.
  Qed.

  (* RB: TODO: Refactor case symmetry and left-right lemma symmetry. *)
  Lemma partialize_mergeable_states_left :
    forall s1 s2,
      PS.mergeable_states (prog_interface c) (prog_interface p) s1 s2 ->
      PS.partialize (PS.unpartialize (PS.merge_partial_states s1 s2)) (prog_interface c) = s1.
  Proof.
    intros s1 s2 Hmerge.
    inversion Hmerge as [ics ? ? Hmerge_ifaces Hcomes_from Hpartial1 Hpartial2]; subst.
    rewrite (mergeable_states_merge Hmerge).
    inversion Hpartial1
      as [gps1 ? mem1 ? regs1 pc1 Hcomp1 | gps1 ? mem1 ? regs1 pc1 Hcomp1];
      subst;
      inversion Hpartial2
        as [gps2 ? mem2 ? regs2 pc2 Hcomp2 | gps2 ? mem2 ? regs2 pc2 Hcomp2];
      subst;
      PS.simplify_turn.
    - exfalso.
      eapply PS.domm_partition_in_neither; eassumption.
    - destruct (Pointer.component pc1 \in domm (prog_interface c)) eqn:Hcase;
        first (rewrite Hcase in Hcomp1; discriminate).
      rewrite Hcase.
      unfold PS.mergeable_states_stack, PS.mergeable_states_memory. simpl.
      erewrite PS.to_partial_stack_merge_stack_left; try eassumption.
      erewrite PS.to_partial_memory_merge_memory_left; try eassumption.
      reflexivity.
    - rewrite Hcomp1.
      unfold PS.mergeable_states_stack, PS.mergeable_states_memory. simpl.
      erewrite PS.to_partial_stack_merge_stack_left; try eassumption.
      erewrite PS.to_partial_memory_merge_memory_left; try eassumption.
      reflexivity.
    - exfalso.
      eapply PS.domm_partition_in_both; eassumption.
  Qed.

  Lemma partialize_mergeable_states_right :
    forall s1 s2,
      PS.mergeable_states (prog_interface c) (prog_interface p) s1 s2 ->
      PS.partialize (PS.unpartialize (PS.merge_partial_states s1 s2)) (prog_interface p) = s2.
  Proof.
    intros s1 s2 Hmerge.
    inversion Hmerge as [ics ? ? Hmerge_ifaces Hcomes_from Hpartial1 Hpartial2]; subst.
    rewrite (mergeable_states_merge Hmerge).
    inversion Hpartial1
      as [gps1 ? mem1 ? regs1 pc1 Hcomp1 | gps1 ? mem1 ? regs1 pc1 Hcomp1];
      subst;
      inversion Hpartial2
        as [gps2 ? mem2 ? regs2 pc2 Hcomp2 | gps2 ? mem2 ? regs2 pc2 Hcomp2];
      subst;
      PS.simplify_turn.
    - exfalso.
      eapply PS.domm_partition_in_neither; eassumption.
    - rewrite Hcomp2.
      unfold PS.mergeable_states_stack, PS.mergeable_states_memory. simpl.
      erewrite PS.to_partial_stack_merge_stack_right; try eassumption.
      erewrite PS.to_partial_memory_merge_memory_right; try eassumption.
      reflexivity.
    - destruct (Pointer.component pc1 \in domm (prog_interface p)) eqn:Hcase;
        first (rewrite Hcase in Hcomp2; discriminate).
      rewrite Hcase.
      unfold PS.mergeable_states_stack, PS.mergeable_states_memory. simpl.
      erewrite PS.to_partial_stack_merge_stack_right; try eassumption.
      erewrite PS.to_partial_memory_merge_memory_right; try eassumption.
      reflexivity.
    - exfalso.
      eapply PS.domm_partition_in_both; eassumption.
  Qed.

  Corollary multi_semantics_implies_partial_semantics:
    forall beh,
      program_behaves msem beh ->
      program_behaves (PS.sem prog emptym) beh.
  Proof.
    intros beh Hbeh.
    destruct (forward_simulation_behavior_improves merged_prog_simulates_multisem Hbeh)
      as [beh' [Hbeh' [| [t [? Hprefix]]]]]; subst;
      first assumption.
    inversion Hbeh as [sini_ms ? Hini_ms Hstbeh_ms | Hini_ms]; subst;
      last by destruct (initial_state_exists) as [sini Hini]; specialize (Hini_ms sini).
    destruct (multi_match_initial_states Hini_ms) as [ini_ps [Hini_ps Hmatch_ini]].
    simpl in *.
    eapply program_runs;
      first exact Hini_ps.
    inversion Hstbeh_ms as [| | | ? [s1 s2] Hstar_ms Hnostep_ms Hfinal_ms]; subst.
    destruct (star_simulation Hstar_ms Hmatch_ini) as [s_ps [Hstar_ps Hmatch]].
    eapply state_goes_wrong;
      first exact Hstar_ps.
    - intros t_ps s_ps' Hstep_ps.
      inversion Hmatch as [? ? Hmerge]; subst.
      apply step_emptym_split in Hstep_ps. destruct Hstep_ps as [Hstep_ps1 Hstep_ps2].
      rewrite (partialize_mergeable_states_left Hmerge) in Hstep_ps1.
      rewrite (partialize_mergeable_states_right Hmerge) in Hstep_ps2.
      eapply Hnostep_ms. econstructor; eassumption.
    - intros Hfinal_ps.
      inversion Hmatch as [? ? Hmerge]; subst.
      apply final_state_emptym_split in Hfinal_ps.
      destruct Hfinal_ps as [Hfinal_ps1 Hfinal_ps2].
      rewrite (partialize_mergeable_states_left Hmerge) in Hfinal_ps1.
      rewrite (partialize_mergeable_states_right Hmerge) in Hfinal_ps2.
      apply Hfinal_ms. constructor; assumption.
  Qed.
End MultiSemantics.

Section Symmetry.
  Variables p c : program.

  Remark step_sym :
    forall sp sc t sp' sc',
      step p c (prepare_global_env (program_link p c)) (sp, sc) t (sp', sc') ->
      step c p (prepare_global_env (program_link c p)) (sc, sp) t (sc', sp').
  Proof.
    intros ? ? ? ? ? Hstep.
    inversion Hstep; subst.
    now constructor.
  Qed.

  Remark star_sym :
    forall sp sc t sp' sc',
      star (MultiSem.step p c) (prepare_global_env (program_link p c)) (sp, sc) t (sp', sc') ->
      star (MultiSem.step c p) (prepare_global_env (program_link c p)) (sc, sp) t (sc', sp').
  Proof.
    intros sp sc t sp' sc' Hstar.
    remember (sp, sc) as s eqn:Hs. remember (sp', sc') as s' eqn:Hs'.
    revert sp sc sp' sc' Hs Hs'.
    apply star_iff_starR in Hstar.
    induction Hstar as [| s1 t1 s2 t2 s3 ? Hstar IHHstar Hstep];
      intros sp sc sp' sc' Hs Hs'.
    - rewrite Hs in Hs'. inversion Hs'; subst.
      now apply star_refl.
    - subst. destruct s2 as [s2 s2'].
      specialize (IHHstar sp sc s2 s2' (eq_refl _) (eq_refl _)).
      apply step_sym in Hstep.
      exact (star_right _ _ IHHstar Hstep (eq_refl _)).
  Qed.
End Symmetry.
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

Section BehaviorStar.
  Variables p c: program.

  Hypothesis wf1 : well_formed_program p.
  Hypothesis wf2 : well_formed_program c.

  Hypothesis main_linkability: linkable_mains p c.
  Hypothesis linkability: linkable (prog_interface p) (prog_interface c).

  Let prog := program_link p c.

  Hypothesis prog_is_closed:
    closed_program prog.

  Hypothesis mergeable_interfaces:
    mergeable_interfaces (prog_interface p) (prog_interface c).

  (* RB: TODO: Add hypotheses and/or encapsulate in own section (both directions
     will be needed in the main proof). Relocate to PS?
     Consider what helper lemmas are natural. *)
  Lemma behavior_prefix_star :
    forall b m,
      program_behaves (PS.sem p (prog_interface c)) b ->
      prefix m b ->
    exists s s',
      PS.initial_state p (prog_interface c) s /\
      star (PS.step p (prog_interface c)) (prepare_global_env p) s (finpref_trace m) s'.
  Proof.
    intros b m.
    destruct m as [tm | tm | tm].
    - intros Hb Hm.
      destruct b as [t | ? | ? | ?];
        simpl in Hm; try contradiction;
        subst t.
      inversion Hb as [s1 ? Hini Hbeh |]; subst.
      inversion Hbeh as [? s2 Hstar Hfinal | | |]; subst.
      now eauto.
    - intros Hb Hm.
      destruct b as [? | ? | ? | t];
        simpl in Hm; try contradiction;
        subst t.
      inversion Hb as [s1 ? Hini Hbeh | Hini]; subst.
      + inversion Hbeh as [| | | ? s2 Hstar Hnostep Hfinal]; subst.
        now eauto.
      + destruct (PS.initial_state_exists wf1 wf2 linkability main_linkability)
          as [s Hini'].
        specialize (Hini s).
        contradiction.
    - revert b.
      induction tm as [| e t IHt] using rev_ind;
        intros b Hb Hm;
        simpl in *.
      + destruct (PS.initial_state_exists wf1 wf2 linkability main_linkability)
          as [s Hini'].
        exists s, s. split; [assumption | now apply star_refl].
      + pose proof behavior_prefix_app_inv Hm as Hprefix.
        specialize (IHt _ Hb Hprefix).
        destruct IHt as [s1 [s2 [Hini Hstar]]].
        inversion Hm as [b']; subst.
        inversion Hb as [s1' ? Hini' Hbeh' | Hini' Hbeh']; subst.
        * assert (Heq : s1 = s1')
            by (eapply PS.initial_state_determinism; eassumption).
          subst s1'.
          inversion Hbeh' as [ t' s2' Hstar' Hfinal' Heq
                             | t' s2' Hstar' Hsilent' Heq
                             | T' Hreact' Heq
                             | t' s2' Hstar' Hstep' Hfinal' Heq];
            subst.
          (* RB: TODO: Refactor block. *)
          -- destruct b' as [tb' | ? | ? | ?];
               simpl in Heq;
               try discriminate.
             inversion Heq; subst t'; clear Heq.
             destruct (star_app_inv (@PS.singleton_traces _ _) _ _ Hstar')
               as [s' [Hstar'1 Hstar'2]].
             now eauto.
          -- (* Same as Terminates case. *)
             destruct b' as [? | tb' | ? | ?];
               simpl in Heq;
               try discriminate.
             inversion Heq; subst t'; clear Heq.
             destruct (star_app_inv (@PS.singleton_traces _ _) _ _ Hstar')
               as [s' [Hstar'1 Hstar'2]].
             now eauto.
          -- (* Similar to Terminates and Diverges, but on an infinite trace.
                Ltac can easily take care of these commonalities. *)
             destruct b' as [? | ? | Tb' | ?];
               simpl in Heq;
               try discriminate.
             inversion Heq; subst T'; clear Heq.
             destruct (forever_reactive_app_inv (@PS.singleton_traces _ _) _ _ Hreact')
               as [s' [Hstar'1 Hreact'2]].
             now eauto.
          -- (* Same as Terminate and Diverges. *)
             destruct b' as [? | ? | ? | tb'];
               simpl in Heq;
               try discriminate.
             inversion Heq; subst t'; clear Heq.
             destruct (star_app_inv (@PS.singleton_traces _ _) _ _ Hstar')
               as [s' [Hstar'1 Hstar'2]].
             now eauto.
        * destruct (PS.initial_state_exists wf1 wf2 linkability main_linkability)
            as [s Hini''].
          specialize (Hini' s).
          contradiction.
  Qed.
End BehaviorStar.

Section ThreewayMultisemProgram.
  Variables p c: program.

  Hypothesis wf1 : well_formed_program p.
  Hypothesis wf2 : well_formed_program c.

  Hypothesis main_linkability: linkable_mains p c.
  Hypothesis linkability: linkable (prog_interface p) (prog_interface c).

  Let prog := program_link p c.

  Hypothesis prog_is_closed:
    closed_program prog.

  Hypothesis mergeable_interfaces:
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Theorem threeway_multisem_mergeable_program:
    forall ips1 ips2 t ips1' ips2',
      PS.is_program_component ips1 (prog_interface c) ->
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      star (PS.step p (prog_interface c)) (prepare_global_env p) ips1 t ips1' ->
      star (PS.step c (prog_interface p)) (prepare_global_env c) ips2 t ips2' ->
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1' ips2'.
  Proof.
    intros s1 s1' t s2 s2' Hcomp1 Hmerge1 Hstar12.
    pose proof PS.mergeable_states_program_to_context Hmerge1 Hcomp1 as Hcomp1'.
    revert s1' s2' Hmerge1 Hcomp1 Hcomp1'.
    apply star_iff_starR in Hstar12.
    induction Hstar12 as [s | s1 t1 s2 t2 s3 ? Hstar12 IHstar Hstep23]; subst;
      intros s1' s2' Hmerge1 Hcomp1 Hcomp1' Hstar12'.
    - pose proof PS.context_epsilon_star_is_silent Hcomp1' Hstar12'; subst s2'.
      assumption.
    - rename s2' into s3'. rename Hstar12' into Hstar13'.
      apply (star_app_inv (@PS.singleton_traces _ _)) in Hstar13'.
      destruct Hstar13' as [s2' [Hstar12' Hstar23']].
      specialize (IHstar s1' s2' Hmerge1 Hcomp1 Hcomp1' Hstar12').
      rename IHstar into Hmerge2.
      destruct t2 as [| e2 [| e2' t2]].
      + (* An epsilon step and comparable epsilon star. One is in the context and
           therefore silent, the other preserves mergeability. *)
        eapply star_step in Hstep23; [| now apply star_refl | now apply eq_refl].
        destruct (PS.is_program_component s2 (prog_interface c)) eqn:Hcomp2.
        * pose proof PS.mergeable_states_program_to_context Hmerge2 Hcomp2 as Hcomp2'.
          pose proof PS.context_epsilon_star_is_silent Hcomp2' Hstar23'; subst s3'.
          assert (Hprog_is_closed_sym := prog_is_closed);
            rewrite closed_program_link_sym in Hprog_is_closed_sym; try assumption.
          pose proof PS.mergeable_states_sym wf1 wf2 linkability Hmerge2 as Hmerge2'.
          pose proof linkable_sym linkability as Hlinkability_sym.
          pose proof MultiSem.mergeable_states_star_E0
               Hlinkability_sym Hprog_is_closed_sym Hmerge2' Hstep23 as Hmerge3'.
          now apply PS.mergeable_states_sym.
        * apply negb_false_iff in Hcomp2.
          pose proof PS.context_epsilon_star_is_silent Hcomp2 Hstep23; subst s3.
          exact (MultiSem.mergeable_states_star_E0
                   linkability prog_is_closed Hmerge2 Hstar23').
      + (* The step generates a trace event, mimicked on the other side (possibly
           between sequences of silent steps). *)
        change [e2] with (E0 ** e2 :: E0) in Hstar23'.
        apply (star_middle1_inv (@PS.singleton_traces _ _)) in Hstar23'.
        destruct Hstar23' as [s2'1 [s2'2 [Hstar2' [Hstep23' Hstar3']]]].
        pose proof MultiSem.mergeable_states_star_E0 linkability prog_is_closed
             Hmerge2 Hstar2' as Hmerge21.
        pose proof MultiSem.mergeable_states_step_trans
             wf1 wf2 main_linkability linkability
             Hmerge21 Hstep23 Hstep23' as Hmerge22.
        exact (MultiSem.mergeable_states_star_E0
                 linkability prog_is_closed Hmerge22 Hstar3').
      + (* Contradiction: a step generates at most one event. *)
        pose proof @PS.singleton_traces _ _ _ _ _ Hstep23 as Hcontra.
        simpl in Hcontra. omega.
  Qed.

  (* RB: TODO: Move these lemmas to PS. *)
  Remark epsilon_step_preserves_program_component:
    forall ips1 ips1',
      PS.is_program_component ips1 (prog_interface c) ->
      Step (PS.sem p (prog_interface c)) ips1 E0 ips1' ->
      PS.is_program_component ips1' (prog_interface c).
  Proof.
    intros s1 s2 Hcomp1 Hstep.
    pose proof step_E0_same_turn Hstep as Hturn12.
    inversion Hturn12 as [? ? Hcomp1' Hcomp2 | ? ? Hcomp1' Hcomp2]; subst.
    - assumption.
    - unfold PS.is_program_component in Hcomp1.
      rewrite Hcomp1' in Hcomp1.
      discriminate.
  Qed.

  Lemma epsilon_star_preserves_program_component:
    forall ips1 ips1',
      PS.is_program_component ips1 (prog_interface c) ->
      Star (PS.sem p (prog_interface c)) ips1 E0 ips1' ->
      PS.is_program_component ips1' (prog_interface c).
  Proof.
    intros s1 s2 Hcomp1 Hstar12.
    remember E0 as t eqn:Ht.
    revert Hcomp1 Ht.
    apply star_iff_starR in Hstar12.
    induction Hstar12 as [s | s1 t1 s2 t2 s3 ? Hstar12 IHstar Hstep23]; subst;
      intros Hcomp1 Ht.
    - assumption.
    - apply Eapp_E0_inv in Ht. destruct Ht; subst.
      specialize (IHstar Hcomp1 (eq_refl _)).
      exact (epsilon_step_preserves_program_component IHstar Hstep23).
  Qed.

  Ltac t_threeway_multisem_step_E0_CS
       Hpartials2 HCSstep Hcomps1 Hpartialm1 Hpartialm1' mem pc Hcomps Hiface :=
        (* Case analysis with special cases for memory and label operations. *)
        inversion Hpartials2 as [? ? ? ? ? ? Hcomps2 | ? ? ? ? ? ? Hcomps2]; subst;
          last (exfalso;
                pose proof CS.silent_step_preserves_component _ _ _ HCSstep as Hcomp;
                simpl in Hcomp; PS.simplify_turn; rewrite Hcomp in Hcomps1;
                eapply PS.domm_partition_in_notin; eassumption);

        [inversion Hpartialm1 as [? ? ? ? ? ? Hcompm1 Hmem1' Hstack1' |]; subst];

        [inversion Hpartialm1' as [? ? ? ? ? ? Hcompm1' | ? ? ? ? ? ? Hcompm1']; subst];
          first (exfalso;
                 PS.simplify_turn; eapply PS.domm_partition_in_neither; eassumption);

        [CS.step_of_executing];
          try eassumption; try reflexivity;
          try match goal with
          | Hstore : Memory.store mem ?PTR _ = Some _,
            Hcomps : Pointer.component ?PTR = Pointer.component pc
            |- Memory.store _ _ _ = Some _
            =>
            (* BEGIN HACK *)
            PS.simplify_turn;
            match goal with
            | Hcompm1 : is_true (Pointer.component pc \notin domm (prog_interface c)) (* HACK *)
              |- _ =>
            (* END HACK *)
              rewrite <- Hcomps in Hcompm1;
              apply partialize_program_store
                with (ctx := prog_interface c) in Hstore;
                try assumption;
              apply unpartialize_program_store;
              eassumption
            end
          end;
          try match goal with
          | Halloc : Memory.alloc mem _ _ = Some _
            |- Memory.alloc _ _ _ = Some _
            =>
            apply unpartialize_program_alloc;
            apply partialize_program_alloc
              with (ctx := prog_interface c) in Halloc;
            assumption
          end;
          try match goal with
          | Hload : Memory.load mem ?PTR = Some _,
            Hmem1' : to_partial_memory mem (domm (prog_interface c)) = (* HACK *)
                     to_partial_memory _ (domm (prog_interface c))
            |- Memory.load _ _ = Some _
            =>
            symmetry in Hmem1';
            destruct PTR as [[C b] o]; simpl in *; subst;
            apply program_load_in_partialized_memory_strong
              with (ctx := domm (prog_interface c)) (mem1 := mem);
              try assumption;
            setoid_rewrite PS.to_partial_memory_merge_partial_memories_left;
              try eassumption;
            reflexivity
          end;
          try match goal with
          | Hlabel : find_label_in_component _ _ _ = Some _
            |- find_label_in_component _ _ _ = Some _
            =>
            rewrite find_label_in_component_program_link_left in Hlabel;
              try assumption; [| now rewrite Hiface];
            rewrite program_linkC;
              try assumption; [| now apply linkable_sym];
            rewrite find_label_in_component_program_link_left; eassumption
          end;
          try match goal with
          | Hlabel : find_label_in_procedure _ _ _ = Some _
            |- find_label_in_procedure _ _ _ = Some _
            =>
            rewrite find_label_in_procedure_program_link_left in Hlabel;
              try assumption; [| now rewrite Hiface];
            rewrite program_linkC;
              try assumption; [| now apply linkable_sym];
            rewrite find_label_in_procedure_program_link_left; eassumption
          end;

        rewrite program_linkC; try assumption;
          [ | now apply linkable_sym];

        eapply execution_invariant_to_linking; eassumption.

  Ltac t_threeway_multisem_step_E0_PS pc Hcompm1' Hmem Hstk :=
    try match goal with (* Jumps. *)
    | Hlabel : find_label_in_component _ pc _ = Some ?PC
      |- _ =>
      pose proof find_label_in_component_1 _ _ _ _ Hlabel as Hcomp;
      rewrite Hcomp
    | Hlabel: find_label_in_procedure _ pc _ = Some ?PC
      |- _ =>
      pose proof find_label_in_procedure_1 _ _ _ _ Hlabel as Hcomp;
      rewrite Hcomp
    | Hop : executing _ pc (IJump _),
      Hpc : Pointer.component ?PC = Pointer.component pc
      |- _ =>
      symmetry in Hpc; rewrite Hpc; rename Hpc into Hcomp
  end;
  [   constructor (* Jumps. *)
    || (rewrite <- Pointer.inc_preserves_component; constructor)
  ];
  [   match goal with
      | Hcomp : Pointer.component pc = Pointer.component _
        |- _ =>
        now rewrite Hcomp in Hcompm1' (* Jumps. *)
      end
    || now rewrite -> Pointer.inc_preserves_component
  |   (erewrite PS.to_partial_memory_merge_partial_memories_right; (* Memory. *)
       reflexivity || eassumption)
    || (rewrite <- Hmem;
       erewrite PS.to_partial_memory_merge_memory_right;
       try easy;
       eassumption)
  | rewrite <- Hstk;
    erewrite PS.to_partial_stack_merge_stack_right;
    try easy;
    eassumption
  ].

  (* RB: TODO: Rename, context can step. *)
  Lemma threeway_multisem_step_E0:
    forall ips1 ips2 ips1',
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      PS.is_program_component ips1 (prog_interface c) ->
      Step (PS.sem p (prog_interface c)) ips1 E0 ips1' ->
      Step (PS.sem c (prog_interface p)) ips2 E0 ips2.
  Proof.
    intros s1 s1' s2 Hmerge1 Hcomp1 Hstep12.
    inversion Hmerge1 as [ics ? ? Hmerge_ifaces Hcomes_from Hpartialm1 Hpartialm1'];
      subst.
    inversion Hstep12
      as [p' ? ? ? ics1 ics2 Hiface _ Hwf1 Hlinkable Hmains HCSstep Hpartials1 Hpartials2];
      subst.
    apply PS.partial_step
      with (p' := p)
           (ics := PS.unpartialize (PS.merge_partial_states s1 s1'))
           (ics' := PS.unpartialize (PS.merge_partial_states s2 s1')).
    - reflexivity.
    - assumption.
    - assumption.
    - now apply linkable_sym.
    - now apply linkable_mains_sym.
    - inversion Hpartials1 as [? ? ? ? ? ? Hcomps1 | ? ? ? ? ? ? Hcomps1]; subst;
        last (exfalso;
              PS.simplify_turn; eapply PS.domm_partition_in_notin; eassumption).
      inversion HCSstep; subst;
        t_threeway_multisem_step_E0_CS
          Hpartials2 HCSstep Hcomps1 Hpartialm1 Hpartialm1' mem pc Hcomps Hiface.
    - (* RB: TODO: Interesting to spin into a lemma, like similar sub-goals. *)
      inversion Hpartialm1 as [? ? ? ? ? ? _ | ? ? ? ? ? ? Hcontra];
        subst;
        last (PS.simplify_turn;
              exfalso; eapply PS.domm_partition_in_notin; eassumption).
      inversion Hpartialm1' as [? ? ? ? ? ? Hcomp1' | ? ? ? ? ? ? Hcomp1'];
        subst;
        first (exfalso; eapply PS.domm_partition_in_neither; eassumption).
      constructor.
      + assumption.
      + erewrite PS.to_partial_memory_merge_memory_right; try easy.
        eassumption.
      + erewrite PS.to_partial_stack_merge_stack_right; try easy.
        eassumption.
    - inversion Hpartialm1 as [? ? ? ? ? ? _ | ? ? ? ? ? ? Hcontra];
        subst;
        last (PS.simplify_turn;
              exfalso; eapply PS.domm_partition_in_notin; eassumption).
      inversion Hpartialm1' as [? ? ? ? ? ? Hcompm1' | ? ? ? ? ? ? Hcompm1'];
        subst;
        first (exfalso; eapply PS.domm_partition_in_neither; eassumption).
      inversion Hpartials1 as [? ? ? ? ? ? Hcomps1 Hmem Hstk |];
        subst.
      inversion Hpartials2 as [? ? ? ? ? ? Hcomps2 | ? ? ? ? ? ? Hcontra];
        subst;
        (* RB: TODO: Possible refactoring of this into lemma, see use above. *)
        last (exfalso;
              pose proof CS.silent_step_preserves_component _ _ _ HCSstep as Hcomp;
              simpl in Hcomp; PS.simplify_turn; rewrite Hcomp in Hcomps1;
              eapply PS.domm_partition_in_notin; eassumption).
      inversion HCSstep; subst;
        (* RB: TODO: Can we make these applications faster? *)
        t_threeway_multisem_step_E0_PS pc Hcompm1' Hmem Hstk.
  Qed.

  (* Compose two stars into a multi-step star. One of the two stars is in the
     context and its partial state remains unaltered; the other performs all the
     steps without interruption. *)
  Lemma threeway_multisem_star_E0_program:
    forall ips1 ips2 ips1' ips2',
      PS.is_program_component ips1 (prog_interface c) ->
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      star (PS.step p (prog_interface c)) (prepare_global_env p) ips1 E0 ips1' ->
      star (PS.step c (prog_interface p)) (prepare_global_env c) ips2 E0 ips2' ->
      star (MultiSem.step p c) (prepare_global_env prog) (ips1, ips2) E0 (ips1', ips2').
  Proof.
    intros s1 s1' s2 s2' Hcomp1 Hmerge1 Hstar12 Hstar12'.
    pose proof PS.mergeable_states_program_to_context Hmerge1 Hcomp1 as Hcomp1'.
    pose proof PS.context_epsilon_star_is_silent Hcomp1' Hstar12'; subst s2'.
    remember E0 as t eqn:Ht.
    revert s1' Ht Hmerge1 Hcomp1 Hcomp1' Hstar12'.
    apply star_iff_starR in Hstar12.
    induction Hstar12 as [s | s1 t1 s2 t2 s3 ? Hstar12 IHstar Hstep23]; subst;
      intros s' Ht Hmerge1 Hcomp1 Hcomp1' Hstar12'.
    - now apply star_refl.
    - apply Eapp_E0_inv in Ht. destruct Ht; subst.
      specialize (IHstar _ (eq_refl _) Hmerge1 Hcomp1 Hcomp1' Hstar12').
      apply star_trans with (t1 := E0) (s2 := (s2, s')) (t2 := E0);
        [assumption | | reflexivity].
      apply star_step with (t1 := E0) (s2 := (s3, s')) (t2 := E0).
      + apply star_iff_starR in Hstar12.
        pose proof threeway_multisem_mergeable_program Hcomp1 Hmerge1 Hstar12 Hstar12'
          as Hmerge2.
        pose proof epsilon_star_preserves_program_component Hcomp1 Hstar12
          as Hcomp2.
        pose proof threeway_multisem_step_E0 Hmerge2 Hcomp2 Hstep23 as Hstep23'.
        now constructor.
      + now constructor.
      + reflexivity.
  Qed.
End ThreewayMultisemProgram.

Section ThreewayMultisem.
  Variables p c: program.

  Hypothesis wf1 : well_formed_program p.
  Hypothesis wf2 : well_formed_program c.

  Hypothesis main_linkability: linkable_mains p c.
  Hypothesis linkability: linkable (prog_interface p) (prog_interface c).

  Let prog := program_link p c.

  Hypothesis prog_is_closed:
    closed_program prog.

  Hypothesis mergeable_interfaces:
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Theorem threeway_multisem_mergeable:
    forall ips1 ips2 t ips1' ips2',
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      star (PS.step p (prog_interface c)) (prepare_global_env p) ips1 t ips1' ->
      star (PS.step c (prog_interface p)) (prepare_global_env c) ips2 t ips2' ->
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1' ips2'.
  Proof.
    intros s1 s1' t s2 s2' Hmerge1 Hstar12 Hstar12'.
    destruct (PS.is_program_component s1 (prog_interface c)) eqn:Hcomp1.
    - eapply threeway_multisem_mergeable_program; eassumption.
    - apply negb_false_iff in Hcomp1.
      apply (PS.mergeable_states_context_to_program Hmerge1) in Hcomp1.
      apply (PS.mergeable_states_sym wf2 wf1 (linkable_sym linkability)).
      eapply threeway_multisem_mergeable_program; try eassumption.
      + now apply linkable_mains_sym.
      + now apply linkable_sym.
      + erewrite closed_program_link_sym; try eassumption.
        now apply linkable_sym.
      + now apply PS.mergeable_states_sym.
  Qed.

  Lemma threeway_multisem_star_E0:
    forall ips1 ips2 ips1' ips2',
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      star (PS.step p (prog_interface c)) (prepare_global_env p) ips1 E0 ips1' ->
      star (PS.step c (prog_interface p)) (prepare_global_env c) ips2 E0 ips2' ->
      star (MultiSem.step p c) (prepare_global_env prog) (ips1, ips2) E0 (ips1', ips2').
  Proof.
    intros s1 s1' s2 s2' Hmerge1 Hstar12 Hstar12'.
    destruct (PS.is_program_component s1 (prog_interface c)) eqn:Hcomp1.
    - eapply threeway_multisem_star_E0_program; eassumption.
    - apply negb_false_iff in Hcomp1.
      apply (PS.mergeable_states_context_to_program Hmerge1) in Hcomp1.
      apply MultiSem.star_sym.
      apply threeway_multisem_star_E0_program; try assumption.
      + now apply linkable_mains_sym.
      + now apply linkable_sym.
      + rewrite closed_program_link_sym; try assumption.
        now apply linkable_sym.
      + now apply PS.mergeable_states_sym.
  Qed.

  Theorem threeway_multisem_star_program:
    forall ips1 ips2 t ips1' ips2',
      PS.is_program_component ips1 (prog_interface c) ->
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      star (PS.step p (prog_interface c)) (prepare_global_env p) ips1 t ips1' ->
      star (PS.step c (prog_interface p)) (prepare_global_env c) ips2 t ips2' ->
      star (MultiSem.step p c) (prepare_global_env prog) (ips1, ips2) t (ips1', ips2').
  Proof.
    intros s1 s1' t s2 s2' Hcomp1 Hmerge1 Hstar12.
    pose proof PS.mergeable_states_program_to_context Hmerge1 Hcomp1 as Hcomp1'.
    revert s1' s2' Hmerge1 Hcomp1 Hcomp1'.
    apply star_iff_starR in Hstar12.
    induction Hstar12 as [s | s1 t1 s2 t2 s3 ? Hstar12 IHstar Hstep23]; subst;
      intros s1' s2' Hmerge1 Hcomp1 Hcomp1' Hstar12'.
    - pose proof PS.context_epsilon_star_is_silent Hcomp1' Hstar12'; subst s2'.
      now apply star_refl.
    - rename s2' into s3'. rename Hstar12' into Hstar13'.
      apply (star_app_inv (@PS.singleton_traces _ _)) in Hstar13'.
      destruct Hstar13' as [s2' [Hstar12' Hstar23']].
      specialize (IHstar s1' s2' Hmerge1 Hcomp1 Hcomp1' Hstar12').
      (* Apply instantiated IH and case analyze step trace. *)
      apply star_trans with (t1 := t1) (s2 := (s2, s2')) (t2 := t2);
        [assumption | | reflexivity].
      apply star_iff_starR in Hstar12.
      pose proof threeway_multisem_mergeable Hmerge1 Hstar12 Hstar12'
        as Hmerge2.
      destruct t2 as [| e2 [| e2' t2]].
      + (* An epsilon step and comparable epsilon star. One is in the context and
           therefore silent, the other executes and leads the MultiSem star. *)
        eapply star_step in Hstep23; [| now apply star_refl | now apply eq_refl].
        exact (threeway_multisem_star_E0 Hmerge2 Hstep23 Hstar23').
      + (* The step generates a trace event, mimicked on the other side (possibly
           between sequences of silent steps). *)
        change [e2] with (E0 ** e2 :: E0) in Hstar23'.
        apply (star_middle1_inv (@PS.singleton_traces _ _)) in Hstar23'.
        destruct Hstar23' as [s2'1 [s2'2 [Hstar2' [Hstep23' Hstar3']]]].
        (* Prefix star. *)
        pose proof star_refl (PS.step p (prog_interface c)) (prepare_global_env p) s2
          as Hstar2.
        pose proof threeway_multisem_star_E0 Hmerge2 Hstar2 Hstar2'
          as Hmstar1.
        (* Propagate mergeability, step. *)
        pose proof threeway_multisem_mergeable Hmerge2 Hstar2 Hstar2' as Hmerge21.
        pose proof MultiSem.multi_step (prepare_global_env prog) Hstep23 Hstep23'
          as Hmstep2.
        (* Propagate mergeability, suffix star. *)
        pose proof MultiSem.mergeable_states_step_trans
             wf1 wf2 main_linkability linkability
             Hmerge21 Hstep23 Hstep23' as Hmerge22.
        pose proof star_refl (PS.step p (prog_interface c)) (prepare_global_env p) s3
          as Hstar3.
        pose proof threeway_multisem_star_E0 Hmerge22 Hstar3 Hstar3' as Hmstar3.
        (* Compose. *)
        exact (star_trans
                 (star_right _ _ Hmstar1 Hmstep2 (eq_refl _))
                 Hmstar3 (eq_refl _)).
      + (* Contradiction: a step generates at most one event. *)
        pose proof @PS.singleton_traces _ _ _ _ _ Hstep23 as Hcontra.
        simpl in Hcontra. omega.
  Qed.
End ThreewayMultisem.

Section ThreewayMultisem'.
  Variables p c: program.

  Hypothesis wf1 : well_formed_program p.
  Hypothesis wf2 : well_formed_program c.

  Hypothesis main_linkability: linkable_mains p c.
  Hypothesis linkability: linkable (prog_interface p) (prog_interface c).

  Let prog := program_link p c.

  Hypothesis prog_is_closed:
    closed_program prog.

  Hypothesis mergeable_interfaces:
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Theorem threeway_multisem_star:
    forall ips1 ips2 t ips1' ips2',
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      star (PS.step p (prog_interface c)) (prepare_global_env p) ips1 t ips1' ->
      star (PS.step c (prog_interface p)) (prepare_global_env c) ips2 t ips2' ->
      star (MultiSem.step p c) (prepare_global_env prog) (ips1, ips2) t (ips1', ips2').
  Proof.
    intros s1 s1' t s2 s2' Hmerge1 Hstar12 Hstar12'.
    destruct (PS.is_program_component s1 (prog_interface c)) eqn:Hcomp1.
    - now apply threeway_multisem_star_program.
    - apply negb_false_iff in Hcomp1.
      apply (PS.mergeable_states_context_to_program Hmerge1) in Hcomp1.
      apply MultiSem.star_sym.
      apply threeway_multisem_star_program; try assumption.
      + now apply linkable_mains_sym.
      + now apply linkable_sym.
      + rewrite closed_program_link_sym; try assumption.
        now apply linkable_sym.
      + now apply PS.mergeable_states_sym.
  Qed.
End ThreewayMultisem'.

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
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Corollary threeway_multisem_star_simulation:
    forall ips1 ips2 t ips1' ips2',
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      star (PS.step p (prog_interface c)) (prepare_global_env p) ips1 t ips1' ->
      star (PS.step c (prog_interface p)) (prepare_global_env c) ips2 t ips2' ->
      star (MultiSem.step p c) (prepare_global_env prog) (ips1, ips2) t (ips1', ips2') /\
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1' ips2'.
  Proof.
    intros. split.
    - apply threeway_multisem_star; assumption.
    - eapply threeway_multisem_mergeable; eassumption.
  Qed.

  Lemma initial_states_mergeability:
    forall s1 s2,
      initial_state (PS.sem p (prog_interface c)) s1 ->
      initial_state (PS.sem c (prog_interface p)) s2 ->
      PS.mergeable_states (prog_interface c) (prog_interface p) s1 s2.
  Proof.
    simpl.
    intros s1 s2 Hs1_init Hs2_init.

    inversion Hs1_init
      as [p' ics1 ? Hiface1 _ Hwf1' Hlinkable1 Hmains1 Hpartial1 HCSini1];
      subst.
    inversion Hs2_init
      as [c' ics2 ? Hiface2 _ Hwf2' Hlinkable2 Hmains2 Hpartial2 HCSini2];
      subst.
    unfold CS.initial_state in HCSini1, HCSini2.

    assert (prog_is_closed_sym := prog_is_closed);
      rewrite (closed_program_link_sym wf1 wf2 linkability) in prog_is_closed_sym.
    assert (Hmatching1 : matching_mains c p')
      by now eapply interface_implies_matching_mains.
    assert (Hmatching2 : matching_mains p c')
      by now eapply interface_implies_matching_mains.
    rewrite (CS.initial_machine_state_after_linking
               _ _ wf1 Hwf1' Hlinkable1
               (interface_preserves_closedness_r
                  wf1 Hwf1' (eq_sym Hiface1) linkability prog_is_closed
                  main_linkability Hmatching1))
      in HCSini1.
    rewrite (CS.initial_machine_state_after_linking
               _ _ wf2 Hwf2' Hlinkable2
               (interface_preserves_closedness_r
                  wf2 Hwf2' (eq_sym Hiface2) (linkable_sym linkability)
                  prog_is_closed_sym (linkable_mains_sym main_linkability)
                  Hmatching2))
      in HCSini2.
    subst ics1 ics2.

    eapply PS.mergeable_states_intro with
        (ics := CS.initial_machine_state (program_link p c)).
    - now apply mergeable_interfaces_sym.
    - destruct (cprog_main_existence prog_is_closed)
        as [main [main_procs [Hmain [Hmain_procs Hdomm]]]].
      exists (program_link p c), main, (CS.initial_machine_state (program_link p c)), E0.
      split; [| split; [| split; [| split]]].
      + apply linking_well_formedness; assumption.
      + assumption.
      + inversion linkability; now rewrite <- unionmC.
      + reflexivity.
      + now apply star_refl.
    - rewrite (CS.initial_machine_state_after_linking
                 _ _ wf1 wf2 linkability prog_is_closed).
      inversion Hpartial1 as [? ? ? ? ? ? Hcomp1 | ? ? ? ? ? ? Hcomp1]; subst;
        inversion Hpartial2 as [? ? ? ? ? ? Hcomp2 | ? ? ? ? ? ? Hcomp2]; subst;
        PS.simplify_turn.
      + exfalso. apply (@domm_partition_program_link_in_neither p c); assumption.
      + assert (Hmainc : CS.prog_main_block c = 0)
          by now rewrite CS.prog_main_block_no_main.
        (* RB: NOTE: The lemma may be generalized by adding an equality on
           interfaces and keeping the two instances distinct in the statement. *)
        assert (Hmainp' : CS.prog_main_block p' = 0)
          by (rewrite <- Hiface1 in Hcomp1;
              now rewrite CS.prog_main_block_no_main).
        rewrite Hmainc Hmainp'.
        constructor.
        * exact Hcomp1.
        * apply PS.to_partial_memory_merge_prepare_procedures_memory_left; assumption.
        * reflexivity.
      + assert (Hmainp : CS.prog_main_block p = 0)
          by now rewrite CS.prog_main_block_no_main.
        rewrite Hmainp.
        constructor.
        * exact Hcomp1.
        * apply PS.to_partial_memory_merge_prepare_procedures_memory_left; assumption.
        * reflexivity.
      + exfalso. eapply PS.domm_partition_in_both; eassumption.
    - (* Symmetric case. *)
      rewrite (CS.initial_machine_state_after_linking
                 _ _ wf1 wf2 linkability prog_is_closed).
      inversion Hpartial1 as [? ? ? ? ? ? Hcomp1 | ? ? ? ? ? ? Hcomp1]; subst;
        inversion Hpartial2 as [? ? ? ? ? ? Hcomp2 | ? ? ? ? ? ? Hcomp2]; subst;
        PS.simplify_turn.
      + exfalso. apply (@domm_partition_program_link_in_neither p c); assumption.
      + assert (Hmainc : CS.prog_main_block c = 0)
          by now rewrite CS.prog_main_block_no_main.
        rewrite Hmainc.
        constructor.
        * exact Hcomp2.
        * inversion linkability as [_ Hdisjoint].
          rewrite <- !domm_prepare_procedures_memory in Hdisjoint.
          rewrite (unionmC Hdisjoint).
          apply PS.to_partial_memory_merge_prepare_procedures_memory_left; first assumption.
          apply linkable_sym; assumption.
        * reflexivity.
      + assert (Hmainp : CS.prog_main_block p = 0)
          by now rewrite CS.prog_main_block_no_main.
        assert (Hmainc' : CS.prog_main_block c' = 0)
          by (rewrite <- Hiface2 in Hcomp2;
              now rewrite CS.prog_main_block_no_main).
        rewrite Hmainp Hmainc' Nat.add_0_r.
        constructor.
        * exact Hcomp2.
        * inversion linkability as [_ Hdisjoint].
          rewrite <- !domm_prepare_procedures_memory in Hdisjoint.
          rewrite (unionmC Hdisjoint).
          apply PS.to_partial_memory_merge_prepare_procedures_memory_left; first assumption.
          apply linkable_sym; assumption.
        * reflexivity.
      + exfalso. eapply PS.domm_partition_in_both; eassumption.
  Qed.

  (* RB: TODO: Move to PS when done. Note the [*_after_linking] convention used
     for similar results in that module as opposed to [*_composition_*] being
     used here (and various forms of [*merge*]). It would be desirable to have a
     look at these and harmonize as needed. *)
  Lemma initial_state_merge_after_linking :
    forall s1 s2,
      PS.initial_state p (prog_interface c) s1 ->
      PS.initial_state c (prog_interface p) s2 ->
      PS.initial_state prog emptym (PS.merge_partial_states s1 s2).
  Proof.
    intros s1 s2 Hini1 Hini2.
    apply PS.initial_state_intro
      with (p' := empty_prog)
           (ics := PS.unpartialize (PS.merge_partial_states s1 s2)).
    - reflexivity.
    - now apply linking_well_formedness.
    - exact empty_prog_is_well_formed.
    - apply linkable_emptym.
      now inversion linkability.
    - now apply linkable_mains_empty_prog.
    - apply MultiSem.mergeable_states_partial_state_emptym
        with (p := p) (c := c);
        try assumption.
      now apply MultiSem.initial_state_split.
    - rewrite linking_empty_program.
      now apply MultiSem.merged_initial_states.
  Qed.

  Corollary partial_programs_composition_prefix :
    forall m,
      does_prefix (PS.sem p (prog_interface c)) m ->
      does_prefix (PS.sem c (prog_interface p)) m ->
      does_prefix (PS.sem prog emptym) m.
  Proof.
    unfold does_prefix.
    intros m [b1 [Hbeh1 Hprefix1]] [b2 [Hbeh2 Hprefix2]].
    inversion Hbeh1 as [s1 beh1 Hini1 Hst_beh1 | Hini1]; subst;
      last now destruct (PS.not_initial_state_contra
                           wf1 wf2 linkability main_linkability Hini1).
    inversion Hbeh2 as [s2 beh2 Hini2 Hst_beh2 | Hini2]; subst;
      last now destruct (PS.not_initial_state_contra
                           wf2 wf1
                           (linkable_sym linkability)
                           (linkable_mains_sym main_linkability)
                           Hini2).
    destruct m as [tm | tm | tm].
    - destruct b1 as [t1 | ? | ? | ?]; try contradiction.
      destruct b2 as [t2 | ? | ? | ?]; try contradiction.
      simpl in Hprefix1, Hprefix2. subst t1 t2.
      inversion Hst_beh1 as [? s1' Hstar1 Hfinal1 | | |]; subst.
      inversion Hst_beh2 as [? s2' Hstar2 Hfinal2 | | |]; subst.
      exists (Terminates tm). split; last reflexivity.
      pose proof initial_states_mergeability Hini1 Hini2 as Hmerge.
      destruct (threeway_multisem_star_simulation Hmerge Hstar1 Hstar2)
        as [Hstar12 Hmerge'].
      apply MultiSem.multi_semantics_implies_partial_semantics; try assumption.
      apply program_runs with (s := (s1, s2)); first easy.
      apply state_terminates with (s' := (s1', s2')); easy.
    - destruct b1 as [? | ? | ? | t1]; try contradiction.
      destruct b2 as [? | ? | ? | t2]; try contradiction.
      simpl in Hprefix1, Hprefix2. subst t1 t2.
      inversion Hst_beh1 as [| | | ? s1' Hstar1 Hstep1 Hfinal1]; subst.
      inversion Hst_beh2 as [| | | ? s2' Hstar2 Hstep2 Hfinal2]; subst.
      exists (Goes_wrong tm). split; last reflexivity.
      pose proof initial_states_mergeability Hini1 Hini2 as Hmerge.
      destruct (threeway_multisem_star_simulation Hmerge Hstar1 Hstar2)
        as [Hstar12 Hmerge'].
      apply MultiSem.multi_semantics_implies_partial_semantics; try assumption.
      apply program_runs with (s := (s1, s2)); first easy.
      apply state_goes_wrong with (s' := (s1', s2')); first easy.
      + intros t s Hcontra.
        inversion Hcontra as [? ? s1'' ? s2'' Hstep1' Hstep2']; subst.
        apply (Hstep1 t s1''). assumption.
      + intros Hcontra.
        inversion Hcontra as [? ? Hfinal1' Hfinal2']; subst. contradiction.
    - (* Here we talk about the stars associated to the behaviors, without
         worrying now about connecting them to the existing initial states.
         RB: TODO: Remove asserts, phrase in terms of the instances of
         behavior_prefix_star directly. *)
      assert
        (exists s s',
            PS.initial_state p (prog_interface c) s /\
            star (PS.step p (prog_interface c)) (prepare_global_env p) s tm s')
        as [s1' [s1'' [Hini1' Hstar1]]].
      {
        destruct
          (behavior_prefix_star
             wf1 wf2 main_linkability linkability prog_is_closed
             Hbeh1 Hprefix1)
          as [s [s' [Hini Hstar]]].
        now exists s, s'.
      }
      assert
        (exists s s',
            PS.initial_state c (prog_interface p) s /\
            star (PS.step c (prog_interface p)) (prepare_global_env c) s tm s')
        as [s2' [s2'' [Hini2' Hstar2]]].
      {
        assert (prog_is_closed_sym := prog_is_closed).
        rewrite (closed_program_link_sym wf1 wf2 linkability) in prog_is_closed_sym.
        destruct
          (behavior_prefix_star
             wf2 wf1
             (linkable_mains_sym main_linkability) (linkable_sym linkability)
             prog_is_closed_sym
             Hbeh2 Hprefix2)
          as [s [s' [Hini Hstar]]].
        now exists s, s'.
      }
      pose proof initial_states_mergeability Hini1' Hini2' as Hmerge.
      destruct (threeway_multisem_star_simulation Hmerge Hstar1 Hstar2)
        as [Hstar12 Hmerge'].
      destruct
        (MultiSem.star_simulation
           wf1 wf2 main_linkability linkability mergeable_interfaces prog_is_closed
           Hstar12 (MultiSem.multi_match_intro Hmerge))
        as [s [Hstar12' Hmulti]].
      eapply program_behaves_finpref_exists; last now apply Hstar12'.
      now apply initial_state_merge_after_linking.
  Qed.
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

  Hypothesis prog_is_closed:
    closed_program (program_link p c).

  Hypothesis mergeable_interfaces:
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Theorem composition_prefix:
    forall m,
      does_prefix (PS.sem p (prog_interface c)) m ->
      does_prefix (PS.sem c (prog_interface p)) m ->
      does_prefix (CS.sem (program_link p c)) m.
  Proof.
    intros m Hpref1 Hpref2.
    inversion mergeable_interfaces as [linkability _].
    destruct
      (partial_programs_composition_prefix
         wf1 wf2 main_linkability linkability prog_is_closed mergeable_interfaces
         Hpref1 Hpref2)
      as [beh [Hbeh Hprefix]].
    exists beh. split; auto.
    - apply PS2CS.partial_semantics_implies_complete_semantics; auto.
      + apply linking_well_formedness; auto.
  Qed.

End Composition.
