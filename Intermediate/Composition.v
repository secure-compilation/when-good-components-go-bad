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

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import Intermediate.

(*
  CS components

  RB: TODO: The following results are currently only used here, but belong
  logically in CS, and should be relocated as they are proved and, where needed,
  generalized. Module qualifiers will be tweaked as needed.
*)

(* RB: NOTE: Consider possible alternatives on [CS.comes_from_initial_state]
   complemented instead by, say, [PS.step] based on what we usually have in
   the context, making for more direct routes. *)
Lemma comes_from_initial_state_step_trans p s t s' :
  CS.comes_from_initial_state s (prog_interface p) ->
  CS.step (prepare_global_env p) s t s' ->
  CS.comes_from_initial_state s' (prog_interface p).
Admitted. (* Grade 2. *)

(*
  PS components

  RB: TODO: The following results are currently only used here, but belong
  logically in PS, and should be relocated as they are proved and, where needed,
  generalized. Module qualifiers will be tweaked as needed.
*)

(* RB: TODO: More properly, this seems to belong in Machine.Memory. However, it
   is natural to resort to a notion of partial memory that seems logically
   related to the supporting components of PS. Again, note, however, that this
   notion of partial memory is already used in the Memory module, and it may be
   a good idea to relocate our compact definitions there. *)
Lemma program_store_to_partialized_memory
      ptr (iface : Program.interface) mem mem' v :
  Pointer.component ptr \in domm iface ->
  Memory.store mem ptr v = Some mem' ->
  PS.to_partial_memory mem (domm iface) = PS.to_partial_memory mem' (domm iface).
Admitted. (* Grade 2. *)

(* RB: TODO: Same notes as above.
   Cf.  program_allocation_in_partialized_memory_strong. *)
Lemma program_allocation_to_partialized_memory
      C (iface : Program.interface) size mem mem' ptr :
  C \in domm iface ->
  Memory.alloc mem C size = Some (mem', ptr) ->
  PS.to_partial_memory mem (domm iface) = PS.to_partial_memory mem' (domm iface).
Admitted. (* Grade 2. *)

(* RB: TODO: On a related note to that above, consider using [Pointer.component]
   in results such as [program_store_in_partialized_memory]. This will save us
   the trouble of having to destruct pointers to use these results. *)

(* RB: TODO: Consider necessary assumptions in a way that most closely matches
   the contexts we will use this on. Do away with uses of [domm] here?*)
Lemma to_partial_memory_merge_memories_left
      (mem1 mem2 : Memory.t) (iface1 iface2 : Program.interface) :
  mergeable_interfaces iface1 iface2 ->
  PS.to_partial_memory
    (PS.merge_memories (PS.to_partial_memory mem1 (domm iface1))
                       (PS.to_partial_memory mem2 (domm iface2)))
    (domm iface1) =
  PS.to_partial_memory mem1 (domm iface1).
Admitted. (* Grade 1. *)

Lemma to_partial_memory_merge_memories_right
      (mem1 mem2 : Memory.t) (iface1 iface2 : Program.interface) :
  mergeable_interfaces iface1 iface2 ->
  PS.to_partial_memory
    (PS.merge_memories (PS.to_partial_memory mem1 (domm iface1))
                       (PS.to_partial_memory mem2 (domm iface2)))
    (domm iface2) =
  PS.to_partial_memory mem2 (domm iface2).
Admitted. (* Grade 1. *)

(* RB: TODO: Add stack well-formedness w.r.t. interfaces. *)
Lemma merge_stacks_partition:
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall gps mem regs pc,
    CS.comes_from_initial_state (gps, mem, regs, pc) (unionm ctx1 ctx2) ->
    PS.unpartialize_stack
      (PS.merge_stacks
         (PS.to_partial_stack gps (domm ctx1))
         (PS.to_partial_stack gps (domm ctx2)))
    = gps.
Admitted. (* Grade 2. *)

(* RB: TODO: Add stack well-formedness w.r.t. interfaces. *)
Lemma merge_stacks_partition_emptym:
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall gps mem regs pc,
    CS.comes_from_initial_state (gps, mem, regs, pc) (unionm ctx1 ctx2) ->
    PS.merge_stacks (PS.to_partial_stack gps (domm ctx1))
                    (PS.to_partial_stack gps (domm ctx2)) =
    PS.to_partial_stack gps fset0.
Admitted. (* Grade 2. *)

Lemma unpartialize_stack_frame_partition:
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall ptr,
    PS.unpartialize_stack_frame
      (PS.merge_stack_frames ((PS.to_partial_frame (domm ctx1) ptr),
                              (PS.to_partial_frame (domm ctx2) ptr))) =
    ptr.
Admitted. (* Grade 1. *)

Lemma unpartialize_stack_merge_stacks_cons_partition:
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall ptr pgps1 pgps2,
    PS.unpartialize_stack
      (PS.merge_stacks (PS.to_partial_frame (domm ctx1) ptr :: pgps1)
                       (PS.to_partial_frame (domm ctx2) ptr :: pgps2)) =
    ptr :: PS.unpartialize_stack (PS.merge_stacks pgps1 pgps2).
Proof.
  intros ctx1 ctx2 Hmerge_ifaces ptr pgps1 pgps2.
  simpl.
  rewrite (unpartialize_stack_frame_partition Hmerge_ifaces).
  reflexivity.
Qed.

(* RB: TODO: Verify the necessary hypotheses for this lemma and its sibling.
   In what provenance conditions are needed on the stacks? Can they be weaker
   than those given here? (This extends beyond extracting parts of the given
   [CS.comes_from_initial_state].) *)
Lemma to_partial_stack_merge_stacks_left:
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall gps1 mem1 regs1 pc1,
    CS.comes_from_initial_state (gps1, mem1, regs1, pc1) (unionm ctx1 ctx2) ->
  forall gps2 mem2 regs2 pc2,
    CS.comes_from_initial_state (gps2, mem2, regs2, pc2) (unionm ctx1 ctx2) ->
    PS.to_partial_stack gps1 (domm ctx1) = PS.to_partial_stack gps2 (domm ctx1) ->
    PS.to_partial_stack
      (PS.unpartialize_stack
         (PS.merge_stacks (PS.to_partial_stack gps1 (domm ctx1))
                          (PS.to_partial_stack gps2 (domm ctx2))))
      (domm ctx1) =
    PS.to_partial_stack gps1 (domm ctx1).
Admitted.

Lemma to_partial_stack_merge_stacks_right:
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall gps1 mem1 regs1 pc1,
    CS.comes_from_initial_state (gps1, mem1, regs1, pc1) (unionm ctx1 ctx2) ->
  forall gps2 mem2 regs2 pc2,
    CS.comes_from_initial_state (gps2, mem2, regs2, pc2) (unionm ctx1 ctx2) ->
    PS.to_partial_stack gps1 (domm ctx1) = PS.to_partial_stack gps2 (domm ctx1) ->
    PS.to_partial_stack
      (PS.unpartialize_stack
         (PS.merge_stacks (PS.to_partial_stack gps1 (domm ctx1))
                          (PS.to_partial_stack gps2 (domm ctx2))))
      (domm ctx2) =
    PS.to_partial_stack gps2 (domm ctx2).
Admitted.

Lemma merge_memories_partition:
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall gps mem regs pc,
    CS.comes_from_initial_state (gps, mem, regs, pc) (unionm ctx1 ctx2) ->
    PS.merge_memories
      (PS.to_partial_memory mem (domm ctx1))
      (PS.to_partial_memory mem (domm ctx2))
  = mem.
Admitted. (* Grade 2. *)

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
    unfold PS.to_partial_memory in *.
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
Admitted. (* Grade 1. *)

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

Lemma st_starN_one:
  forall p ctx G s1 t s2,
    PS.step p ctx G s1 t s2 ->
    same_turn ctx s1 s2 ->
    st_starN p ctx G 1 s1 t s2.
Proof.
  intros p ctx G s1 t s2 Hstep Hsame_turn.
  eapply st_starN_step.
  - apply Hstep.
  - apply Hsame_turn.
  - apply st_starN_refl.
  - rewrite E0_right. reflexivity.
Qed.

Lemma st_starN_trans:
  forall p ctx G n1 s1 t1 s2,
    st_starN p ctx G n1 s1 t1 s2 ->
  forall n2 t2 s3,
    st_starN p ctx G n2 s2 t2 s3 ->
  forall n12,
    n12 = n1 + n2 ->
  forall t12,
    t12 = t1 ** t2 ->
    st_starN p ctx G n12 s1 t12 s3.
Proof.
  intros p ctx G n1.
  induction n1 as [| n1' IHn1'];
    intros s1 t1 s2 H n2 t2 s3 H0 n12 H1 t12 H2.
  - simpl in *; subst.
    inversion H; subst.
    apply H0.
  - inversion H as [| ? ? t1' s2' t2' ? ? Hstep' Hsame_turn' Hst_starN']; subst.
    (* NOTE: Why does the usual eq_refl trick not work here? *)
    assert (n1' + n2 = n1' + n2) as Hn' by reflexivity.
    assert (t2' ** t2 = t2' ** t2) as Ht' by reflexivity.
    specialize (IHn1' _ _ _ Hst_starN' _ _ _ H0
                      _ Hn' _ Ht').
    assert (t1' ** (t2' ** t2) = t1' ** (t2' ** t2)) as Ht'' by reflexivity.
    pose proof st_starN_step Hstep' Hsame_turn' IHn1' Ht'' as Hst_starN.
    rewrite Eapp_assoc.
    apply Hst_starN.
Qed.

(* This helper is not a fundamental lemma and can be derived easily from the
   elementary results above. *)
Lemma st_starN_event_split:
  forall p ctx G n s1 t1 e t2 s2,
    st_starN p ctx G n s1 (t1 ** [e] ** t2) s2 ->
  exists n1 s1' s2' n2,
    st_starN p ctx G n1 s1 t1 s1' /\
    PS.step p ctx G s1' [e] s2' /\
    same_turn ctx s1' s2' /\
    st_starN p ctx G n2 s2' t2 s2 /\
    n = n1 + 1 + n2.
Admitted. (* Grade 2. *)

(* RB: This kind of result seems to point to a possible relocation of the
   "turn stars", possibly to PS, or to their own dedicated module.
   NOTE: The statement of this lemma is stronger than strictly necessary if the
   star runs in the context: here, the number of steps is irrelevant to us:
   only the traces need to coincide. *)
Lemma state_determinism_st_starN:
  forall p ctx G n s1 t s2,
    st_starN p ctx G n s1 t s2 ->
  forall s2',
    st_starN p ctx G n s1 t s2' ->
    s2 = s2'.
Admitted. (* Grade 2. *)

Inductive st_starNR (p: program) (ctx: Program.interface) (G: global_env)
  : nat -> PS.state -> trace -> PS.state -> Prop :=
| st_starNR_refl: forall ips,
    st_starNR p ctx G 0 ips E0 ips
| st_starNR_step: forall n ips t1 ips' t2 ips'' t,
    st_starNR p ctx G n ips t1 ips' ->
    PS.step p ctx G ips' t2 ips'' ->
    same_turn ctx ips' ips'' ->
    t = t1 ** t2 ->
    st_starNR p ctx G (S n) ips t ips''.

Lemma st_starNR_one:
  forall p ctx G s1 t s2,
    PS.step p ctx G s1 t s2 ->
    same_turn ctx s1 s2 ->
    st_starNR p ctx G 1 s1 t s2.
Proof.
  intros p ctx G s1 t s2 Hstep Hsame_turn.
  eapply st_starNR_step.
  - apply st_starNR_refl.
  - apply Hstep.
  - apply Hsame_turn.
  - reflexivity.
Qed.

Lemma st_starNR_trans:
  forall p ctx G n1 s1 t1 s2,
    st_starNR p ctx G n1 s1 t1 s2 ->
  forall n2 t2 s3,
    st_starNR p ctx G n2 s2 t2 s3 ->
  forall n12,
    n12 = n1 + n2 ->
  forall t12,
    t12 = t1 ** t2 ->
    st_starNR p ctx G n12 s1 t12 s3.
Proof.
  intros p ctx G n1 s1 t1 s2 Hst_starNR1 n2 t2 s3 Hst_starNR2.
  generalize dependent Hst_starNR1.
  generalize dependent t1.
  generalize dependent s1.
  generalize dependent n1.
  induction Hst_starNR2
    as [| n s1 t1 s2 t2 s3 t Hst_starNR IHHst_starNR2 Hstep Hsame_turn Ht];
    intros n1 s1' t1' Hst_starNR1 n12 Hn12 t12 Ht12.
  - rewrite plus_comm in Hn12.
    rewrite E0_right in Ht12.
    subst n12 t12.
    apply Hst_starNR1.
  - subst n12 t12.
    assert (n1 + n = n1 + n) as Hn' by reflexivity.
    assert (t1' ** t1 = t1' ** t1) as Ht' by reflexivity.
    specialize (IHHst_starNR2 _ _ _ Hst_starNR1 _ Hn' _ Ht').
    assert ((t1' ** t1) ** t2 = (t1' ** t1) ** t2) as Ht'' by reflexivity.
    pose proof st_starNR_step IHHst_starNR2 Hstep Hsame_turn Ht'' as Hst_starNR'.
    subst t.
    rewrite <- Eapp_assoc.
    rewrite <- Nat.add_succ_comm.
    apply Hst_starNR'.
Qed.

Lemma st_starN_if_st_starNR:
  forall p ctx G n ips t ips',
    st_starNR p ctx G n ips t ips' ->
    st_starN p ctx G n ips t ips'.
Proof.
  intros p ctx G n ips t ips' Hst_starNR.
  induction Hst_starNR
    as [| n s1 t1 s2 t2 s3 t Hst_starNR Hst_starN Hstep Hsame_turn Ht].
  - apply st_starN_refl.
  - apply st_starN_one in Hstep.
    + assert (n + 1 = n + 1) as Hn' by reflexivity.
      assert (t1 ** t2 = t1 ** t2) as Ht' by reflexivity.
      pose proof st_starN_trans Hst_starN Hstep Hn' Ht' as Hst_starN'.
      subst t.
      rewrite plus_comm in Hst_starN'.
      apply Hst_starN'.
    + apply Hsame_turn.
Qed.

Lemma st_starNR_if_st_starN:
  forall p ctx G n ips t ips',
    st_starN p ctx G n ips t ips' ->
    st_starNR p ctx G n ips t ips'.
Proof.
  intros p ctx G n ips t ips' Hst_starN.
  induction Hst_starN
    as [| n s1 t1 s2 t2 s3 t Hstep Hsame_turn Hst_starN Hst_starNR Ht].
  - apply st_starNR_refl.
  - apply st_starNR_one in Hstep.
    + assert (n + 1 = 1 + n) as Hn' by (rewrite plus_comm; reflexivity).
      assert (t1 ** t2 = t1 ** t2) as Ht' by reflexivity.
      pose proof st_starNR_trans Hstep Hst_starNR Hn' Ht' as Hst_starN'.
      subst t.
      rewrite plus_comm in Hst_starN'.
      apply Hst_starN'.
    + apply Hsame_turn.
Qed.

Theorem st_starN_iff_st_starNR:
  forall p ctx G n ips t ips',
    st_starN p ctx G n ips t ips' <->
    st_starNR p ctx G n ips t ips'.
Proof.
  split.
  - apply st_starNR_if_st_starN.
  - apply st_starN_if_st_starNR.
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
      CS.comes_from_initial_state ics (unionm (prog_interface prog) ctx) ->
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
      CS.comes_from_initial_state ics (unionm (prog_interface prog) ctx) ->
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

Ltac CS_step_of_executing :=
  match goal with
  | H : executing _ _ ?INSTR |- _ =>
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

Module ProgCtxSim.
Section Simulation.
  Variables p c: program.

  Hypothesis wf1 : well_formed_program p.
  Hypothesis wf2 : well_formed_program c.

  Hypothesis linkability: linkable (prog_interface p) (prog_interface c).

  Hypothesis main_linkability: linkable_mains p c.

  Hypothesis prog_is_closed:
    closed_program (program_link p c).

  Hypothesis mergeable_interfaces:
    mergeable_interfaces (prog_interface p) (prog_interface c).

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
      ProgramSem.initial_state p (prog_interface c) ips1 ->
    exists ips2,
      ContextSem.initial_state c (prog_interface p) ips2 /\
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
          PS.to_partial_memory mem (domm (prog_interface p)))).
    split.
    - econstructor.
      + apply CS.comes_from_initial_state_mergeable_sym; eassumption.
      + constructor.
        * PS.simplify_turn. eapply PS.domm_partition; eassumption.
        * reflexivity.
        * reflexivity.
      + PS.simplify_turn. eapply PS.domm_partition; eassumption.
    - econstructor.
      + eapply mergeable_interfaces_sym; eassumption.
      + apply CS.comes_from_initial_state_mergeable_sym; eassumption.
      + eassumption.
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
      as [[[[gps mem] regs] pc] ? ? Hmerge_ifaces Hini Hpartial1 Hpartial2]; subst.
    (* Before inverting partial states, some work for both domm_partition cases
       (includes the decomposition of the CS state above). *)
    inversion Hmerge_ifaces as [[_ Hdisjoint] _].
    rewrite (unionmC Hdisjoint) in Hini.
    (* Proceed to case analysis. *)
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
      [ destruct (PS.domm_partition_in_neither Hmerge_iface Hfrom_initial Hpc1 Hpc2)
      |
      | destruct (PS.domm_partition_in_notin Hcc1 Hpc1)
      | destruct (PS.domm_partition_in_both Hmerge_iface Hcc1 Hcc2)].
    inversion Hstep_ps
      as [p' ? ? ? ics1 ics1' Hsame_iface _ Hwf2' Hlinkable Hmains Hstep_cs Hpartial Hpartial'];
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
    inversion Hstep_cs; subst;
      PS.rename_op p pc p' Hop.

    - (* INop *)
      match goal with
      | |- context[PS.CC (?C, ?GPS, ?MEM)] =>
        exists (PS.CC (C, GPS, MEM))
      end.
      split.
      + constructor.
        * easy.
        * easy.
        * econstructor.
          -- reflexivity.
          -- assumption.
          -- assumption.
          -- eapply linkable_sym; eassumption.
          -- exact (linkable_mains_sym main_linkability).
          -- CS_step_of_executing; try reflexivity.
             unfold executing in Hop.
             rewrite (genv_procedures_program_link_left_in Hcc2 wf1 Hwf2' Hlinkable Hmains) in Hop.
             unfold executing.
             rewrite <- (program_linkC wf1 wf2 linkability).
             erewrite (genv_procedures_program_link_left_in
                         Hcc2 wf1 wf2 linkability main_linkability).
             eassumption.
          -- econstructor.
             ++ assumption.
             ++ reflexivity.
             ++ reflexivity.
          -- rewrite <- Pointer.inc_preserves_component.
             econstructor.
             ++ rewrite Pointer.inc_preserves_component.
                assumption.
             ++ reflexivity.
             ++ reflexivity.
      + rewrite <- Hmem.
        rewrite <- Hstk.
        match goal with
        | |- PS.mergeable_states _ _ ?PC ?CC =>
          eapply PS.mergeable_states_intro
            with (ics := PS.unpartialize (PS.merge_partial_states PC CC))
        end.
        * easy.
        * simpl.
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          {
            (* RB: TODO: Refactor into lemma (cf. other cases). *)
            inversion mergeable_interfaces as [[_ Hdisjoint] _]. rewrite fdisjointC in Hdisjoint.
            rewrite (unionmC Hdisjoint) in Hfrom_initial.
            rewrite (unionmC Hdisjoint).
            eapply (PS.comes_from_initial_state_step_trans Hfrom_initial); try easy.
            unfold PS.partialize.
            apply PS.notin_to_in_false in Hpc1. rewrite Hpc1.
            apply PS.notin_to_in_false in Hpc1'. rewrite Hpc1'.
            rewrite Hmem. rewrite Hmem in Hstep_ps.
            rewrite Hstk. rewrite Hstk in Hstep_ps.
            exact Hstep_ps.
          }
        * constructor.
          -- assumption.
          -- by rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          -- by rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
        * simpl.
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite <- Pointer.inc_preserves_component.
          constructor.
          -- by rewrite Pointer.inc_preserves_component.
          -- reflexivity.
          -- reflexivity.

    (* The next few cases admit the same pattern as above, sometimes with very
       minor generalizations. *)

    - (* ILabel *)
      match goal with
      | |- context[PS.CC (?C, ?GPS, ?MEM)] =>
        exists (PS.CC (C, GPS, MEM))
      end.
      split.
      + constructor.
        * easy.
        * easy.
        * econstructor.
          -- reflexivity.
          -- assumption.
          -- assumption.
          -- eapply linkable_sym; eassumption.
          -- exact (linkable_mains_sym main_linkability).
          -- CS_step_of_executing; try reflexivity.
             unfold executing in Hop.
             rewrite (genv_procedures_program_link_left_in Hcc2 wf1 Hwf2' Hlinkable Hmains) in Hop.
             unfold executing.
             rewrite <- (program_linkC wf1 wf2 linkability).
             erewrite (genv_procedures_program_link_left_in
                         Hcc2 wf1 wf2 linkability main_linkability).
             eassumption. (* Change: existential. *)
          -- econstructor.
             ++ assumption.
             ++ reflexivity.
             ++ reflexivity.
          -- rewrite <- Pointer.inc_preserves_component.
             econstructor.
             ++ rewrite Pointer.inc_preserves_component.
                assumption.
             ++ reflexivity.
             ++ reflexivity.
      + rewrite <- Hmem.
        rewrite <- Hstk.
        match goal with
        | |- PS.mergeable_states _ _ ?PC ?CC =>
          eapply PS.mergeable_states_intro
            with (ics := PS.unpartialize (PS.merge_partial_states PC CC))
        end.
        * easy.
        * simpl.
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          {
            (* RB: TODO: Refactor into lemma (cf. other cases). *)
            inversion mergeable_interfaces as [[_ Hdisjoint] _]. rewrite fdisjointC in Hdisjoint.
            rewrite (unionmC Hdisjoint) in Hfrom_initial.
            rewrite (unionmC Hdisjoint).
            eapply (PS.comes_from_initial_state_step_trans Hfrom_initial); try easy.
            unfold PS.partialize.
            apply PS.notin_to_in_false in Hpc1. rewrite Hpc1.
            apply PS.notin_to_in_false in Hpc1'. rewrite Hpc1'.
            rewrite Hmem. rewrite Hmem in Hstep_ps.
            rewrite Hstk. rewrite Hstk in Hstep_ps.
            exact Hstep_ps.
          }
        * constructor.
          -- assumption.
          -- by rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          -- by rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
        * simpl.
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite <- Pointer.inc_preserves_component.
          constructor.
          -- by rewrite Pointer.inc_preserves_component.
          -- reflexivity.
          -- reflexivity.

    - (* IConst *)
      match goal with
      | |- context[PS.CC (?C, ?GPS, ?MEM)] =>
        exists (PS.CC (C, GPS, MEM))
      end.
      split.
      + constructor.
        * easy.
        * easy.
        * econstructor.
          -- reflexivity.
          -- assumption.
          -- assumption.
          -- eapply linkable_sym; eassumption.
          -- exact (linkable_mains_sym main_linkability).
          -- CS_step_of_executing; try reflexivity.
             unfold executing in Hop.
             rewrite (genv_procedures_program_link_left_in Hcc2 wf1 Hwf2' Hlinkable Hmains) in Hop.
             unfold executing.
             rewrite <- (program_linkC wf1 wf2 linkability).
             erewrite (genv_procedures_program_link_left_in
                         Hcc2 wf1 wf2 linkability main_linkability).
             eassumption. (* Change: existential. *)
          -- econstructor.
             ++ assumption.
             ++ reflexivity.
             ++ reflexivity.
          -- rewrite <- Pointer.inc_preserves_component.
             econstructor.
             ++ rewrite Pointer.inc_preserves_component.
                assumption.
             ++ reflexivity.
             ++ reflexivity.
      + rewrite <- Hmem.
        rewrite <- Hstk.
        match goal with
        | |- PS.mergeable_states _ _ ?PC ?CC =>
          eapply PS.mergeable_states_intro
            with (ics := PS.unpartialize (PS.merge_partial_states PC CC))
        end.
        * easy.
        * simpl.
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          {
            (* RB: TODO: Refactor into lemma (cf. other cases). *)
            inversion mergeable_interfaces as [[_ Hdisjoint] _]. rewrite fdisjointC in Hdisjoint.
            rewrite (unionmC Hdisjoint) in Hfrom_initial.
            rewrite (unionmC Hdisjoint).
            eapply (PS.comes_from_initial_state_step_trans Hfrom_initial); try easy.
            unfold PS.partialize.
            apply PS.notin_to_in_false in Hpc1. rewrite Hpc1.
            apply PS.notin_to_in_false in Hpc1'. rewrite Hpc1'.
            rewrite Hmem. rewrite Hmem in Hstep_ps.
            rewrite Hstk. rewrite Hstk in Hstep_ps.
            exact Hstep_ps.
          }
        * constructor.
          -- assumption.
          -- by rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          -- by rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
        * simpl.
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite <- Pointer.inc_preserves_component.
          constructor.
          -- by rewrite Pointer.inc_preserves_component.
          -- reflexivity.
          -- reflexivity.

    - (* IMov *)
      match goal with
      | |- context[PS.CC (?C, ?GPS, ?MEM)] =>
        exists (PS.CC (C, GPS, MEM))
      end.
      split.
      + constructor.
        * easy.
        * easy.
        * econstructor.
          -- reflexivity.
          -- assumption.
          -- assumption.
          -- eapply linkable_sym; eassumption.
          -- exact (linkable_mains_sym main_linkability).
          -- CS_step_of_executing; try reflexivity.
             unfold executing in Hop.
             rewrite (genv_procedures_program_link_left_in Hcc2 wf1 Hwf2' Hlinkable Hmains) in Hop.
             unfold executing.
             rewrite <- (program_linkC wf1 wf2 linkability).
             erewrite (genv_procedures_program_link_left_in
                         Hcc2 wf1 wf2 linkability main_linkability).
             eassumption. (* Change: existential. *)
          -- econstructor.
             ++ assumption.
             ++ reflexivity.
             ++ reflexivity.
          -- rewrite <- Pointer.inc_preserves_component.
             econstructor.
             ++ rewrite Pointer.inc_preserves_component.
                assumption.
             ++ reflexivity.
             ++ reflexivity.
      + rewrite <- Hmem.
        rewrite <- Hstk.
        match goal with
        | |- PS.mergeable_states _ _ ?PC ?CC =>
          eapply PS.mergeable_states_intro
            with (ics := PS.unpartialize (PS.merge_partial_states PC CC))
        end.
        * easy.
        * simpl.
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          {
            (* RB: TODO: Refactor into lemma (cf. other cases). *)
            inversion mergeable_interfaces as [[_ Hdisjoint] _]. rewrite fdisjointC in Hdisjoint.
            rewrite (unionmC Hdisjoint) in Hfrom_initial.
            rewrite (unionmC Hdisjoint).
            eapply (PS.comes_from_initial_state_step_trans Hfrom_initial); try easy.
            unfold PS.partialize.
            apply PS.notin_to_in_false in Hpc1. rewrite Hpc1.
            apply PS.notin_to_in_false in Hpc1'. rewrite Hpc1'.
            rewrite Hmem. rewrite Hmem in Hstep_ps.
            rewrite Hstk. rewrite Hstk in Hstep_ps.
            exact Hstep_ps.
          }
        * constructor.
          -- assumption.
          -- by rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          -- by rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
        * simpl.
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite <- Pointer.inc_preserves_component.
          constructor.
          -- by rewrite Pointer.inc_preserves_component.
          -- reflexivity.
          -- reflexivity.

    - (* IBinOp *)
      match goal with
      | |- context[PS.CC (?C, ?GPS, ?MEM)] =>
        exists (PS.CC (C, GPS, MEM))
      end.
      split.
      + constructor.
        * easy.
        * easy.
        * econstructor.
          -- reflexivity.
          -- assumption.
          -- assumption.
          -- eapply linkable_sym; eassumption.
          -- exact (linkable_mains_sym main_linkability).
          -- CS_step_of_executing; try reflexivity.
             unfold executing in Hop.
             rewrite (genv_procedures_program_link_left_in Hcc2 wf1 Hwf2' Hlinkable Hmains) in Hop.
             unfold executing.
             rewrite <- (program_linkC wf1 wf2 linkability).
             erewrite (genv_procedures_program_link_left_in
                         Hcc2 wf1 wf2 linkability main_linkability).
             eassumption. (* Change: existential. *)
          -- econstructor.
             ++ assumption.
             ++ reflexivity.
             ++ reflexivity.
          -- rewrite <- Pointer.inc_preserves_component.
             econstructor.
             ++ rewrite Pointer.inc_preserves_component.
                assumption.
             ++ reflexivity.
             ++ reflexivity.
      + rewrite <- Hmem.
        rewrite <- Hstk.
        match goal with
        | |- PS.mergeable_states _ _ ?PC ?CC =>
          eapply PS.mergeable_states_intro
            with (ics := PS.unpartialize (PS.merge_partial_states PC CC))
        end.
        * easy.
        * simpl.
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          {
            (* RB: TODO: Refactor into lemma (cf. other cases). *)
            inversion mergeable_interfaces as [[_ Hdisjoint] _]. rewrite fdisjointC in Hdisjoint.
            rewrite (unionmC Hdisjoint) in Hfrom_initial.
            rewrite (unionmC Hdisjoint).
            eapply (PS.comes_from_initial_state_step_trans Hfrom_initial); try easy.
            unfold PS.partialize.
            apply PS.notin_to_in_false in Hpc1. rewrite Hpc1.
            apply PS.notin_to_in_false in Hpc1'. rewrite Hpc1'.
            rewrite Hmem. rewrite Hmem in Hstep_ps.
            rewrite Hstk. rewrite Hstk in Hstep_ps.
            exact Hstep_ps.
          }
        * constructor.
          -- assumption.
          -- by rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          -- by rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
        * simpl.
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite <- Pointer.inc_preserves_component.
          constructor.
          -- by rewrite Pointer.inc_preserves_component.
          -- reflexivity.
          -- reflexivity.

    (* The cases that follow are more interesting as the first pattern finds
       problematic sub-goals in its present form. *)

    - (* ILoad *)
      assert (Hstep_cs' : CS.step (prepare_global_env (program_link p c))
                                  (gps, mem, regs, pc) E0
                                  (gps, mem, Register.set r2 v regs, Pointer.inc pc)).
      {
        (* RB: TODO: Lemma, refactoring for following cases. *)
        CS_step_of_executing; try (reflexivity || eassumption).
        - eapply execution_invariant_to_linking; eassumption.
        - destruct ptr as [[C b] o].
          eapply program_load_in_partialized_memory_strong.
          + exact (eq_sym Hmem).
          + PS.simplify_turn. subst C. assumption.
          + assumption.
      }
      match goal with
      | |- context[PS.CC (?C, ?GPS, ?MEM)] =>
        exists (PS.CC (C, GPS, MEM))
      end.
      split.
      + constructor.
        * easy.
        * apply Hcc2.
        * pose proof PS.context_epsilon_step_is_silent. econstructor.
          -- reflexivity.
          -- assumption.
          -- assumption.
          -- eapply linkable_sym; eassumption.
          -- exact (linkable_mains_sym main_linkability).
          -- rewrite program_linkC.
             apply Hstep_cs'.
             ++ assumption.
             ++ assumption.
             ++ apply linkable_sym; assumption.
          -- assumption.
          -- pose proof PS.partialized_state_is_partial
                  (gps, mem, Register.set r2 v regs, Pointer.inc pc)
                  (prog_interface p)
               as Hpartial''.
             assert (Htmp : Pointer.component (Pointer.inc pc) \in domm (prog_interface p))
               by now rewrite Pointer.inc_preserves_component.
             unfold PS.partialize in Hpartial''.
             rewrite Htmp in Hpartial''.
             rewrite Pointer.inc_preserves_component in Hpartial''.
             assumption.
      + rewrite <- Hmem.
        rewrite <- Hstk.
        match goal with
        | |- PS.mergeable_states _ _ ?PC ?CC =>
          eapply PS.mergeable_states_intro
            with (ics := PS.unpartialize (PS.merge_partial_states PC CC))
        end.
        * easy.
        * simpl.
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          {
            (* RB: TODO: Refactor into lemma (cf. other cases). *)
            inversion mergeable_interfaces as [[_ Hdisjoint] _]. rewrite fdisjointC in Hdisjoint.
            rewrite (unionmC Hdisjoint) in Hfrom_initial.
            rewrite (unionmC Hdisjoint).
            eapply (PS.comes_from_initial_state_step_trans Hfrom_initial); try easy.
            unfold PS.partialize.
            apply PS.notin_to_in_false in Hpc1. rewrite Hpc1.
            apply PS.notin_to_in_false in Hpc1'. rewrite Hpc1'.
            rewrite Hmem. rewrite Hmem in Hstep_ps.
            rewrite Hstk. rewrite Hstk in Hstep_ps.
            exact Hstep_ps.
          }
        * constructor.
          -- assumption.
          -- by rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          -- by rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
        * simpl.
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite <- Pointer.inc_preserves_component.
          constructor.
          -- by rewrite Pointer.inc_preserves_component.
          -- reflexivity.
          -- reflexivity.

    - (* IStore *)
      destruct ptr as [[C b] o] eqn:Hptr.
      PS.simplify_turn. subst C.
      match goal with
      | H : Memory.store _ _ _ = _ |- _ =>
        (* RB: TODO: Destruct and name proof term. *)
        destruct (program_store_in_partialized_memory_strong (eq_sym Hmem) Hpc_partial H)
          as [mem' Hmem']
      end.
      assert (Hstep_cs' : CS.step (prepare_global_env (program_link p c))
                                  (gps, mem, regs1', pc) E0
                                  (gps,
                                   PS.merge_memories
                                     (PS.to_partial_memory mem1 (domm (prog_interface c)))
                                     (PS.to_partial_memory mem (domm (prog_interface p))),
                                   regs1',
                                   Pointer.inc pc)).
      {
        CS_step_of_executing; try (reflexivity || eassumption).
        - eapply execution_invariant_to_linking; eassumption.
        - rewrite Hmem'.
          (* RB: TODO: H is the proof introduced above. *)
          unfold PS.to_partial_memory. rewrite H.
          assert (Hcc2' : Pointer.component ptr \in domm (prog_interface p))
            by now rewrite Hptr.
          rewrite Hptr in Hcc2'.
          pose proof program_store_to_partialized_memory Hcc2' Hmem' as Hmem''.
          unfold PS.to_partial_memory in Hmem''. rewrite Hmem''.
          admit.
      }
      match goal with
      | |- context[PS.CC (?C, ?GPS, ?MEM)] =>
        exists (PS.CC (C, GPS, MEM))
      end.
      split.
      + constructor.
        * easy.
        * apply Hcc2.
        * pose proof PS.context_epsilon_step_is_silent. econstructor.
          -- reflexivity.
          -- assumption.
          -- assumption.
          -- eapply linkable_sym; eassumption.
          -- exact (linkable_mains_sym main_linkability).
          -- rewrite program_linkC.
             apply Hstep_cs'.
             ++ assumption.
             ++ assumption.
             ++ apply linkable_sym; assumption.
          -- assumption.
          -- pose proof PS.partialized_state_is_partial
                  (gps, mem', regs1', Pointer.inc pc)
                  (prog_interface p)
               as Hpartial''.
             assert (Htmp : Pointer.component (Pointer.inc pc) \in domm (prog_interface p))
               by now rewrite Pointer.inc_preserves_component.
             unfold PS.partialize in Hpartial''.
             rewrite Htmp in Hpartial''.
             rewrite Pointer.inc_preserves_component in Hpartial''.
             (* assumption. *)
             rewrite <- Pointer.inc_preserves_component.
             constructor.
             ++ assumption.
             ++ now rewrite (to_partial_memory_merge_memories_right _ _ Hmerge_iface).
             ++ reflexivity.
      + (* rewrite <- Hmem. *)
        rewrite <- Hstk.
        match goal with
        | |- PS.mergeable_states _ _ ?PC ?CC =>
          eapply PS.mergeable_states_intro
            with (ics := PS.unpartialize (PS.merge_partial_states PC CC))
        end.
        * easy.
        * simpl.
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          (* rewrite (merge_memories_partition Hmerge_iface Hfrom_initial). *)
          {
            (* RB: TODO: Refactor into lemma (cf. other cases). *)
            inversion mergeable_interfaces as [[_ Hdisjoint] _]. rewrite fdisjointC in Hdisjoint.
            rewrite (unionmC Hdisjoint) in Hfrom_initial.
            rewrite (unionmC Hdisjoint).
            eapply (PS.comes_from_initial_state_step_trans Hfrom_initial); try easy.
            unfold PS.partialize.
            apply PS.notin_to_in_false in Hpc1. rewrite Hpc1.
            apply PS.notin_to_in_false in Hpc1'. rewrite Hpc1'.
            rewrite Hmem. rewrite Hmem in Hstep_ps.
            rewrite Hstk. rewrite Hstk in Hstep_ps.
            (* The following rewrite replaces the one above, which could be
               performed before the bracketed sequence of operations. *)
            rewrite (to_partial_memory_merge_memories_left _ _ Hmerge_iface).
            exact Hstep_ps.
          }
        * constructor.
          -- assumption.
          -- now rewrite to_partial_memory_merge_memories_left.
          -- by rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
        * simpl.
          (* rewrite (merge_memories_partition Hmerge_iface Hfrom_initial). *)
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite <- Pointer.inc_preserves_component.
          constructor.
          -- by rewrite Pointer.inc_preserves_component.
          -- now rewrite to_partial_memory_merge_memories_right.
          -- reflexivity. (* TODO: Move rewrite here? *)

    - (* IJal *)
      assert (Hstep_cs' : CS.step (prepare_global_env (program_link p c))
                                  (gps, mem, regs, pc) E0
                                  (gps, mem, Register.set R_RA (Ptr (Pointer.inc pc)) regs, pc1')).
      {
        CS_step_of_executing; try (reflexivity || eassumption).
        - eapply execution_invariant_to_linking; eassumption.
        - erewrite find_label_in_component_program_link_left; try assumption.
          match goal with
          | H : find_label_in_component _ _ _ = _ |- _ =>
            erewrite find_label_in_component_program_link_left in H; try assumption
          end.
          rewrite Hsame_iface. assumption.
      }
      match goal with
      | |- context[PS.CC (?C, ?GPS, ?MEM)] =>
        exists (PS.CC (Pointer.component pc1', GPS, MEM))
      end.
      (* Before the split, assert this fact used on both sides. *)
      assert (Hpc_pc1' : Pointer.component pc1' \in domm (prog_interface p)).
      {
        eapply PS.domm_partition.
        - exact (mergeable_interfaces_sym _ _ Hmerge_iface).
        - rewrite <- (unionmC (proj2 linkability)) in Hfrom_initial.
          eapply PS.comes_from_initial_state_step_trans.
          + exact Hfrom_initial.
          + exact Hstep_ps.
          + simpl.
            assert (Htmp : Pointer.component pc \in domm (prog_interface c) = false).
            {
              destruct (Pointer.component pc \in domm (prog_interface c)) eqn:Hcase.
              - rewrite Hcase in Hpc1. discriminate.
              - reflexivity.
            }
            rewrite Htmp.
            reflexivity.
          + simpl.
            assert (Htmp : Pointer.component pc1' \in domm (prog_interface c) = false).
            {
              destruct (Pointer.component pc1' \in domm (prog_interface c)) eqn:Hcase.
              - rewrite Hcase in Hpc_partial'. discriminate.
              - reflexivity.
            }
            rewrite Htmp.
            reflexivity.
        - assumption.
      }
      split.
      + constructor.
        * easy.
        * PS.simplify_turn. eapply PS.domm_partition; try eassumption.
          rewrite <- (unionmC (proj2 linkability)) in Hfrom_initial.
          change (unionm (prog_interface p) (prog_interface c))
            with (prog_interface (program_link p c))
            in Hfrom_initial.
          exact (comes_from_initial_state_step_trans Hfrom_initial Hstep_cs').
        * pose proof PS.context_epsilon_step_is_silent. econstructor.
          -- reflexivity.
          -- assumption.
          -- assumption.
          -- eapply linkable_sym; eassumption.
          -- exact (linkable_mains_sym main_linkability).
          -- rewrite program_linkC.
             apply Hstep_cs'.
             ++ assumption.
             ++ assumption.
             ++ apply linkable_sym; assumption.
          -- assumption.
          -- pose proof PS.partialized_state_is_partial
                  (gps, mem, Register.set R_RA (Ptr (Pointer.inc pc)) regs, pc1')
                  (prog_interface p)
               as Hpartial''.
             unfold PS.partialize in Hpartial''.
             rewrite Hpc_pc1' in Hpartial''.
             assumption.
      + rewrite <- Hmem.
        rewrite <- Hstk.
        match goal with
        | |- PS.mergeable_states _ _ ?PC ?CC =>
          eapply PS.mergeable_states_intro
            with (ics := PS.unpartialize (PS.merge_partial_states PC CC))
        end.
        * easy.
        * simpl.
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          {
            (* RB: TODO: Refactor into lemma (cf. other cases). *)
            inversion mergeable_interfaces as [[_ Hdisjoint] _]. rewrite fdisjointC in Hdisjoint.
            rewrite (unionmC Hdisjoint) in Hfrom_initial.
            rewrite (unionmC Hdisjoint).
            eapply (PS.comes_from_initial_state_step_trans Hfrom_initial); try easy.
            unfold PS.partialize.
            apply PS.notin_to_in_false in Hpc1. rewrite Hpc1.
            apply PS.notin_to_in_false in Hpc1'. rewrite Hpc1'.
            rewrite Hmem. rewrite Hmem in Hstep_ps.
            rewrite Hstk. rewrite Hstk in Hstep_ps.
            exact Hstep_ps.
          }
        * constructor.
          -- assumption.
          -- by rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          -- by rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
        * simpl.
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          (* rewrite <- Pointer.inc_preserves_component. *)
          constructor.
          -- assumption. (* Hpc_pc1' *)
          -- reflexivity.
          -- reflexivity.

    - (* IJump *)
      assert (Hstep_cs' : CS.step (prepare_global_env (program_link p c))
                                  (gps, mem, regs1', pc) E0
                                  (gps, mem, regs1', pc1')).
      {
        CS_step_of_executing; try (reflexivity || eassumption).
        - eapply execution_invariant_to_linking; eassumption.
      }
      match goal with
      | |- context[PS.CC (?C, ?GPS, ?MEM)] =>
        exists (PS.CC (Pointer.component pc1', GPS, MEM))
      end.
      (* Before splitting, we will be needing this on both sides. *)
      assert (H'pc1' : Pointer.component pc1' \in domm (prog_interface p)).
      {
        match goal with
        | H : _ = Pointer.component pc |- _ =>
          rewrite H; assumption
        end.
      }
      split.
      + constructor.
        * easy.
        * assumption.
        * pose proof PS.context_epsilon_step_is_silent. econstructor.
          -- reflexivity.
          -- assumption.
          -- assumption.
          -- eapply linkable_sym; eassumption.
          -- exact (linkable_mains_sym main_linkability).
          -- rewrite program_linkC.
             apply Hstep_cs'.
             ++ assumption.
             ++ assumption.
             ++ apply linkable_sym; assumption.
          -- assumption.
          -- pose proof PS.partialized_state_is_partial
                  (gps, mem, regs1', pc1')
                  (prog_interface p)
               as Hpartial''.
             unfold PS.partialize in Hpartial''.
             rewrite H'pc1' in Hpartial''.
             assumption.
      + rewrite <- Hmem.
        rewrite <- Hstk.
        match goal with
        | |- PS.mergeable_states _ _ ?PC ?CC =>
          eapply PS.mergeable_states_intro
            with (ics := PS.unpartialize (PS.merge_partial_states PC CC))
        end.
        * easy.
        * simpl.
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          {
            (* RB: TODO: Refactor into lemma (cf. other cases). *)
            inversion mergeable_interfaces as [[_ Hdisjoint] _]. rewrite fdisjointC in Hdisjoint.
            rewrite (unionmC Hdisjoint) in Hfrom_initial.
            rewrite (unionmC Hdisjoint).
            eapply (PS.comes_from_initial_state_step_trans Hfrom_initial); try easy.
            unfold PS.partialize.
            apply PS.notin_to_in_false in Hpc1. rewrite Hpc1.
            apply PS.notin_to_in_false in Hpc1'. rewrite Hpc1'.
            rewrite Hmem. rewrite Hmem in Hstep_ps.
            rewrite Hstk. rewrite Hstk in Hstep_ps.
            exact Hstep_ps.
          }
        * constructor.
          -- assumption.
          -- by rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          -- by rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
        * simpl.
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          (* rewrite <- Pointer.inc_preserves_component. *)
          constructor.
          -- match goal with
             | H : Pointer.component pc1' = Pointer.component pc |- _ =>
               rewrite H
             end.
             assumption.
          -- reflexivity.
          -- reflexivity.

    - (* IBnz (CS.BnzNZ) *)
      assert (Hstep_cs' : CS.step (prepare_global_env (program_link p c))
                                  (gps, mem, regs1', pc) E0
                                  (gps, mem, regs1', pc1')).
      {
        CS_step_of_executing; try (reflexivity || eassumption).
        - eapply execution_invariant_to_linking; eassumption.
        - erewrite find_label_in_procedure_program_link_left; try assumption.
          match goal with
          | H : find_label_in_procedure _ _ _ = _ |- _ =>
            erewrite find_label_in_procedure_program_link_left in H; try assumption
          end.
          rewrite Hsame_iface; assumption.
      }
      match goal with
      | |- context[PS.CC (?C, ?GPS, ?MEM)] =>
        exists (PS.CC (Pointer.component pc1', GPS, MEM))
      end.
      (* Before splitting, we will be needing this on both sides. *)
      assert (H'pc1' : Pointer.component pc1' \in domm (prog_interface p)).
      {
        eapply PS.domm_partition; try eassumption.
        (* RB: TODO: Here and elsewhere in this proof, better way to move between
           unionm and prog_interface? *)
        change (unionm (prog_interface p) (prog_interface c))
          with (prog_interface (program_link p c)).
        rewrite <- (unionmC (proj2 linkability)) in Hfrom_initial.
        change (unionm (prog_interface p) (prog_interface c))
          with (prog_interface (program_link p c))
          in Hfrom_initial.
        exact (comes_from_initial_state_step_trans Hfrom_initial Hstep_cs').
      }
      split.
      + constructor.
        * easy.
        * assumption.
        * pose proof PS.context_epsilon_step_is_silent. econstructor.
          -- reflexivity.
          -- assumption.
          -- assumption.
          -- eapply linkable_sym; eassumption.
          -- exact (linkable_mains_sym main_linkability).
          -- rewrite program_linkC.
             apply Hstep_cs'.
             ++ assumption.
             ++ assumption.
             ++ apply linkable_sym; assumption.
          -- assumption.
          -- pose proof PS.partialized_state_is_partial
                  (gps, mem, regs1', pc1')
                  (prog_interface p)
               as Hpartial''.
             unfold PS.partialize in Hpartial''.
             rewrite H'pc1' in Hpartial''.
             assumption.
      + rewrite <- Hmem.
        rewrite <- Hstk.
        match goal with
        | |- PS.mergeable_states _ _ ?PC ?CC =>
          eapply PS.mergeable_states_intro
            with (ics := PS.unpartialize (PS.merge_partial_states PC CC))
        end.
        * easy.
        * simpl.
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          {
            (* RB: TODO: Refactor into lemma (cf. other cases). *)
            inversion mergeable_interfaces as [[_ Hdisjoint] _]. rewrite fdisjointC in Hdisjoint.
            rewrite (unionmC Hdisjoint) in Hfrom_initial.
            rewrite (unionmC Hdisjoint).
            eapply (PS.comes_from_initial_state_step_trans Hfrom_initial); try easy.
            unfold PS.partialize.
            apply PS.notin_to_in_false in Hpc1. rewrite Hpc1.
            apply PS.notin_to_in_false in Hpc1'. rewrite Hpc1'.
            rewrite Hmem. rewrite Hmem in Hstep_ps.
            rewrite Hstk. rewrite Hstk in Hstep_ps.
            exact Hstep_ps.
          }
        * constructor.
          -- assumption.
          -- by rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          -- by rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
        * simpl.
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          (* rewrite <- Pointer.inc_preserves_component. *)
          constructor.
          -- assumption.
          -- reflexivity.
          -- reflexivity.

    - (* IBnz (CS.BnzZ) *)
      assert (Hstep_cs' : CS.step (prepare_global_env (program_link p c))
                                  (gps, mem, regs1', pc) E0
                                  (gps, mem, regs1', Pointer.inc pc)).
      {
        CS_step_of_executing; try (reflexivity || eassumption).
        - eapply execution_invariant_to_linking; eassumption.
      }
      match goal with
      | |- context[PS.CC (?C, ?GPS, ?MEM)] =>
        exists (PS.CC (C, GPS, MEM))
      end.
      split.
      + constructor.
        * easy.
        * assumption.
        * pose proof PS.context_epsilon_step_is_silent. econstructor.
          -- reflexivity.
          -- assumption.
          -- assumption.
          -- eapply linkable_sym; eassumption.
          -- exact (linkable_mains_sym main_linkability).
          -- rewrite program_linkC.
             apply Hstep_cs'.
             ++ assumption.
             ++ assumption.
             ++ apply linkable_sym; assumption.
          -- assumption.
          -- pose proof PS.partialized_state_is_partial
                  (gps, mem, regs1', Pointer.inc pc)
                  (prog_interface p)
               as Hpartial''.
             (* RB: NOTE: This is used at the end, as well. *)
             assert (Htmp : Pointer.component (Pointer.inc pc) \in domm (prog_interface p))
               by now rewrite Pointer.inc_preserves_component.
             unfold PS.partialize in Hpartial''.
             rewrite Htmp in Hpartial''.
             rewrite <- Pointer.inc_preserves_component.
             assumption.
      + rewrite <- Hmem.
        rewrite <- Hstk.
        match goal with
        | |- PS.mergeable_states _ _ ?PC ?CC =>
          eapply PS.mergeable_states_intro
            with (ics := PS.unpartialize (PS.merge_partial_states PC CC))
        end.
        * easy.
        * simpl.
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          {
            (* RB: TODO: Refactor into lemma (cf. other cases). *)
            inversion mergeable_interfaces as [[_ Hdisjoint] _]. rewrite fdisjointC in Hdisjoint.
            rewrite (unionmC Hdisjoint) in Hfrom_initial.
            rewrite (unionmC Hdisjoint).
            eapply (PS.comes_from_initial_state_step_trans Hfrom_initial); try easy.
            unfold PS.partialize.
            apply PS.notin_to_in_false in Hpc1. rewrite Hpc1.
            apply PS.notin_to_in_false in Hpc1'. rewrite Hpc1'.
            rewrite Hmem. rewrite Hmem in Hstep_ps.
            rewrite Hstk. rewrite Hstk in Hstep_ps.
            exact Hstep_ps.
          }
        * constructor.
          -- assumption.
          -- by rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          -- by rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
        * simpl.
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite <- Pointer.inc_preserves_component.
          constructor.
          -- rewrite Pointer.inc_preserves_component. assumption.
          -- reflexivity.
          -- reflexivity.

    - (* IAlloc *)
      (* Auxiliary assert based on the corresponding hypothesis. *)
      match goal with
      | H : Memory.alloc _ _ _ = _ |- _ =>
        (* RB: TODO: Name proof. *)
        destruct (program_allocation_in_partialized_memory_strong (eq_sym Hmem) Hpc_partial H)
          as [mem' Hmem']
      end.
      assert (Hstep_cs' : CS.step (prepare_global_env (program_link p c))
                                  (gps, mem, regs, pc) E0
                                  (gps,
                                   PS.merge_memories
                                     (PS.to_partial_memory mem1 (domm (prog_interface c)))
                                     (PS.to_partial_memory mem (domm (prog_interface p))),
                                   Register.set rptr (Ptr ptr) regs, Pointer.inc pc)).
      {
        CS_step_of_executing; try (reflexivity || eassumption).
        - eapply execution_invariant_to_linking; eassumption.
        - pose proof program_allocation_to_partialized_memory Hcc2 Hmem' as Hmem''.
          rewrite Hmem'. rewrite Hmem''.
          unfold PS.to_partial_memory. rewrite H. (* RB: TODO: H by name. *)
          admit.
      }
      match goal with
      | |- context[PS.CC (?C, ?GPS, ?MEM)] =>
        exists (PS.CC (C, GPS, MEM))
      end.
      split.
      + constructor.
        * easy.
        * assumption.
        * pose proof PS.context_epsilon_step_is_silent. econstructor.
          -- reflexivity.
          -- assumption.
          -- assumption.
          -- eapply linkable_sym; eassumption.
          -- exact (linkable_mains_sym main_linkability).
          -- rewrite program_linkC.
             apply Hstep_cs'.
             ++ assumption.
             ++ assumption.
             ++ apply linkable_sym; assumption.
          -- assumption.
          -- pose proof PS.partialized_state_is_partial
                  (gps,
                   (* RB: TODO: Here and elsewhere, notice duplicate state above. *)
                   PS.merge_memories
                     (PS.to_partial_memory mem1 (domm (prog_interface c)))
                     (PS.to_partial_memory mem (domm (prog_interface p))),
                   Register.set rptr (Ptr ptr) regs, Pointer.inc pc)
                  (prog_interface p)
               as Hpartial''.
             (* RB: NOTE: Same argument used at bottom of proof as well. *)
             assert (Htmp : Pointer.component (Pointer.inc pc) \in domm (prog_interface p))
               by now rewrite Pointer.inc_preserves_component.
             unfold PS.partialize in Hpartial''.
             rewrite Htmp in Hpartial''.
             rewrite <- Pointer.inc_preserves_component.
             rewrite (to_partial_memory_merge_memories_right _ _ Hmerge_iface) in Hpartial''.
             assumption.
      + (* rewrite <- Hmem. *)
        rewrite <- Hstk.
        match goal with
        | |- PS.mergeable_states _ _ ?PC ?CC =>
          eapply PS.mergeable_states_intro
            with (ics := PS.unpartialize (PS.merge_partial_states PC CC))
        end.
        * easy.
        * simpl.
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          (* rewrite (merge_memories_partition Hmerge_iface Hfrom_initial). *)
          {
            (* RB: TODO: Refactor into lemma (cf. other cases). *)
            inversion mergeable_interfaces as [[_ Hdisjoint] _]. rewrite fdisjointC in Hdisjoint.
            rewrite (unionmC Hdisjoint) in Hfrom_initial.
            rewrite (unionmC Hdisjoint).
            eapply (PS.comes_from_initial_state_step_trans Hfrom_initial); try easy.
            unfold PS.partialize.
            apply PS.notin_to_in_false in Hpc1. rewrite Hpc1.
            apply PS.notin_to_in_false in Hpc1'. rewrite Hpc1'.
            rewrite Hmem. rewrite Hmem in Hstep_ps.
            rewrite Hstk. rewrite Hstk in Hstep_ps.
            rewrite (to_partial_memory_merge_memories_left _ _ Hmerge_iface).
            exact Hstep_ps.
          }
        * constructor.
          -- assumption.
          -- now rewrite (to_partial_memory_merge_memories_left _ _ Hmerge_iface).
          -- by rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
        * simpl.
          (* rewrite (merge_memories_partition Hmerge_iface Hfrom_initial). *)
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite <- Pointer.inc_preserves_component.
          constructor.
          -- now rewrite Pointer.inc_preserves_component.
          -- now rewrite (to_partial_memory_merge_memories_right _ _ Hmerge_iface).
          -- reflexivity.

    (* The final cases are the most interesting in that the executing instruction
       transfers control to a different component, which may be outside the
       domain of the program, i.e., in the context's. In addition, the usual
       stock of state manipulations make their appearance. *)

    - (* ICall *)
      (* First discard the case where we step out of the program. *)
      destruct (C' \in domm (prog_interface p)) eqn:Hpc';
        last admit. (* Easy contradiction. *)
      (* Continue with the proof. *)
      assert (Hstep_cs' : CS.step (prepare_global_env (program_link p c))
                                  (gps, mem, regs, pc)
                                  [ECall (Pointer.component pc) P call_arg C']
                                  (Pointer.inc pc :: gps,
                                   mem,
                                   Register.invalidate regs, (C', b, 0%Z))).
      {
        CS_step_of_executing; try (reflexivity || eassumption).
        - eapply execution_invariant_to_linking; eassumption.
        - match goal with
          | H : imported_procedure _ _ _ _ |- _ =>
            simpl in H; rewrite Hsame_iface in H
          end.
          assumption.
        - match goal with
          | H : EntryPoint.get _ _ _ = _ |- _ =>
            rewrite <- H
          end.
          rewrite <- Hsame_iface in Hpc_partial'. simpl in Hpc_partial'.
          erewrite 2!genv_entrypoints_program_link_left; try eassumption.
          reflexivity.
      }
      match goal with
      | |- context[PS.CC (?C, ?GPS, ?MEM)] =>
        exists (PS.CC (C', PS.to_partial_frame (domm (prog_interface p)) (Pointer.inc pc) :: GPS, MEM))
      end.
      (* RB: TODO: Normalizing the stack expression for now, manually, to retain
         the part that is already determined by the match (but still not
         perfect). *)
      change
        (PS.to_partial_frame (domm (prog_interface p)) (Pointer.inc pc) ::
         PS.to_partial_stack gps (domm (prog_interface p)))
      with
        (PS.to_partial_stack (Pointer.inc pc :: gps) (domm (prog_interface p))).
      split.
      + constructor.
        * easy.
        * assumption.
        * econstructor.
          -- reflexivity.
          -- assumption.
          -- assumption.
          -- eapply linkable_sym; eassumption.
          -- exact (linkable_mains_sym main_linkability).
          -- rewrite program_linkC.
             apply Hstep_cs'.
             ++ assumption.
             ++ assumption.
             ++ apply linkable_sym; assumption.
          -- assumption.
          -- pose proof PS.partialized_state_is_partial
                  (Pointer.inc pc :: gps, mem, Register.invalidate regs, (C', b, 0%Z))
                  (prog_interface p)
               as Hpartial''.
             simpl in Hpartial''. rewrite Hpc' in Hpartial''.
             assumption.
      + rewrite <- Hmem.
        (* rewrite <- Hstk. *)
        (* Before processing the goal and looking for its constituents, prepare
           the provenance information that will be needed for all simplifications
           on partial stacks. *)
        assert (Hprov : CS.comes_from_initial_state
                          (gps, mem, regs, pc)
                          (unionm (prog_interface c) (prog_interface p)))
          by assumption.
        (* RB: TODO: The provenance of the second stack is fully expected, though
           not directly available from the context. [Hstep_cs] offers a starting
           point for completing this step. *)
        assert (Hprov' : CS.comes_from_initial_state
                           (gps0, mem1, regs, pc)
                           (unionm (prog_interface c) (prog_interface p)))
          by admit.
        (* Continue with the regular proof. *)
        match goal with
        | |- PS.mergeable_states _ _ ?PC ?CC =>
          eapply PS.mergeable_states_intro
            with (ics := PS.unpartialize (PS.merge_partial_states PC CC))
        end.
        * easy.
        * (* simpl. *)
          unfold PS.unpartialize.
          unfold PS.merge_partial_states; fold PS.merge_partial_states.
          (* rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial). *)
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          {
            (* RB: TODO: Refactor into lemma (cf. other cases). *)
            inversion mergeable_interfaces as [[_ Hdisjoint] _]. rewrite fdisjointC in Hdisjoint.
            rewrite (unionmC Hdisjoint) in Hfrom_initial.
            rewrite (unionmC Hdisjoint).
            eapply (PS.comes_from_initial_state_step_trans Hfrom_initial); try easy.
            unfold PS.partialize.
            apply PS.notin_to_in_false in Hpc1. rewrite Hpc1.
            apply PS.notin_to_in_false in Hpc1'. rewrite Hpc1'.
            rewrite Hmem. rewrite Hmem in Hstep_ps.
            rewrite Hstk. rewrite Hstk in Hstep_ps.
            (* rewrite (to_partial_memory_merge_memories_left _ _ Hmerge_iface). *)
            rewrite (unpartialize_stack_merge_stacks_cons_partition Hmerge_iface).
            simpl.
            (* RB: TODO: The rewrite mangles the goal horribly; for now, [change]
               this back to an orderly form. [match goal] is of course better if
               an easier way does not avail. This problem occurs in identical
               form in all three instances where the above rewrite is used (and
               before [simpl] is used to expose the structure unveiled by the
               rewrite more explicitly, paving the way for the application of the
               second rewrite. *)
            change
              (PS.merge_stacks
                 ((fix map (l : list Pointer.t) : list PS.PartialPointer.t :=
                     match l with
                     | [] => []
                     | a :: t => PS.to_partial_frame (domm (prog_interface c)) a :: map t
                     end) gps0)
                 ((fix map (l : list Pointer.t) : list PS.PartialPointer.t :=
                     match l with
                     | [] => []
                     | a :: t => PS.to_partial_frame (domm (prog_interface p)) a :: map t
                     end) gps))
            with
              (PS.merge_stacks (PS.to_partial_stack gps0 (domm (prog_interface c)))
                               (PS.to_partial_stack gps (domm (prog_interface p)))).
            rewrite (to_partial_stack_merge_stacks_left Hmerge_iface Hprov' Hprov (eq_sym Hstk)).
            exact Hstep_ps.
          }
        * constructor.
          -- assumption.
          -- now rewrite (to_partial_memory_merge_memories_left _ _ Hmerge_iface).
          -- rewrite (unpartialize_stack_merge_stacks_cons_partition Hmerge_iface).
             simpl.
             change
               (PS.merge_stacks
                  ((fix map (l : list Pointer.t) : list PS.PartialPointer.t :=
                      match l with
                      | [] => []
                      | a :: t => PS.to_partial_frame (domm (prog_interface c)) a :: map t
                      end) gps0)
                  ((fix map (l : list Pointer.t) : list PS.PartialPointer.t :=
                      match l with
                      | [] => []
                      | a :: t => PS.to_partial_frame (domm (prog_interface p)) a :: map t
                      end) gps))
             with
               (PS.merge_stacks (PS.to_partial_stack gps0 (domm (prog_interface c)))
                                (PS.to_partial_stack gps (domm (prog_interface p)))).
             rewrite (to_partial_stack_merge_stacks_left Hmerge_iface  Hprov' Hprov (eq_sym Hstk)).
             reflexivity.
        * (* Here, pushing the constructor forward to get simpler goals instead
             of dealing with untimely local unfoldings, and applying the
             constructor after the obvious rewrites have been applied globally
             as in previous cases. (Probably a better generic strategy.) *)
          constructor.
          -- admit. (* Easy. *)
          -- rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
             reflexivity.
          -- rewrite (unpartialize_stack_merge_stacks_cons_partition Hmerge_iface).
             simpl.
             change
               (PS.merge_stacks
                  ((fix map (l : list Pointer.t) : list PS.PartialPointer.t :=
                      match l with
                      | [] => []
                      | a :: t => PS.to_partial_frame (domm (prog_interface c)) a :: map t
                      end) gps0)
                  ((fix map (l : list Pointer.t) : list PS.PartialPointer.t :=
                      match l with
                      | [] => []
                      | a :: t => PS.to_partial_frame (domm (prog_interface p)) a :: map t
                      end) gps))
             with
               (PS.merge_stacks (PS.to_partial_stack gps0 (domm (prog_interface c)))
                                (PS.to_partial_stack gps (domm (prog_interface p)))).
             rewrite (to_partial_stack_merge_stacks_right Hmerge_iface Hprov' Hprov (eq_sym Hstk)).
             reflexivity.

    - (* IReturn *)
      (* Here we know where pc1' is all along. *)
      assert (Hpc' : Pointer.component pc1' \in domm (prog_interface p))
        by admit. (* Easy. *)
      (* Before we proceed, we need to ascertain that gps (the stack on p and c)
         is a perfect counterpart of the stack on p and p' (pc1' :: gps1). That
         is, the top of gps is precisely pc1'. *)
      assert (exists gps', gps = pc1' :: gps')
        as [gps' Heq]
        by admit.
      subst gps.
      (* After the prologue we continue with the standard proof strategy. *)
      assert (Hstep_cs' : CS.step (prepare_global_env (program_link p c))
                                  (pc1' :: gps', mem, regs, pc)
                                  [ERet (Pointer.component pc) ret_arg (Pointer.component pc1')]
                                  (gps', mem, Register.invalidate regs, pc1')).
      {
        CS_step_of_executing; try (reflexivity || eassumption).
        - eapply execution_invariant_to_linking; eassumption.
      }
      match goal with
      | |- context[PS.CC (?C, ?GPS, ?MEM)] =>
        exists (PS.CC (Pointer.component pc1',
                       PS.to_partial_stack gps' (domm (prog_interface p)), (* Get from GPS! *)
                       MEM))
      end.
      split.
      + constructor.
        * easy.
        * assumption.
        * econstructor.
          -- reflexivity.
          -- assumption.
          -- assumption.
          -- eapply linkable_sym; eassumption.
          -- exact (linkable_mains_sym main_linkability).
          -- rewrite program_linkC.
             apply Hstep_cs'.
             ++ assumption.
             ++ assumption.
             ++ apply linkable_sym; assumption.
          -- assumption.
          -- pose proof PS.partialized_state_is_partial
                  (gps', mem, Register.invalidate regs, pc1')
                  (prog_interface p)
               as Hpartial''.
             simpl in Hpartial''. rewrite Hpc' in Hpartial''.
             assumption.
      + rewrite <- Hmem.
        (* rewrite <- Hstk. *)
        (* Before decomposing the goal in its constituting sub-goals, we process
           the stack to get the information needed for the partialized
           rewrites. *)
        inversion Hstk as [Hstk'].
        (* As in the ICall case, we determine that the two stacks involved in the
           partialized rewrites arise from proper executions of programs on the
           joint program-context interface. *)
        assert (Hprov : CS.comes_from_initial_state
                          (gps', mem, Register.invalidate regs, pc1')
                          (unionm (prog_interface c) (prog_interface p))).
        {
          rewrite <- (unionmC (proj2 linkability)).
          rewrite <- (unionmC (proj2 linkability)) in Hfrom_initial.
          change (unionm (prog_interface p) (prog_interface c))
            with (prog_interface (program_link p c))
            in Hfrom_initial.
          exact (comes_from_initial_state_step_trans Hfrom_initial Hstep_cs').
        }
        (* And we continue with the goal. *)
        match goal with
        | |- PS.mergeable_states _ _ ?PC ?CC =>
          eapply PS.mergeable_states_intro
            with (ics := PS.unpartialize (PS.merge_partial_states PC CC))
        end.
        * easy.
        * simpl.
          (* unfold PS.unpartialize. *)
          (* unfold PS.merge_partial_states; fold PS.merge_partial_states. *)
          rewrite (merge_stacks_partition Hmerge_iface Hprov).
          rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
          (* RB: The back that we do not use the bracketed proto-lemma in this
             case points to the provenance information that we need for the stack
             rewrites as the key for this part as well. In fact, the stack cases
             in this IReturn case fall into the purview of the simpler partition
             lemmas given the extended provenance information is available.
             TODO: Have a look at ICall (and the other cases) too. *)
          exact Hprov.
        * constructor.
          -- assumption.
          -- now rewrite (to_partial_memory_merge_memories_left _ _ Hmerge_iface).
          -- rewrite (merge_stacks_partition Hmerge_iface Hprov).
             reflexivity.
        * (* Here, pushing the constructor forward to get simpler goals instead
             of dealing with untimely local unfoldings, and applying the
             constructor after the obvious rewrites have been applied globally
             as in previous cases. (Probably a better generic strategy.) *)
          constructor.
          -- assumption. (* RB: TODO: Bring down assert at the top of case? *)
          -- rewrite (merge_memories_partition Hmerge_iface Hfrom_initial).
             reflexivity.
          -- rewrite (merge_stacks_partition Hmerge_iface Hprov).
             reflexivity.

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
End Simulation.
End ProgCtxSim.

(*
  Context-Program Simulation

  The symmetric of ProgCtxSim. Its structure should be fully equivalent
  and permit complementary reasoning from the side of the context.

  RB: TODO: Refactoring vis-a-vis ProgCtxSim and instantiation of both.
*)

Module CtxProgSim.
Section Simulation.
  Variables p c: program.

  Hypothesis wf1 : well_formed_program p.
  Hypothesis wf2 : well_formed_program c.

  Hypothesis linkability: linkable (prog_interface p) (prog_interface c).

  Hypothesis prog_is_closed:
    closed_program (program_link p c).

  Hypothesis mergeable_interfaces:
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Lemma match_initial_states:
    forall ips1,
      ContextSem.initial_state p (prog_interface c) ips1 ->
    exists ips2,
      ProgramSem.initial_state c (prog_interface p) ips2 /\
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2.
  Proof.
    intros ips1 Hini.
    inversion Hini as [ics ? Hcomes_from Hpartial1 Hcc1]; subst.
    inversion Hcomes_from as [p' [s' [t' [Hini' Hstar']]]].
    inversion Hpartial1 as [? ? ? ? ? ? Hpc1 | ? ? ? ? ? ? _]; subst;
      PS.simplify_turn;
      first destruct (PS.domm_partition_in_notin
                        Hcc1 Hpc1).
    exists
      (PS.PC
         (PS.to_partial_stack gps (domm (prog_interface p)),
          PS.to_partial_memory mem (domm (prog_interface p)),
          regs, pc)).
    split.
    - econstructor.
      + apply CS.comes_from_initial_state_mergeable_sym; eassumption.
      + constructor.
        * PS.simplify_turn. eapply PS.domm_partition_notin; eassumption.
        * reflexivity.
        * reflexivity.
      + PS.simplify_turn. eapply PS.domm_partition_notin; eassumption.
    - econstructor.
      + eapply mergeable_interfaces_sym; eassumption.
      + apply CS.comes_from_initial_state_mergeable_sym; eassumption.
      + assumption.
      + constructor.
        * PS.simplify_turn. eapply PS.domm_partition_notin; eassumption.
        * reflexivity.
        * reflexivity.
  Qed.

  Lemma match_final_states:
    forall ips1 ips2,
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
      ContextSem.final_state (prog_interface c) ips1 ->
      ProgramSem.final_state (prog_interface p) ips2.
  Proof.
    intros ips1 ips2 Hmerge Hfinal1.
    constructor.
    inversion Hfinal1 as [? Hcc]; subst.
    inversion Hmerge
      as [ics ? ? Hmerge_ifaces Hini Hpartial1 Hpartial2]; subst.
    inversion Hpartial1 as [? ? ? ? ? ? Hpc1 | ? ? ? ? ? ? Hcc1]; subst;
      inversion Hpartial2 as [? ? ? ? ? ? Hpc2 | ? ? ? ? ? ? Hcc2]; subst;
      PS.simplify_turn.
    - eapply PS.domm_partition_notin; eassumption.
    - destruct (PS.domm_partition_in_both Hmerge_ifaces Hcc Hcc2).
    - eapply PS.domm_partition_notin; eassumption.
    - destruct (PS.domm_partition_in_both Hmerge_ifaces Hcc Hcc2).
  Qed.

  Lemma lockstep_simulation:
    forall ips1 t ips1',
      Step (ContextSem.sem p (prog_interface c)) ips1 t ips1' ->
    forall ips2,
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
    exists ips2',
      Step (ProgramSem.sem c (prog_interface p)) ips2 t ips2' /\
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1' ips2'.
  Admitted. (* Grade 3. After ProgCtxSim.lockstep_simulation. *)

  Theorem program_simulates_context:
    forward_simulation (ContextSem.sem p (prog_interface c))
                       (ProgramSem.sem c (prog_interface p)).
  Proof.
    eapply forward_simulation_step.
    - apply match_initial_states.
    - apply match_final_states.
    - apply lockstep_simulation.
  Qed.

End Simulation.
End CtxProgSim.

Module StarNSim.
Section Simulation.
  Variables p c: program.

  Hypothesis wf1 : well_formed_program p.
  Hypothesis wf2 : well_formed_program c.

  Hypothesis linkability: linkable (prog_interface p) (prog_interface c).

  Hypothesis main_linkability: linkable_mains p c.

  Hypothesis prog_is_closed:
    closed_program (program_link p c).

  Hypothesis mergeable_interfaces:
    mergeable_interfaces (prog_interface p) (prog_interface c).

  (* RB: TODO: Refactor lemmas (and proof structure) common to both halves of
     the inductive step. *)
  Corollary st_starN_simulation:
    forall n ips1 t ips1',
      st_starN p (prog_interface c) (prepare_global_env p) n ips1 t ips1' ->
    forall ips2,
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
    exists ips2',
      st_starN c (prog_interface p) (prepare_global_env c) n ips2 t ips2' /\
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1' ips2'.
  Proof.
    intros n ips1 t ips1' Hst_starN.
    apply st_starN_iff_st_starNR in Hst_starN.
    induction Hst_starN
      as [| n ips t1 ips' t2 ips'' t Hst_starNR IHHst_starN Hstep Hsame_turn Ht];
      intros ips2 Hmergeable.
    - eexists. split.
      + constructor.
      + assumption.
    - specialize (IHHst_starN _ Hmergeable).
      destruct IHHst_starN as [ips2' [IHHst_starN IHHmergeable]].
      (* By case analysis on program and context components. *)
      destruct (PS.is_program_component ips' (prog_interface c)) eqn:Hcomp_ips'.
      + assert (Step (ProgramSem.sem p (prog_interface c)) ips' t2 ips'') as Hstep'.
        {
          simpl.
          constructor.
          - apply Hcomp_ips'.
          - inversion Hsame_turn as [? ? Hpc_ips' Hpc_ips'' | ? ? Hcc_ips' Hcc_ips''];
              subst.
            * apply Hpc_ips''.
            * unfold PS.is_program_component in Hcomp_ips'.
              rewrite Hcc_ips' in Hcomp_ips'.
              discriminate.
          - apply Hstep.
        }
        destruct (ProgCtxSim.lockstep_simulation
                    wf1 wf2 linkability main_linkability prog_is_closed
                    mergeable_interfaces Hstep' IHHmergeable)
          as [ips2'' [Hstep'' Hmergeable'']].
        apply st_starN_iff_st_starNR in IHHst_starN.
        assert (PS.step c (prog_interface p) (prepare_global_env c) ips2' t2 ips2'')
          as Hstep_ctx''.
        {
          inversion Hstep'' as [? ? ? ? ? Hstep_c]; subst.
          apply Hstep_c.
        }
        assert (same_turn (prog_interface p) ips2' ips2'') as Hsame_step'.
        {
          inversion Hsame_turn as [? ? Hpc1 Hpc2 | ? ? Hcc1 Hcc2]; subst.
          - apply (PS.mergeable_states_program_to_context IHHmergeable) in Hpc1.
            apply (PS.mergeable_states_program_to_context Hmergeable'') in Hpc2.
            exact (same_turn_context Hpc1 Hpc2).
          - apply (PS.mergeable_states_context_to_program IHHmergeable) in Hcc1.
            apply (PS.mergeable_states_context_to_program Hmergeable'') in Hcc2.
            exact (same_turn_program Hcc1 Hcc2).
        }
        pose proof st_starNR_step IHHst_starN Hstep_ctx'' Hsame_step' Ht as Hst_starN'.
        apply st_starN_iff_st_starNR in Hst_starN'.
        exists ips2''. split.
        * apply Hst_starN'.
        * apply Hmergeable''.
      + unfold PS.is_program_component in Hcomp_ips'.
        apply negb_false_iff in Hcomp_ips'.
        assert (Step (ContextSem.sem p (prog_interface c)) ips' t2 ips'') as Hstep'.
        {
          simpl.
          constructor.
          - apply Hcomp_ips'.
          - inversion Hsame_turn as [? ? Hpc_ips' Hpc_ips'' | ? ? Hcc_ips' Hcc_ips''];
              subst.
            * unfold PS.is_program_component in Hpc_ips'.
              rewrite Hcomp_ips' in Hpc_ips'.
              discriminate.
            * apply Hcc_ips''.
          - apply Hstep.
        }
        destruct (CtxProgSim.lockstep_simulation
                    wf1 wf2 linkability prog_is_closed mergeable_interfaces
                    Hstep' IHHmergeable)
          as [ips2'' [Hstep'' Hmergeable'']].
        apply st_starN_iff_st_starNR in IHHst_starN.
        assert (PS.step c (prog_interface p) (prepare_global_env c) ips2' t2 ips2'')
          as Hstep_ctx''.
        {
          inversion Hstep'' as [? ? ? ? ? Hstep_c]; subst.
          apply Hstep_c.
        }
        assert (same_turn (prog_interface p) ips2' ips2'') as Hsame_step'.
        {
          inversion Hsame_turn as [? ? Hpc1 Hpc2 | ? ? Hcc1 Hcc2]; subst.
          - apply (PS.mergeable_states_program_to_context IHHmergeable) in Hpc1.
            apply (PS.mergeable_states_program_to_context Hmergeable'') in Hpc2.
            exact (same_turn_context Hpc1 Hpc2).
          - apply (PS.mergeable_states_context_to_program IHHmergeable) in Hcc1.
            apply (PS.mergeable_states_context_to_program Hmergeable'') in Hcc2.
            exact (same_turn_program Hcc1 Hcc2).
        }
        pose proof st_starNR_step IHHst_starN Hstep_ctx'' Hsame_step' Ht as Hst_starN'.
        apply st_starN_iff_st_starNR in Hst_starN'.
        exists ips2''. split.
        * apply Hst_starN'.
        * apply Hmergeable''.
  Qed.

  Corollary control_change_simulation:
    forall s1 t s2 s1',
      PS.step p (prog_interface c) (prepare_global_env p) s1 t s2 ->
      ~ same_turn (prog_interface c) s1 s2 ->
      PS.mergeable_states (prog_interface c) (prog_interface p) s1 s1' ->
    exists s2',
      PS.step c (prog_interface p) (prepare_global_env c) s1' t s2' /\
      ~ same_turn (prog_interface p) s1' s2' /\
      PS.mergeable_states (prog_interface c) (prog_interface p) s2 s2'.
  Admitted.

  Corollary mt_starN_simulation:
    forall n ips1 t ips1',
      mt_starN p (prog_interface c) (prepare_global_env p) n ips1 t ips1' ->
    forall ips2,
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1 ips2 ->
    exists ips2',
      mt_starN c (prog_interface p) (prepare_global_env c) n ips2 t ips2' /\
      PS.mergeable_states (prog_interface c) (prog_interface p) ips1' ips2'.
  Proof.
    intros n s1 t s2 Hmt_star12.
    induction Hmt_star12
      as [ n s1 t s2 Hst_starN12
         | n1 n2 n3 s1 t1 s2 t2 s3 t3 s4 t
           Hst_starN12 Hstep23 Hturn23 Hmt_starN34 IHmt_starN14 Hn3 Ht];
      subst;
      intros s1' Hmergeable1.
    - (* Single-segment case. *)
      (* The goal follows directly from the single-turn simulation. *)
      destruct (st_starN_simulation Hst_starN12 Hmergeable1)
        as [s2' [Hst_starN12' Hmergeable2]].
      exists s2'. split.
      + apply mt_starN_segment. assumption.
      + assumption.
    - (* Multi-segment case. *)
      (* Here too, we start by simulating the first turn. *)
      destruct (st_starN_simulation Hst_starN12 Hmergeable1)
        as [s2' [Hst_starN12' Hmergeable2]].
      (* Next, simulate the turn change proper. *)
      destruct (control_change_simulation Hstep23 Hturn23 Hmergeable2)
        as [s3' [Hstep23' [Hturn23' Hmergeable3]]].
      (* Finally, specialize the IH, compose the pieces and finish. *)
      specialize (IHmt_starN14 s3' Hmergeable3).
      destruct IHmt_starN14 as [s4' [Hmt_starN34' Hmergeable4]].
      exists s4'. split.
      + exact (mt_starN_control_change
                 Hst_starN12' Hstep23' Hturn23' Hmt_starN34'
                 (eq_refl _) (eq_refl _)).
      + exact Hmergeable4.
  Qed.
End Simulation.
End StarNSim.

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

  Hypothesis mergeable_interfaces:
    mergeable_interfaces (prog_interface p) (prog_interface c).

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
    intros ips1 ips2 HPSini1 HPSini2.
    (* ??? matching_mains introduction *)
    inversion HPSini1
      as [p' ics1 ? Hiface1 _ Hwf1 Hlinkable1 Hmains1 Hpartial1 HCSini1];
      subst.
    inversion HPSini2
      as [c' ics2 ? Hiface2 _ Hwf2 Hlinkable2 Hmains2 Hpartial2 HCSini2];
      subst.
    unfold CS.initial_state, CS.initial_machine_state in HCSini1, HCSini2.
    unfold CS.initial_state, CS.initial_machine_state.
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
    - admit. (* By composability of [prepare_]. *)
    - admit. (* Discard by matching_mains. *)
    - admit. (* By composability of [prepare_]. *)
    - admit. (* Discard by matching_mains. *)
    - admit. (* Discard by matching_mains. *)
    - admit. (* Discard by matching_mains. *)
    - admit. (* Discard by matching_mains. *)
    - inversion Hpartial1 as [? ? ? ? ? ? Hcomp1 | ? ? ? ? ? ? Hcomp1]; subst;
        inversion Hpartial2 as [? ? ? ? ? ? Hcomp2 | ? ? ? ? ? ? Hcomp2]; subst;
        PS.simplify_turn.
      + admit. (* Easy. *)
      + inversion Hwf2 as [_ _ _ _ _ _ Hmain2].
        specialize (Hmain2 Hmainc').
        rewrite Hiface2 in Hmain2.
        now destruct (PS.domm_partition_in_notin Hcomp2 Hmain2).
      + inversion Hwf1 as [_ _ _ _ _ _ Hmain1].
        specialize (Hmain1 Hmainp').
        rewrite Hiface1 in Hmain1.
        now destruct (PS.domm_partition_in_notin Hcomp1 Hmain1).
      + now destruct (PS.domm_partition_in_both mergeable_interfaces Hcomp2 Hcomp1).
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
             unfold PS.to_partial_memory. rewrite filterm_identity.
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
             unfold PS.to_partial_memory. rewrite filterm_identity.
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
                 PS.merge_memories
                   (PS.to_partial_memory mem (domm (prog_interface c)))
                   (PS.to_partial_memory mem (domm (prog_interface p))),
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
        * unfold PS.to_partial_memory.
          by rewrite domm0 filterm_predT.
        * rewrite domm0 (merge_stacks_partition Hmergeable_ifaces Hcomes_from).
          by rewrite (merge_stacks_partition_emptym Hmergeable_ifaces Hcomes_from).
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
                 PS.merge_memories
                   (PS.to_partial_memory mem (domm (prog_interface c)))
                   (PS.to_partial_memory mem (domm (prog_interface p))),
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
          unfold PS.to_partial_memory. rewrite filterm_predT.
          reflexivity.
        * rewrite domm0.
          rewrite (merge_stacks_partition Hmergeable_ifaces Hcomes_from).
          rewrite (merge_stacks_partition_emptym Hmergeable_ifaces Hcomes_from).
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

    inversion Hmatch as [ips1 ips2 Hmergeable]; subst; clear Hmatch.
    inversion Hstep as [? ? ips1' ? ips2' Hstep1 Hstep2]; subst; clear Hstep.

    inversion Hmergeable as [ics ? ? Hmerge_ifaces Hfrom_initial Hpartial1 Hpartial2];
      subst(*; clear Hmergeable*).
    inversion Hstep1
      as [p' ? ? ? ics1 ics1'
          Hifaces1 _ Hwf1' Hlinkable1 Hmains1 HCSstep1 Hpartial_ips1 Hpartial_ips1'];
      subst(*; clear Hstep1*);
      inversion Hstep2
        as [c' ? ? ? ics2 ics2'
            Hifaces2 _ Hwf2' Hlinkable2 Hmains2 HCSstep2 Hpartial_ips2 Hpartial_ips2'];
      subst(*; clear Hstep2*);
      inversion Hpartial1 as [? ? ? ? ? ? Hcomp1 | ? ? ? ? ? ? Hcomp1];
      subst(*; clear Hpartial1*);
      inversion Hpartial2 as [? ? ? ? ? ? Hcomp2 | ? ? ? ? ? ? Hcomp2];
      subst(*; clear Hpartial2*);
      simpl in *; PS.simplify_turn.

    - (* Contra. *)
      now destruct (PS.domm_partition_in_neither
                      (mergeable_interfaces_sym _ _ mergeable_interfaces)
                      Hfrom_initial Hcomp1 Hcomp2).

    - (* program is in the first state *)
      exists (PS.merge_partial_states ips1' ips2'). split.

      + inversion Hpartial_ips1; subst(*; clear Hpartial_ips1*);
          inversion Hpartial_ips2; subst(*; clear Hpartial_ips2*);
          PS.simplify_turn; simpl in *.
        (* RB: TODO: Existing information, and new information, can be extracted
           from the goal and the context, respectively. *)
        eapply PS.partial_step
          with
            (ics:=PS.unpartialize
                    (PS.PC
                       (PS.merge_stacks (PS.to_partial_stack gps (domm (prog_interface c)))
                                        (PS.to_partial_stack gps (domm (prog_interface p))),
                        PS.merge_memories (PS.to_partial_memory mem (domm (prog_interface c)))
                                          (PS.to_partial_memory mem (domm (prog_interface p))),
                        regs, pc)))
            (p':=empty_prog).
        * reflexivity.
        * apply linking_well_formedness; assumption.
        * now apply empty_prog_is_well_formed.
        * apply linkable_emptym. now apply linkability.
        * unfold linkable_mains, empty_prog. simpl.
          now rewrite andb_false_r.
        * admit.
        * constructor.
          ** PS.simplify_turn.
             by rewrite mem_domm.
          ** rewrite domm0. unfold PS.to_partial_memory.
             rewrite filterm_identity. reflexivity.
          ** rewrite domm0.
             rewrite (PS.to_partial_stack_unpartialize_identity
                        (PS.merged_stack_has_no_holes
                           (PS.mergeable_stacks_partition
                              (mergeable_interfaces_sym _ _ mergeable_interfaces)
                              Hfrom_initial))).
             reflexivity.
        * admit.

      + (* prove match *)
        admit.

    - (* program is in the second state *)
      admit. (* RB: Fully symmetrical case. *)

    - (* Contra. *)
      now destruct (PS.domm_partition_in_both mergeable_interfaces Hcomp2 Hcomp1).

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
    mergeable_interfaces (prog_interface p) (prog_interface c).

  (* In this lemma we reason about two complementary single-turn runs, one in p
     and another in c. One of them runs in the program and the other in the
     context; which is which does not matter. Both runs produce the same trace.
     In our languages, steps produce singleton traces, which simplifies our
     reasoning as we can proceed stepwise. The context does not matter when its
     events are produced: it is for the program to choose. *)
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
    induction Hst_star1
      as [| n1 ips1 t1 ips2 t2 ips3 t Hstep12 Hturn1 Hst_starN23 IHHst_star1 Ht];
      subst.

    (* Zero steps, therefore empty trace. *)
    - intros ips2 Hmergeable Hst_star2.
      inversion Hmergeable as [ics ? ? Hmergeable_ifaces Hcomes_from Hpartial1 Hpartial2];
        subst.
      inversion Hst_star2; subst.
      inversion Hpartial1 as [? ? ? ? ? ? Hpc1 | ? ? ? ? ? ? Hcc1]; subst;
        inversion Hpartial2 as [? ? ? ? ? ? Hpc2 | ? ? ? ? ? ? Hcc2]; subst.

      + destruct (PS.domm_partition_in_neither Hmergeable_ifaces Hcomes_from Hpc1 Hpc2).

      (* the program doesn't step, hence we stay still *)
      + apply star_if_st_starN in Hst_star2.
        pose proof PS.context_epsilon_star_is_silent.
        eapply (PS.context_epsilon_star_is_silent Hcc2) in Hst_star2; subst.
        split.
        * constructor.
        * assumption.

      (* the program does a star with an epsilon trace.
         use the fact that the context simulates the program *)
      + assert (Hmergeable' := Hmergeable).
        apply PS.mergeable_states_sym in Hmergeable'; auto.
        assert (prog_is_closed' := prog_is_closed).
        rewrite (closed_program_link_sym wf1 wf2 linkability)
          in prog_is_closed'.
        destruct (StarNSim.st_starN_simulation
                    wf2 wf1
                    (linkable_sym linkability)
                    (linkable_mains_sym main_linkability)
                    prog_is_closed' Hmergeable_ifaces Hst_star2 Hmergeable')
          as [ips1' [Hstar Hmergeable'']].
        (* The following is used by both branches of the split. *)
        inversion Hstar; subst.
        inversion Hmergeable''
          as [ics ? ? Hmergeable_ifaces' Hcomes_from' Hpartial1' Hpartial2'];
          subst.
        inversion Hpartial1' as [? ? ? ? ? ? Hpc1' Hmem1' Hstk1' |]; subst;
          inversion Hpartial2' as [| ? ? ? ? ? ? Hcc2' Hmem2' Hstk2']; subst;
          PS.simplify_turn.
        split.
        * rewrite Hmem1' Hstk1' Hmem2' Hstk2'.
          constructor.
        * match goal with
            | |- PS.mergeable_states _ _ ?S1 ?S2 =>
              eapply PS.mergeable_states_intro with
                  (ics := (PS.unpartialize (PS.merge_partial_states S1 S2)))
          end.
          (* RB: TODO: Refactor occurrences of the following proof pattern once complete. *)
          -- assumption.
          -- simpl.
             rewrite (merge_stacks_partition Hmergeable_ifaces Hcomes_from).
             rewrite (merge_memories_partition Hmergeable_ifaces Hcomes_from).
             assumption.
          -- constructor.
             ++ assumption.
             ++ now rewrite (merge_memories_partition Hmergeable_ifaces Hcomes_from).
             ++ now rewrite (merge_stacks_partition Hmergeable_ifaces Hcomes_from).
          -- constructor.
             ++ assumption.
             ++ now rewrite (merge_memories_partition Hmergeable_ifaces Hcomes_from).
             ++ now rewrite (merge_stacks_partition Hmergeable_ifaces Hcomes_from).

      + destruct (PS.domm_partition_in_both Hmergeable_ifaces Hcc1 Hcc2).

    (* Step and star, possibly non-empty trace. *)
    - rename ips2' into ips3'.
      intros ips1' Hmergeable1 Hst_starN13'.
      (* Trace the first step from the "p" to the "c" run. *)
      assert
        (exists ips2',
            PS.step c (prog_interface p) (prepare_global_env c) ips1' t1 ips2' /\
            PS.mergeable_states (prog_interface c) (prog_interface p) ips2 ips2')
        as [ips2' [Hstep12' Hmergeable2]].
      {
        (* This will be proved by ProgCtxSim.lockstep_simulation or by
           CtxProgSim.lockstep_simulation, depending on which run is the program
           run and which the context run. *)
        admit.
      }
      (* Decompose the "c" star into the first step and the remainder. *)
      assert
        (st_starN c (prog_interface p) (prepare_global_env c) n1 ips2' t2 ips3')
        as Hst_starN23'.
      {
        (* We know that the single-turn run (in "c", here) is deterministic, and
           moreover we have the first step from ips1' to ips2' producing t1. *)
        admit.
      }
      (* assert *)
      (*   (exists ips3', *)
      (*       st_starN c (prog_interface p) (prepare_global_env c) n1 ips2' t2 ips3') *)
      (*   as [ips3'' Hst_starN23']. *)
      (* { *)
      (*   admit. *)
      (* } *)
      (* pose proof state_determinism_st_starN Hst_starN23. Hst_starN23'. *)
      (* From here process the IH and solve the goal. *)
      specialize (IHHst_star1 ips2' Hmergeable2 Hst_starN23').
      destruct IHHst_star1 as [HstarN23 Hmergeable3].
      split.
      + apply starN_step with (t1 := t1) (s' := (ips2, ips2')) (t2 := t2).
        * constructor; assumption.
        * assumption.
        * reflexivity.
      + assumption.

      (* inversion Hmergeable as [ics ? ? Hmergeable_ifaces Hcomes_from Hpartial1 Hpartial2]; *)
      (*   subst. *)
      (* inversion Hpartial1 as [? ? ? ? ? ? Hpc1 | ? ? ? ? ? ? Hcc1]; subst; *)
      (*   inversion Hpartial2 as [? ? ? ? ? ? Hpc2 | ? ? ? ? ? ? Hcc2]; subst. *)

      (* + admit. (* Contra. *) *)

      (* (* the program is stepping *) *)
      (* + (* simulate the step *) *)
      (*   (* use inductive hypothesis *) *)
      (*   (* compose previous results *) *)
      (*   admit. *)

      (* + admit. (* Contra. *) *)

      (* (* the context is stepping *) *)
      (* + admit. *)
  Admitted. (* Grade 3. RB: Might need polishing, but should be fairly simple. *)

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
    intros n1 cs1 ps1 cs2 t1 ps3 t2 n3 t3 s4
           Hcs1 Hps1 Hmerge1 Hst_starN12 Hstep23 Hturn23 Hmt_starN34
           n s4' Hst_starN14.
    (* We reason on two runs: a "program run" that goes all the way in a single
       turn, and a "context run" that changes turns explicitly. In the latter,
       Hstep23 means that t2 is an event that changes from c to p. This must
       involve a contradiction in Hst_starN14. *)

    (* First, move this to the goal. This will help to more easily discharge some
       contradictory cases. *)
    apply Hturn23.

    (* Case analysis on the turn-changing step of the short run. *)
    inversion Hstep23
      as [p' ? ? ? ics1 ics1'
          Hifaces1 _ Hwf1' Hlinkable1 Hmains1 HCSstep1 Hpartial_ips1 Hpartial_ips1'];
      subst.
    inversion HCSstep1; subst;
      (* Silent steps preserve the turn and are discharged right away. *)
      try (eapply step_E0_same_turn; eassumption).

    (* RB: TODO: Name variables and hypotheses that are explicitly used. *)
    - (* ICall *)
      (* This event entails a change of turn as per Hturn23. *)
      destruct (C' \in domm (prog_interface p)) eqn:HpcC';
        first admit. (* Contra. *)

      (* The event is now visible in the long run, so we can split it. *)
      destruct (st_starN_event_split Hst_starN14)
        as [n1' [ps2 [cs3 [n3' [Hst_starN12' [Hstep23' [Hturn23' [Hst_starN14' Hn]]]]]]]].
      pose proof st_starN_same_turn Hst_starN12' as Hturn12'.

      (* Propagate the turn from the beginning of the long run to the event that
         triggers the turn change in the short run. *)
      inversion Hturn12'; subst;
        last admit. (* Contra. *)
      inversion Hturn23'; subst;
        last admit. (* Contra. *)

      (* Extract the information in the target step of the long run.  *)
      inversion Hstep23'
        as [c' ? ? ? ics2 ics2'
            Hifaces2 _ Hwf2' Hlinkable2 Hmains2 HCSstep2 Hpartial_ips2 Hpartial_ips2'];
        subst.
      inversion HCSstep2; subst.
      (* Extract the information of the partial states. All combinations except
         one are obvious contradictions. *)
      inversion Hpartial_ips2
        as [? ? ? ? ? ? Hcomp_ips2 | ? ? ? ? ? ? Hcomp_ips2]; subst;
        inversion Hpartial_ips2'
          as [? ? ? ? ? ? Hcomp_ips2' | ? ? ? ? ? ? Hcomp_ips2']; subst;
        PS.simplify_turn;
        [| admit | admit | admit]. (* Contra. *)

      (* The remaining case is also a contradiction because C' is not in c, but
         as we know from the turn change in the short run, it is also not in p.
         (To conclude this we need provenance information.) *)
      admit.

    - (* IReturn *)
      (* This case will be similar to ICall. *)
      admit.
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
    intros n1 cs1 ps1 cs2 t1 ps3 t2 n3 t3 s4
           Hcs1 Hps1 Hmerge1 Hst_starN12 Hstep23 Hturn23 Hmt_starN34
           n s4' Hst_starN14.
  Admitted. (* Grade 2. After st_starN_with_turn_change_impossible_1. *)

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
    intros n1 ps1 cs1 ps2 t1 cs3 t2 n3 t3 s4
           Hcs1 Hps1 Hmerge1 Hst_starN12 Hstep23 Hturn23 Hmt_starN34
           n s4' Hst_starN14.
  Admitted. (* Grade 2. After st_starN_with_turn_change_impossible_1. *)

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
    intros n1 ps1 cs1 ps2 t1 cs3 t2 n3 t3 s4
           Hcs1 Hps1 Hmerge1 Hst_starN12 Hstep23 Hturn23 Hmt_starN34
           n s4' Hst_starN14.
  Admitted. (* Grade 2. After st_starN_with_turn_change_impossible_1. *)

  (* RB: XXX: I do not believe this is true. In particular, after the turn
     changes nothing tells us that the two runs need to run to exhaustion: each
     is free to stop at any point independently from the other, irrespective of
     whether the runs up to the turn change are identical, and nothing connects
     their "final" states. *)
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
    intros s1 s2 s3' s1' s2'
           s3 s4 s4' n1 n1' n3 n3' t1 t1' t2 t2' t3 t3'
           Hpc_s1 Hcc_s1' Hmerge
           Hst_starN12 Hstep23 Hturn23 Hmt_starN34
           Hst_starN12' Hstep23' Hturn23' Hmt_starN34'.
  Admitted.

  (* RB: XXX: See [same_trace_and_steps] above. *)
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
    intros s1' s2' s3 s1 s2
           s3' s4' s4 n1 n1' n3 n3' t1 t1' t2 t2' t3 t3'
           Hpc_s1 Hcc_s1' Hmerge
           Hst_starN12 Hstep23 Hturn23 Hmt_starN34
           Hst_starN12' Hstep23' Hturn23' Hmt_starN34'.
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
        apply (PS.domm_partition Hsame_ifaces Hcomes_from) in Hpc2.
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
        apply (PS.domm_partition Hsame_ifaces Hcomes_from) in Hpc2.
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
          destruct (MultiSem.lockstep_simulation
                      wf1 wf2 main_linkability linkability mergeable_interfaces
                      Hmultistep Hmultimatch)
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
          destruct (MultiSem.lockstep_simulation
                      wf1 wf2 main_linkability linkability mergeable_interfaces
                      Hmultistep Hmultimatch)
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
    inversion Hs1_init as [? ? ? ? ? ? ? Hmains1]; subst;
      inversion Hs2_init as [? ? ? ? ? ? ? Hmains2]; subst.
    inversion H3; subst; inversion H9; subst;
      inversion H4; subst; inversion H10; subst; simpl in *.

    (* contra, pc is neither in (prog_interface c), nor in (prog_interface p) *)
    - PS.simplify_turn.
      (* show and use the fact that the main has an entrypoint, therefore
         (Pointer.component pc) must be in either (prog_interface c) or (prog_interface p) *)
      (* here it's probably where we need well-formed programs *)
      admit.

    - econstructor.
      + apply mergeable_interfaces_sym; assumption.
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
      + apply mergeable_interfaces_sym; assumption.
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
    forall m,
      does_prefix (PS.sem p (prog_interface c)) m ->
      does_prefix (PS.sem c (prog_interface p)) m ->
      does_prefix (PS.sem prog emptym) m.
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

  Hypothesis prog_is_closed:
    closed_program (program_link p c).

  Hypothesis mergeable_interfaces:
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Theorem composition_for_termination:
    forall t,
      program_behaves (PS.sem p (prog_interface c)) (Terminates t) ->
      program_behaves (PS.sem c (prog_interface p)) (Terminates t) ->
      program_behaves (CS.sem (program_link p c)) (Terminates t).
  Proof.
    intros t Hbeh1 Hbeh2.
    inversion mergeable_interfaces as [linkability _].
    eapply partial_semantics_implies_complete_semantics; auto.
    - apply linking_well_formedness; auto.
    - apply partial_programs_composition; auto.
  Qed.

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
    - apply partial_semantics_implies_complete_semantics; auto.
      + apply linking_well_formedness; auto.
  Qed.

End Composition.
