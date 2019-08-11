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
Require Import Intermediate.Composition.
Require Import Intermediate.Recombination.

Require Import Coq.Program.Equality.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import Intermediate.

Module CS2PS.
Section Simulation.
  Variable prog: program.

  Hypothesis prog_is_well_formed:
    well_formed_program prog.

  Hypothesis prog_is_closed:
    closed_program prog.

  Lemma match_initial_states:
    forall ics,
      CS.initial_state prog ics ->
    exists ips,
      PS.initial_state prog emptym ips /\ PS.partial_state emptym ics ips.
  Admitted.

  Lemma match_final_states:
    forall ics ips,
      PS.partial_state emptym ics ips ->
      CS.final_state (prepare_global_env prog) ics ->
      PS.final_state prog emptym ips.
  Admitted.

  Lemma lockstep_simulation:
    forall ics t ics',
      CS.step (prepare_global_env prog) ics t ics' ->
    forall ips,
      PS.partial_state emptym ics ips ->
    exists ips',
      PS.step prog emptym (prepare_global_env prog) ips t ips' /\ PS.partial_state emptym ics' ips'.
  Admitted.

  (* Lemma star_simulation: *)
  (*   forall ips t ips', *)
  (*     Star (PS.sem prog emptym) ips t ips' -> *)
  (*   forall ics, *)
  (*     PS.partial_state emptym ics ips -> *)
  (*   exists ics', *)
  (*     Star (CS.sem prog) ics t ics' /\ PS.partial_state emptym ics' ips'. *)
  (* Qed. *)

  Theorem PS_simulates_CS:
    forward_simulation (CS.sem prog) (PS.sem prog emptym).
  Proof.
    eapply forward_simulation_step.
    - apply match_initial_states.
    - apply match_final_states.
    - apply lockstep_simulation.
  Qed.

  Corollary partial_semantics_implies_complete_semantics:
    forall beh,
      program_behaves (CS.sem prog) beh ->
      program_behaves (PS.sem prog emptym) beh.
  Admitted.
End Simulation.
End CS2PS.

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

Inductive mt_starNR (p: program) (ctx: Program.interface) (G: global_env)
  : nat -> PS.state -> trace -> PS.state -> Prop :=
| mt_starNR_segment: forall n ips t ips',
    st_starNR p ctx G n ips t ips' ->
    mt_starNR p ctx G n ips t ips'
| mt_starNR_control_change: forall n1 n2 n3 ips t1 ips' t2 ips'' t3 ips''' t,
    mt_starNR p ctx G n1 ips t1 ips' ->
    PS.step p ctx G ips' t2 ips'' ->
    ~ same_turn ctx ips' ips'' ->
    st_starNR p ctx G n2 ips'' t3 ips''' ->
    n3 = S (n1 + n2) ->
    t = t1 ** t2 ** t3 ->
    mt_starNR p ctx G n3 ips t ips'''.

Theorem mt_starN_iff_mt_starNR:
  forall p ctx G n ips t ips',
    mt_starN p ctx G n ips t ips' <->
    mt_starNR p ctx G n ips t ips'.
Admitted. (* Grade 2. *)

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

Theorem mt_starN_if_st_starN:
  forall p ctx G n ips t ips',
    st_starN p ctx G n ips t ips' ->
    mt_starN p ctx G n ips t ips'.
Proof.
  intros p ctx G n ips t ips' Hst_starN.
  exact (mt_starN_segment Hst_starN).
Qed.

(* RB: TODO: Here and in other sections, remove unnecessary hypotheses. *)
Module StateDet.
Section StateDet.
  Variables p c: program.

  Hypothesis wf1 : well_formed_program p.
  Hypothesis wf2 : well_formed_program c.

  Hypothesis linkability: linkable (prog_interface p) (prog_interface c).

  Hypothesis main_linkability: linkable_mains p c.

  Hypothesis prog_is_closed:
    closed_program (program_link p c).

  Hypothesis mergeable_interfaces:
    mergeable_interfaces (prog_interface p) (prog_interface c).

  (* A helper for state_determinism_mt_starN. *)
  Lemma st_starN_prefix_of_mt_starN:
    forall n1 s1 t1 s2,
      st_starN p (prog_interface c) (prepare_global_env p) n1 s1 t1 s2 ->
    forall n2 t2 s3,
      mt_starN p (prog_interface c) (prepare_global_env p) (n1 + n2) s1 (t1 ** t2) s3 ->
      mt_starN p (prog_interface c) (prepare_global_env p) n2 s2 t2 s3.
  Admitted. (* Grade 2. Optional for the one below, possibly slightly annoying. *)

  Theorem state_determinism_mt_starN:
    forall n s1 t s2,
      mt_starN p (prog_interface c) (prepare_global_env p) n s1 t s2 ->
    forall s2',
      mt_starN p (prog_interface c) (prepare_global_env p) n s1 t s2' ->
      s2 = s2'.
  Admitted. (* Grade 2. Possibly slightly annonying, think of possible lemmas. *)
End StateDet.
End StateDet.

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
             ++ erewrite to_partial_memory_merge_partial_memories_right; now eauto.
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
            erewrite to_partial_memory_merge_partial_memories_left; try eauto.
            erewrite unionmC; now eauto.
          }
        * constructor.
          -- assumption.
          -- erewrite to_partial_memory_merge_partial_memories_left; eauto.
          -- by rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
        * simpl.
          (* rewrite (merge_memories_partition Hmerge_iface Hfrom_initial). *)
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite <- Pointer.inc_preserves_component.
          constructor.
          -- by rewrite Pointer.inc_preserves_component.
          -- erewrite to_partial_memory_merge_partial_memories_right; now eauto.
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
             erewrite to_partial_memory_merge_partial_memories_right in Hpartial''; now eauto.
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
            erewrite to_partial_memory_merge_partial_memories_left; try eauto.
            erewrite unionmC; now eauto.
          }
        * constructor.
          -- assumption.
          -- erewrite to_partial_memory_merge_partial_memories_left; now eauto.
          -- by rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
        * simpl.
          (* rewrite (merge_memories_partition Hmerge_iface Hfrom_initial). *)
          rewrite (merge_stacks_partition Hmerge_iface Hfrom_initial).
          rewrite <- Pointer.inc_preserves_component.
          constructor.
          -- now rewrite Pointer.inc_preserves_component.
          -- erewrite to_partial_memory_merge_partial_memories_right; now eauto.
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
            (* rewrite (to_partial_memory_merge_partial_memories_left _ _ Hmerge_iface). *)
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
          -- now rewrite (merge_memories_partition Hmerge_iface Hprov).
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
          -- now rewrite (merge_memories_partition Hmerge_iface Hprov).
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
  Proof.
    (* May it work to use emptyp and prog? *)
    intros s1 t s2 s1' Hstep12 Hturn12 Hmergeable1.
    inversion Hmergeable1
      as [cs1 ? ? Hmergeable_ifaces1 Hcomes_from1 Hpartial1 Hpartial1'];
      subst.
    inversion Hstep12
      as [p' ? ? ? cs1' cs2'
          Hifaces1 _ Hwf1' Hlinkable1 Hmains1 HCSstep1 Hpartial1_bis Hpartial2];
      subst.
    (* Case analysis on CS step and executing instruction. *)
    inversion HCSstep1; subst;
      (* Discard silent steps. *)
      try (exfalso;
           apply Hturn12;
           apply (step_E0_same_turn Hstep12)).
    - (* ICall *)
      (* Case analysis on the location (p or c) of both pc's. *)
      destruct (Pointer.component pc \in domm (prog_interface p)) eqn:Hcase1;
        destruct (C' \in domm (prog_interface p)) eqn:Hcase2.
      + admit. (* Contra. *)
      + admit.
      + admit.
      + admit. (* Contra. *)
    - (* IReturn *)
      admit.
  Admitted. (* Grade 3. Should be somewhat tedious but straightforward. *)

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
      as [| n1 ips1 t1 ips2 t2 ips3 t Hstep12 Hturn12 Hst_starN23 IHHst_star1 Ht];
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
      pose proof
           st_starN_refl p (prog_interface c) (prepare_global_env p) ips2
        as Hst_starN22.
      pose proof
           st_starN_step Hstep12 Hturn12 Hst_starN22 (eq_refl _)
        as Hst_starN12.
      setoid_rewrite E0_right in Hst_starN12.
      destruct
        (StarNSim.st_starN_simulation
           wf1 wf2 linkability main_linkability prog_is_closed mergeable_interfaces
           Hst_starN12 Hmergeable1)
        as [ips2' [Hst_starN12' Hmergeable2]].
      (* (And extract the contained step.) *)
      inversion Hst_starN12'
        as [| ? ? t1' ? ? ? ? Hstep12' Hturn12' Hst_starN_0];
        subst.
      inversion Hst_starN_0; subst.
      rename t1' into t1.
      rewrite E0_right. rewrite E0_right in Hstep12, Hst_starN13'.
      (* Decompose the "c" star into the first step and the remainder. *)
      assert
        (st_starN c (prog_interface p) (prepare_global_env c) n1 ips2' t2 ips3')
        as Hst_starN23'.
      {
        (* We know that the single-turn run (in "c", here) is deterministic, and
           moreover we have the first step from ips1' to ips2' producing t1. *)
        destruct
          (StarNSim.st_starN_simulation
             wf1 wf2 linkability main_linkability prog_is_closed mergeable_interfaces
             Hst_starN23 Hmergeable2)
          as [ips3'' [Hst_starN23' _]].
        pose proof st_starN_step Hstep12' Hturn12' Hst_starN23' (eq_refl _)
          as Hst_starN13''.
        pose proof state_determinism_st_starN Hst_starN13' Hst_starN13'';
          subst ips3''.
        assumption.
      }
      specialize (IHHst_star1 ips2' Hmergeable2 Hst_starN23').
      destruct IHHst_star1 as [HstarN23 Hmergeable3].
      split.
      + apply starN_step with (t1 := t1) (s' := (ips2, ips2')) (t2 := t2).
        * constructor; assumption.
        * assumption.
        * reflexivity.
      + assumption.
  Qed.

  (* RB: TODO: Carefully check statement changes, esp. unproven and w.r.t.
     same_turn. Consider formulating the new premises in terms of same_turn.
     The following few lemmas are currently not used, although it may be useful
     to prove a slightly more general version that encompasses all of them,
     even if the ongoing revision succeeds without their use. *)
  (* Lemma st_starN_with_turn_change_impossible_1: *)
  (*   forall n1 ctx_st prog_st2 ctx_st' t1 prog_st1 t2 n2 t3 ips', *)
  (*     PS.is_program_component prog_st2 (prog_interface c) -> *)
  (*     PS.is_context_component ctx_st (prog_interface p) -> *)
  (*     PS.mergeable_states (prog_interface c) (prog_interface p) *)
  (*                         prog_st2 ctx_st -> *)
  (*     st_starN c (prog_interface p) (prepare_global_env c) *)
  (*              n1 ctx_st t1 ctx_st' -> *)
  (*     PS.step c (prog_interface p) (prepare_global_env c) ctx_st' t2 prog_st1 -> *)
  (*     ~ same_turn (prog_interface p) ctx_st' prog_st1 -> *)
  (*     mt_starN c (prog_interface p) (prepare_global_env c) n2 prog_st1 t3 ips' -> *)
  (*   forall n3 ips'', *)
  (*     st_starN p (prog_interface c) (prepare_global_env p) *)
  (*              n3 prog_st2 (t1 ** t2 ** t3) ips'' -> *)
  (*     False. *)
  (* Proof. *)
  (*   intros n1 cs1 ps1 cs2 t1 ps3 t2 n3 t3 s4 *)
  (*          Hcs1 Hps1 Hmerge1 Hst_starN12 Hstep23 Hturn23 Hmt_starN34 *)
  (*          n s4' Hst_starN14. *)
  (*   (* We reason on two runs: a "program run" that goes all the way in a single *)
  (*      turn, and a "context run" that changes turns explicitly. In the latter, *)
  (*      Hstep23 means that t2 is an event that changes from c to p. This must *)
  (*      involve a contradiction in Hst_starN14. *) *)

  (*   (* First, move this to the goal. This will help to more easily discharge some *)
  (*      contradictory cases. *) *)
  (*   apply Hturn23. *)

  (*   (* Case analysis on the turn-changing step of the short run. *) *)
  (*   inversion Hstep23 *)
  (*     as [p' ? ? ? ics1 ics1' *)
  (*         Hifaces1 _ Hwf1' Hlinkable1 Hmains1 HCSstep1 Hpartial_ips1 Hpartial_ips1']; *)
  (*     subst. *)
  (*   inversion HCSstep1; subst; *)
  (*     (* Silent steps preserve the turn and are discharged right away. *) *)
  (*     try (eapply step_E0_same_turn; eassumption). *)

  (*   (* RB: TODO: Name variables and hypotheses that are explicitly used. *) *)
  (*   - (* ICall *) *)
  (*     (* This event entails a change of turn as per Hturn23. *) *)
  (*     destruct (C' \in domm (prog_interface p)) eqn:HpcC'; *)
  (*       first admit. (* Contra. *) *)

  (*     (* The event is now visible in the long run, so we can split it. *) *)
  (*     destruct (st_starN_event_split Hst_starN14) *)
  (*       as [n1' [ps2 [cs3 [n3' [Hst_starN12' [Hstep23' [Hturn23' [Hst_starN14' Hn]]]]]]]]. *)
  (*     pose proof st_starN_same_turn Hst_starN12' as Hturn12'. *)

  (*     (* Propagate the turn from the beginning of the long run to the event that *)
  (*        triggers the turn change in the short run. *) *)
  (*     inversion Hturn12'; subst; *)
  (*       last admit. (* Contra. *) *)
  (*     inversion Hturn23'; subst; *)
  (*       last admit. (* Contra. *) *)

  (*     (* Extract the information in the target step of the long run.  *) *)
  (*     inversion Hstep23' *)
  (*       as [c' ? ? ? ics2 ics2' *)
  (*           Hifaces2 _ Hwf2' Hlinkable2 Hmains2 HCSstep2 Hpartial_ips2 Hpartial_ips2']; *)
  (*       subst. *)
  (*     inversion HCSstep2; subst. *)
  (*     (* Extract the information of the partial states. All combinations except *)
  (*        one are obvious contradictions. *) *)
  (*     inversion Hpartial_ips2 *)
  (*       as [? ? ? ? ? ? Hcomp_ips2 | ? ? ? ? ? ? Hcomp_ips2]; subst; *)
  (*       inversion Hpartial_ips2' *)
  (*         as [? ? ? ? ? ? Hcomp_ips2' | ? ? ? ? ? ? Hcomp_ips2']; subst; *)
  (*       PS.simplify_turn; *)
  (*       [| admit | admit | admit]. (* Contra. *) *)

  (*     (* The remaining case is also a contradiction because C' is not in c, but *)
  (*        as we know from the turn change in the short run, it is also not in p. *)
  (*        (To conclude this we need provenance information.) *) *)
  (*     admit. *)

  (*   - (* IReturn *) *)
  (*     (* This case will be similar to ICall. *) *)
  (*     admit. *)
  (* Abort. *)

  (* Lemma st_starN_with_turn_change_impossible_1': *)
  (*   forall n1 ctx_st prog_st2 ctx_st' t1 prog_st1 t2 n2 t3 ips', *)
  (*     PS.is_context_component ctx_st (prog_interface c) -> *)
  (*     PS.is_program_component prog_st2 (prog_interface p) -> *)
  (*     PS.mergeable_states (prog_interface c) (prog_interface p) *)
  (*                         ctx_st prog_st2 -> *)
  (*     st_starN p (prog_interface c) (prepare_global_env p) *)
  (*              n1 ctx_st t1 ctx_st' -> *)
  (*     PS.step p (prog_interface c) (prepare_global_env p) ctx_st' t2 prog_st1 -> *)
  (*     ~ same_turn (prog_interface c) ctx_st' prog_st1 -> *)
  (*     mt_starN p (prog_interface c) (prepare_global_env p) n2 prog_st1 t3 ips' -> *)
  (*   forall n3 ips'', *)
  (*     st_starN c (prog_interface p) (prepare_global_env c) *)
  (*              n3 prog_st2 (t1 ** t2 ** t3) ips'' -> *)
  (*     False. *)
  (* Proof. *)
  (*   intros n1 cs1 ps1 cs2 t1 ps3 t2 n3 t3 s4 *)
  (*          Hcs1 Hps1 Hmerge1 Hst_starN12 Hstep23 Hturn23 Hmt_starN34 *)
  (*          n s4' Hst_starN14. *)
  (* Abort. (* Grade 2. After st_starN_with_turn_change_impossible_1. *) *)

  (* Lemma st_starN_with_turn_change_impossible_2: *)
  (*   forall n1 prog_st ctx_st2 prog_st' t1 ctx_st1 t2 n2 t3 ips', *)
  (*     PS.is_context_component ctx_st2 (prog_interface c) -> *)
  (*     PS.is_program_component prog_st (prog_interface p) -> *)
  (*     PS.mergeable_states (prog_interface c) (prog_interface p) *)
  (*                         ctx_st2 prog_st -> *)
  (*     st_starN c (prog_interface p) (prepare_global_env c) *)
  (*              n1 prog_st t1 prog_st' -> *)
  (*     PS.step c (prog_interface p) (prepare_global_env c) prog_st' t2 ctx_st1 -> *)
  (*     ~ same_turn (prog_interface p) prog_st' ctx_st1 -> *)
  (*     mt_starN c (prog_interface p) (prepare_global_env c) n2 ctx_st1 t3 ips' -> *)
  (*   forall n3 ips'', *)
  (*     st_starN p (prog_interface c) (prepare_global_env p) *)
  (*              n3 ctx_st2 (t1 ** t2 ** t3) ips'' -> *)
  (*     False. *)
  (* Proof. *)
  (*   intros n1 ps1 cs1 ps2 t1 cs3 t2 n3 t3 s4 *)
  (*          Hcs1 Hps1 Hmerge1 Hst_starN12 Hstep23 Hturn23 Hmt_starN34 *)
  (*          n s4' Hst_starN14. *)
  (* Abort. (* Grade 2. After st_starN_with_turn_change_impossible_1. *) *)

  (* Lemma st_starN_with_turn_change_impossible_3: *)
  (*   forall n1 prog_st ctx_st2 prog_st' t1 ctx_st1 t2 n2 t3 ips', *)
  (*     PS.is_program_component prog_st (prog_interface c) -> *)
  (*     PS.is_context_component ctx_st2 (prog_interface p) -> *)
  (*     PS.mergeable_states (prog_interface c) (prog_interface p) *)
  (*                         prog_st ctx_st2 -> *)
  (*     st_starN p (prog_interface c) (prepare_global_env p) *)
  (*              n1 prog_st t1 prog_st' -> *)
  (*     PS.step p (prog_interface c) (prepare_global_env p) prog_st' t2 ctx_st1 -> *)
  (*     ~ same_turn (prog_interface c) prog_st' ctx_st1 -> *)
  (*     mt_starN p (prog_interface c) (prepare_global_env p) n2 ctx_st1 t3 ips' -> *)
  (*   forall n3 ips'', *)
  (*     st_starN c (prog_interface p) (prepare_global_env c) *)
  (*              n3 ctx_st2 (t1 ** t2 ** t3) ips'' -> *)
  (*     False. *)
  (* Proof. *)
  (*   intros n1 ps1 cs1 ps2 t1 cs3 t2 n3 t3 s4 *)
  (*          Hcs1 Hps1 Hmerge1 Hst_starN12 Hstep23 Hturn23 Hmt_starN34 *)
  (*          n s4' Hst_starN14. *)
  (* Abort. (* Grade 2. After st_starN_with_turn_change_impossible_1. *) *)

  (* (* RB: XXX: I do not believe this is true. In particular, after the turn *)
  (*    changes nothing tells us that the two runs need to run to exhaustion: each *)
  (*    is free to stop at any point independently from the other, irrespective of *)
  (*    whether the runs up to the turn change are identical, and nothing connects *)
  (*    their "final" states. *) *)
  (* Lemma same_trace_and_steps: *)
  (*   forall prog_st1 prog_st1' prog_st2 ctx_st1 ctx_st1' *)
  (*          ctx_st2 ips' ips'' n1 n1' n2 n2' t1 t1' t2 t2' t3 t3', *)
  (*     PS.is_program_component prog_st1 (prog_interface c) -> *)
  (*     PS.is_context_component ctx_st1 (prog_interface p) -> *)
  (*     PS.mergeable_states (prog_interface c) (prog_interface p) *)
  (*                         prog_st1 ctx_st1 -> *)
  (*     (* first side *) *)
  (*     st_starN p (prog_interface c) (prepare_global_env p) *)
  (*              n1 prog_st1 t1 prog_st1' -> *)
  (*     PS.step p (prog_interface c) (prepare_global_env p) prog_st1' t2 ctx_st2 -> *)
  (*     ~ same_turn (prog_interface c) prog_st1' ctx_st2 -> *)
  (*     mt_starN p (prog_interface c) (prepare_global_env p) n2 ctx_st2 t3 ips' -> *)
  (*     (* second side *) *)
  (*     st_starN c (prog_interface p) (prepare_global_env c) *)
  (*              n1' ctx_st1 t1' ctx_st1' -> *)
  (*     PS.step c (prog_interface p) (prepare_global_env c) ctx_st1' t2' prog_st2 -> *)
  (*     ~ same_turn (prog_interface p) ctx_st1' prog_st2 -> *)
  (*     mt_starN c (prog_interface p) (prepare_global_env c) n2' prog_st2 t3' ips'' -> *)
  (*     (* same steps and same trace *) *)
  (*     t1 = t1' /\ t2 = t2' /\ t3 = t3' /\ n1 = n1' /\ n2 = n2'. *)
  (* Proof. *)
  (*   intros s1 s2 s3' s1' s2' *)
  (*          s3 s4 s4' n1 n1' n3 n3' t1 t1' t2 t2' t3 t3' *)
  (*          Hpc_s1 Hcc_s1' Hmerge *)
  (*          Hst_starN12 Hstep23 Hturn23 Hmt_starN34 *)
  (*          Hst_starN12' Hstep23' Hturn23' Hmt_starN34'. *)
  (* Abort. *)

  (* (* RB: XXX: See [same_trace_and_steps] above. *) *)
  (* Lemma same_trace_and_steps': *)
  (*   forall prog_st1 prog_st1' prog_st2 ctx_st1 ctx_st1' *)
  (*          ctx_st2 ips' ips'' n1 n1' n2 n2' t1 t1' t2 t2' t3 t3', *)
  (*     PS.is_context_component ctx_st1 (prog_interface c) -> *)
  (*     PS.is_program_component prog_st1 (prog_interface p) -> *)
  (*     PS.mergeable_states (prog_interface c) (prog_interface p) *)
  (*                         ctx_st1 prog_st1 -> *)
  (*     (* first side *) *)
  (*     st_starN p (prog_interface c) (prepare_global_env p) *)
  (*              n1 ctx_st1 t1 ctx_st1' -> *)
  (*     PS.step p (prog_interface c) (prepare_global_env p) ctx_st1' t2 prog_st2 -> *)
  (*     ~ same_turn (prog_interface c) ctx_st1' prog_st2 -> *)
  (*     mt_starN p (prog_interface c) (prepare_global_env p) n2 prog_st2 t3 ips'' -> *)
  (*     (* second side *) *)
  (*     st_starN c (prog_interface p) (prepare_global_env c) *)
  (*              n1' prog_st1 t1' prog_st1' -> *)
  (*     PS.step c (prog_interface p) (prepare_global_env c) prog_st1' t2' ctx_st2 -> *)
  (*     ~ same_turn (prog_interface p) prog_st1' ctx_st2 -> *)
  (*     mt_starN c (prog_interface p) (prepare_global_env c) n2' ctx_st2 t3' ips' -> *)
  (*     (* same steps and same trace *) *)
  (*     t1 = t1' /\ t2 = t2' /\ t3 = t3' /\ n1 = n1' /\ n2 = n2'. *)
  (* Proof. *)
  (*   intros s1' s2' s3 s1 s2 *)
  (*          s3' s4' s4 n1 n1' n3 n3' t1 t1' t2 t2' t3 t3' *)
  (*          Hpc_s1 Hcc_s1' Hmerge *)
  (*          Hst_starN12 Hstep23 Hturn23 Hmt_starN34 *)
  (*          Hst_starN12' Hstep23' Hturn23' Hmt_starN34'. *)
  (* Abort. *)

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

    assert (prog_is_closed_sym := prog_is_closed).
    rewrite (closed_program_link_sym wf1 wf2 linkability) in prog_is_closed_sym.

    generalize dependent ips2.
    induction Hmt_star1
      as [| n1 n2 n3 s1 t1 s2 t2 s3 t3 s4 t
            Hst_starN12 Hstep23 Hturn23 Hmt_starN34 IHmt_starN14 Hn3 Ht];
      subst.

    (* single segment *)
    - intros ips2 Hmergeable Hmt_star2.
      rename H into Hst_starN.

      destruct
        (StarNSim.st_starN_simulation
           wf1 wf2 linkability main_linkability prog_is_closed mergeable_interfaces
           Hst_starN Hmergeable)
        as [ips2'' [Hst_starN2 Hmergeable']].
      (* If ips2 takes n steps to get to ips2'' in one turn, and to ips2' in
         possibly several, clearly they coincide. *)
      assert (Hst_starN2' := Hst_starN2).
      apply mt_starN_if_st_starN in Hst_starN2'.
      pose proof StateDet.state_determinism_mt_starN
           wf2 wf1
           (linkable_sym linkability) (linkable_mains_sym main_linkability)
           prog_is_closed_sym (mergeable_interfaces_sym _ _ mergeable_interfaces)
           Hmt_star2 Hst_starN2'
        as Heq.
      subst ips2''.

      exact (threeway_multisem_st_starN_simulation Hmergeable Hst_starN Hst_starN2).

      (* inversion Hmergeable as [ics ? ? Hsame_ifaces Hcomes_from Hpartial1 Hpartial2]; *)
      (*   subst. *)
      (* inversion Hpartial1 as [? ? ? ? ? ? Hpc1 | ? ? ? ? ? ? Hcc1]; subst; *)
      (*   inversion Hpartial2 as [? ? ? ? ? ? Hpc2 | ? ? ? ? ? ? Hcc2]; subst. *)

      (* + (* Contra. *) *)
      (*   PS.simplify_turn. *)
      (*   apply (PS.domm_partition Hsame_ifaces Hcomes_from) in Hpc2. *)
      (*   rewrite Hpc2 in Hpc1. *)
      (*   discriminate. *)

      (* (* the program has control in the first state of the first sequence *) *)
      (* + inversion Hmt_star2; subst. *)

      (*   (* single segment with the same trace *) *)
      (*   * eapply threeway_multisem_st_starN_simulation; eauto. *)

      (*   (* segment + change of control + mt_star *) *)
      (*   (* contradiction *) *)
      (*   (* this case cannot happen since t2 is an event that changes *)
      (*      control and it appears in the st_star segment *) *)
      (*   * exfalso. *)
      (*     eapply st_starN_with_turn_change_impossible_1; eauto. *)

      (* (* the context has control in the first state of the first sequence *) *)
      (* + inversion Hmt_star2; subst. *)

      (*   (* single segment with the same trace *) *)
      (*   * eapply threeway_multisem_st_starN_simulation; eauto. *)

      (*   (* segment + change of control + mt_star *) *)
      (*   (* contradiction *) *)
      (*   (* this case cannot happen since t2 is an event that changes *)
      (*      control and it appears in the st_star segment *) *)
      (*   * exfalso. *)
      (*     eapply st_starN_with_turn_change_impossible_2; eauto. *)

      (* + (* Contra. *) *)
      (*   PS.simplify_turn. *)
      (*   apply (PS.domm_partition_notin Hsame_ifaces) in Hcc2. *)
      (*   rewrite Hcc1 in Hcc2. *)
      (*   discriminate. *)

    (* segment + change of control + mt_star *)
    - rename ips2' into s4'.
      intros s1' Hmergeable1 Hmt_starN14'.

      destruct
        (StarNSim.st_starN_simulation
           wf1 wf2 linkability main_linkability prog_is_closed mergeable_interfaces
           Hst_starN12 Hmergeable1)
        as [s2' [Hst_starN12' Hmergeable2]].
      destruct
        (threeway_multisem_st_starN_simulation
           Hmergeable1 Hst_starN12 Hst_starN12')
        as [HstarN12 _].

      destruct
        (StarNSim.control_change_simulation
           wf1 wf2 linkability main_linkability prog_is_closed mergeable_interfaces
           Hstep23 Hturn23 Hmergeable2)
        as [s3' [Hstep23' [Hturn23' Hmergeable3]]].
      (* destruct *)
        (* (threeway_multisem_control_change *)
           (* Hmergeable2 Hstep23 Hstep23' Hturn23 Hturn23') *)
        (* as [HstarN23 _]. *)

      destruct
        (StarNSim.mt_starN_simulation
           wf1 wf2 linkability main_linkability prog_is_closed mergeable_interfaces
           Hmt_starN34 Hmergeable3)
        as [s4'' [Hmt_starN34' Hmergeable4]].
      pose proof (mt_starN_control_change
                    Hst_starN12' Hstep23' Hturn23' Hmt_starN34'
                    (eq_refl _) (eq_refl _))
        as Hmt_starN14''.
      pose proof StateDet.state_determinism_mt_starN
           wf2 wf1
           (linkable_sym linkability) (linkable_mains_sym main_linkability)
           prog_is_closed_sym (mergeable_interfaces_sym _ _ mergeable_interfaces)
           Hmt_starN14' Hmt_starN14''
        as Heq.
      subst s4''.

      specialize (IHmt_starN14 s3' Hmergeable3 Hmt_starN34').
      destruct IHmt_starN14 as [HstarN34 _].

      split.
      + eapply starN_trans
          with (n1 := n1) (t1 := t1) (s2 := (s2, s2'))
               (n2 := 1 + n2) (t2 := t2 ** t3).
        * assumption.
        * eapply starN_step with (t1 := t2) (s' := (s3, s3')) (t2 := t3).
          -- constructor; assumption.
          -- assumption.
          -- reflexivity.
        * omega.
        * reflexivity.
      + assumption.

    (* - intros ips2 Hmergeable Hmt_star2. *)
    (*   inversion Hmergeable as [ics ? ? Hsame_ifaces Hcomes_from Hpartial1 Hpartial2]; *)
    (*     subst. *)
    (*   inversion Hpartial1 as [? ? ? ? ? ? Hpc1 | ? ? ? ? ? ? Hcc1]; subst; *)
    (*     inversion Hpartial2 as [? ? ? ? ? ? Hpc2 | ? ? ? ? ? ? Hcc2]; subst. *)

    (*   + (* Contra. *) *)
    (*     PS.simplify_turn. *)
    (*     apply (PS.domm_partition Hsame_ifaces Hcomes_from) in Hpc2. *)
    (*     rewrite Hpc2 in Hpc1. *)
    (*     discriminate. *)

    (*   (* the program has control in the first state of the first sequence *) *)
    (*   + inversion Hmt_star2; subst. *)

    (*     (* single segment with the same trace *) *)
    (*     (* contradiction *) *)
    (*     (* this case cannot happen since t2 is an event that changes *)
    (*        control and it appears in the st_star segment *) *)
    (*     * exfalso. *)
    (*       eapply st_starN_with_turn_change_impossible_3; eauto. *)

    (*     (* segment + change of control + mt_star *) *)
    (*     * destruct (same_trace_and_steps *)
    (*                   Hpc1 Hcc2 Hmergeable H H0 H1 Hmt_star1 H2 H3 H4 H5) *)
    (*         as [Ht1 [Ht2 [Ht3 [Hn1 Hn2]]]]. subst. *)
    (*       (* simulate the first segment (trace t0) *) *)

    (*       destruct (threeway_multisem_st_starN_simulation Hmergeable H H2) *)
    (*         as [Hfirst_segment Hmergeable']. *)

    (*       (* build the step that changes control (trace t4) *) *)

    (*       assert (MultiSem.step p c (prepare_global_env prog) (ips', ips'0) t4 (ips'', ips''0)) *)
    (*         as Hmultistep. { *)
    (*         constructor; auto. *)
    (*       } *)

    (*       assert (MultiSem.multi_match p c *)
    (*                                    (ips', ips'0) (PS.merge_partial_states ips' ips'0)) *)
    (*         as Hmultimatch. { *)
    (*         constructor; auto. *)
    (*       } *)

    (*       (* use the multisem simulation to show that the states after the step are still *)
    (*          mergeable *) *)
    (*       destruct (MultiSem.lockstep_simulation *)
    (*                   wf1 wf2 main_linkability linkability mergeable_interfaces *)
    (*                   Hmultistep Hmultimatch) *)
    (*         as [merged_state' [Hmiddle_step Hmergeable'']]. *)
    (*       inversion Hmergeable''; subst. *)

    (*       (* simulate the rest of the sequence (trace t5) *) *)

    (*       destruct (IHHmt_star1 ips''0 H11 H5) *)
    (*         as [Hlast_star Hmergeable''']. *)

    (*       (* compose first segment + step that changes control + last star *) *)

    (*       split. *)
    (*       ** eapply starN_trans. *)
    (*          *** eapply starN_right. *)
    (*              **** apply Hfirst_segment. *)
    (*              **** apply Hmultistep. *)
    (*              **** reflexivity. *)
    (*          *** apply Hlast_star. *)
    (*          *** reflexivity. *)
    (*          *** apply app_assoc. *)
    (*       ** assumption. *)

    (*   (* the context has control in the first state of the first sequence *) *)
    (*   + inversion Hmt_star2; subst. *)

    (*     (* single segment with the same trace *) *)
    (*     (* contradiction *) *)
    (*     (* this case cannot happen since t2 is an event that changes *)
    (*        control and it appears in the st_star segment *) *)
    (*     * exfalso. *)
    (*       eapply st_starN_with_turn_change_impossible_1'; eauto. *)

    (*     (* segment + change of control + mt_star *) *)
    (*     * destruct (same_trace_and_steps' *)
    (*                   Hcc1 Hpc2 Hmergeable H H0 H1 Hmt_star1 H2 H3 H4 H5) *)
    (*         as [Ht1 [Ht2 [Ht3 [Hn1 Hn2]]]]. subst. *)

    (*       (* simulate the first segment (trace t0) *) *)

    (*       destruct (threeway_multisem_st_starN_simulation Hmergeable H H2) *)
    (*         as [Hfirst_segment Hmergeable']. *)

    (*       (* build the step that changes control (trace t4) *) *)

    (*       assert (MultiSem.step p c (prepare_global_env prog) (ips', ips'0) t4 (ips'', ips''0)) *)
    (*         as Hmultistep. { *)
    (*         constructor; auto. *)
    (*       } *)

    (*       assert (MultiSem.multi_match p c *)
    (*                                    (ips', ips'0) (PS.merge_partial_states ips' ips'0)) *)
    (*         as Hmultimatch. { *)
    (*         constructor; auto. *)
    (*       } *)

    (*       (* use the multisem simulation to show that the states after the step are still *)
    (*          mergeable *) *)
    (*       destruct (MultiSem.lockstep_simulation *)
    (*                   wf1 wf2 main_linkability linkability mergeable_interfaces *)
    (*                   Hmultistep Hmultimatch) *)
    (*         as [merged_state' [Hmiddle_step Hmergeable'']]. *)
    (*       inversion Hmergeable''; subst. *)

    (*       (* simulate the rest of the sequence (trace t5) *) *)

    (*       destruct (IHHmt_star1 ips''0 H11 H5) *)
    (*         as [Hlast_star Hmergeable''']. *)

    (*       (* compose first segment + step that changes control + last star *) *)

    (*       split. *)
    (*       ** eapply starN_trans. *)
    (*          *** eapply starN_right. *)
    (*              **** apply Hfirst_segment. *)
    (*              **** apply Hmultistep. *)
    (*              **** reflexivity. *)
    (*          *** apply Hlast_star. *)
    (*          *** reflexivity. *)
    (*          *** apply app_assoc. *)
    (*       ** assumption. *)

    (*   + (* Contra. *) *)
    (*     PS.simplify_turn. *)
    (*     apply (PS.domm_partition_notin Hsame_ifaces) in Hcc2. *)
    (*     rewrite Hcc1 in Hcc2. *)
    (*     discriminate. *)

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
  Admitted. (* RB: Only if needed by partial_programs_composition_prefix. *)

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

  (* Equivalence st_starN n1, n2 on program and context *)
  (* Lemma partial_programs_composition_st_starN : *)
  (*   forall s1 s1' s2 s2' n1 n2 t, *)
  (*     PS.mergeable_states (prog_interface c) (prog_interface p) s1 s1' -> *)
  (*     st_starN p (prog_interface c) (prepare_global_env p) n1 s1 t s2 -> *)
  (*     st_starN c (prog_interface p) (prepare_global_env c) n2 s1' t s2' -> *)
  (*     PS.mergeable_states (prog_interface c) (prog_interface p) s2 s2'. *)
  (* Abort. *)

  (* RB: TODO: Add hypotheses and/or encapsulate in own section, or relocate to
     PS: what is a better match?
     NOTE: For some of these results, I wonder whether the use of "fancy stars"
     is substantially simpler than regular stars, and whether some of the results
     are too strong to be used effectively in all situations where we would need
     their assistance. In particular, the focus on two executions, in the program
     and in the context, taking place in the same number of steps seems too
     strong. *)
  (* Lemma partial_programs_composition_star : *)
  (*   forall sini1 sini2 t s1 s2, *)
  (*     PS.initial_state p (prog_interface c) sini1 -> *)
  (*     PS.initial_state c (prog_interface p) sini2 -> *)
  (*     star (PS.step p (prog_interface c)) (prepare_global_env p) sini1 t s1 -> *)
  (*     star (PS.step c (prog_interface p)) (prepare_global_env c) sini2 t s2 -> *)
  (*   exists sini s, *)
  (*     PS.initial_state prog emptym sini /\ *)
  (*     star (PS.step prog emptym) (prepare_global_env prog) sini t s.     *)
  (* Abort. *)

End PartialComposition.

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
    eapply PS2CS.partial_semantics_implies_complete_semantics; auto.
    - apply linking_well_formedness; auto.
    - apply partial_programs_composition; auto.
  Qed.
End Composition.

Section Recombination.

  Section Mergeable.

  Variables p c p' c' : program.

  Hypothesis Hwfp  : well_formed_program p.
  Hypothesis Hwfc  : well_formed_program c.
  Hypothesis Hwfp' : well_formed_program p'.
  Hypothesis Hwfc' : well_formed_program c'.

  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Hypothesis Hifacep  : prog_interface p  = prog_interface p'.
  Hypothesis Hifacec  : prog_interface c  = prog_interface c'.

  (* RB: TODO: Simplify redundancies in standard hypotheses. *)
  (* Hypothesis Hmain_linkability  : linkable_mains p  c. *)
  (* Hypothesis Hmain_linkability' : linkable_mains p' c'. *)

  Hypothesis Hprog_is_closed  : closed_program (program_link p  c ).
  Hypothesis Hprog_is_closed' : closed_program (program_link p' c').

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem prog.
  Let sem'  := CS.sem prog'.
  Let sem'' := CS.sem prog''.
  Hint Unfold ip ic prog prog' prog'' sem sem' sem''.

  (* TODO: clean
     RB: NOTE: This is no longer needed. A stronger result is obtained from
     existing lemmas and use in place. *)
  Lemma star_mem_well_formed s1 t gps2 mem2 regs2 pc2 :
    initial_state sem s1 ->
    Star sem s1 t (gps2, mem2, regs2, pc2) ->
    fsubset (domm mem2) (domm (unionm ip ic)).
  Proof.
    intros Hini Hstar.
    remember (gps2, mem2, regs2, pc2) as s2.
    revert gps2 mem2 regs2 pc2 Heqs2.
    apply star_iff_starR in Hstar.
    induction Hstar as [|? ? ? ? ? ? ? IH].
    - intros gps mem regs pc Heqs.
      simpl in Hini; unfold CS.initial_state in Hini.
      rewrite CS.initial_machine_state_after_linking in Hini; try assumption;
        last by destruct Hmergeable_ifaces.
      subst; inversion Hini; subst.
      rewrite domm_union 2!domm_prepare_procedures_memory -domm_union.
      now apply fsubsetxx.
    - intros gps3 mem3 regs3 pc3 Heqs3; subst.
      destruct s2 as [[[gps2 mem2] regs2] pc2].
      specialize (IH Hini gps2 mem2 regs2 pc2 eq_refl).
      inversion H; subst; try assumption.
      + unfold Memory.store in H12.
        destruct (mem2 (Pointer.component ptr));
          try destruct (ComponentMemory.store t (Pointer.block ptr) (Pointer.offset ptr) (Register.get r2 regs3));
          try match goal with
              | Heq: Some _ = Some _ |- _ => inversion Heq; subst
              | Heq: None = Some _ |- _ => now inversion Heq
              | Heq: Some = None _ |- _ => now inversion Heq
              end.
        assert (Hin : Pointer.component ptr \in domm (unionm ip ic)).
        { rewrite H11.
          rewrite domm_union.
          rewrite in_fsetU. apply /orP.
          apply star_iff_starR in Hstar.
          eapply pc_component_in_ip_or_ic; eassumption.
        }
        rewrite domm_set.
        rewrite fsubU1set.
        apply /andP. now split.
      + unfold Memory.alloc in H12.
        destruct (mem2 (Pointer.component pc2));
          try destruct (ComponentMemory.alloc t (Z.to_nat size));
          try match goal with
              | Heq: Some _ = Some _ |- _ => inversion Heq; subst
              | Heq: None = Some _ |- _ => now inversion Heq
              | Heq: Some = None _ |- _ => now inversion Heq
              end.
        assert (Hin : Pointer.component pc2 \in domm (unionm ip ic)).
        { rewrite domm_union.
          rewrite in_fsetU. apply /orP.
          apply star_iff_starR in Hstar.
          eapply pc_component_in_ip_or_ic; eassumption.
        }
        rewrite domm_set.
        rewrite fsubU1set.
        apply /andP. now split.
  Qed.

  End Mergeable.

End Recombination.
