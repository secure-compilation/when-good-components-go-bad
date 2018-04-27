Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Blame.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Source.PS.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import Source.

Section Decomposition.
  Variable p c: program.

  Hypothesis wf1 : well_formed_program p.
  Hypothesis wf2 : well_formed_program c.

  Hypothesis linkability: linkable (prog_interface p) (prog_interface c).

  Hypothesis closedness_after_linking:
    closed_program (program_link p c).

  Lemma match_initial_states:
    forall ics,
      CS.initial_state (program_link p c) ics ->
    exists ips,
      PS.initial_state p (prog_interface c) ips /\
      PS.partial_state (prog_interface c) ics ips.
  Proof.
    intros ics Hics_init.
    CS.unfold_states.
    (* case analysis on who has control, then build the partial state *)
    destruct (C \in domm (prog_interface c)) eqn:Htarget;
      exists (PS.partialize (prog_interface c) (C, s, mem, k, e));
      simpl; rewrite Htarget.
    (* context has control *)
    - split.
      + eapply PS.initial_state_intro with (p':=c).
        * reflexivity.
        * assumption.
        * assumption.
        * assumption.
        * assumption.
        * eapply PS.ContextControl; eauto.
        * apply Hics_init.
      + eapply PS.ContextControl; eauto.
    (* program has control *)
    - split.
      + eapply PS.initial_state_intro with (p':=c).
        * reflexivity.
        * assumption.
        * assumption.
        * assumption.
        * assumption.
        * eapply PS.ProgramControl; auto.
          ** PS.simplify_turn.
             unfold negb. rewrite Htarget. auto.
        * apply Hics_init.
      + eapply PS.ProgramControl; auto.
        * PS.simplify_turn.
          unfold negb. rewrite Htarget. auto.
  Qed.

  Lemma match_final_states:
    forall ics ips,
      PS.partial_state (prog_interface c) ics ips ->
      CS.final_state ics ->
      PS.final_state p (prog_interface c) ips.
  Proof.
    intros ics ips Hpartial Hics_final.
    CS.unfold_states.
    (* case analysis on who has control *)
    destruct (C \in domm (prog_interface c)) eqn:Htarget.
    (* context has control *)
    - inversion Hpartial; inversion H; subst.
      + PS.simplify_turn.
        rewrite Htarget in H5. discriminate.
      + apply PS.final_state_context.
        PS.simplify_turn. auto.
    (* program has control *)
    - inversion Hpartial; inversion H; subst.
      + eapply PS.final_state_program with (p':=c).
        * reflexivity.
        * assumption.
        * assumption.
        * assumption.
        * PS.simplify_turn. rewrite Htarget. auto.
        * eauto.
        * assumption.
      + PS.simplify_turn.
        rewrite Htarget in H5. discriminate.
  Qed.

  Lemma match_initial_states_by_partialize : forall scs0,
    CS.initial_state (program_link p c) scs0 ->
    PS.initial_state p (prog_interface c) (PS.partialize (prog_interface c) scs0).
  Proof.
    intros scs0 Hini.
    eapply PS.initial_state_intro;
      try reflexivity;
      try assumption.
    unfold CS.initial_state in Hini.
    unfold CS.initial_machine_state in *.
    rewrite <- PS.partialize_correct.
    destruct (prog_main (program_link p c)) as [main |] eqn:Hmain;
      subst;
      easy.
  Qed.

  Lemma lockstep_simulation:
    forall ics t ics',
      CS.kstep (prepare_global_env (program_link p c)) ics t ics' ->
    forall ips,
      PS.partial_state (prog_interface c) ics ips ->
    exists ips',
      PS.kstep p (prog_interface c) (prepare_global_env p) ips t ips' /\
      PS.partial_state (prog_interface c) ics' ips'.
  Proof.
    intros ics t ics' Hstep ips Hpartial.

    (* case analysis on who has control and the executed step *)
    inversion linkability; subst.
    inversion Hpartial; subst;
    inversion Hstep; subst.

    (** program has control **)

    (* epsilon steps *)

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    (* call *)
    - PS.simplify_turn.
      (* case analisys on the target *)
      destruct (C' \in domm (prog_interface c)) eqn:Htarget.
      (* external call *)
      + eexists. split.
        * eapply PS.partial_step with (p':=c); auto.
          ** eassumption.
          ** eapply PS.ProgramControl; auto.
          ** eapply PS.ContextControl; auto.
        * eapply PS.ContextControl; auto.
      (* internal call *)
      + eexists. split.
        * eapply PS.partial_step with (p':=c); auto.
          ** eassumption.
          ** eapply PS.ProgramControl; auto.
          ** eapply PS.ProgramControl; auto.
             *** PS.simplify_turn.
                 unfold negb. rewrite Htarget. auto.
        * eapply PS.ProgramControl; auto.
          ** PS.simplify_turn.
             unfold negb. rewrite Htarget. auto.

    (* internal return (program to program) *)
    - PS.simplify_turn.
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    (* external return *)
    - PS.simplify_turn.
      (* case analisys on the target *)
      destruct (C' \in domm (prog_interface c)) eqn:Htarget.
      (* external return *)
      + eexists. split.
        * eapply PS.partial_step with (p':=c); auto.
          ** eassumption.
          ** eapply PS.ProgramControl; auto.
          ** eapply PS.ContextControl; auto.
        * eapply PS.ContextControl; auto.
      (* internal return *)
      + eexists. split.
        * eapply PS.partial_step with (p':=c); auto.
          ** eassumption.
          ** eapply PS.ProgramControl; auto.
          ** eapply PS.ProgramControl; auto.
             *** PS.simplify_turn.
                 unfold negb. rewrite Htarget. auto.
        * eapply PS.ProgramControl; auto.
          ** PS.simplify_turn.
             unfold negb. rewrite Htarget. auto.

    (** context has control **)

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
          ** PS.simplify_turn.
             erewrite <- context_allocation_in_partialized_memory; eauto.
      + eapply PS.ContextControl; eauto.
        * PS.simplify_turn.
          erewrite <- context_allocation_in_partialized_memory; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
          ** PS.simplify_turn.
             erewrite <- context_store_in_partialized_memory; eauto.
      + eapply PS.ContextControl; eauto.
        * PS.simplify_turn.
          erewrite <- context_store_in_partialized_memory; eauto.

    - eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    (* internal call *)
    - PS.simplify_turn.
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    (* external call *)
    - PS.simplify_turn.
      (* case analysis on the target *)
      destruct (C' \in domm (prog_interface c)) eqn:Htarget.
      (* internal call *)
      + eexists. split.
        * eapply PS.partial_step with (p':=c); auto.
          ** eassumption.
          ** eapply PS.ContextControl; auto.
          ** eapply PS.ContextControl; auto.
        * eapply PS.ContextControl; auto.
      (* external call *)
      + eexists. split.
        * eapply PS.partial_step with (p':=c); auto.
          ** eassumption.
          ** eapply PS.ContextControl; auto.
          ** eapply PS.ProgramControl; auto.
             *** PS.simplify_turn.
                 unfold negb. rewrite Htarget. auto.
        * eapply PS.ProgramControl; auto.
          ** PS.simplify_turn.
             unfold negb. rewrite Htarget. auto.

    (* internal return *)
    - PS.simplify_turn.
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    (* external return *)
    - PS.simplify_turn.
      (* case analysis on the target *)
      destruct (C' \in domm (prog_interface c)) eqn:Htarget.
      (* internal return *)
      + eexists. split.
        * eapply PS.partial_step with (p':=c); auto.
          ** eassumption.
          ** eapply PS.ContextControl; auto.
          ** eapply PS.ContextControl; auto.
        * eapply PS.ContextControl; auto.
      (* external return *)
      + eexists. split.
        * eapply PS.partial_step with (p':=c); auto.
          ** eassumption.
          ** eapply PS.ContextControl; auto.
          ** eapply PS.ProgramControl; auto.
             *** PS.simplify_turn.
                 unfold negb. rewrite Htarget. auto.
        * eapply PS.ProgramControl; auto.
          ** PS.simplify_turn.
             unfold negb. rewrite Htarget. auto.
  Qed.

  Theorem decomposition:
    forward_simulation (CS.sem (program_link p c))
                       (PS.sem p (prog_interface c)).
  Proof.
    eapply forward_simulation_step.
    - apply match_initial_states.
    - apply match_final_states.
    - apply lockstep_simulation.
  Qed.

  Corollary decomposition_with_safe_behavior:
    forall beh,
      program_behaves (CS.sem (program_link p c)) beh ->
      not_wrong beh ->
      program_behaves (PS.sem p (prog_interface c)) beh.
  Proof.
    intros beh.
    eapply forward_simulation_same_safe_behavior; eauto.
    apply decomposition.
  Qed.

  Corollary decomposition_with_refinement:
    forall beh1,
      program_behaves (CS.sem (program_link p c)) beh1 ->
    exists beh2,
      program_behaves (PS.sem p (prog_interface c)) beh2 /\
      behavior_improves beh1 beh2.
  Proof.
    intros beh1 Hbeh1.
    eapply forward_simulation_behavior_improves; eauto.
    apply decomposition.
  Qed.

  Inductive well_defined_components (iface: Program.interface): event -> Prop :=
  | wf_comps_call: forall C1 P arg C2,
      C1 \in domm iface ->
      C2 \in domm iface ->
      well_defined_components iface (ECall C1 P arg C2)
  | wf_comps_ret: forall C1 arg C2,
      C1 \in domm iface ->
      C2 \in domm iface ->
      well_defined_components iface (ERet C1 arg C2).

  Definition well_defined_components_trace (iface : Program.interface) (t : trace) : Prop :=
    forall e, In e t -> well_defined_components iface e.

  Remark genv_buffers_in_interface C :
    C \in domm (genv_buffers (prepare_global_env (program_link p c))) ->
    C \in domm (prog_interface (program_link p c)).
  Proof.
    rewrite /= domm_map !domm_union.
    by case: wf1 wf2 => [_ _ _ _ -> _ _] [_ _ _ _ -> _ _].
  Qed.

  (* Several alternative formulations are possible. One may include the ERet event
     in the star, express the inclusion of ECall in the trace via In, etc. *)
  Lemma eret_from_initial_star_goes_after_ecall_cs :
    forall s0 t s1 s2 C' v C,
      CS.initial_state (program_link p c) s0 ->
      star CS.kstep (prepare_global_env (program_link p c)) s0 t s1 ->
      CS.kstep (prepare_global_env (program_link p c)) s1 [ERet C' v C] s2 ->
    exists t1 s s' t2 P v',
      star CS.kstep (prepare_global_env (program_link p c)) s0 t1 s /\
      CS.kstep (prepare_global_env (program_link p c)) s [ECall C P v' C'] s' /\
      star CS.kstep (prepare_global_env (program_link p c)) s' t2 s1 /\
      t = t1 ** [ECall C P v' C'] ** t2.
  Admitted.

  Lemma ecall_from_star_has_well_defined_components :
    forall s0 t1 s1 s2 C P v C',
      star CS.kstep (prepare_global_env (program_link p c)) s0 t1 s1 ->
      CS.kstep (prepare_global_env (program_link p c)) s1 [ECall C P v C'] s2 ->
      well_defined_components (prog_interface (program_link p c)) (ECall C P v C').
  Proof.
    intros s0 t1 s1 s2 C P v C' Hstar Hkstep.
    inversion Hkstep; subst.
    by apply wf_comps_call; apply: genv_buffers_in_interface;
    rewrite mem_domm ?H7 ?H10.
  Qed.

  Lemma eret_from_initial_star_has_well_defined_components :
    forall s0 t1 s1 s2 C v C',
      CS.initial_state (program_link p c) s0 ->
      star CS.kstep (prepare_global_env (program_link p c)) s0 t1 s1 ->
      CS.kstep (prepare_global_env (program_link p c)) s1 [ERet C v C'] s2 ->
      well_defined_components (prog_interface (program_link p c)) (ERet C v C').
  Proof.
    intros s0 t1 s1 s2 C v C' Hinitial Hstar Hkstep.
    inversion Hkstep; subst.
    apply wf_comps_ret.
    - destruct (eret_from_initial_star_goes_after_ecall_cs Hinitial Hstar Hkstep)
        as [t1' [s1' [s2' [t2' [P [v' [Hstar1' [Hkstep' [Hstar2' Heq']]]]]]]]].
      subst t1.
      pose proof ecall_from_star_has_well_defined_components Hstar1' Hkstep' as Hwdc.
      inversion Hwdc; subst.
      assumption.
    - now apply: genv_buffers_in_interface; rewrite mem_domm H5.
  Qed.

  (* RB: TODO: Can be further simplified by automating inversion a bit. *)
  Lemma step_from_initial_star_has_well_defined_components :
    forall s0 t1 s1 t2 s2,
      CS.initial_state (program_link p c) s0 ->
      star CS.kstep (prepare_global_env (program_link p c)) s0 t1 s1 ->
      CS.kstep (prepare_global_env (program_link p c)) s1 t2 s2 ->
      well_defined_components_trace (prog_interface (program_link p c)) t2.
  Proof.
    intros s0 t1 s1 t2 s2 Hinitial Hstar Hkstep e HIn.
    inversion Hkstep; subst;
      try inversion HIn; subst.
    - eapply ecall_from_star_has_well_defined_components; eassumption.
    - by inversion H6.
    - eapply eret_from_initial_star_has_well_defined_components; eassumption.
    - by inversion H2.
  Qed.

  (* This follows easily from previous lemmas by a right-side induction on Star. *)
  Lemma initial_star_has_well_defined_components :
    forall sini t sfin,
      initial_state (CS.sem (program_link p c)) sini ->
      Star (CS.sem (program_link p c)) sini t sfin ->
      well_defined_components_trace (unionm (prog_interface p) (prog_interface c)) t.
  Proof.
    intros sini t sfin Hinitial Hstar.
    apply star_iff_starR in Hstar.
    induction Hstar as [| s0 t1 s1 t2 s2 t HStar IHHstar HStep].
    - easy.
    - subst t.
      specialize (IHHstar Hinitial).
      apply star_iff_starR in HStar.
      pose proof
        @step_from_initial_star_has_well_defined_components _ _ _ _ _ Hinitial HStar HStep
        as Hwdc.
      intros e HIn.
      apply in_app_or in HIn as [HIn1 | HIn2];
        by auto.
  Qed.

  Lemma ub_behavior_has_well_defined_components:
    forall t,
      program_behaves (CS.sem (program_link p c)) (Goes_wrong t) ->
    forall e,
      In e t ->
      well_defined_components (prog_interface (program_link p c)) e.
  Proof.
    intros t Hprbeh e HIn.
    inversion Hprbeh as [sini tmp Hini Hstbeh |]; subst;
      last easy.
    inversion Hstbeh as [| | | tmp sfin HStar HNostep Hfinalst]; subst.
    eapply initial_star_has_well_defined_components; eassumption.
  Qed.

  Lemma ub_blaming:
    forall t,
      program_behaves (CS.sem (program_link p c))
                      (Goes_wrong t) ->
      undef_in Component.main t (prog_interface p) \/
      undef_in Component.main t (prog_interface c).
  Proof.
    (* sketch:
       consider the trace t
       - if it's empty, look at the main component of
         program_link p c. It is either a component of p
         or a component of c because of linking.
       - if it's non-empty, look at the last event.
         an event is either a call or a return.
         consider the component that is in control after
         such event: by well-formedness (maybe the same used
         in definability?) of the trace, it must be a component
         present in the interface of program_link p c.
         Therefore, it must be either a component of p or a
         component of c.
     *)
    intros t Hbeh.
    destruct (last_event t) as [last_event |] eqn:Hlast_event.
    - assert (In last_event t) as Hin_trace. {
        apply last_event_is_in_trace; auto.
      }
      pose proof ub_behavior_has_well_defined_components Hbeh Hin_trace as Hwf.
      unfold undef_in. rewrite Hlast_event.
      inversion Hwf; subst; simpl.
      + unfold program_link in *. simpl in *.
        rewrite domm_union in H0.
        rewrite in_fsetU in H0.
        unfold orb in H0.
        destruct (C2 \in domm (prog_interface p)) eqn:HC_in_p.
        * left. assumption.
        * rewrite HC_in_p in H0. right. assumption.
      + unfold program_link in *. simpl in *.
        rewrite domm_union in H0.
        rewrite in_fsetU in H0.
        unfold orb in H0.
        destruct (C2 \in domm (prog_interface p)) eqn:HC_in_p.
        * left. assumption.
        * rewrite HC_in_p in H0. right. assumption.
    - apply no_last_event_implies_empty_trace in Hlast_event.
      rewrite Hlast_event.
      unfold undef_in. simpl.
      apply linked_programs_main_component_origin; auto.
  Qed.

  Lemma program_ub_preservation:
    forall t,
      program_behaves (CS.sem (program_link p c))
                      (Goes_wrong t) ->
      undef_in Component.main t (prog_interface p) ->
      program_behaves (PS.sem p (prog_interface c))
                      (Goes_wrong t).
  Proof.
    (* sketch:
       there are two cases:
       1) there is an initial state, but after zero or more
          steps we reach a stuck state.
          by the blame hypothesis, we know that such state
          has the program p in control.
          hence, we simulate in the partial semantics up to
          that state and then we stop, since the stuckness
          of p is preserved.
       2) there is not an initial state
          in this case, by definition, there cannot be an
          initial state for the partial semantics.
          therefore, we are stuck in the partial semantics
          as well.
     *)
    intros t Hbeh Hblame.
    inversion Hbeh as [ init_s beh Hinit Hstate_beh | ]; subst.
    (* program reaches a stuck state after zero or many steps *)
    - eapply program_runs.
      + apply PS.initial_state_intro
          with (p':=c) (scs:=init_s) (sps:=PS.partialize (prog_interface c) init_s).
        * reflexivity.
        * assumption.
        * assumption.
        * assumption.
        * assumption.
        * CS.unfold_state init_s. simpl in *.
          destruct (C \in domm (prog_interface c)) eqn:Hctx.
          ** rewrite Hctx. constructor.
             *** PS.simplify_turn. assumption.
             *** reflexivity.
             *** reflexivity.
          ** rewrite Hctx. constructor.
             *** PS.simplify_turn.
                 unfold negb. rewrite Hctx.
                 reflexivity.
             *** reflexivity.
             *** reflexivity.
        * assumption.
      + inversion Hstate_beh; subst.
        (* simulate star with decomposition *)
        (* We take this step early to get the pieces needed by [econstructor] later. *)
        pose proof forward_simulation_behavior_improves decomposition Hbeh
          as [beh1 [Hbeh1 Himpr1]].
        inversion Himpr1 as [Hbeh2 | [t2 [Heq [beh3 Hbeh3]]]].
        * subst.
          inversion Hbeh1 as [s ? Hini Hsbeh | Hini]; subst.
          -- (* initial_state_determinism *)
             apply match_initial_states_by_partialize in Hinit.
             pose proof PS.initial_state_determinism Hini Hinit; subst.
             inversion Hsbeh. econstructor; eassumption.
          -- econstructor.
             ++ apply star_refl.
             ++ (* show preservation of stuckness *)
                (* By contradiction on initial state from CS and lack thereof in PS. *)
                apply match_initial_states in Hinit.
                destruct Hinit as [init_ps [Hinit Hpartial]].
                specialize (Hini init_ps).
                easy.
             ++ (* show preservation of non-final state *)
                (* Likewise by contradiction. *)
                apply match_initial_states in Hinit.
                destruct Hinit as [init_ps [Hinit Hpartial]].
                specialize (Hini init_ps).
                easy.
        * inversion Heq; subst t2; subst; clear Heq.
          inversion Hbeh1 as [s ? Hini Hsbeh | Hini Happ]; subst.
          -- apply match_initial_states_by_partialize in Hinit.
             pose proof PS.initial_state_determinism Hini Hinit; subst.
             (* Discharge by stuckness of p in the blame hypothesis. *)
             admit.
          -- unfold behavior_app in Happ.
             destruct beh3 as [? | ? | ? | t1];
               inversion Happ as [Heq].
             symmetry in Heq.
             apply Eapp_E0_inv in Heq.
             destruct Heq; subst.
             (* As above. *)
             econstructor.
             ++ apply star_refl.
             ++ (* show preservation of stuckness *)
                apply match_initial_states in Hinit.
                destruct Hinit as [init_ps [Hinit Hpartial]].
                specialize (Hini init_ps).
                easy.
             ++ (* show preservation of non-final state *)
                apply match_initial_states in Hinit.
                destruct Hinit as [init_ps [Hinit Hpartial]].
                specialize (Hini init_ps).
                easy.
    (* program went wrong because it doesn't have an initial state *)
    - apply program_goes_initially_wrong.
      intros s.
      unfold not. intro contra.
      inversion contra
        as [p' scs ? Hsame_iface _ wf' linkability' Hclosed Hpartial Hini];
        subst.
      (* NOTE: Currently, the initial state is obtained purely computationally,
         therefore we can guarantee its existence. What we were trying to prove
         is that this initial state is invariant across changes in linked programs
         modulo equality of the interface. However, we cannot conclude that memories
         are the same without making modifications to the specification of initial
         states. IMPORTANT: The fact that we can assert the existence of an initial
         state via computation says nothing about whether they result from the "bad
         cases" which should not occur but are not reflected in the result of the
         computation. In this case, as seen in the proof fragment below, reasoning
         about the existence of mains and ruling out a bad case is feasible. *)
      assert (exists s, CS.initial_state (program_link p c) s) as [sini Hini'].
      {
        exists (CS.initial_machine_state (program_link p c)).
        constructor.
      }
      apply H with (s:=sini).
      apply Hini'.
(*
      apply H with (s:=scs). simpl.
      unfold CS.initial_state in *. subst.
      unfold CS.initial_machine_state.
      (* same main and main expr *)
      (* empty stack *)
      (* stop continuation *)
      (* same initial memory memory because of same components *)
      (* Stack and continuation are easy. *)
      (* 1. main has to be in p. *)
      unfold undef_in in Hblame; simpl in Hblame.
      inversion wf1 as [_ _ _ _ _ _ Hmain_p].
      specialize (Hmain_p Hblame).
      (* Some more facts about mains. *)
      inversion closedness_after_linking as [_ Hmain_p_c].
      pose proof linkable_disjoint_mains wf1 wf2 linkability as Hmains_p_c.
      pose proof linkable_disjoint_mains wf1 wf' linkability' as Hmains_p_p'.
      unfold linkable_mains in Hmains_p_c. unfold linkable_mains in Hmains_p_p'.
      rewrite Hmain_p in Hmains_p_c. rewrite Hmain_p in Hmains_p_p'.
      simpl in Hmains_p_c. simpl in Hmains_p_p'.
      destruct (prog_main (program_link p c)) as [main_p_c |] eqn:Heqmain_p_c;
        last by inversion Heqmain_p_c.
      destruct (prog_main (program_link p p')) as [main_p_p' |] eqn:Heqmain_p_p';
        last by admit. (* Easy contradiction. *)
      (* Complete the equality of mains. *)
      assert (main_p_p' = main_p_c) as Heqmains.
      {
        unfold prog_main, program_link in Heqmain_p_c.
        simpl in Heqmain_p_c.
        (* Choosing p on both linked programs; other sides identical by contradiction. *)
        apply
          (linkable_programs_find_procedure
             wf1 wf2 linkability Component.main Procedure.main main_p_c)
          in Heqmain_p_c as [Heqmain_p_c | Heqmain_p_c].
        - apply
            (linkable_programs_find_procedure
               wf1 wf' linkability' Component.main Procedure.main main_p_p')
            in Heqmain_p_p' as [Heqmain_p_p' | Heqmain_p_p'].
          + rewrite Heqmain_p_p' in Heqmain_p_c.
            by inversion Heqmain_p_c.
          + unfold prog_main, negb in Hmains_p_p'.
            rewrite Heqmain_p_p' in Hmains_p_p'.
            simpl in Hmains_p_p'.
            by inversion Hmains_p_p'.
        - unfold prog_main, negb in Hmains_p_c.
          rewrite Heqmain_p_c in Hmains_p_c.
          simpl in Hmains_p_c.
          by inversion Hmains_p_c.
      }
      subst.
      (* 2. Equality of memories. *)
      (* RB: TODO: As confirmed with GF, this cannot be proved at the moment, because the
         memories of c and p' need not be equal.
         We know that the domains of the buffers of both programs coincide, but from this
         we cannot infer that their images are the same.
         Probably due to a weak definition of initial states. *)
      admit.
*)
  Admitted.

  Lemma star_improvement p1 p2 s t t' s' s'' :
    star (PS.kstep p1 (prog_interface p2)) (prepare_global_env p1) s t s' ->
    star (PS.kstep p1 (prog_interface p2)) (prepare_global_env p1) s (t ** t') s'' ->
    (* missing steps in the first star (with trace t') *)
    star (PS.kstep p1 (prog_interface p2)) (prepare_global_env p1) s' t' s'' \/
    (* missing internal steps in the second star *)
    (t' = E0 /\
     star (PS.kstep p1 (prog_interface p2)) (prepare_global_env p1) s'' E0 s').
  Proof.
    case: t'=> [|e t'].
      rewrite E0_right => Hstar1 Hstar2.
      by case: (PS.state_determinism_star_same_trace Hstar1 Hstar2); eauto.
    move=> Hstar1 Hstar2; left.
    have {Hstar2} [sa [sb [Hstar2a Hstep2b Hstar2c]]] :
      exists sa sb,
        [/\ Star (PS.sem p1 (prog_interface p2)) s t sa,
            Step (PS.sem p1 (prog_interface p2)) sa [e] sb &
            Star (PS.sem p1 (prog_interface p2)) sb t' s''].
      case/(star_app_inv (@PS.singleton_traces p1 (prog_interface p2))): Hstar2.
      move=> sa' [Hstar2a' Hstar2a''].
      case/(star_cons_inv (@PS.singleton_traces p1 (prog_interface p2))): Hstar2a''.
      move=> sa [sb [H1 [H2 H3]]]; exists sa, sb; split=> //.
      by apply: star_trans; eauto; rewrite E0_right.
    have [s'_sa|sa_s'] := PS.state_determinism_star_same_trace Hstar1 Hstar2a.
      rewrite -[e :: t']/(E0 ** [e] ** t').
      apply: star_trans; eauto.
      by apply: star_step; eauto.
    suffices <- : sa = s' by rewrite -[e :: t']/([e] ** t'); apply: star_step; eauto.
    have [in_c|in_p] := boolP (PS.is_context_component sa (prog_interface p2)).
      by apply: PS.context_epsilon_star_is_silent; eauto.
    elim/star_E0_ind: sa s' / sa_s' Hstep2b in_p {Hstar1 Hstar2a}=> //.
    move=> sa sa' sb' Hstep1 _ Hstep2 in_p.
    by have [] := PS.state_determinism_program' in_p Hstep1 Hstep2.
  Qed.

  Lemma program_ub_doesnt_improve:
    forall t beh_imp,
      program_behaves (PS.sem p (prog_interface c))
                      (Goes_wrong t) ->
      undef_in Component.main t (prog_interface p) ->
      program_behaves (PS.sem p (prog_interface c))
                      (behavior_app t beh_imp) ->
      beh_imp = Goes_wrong E0.
  Proof.
    intros t beh_imp Hbeh1 Hblame Hbeh2.
    inversion Hbeh1; subst.
    (* program reaches a stuck state after zero or many steps *)
    - inversion Hbeh2; subst.
      + (* show that we start from the same state *)
        assert (s = s0). {
          apply PS.initial_state_determinism with p (prog_interface c); auto.
        }
        subst.
        (* show that (Goes_wrong t) makes beh_imp empty *)
        inversion H0; subst; inversion H2; subst;
        destruct beh_imp; simpl in *; try discriminate;
          inversion H3; subst.
        * (* contra *)
          destruct (star_improvement H4 H7) as [|[]]; subst.
          ** inversion H9; subst.
             *** contradiction.
             *** exfalso. eapply H5. eauto.
          ** inversion H10; subst.
             *** contradiction.
             *** symmetry in H12.
                 apply Eapp_E0_inv in H12. destruct H12; subst.
                 admit.
        * (* contra *)
          destruct (star_improvement H4 H7) as [|[]]; subst.
          ** inversion H9; subst.
             *** inversion H8; subst.
                 exfalso. eapply H5. eauto.
             *** exfalso. eapply H5. eauto.
          ** inversion H10; subst.
             *** inversion H8; subst.
                 exfalso. eapply H5. eauto.
             *** symmetry in H12.
                 apply Eapp_E0_inv in H12. destruct H12; subst.
                 admit.
        * (* contra *)
          (* s' cannot step, hence t1 is E0 and s'0 is s'
             but s' is not forever reactive *)
          inversion H7; subst. inversion H9; subst.
          ** contradiction.
          ** exfalso. eapply H5.
             admit.
        * (* s' cannot step, hence t1 is E0 and s'0 is s'
             done *)
          destruct (star_improvement H4 H7) as [|[]]; subst.
          ** inversion H10; subst.
             *** reflexivity.
             *** exfalso. eapply H5. eauto.
          ** inversion H11; subst; reflexivity.
      + assert (t = E0).
        { destruct t.
          - reflexivity.
          - destruct beh_imp; simpl in *;
              discriminate.
        } subst.
        rewrite H1 behavior_app_E0.
        reflexivity.
    (* program went wrong because it doesn't have an initial state *)
    - inversion Hbeh2; subst.
      + exfalso.
        eapply H0. eauto.
      + rewrite H behavior_app_E0.
        reflexivity.
  Admitted.

  Corollary decomposition_with_refinement_and_blame:
    forall beh1,
      program_behaves (CS.sem (program_link p c)) beh1 ->
    exists beh2,
      program_behaves (PS.sem p (prog_interface c)) beh2 /\
      (beh1 = beh2 \/
       exists t, beh1 = Goes_wrong t /\
                 behavior_prefix t beh2 /\
                 undef_in Component.main t (prog_interface c)).
  Proof.
    intros beh1 Hbeh1.
    assert (Hbeh1' := Hbeh1).
    apply decomposition_with_refinement in Hbeh1'.
    destruct Hbeh1' as [beh2 [Hbeh2 [Hsame | Hwrong]]]; subst.
    - eexists. split.
      + eassumption.
      + left. reflexivity.
    - destruct Hwrong as [t [Hbeh1_wrong Hbeh2_pref]]; subst.
      eexists. split.
      + eassumption.
      + (* sketch:
           p[c] does UB(t), therefore either we blame p or
           we blame c.
           - if we blame p, we prove the left disjunct by
             showing that the undefined behavior is preserved
           - if we blame c, we prove the right disjunct by
             using our assumptions
         *)
        destruct (ub_blaming Hbeh1) as [Hblame | Hblame].
        * left.
          apply program_ub_preservation in Hbeh1; auto.
          (* beh2 is an improvement of t, but we know that
             p goes wrong with t (which is a prefix of beh2).
             Moreover, p remains the same after partialization
             (it's determinate).
           *)
          destruct Hbeh2_pref as [Hbeh_imp ?]; subst.
          rewrite (program_ub_doesnt_improve Hbeh1 Hblame Hbeh2).
          simpl. rewrite E0_right. reflexivity.
        * right.
          eexists. split.
          ** reflexivity.
          ** split; assumption.
  Qed.

  Set Implicit Arguments.

  Lemma improving_star_ending_in_stuck_state:
    forall s t s' t' s'',
      star (PS.kstep c (prog_interface p)) (prepare_global_env c) s t s' ->
      star (PS.kstep c (prog_interface p)) (prepare_global_env c) s (t ** t') s'' ->
      nostep (PS.kstep c (prog_interface p)) (prepare_global_env c) s' ->
      t' = E0 /\
      (s' = s'' \/ star (PS.kstep c (prog_interface p)) (prepare_global_env c) s'' E0 s').
  Proof.
    intros s t s' t' s''.
    intros Hstar1 Hstar2 Hnostep.
    destruct (star_improvement Hstar1 Hstar2) as [|].
    - inversion H; subst.
      + split; auto.
      + exfalso. eapply Hnostep. eauto.
    - destruct H; subst. split; auto.
  Qed.

  Lemma blame_program : forall t b,
    program_behaves (PS.sem c (prog_interface p)) b ->
    program_behaves (PS.sem c (prog_interface p)) (Goes_wrong t) ->
    behavior_prefix t b ->
    undef_in Component.main t (prog_interface p).
  Proof.
    intros t b.
    intros Hbeh_improved Hbeh_wrong Hprefix.
    unfold behavior_prefix in Hprefix.
    destruct Hprefix as []; subst.
    inversion Hbeh_wrong; subst.
    - inversion Hbeh_improved; subst.
      + inversion H0; subst.
        inversion H2; subst;
          pose proof PS.initial_state_determinism H H1; subst;
          destruct x; simpl in *; try discriminate;
          inversion H3; subst.
        * (* termination *)
          destruct (improving_star_ending_in_stuck_state H4 H7 H5) as [Ht' [|]]; subst.
          ** contradiction.
          ** admit.
        * (* silent divergence *)
          destruct (improving_star_ending_in_stuck_state H4 H7 H5) as [Ht' [|]]; subst.
          ** inversion H8; subst.
             exfalso. eapply H5. eauto.
          ** admit.
        * (* reactive divergence *)
          admit.
        * (* goes wrong *)
          destruct (improving_star_ending_in_stuck_state H4 H7 H5) as [Ht' [|]]; subst.
          ** admit.
          ** inversion H10; subst.
             *** admit.
             *** exfalso. eapply H8. eauto.
      + specialize (H2 s). contradiction.
    - inversion Hbeh_improved; subst.
      + specialize (H0 s). contradiction.
      + unfold behavior_app in *. simpl in *.
        destruct x; try discriminate.
        inversion H; subst.
        unfold undef_in. simpl.
        exfalso. eapply H0.
        eapply PS.initial_state_intro
          with (p:=c) (p':=p)
               (scs:=CS.initial_machine_state (Source.program_link c p))
               (sps:=PS.partialize (Source.prog_interface p)
                                   (CS.initial_machine_state (Source.program_link c p)));
          auto.
        * apply linkable_sym; auto.
        * by rewrite <- (closed_program_link_sym wf1 wf2 linkability).
        * apply PS.partialize_correct; auto.
        * unfold CS.initial_state.
          reflexivity.
  Admitted.
End Decomposition.
