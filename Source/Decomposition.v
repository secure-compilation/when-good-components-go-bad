Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Blame.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import Common.Traces.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Source.PS.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

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
      exists (PS.partialize (prog_interface c) [CState C, s, mem, k, e, arg]);
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
        by rewrite Htarget in H6.
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
        rewrite Htarget in H6. discriminate.
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

  (* This follows easily from previous lemmas by a right-side induction on Star. *)
  Lemma initial_star_has_well_defined_components :
    forall sini t sfin,
      initial_state (CS.sem (program_link p c)) sini ->
      Star (CS.sem (program_link p c)) sini t sfin ->
      well_defined_components_trace (unionm (prog_interface p) (prog_interface c)) t.
  Proof.
    move=> sini t sfin Hinitial Hstar e /In_in in_t.
    move: (cprog_main_existence closedness_after_linking).
    case e_main: (prog_main _)=> [mainP|] //= _.
    have := linking_well_formedness wf1 wf2 linkability.
    move/(CS.trace_wf Hstar Hinitial e_main)=> trace_wf.
    have := cprog_closed_interface closedness_after_linking.
    move/(well_formed_trace_int trace_wf)/seq.allP/(_ _ in_t).
    rewrite /declared_event_comps.
    by case: e {in_t}=> /= [????|???] /andP [??]; constructor.
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

  Lemma ub_blaming t :
    program_behaves (CS.sem (program_link p c)) (Goes_wrong t) ->
    undef_in t (prog_interface p) \/
    undef_in t (prog_interface c).
  Proof.
    move=> Hbeh; rewrite /undef_in /last_comp.
    apply/fsetUP; rewrite -domm_union /last_comp.
    have wf12 := linking_well_formedness wf1 wf2 linkability.
    rewrite -[unionm _ _]/(prog_interface (program_link p c)).
    move: (seq.mem_last Component.main (seq.map next_comp_of_event t)).
    rewrite seq.inE=> /orP [/eqP ->|].
      case: closedness_after_linking; rewrite wfprog_defined_procedures //.
      by rewrite /prog_main /find_procedure mem_domm; case: getm.
    case/seq.mapP=> e /In_in e_in_t ->.
    by case: (ub_behavior_has_well_defined_components Hbeh e_in_t).
  Qed.

  Lemma program_ub_preservation:
    forall t,
      program_behaves (CS.sem (program_link p c))
                      (Goes_wrong t) ->
      undef_in t (prog_interface p) ->
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
          with (p':=c) (scs:=init_s) (sps:=PS.partialize (prog_interface c) init_s)=> //.
        CS.unfold_state init_s. simpl in *.
        have [Hctx|Hctx] := boolP (C \in domm (prog_interface c)); by constructor.
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

  Lemma program_ub_doesnt_improve t beh_imp :
    program_behaves (PS.sem p (prog_interface c)) (Goes_wrong t) ->
    undef_in t (prog_interface p) ->
    program_behaves (PS.sem p (prog_interface c)) (behavior_app t beh_imp) ->
    beh_imp = Goes_wrong E0.
  Proof.
    move e_t: (Goes_wrong t)=> beh Hbeh.
    case: beh / Hbeh e_t; last first.
      (* program went wrong because it doesn't have an initial state *)
      move=> not_init [->] _; rewrite behavior_app_E0.
      by case: beh_imp / => // ? ? /not_init.
    (* program reaches a stuck state after zero or many steps *)
    move=> s_i beh Hinitial Hbeh.
    case: beh / Hbeh t=> // t s_f Hstar Hstuck Hnot_final _ [->] Hin_p.
    move e_beh: (behavior_app t beh_imp)=> beh Hbeh.
    case: beh / Hbeh e_beh; last by move=> /(_ _ Hinitial).
    move=> s_i' beh Hinitial'; have {s_i' Hinitial'} -> : s_i' = s_i.
      exact: PS.initial_state_determinism Hinitial' Hinitial.
    have [|/empty_behaviorPn beh_n0] := boolP (empty_behavior beh_imp).
      case: beh_imp=> _ //= /eqP ->; rewrite E0_right=> Hbeh e_beh;
      case: beh / Hbeh t e_beh Hstar Hin_p;
      move=> // t s_f' Hstar' Hfinal _ [->] Hstar Hin_p.
        have [ff|ff] := PS.state_determinism_star_same_trace Hstar Hstar'.
          case: ff Hnot_final Hfinal Hstuck=> [? Hnot_final /Hnot_final //|].
          by move=> ?????? Hstep _ _ _ _ /(_ _ _ Hstep).
        have {Hin_p} Hin_p : PS.is_program_component s_f' (prog_interface c).
          case: linkability=> _ dis.
          by rewrite -(PS.undef_in_program dis Hinitial Hstar').
        elim/star_E0_ind: s_f' s_f / ff Hnot_final Hfinal Hin_p {Hstuck Hstar Hstar'}.
          by move=> ? Hnot_final /Hnot_final.
        move=> s_f' s s_f Hstep _ _ Hfinal Hin_p.
        by have := PS.final_state_stuck Hfinal Hin_p Hstep.
      have [ff|ff] := PS.state_determinism_star_same_trace Hstar Hstar'.
        suffices [s contra] : exists s, Step (PS.sem p (prog_interface c)) s_f E0 s.
          by case/Hstuck: contra.
        by elim/star_E0_ind: ff Hfinal=> [? []|]; eauto.
      have {Hin_p} Hin_p : PS.is_program_component s_f' (prog_interface c).
        case: linkability=> _ dis.
        by rewrite -(PS.undef_in_program dis Hinitial Hstar').
      suffices [s contra] : exists s, Step (PS.sem p (prog_interface c)) s_f E0 s.
        by case/Hstuck: contra.
      elim/star_E0_ind: s_f' s_f / ff Hfinal Hin_p {Hstuck Hnot_final Hstar Hstar'}.
        by move=> s []; eauto.
      move=> s_a s_b s_c Hstep IH Hfinal Hin_p; apply: IH=> //.
        case: s_a / Hfinal Hstep Hin_p=> s_a s_b' /= Hstep' Hfinal Hstep Hin_p.
        by rewrite (PS.state_determinism_program Hin_p Hstep Hstep').
      rewrite /PS.is_program_component /PS.is_context_component /turn_of /=.
      by rewrite (PS.kstep_component Hstep).
    case: beh_n0=> {beh_imp} e [beh_imp ->].
    rewrite -behavior_app_assoc => Hbeh e_beh.
    move: Hbeh; rewrite -{}e_beh {beh}.
    case/(@state_behaves_app_inv _ (@PS.singleton_traces p (prog_interface c))).
    move=> s3 [/(star_middle1_inv (@PS.singleton_traces p (prog_interface c)))].
    case=> s1 [s2 [Hstar1 [Hstep2 Hstar3]]].
    have {Hstar} [Hstar|Hstar] := PS.state_determinism_star_same_trace Hstar Hstar1.
      suffices [s [t' contra]] : exists s t', Step (PS.sem p (prog_interface c)) s_f t' s.
        by case/Hstuck: contra.
      by elim/star_E0_ind: s_f s1 / Hstar Hstep2 {Hstuck Hnot_final Hstar1}; eauto.
    have {Hin_p} Hin_p : PS.is_program_component s1 (prog_interface c).
      case: linkability=> _ dis.
      by rewrite -(PS.undef_in_program dis Hinitial Hstar1).
    elim/star_E0_ind: s1 s_f / Hstar Hstuck Hstep2 Hin_p {Hnot_final Hstar1}.
      by move=> s_f Hstuck /Hstuck.
    move=> s1 s1a s1b Hstep1 _ _ Hstep2 Hin_p.
    by have [] := PS.state_determinism_program' Hin_p Hstep1 Hstep2.
  Qed.

  Corollary decomposition_with_refinement_and_blame:
    forall beh1,
      program_behaves (CS.sem (program_link p c)) beh1 ->
    exists beh2,
      program_behaves (PS.sem p (prog_interface c)) beh2 /\
      (beh1 = beh2 \/
       exists t, beh1 = Goes_wrong t /\
                 behavior_prefix t beh2 /\
                 undef_in t (prog_interface c)).
  Proof.
    intros beh1 Hbeh1.
    assert (Hbeh1' := Hbeh1).
    apply decomposition_with_refinement in Hbeh1'.
    destruct Hbeh1' as [beh2 [Hbeh2 [Hsame | Hwrong]]]; subst.
    - eexists. split.
      + eassumption.
      + left. reflexivity.
    - destruct Hwrong as [t [Hbeh1_wrong Hbeh2_pref]]; subst.
      eexists. split; first eauto.
      (* sketch:
         p[c] does UB(t), therefore either we blame p or
         we blame c.
         - if we blame p, we prove the left disjunct by
           showing that the undefined behavior is preserved
         - if we blame c, we prove the right disjunct by
           using our assumptions
       *)
      destruct (ub_blaming Hbeh1) as [Hblame | Hblame]; last eauto.
      left.
      apply program_ub_preservation in Hbeh1; auto.
      (* beh2 is an improvement of t, but we know that
         p goes wrong with t (which is a prefix of beh2).
         Moreover, p remains the same after partialization
         (it's determinate).
       *)
      destruct Hbeh2_pref as [Hbeh_imp ?]; subst.
      rewrite (program_ub_doesnt_improve Hbeh1 Hblame Hbeh2).
      by rewrite /= E0_right.
  Qed.

  Set Implicit Arguments.

  Lemma improving_star_ending_in_stuck_state:
    forall s t s' t' s'',
      star (PS.kstep c (prog_interface p)) (prepare_global_env c) s t s' ->
      star (PS.kstep c (prog_interface p)) (prepare_global_env c) s (t ** t') s'' ->
      nostep (PS.kstep c (prog_interface p)) (prepare_global_env c) s' ->
      t' = E0 /\ star (PS.kstep c (prog_interface p)) (prepare_global_env c) s'' E0 s'.
  Proof.
    intros s t s' t' s''.
    intros Hstar1 Hstar2 Hnostep.
    destruct (PS.star_prefix Hstar1 Hstar2) as [|].
    - inversion H; subst.
      + split; auto.
      + exfalso. eapply Hnostep. eauto.
    - destruct H; subst. split; auto.
  Qed.

  Lemma blame_program t b :
    program_behaves (PS.sem c (prog_interface p)) b ->
    program_behaves (PS.sem c (prog_interface p)) (Goes_wrong t) ->
    behavior_prefix t b ->
    undef_in t (prog_interface p).
  Proof.
  case: b / => //; last first.
    move: closedness_after_linking; rewrite link_sym // => H.
    by case: (PS.exists_initial_state (linkable_sym linkability) wf2 wf1 H)=> ? H' /(_ _ H').
  move e_beh': (Goes_wrong _) => beh' s0 beh Hinitial Hbeh Hbeh'.
  case: beh' / Hbeh' e_beh'; last by move=> /(_ _ Hinitial).
  move=> s0' beh' Hinitial'.
  rewrite -(PS.initial_state_determinism Hinitial Hinitial') {s0' Hinitial'}.
  move=> Hbeh'; case: beh' / Hbeh' t => //=.
  move=> t' s_f' Hstar' Hstuck' Hnot_final' _ [->].
  Admitted.

  Lemma blame_program' t b :
    program_behaves (PS.sem c (prog_interface p)) b ->
    program_behaves (PS.sem c (prog_interface p)) (Goes_wrong t) ->
    behavior_prefix t b ->
    undef_in t (prog_interface c).
  Proof.
  case: b / => //; last first.
    move: closedness_after_linking; rewrite link_sym // => H.
    by case: (PS.exists_initial_state (linkable_sym linkability) wf2 wf1 H)=> ? H' /(_ _ H').
  move e_beh': (Goes_wrong _) => beh' s0 beh Hinitial Hbeh Hbeh'.
  case: beh' / Hbeh' e_beh'; last by move=> /(_ _ Hinitial).
  move=> s0' beh' Hinitial'.
  rewrite -(PS.initial_state_determinism Hinitial Hinitial') {s0' Hinitial'}.
  move=> Hbeh'; case: beh' / Hbeh' t => //=.
  move=> t' s_f' Hstar' Hstuck' Hnot_final' _ [->].
  move/linkable_sym: linkability=> linkability'.
  rewrite (PS.undef_in_program linkability'.2 Hinitial Hstar').
  move=> _.
  apply/negP=> in_context; apply: Hnot_final'.
  constructor; by eauto.
  Qed.

  Lemma weird t : ~ program_behaves (PS.sem c (prog_interface p)) (Goes_wrong t).
  Proof.
  move=> Ht.
  have pre : behavior_prefix t (Goes_wrong t).
    by exists (Goes_wrong E0); rewrite /= E0_right.
  move: (blame_program Ht Ht pre) (blame_program' Ht Ht pre).
  rewrite /undef_in => H.
  by case: linkability=> _ /fdisjointP/(_ _ H)/negP.
  Qed.

End Decomposition.
