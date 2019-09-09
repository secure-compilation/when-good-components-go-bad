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
Require Import Old.Source.CS.
Require Import Old.Source.PS.

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

    - (* KS_Binop1 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - (* KS_Binop2 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - (* KS_BinopEval *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - (* KS_Seq1 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - (* KS_Seq2 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - (* KS_If1 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - (* KS_If2 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - (* KS_Arg *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - (* KS_LocalBuffer *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - (* KS_Alloc1 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - (* KS_AllocEval *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - (* KS_Deref1 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - (* KS_DerefEval *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - (* KS_Assign1 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - (* KS_Assign2 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - (* KS_AssignEval *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - (* KS_InitCall *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * econstructor; eauto.
      + econstructor; auto.

    - (* KS_InternalCall *)
      eexists. split.
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

    - (* KS_Binop1 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - (* KS_Binop2 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - (* KS_BinopEval *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - (* KS_Seq1 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - (* KS_Seq2 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - (* KS_If1 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - (* KS_If2 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - (* KS_Arg *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - (* KS_LocalBuffer *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - (* KS_Alloc1 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - (* KS_AllocEval *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
          ** PS.simplify_turn.
             match goal with (* TODO: clean up. *)
             | |- ?FMEM = ?FMEM' =>
               change FMEM with (to_partial_memory mem (domm (prog_interface c)));
               change FMEM' with (to_partial_memory mem' (domm (prog_interface c)))
             end.
             erewrite <- context_allocation_in_partialized_memory; eauto.
      + eapply PS.ContextControl; eauto.
        * PS.simplify_turn.
          match goal with (* TODO: clean up. *)
          | |- ?FMEM = ?FMEM' =>
            change FMEM with (to_partial_memory mem (domm (prog_interface c)));
            change FMEM' with (to_partial_memory mem' (domm (prog_interface c)))
          end.
          erewrite <- context_allocation_in_partialized_memory; eauto.

    - (* KS_Deref1 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - (* KS_DerefEval *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - (* KS_Assign1 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - (* KS_Assign2 *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
      + eapply PS.ContextControl; eauto.

    - (* KS_AssignEval *)
      eexists. split.
      + eapply PS.partial_step with (p':=c); eauto.
        * eapply PS.ContextControl; eauto.
          ** PS.simplify_turn.
             match goal with (* TODO: clean up. *)
             | |- ?FMEM = ?FMEM' =>
               change FMEM with (to_partial_memory mem (domm (prog_interface c)));
               change FMEM' with (to_partial_memory mem' (domm (prog_interface c)))
             end.
             erewrite <- context_store_in_partialized_memory; eauto.
      + eapply PS.ContextControl; eauto.
        * PS.simplify_turn.
          match goal with (* TODO: clean up. *)
          | |- ?FMEM = ?FMEM' =>
            change FMEM with (to_partial_memory mem (domm (prog_interface c)));
            change FMEM' with (to_partial_memory mem' (domm (prog_interface c)))
          end.
          erewrite <- context_store_in_partialized_memory; eauto.

    - (* KS_InitCall *)
      eexists. split.
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
End Decomposition.
