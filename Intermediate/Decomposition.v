Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.
Require Import Intermediate.PS.

Import Intermediate.

Section Decomposition.
  Variables p c: program.

  Let mainC := fst (prog_main p).
  Let mainP := snd (prog_main p).
  Let split := map fst (NMap.elements (prog_interface p)).
  Let G := init_genv (program_link p c (prog_main p)).
  Let G' := init_genv (PS.partial_program p (prog_interface c)).

  Inductive related_states : CS.state -> PS.state -> Prop :=
  | ProgramControl:
      forall gps pgps mem pmem regs pc,
        PS.is_program_component G (Pointer.component pc) ->
        pgps = PS.to_partial_stack gps split ->
        PS.maps_match_on split mem pmem ->
        related_states (gps, mem, regs, pc)
                       (PS.PC (pgps, pmem, regs, pc))
  | ContextControl_Normal:
      forall gps pgps mem pmem regs pc,
        PS.is_context_component G (Pointer.component pc) ->
        pgps = PS.to_partial_stack gps split ->
        PS.maps_match_on split mem pmem ->
        related_states (gps, mem, regs, pc)
                       (PS.CC (pgps, pmem, Pointer.component pc) PS.Normal)
  | ContextControl_WentWrong:
      forall gps pgps mem pmem regs pc,
        PS.is_context_component G (Pointer.component pc) ->
        pgps = PS.to_partial_stack gps split ->
        PS.maps_match_on split mem pmem ->
        (forall s' t, ~ CS.step G (gps,mem,regs,pc) t s') ->
        ~ (forall r, CS.final_state G (gps,mem,regs,pc) r) ->
        related_states (gps, mem, regs, pc)
                       (PS.CC (pgps, pmem, Pointer.component pc) PS.WentWrong).

  Lemma initial_states_match:
    forall s1,
      CS.initial_state G mainC mainP s1 ->
    exists s2,
      PS.initial_state G' mainC mainP s2 /\ related_states s1 s2.
  Proof.
    intros s1 Hs1_init.
    CS.unfold_state.
    destruct Hs1_init as [Hempty_stack [Hpc_comp [Hpc_block Hpc_offset]]].
    destruct (NMapExtra.F.In_dec (genv_entrypoints G) mainC) as [Hprg|Hctx].
    - exists (PS.PC (PS.to_partial_stack s split, mem, regs, pc)).
      split.
      + unfold PS.initial_state.
        subst. repeat split; eauto.
        unfold G'.
        (* TODO prove linking doesn't create problems *)
        admit.
      + apply ProgramControl; auto.
        * unfold PS.is_program_component.
          subst mainC. rewrite Hpc_comp.
          auto.
        * apply PS.maps_match_on_reflexive.
    - exists (PS.CC (PS.to_partial_stack s split, mem, Pointer.component pc)
               PS.Normal).
      split.
      + unfold PS.initial_state.
        subst. repeat split. auto.
      + apply ContextControl_Normal; auto.
        * unfold PS.is_context_component.
          unfold PS.is_program_component.
          subst mainC. rewrite Hpc_comp.
          auto.
        * apply PS.maps_match_on_reflexive.
  Admitted.

  Lemma final_states_match:
    forall s1 s2 r,
      related_states s1 s2 ->
      CS.final_state G s1 r -> PS.final_state G' s2 r.
  Proof.
    intros s1 s2 r Hs1s2_rel Hs1_final.
    CS.unfold_state.
    destruct Hs1_final as [procs [proc [Hprocs [Hproc Hinstr]]]].
    unfold PS.final_state.
    inversion Hs1s2_rel; subst.
    - unfold executing. eexists. eexists. eauto.
      repeat split; eauto.
      + (* TODO prove linking doesn't create problems *)
        admit.
    - reflexivity.
    - admit.
  Admitted.

  Lemma lockstep_simulation:
    forall s1 t s1',
      CS.step G s1 t s1' ->
    forall s2,
      related_states s1 s2 ->
    exists s2',
      PS.step G' s2 t s2' /\ related_states s1' s2'.
  Proof.
    intros s1 t s1' Hstep s2 Hs1s2_rel.
    inversion Hs1s2_rel; subst;
      inversion Hstep; subst.
    (* the program has control and doesn't produce an event *)
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.

    (* the program has control and produces an event *)
    - admit.
    - admit.

    (* the context has control and doesn't produce an event *)
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.

    (* the context has control and produces an event *)
    - admit.
    - admit.
  Admitted.

  Theorem PS_simulates_CS:
    forward_simulation (CS.sem (program_link p c (prog_main p)))
                       (PS.sem p (prog_interface c)).
  Proof.
    apply forward_simulation_step with related_states.
    - apply initial_states_match.
    - apply final_states_match.
    - apply lockstep_simulation.
  Qed.

  Corollary PS_improves_CS_behavior:
    forall beh1,
      program_behaves (CS.sem (program_link p c (prog_main p))) beh1 ->
    exists beh2,
      program_behaves (PS.sem p (prog_interface c)) beh2 /\ behavior_improves beh1 beh2.
  Proof.
    intros.
    eapply forward_simulation_behavior_improves; eauto.
    apply PS_simulates_CS.
  Qed.

  Corollary PS_behaves_as_CS:
    forall beh,
      program_behaves (CS.sem (program_link p c (prog_main p))) beh ->
      program_behaves (PS.sem p (prog_interface c)) beh.
  Proof.
  Admitted.
End Decomposition.