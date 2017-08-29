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
  Variable mainC: Component.id.
  Variable mainP: Procedure.id.

  (* p and c are valid programs *)
  Hypothesis pWF: well_formed_program p.
  Hypothesis cWF: well_formed_program c.

  (* linking p and c results in a valid closed program *)
  (* (we assume to have a valid main procedure from which to start execution) *)
  (* partializing still return a partial program *)
  Hypothesis pcWF:
    well_formed_program (program_link p c mainC mainP).
  Hypothesis pcClosed:
    closed_program (program_link p c mainC mainP).
  Hypothesis partialWF:
    well_formed_program (PS.partial_program p mainC mainP (prog_interface c)).

  Let split := map fst (NMap.elements (prog_interface p)).
  Let G := init_genv (program_link p c mainC mainP).
  Let G' := init_genv (PS.partial_program p mainC mainP (prog_interface c)).

  Lemma G_is_well_formed:
    well_formed_global_env G.
  Proof.
    apply (init_genv_preserves_well_formedness
             (program_link p c mainC mainP));
      auto.
  Qed.

  Lemma G'_is_well_formed:
    well_formed_global_env G'.
  Proof.
    apply (init_genv_preserves_well_formedness
             (PS.partial_program p mainC mainP (prog_interface c)));
      auto.
  Qed.

  Inductive related_states : CS.state -> PS.state -> Prop :=
  | ProgramControl:
      forall gps pgps mem pmem regs pc,
        PS.is_program_component G (Pointer.component pc) ->
        pgps = PS.to_partial_stack gps split ->
        NMap.In (Pointer.component pc) mem ->
        PS.maps_match_on split mem pmem ->
        related_states (gps, mem, regs, pc)
                       (PS.PC (pgps, pmem, regs, pc))
  | ContextControl_Normal:
      forall gps pgps mem pmem regs pc,
        PS.is_context_component G (Pointer.component pc) ->
        pgps = PS.to_partial_stack gps split ->
        NMap.In (Pointer.component pc) mem ->
        PS.maps_match_on split mem pmem ->
        related_states (gps, mem, regs, pc)
                       (PS.CC (pgps, pmem, Pointer.component pc) PS.Normal)
  | ContextControl_WentWrong:
      forall gps pgps mem pmem regs pc,
        PS.is_context_component G (Pointer.component pc) ->
        pgps = PS.to_partial_stack gps split ->
        NMap.In (Pointer.component pc) mem ->
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
    destruct Hs1_init as [Hempty_stack [[Hpc_comp [Hpc_block Hpc_offset]] Hmem]].
    destruct (NMapExtra.F.In_dec (genv_entrypoints G) mainC) as [Hprg|Hctx].
    - exists (PS.PC (PS.to_partial_stack s split, mem, regs, pc)).
      split.
      + unfold PS.initial_state.
        subst. repeat split; eauto.
        unfold G, G'.
        * admit. (* TODO prove that entrypoints are the same in both G and G' *)
        * admit. (* TODO prove that program components have a memory *)
      + apply ProgramControl; auto.
        * unfold PS.is_program_component.
          subst mainC. auto.
        * apply Hmem. rewrite Hpc_comp.
          apply wfgenv_entrypoints_soundness; auto.
          apply G_is_well_formed.
        * apply PS.maps_match_on_reflexive.
    - exists (PS.CC (PS.to_partial_stack s split, mem, Pointer.component pc) PS.Normal).
      split.
      + unfold PS.initial_state.
        subst. repeat split. auto.
        * admit. (* TODO prove that program components have a memory *)
      + apply ContextControl_Normal; auto.
        * unfold PS.is_context_component, PS.is_program_component.
          subst mainC. auto.
        * (* TODO prove that p's main component is in the interface *)
          admit.
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
      + unfold G, G'.
        (* TODO prove that if G has a procedure, then G' has it as well *)
        admit.
    - reflexivity.
    - exfalso.
      apply H9. intro. unfold CS.final_state.
      unfold executing. eexists. eexists. eauto.
  Admitted.

  Lemma split_agrees_with_global_env:
    forall C, PS.is_program_component G C -> In C split.
  Proof.
    intros C Hprog.
    unfold PS.is_program_component, split in *.

    assert (Hprogcomp := Hprog).
    apply (wfgenv_entrypoints_soundness G G_is_well_formed) in Hprog.
    unfold G in Hprog. unfold init_genv in Hprog.
    destruct (init_all (program_link p c mainC mainP)).
    simpl in Hprog. destruct p0. simpl in Hprog.
    apply NMapExtra.update_in_iff in Hprog.
    destruct Hprog.
    - assert (H' := H).
      apply NMapExtra.F.elements_in_iff in H'.
      destruct H' as [CI Hin].
      change C with (fst (C, CI)).
      apply (in_map fst (NMap.elements (prog_interface p))).
      (* TODO prove that InA => In *)
      admit.
    - admit. (* contradiction, the component belongs to the program *)
  Admitted.

  Lemma genv_extension_after_partialize_1:
    forall C CI,
      NMap.MapsTo C CI (genv_interface G') -> NMap.MapsTo C CI (genv_interface G).
  Proof.
  Admitted.

  Lemma genv_extension_after_partialize_2:
    forall C Cprocs,
      NMap.MapsTo C Cprocs (genv_procedures G') -> NMap.MapsTo C Cprocs (genv_procedures G).
  Proof.
  Admitted.

  Lemma genv_extension_after_partialize_3:
    forall C Centrypoints,
      NMap.MapsTo C Centrypoints (genv_entrypoints G') ->
      NMap.MapsTo C Centrypoints (genv_entrypoints G).
  Proof.
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
      inversion Hstep; subst;

    (* extract the current component's memory *)
    destruct H1 as [cmem Hcmem].

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
    - destruct (NMapExtra.F.In_dec (genv_entrypoints G) C') as [Htarget|Htarget].
      (* internal call *)
      + eexists. split.
        * eapply PS.Program_Internal_Call; eauto.
          ** admit.
          ** admit.
          ** unfold PS.is_program_component.
             (* TODO prove that partialize preserves entrypoints (genv_extension) *)
             admit.
          ** admit.
        * apply ProgramControl; auto.
          ** (* TODO rethink this part *)
             admit.
          ** admit.
      (* external call *)
      + eexists. split.
        * eapply PS.Program_External_Call; eauto.
          ** admit.
          ** admit.
          ** unfold PS.is_program_component.
             (* TODO prove that partialize preserves entrypoints (genv_extension) *)
             admit.
        * apply ContextControl_Normal.
          ** admit.
          ** admit.
          ** admit.
          ** auto.
    - destruct (NMapExtra.F.In_dec (genv_entrypoints G) (Pointer.component pc'))
                 as [Htarget|Htarget].
      (* internal return *)
      + eexists. split.
        * eapply PS.Program_Internal_Return; auto.
          ** admit.
          ** (* TODO rethink this part *)
            admit.
          ** unfold PS.is_program_component.
             (* TODO prove that partialize preserves entrypoints (genv_extension) *)
             admit.
        * apply ProgramControl; auto.
          admit.
      (* external return *)
      + eexists. split.
        * eapply PS.Program_External_Return; auto.
          ** admit.
          ** (* TODO partialize & context components *) admit.
          ** (* TOOD rethink this part *) admit.
        * apply ContextControl_Normal; auto.
          admit.

    (* the context has control and doesn't produce an event *)
    - eexists. split.
      + apply PS.Context_Epsilon.
      + assert (Hpc: Pointer.component pc = Pointer.component (Pointer.inc pc)). {
          destruct pc. destruct p0. reflexivity.
        } rewrite Hpc.
        apply ContextControl_Normal with (pc:=Pointer.inc pc).
        * rewrite <- Hpc. auto.
        * reflexivity.
        * rewrite Pointer.inc_preserves_component.
          eexists. eauto.
        * auto.
    - eexists. split.
      + apply PS.Context_Epsilon.
      + assert (Hpc: Pointer.component pc = Pointer.component (Pointer.inc pc)). {
          destruct pc. destruct p0. reflexivity.
        } rewrite Hpc.
        apply ContextControl_Normal with (pc:=Pointer.inc pc).
        * rewrite <- Hpc. auto.
        * reflexivity.
        * rewrite Pointer.inc_preserves_component.
          eexists. eauto.
        * auto.
    - eexists. split.
      + apply PS.Context_Epsilon.
      + assert (Hpc: Pointer.component pc = Pointer.component (Pointer.inc pc)). {
          destruct pc. destruct p0. reflexivity.
        } rewrite Hpc.
        apply ContextControl_Normal with (pc:=Pointer.inc pc).
        * rewrite <- Hpc. auto.
        * reflexivity.
        * rewrite Pointer.inc_preserves_component.
          eexists. eauto.
        * auto.
    - eexists. split.
      + apply PS.Context_Epsilon.
      + assert (Hpc: Pointer.component pc = Pointer.component (Pointer.inc pc)). {
          destruct pc. destruct p0. reflexivity.
        } rewrite Hpc.
        apply ContextControl_Normal with (pc:=Pointer.inc pc).
        * rewrite <- Hpc. auto.
        * reflexivity.
        * rewrite Pointer.inc_preserves_component.
          eexists. eauto.
        * auto.
    - eexists. split.
      + apply PS.Context_Epsilon.
      + assert (Hpc: Pointer.component pc = Pointer.component (Pointer.inc pc)). {
          destruct pc. destruct p0. reflexivity.
        } rewrite Hpc.
        apply ContextControl_Normal with (pc:=Pointer.inc pc).
        * rewrite <- Hpc. auto.
        * reflexivity.
        * rewrite Pointer.inc_preserves_component.
          eexists. eauto.
        * auto.
    - eexists. split.
      + apply PS.Context_Epsilon.
      + assert (Hpc: Pointer.component pc = Pointer.component (Pointer.inc pc)). {
          destruct pc. destruct p0. reflexivity.
        } rewrite Hpc.
        apply ContextControl_Normal with (pc:=Pointer.inc pc).
        * rewrite <- Hpc. auto.
        * reflexivity.
        * rewrite Pointer.inc_preserves_component.
          eexists. eauto.
        * auto.
    - eexists. split.
      + apply PS.Context_Epsilon.
      + assert (Hpc: Pointer.component pc = Pointer.component (Pointer.inc pc)). {
          destruct pc. destruct p0. reflexivity.
        } rewrite Hpc.
        apply ContextControl_Normal with (pc:=Pointer.inc pc).
        * rewrite <- Hpc. auto.
        * reflexivity.
        * rewrite Pointer.inc_preserves_component.
          admit.
        * (* TODO prove that Memory.store preserves maps_match_on *)
          admit.
    - eexists. split.
      + apply PS.Context_Epsilon.
      + (* TODO prove that when using find_label_in_component we remain in the
           same component *)
        admit.
    - eexists. split.
      + apply PS.Context_Epsilon.
      + rewrite <- H10. apply ContextControl_Normal; auto.
        * rewrite H10. auto.
        * rewrite H10. eexists. eauto.
    - eexists. split.
      + apply PS.Context_Epsilon.
      + (* TODO prove that when using find_label_in_procedure we remain in the
           same component *)
        admit.
    - eexists. split.
      + apply PS.Context_Epsilon.
      + assert (Hpc: Pointer.component pc = Pointer.component (Pointer.inc pc)). {
          destruct pc. destruct p0. reflexivity.
        } rewrite Hpc.
        apply ContextControl_Normal; auto.
        * rewrite <- Hpc. auto.
        * rewrite Pointer.inc_preserves_component.
          eexists. eauto.
    - eexists. split.
      + apply PS.Context_Epsilon.
      + assert (Hpc: Pointer.component pc = Pointer.component (Pointer.inc pc)). {
          destruct pc. destruct p0. reflexivity.
        } rewrite Hpc.
        apply ContextControl_Normal with (pc:=Pointer.inc pc).
        * rewrite <- Hpc. auto.
        * reflexivity.
        * (* TODO prove that Memory.alloc preserves maps_match_on *)
          admit.
        * admit. (* TODO investigate more here *)

    (* the context has control and produces an event *)
    - destruct (NMapExtra.F.In_dec (genv_entrypoints G) C') as [Htarget|Htarget].
      (* internal call *)
      + admit.
      (* external call *)
      + admit.
    - destruct (NMapExtra.F.In_dec (genv_entrypoints G) (Pointer.component pc))
        as [Htarget|Htarget].
      (* internal return *)
      + admit.
      (* external return *)
      + admit.

    (* the context goes wrong *)
    - exfalso. eapply H3. eauto.
    - exfalso. eapply H3. eauto.
    - exfalso. eapply H3. eauto.
    - exfalso. eapply H3. eauto.
    - exfalso. eapply H3. eauto.
    - exfalso. eapply H3. eauto.
    - exfalso. eapply H3. eauto.
    - exfalso. eapply H3. eauto.
    - exfalso. eapply H3. eauto.
    - exfalso. eapply H3. eauto.
    - exfalso. eapply H3. eauto.
    - exfalso. eapply H3. eauto.
    - exfalso. eapply H3. eauto.
    - exfalso. eapply H3. eauto.
  Admitted.

  Theorem PS_simulates_CS:
    forward_simulation (CS.sem (program_link p c mainC mainP))
                       (PS.sem p mainC mainP (prog_interface c)).
  Proof.
    apply forward_simulation_step with related_states.
    - apply initial_states_match.
    - apply final_states_match.
    - apply lockstep_simulation.
  Qed.

  Corollary PS_improves_CS_behavior:
    forall beh1,
      program_behaves (CS.sem (program_link p c mainC mainP)) beh1 ->
    exists beh2,
      program_behaves (PS.sem p mainC mainP (prog_interface c)) beh2 /\
      behavior_improves beh1 beh2.
  Proof.
    intros.
    eapply forward_simulation_behavior_improves; eauto.
    apply PS_simulates_CS.
  Qed.

  Corollary PS_behaves_as_CS:
    forall beh,
      program_behaves (CS.sem (program_link p c mainC mainP)) beh ->
      program_behaves (PS.sem p mainC mainP (prog_interface c)) beh.
  Proof.
  Admitted.
End Decomposition.