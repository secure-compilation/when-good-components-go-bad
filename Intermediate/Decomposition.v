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
Require Import S2I.Definitions.

Import Intermediate.

Ltac simplify_turn :=
  unfold S.PS.is_program_component, S.PS.is_context_component in *;
  unfold I.PS.is_program_component, I.PS.is_context_component in *;
  unfold turn_of, S.PS.state_turn, I.PS.state_turn in *;
  simpl in *;
  auto.

Section Decomposition.
  Variable prog: Intermediate.program.
  Variable ctx: Program.interface.

  (*
  Hypothesis input_program_closedness:
    Intermediate.closed_program prog.
   *)

  Hypothesis context_validity:
    forall C CI, PMap.MapsTo C CI ctx -> PMap.MapsTo C CI (Intermediate.prog_interface prog).

  Let G : Intermediate.GlobalEnv.global_env := Intermediate.GlobalEnv.init_genv prog.

  Lemma match_initial_states:
    forall ics,
      I.CS.initial_state prog ics ->
    exists ips,
      I.PS.initial_state prog ctx ips /\ I.PS.partial_state ctx ics ips.
  Proof.
    intros ics Hics_init.
    I.CS.unfold_state.
    (* case analysis on who has control, then build the partial state *)
    destruct (PMap.mem (Pointer.component pc) ctx) eqn:Htarget.
    (* context has control *)
    - exists (I.PS.CC (Pointer.component pc,
                  I.PS.to_partial_stack s (map fst (PMap.elements ctx)),
                  PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) Normal).
      split.
      + econstructor.
        * eapply I.PS.ContextControl_Normal; eauto.
          ** simplify_turn.
             apply PMapFacts.mem_in_iff. auto.
          ** apply PMapFacts.Equal_refl.
        * eauto.
      + eapply I.PS.ContextControl_Normal; eauto.
          ** simplify_turn.
             apply PMapFacts.mem_in_iff. auto.
          ** apply PMapFacts.Equal_refl.
    (* program has control *)
    - exists (I.PS.PC (I.PS.to_partial_stack s (map fst (PMap.elements ctx)),
                  PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem,
                  regs, pc)).
      split.
      + econstructor.
        * eapply I.PS.ProgramControl; auto.
          ** simplify_turn.
             apply PMapFacts.not_mem_in_iff. auto.
          ** apply PMapFacts.Equal_refl.
        * eauto.
      + eapply I.PS.ProgramControl; auto.
          ** simplify_turn.
             apply PMapFacts.not_mem_in_iff. auto.
          ** apply PMapFacts.Equal_refl.
  Qed.

  Lemma match_final_states:
    forall ics ips r,
      I.PS.partial_state ctx ics ips ->
      I.CS.final_state G ics r ->
      I.PS.final_state prog ctx ips r.
  Proof.
    intros ics ips r Hpartial Hics_final.
    I.CS.unfold_state.
    (* case analysis on who has control *)
    destruct (PMap.mem (Pointer.component pc) ctx) eqn:Htarget.
    (* context has control *)
    - inversion Hpartial; inversion H; subst.
      + simplify_turn.
        apply PMapFacts.mem_in_iff in Htarget.
        contradiction.
      + apply I.PS.final_state_context.
        simplify_turn.
    (* program has control *)
    - inversion Hpartial; inversion H; subst.
      + eapply I.PS.final_state_program.
        * simplify_turn.
        * eauto.
        * eauto.
      + apply PMapFacts.not_mem_in_iff in Htarget.
        contradiction.
  Qed.

  Lemma pc_inc_within_partial_frame_1:
    forall pc,
      PMap.In (Pointer.component pc) ctx ->
      I.PS.to_partial_frame (map fst (PMap.elements ctx)) pc = (Pointer.component pc, None).
  Proof.
    intros pc Hin_ctx.
    unfold I.PS.to_partial_frame, Pointer.inc, Pointer.add.
    destruct pc as [[C b] o].
    simpl in *. simplify_turn.
    destruct (Util.Lists.mem C (map fst (PMap.elements ctx))) eqn:Hin.
    *** reflexivity.
    *** exfalso. (* contra *)
        apply Util.Lists.not_in_iff_mem_false in Hin.
        apply Hin.
        unfold PMap.In, PMap.Raw.In0 in Hin_ctx.
        destruct Hin_ctx as [CI HCI].
        apply PMapFacts.elements_mapsto_iff in HCI.
        apply SetoidList.InA_altdef in HCI.
        apply Exists_exists in HCI.
        destruct HCI as [[] []].
        apply in_map_iff. exists (k,i). simpl. split.
        **** inversion H0. inversion H1. auto.
        **** auto.
  Qed.

  Lemma pc_inc_within_partial_frame_2:
    forall pc,
      ~ PMap.In (Pointer.component pc) ctx ->
      I.PS.to_partial_frame (map fst (PMap.elements ctx)) pc
      = (Pointer.component pc, Some (Pointer.block pc, Pointer.offset pc)).
  Proof.
    intros pc Hnot_in_ctx.
    unfold I.PS.to_partial_frame, Pointer.inc, Pointer.add.
    destruct pc as [[C b] o].
    simpl in *. simplify_turn.
    destruct (Util.Lists.mem C (map fst (PMap.elements ctx))) eqn:Hin.
    *** exfalso. (* contra *)
        apply Util.Lists.in_iff_mem_true in Hin.
        apply Hnot_in_ctx. unfold PMap.In, PMap.Raw.In0.
        apply in_map_iff in Hin. destruct Hin as [[] []].
        simpl in *. subst.
        eexists.
        apply PMapFacts.elements_mapsto_iff.
        apply SetoidList.In_InA.
        **** econstructor.
             ***** constructor; reflexivity.
             ***** constructor; destruct x; destruct y; inversion H; auto.
             ***** constructor; destruct x; destruct y; destruct z;
                   inversion H; inversion H1; simpl in *; subst; auto.
        **** apply H0.
    *** reflexivity.
  Qed.

  Lemma imported_procedure_in_context:
    forall C C' P,
      PMap.In C ctx ->
      imported_procedure (genv_interface G) C C' P ->
      imported_procedure ctx C C' P.
  Proof.
    intros C C' P Hin_ctx Himport.
    unfold imported_procedure in *.
    unfold PMap.In, PMap.Raw.In0 in Hin_ctx.
    destruct Hin_ctx as [CI HCI].
    destruct Himport as [CI' [HCI' Himp]].
    unfold Program.has_component in *.
    assert (HCI2 := HCI).
    apply context_validity in HCI.
    unfold G, init_genv in HCI'.
    destruct (init_all prog). destruct p. simpl in *.
    pose proof (PMapFacts.MapsTo_fun HCI HCI'). subst.
    exists CI'. split; auto.
  Qed.

  Lemma lockstep_simulation:
    forall ics t ics',
      I.CS.step G ics t ics' ->
    forall ips,
      I.PS.partial_state ctx ics ips ->
    exists ips',
      I.PS.step ctx G ips t ips' /\ I.PS.partial_state ctx ics' ips'.
  Proof.
    intros ics t ics' Hstep ips Hpartial.

    (* case analysis on who has control *)
    inversion Hpartial; subst;
    inversion Hstep; subst.

    (** program has control **)

    (* epsilon steps *)

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
      + econstructor; auto.
        ** simplify_turn.
           unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
      + econstructor; auto.
        ** simplify_turn.
           unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
      + econstructor; auto.
        ** simplify_turn.
           unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
      + econstructor; auto.
        ** simplify_turn.
           unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
      + econstructor; auto.
        ** simplify_turn.
           unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
      + econstructor; auto.
        ** simplify_turn.
           unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.

    - destruct (Memory.store pmem ptr (Register.get r2 regs)) as [pmem'|] eqn:Hpmem'.
      + exists (I.PS.PC (I.PS.to_partial_stack gps (map fst (PMap.elements ctx)),
                    pmem', regs, Pointer.inc pc)).
        split.
        * econstructor; auto.
          ** apply Hstep.
          ** econstructor; auto.
          ** econstructor; eauto.
             *** simplify_turn.
                 unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
             *** unfold Memory.store in *.
                 destruct ptr; destruct p.
                 destruct (PMap.find i pmem)
                          eqn:Hmem_find1; try discriminate.
                 destruct (ComponentMemory.store t i0 o (Register.get r2 regs))
                          eqn:Hmem_store1; try discriminate.
                 inversion Hpmem'; subst.
                 destruct (PMap.find i mem)
                   eqn:Hmem_find2; try discriminate.
                 destruct (ComponentMemory.store t1 i0 o (Register.get r2 regs))
                   eqn:Hmem_store2; try discriminate.
                 inversion H10; subst.
                 assert (t = t1). {
                   specialize (H2 i). rewrite H2 in Hmem_find1.
                   apply PMapFacts.find_mapsto_iff in Hmem_find1.
                   apply PMapExtra.filter_iff in Hmem_find1.
                   destruct Hmem_find1.
                   apply PMap.find_1 in H. rewrite H in Hmem_find2.
                   inversion Hmem_find2. reflexivity.
                   (* morphisms stuff *)
                   unfold Morphisms.Proper, Morphisms.respectful.
                   intros. subst. reflexivity.
                 }
                 subst.
                 rewrite Hmem_store2 in Hmem_store1. inversion Hmem_store1.
                 subst.
                 rewrite H2.

                 unfold PMap.Equal. intro.
                 rewrite PMapFacts.add_o.
                 destruct (PMapFacts.eq_dec i y).
                 **** subst. admit.
                 **** admit.
        * econstructor; eauto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
          ** admit.
      + (* contra *)
        unfold Memory.store in *.
        destruct ptr; destruct p.
        destruct (PMap.find i mem)
                 eqn:Hmem_find2; try discriminate.
        destruct (ComponentMemory.store t i0 o (Register.get r2 regs))
                 eqn:Hmem_store1; try discriminate.
        inversion H10; subst.
        destruct (PMap.find i pmem)
                 eqn:Hmem_find1; try discriminate.
        * destruct (ComponentMemory.store t1 i0 o (Register.get r2 regs))
                 eqn:Hmem_store2; try discriminate.
          assert (t = t1). {
            specialize (H2 i). rewrite H2 in Hmem_find1.
            apply PMapFacts.find_mapsto_iff in Hmem_find1.
            apply PMapExtra.filter_iff in Hmem_find1.
            destruct Hmem_find1.
            apply PMap.find_1 in H. rewrite H in Hmem_find2.
            inversion Hmem_find2. reflexivity.
            (* morphisms stuff *)
            unfold Morphisms.Proper, Morphisms.respectful.
            intros. subst. reflexivity.
          }
          subst.
          rewrite Hmem_store2 in Hmem_store1. inversion Hmem_store1.
        * (* contra *)
          admit.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn. erewrite <- find_label_in_component_1; eauto.
      + econstructor; auto.
        ** simplify_turn. erewrite <- find_label_in_component_1; eauto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn. rewrite H9. eauto.
      + econstructor; auto.
        ** simplify_turn. rewrite H9. eauto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn. erewrite <- find_label_in_procedure_1; eauto.
      + econstructor; auto.
        ** simplify_turn. erewrite <- find_label_in_procedure_1; eauto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
      + econstructor; auto.
        ** simplify_turn.
           unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.

    - eexists. split.
      + econstructor; auto.
        * apply Hstep.
        * econstructor; auto.
        * econstructor; eauto.
          ** simplify_turn.
             unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
          ** (* should be provable *) admit.
      + econstructor; auto.
        ** simplify_turn.
           unfold Pointer.inc, Pointer.add. destruct pc. destruct p. auto.
        ** (* should be provable *) admit.

    (* call *)
    (* case analysis on the target *)
    - destruct (PMap.mem C' ctx) eqn:Htarget.
      (* external call *)
      + eexists. split.
        * eapply I.PS.Program_External_Call; eauto.
          ** reflexivity.
          ** simplify_turn.
             apply PMapFacts.mem_in_iff. auto.
        * eapply I.PS.ContextControl_Normal; eauto.
          ** simplify_turn.
             apply PMapFacts.mem_in_iff. auto.
          ** unfold I.PS.to_partial_stack. simpl.
             rewrite pc_inc_within_partial_frame_2; auto.
             unfold Pointer.inc, Pointer.add. destruct pc as [[]]. reflexivity.
             unfold Pointer.inc, Pointer.add. destruct pc as [[]]. simpl. simplify_turn.
      (* internal call *)
      + eexists. split.
        * eapply I.PS.Program_Internal_Call; eauto.
          ** reflexivity.
          ** simplify_turn.
             apply PMapFacts.not_mem_in_iff. auto.
        * eapply I.PS.ProgramControl; eauto.
          ** simplify_turn.
             apply PMapFacts.not_mem_in_iff. auto.
          ** unfold I.PS.to_partial_stack. simpl.
             rewrite pc_inc_within_partial_frame_2; auto.
             unfold Pointer.inc, Pointer.add. destruct pc as [[]]. reflexivity.
             unfold Pointer.inc, Pointer.add. destruct pc as [[]]. simpl. simplify_turn.

    (* return *)
    (* case analysis on the target *)
    - destruct (PMap.mem (Pointer.component pc') ctx) eqn:Htarget.
      (* external return *)
      + eexists. split.
        * eapply I.PS.Program_External_Return; eauto.
          ** reflexivity.
          ** simplify_turn.
             apply PMapFacts.mem_in_iff. auto.
          ** unfold I.PS.to_partial_stack. simpl.
             apply PMapFacts.mem_in_iff in Htarget.
             rewrite pc_inc_within_partial_frame_1; auto.
        * eapply I.PS.ContextControl_Normal; eauto.
          ** simplify_turn.
             apply PMapFacts.mem_in_iff. auto.
      (* internal return *)
      + eexists. split.
        * eapply I.PS.Program_Internal_Return; eauto.
          ** reflexivity.
          ** simplify_turn.
             apply PMapFacts.not_mem_in_iff. auto.
          ** unfold I.PS.to_partial_stack. simpl.
             rewrite pc_inc_within_partial_frame_2.
             *** reflexivity.
             *** apply PMapFacts.not_mem_in_iff. auto.
        * eapply I.PS.ProgramControl; eauto.
          ** destruct pc' as [[]]. simpl. reflexivity.
          ** simplify_turn.
             apply PMapFacts.not_mem_in_iff. auto.

    (** context has control **)

    (* epsilon steps *)
    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * unfold Pointer.inc, Pointer.add. destruct pc. destruct p. reflexivity.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * unfold Pointer.inc, Pointer.add. destruct pc. destruct p. reflexivity.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * unfold Pointer.inc, Pointer.add. destruct pc. destruct p. reflexivity.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * unfold Pointer.inc, Pointer.add. destruct pc. destruct p. reflexivity.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * unfold Pointer.inc, Pointer.add. destruct pc. destruct p. reflexivity.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * unfold Pointer.inc, Pointer.add. destruct pc. destruct p. reflexivity.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * unfold Pointer.inc, Pointer.add. destruct pc. destruct p. reflexivity.
        * (* should be provable *) admit.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * erewrite find_label_in_component_1; eauto.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * rewrite H9; eauto.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * erewrite find_label_in_procedure_1; eauto.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * unfold Pointer.inc, Pointer.add. destruct pc. destruct p. reflexivity.

    - eexists. split.
      + eapply I.PS.Context_Epsilon; auto.
      + eapply I.PS.ContextControl_Normal; eauto.
        * unfold Pointer.inc, Pointer.add. destruct pc. destruct p. reflexivity.
        * (* should be provable *) admit.

    (* call *)
    (* case analysis on the target *)
    - destruct (PMap.mem C' ctx) eqn:Htarget.
      (* internal call *)
      + eexists. split.
        * eapply I.PS.Context_Internal_Call.
          ** eauto.
          ** eauto.
          ** reflexivity.
          ** simplify_turn.
          ** simplify_turn.
             apply PMapFacts.mem_in_iff. auto.
          ** auto.
          ** simplify_turn.
             apply imported_procedure_in_context; auto.
          ** eauto.
        * eapply I.PS.ContextControl_Normal.
          ** eauto.
          ** eauto.
          ** simplify_turn.
             apply PMapFacts.mem_in_iff. auto.
          ** auto.
          ** unfold I.PS.to_partial_stack. simpl.
             apply PMapFacts.mem_in_iff in Htarget.
             rewrite pc_inc_within_partial_frame_1.
             *** unfold Pointer.inc, Pointer.add.
                 destruct pc as [[]]. reflexivity.
             *** unfold Pointer.inc, Pointer.add.
                 destruct pc as [[]]. simpl. simplify_turn.
      (* external call *)
      + exists (I.PS.PC ((Pointer.component pc, None) ::
                    I.PS.to_partial_stack gps (map fst (PMap.elements ctx)),
                    pmem, Register.invalidate regs, pc')).
        split.
        * eapply I.PS.Context_External_Call.
          ** eauto.
          ** eauto.
          ** reflexivity.
          ** simplify_turn.
          ** simplify_turn.
             apply PMapFacts.not_mem_in_iff.
             change C' with (Pointer.component pc') in Htarget.
             apply Htarget.
          ** simplify_turn.
             apply imported_procedure_in_context; auto.
          ** eauto.
          ** eauto.
          ** eauto.
          ** eauto.
        * eapply I.PS.ProgramControl; auto.
          ** simplify_turn.
             apply PMapFacts.not_mem_in_iff. auto.
          ** unfold I.PS.to_partial_stack. simpl.
             rewrite pc_inc_within_partial_frame_1.
             *** unfold Pointer.inc, Pointer.add.
                 destruct pc as [[]]. reflexivity.
             *** unfold Pointer.inc, Pointer.add.
                 destruct pc as [[]]. simpl. simplify_turn.

    (* return *)
    (* case analysis on the target *)
    - destruct (PMap.mem (Pointer.component pc') ctx) eqn:Htarget.
      (* internal return *)
      + eexists. split.
        * eapply I.PS.Context_Internal_Return.
          ** eauto.
          ** eauto.
          ** reflexivity.
          ** simplify_turn.
          ** simplify_turn.
             apply PMapFacts.mem_in_iff. auto.
          ** auto.
          ** unfold I.PS.to_partial_stack. simpl.
             apply PMapFacts.mem_in_iff in Htarget.
             rewrite pc_inc_within_partial_frame_1.
             *** unfold Pointer.inc, Pointer.add.
                 destruct pc as [[]]. reflexivity.
             *** unfold Pointer.inc, Pointer.add.
                 destruct pc as [[]]. simpl. simplify_turn.
        * eapply I.PS.ContextControl_Normal.
          ** eauto.
          ** eauto.
          ** simplify_turn.
             apply PMapFacts.mem_in_iff. auto.
          ** auto.
          ** eauto.
      (* external return *)
      + exists (I.PS.PC (I.PS.to_partial_stack gps' (map fst (PMap.elements ctx)),
                    pmem, Register.invalidate regs, pc')).
        split.
        * eapply I.PS.Context_External_Return.
          ** eauto.
          ** eauto.
          ** reflexivity.
          ** simplify_turn.
          ** simplify_turn.
             apply PMapFacts.not_mem_in_iff. eauto.
          ** eauto.
          ** unfold I.PS.to_partial_stack. simpl.
             apply PMapFacts.not_mem_in_iff in Htarget.
             rewrite pc_inc_within_partial_frame_2.
             *** unfold Pointer.inc, Pointer.add.
                 destruct pc as [[]]. reflexivity.
             *** unfold Pointer.inc, Pointer.add.
                 destruct pc as [[]]. simpl. simplify_turn.
          ** destruct pc' as [[]]. reflexivity.
        * eapply I.PS.ProgramControl.
          ** eauto.
          ** reflexivity.
          ** simplify_turn.
             apply PMapFacts.not_mem_in_iff. auto.
          ** eauto.
          ** auto.
  Admitted.

  Theorem decomposition:
    forward_simulation (I.CS.sem prog) (I.PS.sem prog ctx).
  Proof.
    eapply forward_simulation_step.
    - apply match_initial_states.
    - apply match_final_states.
    - apply lockstep_simulation.
  Qed.

  Corollary decomposition_with_refinement:
    forall beh1, program_behaves (I.CS.sem prog) beh1 ->
    exists beh2, program_behaves (I.PS.sem prog ctx) beh2 /\ behavior_improves beh1 beh2.
  Proof.
    intros beh1 Hbeh1.
    eapply forward_simulation_behavior_improves; eauto.
    apply decomposition.
  Qed.
End Decomposition.

Section DecompositionAndLinking.
  Variable p c: Intermediate.program.
  Variable mainC: Component.id.
  Variable mainP: Procedure.id.

  Corollary decomposition_with_linking:    
    forward_simulation (I.CS.sem (Intermediate.program_link p c mainC mainP))
                       (I.PS.sem (Intermediate.program_link p c mainC mainP)
                                 (Intermediate.prog_interface c)).
  Proof.
    apply decomposition.
    intros C CI Hin_c.
    unfold program_link. simpl.
    apply PMapExtra.update_mapsto_iff. left. auto.
  Qed.
End DecompositionAndLinking.