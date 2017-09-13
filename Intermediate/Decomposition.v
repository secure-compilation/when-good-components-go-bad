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

  (* p and c can be linked *)
  Hypothesis linkability:
    linkable_programs p c.

  (* linking p and c results in a closed program *)
  (* (it should also be a well-formed program, but this should follow from
      the fact that p and c are linkable) *)
  Hypothesis linked_program_closedness:
    closed_program (program_link p c mainC mainP).

  Let split := map fst (NMap.elements (prog_interface p)).
  Let G := init_genv (program_link p c mainC mainP).
  Let G' := init_genv (PS.partialize (program_link p c mainC mainP) (prog_interface c)).

  Lemma G_is_well_formed:
    well_formed_global_env G.
  Proof.
    apply (init_genv_preserves_well_formedness (program_link p c mainC mainP)).
    - apply linking_well_formedness; auto.
  Qed.

  Lemma G'_is_well_formed:
    well_formed_global_env G'.
  Proof.
    apply (init_genv_preserves_well_formedness
          (PS.partialize (program_link p c mainC mainP) (prog_interface c))); auto.
    - destruct linkability; auto.
      unfold PS.partialize, program_link. simpl.
      (* TODO to prove *)
      (* it would be easy to prove if we had some lemmas about maps update combined
         with the map diff and filter operations *)
  Admitted.

  Inductive related_states : CS.state -> PS.state -> Prop :=
  | ProgramControl:
      forall gps pgps mem pmem regs pc,
        (* the program has control *)
        PS.is_program_component G' (Pointer.component pc) ->
        (* the partial stack is in sync *)
        pgps = PS.to_partial_stack gps split ->
        (* mem contains exactly all components memories *)
        (forall C, NMap.In C (prog_interface (program_link p c mainC mainP)) <->
              NMap.In C mem) ->
        (* pmem contains exactly all program components memories of mem *)
        (forall C, PS.is_program_component G' C ->
              (forall Cmem, NMap.MapsTo C Cmem mem <-> NMap.MapsTo C Cmem pmem)) ->
        (* registers and the program counter are equal *)
        related_states (gps, mem, regs, pc)
                       (PS.PC (pgps, pmem, regs, pc))

  | ContextControl_Normal:
      forall gps pgps mem pmem regs pc,
        (* the context has control *)
        PS.is_context_component (prog_interface c) (Pointer.component pc) ->
        (* the partial stack is in sync *)
        pgps = PS.to_partial_stack gps split ->
        (* mem contains exactly all components memories *)
        (forall C, NMap.In C (prog_interface (program_link p c mainC mainP)) <->
              NMap.In C mem) ->
        (* pmem contains exactly all program components memories of mem *)
        (forall C, PS.is_program_component G' C ->
              (forall Cmem, NMap.MapsTo C Cmem mem <-> NMap.MapsTo C Cmem pmem)) ->
        (* registers and the program counter are equal *)
        related_states (gps, mem, regs, pc)
                       (PS.CC (Pointer.component pc, pgps, pmem) PS.Normal)

  | ContextControl_WentWrong:
      forall gps pgps mem pmem regs pc,
        (* the context has control *)
        PS.is_context_component (prog_interface c) (Pointer.component pc) ->
        (* the partial stack is in sync *)
        pgps = PS.to_partial_stack gps split ->
        (* mem contains exactly all components memories *)
        (forall C, NMap.In C (prog_interface (program_link p c mainC mainP)) <->
              NMap.In C mem) ->
        (* pmem contains exactly all program components memories of mem *)
        (forall C, PS.is_program_component G' C ->
              (forall Cmem, NMap.MapsTo C Cmem mem <-> NMap.MapsTo C Cmem pmem)) ->
        (* the current state doesn't step and it's not final (i.e. it's stuck) *)
        (forall s' t, ~ CS.step G (gps,mem,regs,pc) t s') ->
        ~ (forall r, CS.final_state G (gps,mem,regs,pc) r) ->
        (* registers and the program counter are equal *)
        related_states (gps, mem, regs, pc)
                       (PS.CC (Pointer.component pc, pgps, pmem) PS.WentWrong).

  Lemma initial_states_match:
    forall s1,
      CS.initial_state (program_link p c mainC mainP) s1 ->
    exists s2,
      PS.initial_state (PS.partialize (program_link p c mainC mainP) (prog_interface c))
                       (prog_interface c) s2
      /\ related_states s1 s2.
  Proof.
    (*
    intros s1 Hs1_init.
    CS.unfold_state.
    destruct Hs1_init
      as [Hempty_stack [Hmem1 [Hmem2 [Hregs [Hpc_comp [Hpc_block Hpc_offset]]]]]].
    destruct (NMapExtra.F.In_dec (prog_interface p) mainC) as [Hprg|Hctx].
    (* program has control case *)
    - exists (PS.PC (PS.to_partial_stack s split,
                NMapExtra.filter (fun C _ => NMap.mem C (prog_interface p)) mem,
                regs, pc)).
      split.
      + unfold PS.initial_state.
        split.
        * subst. auto.
        * split.
          ** intro C. split.
             *** intro HCprog.
                 unfold PS.is_program_component in HCprog.
                 unfold G', init_genv in HCprog.
                 destruct (init_all (PS.partialize (program_link p c mainC mainP)
                                                   (prog_interface c))).
                 destruct p0. simpl in HCprog.
                 apply NMapExtra.diff_in_iff in HCprog. destruct HCprog.
                 apply NMapExtra.update_in_iff in H. destruct H.
                 **** specialize (Hmem1 C).
                      assert (HCinPC: NMap.In C (prog_interface
                                                  (program_link p c mainC mainP))). {
                        unfold program_link. simpl.
                        apply NMapExtra.update_in_iff. left. auto.
                      } apply Hmem1 in HCinPC.
                      destruct HCinPC.
                      exists x.
                      apply NMapExtra.filter_iff.
                      ***** unfold Morphisms.Proper, Morphisms.respectful.
                            intros. subst. reflexivity.
                      ***** split.
                      ****** auto.
                      ****** apply NMapExtra.F.mem_in_iff. auto.
                 **** contradiction.
             *** intro.
                 destruct H.
                 apply NMapExtra.filter_iff in H.
                 **** destruct H. apply NMapExtra.F.mem_in_iff in H0.
                      unfold PS.is_program_component, G', init_genv.
                      destruct (init_all (PS.partialize (program_link p c mainC mainP)
                                                        (prog_interface c))).
                      destruct p0. simpl.
                      apply NMapExtra.diff_in_iff. split.
                      ***** apply NMapExtra.update_in_iff. left. auto.
                      ***** destruct linkability as [? [? []]].
                      unfold NMapExtra.Disjoint in H3.
                      specialize (H3 C). intro.
                      apply H3. split. auto. auto.
                 **** unfold Morphisms.Proper, Morphisms.respectful.
                      intros. subst. reflexivity.
          ** split.
             *** (* TODO prove that memory gets initialized in the same way *) admit.
             *** split.
                 **** subst. reflexivity.
                 **** split.
                      ***** unfold PS.is_program_component.
                      simpl in Hpc_comp. subst.
                      unfold G', init_genv.
                      destruct (init_all
                                  (PS.partialize (program_link p c (Pointer.component pc)
                                                               mainP)
                                                 (prog_interface c))).
                      destruct p0. simpl.
                      apply NMapExtra.diff_in_iff. split.
                      ****** apply NMapExtra.update_in_iff. left. auto.
                      ****** unfold linkable_programs in linkability.
                      destruct linkability as [? [? [Hdisjoint ?]]].
                      unfold NMapExtra.Disjoint in Hdisjoint.
                      specialize (Hdisjoint (Pointer.component pc)).
                      intro. apply Hdisjoint. split; auto.
                      ***** split.
                      ****** rewrite Hpc_comp. simpl. reflexivity.
                      ****** simpl in *. split.
                      ******* unfold G', init_genv.
                        (* TODO prove that entrypoints are the same in G and G' *)
                        admit.
                      ******* auto.
      + apply ProgramControl.
        * simpl in *. rewrite Hpc_comp.
          unfold PS.is_program_component. unfold G', init_genv.
          destruct (init_all (PS.partialize (program_link p c mainC mainP)
                                            (prog_interface c))).
          destruct p0. simpl.
          apply NMapExtra.diff_in_iff. split.
          ** apply NMapExtra.update_in_iff. left. auto.
          ** destruct linkability as [? [? []]].
             unfold NMapExtra.Disjoint in H1.
             specialize (H1 mainC). intro.
             apply H1. split. auto. auto.
        * subst. reflexivity.
        * intro C. simpl. split.
          ** intro. apply Hmem1. unfold G, init_genv.
             destruct (init_all (program_link p c mainC mainP)). destruct p0. simpl.
             auto.
          ** intro.
             unfold G, init_genv in Hmem1.
             destruct (init_all (program_link p c mainC mainP)). destruct p0. simpl in *.
             apply Hmem1. auto.
        * intros C HCprog Cmem. split.
          ** intro. apply NMapExtra.filter_iff.
             *** unfold Morphisms.Proper, Morphisms.respectful.
                 intros. subst. reflexivity.
             *** split. auto.
                 unfold PS.is_program_component in HCprog.
                 unfold G', init_genv in HCprog.
                 destruct (init_all (PS.partialize (program_link p c mainC mainP)
                                                   (prog_interface c))).
                 destruct p0. simpl in HCprog.
                 apply NMapExtra.diff_in_iff in HCprog. destruct HCprog.
                 apply NMapExtra.update_in_iff in H0. destruct H0.
                 **** apply NMapExtra.F.mem_in_iff. auto.
                 **** contradiction.
          ** intro.
             unfold PS.is_program_component in HCprog.
             unfold G', init_genv in HCprog.
             destruct (init_all (PS.partialize (program_link p c mainC mainP)
                                               (prog_interface c))).
             destruct p0. simpl in HCprog.
             apply NMapExtra.diff_in_iff in HCprog. destruct HCprog.
             apply NMapExtra.update_in_iff in H0. destruct H0.
             *** apply NMapExtra.filter_iff in H.
                 **** destruct H. auto.
                 **** unfold Morphisms.Proper, Morphisms.respectful.
                      intros. subst. reflexivity.
             *** contradiction.

    (* context has control case *)
    - exists (PS.CC (mainC,
                     PS.to_partial_stack s split,
                     NMapExtra.filter (fun C _ => NMap.mem C (prog_interface p)) mem) PS.Normal).
      split.
      + unfold PS.initial_state.
        split.
        * subst. reflexivity.
        * split.
          ** intro C. split.
             *** intro HCinprog.
                 unfold PS.is_program_component in HCinprog.
                 unfold G', init_genv in HCinprog.
                 destruct (init_all (PS.partialize (program_link p c mainC mainP)
                                                   (prog_interface c))).
                 destruct p0. simpl in HCinprog.
                 apply NMapExtra.diff_in_iff in HCinprog.
                 destruct HCinprog as [H1 H2].
                 specialize (Hmem1 C).
                 unfold program_link in Hmem1. simpl in Hmem1.
                 assert (H1' := H1).
                 apply Hmem1 in H1. destruct H1.
                 exists x. apply NMapExtra.filter_iff.
                 **** unfold Morphisms.Proper, Morphisms.respectful.
                      intros. subst. reflexivity.
                 **** split.
                      ***** apply H.
                      ***** apply NMapExtra.F.mem_in_iff. 
                      apply NMapExtra.update_in_iff in H1'.
                      destruct H1'; try contradiction.
                      auto.
             *** intro HCinmem.
                 unfold PS.is_program_component, G', init_genv.
                 destruct (init_all (PS.partialize (program_link p c mainC mainP)
                                                   (prog_interface c))).
                 destruct p0. simpl.
                 apply NMapExtra.diff_in_iff. split.
                 **** destruct HCinmem. apply NMapExtra.filter_iff in H.
                      ***** destruct H. apply NMapExtra.F.mem_in_iff in H0.
                      apply NMapExtra.update_in_iff. left. auto.
                      ***** unfold Morphisms.Proper, Morphisms.respectful.
                      intros. subst. reflexivity.
                 (* disjointness of interfaces *)
                 **** destruct linkability as [? [? []]].
                      unfold NMapExtra.Disjoint in H1.
                      specialize (H1 C). intro.
                      apply H1. split.
                      ***** destruct HCinmem. apply NMapExtra.filter_iff in H4.
                      destruct H4. apply NMapExtra.F.mem_in_iff in H5. auto.
                      ****** unfold Morphisms.Proper, Morphisms.respectful.
                      intros. subst. reflexivity.
                      ***** auto.
          ** split.
             *** (* TODO prove that memory gets initialized in the same way *) admit.
             *** split.
                 **** (* TODO prove that the executing component belongs to the context *)
                   admit.
                 **** split.
                      ***** simpl in *. auto. 
                      ***** reflexivity.
      + replace mainC with (Pointer.component pc). apply ContextControl_Normal.
        * simpl in Hpc_comp. rewrite Hpc_comp.
          admit.
        * subst. reflexivity.
        * intro C. split; intro; apply (Hmem1 C); auto.
        * intros. split.
          ** intro.
             apply NMapExtra.filter_iff.
             *** unfold Morphisms.Proper, Morphisms.respectful.
                 intros. subst. reflexivity.
             *** split. auto.
                 apply NMapExtra.F.mem_in_iff.
                 unfold PS.is_program_component in H.
                 unfold G', init_genv in H.
                 destruct (init_all (PS.partialize (program_link p c mainC mainP)
                                                   (prog_interface c))).
                 destruct p0. simpl in H.
                 apply NMapExtra.diff_in_iff in H. destruct H.
                 apply NMapExtra.update_in_iff in H. destruct H; try contradiction.
                 auto.
          ** intro. apply NMapExtra.filter_iff in H0.
             *** destruct H0. auto.
             *** unfold Morphisms.Proper, Morphisms.respectful.
                 intros. subst. reflexivity.
     *)
  Admitted.

  Lemma final_states_match:
    forall s1 s2 r,
      related_states s1 s2 ->
      CS.final_state G s1 r -> PS.final_state G' s2 r.
  Proof.
    intros s1 s2 r Hs1s2_rel Hs1_final.
    CS.unfold_state.
    destruct Hs1_final as [procs [proc [Hprocs [Hproc Hinstr]]]].
  Admitted.

  Lemma lockstep_simulation:
    forall s1 t s1',
      CS.step G s1 t s1' ->
    forall s2,
      related_states s1 s2 ->
    exists s2',
      PS.step (prog_interface c) G' s2 t s2' /\ related_states s1' s2'.
  Proof.
    intros s1 t s1' Hstep s2 Hs1s2_rel.
(*
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
 *)
  Admitted.

  Theorem PS_simulates_CS:
    forward_simulation (CS.sem (program_link p c mainC mainP))
                       (PS.sem (program_link p c mainC mainP) (prog_interface c)).
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
      program_behaves (PS.sem (program_link p c mainC mainP) (prog_interface c)) beh2 /\
      behavior_improves beh1 beh2.
  Proof.
    intros.
    eapply forward_simulation_behavior_improves; eauto.
    apply PS_simulates_CS.
  Qed.

  Corollary PS_behaves_as_CS:
    forall beh, program_behaves (CS.sem (program_link p c mainC mainP)) beh ->
           program_behaves (PS.sem (program_link p c mainC mainP) (prog_interface c)) beh.
  Proof.
  Admitted.
End Decomposition.