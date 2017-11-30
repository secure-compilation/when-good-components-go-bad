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

(* iface1 is part of iface2 *)
Definition part_of (iface1 iface2: Program.interface) : Prop :=
  forall C CI,
    PMap.MapsTo C CI iface1 -> PMap.MapsTo C CI iface2.

(* partializing a closed program gives two partial programs which are linkable *)
Lemma linkability_of_a_partialized_program:
  forall prog ctx,
    part_of ctx (prog_interface prog) ->
    well_formed_program prog ->
    closed_program prog ->
    linkable_programs
      (partialize_program prog ctx)
      (partialize_program prog (prog_interface (partialize_program prog ctx))).
Proof.
Admitted.

(* partializing a closed well-formed program and linking the resulting partial programs
   gives back the original program *)
Lemma linking_a_partialized_program:
  forall prog ctx,
    part_of ctx (prog_interface prog) ->
    well_formed_program prog ->
    closed_program prog ->
    prog_eq prog
            (program_link (partialize_program prog ctx)
                          (partialize_program prog (prog_interface (partialize_program prog ctx)))
                          (fst (prog_main prog)) (snd (prog_main prog))).
Proof.
Admitted.

Corollary init_genv_after_linking_a_partialized_program:
  forall prog ctx,
    part_of ctx (prog_interface prog) ->
    well_formed_program prog ->
    closed_program prog ->
    genv_eq (init_genv prog)
            (init_genv
               (program_link (partialize_program prog ctx)
                             (partialize_program prog (prog_interface (partialize_program prog ctx)))
                             (fst (prog_main prog)) (snd (prog_main prog)))).
Proof.
  intros prog ctx Hpart_of Hwell_formedness Hclosedness.
  apply init_genv_with_same_program.
  apply linking_a_partialized_program; auto.
Qed.

(* tricky filtering step *)
Lemma double_filtering:
  forall iface1 iface2,
    part_of iface2 iface1 ->
    PMap.Equal
      (PMapExtra.filter
         (fun k _ => negb (PMap.mem k (PMapExtra.filter
                                         (fun k' _ => negb (PMap.mem k' iface2))
                                         iface1)))
         iface1) iface2.
Proof.
Admitted.

Lemma init_genv_with_extension_of_partialized_program:
  forall prog ctx,
    part_of ctx (prog_interface prog) ->
    genv_eq (init_genv prog)
            (extend_genv (init_genv (partialize_program prog ctx))
                         (init_genv (partialize_program prog (prog_interface (partialize_program prog ctx))))).
Proof.
Admitted.

(* simulations work with program equality *)
(* is this a problem? Is program equality creating problems here that we have
   to mix it with CompCert definitions that doesn't care about it? I think it might *)
Lemma same_program_forward_simulation:
  forall p p1 ctx,
    forward_simulation (CS.sem p) (PS.sem p1 ctx) ->
  forall p2,
    prog_eq p1 p2 ->
    forward_simulation (CS.sem p) (PS.sem p2 ctx).
Proof.
Admitted.

(* partializing after the linking phase should give back the original partial program *)
Lemma partialize_after_linking:
  forall p c,
    linkable_programs p c ->
    prog_eq (partialize_program (program_link p c (fst (prog_main p)) (snd (prog_main p)))
                                (prog_interface c)) p.
Proof.
Admitted.

Section Decomposition.
  Variable prog: program.
  Variable ctx: Program.interface.

  Hypothesis input_program_well_formedness:
    well_formed_program prog.

  Hypothesis input_program_closedness:
    closed_program prog.

  Hypothesis context_validity:
    part_of ctx (prog_interface prog).

  Let pprog := partialize_program prog ctx.

  Lemma match_initial_states:
    forall ics,
      CS.initial_state prog ics ->
    exists ips,
      PS.initial_state pprog ctx ips /\ PS.partial_state ctx ics ips.
  Proof.
    intros ics Hics_init.
    CS.unfold_states.
    (* case analysis on who has control, then build the partial state *)
    destruct (PMap.mem (Pointer.component pc) ctx) eqn:Htarget;
      exists (PS.partialize (s, mem, regs, pc) ctx);
      simpl; rewrite Htarget.
    (* context has control *)
    - split.
      + eapply PS.initial_state_intro
          with (p':=partialize_program prog (prog_interface pprog)).
        * subst pprog.
          apply linkability_of_a_partialized_program; auto.
        * eapply PS.ContextControl; eauto.
          ** PS.simplify_turn.
             apply PMapFacts.mem_in_iff. auto.
          ** apply PMapFacts.Equal_refl.
        * subst pprog.
          eapply CS.same_program_initial_state with (p1:=prog).
          ** simpl. apply linking_a_partialized_program; auto.
          ** eassumption.
      + eapply PS.ContextControl; eauto.
        ** PS.simplify_turn.
           apply PMapFacts.mem_in_iff. auto.
        ** apply PMapFacts.Equal_refl.
    (* program has control *)
    - split.
      + eapply PS.initial_state_intro
          with (p':=partialize_program prog (prog_interface pprog)).
        * subst pprog.
          apply linkability_of_a_partialized_program; auto.
        * eapply PS.ProgramControl; auto.
          ** PS.simplify_turn.
             apply PMapFacts.not_mem_in_iff. auto.
          ** apply PMapFacts.Equal_refl.
        * subst pprog.
          eapply CS.same_program_initial_state with (p1:=prog).
          ** simpl; apply linking_a_partialized_program; auto.
          ** eassumption.
      + eapply PS.ProgramControl; auto.
        ** PS.simplify_turn.
           apply PMapFacts.not_mem_in_iff. auto.
        ** apply PMapFacts.Equal_refl.
  Qed.

  Lemma match_final_states:
    forall ics ips,
      PS.partial_state ctx ics ips ->
      CS.final_state (init_genv prog) ics ->
      PS.final_state pprog ctx ips.
  Proof.
    intros ics ips Hpartial Hics_final.
    CS.unfold_states.
    (* case analysis on who has control *)
    destruct (PMap.mem (Pointer.component pc) ctx) eqn:Htarget.
    (* context has control *)
    - inversion Hpartial; inversion H; subst.
      + PS.simplify_turn.
        apply PMapFacts.mem_in_iff in Htarget.
        contradiction.
      + apply PS.final_state_context.
        PS.simplify_turn. auto.
    (* program has control *)
    - inversion Hpartial; inversion H; subst.
      + eapply PS.final_state_program
          with (p':=partialize_program prog (prog_interface pprog)).
        * subst pprog.
          apply linkability_of_a_partialized_program; auto.
        * PS.simplify_turn. auto.
        * eauto.
        * subst pprog.
          eapply CS.same_genv_final_state with (G1:=init_genv prog).
          ** simpl; apply init_genv_after_linking_a_partialized_program; auto.
          ** assumption.
      + apply PMapFacts.not_mem_in_iff in Htarget.
        contradiction.
  Qed.

  Lemma lockstep_simulation:
    forall ics t ics',
      CS.step (init_genv prog) ics t ics' ->
    forall ips,
      PS.partial_state ctx ics ips ->
    exists ips',
      PS.step ctx (init_genv pprog) ips t ips' /\ PS.partial_state ctx ics' ips'.
  Proof.
    intros ics t ics' Hstep ips Hpartial.

    (* case analysis on who has control and the executed step *)
    inversion Hpartial; subst;
    inversion Hstep; subst;
      match goal with
      | Heq1: CS.state_eq _ _,
        Heq2: CS.state_eq _ _ |- _ =>
        inversion Heq1; subst; inversion Heq2; subst
      end.

    (** program has control **)

    (* epsilon steps *)

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * subst pprog. simpl.
          apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** subst pprog. apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * econstructor; eauto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
          ** match goal with
             | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
               PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
               eapply Memory.equivalence_under_filter;
               symmetry; apply Hmem_eq
             end.
      + econstructor; auto.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.
        ** match goal with
           | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
             PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
             eapply Memory.equivalence_under_filter;
             symmetry; apply Hmem_eq
           end.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * econstructor; auto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
          ** match goal with
             | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
               PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
               eapply Memory.equivalence_under_filter;
               symmetry; apply Hmem_eq
             end.
      + econstructor; auto.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.
        ** match goal with
           | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
             PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
             eapply Memory.equivalence_under_filter;
             symmetry; apply Hmem_eq
           end.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * econstructor; auto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
          ** match goal with
             | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
               PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
               eapply Memory.equivalence_under_filter;
               symmetry; apply Hmem_eq
             end.
      + econstructor; auto.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.
        ** match goal with
           | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
             PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
             eapply Memory.equivalence_under_filter;
             symmetry; apply Hmem_eq
           end.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * econstructor; auto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
          ** match goal with
             | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
               PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
               eapply Memory.equivalence_under_filter;
               symmetry; apply Hmem_eq
             end.
      + econstructor; auto.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.
        ** match goal with
           | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
             PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
             eapply Memory.equivalence_under_filter;
             symmetry; apply Hmem_eq
           end.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * econstructor; auto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
          ** match goal with
             | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
               PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
               eapply Memory.equivalence_under_filter;
               symmetry; apply Hmem_eq
             end.
      + econstructor; auto.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.
        ** match goal with
           | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
             PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
             eapply Memory.equivalence_under_filter;
             symmetry; apply Hmem_eq
           end.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * econstructor; auto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
          ** match goal with
             | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
               PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
               eapply Memory.equivalence_under_filter;
               symmetry; apply Hmem_eq
             end.
      + econstructor; auto.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.
        ** match goal with
           | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
             PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
             eapply Memory.equivalence_under_filter;
             symmetry; apply Hmem_eq
           end.

    - destruct (Memory.store pmem ptr (Register.get r2 regs0)) as [pmem'|] eqn:Hpmem'.
      + PS.simplify_turn. apply PMapFacts.not_mem_in_iff in H.
        exists (PS.partialize (gps0, mem', regs0, Pointer.inc pc0) ctx).
        simpl. rewrite Pointer.inc_preserves_component, H.
        split.
        * eapply PS.partial_step
            with (p':=partialize_program prog (prog_interface pprog)); auto.
          ** apply double_filtering; auto.
          ** apply CS.equal_genvs_step with (G1:=init_genv prog).
             *** apply init_genv_with_extension_of_partialized_program; auto.
             *** eassumption.
          ** econstructor; eauto.
             *** PS.simplify_turn; apply PMapFacts.not_mem_in_iff; auto.
          ** econstructor; auto.
             *** PS.simplify_turn.
                 rewrite Pointer.inc_preserves_component.
                 apply PMapFacts.not_mem_in_iff; auto.
             *** apply Memory.equivalence_under_filter.
                 rewrite H13. reflexivity.
        * econstructor; auto.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component.
             apply PMapFacts.not_mem_in_iff; auto.
          ** apply Memory.equivalence_under_filter.
             rewrite H13. reflexivity.
      + (* contra *)
        PS.simplify_turn. rewrite <- H4 in H.
        exfalso.
        eapply Memory.impossible_program_store_failure; eauto.
        rewrite H0. apply Memory.equivalence_under_filter.
        assumption.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * econstructor; auto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             erewrite <- find_label_in_component_1; eauto.
          ** match goal with
             | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
               PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
               eapply Memory.equivalence_under_filter;
               symmetry; apply Hmem_eq
             end.
      + econstructor; auto.
        ** PS.simplify_turn.
           erewrite <- find_label_in_component_1; eauto.
        ** match goal with
           | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
             PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
             eapply Memory.equivalence_under_filter;
             symmetry; apply Hmem_eq
           end.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * econstructor; auto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             match goal with
             | Hsame_comp: Pointer.component _ = Pointer.component _ |- _ =>
               rewrite Hsame_comp; assumption
             end.
          ** match goal with
             | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
               PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
               eapply Memory.equivalence_under_filter;
               symmetry; apply Hmem_eq
             end.
      + econstructor; auto.
        ** PS.simplify_turn.
           match goal with
           | Hsame_comp: Pointer.component _ = Pointer.component _ |- _ =>
             rewrite Hsame_comp; assumption
           end.
        ** match goal with
           | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
             PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
             eapply Memory.equivalence_under_filter;
             symmetry; apply Hmem_eq
           end.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * econstructor; auto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             erewrite <- find_label_in_procedure_1; eauto.
          ** match goal with
             | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
               PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
               eapply Memory.equivalence_under_filter;
               symmetry; apply Hmem_eq
             end.
      + econstructor; auto.
        ** PS.simplify_turn.
           erewrite <- find_label_in_procedure_1; eauto.
        ** match goal with
           | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
             PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
             eapply Memory.equivalence_under_filter;
             symmetry; apply Hmem_eq
           end.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * econstructor; auto.
        * econstructor; eauto.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
          ** match goal with
             | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
               PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
               eapply Memory.equivalence_under_filter;
               symmetry; apply Hmem_eq
             end.
      + econstructor; auto.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.
        ** match goal with
           | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
             PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
             eapply Memory.equivalence_under_filter;
             symmetry; apply Hmem_eq
           end.

    - destruct (Memory.alloc pmem (Pointer.component pc0) (Z.to_nat size))
        as [[pmem']|] eqn:Hpmem'.
      + PS.simplify_turn. apply PMapFacts.not_mem_in_iff in H.
        exists (PS.partialize (gps0, mem', Register.set rptr (Ptr ptr) regs0, Pointer.inc pc0) ctx).
        simpl. rewrite Pointer.inc_preserves_component, H.
        split.
        * eapply PS.partial_step
            with (p':=partialize_program prog (prog_interface pprog)); auto.
          ** apply double_filtering; auto.
          ** apply CS.equal_genvs_step with (G1:=init_genv prog).
             *** apply init_genv_with_extension_of_partialized_program; auto.
             *** eassumption.
          ** econstructor; eauto.
             *** PS.simplify_turn; apply PMapFacts.not_mem_in_iff in H; auto.
          ** econstructor; eauto.
             *** PS.simplify_turn.
                 rewrite Pointer.inc_preserves_component.
                 apply PMapFacts.not_mem_in_iff in H; auto.
             *** apply Memory.equivalence_under_filter.
                 symmetry. assumption.
        * econstructor; eauto.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component.
             apply PMapFacts.not_mem_in_iff in H; auto.
          ** apply Memory.equivalence_under_filter.
             symmetry. assumption.
      + (* contra *)
        PS.simplify_turn.
        exfalso.
        eapply Memory.impossible_program_allocation_failure; eauto.
        match goal with
        | Hfilter: PMap.Equal ?PMEM (PMapExtra.filter _ _) |-
          PMap.Equal ?PMEM (PMapExtra.filter _ _) =>
          rewrite Hfilter; apply Memory.equivalence_under_filter; assumption
        end.

    (* call *)
    (* case analysis on the target *)
    - destruct (PMap.mem C' ctx) eqn:Htarget.
      (* external call *)
      + eexists. split.
        * eapply PS.partial_step
            with (p':=partialize_program prog (prog_interface pprog)); auto.
          ** apply double_filtering; auto.
          ** apply CS.equal_genvs_step with (G1:=init_genv prog).
             *** apply init_genv_with_extension_of_partialized_program; auto.
             *** eassumption.
          ** eapply PS.ProgramControl; auto.
          ** eapply PS.ContextControl; auto.
             *** PS.simplify_turn.
                 apply PMapFacts.mem_in_iff. auto.
             *** match goal with
                 | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
                   PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
                   eapply Memory.equivalence_under_filter;
                   symmetry; apply Hmem_eq
                 end.
        * eapply PS.ContextControl; auto.
          ** PS.simplify_turn.
             apply PMapFacts.mem_in_iff. auto.
          ** match goal with
             | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
               PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
               eapply Memory.equivalence_under_filter;
               symmetry; apply Hmem_eq
             end.
      (* internal call *)
      + eexists. split.
        * eapply PS.partial_step
            with (p':=partialize_program prog (prog_interface pprog)); auto.
          ** apply double_filtering; auto.
          ** apply CS.equal_genvs_step with (G1:=init_genv prog).
             *** apply init_genv_with_extension_of_partialized_program; auto.
             *** eassumption.
          ** eapply PS.ProgramControl; auto.
          ** eapply PS.ProgramControl; auto.
             *** PS.simplify_turn.
                 apply PMapFacts.not_mem_in_iff. auto.
             *** match goal with
                 | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
                   PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
                   eapply Memory.equivalence_under_filter;
                   symmetry; apply Hmem_eq
                 end.
        * eapply PS.ProgramControl; auto.
          ** PS.simplify_turn.
             apply PMapFacts.not_mem_in_iff. auto.
          ** match goal with
             | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
               PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
               eapply Memory.equivalence_under_filter;
               symmetry; apply Hmem_eq
             end.

    (* return *)
    (* case analysis on the target *)
    - destruct (PMap.mem (Pointer.component pc') ctx) eqn:Htarget.
      (* external return *)
      + eexists. split.
        * eapply PS.partial_step
            with (p':=partialize_program prog (prog_interface pprog)); auto.
          ** apply double_filtering; auto.
          ** apply CS.equal_genvs_step with (G1:=init_genv prog).
             *** apply init_genv_with_extension_of_partialized_program; auto.
             *** eassumption.
          ** eapply PS.ProgramControl; auto.
          ** eapply PS.ContextControl; auto.
             *** PS.simplify_turn.
                 apply PMapFacts.mem_in_iff. auto.
             *** match goal with
                 | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
                   PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
                   eapply Memory.equivalence_under_filter;
                   symmetry; apply Hmem_eq
                 end.
        * eapply PS.ContextControl; auto.
          ** PS.simplify_turn.
             apply PMapFacts.mem_in_iff. auto.
          ** match goal with
             | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
               PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
               eapply Memory.equivalence_under_filter;
               symmetry; apply Hmem_eq
             end.
      (* internal return *)
      + eexists. split.
        * eapply PS.partial_step
            with (p':=partialize_program prog (prog_interface pprog)); auto.
          ** apply double_filtering; auto.
          ** apply CS.equal_genvs_step with (G1:=init_genv prog).
             *** apply init_genv_with_extension_of_partialized_program; auto.
             *** eassumption.
          ** eapply PS.ProgramControl; auto.
          ** eapply PS.ProgramControl; auto.
             *** PS.simplify_turn.
                 apply PMapFacts.not_mem_in_iff. auto.
             *** match goal with
                 | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
                   PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
                   eapply Memory.equivalence_under_filter;
                   symmetry; apply Hmem_eq
                 end.
        * eapply PS.ProgramControl; auto.
          ** PS.simplify_turn.
             apply PMapFacts.not_mem_in_iff. auto.
          ** match goal with
             | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
               PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
               eapply Memory.equivalence_under_filter;
               symmetry; apply Hmem_eq
             end.

    (** context has control **)

    (* epsilon steps *)

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
          ** auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
          ** auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
          ** auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
          ** auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
          ** auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
          ** auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
          ** auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
          ** auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             erewrite <- find_label_in_component_1; eauto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           erewrite <- find_label_in_component_1; eauto.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
          ** auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite H4. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite H4. auto.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
          ** auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             erewrite <- find_label_in_procedure_1; eauto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           erewrite <- find_label_in_procedure_1; eauto.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
          ** auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    - eexists. split.
      + eapply PS.partial_step
          with (p':=partialize_program prog (prog_interface pprog)); auto.
        * apply double_filtering; auto.
        * apply CS.equal_genvs_step with (G1:=init_genv prog).
          ** apply init_genv_with_extension_of_partialized_program; auto.
          ** eassumption.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn. auto.
          ** auto.
        * eapply PS.ContextControl;
            try reflexivity.
          ** PS.simplify_turn.
             rewrite Pointer.inc_preserves_component. auto.
      + eapply PS.ContextControl;
          try reflexivity.
        ** PS.simplify_turn.
           rewrite Pointer.inc_preserves_component. auto.

    (* call *)
    (* case analysis on the target *)
    - destruct (PMap.mem C' ctx) eqn:Htarget.
      (* internal call *)
      + eexists. split.
        * eapply PS.partial_step
            with (p':=partialize_program prog (prog_interface pprog)); auto.
          ** apply double_filtering; auto.
          ** apply CS.equal_genvs_step with (G1:=init_genv prog).
             *** apply init_genv_with_extension_of_partialized_program; auto.
             *** eassumption.
          ** eapply PS.ContextControl; auto.
          ** eapply PS.ContextControl; auto.
             *** PS.simplify_turn.
                 apply PMapFacts.mem_in_iff. auto.
             *** match goal with
                 | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
                   PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
                   eapply Memory.equivalence_under_filter;
                   symmetry; apply Hmem_eq
                 end.
        * eapply PS.ContextControl; auto.
          ** PS.simplify_turn.
             apply PMapFacts.mem_in_iff. auto.
          ** match goal with
             | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
               PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
               eapply Memory.equivalence_under_filter;
               symmetry; apply Hmem_eq
             end.
      (* external call *)
      + eexists. split.
        * eapply PS.partial_step
            with (p':=partialize_program prog (prog_interface pprog)); auto.
          ** apply double_filtering; auto.
          ** apply CS.equal_genvs_step with (G1:=init_genv prog).
             *** apply init_genv_with_extension_of_partialized_program; auto.
             *** eassumption.
          ** eapply PS.ContextControl; auto.
          ** eapply PS.ProgramControl; auto.
             *** PS.simplify_turn.
                 apply PMapFacts.not_mem_in_iff. auto.
             *** match goal with
                 | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
                   PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
                   eapply Memory.equivalence_under_filter;
                   symmetry; apply Hmem_eq
                 end.
        * eapply PS.ProgramControl; auto.
          ** PS.simplify_turn.
             apply PMapFacts.not_mem_in_iff. auto.
          ** match goal with
             | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
               PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
               eapply Memory.equivalence_under_filter;
               symmetry; apply Hmem_eq
             end.

    (* return *)
    (* case analysis on the target *)
    - destruct (PMap.mem (Pointer.component pc') ctx) eqn:Htarget.
      (* internal return *)
      + eexists. split.
        * eapply PS.partial_step
            with (p':=partialize_program prog (prog_interface pprog)); auto.
          ** apply double_filtering; auto.
          ** apply CS.equal_genvs_step with (G1:=init_genv prog).
             *** apply init_genv_with_extension_of_partialized_program; auto.
             *** eassumption.
          ** eapply PS.ContextControl; auto.
          ** eapply PS.ContextControl; auto.
             *** PS.simplify_turn.
                 apply PMapFacts.mem_in_iff. auto.
             *** match goal with
                 | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
                   PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
                   eapply Memory.equivalence_under_filter;
                   symmetry; apply Hmem_eq
                 end.
        * eapply PS.ContextControl; auto.
          ** PS.simplify_turn.
             apply PMapFacts.mem_in_iff. auto.
          ** match goal with
             | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
               PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
               eapply Memory.equivalence_under_filter;
               symmetry; apply Hmem_eq
             end.
      (* external return *)
      + eexists. split.
        * eapply PS.partial_step
            with (p':=partialize_program prog (prog_interface pprog)); auto.
          ** apply double_filtering; auto.
          ** apply CS.equal_genvs_step with (G1:=init_genv prog).
             *** apply init_genv_with_extension_of_partialized_program; auto.
             *** eassumption.
          ** eapply PS.ContextControl; auto.
          ** eapply PS.ProgramControl; auto.
             *** PS.simplify_turn.
                 apply PMapFacts.not_mem_in_iff. auto.
             *** match goal with
                 | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
                   PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
                   eapply Memory.equivalence_under_filter;
                   symmetry; apply Hmem_eq
                 end.
        * eapply PS.ProgramControl; auto.
          ** PS.simplify_turn.
             apply PMapFacts.not_mem_in_iff. auto.
          ** match goal with
             | Hmem_eq: PMap.Equal ?MEM1 ?MEM0 |-
               PMap.Equal _ (PMapExtra.filter _ ?MEM1) =>
               eapply Memory.equivalence_under_filter;
               symmetry; apply Hmem_eq
             end.
  Qed.

  Theorem decomposition:
    forward_simulation (CS.sem prog) (PS.sem pprog ctx).
  Proof.
    eapply forward_simulation_step.
    - apply match_initial_states.
    - apply match_final_states.
    - apply lockstep_simulation.
  Qed.

  Corollary decomposition_with_refinement:
    forall beh1, program_behaves (CS.sem prog) beh1 ->
    exists beh2, program_behaves (PS.sem pprog ctx) beh2 /\ behavior_improves beh1 beh2.
  Proof.
    intros beh1 Hbeh1.
    eapply forward_simulation_behavior_improves; eauto.
    apply decomposition.
  Qed.
End Decomposition.

Section DecompositionAndLinking.
  Variable p c: program.

  Hypothesis linkability:
    linkable_programs p c.

  Hypothesis closedness_after_linking:
    closed_program (program_link p c (fst (prog_main p)) (snd (prog_main p))).

  Lemma context_validity:
    part_of (prog_interface c)
            (prog_interface (program_link p c (fst (prog_main p)) (snd (prog_main p)))).
  Proof.
    unfold part_of.
    intros C CI Hin.
    simpl.
    apply PMapExtra.update_mapsto_iff. left.
    assumption.
  Qed.

  Corollary decomposition_with_linking:
    forward_simulation (CS.sem (program_link p c (fst (prog_main p)) (snd (prog_main p))))
                       (PS.sem p (prog_interface c)).
  Proof.
    eapply same_program_forward_simulation.
    - eapply decomposition.
      + apply (linking_well_formedness p c (fst (prog_main p)) (snd (prog_main p))
                                       linkability).
      + assumption.
      + apply context_validity.
    - apply partialize_after_linking; auto.
  Qed.
End DecompositionAndLinking.