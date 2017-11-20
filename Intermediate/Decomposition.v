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
  Variable prog: program.
  Variable ctx: Program.interface.

  (*
  Hypothesis input_program_closedness:
    closed_program prog.
   *)

  (* might be useful in the future
  Hypothesis context_validity:
    forall C CI,
      PMap.MapsTo C CI ctx -> PMap.MapsTo C CI (prog_interface prog).
   *)

  (* Might be useful in the future:
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
   *)

  Let G: global_env := init_genv prog.

  Lemma match_initial_states:
    forall ics,
      CS.initial_state prog ics ->
    exists ips,
      PS.initial_state prog ctx ips /\ PS.partial_state ctx ics ips.
  Proof.
    intros ics Hics_init.
    CS.unfold_states.
    (* case analysis on who has control, then build the partial state *)
    destruct (PMap.mem (Pointer.component pc) ctx) eqn:Htarget;
      exists (PS.partialize (s, mem, regs, pc) ctx);
      simpl; rewrite Htarget.
    (* context has control *)
    - split.
      + econstructor.
        * eapply PS.ContextControl; eauto.
          ** PS.simplify_turn.
             apply PMapFacts.mem_in_iff. auto.
          ** apply PMapFacts.Equal_refl.
        * eauto.
      + eapply PS.ContextControl; eauto.
        ** PS.simplify_turn.
           apply PMapFacts.mem_in_iff. auto.
        ** apply PMapFacts.Equal_refl.
    (* program has control *)
    - split.
      + econstructor.
        * eapply PS.ProgramControl; auto.
          ** PS.simplify_turn.
             apply PMapFacts.not_mem_in_iff. auto.
          ** apply PMapFacts.Equal_refl.
        * eauto.
      + eapply PS.ProgramControl; auto.
        ** PS.simplify_turn.
           apply PMapFacts.not_mem_in_iff. auto.
        ** apply PMapFacts.Equal_refl.
  Qed.

  Lemma match_final_states:
    forall ics ips,
      PS.partial_state ctx ics ips ->
      CS.final_state G ics ->
      PS.final_state prog ctx ips.
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
      + eapply PS.final_state_program.
        * PS.simplify_turn. auto.
        * eauto.
        * eauto.
      + apply PMapFacts.not_mem_in_iff in Htarget.
        contradiction.
  Qed.

  Lemma lockstep_simulation:
    forall ics t ics',
      CS.step G ics t ics' ->
    forall ips,
      PS.partial_state ctx ics ips ->
    exists ips',
      PS.step ctx G ips t ips' /\ PS.partial_state ctx ics' ips'.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
        * econstructor; auto.
          ** apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
        * econstructor; auto.
          ** apply Hstep.
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
        * econstructor; auto.
          ** apply Hstep.
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
        * econstructor; auto.
          ** apply Hstep.
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
        * econstructor; auto.
          ** apply Hstep.
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
        * econstructor; auto.
          ** apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
      + econstructor; auto.
        * apply Hstep.
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
        * econstructor; auto.
          ** apply Hstep.
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
        * econstructor; auto.
          ** apply Hstep.
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
        * econstructor; auto.
          ** apply Hstep.
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
        * econstructor; auto.
          ** apply Hstep.
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
    forward_simulation (CS.sem prog) (PS.sem prog ctx).
  Proof.
    eapply forward_simulation_step.
    - apply match_initial_states.
    - apply match_final_states.
    - apply lockstep_simulation.
  Qed.

  Corollary decomposition_with_refinement:
    forall beh1, program_behaves (CS.sem prog) beh1 ->
    exists beh2, program_behaves (PS.sem prog ctx) beh2 /\ behavior_improves beh1 beh2.
  Proof.
    intros beh1 Hbeh1.
    eapply forward_simulation_behavior_improves; eauto.
    apply decomposition.
  Qed.
End Decomposition.

Section DecompositionAndLinking.
  Variable p c: program.
  Variable mainC: Component.id.
  Variable mainP: Procedure.id.

  Corollary decomposition_with_linking:    
    forward_simulation (CS.sem (program_link p c mainC mainP))
                       (PS.sem (program_link p c mainC mainP)
                               (prog_interface c)).
  Proof.
    apply decomposition.
  Qed.
End DecompositionAndLinking.