Require Import Common.
Require Import Events.
Require Import Machine.
Require Import LTT.
Require Import PLTT.
Require Import Smallstep.

Module LTT_TO_PLTT.

Include AbstractMachine.

Inductive match_states (split : list Component.id)
  : LTT.state -> PLTT.partial_state -> Prop :=
| program_control:
    forall C s ps mem pmem regs pc,
      PLTT.is_program_component C split ->
      ps = PLTT.to_partial_stack s split ->
      PLTT.maps_match_on split mem pmem ->
      match_states split
                   (C, s, mem, regs, pc)
                   (PLTT.PC (C, ps, pmem, regs, pc))

| context_control:
    forall C s ps mem pmem regs pc,
      PLTT.is_context_component C split ->
      ps = PLTT.to_partial_stack s split ->
      PLTT.maps_match_on split mem pmem ->
      match_states split
                   (C, s, mem, regs, pc)
                   (PLTT.CC (C, ps, pmem)).

Hint Constructors match_states.

Section SIMULATION.
  Variable p : LTT.program.
  Variable pp : PLTT.program.
  Variable split : list Component.id.

  (* the split is well-formed w.r.t. to the program interface *)
  Hypothesis splitWF :
    forall C,
      In C split ->
    exists CI,
      In CI (LTT.prog_interface p) /\ Component.name CI = C.

  (* the partial program is obtained by "splitting" the original
     program w.r.t. to split *)
  Hypothesis p_transfto_pp :
    pp = PLTT.apply_split p split splitWF.

  (* build the global environments *)
  Let G := LTT.mkGlobalEnv (LTT.prog_interface p)
                           (LTT.prog_entrypoints p).
  Let G' := PLTT.mkGlobalEnv (LTT.prog_interface p)
                             (LTT.prog_entrypoints p)
                             split.

  Lemma initial_states_match:
    forall s,
      LTT.initial_state p s ->
    exists ps,
      PLTT.initial_state pp ps /\ match_states split s ps.
  Proof.
    intros s Hs_init.
    rewrite p_transfto_pp.
    destruct s
      as [[[[C d] mem] regs] pc] eqn:Hstate_s.
    destruct Hs_init
      as [C_is_0 [empty_stack [empty_regs main_proc]]].
    destruct (Util.mem 0 split) eqn:Hcontrol.
    - exists (PLTT.PC (0, [], mem, regs,
                       EntryPoint.get 0 0 (LTT.genv_entrypoints G))).
      split.
      + unfold PLTT.initial_state.
        split; auto.
      + rewrite C_is_0, empty_stack, empty_regs, main_proc. simpl.
        apply program_control; try auto.
        * unfold PLTT.is_program_component.
          apply Util.in_iff_mem_true. auto.
    - exists (PLTT.CC (0, [], mem)).
      split.
      + unfold PLTT.initial_state.
        split; auto.
      + rewrite C_is_0, empty_stack, empty_regs, main_proc. simpl.
        apply context_control; try auto.
        * unfold PLTT.is_context_component.
          apply Util.not_in_iff_mem_false. auto.
  Qed.

  Lemma final_states_match:
    forall s ps,
      match_states split s ps ->
      LTT.final_state s ->
      PLTT.final_state ps.
  Proof.
    intros s ps Hmatch_states Hs_final.
    destruct s
      as [[[[C d] mem] regs] pc] eqn:Hstate_s.
    destruct Hs_final
      as [empty_stack executing_halt].
    unfold PLTT.final_state.
    inversion Hmatch_states; subst; auto.
  Qed.

  Lemma lockstep_simulation:
    forall s t s',
      LTT.step G s t s' ->
      forall ps,
        match_states split s ps ->
      exists ps',
        PLTT.step G' ps t ps' /\ match_states split s' ps'.
  Proof.
    intros s t s'.
    intros Hstep ps Hmatch_states.

    (* extract the currently executing component memory *)
    destruct (LTT.step_implies_memory_existence G s t s' Hstep)
      as [Cmem HCmem].

    (* useful facts *)
    pose (LTT.prog_entrypoints p) as E.
    pose (LTT.prog_entrypoints_wf p) as EWF.
    assert (HG_unfolded:
              G = {|
                LTT.genv_interfaces := LTT.genv_interfaces G;
                LTT.genv_entrypoints := LTT.genv_entrypoints G
              |}). {
      destruct G. simpl. auto.
    } rewrite HG_unfolded in Hstep.

    (* case analysis on who has control and on the execution *)
    inversion Hmatch_states as
        [ C d pd mem pmem regs pc Hcontrol Hpstack Hmem
        | C d pd mem pmem regs pc Hcontrol Hpstack Hmem ]; subst;
      inversion Hstep; subst;

        (* try to extract the current component interface *)
        try (destruct (splitWF C Hcontrol)
              as [CI [C_in_I CI_name]]);
        (* simplify assumptions about memory *)
        simpl in HCmem;

        (* context epsilon steps (except store) *)
        try (eexists; split;
             [ apply PLTT.Context_Epsilon
             | apply context_control; auto
             ]);

        (* program epsilon steps (except store) *)
        try (eexists; split;
             [ eapply PLTT.Program_Epsilon;
               [ apply HCmem
               | apply HCmem
               | eauto
               | apply Hstep
               | apply Hmem; auto
               | apply HCmem
               ]
             | auto
            ]).

    (* program store *)
    - exists (PLTT.PC (C, PLTT.to_partial_stack d split,
                       Memory.set pmem C
                                  (Register.get r1 regs)
                                  (Register.get r2 regs),
                       regs, pc+1)).
      split.
      (* step *)
      + remember (Memory.local_update
                    (Register.get r1 regs)
                    (Register.get r2 regs) Cmem)
          as updated_Cmem.
        eapply PLTT.Program_Epsilon with
            (s:=d) (cmem:=Cmem)
            (cmem':=updated_Cmem)
            (wmem':=M.add C updated_Cmem mem).
        * apply HCmem.
        * apply M.add_1. reflexivity.
        * unfold PLTT.maps_match_on.
          intros. split; intro; eassumption.
        * unfold Memory.set in Hstep.
          rewrite (M.find_1 HCmem) in Hstep.
          rewrite Hequpdated_Cmem.
          apply Hstep.
        * apply Hmem; assumption.
        * unfold Memory.set.
          apply Hmem in HCmem.
          rewrite (M.find_1 HCmem).
          rewrite Hequpdated_Cmem.
          apply M.add_1.
          ** reflexivity.
          ** assumption.
      (* states match *)
      + apply program_control; auto.
        * apply PLTT.update_related_memories with
              (C:=C) (mem1:=mem) (mem2:=pmem)
              (addr:=Register.get r1 regs)
              (val:=Register.get r2 regs);
            auto.

    (* program is calling *)
    - destruct (in_dec Nat.eq_dec C' split) as [ HC'origin | ? ];
        eexists; split.
      (* internal call - step *)
      + apply PLTT.Program_Internal_Call; auto.
      (* internal call - states match *)
      + destruct (splitWF C' HC'origin)
          as [C'I [C'I_in_I C'I_name_is_C']].
        destruct (EWF C'I C' C'I_in_I C'I_name_is_C')
          as [C'_in_E' [addrs C'_mapsto_E']].
        rewrite EntryPoint.get_on_compatible_entrypoints with
            (E':=E) (addrs:=addrs).
        apply program_control; eauto.
        * simpl.
          apply Util.in_iff_mem_true in Hcontrol.
          rewrite Hcontrol.
          reflexivity.
        * eauto.
        * auto.
      (* external call - step *)
      + apply PLTT.Program_External_Call; auto.
      (* external call - states match *)
      + apply context_control; auto.
        * simpl.
          apply Util.in_iff_mem_true in Hcontrol.
          rewrite Hcontrol.
          reflexivity.

    (* program is returning *)
    - destruct (in_dec Nat.eq_dec C' split)
        as [ HC'origin | HC'origin ];
        eexists; split.
      (* internal return - step *)
      + apply PLTT.Program_Internal_Return; auto.
        * simpl.
          apply Util.in_iff_mem_true in HC'origin.
          rewrite HC'origin. reflexivity.
      (* internal return - states match *)
      + eauto.
      (* external return - step *)
      + apply PLTT.Program_External_Return; auto.
        * simpl.
          apply Util.not_in_iff_mem_false in HC'origin.
          rewrite HC'origin. reflexivity.
      (* external return - states match *)
      + eauto.

    (* context store - states match *)
    - unfold PLTT.maps_match_on.
      intros C' C'mem HC'origin.
      split.
      + intro HC'map.
        apply Hmem; auto.
        * destruct (M.find (elt:=list nat) C mem) eqn:HCfind.
          ** unfold Memory.set in HC'map.
             rewrite HCfind in HC'map.
             apply M.add_3 in HC'map; auto.
             *** unfold not. intros HeqCC'.
                 apply Hcontrol.
                 rewrite <- HeqCC' in HC'origin.
                 apply HC'origin.
          ** unfold Memory.set in HC'map.
             rewrite HCfind in HC'map.
             assumption.
      + intro HC'map.
        assert (HneqCC': C <> C').
        { intro HeqCC'. apply Hcontrol.
          rewrite <- HeqCC' in HC'origin. apply HC'origin. }
        unfold Memory.set.
        destruct (M.find (elt:=list nat) C mem) eqn:HCfind.
        * assert (HC'mem: PLTT.M.MapsTo C' C'mem mem).
          { apply Hmem; assumption. }
          eapply M.add_2; assumption.
        * apply Hmem; auto.

    (* context call is calling *)
    - destruct (in_dec Nat.eq_dec C' split) as [ HC'origin | ? ];
        eexists; split.
      (* external call - step *)
      + apply PLTT.Context_External_Call;
          try assumption.
        * apply PLTT.push_by_context_preserves_partial_stack; eauto.
      (* external call - states match *)
      + destruct (splitWF C' HC'origin)
          as [CI [CI_in_I CI_name_is_C']].
        destruct (EWF CI C' CI_in_I CI_name_is_C')
          as [C'_in_E' [addrs C'_mapsto_E']].
        rewrite EntryPoint.get_on_compatible_entrypoints with
            (E':=E) (addrs:=addrs).
        apply program_control; eauto.
        * eauto.
        * assumption.
      (* internal call - step *)
      + apply PLTT.Context_Internal_Call;
          try assumption.
        * apply PLTT.push_by_context_preserves_partial_stack; eauto.
      (* internal call - states match *)
      + eauto.

    (* context is returning *)
    - destruct (in_dec Nat.eq_dec C' split) as [HC'origin | ?];
        eexists; split.
      (* external return - step*)
      + apply PLTT.Context_External_Return; auto.
        * simpl. apply Util.in_iff_mem_true in HC'origin.
          rewrite HC'origin.
          reflexivity.
      (* external return - states match *)
      + eauto.
      (* internal return - step *)
      + apply PLTT.Context_Internal_Return; auto.
        * apply PLTT.push_by_context_preserves_partial_stack; auto.
      (* internal return - states match *)
      + eauto.
  Qed.

  Theorem forward_simulation_between_LTT_and_PLTT:
    forward_simulation (LTT.semantics p) (PLTT.semantics pp).
  Proof.
    apply Forward_simulation with (match_states split).
    constructor.
    - apply initial_states_match.
    - apply final_states_match.
    - rewrite p_transfto_pp.
      apply lockstep_simulation.
  Qed.
End SIMULATION.
End LTT_TO_PLTT.