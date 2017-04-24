Require Import Common.
Require Import Events.
Require Import Machine.
Require Import LTT.
Require Import PLTT.

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

Definition memory_wf (Is : list Component.interface) (s : LTT.state) :=
  match s with
  | (C,d,mem,regs,pc) =>
    forall CI C,
      In CI Is -> Component.name CI = C ->
      exists Cmem, M.MapsTo C Cmem mem
  end.

Definition split_wf (Is : list Component.interface) (split : list Component.id) :=
  forall C,
    In C split ->
    exists CI, In CI Is /\ Component.name CI = C.

(* if entrypoints are well-formed, then they remain
   well-formed even if we consider only the ones relative to the
   components in the split *)
Theorem entrypoints_exist_wrt_split:
  forall (G : LTT.global_env) split
         (splitWF : split_wf (LTT.get_interfaces G) split),
  forall CI C,
    In CI (LTT.get_interfaces G) ->
    Component.name CI = C ->
    In C split ->
    M.In C (LTT.get_entrypoints G) /\
    exists addrs, M.MapsTo C addrs (LTT.get_entrypoints G).
Proof.
  intros G split splitWF.
  intros CI C HCI_in_I HCI_name_is_C HC_in_split.
  apply (LTT.entrypoints_exist G) with CI; assumption.
Qed.

Theorem initial_states_match:
  forall Is E EWF split splitWF s,
    let G := LTT.mkGlobalEnv Is E EWF in
    LTT.initial_state G s ->
    exists ps,
      let EWF' := entrypoints_exist_wrt_split G split splitWF in
      let G' := PLTT.mkGlobalEnv Is E split EWF' splitWF in
      PLTT.initial_state G' ps /\ match_states split s ps.
Proof.
  intros Is E EWF split splitWF s G.
  intros Hinit_s.
  destruct s as [[[[C d] mem] regs] pc] eqn:Hstate_s.
  destruct Hinit_s as [C_is_0 [empty_stack [empty_regs main_proc]]].
  destruct (Util.mem 0 split) eqn:Hcontrol.
  - exists (PLTT.PC (0, [], mem, regs, EntryPoint.get 0 0 E)).
    intro G'. split.
    + unfold PLTT.initial_state.
      split; auto.
    + rewrite C_is_0, empty_stack, empty_regs, main_proc. simpl.
      apply program_control; try auto.
      * unfold PLTT.is_program_component.
        apply Util.in_iff_mem_true. auto.
  - exists (PLTT.CC (0, [], mem)).
    intro G'. split.
    + unfold PLTT.initial_state.
      split; auto.
    + rewrite C_is_0, empty_stack, empty_regs, main_proc. simpl.
      apply context_control; try auto.
      * unfold PLTT.is_context_component.
        apply Util.not_in_iff_mem_false. auto.
Qed.

Theorem final_states_match:
  forall s (split : list Component.id),
    LTT.final_state s ->
    exists ps, PLTT.final_state ps /\ match_states split s ps.
Proof.
  intros s split Hfinal_s.
  destruct s as [[[[C d] mem] regs] pc] eqn:Hstate_s.
  destruct Hfinal_s as [empty_stack executing_halt].
  destruct (Util.mem C split) eqn:Hcontrol.
  - exists (PLTT.PC (C, [], mem, regs, pc)). split.
    + split; auto.
    + subst. apply program_control; auto.
      * apply Util.in_iff_mem_true. auto.
  - exists (PLTT.CC (C, [], mem)). split.
    + split; auto.
    + subst. apply context_control; auto.
      * apply Util.not_in_iff_mem_false. auto.
Qed.

Theorem option_simulation:
  forall I E s s' ps t split,
  (* well-formedness requirements *)
  forall EWF,
  forall (splitWF : split_wf I split),
  forall (memWF : memory_wf I s),
    (* Simulation premises *)
    let G := LTT.mkGlobalEnv I E EWF in
    (LTT.step G s t s' /\ match_states split s ps) ->

    (* Simulation argument *)
    (t = E0 /\ match_states split s' ps) \/
    (exists ps',
        let EWF' := entrypoints_exist_wrt_split G split splitWF in
        let G' := PLTT.mkGlobalEnv I E split EWF' splitWF in
        PLTT.step G' ps t ps' /\ match_states split s' ps').
Proof.
  intros I E s s' ps t split.
  intros EWF splitWF memWF G [Hstep Hmatch_states].

  (* case analysis on who has control and on the execution *)
  inversion Hmatch_states as
      [ C d pd mem pmem regs pc Hcontrol Hpstack Hmem
      | C d pd mem pmem regs pc Hcontrol Hpstack Hmem ]; subst;
    inversion Hstep; subst;

    (* try to extract the current component memory *)
    try (destruct (splitWF C Hcontrol) as [CI [C_in_I CI_name]];
         destruct (memWF CI C C_in_I CI_name) as [Cmem HCmem]);

    (* prove context epsilon steps by staying still *)
    try (left; split;
         [ | apply context_control ];
         auto);

    (* prove program epsilon steps *)
    try (right; eexists; split;
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
  - right.
    exists (PLTT.PC (C, PLTT.to_partial_stack d split,
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
  - right.
    destruct (in_dec Nat.eq_dec C' split) as [ HC'origin | ? ];
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
  - right.
    destruct (in_dec Nat.eq_dec C' split)
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
  - right.
    destruct (in_dec Nat.eq_dec C' split) as [ HC'origin | ? ];
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
  - right.
    destruct (in_dec Nat.eq_dec C' split) as [HC'origin | ?];
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

End LTT_TO_PLTT.