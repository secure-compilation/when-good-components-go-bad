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

Theorem option_simulation:
  forall I E EWF split s s' ps t,
  forall (splitWF : split_wf I split),
  forall (memWF : memory_wf I s),
    let G := LTT.mkGlobalEnv I E EWF in

    (* Simulation premises *)
    (LTT.step G s t s' /\ match_states split s ps) ->

    (* Simulation argument *)
    (t = E0 /\ match_states split s' ps) \/
    (exists ps',
        let G' := PLTT.mkGlobalEnv I E split EWF splitWF in
        PLTT.step G' ps t ps' /\ match_states split s' ps').
Proof.
  intros I E EWF split s s' ps t.
  intros splitWF memWF G [Hstep Hmatch_states].

  (* case analysis on who has control and on the execution *)
  inversion Hmatch_states as
      [ C d pd mem pmem regs pc Hcontrol Hpstack Hmem |
        C d pd mem pmem regs pc Hcontrol Hpstack Hmem ]; subst;
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
        | simpl; unfold PLTT.maps_match_on;
          split; intro; eassumption
        | apply Hstep
        | apply Hmem; auto
        | apply HCmem
        ]
      | apply program_control;
        [ assumption
        | reflexivity
        | unfold PLTT.maps_match_on;
          intros; split; intro; assumption
        ]]).

  (* program store *)
  - right.
    exists (PLTT.PC (C, PLTT.to_partial_stack d split,
                     Memory.set pmem C
                                (Register.get r1 regs)
                                (Register.get r2 regs),
                     regs, pc+1)).
    split.
    (* step *)
    + eapply PLTT.Program_Epsilon with
        (s:=d) (cmem:=Cmem)
        (cmem':=Memory.local_update
                  (Register.get r1 regs)
                  (Register.get r2 regs) Cmem)
        (wmem':=M.add C (Memory.local_update
                           (Register.get r1 regs)
                           (Register.get r2 regs) Cmem)
                      mem).
      * apply HCmem.
      * apply M.add_1. reflexivity.
      * unfold PLTT.maps_match_on.
        intros. split; intro; eassumption.
      * unfold Memory.set in Hstep.
        rewrite (M.find_1 HCmem) in Hstep.
        apply Hstep.
      * apply Hmem; assumption.
      * unfold Memory.set.
        apply Hmem in HCmem.
        rewrite (M.find_1 HCmem).
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
      rewrite EntryPoint.get_works_locally with
        (E':=E) (addrs:=addrs).
      apply program_control; eauto.
      * simpl.
        apply Util.in_implies_mem_true in Hcontrol.
        rewrite Hcontrol.
        reflexivity.
      * eauto.
      * auto.
    (* external call - step *)
    + apply PLTT.Program_External_Call; auto.
    (* external call - states match *)
    + apply context_control; auto.
      * simpl.
        apply Util.in_implies_mem_true in Hcontrol.
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
        apply Util.in_implies_mem_true in HC'origin.
        rewrite HC'origin. reflexivity.
    (* internal return - states match *)
    + eauto.
    (* external return - step *)
    + apply PLTT.Program_External_Return; auto.
      * simpl.
        apply Util.not_in_implies_mem_false in HC'origin.
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
      assert (HneqC1C': C <> C').
      { intro HeqCC'. apply Hcontrol.
        rewrite <- HeqCC' in HC'origin. apply HC'origin. }
      unfold Memory.set.
      destruct (M.find (elt:=list nat) C mem) eqn:HC1find.
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
      rewrite EntryPoint.get_works_locally with
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
      * simpl. apply Util.in_implies_mem_true in HC'origin.
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