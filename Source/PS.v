Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.

Require Import Coq.Program.Equality.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Module PS.

Import Source.

Definition stack : Type := list (Component.id * option (value * CS.cont)).

Definition program_state : Type := Component.id * stack * Memory.t * CS.cont * expr.
Definition context_state : Type := Component.id * stack * Memory.t.

Inductive state : Type :=
| PC : program_state -> state
| CC : context_state -> state.

Ltac unfold_state st :=
  let C := fresh "C" in
  let pgps := fresh "pgps" in
  let pmem := fresh "pmem" in
  let k := fresh "k" in
  let e := fresh "e" in
  destruct st as [[[[[C pgps] pmem] k] e] | [[C pgps] pmem]].

Ltac unfold_states :=
  repeat match goal with
         | st: state |- _ => unfold_state st
         end.

Definition component_of_state (sps: state) : Component.id :=
  match sps with
  | PC (C, _, _, _, _) => C
  | CC (C, _, _)       => C
  end.

Instance state_turn : HasTurn state := {
  turn_of s iface := component_of_state s \in domm iface
}.

Definition is_context_component (ps: state) ctx := turn_of ps ctx.
Definition is_program_component (ps: state) ctx := negb (is_context_component ps ctx).

Ltac simplify_turn :=
  unfold PS.is_program_component, PS.is_context_component in *;
  unfold turn_of, PS.state_turn in *;
  simpl in *.

(* stack partialization *)

Definition to_partial_frame (ctx: {fset Component.id}) frame : Component.id * option (value * CS.cont) :=
  let '(C, v, k) := frame in
  if C \in ctx then
    (C, None)
  else
    (C, Some (v, k)).

Fixpoint drop_last_frames_if_needed
         (ctx: {fset Component.id}) (s: CS.stack) (Cincontrol: Component.id)
  : CS.stack :=
  match s with
  | [] => []
  | (C, v, k) :: s' =>
    if (C \in ctx) && (Component.eqb C Cincontrol) then
      drop_last_frames_if_needed ctx s' Cincontrol
    else
      s
  end.

Fixpoint to_partial_stack_helper
         (ctx: {fset Component.id}) (s: CS.stack) last_frame
  : PS.stack :=
  match s with
  | [] => [to_partial_frame ctx last_frame]
  | (C, v, k) :: s' =>
    let '(C', v', k') := last_frame in
    if (C \in ctx) && (Component.eqb C C') then
      to_partial_stack_helper ctx s' last_frame
    else
      to_partial_frame ctx last_frame ::
      to_partial_stack_helper ctx s' (C, v, k)
  end.

Lemma to_partial_stack_helper_nonempty:
  forall ctx gps frame,
    ~ to_partial_stack_helper ctx gps frame = [].
Proof.
  intros ctx gps [[C v] k].
  induction gps as [|[[C' v'] k'] gps']; subst; simpl.
  - unfold not. intro. discriminate.
  - destruct (C' \in ctx) eqn:HC'in_ctx;
      rewrite HC'in_ctx; simpl.
    + destruct (Component.eqb C' C) eqn:HC'eqC; auto.
      destruct (C \in ctx) eqn:HCin_ctx;
        rewrite HCin_ctx; simpl.
      * unfold not. intro. discriminate.
      * unfold not. intro. discriminate.
    + destruct (C \in ctx) eqn:HCin_ctx;
        rewrite HCin_ctx; simpl.
      * unfold not. intro. discriminate.
      * unfold not. intro. discriminate.
Qed.

Definition to_partial_stack
          (s: CS.stack) (ctx: {fset Component.id}) (Cincontrol: Component.id) :=
  match drop_last_frames_if_needed ctx s Cincontrol with
  | [] => []
  | last_frame :: s' =>
    to_partial_stack_helper ctx s' last_frame
  end.

(*
Fixpoint to_partial_stack_helper
         (ctx: {fset Component.id}) (s: CS.stack) last_frame (Cincontrol: Component.id)
  : PS.stack :=
  match s with
  | [] => []
  | (C, v, k) :: nil =>
    let '(C', v', k') := last_frame in
    if C \in ctx then
      if Component.eqb C C' then
        if Component.eqb C Cincontrol then
          nil
        else
          to_partial_frame ctx last_frame :: nil
      else
        if Component.eqb C Cincontrol then
          to_partial_frame ctx last_frame :: nil
        else
          to_partial_frame ctx last_frame ::
          to_partial_frame ctx (C, v, k)  :: nil
    else
      to_partial_frame ctx last_frame ::
      to_partial_frame ctx (C, v, k)  :: nil
  | (C, v, k) :: s' =>
    let '(C', v', k') := last_frame in
    if (C \in ctx) && (Component.eqb C C') then
      to_partial_stack_helper ctx s' (C, v, k) Cincontrol
    else
      to_partial_frame ctx last_frame ::
      to_partial_stack_helper ctx s' (C, v, k) Cincontrol
  end.

Definition to_partial_stack
          (s: CS.stack) (ctx: {fset Component.id}) (Cincontrol: Component.id) :=
  match rev s with
  | [] => []
  | first_frame :: s'_rev =>
    rev (to_partial_stack_helper ctx s'_rev first_frame Cincontrol)
  end.

Inductive partial_stack (ctx: {fset Component.id})
  : Component.id -> CS.stack -> PS.stack -> Prop :=
| partial_stack_nil: forall C,
    partial_stack ctx C [] []
| partial_stack_prog_push:
    forall gps pgps C C' f_C f_v f_k,
      f_C \notin ctx ->
      partial_stack ctx C gps pgps ->
      partial_stack ctx C' ((f_C, f_v, f_k) :: gps) ((f_C, Some (f_v, f_k)) :: pgps)
| partial_stack_ctx_push_1:
    forall C f_C f_v f_k,
      f_C \in ctx ->
      Component.eqb f_C C = true ->
      partial_stack ctx C [(f_C, f_v, f_k)] []
| partial_stack_ctx_push_2:
    forall C f_C f_v f_k,
      f_C \in ctx ->
      Component.eqb f_C C = false ->
      partial_stack ctx C [(f_C, f_v, f_k)] [(f_C, None)]
| partial_stack_ctx_push_3:
    forall gps pgps C C' f_C f_v f_k C1,
      f_C \in ctx ->
      partial_stack ctx C gps ((C1, None) :: pgps) ->
      Component.eqb f_C C1 = true ->
      partial_stack ctx C' ((f_C, f_v, f_k) :: gps) ((C1, None) :: pgps)
| partial_stack_ctx_push_4:
    forall gps pgps C C' f_C f_v f_k C1 frame_content,
      f_C \in ctx ->
      partial_stack ctx C gps ((C1, frame_content) :: pgps) ->
      Component.eqb f_C C1 = false ->
      partial_stack ctx C' ((f_C, f_v, f_k) :: gps) ((f_C, None) :: (C1, frame_content) :: pgps).
(* TODO add other cases, then prove equivalence with to_partial_stack *)
*)

Lemma partial_stack_push_by_program:
  forall ctx gps1 gps2 C_incontrol,
    C_incontrol \notin ctx ->
    to_partial_stack gps1 ctx C_incontrol = to_partial_stack gps2 ctx C_incontrol ->
  forall v k C_incontrol',
    to_partial_stack ((C_incontrol, v, k) :: gps1) ctx C_incontrol' =
    to_partial_stack ((C_incontrol, v, k) :: gps2) ctx C_incontrol'.
Proof.
  intros ctx gps1 gps2 C_incontrol Hprog Hsame_stacks.
  intros v k C_incontrol'.

  unfold to_partial_stack in *.
  unfold drop_last_frames_if_needed.
  unfold negb in Hprog.
  destruct (C_incontrol \in ctx) eqn:Hnot_in_ctx;
    try discriminate.
  rewrite Hnot_in_ctx. simpl in *.

  induction gps1 as [|[[C' v'] k'] gps1']; subst; simpl in *.
  - rewrite Hnot_in_ctx.
    induction gps2 as [|[[C' v'] k'] gps2']; subst; simpl in *.
    + rewrite Hnot_in_ctx.
      reflexivity.
    + repeat destruct p.
      destruct (C' \in ctx) eqn:HC'_in_ctx;
        rewrite HC'_in_ctx in Hsame_stacks.
      * assert (Component.eqb C' C_incontrol = false) as HC'neqC. {
          destruct (Component.eqb C' C_incontrol) eqn:H.
          - unfold Component.eqb in H.
            apply Nat.eqb_eq in H. subst.
            rewrite Hnot_in_ctx in HC'_in_ctx.
            discriminate.
          - reflexivity.
        }
        destruct (Component.eqb C' C_incontrol) eqn:Hcontrol;
          try rewrite Hcontrol in Hsame_stacks;
          simpl in *.
        ** rewrite HC'_in_ctx. simpl.
           specialize (IHgps2' Hsame_stacks).
           rewrite IHgps2'.
           reflexivity.
        ** rewrite HC'_in_ctx. simpl.
           rewrite Hnot_in_ctx. rewrite Hsame_stacks.
           reflexivity.
      * rewrite HC'_in_ctx. simpl in *.
        rewrite Hnot_in_ctx.
        rewrite Hsame_stacks. reflexivity.
  - rewrite Hnot_in_ctx.
    induction gps2 as [|[[C'' v''] k''] gps2']; subst; simpl in *.
    + assert (C' \in ctx) as HC'in_ctx. {
        destruct (C' \in ctx) eqn:HC'_in_ctx; auto.
        rewrite HC'_in_ctx in Hsame_stacks.
        simpl in Hsame_stacks.
        exfalso.
        eapply to_partial_stack_helper_nonempty; eauto.
      }
      assert (Component.eqb C' C_incontrol) as HC'eqC_incontrol. {
        destruct (Component.eqb C' C_incontrol) eqn:HC'eqC_incontrol; auto.
        rewrite HC'in_ctx in Hsame_stacks.
        simpl in Hsame_stacks.
        exfalso.
        eapply to_partial_stack_helper_nonempty; eauto.
      }
      assert (drop_last_frames_if_needed ctx gps1' C_incontrol = []) as Hempty_drop. {
        destruct (drop_last_frames_if_needed ctx gps1' C_incontrol) eqn:Hempty_drop; auto.
        rewrite HC'in_ctx HC'eqC_incontrol in Hsame_stacks.
        simpl in Hsame_stacks.
        exfalso.
        eapply to_partial_stack_helper_nonempty; eauto.
      }
      rewrite HC'in_ctx HC'eqC_incontrol. simpl.
      rewrite Hempty_drop in IHgps1'.
      rewrite IHgps1'; auto.
    + (* the hard case *) admit.
Admitted.

Lemma partial_stack_push_by_context:
  forall ctx gps1 gps2 C_incontrol,
    C_incontrol \in ctx ->
    to_partial_stack gps1 ctx C_incontrol = to_partial_stack gps2 ctx C_incontrol ->
  forall v1 k1 v2 k2 C_incontrol',
    to_partial_stack ((C_incontrol, v1, k1) :: gps1) ctx C_incontrol' =
    to_partial_stack ((C_incontrol, v2, k2) :: gps2) ctx C_incontrol'.
Proof.
  intros ctx gps1 gps2 C_incontrol Hctx Hsame_stacks.
  intros v1 k1 v2 k2 C_incontrol'.
  (* this may be slightly harder than the previous one *)
Admitted.

Lemma partial_stack_pop:
  forall ctx last_frame1 gps1 last_frame2 gps2 C_incontrol,
    to_partial_stack (last_frame1 :: gps1) ctx C_incontrol =
    to_partial_stack (last_frame2 :: gps2) ctx C_incontrol ->
  forall C_incontrol',
    to_partial_stack gps1 ctx C_incontrol' = to_partial_stack gps2 ctx C_incontrol'.
Proof.
  intros ctx last_frame1 gps1 last_frame2 gps2 C_incontrol Hsame_stacks C_incontrol'.
  unfold to_partial_stack.
Admitted.

Inductive partial_state (ctx: Program.interface) : CS.state -> PS.state -> Prop :=
| ProgramControl: forall C gps pgps mem pmem k e,
    (* program has control *)
    is_program_component (PC (C, pgps, pmem, k, e)) ctx ->

    (* we forget about context memories *)
    pmem = filterm (fun k _ => negb (k \in domm ctx)) mem ->

    (* we put holes in place of context information in the stack *)
    pgps = to_partial_stack gps (domm ctx) C ->

    partial_state ctx (C, gps, mem, k, e) (PC (C, pgps, pmem, k, e))

| ContextControl: forall C gps pgps mem pmem k e,
    (* context has control *)
    is_context_component (CC (C, pgps, pmem)) ctx ->

    (* we forget about context memories *)
    pmem = filterm (fun k _ => negb (k \in domm ctx)) mem ->

    (* we put holes in place of context information in the stack *)
    pgps = to_partial_stack gps (domm ctx) C ->

    partial_state ctx (C, gps, mem, k, e) (CC (C, pgps, pmem)).

Definition partialize (ctx: Program.interface) (scs: CS.state) : PS.state :=
  let '(C, gps, mem, k, e) := scs in
  let pgps := to_partial_stack gps (domm ctx) C in
  let pmem := filterm (fun k _ => negb (k \in domm ctx)) mem in
  if C \in domm ctx then CC (C, pgps, pmem)
  else PC (C, pgps, pmem, k, e).

Lemma partialize_correct:
  forall scs sps ctx,
    partialize ctx scs = sps <-> partial_state ctx scs sps.
Proof.
  intros scs sps ctx.
  split.
  - intros Hpartialize.
    CS.unfold_states. unfold partialize in *.
    destruct (C \in domm ctx) eqn:Hwhere;
      rewrite <- Hpartialize.
    + constructor;
        try reflexivity.
      * PS.simplify_turn. assumption.
    + constructor;
        try reflexivity.
      * PS.simplify_turn. rewrite Hwhere. auto.
  - intros Hpartial_state.
    inversion Hpartial_state; subst.
    + PS.simplify_turn.
      unfold negb in H.
      destruct (C \in domm ctx) eqn:Hwhere.
      * rewrite Hwhere in H. inversion H.
      * rewrite Hwhere. reflexivity.
    + PS.simplify_turn.
      rewrite H. reflexivity.
Qed.

(* transition system *)

Inductive initial_state (p: program) (ctx: Program.interface) : state -> Prop :=
| initial_state_intro: forall p' scs sps,
    prog_interface p' = ctx ->
    linkable_programs p p' ->
    partial_state ctx scs sps ->
    CS.initial_state (program_link p p') scs ->
    initial_state p ctx sps.

Inductive final_state (p: program) (ctx: Program.interface) : state -> Prop :=
| final_state_program: forall p' scs sps,
    prog_interface p' = ctx ->
    linkable_programs p p' ->
    ~ turn_of sps ctx ->
    partial_state ctx scs sps ->
    CS.final_state scs ->
    final_state p ctx sps
| final_state_context: forall sps,
    turn_of sps ctx ->
    final_state p ctx sps.

Inductive kstep (p: program) (ctx: Program.interface)
  : global_env -> state -> trace -> state -> Prop :=
| partial_step:
    forall p' sps t sps' scs scs',
      prog_interface p' = ctx ->
      linkable_programs p p' ->
      CS.kstep (prepare_global_env (program_link p p')) scs t scs' ->
      partial_state ctx scs sps ->
      partial_state ctx scs' sps' ->
      kstep p ctx (prepare_global_env p) sps t sps'.

Lemma state_determinism_program:
  forall p ctx G sps t sps',
    is_program_component sps ctx ->
    kstep p ctx G sps t sps' ->
  forall sps'',
    kstep p ctx G sps t sps'' ->
    sps' = sps''.
Proof.
  intros p ctx G sps t sps' Hcontrol Hstep1 sps'' Hstep2.

  inversion Hstep1
    as [p1 sps1 t1 sps1' scs1 scs1' Hiface1 Hlink1 Hkstep1 Hpartial_sps1 Hpartial_sps1'];
    subst.
  inversion Hstep2
    as [p2 sps2 t2 sps2' scs2 scs2' Hiface2 Hlink2 Hkstep2 Hpartial_sps2 Hpartial_sps2'];
    subst.

  (* case analysis on who has control *)
  inversion Hpartial_sps1; subst.
  - inversion Hpartial_sps2; subst;
    inversion Hkstep1; subst; inversion Hkstep2; subst;
    inversion Hpartial_sps1'; subst; inversion Hpartial_sps2'; subst; PS.simplify_turn;
      try (match goal with
           | Hstack: to_partial_stack ?GPS1 _ _ = to_partial_stack ?GPS2 _ _,
             Hmem: filterm ?PRED ?MEM1 = filterm ?PRED ?MEM2 |- _ =>
             rewrite Hstack Hmem
           end);
      try reflexivity;
      try (match goal with
           | Hin: context[domm (prog_interface p1)],
             Hnotin: context[domm (prog_interface p1)] |- _ =>
             rewrite Hin in Hnotin; discriminate
           end);
      try omega.

    (* local *)
    + (* show that b and b0 are the same *)
      admit.

    (* alloc *)
    + (* show that memory changes in the same way *)
      admit.

    (* deref *)
    + (* show that the loaded value is the same (v == v0) *)
      admit.

    (* assign *)
    + (* show that memory changes in the same way *)
      admit.

    (* call *)

    (* inside the same component *)
    + (* show stack and memory are changing in the same way *)
      admit.
    (* internal *)
    + unfold to_partial_stack. simpl.
      (* show stack and memory are changing in the same way *)
      admit.
    (* external *)
    + admit.

    (* return *)

    (* inside the same component *)
    + (* show stack and memory are changing in the same way *)
      admit.
    (* internal *)
    + unfold to_partial_stack. simpl.
      (* show stack and memory are changing in the same way *)
      admit.
    (* external *)
    + admit.

  - PS.simplify_turn.
    match goal with
    | Hin: context[domm (prog_interface p1)],
      Hnotin: context[domm (prog_interface p1)] |- _ =>
      rewrite Hin in Hnotin; discriminate
    end.
Admitted.

Lemma context_allocation_gets_filtered:
  forall (ctx: {fset Component.id}) mem C size mem' ptr,
    Memory.alloc mem C size = Some (mem', ptr) ->
    filterm (fun k _ => k \notin ctx) mem' = filterm (fun k _ => k \notin ctx) mem.
Proof.
Admitted.

Lemma context_store_gets_filtered:
  forall (ctx: {fset Component.id}) mem C b o v mem',
    Memory.store mem (C, b, o) v = Some mem' ->
    filterm (fun k _ => k \notin ctx) mem' = filterm (fun k _ => k \notin ctx) mem.
Proof.
Admitted.

Lemma context_epsilon_step_is_silent:
  forall p ctx G sps sps',
    is_context_component sps ctx ->
    kstep p ctx G sps E0 sps' ->
    sps = sps'.
Proof.
  intros p ctx G sps sps' Hcontrol Hkstep.

  inversion Hkstep
    as [p' ? ? ? scs scs' Hiface Hlink Hcs_kstep Hpartial_sps Hpartial_sps'];
    subst.

  inversion Hpartial_sps; subst; PS.simplify_turn.

  (* the program has control (contra) *)
  - match goal with
    | Hin: context[domm (prog_interface p')],
      Hnotin: context[domm (prog_interface p')] |- _ =>
      rewrite Hin in Hnotin; discriminate
    end.

  (* the context has control (assumption) *)
  - inversion Hcs_kstep; subst;
    inversion Hpartial_sps'; subst; PS.simplify_turn;
      try (match goal with
           | Hin: context[domm (prog_interface p')],
             Hnotin: context[domm (prog_interface p')] |- _ =>
             rewrite Hin in Hnotin; discriminate
           end);
      try reflexivity.

    (* alloc *)
    + erewrite context_allocation_gets_filtered with (mem':=mem'); eauto.

    (* assign *)
    + erewrite context_store_gets_filtered with (mem':=mem'); eauto.

    (* same component call *)
    + erewrite context_store_gets_filtered with (mem':=mem'); eauto.
      (* work on stack partialization *)
      admit.

    (* same component return *)
    + erewrite context_store_gets_filtered with (mem':=mem'); eauto.
      (* work on stack partialization *)
      admit.
Admitted.

Lemma context_epsilon_star_is_silent:
  forall p ctx G sps sps',
    is_context_component sps ctx ->
    star (kstep p ctx) G sps E0 sps' ->
    sps = sps'.
Proof.
  intros p ctx G sps sps' Hcontrol Hstar.
  dependent induction Hstar; subst.
  - reflexivity.
  - symmetry in H0. apply Eapp_E0_inv in H0.
    destruct H0 as []. subst.
    apply context_epsilon_step_is_silent in H; auto. subst.
    apply IHHstar; auto.
Qed.

Lemma state_determinism_context:
  forall p ctx G sps t sps',
    is_context_component sps ctx ->
    kstep p ctx G sps t sps' ->
  forall sps'',
    kstep p ctx G sps t sps'' ->
    sps' = sps''.
Proof.
  intros p ctx G sps t sps' Hcontrol Hstep1 sps'' Hstep2.

  inversion Hstep1
    as [p1 sps1 t1 sps1' scs1 scs1' Hiface1 Hlink1 Hkstep1 Hpartial_sps1 Hpartial_sps1'];
    subst.
  inversion Hstep2
    as [p2 sps2 t2 sps2' scs2 scs2' Hiface2 Hlink2 Hkstep2 Hpartial_sps2 Hpartial_sps2'];
    subst.

  (* case analysis on who has control *)
  inversion Hpartial_sps1; subst.
  - PS.simplify_turn.
    match goal with
    | Hin: context[domm (prog_interface p1)],
      Hnotin: context[domm (prog_interface p1)] |- _ =>
      rewrite Hin in Hnotin; discriminate
    end.

  - inversion Hpartial_sps2; subst.
    inversion Hkstep1; subst;
      try (rewrite <- (context_epsilon_step_is_silent H Hstep1);
           rewrite <- (context_epsilon_step_is_silent H4 Hstep2);
           simpl; reflexivity).

    (* internal & external call *)
    + inversion Hkstep2; subst.
      inversion Hpartial_sps1'; subst;
      inversion Hpartial_sps2'; subst; PS.simplify_turn.
      * (* same memory *)
        rewrite (context_store_gets_filtered (domm (prog_interface p1)) H16).
        rewrite (context_store_gets_filtered (domm (prog_interface p1)) H25).
        rewrite H5. simpl.
        (* same expression *)
        unfold find_procedure in H10, H21.
        rewrite unionmE in H10.
        rewrite unionmE in H21.
        destruct (isSome ((prog_procedures p) C')) eqn:Hwhere;
          try discriminate.
        *** rewrite Hwhere in H10, H21.
            destruct ((prog_procedures p) C') eqn:Hwhat;
              try discriminate.
            rewrite H10 in H21. inversion H21; subst.
            (* same stack *)
            admit.
        *** rewrite Hwhere in H10, H21.
            (* C' is not in p1's interface,
               C' is not in p1's procedures by well-formedness of p1 (from linkability),
               contradiction *)
            inversion Hlink1; subst.
            pose proof (wfprog_well_formed_procedures_1 p1 H1) as Hp1_wfprocs.
            admit.
      * match goal with
        | Hin: context[domm (prog_interface p1)],
          Hnotin: context[domm (prog_interface p1)] |- _ =>
          rewrite Hin in Hnotin; discriminate
        end.
      * match goal with
        | Hin: context[domm (prog_interface p1)],
          Hnotin: context[domm (prog_interface p1)] |- _ =>
          rewrite Hin in Hnotin; discriminate
        end.
      * (* same memory *)
        rewrite (context_store_gets_filtered (domm (prog_interface p1)) H16).
        rewrite (context_store_gets_filtered (domm (prog_interface p1)) H25).
        rewrite H5. simpl.
        (* same stack *)
        admit.

    (* internal & external return *)
    + inversion Hkstep2; subst.
      inversion Hpartial_sps1'; subst;
      inversion Hpartial_sps2'; subst; PS.simplify_turn.
      * (* same memory *)
        rewrite (context_store_gets_filtered (domm (prog_interface p1)) H12).
        rewrite (context_store_gets_filtered (domm (prog_interface p1)) H16).
        rewrite H5. simpl.
        (* same stack *)
        (*erewrite partial_stack_pop*)
        admit.
      * match goal with
        | Hin: context[domm (prog_interface p1)],
          Hnotin: context[domm (prog_interface p1)] |- _ =>
          rewrite Hin in Hnotin; discriminate
        end.
      * match goal with
        | Hin: context[domm (prog_interface p1)],
          Hnotin: context[domm (prog_interface p1)] |- _ =>
          rewrite Hin in Hnotin; discriminate
        end.
      * (* same memory *)
        rewrite (context_store_gets_filtered (domm (prog_interface p1)) H12).
        rewrite (context_store_gets_filtered (domm (prog_interface p1)) H16).
        rewrite H5. simpl.
        (* same stack *)
        (*erewrite partial_stack_pop;
          try reflexivity;
          try eassumption.*)
        admit.
Admitted.

Theorem state_determinism:
  forall p ctx G sps t sps',
    kstep p ctx G sps t sps' ->
  forall sps'',
    kstep p ctx G sps t sps'' ->
    sps' = sps''.
Proof.
  intros p ctx G sps t sps' Hstep1 sps'' Hstep2.

  inversion Hstep1
    as [p1 sps1 t1 sps1' scs1 scs1' Hiface1 Hlink1 Hkstep1 Hpartial_sps1 Hpartial_sps1'];
    subst.
  inversion Hstep2
    as [p2 sps2 t2 sps2' scs2 scs2' Hiface2 Hlink2 Hkstep2 Hpartial_sps2 Hpartial_sps2'];
    subst.

  (* case analysis on who has control *)
  inversion Hpartial_sps1; subst.
  - eapply state_determinism_program; eauto.
  - eapply state_determinism_context; eauto.
Qed.

Corollary state_determinism_star:
  forall p ctx G sps t sps' sps'',
    star (kstep p ctx) G sps t sps' ->
    star (kstep p ctx) G sps t sps'' ->
    sps' = sps''.
Proof.
  intros p ctx G sps t sps' sps'' Hstar1 Hstar2.
  (* by induction + state determinism *)
  (* case analysis on who has control (in sps) *)
  PS.unfold_state sps.

  (*** program has control ***)
  - induction Hstar1; subst.
    + inversion Hstar2; subst.
      * reflexivity.
      * symmetry in H1. apply Eapp_E0_inv in H1.
        destruct H1 as []. subst.
        admit.
    + inversion Hstar2; subst.
      * symmetry in H2. apply Eapp_E0_inv in H2.
        destruct H2 as []. subst.
        admit.
      * admit.

  (*** context has control ***)
  - induction Hstar1; subst.
    + inversion Hstar2; subst.
      * reflexivity.
      * symmetry in H1. apply Eapp_E0_inv in H1.
        destruct H1 as []. subst.
        apply context_epsilon_step_is_silent in H; subst.
        ** apply context_epsilon_star_is_silent in Hstar2; subst.
           *** reflexivity.
           *** admit.
        ** admit.
    + admit.
Admitted.

(* partial semantics *)
Section Semantics.
  Variable p: program.
  Variable ctx: Program.interface.

  Hypothesis valid_program:
    well_formed_program p.

  Hypothesis disjoint_interfaces:
    fdisjoint (domm (prog_interface p)) (domm ctx).

  Hypothesis merged_interface_is_closed:
    closed_interface (unionm (prog_interface p) ctx).

  Definition sem :=
    @Semantics_gen state global_env (kstep p ctx)
                   (initial_state p ctx)
                   (final_state p ctx) (prepare_global_env p).
End Semantics.
End PS.
