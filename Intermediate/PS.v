Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.

Require Import Coq.Program.Equality.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Module PS.

Import Intermediate.

Module PartialPointer.
  Definition t : Type := Component.id * option (Block.id * Block.offset).
End PartialPointer.

Lemma partial_pointer_to_pointer_eq :
  forall pt1 pt2,
    (Pointer.component pt1, Some (Pointer.block pt1, Pointer.offset pt1)) =
    (Pointer.component pt2, Some (Pointer.block pt2, Pointer.offset pt2)) ->
    pt1 = pt2.
Proof. by move=> [[??]?] [[??]?] [-> -> ->]. Qed.

Definition stack := list PartialPointer.t.

Definition program_state : Type := stack * Memory.t * Register.t * Pointer.t.
Definition context_state : Type := Component.id * stack * Memory.t.

Inductive state : Type :=
| PC : program_state -> state
| CC : context_state -> state.

Definition state_component (ps: state) : Component.id :=
  match ps with
  | PC (_, _, _, pc) => Pointer.component pc
  | CC (C, _, _) => C
  end.

Definition state_memory (ps: state) : Memory.t :=
  match ps with
  | PC (_, mem, _, _) => mem
  | CC (_, _, mem) => mem
  end.

Definition state_stack (ps: state) : stack :=
  match ps with
  | PC (gps, _, _, _) => gps
  | CC (_, gps, _) => gps
  end.

Ltac unfold_state st :=
  match goal with
    |- _ => let pgps := fresh "pgps" in
            let pmem := fresh "pmem" in
            let regs := fresh "regs" in
            let pc := fresh "pc" in
            let comp := fresh "C" in
            destruct st as [[[[pgps pmem] regs] pc] | [[comp pgps] pmem]]
  end.

Ltac unfold_states :=
  repeat (match goal with
          | st: state |- _ => unfold_state st
          end).

Instance state_turn : HasTurn state := {
  turn_of s iface :=
    match s with
    | PC (_, _, _, pc) => Pointer.component pc \in domm iface
    | CC (C, _, _) => C \in domm iface
    end
}.

Definition is_context_component (ps: state) ctx := turn_of ps ctx.
Definition is_program_component (ps: state) ctx := negb (is_context_component ps ctx).

Ltac simplify_turn :=
  unfold PS.is_program_component, PS.is_context_component in *;
  unfold turn_of, PS.state_turn in *;
  simpl in *.

Remark pc_component_not_in_ctx:
  forall stk mem regs pc ctx,
    is_program_component (PC (stk, mem, regs, pc)) ctx ->
    Pointer.component pc \notin domm ctx.
Proof.
  intros stk mem regs pc ctx Hpc.
  simplify_turn.
  assumption.
Qed.

Remark cc_component_in_ctx:
  forall cid stk mem ctx,
    is_context_component (CC (cid, stk, mem)) ctx ->
    cid \in domm ctx.
Proof.
  intros cid stk mem ctx Hcc.
  simplify_turn.
  assumption.
Qed.

(* stack partialization *)

Definition to_partial_frame (ctx: {fset Component.id}) frame : PartialPointer.t :=
  if Pointer.component frame \in ctx then
    (Pointer.component frame, None)
  else
    (Pointer.component frame, Some (Pointer.block frame, Pointer.offset frame)).

Definition to_partial_stack (s : CS.stack) (ctx: {fset Component.id}) :=
  map (to_partial_frame ctx) s.

Lemma ptr_within_partial_frame_1 (ctx: Program.interface):
  forall ptr,
    Pointer.component ptr \in domm ctx = true ->
    to_partial_frame (domm ctx) ptr = (Pointer.component ptr, None).
Proof.
  intros ptr Hin_ctx.
  unfold to_partial_frame, Pointer.inc, Pointer.add.
  destruct ptr as [[C b] o]. simpl in *.
  rewrite Hin_ctx. reflexivity.
Qed.

Lemma ptr_within_partial_frame_2 (ctx: Program.interface):
  forall ptr,
    Pointer.component ptr \in domm ctx = false ->
    to_partial_frame (domm ctx) ptr
    = (Pointer.component ptr, Some (Pointer.block ptr, Pointer.offset ptr)).
Proof.
  intros ptr Hnot_in_ctx.
  unfold to_partial_frame, Pointer.inc, Pointer.add.
  destruct ptr as [[C b] o]. simpl in *.
  rewrite Hnot_in_ctx. reflexivity.
Qed.

Lemma to_partial_frame_with_empty_context:
  forall C b o,
    to_partial_frame fset0 (C, b, o) = (C, Some (b, o)).
Proof.
  intros. reflexivity.
Qed.

Lemma to_partial_stack_with_empty_context:
  forall gps1 gps2,
    to_partial_stack gps1 fset0 = to_partial_stack gps2 fset0 ->
    gps1 = gps2.
Proof.
  intros.
  generalize dependent gps2.
  induction gps1.
  - destruct gps2.
    + reflexivity.
    + discriminate.
  - intros.
    induction gps2.
    + discriminate.
    + simpl in *.
      inversion H; subst.
      destruct a as [[]]. destruct a0 as [[]].
      simpl in *. subst.
      rewrite (IHgps1 gps2); auto.
Qed.

Inductive partial_state (ctx: Program.interface) : CS.state -> PS.state -> Prop :=
| ProgramControl: forall gps pgps mem pmem regs pc,
    (* program has control *)
    is_program_component (PC (pgps, pmem, regs, pc)) ctx ->

    (* we forget about context memories *)
    pmem = filterm (fun k _ => negb (k \in domm ctx)) mem ->

    (* we put holes in place of context information in the stack *)
    pgps = to_partial_stack gps (domm ctx) ->

    partial_state ctx (gps, mem, regs, pc) (PC (pgps, pmem, regs, pc))

| ContextControl: forall gps pgps mem pmem regs pc,
    (* context has control *)
    is_context_component (CC (Pointer.component pc, pgps, pmem)) ctx ->

    (* we forget about context memories *)
    pmem = filterm (fun k _ => negb (k \in domm ctx)) mem ->

    (* we put holes in place of context information in the stack *)
    pgps = to_partial_stack gps (domm ctx) ->

    partial_state ctx (gps, mem, regs, pc) (CC (Pointer.component pc, pgps, pmem)).

Definition partialize (ics: CS.state) (ctx: Program.interface) : PS.state :=
  let '(gps, mem, regs, pc) := ics in
  if Pointer.component pc \in domm ctx then
    CC (Pointer.component pc,
        to_partial_stack gps (domm ctx),
        filterm (fun k _ => negb (k \in domm ctx)) mem)
  else
    PC (to_partial_stack gps (domm ctx),
        filterm (fun k _ => negb (k \in domm ctx)) mem,
        regs, pc).

Lemma partialize_correct:
  forall ics ips ctx,
    partialize ics ctx = ips <-> partial_state ctx ics ips.
Proof.
  intros ics ips ctx.
  split.
  - intros Hpartialize.
    CS.unfold_states. simpl in *.
    destruct (Pointer.component pc \in domm ctx) eqn:Hcontrol;
      rewrite Hcontrol in Hpartialize; rewrite <- Hpartialize.
    + constructor; try reflexivity.
      * PS.simplify_turn. assumption.
    + constructor; try reflexivity.
      * PS.simplify_turn. rewrite Hcontrol. reflexivity.
  - intros Hpartial_state.
    inversion Hpartial_state; subst; PS.simplify_turn.
    + destruct (Pointer.component pc \in domm ctx) eqn:Hcontrol.
      * rewrite Hcontrol in H. discriminate.
      * rewrite Hcontrol.
        reflexivity.
    + rewrite H.
      reflexivity.
Qed.

Lemma partialized_state_is_partial:
  forall ics ctx,
    partial_state ctx ics (partialize ics ctx).
Proof.
  intros ics ctx.
  apply partialize_correct.
  reflexivity.
Qed.

(* unpartializing partial states without holes *)

Definition unpartialize_stack_frame (frame: PartialPointer.t): Pointer.t :=
  match frame with
  | (C, None) =>
    (* bad case that shouldn't happen, just return first state *)
    (C, 1, 0%Z)
  | (C, Some (b, o)) => (C, b, o)
  end.

Definition unpartialize_stack (pgps: stack): CS.stack :=
  map unpartialize_stack_frame pgps.

Definition unpartialize (ips: state): CS.state :=
  match ips with
  | PC (pgps, mem, regs, pc) =>
    (unpartialize_stack pgps, mem, regs, pc)
  | CC _ =>
    (* bad case that shouldn't happen, return bogus state *)
    ([], emptym, emptym, (0, 0, 0%Z))
  end.

Inductive stack_without_holes: stack -> Prop :=
| stack_without_holes_nil:
    stack_without_holes nil
| stack_without_holes_cons: forall pgps C b o,
    stack_without_holes pgps ->
    stack_without_holes ((C, Some (b, o)) :: pgps).

Lemma to_partial_stack_with_empty_context_has_no_holes:
  forall gps,
    stack_without_holes (to_partial_stack gps fset0).
Proof.
  intros gps.
  induction gps.
  - simpl. constructor.
  - simpl.
    destruct a. destruct p.
    rewrite to_partial_frame_with_empty_context.
    econstructor; auto.
Qed.

Lemma to_partial_stack_unpartialize_identity:
  forall pgps,
    stack_without_holes pgps ->
    to_partial_stack (unpartialize_stack pgps) fset0 = pgps.
Proof.
  intros pgps Hnoholes.
  induction Hnoholes; subst.
  - reflexivity.
  - simpl. rewrite IHHnoholes. reflexivity.
Qed.

Lemma unpartializing_complete_stack_frame:
  forall frame,
    unpartialize_stack_frame (to_partial_frame fset0 frame) = frame.
Proof.
  intros frame.
  destruct frame as [[C b] o].
  reflexivity.
Qed.

Lemma unpartializing_complete_stack:
  forall stack,
    unpartialize_stack (to_partial_stack stack fset0) = stack.
Proof.
  intros stack.
  induction stack; simpl.
  - reflexivity.
  - rewrite IHstack.
    destruct a as [[]].
    reflexivity.
Qed.

Theorem unpartializing_complete_states:
  forall ics,
    unpartialize (partialize ics emptym) = ics.
Proof.
  intros ics.
  CS.unfold_states. simpl.
  rewrite mem_domm. simpl.
  rewrite domm0.
  rewrite unpartializing_complete_stack.
  rewrite filterm_identity. reflexivity.
Qed.

(* merging partial states *)

Inductive mergeable_stack_frames: PartialPointer.t -> PartialPointer.t -> Prop :=
| mergeable_stack_frames_first: forall C1 b1 o1 C2,
    C1 = C2 ->
    mergeable_stack_frames (C1, Some (b1, o1)) (C2, None)
| mergeable_stack_frames_second: forall C1 C2 b2 o2,
    C1 = C2 ->
    mergeable_stack_frames (C1, None) (C1, Some (b2, o2)).

Inductive mergeable_stacks : stack -> stack -> Prop :=
| mergeable_stacks_nil:
    mergeable_stacks [] []
| mergeable_stacks_cons: forall pgps1 pgps2 frame1 frame2,
    mergeable_stacks pgps1 pgps2 ->
    mergeable_stack_frames frame1 frame2 ->
    mergeable_stacks (frame1 :: pgps1) (frame2 :: pgps2).

Definition mergeable_memories (mem1 mem2: Memory.t): Prop :=
  fdisjoint (domm mem1) (domm mem2).

Definition mergeable_interfaces (ctx1 ctx2: Program.interface) : Prop :=
  linkable ctx1 ctx2 /\
  closed_interface (unionm ctx1 ctx2).

Lemma mergeable_interfaces_sym ctx1 ctx2 :
  mergeable_interfaces ctx1 ctx2 ->
  mergeable_interfaces ctx2 ctx1.
Proof.
  intros [Hlinkable Hclosed].
  split.
  - apply (linkable_sym Hlinkable).
  - apply (closed_interface_sym _ _ Hclosed).
Qed.

(* NOTE: Instance of a more general property which may be added to CoqUtils.
   TODO: Harmonize naming of two directions or unify with iff.
         Add domain conditions to the following lemmas.
         Reduce amount of lemmas, possibly supplement with tactics. *)
(* XXX: This result is false without assuming more hypotheses about C: it is
        equivalent to saying that if two interfaces are mergeable then every
        component belongs to one of them. *)
Lemma domm_partition :
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall C,
    C \notin domm ctx2 ->
    C \in domm ctx1.
Admitted. (* Rank 1. *)

Lemma domm_partition_notin :
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall C,
    C \in domm ctx2 ->
    C \notin domm ctx1.
Admitted. (* Rank 1. *)

Inductive mergeable_states_pc_cc: state -> state -> Prop :=
| mergeable_states_pc_cc_first: forall gps1 mem1 regs1 pc1 C2 gps2 mem2,
    mergeable_states_pc_cc (PC (gps1, mem1, regs1, pc1)) (CC (C2, gps2, mem2))
| mergeable_states_pc_cc_second: forall C1 gps1 mem1 gps2 mem2 regs2 pc2,
    mergeable_states_pc_cc (CC (C1, gps1, mem1)) (PC (gps2, mem2, regs2, pc2)).
Lemma domm_partition_in_both ctx1 ctx2 C :
  mergeable_interfaces ctx1 ctx2 ->
  C \in domm ctx1 ->
  C \in domm ctx2 ->
  False.
Admitted. (* Rank 1. *)

Lemma domm_partition_in_neither ctx1 ctx2 C :
  mergeable_interfaces ctx1 ctx2 ->
  C \notin domm ctx1 ->
  C \notin domm ctx2 ->
  False.
Admitted. (* Rank 1. *)

Inductive mergeable_states (ctx1 ctx2: Program.interface): state -> state -> Prop :=
| mergeable_states_intro: forall ics ips1 ips2,
    mergeable_interfaces ctx1 ctx2 ->
    CS.comes_from_initial_state ics ->
    partial_state ctx1 ics ips1 ->
    partial_state ctx2 ics ips2 ->
    mergeable_states ctx1 ctx2 ips1 ips2.

Lemma mergeable_stack_frames_sym:
  forall frame1 frame2,
    mergeable_stack_frames frame1 frame2 ->
    mergeable_stack_frames frame2 frame1.
Proof.
  intros.
  inversion H; subst;
    econstructor; auto.
Qed.

Lemma mergeable_stacks_sym:
  forall pgps1 pgps2,
    mergeable_stacks pgps1 pgps2 ->
    mergeable_stacks pgps2 pgps1.
Proof.
  intros pgps1 pgps2 Hmergeable.
  induction Hmergeable; subst;
    constructor; auto.
  - apply mergeable_stack_frames_sym; auto.
Qed.

Lemma mergeable_stacks_partition gps ctx1 ctx2:
  mergeable_interfaces ctx1 ctx2 ->
  mergeable_stacks (to_partial_stack gps (domm ctx1)) (to_partial_stack gps (domm ctx2)).
Proof.
Admitted. (* Grade 2. *)

Lemma mergeable_memories_sym:
  forall pmem1 pmem2,
    mergeable_memories pmem1 pmem2 ->
    mergeable_memories pmem2 pmem1.
Proof.
  intros pmem1 pmem2 Hmergeable.
  unfold mergeable_memories in *.
  rewrite fdisjointC. auto.
Qed.

Lemma mergeable_states_pc_cc_sym s1 s2:
  mergeable_states_pc_cc s1 s2 ->
  mergeable_states_pc_cc s2 s1.
Proof.
  intros Hmerge.
  inversion Hmerge; subst;
    constructor.
Qed.

(* RB: TODO: Obtain linkability from mergeability. *)
Lemma mergeable_states_sym:
  forall p c s1 s2,
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    mergeable_states (prog_interface c) (prog_interface p) s1 s2 ->
    mergeable_states (prog_interface p) (prog_interface c) s2 s1.
Proof.
  intros p c s1 s2 Hp_wf Hc_wf Hlink Hmergeable.
  inversion Hmergeable; subst.
  - econstructor; auto.
    + apply mergeable_interfaces_sym; assumption.
    + eassumption.
    + eassumption.
    + eassumption.
Qed.

Lemma mergeable_states_stacks ctx1 ctx2 ips1 ips2 gps1 gps2:
  mergeable_states ctx1 ctx2 ips1 ips2 ->
  state_stack ips1 = gps1 ->
  state_stack ips2 = gps2 ->
  mergeable_stacks gps1 gps2.
Proof.
  intros Hmerge Hstk1 Hstk2.
  inversion Hmerge as [ics ? ? Hmerge_ifaces Hprovenance Hpartial1 Hpartial2]; subst.
    inversion Hpartial1; subst;
    inversion Hpartial2; subst;
    apply mergeable_stacks_partition; assumption.
Qed.

Definition merge_stack_frames (frames: PartialPointer.t * PartialPointer.t): PartialPointer.t :=
  match frames with
  | ((C, None), (_, None)) =>
    (* bad case that shouldn't happen, just return first frame *)
    (C, None)
  | ((C, None), (_, Some (b, o))) => (C, Some (b, o))
  | ((C, Some (b, o)), (_, None)) => (C, Some (b, o))
  | ((C, Some (b, o)), (_, Some _)) =>
    (* bad case that shouldn't happen, just return first frame *)
    (C, None)
  end.

Definition merge_stacks (gps1 gps2: stack): stack :=
  map merge_stack_frames (combine gps1 gps2).

Lemma merged_stack_has_no_holes:
  forall pgps1 pgps2,
    mergeable_stacks pgps1 pgps2 ->
    stack_without_holes (merge_stacks pgps1 pgps2).
Proof.
  intros pgps1 pgps2 Hmergeable.
  unfold merge_stacks.
  induction Hmergeable; subst; simpl.
  - constructor.
  - destruct frame1 as [C [[b o]|]];
    destruct frame2 as [C' [[b' o']|]];
      try inversion H.
    + constructor; auto.
    + constructor; auto.
Qed.

(* RB: TODO: Add stack well-formedness w.r.t. interfaces. *)
Lemma merge_stacks_partition:
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall gps,
    unpartialize_stack
      (merge_stacks
         (to_partial_stack gps (domm ctx1))
         (to_partial_stack gps (domm ctx2)))
    = gps.
Admitted. (* Grade 2. *)

(* RB: TODO: Add stack well-formedness w.r.t. interfaces. *)
Lemma merge_stacks_partition_emptym:
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall gps,
    merge_stacks (to_partial_stack gps (domm ctx1))
                 (to_partial_stack gps (domm ctx2)) =
    to_partial_stack gps fset0.
Admitted. (* Grade 2. *)

Definition merge_memories (mem1 mem2: Memory.t): Memory.t :=
  unionm mem1 mem2.

Lemma merge_memories_partition:
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall mem,
    merge_memories
      (filterm (fun (k : nat) (_ : ComponentMemory.t) => k \notin domm ctx1) mem)
      (filterm (fun (k : nat) (_ : ComponentMemory.t) => k \notin domm ctx2) mem)
  = mem.
Admitted. (* Grade 2. *)

Definition merge_partial_states (ips1 ips2: state) : state :=
  match ips1 with
  | PC (gps1, mem1, regs, pc) =>
    match ips2 with
    | PC _ =>
      (* bad case that shouldn't happen, just return first state *)
      ips1
    | CC (C, gps2, mem2) =>
      PC (merge_stacks gps1 gps2, merge_memories mem1 mem2, regs, pc)
    end
  | CC (C, gps1, mem1) =>
    match ips2 with
    | PC (gps2, mem2, regs, pc) =>
      PC (merge_stacks gps1 gps2, merge_memories mem1 mem2, regs, pc)
    | CC _ =>
      (* bad case that shouldn't happen, just return first state *)
      ips1
    end
  end.

(* transition system *)

Inductive initial_state (p: program) (ctx: Program.interface) : state -> Prop :=
| initial_state_intro: forall p' ics ips,
    prog_interface p' = ctx ->
    well_formed_program p ->
    well_formed_program p' ->
    linkable (prog_interface p) (prog_interface p') ->
    partial_state ctx ics ips ->
    CS.initial_state (program_link p p') ics ->
    initial_state p ctx ips.

Inductive final_state (p: program) (ctx: Program.interface) : state -> Prop :=
| final_state_program: forall p' ics ips,
    prog_interface p' = ctx ->
    well_formed_program p ->
    well_formed_program p' ->
    linkable (prog_interface p) (prog_interface p') ->
    ~ turn_of ips ctx ->
    partial_state ctx ics ips ->
    CS.final_state
      (prepare_global_env (program_link p p')) ics ->
    final_state p ctx ips
| final_state_context: forall ips,
    turn_of ips ctx ->
    final_state p ctx ips.

Inductive step (p: program) (ctx: Program.interface)
  : global_env -> state -> trace -> state -> Prop :=
| partial_step:
    forall p' ips t ips' ics ics',
      prog_interface p' = ctx ->
      well_formed_program p ->
      well_formed_program p' ->
      linkable (prog_interface p) (prog_interface p') ->
      CS.step (prepare_global_env (program_link p p')) ics t ics' ->
      partial_state ctx ics ips ->
      partial_state ctx ics' ips' ->
      step p ctx (prepare_global_env p) ips t ips'.

Theorem context_epsilon_step_is_silent:
  forall p ctx G ips ips',
    is_context_component ips ctx ->
    step p ctx G ips E0 ips' ->
    ips' = ips.
Proof.
  intros p ctx G ips ips' Hcc Hstep.
  inversion Hstep; subst.
  match goal with
  | Hpartial1: partial_state _ _ _,
    Hpartial2: partial_state _ _ _ |- _ =>
    inversion Hpartial2; subst; PS.simplify_turn;
    inversion Hpartial1; subst; PS.simplify_turn
  end.
  - rewrite Hcc in H.
    discriminate.
  - rewrite Hcc in H.
    discriminate.
  - (* contra *)
    assert (Pointer.component pc = Pointer.component pc0) as Hsame_comp. {
      inversion H3; subst;
        try (rewrite Pointer.inc_preserves_component; reflexivity);
        try (symmetry; assumption).
      + erewrite find_label_in_component_1; now eauto.
      + erewrite find_label_in_procedure_1; now eauto.
    }
    rewrite <- Hsame_comp in H6.
    rewrite Hcc in H6.
    discriminate.
  - inversion H3; subst;
      try (rewrite Pointer.inc_preserves_component; reflexivity);
      try (symmetry; assumption).
    + rewrite Pointer.inc_preserves_component.
      destruct ptr as [[]].
      erewrite context_store_in_partialized_memory; eauto.
      * rewrite Pointer.inc_preserves_component.
        rewrite <- H17. eassumption.
    + erewrite find_label_in_component_1 with (pc:=pc); eauto.
    + rewrite H17. reflexivity.
    + erewrite find_label_in_procedure_1 with (pc:=pc); eauto.
    + rewrite Pointer.inc_preserves_component.
      erewrite context_allocation_in_partialized_memory; eauto.
      * rewrite Pointer.inc_preserves_component.
        eassumption.
Qed.

Corollary context_epsilon_star_is_silent:
  forall p ctx G ctx_state ips',
    is_context_component ctx_state ctx ->
    star (step p ctx) G ctx_state E0 ips' ->
    ips' = ctx_state.
Proof.
  intros p ctx G ctx_state ips' Hcc Hstar.
  dependent induction Hstar; subst.
  - reflexivity.
  - symmetry in H0. apply Eapp_E0_inv in H0. destruct H0. subst.
    apply (context_epsilon_step_is_silent Hcc) in H. subst.
    apply IHHstar; auto.
Qed.

(* Taking care for now not to mangle hypotheses that may be useful later.
   Using the above remarks instead of simplify_turn directly is somewhat faster. *)
Ltac discharge_pc_cc Hpc Hcc :=
  pose proof pc_component_not_in_ctx Hpc as Hin;
  pose proof cc_component_in_ctx Hcc as Hnotin;
  rewrite Pointer.inc_preserves_component in Hnotin;
  rewrite Hnotin in Hin;
  discriminate.

(* Early renaming of hypotheses generated by cumbersome step inversions.
   Useful for later quick selection of hypotheses without pattern matching. *)
Ltac rename_op p pc1 P12 HOP :=
  match goal with
  | Hop : executing (prepare_global_env (program_link p P12)) pc1 _ |- _ =>
    rename Hop into HOP
  end.

(* In the program, both steps in sync should fetch the same instruction.
   By chaining inversions on component procedures, procedure code and
   instruction, goals involving pairs of non-matching instructions are
   moreover discharged by contradiction. *)
Ltac unify_op Hop1 Hop2 Hcomp Hsame_iface :=
  apply pc_component_not_in_ctx in Hcomp;
  pose proof Hcomp as Hcomp';
  rewrite <- Hsame_iface in Hcomp';
  inversion Hop1 as [procs1 [code1 [Hgenv1 [Hprocs1 [_ Hinstr1]]]]];
  inversion Hop2 as [procs2 [code2 [Hgenv2 [Hprocs2 [_ Hinstr2]]]]];
  pose proof @genv_procedures_program_link_left _ _ Hcomp as Hgenv1';
  pose proof @genv_procedures_program_link_left _ _ Hcomp' as Hgenv2';
  rewrite Hgenv1' in Hgenv1;
  rewrite Hgenv2' in Hgenv2;
  rewrite Hgenv2 in Hgenv1;
  inversion Hgenv1; subst procs2;
  rewrite Hprocs2 in Hprocs1;
  inversion Hprocs1; subst code2;
  rewrite Hinstr2 in Hinstr1;
  inversion Hinstr1.

Ltac discharge_op_neq Hop1 Hop2 Hcomp Hsame_iface :=
  unify_op Hop1 Hop2 Hcomp Hsame_iface;
  discriminate.

Ltac unify_op_eq Hop1 Hop2 Hcomp Hsame_iface :=
  unify_op Hop1 Hop2 Hcomp Hsame_iface;
  subst.

Ltac unify_get :=
  match goal with
  | Hget1 : Register.get ?REG ?REGS = ?V1,
    Hget2 : Register.get ?REG ?REGS = ?V2 |- _ =>
    rewrite Hget2 in Hget1;
    inversion Hget1; subst
  end.

Ltac unify_load pc Hcomp Hmem12 :=
  match goal with
  | Hload1 : Memory.load ?CMEM1 ?PTR = Some ?V1,
    Hload2 : Memory.load ?CMEM2 ?PTR = Some ?V2,
    Heq: Pointer.component ?PTR = Pointer.component pc |- _ =>
    pose proof Hcomp as Hptr;
    rewrite <- Heq in Hptr;
    pose proof program_load_in_partialized_memory Hmem12 Hptr Hload1 Hload2;
    subst
  end.

Ltac unify_store pc Hcomp Hmem12 :=
  match goal with
  | Hstore1 : Memory.store ?CMEM1 ?PTR ?GET = Some ?MEM1,
    Hstore2 : Memory.store ?CMEM2 ?PTR ?GET = Some ?MEM2,
    Heq: Pointer.component ?PTR = Pointer.component pc |- _ =>
    pose proof Hcomp as Hptr;
    rewrite <- Heq in Hptr;
    pose proof program_store_in_partialized_memory Hmem12 Hptr Hstore1 Hstore2 as Hmem12';
    rewrite Hmem12'
  end.

Ltac unify_component_label Hcomp Hcomp' :=
  match goal with
  | Hlabel1 : find_label_in_component (prepare_global_env (program_link ?P ?P1)) ?PC ?L = Some ?PC1,
    Hlabel2 : find_label_in_component (prepare_global_env (program_link ?P ?P2)) ?PC ?L = Some ?PC2  |- _ =>
    pose proof find_label_in_component_program_link_left Hlabel1 Hcomp as Hlabel1';
    pose proof find_label_in_component_program_link_left Hlabel2 Hcomp' as Hlabel2';
    rewrite Hlabel2' in Hlabel1';
    inversion Hlabel1'; subst
  end.

Ltac unify_procedure_label Hcomp Hcomp' :=
  match goal with
  | Hlabel1 : find_label_in_procedure (prepare_global_env (program_link ?P ?P1)) ?PC ?L = Some ?PC1,
    Hlabel2 : find_label_in_procedure (prepare_global_env (program_link ?P ?P2)) ?PC ?L = Some ?PC2  |- _ =>
    pose proof find_label_in_procedure_program_link_left Hlabel1 Hcomp as Hlabel1';
    pose proof find_label_in_procedure_program_link_left Hlabel2 Hcomp' as Hlabel2';
    rewrite Hlabel2' in Hlabel1';
    inversion Hlabel1'; subst
  end.

(* RB: TODO: Simplify Some pattern. *)
Ltac unify_alloc Hmem12 Hcomp :=
  match goal with
  | Halloc1 : Memory.alloc ?CMEM1 ?CID ?SIZE = Some (?MEM1, ?PTR1),
    Halloc2 : Memory.alloc ?CMEM2 ?CID ?SIZE = Some (?MEM2, ?PTR2) |- _ =>
    pose proof program_allocation_in_partialized_memory Hmem12 Hcomp Halloc1 Halloc2
      as [Hptr Halloc];
    subst;
    rewrite Halloc
  end.

Ltac unify_entrypoint Hpc1' Hpc2' Hsame_iface :=
  match goal with
  | Hentry1 : EntryPoint.get ?C ?PROC (genv_entrypoints (prepare_global_env (program_link ?P ?P1))) = ?B1,
    Hentry2 : EntryPoint.get ?C ?PROC (genv_entrypoints (prepare_global_env (program_link ?P ?P2))) = ?B2  |- _ =>
    pose proof genv_entrypoints_program_link_left Hentry1 Hpc1' as Hentry1';
    rewrite <- Hsame_iface in Hpc2';
    pose proof genv_entrypoints_program_link_left Hentry2 Hpc2' as Hentry2';
    rewrite Hentry2' in Hentry1';
    inversion Hentry1'; subst
  end.

(* Turns must have been simplified. *)
Ltac discharge_pc Hpc Hcc :=
  rewrite Hcc in Hpc;
  discriminate.

(* Generates two sub-goals. *)
Ltac analyze_stack p1 pc1 pc2 Hhead :=
  match goal with
  | Heq : Pointer.component pc1 = Pointer.component pc2  |- _ =>
    unfold to_partial_frame in Hhead;
    (* Case analysis on both frame pointers. *)
    destruct (Pointer.component pc1 \in domm (prog_interface p1)) eqn:Heq1;
    destruct (Pointer.component pc2 \in domm (prog_interface p1)) eqn:Heq2;
    [                                               (* User-guided contradiction *)
    | discriminate                                  (* Direct contradiction *)
    | discriminate                                  (* Direct contradiction *)
    | apply partial_pointer_to_pointer_eq in Hhead;
      subst                                         (* User tactic *)
    ]
  end.

Lemma state_determinism_program:
  forall p ctx G ips t ips',
    is_program_component ips ctx ->
    step p ctx G ips t ips' ->
  forall ips'',
    step p ctx G ips t ips'' ->
    ips' = ips''.
Proof.
  intros p ctx G ps t ps1 Hcomp Hstep_ps1 ps2 Hstep_ps2.

  inversion Hstep_ps1
    as [p1 ? ? ? cs1 cs1' ? Hwfp Hwfp1 Hlink1 Hstep_cs1 Hpartial1 Hpartial1'];
    subst.
  inversion Hstep_ps2
    as [p2 ? ? ? cs2 cs2' Hsame_iface _ Hwfp2 Hlink2 Hstep_cs2 Hpartial2 Hpartial2'];
    subst.

  (* Case analysis on who has control. *)
  inversion Hpartial1 as [cstk1 ? cmem1 ? regs1 pc1 Hpc1 | cstk1 ? cmem1 ? regs1 pc1 Hcc1];
    subst;
    (* Context control is discharged by contradiction. *)
    last (simplify_turn; rewrite Hcc1 in Hcomp; discriminate).

  inversion Hpartial2 as [cstk2 ? cmem2 ? regs2 pc2 Hpc2 Hmem12 Hstk12 |]; subst.
  (* First, case analysis of CS steps with explicit naming of hypotheses of interest.
     Cases where the operations in both steps do not coincide can be discharged. *)
  inversion Hstep_cs1; subst; rename_op p pc1 p1 Hop1;
    inversion Hstep_cs2; subst; rename_op p pc1 p2 Hop2;
    try discharge_op_neq Hop1 Hop2 Hcomp Hsame_iface;
    (* Second, case analysis of partial steps.
       Cases where program and component do not match can be discharged. *)
    inversion Hpartial1'
      as [cstk1' ? cmem1' ? regs1' pc1' Hpc1' | cstk1' ? cmem1' ? regs1' pc1' Hcc1'];
      subst;
    inversion Hpartial2'
      as [cstk2' ? cmem2' ? regs2' pc2' Hpc2' | cstk2' ? cmem2' ? regs2' pc2' Hcc2'];
      subst;
    try discharge_pc_cc Hcomp Hcc1';
    try discharge_pc_cc Hcomp Hcc2';
    (* For the remaining goals, unify components of their matching opcodes and their
       various optional components: register and memory reads and stores, component
       labels, allocs and entry points. *)
    unify_op_eq Hop1 Hop2 Hcomp Hsame_iface;
    simplify_turn;
    try unify_get;
    try unify_load pc1 Hcomp Hmem12;
    try unify_store pc1 Hcomp Hmem12;
    try unify_component_label Hcomp Hcomp';
    try unify_procedure_label Hcomp Hcomp';
    try unify_alloc Hmem12 Hcomp;
    try unify_entrypoint Hpc1' Hpc2' Hsame_iface;
    (* Rewrite memory and stack, where applicable. *)
    try rewrite Hmem12;
    try rewrite Hstk12;
    (* With this, most goals go away either by reflexivity or by contradiction, either
       direct or on the turns of both components. *)
    try reflexivity;
    try contradiction;
    try discharge_pc Hpc1' Hcc2';
    try discharge_pc Hpc2' Hcc1';
    (* All that remains are returns, in which case the stack is decomposed. *)
    inversion Hstk12 as [[Hhead Htail]].
  (* RB: TODO: Discharges and proof strategies can be found automatically. *)
  - analyze_stack p1 pc'0 pc' Hhead.
    + discharge_pc Hpc2' Heq1.
    + reflexivity.
  - analyze_stack p1 pc'0 pc' Hhead.
    + discharge_pc Hpc1' Heq2.
    + discharge_pc Hcc2' Heq2.
  - analyze_stack p1 pc'0 pc' Hhead.
    + discharge_pc Hpc2' Heq1.
    + discharge_pc Hcc1' Heq1.
  - congruence.
Qed.

Lemma state_determinism_context:
  forall p ctx G ips t ips',
    is_context_component ips ctx ->
    step p ctx G ips t ips' ->
  forall ips'',
    step p ctx G ips t ips'' ->
    ips' = ips''.
Admitted. (* Grade 3, check. Compare with state_determinism_program. *)

Theorem state_determinism:
  forall p ctx G ips t ips',
    step p ctx G ips t ips' ->
  forall ips'',
    step p ctx G ips t ips'' ->
    ips' = ips''.
Proof.
  intros p ctx G ps t ps1 Hstep_ps1 ps2 Hstep_ps2.
  inversion Hstep_ps1 as [? ? ? ? ? _ _ _ _ _ _ Hpartial1 _]; subst.
  (* Case analysis on who has control. *)
  inversion Hpartial1; subst.
  - eapply state_determinism_program; eassumption.
  - eapply state_determinism_context; eassumption.
Qed.

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
    @Semantics_gen state global_env (step p ctx)
                   (initial_state p ctx)
                   (final_state p ctx) (prepare_global_env p).
End Semantics.
End PS.
