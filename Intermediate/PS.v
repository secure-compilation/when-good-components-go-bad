Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.

Module PS.

Import Intermediate.

Module PartialPointer.
  Definition t : Type := Component.id * option (Block.id * Block.offset).
End PartialPointer.

Definition stack := list PartialPointer.t.

Definition program_state : Type := stack * Memory.t * Register.t * Pointer.t.
Definition context_state : Type := Component.id * stack * Memory.t.

Inductive state : Type :=
| PC : program_state -> state
| CC : context_state -> exec_state -> state.

Ltac unfold_state :=
  match goal with
  | H: state |- _ =>
    let pgps := fresh "pgps" in
    let pmem := fresh "pmem" in
    let regs := fresh "regs" in
    let pc := fresh "pc" in
    let comp := fresh "C" in
    destruct H as [[[[pgps pmem] regs] pc] | [[comp pgps] pmem] []]
  end.

Inductive state_eq: state -> state -> Prop :=
| program_states_eq: forall pgps1 pmem1 regs1 pc1 pgps2 pmem2 regs2 pc2,
    pgps1 = pgps2 ->
    PMap.Equal pmem1 pmem2 ->
    regs1 = regs2 ->
    pc1 = pc2 ->
    state_eq (PC (pgps1, pmem1, regs1, pc1)) (PC (pgps2, pmem2, regs2, pc2))
| context_state_eq: forall C1 pgps1 pmem1 C2 pgps2 pmem2,
    C1 = C2 ->
    pgps1 = pgps2 ->
    PMap.Equal pmem1 pmem2 ->
    state_eq (CC (C1, pgps1, pmem1) Normal) (CC (C2, pgps2, pmem2) Normal).

Lemma state_eq_refl:
  forall s,
    state_eq s s.
Proof.
  intros; unfold_state; constructor; reflexivity.
Qed.

Lemma state_eq_sym:
  forall s1 s2,
    state_eq s1 s2 -> state_eq s2 s1.
Proof.
  intros s1 s2 H.
  inversion H; subst;
    constructor;
    try reflexivity;
    try symmetry; assumption.
Qed.

Lemma state_eq_trans:
  forall s1 s2 s3,
    state_eq s1 s2 -> state_eq s2 s3 -> state_eq s1 s3.
Proof.
  intros s1 s2 s3 H1 H2.
  inversion H1; subst; inversion H2; subst;
    constructor;
    try reflexivity;
    try etransitivity; eauto.
Qed.

Add Parametric Relation: (state) (state_eq)
    reflexivity proved by (state_eq_refl)
    symmetry proved by (state_eq_sym)
    transitivity proved by (state_eq_trans)
      as state_eq_rel.

Instance state_turn : HasTurn state := {
  turn_of s iface :=
    match s with
    | PC (_, _, _, pc) => PMap.In (Pointer.component pc) iface
    | CC (C, _, _) _ => PMap.In C iface
    end
}.

Definition is_context_component (ps: state) ctx := turn_of ps ctx.
Definition is_program_component (ps: state) ctx := ~ is_context_component ps ctx.

Ltac simplify_turn :=
  unfold PS.is_program_component, PS.is_context_component in *;
  unfold turn_of, PS.state_turn in *;
  simpl in *.

(* stack partialization *)

Definition to_partial_frame ctx frame : PartialPointer.t :=
  let '(C, b, o) := frame in
  if Util.Lists.mem C ctx then
    (C, None)
  else
    (C, Some (b, o)).

Definition to_partial_stack (s : CS.stack) (ctx: list Component.id) :=
  map (to_partial_frame ctx) s.

(* might be useful in the future
Lemma push_by_context_preserves_partial_stack:
  forall s ps ctx C b o,
    Util.Lists.mem C ctx = true ->
    to_partial_stack s ctx = ps ->
    to_partial_stack ((C,b,o)::s) ctx = (C,None) :: ps.
Proof.
  intros s ps ctx C b o Hprogturn H.
  simpl. rewrite Hprogturn. rewrite H. reflexivity.
Qed.

Lemma push_by_prog_preserves_partial_stack:
  forall s ps ctx C b o,
    ~ (In C ctx) ->
    to_partial_stack s ctx = ps ->
    to_partial_stack ((C,b,o)::s) ctx = (C,Some (b,o)) :: ps.
Proof.
  intros s ps ctx C b o Hprogturn Hpstack.
  simpl. apply Util.Lists.not_in_iff_mem_false in Hprogturn.
  rewrite Hprogturn. rewrite Hpstack. reflexivity.
Qed.

Lemma pc_inc_within_partial_frame_1 (ctx: Program.interface):
  forall pc,
    PMap.In (Pointer.component pc) ctx ->
    PS.to_partial_frame (map fst (PMap.elements ctx)) pc = (Pointer.component pc, None).
Proof.
  intros pc Hin_ctx.
  unfold PS.to_partial_frame, Pointer.inc, Pointer.add.
  destruct pc as [[C b] o].
  simpl in *. PS.simplify_turn.
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

Lemma pc_inc_within_partial_frame_2 (ctx: Program.interface):
  forall pc,
    ~ PMap.In (Pointer.component pc) ctx ->
    PS.to_partial_frame (map fst (PMap.elements ctx)) pc
    = (Pointer.component pc, Some (Pointer.block pc, Pointer.offset pc)).
Proof.
  intros pc Hnot_in_ctx.
  unfold PS.to_partial_frame, Pointer.inc, Pointer.add.
  destruct pc as [[C b] o].
  simpl in *. PS.simplify_turn.
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
*)

Lemma to_partial_frame_with_empty_context:
  forall C b o,
    to_partial_frame [] (C, b, o) = (C, Some (b, o)). 
Proof.
  intros. reflexivity.
Qed.

Lemma to_partial_stack_with_empty_context:
  forall gps1 gps2,
    to_partial_stack gps1 [] = to_partial_stack gps2 [] ->
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
      do 2 rewrite to_partial_frame_with_empty_context in H1.
      inversion H1. subst.
      rewrite (IHgps1 gps2 H2).
      reflexivity.
Qed.

Inductive partial_state (ctx: Program.interface) : CS.state -> PS.state -> Prop :=
| ProgramControl: forall gps pgps mem pmem regs pc,
    (* program has control *)
    is_program_component (PC (pgps, pmem, regs, pc)) ctx ->

    (* we forget about context memories *)
    PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->

    (* we put holes in place of context information in the stack *)
    pgps = to_partial_stack gps (map fst (PMap.elements ctx)) ->

    partial_state ctx (gps, mem, regs, pc) (PC (pgps, pmem, regs, pc))

| ContextControl_Normal: forall gps pgps mem pmem regs pc,
    (* context has control *)
    is_context_component (CC (Pointer.component pc, pgps, pmem) Normal) ctx ->

    (* we forget about context memories *)
    PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->

    (* we put holes in place of context information in the stack *)
    pgps = to_partial_stack gps (map fst (PMap.elements ctx)) ->

    partial_state ctx (gps, mem, regs, pc) (CC (Pointer.component pc, pgps, pmem) Normal).

Definition partialize (ics: CS.state) (ctx: Program.interface) : PS.state :=
  let '(gps, mem, regs, pc) := ics in
  if PMap.mem (Pointer.component pc) ctx then
    CC (Pointer.component pc,
        to_partial_stack gps (map fst (PMap.elements ctx)),
        PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) Normal
  else
    PC (to_partial_stack gps (map fst (PMap.elements ctx)),
        PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem,
        regs, pc).

Lemma partialize_correct:
  forall ics ips ctx,
    state_eq (partialize ics ctx) ips <-> partial_state ctx ics ips.
Proof.
  intros ics ips ctx.
  split.
  - intro H.
    CS.unfold_state.
    inversion H; subst;
      destruct (PMap.mem (Pointer.component pc) ctx) eqn:Hcontrol; subst;
        try discriminate.
    + inversion H0; subst.
      eapply PS.ProgramControl; eauto.
      * simplify_turn.
        apply PMapFacts.not_mem_in_iff. eauto.
      * symmetry. assumption.
    + inversion H0; subst.
      eapply PS.ContextControl_Normal; eauto.
      * simplify_turn.
        apply PMapFacts.mem_in_iff. eauto.
      * symmetry. assumption.
  - intros Hpartial_state.
    unfold partialize.
    inversion Hpartial_state; subst; simplify_turn;
      [ apply PMapFacts.not_mem_in_iff in H
      | apply PMapFacts.mem_in_iff in H ];
      rewrite H; simpl;
        econstructor; eauto; symmetry; auto.
Qed.

Lemma equal_states_partialize:
  forall ctx ics1 ics2 ips,
    CS.state_eq ics1 ics2 ->
    PS.partial_state ctx ics1 ips ->
    PS.partial_state ctx ics2 ips.
Proof.
  intros ctx ics1 ics2 ips.
  intros Heq Hics1_partial.
  inversion Heq; subst.
  inversion Hics1_partial; subst.
  - econstructor.
    + simplify_turn. auto.
    + rewrite H6.
      intros C.
      destruct (PMap.find C (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem1))
               eqn:Hfind1;
      destruct (PMap.find C (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem2))
               eqn:Hfind2.
      * apply PMap.find_2 in Hfind1.
        apply PMap.find_2 in Hfind2.
        apply PMapExtra.filter_iff in Hfind1.
        apply PMapExtra.filter_iff in Hfind2.
        destruct Hfind1 as [Hmapsto1 Hcond1].
        destruct Hfind2 as [Hmapsto2 Hcond2].
        rewrite H0 in Hmapsto1.
        erewrite (PMapFacts.MapsTo_fun Hmapsto1 Hmapsto2).
        reflexivity.
        ** (* morphisms stuff *)
          unfold Morphisms.Proper, Morphisms.respectful.
          intros. subst. reflexivity.
        ** (* morphisms stuff *)
          unfold Morphisms.Proper, Morphisms.respectful.
          intros. subst. reflexivity.
      * apply PMap.find_2 in Hfind1.
        apply PMapFacts.not_find_in_iff in Hfind2.
        apply PMapExtra.filter_iff in Hfind1.
        destruct Hfind1 as [Hmapsto1 Hcond1].
        exfalso.
        apply Hfind2.
        eexists. apply PMapExtra.filter_iff.
        ** (* morphisms stuff *)
          unfold Morphisms.Proper, Morphisms.respectful.
          intros. subst. reflexivity.
        ** rewrite H0 in Hmapsto1.
           split; eauto.
        ** (* morphisms stuff *)
          unfold Morphisms.Proper, Morphisms.respectful.
          intros. subst. reflexivity.
      * apply PMap.find_2 in Hfind2.
        apply PMapFacts.not_find_in_iff in Hfind1.
        apply PMapExtra.filter_iff in Hfind2.
        destruct Hfind2 as [Hmapsto2 Hcond2].
        exfalso.
        apply Hfind1.
        eexists. apply PMapExtra.filter_iff.
        ** (* morphisms stuff *)
          unfold Morphisms.Proper, Morphisms.respectful.
          intros. subst. reflexivity.
        ** rewrite <- H0 in Hmapsto2.
           split; eauto.
        ** (* morphisms stuff *)
          unfold Morphisms.Proper, Morphisms.respectful.
          intros. subst. reflexivity.
      * reflexivity.
    + reflexivity.
  - econstructor.
    + simplify_turn. auto.
    + rewrite H6.
      intros C.
      destruct (PMap.find C (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem1))
               eqn:Hfind1;
      destruct (PMap.find C (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem2))
               eqn:Hfind2.
      * apply PMap.find_2 in Hfind1.
        apply PMap.find_2 in Hfind2.
        apply PMapExtra.filter_iff in Hfind1.
        apply PMapExtra.filter_iff in Hfind2.
        destruct Hfind1 as [Hmapsto1 Hcond1].
        destruct Hfind2 as [Hmapsto2 Hcond2].
        rewrite H0 in Hmapsto1.
        erewrite (PMapFacts.MapsTo_fun Hmapsto1 Hmapsto2).
        reflexivity.
        ** (* morphisms stuff *)
          unfold Morphisms.Proper, Morphisms.respectful.
          intros. subst. reflexivity.
        ** (* morphisms stuff *)
          unfold Morphisms.Proper, Morphisms.respectful.
          intros. subst. reflexivity.
      * apply PMap.find_2 in Hfind1.
        apply PMapFacts.not_find_in_iff in Hfind2.
        apply PMapExtra.filter_iff in Hfind1.
        destruct Hfind1 as [Hmapsto1 Hcond1].
        exfalso.
        apply Hfind2.
        eexists. apply PMapExtra.filter_iff.
        ** (* morphisms stuff *)
          unfold Morphisms.Proper, Morphisms.respectful.
          intros. subst. reflexivity.
        ** rewrite H0 in Hmapsto1.
           split; eauto.
        ** (* morphisms stuff *)
          unfold Morphisms.Proper, Morphisms.respectful.
          intros. subst. reflexivity.
      * apply PMap.find_2 in Hfind2.
        apply PMapFacts.not_find_in_iff in Hfind1.
        apply PMapExtra.filter_iff in Hfind2.
        destruct Hfind2 as [Hmapsto2 Hcond2].
        exfalso.
        apply Hfind1.
        eexists. apply PMapExtra.filter_iff.
        ** (* morphisms stuff *)
          unfold Morphisms.Proper, Morphisms.respectful.
          intros. subst. reflexivity.
        ** rewrite <- H0 in Hmapsto2.
           split; eauto.
        ** (* morphisms stuff *)
          unfold Morphisms.Proper, Morphisms.respectful.
          intros. subst. reflexivity.
      * reflexivity.
    + reflexivity.
Qed.

(* unpartializing partial states without holes *)

Definition unpartialize_stack_frame (frame: PS.PartialPointer.t): Pointer.t :=
  match frame with
  | (C, None) =>
    (* bad case that shouldn't happen, just return first state *)
    (C, 1%positive, 0)
  | (C, Some (b, o)) => (C, b, o)
  end.

Definition unpartialize_stack (pgps: PS.stack): CS.stack :=
  map unpartialize_stack_frame pgps.

Definition unpartialize (ips: PS.state): CS.state :=
  match ips with
  | PS.PC (pgps, mem, regs, pc) =>
    (unpartialize_stack pgps, mem, regs, pc)
  | PS.CC _ _ =>
    (* bad case that shouldn't happen, just return first state *)
    ([], PMap.empty ComponentMemory.t, [], (1%positive, 1%positive, 0))
  end.

Lemma unpartializing_complete_stack_frame:
  forall frame,
    unpartialize_stack_frame (to_partial_frame [] frame) = frame.
Proof.
  intros frame.
  destruct frame as [[C b] o].
  reflexivity.
Qed.

Lemma unpartializing_complete_stack:
  forall stack,
    unpartialize_stack (to_partial_stack stack []) = stack.
Proof.
  intros stack.
  induction stack; simpl.
  - reflexivity.
  - rewrite unpartializing_complete_stack_frame.
    rewrite IHstack.
    reflexivity.
Qed.

(* TODO generalize for arbitrary maps *)
Lemma filter_identity:
  forall (mem: Memory.t),
    PMap.Equal (PMapExtra.filter (fun _ _ => true) mem) mem.
Proof.
  intros mem C.
  destruct (PMap.find C (PMapExtra.filter (fun _ _ => true) mem)) eqn:Hfind.
  - apply PMap.find_2 in Hfind.
    apply PMapExtra.filter_iff in Hfind.
    + destruct Hfind as [Hfound []].
      apply PMap.find_1 in Hfound.
      rewrite Hfound. reflexivity.
    + (* morphisms stuff *)
      unfold Morphisms.Proper, Morphisms.respectful.
      intros. subst. reflexivity.
  - apply PMapFacts.not_find_in_iff in Hfind.
    symmetry. apply PMapFacts.not_find_in_iff.
    intro contra. apply Hfind.
    destruct contra as [Cmem contra].
    eexists. apply PMapExtra.filter_iff.
    + (* morphisms stuff *)
      unfold Morphisms.Proper, Morphisms.respectful.
      intros. subst. reflexivity.
    + split; eauto.
Qed.

Lemma unpartializing_complete_states:
  forall ics,
    CS.state_eq (unpartialize (partialize ics (PMap.empty Component.interface))) ics.
Proof.
  intros ics.
  CS.unfold_state. simpl.
  constructor;
    try reflexivity.
  - apply unpartializing_complete_stack.
  - apply filter_identity.
Qed.

(* merging partial states *)

Definition get_executing_component (ips: PS.state): Component.id :=
  match ips with
  | PS.PC (_, _, _, pc) => Pointer.component pc
  | PS.CC (C, _, _) Normal => C
end.

Definition get_global_protected_stack (ips: PS.state): PS.stack :=
  match ips with
  | PS.PC (gps, _, _, _) => gps
  | PS.CC (_, gps, _) Normal => gps
  end.

Definition get_memory (ips: PS.state): Memory.t :=
  match ips with
  | PS.PC (_, mem, _, _) => mem
  | PS.CC (_, _, mem) Normal => mem
  end.

Inductive mergeable_stack_frames: PS.PartialPointer.t * PS.PartialPointer.t -> Prop :=
| mergeable_stack_frames_first: forall C1 b1 o1 C2,
    C1 = C2 ->
    mergeable_stack_frames ((C1, Some (b1, o1)), (C2, None))
| mergeable_stack_frames_second: forall C1 C2 b2 o2,
    C1 = C2 ->
    mergeable_stack_frames ((C1, None), (C1, Some (b2, o2))).

Definition mergeable_stacks (gps1 gps2: PS.stack): Prop :=
  forall frames, In frames (combine gps1 gps2) -> mergeable_stack_frames frames.

Definition mergeable_memories (mem1 mem2: Memory.t): Prop :=
  PMapExtra.Disjoint mem1 mem2.

Definition mergeable_states (ips1 ips2: PS.state): Prop :=
  get_executing_component ips1 = get_executing_component ips2 /\
  mergeable_stacks (get_global_protected_stack ips1) (get_global_protected_stack ips2) /\
  mergeable_memories (get_memory ips1) (get_memory ips2).

Definition merge_stack_frames (frames: PS.PartialPointer.t * PS.PartialPointer.t): PS.PartialPointer.t :=
  match frames with
  | ((C, None), (C', None)) =>
    (* bad case that shouldn't happen, just return first frame *)
    (C, None)
  | ((C, None), (C', Some (b, o))) => (C, Some (b, o))
  | ((C, Some (b, o)), (C', None)) => (C, Some (b, o))
  | ((C, Some (b, o)), (C', Some _)) =>
    (* bad case that shouldn't happen, just return first frame *)
    (C, None)
  end.

Fixpoint merge_stacks (gps1 gps2: PS.stack): PS.stack :=
  map merge_stack_frames (combine gps1 gps2).

Definition merge_memories (mem1 mem2: Memory.t): Memory.t := PMapExtra.update mem1 mem2.

Definition merge_partial_states (ips1 ips2: PS.state) : PS.state :=
  match ips1 with
  | PS.PC (gps1, mem1, regs, pc) =>
    match ips2 with
    | PS.PC _ =>
      (* bad case that shouldn't happen, just return first state *)
      ips1
    | PS.CC (C, gps2, mem2) Normal =>
      PS.PC (merge_stacks gps1 gps2, merge_memories mem1 mem2, regs, pc)
    end
  | PS.CC (C, gps1, mem1) Normal =>
    match ips2 with
    | PS.PC (gps2, mem2, regs, pc) =>
      PS.PC (merge_stacks gps1 gps2, merge_memories mem1 mem2, regs, pc)
    | PS.CC _ Normal =>
      (* bad case that shouldn't happen, just return first state *)
      ips1
    end
  end.

(* transition system *)

Inductive initial_state (p: program) (ctx: Program.interface) : state -> Prop :=
| initial_state_intro: forall ics ips,
    partial_state ctx ics ips ->
    CS.initial_state p ics ->
    initial_state p ctx ips.

Inductive final_state (p: program) (ctx: Program.interface) : state -> Prop :=
| final_state_program: forall ics ips,
    ~ turn_of ips ctx ->
    partial_state ctx ics ips ->
    CS.final_state (init_genv p) ics ->
    final_state p ctx ips
| final_state_context: forall ips,
    turn_of ips ctx ->
    final_state p ctx ips.

Inductive step (ctx: Program.interface) (G: global_env)
  : state -> trace -> state -> Prop :=
| partial_step:
    forall ips t ips' ics ics',
      CS.step G ics t ics' ->
      partial_state ctx ics ips ->
      partial_state ctx ics' ips' ->
      step ctx G ips t ips'.

(* partial semantics *)

Section Semantics.
  Variable p: program.
  Variable ctx: Program.interface.

  Let G := init_genv p.

  Hypothesis valid_program:
    well_formed_program p.

  Hypothesis complete_program:
    closed_program p.

  (* the context is part of p *)
  Hypothesis valid_context:
    forall C CI, PMap.MapsTo C CI ctx -> PMap.MapsTo C CI (prog_interface p).

  Definition sem :=
    @Semantics_gen state global_env (step ctx)
                   (initial_state p ctx)
                   (final_state p ctx) G.
End Semantics.
End PS.
