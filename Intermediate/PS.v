Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.

Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

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
| CC : context_state -> state.

Ltac unfold_states :=
  match goal with
  | H: state |- _ =>
    let pgps := fresh "pgps" in
    let pmem := fresh "pmem" in
    let regs := fresh "regs" in
    let pc := fresh "pc" in
    let comp := fresh "C" in
    destruct H as [[[[pgps pmem] regs] pc] | [[comp pgps] pmem]]
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
    state_eq (CC (C1, pgps1, pmem1)) (CC (C2, pgps2, pmem2)).

Lemma state_eq_refl:
  forall s,
    state_eq s s.
Proof.
  intros; unfold_states; constructor; reflexivity.
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
    | CC (C, _, _) => PMap.In C iface
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

Lemma ptr_within_partial_frame_1 (ctx: Program.interface):
  forall ptr,
    PMap.In (Pointer.component ptr) ctx ->
    to_partial_frame (map fst (PMap.elements ctx)) ptr = (Pointer.component ptr, None).
Proof.
  intros ptr Hin_ctx.
  unfold to_partial_frame, Pointer.inc, Pointer.add.
  destruct ptr as [[C b] o].
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

Lemma ptr_within_partial_frame_2 (ctx: Program.interface):
  forall ptr,
    ~ PMap.In (Pointer.component ptr) ctx ->
    to_partial_frame (map fst (PMap.elements ctx)) ptr
    = (Pointer.component ptr, Some (Pointer.block ptr, Pointer.offset ptr)).
Proof.
  intros ptr Hnot_in_ctx.
  unfold to_partial_frame, Pointer.inc, Pointer.add.
  destruct ptr as [[C b] o].
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

| ContextControl: forall gps pgps mem pmem regs pc,
    (* context has control *)
    is_context_component (CC (Pointer.component pc, pgps, pmem)) ctx ->

    (* we forget about context memories *)
    PMap.Equal pmem (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem) ->

    (* we put holes in place of context information in the stack *)
    pgps = to_partial_stack gps (map fst (PMap.elements ctx)) ->

    partial_state ctx (gps, mem, regs, pc) (CC (Pointer.component pc, pgps, pmem)).

Definition partialize (ics: CS.state) (ctx: Program.interface) : PS.state :=
  let '(gps, mem, regs, pc) := ics in
  if PMap.mem (Pointer.component pc) ctx then
    CC (Pointer.component pc,
        to_partial_stack gps (map fst (PMap.elements ctx)),
        PMapExtra.filter (fun k _ => negb (PMap.mem k ctx)) mem)
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
    CS.unfold_states.
    inversion H; subst;
      destruct (PMap.mem (Pointer.component pc) ctx) eqn:Hcontrol; subst;
        try discriminate.
    + inversion H0; subst.
      eapply ProgramControl; eauto.
      * simplify_turn.
        apply PMapFacts.not_mem_in_iff. eauto.
      * symmetry. assumption.
    + inversion H0; subst.
      eapply ContextControl; eauto.
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

Set Implicit Arguments.

Add Morphism (partialize)
    with signature
      (@CS.state_eq) ==> (@PMap.Equal Component.interface) ==> (state_eq)
      as partialize_eq.
Proof.
  intros ics1 ics2 Hics_eq ctx1 ctx2 Hctx_eq.
  inversion Hics_eq; subst.
  simpl.
  rewrite Hctx_eq.
  destruct (PMap.mem (elt:=Component.interface) (Pointer.component pc2) ctx2).
  - constructor.
    + reflexivity.
    + induction gps2.
      * reflexivity.
      * simpl.
        destruct (PMap.mem (Pointer.component a) ctx1) eqn:Hwhere.
        ** apply PMapFacts.mem_in_iff in Hwhere.
           rewrite ptr_within_partial_frame_1; auto.
           rewrite Hctx_eq in Hwhere.
           rewrite ptr_within_partial_frame_1; auto.
           inversion Hics_eq; subst.
           assert (CS.state_eq (gps2, mem1, regs2, pc2) (gps2, mem2, regs2, pc2)). {
             constructor; try reflexivity; try assumption.
           }
           rewrite IHgps2; auto.
        ** apply PMapFacts.not_mem_in_iff in Hwhere.
           rewrite ptr_within_partial_frame_2; auto.
           rewrite Hctx_eq in Hwhere.
           rewrite ptr_within_partial_frame_2; auto.
           inversion Hics_eq; subst.
           assert (CS.state_eq (gps2, mem1, regs2, pc2) (gps2, mem2, regs2, pc2)). {
             constructor; try reflexivity; try assumption.
           }
           rewrite IHgps2; auto.
    + intros C.
      destruct (PMap.find C (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx1)) mem1))
               eqn:Hfind1;
      destruct (PMap.find C (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx2)) mem2))
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
           destruct (PMap.mem (elt:=Component.interface) C ctx1) eqn:Hwhere;
             try discriminate.
           apply PMapFacts.not_mem_in_iff in Hwhere. rewrite Hctx_eq in Hwhere.
           destruct (PMap.mem (elt:=Component.interface) C ctx2) eqn:Hwhere';
             try discriminate.
           *** apply PMapFacts.mem_in_iff in Hwhere'. contradiction.
           *** auto.
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
           destruct (PMap.mem (elt:=Component.interface) C ctx2) eqn:Hwhere;
             try discriminate.
           apply PMapFacts.not_mem_in_iff in Hwhere. rewrite <- Hctx_eq in Hwhere.
           destruct (PMap.mem (elt:=Component.interface) C ctx1) eqn:Hwhere';
             try discriminate.
           *** apply PMapFacts.mem_in_iff in Hwhere'. contradiction.
           *** auto.
        ** (* morphisms stuff *)
          unfold Morphisms.Proper, Morphisms.respectful.
          intros. subst. reflexivity.
      * reflexivity.
  - constructor.
    + induction gps2.
      * reflexivity.
      * simpl.
        destruct (PMap.mem (Pointer.component a) ctx1) eqn:Hwhere.
        ** apply PMapFacts.mem_in_iff in Hwhere.
           rewrite ptr_within_partial_frame_1; auto.
           rewrite Hctx_eq in Hwhere.
           rewrite ptr_within_partial_frame_1; auto.
           inversion Hics_eq; subst.
           assert (CS.state_eq (gps2, mem1, regs2, pc2) (gps2, mem2, regs2, pc2)). {
             constructor; try reflexivity; try assumption.
           }
           rewrite IHgps2; auto.
        ** apply PMapFacts.not_mem_in_iff in Hwhere.
           rewrite ptr_within_partial_frame_2; auto.
           rewrite Hctx_eq in Hwhere.
           rewrite ptr_within_partial_frame_2; auto.
           inversion Hics_eq; subst.
           assert (CS.state_eq (gps2, mem1, regs2, pc2) (gps2, mem2, regs2, pc2)). {
             constructor; try reflexivity; try assumption.
           }
           rewrite IHgps2; auto.
    + intros C.
      destruct (PMap.find C (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx1)) mem1))
               eqn:Hfind1;
      destruct (PMap.find C (PMapExtra.filter (fun k _ => negb (PMap.mem k ctx2)) mem2))
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
           destruct (PMap.mem (elt:=Component.interface) C ctx1) eqn:Hwhere;
             try discriminate.
           apply PMapFacts.not_mem_in_iff in Hwhere. rewrite Hctx_eq in Hwhere.
           destruct (PMap.mem (elt:=Component.interface) C ctx2) eqn:Hwhere';
             try discriminate.
           *** apply PMapFacts.mem_in_iff in Hwhere'. contradiction.
           *** auto.
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
           destruct (PMap.mem (elt:=Component.interface) C ctx2) eqn:Hwhere;
             try discriminate.
           apply PMapFacts.not_mem_in_iff in Hwhere. rewrite <- Hctx_eq in Hwhere.
           destruct (PMap.mem (elt:=Component.interface) C ctx1) eqn:Hwhere';
             try discriminate.
           *** apply PMapFacts.mem_in_iff in Hwhere'. contradiction.
           *** auto.
        ** (* morphisms stuff *)
          unfold Morphisms.Proper, Morphisms.respectful.
          intros. subst. reflexivity.
      * reflexivity.
    + reflexivity.
    + reflexivity.
Qed.

Unset Implicit Arguments.

Lemma equal_states_partialize:
  forall ctx ics1 ics2 ips,
    CS.state_eq ics1 ics2 ->
    partial_state ctx ics1 ips ->
    partial_state ctx ics2 ips.
Proof.
  intros ctx ics1 ics2 ips.
  intros Hics_eq Hics1_partial.
  apply partialize_correct.
  apply partialize_correct in Hics1_partial.
  rewrite <- Hics1_partial.
  symmetry. f_equiv; auto.
Qed.

(* unpartializing partial states without holes *)

Definition unpartialize_stack_frame (frame: PartialPointer.t): Pointer.t :=
  match frame with
  | (C, None) =>
    (* bad case that shouldn't happen, just return first state *)
    (C, 1%positive, 0)
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
    ([], PMap.empty ComponentMemory.t, [], (1%positive, 1%positive, 0))
  end.

Inductive stack_without_holes: stack -> Prop :=
| stack_without_holes_nil:
    stack_without_holes nil
| stack_without_holes_cons: forall pgps C b o,
    stack_without_holes pgps ->
    stack_without_holes ((C, Some (b, o)) :: pgps).

Lemma to_partial_stack_with_empty_context_has_no_holes:
  forall gps,
    stack_without_holes (to_partial_stack gps []).
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
    to_partial_stack (unpartialize_stack pgps) [] = pgps.
Proof.
  intros pgps Hnoholes.
  induction Hnoholes; subst.
  - reflexivity.
  - simpl. rewrite IHHnoholes. reflexivity.
Qed.

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

Theorem unpartializing_complete_states:
  forall ics,
    CS.state_eq (unpartialize (partialize ics (PMap.empty Component.interface))) ics.
Proof.
  intros ics.
  CS.unfold_states. simpl.
  constructor;
    try reflexivity.
  - apply unpartializing_complete_stack.
  - apply Memory.filter_identity.
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
  PMapExtra.Disjoint mem1 mem2.

Inductive mergeable_states (ctx1 ctx2: Program.interface): state -> state -> Prop :=
| mergeable_states_first: forall pgps1 pmem1 regs pc C pgps2 pmem2,
    is_program_component (PC (pgps1, pmem1, regs, pc)) ctx1 ->
    is_context_component (CC (C, pgps2, pmem2)) ctx2 ->
    Pointer.component pc = C ->
    mergeable_stacks pgps1 pgps2 ->
    mergeable_memories pmem1 pmem2 ->
    mergeable_states ctx1 ctx2 (PC (pgps1, pmem1, regs, pc)) (CC (C, pgps2, pmem2))
| mergeable_states_second: forall pgps1 pmem1 regs pc C pgps2 pmem2,
    is_context_component (CC (C, pgps1, pmem1)) ctx1 ->
    is_program_component (PC (pgps2, pmem2, regs, pc)) ctx2 ->
    Pointer.component pc = C ->
    mergeable_stacks pgps1 pgps2 ->
    mergeable_memories pmem1 pmem2 ->
    mergeable_states ctx1 ctx2 (CC (C, pgps1, pmem1)) (PC (pgps2, pmem2, regs, pc)).

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

Definition merge_memories (mem1 mem2: Memory.t): Memory.t :=
  PMapExtra.update mem1 mem2.

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

Set Implicit Arguments.

Add Morphism (merge_partial_states)
    with signature
      state_eq ==> state_eq ==> state_eq
      as merge_partial_states_eq.
Proof.
  intros ips1 ips2 Heq1 ips1' ips2' Heq2.
  inversion Heq1; subst; inversion Heq2; subst; simpl.
  - constructor;
      try reflexivity.
    + assumption.
  - constructor;
      try reflexivity.
    + rewrite H0, H2.
      reflexivity.
  - constructor;
      try reflexivity.
    + rewrite H0, H1.
      reflexivity.
  - constructor;
      try reflexivity.
    + assumption.
Qed.

Unset Implicit Arguments.

(* transition system *)

Inductive initial_state (p: program) (ctx: Program.interface) : state -> Prop :=
| initial_state_intro: forall p' ics ips,
    linkable_programs p p' ->
    partial_state ctx ics ips ->
    CS.initial_state (program_link p p' (fst (prog_main p)) (snd (prog_main p))) ics ->
    initial_state p ctx ips.

Inductive final_state (p: program) (ctx: Program.interface) : state -> Prop :=
| final_state_program: forall p' ics ips,
    linkable_programs p p' ->
    ~ turn_of ips ctx ->
    partial_state ctx ics ips ->
    CS.final_state
      (init_genv (program_link p p' (fst (prog_main p)) (snd (prog_main p)))) ics ->
    final_state p ctx ips
| final_state_context: forall ips,
    turn_of ips ctx ->
    final_state p ctx ips.

Inductive step (ctx: Program.interface) (G: global_env)
  : state -> trace -> state -> Prop :=
| partial_step:
    forall p' ips t ips' ics ics',
      PMap.Equal (prog_interface p') ctx ->
      CS.step (extend_genv G (init_genv p')) ics t ics' ->
      partial_state ctx ics ips ->
      partial_state ctx ics' ips' ->
      step ctx G ips t ips'.

Theorem equal_states_step:
  forall ctx G ips1 t ips1' ips2 ips2',
    step ctx G ips1 t ips1' ->
    state_eq ips1 ips2 ->
    state_eq ips1' ips2' ->
    step ctx G ips2 t ips2'.
Proof.
  intros ctx G ips1 t ips1' ips2 ips2' Hstep Heq1 Heq2.
  inversion Hstep; subst.
  apply partial_step with (ics:=ics) (ics':=ics') (p':=p').
  + assumption.
  + assumption.
  + apply PS.partialize_correct.
    rewrite <- Heq1.
    apply PS.partialize_correct.
    assumption.
  + apply PS.partialize_correct.
    rewrite <- Heq2.
    apply PS.partialize_correct.
    assumption.
Qed.

Theorem equal_states_step_2:
  forall ctx G ips1 t ips1' ips2,
    state_eq ips1 ips2 ->
    step ctx G ips1 t ips1' ->
  exists ips2',
    step ctx G ips2 t ips2' /\ state_eq ips1' ips2'.
Proof.
  intros ctx G ips1 t ips1' ips2 Heq Hstep.
  inversion Hstep; subst.
  exists ips1'. split.
  - apply partial_step with (ics:=ics) (ics':=ics') (p':=p').
    + assumption.
    + assumption.
    + do 2 CS.unfold_states.
      inversion Heq; subst.
      * inversion H1; subst.
        constructor.
        ** PS.simplify_turn. auto.
        ** rewrite <- H4. assumption.
        ** reflexivity.
      * inversion H1; subst.
        constructor.
        ** PS.simplify_turn. auto.
        ** rewrite <- H5. assumption.
        ** reflexivity.
    + auto.
  - reflexivity.
Qed.

Theorem context_epsilon_step_is_silent:
  forall ctx G ips ips',
    step ctx G (CC ips) E0 ips' ->
    state_eq (CC ips) ips'.
Proof.
  intros ctx G ips ips' Hstep.
  inversion Hstep; subst.
  inversion H1; subst; PS.simplify_turn.
  inversion H2; subst; PS.simplify_turn.
  - (* contra *)
    assert (Pointer.component pc = Pointer.component pc0) as Hsame_comp. {
      inversion H0; subst;
        match goal with
        | Heq1: CS.state_eq _ _,
          Heq2: CS.state_eq _ _ |- _ =>
          inversion Heq1; subst; inversion Heq2; subst
        end;
        try (rewrite Pointer.inc_preserves_component; reflexivity);
        try (symmetry; assumption).
      + erewrite find_label_in_component_1; eauto.
      + erewrite find_label_in_procedure_1; eauto.
    }
    rewrite Hsame_comp in *.
    contradiction.
  - constructor.
    + assert (Pointer.component pc = Pointer.component pc0) as Hsame_comp. {
        inversion H0; subst;
          match goal with
          | Heq1: CS.state_eq _ _,
            Heq2: CS.state_eq _ _ |- _ =>
            inversion Heq1; subst; inversion Heq2; subst
          end;
          try (rewrite Pointer.inc_preserves_component; reflexivity);
          try (symmetry; assumption).
        + erewrite find_label_in_component_1; eauto.
        + erewrite find_label_in_procedure_1; eauto.
      }
      apply Hsame_comp.
    + inversion H0; subst;
        match goal with
        | Heq1: CS.state_eq _ _,
          Heq2: CS.state_eq _ _ |- _ =>
          inversion Heq1; subst; inversion Heq2; subst
        end; reflexivity.
    + inversion H0; subst;
        match goal with
        | Heq1: CS.state_eq _ _,
          Heq2: CS.state_eq _ _ |- _ =>
          inversion Heq1; subst; inversion Heq2; subst
        end;
        try match goal with
        | Hfilter1: PMap.Equal ?PMEM1 (PMapExtra.filter _ ?MEM1),
          Hfilter2: PMap.Equal ?PMEM2 (PMapExtra.filter _ ?MEM2),
          Heq1: PMap.Equal ?MEM1 ?MEM3,
          Heq2: PMap.Equal ?MEM2 ?MEM3 |- _ =>
          rewrite Hfilter1, Hfilter2;
          apply Memory.equivalence_under_filter;
          rewrite Heq1, Heq2;
          reflexivity
        end.
      * rewrite H6.
        erewrite Memory.context_store_is_filtered with (ptr:=ptr) (mem':=mem').
        ** apply Memory.equivalence_under_filter. symmetry. assumption.
        ** rewrite H10. assumption.
        ** eassumption.
        ** rewrite H5. apply Memory.equivalence_under_filter. assumption.
      * rewrite H6.
        erewrite Memory.context_allocation_is_filtered with (mem':=mem').
        ** apply Memory.equivalence_under_filter. symmetry. assumption.
        ** eassumption.
        ** rewrite Pointer.inc_preserves_component. eassumption.
        ** rewrite H5. apply Memory.equivalence_under_filter. assumption.
Qed.

Corollary context_epsilon_star_is_silent:
  forall ctx G ips ctx_state ips',
    state_eq ips (CC ctx_state) ->
    star (step ctx) G ips E0 ips' ->
    state_eq ips ips'.
Proof.
  intros ctx G ips ctx_state ips' Heq_ctx Hstar.
  dependent induction Hstar; subst.
  - reflexivity.
  - symmetry in H0. apply Eapp_E0_inv in H0. destruct H0. subst.
    rewrite Heq_ctx.
    destruct (equal_states_step_2 ctx G s1 E0 s2 (CC ctx_state) Heq_ctx H)
      as [s2' []].
    apply context_epsilon_step_is_silent in H0.
    rewrite <- H0 in H1. rewrite <- H1.
    apply IHHstar; auto.
Qed.

(* this should hold even for program steps *)
Theorem context_same_trace_determinism:
  forall ctx G ips ctx_state t ctx_state',
    state_eq (CC ctx_state) ips ->
    step ctx G ips t (CC ctx_state') ->
  forall ctx_state'',
    step ctx G ips t (CC ctx_state'') ->
    state_eq (CC ctx_state') (CC ctx_state'').
Proof.
  intros ctx G ips ctx_state t ctx_state' Heq Hstep1 ctx_state'' Hstep2.
  inversion Heq; subst.
  inversion Hstep1; subst; inversion Hstep2; subst.
  inversion H1; subst; inversion H3; subst.
  inversion H6; subst; inversion H7; subst.

  inversion H0; subst.
  + inversion H11; subst; inversion H20; subst.
    inversion H5; subst.
    * inversion H21; subst; inversion H23; subst.
      PS.simplify_turn.
      constructor.
      ** do 2 rewrite Pointer.inc_preserves_component.
         symmetry. assumption.
      ** assumption.
      ** rewrite <- H2 in H13.
         rewrite <- H2 in H17.

         rewrite <- H31 in H30.
         pose proof (Memory.equivalence_under_filter
                       mem mem0 (fun k _ => negb (PMap.mem k ctx)) H30).
         rewrite H24 in H13. rewrite <- H13 in H10.

         rewrite <- H36 in H35.
         pose proof (Memory.equivalence_under_filter
                       mem1 mem2 (fun k _ => negb (PMap.mem k ctx)) H35).
         rewrite H25 in H17. rewrite <- H15 in H17.

         rewrite H10, H17.
         reflexivity.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
Admitted.

(* partial semantics *)

Section Semantics.
  Variable p: program.
  Variable ctx: Program.interface.

  Let G := init_genv p.

  Hypothesis valid_program:
    well_formed_program p.

  Hypothesis merged_interface_is_closed:
    closed_interface (PMapExtra.update (prog_interface p) ctx).

  Definition sem :=
    @Semantics_gen state global_env (step ctx)
                   (initial_state p ctx)
                   (final_state p ctx) G.
End Semantics.
End PS.
