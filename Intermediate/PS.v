Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
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

Lemma ptr_within_partial_frame_inv_2 :
  forall ptr1 ptr2 (ctx : Program.interface),
    to_partial_frame (domm ctx) ptr1 = to_partial_frame (domm ctx) ptr2 ->
    Pointer.component ptr1 \notin domm ctx ->
    ptr1 = ptr2.
Proof.
  intros ptr1 ptr2 ctx Heq Hnotin.
  destruct ptr1 as [[C1 b1] o1].
  destruct ptr2 as [[C2 b2] o2].
  rewrite PS.ptr_within_partial_frame_2 in Heq.
  - destruct (C2 \in domm ctx) eqn:Hcase.
    + rewrite PS.ptr_within_partial_frame_1 in Heq.
      * now inversion Heq.
      * now rewrite Hcase.
    + rewrite PS.ptr_within_partial_frame_2 in Heq.
      * now inversion Heq.
      * now rewrite Hcase.
  - destruct (C1 \in domm ctx) eqn:Hcase; now rewrite Hcase in Hnotin.
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

(* Memory partialization. *)

(* RB: TODO: Here and above, Program.interface vs. fset. *)
Definition to_partial_memory (mem : Memory.t) (ctx : {fset Component.id}) :=
  filterm (fun k _ => negb (k \in ctx)) mem.

(* RB: TODO: More properly, this seems to belong in Machine.Memory. However, it
   is natural to resort to a notion of partial memory that seems logically
   related to the supporting components of PS. Again, note, however, that this
   notion of partial memory is already used in the Memory module, and it may be
   a good idea to relocate our compact definitions there.

   Otherwise, this is a more convenient wrapper for
   context_store_in_partialized_memory which does not require the destruction of
   pointers, and could conceivably replace the wrappee throughout the
   development. *)
Lemma program_store_to_partialized_memory
      ptr (iface : Program.interface) mem mem' v :
  Pointer.component ptr \in domm iface ->
  Memory.store mem ptr v = Some mem' ->
  to_partial_memory mem (domm iface) = to_partial_memory mem' (domm iface).
Proof.
  destruct ptr as [[C b] o]. simpl.
  intros Hdome Hsome.
  unfold to_partial_memory. symmetry.
  eapply context_store_in_partialized_memory; eassumption.
Qed.

(* RB: TODO: Same notes as above.
   Cf.  program_allocation_in_partialized_memory_strong. *)
Lemma program_allocation_to_partialized_memory
      C (iface : Program.interface) size mem mem' ptr :
  C \in domm iface ->
  Memory.alloc mem C size = Some (mem', ptr) ->
  to_partial_memory mem (domm iface) = to_partial_memory mem' (domm iface).
Proof.
  destruct ptr as [[C' b] o]. simpl.
  intros Hdome Hsome.
  unfold to_partial_memory. symmetry.
  eapply context_allocation_in_partialized_memory; eassumption.
Qed.

(* RB: TODO: On a related note to that above, consider using [Pointer.component]
   in results such as [program_store_in_partialized_memory]. This will save us
   the trouble of having to destruct pointers to use these results. *)

(* RB: TODO: This is a specialized version that utilizes premises in the exact
   shape they are available in our contexts. It could be a wrapper of a slightly
   more abstract form of the lemma, where the two memories are related, say, by
   their domains. (Incidentally, do away with uses of [domm] here?) *)
Remark prog_ctx_sim_domm_memories
       (mem1 mem2 : Memory.t) (iface1 iface2 : Program.interface) :
    mergeable_interfaces iface1 iface2 ->
    (* Specialized assumptions:
       - mem2's domain is that of iface1 and iface2.
       - mem0 and mem2's domains are related, so in mem0 there is nothing outside
         of iface1 and iface2.
       - mem0 steps to mem1, so their domains coincide: mem1 is also "clean". *)
  forall G gps0 mem0 regs0 pc0 t gps1 regs1 pc1,
    CS.step G (gps0, mem0, regs0, pc0) t (gps1, mem1, regs1, pc1) ->
    to_partial_memory mem2 (domm iface1) =
    to_partial_memory mem0 (domm iface1) ->
  forall gps2 regs2 pc2,
    CS.comes_from_initial_state (gps2, mem2, regs2, pc2)
                                (unionm iface1 iface2) ->
    domm mem1 = domm mem2.
Admitted. (* Grade 2. *)

Inductive partial_state (ctx: Program.interface) : CS.state -> PS.state -> Prop :=
| ProgramControl: forall gps pgps mem pmem regs pc,
    (* program has control *)
    is_program_component (PC (pgps, pmem, regs, pc)) ctx ->

    (* we forget about context memories *)
    pmem = to_partial_memory mem (domm ctx) ->

    (* we put holes in place of context information in the stack *)
    pgps = to_partial_stack gps (domm ctx) ->

    partial_state ctx (gps, mem, regs, pc) (PC (pgps, pmem, regs, pc))

| ContextControl: forall gps pgps mem pmem regs pc,
    (* context has control *)
    is_context_component (CC (Pointer.component pc, pgps, pmem)) ctx ->

    (* we forget about context memories *)
    pmem = to_partial_memory mem (domm ctx) ->

    (* we put holes in place of context information in the stack *)
    pgps = to_partial_stack gps (domm ctx) ->

    partial_state ctx (gps, mem, regs, pc) (CC (Pointer.component pc, pgps, pmem)).

Definition partialize (ics: CS.state) (ctx: Program.interface) : PS.state :=
  let '(gps, mem, regs, pc) := ics in
  if Pointer.component pc \in domm ctx then
    CC (Pointer.component pc,
        to_partial_stack gps (domm ctx),
        to_partial_memory mem (domm ctx))
  else
    PC (to_partial_stack gps (domm ctx),
        to_partial_memory mem (domm ctx),
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
  unfold to_partial_memory. rewrite filterm_identity. reflexivity.
Qed.

(* merging partial states *)

Inductive mergeable_stack_frames: PartialPointer.t -> PartialPointer.t -> Prop :=
| mergeable_stack_frames_first: forall C b1 o1,
    mergeable_stack_frames (C, Some (b1, o1)) (C, None)
| mergeable_stack_frames_second: forall C b2 o2,
    mergeable_stack_frames (C, None) (C, Some (b2, o2)).

Inductive mergeable_stacks : stack -> stack -> Prop :=
| mergeable_stacks_nil:
    mergeable_stacks [] []
| mergeable_stacks_cons: forall pgps1 pgps2 frame1 frame2,
    mergeable_stacks pgps1 pgps2 ->
    mergeable_stack_frames frame1 frame2 ->
    mergeable_stacks (frame1 :: pgps1) (frame2 :: pgps2).

(* RB: TODO: We may want to either define what it means for each component to
   be mergeable as close as possible to its original definition, or collect
   all these together. The current definition of the top-level proof points to
   interface mergeability at least not belonging here, but in the Common part
   of the development. (Is it possible to reorganize the components of the top-
   level proof, in particular the proof of composition where an assumption of
   this type appears, so that this detail is hidden?) *)

Definition mergeable_memories (mem1 mem2: Memory.t): Prop :=
  fdisjoint (domm mem1) (domm mem2).

(* NOTE: Instance of a more general property which may be added to CoqUtils.
   TODO: Harmonize naming of two directions or unify with iff.
         Reduce amount of lemmas, possibly supplement with tactics. *)
Lemma domm_partition :
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall gps mem regs pc,
    CS.comes_from_initial_state (gps, mem, regs, pc) (unionm ctx1 ctx2) ->
    Pointer.component pc \notin domm ctx2 ->
    Pointer.component pc \in domm ctx1.
Proof.
  intros ctx1 ctx2 Hmerge gps mem regs pc
         [p [mainP [ics [t [Hwf [Hmain [Hiface [Hini HStar]]]]]]]].
  revert ctx1 ctx2 Hmerge Hiface Hini.
  simpl in HStar.
  remember CS.step as step.
  remember (prepare_global_env p) as env.
  remember (gps, mem, regs, pc) as ics'.
  revert Heqstep p mainP Hwf Hmain Heqenv gps mem regs pc Heqics'.
  apply star_iff_starR in HStar.
  induction HStar as [| s1 t1 s2 t2 s3 t12 HstarR IHHStar Hstep Ht12];
    intros Heqstep p mainP Hwf Hmain Heqenv gps mem regs pc Heqics'
           ctx1 ctx2 Hmerge Hiface Hini Hpc2;
    subst.
  - unfold CS.initial_state, CS.initial_machine_state in Hini.
    rewrite Hmain in Hini.
    destruct (prepare_procedures p (prepare_initial_memory p))
      as [[mem_p dummy] entrypoints_p] eqn:Hprocs.
    inversion Hini; subst; simpl in *.
    inversion Hwf as [_ _ _ _ _ Hmain_existence _].
    specialize (Hmain_existence _ Hmain).
    destruct Hmain_existence as [main_procs [Hmain_procs Hdomm_main_procs]].
    (* TODO: Here is the recurring dommP inelegance again. *)
    assert (Hdomm_procs : Component.main \in domm (prog_procedures p))
      by (apply /dommP; eauto).
    inversion Hwf as [_ Hdef_procs _ _ _ _ _].
    rewrite <- Hdef_procs, Hiface in Hdomm_procs.
    assert (exists CI, (unionm ctx1 ctx2) Component.main = Some CI)
      as [CI Hctx12]
      by (apply /dommP; assumption).
    assert (Hctx2 : ctx2 Component.main = None)
      by (apply /dommPn; assumption).
    rewrite unionmE in Hctx12.
    destruct (ctx1 Component.main) as [main1 |] eqn:Hcase1;
      rewrite Hcase1 in Hctx12;
      simpl in Hctx12.
    + apply /dommP. now eauto.
    + congruence.
  - (* Peel trivial layers off IH. *)
    destruct s2 as [[[gps2 mem2] regs2] pc2].
    specialize (IHHStar (eq_refl _) _ _ Hwf Hmain (eq_refl _)
               gps2 mem2 regs2 pc2 (eq_refl _) ctx1 ctx2 Hmerge Hiface Hini).
    (* Continue by case analysis. *)
    inversion Hstep; subst;
      (* Most cases are straightforward. *)
      try (rewrite Pointer.inc_preserves_component;
           rewrite Pointer.inc_preserves_component in Hpc2;
           auto).
    (* The interesting cases involve tests, jumps, calls and returns. *)
    + match goal with
      | H : find_label_in_component _ pc2 _ = Some _ |- _ =>
        apply find_label_in_component_1 in H;
        rewrite <- H;
        rewrite <- H in Hpc2;
        now auto
      end.
    + match goal with
      | H : Pointer.component pc = Pointer.component pc2 |- _ =>
        rewrite H;
        rewrite H in Hpc2;
        now auto
      end.
    + match goal with
      | H : find_label_in_procedure _ pc2 _ = Some _ |- _ =>
        apply find_label_in_procedure_1 in H;
        rewrite <- H;
        rewrite <- H in Hpc2;
        now auto
      end.
    + (* Calls are well-formed events, so their components are properly imported.
         Because the global interface is closed, this implies they are exported
         at the right place, from which they can be concluded be part of said
         global interface, on one side or the other. *)
      simpl in *.
      match goal with
      | H1 : starR CS.step _ _ ?T1 _, H2 : CS.step _ _ ?T2 _ |- _ =>
        pose proof starR_step H1 H2 (eq_refl _) as Htrace
      end.
      apply star_iff_starR in Htrace.
      pose proof CS.intermediate_well_formed_trace _ _ _ _ _ Htrace Hini Hmain Hwf as Hwft.
      (* We need to play with sequences here; let's get the interesting part
         right first, but not the information is in Hwft. *)
      assert (Hwfe : Traces.well_formed_event (prog_interface p)
                                              (ECall (Pointer.component pc2) P call_arg C')).
      {
        unfold Traces.well_formed_trace in Hwft.
        apply andb_prop in Hwft. destruct Hwft as [_ Hall].
        rewrite seq.all_cat in Hall.
        apply andb_prop in Hall. destruct Hall as [_ Hall].
        rewrite seq.all_seq1 in Hall.
        assumption.
      }
      apply andb_prop in Hwfe. destruct Hwfe as [_ Himported].
      apply imported_procedure_iff in Himported.
      inversion Hmerge as [_ Hclosed_exported].
      rewrite <- Hiface in Hclosed_exported.
      specialize (Hclosed_exported _ _ _ Himported).
      destruct Hclosed_exported as [CI [Hhas_comp Hexporting]].
      apply has_component_in_domm_prog_interface in Hhas_comp.
      (* TODO: Apply dommP on premises less haphazardly. *)
      assert (exists CI', (prog_interface p) C' = Some CI')
        as [CI' HCI']
        by (by apply /dommP).
      rewrite Hiface unionmE in HCI'.
      destruct (ctx1 C') as [CI'' |] eqn:Hcase.
      * apply /dommP. now eauto.
      * rewrite Hcase in HCI'. simpl in HCI'.
        (* TODO: Same artifact on dommP as above. *)
        assert (Hcontra : C' \in domm ctx2) by (apply /dommP; eauto).
        rewrite Hcontra in Hpc2.
        discriminate.
      (* Returns are well-bracketed events, each paired with a prior matching
         call event. The call for the return is itself a well-formed event whose
         source component correctly imports the requisite components. From this
         fact we can case analyze the side of the interface the source is in. *)
    + (* NOTE: Comment above breaks COQDEP build if placed here in this file! *)
      match goal with
      | H1 : starR CS.step _ _ ?T1 _, H2 : CS.step _ _ ?T2 _ |- _ =>
        pose proof starR_step H1 H2 (eq_refl _) as Htrace
      end.
      apply star_iff_starR in Htrace.
      apply CS.intermediate_well_bracketed_trace in Htrace.
      rewrite (CS.initial_state_stack_state0 _ _ Hini) in Htrace.
      destruct (Traces.well_bracketed_trace_inv Htrace) as [t1' [Pid [arg [t2 Ht1]]]].
      subst t1.
      assert (Hwfe : Traces.well_formed_event (prog_interface p)
                                              (ECall (Pointer.component pc) Pid arg
                                                     (Pointer.component pc2))).
      {
        apply star_iff_starR in HstarR.
        pose proof CS.intermediate_well_formed_trace _ _ _ _ _ HstarR Hini Hmain Hwf as Hwft.
        unfold Traces.well_formed_trace in Hwft.
        apply andb_prop in Hwft. destruct Hwft as [_ Hall].
        rewrite seq.all_cat in Hall.
        apply andb_prop in Hall. destruct Hall as [_ Hall].
        apply andb_prop in Hall. destruct Hall as [Hwfe _].
        assumption.
      }
      apply andb_prop in Hwfe. destruct Hwfe as [_ Himported].
      apply imported_procedure_iff in Himported.
      destruct Himported as [CI [Hhas_comp _]].
      unfold Program.has_component in Hhas_comp.
      rewrite Hiface unionmE in Hhas_comp.
      destruct (ctx1 (Pointer.component pc)) as [CI' |] eqn:Hcase;
        rewrite Hcase in Hhas_comp;
        simpl in Hhas_comp.
      * apply /dommP. now eauto.
      * assert (Hcontra : ctx2 (Pointer.component pc) = None)
          by (apply /dommPn; assumption).
        (* TODO: Above, better application of dommPn on a premise. *)
        rewrite Hcontra in Hhas_comp. discriminate.
Qed.

Lemma domm_partition_notin :
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall C,
    C \in domm ctx2 ->
    C \notin domm ctx1.
Proof.
by move=> ctx1 ctx2 [[_]]; rewrite fdisjointC=> /fdisjointP.
Qed.

(* RB: TODO: Complete assumptions, possibly rephrase in terms of _neither. *)
Lemma domm_partition_in_both ctx1 ctx2 C :
  mergeable_interfaces ctx1 ctx2 ->
  C \in domm ctx1 ->
  C \in domm ctx2 ->
  False.
Proof.
  intros H H0 H1. apply (domm_partition_notin H) in H1.
  now rewrite H0 in H1.
Qed.

Lemma domm_partition_in_neither ctx1 ctx2 :
    mergeable_interfaces ctx1 ctx2 ->
  forall gps mem regs pc,
    CS.comes_from_initial_state (gps, mem, regs, pc) (unionm ctx1 ctx2) ->
    Pointer.component pc \notin domm ctx1 ->
    Pointer.component pc \notin domm ctx2 ->
    False.
Proof.
  intros Hmerge_ifaces gps mem regs pc Hcomes_from Hnotin1 Hnotin2.
  apply (domm_partition Hmerge_ifaces Hcomes_from) in Hnotin2.
  now rewrite Hnotin2 in Hnotin1.
Qed.

(* RB: TODO: Complete assumptions as above.
   Look for places where instances of this lemma are inlined in the proofs? *)
Lemma domm_partition_in_notin (ctx1 : Program.interface) C :
  C \in domm ctx1 ->
  C \notin domm ctx1 ->
  False.
Proof.
  intros Hin Hnotin. now rewrite Hin in Hnotin.
Qed.

Lemma domm_partition_program_link_in_neither p c :
  well_formed_program p ->
  well_formed_program c ->
  closed_program (program_link p c) ->
  Component.main \notin domm (prog_interface p) ->
  Component.main \notin domm (prog_interface c) ->
  False.
Proof.
  intros [_ _ _ _ _ _ [_ Hmainp]] [_ _ _ _ _ _ [_ Hmainc]]
         [_ [main [_ [Hmain _]]]] Hmainp' Hmainc'.
  destruct (prog_main p) as [mainp |] eqn:Hcasep.
  - specialize (Hmainp (eq_refl _)).
    rewrite Hmainp in Hmainp'.
    discriminate.
  - destruct (prog_main c) as [mainc |] eqn:Hcasec.
    +  specialize (Hmainc (eq_refl _)).
       rewrite Hmainc in Hmainc'.
       discriminate.
    + simpl in Hmain.
      rewrite Hcasep Hcasec in Hmain.
      discriminate.
Qed.

Lemma domm_partition_in_union_in_neither (ctx1 ctx2 : Program.interface) C :
  C \in domm (unionm ctx1 ctx2) ->
  C \notin domm ctx1 ->
  C \notin domm ctx2 ->
  False.
Proof.
  intros Hin12 Hnotin1 Hnotin2.
  destruct (C \in domm ctx1) eqn:Hcase1; first discriminate.
  destruct (C \in domm ctx2) eqn:Hcase2; first discriminate.
  assert (exists v, (unionm ctx1 ctx2) C = Some v)
    as [v Hv12]
    by now apply /dommP.
  rewrite unionmE in Hv12.
  assert (Hv1 : ctx1 C = None) by (apply /dommPn; congruence).
  assert (Hv2 : ctx2 C = None) by (apply /dommPn; congruence).
  rewrite Hv1 Hv2 in Hv12. discriminate.
Qed.

Inductive mergeable_states (ctx1 ctx2: Program.interface): state -> state -> Prop :=
| mergeable_states_intro: forall ics ips1 ips2,
    mergeable_interfaces ctx1 ctx2 ->
    CS.comes_from_initial_state ics (unionm ctx1 ctx2) ->
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
  forall mem regs pc,
    CS.comes_from_initial_state (gps, mem, regs, pc) (unionm ctx1 ctx2) ->
    mergeable_stacks (to_partial_stack gps (domm ctx1)) (to_partial_stack gps (domm ctx2)).
Proof.
  intros Hmerge mem regs pc
         [p [mainP [ics [t [Hwf [Hmain [Hiface [Hini HStar]]]]]]]].
  revert ctx1 ctx2 Hmerge Hiface Hini.
  simpl in HStar.
  remember CS.step as step.
  remember (prepare_global_env p) as env.
  remember (gps, mem, regs, pc) as ics'.
  revert Heqstep p mainP Hwf Hmain Heqenv gps mem regs pc Heqics'.
  apply star_iff_starR in HStar.
  induction HStar as [| s1 t1 s2 t2 s3 t12 HstarR IHHStar Hstep Ht12];
    intros Heqstep p mainP Hwf Hmain Heqenv gps mem regs pc Heqics'
           ctx1 ctx2 Hmerge Hiface Hini;
    subst.
  - unfold CS.initial_state, CS.initial_machine_state in Hini.
    rewrite Hmain in Hini.
    destruct (prepare_procedures p (prepare_initial_memory p))
      as [[mem_p _] entrypoints_p].
    inversion Hini; subst.
    now constructor.
  - destruct s2 as [[[gps2 mem2] regs2] pc2].
    specialize (IHHStar (eq_refl _) _ _ Hwf Hmain (eq_refl _)
                        gps2 mem2 regs2 pc2 (eq_refl _) _ _ Hmerge Hiface Hini).
    inversion Hstep; subst;
      (* In most cases, the stack is unchanged. The goal is exactly the IH. *)
      try assumption.
    + (* ICall case *)
      simpl. constructor.
      * (* On the one hand, we have the base stack in the IH. *)
        assumption.
      * (* On the other, we have the new frame. *)
        simpl.
        (* TODO: This kind of useful results can be expressed easily as lemmas
           in the fashion of existing results, e.g., domm_partition (ideally,
           derive these from the simplest formulation). *)
        assert (Hdomm : Pointer.component pc2 \in domm ctx1 \/
                        Pointer.component pc2 \in domm ctx2).
        {
          destruct (Pointer.component pc2 \in domm ctx1) eqn:Hcase.
          - left. reflexivity.
          - right.
            eapply domm_partition.
            + apply mergeable_interfaces_sym.
              eassumption.
            + rewrite unionmC.
              * apply star_iff_starR in HstarR.
                now repeat (esplit; eauto).
              * inversion Hmerge as [[_ Hdisjoint] _].
                rewrite fdisjointC.
                assumption.
            + rewrite Hcase. reflexivity.
        }
        destruct Hdomm as [Hdomm | Hdomm];
          rewrite <- Pointer.inc_preserves_component in Hdomm.
        (* TODO: The following two cases are symmetric and could be refactored. *)
        -- assert (Hdomm' : Pointer.component (Pointer.inc pc2) \in domm ctx2 = false).
           {
             apply mergeable_interfaces_sym in Hmerge.
             pose proof domm_partition_notin Hmerge Hdomm as Hdomm'.
             (* TODO: There are probably more succinct ways to do this. *)
             destruct (Pointer.component (Pointer.inc pc2) \in domm ctx2) eqn:Hcase.
             - rewrite Hcase in Hdomm'. discriminate.
             - reflexivity.
           }
           rewrite (ptr_within_partial_frame_1 Hdomm).
           rewrite (ptr_within_partial_frame_2 Hdomm').
           now constructor.
        -- assert (Hdomm' : Pointer.component (Pointer.inc pc2) \in domm ctx1 = false).
           {
             pose proof domm_partition_notin Hmerge Hdomm as Hdomm'.
             (* TODO: There are probably more succinct ways to do this. *)
             destruct (Pointer.component (Pointer.inc pc2) \in domm ctx1) eqn:Hcase.
             - rewrite Hcase in Hdomm'. discriminate.
             - reflexivity.
           }
           rewrite (ptr_within_partial_frame_1 Hdomm).
           rewrite (ptr_within_partial_frame_2 Hdomm').
           now constructor.
    + (* IReturn case: the IH contains the desired substack. *)
      inversion IHHStar; subst.
      assumption.
Qed.

Lemma mergeable_memories_sym:
  forall pmem1 pmem2,
    mergeable_memories pmem1 pmem2 ->
    mergeable_memories pmem2 pmem1.
Proof.
  intros pmem1 pmem2 Hmergeable.
  unfold mergeable_memories in *.
  rewrite fdisjointC. auto.
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
    + apply CS.comes_from_initial_state_mergeable_sym; eassumption.
    + assumption.
    + assumption.
Qed.

(* TODO: Consider potential refactors with other [mergeable_] results
   as the proofs are being built. *)
Lemma mergeable_states_program_to_program ctx1 ctx2 ps1 ps2 :
  mergeable_states ctx1 ctx2 ps1 ps2 ->
  is_program_component ps1 ctx1 ->
  is_program_component ps2 ctx1.
Proof.
  intros Hmergeable Hpc.
  inversion Hmergeable as [ics ? ? Hmergeable_ifaces Hcomes_from Hpartial1 Hpartial2];
    subst.
  inversion Hpartial1 as [? ? ? ? ? ? Hpc1 | ? ? ? ? ? ? Hcc1]; subst;
    inversion Hpartial2 as [? ? ? ? ? ? Hpc2 | ? ? ? ? ? ? Hcc2]; subst.
  - now destruct (domm_partition_in_neither Hmergeable_ifaces Hcomes_from Hpc1 Hpc2).
  - assumption.
  - assumption.
  - now destruct (domm_partition_in_both Hmergeable_ifaces Hcc1 Hcc2).
Qed.

Lemma mergeable_states_program_to_context ctx1 ctx2 ps1 ps2 :
  mergeable_states ctx1 ctx2 ps1 ps2 ->
  is_program_component ps1 ctx1 ->
  is_context_component ps2 ctx2.
Proof.
  intros Hmergeable Hpc.
  inversion Hmergeable as [ics ? ? Hmergeable_ifaces Hcomes_from Hpartial1 Hpartial2];
    subst.
  inversion Hpartial1 as [? ? ? ? ? ? Hpc1 | ? ? ? ? ? ? Hcc1]; subst;
    inversion Hpartial2 as [? ? ? ? ? ? Hpc2 | ? ? ? ? ? ? Hcc2]; subst.
  - now destruct (domm_partition_in_neither Hmergeable_ifaces Hcomes_from Hpc1 Hpc2).
  - assumption.
  - now destruct (domm_partition_in_notin Hcc1 Hpc).
  - now destruct (domm_partition_in_both Hmergeable_ifaces Hcc1 Hcc2).
Qed.

Lemma mergeable_states_context_to_context ctx1 ctx2 ps1 ps2 :
  mergeable_states ctx1 ctx2 ps1 ps2 ->
  is_context_component ps1 ctx1 ->
  is_context_component ps2 ctx1.
Proof.
  intros Hmergeable Hpc.
  inversion Hmergeable as [ics ? ? Hmergeable_ifaces Hcomes_from Hpartial1 Hpartial2];
    subst.
  inversion Hpartial1 as [? ? ? ? ? ? Hpc1 | ? ? ? ? ? ? Hcc1]; subst;
    inversion Hpartial2 as [? ? ? ? ? ? Hpc2 | ? ? ? ? ? ? Hcc2]; subst.
  - now destruct (domm_partition_in_neither Hmergeable_ifaces Hcomes_from Hpc1 Hpc2).
  - assumption.
  - assumption.
  - now destruct (domm_partition_in_both Hmergeable_ifaces Hcc1 Hcc2).
Qed.

Lemma mergeable_states_context_to_program ctx1 ctx2 ps1 ps2 :
  mergeable_states ctx1 ctx2 ps1 ps2 ->
  is_context_component ps1 ctx1 ->
  is_program_component ps2 ctx2.
Proof.
  intros Hmergeable Hpc.
  inversion Hmergeable as [ics ? ? Hmergeable_ifaces Hcomes_from Hpartial1 Hpartial2];
    subst.
  inversion Hpartial1 as [? ? ? ? ? ? Hpc1 | ? ? ? ? ? ? Hcc1]; subst;
    inversion Hpartial2 as [? ? ? ? ? ? Hpc2 | ? ? ? ? ? ? Hcc2]; subst.
  - now destruct (domm_partition_in_neither Hmergeable_ifaces Hcomes_from Hpc1 Hpc2).
  - destruct (domm_partition_in_notin Hpc Hpc1).
  - assumption.
  - now destruct (domm_partition_in_both Hmergeable_ifaces Hcc1 Hcc2).
Qed.

(* Merged stacks and their properties. *)

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
    eapply mergeable_stacks_partition; eassumption.
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

Lemma unpartialize_stack_frame_partition:
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall ptr,
    Pointer.component ptr \in domm (unionm ctx1 ctx2) ->
    unpartialize_stack_frame
      (merge_stack_frames ((to_partial_frame (domm ctx1) ptr),
                           (to_partial_frame (domm ctx2) ptr))) =
    ptr.
Proof.
  intros ctx1 ctx2 Hmergeable ptr Hdomm.
  destruct (Pointer.component ptr \in domm ctx1) eqn:Hcase1;
    destruct (Pointer.component ptr \in domm ctx2) eqn:Hcase2;
    unfold PS.to_partial_frame;
    rewrite Hcase1 Hcase2; simpl.
  - exfalso. eapply domm_partition_in_both; eassumption.
  - now rewrite Pointer.compose.
  - now rewrite Pointer.compose.
  - assert (Hmap1 : ctx1 (Pointer.component ptr) = None)
      by (apply /dommPn; unfold negb; now rewrite Hcase1).
    assert (Hmap2 : ctx2 (Pointer.component ptr) = None)
      by (apply /dommPn; unfold negb; now rewrite Hcase2).
    assert (exists v, (unionm ctx1 ctx2) (Pointer.component ptr) = Some v)
      as [Ci Hunion]
      by now apply /dommP.
    now rewrite unionmE Hmap1 Hmap2 in Hunion.
Qed.

(* RB: TODO: Add stack well-formedness w.r.t. interfaces. *)
Lemma merge_stacks_partition:
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall gps mem regs pc,
    CS.comes_from_initial_state (gps, mem, regs, pc) (unionm ctx1 ctx2) ->
    unpartialize_stack
      (merge_stacks
         (to_partial_stack gps (domm ctx1))
         (to_partial_stack gps (domm ctx2)))
    = gps.
Admitted. (* Grade 2. RB: Assigned to FG. *)

(* RB: TODO: Add stack well-formedness w.r.t. interfaces.
   This follows from the well-bracketedness of traces. More generally, the
   merge_stacks_partition property holds whenever the domain of the stack is
   that of the mergeable interfaces. In particular, this property is satisfied
   by stacks that originate from a correct program execution. *)
Lemma merge_stacks_partition_cons:
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall frame gps mem regs pc,
    CS.comes_from_initial_state (frame :: gps, mem, regs, pc) (unionm ctx1 ctx2) ->
    unpartialize_stack
      (merge_stacks
         (to_partial_stack gps (domm ctx1))
         (to_partial_stack gps (domm ctx2)))
    = gps.
Admitted. (* Grade 2. RB: Assigned to FG. *)

(* RB: TODO: Add stack well-formedness w.r.t. interfaces. *)
Lemma merge_stacks_partition_emptym:
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall gps mem regs pc,
    CS.comes_from_initial_state (gps, mem, regs, pc) (unionm ctx1 ctx2) ->
    merge_stacks (to_partial_stack gps (domm ctx1))
                 (to_partial_stack gps (domm ctx2)) =
    to_partial_stack gps fset0.
Admitted. (* Grade 2: RB: Assigned to FG. *)

Lemma unpartialize_stack_merge_stacks_cons_partition:
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall ptr pgps1 pgps2,
    Pointer.component ptr \in domm (unionm ctx1 ctx2) ->
    unpartialize_stack
      (merge_stacks (to_partial_frame (domm ctx1) ptr :: pgps1)
                    (to_partial_frame (domm ctx2) ptr :: pgps2)) =
    ptr :: unpartialize_stack (merge_stacks pgps1 pgps2).
Proof.
  intros ctx1 ctx2 Hmerge_ifaces ptr pgps1 pgps2 Hptr.
  simpl.
  now rewrite (unpartialize_stack_frame_partition Hmerge_ifaces).
Qed.

(* RB: TODO: Verify the necessary hypotheses for this lemma and its sibling.
   In what provenance conditions are needed on the stacks? Can they be weaker
   than those given here? (This extends beyond extracting parts of the given
   [CS.comes_from_initial_state].) *)
Lemma to_partial_stack_merge_stacks_left:
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall gps1 mem1 regs1 pc1,
    CS.comes_from_initial_state (gps1, mem1, regs1, pc1) (unionm ctx1 ctx2) ->
  forall gps2 mem2 regs2 pc2,
    CS.comes_from_initial_state (gps2, mem2, regs2, pc2) (unionm ctx1 ctx2) ->
    to_partial_stack gps1 (domm ctx1) = to_partial_stack gps2 (domm ctx1) ->
    to_partial_stack
      (unpartialize_stack
         (merge_stacks (to_partial_stack gps1 (domm ctx1))
                       (to_partial_stack gps2 (domm ctx2))))
      (domm ctx1) =
    to_partial_stack gps1 (domm ctx1).
Admitted. (* Grade 2. Note comments. *)

Corollary to_partial_stack_merge_stack_left :
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall gps mem regs pc,
    CS.comes_from_initial_state (gps, mem, regs, pc) (unionm ctx1 ctx2) ->
    to_partial_stack
      (unpartialize_stack
         (merge_stacks (to_partial_stack gps (domm ctx1))
                       (to_partial_stack gps (domm ctx2))))
      (domm ctx1) =
    to_partial_stack gps (domm ctx1).
Admitted. (* Grade 2. *)

Lemma to_partial_stack_merge_stacks_right:
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall gps1 mem1 regs1 pc1,
    CS.comes_from_initial_state (gps1, mem1, regs1, pc1) (unionm ctx1 ctx2) ->
  forall gps2 mem2 regs2 pc2,
    CS.comes_from_initial_state (gps2, mem2, regs2, pc2) (unionm ctx1 ctx2) ->
    to_partial_stack gps1 (domm ctx1) = to_partial_stack gps2 (domm ctx1) ->
    to_partial_stack
      (unpartialize_stack
         (merge_stacks (to_partial_stack gps1 (domm ctx1))
                       (to_partial_stack gps2 (domm ctx2))))
      (domm ctx2) =
    to_partial_stack gps2 (domm ctx2).
Admitted. (* Grade 2. Note comments for lemma above. *)

Corollary to_partial_stack_merge_stack_right :
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall gps mem regs pc,
    CS.comes_from_initial_state (gps, mem, regs, pc) (unionm ctx1 ctx2) ->
    to_partial_stack
      (unpartialize_stack
         (merge_stacks (to_partial_stack gps (domm ctx1))
                       (to_partial_stack gps (domm ctx2))))
      (domm ctx2) =
    to_partial_stack gps (domm ctx2).
Admitted. (* Grade 2. *)

(* Controlled rewrites on cons'ed stacks. *)
Lemma to_partial_stack_cons :
  forall frame gps ctx,
    to_partial_stack (frame :: gps) ctx =
    to_partial_frame ctx frame :: to_partial_stack gps ctx.
Proof.
  reflexivity.
Qed.

Lemma unpartialize_stack_cons :
  forall ptr gps,
    unpartialize_stack (ptr :: gps) =
    unpartialize_stack_frame ptr :: unpartialize_stack gps.
Proof.
  reflexivity.
Qed.

Lemma merge_stacks_cons :
  forall ctx1 ctx2 ptr1 ptr2 gps1 gps2,
    merge_stacks
      (to_partial_frame ctx1 ptr1 :: to_partial_stack gps1 ctx1)
      (to_partial_frame ctx2 ptr2 :: to_partial_stack gps2 ctx2) =
    merge_stack_frames (to_partial_frame ctx1 ptr1, to_partial_frame ctx2 ptr2) ::
      merge_stacks (to_partial_stack gps1 ctx1) (to_partial_stack gps2 ctx2).
Proof.
  reflexivity.
Qed.

(* Merged memories and their properties. *)

Definition merge_memories (mem1 mem2: Memory.t): Memory.t :=
  unionm mem1 mem2.

Lemma merge_memories_partition:
  forall ctx1 ctx2,
    mergeable_interfaces ctx1 ctx2 ->
  forall gps mem regs pc,
    CS.comes_from_initial_state (gps, mem, regs, pc) (unionm ctx1 ctx2) ->
    merge_memories
      (to_partial_memory mem (domm ctx1))
      (to_partial_memory mem (domm ctx2))
    = mem.
Proof.
  intros ctx1 ctx2 Hmerge gps mem regs pc Hcomes_from.
  inversion Hmerge as [[_ Hdisjoint] _].
  apply CS.comes_from_initial_state_mem_domm in Hcomes_from.
  simpl in Hcomes_from.
  unfold merge_memories, to_partial_memory.
  (* By case analysis. *)
  apply /eq_fmap => C.
  rewrite unionmE 2!filtermE.
  destruct (C \notin domm ctx1) eqn:Hdomm1;
    destruct (C \notin domm ctx2) eqn:Hdomm2;
    destruct (mem C) as [memC |] eqn:Hmem; rewrite Hmem;
    try reflexivity.
  (* A single contradictory case is left. *)
  - exfalso.
    apply negb_false_iff in Hdomm1. apply negb_false_iff in Hdomm2.
    eapply fdisjoint_partition_notinboth; eassumption.
Qed.

(* RB: TODO: The main rewrite sequence can be seen as two instances of a simpler
   lemma, which will probably operate on simpler assumptions than the ones here,
   taken from the contexts where we will apply these rewrites. In addition,
   some of the previous reasoning on memories may be rephrased using these
   results. *)
Lemma to_partial_memory_merge_prepare_procedures_memory_left (p c1 c2 : program) :
  prog_interface c1 = prog_interface c2 ->
  linkable (prog_interface p) (prog_interface c2) ->
  to_partial_memory (merge_memories (prepare_procedures_memory p)
                                    (prepare_procedures_memory c1))
                    (domm (prog_interface c2)) =
  to_partial_memory (merge_memories (prepare_procedures_memory p)
                                    (prepare_procedures_memory c2))
                    (domm (prog_interface c2)).
Proof.
  intros Hiface [_ Hdisjoint].
  unfold to_partial_memory, merge_memories.
  rewrite <- domm_prepare_procedures_memory,
          -> filterm_union,
          -> fdisjoint_filterm_full,
          -> fdisjoint_filterm_empty, -> unionm0,
          -> filterm_union,
          -> fdisjoint_filterm_full,
          -> fdisjoint_filterm_empty, -> unionm0;
    first reflexivity;
    (* The rewrites generate a few extra goals that we can discharge by normalizing
       the domain expression and then using our assumptions. *)
    try rewrite -> !domm_prepare_procedures_memory; congruence.
Qed.

(* RB: TODO: In this and related lemmas, consider symmetric versions and simplify
   accordingly (for example, two pairs on each of these: _left and _right2, and
   _left2 and _right). The single-memory _left lemma is also closely related
   to both. *)
Lemma to_partial_memory_merge_partial_memories_left
      (mem1 mem2 : Memory.t) (iface1 iface2 : Program.interface) :
    mergeable_interfaces iface1 iface2 ->
    (* Specialized assumptions:
       - mem2's domain is that of iface1 and iface2.
       - mem0 and mem2's domains are related, so in mem0 there is nothing outside
         of iface1 and iface2.
       - mem0 steps to mem1, so their domains coincide: mem1 is also "clean". *)
  forall G gps0 mem0 regs0 pc0 t gps1 regs1 pc1,
    CS.step G (gps0, mem0, regs0, pc0) t (gps1, mem1, regs1, pc1) ->
    to_partial_memory mem2 (domm iface1) =
    to_partial_memory mem0 (domm iface1) ->
  forall gps2 regs2 pc2,
    CS.comes_from_initial_state (gps2, mem2, regs2, pc2)
                                (unionm iface1 iface2) ->
    (* And the main result. *)
    to_partial_memory
      (merge_memories (to_partial_memory mem1 (domm iface1))
                      (to_partial_memory mem2 (domm iface2)))
      (domm iface1) =
    to_partial_memory mem1 (domm iface1).
Proof.
  intros Hmerge G gps0 mem0 regs0 pc0 t gps1 regs1 pc1
         Hstep01 Hpartial20 gps2 regs2 pc2 Hcomes_from2.
  inversion Hmerge as [[_ Hdisjoint] _].
  apply CS.step_preserves_mem_domm in Hstep01.
  apply CS.comes_from_initial_state_mem_domm in Hcomes_from2.
  simpl in Hstep01, Hcomes_from2.
  unfold to_partial_memory, merge_memories in *.
  rewrite -> filterm_union, -> 2!filterm_domm_unionm,
          -> unionmI, <- Hcomes_from2, -> fdisjoint_filterm_empty, -> unionm0;
    try reflexivity.
  simpl.
  rewrite (domm_filterm_fdisjoint_unionm Hdisjoint Hcomes_from2).
  rewrite (domm_filterm_partial_memory
             Hdisjoint Hstep01 Hcomes_from2 (eq_sym Hpartial20)).
  now rewrite fdisjointC.
Qed.

Lemma to_partial_memory_merge_partial_memories_left_2
      (mem1 mem2 : Memory.t) (iface1 iface2 : Program.interface) :
    mergeable_interfaces iface1 iface2 ->
    (* Specialized assumptions: symmetric to those above. *)
  forall G gps0 mem0 regs0 pc0 t gps2 regs2 pc2,
    CS.step G (gps0, mem0, regs0, pc0) t (gps2, mem2, regs2, pc2) ->
  forall gps1 regs1 pc1,
    to_partial_memory mem1 (domm iface2) =
    to_partial_memory mem0 (domm iface2) ->
    CS.comes_from_initial_state (gps1, mem1, regs1, pc1)
                                (unionm iface1 iface2) ->
    (* And the main result. *)
    to_partial_memory
      (merge_memories (to_partial_memory mem1 (domm iface1))
                      (to_partial_memory mem2 (domm iface2)))
      (domm iface1) =
    to_partial_memory mem1 (domm iface1).
Proof.
  intros Hmerge G gps0 mem0 regs0 pc0 t gps2 regs2 pc2
         Hstep02 gps1 regs1 pc1 Hpartial10 Hcomes_from1.
  inversion Hmerge as [[_ Hdisjoint] _].
  apply CS.step_preserves_mem_domm in Hstep02.
  apply CS.comes_from_initial_state_mem_domm in Hcomes_from1.
  simpl in Hstep02, Hcomes_from1.
  unfold to_partial_memory, merge_memories in *.
  (* Pose the symmetric statement. *)
  assert (Hcomes_from1' := Hcomes_from1);
    rewrite -> (unionmC Hdisjoint) in Hcomes_from1'.
  rewrite fdisjointC in Hdisjoint.
  (* And state the subset fact, the other novelty w.r.t. the other proofs. *)
  pose proof filterm_partial_memory_fsubset
       Hdisjoint Hstep02 Hcomes_from1' (eq_sym Hpartial10)
    as Hsubset.
  rewrite -> filterm_union, -> 2!filterm_domm_unionm,
          -> unionmI, <- Hcomes_from1, -> fsubset_filterm_domm_emptym, -> unionm0;
    try easy. (* Here we apply the new assumption, as well. *)
  rewrite (domm_filterm_fdisjoint_unionm Hdisjoint Hcomes_from1').
  rewrite (domm_filterm_partial_memory
             Hdisjoint Hstep02 Hcomes_from1' (eq_sym Hpartial10)).
  assumption.
Qed.

Corollary to_partial_memory_merge_memory_left :
  forall iface1 iface2,
    mergeable_interfaces iface1 iface2 ->
  forall gps mem regs pc,
    CS.comes_from_initial_state (gps, mem, regs, pc) (unionm iface1 iface2) ->
    to_partial_memory
      (merge_memories (to_partial_memory mem (domm iface1))
                      (to_partial_memory mem (domm iface2)))
      (domm iface1) =
    to_partial_memory mem (domm iface1).
Proof.
  intros iface1 iface2 Hmerge gps mem regs pc Hcomes_from.
  inversion Hmerge as [[_ Hdisjoint] _].
  apply CS.comes_from_initial_state_mem_domm in Hcomes_from.
  simpl in Hcomes_from.
  unfold to_partial_memory, merge_memories in *.
  rewrite -> filterm_union, -> 2!filterm_domm_unionm,
          -> unionmI, <- Hcomes_from, -> fdisjoint_filterm_empty, -> unionm0;
    try reflexivity.
  rewrite (domm_filterm_fdisjoint_unionm Hdisjoint Hcomes_from).
  rewrite (unionmC Hdisjoint) in Hcomes_from. rewrite fdisjointC in Hdisjoint.
  rewrite (domm_filterm_fdisjoint_unionm Hdisjoint Hcomes_from).
  assumption.
Qed.

Lemma to_partial_memory_merge_partial_memories_right
      (mem1 mem2 : Memory.t) (iface1 iface2 : Program.interface) :
    mergeable_interfaces iface1 iface2 ->
    (* Specialized assumptions:
       - mem2's domain is that of iface1 and iface2.
       - mem0 and mem2's domains are related, so in mem0 there is nothing outside
         of iface1 and iface2.
       - mem0 steps to mem1, so their domains coincide: mem1 is also "clean". *)
  forall G gps0 mem0 regs0 pc0 t gps1 regs1 pc1,
    CS.step G (gps0, mem0, regs0, pc0) t (gps1, mem1, regs1, pc1) ->
    to_partial_memory mem2 (domm iface1) =
    to_partial_memory mem0 (domm iface1) ->
  forall gps2 regs2 pc2,
    CS.comes_from_initial_state (gps2, mem2, regs2, pc2)
                                (unionm iface1 iface2) ->
    (* And the main result. *)
    to_partial_memory
      (merge_memories (to_partial_memory mem1 (domm iface1))
                      (to_partial_memory mem2 (domm iface2)))
      (domm iface2) =
    to_partial_memory mem2 (domm iface2).
Proof.
  intros Hmerge G gps0 mem0 regs0 pc0 t gps1 regs1 pc1
         Hstep01 Hpartial20 gps2 regs2 pc2 Hcomes_from2.
  inversion Hmerge as [[_ Hdisjoint] _].
  apply CS.step_preserves_mem_domm in Hstep01.
  apply CS.comes_from_initial_state_mem_domm in Hcomes_from2.
  simpl in Hstep01, Hcomes_from2.
  (* Pose the symmetric statement. *)
  assert (Hcomes_from2' := Hcomes_from2);
    rewrite -> (unionmC Hdisjoint) in Hcomes_from2'.
  (* And state the subset fact, the other novelty w.r.t. the other proofs. *)
  pose proof filterm_partial_memory_fsubset
       Hdisjoint Hstep01 Hcomes_from2 (eq_sym Hpartial20)
    as Hsubset.
  unfold to_partial_memory, merge_memories in *.
  rewrite -> filterm_union, -> 2!filterm_domm_unionm,
          -> unionmI, <- Hcomes_from2', -> fsubset_filterm_domm_emptym, -> union0m;
    try easy. (* Here we apply the new assumption, as well. *)
  rewrite (domm_filterm_fdisjoint_unionm Hdisjoint Hcomes_from2).
  rewrite (domm_filterm_partial_memory
             Hdisjoint Hstep01 Hcomes_from2 (eq_sym Hpartial20)).
  now rewrite fdisjointC.
Qed.

Lemma to_partial_memory_merge_partial_memories_right_2
      (mem1 mem2 : Memory.t) (iface1 iface2 : Program.interface) :
    mergeable_interfaces iface1 iface2 ->
    (* Specialized assumptions: symmetric to those above. *)
  forall G gps0 mem0 regs0 pc0 t gps2 regs2 pc2,
    CS.step G (gps0, mem0, regs0, pc0) t (gps2, mem2, regs2, pc2) ->
  forall gps1 regs1 pc1,
    to_partial_memory mem1 (domm iface2) =
    to_partial_memory mem0 (domm iface2) ->
    CS.comes_from_initial_state (gps1, mem1, regs1, pc1)
                                (unionm iface1 iface2) ->
    (* And the main result. *)
    to_partial_memory
      (merge_memories (to_partial_memory mem1 (domm iface1))
                      (to_partial_memory mem2 (domm iface2)))
      (domm iface2) =
    to_partial_memory mem2 (domm iface2).
Proof.
  intros Hmerge G gps0 mem0 regs0 pc0 t gps2 regs2 pc2
         Hstep02 gps1 regs1 pc1 Hpartial10 Hcomes_from1.
  inversion Hmerge as [[_ Hdisjoint] _].
  apply CS.step_preserves_mem_domm in Hstep02.
  apply CS.comes_from_initial_state_mem_domm in Hcomes_from1.
  simpl in Hstep02, Hcomes_from1.
  (* Rewrite symmetries up front. *)
  rewrite (unionmC Hdisjoint) in Hcomes_from1. rewrite fdisjointC in Hdisjoint.
  unfold to_partial_memory, merge_memories in *.
  rewrite -> filterm_union, -> 2!filterm_domm_unionm,
          -> unionmI, <- Hcomes_from1,
          -> fdisjoint_filterm_empty, -> union0m;
    try reflexivity.
  rewrite (domm_filterm_fdisjoint_unionm Hdisjoint Hcomes_from1).
  rewrite (domm_filterm_partial_memory
             Hdisjoint Hstep02 Hcomes_from1 (eq_sym Hpartial10)).
  (* The end is simplified w.r.t. *_left. *)
  assumption.
Qed.

Corollary to_partial_memory_merge_memory_right :
  forall iface1 iface2,
    mergeable_interfaces iface1 iface2 ->
  forall gps mem regs pc,
    CS.comes_from_initial_state (gps, mem, regs, pc) (unionm iface1 iface2) ->
    to_partial_memory
      (merge_memories (to_partial_memory mem (domm iface1))
                      (to_partial_memory mem (domm iface2)))
      (domm iface2) =
    to_partial_memory mem (domm iface2).
Proof.
  intros iface1 iface2 Hmerge gps mem regs pc Hcomes_from.
  inversion Hmerge as [[_ Hdisjoint] _].
  apply CS.comes_from_initial_state_mem_domm in Hcomes_from.
  simpl in Hcomes_from.
  (* Rewrite symmetries up front. *)
  rewrite (unionmC Hdisjoint) in Hcomes_from. rewrite fdisjointC in Hdisjoint.
  unfold to_partial_memory, merge_memories in *.
  rewrite -> filterm_union, -> 2!filterm_domm_unionm,
          -> unionmI, <- Hcomes_from, -> fdisjoint_filterm_empty, -> union0m;
    try reflexivity.
  rewrite (domm_filterm_fdisjoint_unionm Hdisjoint Hcomes_from).
  rewrite (unionmC Hdisjoint) in Hcomes_from. rewrite fdisjointC in Hdisjoint.
  rewrite (domm_filterm_fdisjoint_unionm Hdisjoint Hcomes_from).
  now rewrite fdisjointC.
Qed.

(* The following two lemmas manipulate memory stores and partialized memories
   more conveniently than the full-fledged "partialized" results. Note naming
   conventions for some of those are currently somewhat confusing.  *)
Lemma partialize_program_store :
  forall mem mem' (ctx : Program.interface) ptr v,
    Pointer.component ptr \notin domm ctx ->
    Memory.store mem ptr v = Some mem' ->
    Memory.store (PS.to_partial_memory mem (domm ctx)) ptr v =
    Some (PS.to_partial_memory mem' (domm ctx)).
Proof.
  unfold Memory.store, to_partial_memory.
  intros mem mem' ctx ptr v Hnotin Hstore.
  destruct (mem (Pointer.component ptr)) as [memC |] eqn:HmemC;
    last discriminate.
  destruct (ComponentMemory.store memC (Pointer.block ptr) (Pointer.offset ptr) v)
    as [memC' |] eqn:HmemC';
    last discriminate.
  inversion Hstore as [[Hstore']].
  now rewrite (getm_filterm_notin_domm _ Hnotin) HmemC HmemC'
      (setm_filterm_notin_domm _ _ Hnotin).
Qed.

Lemma unpartialize_program_store :
  forall mem1 mem1' mem2 ptr v,
    Memory.store mem1 ptr v = Some mem1' ->
    Memory.store (merge_memories mem1 mem2) ptr v =
    Some (merge_memories mem1' mem2).
Proof.
  unfold Memory.store.
  intros mem1 mem1' mem2 ptr v Hstore.
  unfold merge_memories. rewrite unionmE.
  destruct (mem1 (Pointer.component ptr)) eqn:Hcase1; rewrite Hcase1;
    last discriminate.
  simpl.
  destruct (ComponentMemory.store t (Pointer.block ptr) (Pointer.offset ptr) v) eqn:Hcase2;
    last discriminate.
  rewrite setm_union. now inversion Hstore.
Qed.

Lemma partialize_program_alloc :
  forall mem mem' (ctx : Program.interface) C ptr size,
    C \notin domm ctx ->
    Memory.alloc mem C size = Some (mem', ptr) ->
    Memory.alloc (to_partial_memory mem (domm ctx)) C size =
    Some (to_partial_memory mem' (domm ctx), ptr).
Proof.
  unfold Memory.alloc, to_partial_memory.
  intros mem mem' ctx C ptr size Hnotin Halloc.
  destruct (mem C) as [memC |] eqn:HmemC;
    last discriminate.
  destruct (ComponentMemory.alloc memC size) as [memC' b] eqn:HmemC'.
  inversion Halloc; subst.
  now rewrite (getm_filterm_notin_domm _ Hnotin) HmemC HmemC'
      (setm_filterm_notin_domm _ _ Hnotin).
Qed.

Lemma unpartialize_program_alloc :
  forall mem1 mem1' mem2 C ptr size,
    Memory.alloc mem1 C size = Some (mem1', ptr) ->
    Memory.alloc (merge_memories mem1 mem2) C size =
    Some (merge_memories mem1' mem2, ptr).
Proof.
  unfold Memory.alloc.
  intros mem1 mem1' mem2 C ptr size Halloc.
  unfold merge_memories. rewrite unionmE.
  destruct (mem1 C) as [memC |] eqn:Hcase1; rewrite Hcase1;
    last discriminate.
  simpl.
  destruct (ComponentMemory.alloc memC size) as [memC' b].
  rewrite setm_union. now inversion Halloc.
Qed.

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

(* Composition of mergeable states. *)

(* The following definitions are meant to manipulate pairs of mergeable states
   piecemeal. If the states are indeed mergeable, no error conditions (treated
   silently by the definitions, for now) occur. Moreover, they result in stacks
   and memories "without holes" w.r.t. to the generating states and interfaces,
   provided that the mergeability assumptions is present. *)

Definition mergeable_states_stack (s s' : state) : stack :=
  merge_stacks (state_stack s) (state_stack s').

Definition mergeable_states_memory (s s' : state) : Memory.t :=
  merge_memories (state_memory s) (state_memory s').

Definition mergeable_states_regs (s s' : state) : Register.t :=
  match s, s' with
    | PS.PC(_, _, regs, _), PS.CC(_, _, _)
    | PS.CC(_, _, _), PS.PC(_, _, regs, _) => regs
    (* The following will not happen if s and s' are mergeable. *)
    | _, _ => Register.init
  end.

Definition mergeable_states_pc (s s' : state) : Pointer.t :=
  match s, s' with
    | PS.PC(_, _, _, pc), PS.CC(_, _, _)
    | PS.CC(_, _, _), PS.PC(_, _, _, pc) => pc
    (* The following will not happen if s and s' are mergeable. *)
    | _, _ => (Component.main, 0, 0%Z)
  end.

Definition mergeable_states_state (s s' : state) : state :=
  PS.PC (mergeable_states_stack s s',
         mergeable_states_memory s s',
         mergeable_states_regs s s',
         mergeable_states_pc s s').

(* Moreover, mergeable states can, by definition, be merged, and the order of the
   arguments does not affect the result. (If they are not mergeable, the result
   would be morally the same, but the resulting garbage may not be identical). *)

Lemma merge_partial_states_sym ctx1 ctx2 ips1 ips2 :
  mergeable_states ctx1 ctx2 ips1 ips2 ->
  merge_partial_states ips1 ips2 = merge_partial_states ips2 ips1.
Proof.
  intros Hmerge.
  inversion Hmerge as [ics ? ? Hifaces Hcomes_from Hpartial1 Hpartial2]; subst.
  (* Some up front facts about symmetry. *)
  pose proof mergeable_interfaces_sym _ _ Hifaces as Hifaces_sym.
  pose proof unionmC (proj2 (proj1 Hifaces)) as Hunionm_sym.
  (* Case analysis. *)
  inversion Hpartial1 as [ gps1 ? mem1 ? regs1 pc1 Hcomp1
                         | gps1 ? mem1 ? regs1 pc1 Hcomp1];
    inversion Hpartial2 as [ gps2 ? mem2 ? regs2 pc2 Hcomp2 ? ? Heq
                           | gps2 ? mem2 ? regs2 pc2 Hcomp2 ? ? Heq];
    subst;
    PS.simplify_turn;
    inversion Heq; subst gps2 mem2 regs2 pc2.
  - (* RB: NOTE: Some of these common patterns are potential lemma candidates. *)
    pose proof CS.comes_from_initial_state_pc_domm _ _ Hcomes_from as Hcontra.
    exfalso. eapply domm_partition_in_union_in_neither; eassumption.
  - (* RB: NOTE: Symmetric lemmas? Also same script for next two cases. *)
    erewrite merge_memories_partition; try eassumption.
    erewrite merge_memories_partition; try (try rewrite <- Hunionm_sym; eassumption).
    erewrite merge_stacks_partition_emptym; try eassumption.
    erewrite merge_stacks_partition_emptym; try (try rewrite <- Hunionm_sym; eassumption).
    reflexivity.
  - erewrite merge_memories_partition; try eassumption.
    erewrite merge_memories_partition; try (try rewrite <- Hunionm_sym; eassumption).
    erewrite merge_stacks_partition_emptym; try eassumption.
    erewrite merge_stacks_partition_emptym; try (try rewrite <- Hunionm_sym; eassumption).
    reflexivity.
  - exfalso. eapply domm_partition_in_both; eassumption.
Qed.

(* transition system *)

Inductive initial_state (p: program) (ctx: Program.interface) : state -> Prop :=
| initial_state_intro: forall p' ics ips,
    prog_interface p' = ctx ->
    well_formed_program p ->
    well_formed_program p' ->
    linkable (prog_interface p) (prog_interface p') ->
    linkable_mains p p' ->
    partial_state ctx ics ips ->
    CS.initial_state (program_link p p') ics ->
    initial_state p ctx ips.

Inductive final_state (p: program) (ctx: Program.interface) : state -> Prop :=
| final_state_program: forall p' ics ips,
    prog_interface p' = ctx ->
    well_formed_program p ->
    well_formed_program p' ->
    linkable (prog_interface p) (prog_interface p') ->
    linkable_mains p p' ->
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
      linkable_mains p p' ->
      CS.step (prepare_global_env (program_link p p')) ics t ics' ->
      partial_state ctx ics ips ->
      partial_state ctx ics' ips' ->
      step p ctx (prepare_global_env p) ips t ips'.

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

  Lemma singleton_traces:
    single_events sem.
  Proof.
    unfold single_events.
    intros s t s' Hstep.
    (* RB: This generates unnecessarily restrictive conditions. *)
    (* inversion Hstep as [? ? ? ? ? ? ? ? ? ? ? HCSstep]; subst. *)
    (* apply CS.singleton_traces in HCSstep. *)
    (* exact HCSstep. *)
    inversion Hstep; simpl;
      match goal with
      | Hcs_step: CS.step _ _ _ _ |- _ =>
        apply CS.singleton_traces in Hcs_step
      end; auto.
  Qed.
End Semantics.

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
      inversion H4; subst;
        try (rewrite Pointer.inc_preserves_component; reflexivity);
        try (symmetry; assumption).
      + erewrite find_label_in_component_1; now eauto.
      + erewrite find_label_in_procedure_1; now eauto.
    }
    rewrite <- Hsame_comp in H7.
    rewrite Hcc in H7.
    discriminate.
  - inversion H4; subst;
      try (rewrite Pointer.inc_preserves_component; reflexivity);
      try (symmetry; assumption).
    + rewrite Pointer.inc_preserves_component.
      destruct ptr as [[]].
      unfold to_partial_memory. erewrite context_store_in_partialized_memory; eauto.
      * rewrite Pointer.inc_preserves_component.
        rewrite <- H18. eassumption.
    + erewrite find_label_in_component_1 with (pc:=pc); eauto.
    + rewrite H18. reflexivity.
    + erewrite find_label_in_procedure_1 with (pc:=pc); eauto.
    + rewrite Pointer.inc_preserves_component.
      unfold to_partial_memory. erewrite context_allocation_in_partialized_memory; eauto.
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
Ltac unify_op Hop1 Hop2 Hcomp Hwf Hwf1 Hwf2 Hlink1 Hlink2 Hmains1 Hmains2 Hsame_iface :=
  apply pc_component_not_in_ctx in Hcomp;
  pose proof Hcomp as Hcomp';
  rewrite <- Hsame_iface in Hcomp';
  inversion Hop1 as [procs1 [code1 [Hgenv1 [Hprocs1 [_ Hinstr1]]]]];
  inversion Hop2 as [procs2 [code2 [Hgenv2 [Hprocs2 [_ Hinstr2]]]]];
  pose proof @genv_procedures_program_link_left_notin _ _ Hcomp _ Hwf Hwf1 Hlink1 Hmains1
    as Hgenv1';
  pose proof @genv_procedures_program_link_left_notin _ _ Hcomp' _ Hwf Hwf2 Hlink2 Hmains2
    as Hgenv2';
  rewrite Hgenv1' in Hgenv1;
  rewrite Hgenv2' in Hgenv2;
  rewrite Hgenv2 in Hgenv1;
  inversion Hgenv1; subst procs2;
  rewrite Hprocs2 in Hprocs1;
  inversion Hprocs1; subst code2;
  rewrite Hinstr2 in Hinstr1;
  inversion Hinstr1.

Ltac discharge_op_neq Hop1 Hop2 Hcomp Hwf Hwf1 Hwf2 Hlink1 Hlink2 Hmains1 Hmains2 Hsame_iface :=
  unify_op Hop1 Hop2 Hcomp Hwf Hwf1 Hwf2 Hlink1 Hlink2 Hmains1 Hmains2 Hsame_iface;
  discriminate.

Ltac unify_op_eq Hop1 Hop2 Hcomp Hwf Hwf1 Hwf2 Hlink1 Hlink2 Hmains1 Hmains2 Hsame_iface :=
  unify_op Hop1 Hop2 Hcomp Hwf Hwf1 Hwf2 Hlink1 Hlink2 Hmains1 Hmains2 Hsame_iface;
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

Ltac unify_component_label Hcomp Hcomp' Hwf Hwf1 Hwf2 Hlink1 Hlink2 Hmains1 Hmains2 :=
  match goal with
  | Hlabel1 : find_label_in_component (prepare_global_env (program_link ?P ?P1)) ?PC ?L = Some ?PC1,
    Hlabel2 : find_label_in_component (prepare_global_env (program_link ?P ?P2)) ?PC ?L = Some ?PC2  |- _ =>
    pose proof @find_label_in_component_program_link_left _ _ Hcomp _ Hwf Hwf1 Hlink1 Hmains1
      as Hlabel1';
    pose proof @find_label_in_component_program_link_left _ _ Hcomp' _ Hwf Hwf2 Hlink2 Hmains2
      as Hlabel2';
    rewrite Hlabel1' in Hlabel1;
    rewrite Hlabel2' in Hlabel2;
    rewrite Hlabel2 in Hlabel1;
    inversion Hlabel1; subst
  end.

Ltac unify_procedure_label Hcomp Hcomp' Hwf Hwf1 Hwf2 Hlink1 Hlink2 Hmains1 Hmains2 :=
  match goal with
  | Hlabel1 : find_label_in_procedure (prepare_global_env (program_link ?P ?P1)) ?PC ?L = Some ?PC1,
    Hlabel2 : find_label_in_procedure (prepare_global_env (program_link ?P ?P2)) ?PC ?L = Some ?PC2  |- _ =>
    pose proof @find_label_in_procedure_program_link_left _ _ Hcomp _ Hwf Hwf1 Hlink1 Hmains1
      as Hlabel1';
    pose proof @find_label_in_procedure_program_link_left _ _ Hcomp' _ Hwf Hwf2 Hlink2 Hmains2
      as Hlabel2';
    rewrite Hlabel1' in Hlabel1;
    rewrite Hlabel2' in Hlabel2;
    rewrite Hlabel2 in Hlabel1;
    inversion Hlabel1; subst
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

(* At the moment, with the new definitions, two pattern-maching scenarios
      EntryPoint.get ?C ?PROC (_ (program_link ?P ?P1))
      EntryPoint.get ?C ?PROC (_ (_ (program_link ?P ?P1)))
   depending on the state of unfolding. Ltac is not smart enough to see one
   as a special case of the other. It is innocuous at the moment and quick
   to ignore that part of the pattern-match, but even wildcards in place of
   the concrete, now duplicate pattern, are less clear. *)
Ltac unify_entrypoint Hpc1' Hpc2' Hwf Hwf1 Hwf2 Hlink1 Hlink2 Hmains1 Hmains2 Hsame_iface :=
  match goal with
  | Hentry1 : EntryPoint.get ?C ?PROC _ = ?B1,
    Hentry2 : EntryPoint.get ?C ?PROC _ = ?B2  |- _ =>
    pose proof @genv_entrypoints_program_link_left _ _ Hpc1' _ Hwf Hwf1 Hlink1 Hmains1
      as Hentry1';
    rewrite <- Hsame_iface in Hpc2';
    pose proof @genv_entrypoints_program_link_left _ _ Hpc2' _ Hwf Hwf2 Hlink2 Hmains2
      as Hentry2';
    rewrite Hentry1' in Hentry1;
    rewrite Hentry2' in Hentry2;
    rewrite Hentry2 in Hentry1;
    inversion Hentry1; subst
  end.

Ltac unify_inc_pc Hcc1 Hcc2 :=
  rewrite <- Pointer.inc_preserves_component in Hcc1;
  rewrite (ptr_within_partial_frame_1 Hcc1);
  rewrite Pointer.inc_preserves_component;
  rewrite <- Pointer.inc_preserves_component in Hcc2;
  rewrite (ptr_within_partial_frame_1 Hcc2);
  rewrite Pointer.inc_preserves_component.

Ltac unify_regs :=
  match goal with
  | Hregs1 : Register.get R_COM ?REGS1 = Int ?CALL_ARG,
    Hregs2 : Register.get R_COM ?REGS2 = Int ?CALL_ARG |- _ =>
    rewrite <- Hregs1 in Hregs2;
    rewrite (Register.invalidate_eq Hregs2)
  end.

Ltac unify_components_eq :=
  match goal with
  | Hcomps : Pointer.component ?PC1 = Pointer.component ?PC2 |- _ =>
    rewrite Hcomps
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

(* RB: Where to put this? Is it direct from CoqUtils?
   As it is, just a convenience to make tactics more readable. *)
Remark notin_to_in_false : forall (Cid : Component.id) (iface : Program.interface),
  Cid \notin domm iface -> Cid \in domm iface = false.
Proof.
  intros Cid iface Hnotin.
  destruct (Cid \in domm iface) eqn:Heq;
    easy.
Qed.

(* we can prove a strong form of state determinism when the program is in control *)
Lemma state_determinism_program' p ctx G sps t1 t2 sps' :
  is_program_component sps ctx ->
  step p ctx G sps t1 sps' ->
  forall sps'', step p ctx G sps t2 sps'' ->
                t1 = t2 /\ sps' = sps''.
Admitted. (* Grade 3. Not hard; requires some additional porting from Source. *)

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
    as [p1 ? ? ? cs1 cs1' ? Hwfp Hwfp1 Hlink1 Hmains1 Hstep_cs1 Hpartial1 Hpartial1'];
    subst.
  inversion Hstep_ps2
    as [p2 ? ? ? cs2 cs2' Hsame_iface _ Hwfp2 Hlink2 Hmains2 Hstep_cs2 Hpartial2 Hpartial2'];
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
    try discharge_op_neq Hop1 Hop2 Hcomp Hwfp Hwfp1 Hwfp2 Hlink1 Hlink2 Hmains1 Hmains2 Hsame_iface;
    (* Second, case analysis of partial steps.
       Cases where program and component do not match can be discharged. *)
    inversion Hpartial1'
      as [cstk1' ? cmem1' ? regs1' pc1' Hpc1' | cstk1' ? cmem1' ? regs1' pc1' Hcc1'];
      subst;
    inversion Hpartial2'
      as [cstk2' ? cmem2' ? regs2' pc2' Hpc2' | cstk2' ? cmem2' ? regs2' pc2' Hcc2'];
      subst;
    (* (Now that we are done inverting, expose this definition.) *)
    unfold to_partial_memory in *;
    try discharge_pc_cc Hcomp Hcc1';
    try discharge_pc_cc Hcomp Hcc2';
    (* For the remaining goals, unify components of their matching opcodes and their
       various optional components: register and memory reads and stores, component
       labels, allocs and entry points. *)
    unify_op_eq Hop1 Hop2 Hcomp Hwfp Hwfp1 Hwfp2 Hlink1 Hlink2 Hmains1 Hmains2 Hsame_iface;
    simplify_turn;
    try unify_get;
    try unify_load pc1 Hcomp Hmem12;
    try unify_store pc1 Hcomp Hmem12;
    try unify_component_label Hcomp Hcomp' Hwfp Hwfp1 Hwfp2 Hlink1 Hlink2 Hmains1 Hmains2;
    try unify_procedure_label Hcomp Hcomp' Hwfp Hwfp1 Hwfp2 Hlink1 Hlink2 Hmains1 Hmains2;
    try unify_alloc Hmem12 Hcomp;
    try unify_entrypoint Hpc1' Hpc2' Hwfp Hwfp1 Hwfp2 Hlink1 Hlink2 Hmains1 Hmains2 Hsame_iface;
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
Proof.
  intros p ctx G ps t ps1 Hcomp Hstep_ps1 ps2 Hstep_ps2.

  inversion Hstep_ps1
    as [p1 ? ? ? cs1 cs1' ? Hwfp Hwfp1 Hlink1 Hmains1 Hstep_cs1 Hpartial1 Hpartial1'];
    subst.
  inversion Hstep_ps2
    as [p2 ? ? ? cs2 cs2' Hsame_iface _ Hwfp2 Hlink2 Hmains2 Hstep_cs2 Hpartial2 Hpartial2'];
    subst.

  (* Case analysis on who has control. *)
  inversion Hpartial1 as [cstk1 ? cmem1 ? regs1 pc1 Hpc1 | cstk1 ? cmem1 ? regs1 pc1 Hcc1];
    subst;
    (* Program control is discharged by contradiction. *)
    first (simplify_turn; rewrite Hcomp in Hpc1; discriminate).

  inversion Hpartial2 as [| cstk2 ? cmem2 ? regs2 pc2 Hcc2 Hmem12 Hstk12 DUMMY Hcompeq];
    subst.
  (* First, case analysis of CS steps. *)
  inversion Hstep_cs1; subst;
    inversion Hstep_cs2; subst;
    (* All subgoals but two involve an emtpy trace: state determinism applies. *)
    try (rewrite (context_epsilon_step_is_silent Hcomp Hstep_ps1);
         rewrite (context_epsilon_step_is_silent Hcomp Hstep_ps2);
         reflexivity);
    inversion Hpartial1'
      as [cstk1' ? cmem1' ? regs1' pc1' Hpc1' | cstk1' ? cmem1' ? regs1' pc1' Hcc1'];
      subst;
    inversion Hpartial2'
      as [cstk2' ? cmem2' ? regs2' pc2' Hpc2' | cstk2' ? cmem2' ? regs2' pc2' Hcc2'];
      subst;
    simplify_turn.
  (* ICall *)
  - rewrite Hmem12.
    rewrite Hstk12.
    unify_inc_pc Hcc1 Hcc2.
    unify_regs.
    unify_components_eq.
    unify_entrypoint Hpc1' Hpc2' Hwfp Hwfp1 Hwfp2 Hlink1 Hlink2 Hmains1 Hmains2 Hsame_iface.
    reflexivity.
  - discharge_pc Hpc1' Hcc2'.
  - discharge_pc Hpc2' Hcc1'.
  - rewrite Hmem12.
    rewrite Hstk12.
    unify_inc_pc Hcc1 Hcc2.
    unify_components_eq.
    reflexivity.
  (* IReturn *)
  - rewrite Hmem12.
    inversion Hstk12 as [Hstk12'].
    rewrite (ptr_within_partial_frame_2 (notin_to_in_false Hpc1')) in Hstk12'.
    rewrite (ptr_within_partial_frame_2 (notin_to_in_false Hpc2')) in Hstk12'.
    apply partial_pointer_to_pointer_eq in Hstk12'; subst.
    unify_regs.
    reflexivity.
  - rewrite (ptr_within_partial_frame_1 Hcc2') in Hstk12.
    rewrite (ptr_within_partial_frame_2 (notin_to_in_false Hpc1')) in Hstk12.
    easy.
  - rewrite (ptr_within_partial_frame_1 Hcc1') in Hstk12.
    rewrite (ptr_within_partial_frame_2 (notin_to_in_false Hpc2')) in Hstk12.
    easy.
  - rewrite Hmem12.
    inversion Hstk12.
    unify_components_eq.
    reflexivity.
Qed.

Theorem state_determinism:
  forall p ctx G ips t ips',
    step p ctx G ips t ips' ->
  forall ips'',
    step p ctx G ips t ips'' ->
    ips' = ips''.
Proof.
  intros p ctx G ps t ps1 Hstep_ps1 ps2 Hstep_ps2.
  inversion Hstep_ps1 as [? ? ? ? ? _ _ _ _ _ _ _ Hpartial1 _]; subst.
  (* Case analysis on who has control. *)
  inversion Hpartial1; subst.
  - eapply state_determinism_program; eassumption.
  - eapply state_determinism_context; eassumption.
Qed.

Lemma state_determinism_star_E0 p ctx s s1 s2 :
  star (PS.step p ctx) (prepare_global_env p) s E0 s1 ->
  star (PS.step p ctx) (prepare_global_env p) s E0 s2 ->
  star (PS.step p ctx) (prepare_global_env p) s1 E0 s2 \/
  star (PS.step p ctx) (prepare_global_env p) s2 E0 s1.
Proof.
move=> Hstar1.
elim/star_E0_ind': s s1 / Hstar1 s2=> [s|s s1 s1' Hstep1 Hstar1 IH] s2; eauto.
move=> Hstar2; elim/star_E0_ind': s s2 / Hstar2 Hstep1.
  by move=> s Hstep1; right; apply: star_step; eauto.
move=> s s2 s2' Hstep2 Hstar2 _ Hstep1; apply: IH.
suffices -> : s1 = s2 by [].
by apply: state_determinism Hstep2.
Qed.

Lemma state_determinism_star_same_trace p ctx s t s1 s2 :
  star (PS.step p ctx) (prepare_global_env p) s t s1 ->
  star (PS.step p ctx) (prepare_global_env p) s t s2 ->
  star (PS.step p ctx) (prepare_global_env p) s1 E0 s2 \/
  star (PS.step p ctx) (prepare_global_env p) s2 E0 s1.
Proof.
elim: t s => [|e t IH] s; first exact: state_determinism_star_E0.
case/(star_cons_inv (@singleton_traces p ctx)) => [s' [s1' [e_01 [e_11 e_t1]]]].
case/(star_cons_inv (@singleton_traces p ctx)) => [s'_ [s2' [e_02 [e_12]]]].
have {e_01 e_02} e_s : s' = s'_.
  have {e_t1 IH} H := state_determinism_star_E0 e_01 e_02.
  without loss H : s' s'_ s1' s2' e_11 e_12 {H e_01 e_02} / Star (sem p ctx) s' E0 s'_.
    by case: H; eauto=> H1 H2; apply: esym; eauto.
  have [in_c|in_p] := boolP (is_context_component s' ctx).
    symmetry. (* RB: The equality of the following lemma is reversed! *)
    exact: context_epsilon_star_is_silent in_c H.
  elim/star_E0_ind: s' s'_ / H in_p e_11 {e_12} => //.
  move=> s' s'm s'_ Hstep1 _ in_p Hstep2.
  by have [] := state_determinism_program' in_p Hstep1 Hstep2.
move: e_s e_12 => <- {s'_} e_12.
by have {s2' e_12} <- := state_determinism e_11 e_12; eauto.
Qed.

(* RB: TODO: Port missing generic results from Source.PS to here. *)

Lemma comes_from_initial_state_step_trans :
  forall p ctx ics ips t ics' ips',
    CS.comes_from_initial_state ics (unionm (prog_interface p) ctx) ->
    step p ctx (prepare_global_env p) ips t ips' ->
    ips = partialize ics ctx ->
    ips' = partialize ics' ctx ->
    CS.comes_from_initial_state ics' (unionm (prog_interface p) ctx).
Admitted. (* Grade 3. *)

Lemma initial_state_exists :
  forall p c,
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    linkable_mains p c ->
  exists s,
    initial_state p (prog_interface c) s.
Proof.
  eexists. econstructor; try (reflexivity || assumption).
  apply partialized_state_is_partial.
Qed.

Lemma not_initial_state_contra : forall p c,
  well_formed_program p ->
  well_formed_program c ->
  linkable (prog_interface p) (prog_interface c) ->
  linkable_mains p c ->
  (forall s, ~ initial_state p (prog_interface c) s) ->
  False.
Proof.
  intros ? ? H1 H2 H3 H4 Hcontra.
  destruct (initial_state_exists H1 H2 H3 H4) as [s ?].
  specialize (Hcontra s).
  contradiction.
Qed.

(* A version of state determinism inspired by the needs and resources in
   Composition. RB: NOTE: Consider a simpler version of this result such as is
   given for Source.PS. *)
Lemma initial_state_determinism :
  forall p c s1 s2,
    initial_state p (prog_interface c) s1 ->
    initial_state p (prog_interface c) s2 ->
    well_formed_program p ->
    well_formed_program c ->
    closed_program (program_link p c) ->
    linkable (prog_interface p) (prog_interface c) ->
    linkable_mains p c ->
    s1 = s2.
Proof.
  intros p c ? ?
         [c1 ics1 s1 Hiface1 _ Hwf1 Hlinkable1 Hmains1 Hpartial1 HCSini1]
         [c2 ics2 s2 Hiface2 _ Hwf2 Hlinkable2 Hmains2 Hpartial2 HCSini2]
         Hwfp Hwfc Hclosed Hlinkable Hmains.
  unfold CS.initial_state in HCSini1, HCSini2; subst ics1 ics2.
  (* RB: TODO: Possibly spin out another mini-lemma for the application to
     CS.initial_machine_state. *)
  symmetry in Hiface1, Hiface2.
  assert (Hclosed1 : closed_program (program_link p c1)). {
    apply interface_preserves_closedness_r' with (p2 := c); assumption.
  }
  assert (Hclosed2 : closed_program (program_link p c2)). {
    apply interface_preserves_closedness_r' with (p2 := c); assumption.
  }
  rewrite CS.initial_machine_state_after_linking in Hpartial1; try assumption.
  rewrite CS.initial_machine_state_after_linking in Hpartial2; try assumption.
  (* Case analysis on the location of the main procedure, exposing some of the
     structure up front to make case rewrites automatic. Also observe the common
     case analysis and inversion structure on both cases, susceptible to simple,
     tactic-based refactoring (or otherwise). *)
  unfold linkable_mains in Hmains1, Hmains2.
  inversion Hclosed1 as [_ [mainpc1 [main_procs1 [Hmainpc1 _]]]].
  inversion Hclosed2 as [_ [mainpc2 [main_procs2 [Hmainpc2 _]]]].
  simpl in Hmainpc1, Hmainpc2.
  unfold CS.prog_main_block in Hpartial1, Hpartial2.
  destruct (prog_main p) as [mainp |] eqn:Hmainp.
  - (* main in p. *)
    destruct (prog_main c1) as [mainc1 |] eqn:Hmainc1; first discriminate.
    destruct (prog_main c2) as [mainc1 |] eqn:Hmainc2; first discriminate.
    inversion Hpartial1 as [? ? ? ? ? ? Hcomp1 | ? ? ? ? ? ? Hcomp1]; subst;
      inversion Hpartial2 as [? ? ? ? ? ? Hcomp2 | ? ? ? ? ? ? Hcomp2]; subst;
      simplify_turn.
    + rewrite !to_partial_memory_merge_prepare_procedures_memory_left; congruence.
    + exfalso. eapply domm_partition_in_notin; eassumption.
    + exfalso. eapply domm_partition_in_notin; eassumption.
    + rewrite !to_partial_memory_merge_prepare_procedures_memory_left; congruence.
  - (* main in c1 and c2. *)
    destruct (prog_main c1) as [mainc1 |] eqn:Hmainc1; last discriminate.
    destruct (prog_main c2) as [mainc2 |] eqn:Hmainc2; last discriminate.
    inversion Hpartial1 as [? ? ? ? ? ? Hcomp1 | ? ? ? ? ? ? Hcomp1]; subst;
      inversion Hpartial2 as [? ? ? ? ? ? Hcomp2 | ? ? ? ? ? ? Hcomp2]; subst;
      simplify_turn.
    + (* RB: NOTE Another possibility here is to prove reflexivity by rewriting
         as in the other cases. This also requires a rewrite on EntryPoint.get to
         their None case. *)
      assert (Hmainc1' : is_true (prog_main c1)) by now rewrite Hmainc1.
      pose proof (proj2 (wfprog_main_component Hwf1) Hmainc1') as Hcontra.
      rewrite <- Hiface1 in Hcontra.
      exfalso. eapply domm_partition_in_notin; eassumption.
    + exfalso. eapply domm_partition_in_notin; eassumption.
    + exfalso. eapply domm_partition_in_notin; eassumption.
    + rewrite !to_partial_memory_merge_prepare_procedures_memory_left; congruence.
Qed.

End PS.
