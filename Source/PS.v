Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.Maps.
Require Import Common.CompCertExtensions.
Require Import Common.Blame.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Lib.Extra.

Require Import Coq.Program.Equality.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From mathcomp Require ssrnat.

Canonical ssrnat.nat_eqType.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Module PS.

Import Source.

Definition stack : Type := list (Component.id * option (value * CS.cont)).

Definition program_state : Type := Component.id * stack * Memory.t * CS.cont * expr * value.
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
  let arg := fresh "arg" in
  destruct st as [[[[[[C pgps] pmem] k] e] arg] | [[C pgps] pmem]].

Ltac unfold_states :=
  repeat match goal with
         | st: state |- _ => unfold_state st
         end.

Definition s_component (sps: state) : Component.id :=
  match sps with
  | PC (C, _, _, _, _, _) => C
  | CC (C, _, _)          => C
  end.

Instance state_turn : HasTurn state := {
  turn_of s iface := s_component s \in domm iface
}.

Definition is_context_component (ps: state) ctx := turn_of ps ctx.
Definition is_program_component (ps: state) ctx := negb (is_context_component ps ctx).

Ltac simplify_turn :=
  unfold PS.is_program_component, PS.is_context_component in *;
  unfold turn_of, PS.state_turn in *;
  simpl in *.

(* stack partialization *)

Definition to_partial_frame (ctx: {fset Component.id}) frame : Component.id * option (value * CS.cont) :=
  let: CS.Frame C v k := frame in
  if C \in ctx then
    (C, None)
  else
    (C, Some (v, k)).

Fixpoint drop_last_frames_if_needed
         (ctx: {fset Component.id}) (s: CS.stack) (Cincontrol: Component.id)
  : CS.stack :=
  match s with
  | [] => []
  | CS.Frame C v k :: s' =>
    if (C \in ctx) && (C == Cincontrol) then
      drop_last_frames_if_needed ctx s' Cincontrol
    else
      s
  end.

Fixpoint to_partial_stack_helper
         (ctx: {fset Component.id}) (s: CS.stack) last_frame
  : PS.stack :=
  match s with
  | [] => [:: to_partial_frame ctx last_frame]
  | CS.Frame C v k :: s' =>
    let: CS.Frame C' _ _ := last_frame in
    if (C \in ctx) && (C == C') then
      to_partial_stack_helper ctx s' last_frame
    else
      to_partial_frame ctx last_frame ::
      to_partial_stack_helper ctx s' (CS.Frame C v k)
  end.

Lemma to_partial_stack_helper_nonempty:
  forall ctx gps frame,
    to_partial_stack_helper ctx gps frame <> [].
Proof.
  move=> ctx gps [C v k].
  elim: gps => [|[C' v' k'] gps' IH] //=.
  by case: ifP.
Qed.

Definition to_partial_stack
          (s: CS.stack) (ctx: {fset Component.id}) (Cincontrol: Component.id) :=
  match drop_last_frames_if_needed ctx s Cincontrol with
  | [] => []
  | last_frame :: s' =>
    to_partial_stack_helper ctx s' last_frame
  end.

Example to_partial_stack_empty_context:
  let in_s := [CS.Frame 1 (Int 1) Kstop;
               CS.Frame 0 (Int 0) Kstop] in
  let out_s := [(1, Some (Int 1, Kstop));
                (0, Some (Int 0, Kstop))] in
  to_partial_stack in_s fset0 1 = out_s.
Proof. by []. Qed.

Example to_partial_stack_context_internal_call_at_the_end:
  let in_s := [CS.Frame 1 (Int 2) Kstop;
               CS.Frame 1 (Int 1) Kstop;
               CS.Frame 0 (Int 0) Kstop] in
  let out_s := [(1, None); (0, Some (Int 0, Kstop))] in
  to_partial_stack in_s (fset1 1) 2 = out_s.
Proof. by []. Qed.

Example to_partial_stack_context_internal_call_at_the_beginning:
  let in_s := [CS.Frame 1 (Int 2) Kstop;
               CS.Frame 0 (Int 1) Kstop;
               CS.Frame 0 (Int 0) Kstop] in
  let out_s := [(1, Some (Int 2, Kstop));
                (0, None)] in
  to_partial_stack in_s (fset1 0) 1 = out_s.
Proof. by []. Qed.

Example to_partial_stack_context_internal_call_in_the_middle:
  let in_s := [CS.Frame 2 (Int 4) Kstop;
               CS.Frame 1 (Int 3) Kstop;
               CS.Frame 1 (Int 2) Kstop;
               CS.Frame 1 (Int 1) Kstop;
               CS.Frame 0 (Int 0) Kstop] in
  let out_s := [(2, Some (Int 4, Kstop));
                (1, None); (0, Some (Int 0, Kstop))] in
  to_partial_stack in_s (fset1 1) 1 = out_s.
Proof.  by []. Qed.

Example to_partial_stack_program_internal_calls:
  let in_s := [CS.Frame 3 (Int 7) Kstop;
               CS.Frame 3 (Int 6) Kstop;
               CS.Frame 1 (Int 5) Kstop;
               CS.Frame 2 (Int 4) Kstop;
               CS.Frame 2 (Int 3) Kstop;
               CS.Frame 1 (Int 2) Kstop;
               CS.Frame 0 (Int 1) Kstop;
               CS.Frame 0 (Int 0) Kstop] in
  let out_s := [(3, Some (Int 7, Kstop)); (3, Some (Int 6, Kstop));
                (1, None);
                (2, Some (Int 4, Kstop)); (2, Some (Int 3, Kstop));
                (1, None);
                (0, Some (Int 1, Kstop)); (0, Some (Int 0, Kstop))] in
  to_partial_stack in_s (fset1 1) 1 = out_s.
Proof.
  compute. reflexivity.
Qed.

Example to_partial_stack_context_internal_calls:
  let in_s := [CS.Frame 0 (Int 7) Kstop;
               CS.Frame 0 (Int 6) Kstop;
               CS.Frame 2 (Int 5) Kstop;
               CS.Frame 0 (Int 4) Kstop;
               CS.Frame 0 (Int 3) Kstop;
               CS.Frame 1 (Int 2) Kstop;
               CS.Frame 0 (Int 1) Kstop;
               CS.Frame 0 (Int 0) Kstop] in
  let out_s := [(2, Some (Int 5, Kstop));
                (0, None);
                (1, Some (Int 2, Kstop));
                (0, None)] in
  to_partial_stack in_s (fset1 0) 0 = out_s.
Proof.
  compute. reflexivity.
Qed.

Lemma partial_stack_push_by_program:
  forall ctx gps1 gps2 C_incontrol,
    C_incontrol \notin ctx ->
    to_partial_stack gps1 ctx C_incontrol =
    to_partial_stack gps2 ctx C_incontrol ->
  forall v k C_incontrol',
    to_partial_stack (CS.Frame C_incontrol v k :: gps1) ctx C_incontrol' =
    to_partial_stack (CS.Frame C_incontrol v k :: gps2) ctx C_incontrol'.
Proof.
  rewrite /to_partial_stack /=.
  move=> ctx gps1 gps2 C_incontrol Hprog Hsame_stacks.
  move=> v k C_incontrol'; rewrite (negbTE Hprog) /=.
  elim: gps1 gps2 Hsame_stacks=> [|[C1 v1 k1] gps1 IH] /=.
    case=> [|[C' v' k'] gps2']; rewrite /= (negbTE Hprog) //.
    case: ifP => [|_ <- //] /andP [HC'_in_ctx /eqP contra].
    by move: Hprog; rewrite -contra HC'_in_ctx.
  case=> [|[C2 v2 k2] gps2]; rewrite /= (negbTE Hprog).
    case: ifP; last by move=> _ ->.
    case/andP => [HC'_in_ctx /eqP contra].
    by move: Hprog; rewrite -contra HC'_in_ctx.
  case: ifP.
    case/andP=> [C1_in_ctx /eqP e1]; subst C_incontrol.
    by rewrite C1_in_ctx in Hprog.
  case: ifP => [|_ _ -> //].
  case/andP=> [C2_in_ctx /eqP e2]; subst C_incontrol.
  by rewrite C2_in_ctx in Hprog.
Qed.

Lemma partial_stack_ignores_change_by_context_with_control:
  forall ctx gps C_incontrol,
    C_incontrol \in ctx ->
  forall v k,
    to_partial_stack (CS.Frame C_incontrol v k :: gps) ctx C_incontrol =
    to_partial_stack gps ctx C_incontrol.
Proof.
  intros ctx gps C_incontrol Hin_ctx v k.
  unfold to_partial_stack.
  destruct gps as [|[C' v' k'] gps'];
  by rewrite /= Hin_ctx /= eqxx.
Qed.

Lemma partial_stack_outside_context_preserves_top :
  forall C C' v k s ctx,
    C' \in ctx = false ->
  exists frame rest,
    to_partial_stack (CS.Frame C' v k :: s) ctx C = (C', frame) :: rest.
Proof.
  intros Cid' Cid val cont st ctx Hctx.
  induction st as [| hd st IHst].
  - unfold to_partial_stack, drop_last_frames_if_needed.
    rewrite Hctx. simpl.
    rewrite Hctx. simpl.
    eexists. eexists. reflexivity.
  - (* Extract information from IH. *)
    destruct IHst as [frame [rest IHst]].
    unfold to_partial_stack in IHst. simpl in IHst.
    rewrite Hctx in IHst. simpl in IHst.
    (* Substitute information into the goal. *)
    unfold to_partial_stack, drop_last_frames_if_needed.
    rewrite Hctx. simpl.
    rewrite IHst. simpl.
    destruct hd as [C v0 k1].
    destruct (C \in ctx) eqn:Hcase1; rewrite Hcase1;
      destruct (C == Cid); simpl;
        try (try rewrite Hctx; eexists; eexists; reflexivity).
Qed.

Lemma partial_stack_outside_control_preserves_top :
  forall C C' v k s ctx,
    C <> C' ->
  exists frame rest,
    to_partial_stack (CS.Frame C' v k :: s) ctx C = (C', frame) :: rest.
Proof.
  intros Cid' Cid val cont st ctx Hneq'.
  assert (Cid == Cid' = false) as Hneq
    by (apply /eqP; intro Heq; by symmetry in Heq).
  induction st as [| hd st IHst].
  - unfold to_partial_stack, drop_last_frames_if_needed.
    rewrite Hneq. rewrite andb_comm. simpl.
    destruct (Cid \in ctx) eqn:Hcase1; rewrite Hcase1;
      by eauto.
  - (* Extract information from IH. *)
    destruct IHst as [frame [rest IHst]].
    unfold to_partial_stack in IHst. simpl in IHst.
    rewrite Hneq in IHst. rewrite andb_comm in IHst. simpl in IHst.
    (* Substitute information into the goal. *)
    unfold to_partial_stack, drop_last_frames_if_needed.
    rewrite Hneq. rewrite andb_comm. simpl.
    rewrite IHst. simpl.
    destruct hd as [C v0 k1].
    destruct (C \in ctx) eqn:Hcase1; rewrite Hcase1;
      destruct (C == Cid) eqn:Hcase2; simpl;
      (try (destruct (Cid \in ctx) eqn:Hcase3; rewrite Hcase3); eauto).
Qed.

Lemma partial_stacks_unequal_top_internal :
  forall C1 C2 v1 v2 k1 k2 s1 s2 ctx,
    C1 \notin ctx ->
    C1 <> C2 ->
    to_partial_stack (CS.Frame C1 v1 k1 :: s1) ctx C1 <>
    to_partial_stack (CS.Frame C2 v2 k2 :: s2) ctx C1.
Proof.
  intros C1 C2 v1 v2 k1 k2 s1 s2 ctx Hctx Hneq Hstack.
  assert (C1 \in ctx = false) as Hctx' by (by destruct (C1 \in ctx)).
  pose proof partial_stack_outside_context_preserves_top as Hpres1.
  specialize (Hpres1 C1 _ v1 k1 s1 _ Hctx').
  destruct Hpres1 as [frame1 [rest1 Hpres1]].
  pose proof partial_stack_outside_control_preserves_top as Hpres2.
  specialize (Hpres2 C1 _ v2 k2 s2 ctx Hneq).
  destruct Hpres2 as [frame2 [rest2 Hpres2]].
  rewrite Hpres1 in Hstack. rewrite Hpres2 in Hstack.
  inversion Hstack as [Hcontra].
  by intuition.
Qed.

Lemma partial_stacks_unequal_top_external :
  forall C C1 C2 v1 v2 k1 k2 s1 s2 ctx,
    C1 \notin ctx ->
    C2 \in ctx ->
    C <> C2 ->
    to_partial_stack (CS.Frame C1 v1 k1 :: s1) ctx C <>
    to_partial_stack (CS.Frame C2 v2 k2 :: s2) ctx C.
Proof.
  intros C C1 C2 v1 v2 k1 k2 s1 s2 ctx Hnotin Hin Hneq Hstack.
  assert (C1 \in ctx = false) as Hnotin' by (by destruct (C1 \in ctx)).
  pose proof partial_stack_outside_context_preserves_top as Hpres1.
  specialize (Hpres1 C C1 v1 k1 s1 ctx Hnotin').
  destruct Hpres1 as [frame1 [rest1 Hpres1]].
  rewrite Hpres1 in Hstack.
  pose proof partial_stack_outside_control_preserves_top as Hpres2.
  specialize (Hpres2 C C2 v2 k2 s2 ctx Hneq).
  destruct Hpres2 as [frame2 [rest2 Hpres2]].
  rewrite Hpres2 in Hstack.
  inversion Hstack; subst.
  by rewrite Hin in Hnotin.
Qed.

Lemma partial_stacks_equal_top_external_context :
  forall C C1 C2 v1 v2 k1 k2 s1 s2 ctx,
    C1 \notin ctx ->
    C2 \notin ctx ->
    to_partial_stack (CS.Frame C1 v1 k1 :: s1) ctx C =
    to_partial_stack (CS.Frame C2 v2 k2 :: s2) ctx C ->
    C1 = C2.
Proof.
  intros C C1 C2 v1 v2 k1 k2 s1 s2 ctx Hnotin1 Hnotin2 Hstack.
  pose proof partial_stack_outside_context_preserves_top as Hpres1.
  assert (C1 \in ctx = false) as Hdomm1 by (by destruct (C1 \in ctx)).
  specialize (Hpres1 C C1 v1 k1 s1 ctx Hdomm1).
  destruct Hpres1 as [frame1 [rest1 Hpres1]].
  rewrite Hpres1 in Hstack.
  pose proof partial_stack_outside_context_preserves_top as Hpres2.
  assert (C2 \in ctx = false) as Hdomm2 by (by destruct (C2 \in ctx)).
  specialize (Hpres2 C C2 v2 k2 s2 ctx Hdomm2).
  destruct Hpres2 as [frame2 [rest2 Hpres2]].
  rewrite Hpres2 in Hstack.
  by inversion Hstack.
Qed.

Lemma partial_stacks_equal_top_external_control :
  forall C C1 C2 v1 v2 k1 k2 s1 s2 ctx,
    C <> C1 ->
    C <> C2 ->
    to_partial_stack (CS.Frame C1 v1 k1 :: s1) ctx C =
    to_partial_stack (CS.Frame C2 v2 k2 :: s2) ctx C ->
    C1 = C2.
Proof.
  intros C C1 C2 v1 v2 k1 k2 s1 s2 ctx Hneq1 Hneq2 Hstack.
  pose proof partial_stack_outside_control_preserves_top as Hpres1.
  specialize (Hpres1 C C1 v1 k1 s1 ctx Hneq1).
  destruct Hpres1 as [frame1 [rest1 Hpres1]].
  rewrite Hpres1 in Hstack.
  pose proof partial_stack_outside_control_preserves_top as Hpres2.
  specialize (Hpres2 C C2 v2 k2 s2 ctx Hneq2).
  destruct Hpres2 as [frame2 [rest2 Hpres2]].
  rewrite Hpres2 in Hstack.
  by inversion Hstack.
Qed.

Lemma partial_stack_push_by_context:
  forall ctx C C' v1 k1 v2 k2 gps1 gps2,
    C <> C' ->
    C \in ctx ->
    to_partial_stack gps1 ctx C =
    to_partial_stack gps2 ctx C ->
    to_partial_stack (CS.Frame C v1 k1 :: gps1) ctx C' =
    to_partial_stack (CS.Frame C v2 k2 :: gps2) ctx C'.
Proof.
  intros ctx C C' v1 k1 v2 k2 gps1 gps2.
  move=> /eqP Hdiff Hctx Hstacks.
  unfold to_partial_stack. simpl.
  rewrite Hctx /= (negbTE Hdiff).
  unfold to_partial_stack in Hstacks.
  induction gps1 as [|[C_a v_a k_a] gps1']; simpl in *.
  - induction gps2 as [|[C_b v_b k_b] gps2']; simpl in *.
    + rewrite Hctx. reflexivity.
    + rewrite Hctx.
      rewrite Hctx in IHgps2'.
      destruct (C_b \in ctx) eqn:HC_b_in_ctx.
      * rewrite HC_b_in_ctx.
        rewrite HC_b_in_ctx in Hstacks. simpl in *.
        destruct (C_b == C) eqn:HC_b_eq_C.
        ** simpl. apply IHgps2'; auto.
        ** exfalso.
           symmetry in Hstacks.
           eapply to_partial_stack_helper_nonempty.
           eauto.
      * rewrite HC_b_in_ctx in Hstacks. simpl in *.
        exfalso.
        symmetry in Hstacks.
        eapply to_partial_stack_helper_nonempty.
        eauto.
  - rewrite Hctx.
    induction gps2 as [|[C_b v_b k_b] gps2']; simpl in *.
    * destruct (C_a \in ctx) eqn:HC_a_in_ctx.
      ** rewrite HC_a_in_ctx.
         rewrite HC_a_in_ctx in Hstacks. simpl in *.
         destruct (C_a == C) eqn:HC_a_eq_C.
         *** apply IHgps1'; auto.
         *** exfalso.
             symmetry in Hstacks.
             eapply to_partial_stack_helper_nonempty.
             eauto.
      ** rewrite HC_a_in_ctx in Hstacks. simpl in *.
         exfalso.
         eapply to_partial_stack_helper_nonempty.
         eauto.
    * rewrite Hctx.
      rewrite Hctx in IHgps1'.
      destruct (C_a \in ctx) eqn:HC_a_in_ctx.
      ** rewrite HC_a_in_ctx.
         rewrite HC_a_in_ctx in Hstacks.
         rewrite HC_a_in_ctx in IHgps2'.
         destruct (C_a == C) eqn:HC_a_eq_C.
         *** destruct (C_b \in ctx) eqn:HC_b_in_ctx.
             **** rewrite HC_b_in_ctx.
                  rewrite HC_b_in_ctx in Hstacks.
                  rewrite HC_b_in_ctx in IHgps1'.
                  simpl in *.
                  destruct (C_b == C) eqn:HC_b_eq_C.
                  ***** apply IHgps1'; auto.
                  ***** apply IHgps1'; auto.
             **** rewrite HC_b_in_ctx.
                  rewrite HC_b_in_ctx in Hstacks.
                  rewrite HC_b_in_ctx in IHgps1'.
                  simpl in *.
                  apply IHgps1'; auto.
         *** destruct (C_b \in ctx) eqn:HC_b_in_ctx.
             **** rewrite HC_b_in_ctx.
                  rewrite HC_b_in_ctx in Hstacks.
                  rewrite HC_b_in_ctx in IHgps1'.
                  simpl in *.
                  destruct (C_b == C) eqn:HC_b_eq_C.
                  ***** apply IHgps2'; auto.
                  ***** rewrite Hstacks. reflexivity.
             **** rewrite HC_b_in_ctx.
                  rewrite HC_b_in_ctx in Hstacks.
                  rewrite HC_b_in_ctx in IHgps1'.
                  simpl in *.
                  rewrite Hstacks. reflexivity.
      ** rewrite HC_a_in_ctx.
         rewrite HC_a_in_ctx in Hstacks.
         rewrite HC_a_in_ctx in IHgps2'.
         destruct (C_b \in ctx) eqn:HC_b_in_ctx.
         *** rewrite HC_b_in_ctx.
             rewrite HC_b_in_ctx in Hstacks.
             rewrite HC_b_in_ctx in IHgps1'.
             destruct (C_b == C) eqn:HC_b_eq_C.
             **** apply IHgps2'; auto.
             **** simpl in *.
                  rewrite Hstacks. reflexivity.
         *** rewrite HC_b_in_ctx.
             rewrite HC_b_in_ctx in Hstacks.
             rewrite HC_b_in_ctx in IHgps1'.
             simpl in *.
             rewrite Hstacks. reflexivity.
Qed.

Lemma partial_stack_pop_to_program:
  forall ctx C C' old_call_arg1 k1 old_call_arg2 k2 gps1 gps2,
    C' \notin ctx ->
    to_partial_stack (CS.Frame C' old_call_arg1 k1 :: gps1) ctx C =
    to_partial_stack (CS.Frame C' old_call_arg2 k2 :: gps2) ctx C ->
    old_call_arg1 = old_call_arg2 /\ k1 = k2 /\
    to_partial_stack gps1 ctx C' = to_partial_stack gps2 ctx C'.
Proof.
  intros ctx C C' old_call_arg1 k1 old_call_arg2 k2 gps1 gps2.
  intros Hprog Hstack.
  unfold to_partial_stack in Hstack.
  unfold drop_last_frames_if_needed in Hstack.
  destruct (C' \in ctx) eqn:Hin_ctx_aux;
    try discriminate.
  rewrite Hin_ctx_aux in Hstack. simpl in Hstack.
  destruct gps1 as [|[C_a v_a k_a] gps1'].
  - destruct gps2 as [|[C_b v_b k_b] gps2'].
    + simpl in *.
      rewrite Hin_ctx_aux in Hstack.
      inversion Hstack. subst.
      repeat split.
    + simpl in *.
      rewrite Hin_ctx_aux in Hstack.
      destruct (C_b \in ctx) eqn:HC_b_in_ctx;
        rewrite HC_b_in_ctx in Hstack.
      * destruct (C_b == C') eqn:HC_b_eq_C';
          simpl in *.
        ** move/eqP in HC_b_eq_C'. subst.
           rewrite Hin_ctx_aux in HC_b_in_ctx.
           discriminate.
        ** inversion Hstack.
           exfalso.
           symmetry in H2.
           eapply to_partial_stack_helper_nonempty.
           eauto.
      * simpl in *.
        inversion Hstack.
        exfalso.
        symmetry in H2.
        eapply to_partial_stack_helper_nonempty.
        eauto.
  - destruct gps2 as [|[C_b v_b k_b] gps2'].
    + simpl in *.
      rewrite Hin_ctx_aux in Hstack.
      destruct (C_a \in ctx) eqn:HC_a_in_ctx;
        rewrite HC_a_in_ctx in Hstack.
      * destruct (C_a == C') eqn:HC_a_eq_C';
          simpl in *.
        ** move/eqP in HC_a_eq_C'. subst.
           rewrite Hin_ctx_aux in HC_a_in_ctx.
           discriminate.
        ** inversion Hstack.
           exfalso.
           symmetry in H2.
           eapply to_partial_stack_helper_nonempty.
           eauto.
      * simpl in *.
        inversion Hstack.
        exfalso.
        symmetry in H2.
        eapply to_partial_stack_helper_nonempty.
        eauto.
    + simpl in Hstack.
      rewrite Hin_ctx_aux in Hstack.
      destruct (C_a \in ctx) eqn:HC_a_in_ctx.
      * destruct (C_b \in ctx) eqn:HC_b_in_ctx.
        ** rewrite HC_a_in_ctx in Hstack.
           rewrite HC_b_in_ctx in Hstack.
           destruct (C_a == C') eqn:HC_a_eq_C'.
           *** destruct (C_b == C') eqn:HC_b_eq_C'.
               **** simpl in *.
                    apply Nat.eqb_eq in HC_a_eq_C'. subst.
                    rewrite Hin_ctx_aux in HC_a_in_ctx.
                    discriminate.
               **** simpl in *.
                    apply Nat.eqb_eq in HC_a_eq_C'. subst.
                    rewrite Hin_ctx_aux in HC_a_in_ctx.
                    discriminate.
           *** destruct (C_b == C') eqn:HC_b_eq_C'.
               **** simpl in *.
                    apply Nat.eqb_eq in HC_b_eq_C'. subst.
                    rewrite Hin_ctx_aux in HC_b_in_ctx.
                    discriminate.
               **** simpl in *.
                    inversion Hstack. subst.
                    repeat split.
                    unfold to_partial_stack.
                    unfold drop_last_frames_if_needed.
                    rewrite HC_a_in_ctx HC_b_in_ctx.
                    rewrite HC_a_eq_C' HC_b_eq_C'.
                    simpl. auto.
        ** rewrite HC_a_in_ctx in Hstack.
           rewrite HC_b_in_ctx in Hstack.
           simpl in *.
           destruct (C_a == C') eqn:HC_a_eq_C'.
           *** apply Nat.eqb_eq in HC_a_eq_C'. subst.
               rewrite Hin_ctx_aux in HC_a_in_ctx.
               discriminate.
           *** inversion Hstack. subst.
               repeat split.
               unfold to_partial_stack.
               unfold drop_last_frames_if_needed.
               rewrite HC_a_in_ctx HC_b_in_ctx.
               simpl.
               rewrite HC_a_eq_C'.
               auto.
      * destruct (C_b \in ctx) eqn:HC_b_in_ctx.
        ** rewrite HC_a_in_ctx in Hstack.
           rewrite HC_b_in_ctx in Hstack.
           simpl in *.
           destruct (C_b == C') eqn:HC_b_eq_C'.
           *** apply Nat.eqb_eq in HC_b_eq_C'. subst.
               rewrite Hin_ctx_aux in HC_b_in_ctx.
               discriminate.
           *** inversion Hstack. subst.
               repeat split.
               unfold to_partial_stack.
               unfold drop_last_frames_if_needed.
               rewrite HC_b_in_ctx HC_b_eq_C'.
               rewrite HC_a_in_ctx. simpl.
               rewrite H2. reflexivity.
        ** rewrite HC_a_in_ctx in Hstack.
           rewrite HC_b_in_ctx in Hstack.
           simpl in *.
           inversion Hstack. subst.
           repeat split.
           unfold to_partial_stack.
           unfold drop_last_frames_if_needed.
           rewrite HC_b_in_ctx.
           rewrite HC_a_in_ctx. simpl.
           rewrite H2. reflexivity.
Qed.

Lemma partial_stack_pop_to_context:
  forall ctx C C' v1 k1 v2 k2 gps1 gps2,
    C <> C' ->
    C' \in ctx ->
    to_partial_stack (CS.Frame C' v1 k1 :: gps1) ctx C =
    to_partial_stack (CS.Frame C' v2 k2 :: gps2) ctx C ->
    to_partial_stack gps1 ctx C' = to_partial_stack gps2 ctx C'.
Proof.
  intros ctx C C' v1 k1 v2 k2 gps1 gps2.
  move=> /eqP Hdiff Hctx Hstacks.
  unfold to_partial_stack in Hstacks. simpl in *.
  rewrite eq_sym (negbTE Hdiff) Hctx /= in Hstacks.
  induction gps1 as [|[C_a v_a k_a] gps1']; simpl in *.
  - induction gps2 as [|[C_b v_b k_b] gps2']; simpl in *.
    + reflexivity.
    + rewrite Hctx in Hstacks.
      rewrite Hctx in IHgps2'.
      unfold to_partial_stack. simpl.
      destruct (C_b \in ctx) eqn:HC_b_in_ctx.
      * rewrite HC_b_in_ctx.
        rewrite HC_b_in_ctx in Hstacks.
        destruct (C_b == C') eqn:HC_b_eq_C'.
        ** unfold to_partial_stack in IHgps2'.
           simpl in *.
           apply IHgps2'; auto.
        ** simpl in *.
           inversion Hstacks.
           exfalso.
           symmetry in H0.
           eapply to_partial_stack_helper_nonempty in H0.
           auto.
      * rewrite HC_b_in_ctx.
        rewrite HC_b_in_ctx in Hstacks.
        simpl in *.
        inversion Hstacks.
        exfalso.
        symmetry in H0.
        eapply to_partial_stack_helper_nonempty in H0.
        auto.
  - induction gps2 as [|[C_b v_b k_b] gps2']; simpl in *.
    + rewrite Hctx in Hstacks.
      rewrite Hctx in IHgps1'.
      unfold to_partial_stack. simpl.
      destruct (C_a \in ctx) eqn:HC_a_in_ctx.
      * rewrite HC_a_in_ctx.
        rewrite HC_a_in_ctx in Hstacks.
        destruct (C_a == C') eqn:HC_a_eq_C'.
        ** unfold to_partial_stack in IHgps1'.
           simpl in *.
           apply IHgps1'; auto.
        ** simpl in *.
           inversion Hstacks.
           exfalso.
           eapply to_partial_stack_helper_nonempty in H0.
           auto.
      * rewrite HC_a_in_ctx.
        rewrite HC_a_in_ctx in Hstacks.
        simpl in *.
        inversion Hstacks.
        exfalso.
        eapply to_partial_stack_helper_nonempty in H0.
        auto.
    + rewrite Hctx in Hstacks.
      rewrite Hctx in IHgps1'.
      rewrite Hctx in IHgps2'.
      unfold to_partial_stack.
      unfold to_partial_stack in IHgps1'.
      unfold to_partial_stack in IHgps2'.
      simpl in *.
      destruct (C_a \in ctx) eqn:HC_a_in_ctx.
      * rewrite HC_a_in_ctx.
        rewrite HC_a_in_ctx in Hstacks.
        rewrite HC_a_in_ctx in IHgps2'.
        destruct (C_a == C') eqn:HC_a_eq_C'.
        ** apply IHgps1'. auto.
        ** simpl in *.
           destruct (C_b \in ctx) eqn:HC_b_in_ctx.
           *** rewrite HC_b_in_ctx.
               rewrite HC_b_in_ctx in Hstacks.
               rewrite HC_b_in_ctx in IHgps1'.
               destruct (C_b == C') eqn:HC_b_eq_C'.
               **** simpl in *.
                    apply IHgps2'; auto.
               **** simpl in *.
                    inversion Hstacks. rewrite H0. reflexivity.
           *** rewrite HC_b_in_ctx.
               rewrite HC_b_in_ctx in Hstacks.
               rewrite HC_b_in_ctx in IHgps1'.
               simpl in *.
               inversion Hstacks. rewrite H0. reflexivity.
      * rewrite HC_a_in_ctx.
        rewrite HC_a_in_ctx in Hstacks.
        rewrite HC_a_in_ctx in IHgps2'.
        simpl in *.
        destruct (C_b \in ctx) eqn:HC_b_in_ctx.
        ** rewrite HC_b_in_ctx.
           rewrite HC_b_in_ctx in Hstacks.
           rewrite HC_b_in_ctx in IHgps1'.
           destruct (C_b == C') eqn:HC_b_eq_C'.
           *** simpl in *.
               apply IHgps2'; auto.
           *** simpl in *.
               inversion Hstacks. rewrite H0. reflexivity.
        ** rewrite HC_b_in_ctx.
           rewrite HC_b_in_ctx in Hstacks.
           rewrite HC_b_in_ctx in IHgps1'.
           simpl in *.
           inversion Hstacks. rewrite H0. reflexivity.
Qed.

Inductive partial_state (ctx: Program.interface) : CS.state -> PS.state -> Prop :=
| ProgramControl: forall C gps pgps mem pmem k e arg,
    (* program has control *)
    is_program_component (PC (C, pgps, pmem, k, e, arg)) ctx ->

    (* we forget about context memories *)
    pmem = filterm (fun k _ => negb (k \in domm ctx)) mem ->

    (* we put holes in place of context information in the stack *)
    pgps = to_partial_stack gps (domm ctx) C ->

    partial_state ctx [CState C, gps, mem, k, e, arg] (PC (C, pgps, pmem, k, e, arg))

| ContextControl: forall C gps pgps mem pmem k e arg,
    (* context has control *)
    is_context_component (CC (C, pgps, pmem)) ctx ->

    (* we forget about context memories *)
    pmem = filterm (fun k _ => negb (k \in domm ctx)) mem ->

    (* we put holes in place of context information in the stack *)
    pgps = to_partial_stack gps (domm ctx) C ->

    partial_state ctx [CState C, gps, mem, k, e, arg] (CC (C, pgps, pmem)).

Definition partialize (ctx: Program.interface) (scs: CS.state) : PS.state :=
  let: CS.State C gps mem k e arg := scs in
  let pgps := to_partial_stack gps (domm ctx) C in
  let pmem := filterm (fun k _ => negb (k \in domm ctx)) mem in
  if C \in domm ctx then CC (C, pgps, pmem)
  else PC (C, pgps, pmem, k, e, arg).

Lemma s_component_partialize ctx scs :
  s_component (partialize ctx scs) = CS.s_component scs.
Proof. by case: scs=> C ????? /=; case: ifP. Qed.

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



Ltac backward_easy :=
  by move=> *;
  match goal with
  | in_prog : is_true (?C \notin domm ?ctx),
    e_part  : (if ?C \in ?Cs then _ else _) = partialize ?ctx ?scs2
  |- match CS.eval_kstep _ ?scs2 with _ => _ end =>
    rewrite (negbTE in_prog) (lock CS.eval_kstep) (lock filterm) in e_part *;
    case: scs2 e_part=> [C' stk2 mem2 k' e' arg'] /=;
    case: ifP => // _ []; rewrite -(lock filterm);
    intros <- e_stk e_mem <- <- <-;
    rewrite -lock /= (negbTE in_prog) e_stk e_mem
  end.

Lemma backward p ctx p1 p2 scs1 t scs1' scs2 :
  well_formed_program p ->
  well_formed_program p1 ->
  well_formed_program p2 ->
  linkable (prog_interface p) ctx ->
  closed_interface (unionm (prog_interface p) ctx) ->
  prog_interface p1 = ctx ->
  prog_interface p2 = ctx ->
  partialize ctx scs1 = partialize ctx scs2 ->
  CS.s_component scs1 \notin domm ctx ->
  CS.kstep (prepare_global_env (program_link p p1)) scs1 t scs1' ->
  exists2 scs2',
    CS.kstep (prepare_global_env (program_link p p2)) scs2 t scs2' &
    partialize ctx scs1' = partialize ctx scs2'.
Proof.
move=> wf wf1 wf2 link clos int1 int2 e_part in_prog step.
suffices : match CS.eval_kstep (prepare_global_env (program_link p p2)) scs2 return Prop with
           | Some (t', scs2') => t = t' /\ partialize ctx scs1' = partialize ctx scs2'
           | None             => False
           end.
  case ev: CS.eval_kstep=> [[t' scs2']|] //=.
  by move/CS.eval_kstep_sound in ev => - [-> ?]; eauto.
case: scs1 t scs1' / step in_prog e_part => /=; try backward_easy.
- (* Allocation *)
  move=> C stk1 mem1 mem1' k size ptr arg /Zgt_is_gt_bool size_pos e_mem1 in_prog.
  rewrite (negbTE in_prog) (lock CS.eval_kstep) (lock filterm).
  case: scs2=> [C' stk2 mem2 k' e' arg'] /=.
  case: ifP=> // _ []; rewrite -(lock filterm).
  move=> {C' k' e' arg'} <- e_stk e_mem <- <- <-.
  rewrite -lock /= size_pos.
  case: (program_allocation_in_partialized_memory_strong e_mem in_prog e_mem1).
  by move=> mem2' e_mem2 e_mem'; rewrite e_mem2 /= (negbTE in_prog) e_stk e_mem'.
- (* Load *)
  move=> C stk1 mem1 k _ b' o' v arg <- e_v in_prog.
  rewrite (negbTE in_prog) (lock CS.eval_kstep) (lock filterm).
  case: scs2=> [C' stk2 mem2 k' e' arg'] /=.
  case: ifP=> // _ []; rewrite -(lock filterm).
  move=> {C' k' e' arg'} <- e_stk e_mem <- <- <-.
  rewrite -lock /= eqxx.
  rewrite (program_load_in_partialized_memory_strong e_mem in_prog e_v) /=.
  by rewrite (negbTE in_prog) e_stk e_mem.
- (* Store *)
  move=> C stk mem1 mem1' k v _ b' o' arg <- e_mem1 in_prog.
  rewrite (negbTE in_prog) (lock CS.eval_kstep) (lock filterm).
  case: scs2=> [C' stk2 mem2 k' e' arg'] /=.
  case: ifP=> // _ []; rewrite -(lock filterm).
  move=> {C' k' e' arg'} <- e_stk e_mem <- <- <-.
  rewrite -lock /= eqxx.
  case: (program_store_in_partialized_memory_strong e_mem in_prog e_mem1).
  move=> mem2' e_mem2 e_mem'; rewrite e_mem2 /=.
  by rewrite (negbTE in_prog) e_stk e_mem'.
- (* Internal Call *)
  move=> C stk1 mem1 k _ P v P_expr old <- e_P in_prog.
  rewrite (negbTE in_prog) (lock CS.eval_kstep) (lock filterm).
  case: scs2=> [C' stk2 mem2 k' e' arg'] /=.
  case: ifP=> // _ []; rewrite -(lock filterm).
  move=> {C' k' e' arg'} <- e_stk e_mem <- <- <-.
  rewrite -lock /= eqxx.
  case: (find_procedure_in_linked_programs wf wf1 _ e_P); rewrite ?int1 //.
  move=> in_p e_P'.
  rewrite (_ : find_procedure _ _ _ = Some P_expr); last first.
    apply/linkable_programs_find_procedure=> //; auto.
    by rewrite int2.
  by rewrite /= (negbTE in_prog) (partial_stack_push_by_program in_prog e_stk) e_mem.
- (* External Call *)
  move=> C stk1 mem1 k C' P v P_expr old /eqP ne import e_P in_prog.
  rewrite (negbTE in_prog) (lock CS.eval_kstep) (lock filterm).
  case: scs2=> [C'' stk2 mem2 k' e' arg'] /=.
  case: ifP=> // _ []; rewrite -(lock filterm).
  move=> {C'' k' e' arg'} <- e_stk e_mem <- <- <-.
  rewrite -lock /= (negbTE ne).
  move/imported_procedure_iff: import.
  rewrite /imported_procedure_b !unionmE.
  case C_p: (prog_interface p C)=> [CI|] //=; last first.
    by move: in_prog; rewrite -int1 mem_domm;  case: getm.
  move=> import; rewrite import; move: e_P; rewrite /find_procedure !unionmE.
  case C'_p: (prog_procedures p C')=> [CI'|] //=.
  + (* Call into program *)
    move=> ->.
    have in_prog' : C' \notin domm ctx.
      case: link => _ /fdisjointP/(_ C'); apply.
      by rewrite wfprog_defined_procedures // mem_domm C'_p.
    by rewrite /= (negbTE in_prog') (partial_stack_push_by_program in_prog e_stk) e_mem.
  + (* Call into context *)
    case C'_ctx1: (prog_procedures p1 C')=> [C'_procs1|] //= C'_P1.
    have in_ctx : C' \in domm ctx.
      by rewrite -int1 wfprog_defined_procedures // mem_domm C'_ctx1.
    have /dommP [C'_procs2 C'_ctx2] : C' \in domm (prog_procedures p2).
      by rewrite -wfprog_defined_procedures // int2.
    rewrite C'_ctx2.
    have C'_P' : exported_procedure (prog_interface (program_link p p2)) C' P.
      move: (clos C); rewrite -int2; apply.
      exists CI; rewrite /Program.has_component /Component.is_importing /=.
      by rewrite unionmE C_p /=.
    have {C'_P'} C'_P' : exported_procedure (prog_interface p2) C' P.
      case: C'_P' => CI' [].
      rewrite /exported_procedure /Program.has_component /Component.is_exporting.
      rewrite /= unionmE -mem_domm wfprog_defined_procedures // mem_domm C'_p /=.
      by eauto.
    move: (wfprog_exported_procedures_existence wf2 C'_P').
    rewrite /find_procedure C'_ctx2.
    case: (C'_procs2 P)=> //= P_expr' _.
    by rewrite in_ctx e_mem (partial_stack_push_by_program in_prog e_stk).
- (* Internal return *)
  admit.
- (* External return *)
  admit.
Admitted.

(* transition system *)

Inductive initial_state (p: program) (ctx: Program.interface) : state -> Prop :=
| initial_state_intro: forall p' scs sps,
    prog_interface p' = ctx ->
    well_formed_program p ->
    well_formed_program p' ->
    linkable (prog_interface p) (prog_interface p') ->
    closed_program (program_link p p') ->
    partial_state ctx scs sps ->
    CS.initial_state (program_link p p') scs ->
    initial_state p ctx sps.

Lemma exists_initial_state p p' :
  linkable (prog_interface p) (prog_interface p') ->
  well_formed_program p ->
  well_formed_program p' ->
  closed_program (program_link p p') ->
  exists sps, initial_state p (prog_interface p') sps.
Proof.
move=> Hlink wf wf' Hclosed.
eexists (partialize (prog_interface p') (CS.initial_machine_state (program_link p p'))).
apply: PS.initial_state_intro; eauto.
- by rewrite <- partialize_correct.
- by [].
Qed.

Inductive final_state (p: program) (ctx: Program.interface) (sps: state) : Prop :=
| final_state_program: forall p' scs,
    prog_interface p' = ctx ->
    well_formed_program p ->
    well_formed_program p' ->
    linkable (prog_interface p) (prog_interface p') ->
    ~ turn_of sps ctx ->
    partial_state ctx scs sps ->
    CS.final_state scs ->
    final_state p ctx sps
| final_state_context:
    turn_of sps ctx ->
    final_state p ctx sps.

Inductive kstep
          (p: program) (ctx: Program.interface) (G : global_env)
          (sps : state) (t : trace) (sps' : state) : Prop :=
| partial_step:
    forall p' scs scs',
      prog_interface p' = ctx ->
      well_formed_program p ->
      well_formed_program p' ->
      linkable (prog_interface p) (prog_interface p') ->
      closed_interface (unionm (prog_interface p) (prog_interface p')) ->
      CS.kstep (prepare_global_env (program_link p p')) scs t scs' ->
      partial_state ctx scs sps ->
      partial_state ctx scs' sps' ->
      kstep p ctx G sps t sps'.

(* FIXME: This is subsumed by s_component_partialize *)

Lemma partial_state_component ctx scs sps :
  partial_state ctx scs sps ->
  s_component sps = CS.s_component scs.
Proof. by case: scs sps /. Qed.

Lemma kstep_component p ctx G s t s' :
  kstep p ctx G s t s' ->
  s_component s' =
  if t is e :: _ then next_comp_of_event e
  else s_component s.
Proof.
case=> p' scs scs' p'_ctx wf_p wf_p' Hlink _ Hstep.
move=> /partial_state_component -> /partial_state_component ->.
by rewrite (CS.kstep_component Hstep).
Qed.

Lemma final_state_stuck p ctx G st :
  final_state p ctx st ->
  is_program_component st ctx ->
  forall t st', ~ kstep p ctx G st t st'.
Proof.
move=> Hfinal Hin_p t st' Hstep.
case: Hstep Hfinal Hin_p.
move=> p1 scs1 scs1' e_ctx1 wf_p wf_p1 Hlink1 _ Hstep Hpart1 _.
case; last first.
  by rewrite /is_program_component /is_context_component => ->.
move=> p2 scs2 e_ctx2 _ wf_p2 Hlink2 _ Hpart2 Hfinal Hin_p.
suffices /CS.final_state_stuck: CS.final_state scs1 by apply; eauto.
case: scs1 st / Hpart1 Hpart2 Hin_p {Hstep}; last first.
  by rewrite /is_program_component=> ???????? ->.
move=> C gps pgps mem pmem k e arg _ e_pmem e_pgps.
move e_sps: (PC _)=> sps Hpart2.
case: scs2 sps / Hpart2 e_sps Hfinal e_pgps; last first.
  by rewrite /is_program_component=> ???????? ->.
move=> C' gps' ?????? _ -> -> [-> -> <- <- <- ->] /=.
rewrite /is_program_component /is_context_component /turn_of /=.
case; first by auto.
case=> [v [-> [-> ->]]] e_gps notin; rewrite (_ : gps = [::]); eauto.
move/esym: e_gps; rewrite /to_partial_stack /=.
case: gps=> //= [[C'' v' k'] gps]; rewrite andbC.
by case: eqP=> //= [->|_]; first rewrite (negbTE notin);
move=> /to_partial_stack_helper_nonempty.
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
    @Semantics_gen state global_env (kstep p ctx)
                   (initial_state p ctx)
                   (final_state p ctx) (prepare_global_env p).

  Lemma singleton_traces:
    single_events sem.
  Proof.
    unfold single_events.
    intros s t s' Hstep.
    inversion Hstep; simpl;
      match goal with
      | Hcs_step: CS.kstep _ _ _ _ |- _ =>
        apply CS.singleton_traces in Hcs_step
      end; auto.
  Qed.

  Lemma star_component s1 t s2 :
    Star sem s1 t s2 ->
    s_component s2 =
    last (s_component s1) [seq next_comp_of_event e | e <- t].
  Proof.
    elim: s1 t s2 / => //= s1 t1 s2 t2 s3 _ Hstep _ -> ->.
    rewrite map_cat last_cat (kstep_component Hstep).
    move/singleton_traces: Hstep.
    by case: t1=> [|e [|e' t1]] //= *; omega.
  Qed.

  Lemma undef_in_program s1 t s2 :
    initial_state p ctx s1 ->
    Star sem s1 t s2 ->
    undef_in t (prog_interface p) ->
    is_program_component s2 ctx.
  Proof.
    move=> Hinitial Hstar.
    rewrite /undef_in /last_comp /is_program_component /is_context_component.
    rewrite /turn_of /= (star_component Hstar).
    have -> : s_component s1 = Component.main.
      case: s1 / Hinitial {Hstar} => ???????? Hpart.
      rewrite (partial_state_component Hpart) => ->.
      by rewrite /CS.initial_machine_state; case: prog_main.
    by move/fdisjointP: disjoint_interfaces; apply.
  Qed.

End Semantics.

Theorem initial_state_determinism:
  forall p ctx s1 s2,
    initial_state p ctx s1 ->
    initial_state p ctx s2 ->
    s1 = s2.
Proof.
  intros p ctx s1 s2 Hinit1 Hinit2.
  inversion Hinit1 as [p1 scs1 ? ? Hwf Hwf1 Hlinkable1 Hclosed1 Hpartial1 Hinitial1];
    inversion Hinit2 as [p2 scs2 ? Hsame_iface _ Hwf2 Hlinkable2 Hclosed2 Hpartial2 Hinitial2];
    subst.
  unfold CS.initial_state in *. subst.
  apply partialize_correct in Hpartial1.
  apply partialize_correct in Hpartial2.
  unfold CS.initial_machine_state in *.
  (* RB: TODO: CS.initial_machine state shouldn't produce None; lemma and refactoring. *)
  assert (exists main1, prog_main (program_link p p1) = Some main1) as [main1 Hmain1].
  {
    inversion Hclosed1.
    destruct (prog_main (program_link p p1)); [eauto | discriminate].
  }
  assert (exists main2, prog_main (program_link p p2) = Some main2) as [main2 Hmain2].
  {
    inversion Hclosed2.
    destruct (prog_main (program_link p p2)); [eauto | discriminate].
  }
  rewrite Hmain1 in Hpartial1.
  rewrite Hmain2 in Hpartial2.
  (* Some facts of common interest. *)
  inversion Hwf as [_ _ _ _ Hbuffers _ _].
  inversion Hwf1 as [_ Hprocs1 _ _ Hbuffers1 _ _].
  inversion Hwf2 as [_ Hprocs2 _ _ Hbuffers2 _ _].
  inversion Hlinkable1 as [_ Hdisjoint1]. inversion Hlinkable2 as [_ Hdisjoint2].
  pose proof linkable_disjoint_procedures Hwf Hwf1 Hlinkable1 as Hdisjproc1.
  pose proof linkable_disjoint_procedures Hwf Hwf2 Hlinkable2 as Hdisjproc2.
  (* same main component, same main expression *)
  (* empty stack *)
  (* stop continuation *)
  (* same partialized initial memory *)
  unfold partialize, CS.prepare_initial_memory, prepare_buffers, prog_buffers in Hpartial1.
  unfold partialize, CS.prepare_initial_memory, prepare_buffers, prog_buffers in Hpartial2.
  simpl in Hpartial1. simpl in Hpartial2.
  rewrite Hbuffers1 in Hpartial1. rewrite Hbuffers1 in Hpartial2.
  rewrite Hbuffers in Hdisjoint1. rewrite Hbuffers2 in Hdisjoint2.
  (* After unifying terminology, memories are of interest in both main cases. *)
  assert (
      filterm (fun (k : nat) (_ : ComponentMemory.t) => k \notin domm (prog_buffers p1))
                    (mapm
                       (fun initial_buffer : nat + list value =>
                        ComponentMemory.prealloc (setm emptym 0 initial_buffer))
                       (unionm (prog_buffers p) (prog_buffers p1)))
      =
      filterm (fun (k : nat) (_ : ComponentMemory.t) => k \notin domm (prog_buffers p1))
                    (mapm
                       (fun initial_buffer : nat + list value =>
                        ComponentMemory.prealloc (setm emptym 0 initial_buffer))
                       (unionm (prog_buffers p) (prog_buffers p2)))
    ) as Hmem.
  {
    clear Hpartial1 Hpartial2.
    pattern (prog_buffers p1) at -3.
    rewrite <- Hbuffers1.
    rewrite <- Hsame_iface.
    rewrite Hbuffers2.
    rewrite fdisjoint_filterm_mapm_unionm.
    - rewrite fdisjoint_filterm_mapm_unionm.
      + (* On p1... *)
        rewrite Hbuffers1 in Hdisjoint1.
        rewrite fdisjointC in Hdisjoint1.
        pose proof (domm_map
                   (fun initial_buffer =>
                     ComponentMemory.prealloc (setm emptym 0 initial_buffer))
                   (prog_buffers p))
          as Hdomm.
        rewrite <- Hdomm in Hdisjoint1.
        rewrite fdisjointC in Hdisjoint1.
        erewrite fdisjoint_filterm_full; last by assumption.
        (* ... and on p2, essentially the same. *)
        rewrite Hbuffers in Hdisjoint2.
        rewrite fdisjointC in Hdisjoint2.
        rewrite <- Hdomm in Hdisjoint2.
        rewrite fdisjointC in Hdisjoint2.
        erewrite fdisjoint_filterm_full; last by assumption.
        reflexivity.
      + by rewrite Hbuffers in Hdisjoint2.
    - by rewrite Hbuffers1 in Hdisjoint1.
  }
  (* Done with memory, useful for both cases. *)
  rewrite Hmem in Hpartial1.
  destruct (Component.main \in domm (prog_buffers p1)) eqn:Hif;
    rewrite Hif in Hpartial1; rewrite Hif in Hpartial2.
  - rewrite <- Hpartial1.
    rewrite <- Hpartial2.
    reflexivity.
  - (* Correspondence of mains is only interesting on this case. On one side... *)
    unfold prog_main, prog_procedures, program_link in Hmain1.
    rewrite (unionmC Hdisjproc1) in Hmain1.
    rewrite <- Hbuffers1 in Hif.
    rewrite Hprocs1 in Hif.
    pose proof find_procedure_unionm_r Hmain1 Hif as Hfind1.
    (* ... and another, almost the same, with some extra rewriting. *)
    unfold prog_main, prog_procedures, program_link in Hmain2.
    rewrite <- Hprocs1 in Hif.
    rewrite <- Hsame_iface in Hif.
    rewrite Hprocs2 in Hif.
    rewrite (unionmC Hdisjproc2) in Hmain2.
    pose proof find_procedure_unionm_r Hmain2 Hif as Hfind2.
    (* Join both sides, then complete the equality as above. *)
    assert (main1 = main2) by congruence; subst main2.
    rewrite <- Hpartial1.
    rewrite <- Hpartial2.
    reflexivity.
Qed.

(* we can prove a strong form of state determinism when the program is in control *)
Lemma state_determinism_program' p ctx G sps t1 t2 sps' :
  is_program_component sps ctx ->
  kstep p ctx G sps t1 sps' ->
  forall sps'', kstep p ctx G sps t2 sps'' ->
                t1 = t2 /\ sps' = sps''.
Proof.
  move=> in_prog step1.
  case: step1 in_prog=> {sps sps'} p1 scs1 scs1' int1 wf wf1 link clos kstep1
                        /partialize_correct <- /partialize_correct <-
                        in_prog sps''.
  case=> {sps''} p2 scs2 scs2' int2 _  wf2 _ _ kstep2
         /partialize_correct e12 /partialize_correct <-.
  have {in_prog} in_prog : CS.s_component scs1 \notin domm ctx.
    move: in_prog; simplify_turn.
    case: (scs1)=> [C ? ? ? ? ?] /=.
    by case: ifPn => /= [-> //|].
  rewrite int1 in link clos.
  move/CS.eval_kstep_complete in kstep2.
  case: (backward wf wf1 wf2 link clos int1 int2 (esym e12) in_prog kstep1).
  move=> scs2'' /CS.eval_kstep_complete; rewrite kstep2.
  by move=> [<- <-] <-.
Qed.

(* The weaker state determinism with program in control follows from the above. *)
Lemma state_determinism_program :
  forall p ctx G sps t sps',
    is_program_component sps ctx ->
    kstep p ctx G sps t sps' ->
  forall sps'',
    kstep p ctx G sps t sps'' ->
    sps' = sps''.
Proof.
  intros p ctx G sps t sps' Hpc Hkstep1 sps'' Hkstep2.
  apply (state_determinism_program' Hpc Hkstep1 Hkstep2).
Qed.

Lemma context_epsilon_step_is_silent:
  forall p ctx G sps sps',
    is_context_component sps ctx ->
    kstep p ctx G sps E0 sps' ->
    sps = sps'.
Proof.
  intros p ctx G sps sps' Hcontrol Hkstep.

  inversion Hkstep
    as [p' scs scs' Hiface Hlink _ _ _ Hcs_kstep Hpartial_sps Hpartial_sps'];
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
    + erewrite context_allocation_in_partialized_memory with (mem':=mem'); eauto.

    (* assign *)
    + erewrite context_store_in_partialized_memory with (mem':=mem'); eauto.

    (* same component call *)
    + rewrite partial_stack_ignores_change_by_context_with_control; auto.

    (* same component return *)
    + rewrite partial_stack_ignores_change_by_context_with_control; auto.
Qed.

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
move=> p ctx G sps t sps' in_ctx.
have [-> {t}|ne] := altP (t =P E0).
  move/(context_epsilon_step_is_silent in_ctx) => <- ?.
  by move/(context_epsilon_step_is_silent in_ctx) => <-.
case=> p1 scs1 scs1' iface1 wfp wfp1 link1 _ kstep1
      /partialize_correct partial_sps1 /partialize_correct partial_sps1' sps''.
case=> p2 scs2 scs2' iface2 _ wfp2 link2 _ kstep2
      /partialize_correct partial_sps2 /partialize_correct partial_sps2'.
PS.simplify_turn; rewrite -partial_sps1 s_component_partialize in in_ctx.
move: partial_sps1; rewrite -{}partial_sps2 => part.
rewrite -{}partial_sps1' -{}partial_sps2' {sps' sps''}.
case: scs1 t scs1' / kstep1 in_ctx ne part kstep2 => //=.
- (* External call *)
  move=> C stk1 mem1 k1 C' P v P_expr old1.
  move=> /eqP ne Himport1 Hfind1 in_ctx _ e_part.
  move e_t: [:: ECall _ _ _ _] => t kstep2.
  case: scs2 t scs2' / kstep2 C P v C' e_t in_ctx ne Himport1 Hfind1 e_part => //.
  move=> C stk2 mem2 k2 C' P v P_expr2 old2 _ Himport2 Hfind2.
  move=> _ _ _ _ [-> -> -> ->] in_ctx /eqP ne Himport1 Hfind1.
  rewrite /= in_ctx (lock filterm); case => e_stk; rewrite -lock => e_mem.
  have [in_ctx'|in_prog] := boolP (C' \in domm ctx).
    by rewrite (partial_stack_push_by_context old1 k1 old2 k2 ne in_ctx e_stk) e_mem.
  rewrite (partial_stack_push_by_context old1 k1 old2 k2 ne in_ctx e_stk) e_mem.
  case: (find_procedure_in_linked_programs wfp wfp1 link1 Hfind1).
    by rewrite iface1.
  case: (find_procedure_in_linked_programs wfp wfp2 link2 Hfind2).
    by rewrite iface2.
  by move=> _ -> _ [->].
- (* External return *)
  move=> C stk1 mem1 k1 v arg C' old1 ne in_ctx _ e_part.
  move e_t: [:: ERet _ _ _] => t kstep2.
  case: scs2 t scs2' / kstep2 C v C' e_t in_ctx ne e_part=> //.
  move=> C stk2 mem2 mem2' k2 v C' old2 _.
  move=> _ _ _ [-> -> ->] in_ctx ne.
  rewrite /= in_ctx (lock filterm).
  case=> e_stk; rewrite -lock=> e_mem.
  have [in_ctx'|in_prog] := boolP (C' \in domm ctx).
    by rewrite (partial_stack_pop_to_context ne in_ctx' e_stk) e_mem.
  case: (partial_stack_pop_to_program in_prog e_stk)=> <- [<- <-].
  by rewrite e_mem.
Qed.

Theorem state_determinism:
  forall p ctx G sps t sps',
    kstep p ctx G sps t sps' ->
  forall sps'',
    kstep p ctx G sps t sps'' ->
    sps' = sps''.
Proof.
  intros p ctx G sps t sps' Hstep1 sps'' Hstep2.
  inversion Hstep1 as [? ? _ _ _ _ _ _ _ Hpartial_sps1 _]; subst.
  (* case analysis on who has control *)
  inversion Hpartial_sps1; subst.
  - eapply state_determinism_program; eassumption.
  - eapply state_determinism_context; eassumption.
Qed.

(* Consider two star sequences starting from the same state (s),
   with the same number of steps (n) and the same trace (t):

        t            t
     s ->n s'     s ->n s''

   What can we say about s' and s''?
   Because of epsilon steps, there are several cases. In particular, problems are created
   by context epsilon steps in the middle of the sequence and program epsilon steps at the
   end of sequence. Recall that context epsilon steps are silent (they do not modify the state),
   while program epsilon steps are not (they modify the state).

   1) desync due to (m > 0) context epsilon steps in the middle of the first star
           t          E0
        s ->(n-m) s' ->m s''
      a) m program epsilon steps at the end of the second star
         s' <> s''
      b) m context epsilon steps at the end of the second star
         s' = s''
      Notice that we cannot have a mix of program and context steps because
      there would be a visible event due to the change of control.

   2) desync due to (m > 0) context epsilon steps in the middle of the second star
           t          E0
        s ->(n-m) s'' ->m s'
      a) m program epsilon steps at the end of the second star
         s' <> s''
      b) m context epsilon steps at the end of the second star
         s' = s''

   3) in sync, exact same steps
        s' = s''
      or, alternatively:
           t          E0
        s ->(n-0) s' ->0 s''
      which implies s' = s''

   In general:
     s' = s'' \/
                       t          E0
     (exists m > 0, s ->(n-m) s' ->m s'' /\ s' <> s'') \/
                       t           E0
     (exists m > 0, s ->(n-m) s'' ->m s' /\ s' <> s'')
*)

(* AAA: This does not appear to be used right now; remove? *)
Theorem state_determinism_starN_with_same_prefix:
  forall p ctx n sps t t' sps1' sps2',
    starN (kstep p ctx) (prepare_global_env p) n sps t sps1' ->
    starN (kstep p ctx) (prepare_global_env p) n sps (t ** t') sps2' ->
    (t' = E0 /\ sps1' = sps2') \/
    (exists m,
      starN (kstep p ctx) (prepare_global_env p) m sps1' t' sps2' /\ sps1' <> sps2') \/
    (exists m,
      t' = E0 /\ starN (kstep p ctx) (prepare_global_env p) m sps2' E0 sps1' /\ sps1' <> sps2').
Proof. Admitted.

(* AAA: This does not appear to be used right now; remove? *)
Corollary state_determinism_starN:
  forall p ctx n sps t sps' sps'',
    starN (kstep p ctx) (prepare_global_env p) n sps t sps' ->
    starN (kstep p ctx) (prepare_global_env p) n sps t sps'' ->
    sps' = sps'' \/
    (exists m,
      starN (kstep p ctx) (prepare_global_env p) m sps' E0 sps'' /\ sps' <> sps'') \/
    (exists m,
      starN (kstep p ctx) (prepare_global_env p) m sps'' E0 sps' /\ sps' <> sps'').
Proof.
  intros p ctx n sps t sps' sps''.
  intros HstarN1 HstarN2.
  rewrite <- (E0_right t) in HstarN2.
  destruct (state_determinism_starN_with_same_prefix HstarN1 HstarN2) as [[]|[|[m []]]]; subst.
  - left. reflexivity.
  - right. left. assumption.
  - right. right. eexists. eassumption.
Qed.

(* If a state s leads to two states s1 and s2 with the same trace t, it must
   be the case that s1 and s2 are connected. We arrive at s1 and s2 after a
   series of coordinated and identical alternations between program and
   context. Both s1 and s2 are either in the program or in the context. From
   the common starting state, observe the following facts about the sequence
   of phases.

    - A program phase starting from the same state is deterministic until
      the end of the execution or a change of control.

    - A context phase from the same state is silent until the end of the
      execution or a change of control.

   Note moreover that the shared trace preserves the state across turn
   boundaries. In the final phase, i.e., that of s1 and s2, we stop at two
   points in the deterministic execution of the program (in which case one
   of the two may always catch up to the other if needed), or at two
   indistinguishable states of the context. *)
Lemma state_determinism_star_E0 p ctx s s1 s2 :
  star (PS.kstep p ctx) (prepare_global_env p) s E0 s1 ->
  star (PS.kstep p ctx) (prepare_global_env p) s E0 s2 ->
  star (PS.kstep p ctx) (prepare_global_env p) s1 E0 s2 \/
  star (PS.kstep p ctx) (prepare_global_env p) s2 E0 s1.
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
  star (PS.kstep p ctx) (prepare_global_env p) s t s1 ->
  star (PS.kstep p ctx) (prepare_global_env p) s t s2 ->
  star (PS.kstep p ctx) (prepare_global_env p) s1 E0 s2 \/
  star (PS.kstep p ctx) (prepare_global_env p) s2 E0 s1.
Proof.
elim: t s => [|e t IH] s; first exact: state_determinism_star_E0.
case/(star_cons_inv (@singleton_traces p ctx)) => [s' [s1' [e_01 [e_11 e_t1]]]].
case/(star_cons_inv (@singleton_traces p ctx)) => [s'_ [s2' [e_02 [e_12]]]].
have {e_01 e_02} e_s : s' = s'_.
  have {e_t1 IH} H := state_determinism_star_E0 e_01 e_02.
  without loss H : s' s'_ s1' s2' e_11 e_12 {H e_01 e_02} / Star (sem p ctx) s' E0 s'_.
    by case: H; eauto=> H1 H2; apply: esym; eauto.
  have [in_c|in_p] := boolP (is_context_component s' ctx).
    exact: context_epsilon_star_is_silent in_c H.
  elim/star_E0_ind: s' s'_ / H in_p e_11 {e_12} => //.
  move=> s' s'm s'_ Hstep1 _ in_p Hstep2.
  by have [] := state_determinism_program' in_p Hstep1 Hstep2.
move: e_s e_12 => <- {s'_} e_12.
by have {s2' e_12} <- := state_determinism e_11 e_12; eauto.
Qed.

Lemma star_prefix p ctx s t t' s' s'' :
  star (kstep p ctx) (prepare_global_env p) s t s' ->
  star (kstep p ctx) (prepare_global_env p) s (t ** t') s'' ->
  (* missing steps in the first star (with trace t') *)
  star (kstep p ctx) (prepare_global_env p) s' t' s'' \/
  (* missing internal steps in the second star *)
  (t' = E0 /\
   star (kstep p ctx) (prepare_global_env p) s'' E0 s').
Proof.
case: t'=> [|e t'].
  rewrite E0_right => Hstar1 Hstar2.
  by case: (state_determinism_star_same_trace Hstar1 Hstar2); eauto.
move=> Hstar1 /(star_middle1_inv (@singleton_traces p ctx)) Hstar2; left.
case: Hstar2=> sa [sb [Hstar2a [Hstep2b Hstar2c]]].
have [s'_sa|sa_s'] := state_determinism_star_same_trace Hstar1 Hstar2a.
  rewrite -[e :: t']/(E0 ** [e] ** t').
  apply: star_trans; eauto.
  by apply: star_step; eauto.
suffices <- : sa = s' by rewrite -[e :: t']/([e] ** t'); apply: star_step; eauto.
have [in_c|in_p] := boolP (is_context_component sa ctx).
  by apply: context_epsilon_star_is_silent; eauto.
elim/star_E0_ind: sa s' / sa_s' Hstep2b in_p {Hstar1 Hstar2a}=> //.
move=> sa sa' sb' Hstep1 _ Hstep2 in_p.
by have [] := state_determinism_program' in_p Hstep1 Hstep2.
Qed.

End PS.
