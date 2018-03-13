Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.Maps.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.

Require Import Coq.Program.Equality.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require ssrnat.

Canonical ssrnat.nat_eqType.

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
    if (C \in ctx) && (C == Cincontrol) then
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
    let '(C', _, _) := last_frame in
    if (C \in ctx) && (C == C') then
      to_partial_stack_helper ctx s' last_frame
    else
      to_partial_frame ctx last_frame ::
      to_partial_stack_helper ctx s' (C, v, k)
  end.

Lemma to_partial_stack_helper_nonempty:
  forall ctx gps frame,
    to_partial_stack_helper ctx gps frame <> [].
Proof.
  move=> ctx gps [[C v] k].
  elim: gps => [|[[C' v'] k'] gps' IH] //=.
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
  let in_s := [(1, Int 1, Kstop);
               (0, Int 0, Kstop)] in
  let out_s := [(1, Some (Int 1, Kstop));
                (0, Some (Int 0, Kstop))] in
  to_partial_stack in_s fset0 1 = out_s.
Proof. by []. Qed.

Example to_partial_stack_context_internal_call_at_the_end:
  let in_s := [(1, Int 2, Kstop); (1, Int 1, Kstop);
               (0, Int 0, Kstop)] in
  let out_s := [(1, None); (0, Some (Int 0, Kstop))] in
  to_partial_stack in_s (fset1 1) 2 = out_s.
Proof. by []. Qed.

Example to_partial_stack_context_internal_call_at_the_beginning:
  let in_s := [(1, Int 2, Kstop);
               (0, Int 1, Kstop); (0, Int 0, Kstop)] in
  let out_s := [(1, Some (Int 2, Kstop));
                (0, None)] in
  to_partial_stack in_s (fset1 0) 1 = out_s.
Proof. by []. Qed.

Example to_partial_stack_context_internal_call_in_the_middle:
  let in_s := [(2, Int 4, Kstop);
               (1, Int 3, Kstop); (1, Int 2, Kstop); (1, Int 1, Kstop);
               (0, Int 0, Kstop)] in
  let out_s := [(2, Some (Int 4, Kstop));
                (1, None); (0, Some (Int 0, Kstop))] in
  to_partial_stack in_s (fset1 1) 1 = out_s.
Proof.  by []. Qed.

Example to_partial_stack_program_internal_calls:
  let in_s := [(3, Int 7, Kstop); (3, Int 6, Kstop);
               (1, Int 5, Kstop);
               (2, Int 4, Kstop); (2, Int 3, Kstop);
               (1, Int 2, Kstop);
               (0, Int 1, Kstop); (0, Int 0, Kstop)] in
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
  let in_s := [(0, Int 7, Kstop); (0, Int 6, Kstop);
               (2, Int 5, Kstop);
               (0, Int 4, Kstop); (0, Int 3, Kstop);
               (1, Int 2, Kstop);
               (0, Int 1, Kstop); (0, Int 0, Kstop)] in
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
    to_partial_stack ((C_incontrol, v, k) :: gps1) ctx C_incontrol' =
    to_partial_stack ((C_incontrol, v, k) :: gps2) ctx C_incontrol'.
Proof.
  rewrite /to_partial_stack /=.
  move=> ctx gps1 gps2 C_incontrol Hprog Hsame_stacks.
  move=> v k C_incontrol'; rewrite (negbTE Hprog) /=.
  elim: gps1 gps2 Hsame_stacks=> [|[[C1 v1] k1] gps1 IH] /=.
    case=> [|[[C' v'] k'] gps2']; rewrite /= (negbTE Hprog) //.
    case: ifP => [|_ <- //] /andP [HC'_in_ctx /eqP contra].
    by move: Hprog; rewrite -contra HC'_in_ctx.
  case=> [|[[C2 v2] k2] gps2]; rewrite /= (negbTE Hprog).
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
    to_partial_stack ((C_incontrol, v, k) :: gps) ctx C_incontrol =
    to_partial_stack gps ctx C_incontrol.
Proof.
  intros ctx gps C_incontrol Hin_ctx v k.
  unfold to_partial_stack.
  destruct gps as [|[[C' v'] k'] gps'];
  by rewrite /= Hin_ctx /= eqxx.
Qed.

Lemma partial_stack_push_by_context:
  forall ctx C C' v1 k1 v2 k2 gps1 gps2,
    C <> C' ->
    C \in ctx ->
    to_partial_stack gps1 ctx C =
    to_partial_stack gps2 ctx C ->
    to_partial_stack ((C, v1, k1) :: gps1) ctx C' =
    to_partial_stack ((C, v2, k2) :: gps2) ctx C'.
Proof.
  intros ctx C C' v1 k1 v2 k2 gps1 gps2.
  move=> /eqP Hdiff Hctx Hstacks.
  unfold to_partial_stack. simpl.
  rewrite Hctx /= (negbTE Hdiff).
  unfold to_partial_stack in Hstacks.
  induction gps1 as [|[[C_a v_a] k_a] gps1']; simpl in *.
  - induction gps2 as [|[[C_b v_b] k_b] gps2']; simpl in *.
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
    induction gps2 as [|[[C_b v_b] k_b] gps2']; simpl in *.
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
    to_partial_stack ((C', old_call_arg1, k1) :: gps1) ctx C =
    to_partial_stack ((C', old_call_arg2, k2) :: gps2) ctx C ->
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
  destruct gps1 as [|[[C_a v_a] k_a] gps1'].
  - destruct gps2 as [|[[C_b v_b] k_b] gps2'].
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
  - destruct gps2 as [|[[C_b v_b] k_b] gps2'].
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
    to_partial_stack ((C', v1, k1) :: gps1) ctx C =
    to_partial_stack ((C', v2, k2) :: gps2) ctx C ->
    to_partial_stack gps1 ctx C' = to_partial_stack gps2 ctx C'.
Proof.
  intros ctx C C' v1 k1 v2 k2 gps1 gps2.
  move=> /eqP Hdiff Hctx Hstacks.
  unfold to_partial_stack in Hstacks. simpl in *.
  rewrite eq_sym (negbTE Hdiff) Hctx /= in Hstacks.
  induction gps1 as [|[[C_a v_a] k_a] gps1']; simpl in *.
  - induction gps2 as [|[[C_b v_b] k_b] gps2']; simpl in *.
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
  - induction gps2 as [|[[C_b v_b] k_b] gps2']; simpl in *.
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
    well_formed_program p ->
    well_formed_program p' ->
    linkable (prog_interface p) (prog_interface p') ->
    partial_state ctx scs sps ->
    CS.initial_state (program_link p p') scs ->
    initial_state p ctx sps.

Inductive final_state (p: program) (ctx: Program.interface) : state -> Prop :=
| final_state_program: forall p' scs sps,
    prog_interface p' = ctx ->
    well_formed_program p ->
    well_formed_program p' ->
    linkable (prog_interface p) (prog_interface p') ->
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
      well_formed_program p ->
      well_formed_program p' ->
      linkable (prog_interface p) (prog_interface p') ->
      CS.kstep (prepare_global_env (program_link p p')) scs t scs' ->
      partial_state ctx scs sps ->
      partial_state ctx scs' sps' ->
      kstep p ctx (prepare_global_env p) sps t sps'.

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
End Semantics.

Theorem initial_state_determinism:
  forall p ctx s1 s2,
    initial_state p ctx s1 ->
    initial_state p ctx s2 ->
    s1 = s2.
Proof.
  intros p ctx s1 s2 Hinit1 Hinit2.
  inversion Hinit1 as [p1 scs1 ? ? Hwf Hwf1 Hlinkable1 Hpartial1 Hinitial1];
    inversion Hinit2 as [p2 scs2 ? Hsame_iface _ Hwf2 Hlinkable2 Hpartial2 Hinitial2];
    subst.
  unfold CS.initial_state in *. subst.
  apply partialize_correct in Hpartial1.
  apply partialize_correct in Hpartial2.
  unfold CS.initial_machine_state in *.
  (* RB: TODO: CS.initial_machine state shouldn't produce None. *)
  assert (exists main1, prog_main (program_link p p1) = Some main1) as [main1 Hmain1] by admit.
  assert (exists main2, prog_main (program_link p p2) = Some main2) as [main2 Hmain2] by admit.
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
        pose proof domm_mapm (nat + list value) ComponentMemory.t (prog_buffers p)
             (fun initial_buffer : nat + list value =>
                ComponentMemory.prealloc (setm emptym 0 initial_buffer))
          as Hdomm.
        rewrite fdisjointC in Hdisjoint1.
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
Admitted.

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
    as [p1 sps1 t1 sps1' scs1 scs1' Hiface1 wf wf1 Hlink1 Hkstep1 Hpartial_sps1 Hpartial_sps1'];
    subst.
  inversion Hstep2
    as [p2 sps2 t2 sps2' scs2 scs2' Hiface2 _  wf2 Hlink2 Hkstep2 Hpartial_sps2 Hpartial_sps2'];
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
      suffices -> : b = b0 by [].
      move: H6 H10; rewrite !mapmE /=.
      case: getm=> [v1|] //= [<-].
      by case: getm=> [v2|] //= [<-].

    (* alloc *)
    + (* show that memory changes in the same way *)
      destruct (program_allocation_in_partialized_memory H7 H H11 H12)
        as [Hptr Hmem].
      rewrite H8 Hptr Hmem.
      reflexivity.

    (* deref *)
    + (* show that the loaded value is the same (v == v0) *)
      rewrite (program_load_in_partialized_memory H7 H H11 H13).
      reflexivity.

    (* assign *)
    + (* show that memory changes in the same way *)
      rewrite H8.
      rewrite (program_store_in_partialized_memory H7 H H11 H14).
      reflexivity.

    (* call *)

    (* inside the same component *)
    + (* show stack and memory are changing in the same way *)
      assert (b = b0).
      { move: H12 H18; rewrite !mapmE /=.
        case: getm=> [v1|] //= [<-].
        by case: getm=> [v2|] //= [<-]. }
      assert (b' = b'0).
      { move: H14 H20; rewrite !mapmE /=.
        case: getm=> [v1|] //= [<-].
        by case: getm=> [v2|] //= [<-].
      }
      assert (P_expr = P_expr0). {
        destruct (find_procedure_in_linked_programs wf wf1 Hlink1 H9 H)
          as [HP_expr Hfind_proc].
        rewrite <- Hiface2 in H.
        destruct (find_procedure_in_linked_programs wf wf2 Hlink2 H17 H)
          as [HP_expr' Hfind_proc'].
        rewrite Hfind_proc in Hfind_proc'.
        inversion Hfind_proc'. subst.
        reflexivity.
      }
      subst.
      assert (old_call_arg0 = old_call_arg)
        as Hsame_old_call_arg.
      { eapply program_load_in_partialized_memory
          with (mem1:=mem0) (mem2:=mem); eauto. }
      erewrite partial_stack_push_by_program with (gps2:=gps0);
        auto.
      rewrite (program_store_in_partialized_memory H7 H H15 H21).
      subst.
      reflexivity.

    (* internal *)
    + (* show stack and memory are changing in the same way *)
      assert (b = b0).
      { destruct (prepare_buffers_of_linked_programs wf wf1 Hlink1 H13 H) as [? Hb].
        rewrite <- Hiface2 in H.
        destruct (prepare_buffers_of_linked_programs wf wf2 Hlink2 H21 H) as [? Hb'].
        rewrite Hb in Hb'. inversion Hb'.
        subst.
        reflexivity.
      }
      assert (b' = b'0).
      { destruct (prepare_buffers_of_linked_programs wf wf1 Hlink1 H15 H12) as [? Hb].
        rewrite <- Hiface2 in H12.
        destruct (prepare_buffers_of_linked_programs wf wf2 Hlink2 H23 H12) as [? Hb'].
        rewrite Hb in Hb'. inversion Hb'.
        subst.
        reflexivity.
      }
      assert (P_expr = P_expr0). {
        destruct (find_procedure_in_linked_programs wf wf1 Hlink1 H10 H12)
          as [HP_expr Hfind_proc].
        rewrite <- Hiface2 in H12.
        destruct (find_procedure_in_linked_programs wf wf2 Hlink2 H20 H12)
          as [HP_expr' Hfind_proc'].
        rewrite Hfind_proc in Hfind_proc'.
        inversion Hfind_proc'. subst.
        reflexivity.
      }
      subst.
      assert (old_call_arg0 = old_call_arg)
        as Hsame_old_call_arg.
      { eapply program_load_in_partialized_memory
          with (C:=C) (mem1:=mem0) (mem2:=mem); eauto. }
      subst.
      rewrite (program_store_in_partialized_memory H7 H12 H16 H24).
      erewrite partial_stack_push_by_program with (gps2:=gps0); auto.

    (* external *)
    + assert (b = b0).
      { destruct (prepare_buffers_of_linked_programs wf wf1 Hlink1 H13 H) as [? Hb].
        rewrite <- Hiface2 in H.
        destruct (prepare_buffers_of_linked_programs wf wf2 Hlink2 H21 H) as [? Hb'].
        rewrite Hb in Hb'. inversion Hb'.
        subst.
        reflexivity.
      }
      subst.
      assert (old_call_arg0 = old_call_arg)
        as Hsame_old_call_arg.
      { eapply program_load_in_partialized_memory
          with (C:=C) (mem1:=mem0) (mem2:=mem); eauto. }
      subst.
      erewrite partial_stack_push_by_program with (gps2:=gps0); auto.
      rewrite (context_store_in_partialized_memory H12 H16).
      rewrite (context_store_in_partialized_memory H12 H24).
      rewrite H7.
      reflexivity.

    (* return *)

    (* inside the same component *)
    (* show stack and memory are changing in the same way *)
    + assert (b = b0).
      { destruct (prepare_buffers_of_linked_programs wf wf1 Hlink1 H11 H) as [? Hb].
        rewrite <- Hiface2 in H.
        destruct (prepare_buffers_of_linked_programs wf wf2 Hlink2 H9 H) as [? Hb'].
        rewrite Hb in Hb'. inversion Hb'.
        subst.
        reflexivity.
      }
      subst.
      destruct (partial_stack_pop_to_program H H8)
        as [Hold_call_arg [Hkont Hstack]].
      subst. rewrite Hstack.
      rewrite (program_store_in_partialized_memory H7 H13 H12 H10).
      reflexivity.

    (* internal *)
    + (* show stack and memory are changing in the same way *)
      assert (b = b0).
      { destruct (prepare_buffers_of_linked_programs wf wf1 Hlink1 H11 H15) as [? Hb].
        rewrite <- Hiface2 in H15.
        destruct (prepare_buffers_of_linked_programs wf wf2 Hlink2 H13 H15) as [? Hb'].
        rewrite Hb in Hb'. inversion Hb'.
        subst.
        reflexivity.
      }
      subst.
      destruct (partial_stack_pop_to_program H15 H8)
        as [Hold_call_arg [Hkont Hstack]].
      subst. rewrite Hstack.
      rewrite (program_store_in_partialized_memory H7 H15 H12 H14).
      reflexivity.

    (* external *)
    + rewrite (context_store_in_partialized_memory H15 H12).
      rewrite (context_store_in_partialized_memory H15 H14).
      rewrite H7.
      rewrite (partial_stack_pop_to_context H10 H15 H8).
      reflexivity.

  (* context has control (contra) *)
  - PS.simplify_turn.
    match goal with
    | Hin: context[domm (prog_interface p1)],
      Hnotin: context[domm (prog_interface p1)] |- _ =>
      rewrite Hin in Hnotin; discriminate
    end.
Qed.

(* we can prove something stronger when program is in control *)
Lemma state_determinism_program':
  forall p ctx G sps t1 t2 sps',
    is_program_component sps ctx ->
    kstep p ctx G sps t1 sps' ->
  forall sps'',
    kstep p ctx G sps t2 sps'' ->
    t1 = t2 /\ sps' = sps''.
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
    as [p' ? ? ? scs scs' Hiface Hlink _ _ Hcs_kstep Hpartial_sps Hpartial_sps'];
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
    + erewrite context_store_in_partialized_memory with (mem':=mem'); eauto.
      rewrite partial_stack_ignores_change_by_context_with_control; auto.

    (* same component return *)
    + erewrite context_store_in_partialized_memory with (mem':=mem'); eauto.
      rewrite partial_stack_ignores_change_by_context_with_control; auto.
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
  intros p ctx G sps t sps' Hcontrol Hstep1 sps'' Hstep2.

  inversion Hstep1
    as [p1 sps1 t1 sps1' scs1 scs1' Hiface1 Hwfp Hwfp1 Hlink1 Hkstep1 Hpartial_sps1 Hpartial_sps1'];
    subst.
  inversion Hstep2
    as [p2 sps2 t2 sps2' scs2 scs2' Hiface2 _ Hwfp2 Hlink2 Hkstep2 Hpartial_sps2 Hpartial_sps2'];
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
      (* external call *)
      * assert (P_expr = P_expr0). {
          destruct (find_procedure_in_linked_programs Hwfp Hwfp1 Hlink1 H10 H12)
            as [HP_expr Hfind_proc].
          rewrite <- Hiface2 in H12.
          destruct (find_procedure_in_linked_programs Hwfp Hwfp2 Hlink2 H21 H12)
            as [HP_expr' Hfind_proc'].
          rewrite Hfind_proc in Hfind_proc'.
          inversion Hfind_proc'. subst.
          reflexivity.
        }
        subst.
        assert (b' = b'0).
        { destruct (prepare_buffers_of_linked_programs Hwfp Hwfp1 Hlink1 H15 H12) as [? Hb].
          rewrite <- Hiface2 in H12.
          destruct (prepare_buffers_of_linked_programs Hwfp Hwfp2 Hlink2 H24 H12) as [? Hb'].
          rewrite Hb in Hb'. inversion Hb'.
          subst.
          reflexivity.
        }
        subst.
        (* same stack *)
        rewrite (partial_stack_push_by_context
                   old_call_arg k1 old_call_arg0 k H8 H H6).
        (* same memory *)
        rewrite (program_store_in_partialized_memory H5 H12 H16 H25).
        reflexivity.
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
      (* internal call *)
      * (* same stack *)
        rewrite (partial_stack_push_by_context
                   old_call_arg k1 old_call_arg0 k H8 H H6).
        (* same memory *)
        erewrite context_store_in_partialized_memory with (mem0:=mem) (mem':=mem'); eauto.
        erewrite context_store_in_partialized_memory with (mem0:=mem0) (mem':=mem'0); eauto.
        rewrite H5.
        reflexivity.

    (* internal & external return *)
    + inversion Hkstep2; subst.
      inversion Hpartial_sps1'; subst;
      inversion Hpartial_sps2'; subst; PS.simplify_turn.
      (* external return *)
      * (* same stack *)
        destruct (partial_stack_pop_to_program H9 H6) as [Hsame_arg [Hsame_k Hstack]].
        subst. rewrite Hstack.
        (* same memory *)
        assert (b = b0).
        { destruct (prepare_buffers_of_linked_programs Hwfp Hwfp1 Hlink1 H11 H9) as [? Hb].
          rewrite <- Hiface2 in H9.
          destruct (prepare_buffers_of_linked_programs Hwfp Hwfp2 Hlink2 H15 H9) as [? Hb'].
          rewrite Hb in Hb'. inversion Hb'.
          subst.
          reflexivity.
        }
        subst.
        rewrite (program_store_in_partialized_memory H5 H9 H12 H16).
        reflexivity.
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
      (* internal return *)
      * (* same stack *)
        rewrite (partial_stack_pop_to_context H10 H9 H6).
        (* same memory *)
        erewrite context_store_in_partialized_memory with (mem0:=mem) (mem':=mem'); eauto.
        erewrite context_store_in_partialized_memory with (mem0:=mem0) (mem':=mem'0); eauto.
        rewrite H5.
        reflexivity.
Qed.

Theorem state_determinism:
  forall p ctx G sps t sps',
    kstep p ctx G sps t sps' ->
  forall sps'',
    kstep p ctx G sps t sps'' ->
    sps' = sps''.
Proof.
  intros p ctx G sps t sps' Hstep1 sps'' Hstep2.

  inversion Hstep1
    as [p1 sps1 t1 sps1' scs1 scs1' Hiface1 Hwfp Hwfp1 Hlink1 Hkstep1 Hpartial_sps1 Hpartial_sps1'];
    subst.
  inversion Hstep2
    as [p2 sps2 t2 sps2' scs2 scs2' Hiface2 _ Hwfp2 Hlink2 Hkstep2 Hpartial_sps2 Hpartial_sps2'];
    subst.

  (* case analysis on who has control *)
  inversion Hpartial_sps1; subst.
  - eapply state_determinism_program; now eauto.
  - eapply state_determinism_context; now eauto.
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

Theorem state_determinism_starN_with_same_prefix:
  forall p ctx n sps t t' sps' sps'',
    starN (kstep p ctx) (prepare_global_env p) n sps t sps' ->
    starN (kstep p ctx) (prepare_global_env p) n sps (t ** t') sps'' ->
    (t' = E0 /\ sps' = sps'') \/
    (exists m,
      starN (kstep p ctx) (prepare_global_env p) m sps' t' sps'' /\ sps' <> sps'') \/
    (exists m,
      t' = E0 /\ starN (kstep p ctx) (prepare_global_env p) m sps'' E0 sps' /\ sps' <> sps'').
Proof.
  intros p ctx n sps t t' sps' sps''.
  intros HstarN1 HstarN2.
Admitted.

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
End PS.
