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

Example to_partial_stack_empty_context:
  let in_s := [(1, Int 1, Kstop);
               (0, Int 0, Kstop)] in
  let out_s := [(1, Some (Int 1, Kstop));
                (0, Some (Int 0, Kstop))] in
  to_partial_stack in_s fset0 1 = out_s.
Proof.
  compute. reflexivity.
Qed.

Example to_partial_stack_context_internal_call_at_the_end:
  let in_s := [(1, Int 2, Kstop); (1, Int 1, Kstop);
               (0, Int 0, Kstop)] in
  let out_s := [(1, None); (0, Some (Int 0, Kstop))] in
  to_partial_stack in_s (fset1 1) 2 = out_s.
Proof.
  compute. reflexivity.
Qed.

Example to_partial_stack_context_internal_call_at_the_beginning:
  let in_s := [(1, Int 2, Kstop);
               (0, Int 1, Kstop); (0, Int 0, Kstop)] in
  let out_s := [(1, Some (Int 2, Kstop));
                (0, None)] in
  to_partial_stack in_s (fset1 0) 1 = out_s.
Proof.
  compute. reflexivity.
Qed.

Example to_partial_stack_context_internal_call_in_the_middle:
  let in_s := [(2, Int 4, Kstop);
               (1, Int 3, Kstop); (1, Int 2, Kstop); (1, Int 1, Kstop);
               (0, Int 0, Kstop)] in
  let out_s := [(2, Some (Int 4, Kstop));
                (1, None); (0, Some (Int 0, Kstop))] in
  to_partial_stack in_s (fset1 1) 1 = out_s.
Proof.
  compute. reflexivity.
Qed.

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
    + (* the hard case with lots of case analysis *)
      destruct (C' \in ctx) eqn:HC'in_ctx.
      * rewrite HC'in_ctx.
        simpl.
        rewrite HC'in_ctx in Hsame_stacks.
        simpl in Hsame_stacks.
        destruct (Component.eqb C' C_incontrol)
                 eqn:HC'eqC_incontrol.
        ** destruct (drop_last_frames_if_needed
                       ctx gps1' C_incontrol) eqn:Hdrop_gps1'.
           *** assert (C'' \in ctx) as HC''in_ctx.
               { destruct (C'' \in ctx) eqn:HC''in_ctx; auto.
                 rewrite HC''in_ctx in Hsame_stacks.
                 simpl in Hsame_stacks.
                 exfalso.
                 symmetry in Hsame_stacks.
                 eapply to_partial_stack_helper_nonempty.
                 eauto.
               }
               assert (Component.eqb C'' C_incontrol) as
                   HC''eqC_incontrol.
               { rewrite HC''in_ctx in Hsame_stacks.
                 destruct (Component.eqb C'' C_incontrol)
                          eqn:HC''eqC_incontrol; auto.
                 simpl in Hsame_stacks.
                 exfalso.
                 symmetry in Hsame_stacks.
                 eapply to_partial_stack_helper_nonempty.
                 eauto.
               }
               assert (drop_last_frames_if_needed
                         ctx gps2' C_incontrol = [])
                 as Hdrop_gps2'.
               { rewrite HC''in_ctx in Hsame_stacks.
                 rewrite HC''eqC_incontrol in Hsame_stacks.
                 simpl in Hsame_stacks.
                 destruct (drop_last_frames_if_needed
                             ctx gps2' C_incontrol); auto.
                 exfalso.
                 symmetry in Hsame_stacks.
                 eapply to_partial_stack_helper_nonempty.
                 eauto.
               }
               rewrite HC''in_ctx HC''eqC_incontrol. simpl.
               rewrite HC''in_ctx in IHgps1'.
               rewrite HC''eqC_incontrol in IHgps1'.
               rewrite Hdrop_gps2' in IHgps1'.
               simpl in IHgps1'.
               apply IHgps1'; auto.
           *** destruct (C'' \in ctx) eqn:HC''in_ctx.
               **** rewrite HC''in_ctx.
                    rewrite HC''in_ctx in Hsame_stacks.
                    destruct (Component.eqb C'' C_incontrol)
                             eqn:HC''eqC_incontrol; simpl in *.
                    ***** rewrite HC''in_ctx in IHgps1'.
                          simpl in IHgps1'.
                          apply IHgps1'.
                          rewrite Hsame_stacks.
                          reflexivity.
                    ***** rewrite Hnot_in_ctx.
                          rewrite Hnot_in_ctx in IHgps1'.
                          rewrite HC''in_ctx in IHgps1'.
                          simpl in IHgps1'.
                          apply IHgps1'; auto.
               **** rewrite HC''in_ctx.
                    rewrite Hnot_in_ctx. simpl.
                    rewrite HC''in_ctx in Hsame_stacks.
                    simpl in Hsame_stacks.
                    rewrite Hnot_in_ctx in IHgps1'.
                    rewrite HC''in_ctx in IHgps1'.
                    simpl in IHgps1'.
                    apply IHgps1'; auto.
        ** destruct (C'' \in ctx) eqn:HC''in_ctx.
           *** rewrite HC''in_ctx.
               rewrite HC''in_ctx in Hsame_stacks.
               destruct (Component.eqb C'' C_incontrol)
                        eqn:HC''eqC_incontrol; simpl in *.
               **** destruct (drop_last_frames_if_needed
                                ctx gps2') eqn:Hdrop_gps2'.
                    ***** (* contra *)
                      exfalso.
                      eapply to_partial_stack_helper_nonempty.
                      eauto.
                    ***** rewrite HC''in_ctx in IHgps1'.
                          simpl in IHgps1'.
                          rewrite HC'in_ctx in IHgps2'.
                          simpl in IHgps2'.
                          apply IHgps2'; auto.
               **** rewrite Hnot_in_ctx.
                    rewrite Hsame_stacks. reflexivity.
           *** rewrite Hnot_in_ctx.
               rewrite HC''in_ctx. simpl.
               rewrite HC''in_ctx in Hsame_stacks.
               simpl in Hsame_stacks.
               rewrite Hsame_stacks. reflexivity.
      * rewrite Hnot_in_ctx.
        rewrite HC'in_ctx. simpl.
        rewrite HC'in_ctx in Hsame_stacks.
        simpl in Hsame_stacks.
        destruct (C'' \in ctx) eqn:HC''in_ctx.
        ** rewrite HC''in_ctx.
           rewrite HC''in_ctx in Hsame_stacks.
           destruct (Component.eqb C'' C_incontrol)
                    eqn:HC''eqC_incontrol; simpl in *.
           *** rewrite Hsame_stacks.
               destruct (drop_last_frames_if_needed
                           ctx gps2') eqn:Hdrop_gps2'.
               **** (* contra *)
                    exfalso.
                    eapply to_partial_stack_helper_nonempty.
                    eauto.
               **** rewrite <- Hsame_stacks.
                    rewrite HC''in_ctx in IHgps1'.
                    simpl in IHgps1'.
                    rewrite HC'in_ctx in IHgps2'.
                    simpl in IHgps2'.
                    apply IHgps2'; auto.
           *** rewrite Hsame_stacks. reflexivity.
        ** rewrite HC''in_ctx.
           rewrite HC''in_ctx in Hsame_stacks.
           simpl in *.
           rewrite Hsame_stacks. reflexivity.
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
  destruct gps as [|[[C' v'] k'] gps'].
  - simpl. rewrite Hin_ctx.
    unfold Component.eqb. rewrite Nat.eqb_refl. simpl.
    reflexivity.
  - simpl. rewrite Hin_ctx.
    unfold Component.eqb. rewrite Nat.eqb_refl. simpl.
    reflexivity.
Qed.

Lemma partial_stack_pop_by_program_to_context:
  forall ctx C_incontrol C' v1 k1 v2 k2 gps1 gps2,
    C' <> C_incontrol ->
    C_incontrol \notin ctx ->
    C' \in ctx ->
    to_partial_stack ((C', v1, k1) :: gps1) ctx C_incontrol =
    to_partial_stack ((C', v2, k2) :: gps2) ctx C_incontrol ->
    to_partial_stack gps1 ctx C' = to_partial_stack gps2 ctx C'.
Proof.
  intros ctx C_incontrol C' v1 k1 v2 k2 gps1 gps2.
  intros Hdiff Hprog Hctx Hstack.
  unfold to_partial_stack in Hstack.
  unfold drop_last_frames_if_needed in Hstack.
  rewrite Hctx in Hstack.
  apply Nat.eqb_neq in Hdiff.
  unfold Component.eqb in Hstack.
  rewrite Hdiff in Hstack. simpl in Hstack.
  induction gps1 as [|[[C_a v_a] k_a] gps1'].
  - induction gps2 as [|[[C_b v_b] k_b] gps2'].
    + reflexivity.
    + simpl in *.
      rewrite Hctx in Hstack.
      destruct (C_b \in ctx) eqn:HC_b_in_ctx.
      * rewrite HC_b_in_ctx in Hstack.
        destruct (Component.eqb C_b C') eqn:HC_b_eq_C'.
        ** simpl in *.
           rewrite Hctx in IHgps2'.
           unfold to_partial_stack in *. simpl.
           rewrite HC_b_in_ctx.
           rewrite HC_b_eq_C'. simpl in *.
           rewrite IHgps2'; auto.
           destruct (drop_last_frames_if_needed ctx gps2' C');
             reflexivity.
        ** simpl in *.
           inversion Hstack.
           exfalso.
           symmetry in H0.
           eapply to_partial_stack_helper_nonempty.
           eauto.
      * rewrite HC_b_in_ctx in Hstack.
        simpl in *.
        inversion Hstack.
        exfalso.
        symmetry in H0.
        eapply to_partial_stack_helper_nonempty.
        eauto.
  - induction gps2 as [|[[C_b v_b] k_b] gps2'].
    + simpl in *.
      rewrite Hctx in Hstack.
      destruct (C_a \in ctx) eqn:HC_a_in_ctx.
      * rewrite HC_a_in_ctx in Hstack.
        destruct (Component.eqb C_a C') eqn:HC_a_eq_C'.
        ** simpl in *.
           unfold to_partial_stack. simpl.
           apply Nat.eqb_eq in HC_a_eq_C'. subst.
           rewrite HC_a_in_ctx. simpl.
           unfold Component.eqb.
           rewrite Nat.eqb_refl.
           induction gps1'.
           *** simpl in *. reflexivity.
           *** simpl in *. destruct a. destruct p.
               rewrite HC_a_in_ctx in Hstack.
               destruct (i \in ctx) eqn:H1.
               **** rewrite H1 in Hstack.
                    destruct (Component.eqb i C') eqn:Hi_eq_C'.
                    ***** simpl in *.
                          rewrite H1. simpl.
                          apply IHgps1'0.
                          intro.
                          rewrite <- IHgps1'.
                          unfold to_partial_stack. simpl.
                          rewrite H1 Hi_eq_C'. simpl.
                          reflexivity.
                          rewrite H1 Hctx. simpl. auto. auto.
                    ***** simpl in *.
                          inversion Hstack.
                          exfalso.
                          symmetry in H0.
                          eapply to_partial_stack_helper_nonempty.
                          eauto.
               **** rewrite H1 in Hstack. simpl in *.
                    simpl in *.
                    inversion Hstack.
                    exfalso.
                    symmetry in H0.
                    eapply to_partial_stack_helper_nonempty.
                    eauto.
        ** simpl in *.
           inversion Hstack.
           exfalso.
           symmetry in H0.
           eapply to_partial_stack_helper_nonempty.
           eauto.
      * rewrite HC_a_in_ctx in Hstack. simpl in *.
        simpl in *.
        inversion Hstack.
        exfalso.
        symmetry in H0.
        eapply to_partial_stack_helper_nonempty.
        eauto.
    + simpl in Hstack.
      rewrite Hctx in Hstack.
      destruct (C_a \in ctx) eqn:HC_a_in_ctx.
      * rewrite HC_a_in_ctx in Hstack.
        destruct (Component.eqb C_a C') eqn:HC_a_eq_C'.
        ** simpl in *.
           admit.
           (*
           unfold to_partial_stack in IHgps2'.
           rewrite Hctx HC_a_in_ctx HC_a_eq_C' in IHgps2'.
           simpl in *.
           rewrite HC_a_in_ctx in IHgps2'. simpl in *.
           rewrite HC_a_eq_C' in IHgps2'.
           unfold to_partial_stack. simpl.
           rewrite HC_a_in_ctx HC_a_eq_C'. simpl.
           assert (C_b \in ctx) as HC_b_in_ctx.
           { admit.
           }
           assert (Component.eqb C_b C') as HC_b_eq_C'.
           { admit.
           }
           rewrite HC_b_in_ctx HC_b_eq_C' in Hstack. simpl in *.
           rewrite IHgps2'; auto.
           unfold to_partial_stack. simpl.
           rewrite HC_b_in_ctx HC_b_eq_C'. simpl.
           reflexivity.*)
        ** simpl in *.
           rewrite Hctx HC_a_in_ctx HC_a_eq_C' in IHgps2'.
           simpl in *.
           destruct (C_b \in ctx) eqn:HC_b_in_ctx.
           *** rewrite HC_b_in_ctx in Hstack. simpl in *.
               destruct (Component.eqb C_b C') eqn:HC_b_eq_C'.
               **** admit. (*rewrite IHgps2'; auto.
                    unfold to_partial_stack. simpl.
                    rewrite HC_b_in_ctx HC_b_eq_C'. simpl.
                    reflexivity.*)
               **** unfold to_partial_stack. simpl.
                    rewrite HC_a_in_ctx HC_a_eq_C'.
                    rewrite HC_b_in_ctx HC_b_eq_C'.
                    simpl. inversion Hstack.
                    auto.
           *** rewrite HC_b_in_ctx in Hstack. simpl in *.
               unfold to_partial_stack. simpl.
               rewrite HC_a_in_ctx HC_b_in_ctx. simpl.
               rewrite HC_a_eq_C'.
               inversion Hstack. auto.
      * rewrite HC_a_in_ctx in Hstack. simpl in Hstack.
        destruct (C_b \in ctx) eqn:HC_b_in_ctx.
        ** rewrite HC_b_in_ctx in Hstack. simpl in Hstack.
           destruct (Component.eqb C_b C') eqn:HC_b_eq_C'.
           *** simpl in *.
               rewrite Hctx HC_a_in_ctx in IHgps2'. simpl in *.
               admit.
               (*rewrite IHgps2'; auto.
               unfold to_partial_stack. simpl.
               rewrite HC_b_in_ctx HC_b_eq_C'. simpl.
               reflexivity.*)
           *** inversion Hstack.
               unfold to_partial_stack. simpl.
               rewrite HC_a_in_ctx HC_b_in_ctx. simpl.
               rewrite HC_b_eq_C'.
               auto.
        ** rewrite HC_b_in_ctx in Hstack. simpl in Hstack.
           unfold to_partial_stack. simpl.
           rewrite HC_a_in_ctx HC_b_in_ctx. simpl.
           inversion Hstack.
           auto.
Admitted.

Lemma partial_stack_pop_by_program_to_program:
  forall ctx C C' old_call_arg1 k1 old_call_arg2 k2 gps1 gps2,
    C \notin ctx ->
    C' \notin ctx ->
    to_partial_stack ((C', old_call_arg1, k1) :: gps1) ctx C =
    to_partial_stack ((C', old_call_arg2, k2) :: gps2) ctx C ->
    old_call_arg1 = old_call_arg2 /\ k1 = k2 /\
    to_partial_stack gps1 ctx C' = to_partial_stack gps2 ctx C'.
Proof.
  intros ctx C C' old_call_arg1 k1 old_call_arg2 k2 gps1 gps2.
  intros Hprog1 Hprog2 Hstack.
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
      * destruct (Component.eqb C_b C') eqn:HC_b_eq_C';
          simpl in *.
        ** apply Nat.eqb_eq in HC_b_eq_C'. subst.
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
      * destruct (Component.eqb C_a C') eqn:HC_a_eq_C';
          simpl in *.
        ** apply Nat.eqb_eq in HC_a_eq_C'. subst.
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
           destruct (Component.eqb C_a C') eqn:HC_a_eq_C'.
           *** destruct (Component.eqb C_b C') eqn:HC_b_eq_C'.
               **** simpl in *.
                    apply Nat.eqb_eq in HC_a_eq_C'. subst.
                    rewrite Hin_ctx_aux in HC_a_in_ctx.
                    discriminate.
               **** simpl in *.
                    apply Nat.eqb_eq in HC_a_eq_C'. subst.
                    rewrite Hin_ctx_aux in HC_a_in_ctx.
                    discriminate.
           *** destruct (Component.eqb C_b C') eqn:HC_b_eq_C'.
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
           destruct (Component.eqb C_a C') eqn:HC_a_eq_C'.
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
           destruct (Component.eqb C_b C') eqn:HC_b_eq_C'.
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

Lemma program_allocation_in_partialized_memory:
  forall (ctx: {fset Component.id}) mem1 mem2,
    filterm (fun k _ => k \notin ctx) mem1 =
    filterm (fun k _ => k \notin ctx) mem2 ->
  forall C size mem1' mem2' ptr1 ptr2,
    C \notin ctx ->
    Memory.alloc mem1 C size = Some (mem1', ptr1) ->
    Memory.alloc mem2 C size = Some (mem2', ptr2) ->
    ptr1 = ptr2 /\
    filterm (fun k _ => k \notin ctx) mem1' =
    filterm (fun k _ => k \notin ctx) mem2'.
Proof.
Admitted.

Lemma program_load_in_partialized_memory:
  forall (ctx: {fset Component.id}) mem1 mem2,
    filterm (fun k _ => k \notin ctx) mem1 =
    filterm (fun k _ => k \notin ctx) mem2 ->
  forall C b o v1 v2,
    C \notin ctx ->
    Memory.load mem1 (C, b, o) = Some v1 ->
    Memory.load mem2 (C, b, o) = Some v2 ->
    v1 = v2.
Proof.
Admitted.

Lemma program_store_in_partialized_memory:
  forall (ctx: {fset Component.id}) mem1 mem2,
    filterm (fun k _ => k \notin ctx) mem1 =
    filterm (fun k _ => k \notin ctx) mem2 ->
  forall C b o v mem1' mem2',
    C \notin ctx ->
    Memory.store mem1 (C, b, o) v = Some mem1' ->
    Memory.store mem2 (C, b, o) v = Some mem2' ->
    filterm (fun k _ => k \notin ctx) mem1' =
    filterm (fun k _ => k \notin ctx) mem2'.
Proof.
Admitted.

Lemma context_allocation_in_partialized_memory:
  forall (ctx: {fset Component.id}) mem C size mem' ptr,
    C \in ctx ->
    Memory.alloc mem C size = Some (mem', ptr) ->
    filterm (fun k _ => k \notin ctx) mem' =
    filterm (fun k _ => k \notin ctx) mem.
Proof.
Admitted.

Lemma context_store_in_partialized_memory:
  forall (ctx: {fset Component.id}) mem C b o v mem',
    C \in ctx ->
    Memory.store mem (C, b, o) v = Some mem' ->
    filterm (fun k _ => k \notin ctx) mem' =
    filterm (fun k _ => k \notin ctx) mem.
Proof.
Admitted.

Lemma state_determinism_program:
  forall p ctx G sps t sps',
    is_program_component sps ctx ->
    kstep p ctx G sps t sps' ->
  forall sps'',
    kstep p ctx G sps t sps'' ->
    sps' = sps''.
Proof.
Admitted.
(* XXX
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
      destruct (prepare_buffers_of_linked_programs Hlink1 H10 H) as [? Hb].
      rewrite <- Hiface2 in H.
      destruct (prepare_buffers_of_linked_programs Hlink2 H6 H) as [? Hb'].
      rewrite Hb in Hb'. inversion Hb'.
      subst.
      reflexivity.

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
      { destruct (prepare_buffers_of_linked_programs Hlink1 H12 H) as [? Hb].
        rewrite <- Hiface2 in H.
        destruct (prepare_buffers_of_linked_programs Hlink2 H18 H) as [? Hb'].
        rewrite Hb in Hb'. inversion Hb'.
        subst.
        reflexivity.
      }
      assert (b' = b'0).
      { destruct (prepare_buffers_of_linked_programs Hlink1 H14 H) as [? Hb].
        rewrite <- Hiface2 in H.
        destruct (prepare_buffers_of_linked_programs Hlink2 H20 H) as [? Hb'].
        rewrite Hb in Hb'. inversion Hb'.
        subst.
        reflexivity.
      }
      assert (P_expr = P_expr0). {
        destruct (find_procedure_in_linked_programs Hlink1 H9 H)
          as [HP_expr Hfind_proc].
        rewrite <- Hiface2 in H.
        destruct (find_procedure_in_linked_programs Hlink2 H17 H)
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
      { destruct (prepare_buffers_of_linked_programs Hlink1 H13 H) as [? Hb].
        rewrite <- Hiface2 in H.
        destruct (prepare_buffers_of_linked_programs Hlink2 H21 H) as [? Hb'].
        rewrite Hb in Hb'. inversion Hb'.
        subst.
        reflexivity.
      }
      assert (b' = b'0).
      { destruct (prepare_buffers_of_linked_programs Hlink1 H15 H12) as [? Hb].
        rewrite <- Hiface2 in H12.
        destruct (prepare_buffers_of_linked_programs Hlink2 H23 H12) as [? Hb'].
        rewrite Hb in Hb'. inversion Hb'.
        subst.
        reflexivity.
      }
      assert (P_expr = P_expr0). {
        destruct (find_procedure_in_linked_programs Hlink1 H10 H12)
          as [HP_expr Hfind_proc].
        rewrite <- Hiface2 in H12.
        destruct (find_procedure_in_linked_programs Hlink2 H20 H12)
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
      { destruct (prepare_buffers_of_linked_programs Hlink1 H13 H) as [? Hb].
        rewrite <- Hiface2 in H.
        destruct (prepare_buffers_of_linked_programs Hlink2 H21 H) as [? Hb'].
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
      { destruct (prepare_buffers_of_linked_programs Hlink1 H11 H) as [? Hb].
        rewrite <- Hiface2 in H.
        destruct (prepare_buffers_of_linked_programs Hlink2 H9 H) as [? Hb'].
        rewrite Hb in Hb'. inversion Hb'.
        subst.
        reflexivity.
      }
      subst.
      destruct (partial_stack_pop_by_program_to_program H H H8)
        as [Hold_call_arg [Hkont Hstack]].
      subst. rewrite Hstack.
      rewrite (program_store_in_partialized_memory H7 H13 H12 H10).
      reflexivity.

    (* internal *)
    + (* show stack and memory are changing in the same way *)
      assert (b = b0).
      { destruct (prepare_buffers_of_linked_programs Hlink1 H11 H15) as [? Hb].
        rewrite <- Hiface2 in H15.
        destruct (prepare_buffers_of_linked_programs Hlink2 H13 H15) as [? Hb'].
        rewrite Hb in Hb'. inversion Hb'.
        subst.
        reflexivity.
      }
      subst.
      destruct (partial_stack_pop_by_program_to_program H H15 H8)
        as [Hold_call_arg [Hkont Hstack]].
      subst. rewrite Hstack.
      rewrite (program_store_in_partialized_memory H7 H15 H12 H14).
      reflexivity.

    (* external *)
    + rewrite (context_store_in_partialized_memory H15 H12).
      rewrite (context_store_in_partialized_memory H15 H14).
      rewrite H7.
      apply Nat.neq_sym in H10.
      destruct (partial_stack_pop_by_program_to_context H10 H H15 H8)
        as [Hold_call_arg [Hkont Hstack]].
      reflexivity.

  (* context has control (contra) *)
  - PS.simplify_turn.
    match goal with
    | Hin: context[domm (prog_interface p1)],
      Hnotin: context[domm (prog_interface p1)] |- _ =>
      rewrite Hin in Hnotin; discriminate
    end.
Qed.
*)

Lemma context_epsilon_step_is_silent:
  forall p ctx G sps sps',
    is_context_component sps ctx ->
    kstep p ctx G sps E0 sps' ->
    sps = sps'.
Proof.
Admitted.
(* XXX
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
*)

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
(* XXX
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
        (* TODO *)
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
            pose proof (wfprog_well_formed_procedures_1 H1) as Hp1_wfprocs.
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
        (* TODO *)
        (* same stack *)
        admit.

    (* internal & external return *)
    + inversion Hkstep2; subst.
      inversion Hpartial_sps1'; subst;
      inversion Hpartial_sps2'; subst; PS.simplify_turn.
      * (* same memory *)
        (* TODO *)
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
        (* TODO *)
        (* same stack *)
        (*erewrite partial_stack_pop;
          try reflexivity;
          try eassumption.*)
        admit.
*)
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
