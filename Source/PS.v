Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.Maps.
Require Import Common.CompCertExtensions.
Require Import Common.Blame.
Require Import Common.Traces.
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

Definition s_stack (sps: state) : stack :=
  match sps with
  | PC (_, stk, _, _, _, _) => stk
  | CC (_, stk, _)          => stk
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
  (C, if C \in ctx then None else Some (v, k)).

(* FIXME: This can be expressed in terms of drop and find. *)
Fixpoint drop_while {T : Type} (a : pred T) (s : seq T) :=
  if s is x :: s' then
    if a x then drop_while a s' else s
  else [::].

Lemma eq_drop_while T (a1 a2 : T -> bool) :
  a1 =1 a2 -> drop_while a1 =1 drop_while a2.
Proof. by move=> e_a; elim=> [//|x s /= ->]; rewrite e_a. Qed.

(** FIXME: This function could probably be simplified if we replaced
    [last_frame] with the component of the last frame, and changed the
    definition of [to_partial_stack] so that it always put the last frame at the
    head of the list. *)

Fixpoint to_partial_stack_helper
         (ctx: {fset Component.id}) (s: CS.stack) last_frame
  : PS.stack :=
  match s with
  | [] => [:: to_partial_frame ctx last_frame]
  | CS.Frame C v k :: s' =>
    if (C \in ctx) && (C == CS.f_component last_frame) then
      to_partial_stack_helper ctx s' last_frame
    else
      to_partial_frame ctx last_frame ::
      to_partial_stack_helper ctx s' (CS.Frame C v k)
  end.

Lemma to_partial_stack_helperE ctx stk last_frame :
  to_partial_stack_helper ctx stk last_frame =
  to_partial_frame ctx last_frame ::
  match drop_while (fun '(CS.Frame C _ _) => (C \in ctx) && (C == CS.f_component last_frame)) stk with
  | [::] => [::]
  | last_frame' :: stk => to_partial_stack_helper ctx stk last_frame'
  end.
Proof.
elim: stk last_frame=> [|[C' v' k'] stk IH] //= [C v k] /=.
case: eqP=> [-> {C'}|_].
  by rewrite andbT IH /=; case: ifP=> //= ->.
by rewrite andbF.
Qed.

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
  match drop_while (fun '(CS.Frame C _ _) => (C \in ctx) && (C == Cincontrol)) s with
  | [] => []
  | last_frame :: s' =>
    to_partial_stack_helper ctx s' last_frame
  end.

(* XXX: This lemma seems more useful to reason about [to_partial_stack] *)

Lemma to_partial_stackE stk ctx C :
  to_partial_stack stk ctx C =
  let stk := if C \in ctx
             then drop_while (pred1 C \o CS.f_component) stk
             else stk in
  if stk is frame :: stk'
  then to_partial_frame ctx frame :: to_partial_stack stk' ctx (CS.f_component frame)
  else [::].
Proof.
case: stk=> [|[C' v k] stk] /=; first by rewrite if_same.
rewrite /to_partial_stack /=.
case: eqP => [-> {C'}|_]; last first.
  rewrite andbF to_partial_stack_helperE.
  by case: ifP=> [Cin|Cnin].
rewrite andbT; case: ifP=> [Cin|Cnin]; last by rewrite to_partial_stack_helperE.
rewrite (_ : drop_while _ _ = drop_while (pred1 C \o CS.f_component) stk); last first.
  apply/eq_drop_while; case=> [???] /=; rewrite andbC.
  by case: eqP=> // ->; rewrite Cin.
case: drop_while=> [|frame stk'] //.
by rewrite to_partial_stack_helperE.
Qed.

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

Lemma partial_stack_push_by_program ctx gps1 gps2 C :
  C \notin ctx ->
  to_partial_stack gps1 ctx C =
  to_partial_stack gps2 ctx C ->
  forall v k C',
    to_partial_stack (CS.Frame C v k :: gps1) ctx C' =
    to_partial_stack (CS.Frame C v k :: gps2) ctx C'.
Proof.
move=> in_prog e_stk v k C'.
rewrite to_partial_stackE [RHS]to_partial_stackE /=.
case: eqP => [<- {C'}|ne]; last by rewrite !if_same e_stk.
by rewrite (negbTE in_prog) /= (negbTE in_prog) e_stk.
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
move=> C C' v k stk ctx in_prog.
rewrite to_partial_stackE /=; case: eqP in_prog=> [-> {C'}|ne] in_prog.
  by rewrite in_prog /= in_prog; eauto.
by rewrite if_same /= in_prog; eauto.
Qed.

Lemma partial_stack_outside_control_preserves_top :
  forall C C' v k s ctx,
    C <> C' ->
  exists frame rest,
    to_partial_stack (CS.Frame C' v k :: s) ctx C = (C', frame) :: rest.
Proof.
move=> C C' v k s ctx /eqP ne.
by rewrite to_partial_stackE /= eq_sym (negbTE ne) if_same /=; eauto.
Qed.

Lemma partial_stacks_unequal_top_internal :
  forall C1 C2 v1 v2 k1 k2 s1 s2 ctx,
    C1 \notin ctx ->
    C1 <> C2 ->
    to_partial_stack (CS.Frame C1 v1 k1 :: s1) ctx C1 <>
    to_partial_stack (CS.Frame C2 v2 k2 :: s2) ctx C1.
Proof.
move=> C1 C2 v1 v2 k1 k2 s1 s2 ctx in_prog H contra; apply: H.
move: contra; rewrite to_partial_stackE (to_partial_stackE (_ :: s2)).
by rewrite (negbTE in_prog) /= (negbTE in_prog); case.
Qed.

Lemma partial_stacks_unequal_top_external :
  forall C C1 C2 v1 v2 k1 k2 s1 s2 ctx,
    C1 \notin ctx ->
    C2 \in ctx ->
    C <> C2 ->
    to_partial_stack (CS.Frame C1 v1 k1 :: s1) ctx C <>
    to_partial_stack (CS.Frame C2 v2 k2 :: s2) ctx C.
Proof.
move=> C C1 C2 v1 v2 k1 k2 s1 s2 ctx in_prog in_ctx H contra; apply: H.
move: contra; rewrite to_partial_stackE (to_partial_stackE (_ :: s2)) /=.
case: (C1 =P C) in_prog => [-> {C1}|ne1] in_prog.
  by rewrite (negbTE in_prog) /=; case.
case: (C2 =P C) in_ctx  => [-> {C2} //|ne2] in_ctx.
by rewrite !if_same /= (negbTE in_prog) in_ctx.
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
move=> ctx C C' v1 k1 v2 k2 gps1 gps2 /eqP ne in_ctx.
by rewrite !(to_partial_stackE (_ :: _)) /= (negbTE ne) !if_same /= in_ctx => ->.
Qed.

Lemma partial_stack_pop_to_program:
  forall ctx C C' old_call_arg1 k1 old_call_arg2 k2 gps1 gps2,
    C' \notin ctx ->
    to_partial_stack (CS.Frame C' old_call_arg1 k1 :: gps1) ctx C =
    to_partial_stack (CS.Frame C' old_call_arg2 k2 :: gps2) ctx C ->
    old_call_arg1 = old_call_arg2 /\ k1 = k2 /\
    to_partial_stack gps1 ctx C' = to_partial_stack gps2 ctx C'.
Proof.
move=> ????????? in_prog.
rewrite !(to_partial_stackE (_ :: _)) /=.
case: eqP in_prog=> [->|ne] in_prog.
  by rewrite (negbTE in_prog) /= (negbTE in_prog); case=> -> -> ->.
by rewrite !if_same /= (negbTE in_prog); case=> -> -> ->.
Qed.

Lemma partial_stack_pop_to_context:
  forall ctx C C' v1 k1 v2 k2 gps1 gps2,
    C <> C' ->
    C' \in ctx ->
    to_partial_stack (CS.Frame C' v1 k1 :: gps1) ctx C =
    to_partial_stack (CS.Frame C' v2 k2 :: gps2) ctx C ->
    to_partial_stack gps1 ctx C' = to_partial_stack gps2 ctx C'.
Proof.
move=> ????????? /eqP ne in_ctx; rewrite !(to_partial_stackE (_ :: _)) /=.
by rewrite eq_sym (negbTE ne) !if_same /= in_ctx; case.
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

Ltac parallel_concrete_easy :=
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

Lemma parallel_concrete p ctx p1 p2 scs1 t scs1' scs2 :
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
case: scs1 t scs1' / step in_prog e_part => /=; try parallel_concrete_easy.
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
  move=> C stk1 mem1 k v arg _ old <- in_prog.
  rewrite (negbTE in_prog) (lock CS.eval_kstep) (lock filterm).
  case: scs2=> [C' stk2 mem2 k' e' arg'] /=.
  case: ifP=> // _ []; rewrite -(lock filterm).
  move=> {C' k' e' arg'} <- e_stk e_mem <- <- <-.
  move: e_stk; rewrite to_partial_stackE (negbTE in_prog) /= (negbTE in_prog).
  rewrite (to_partial_stackE stk2) (negbTE in_prog) /=.
  case: stk2=> [//|[_ v' k'] stk2] /= [<-]; rewrite (negbTE in_prog).
  by case=> <- <- e_stk; rewrite -lock /= eqxx (negbTE in_prog) e_stk e_mem.
- (* External return *)
  move=> C stk1 mem1 k v arg C' old ne in_prog.
  rewrite (negbTE in_prog) (lock CS.eval_kstep) (lock filterm).
  case: scs2=> [C'' stk2 mem2 k' e' arg'] /=.
  case: ifP=> // _ []; rewrite -(lock filterm).
  move=> {C'' k' e' arg'} <- e_stk e_mem <- <- <-.
  case: ifPn=> [in_ctx|in_prog'].
  + (* Return to context *)
    move: ne e_stk=> /eqP ne.
    rewrite to_partial_stackE (negbTE in_prog) /= in_ctx.
    rewrite [to_partial_stack stk2 _ _]to_partial_stackE (negbTE in_prog) /=.
    case: stk2=> [|[C2 v2 k2] stk2] //= [<- {C2} _ e_stk].
    by rewrite -lock /= in_ctx (negbTE ne) e_stk e_mem.
  + (* Return to program *)
    move: e_stk.
    rewrite to_partial_stackE (negbTE in_prog) /= (negbTE in_prog').
    rewrite (to_partial_stackE stk2) (negbTE in_prog) /=.
    case: stk2=> [|[_ old2 k2] stk2] //= [<-]; rewrite (negbTE in_prog').
    case=> <- <- {old2 k2} e_stk.
    rewrite -lock /=; move/eqP/negbTE: ne=> ->.
    by rewrite (negbTE in_prog') e_stk e_mem.
Qed.

Lemma parallel_concrete' p ctx p1 p2 scs1 t1 scs1' scs2 t2 scs2' :
  well_formed_program p ->
  well_formed_program p1 ->
  well_formed_program p2 ->
  linkable (prog_interface p) ctx ->
  closed_interface (unionm (prog_interface p) ctx) ->
  prog_interface p1 = ctx ->
  prog_interface p2 = ctx ->
  partialize ctx scs1 = partialize ctx scs2 ->
  CS.s_component scs1 \notin domm ctx ->
  CS.kstep (prepare_global_env (program_link p p1)) scs1 t1 scs1' ->
  CS.kstep (prepare_global_env (program_link p p2)) scs2 t2 scs2' ->
  t1 = t2 /\ partialize ctx scs1' = partialize ctx scs2'.
Proof.
move=> wf wf1 wf2 link clos int1 int2 part in_prog1 step1 /CS.eval_kstep_complete step2.
have := parallel_concrete wf wf1 wf2 link clos int1 int2 part in_prog1 step1.
case=> scs2'' /CS.eval_kstep_complete step2' ->; split; congruence.
Qed.

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

(* FIXME: The global environment is not serving any purpose right now. *)
Inductive kstep
          (p: program) (ctx: Program.interface) (G : global_env)
          (sps : state) (t : trace) (sps' : state) : Prop :=
| partial_step:
    forall p' scs scs',
      prog_interface p' = ctx ->
      well_formed_program p ->
      well_formed_program p' ->
      linkable (prog_interface p) (prog_interface p') ->
      closed_program (program_link p p') ->
      CS.kstep (prepare_global_env (program_link p p')) scs t scs' ->
      partial_state ctx scs sps ->
      partial_state ctx scs' sps' ->
      kstep p ctx G sps t sps'.

Lemma backward p c G scs sps t sps' :
  well_formed_program p ->
  well_formed_program c ->
  linkable (prog_interface p) (prog_interface c) ->
  closed_interface (unionm (prog_interface p) (prog_interface c)) ->
  is_program_component sps (prog_interface c) ->
  kstep p (prog_interface c) G sps t sps' ->
  partialize (prog_interface c) scs = sps ->
  exists2 scs',
    CS.kstep (prepare_global_env (program_link p c)) scs t scs' &
    partialize (prog_interface c) scs' = sps'.
Proof.
rewrite /is_program_component /is_context_component /=.
move=> wfp wfc link clos in_prog step e_sps.
case: step e_sps in_prog => c2 scs2 scs2' e_int _ wfc2 _ _ /= step2.
move=> /partialize_correct <- /partialize_correct <- e_sps.
rewrite s_component_partialize => in_prog.
have [scs' step ->] := parallel_concrete wfp wfc2 wfc link clos e_int erefl (esym e_sps) in_prog step2.
by eauto.
Qed.

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

  Local Open Scope fset_scope.

  Definition stack_components (ps : state) :=
    s_component ps |: fset [seq f.1 | f <- s_stack ps].

  Lemma stack_components_partialize scs :
    stack_components (partialize ctx scs) = CS.stack_components scs.
  Proof.
  rewrite /stack_components /CS.stack_components.
  case: scs=> C stk mem k e arg; do 2![rewrite fun_if /= if_same].
  elim: stk C {mem k e arg} => [//|[C' v k] stk IH] C /=.
  rewrite to_partial_stackE /=; case: eqP=> [-> {C'}|_]; last first.
    by rewrite if_same /= 2!fset_cons IH.
  case: ifP=> [Cin|] /=; last by rewrite 2!fset_cons IH.
  by rewrite fset_cons fsetUA fsetUid -IH // to_partial_stackE Cin.
  Qed.

  Lemma stack_components_step ps t ps' :
    Step sem ps t ps' ->
    fsubset (stack_components ps) (domm (unionm (prog_interface p) ctx)) ->
    fsubset (stack_components ps') (domm (unionm (prog_interface p) ctx)).
  Proof.
  case=> p' cs cs' e_ctx wf wf' link clos step.
  do 2![move=> /partialize_correct <-]; rewrite !stack_components_partialize.
  by rewrite -e_ctx; apply: CS.stack_components_step step.
  Qed.

  Lemma stack_components_star ps t ps' :
    initial_state p ctx ps ->
    Star sem ps t ps' ->
    fsubset (stack_components ps') (domm (unionm (prog_interface p) ctx)).
  Proof.
  move=> init star.
  set S := domm (unionm (prog_interface p) ctx).
  have {init} ps_ok : fsubset (stack_components ps) S.
    case: ps / init {star}=> p' cs ps e_p' wf wf' link clos.
    move=> /partialize_correct <- ->; rewrite stack_components_partialize.
    rewrite /S -e_p'.
    have {wf wf'} wf : well_formed_program (program_link p p').
      exact: linking_well_formedness.
    apply: (CS.stack_components_star wf clos)=> //.
    exact: star_refl.
  elim: ps t ps' / star ps_ok=> // ps1 t1 ps2 t2 ps3 _ step _ IH _ ps1_ok.
  by apply: IH; apply: stack_components_step ps1_ok; eauto.
  Qed.

  Lemma undef_in_program s1 t s2 :
    initial_state p ctx s1 ->
    Star sem s1 t s2 ->
    undef_in t (prog_interface p) = is_program_component s2 ctx.
  Proof.
  move=> Hinitial Hstar.
  rewrite /undef_in /last_comp /is_program_component /is_context_component.
  rewrite /turn_of /= (star_component Hstar).
  have -> : Component.main = s_component s1.
    case: s1 / Hinitial {Hstar} => ???????? Hpart.
    rewrite (partial_state_component Hpart) => ->.
    by rewrite /CS.initial_machine_state; case: prog_main.
  rewrite -(star_component Hstar).
  move: (stack_components_star Hinitial Hstar).
  rewrite /stack_components fsubU1set; case/andP.
  rewrite domm_union; case/fsetUP.
    move=> in_p; rewrite in_p.
    by rewrite (fdisjointP _ _ disjoint_interfaces).
  move=> in_ctx; rewrite in_ctx => _; apply/negbTE.
  move: disjoint_interfaces; rewrite fdisjointC.
  by move/fdisjointP; apply.
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
  unfold partialize, prepare_buffers, prog_buffers in Hpartial1.
  unfold partialize, prepare_buffers, prog_buffers in Hpartial2.
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
case: step1 in_prog
      => {sps sps'} p1 scs1 scs1' int1 wf wf1 link /cprog_closed_interface clos
         kstep1 /partialize_correct <- /partialize_correct <- in_prog sps''.
case=> {sps''} p2 scs2 scs2' int2 _  wf2 _ _ kstep2
       /partialize_correct e12 /partialize_correct <-.
have {in_prog} in_prog : CS.s_component scs1 \notin domm ctx.
  move: in_prog; simplify_turn.
  case: (scs1)=> [C ? ? ? ? ?] /=.
  by case: ifPn => /= [-> //|].
rewrite /= int1 in link clos.
move/CS.eval_kstep_complete in kstep2.
case: (parallel_concrete wf wf1 wf2 link clos int1 int2 (esym e12) in_prog kstep1).
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

Lemma context_epsilon_step_is_silent' p ctx scs scs' :
  well_formed_program p ->
  well_formed_program ctx ->
  linkable (prog_interface p) (prog_interface ctx) ->
  closed_program (program_link p ctx) ->
  CS.s_component scs \in domm (prog_interface ctx) ->
  Step (CS.sem (program_link p ctx)) scs E0 scs' ->
  partialize (prog_interface ctx) scs = partialize (prog_interface ctx) scs'.
Proof.
move=> wf wf_ctx link clos in_ctx step.
pose G := mkGlobalEnv emptym emptym.
have {step} :
  kstep p (prog_interface ctx) G (partialize (prog_interface ctx) scs) E0 (partialize (prog_interface ctx) scs').
  by apply: partial_step; eauto; apply/partialize_correct.
apply: context_epsilon_step_is_silent=> /=.
by rewrite /is_context_component /= s_component_partialize.
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

Lemma context_epsilon_star_is_silent' p ctx scs scs':
  well_formed_program p ->
  well_formed_program ctx ->
  linkable (prog_interface p) (prog_interface ctx) ->
  closed_program (program_link p ctx) ->
  CS.s_component scs \in domm (prog_interface ctx) ->
  Star (CS.sem (program_link p ctx)) scs E0 scs' ->
  partialize (prog_interface ctx) scs = partialize (prog_interface ctx) scs'.
Proof.
move=> wf wf_ctx link clos in_ctx star.
elim/star_E0_ind: scs scs' / star in_ctx=> // scs scs' scs'' step IH in_ctx.
have e := context_epsilon_step_is_silent' wf wf_ctx link clos in_ctx step.
rewrite e; apply: IH.
by rewrite -(s_component_partialize (prog_interface ctx)) -e s_component_partialize.
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

Lemma state_determinism' p ctx p1 p2 scs1 t scs1' scs2 scs2' :
  well_formed_program p ->
  well_formed_program p1 ->
  well_formed_program p2 ->
  linkable (prog_interface p) ctx ->
  closed_program (program_link p p1) ->
  closed_program (program_link p p2) ->
  prog_interface p1 = ctx ->
  prog_interface p2 = ctx ->
  partialize ctx scs1 = partialize ctx scs2 ->
  CS.kstep (prepare_global_env (program_link p p1)) scs1 t scs1' ->
  CS.kstep (prepare_global_env (program_link p p2)) scs2 t scs2' ->
  partialize ctx scs1' = partialize ctx scs2'.
Proof.
move=> wf wf1 wf2 link clos1 clos2 int1 int2 part step1 step2.
pose G := {| genv_interface := emptym; genv_procedures := emptym |}.
have {step1 clos1 int1} step1 : kstep p ctx G (partialize ctx scs1) t (partialize ctx scs1').
  move=> {wf2 int2 step2}; apply: partial_step; eauto; try congruence;
  exact/partialize_correct.
have {step2 clos2 int2} step2 : kstep p ctx G (partialize ctx scs1) t (partialize ctx scs2').
  move=> {wf1}; apply: partial_step; eauto; try congruence;
  exact/partialize_correct.
by apply: state_determinism step2.
Qed.

(* FIXME: Rename this *)
Lemma parallel_exec1 p ctx p1 p2 scs1 scs1' scs2 scs2' t t1 t2 :
  well_formed_program p ->
  well_formed_program p1 ->
  well_formed_program p2 ->
  linkable (prog_interface p) ctx ->
  closed_program (program_link p p1) ->
  closed_program (program_link p p2) ->
  prog_interface p1 = ctx ->
  prog_interface p2 = ctx ->
  partialize ctx scs1 = partialize ctx scs2 ->
  Star (CS.sem (program_link p p1)) scs1 (t ** t1) scs1' ->
  Star (CS.sem (program_link p p2)) scs2 (t ** t2) scs2' ->
  exists scs1'' scs2'',
    [/\ Star (CS.sem (program_link p p1)) scs1 t scs1'',
        Star (CS.sem (program_link p p2)) scs2 t scs2'',
        Star (CS.sem (program_link p p1)) scs1'' t1 scs1',
        Star (CS.sem (program_link p p2)) scs2'' t2 scs2' &
        partialize ctx scs1'' = partialize ctx scs2''].
Proof.
move=> wf wf1 wf2 link clos1 clos2 int1 int2.
elim: t scs1 scs2=> /= [|e t IH] scs1 scs2.
  move=> part star1 star2; exists scs1, scs2; split=> //;
  exact: star_refl.
move=> part.
case/(star_cons_inv (@CS.singleton_traces _))=> scs1a [scs1b [star1a [step1b star1c]]].
case/(star_cons_inv (@CS.singleton_traces _))=> scs2a [scs2b [star2a [step2b star2c]]].
have clos: closed_interface (unionm (prog_interface p) ctx).
  rewrite -int1; apply: cprog_closed_interface clos1.
suffices: partialize ctx scs1a = partialize ctx scs2a.
  move=> {part} part.
  have {part} part: partialize ctx scs1b = partialize ctx scs2b.
    exact: state_determinism' step1b step2b.
  case/(_ _ _ part): IH=> // {part} [scs1c [scs2c [star1c' star2c' star1d star2d part]]].
  exists scs1c, scs2c; split=> //.
    apply: (star_trans star1a)=> //=.
    exact: (star_step _ _ step1b star1c').
  apply: (star_trans star2a)=> //=.
  exact: (star_step _ _ step2b star2c').
have [in_ctx1|in_prog1] := boolP (CS.s_component scs1 \in domm ctx).
  have e_1a : partialize ctx scs1 = partialize ctx scs1a.
    move: wf wf1 link clos1 in_ctx1 star1a; rewrite -int1.
    exact: context_epsilon_star_is_silent'.
  have e_2a : partialize ctx scs2 = partialize ctx scs2a.
    move: wf wf2 link clos2 in_ctx1 star2a.
    rewrite -(s_component_partialize ctx scs1) part s_component_partialize -int2.
    exact: context_epsilon_star_is_silent'.
  by rewrite e_1a e_2a in part.
elim/star_E0_ind: scs1 scs1a / star1a scs2 star2a part step1b in_prog1.
  move=> scs1a scs2 star2a part step1a in_prog1.
  elim/star_E0_ind: scs2 scs2a / star2a part step2b=> //.
  move=> scs2 scs2a scs2a' step2a _ part _.
  by case: (parallel_concrete' wf wf1 wf2 link clos int1 int2 part in_prog1 step1a step2a).
move=> {IH} scs1 scs1a scs1a' step1a IH scs2 star2a part step1a' in_prog1.
case: (parallel_concrete wf wf1 wf2 link clos int1 int2 part in_prog1 step1a).
move=> scs2a' step2a' part'.
have star2a' : Star (CS.sem (program_link p p2)) scs2a' E0 scs2a.
  elim/star_E0_ind': scs2 scs2a / star2a step2b {IH part} step2a'.
    move=> ? /CS.eval_kstep_correct H.
    by move/CS.eval_kstep_correct; rewrite H.
  move=> scs2aa scs2ab scs2ac step2aa star2ab _ step2ac.
  move/CS.eval_kstep_correct.
  by move/CS.eval_kstep_correct: step2aa => -> [<-].
have {in_prog1} in_prog1 : CS.s_component scs1a \notin domm ctx.
  by rewrite (CS.kstep_component step1a).
by apply: IH star2a' part' step1a' in_prog1.
Qed.

(* FIXME: This is not being used right now *)
Lemma parallel_exec p ctx p1 p2 scs1 scs1' scs2 scs2' t t' :
  well_formed_program p ->
  well_formed_program p1 ->
  well_formed_program p2 ->
  linkable (prog_interface p) ctx ->
  closed_program (program_link p p1) ->
  closed_program (program_link p p2) ->
  prog_interface p1 = ctx ->
  prog_interface p2 = ctx ->
  partialize ctx scs1 = partialize ctx scs2 ->
  Star (CS.sem (program_link p p1)) scs1 (t ** t') scs1' ->
  Star (CS.sem (program_link p p2)) scs2 (t      ) scs2' ->
  Nostep (CS.sem (program_link p p2)) scs2' ->
  CS.final_state scs1' ->
  CS.s_component scs2' \notin domm ctx ->
  CS.final_state scs2'.
Proof.
rewrite -[t in Star _ _ t scs2']E0_right.
move=> wf wf1 wf2 link clos1 clos2 int1 int2 part star1 star2.
have := parallel_exec1 wf wf1 wf2 link clos1 clos2 int1 int2 part star1 star2.
case=> {t scs1 scs2 star1 star2 part} [scs1 [scs2 [_ _ star1 star2 part]]].
rewrite (CS.star_component star2) /=.
elim: scs1 t' scs1' / star1 scs2 part star2.
  move=> scs1 scs2 part star2 nostep2 final1 in_prog.
  have final2 : CS.final_state scs2.
    case: scs1 scs2 in_prog part final1 {star2}
          => [C1 stk1 mem1 k1 e1 arg1] [C2 stk2 mem2 k2 e2 arg2] /=.
    move=> in_prog; rewrite (negbTE in_prog).
    case: ifP=> // _ [-> {C1} e_stk _ -> -> _] H.
    case: H e_stk => [-> //|[v [-> [-> ->]]]] /=; auto.
    do 2![rewrite to_partial_stackE (negbTE in_prog) /=].
    by case: stk2=> //; right; eauto.
  elim/star_E0_ind: scs2 scs2' / star2 final2 {part nostep2 in_prog}=> //.
  move=> scs2 scs2' scs2'' step2 _ final2.
  by case/(CS.final_state_stuck final2): step2.
move=> scs1 t1 scs1' t2 scs1'' _ step1 _ IH _.
move=> scs2 part star2 nostep2 final1 in_prog2.
have clos : closed_interface (unionm (prog_interface p) ctx).
  by rewrite -int1; apply: cprog_closed_interface clos1.
have in_prog1 : CS.s_component scs1 \notin domm ctx.
  by rewrite -(s_component_partialize ctx scs1) part s_component_partialize.
case: (parallel_concrete wf wf1 wf2 link clos int1 int2 part in_prog1 step1).
elim/star_E0_ind': scs2 scs2' / star2 {part} nostep2 in_prog2 IH.
  by move=> scs2 nostep2 _ _ scs2' /nostep2.
move=> scs2 scs21' scs2'' step21 star2 _ nostep2 in_prog2 IH scs22'.
have {in_prog2} in_prog2 : CS.s_component scs21' \notin domm ctx.
  by rewrite (CS.kstep_component step21).
move/CS.eval_kstep_correct; move/CS.eval_kstep_correct: step21 => -> [_ <-] {scs22'}.
move=> part'.
exact: IH part' star2 nostep2 final1 in_prog2.
Qed.

(* This is a new version of parallel_exec that we need in the new
   proof of blame_program *)
Lemma parallel_exec' p ctx p1 p2 scs1 scs1' scs2 scs2' t t' e :
  well_formed_program p ->
  well_formed_program p1 ->
  well_formed_program p2 ->
  linkable (prog_interface p) ctx ->
  closed_program (program_link p p1) ->
  closed_program (program_link p p2) ->
  prog_interface p1 = ctx ->
  prog_interface p2 = ctx ->
  partialize ctx scs1 = partialize ctx scs2 ->
  Star (CS.sem (program_link p p1)) scs1 (t ** e :: t') scs1' ->
  Star (CS.sem (program_link p p2)) scs2 (t           ) scs2' ->
  Nostep (CS.sem (program_link p p2)) scs2' ->
  CS.s_component scs2' \in domm ctx.
Proof.
rewrite -[t in Star _ _ t scs2']E0_right.
move=> wf wf1 wf2 link clos1 clos2 int1 int2 part star1 star2.
have clos : closed_interface (unionm (prog_interface p) ctx).
  by rewrite -int1; apply: cprog_closed_interface clos1.
have := parallel_exec1 wf wf1 wf2 link clos1 clos2 int1 int2 part star1 star2.
case=> {t scs1 scs2 star1 star2 part} [scs1 [scs2 [_ _ star1 star2 part]]] nostep2.
rewrite (CS.star_component star2) /=.
have [//|in_prog2] := boolP (_ \in _).
case/(star_cons_inv (@CS.singleton_traces _)): star1=> scs1a [scs1b [star1a [step1b _]]].
elim/star_E0_ind': scs2 scs2' / star2 scs1 star1a part nostep2 in_prog2.
  move=> scs2 scs1 star1a.
  have [t [scs1a' step1]]: exists t scs1a', Step (CS.sem (program_link p p1)) scs1 t scs1a'.
    elim/star_E0_ind': scs1 scs1a / star1a step1b; by eauto.
  move=> part nostep2 in_prog2.
  rewrite -(s_component_partialize ctx) -part s_component_partialize in in_prog2.
  have := parallel_concrete wf wf1 wf2 link clos int1 int2 part in_prog2 step1.
  by case=> scs2' /nostep2.
move=> scs2 scs2' scs2'' step2 star2 IH scs1 star1 part nostep2 in_prog2.
elim/star_E0_ind': scs1 scs1a / star1 step1b IH part.
  move=> scs1 step1b _ part.
  rewrite -(s_component_partialize ctx) -part s_component_partialize in in_prog2.
  by have [] := parallel_concrete' wf wf1 wf2 link clos int1 int2 part in_prog2 step1b step2.
move=> scs1 scs1a scs1a' step1a star1 _ step1b IH part.
move: (in_prog2); rewrite -(s_component_partialize ctx) -part s_component_partialize => in_prog1.
have {part} [_ part] :=
  parallel_concrete' wf wf1 wf2 link clos int1 int2 part in_prog1 step1a step2.
move: (CS.kstep_component step2) in_prog2=> /= <-.
exact: IH star1 part nostep2.
Qed.

(* Placement note: right now, there are similar lemmas to this one here in PS,
  as opposed to none in CS, where it would more logically belong. *)
Lemma blame_last_comp_star p c scs1 t scs2:
  CS.initial_state (program_link p c) scs1 ->
  Star (CS.sem (program_link p c)) scs1 t scs2 ->
  CS.s_component scs2 \in domm (prog_interface c) ->
  last_comp t \in domm (prog_interface c).
Proof.
move=> -> star.
rewrite (CS.star_component star) /CS.initial_machine_state.
by case: prog_main.
Qed.

Lemma partialize_partition p p1 p2 scs1 scs2 :
  well_formed_program p ->
  well_formed_program p1 ->
  well_formed_program p2 ->
  prog_interface p1 = prog_interface p2 ->
  linkable (prog_interface p) (prog_interface p1) ->
  closed_program (program_link p p1) ->
  closed_program (program_link p p2) ->
  CS.initial_state (program_link p p1) scs1 ->
  CS.initial_state (program_link p p2) scs2 ->
  partialize (prog_interface p1) scs1 =
  partialize (prog_interface p1) scs2.
Proof.
move: scs1 scs2=> _ _ wf wf1 wf2 e_int link clos1 clos2 -> ->.
rewrite /CS.initial_machine_state.
case e1: (prog_main (program_link p p1)) (cprog_main_existence clos1) => [main1|] //= _.
case e2: (prog_main (program_link p p2)) (cprog_main_existence clos2) => [main2|] //= _.
rewrite (_ : filterm _ _ = filterm (fun k _ => k \notin domm (prog_interface p1))
                                   (prepare_buffers (program_link p p2))); last first.
  apply/eq_fmap=> C; rewrite/prepare_buffers /= !filtermE !mapmE !unionmE.
  case p_b: (prog_buffers p C)=> [buf|] //=.
  have : prog_buffers p1 C = prog_buffers p2 C :> bool.
    by rewrite -!mem_domm -2?wfprog_defined_buffers // e_int.
  case e: (prog_buffers p1 C) (prog_buffers p2 C)=> [buf1|] [buf2|] //= _.
  by rewrite wfprog_defined_buffers // mem_domm e.
case: ifP=> [//|nin]; congr PC; repeat congr pair.
move: e1 e2.
rewrite /prog_main 2?[program_link p _]link_sym -1?e_int //.
move: nin (nin); rewrite {2}e_int ?wfprog_defined_procedures // => nin1 nin2.
move/find_procedure_unionm_r/(_ nin1)=> e1.
move/find_procedure_unionm_r/(_ nin2).
by rewrite e1; case.
Qed.

Lemma does_prefix_star : forall X m
  (Hprefix : does_prefix X m)
  (Hnot_wrong' : not_wrong_finpref m),
  exists (si : Smallstep.state X) (sf : Smallstep.state X),
    Smallstep.initial_state X si /\
    Star X si (finpref_trace m) sf  /\
    ((exists t, m = FTerminates t) -> Smallstep.final_state X sf).
Proof.
  intros X m Hprefix Hnot_wrong'.
  destruct Hprefix as [b [Hb Hmb]]. inversion Hb; subst. inversion H0; subst.
  destruct m as [t'| t' |t']; simpl; simpl in Hmb; subst; try easy. eauto.
  Focus 5. {
    destruct m as [t | t | t];
      try contradiction.
    destruct t as [| e t].
    - simpl in *. (* Dead end. *) admit.
    - admit.
  }
Admitted.


(* RB: TODO: Source prefixes no longer needed: clean proof. *)
Lemma blame_program:
  forall
    p Cs t' P' m
    (well_formed_p : well_formed_program p)
    (well_formed_Cs : well_formed_program Cs)
    (Hlinkable_p_Cs : linkable (prog_interface p) (prog_interface Cs))
    (Hclosed_p_Cs : Source.closed_program (Source.program_link p Cs))
    (HpCs_beh : program_behaves (CS.sem (program_link p Cs)) (Goes_wrong t'))
    (well_formed_P' : well_formed_program P')
    (Hsame_iface1 : prog_interface P' = prog_interface p)
    (HP'Cs_closed : Source.closed_program (Source.program_link P' Cs))
    (HP'_Cs_beh_new : does_prefix (CS.sem (program_link P' Cs)) m)
    (Hnot_wrong' : not_wrong_finpref m)
    (K : trace_finpref_prefix t' m),
    (prefix m (Goes_wrong t') \/ undef_in t' (Source.prog_interface p)).
Proof.
  intros p Cs t' P' m well_formed_p well_formed_Cs Hlinkable_p_Cs Hclosed_p_Cs
         HpCs_beh well_formed_P' Hsame_iface1 HP'Cs_closed
         HP'_Cs_beh_new Hnot_wrong' K.

  apply does_prefix_star in HP'_Cs_beh_new; [| easy].
  destruct HP'_Cs_beh_new as [sini1 [sfin1 [Hini1 [HStar1 Hfinal1']]]].

  inversion HpCs_beh as [sini2 ? Hini2 Hstbeh2 | Hnot_initial2]; subst;
    last (destruct (CS.initial_state_exists (Source.program_link p Cs)) as [wit Hf];
          specialize (Hnot_initial2 wit);
          contradiction).
  inversion Hstbeh2 as [| | | ? sfin2 HStar2 HNostep2 Hnot_final2]; subst.
  rewrite
    (Source.closed_program_link_sym well_formed_p well_formed_Cs Hlinkable_p_Cs)
    in Hclosed_p_Cs.
  assert (Hlinkable_P'_Cs := Hlinkable_p_Cs).
  rewrite <- Hsame_iface1 in Hlinkable_P'_Cs.
  rewrite
    (Source.closed_program_link_sym well_formed_P' well_formed_Cs Hlinkable_P'_Cs)
    in HP'Cs_closed.
  assert (Hpartialize :
            partialize (prog_interface p) sini1 = partialize (prog_interface p) sini2).
  {
    pose proof partialize_partition.
    rewrite (Source.link_sym well_formed_P' well_formed_Cs Hlinkable_P'_Cs)
      in Hini1.
    rewrite (Source.link_sym well_formed_p well_formed_Cs Hlinkable_p_Cs)
      in Hini2.
    pose proof PS.partialize_partition
         well_formed_Cs well_formed_P' well_formed_p
         Hsame_iface1 (linkable_sym Hlinkable_P'_Cs) HP'Cs_closed Hclosed_p_Cs
         Hini1 Hini2.
    congruence.
  }
  rewrite (Source.link_sym well_formed_P' well_formed_Cs Hlinkable_P'_Cs)
    in HStar1 (* HNostep1 Hfinal1*).
  rewrite (Source.link_sym well_formed_p well_formed_Cs Hlinkable_p_Cs)
    in HStar2 HNostep2.
  (* Case analysis on m. FGoes_wrong can be ruled out by contradiction,
     but also solved exactly like the others. *)
  assert (Hrefl : prog_interface p = prog_interface p) by reflexivity.
  (* destruct (classic (t' = m)). *)
  destruct m as [tm | tm | tm];
    (destruct K as [tm' Htm']; subst tm;
     unfold finpref_trace in HStar1).
  - simpl. right.
    assert(Hfinal1 : Smallstep.final_state (CS.sem (program_link P' Cs)) sfin1).
      apply Hfinal1'. eauto.

    (* RB: TODO: Lemma relating final_state and Nostep.
       Also simplify all the annoying rewriting that follows. *)
    assert (HNostep1 : Nostep (CS.sem (Source.program_link P' Cs)) sfin1).
    {
      simpl in Hfinal1. simpl.
      intros tcon scon Hcontra.
      CS.unfold_state sfin1.
      destruct Hfinal1 as [Hexit | [val [Hexpr [Hcont Hstack]]]]; subst;
        inversion Hcontra.
    }

    rewrite (Source.link_sym well_formed_P' well_formed_Cs Hlinkable_P'_Cs)
      in HNostep1 Hfinal1.

     pose proof PS.parallel_exec
       well_formed_Cs well_formed_P' well_formed_p
       (linkable_sym Hlinkable_p_Cs)
       HP'Cs_closed Hclosed_p_Cs
       Hsame_iface1 Hrefl
       Hpartialize
       HStar1 HStar2 HNostep2 Hfinal1
       as Hparallel;
     case: (boolP (CS.s_component sfin2 \in domm (Source.prog_interface p)))=> [Hparallel1|/Hparallel Hparallel2];
       [ rewrite (Source.link_sym well_formed_p well_formed_Cs Hlinkable_p_Cs)
           in Hini2;
         exact (PS.blame_last_comp_star Hini2 HStar2 Hparallel1)
       | easy ].
  - simpl in Hnot_wrong'. tauto.
  - simpl. destruct tm'.
    + left. exists (Goes_wrong []). simpl. repeat rewrite E0_right. reflexivity.
    + right.
     pose proof PS.parallel_exec'
       well_formed_Cs well_formed_P' well_formed_p
       (linkable_sym Hlinkable_p_Cs)
       HP'Cs_closed Hclosed_p_Cs
       Hsame_iface1 Hrefl
       Hpartialize
       HStar1 HStar2 HNostep2
       as Hparallel. unfold undef_in.
       rewrite (Source.link_sym well_formed_p well_formed_Cs Hlinkable_p_Cs) in Hini2;
       eapply PS.blame_last_comp_star; try eassumption. exact Hini2.
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
