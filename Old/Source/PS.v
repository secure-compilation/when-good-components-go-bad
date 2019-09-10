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
Require Import Source.PS.
Require Import Lib.Extra.

Require Import Coq.Program.Equality.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From mathcomp Require ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import Source.
Import Source.PS.
Import Source.PS.PS.

Module PS.

Definition s_stack (sps: state) : stack :=
  match sps with
  | PC (_, stk, _, _, _, _) => stk
  | CC (_, stk, _)          => stk
  end.

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

Lemma to_partial_stack_helper_nonempty:
  forall ctx gps frame,
    to_partial_stack_helper ctx gps frame <> [].
Proof.
  move=> ctx gps [C v k].
  elim: gps => [|[C' v' k'] gps' IH] //=.
  by case: ifP.
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

  Local Open Scope fset_scope.

  Definition sem :=
    @Semantics_gen state global_env (kstep p ctx)
                   (initial_state p ctx)
                   (final_state p ctx) (prepare_global_env p).

  Definition stack_components (ps : state) :=
    s_component ps |: fset [seq f.1 | f <- s_stack ps].

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
                 (fun bufs =>
                          ComponentMemory.prealloc
                            (get_buffers_as_map bufs))
                       (unionm (prog_buffers p) (prog_buffers p1)))
      =
      filterm (fun (k : nat) (_ : ComponentMemory.t) => k \notin domm (prog_buffers p1))
                    (mapm
                       (fun bufs =>
                         ComponentMemory.prealloc
                           (get_buffers_as_map bufs))
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
                   (fun initial_buffers =>
                      ComponentMemory.prealloc
                         (get_buffers_as_map initial_buffers))
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
