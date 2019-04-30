Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.
Require Import Intermediate.PS.
Require Import Intermediate.Decomposition.
Require Import Intermediate.Composition.

Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import Intermediate.

(* RB: NOTE: The current build depends on PS and Composition, both taking a
   relatively long time to compile, but it may still be desirable to consult
   them interactively. To speed up the build process, small, tentative additions
   to those modules can be added here. Note that, in principle, the role of PS
   will be assimilated by Recombination or become very reduced. *)

(* RB: TODO: Relocate to CS. *)
Definition state_regs (s : CS.state) : Register.t :=
  let '(_, _, regs, _) := s in regs.

(* This section will be used to state various preliminary lemma without having to pollute
   other sections. *)
Section Prelim.
  (* RB: TODO: Remove reliance on auto-names. Also note that this follows from
     silent_step_preserves_program_component, posed below. *)
  Lemma epsilon_star_preserves_program_component p c s1 s2 :
    CS.is_program_component s1 (prog_interface c) ->
    Star (CS.sem (program_link p c)) s1 E0 s2 ->
    CS.is_program_component s2 (prog_interface c).
  Proof.
    intros Hprg_component Hstar.
    remember E0 as t.
    induction Hstar.
    - assumption.
    - subst; assert (t1 = E0) by now induction t1.
      assert (t2 = E0) by now induction t1. subst.
      apply IHHstar; try assumption.
      clear H0 IHHstar Hstar.
      unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn in *.
      inversion H;
        try (match goal with
            | Heq : (_, _, _, _) = s1 |- _ => rewrite -Heq in Hprg_component
            end);
        try now rewrite Pointer.inc_preserves_component.
      + erewrite <- find_label_in_component_1; eassumption.
      + now rewrite H2.
      + erewrite <- find_label_in_procedure_1; eassumption.
  Qed.
End Prelim.

(* The merge functions only depend on the interfaces that are considered. *)
Section Merge.

  Variable ip ic : Program.interface.
  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces ip ic.

  Definition merge_frames (f f''   : Pointer.t) : Pointer.t :=
    if Pointer.component f \in domm ip then f else f''.

  Fixpoint merge_stacks (s s'' : CS.stack) : CS.stack :=
    match s, s'' with
    | [], [] => []
    | f :: s, f'' :: s'' => merge_frames f f'' :: merge_stacks s s''
    | _, _ => [] (* Should not happen *)
    end.

  (* Copy-pasted straight from PS.v *)
  (* RB: TODO: Here and above, Program.interface vs. fset. *)
  Definition to_partial_memory (mem : Memory.t) (ctx : {fset Component.id}) :=
  filterm (fun k _ => negb (k \in ctx)) mem.

  Definition merge_memories (m m'' : Memory.t) : Memory.t :=
    unionm (to_partial_memory m   (domm ic))
           (to_partial_memory m'' (domm ip)). (* Note that prog_interface c = prog_interface c' *)

  Definition merge_registers (r r'' : Register.t) (pc : Pointer.t) : Register.t :=
    if Pointer.component pc \in domm ip then r else r''.

  Definition merge_pcs (pc pc'' : Pointer.t) : Pointer.t :=
    if Pointer.component pc \in domm ip then pc else pc''.

  Definition merge_states (state state'' : CS.state) : CS.state :=
    let '(s, m, r, pc) := state in
    let '(s'', m'', r'', pc'') := state'' in
    (merge_stacks s s'', merge_memories m m'', merge_registers r r'' pc, merge_pcs pc pc'').

  (* Various lemmas about these functions *)

  (* JT: TODO: Move this lemma to another section *)
  (**)
  Lemma component_in_ip_notin_ic C :
    C \in domm ip ->
    C \notin domm ic.
  Proof.
    intros Hptr.
    inversion Hmergeable_ifaces as [Hlinkable _].
    inversion Hlinkable as [_ Hdisj].
    move: Hdisj => /fdisjointP.
    intros H.
    now apply H.
  Qed.

  (* JT: TODO: Move this lemma to another section *)
  Lemma component_in_ic_notin_ip C :
    C \in domm ic ->
    C \notin domm ip.
  Proof.
    intros Hptr.
    inversion Hmergeable_ifaces as [Hlinkable _].
    inversion Hlinkable as [_ Hdisj].
    move: Hdisj.
    rewrite fdisjointC => /fdisjointP.
    intros H.
    now apply H.
  Qed.

  (* RB: TODO: Add side conditions (well-formed programs, linkable interfaces,
     etc. *)
  (* JT: I don't think we need any more side condition here *)
  Lemma merge_frames_program frame frame'' :
    Pointer.component frame \in domm ip ->
    merge_frames frame frame'' = frame.
  Proof.
    intros Hpc. unfold merge_frames. now rewrite Hpc.
  Qed.

  Lemma merge_stacks_cons_program frame gps frame'' gps'' :
    Pointer.component frame \in domm ip ->
    merge_stacks (frame :: gps) (frame'' :: gps'') = frame :: merge_stacks gps gps''.
  Proof.
    intros Hpc. simpl. now rewrite merge_frames_program.
  Qed.

  Lemma merge_frames_context frame frame'' :
    Pointer.component frame \in domm ic ->
    merge_frames frame frame'' = frame''.
  Proof.
    intros Hpc.
    apply component_in_ic_notin_ip in Hpc.
    unfold merge_frames.
    move: Hpc => /negP Hpc.
    now destruct (Pointer.component frame \in domm ip) eqn:Heq.
  Qed.


  Lemma merge_stacks_cons_context frame gps frame'' gps'' :
    Pointer.component frame \in domm ic ->
    merge_stacks (frame :: gps) (frame'' :: gps'') =
    frame'' :: merge_stacks gps gps''.
  Proof.
    intros Hpc. simpl. now rewrite merge_frames_context.
  Qed.

  Definition merge_states_stack s s'' :=
    merge_stacks (CS.state_stack s) (CS.state_stack s'').

  Lemma merge_states_stack_pc_independent_right s1 stack2 mem2 regs2 pc2 pc2' :
    merge_states_stack s1 (stack2, mem2, regs2, pc2) = merge_states_stack s1 (stack2, mem2, regs2, pc2').
  Proof.
    destruct s1 as [[[gps1 mem1] regs1] pc1].
    unfold merge_states_stack.
    reflexivity.
  Qed.

  Definition merge_states_stack_mem_independent_right s1 stack2 mem2 mem2' regs2 pc2 :
    merge_states_stack s1 (stack2, mem2, regs2, pc2) = merge_states_stack s1 (stack2, mem2', regs2, pc2).
  Proof.
    destruct s1 as [[[gps1 mem1] regs1] pc1].
    unfold merge_states_stack.
    reflexivity.
  Qed.


  Definition merge_states_mem s s'' :=
    merge_memories (CS.state_mem s) (CS.state_mem s'').

  Lemma merge_states_mem_pc_independent_right s1 stack2 mem2 regs2 pc2 pc2' :
    merge_states_mem s1 (stack2, mem2, regs2, pc2) = merge_states_mem s1 (stack2, mem2, regs2, pc2').
  Proof.
    destruct s1 as [[[stack1 mem1] regs1] pc1].
    unfold merge_states_mem.
    reflexivity.
  Qed.

  Definition merge_states_regs s s'' :=
    if Pointer.component (CS.state_pc s) \in domm ip then
      state_regs s
    else
      state_regs s''.

  Definition merge_states_pc s s'' :=
    if Pointer.component (CS.state_pc s) \in domm ip then
      CS.state_pc s
    else
      CS.state_pc s''.

  Remark merge_states_unfold s s'' :
    merge_states s s'' =
    (merge_states_stack s s'',
     merge_states_mem s s'',
     merge_states_regs s s'',
     merge_states_pc s s'').
  Proof.
    destruct s as [[[stack mem] reg] pc]; destruct s'' as [[[stack'' mem''] reg''] pc''].
    unfold merge_states_stack, merge_states_mem, merge_states_regs, merge_states_pc.
    now simpl.
  Qed.
End Merge.

(* RB: TODO: Harmonize naming conventions. *)
Section Mergeable.
  Variables p c p' c' : program.

  Hypothesis Hwfp  : well_formed_program p.
  Hypothesis Hwfc  : well_formed_program c.
  Hypothesis Hwfp' : well_formed_program p'.
  Hypothesis Hwfc' : well_formed_program c'.

  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Hypothesis Hifacep  : prog_interface p  = prog_interface p'.
  Hypothesis Hifacec  : prog_interface c  = prog_interface c'.

  (* RB: TODO: Simplify redundancies in standard hypotheses. *)
  (* Hypothesis Hmain_linkability  : linkable_mains p  c. *)
  (* Hypothesis Hmain_linkability' : linkable_mains p' c'. *)

  Hypothesis Hprog_is_closed  : closed_program (program_link p  c ).
  Hypothesis Hprog_is_closed' : closed_program (program_link p' c').

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem prog.
  Let sem'  := CS.sem prog'.
  Let sem'' := CS.sem prog''.
  Hint Unfold ip ic prog prog' prog'' sem sem' sem''.

  (* An "extensional" reading of program states a la Composition, depending
     directly on the partial programs concerned (implicitly through the section
     mechanism. *)
  Inductive mergeable_states (s s'' : CS.state)
  : Prop :=
    mergeable_states_intro : forall s0 s0'' t,
      initial_state (CS.sem (program_link p  c )) s0   ->
      initial_state (CS.sem (program_link p' c')) s0'' ->
      Star (CS.sem (program_link p  c )) s0   t s   ->
      Star (CS.sem (program_link p' c')) s0'' t s'' ->
      mergeable_states s s''.

  Lemma mergeable_states_ind' : forall P : CS.state -> CS.state -> Prop,
      (forall (s s'' : CS.state),
          initial_state (CS.sem (program_link p c)) s ->
          initial_state (CS.sem (program_link p' c')) s'' ->
          P s s'') ->
      (forall (s1 s2 s'' : CS.state),
          mergeable_states s1 s'' ->
          Step (CS.sem (program_link p c)) s1 E0 s2 ->
          P s1 s'' ->
          P s2 s'') ->
      (forall (s s1'' s2'' : CS.state),
          mergeable_states s s1'' ->
          Step (CS.sem (program_link p' c')) s1'' E0 s2'' ->
          P s s1'' ->
          P s s2'') ->
      (forall (s1 s2 s1'' s2'' : CS.state) (t : trace),
          t <> E0 ->
          mergeable_states s1 s1'' ->
          Step (CS.sem (program_link p c)) s1 t s2 ->
          Step (CS.sem (program_link p' c')) s1'' t s2'' ->
          P s1 s1'' ->
          P s2 s2'') ->
      forall (s s'' : CS.state), mergeable_states s s'' -> P s s''.
  Proof.
    intros P.
    intros Hindini HindE0l HindE0r Hindstep.
    intros s s'' Hmerg.
    inversion Hmerg as
        [s0 s0'' t Hini Hini'' Hstar Hstar''].
    apply star_iff_starR in Hstar. apply star_iff_starR in Hstar''.
    generalize dependent s''.
    induction Hstar; intros s'' Hmerg Hstar''.
    - remember E0 as t.
      induction Hstar''.
      + now apply Hindini.
      + subst.
        assert (Ht1 : t1 = E0) by now destruct t1.
        assert (Ht2 : t2 = E0) by now destruct t1.
        subst; clear H0.
        specialize (IHHstar'' eq_refl HindE0l HindE0r Hindstep).
        assert (Hmergss2 : mergeable_states s s2).
        { apply star_iff_starR in Hstar''.
          econstructor. apply Hini. apply Hini''. apply star_refl.
          assumption. }
        specialize (IHHstar'' Hini'' Hmergss2). eapply HindE0r; eauto.
    - pose proof (CS.singleton_traces (program_link p c) _ _ _ H).
      assert (t2 = E0 \/ exists ev, t2 = [ev]).
      { clear -H1.
        inversion H1.
        - right. destruct t2. simpl in *; congruence.
          simpl in *. destruct t2; eauto. simpl in *. congruence.
        - left. inversion H0. destruct t2; simpl in *. reflexivity.
          congruence. }
      destruct H2 as [Ht2E0 | [ev Ht2ev]].
      + subst.
        unfold "**" in Hstar''; rewrite app_nil_r in Hstar''.
        assert (Hmergs2s'' : mergeable_states s2 s'').
        { econstructor. eauto. eauto.
          apply star_iff_starR in Hstar. apply Hstar.
          apply star_iff_starR in Hstar''. apply Hstar''. }
        specialize (IHHstar Hini s'' Hmergs2s'' Hstar'').
        eapply HindE0l; eauto.
      + subst.
        remember (t1 ** [ev]) as t.
        induction Hstar''; subst.
        * (* contradiction *)
          assert (E0 <> t1 ** [ev]) by now induction t1. contradiction.
        * subst.
          specialize (IHHstar'' Hini'' IHHstar).
          pose proof (CS.singleton_traces (program_link p' c') _ _ _ H0) as H4.
          assert (H5: t2 = E0 \/ exists ev, t2 = [ev]).
          { clear -H4.
            inversion H4.
            - right. destruct t2. simpl in *; congruence.
              simpl in *. destruct t2; eauto. simpl in *. congruence.
            - left. inversion H0. destruct t2; simpl in *. reflexivity.
              congruence. }
          destruct H5 as [ht2E0 | [ev' Ht2ev']].
          ** subst.
             unfold "**" in H2; rewrite app_nil_r in H2; subst.
             assert (Hmergs3s4 : mergeable_states s3 s4).
             { econstructor; eauto.
               apply star_iff_starR.
               eapply starR_step.
               apply Hstar.
               eauto. reflexivity.
               apply star_iff_starR in Hstar''; apply Hstar''. }
             specialize (IHHstar'' Hmergs3s4 eq_refl).
             eapply HindE0r; eauto.
          ** subst.
             assert (t1 = t0 /\ ev = ev') as [Ht1t0 Hevev'] by now apply app_inj_tail.
             subst. clear H4 IHHstar'' H1 H2.
             specialize (IHHstar Hini s4).
             assert (mergeable_states s2 s4).
             { econstructor; eauto. apply star_iff_starR in Hstar; apply Hstar.
               apply star_iff_starR in Hstar''; apply Hstar''. }
             specialize (IHHstar H1 Hstar'').
             eapply Hindstep with (t := [ev']); eauto. unfold E0. congruence.
  Qed.

  (* JT: Removed the commented part *)

  Lemma mergeable_states_pc_same_component s s'' :
    mergeable_states s s'' ->
    Pointer.component (CS.state_pc s) = Pointer.component (CS.state_pc s'').
  Proof.
    intros Hmerg.
    induction Hmerg
      as [s s'' Hini Hini''
         | s1 s2 s'' Hmerg Hstep IH
         | s s1'' s2'' Hmerg Hstep IH
         | s1 s2 s1'' s2'' t Hdiff Hmerg Hstep Hstep'' IH]
           using mergeable_states_ind'.
    - (* Initial state *)
      inversion Hini; inversion Hini''; subst.
      unfold CS.state_pc. unfold CS.initial_machine_state.
      destruct (prog_main (program_link p c)); destruct (prog_main (program_link p' c')); eauto.
    - (* Silent step on the left *)
      rewrite <- IH.
      (* Now, the only result to prove is that stepping silently doesn't modify the
         component we're executing. Most of the cases are solvable trivially.
         The two other cases are solved by applying lemmas proved previously.
       *)
      inversion Hstep; subst; try now (destruct pc as [[C b] o]; eauto).
      + simpl in *.
        now apply find_label_in_component_1 in H0.
      + simpl in *.
        now apply find_label_in_procedure_1 in H2.
    - (* Silent step on the right *)
      rewrite IH.
      (* Same as above *)
      inversion Hstep; subst; try now (destruct pc as [[C b] o]; eauto).
      + simpl in *.
        now apply find_label_in_component_1 in H0.
      + simpl in *.
        now apply find_label_in_procedure_1 in H2.
    - (* Non-silent step *)
      inversion Hstep; subst; try contradiction.
      inversion Hstep''; subst; try contradiction.
      + reflexivity.
      + simpl in *.
        inversion Hstep''; reflexivity.
  Qed.

  (* TODO: move to CS.v
     RB: NOTE: Substitute for existing results. *)
  Lemma pc_component_in_ip_or_ic : forall s st mem reg pc t,
      initial_state sem s ->
      Star sem s t (st, mem, reg, pc) ->
      Pointer.component pc \in domm ip \/ Pointer.component pc \in domm ic.
  Proof.
    intros s st mem reg pc t Hini Hstar.
    assert (H : Pointer.component pc \in domm (prog_interface prog)).
    { replace pc with (CS.state_pc (st, mem, reg, pc)); try reflexivity.
      apply CS.comes_from_initial_state_pc_domm.
      destruct (cprog_main_existence Hprog_is_closed) as [i [_ [? _]]].
      exists prog, i, s, t.
      split; first (destruct Hmergeable_ifaces; now apply linking_well_formedness).
      repeat split; eauto. }
    move: H. simpl. rewrite domm_union. now apply /fsetUP.
  Qed.

(**)
  Lemma merge_mergeable_states_regs_program s s'' :
    CS.is_program_component s ic ->
    mergeable_states s s'' ->
    merge_states_regs ip s s'' = state_regs s.
  Proof.
    intros Hcomp Hmerg.
    destruct s as [[[stack mem] reg] pc]; destruct s'' as [[[stack'' mem''] reg''] pc''].
    unfold merge_states_regs. simpl.
    unfold merge_registers.
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn in Hcomp.
    inversion Hmerg as [s0 s0'' t  Hini Hini'' Hstar Hstar''].
    destruct (pc_component_in_ip_or_ic Hini Hstar) as [H | H].
    - now rewrite H.
    - now rewrite H in Hcomp.
  Qed.

  Lemma merge_mergeable_states_pc_program s s'' :
    CS.is_program_component s ic ->
    mergeable_states s s'' ->
    merge_states_pc ip s s'' = CS.state_pc s.
  Proof.
    intros Hcomp Hmerg.
    destruct s as [[[stack mem] reg] pc]; destruct s'' as [[[stack'' mem''] reg''] pc''].
    unfold merge_states_pc. simpl.
    unfold merge_pcs.
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn in Hcomp.
    inversion Hmerg as [s0 s0'' t  Hini Hini'' Hstar Hstar''].
    destruct (pc_component_in_ip_or_ic Hini Hstar) as [H | H].
    - now rewrite H.
    - now rewrite H in Hcomp.
  Qed.

  Lemma merge_mergeable_states_regs_context s s'' :
    CS.is_context_component s ic ->
    mergeable_states s s'' ->
    merge_states_regs ip s s'' = state_regs s''.
  Proof.
    intros Hcomp Hmerg.
    destruct s as [[[stack mem] reg] pc]; destruct s'' as [[[stack'' mem''] reg''] pc''].
    unfold merge_states_regs. simpl.
    unfold merge_registers.
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn in Hcomp.
    inversion Hmergeable_ifaces as [Hlinkable _].
    destruct Hlinkable as [_ Hdisj].
    move: Hdisj.
    rewrite fdisjointC => /fdisjointP Hdisj.
    specialize (Hdisj (Pointer.component pc) Hcomp).
    move: Hdisj => /negP => Hdisj.
    destruct (Pointer.component pc \in domm ip) eqn:Heq; now rewrite Heq.
  Qed.

  Lemma merge_mergeable_states_pc_context s s'' :
    CS.is_context_component s ic ->
    mergeable_states s s'' ->
    merge_states_pc ip s s'' = CS.state_pc s''.
  Proof.
    intros Hcomp Hmerg.
    destruct s as [[[stack mem] reg] pc]; destruct s'' as [[[stack'' mem''] reg''] pc''].
    unfold merge_states_pc. simpl.
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn in Hcomp.
    inversion Hmergeable_ifaces as [Hlinkable _].
    destruct Hlinkable as [_ Hdisj].
    move: Hdisj.
    rewrite fdisjointC => /fdisjointP Hdisj.
    specialize (Hdisj (Pointer.component pc) Hcomp).
    move: Hdisj => /negP => Hdisj.
    destruct (Pointer.component pc \in domm ip) eqn:Heq; now rewrite Heq.
  Qed.

  Lemma mergeable_states_merge_program s s'' :
    CS.is_program_component s ic ->
    mergeable_states s s'' ->
    merge_states ip ic s s'' =
    (merge_states_stack ip s s'',
     merge_states_mem ip ic s s'',
     state_regs s,
     CS.state_pc s).
  Proof.
    intros Hcomp Hmerg.
    rewrite merge_states_unfold.
    rewrite merge_mergeable_states_pc_program; try assumption.
    rewrite merge_mergeable_states_regs_program; try assumption.
    reflexivity.
  Qed.

  Lemma mergeable_states_merge_context s s'' :
    CS.is_context_component s ic ->
    mergeable_states s s'' ->
    merge_states ip ic s s'' =
    (merge_states_stack ip s s'',
     merge_states_mem ip ic s s'',
     state_regs s'',
     CS.state_pc s'').
  Proof.
    intros Hcomp Hmerg.
    rewrite merge_states_unfold.
    rewrite merge_mergeable_states_pc_context; try assumption.
    rewrite merge_mergeable_states_regs_context; try assumption.
    reflexivity.
  Qed.
(**)

  Lemma mergeable_states_program_to_program s s'' :
    mergeable_states s s'' ->
    CS.is_program_component s   ic ->
    CS.is_program_component s'' ic.
  Proof.
    destruct s   as [[[? ?] ?] pc  ].
    destruct s'' as [[[? ?] ?] pc''].
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn.
    intros Hmerge Hpc.
    pose proof mergeable_states_pc_same_component Hmerge as Hcomp. simpl in Hcomp.
    congruence.
  Qed.

  Lemma mergeable_states_context_to_program s1 s2 :
    mergeable_states s1 s2 ->
    CS.is_context_component s1 ic ->
    CS.is_program_component s2 ip.
  Proof.
    intros Hmerg.
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn.
    destruct s1 as [[[stack1 mem1] reg1] pc1]; destruct s2 as [[[stack2 mem2] reg2] pc2].
    assert (Hpc : Pointer.component pc1 = Pointer.component pc2).
    { eapply mergeable_states_pc_same_component with
          (s := (stack1, mem1, reg1, pc1)) (s'' := (stack2, mem2, reg2, pc2)).
      eassumption. }
    rewrite <- Hpc; clear Hpc.
    inversion Hmerg
      as [? ? ? Hini Hini'' Hstar Hstar'']; subst.
    destruct Hmergeable_ifaces as [[_ Hdisj] _].
    move: Hdisj.
    rewrite fdisjointC => /fdisjointP Hdisj.
    now auto.
  Qed.

  Lemma mergeable_states_program_to_context s s'' :
    mergeable_states s s'' ->
    CS.is_program_component s ic ->
    CS.is_context_component s'' ip.
  Proof.
    intros Hmerg.
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn.
    destruct s as [[[stack mem] reg] pc]; destruct s'' as [[[stack'' mem''] reg''] pc''].
    assert (Hpc : Pointer.component pc = Pointer.component pc'').
    { eapply mergeable_states_pc_same_component with
          (s := (stack, mem, reg, pc)) (s'' := (stack'', mem'', reg'', pc'')).
      eassumption. }
    rewrite <- Hpc.

    inversion Hmerg as [s0 _ t Hini _ Hstar _].
    pose proof (pc_component_in_ip_or_ic Hini Hstar).
    intros Hn; destruct H.
    assumption.
    rewrite H in Hn. inversion Hn.
  Qed.

  (* RB: NOTE: Try to phrase everything either as CS.is_XXX_component, or as
     \[not]in. This is the equivalent of the old [PS.domm_partition]. *)
  Lemma mergeable_states_notin_to_in s s'' :
    mergeable_states s s'' ->
    Pointer.component (CS.state_pc s) \notin domm ip ->
    Pointer.component (CS.state_pc s) \in domm ic.
  Proof.
    intros Hmerg Hpc_notin.
    inversion Hmerg as [? ? ? Hini ? Hstar ?].
    destruct s as [[[? ?] ?] pc].
    pose proof (pc_component_in_ip_or_ic Hini Hstar) as Hpc.
    destruct Hpc.
    - now rewrite H1 in Hpc_notin.
    - now assumption.
  Qed.

  Lemma mergeable_states_cons_domm
        frame1   gps1   mem1   regs1   pc1
        frame1'' gps1'' mem1'' regs1'' pc1'' :
    mergeable_states (frame1   :: gps1  , mem1  , regs1  , pc1  )
                     (frame1'' :: gps1'', mem1'', regs1'', pc1'') ->
    Pointer.component frame1 = Pointer.component frame1''.
  Admitted.
End Mergeable.

Section MergeSym.

  Variables p c p' c' : program.
  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Hypothesis Hifacep  : prog_interface p  = prog_interface p'.
  Hypothesis Hifacec  : prog_interface c  = prog_interface c'.

  Hypothesis Hwfp  : well_formed_program p.
  Hypothesis Hwfc  : well_formed_program c.
  Hypothesis Hwfp' : well_formed_program p'.
  Hypothesis Hwfc' : well_formed_program c'.

  Hypothesis Hprog_is_closed  : closed_program (program_link p  c ).

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem prog.
  Let sem'  := CS.sem prog'.
  Let sem'' := CS.sem prog''.
  Hint Unfold ip ic prog prog' prog'' sem sem' sem''.

  Lemma merge_states_sym s s'' :
    mergeable_states p c p' c' s s'' ->
    merge_states ip ic s s'' = merge_states ic ip s'' s.
  Proof.
    intros Hmerg.
    inversion Hmerg as [s0 s0'' t Hini Hini'' Hstar Hstar''].
    destruct s as [[[stack mem] reg] pc]; destruct s'' as [[[stack'' mem''] reg''] pc''].
    unfold merge_states.

    (* TODO: state the symmetry lemma for each of the element. *)
    (* JT: I tried stating the symmetry lemma for each element, but the
       conditions for which it holds are not totally easy to state in a
       simple manner. I still think proving this result will be easy, so
       I leave it for later. *)
  Admitted.

  Lemma mergeable_states_sym s1 s1'' : mergeable_states p c p' c' s1 s1'' <-> mergeable_states c' p' c p s1'' s1.
  Proof.
    split.
    - intros Hmerg.
      inversion Hmerg as [s0 s0'' t ? ? ? ?].
      inversion Hmergeable_ifaces as [Hlinkable _].
      pose proof (program_linkC Hwfc Hwfp (linkable_sym Hlinkable)) as Hcp.
      rewrite Hifacec Hifacep in Hlinkable.
      pose proof (program_linkC Hwfc' Hwfp' (linkable_sym Hlinkable)) as Hc'p'.
      apply mergeable_states_intro with (s0 := s0'') (s0'' := s0) (t := t);
        try (now rewrite Hcp);
        try (now rewrite Hc'p').
    - intros Hmerg.
      inversion Hmerg as [s0'' s0 t ? ? ? ?].
      inversion Hmergeable_ifaces as [Hlinkable _].
      pose proof (program_linkC Hwfc Hwfp (linkable_sym Hlinkable)) as Hcp.
      rewrite Hifacec Hifacep in Hlinkable.
      pose proof (program_linkC Hwfc' Hwfp' (linkable_sym Hlinkable)) as Hc'p'.
      apply mergeable_states_intro with (s0 := s0) (s0'' := s0'') (t := t);
        try (now rewrite -Hcp);
        try (now rewrite -Hc'p').
  Qed.

End MergeSym.

Section PS.
  Variables p c p' c' : program.
  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Hypothesis Hifacep  : prog_interface p  = prog_interface p'.
  Hypothesis Hifacec  : prog_interface c  = prog_interface c'.

  Hypothesis Hwfp  : well_formed_program p.
  Hypothesis Hwfc  : well_formed_program c.
  Hypothesis Hwfp' : well_formed_program p'.
  Hypothesis Hwfc' : well_formed_program c'.

  Hypothesis Hprog_is_closed  : closed_program (program_link p  c ).

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem prog.
  Let sem'  := CS.sem prog'.
  Let sem'' := CS.sem prog''.
  Hint Unfold ip ic prog prog' prog'' sem sem' sem''.

    (* Given a silent star driven by the "program" side p, the "context" side c
     remains unaltered. *)
  (* Lemma context_epsilon_star_is_silent s1 s2 : *)
  (*   CS.is_program_component s1 (prog_interface c) -> *)
  (*   Star (CS.sem (program_link p c)) s1 E0 s2 -> *)
  (*   PS.partialize s1 (prog_interface p) = PS.partialize s2 (prog_interface p). *)
  (* Admitted. *)

  (* Lemma merge_states_partialize s s1'' s2'' : *)
  (*   mergeable_states p c p' c' s s1'' -> *)
  (*   PS.partialize s1'' (prog_interface p) = PS.partialize s2'' (prog_interface p) -> *)
  (*   merge_states (prog_interface p) (prog_interface c) s s1'' = *)
  (*   merge_states (prog_interface p) (prog_interface c) s s2''. *)
  (* Admitted. *)

  Ltac t_merge_states_silent_star_mergeable Hini Hini'' Hstar0 Hstar0'' Hstar :=
    match goal with
      | |- mergeable_states _ _ _ _ _ (_, _, _, Pointer.inc _) =>
        eapply (mergeable_states_intro Hini Hini'' Hstar0);
          apply (star_trans Hstar0'') with (t2 := E0);
          [ eapply (star_trans Hstar); last reflexivity;
            eapply star_step;
            [ eassumption | apply star_refl | reflexivity]
          | unfold "**"; now rewrite app_nil_r
          ]
      | |- mergeable_states _ _ _ _ _ (_, _, _, _) =>
        eapply (mergeable_states_intro Hini Hini'' Hstar0);
          apply (star_trans Hstar0'') with (t2 := E0);
          [ eapply (star_trans Hstar); last reflexivity;
            eapply star_refl
          | unfold "**"; now rewrite app_nil_r
          ]
    end.

  Ltac t_merge_states_silent_star Hini Hini'' Hstar0 Hstar0'' Hstar :=
    erewrite !mergeable_states_merge_program;
        first erewrite merge_states_stack_pc_independent_right;
        first erewrite merge_states_mem_pc_independent_right;
        first reflexivity; try eassumption;
          t_merge_states_silent_star_mergeable Hini Hini'' Hstar0 Hstar0'' Hstar.

  (* JT: I think this lemma could replace the two above lemmas *)
  Lemma merge_states_silent_star s s1'' s2'' :
    mergeable_states p c p' c' s s1'' ->
    CS.is_program_component s (prog_interface c) ->
    Star (CS.sem (program_link p' c')) s1'' E0 s2'' ->
    merge_states (prog_interface p) (prog_interface c) s s1'' =
    merge_states (prog_interface p) (prog_interface c) s s2''.
  Proof.
    intros Hmerg Hcomp Hstar.
    remember E0 as t.
    apply star_iff_starR in Hstar.
    induction Hstar.
    - reflexivity.
    - subst.
      assert (H1 : t1 = E0) by now destruct t1.
      assert (H2 : t2 = E0) by now destruct t1.
      subst; clear H0.
      assert (Hcomp1 : CS.is_program_component s1 (prog_interface c)) by admit.
      specialize (IHHstar Hmerg eq_refl).
      apply star_iff_starR in Hstar.
      assert (Hcomp2 : CS.is_program_component s2 (prog_interface c'))
       by now (eapply epsilon_star_preserves_program_component; try rewrite -Hifacec; eauto).
      rewrite IHHstar; clear IHHstar.
      inversion Hmerg as [s0 s0'' t Hini Hini'' Hstar0 Hstar0''].
      inversion H; subst; try now t_merge_states_silent_star Hini Hini'' Hstar0 Hstar0'' Hstar.
      + erewrite !mergeable_states_merge_program; try eassumption.
        erewrite merge_states_stack_pc_independent_right with (pc2' := Pointer.inc pc); try eassumption.
        erewrite merge_states_mem_pc_independent_right with (pc2' := Pointer.inc pc); try eassumption.
        erewrite merge_states_stack_mem_independent_right with (mem2' := mem'); try eassumption.
        assert (Heq: merge_states_mem (prog_interface p) (prog_interface c) s (gps, mem, regs, Pointer.inc pc) =
                     merge_states_mem (prog_interface p) (prog_interface c) s (gps, mem', regs, Pointer.inc pc)).
        { unfold merge_states_mem, merge_memories, to_partial_memory; simpl.
          (* this seems complicated to prove :( *) admit. }
        now rewrite Heq.
        t_merge_states_silent_star_mergeable Hini Hini'' Hstar0 Hstar0'' Hstar.
        t_merge_states_silent_star_mergeable Hini Hini'' Hstar0 Hstar0'' Hstar.
  Admitted.

  (* The following should be an easy corollary of the _is_silent lemma. *)
  Lemma context_epsilon_star_merge_states s s1 s2 :
    mergeable_states p c p' c' s s1 ->
    CS.is_program_component s (prog_interface c) ->
    Star (CS.sem (program_link p' c')) s1 E0 s2 ->
    Star (CS.sem (program_link p  c'))
         (merge_states (prog_interface p) (prog_interface c) s s1) E0
         (merge_states (prog_interface p) (prog_interface c) s s2).
  Proof.
    intros Hmerg Hcomp Hstar.
    rewrite (merge_states_silent_star Hmerg Hcomp Hstar).
    apply star_refl.
  Qed.

End PS.

  Lemma to_partial_memory_in ip ic mem ptr :
    mergeable_interfaces ip ic ->
    ptr \in domm ip ->
    (to_partial_memory mem (domm ic)) ptr = mem ptr.
  Admitted.

  Lemma to_partial_memory_notin ip ic mem ptr :
    mergeable_interfaces ip ic ->
    ptr \in domm ic ->
    (to_partial_memory mem (domm ic)) ptr = None.
  Admitted.

  (* Search _ prepare_procedures_memory. *)
  (* Search _ PS.to_partial_memory unionm. *)
  Lemma prepare_procedures_memory_left p c :
    linkable (prog_interface p) (prog_interface c) ->
    to_partial_memory
      (unionm (prepare_procedures_memory p) (prepare_procedures_memory c))
      (domm (prog_interface c)) =
    prepare_procedures_memory p.
  Proof.
    intros [_ Hdisjoint].
    unfold to_partial_memory, merge_memories.
    rewrite <- domm_prepare_procedures_memory,
          -> filterm_union,
          -> fdisjoint_filterm_full,
          -> fdisjoint_filterm_empty, -> unionm0;
      first reflexivity;
      try rewrite -> !domm_prepare_procedures_memory; congruence.
  Qed.

  Lemma prepare_procedures_memory_right p c :
    linkable (prog_interface p) (prog_interface c) ->
    to_partial_memory
      (unionm (prepare_procedures_memory p) (prepare_procedures_memory c))
      (domm (prog_interface p)) =
    prepare_procedures_memory c.
  Proof.
    intros Hlinkable.
    rewrite unionmC; try assumption.
    apply prepare_procedures_memory_left with (c := p) (p := c).
    now apply linkable_sym.
    inversion Hlinkable. 
    now rewrite !domm_prepare_procedures_memory.
  Qed.
  
Section BehaviorStar.
  Variables p c: program.

  (* RB: Could be phrased in terms of does_prefix. *)
  Theorem behavior_prefix_star b m :
    program_behaves (CS.sem (program_link p c)) b ->
    prefix m b ->
  exists s1 s2,
    CS.initial_state (program_link p c) s1 /\
    Star (CS.sem (program_link p c)) s1 (finpref_trace m) s2.
  Proof.
    destruct m as [tm | tm | tm].
    - intros Hb Hm.
      destruct b as [t | ? | ? | ?];
        simpl in Hm; try contradiction;
        subst t.
      inversion Hb as [s1 ? Hini Hbeh |]; subst.
      inversion Hbeh as [? s2 Hstar Hfinal | | |]; subst.
      eexists; eexists; split; now eauto.
    - intros Hb Hm.
      destruct b as [? | ? | ? | t];
        simpl in Hm; try contradiction;
        subst t.
      inversion Hb as [s1 ? Hini Hbeh | Hini]; subst.
      + inversion Hbeh as [| | | ? s2 Hstar Hnostep Hfinal]; subst.
        eexists; eexists; split; now eauto.
      + specialize (Hini (CS.initial_machine_state (program_link p c))).
        congruence.
    - revert b.
      induction tm as [| e t IHt] using rev_ind;
        intros b Hb Hm;
        simpl in *.
      + exists (CS.initial_machine_state (program_link p c)), (CS.initial_machine_state (program_link p c)).
        split; [congruence | now apply star_refl].
      + pose proof behavior_prefix_app_inv Hm as Hprefix.
        specialize (IHt _ Hb Hprefix).
        destruct IHt as [s1 [s2 [Hini Hstar]]].
        inversion Hm as [b']; subst.
        inversion Hb as [s1' ? Hini' Hbeh' | Hini' Hbeh']; subst.
        * assert (Heq : s1 = s1')
            by now (inversion Hini; inversion Hini').
          subst s1'.
          inversion Hbeh' as [ t' s2' Hstar' Hfinal' Heq
                             | t' s2' Hstar' Hsilent' Heq
                             | T' Hreact' Heq
                             | t' s2' Hstar' Hstep' Hfinal' Heq];
            subst.
          (* RB: TODO: Refactor block. *)
          -- destruct b' as [tb' | ? | ? | ?];
               simpl in Heq;
               try discriminate.
             inversion Heq; subst t'; clear Heq.
             destruct (star_app_inv (CS.singleton_traces (program_link p c)) _ _ Hstar')
               as [s' [Hstar'1 Hstar'2]].
             now eauto.
          -- (* Same as Terminates case. *)
             destruct b' as [? | tb' | ? | ?];
               simpl in Heq;
               try discriminate.
             inversion Heq; subst t'; clear Heq.
             destruct (star_app_inv (CS.singleton_traces (program_link p c)) _ _ Hstar')
               as [s' [Hstar'1 Hstar'2]].
             now eauto.
          -- (* Similar to Terminates and Diverges, but on an infinite trace.
                Ltac can easily take care of these commonalities. *)
             destruct b' as [? | ? | Tb' | ?];
               simpl in Heq;
               try discriminate.
             inversion Heq; subst T'; clear Heq.
             destruct (forever_reactive_app_inv (CS.singleton_traces (program_link p c)) _ _ Hreact')
               as [s' [Hstar'1 Hreact'2]].
             now eauto.
          -- (* Same as Terminate and Diverges. *)
             destruct b' as [? | ? | ? | tb'];
               simpl in Heq;
               try discriminate.
             inversion Heq; subst t'; clear Heq.
             destruct (star_app_inv (CS.singleton_traces (program_link p c)) _ _ Hstar')
               as [s' [Hstar'1 Hstar'2]].
             now eauto.
        * specialize (Hini' (CS.initial_machine_state (program_link p c))).
          congruence.
  Qed.
End BehaviorStar.

Section ThreewayMultisem1.
  Variables p c p' c' : program.

  Hypothesis Hwfp  : well_formed_program p.
  Hypothesis Hwfc  : well_formed_program c.
  Hypothesis Hwfp' : well_formed_program p'.
  Hypothesis Hwfc' : well_formed_program c'.

  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Hypothesis Hifacep  : prog_interface p  = prog_interface p'.
  Hypothesis Hifacec  : prog_interface c  = prog_interface c'.

  (* RB: TODO: Simplify redundancies in standard hypotheses. *)
  Hypothesis Hmain_linkability  : linkable_mains p  c.
  Hypothesis Hmain_linkability' : linkable_mains p' c'.

  Hypothesis Hprog_is_closed  : closed_program (program_link p  c ).
  Hypothesis Hprog_is_closed' : closed_program (program_link p' c').

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem prog.
  Let sem'  := CS.sem prog'.
  Let sem'' := CS.sem prog''.
  Hint Unfold ip ic prog prog' prog'' sem sem' sem''.

  (* RB: TODO: More the following few helper lemmas to their appropriate
     location. Consider changing the naming conventions from
     "partialized" to "recombined" or similar. Exposing the innards of the
     memory merge operation is not pretty; sealing them would require to
     add the program step from s to the lemmas. In this block, mergeable_states
     may be too strong and could be weakened if it were interesting to do so.

     See comments for pointers to existing related lemmas. *)

  Lemma is_program_component_pc_in_domm s s'' :
    CS.is_program_component s ic ->
    mergeable_states p c p' c' s s'' ->
    Pointer.component (CS.state_pc s) \in domm ip.
  Proof.
    intros Hpc Hmerge.
    assert (Hcc := Hmerge);
      apply mergeable_states_program_to_context in Hcc; try assumption.
    unfold CS.is_context_component, turn_of, CS.state_turn in Hcc.
    rewrite (mergeable_states_pc_same_component Hmerge).
    now destruct s'' as [[[? ?] ?] ?].
  Qed.

  Lemma is_program_component_pc_notin_domm s :
    CS.is_program_component s ic ->
    Pointer.component (CS.state_pc s) \notin domm ic.
  Proof.
    now destruct s as [[[? ?] ?] ?].
  Qed.

  Lemma to_partial_memory_merge_memories_left s s'' :
    mergeable_states p c p' c' s s'' ->
    to_partial_memory                       (CS.state_mem s)                     (domm ic) =
    to_partial_memory (merge_memories ip ic (CS.state_mem s) (CS.state_mem s'')) (domm ic).
  Proof.
    intros Hmerg.
    unfold to_partial_memory.
    simpl.
  Admitted.

  (* Search _ Memory.load filterm. *)
  Lemma program_load_to_partialized_memory s s'' ptr v :
    CS.is_program_component s ic ->
    mergeable_states p c p' c' s s'' ->
    Pointer.component ptr = Pointer.component (CS.state_pc s) ->
    Memory.load (CS.state_mem s) ptr = Some v ->
    Memory.load (merge_memories ip ic (CS.state_mem s) (CS.state_mem s'')) ptr =
    Some v.
  Proof.
    intros Hpc Hmerge Hptr Hload.
    destruct s as [[[gps mem] regs] pc]. destruct ptr as [[C b] o]. simpl in *. subst.
    pose proof is_program_component_pc_notin_domm Hpc as Hdomm.
    pose proof to_partial_memory_merge_memories_left Hmerge as Hmem.
    now erewrite <- (program_load_in_partialized_memory_strong Hmem Hdomm).
  Qed.

  (* RB: NOTE: Consider removing weaker version of lemma above. *)
  Lemma program_load_to_partialized_memory_strong s s'' ptr :
    CS.is_program_component s ic ->
    mergeable_states p c p' c' s s'' ->
    Pointer.component ptr = Pointer.component (CS.state_pc s) ->
    Memory.load (CS.state_mem s) ptr =
    Memory.load (merge_memories ip ic (CS.state_mem s) (CS.state_mem s'')) ptr.
  Proof.
    destruct (Memory.load (CS.state_mem s) ptr) as [v |] eqn:Hcase1;
      first (symmetry; now apply program_load_to_partialized_memory).
    (* The new part is the None case. *)
    intros Hpc Hmerge Hptr.
    destruct s as [[[gps mem] regs] pc]; destruct ptr as [[C b] o];
      unfold Memory.load, merge_memories in *; simpl in *; subst.
    eapply is_program_component_pc_in_domm in Hpc; try eassumption.
    erewrite unionmE, to_partial_memory_in, to_partial_memory_notin;
      try eassumption;
      [| apply mergeable_interfaces_sym; eassumption].
    now destruct (mem (Pointer.component pc)).
  Qed.

  (* Search _ Memory.store filterm. *)
  (* Search _ Memory.store PS.to_partial_memory. *)
  (* Search _ Memory.store PS.merge_memories. *)
  Lemma program_store_to_partialized_memory s s'' ptr v mem :
    CS.is_program_component s ic ->
    mergeable_states p c p' c' s s'' ->
    Pointer.component ptr = Pointer.component (CS.state_pc s) ->
    Memory.store (CS.state_mem s) ptr v = Some mem ->
    Memory.store (merge_memories ip ic (CS.state_mem s) (CS.state_mem s'')) ptr v =
    Some (merge_memories ip ic mem (CS.state_mem s'')).
  Proof.
    intros Hpc Hmerge Hptr Hstore.
    pose proof is_program_component_pc_notin_domm Hpc as Hnotin.
    rewrite <- Hptr in Hnotin.
    pose proof PS.partialize_program_store Hnotin Hstore as Hstore'.
    pose proof PS.unpartialize_program_store
         (PS.to_partial_memory (CS.state_mem s'') (domm ip)) Hstore' as Hstore''.
    done.
  Qed.

  (* Search _ Memory.alloc filterm. *)
  (* Search _ Memory.alloc PS.to_partial_memory. *)
  (* Search _ Memory.alloc PS.merge_memories. *)
  Lemma program_alloc_to_partialized_memory s s'' mem ptr size :
    CS.is_program_component s ic ->
    mergeable_states p c p' c' s s'' ->
    Memory.alloc (CS.state_mem s) (CS.state_component s) size = Some (mem, ptr) ->
    Memory.alloc (merge_memories ip ic (CS.state_mem s) (CS.state_mem s''))
                 (CS.state_component s) size =
    Some (merge_memories ip ic mem (CS.state_mem s''), ptr).
  Proof.
    intros Hpc Hmerge Halloc.
    pose proof is_program_component_pc_notin_domm Hpc as Hnotin.
    pose proof PS.partialize_program_alloc Hnotin Halloc as Halloc'.
    pose proof PS.unpartialize_program_alloc
         (PS.to_partial_memory (CS.state_mem s'') (domm ip)) Halloc' as Halloc''.
    done.
  Qed.

  (* Search _ find_label_in_component. *)
  Lemma find_label_in_component_recombination s s'' l pc :
    CS.is_program_component s ic ->
    mergeable_states p c p' c' s s'' ->
    find_label_in_component (globalenv sem) (CS.state_pc s) l = Some pc ->
    find_label_in_component (globalenv sem') (CS.state_pc s) l = Some pc.
  Proof.
    destruct s as [[[? ?] ?] pc_]. simpl.
    intros Hpc Hmerge Hlabel.
    pose proof proj1 Hmergeable_ifaces as Hlinkable.
    pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmains.
    pose proof find_label_in_component_1 _ _ _ _ Hlabel as Hpc_.
    pose proof is_program_component_pc_notin_domm Hpc as Hdomm; simpl in Hdomm.
    rewrite (find_label_in_component_program_link_left _ _ _ _ Hmains) in Hlabel;
      try assumption.
    unfold ic in Hdomm; rewrite Hifacec in Hdomm.
    rewrite (find_label_in_component_program_link_left Hdomm Hwfp);
      try congruence.
    apply linkable_implies_linkable_mains; congruence.
  Qed.

  (* Search _ find_label_in_procedure. *)
  Lemma find_label_in_procedure_recombination s s'' l pc :
    CS.is_program_component s ic ->
    mergeable_states p c p' c' s s'' ->
    find_label_in_procedure (globalenv sem) (CS.state_pc s) l = Some pc ->
    find_label_in_procedure (globalenv sem') (CS.state_pc s) l = Some pc.
  Proof.
    destruct s as [[[? ?] ?] pc_]. simpl.
    intros Hpc Hmerge Hlabel.
    pose proof proj1 Hmergeable_ifaces as Hlinkable.
    pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmains.
    pose proof find_label_in_procedure_1 _ _ _ _ Hlabel as Hpc_.
    pose proof is_program_component_pc_notin_domm Hpc as Hdomm; simpl in Hdomm.
    rewrite (find_label_in_procedure_program_link_left _ _ _ _ Hmains) in Hlabel;
      try assumption.
    unfold find_label_in_procedure in *.
    destruct ((genv_procedures (prepare_global_env p)) (Pointer.component pc_))
      as [C_procs |] eqn:Hcase; last discriminate.
    rewrite Hifacec in Hlinkable. unfold ic in Hdomm; rewrite Hifacec in Hdomm.
    pose proof linkable_implies_linkable_mains Hwfp Hwfc' Hlinkable as Hmains'.
    rewrite (genv_procedures_program_link_left_notin _ _ _ _ Hmains');
      try assumption.
    now rewrite Hcase.
  Qed.

  (* Search _ PS.is_program_component Pointer.component. *)
  Lemma is_program_component_in_domm s s'' :
    CS.is_program_component s ic ->
    mergeable_states p c p' c' s s'' ->
    CS.state_component s \in domm (prog_interface p).
  Admitted.

  Lemma silent_step_preserves_program_component s1 s2 :
    CS.is_program_component s1 ic ->
    Step sem s1 E0 s2 ->
    CS.is_program_component s2 ic.
  Proof.
    intros Hcomp1 Hstep12.
    destruct s1 as [[[? ?] ?] pc1].
    destruct s2 as [[[? ?] ?] pc2].
    unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn.
    pose proof CS.silent_step_preserves_component _ _ _ Hstep12 as Heq.
    simpl in Heq. now rewrite <- Heq.
  Qed.

  (* Search _ imported_procedure. *)
  (* RB: NOTE: This kind of lemma is usually the composition of two unions, one
     of which is generally extant. *)
  Lemma imported_procedure_recombination s C P :
    CS.is_program_component s ic ->
    imported_procedure
      (genv_interface (globalenv sem )) (CS.state_component s) C P ->
    imported_procedure
      (genv_interface (globalenv sem')) (CS.state_component s) C P.
  Proof.
    intros Hpc Himp.
    pose proof is_program_component_pc_notin_domm Hpc as Hdomm; simpl in Hdomm.
    rewrite (imported_procedure_unionm_left Hdomm) in Himp.
    destruct Himp as [CI [Hcomp Himp]]. exists CI. split; [| assumption].
    unfold Program.has_component. rewrite unionmE. now rewrite Hcomp.
  Qed.

  (* RB: NOTE: The two EntryPoint lemmas can be phrased as a more general one
     operating on an explicit program link, one then being the exact symmetric of
     the other, i.e., its application after communativity of linking. There is a
     choice of encoding of component membership in both cases. *)

  (* Search _ EntryPoint.get. *)
  Lemma genv_entrypoints_recombination_left C P b :
    C \in domm ip ->
    EntryPoint.get C P (genv_entrypoints (globalenv sem )) = Some b ->
    EntryPoint.get C P (genv_entrypoints (globalenv sem')) = Some b.
  Proof.
    intros Hdomm Hentry.
    pose proof proj1 Hmergeable_ifaces as Hlinkable.
    eapply (PS.domm_partition_notin (mergeable_interfaces_sym _ _ Hmergeable_ifaces)) in Hdomm.
    rewrite genv_entrypoints_program_link_left in Hentry; try assumption.
    unfold ic in Hdomm; rewrite Hifacec in Hlinkable, Hdomm.
    rewrite genv_entrypoints_program_link_left; try assumption.
    now apply linkable_implies_linkable_mains.
  Qed.

  Lemma genv_entrypoints_recombination_right C P b :
    C \in domm ic ->
    EntryPoint.get C P (genv_entrypoints (globalenv sem'')) = Some b ->
    EntryPoint.get C P (genv_entrypoints (globalenv sem' )) = Some b.
  Proof.
    unfold sem'', sem', prog'', prog'. intros Hdomm Hentry.
    pose proof proj1 Hmergeable_ifaces as Hlinkable.
    rewrite program_linkC in Hentry; try congruence.
    rewrite program_linkC; try congruence.
    (* RB: TODO: Apply symmetry after making independent from sectioning. *)
    (* apply genv_entrypoints_recombination_left. *)
  Admitted.

  (* RB: NOTE: The regular, non-helper contents of the section start here. *)

  Lemma threeway_multisem_mergeable_step_E0 s1 s2 s1'' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' s1 s1'' ->
    Step sem s1 E0 s2 ->
    mergeable_states p c p' c' s2 s1''.
  Proof.
    intros Hcomp1 Hmerge1 Hstep12.
    inversion Hmerge1 as [s0 s0'' t Hini1 Hini2 Hstar01 Hstar01''].
    apply mergeable_states_intro with (s0 := s0) (s0'' := s0'') (t := t);
      try assumption.
    eapply star_right; try eassumption; now rewrite E0_right.
  Qed.

  (* RB: NOTE: The structure follows closely that of
     threeway_multisem_star_program. *)
  Theorem threeway_multisem_mergeable_program s1 s1'' t s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' s1 s1'' ->
    Star sem   s1   t s2   ->
    Star sem'' s1'' t s2'' ->
    mergeable_states p c p' c' s2 s2''.
  Proof.
    intros _ Hmerg Hstar Hstar''.
    inversion Hmerg as [s0 s0'' t0 Hini Hini'' Hstar0 Hstar0''].
    econstructor.
    - eassumption.
    - eassumption.
    - eapply star_trans; try eassumption; reflexivity.
    - eapply star_trans; try eassumption; reflexivity.
  Qed.

  Ltac t_threeway_multisem_step_E0 :=
    Composition.CS_step_of_executing;
    try eassumption; try reflexivity;
    (* Solve side goals for CS step. *)
    match goal with
    | |- Memory.load _ _ = _ =>
      apply program_load_to_partialized_memory;
      try assumption; [now rewrite Pointer.inc_preserves_component]
    | |- Memory.store _ _ _ = _ =>
      apply program_store_to_partialized_memory; eassumption
    | |- find_label_in_component _ _ _ = _ =>
      eapply find_label_in_component_recombination; eassumption
    | |- find_label_in_procedure _ _ _ = _ =>
      eapply find_label_in_procedure_recombination; eassumption
    | |- Memory.alloc _ _ _ = _ =>
      now apply program_alloc_to_partialized_memory
    | _ => idtac
    end;
    (* Apply linking invariance and solve side goals. *)
    eapply execution_invariant_to_linking; try eassumption;
    [ congruence
    | apply linkable_implies_linkable_mains; congruence
    | eapply is_program_component_in_domm; eassumption
    ].

  Lemma threeway_multisem_step_E0 s1 s2 s1'' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' s1 s1'' ->
    Step sem  s1 E0 s2 ->
    Step sem' (merge_states ip ic s1 s1'') E0 (merge_states ip ic s2 s1'').
  Proof.
    intros Hcomp1 Hmerge1 Hstep12.
    (* Derive some useful facts and begin to expose state structure. *)
    inversion Hmergeable_ifaces as [Hlinkable _].
    rewrite (mergeable_states_merge_program
               Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hcomp1 Hmerge1).
    pose proof silent_step_preserves_program_component Hcomp1 Hstep12 as Hcomp2.
    pose proof threeway_multisem_mergeable_step_E0 Hcomp1 Hmerge1 Hstep12
      as Hmerge2.
    rewrite (mergeable_states_merge_program
               Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hcomp2 Hmerge2).
    destruct s1 as [[[gps1 mem1] regs1] pc1].
    destruct s2 as [[[gps2 mem2] regs2] pc2].
    destruct s1'' as [[[gps1'' mem1''] regs1''] pc1''].
    (* Case analysis on step. *)
    inversion Hstep12; subst;
      t_threeway_multisem_step_E0.
  Qed.

  (* Compose two stars into a merged star. The "program" side drives both stars
     and performs all steps without interruption, the "context" side remains
     unaltered in both stars. *)
  Theorem threeway_multisem_star_E0_program s1 s1'' s2 s2'':
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' s1 s1'' ->
    Star sem   s1   E0 s2   ->
    Star sem'' s1'' E0 s2'' ->
    Star sem'  (merge_states ip ic s1 s1'') E0 (merge_states ip ic s2 s2'').
  Proof.
    intros Hcomp1 Hmerge1 Hstar12 Hstar12''.
    pose proof mergeable_states_program_to_program Hmerge1 Hcomp1 as Hcomp1'.
    rewrite Hifacec in Hcomp1'.
    remember E0 as t eqn:Ht.
    revert Ht Hmerge1 Hcomp1 Hcomp1' Hstar12''.
    apply star_iff_starR in Hstar12.
    induction Hstar12 as [s | s1 t1 s2 t2 s3 ? Hstar12 IHstar Hstep23]; subst;
      intros Ht Hmerge1 Hcomp1 Hcomp1' Hstar12'.
    - rewrite -Hifacec in Hcomp1'.
      unfold ip, ic; erewrite merge_states_silent_star; try eassumption.
      now apply star_refl.
    - apply Eapp_E0_inv in Ht. destruct Ht; subst.
      specialize (IHstar (eq_refl _) Hmerge1 Hcomp1 Hcomp1' Hstar12').
      apply star_trans with (t1 := E0) (s2 := merge_states ip ic s2 s2'') (t2 := E0);
        [assumption | | reflexivity].
      apply star_step with (t1 := E0) (s2 := merge_states ip ic s3 s2'') (t2 := E0).
      + apply star_iff_starR in Hstar12.
        pose proof threeway_multisem_mergeable_program Hcomp1 Hmerge1 Hstar12 Hstar12'
          as Hmerge2.
        pose proof epsilon_star_preserves_program_component Hcomp1 Hstar12
          as Hcomp2.
        exact (threeway_multisem_step_E0 Hcomp2 Hmerge2 Hstep23).
      + now constructor.
      + reflexivity.
  Qed.

  (* RB: NOTE: Observe similarity with threeway_multisem_mergeable_program, use
     to replace this if possible. *)
  Lemma threeway_multisem_event_lockstep_program_mergeable s1 s1'' e s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' s1 s1'' ->
    Step sem   s1   [e] s2   ->
    Step sem'' s1'' [e] s2'' ->
    mergeable_states p c p' c' s2 s2''.
  Proof.
    intros Hcomp1 Hmerge1 Hstep12 Hstep12''.
    inversion Hmerge1 as [s0 s0'' t Hini0 Hini0'' Hstar01 Hstar01''].
    apply mergeable_states_intro with (s0 := s0) (s0'' := s0'') (t := t ** [e]).
    - assumption.
    - assumption.
    - eapply star_right; try eassumption; reflexivity.
    - eapply star_right; try eassumption; reflexivity.
  Qed.

  Ltac t_threeway_multisem_event_lockstep_program_step_call Hcomp1 Hmerge1 :=
    apply CS.Call; try assumption;
    [
    | now apply (imported_procedure_recombination Hcomp1)
    |    (now apply genv_entrypoints_recombination_left)
      || (now apply genv_entrypoints_recombination_right)
    ];
    (* Apply linking invariance and solve side goals (very similar to the
       silent case, but slightly different setup). *)
    [eapply execution_invariant_to_linking; try eassumption;
      [ congruence
      | apply linkable_implies_linkable_mains; congruence
      | exact (is_program_component_in_domm Hcomp1 Hmerge1)
      ]
    ].

  Ltac t_threeway_multisem_event_lockstep_program_step_return Hcomp1 Hmerge1 :=
    apply CS.Return; try congruence; (* [congruence] to cover context case. *)
    eapply execution_invariant_to_linking; try eassumption;
    [ congruence
    | apply linkable_implies_linkable_mains; congruence
    | exact (is_program_component_in_domm Hcomp1 Hmerge1)
    ].

  (* RB: TODO: Does it make sense to compact calls and returns into a unified
     solve tactic? *)
  Lemma threeway_multisem_event_lockstep_program_step s1 s1'' e s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' s1 s1'' ->
    Step sem   s1   [e] s2   ->
    Step sem'' s1'' [e] s2'' ->
    Step sem'  (merge_states ip ic s1 s1'') [e] (merge_states ip ic s2 s2'').
  Proof.
    intros Hcomp1 Hmerge1 Hstep12 Hstep12''.
    (* Derive some useful facts and begin to expose state structure. *)
    inversion Hmergeable_ifaces as [Hlinkable _].
    rewrite (mergeable_states_merge_program
               Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hcomp1 Hmerge1).
    pose proof threeway_multisem_event_lockstep_program_mergeable
         Hcomp1 Hmerge1 Hstep12 Hstep12'' as Hmerge2.
    set s1copy := s1. destruct s1 as [[[gps1 mem1] regs1] pc1].
    set s2copy := s2. destruct s2 as [[[gps2 mem2] regs2] pc2].
    destruct s1'' as [[[gps1'' mem1''] regs1''] pc1''].
    destruct s2'' as [[[gps2'' mem2''] regs2''] pc2''].
    (* Case analysis on step. *)
    inversion Hstep12; subst;
      inversion Hstep12''; subst.
    - (* Call: case analysis on call point. *)
      pose proof is_program_component_in_domm Hcomp1 Hmerge1 as Hdomm.
      unfold CS.state_component in Hdomm; simpl in Hdomm. unfold ip, ic.
      rewrite <- Pointer.inc_preserves_component in Hdomm.
      destruct (CS.is_program_component s2copy ic) eqn:Hcomp2;
        [ pose proof mergeable_states_program_to_context
               Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hmerge2 Hcomp2 as Hcomp2''
        | apply negb_false_iff in Hcomp2 ];
        [ erewrite mergeable_states_merge_program
        | erewrite mergeable_states_merge_context ]; try eassumption;
        unfold merge_states_mem, merge_states_stack;
        rewrite merge_stacks_cons_program; try eassumption;
        match goal with
        | Heq : Pointer.component pc1'' = Pointer.component pc1 |- _ =>
          rewrite Heq
        end;
        [| erewrite Register.invalidate_eq with (regs2 := regs1); [| congruence]];
        t_threeway_multisem_event_lockstep_program_step_call Hcomp1 Hmerge1.
    - (* Return: case analysis on return point. *)
      match goal with
      | H1 : Pointer.component pc1'' = Pointer.component pc1,
        H2 : Pointer.component pc2'' = Pointer.component pc2 |- _ =>
        rename H1 into Heq1; rename H2 into Heq2
      end.
      destruct (CS.is_program_component s2copy ic) eqn:Hcomp2;
        [| apply negb_false_iff in Hcomp2];
        [ rewrite (mergeable_states_merge_program _ _ _ _ _ Hmerge2); try assumption
        | rewrite (mergeable_states_merge_context _ _ Hmerge2); try assumption ];
        unfold merge_states_mem, merge_states_stack; simpl;
        [ pose proof is_program_component_in_domm Hcomp2 Hmerge2 as Hcomp2'';
          erewrite merge_frames_program; try eassumption
        | erewrite merge_frames_context; try eassumption ];
        [ rewrite Heq1 Heq2 | rewrite Heq1 ];
        [| erewrite Register.invalidate_eq with (regs2 := regs1); [| congruence]];
        t_threeway_multisem_event_lockstep_program_step_return Hcomp1 Hmerge1.
  Qed.

  Lemma threeway_multisem_event_lockstep_program s1 s1'' e s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' s1 s1'' ->
    Step sem   s1   [e] s2   ->
    Step sem'' s1'' [e] s2'' ->
    Step sem'  (merge_states ip ic s1 s1'') [e] (merge_states ip ic s2 s2'') /\
    mergeable_states p c p' c' s2 s2''.
  Proof.
    split.
    - now apply threeway_multisem_event_lockstep_program_step.
    - eapply threeway_multisem_event_lockstep_program_mergeable; eassumption.
  Qed.
End ThreewayMultisem1.

Section ThreewayMultisem2.
  Variables p c p' c' : program.

  Hypothesis Hwfp  : well_formed_program p.
  Hypothesis Hwfc  : well_formed_program c.
  Hypothesis Hwfp' : well_formed_program p'.
  Hypothesis Hwfc' : well_formed_program c'.

  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Hypothesis Hifacep  : prog_interface p  = prog_interface p'.
  Hypothesis Hifacec  : prog_interface c  = prog_interface c'.

  (* RB: TODO: Simplify redundancies in standard hypotheses. *)
  Hypothesis Hmain_linkability  : linkable_mains p  c.
  Hypothesis Hmain_linkability' : linkable_mains p' c'.

  Hypothesis Hprog_is_closed  : closed_program (program_link p  c ).
  Hypothesis Hprog_is_closed' : closed_program (program_link p' c').

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem prog.
  Let sem'  := CS.sem prog'.
  Let sem'' := CS.sem prog''.
  Hint Unfold ip ic prog prog' prog'' sem sem' sem''.

  (* RB: TODO: Rename, relocate. *)
  Lemma threeway_multisem_mergeable s1 s1'' t s2 s2'' :
    mergeable_states p c p' c' s1 s1'' ->
    Star sem   s1   t s2   ->
    Star sem'' s1'' t s2'' ->
    mergeable_states p c p' c' s2 s2''.
  Proof.
    intros Hmerg Hstar12 Hstar12''.
    inversion Hmerg
      as [? ? ? Hini Hini'' Hstar Hstar'']; subst.
    econstructor; try eassumption;
      eapply star_trans; try eassumption; reflexivity.
  Qed.

  (* RB: TODO: Implicit parameters, compact if possible. *)
  Lemma threeway_multisem_star_E0 s1 s1'' s2 s2'':
    mergeable_states p c p' c' s1 s1'' ->
    Star sem   s1   E0 s2   ->
    Star sem'' s1'' E0 s2'' ->
    Star sem'  (merge_states ip ic s1 s1'') E0 (merge_states ip ic s2 s2'').
  Proof.
    intros H H0 H1.
    destruct (CS.is_program_component s1 ic) eqn:Hprg_component.
    - now apply threeway_multisem_star_E0_program.
    - Check merge_states_sym.
      rewrite (merge_states_sym _ _ _ _ _ _ _ _ H); try assumption.
      rewrite (merge_states_sym _ _ _ _ _ _ _ _ (threeway_multisem_mergeable H H0 H1)); try assumption.
      (* unfold merge_states. *)
      (* fold (merge_states c p s1'' s1). *)
      (* erewrite PS.merge_partial_states_sym. fold (merge_states c p s2'' s2). *)
      assert (Hlinkable : linkable ip ic) by now destruct Hmergeable_ifaces.
      unfold ic in Hlinkable. rewrite Hifacec in Hlinkable.
      pose proof (program_linkC Hwfp Hwfc' Hlinkable) as Hprg_linkC'.
      unfold sem', prog'.
      rewrite Hprg_linkC'.

      pose proof (program_linkC Hwfp' Hwfc') as Hprg_linkC''; rewrite <- Hifacep in Hprg_linkC''.
      unfold sem'', prog'' in H1.
      rewrite (Hprg_linkC'' Hlinkable) in H1.
      pose proof (program_linkC Hwfp Hwfc) as Hprg_linkC; rewrite Hifacec in Hprg_linkC.
      unfold sem, prog in H0.
      rewrite (Hprg_linkC Hlinkable) in H0.

      pose proof (threeway_multisem_star_E0_program) as Hmultisem.

      specialize (Hmultisem c' p' c p).
      specialize (Hmultisem Hwfc' Hwfp' Hwfc Hwfp).
      rewrite <- Hifacep, <- Hifacec in Hmultisem.
      specialize (Hmultisem (mergeable_interfaces_sym ip ic Hmergeable_ifaces) eq_refl eq_refl).
      specialize (Hmultisem (linkable_mains_sym Hmain_linkability') (linkable_mains_sym Hmain_linkability)).
      assert (Hclosed'' : closed_program (program_link c' p')) by now rewrite <- (Hprg_linkC'' Hlinkable).
      assert (Hclosed : closed_program (program_link c p)) by now rewrite <- (Hprg_linkC Hlinkable).
      specialize (Hmultisem Hclosed'' Hclosed).
      specialize (Hmultisem s1'' s1 s2'' s2).
      assert (His_prg_component'' : CS.is_program_component s1'' (prog_interface p)).
      { eapply mergeable_states_context_to_program.
        apply Hmergeable_ifaces.
        apply H.
        unfold CS.is_program_component in Hprg_component. apply negbFE in Hprg_component.
        assumption.
      }
      assert (Hmerg_sym : mergeable_states c' p' c p s1'' s1).
      { inversion H.
        econstructor;
          try rewrite <- (Hprg_linkC Hlinkable); try rewrite <- (Hprg_linkC'' Hlinkable); eauto.
      }
      (* pose proof (program_linkC Hwfp' Hwfc') as Hprg_linkC''; rewrite <- Hifacep in Hprg_linkC''. *)
      (* unfold sem'', prog'' in H1. *)
      (* rewrite (Hprg_linkC'' Hlinkable) in H1. *)
      (* pose proof (program_linkC Hwfp Hwfc) as Hprg_linkC; rewrite Hifacec in Hprg_linkC. *)
      (* unfold sem, prog in H0.  *)
      (* rewrite (Hprg_linkC Hlinkable) in H0. *)
      specialize (Hmultisem His_prg_component'' Hmerg_sym H1 H0).
      assumption.
  Qed.

  (* A restricted version of the lockstep simulation on event-producing steps.
     RB: NOTE: Here is where we depart from the multi-semantics and need to
     furnish our own version. We may save effort if, as is the case here, we only
     need to concern ourselves with visible steps.

     This replaces the following two steps below:
      - MultiSem.multi_step
      - MultiSem.mergeable_states_step_trans *)
  Lemma threeway_multisem_event_lockstep s1 s1'' e s2 s2'' :
    mergeable_states p c p' c' s1 s1'' ->
    Step sem   s1   [e] s2   ->
    Step sem'' s1'' [e] s2'' ->
    Step sem'  (merge_states ip ic s1 s1'') [e] (merge_states ip ic s2 s2'') /\
    mergeable_states p c p' c' s2 s2''.
  Proof.
    intros Hmerge1 Hstep12 Hstep12''.
    destruct (CS.is_program_component s1 ic) eqn:Hcase.
    - now apply threeway_multisem_event_lockstep_program.
    - inversion Hmergeable_ifaces as [Hlinkable _].
      pose proof @threeway_multisem_event_lockstep_program c' p' c p
           Hwfc' Hwfp' Hwfc Hwfp as H.
      rewrite <- Hifacec, <- Hifacep in H.
      specialize (H (mergeable_interfaces_sym _ _ Hmergeable_ifaces) eq_refl eq_refl
                 (linkable_mains_sym Hmain_linkability') (linkable_mains_sym Hmain_linkability)).
      rewrite (closed_program_link_sym Hwfc Hwfp (linkable_sym Hlinkable)) in H.
      rewrite Hifacec Hifacep in Hlinkable;
        rewrite (closed_program_link_sym Hwfc' Hwfp' (linkable_sym Hlinkable)) in H.
      specialize (H Hprog_is_closed' Hprog_is_closed).
      specialize (H s1'' s1 e s2'' s2).

      assert (Hmerge11 := Hmerge1).
      erewrite mergeable_states_sym in Hmerge11; try eassumption.
      erewrite mergeable_states_sym; try eassumption.
      unfold ip, ic; erewrite merge_states_sym; try eassumption.
      assert (Hmerge2 : mergeable_states p c p' c' s2 s2'').
      { inversion Hmerge1.
        econstructor; try eassumption.
        apply star_iff_starR; eapply starR_step; try eassumption.
        apply star_iff_starR; eassumption. reflexivity.
        apply star_iff_starR; eapply starR_step; try eassumption.
        apply star_iff_starR; eassumption. reflexivity. }
      rewrite (merge_states_sym _ _ _ _ _ _ _ _ Hmerge2); try assumption.
      unfold sem', prog'; rewrite program_linkC; try congruence.
      apply H; try assumption.
      + unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn.
        pose proof mergeable_states_pc_same_component Hmerge1 as Hpc.
        destruct s1 as [[[? ?] ?] pc1]; destruct s1'' as [[[? ?] ?] pc1''].
        simpl in Hpc.
        rewrite -Hpc.
        unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn in Hcase.
        inversion Hmerge1 as [? ? ? Hini ? Hstar ?].
        destruct (pc_component_in_ip_or_ic Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hini Hstar).
        apply component_in_ip_notin_ic with (ic := ic) in H2.
        move: Hcase => /idP Hcase. rewrite H2 in Hcase. congruence. assumption.
        now apply component_in_ic_notin_ip with (ip := ip) in H2.
      + rewrite program_linkC; try assumption.
        now apply linkable_sym in Hlinkable.
      + rewrite program_linkC; try assumption.
        rewrite -Hifacec -Hifacep in Hlinkable.
        now apply linkable_sym.
  Qed.
  (* RB: TODO: JT will factor the symmetric proofs. *)
  (* JT: TODO: clean this proof. *)

  Theorem threeway_multisem_star_program s1 s1'' t s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' s1 s1'' ->
    Star sem   s1   t s2   ->
    Star sem'' s1'' t s2'' ->
    Star sem'  (merge_states ip ic s1 s1'') t (merge_states ip ic s2 s2'').
  Proof.
    simpl in *. intros Hcomp1 Hmerge1 Hstar12. revert s1'' s2'' Hcomp1 Hmerge1.
    apply star_iff_starR in Hstar12.
    induction Hstar12 as [s | s1 t1 s2 t2 s3 ? Hstar12 IHstar12' Hstep23]; subst;
      intros s1'' s2'' Hcomp1 Hmerge1 Hstar12''.
    - eapply context_epsilon_star_merge_states; eassumption.
    - rename s2'' into s3''. rename Hstar12'' into Hstar13''.
      apply (star_app_inv (@CS.singleton_traces _)) in Hstar13''
        as [s2'' [Hstar12'' Hstar23'']].
      specialize (IHstar12' _ _ Hcomp1 Hmerge1 Hstar12'').
      (* Apply instantiated IH and case analyze step trace. *)
      apply star_trans with (t1 := t1) (s2 := merge_states ip ic s2 s2'') (t2 := t2);
        [assumption | | reflexivity].
      apply star_iff_starR in Hstar12.
      pose proof threeway_multisem_mergeable Hmerge1 Hstar12 Hstar12''
        as Hmerge2.
      destruct t2 as [| e2 [| e2' t2]].
      + (* An epsilon step and comparable epsilon star. One is in the context and
           therefore silent, the other executes and leads the MultiSem star. *)
        eapply star_step in Hstep23; [| now apply star_refl | now apply eq_refl].
        exact (threeway_multisem_star_E0 Hmerge2 Hstep23 Hstar23'').
      + (* The step generates a trace event, mimicked on the other side (possibly
           between sequences of silent steps). *)
        change [e2] with (E0 ** e2 :: E0) in Hstar23''.
        apply (star_middle1_inv (@CS.singleton_traces _)) in Hstar23''
          as [s2''1 [s2''2 [Hstar2'' [Hstep23'' Hstar3'']]]].
        (* Prefix star. *)
        pose proof star_refl CS.step (prepare_global_env (program_link p c)) s2
          as Hstar2.
        pose proof threeway_multisem_star_E0 Hmerge2 Hstar2 Hstar2''
          as Hstar2'.
        (* Propagate mergeability, step. *)
        pose proof threeway_multisem_mergeable Hmerge2 Hstar2 Hstar2'' as Hmerge21.
        pose proof threeway_multisem_event_lockstep Hmerge21 Hstep23 Hstep23''
          as [Hstep23' Hmerge22].
        (* Propagate mergeability, suffix star. *)
        pose proof star_refl CS.step (prepare_global_env (program_link p c)) s3
          as Hstar3.
        pose proof threeway_multisem_star_E0 Hmerge22 Hstar3 Hstar3'' as Hstar3'.
        (* Compose. *)
        exact (star_trans
                 (star_right _ _ Hstar2' Hstep23' (eq_refl _))
                 Hstar3' (eq_refl _)).
      + (* Contradiction: a step generates at most one event. *)
        pose proof @CS.singleton_traces _ _ _ _ Hstep23 as Hcontra.
        simpl in Hcontra. omega.
  Qed.
End ThreewayMultisem2.

Section ThreewayMultisem3.
  Variables p c p' c' : program.

  Hypothesis Hwfp  : well_formed_program p.
  Hypothesis Hwfc  : well_formed_program c.
  Hypothesis Hwfp' : well_formed_program p'.
  Hypothesis Hwfc' : well_formed_program c'.

  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Hypothesis Hifacep  : prog_interface p  = prog_interface p'.
  Hypothesis Hifacec  : prog_interface c  = prog_interface c'.

  (* RB: TODO: Simplify redundancies in standard hypotheses. *)
  Hypothesis Hmain_linkability  : linkable_mains p  c.
  Hypothesis Hmain_linkability' : linkable_mains p' c'.

  Hypothesis Hprog_is_closed  : closed_program (program_link p  c ).
  Hypothesis Hprog_is_closed' : closed_program (program_link p' c').

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem prog.
  Let sem'  := CS.sem prog'.
  Let sem'' := CS.sem prog''.
  Hint Unfold ip ic prog prog' prog'' sem sem' sem''.

  Theorem threeway_multisem_star s1 s1'' t s2 s2'' :
    mergeable_states p c p' c' s1 s1'' ->
    Star (CS.sem (program_link p  c )) s1   t s2   ->
    Star (CS.sem (program_link p' c')) s1'' t s2'' ->
    Star (CS.sem (program_link p  c')) (merge_states ip ic s1 s1'') t (merge_states ip ic s2 s2'').
    (* /\ mergeable_states ip ic s2 s2'' *)
  Proof.
    intros Hmerge1 Hstar12 Hstar12''.
    destruct (CS.is_program_component s1 ic) eqn:Hcomp1.
    - now apply threeway_multisem_star_program.
    - apply negb_false_iff in Hcomp1.
      apply (mergeable_states_context_to_program Hmergeable_ifaces Hmerge1)
        in Hcomp1.
      assert (Hmerge2: mergeable_states p c p' c' s2 s2'')
        by (eapply threeway_multisem_mergeable; eassumption).
      rewrite program_linkC in Hstar12; try assumption;
        last admit. (* Easy. *)
      rewrite program_linkC in Hstar12''; try assumption;
        last admit. (* Easy. *)
      rewrite program_linkC; try assumption;
        last admit. (* Easy. *)
      unfold ip, ic.
      setoid_rewrite merge_states_sym at 1 2; try eassumption.
      (* apply threeway_multisem_star_program. *)
      (* apply threeway_multisem_star_program with (p' := c). *)
  Admitted. (* RB: NOTE: Assigned to JT. *)
End ThreewayMultisem3.

(* Section ThreewayMultisem. *)
Section Recombination.
  Variables p c p' c' : program.

  Hypothesis Hwfp  : well_formed_program p.
  Hypothesis Hwfc  : well_formed_program c.
  Hypothesis Hwfp' : well_formed_program p'.
  Hypothesis Hwfc' : well_formed_program c'.

  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Hypothesis Hifacep  : prog_interface p  = prog_interface p'.
  Hypothesis Hifacec  : prog_interface c  = prog_interface c'.

  (* RB: TODO: Simplify redundancies in standard hypotheses. *)
  Hypothesis Hmain_linkability  : linkable_mains p  c.
  Hypothesis Hmain_linkability' : linkable_mains p' c'.

  Hypothesis Hprog_is_closed  : closed_program (program_link p  c ).
  Hypothesis Hprog_is_closed' : closed_program (program_link p' c').

  Let ip := prog_interface p.
  Let ic := prog_interface c.
  Let prog   := program_link p  c.
  Let prog'  := program_link p  c'.
  Let prog'' := program_link p' c'.
  Let sem   := CS.sem prog.
  Let sem'  := CS.sem prog'.
  Let sem'' := CS.sem prog''.
  Hint Unfold ip ic prog prog' prog'' sem sem' sem''.

  (* RB: NOTE: Relocate lemmas on initial states when ready. *)
  Lemma initial_states_mergeability s s'' :
    initial_state sem   s   ->
    initial_state sem'' s'' ->
    mergeable_states p c p' c' s s''.
  Proof.
    simpl. unfold CS.initial_state.
    intros Hini Hini''.
    apply mergeable_states_intro with (s0 := s) (s0'' := s'') (t := E0); subst;
      reflexivity || now apply star_refl.
  Qed.

  (* RB: NOTE: Here, the existential is explicitly instantiated; the mergeability
     relation is also different than in standard "two-way" simulations. *)
  Theorem match_initial_states s s'' :
    initial_state sem   s   ->
    initial_state sem'' s'' ->
    initial_state sem'  (merge_states ip ic s s'') /\
    mergeable_states p c p' c' s s''.
  Proof.
    intros Hini Hini''.
    pose proof initial_states_mergeability Hini Hini'' as Hmerge.
    simpl in *. unfold CS.initial_state in *. subst.
    split; last assumption.
    inversion Hmergeable_ifaces as [Hlinkable _].
    (* Expose structure of initial states. *)
    rewrite !CS.initial_machine_state_after_linking; try congruence;
      last (apply interface_preserves_closedness_r with (p2 := c); try assumption;
            now apply interface_implies_matching_mains).
    unfold merge_states, merge_memories, merge_registers, merge_pcs; simpl.
    (* Memory simplifictions. *)
    rewrite (prepare_procedures_memory_left Hlinkable).
    unfold ip. erewrite Hifacep at 1. rewrite Hifacep Hifacec in Hlinkable.
    rewrite (prepare_procedures_memory_right Hlinkable).
    (* Case analysis on main and related simplifications. *)
    destruct (Component.main \in domm ip) eqn:Hcase;
      rewrite Hcase.
    - pose proof component_in_ip_notin_ic Hmergeable_ifaces Hcase as Hnotin.
      rewrite (CS.prog_main_block_no_main _ Hwfc Hnotin).
      rewrite Hifacec in Hnotin. now rewrite (CS.prog_main_block_no_main _ Hwfc' Hnotin).
    - (* Symmetric case. *)
  Admitted.

  (* RB: NOTE: Consider execution invariance and similar lemmas on the right as
     well, as symmetry arguments reoccur all the time.
     TODO: Observe the proof of match_nostep is almost identical, and refactor
     accordingly. *)
  Theorem match_final_states s s'' :
    mergeable_states p c p' c' s s'' ->
    final_state sem   s   ->
    final_state sem'' s'' ->
    final_state sem'  (merge_states ip ic s s'').
  Proof.
    destruct s as [[[gps mem] regs] pc].
    destruct s'' as [[[gps'' mem''] regs''] pc''].
    unfold final_state. simpl. unfold merge_pcs.
    intros Hmerge Hfinal Hfinal''.
    inversion Hmergeable_ifaces as [Hlinkable _].
    destruct (Pointer.component pc \in domm ip) eqn:Hcase.
    - apply execution_invariant_to_linking with (c1 := c); try easy.
      + congruence.
      + apply linkable_implies_linkable_mains; congruence.
    - (* Symmetric case. *)
      unfold prog', prog'' in *.
      rewrite program_linkC in Hfinal''; try congruence.
      rewrite program_linkC; try congruence.
      apply linkable_sym in Hlinkable.
      apply linkable_mains_sym in Hmain_linkability.
      apply linkable_mains_sym in Hmain_linkability'.
      apply execution_invariant_to_linking with (c1 := p'); try congruence.
      + apply linkable_implies_linkable_mains; congruence.
      + setoid_rewrite <- (mergeable_states_pc_same_component Hmerge).
        rewrite <- Hifacec.
        apply negb_true_iff in Hcase.
        eapply (mergeable_states_notin_to_in _ _ _ _ Hmerge); try eassumption.
        (* RB: TODO: After lemma is proved, simplify lemma application and remove
           shelved goals. *)
        Unshelve. all:assumption.
  Qed.

  Theorem star_simulation s1 s1'' t s2 s2'' :
    mergeable_states p c p' c' s1 s1'' ->
    Star sem   s1   t s2   ->
    Star sem'' s1'' t s2'' ->
    Star sem'  (merge_states ip ic s1 s1'') t (merge_states ip ic s2 s2'') /\
    mergeable_states p c p' c' s2 s2''.
  Proof.
    intros. split.
    - now apply threeway_multisem_star.
    - eapply threeway_multisem_mergeable; eassumption.
  Qed.

  (* RB: TODO: Move when finished. In the current form, these lemmas are
     sufficient if unsatisfying in that only an imprecise existential is
     offered. *)
  Lemma program_store_from_partialized_memory s s'' ptr v mem' :
    Pointer.component (CS.state_pc s) \in domm ip ->
    Pointer.component ptr = Pointer.component (CS.state_pc s) ->
    Memory.store (merge_states_mem ip ic s s'') ptr v = Some mem' ->
  exists mem,
    Memory.store (CS.state_mem s) ptr v = Some mem.
  Proof.
    destruct s as [[[gps mem] regs] pc].
    destruct s'' as [[[gps'' mem''] regs''] pc''].
    destruct ptr as [[C b] o].
    unfold Memory.store, merge_states, merge_states_mem, merge_memories.
    intros Hdomm Hcomp.
    rewrite unionmE Hcomp.
    erewrite to_partial_memory_in; try eassumption.
    erewrite to_partial_memory_notin;
      try eassumption; [| apply mergeable_interfaces_sym; eassumption].
    simpl.
    destruct (mem (Pointer.component pc)) as [memC |] eqn:Hcase1;
      last discriminate.
    simpl.
    destruct (ComponentMemory.store memC b o v) as [memC' |] eqn:Hcase2;
      last discriminate.
    now eauto.
  Qed.

  Lemma program_alloc_from_partialized_memory s s'' size mem' ptr' :
    Pointer.component (CS.state_pc s) \in domm ip ->
    Memory.alloc (merge_states_mem ip ic s s'') (CS.state_component s) size =  Some (mem', ptr') ->
  exists mem ptr,
    Memory.alloc (CS.state_mem s) (CS.state_component s) size = Some (mem, ptr).
  Proof.
    destruct s as [[[gps mem] regs] pc].
    destruct s'' as [[[gps'' mem''] regs''] pc''].
    unfold Memory.alloc, merge_states, merge_states_mem, merge_memories, CS.state_component.
    intros Hdomm.
    rewrite unionmE.
    erewrite to_partial_memory_in; try eassumption.
    erewrite to_partial_memory_notin;
      try eassumption; [| apply mergeable_interfaces_sym; eassumption].
    simpl.
    destruct (mem (Pointer.component pc)) as [memC |] eqn:Hcase1;
      last discriminate.
    simpl.
    destruct (ComponentMemory.alloc memC size) as [memC' b].
    now eauto.
  Qed.

  Theorem threeway_multisem_step_inv_program s1 s1'' t s2' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' s1 s1'' ->
    Step sem' (merge_states ip ic s1 s1'') t s2' ->
  exists s2,
    Step sem                      s1       t s2.
  Proof.
    intros Hpc Hmerge Hstep.
    destruct s1 as [[[gps1 mem1] regs1] pc1].
    destruct s1'' as [[[gps1'' mem1''] regs1''] pc1''].
    inversion Hmergeable_ifaces as [Hlinkable _].
    pose proof is_program_component_pc_in_domm
         Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hpc Hmerge as Hdomm.
    pose proof is_program_component_pc_in_domm
         Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hpc Hmerge as Hdomm'.
    pose proof is_program_component_pc_notin_domm Hpc as Hnotin.
    assert (Hmains : linkable_mains p c')
      by (apply linkable_implies_linkable_mains; congruence).
    rewrite (mergeable_states_merge_program _ _ _ _ _ Hmerge) in Hstep;
      try assumption.
    inversion Hstep; subst.

    (* 7, 12 *)

    1:{

      match goal with
      (* Calls. *)
      | Hget : EntryPoint.get _ _ _ = _ |- _ =>
        apply genv_entrypoints_interface_some with (p' := prog) in Hget as [b' Hget];
          [| simpl; congruence]
      (* Returns. *)
      | Hcons : ?PC' :: ?GPS' = ?GPS (* merge_states_stack *) |- _ =>
        destruct GPS as [| frame1' gps1'] eqn:Hgps; [discriminate |];
        destruct gps1 as [| frame1 gps1]; [now destruct gps1'' |];
        destruct gps1'' as [| frame1'' gps1'']; [easy |];
        inversion Hcons; subst PC' GPS';
        assert (Heq : Pointer.component frame1 = Pointer.component frame1')
          by (unfold merge_states_stack in Hgps;
              inversion Hgps as [[Hframe Hdummy]];
              unfold merge_frames;
              destruct (Pointer.component frame1 \in domm ip) eqn:Hcase; rewrite Hcase;
              [ reflexivity
              | eapply mergeable_states_cons_domm; last exact Hmerge; eassumption]);
        rewrite <- Heq
      | _ => idtac
      end.
      eexists;
      Composition.CS_step_of_executing;
        try eassumption; try congruence; try reflexivity;
        match goal with
        (* Memory operations. *)
        | Hload : Memory.load _ _ = _ |- Memory.load _ _ = _ =>
          unfold merge_states_mem in Hload;
          erewrite <- program_load_to_partialized_memory_strong in Hload;
          try exact Hmerge; eassumption
        | |- Memory.store _ _ _ = _ => fail
        | |- Memory.alloc _ _ _ = _ => fail
        (* Jumps. *)
        | Hlabel : find_label_in_component _ _ _ = _ |- find_label_in_component _ _ _ = _ =>
          rewrite find_label_in_component_program_link_left;
          rewrite find_label_in_component_program_link_left in Hlabel;
          try eassumption; simpl in *; congruence
        | Hlabel : find_label_in_procedure _ _ _ = _ |- find_label_in_procedure _ _ _ = _ =>
          rewrite find_label_in_procedure_program_link_left;
          rewrite find_label_in_procedure_program_link_left in Hlabel;
          try eassumption; simpl in *; congruence
        (* Calls. *)
        | Himp : imported_procedure _ _ _ _ |- imported_procedure _ _ _ _ =>
          rewrite imported_procedure_unionm_left; [| assumption];
          rewrite Hifacec in Hnotin; now rewrite imported_procedure_unionm_left in Himp
        | _ => idtac
        end;
      apply execution_invariant_to_linking with (c1 := c');
        try eassumption; [congruence].

    }

  Admitted.

  Corollary match_nostep s s'' :
    mergeable_states p c p' c' s s'' ->
    Nostep sem   s   ->
    Nostep sem'' s'' ->
    Nostep sem'  (merge_states ip ic s s'').
  Proof.
    rename s into s1. rename s'' into s1''.
    (* destruct s as [[[gps mem] regs] pc]. *)
    (* destruct s'' as [[[gps'' mem''] regs''] pc'']. *)
    intros Hmerge Hstep Hstep'' t s2' Hstep'.
    destruct (CS.is_program_component s1 ic) eqn:Hcase.
    - pose proof threeway_multisem_step_inv_program Hcase Hmerge Hstep'
        as [s2 Hcontra].
      specialize (Hstep t s2). contradiction.
    - (* Symmetric case. *)
  Admitted.

  Corollary match_nofinal s s'' :
    mergeable_states p c p' c' s s'' ->
    ~ final_state sem   s   ->
    ~ final_state sem'' s'' ->
    ~ final_state sem'  (merge_states ip ic s s'').
  Proof.
    destruct s as [[[gps mem] regs] pc].
    destruct s'' as [[[gps'' mem''] regs''] pc''].
    unfold final_state. simpl. unfold merge_pcs.
    intros Hmerge Hfinal Hfinal'' Hfinal'.
    inversion Hmergeable_ifaces as [Hlinkable _].
    destruct (Pointer.component pc \in domm ip) eqn:Hcase.
    - apply execution_invariant_to_linking with (c2 := c) in Hfinal'; try easy.
      + congruence.
      + apply linkable_implies_linkable_mains; congruence.
    - (* Symmetric case. *)
      unfold prog', prog'' in *.
      rewrite program_linkC in Hfinal'; try congruence.
      rewrite program_linkC in Hfinal''; try congruence.
      apply execution_invariant_to_linking with (c2 := p') in Hfinal'; try easy.
      + apply linkable_sym; congruence.
      + apply linkable_sym; congruence.
      + apply linkable_mains_sym, linkable_implies_linkable_mains; congruence.
      + apply linkable_mains_sym, linkable_implies_linkable_mains; congruence.
      + setoid_rewrite <- (mergeable_states_pc_same_component Hmerge).
        rewrite <- Hifacec.
        apply negb_true_iff in Hcase.
        now eapply (mergeable_states_notin_to_in _ _ _ _ Hmerge).
        (* RB: TODO: After lemma is proved, simplify lemma application and remove
           shelved goals. *)
        Unshelve. all:assumption.
  Qed.
(* End ThreewayMultisem. *)

(* Section Recombination. *)
(*   Variables p c p' c' : program. *)

(*   Hypothesis Hwfp  : well_formed_program p. *)
(*   Hypothesis Hwfc  : well_formed_program c. *)
(*   Hypothesis Hwfp' : well_formed_program p'. *)
(*   Hypothesis Hwfc' : well_formed_program c'. *)

(*   Hypothesis Hmergeable_ifaces : *)
(*     mergeable_interfaces (prog_interface p) (prog_interface c). *)

(*   Hypothesis Hifacep  : prog_interface p  = prog_interface p'. *)
(*   Hypothesis Hifacec  : prog_interface c  = prog_interface c'. *)

(*   (* RB: TODO: Simplify redundancies in standard hypotheses. *) *)
(*   Hypothesis Hmain_linkability  : linkable_mains p  c. *)
(*   Hypothesis Hmain_linkability' : linkable_mains p' c'. *)

(*   Hypothesis Hprog_is_closed  : closed_program (program_link p  c ). *)
(*   Hypothesis Hprog_is_closed' : closed_program (program_link p' c'). *)

(*   Let ip := prog_interface p. *)
(*   Let ic := prog_interface c. *)
(*   Let prog   := program_link p  c. *)
(*   Let prog'  := program_link p  c'. *)
(*   Let prog'' := program_link p' c'. *)
(*   Let sem   := CS.sem prog. *)
(*   Let sem'  := CS.sem prog'. *)
(*   Let sem'' := CS.sem prog''. *)
(*   Hint Unfold ip ic prog prog' prog'' sem sem' sem''. *)

  (* RB: NOTE: Possible improvements:
      - Get rid of assert idioms in FTbc case. RB: TODO: Assigned to JT.
      - Try to refactor case analysis in proof.
     This result is currently doing the legwork of going from a simulation on
     stars to one on program behaviors without direct mediation from the CompCert
     framework. *)
  Theorem recombination_prefix m :
    does_prefix sem   m ->
    does_prefix sem'' m ->
    does_prefix sem'  m.
  Proof.
    unfold does_prefix.
    intros [b [Hbeh Hprefix]] [b'' [Hbeh'' Hprefix'']].
    assert (Hst_beh := Hbeh). assert (Hst_beh'' := Hbeh'').
    apply CS.program_behaves_inv in Hst_beh   as [s1   [Hini1   Hst_beh  ]].
    apply CS.program_behaves_inv in Hst_beh'' as [s1'' [Hini1'' Hst_beh'']].
    destruct m as [tm | tm | tm].
    - destruct b   as [t   | ? | ? | ?]; try contradiction.
      destruct b'' as [t'' | ? | ? | ?]; try contradiction.
      simpl in Hprefix, Hprefix''. subst t t''.
      inversion Hst_beh   as [? s2   Hstar12   Hfinal2   | | |]; subst.
      inversion Hst_beh'' as [? s2'' Hstar12'' Hfinal2'' | | |]; subst.
      exists (Terminates tm). split; last reflexivity.
      pose proof match_initial_states Hini1 Hini1'' as [Hini1' Hmerge1].
      pose proof star_simulation Hmerge1 Hstar12 Hstar12'' as [Hstar12' Hmerge2].
      apply program_runs with (s := merge_states ip ic s1 s1'');
        first assumption.
      apply state_terminates with (s' := merge_states ip ic s2 s2'');
        first assumption.
      now apply match_final_states.
    - destruct b   as [? | ? | ? | t  ]; try contradiction.
      destruct b'' as [? | ? | ? | t'']; try contradiction.
      simpl in Hprefix, Hprefix''. subst t t''.
      inversion Hst_beh   as [| | | ? s2   Hstar12   Hstep2   Hfinal2  ]; subst.
      inversion Hst_beh'' as [| | | ? s2'' Hstar12'' Hstep2'' Hfinal2'']; subst.
      exists (Goes_wrong tm). split; last reflexivity.
      pose proof match_initial_states Hini1 Hini1'' as [Hini' Hmerge1].
      pose proof star_simulation Hmerge1 Hstar12 Hstar12'' as [Hstar12' Hmerge2].
      apply program_runs with (s := merge_states ip ic s1 s1'');
        first assumption.
      apply state_goes_wrong with (s' := merge_states ip ic s2 s2'');
        first assumption.
      + now apply match_nostep.
      + now apply match_nofinal.
    - (* Here we talk about the stars associated to the behaviors, without
         worrying now about connecting them to the existing initial states.
         RB: TODO: Remove asserts, phrase in terms of the instances of
         behavior_prefix_star directly. *)
      assert
        (exists s s',
            initial_state (CS.sem (program_link p c)) s /\
            Star (CS.sem (program_link p c)) s tm s')
        as [s1_ [s2 [Hini1_ Hstar12]]].
      {
        inversion Hmergeable_ifaces as [Hlinkable _].
        destruct (behavior_prefix_star Hbeh Hprefix)
          as [s1_ [s2 [Hini1_ Hstar12]]].
        now exists s1_, s2.
      }
      assert
        (exists s s',
            initial_state (CS.sem (program_link p' c')) s /\
            Star (CS.sem (program_link p' c')) s tm s')
        as [s1''_ [s2'' [Hini1''_ Hstar12'']]].
      {
        rewrite -> Hifacep, -> Hifacec in Hmergeable_ifaces.
        destruct (behavior_prefix_star Hbeh'' Hprefix'')
          as [s1''_ [s2'' [Hini1''_ Hstar12'']]].
        now exists s1''_, s2''.
      }
      pose proof match_initial_states Hini1_ Hini1''_ as [Hini1' Hmerge1].
      pose proof star_simulation Hmerge1 Hstar12 Hstar12'' as [Hstar12' Hmerge2].
      eapply program_behaves_finpref_exists;
        last now apply Hstar12'.
      assumption.
  Qed.
End Recombination.