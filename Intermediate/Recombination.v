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

(*
Section Merge.

  (* Hypotheses *)
  Variable p c p' c' : program.

  Hypothesis wf_p : well_formed_program p.
  Hypothesis wf_p' : well_formed_program p'.
  Hypothesis wf_c : well_formed_program c.
  Hypothesis wf_c' : well_formed_program c'.

  Hypothesis same_interfacep : prog_interface p = prog_interface p'.
  Hypothesis same_interfacec : prog_interface c = prog_interface c'.

  Hypothesis main_linkability : linkable_mains p c.
  Hypothesis main_linkability'' : linkable_mains p' c'.
  Hypothesis linkability : linkable (prog_interface p) (prog_interface c).
  Hypothesis linkability'' : linkable (prog_interface p') (prog_interface c').

  Hypothesis mergeable_ifaces:
    mergeable_interfaces (prog_interface p) (prog_interface c).
  Hypothesis mergeable_ifaces'':
    mergeable_interfaces (prog_interface p') (prog_interface c').

  Let prog := program_link p c.
  Let prog'' := program_link p' c'.

  Hypothesis prog_is_closed : closed_program prog.
  Hypothesis prog''_is_closed : closed_program prog''.


  (* Defintiion of mergeable states *)
  Inductive mergeable_frames : Pointer.t -> Pointer.t -> Prop :=
  | mergeable_frames_same_component : forall c c'' b b'' o o'',
      c = c'' ->
      c \in domm (prog_interface prog) -> 
      mergeable_frames (c, b, o) (c'', b'', o'')
  .

  Inductive mergeable_stacks : CS.stack -> CS.stack -> Prop :=
  | mergeable_stacks_nil  : mergeable_stacks [] []
  | mergeable_stacks_cons : forall (s s'' : CS.stack) (f f'' : Pointer.t),
      mergeable_stacks s s'' ->
      mergeable_frames f f'' ->
      mergeable_stacks (f :: s) (f'' :: s'')
  .

  Inductive mergeable_memories : Memory.t -> Memory.t -> Prop :=
  | mergeable_memory_same_domm : forall (m m'' : Memory.t),
      domm m = domm (prog_interface prog)  ->
      domm m'' = domm (prog_interface prog'') ->
      mergeable_memories m m''
  .

  Inductive mergeable_states : CS.state -> CS.state -> Prop :=
  | mergeable : forall (s s'' : CS.stack) (m m'' : Memory.t)
                        (r r'' : Register.t) (pc pc'' : Pointer.t),
      mergeable_stacks s s'' ->
      mergeable_memories m m'' ->
      Pointer.component pc = Pointer.component pc'' ->
      Pointer.component pc \in domm (prog_interface prog) ->
      mergeable_states (s, m, r, pc) (s'', m'', r'', pc'')
  .
 


  (* Definition of the function to merge two states *)
  Definition merge_frames (f f''   : Pointer.t) :=
    if Nat.eqb (Pointer.component f) (Pointer.component f'') then
      if Pointer.component f \in domm (prog_interface p) then
        Some f
      else
        if Pointer.component f \in domm (prog_interface c') then Some f''
        else
          None
    else None.
  
  Fixpoint merge_stacks (s s'' : CS.stack) : option CS.stack :=
    match s, s'' with
    | [], [] => Some []
    | f :: s, f'' :: s'' =>
      match merge_stacks s s'', merge_frames f f'' with
      | Some s', Some f' => Some (f' :: s')
      | _, _ => None
      end
    | _, _ => None
    end.
  
  Definition merge_memories (m m'' : Memory.t) :=
    unionm (PS.to_partial_memory m (domm (prog_interface p)))
           (PS.to_partial_memory m'' (domm (prog_interface c'))).

  Definition merge_registers (r r'' : Register.t) (pc : Pointer.t) : option Register.t :=
    let id := Pointer.component pc in
    if id \in domm (prog_interface p) then Some r else
      if id \in domm (prog_interface c') then Some r'' else
        None.

  Definition merge_pcs (pc pc'' : Pointer.t) : option Pointer.t :=
    let id := Pointer.component pc in
    if id \in domm (prog_interface p) then Some pc else
      if id \in domm (prog_interface c') then Some pc'' else
        None.

  Definition merge_states (state state'' : CS.state) : option CS.state :=
    let '(s, m, r, pc) := state in
    let '(s'', m'', r'', pc'') := state'' in

    match merge_stacks s s'' with
    | None => None
    | Some s' =>
      let m' := merge_memories m m'' in
      match merge_registers r r'' pc with
      | None => None
      | Some r' =>
        match merge_pcs pc pc'' with
        | None => None
        | Some pc' => Some (s', m', r', pc')
        end
      end
    end.

  Lemma mergeable_states_are_mergeable : forall state state'',
      mergeable_states state state'' -> exists state', merge_states state state'' = Some state'.
  Proof.
    intros state state'' H.
    inversion H as [? ? ? ? ? ? ? ? Hstacks Hmems Hpceq Hpcin]; subst.
    assert (Hreg : exists r', merge_registers r r'' pc = Some r').
    { unfold merge_registers.
      unfold prog in Hpcin.
      simpl in Hpcin.
      rewrite domm_union in Hpcin.
      move: Hpcin => /fsetUP Hpcin.
      destruct Hpcin as [Hpcin | Hpcin]; try rewrite Hpcin. now eexists.
      rewrite same_interfacec in Hpcin; rewrite Hpcin.
      destruct (Pointer.component pc \in domm (prog_interface p)); eauto.
    }
    assert (Hpc : exists pc', merge_pcs pc pc'' = Some pc').
    { unfold merge_pcs.
      unfold prog in Hpcin. simpl in Hpcin.
      rewrite domm_union in Hpcin.
      move: Hpcin => /fsetUP Hpcin.
      destruct Hpcin as [Hpcin | Hpcin]; [rewrite Hpcin; now eexists|].
      rewrite same_interfacec in Hpcin; rewrite Hpcin.
      destruct (Pointer.component pc \in domm (prog_interface p)); eauto.
    }
    destruct Hreg as [r' Hr']; destruct Hpc as [pc' Hpc'].
    assert (Hstacks': exists s', merge_stacks s s'' = Some s').
    { induction Hstacks.
      - now eexists.
      - assert (Hmergeable: mergeable_states (s, m, r, pc) (s'', m'', r'', pc''))
          by now constructor.
        destruct (IHHstacks Hmergeable) as [s' Hs'].
        simpl; rewrite Hs'.
        assert (Hframes : exists f', merge_frames f f'' = Some f').
        { unfold merge_frames. inversion H0; subst. simpl.
          assert (H1: c'' =? c'') by (clear; induction c''; eauto); rewrite H1.
          unfold prog in H2. simpl in H2.
          rewrite domm_union in H2.
          move: H2 => /fsetUP H2.
          destruct H2 as [H2 | H2]; [rewrite H2; now eexists|].
          destruct (c'' \in domm (prog_interface p)) eqn:eq; rewrite eq; eauto.
          rewrite same_interfacec in H2; rewrite H2; eauto.
        }
        destruct Hframes as [f' Hf']; rewrite Hf'; now eauto.
    }
    destruct Hstacks' as [s' Hs']; simpl; rewrite Hs' Hpc' Hr'; eauto.
  Qed.
  
End Merge.
*)

(* RB: NOTE: The current build depends on PS and Composition, both taking a
   relatively long time to compile, but it may still be desirable to consult
   them interactively. To speed up the build process, small, tentative additions
   to those modules can be added here. Note that, in principle, the role of PS
   will be assimilated by Recombination or become very reduced. *)

(* RB: TODO: Relocate to CS. *)
Definition state_regs (s : CS.state) : Register.t :=
  let '(_, _, regs, _) := s in regs.

(* RB: TODO: Harmonize naming conventions. *)
Section Merge.
  Variables p c p' c' : program.
  Hypothesis Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).

  Hypothesis Hifacep  : prog_interface p  = prog_interface p'.
  Hypothesis Hifacec  : prog_interface c  = prog_interface c'.

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

  Inductive mergeable_states' (s s'' : CS.state)
    : Prop :=
  | mergeable_ini :
      initial_state (CS.sem (program_link p  c )) s   ->
      initial_state (CS.sem (program_link p' c')) s'' ->
      mergeable_states' s s''
  | mergeable_trace : forall t s0 s0'',
      mergeable_states' s0 s0'' ->
      Star (CS.sem (program_link p  c )) s0   t s   ->
      Star (CS.sem (program_link p' c')) s0'' t s'' ->
      mergeable_states' s s''.

  Lemma mergeable_states_equiv : forall s s'',
      mergeable_states s s'' <-> mergeable_states' s s''.
  Proof.
    intros s s''; split; intros H.
    - inversion H; subst.
      eapply mergeable_trace; eauto. now apply mergeable_ini.
    - induction H.
      + econstructor; now eauto using star_refl.
      + inversion IHmergeable_states'.
        econstructor; now eauto using star_trans.
  Qed.

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
   
  Definition merge_states (s s'' : CS.state)
    : CS.state :=
    PS.unpartialize (PS.merge_partial_states (PS.partialize s   ic)
                                             (PS.partialize s'' ip)).

  (* Composition of mergeable states. *)

  (* The following definitions are meant to manipulate pairs of mergeable states
     piecemeal. If the states are indeed mergeable, no error conditions (treated
     silently by the definitions, for now) occur. Moreover, they result in stacks
     and memories "without holes" w.r.t. to the generating states and interfaces,
     provided that the mergeability assumptions is present. *)

  Definition merge_stacks (gps gps'' : CS.stack) : CS.stack :=
    PS.unpartialize_stack
      (PS.merge_stacks
         (PS.to_partial_stack gps (domm ic))
         (PS.to_partial_stack gps'' (domm ip))).

  (* RB: TODO: Rename these definitions to merge_states_. *)
  Definition mergeable_states_stack (s s'' : CS.state) : CS.stack :=
    merge_stacks (CS.state_stack s) (CS.state_stack s'').

  Definition merge_memories (mem mem'' : Memory.t) : Memory.t :=
    PS.merge_memories
      (PS.to_partial_memory mem   (domm ic))
      (PS.to_partial_memory mem'' (domm ip)).

  Definition mergeable_states_memory (s s'' : CS.state) : Memory.t :=
    merge_memories (CS.state_mem s) (CS.state_mem s'').

  Definition mergeable_states_regs (s s'' : CS.state) : Register.t :=
    if Pointer.component (CS.state_pc s) \in domm ic then
      state_regs s
    else
      state_regs s''.

  (* RB: TODO: Observe that stack frames are actually pointers, and also useful
     in the context of PC. Adjust naming. *)
  Definition mergeable_states_pc (s s'' : CS.state) : Pointer.t :=
    PS.unpartialize_stack_frame
      (PS.merge_stack_frames
         (PS.to_partial_frame (domm ic) (CS.state_pc s  ),
          PS.to_partial_frame (domm ip) (CS.state_pc s''))).

  Definition mergeable_states_state (s s'' : CS.state) : CS.state :=
    (mergeable_states_stack  s s'',
     mergeable_states_memory s s'',
     mergeable_states_regs   s s'',
     mergeable_states_pc     s s'').

  (* RB: TODO: Add side conditions (well-formed programs, linkable interfaces,
     etc. *)
  Lemma merge_stacks_cons_program frame gps frame'' gps'' :
    Pointer.component frame \in domm ip ->
    merge_stacks (frame :: gps) (frame'' :: gps'') =
    frame :: merge_stacks gps gps''.
  Admitted.

  Lemma merge_stacks_cons_context frame gps frame'' gps'' :
    Pointer.component frame \in domm ic ->
    merge_stacks (frame :: gps) (frame'' :: gps'') =
    frame'' :: merge_stacks gps gps''.
  Admitted.

  Lemma mergeable_states_merge s s'' :
    mergeable_states s s'' ->
    merge_states s s'' =
    mergeable_states_state s s''.
  Admitted.

  Lemma mergeable_states_merge_program s s'' :
    CS.is_program_component s ic ->
    mergeable_states s s'' ->
    merge_states s s'' =
    (mergeable_states_stack s s'',
     mergeable_states_memory s s'',
     state_regs s,
     CS.state_pc s).
  Admitted.

  Lemma mergeable_states_merge_context s s'' :
    CS.is_context_component s ic ->
    mergeable_states s s'' ->
    merge_states s s'' =
    (mergeable_states_stack s s'',
     mergeable_states_memory s s'',
     state_regs s'',
     CS.state_pc s'').
  Admitted.

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

  Lemma mergeable_states_program_to_program s1 s2 :
    mergeable_states s1 s2 ->
    CS.is_program_component s1 ic ->
    CS.is_program_component s2 ic.
  Admitted.

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
    (* Related to PS.domm_partition? The proof is scary. *)
    intros Hmerg.
    inversion Hmerg as [? ? ? Hini Hini'' Hstar Hstar'']; subst.
    apply star_iff_starR in Hstar. apply star_iff_starR in Hstar''.
    induction Hstar.    
  Admitted.

End Merge.

Section MergeSym.
  Lemma merge_states_sym p c p' c' s s'' :
    mergeable_states p c p' c' s s'' ->
    merge_states p c s s'' = merge_states c p s'' s.
  Admitted.
End MergeSym.

Section PS.
  (* RB: TODO: Add hypotheses to section and/or theorems as needed. Currently
     this make proof application lightweight. *)

  (* Lemma mergeable_states_context_to_program ctx1 ctx2 s1 s2 : *)
  (*   mergeable_states ctx1 ctx2 s1 s2 -> *)
  (*   CS.is_context_component s1 ctx1 -> *)
  (*   CS.is_program_component s2 ctx2. *)
  (* Admitted. *)

  (* Lemma mergeable_states_program_to_context ctx1 ctx2 s1 s2 : *)
  (*   mergeable_states ctx1 ctx2 s1 s2 -> *)
  (*   CS.is_program_component s1 ctx1 -> *)
  (*   CS.is_context_component s2 ctx2. *)
  (* Admitted. *)

  (* Given a silent star driven by the "program" side p, the "context" side c
     remains unaltered. *)
  Lemma context_epsilon_star_is_silent p c s1 s2 :
    CS.is_program_component s1 (prog_interface c) ->
    Star (CS.sem (program_link p c)) s1 E0 s2 ->
    PS.partialize s1 (prog_interface p) = PS.partialize s2 (prog_interface p).
  Admitted.

  (* The following should be an easy corollary of the _is_silent lemma. *)
  Lemma context_epsilon_star_merge_states p c p' c' s s1 s2 :
    mergeable_states p c p' c' s s1 ->
    CS.is_program_component s (prog_interface c) ->
    Star (CS.sem (program_link p' c')) s1 E0 s2 ->
    Star (CS.sem (program_link p  c'))
         (merge_states p c s s1) E0
         (merge_states p c s s2).
  Admitted.

  Lemma epsilon_star_preserves_program_component p c s1 s2 :
    CS.is_program_component s1 (prog_interface c) ->
    Star (CS.sem (program_link p c)) s1 E0 s2 ->
    CS.is_program_component s2 (prog_interface c).
  Admitted.
End PS.

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
  Admitted. (* RB: NOTE: JT will fill it in. *)

  (* RB: TODO: More the following few helper lemmas to their appropriate
     location. Consider changing the naming conventions from
     "partialized" to "recombined" or similar. Exposing the innards of the
     memory merge operation is not pretty; sealing them would require to
     add the program step from s to the lemmas. In this block, mergeable_states
     may be too strong and could be weakened if it were interesting to do so. *)
  Lemma program_load_to_partialized_memory s s'' ptr v :
    CS.is_program_component s ic ->
    mergeable_states p c p' c' s s'' ->
    Pointer.component ptr = Pointer.component (CS.state_pc s) ->
    Memory.load (CS.state_mem s) ptr = Some v ->
    Memory.load (merge_memories p c (CS.state_mem s) (CS.state_mem s'')) ptr =
    Some v.
  Admitted.

  Lemma program_store_to_partialized_memory s s'' ptr v mem :
    CS.is_program_component s ic ->
    mergeable_states p c p' c' s s'' ->
    Pointer.component ptr = Pointer.component (CS.state_pc s) ->
    Memory.store (CS.state_mem s) ptr v = Some mem ->
    Memory.store (merge_memories p c (CS.state_mem s) (CS.state_mem s'')) ptr v =
    Some (merge_memories p c mem (CS.state_mem s'')).
  Admitted.

  Lemma program_alloc_to_partialized_memory s s'' mem ptr size :
    CS.is_program_component s ic ->
    mergeable_states p c p' c' s s'' ->
    Memory.alloc (CS.state_mem s) (CS.state_component s) size = Some (mem, ptr) ->
    Memory.alloc (merge_memories p c (CS.state_mem s) (CS.state_mem s''))
                 (CS.state_component s) size =
    Some (merge_memories p c mem (CS.state_mem s''), ptr).
  Admitted.

  Lemma find_label_in_component_recombination s s'' l pc :
    CS.is_program_component s ic ->
    mergeable_states p c p' c' s s'' ->
    find_label_in_component (globalenv sem) (CS.state_pc s) l = Some pc ->
    find_label_in_component (globalenv sem') (CS.state_pc s) l = Some pc.
  Admitted.

  Lemma find_label_in_procedure_recombination s s'' l pc :
    CS.is_program_component s ic ->
    mergeable_states p c p' c' s s'' ->
    find_label_in_procedure (globalenv sem) (CS.state_pc s) l = Some pc ->
    find_label_in_procedure (globalenv sem') (CS.state_pc s) l = Some pc.
  Admitted.

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
    simpl in Heq.
    now rewrite <- Heq.
  Qed.

  Lemma imported_procedure_recombination s C P :
    CS.is_program_component s ic ->
    imported_procedure
      (genv_interface (globalenv sem )) (CS.state_component s) C P ->
    imported_procedure
      (genv_interface (globalenv sem')) (CS.state_component s) C P.
  Admitted.

  (* RB: NOTE: The two EntryPoint lemmas can be phrased as a more general one
     operating on an explicit program link, one then being the exact symmetric of
     the other, i.e., its application after communativity of linking. There is a
     choice of encoding of component membership in both cases. *)

  (* Search _ EntryPoint.get. *)
  Lemma genv_entrypoints_recombination_left C P b :
    C \in domm ip ->
    EntryPoint.get C P (genv_entrypoints (globalenv sem )) = Some b ->
    EntryPoint.get C P (genv_entrypoints (globalenv sem')) = Some b.
  Admitted.

  Lemma genv_entrypoints_recombination_right C P b :
    C \in domm ic ->
    EntryPoint.get C P (genv_entrypoints (globalenv sem'')) = Some b ->
    EntryPoint.get C P (genv_entrypoints (globalenv sem' )) = Some b.
  Admitted.

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
    Step sem' (merge_states p c s1 s1'') E0 (merge_states p c s2 s1'').
  Proof.
    intros Hcomp1 Hmerge1 Hstep12.
    (* Derive some useful facts and begin to expose state structure. *)
    inversion Hmergeable_ifaces as [Hlinkable _].
    rewrite (mergeable_states_merge_program
               Hmergeable_ifaces Hifacep Hifacec Hcomp1 Hmerge1).
    pose proof silent_step_preserves_program_component Hcomp1 Hstep12 as Hcomp2.
    pose proof threeway_multisem_mergeable_step_E0 Hcomp1 Hmerge1 Hstep12
      as Hmerge2.
    rewrite (mergeable_states_merge_program
               Hmergeable_ifaces Hifacep Hifacec Hcomp2 Hmerge2).
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
    Star sem'  (merge_states p c s1 s1'') E0 (merge_states p c s2 s2'').
  Proof.
    intros Hcomp1 Hmerge1 Hstar12 Hstar12''.
    pose proof mergeable_states_program_to_program
         Hmergeable_ifaces Hifacep Hifacec Hmerge1 Hcomp1 as Hcomp1'.
    rewrite Hifacec in Hcomp1'.
    pose proof context_epsilon_star_is_silent Hcomp1' Hstar12'' as Hs2'.
    remember E0 as t eqn:Ht.
    revert Ht Hmerge1 Hcomp1 Hcomp1' Hstar12''.
    apply star_iff_starR in Hstar12.
    induction Hstar12 as [s | s1 t1 s2 t2 s3 ? Hstar12 IHstar Hstep23]; subst;
      intros Ht Hmerge1 Hcomp1 Hcomp1' Hstar12'.
    - (* RB: TODO: Follows from Hs2', ideally via a recurring lemma. Compare with
         its role in the inductive step. *)
      (* now apply star_refl. *)
      admit.
    - apply Eapp_E0_inv in Ht. destruct Ht; subst.
      specialize (IHstar (eq_refl _) Hmerge1 Hcomp1 Hcomp1' Hstar12').
      apply star_trans with (t1 := E0) (s2 := merge_states p c s2 s2'') (t2 := E0);
        [assumption | | reflexivity].
      apply star_step with (t1 := E0) (s2 := merge_states p c s3 s2'') (t2 := E0).
      + apply star_iff_starR in Hstar12.
        pose proof threeway_multisem_mergeable_program Hcomp1 Hmerge1 Hstar12 Hstar12'
          as Hmerge2.
        pose proof epsilon_star_preserves_program_component Hcomp1 Hstar12
          as Hcomp2.
        exact (threeway_multisem_step_E0 Hcomp2 Hmerge2 Hstep23).
      + now constructor.
      + reflexivity.
  Admitted.

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

  Lemma threeway_multisem_event_lockstep_program_step s1 s1'' e s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' s1 s1'' ->
    Step sem   s1   [e] s2   ->
    Step sem'' s1'' [e] s2'' ->
    Step sem'  (merge_states p c s1 s1'') [e] (merge_states p c s2 s2'').
  Proof.
    intros Hcomp1 Hmerge1 Hstep12 Hstep12''.
    (* Derive some useful facts and begin to expose state structure. *)
    inversion Hmergeable_ifaces as [Hlinkable _].
    rewrite (mergeable_states_merge_program
               Hmergeable_ifaces Hifacep Hifacec Hcomp1 Hmerge1).
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
      pose proof is_program_component_in_domm Hcomp1 Hmerge1 as Hdomm;
        unfold CS.state_component in Hdomm; simpl in Hdomm;
        rewrite <- Pointer.inc_preserves_component in Hdomm.
      destruct (CS.is_program_component s2copy ic) eqn:Hcomp2.
      + rewrite (mergeable_states_merge_program
                   Hmergeable_ifaces Hifacep Hifacec Hcomp2 Hmerge2).
        unfold mergeable_states_memory, mergeable_states_stack; simpl.
        rewrite (merge_stacks_cons_program
                   Hmergeable_ifaces Hifacep Hifacec _ _ _ Hdomm).
        match goal with
        | Heq : Pointer.component pc1'' = Pointer.component pc1 |- _ =>
          rewrite Heq
        end.
        apply CS.Call; try assumption;
          [
          | admit
          | admit
          ].
        (* Apply linking invariance and solve side goals (very similar to the
           silent case, but slightly different setup). *)
        eapply execution_invariant_to_linking; try eassumption;
          [ congruence
          | apply linkable_implies_linkable_mains; congruence
          | exact (is_program_component_in_domm Hcomp1 Hmerge1)
          ].
      + apply negb_false_iff in Hcomp2.
        rewrite (mergeable_states_merge_context
                   Hmergeable_ifaces Hifacep Hifacec Hcomp2 Hmerge2).
        unfold mergeable_states_memory, mergeable_states_stack; simpl.
        rewrite (merge_stacks_cons_program
                   Hmergeable_ifaces Hifacep Hifacec _ _ _ Hdomm).
        match goal with
        | Heq : Pointer.component pc1'' = Pointer.component pc1 |- _ =>
          rewrite Heq
        end.
        erewrite Register.invalidate_eq with (regs2 := regs1); last congruence.
        apply CS.Call; try assumption;
          [
          | admit
          | admit
          ].
        eapply execution_invariant_to_linking; try eassumption;
          [ congruence
          | apply linkable_implies_linkable_mains; congruence
          | exact (is_program_component_in_domm Hcomp1 Hmerge1)
          ].
    - (* Return: case analysis on return point. *)
      destruct (CS.is_program_component s2copy ic) eqn:Hcomp2.
      + rewrite (mergeable_states_merge_program
                   Hmergeable_ifaces Hifacep Hifacec Hcomp2 Hmerge2).
        unfold mergeable_states_memory, mergeable_states_stack; simpl.
        assert (Hdomm : Pointer.component pc2 \in domm ip) by admit.
        rewrite (merge_stacks_cons_program
                   Hmergeable_ifaces Hifacep Hifacec _ _ _ Hdomm).
        match goal with
        | Heq1 : Pointer.component pc1'' = Pointer.component pc1,
          Heq2 : Pointer.component pc2'' = Pointer.component pc2 |- _ =>
          rewrite Heq1 Heq2
        end.
        apply CS.Return; try congruence. (* [congruence] to cover context case. *)
        eapply execution_invariant_to_linking; try eassumption;
          [ congruence
          | apply linkable_implies_linkable_mains; congruence
          | exact (is_program_component_in_domm Hcomp1 Hmerge1)
          ].
      + apply negb_false_iff in Hcomp2.
        rewrite (mergeable_states_merge_context
                   Hmergeable_ifaces Hifacep Hifacec Hcomp2 Hmerge2).
        unfold mergeable_states_memory, mergeable_states_stack; simpl.
        assert (Hdomm : Pointer.component pc2 \in domm ic) by admit.
        rewrite (merge_stacks_cons_context
                   Hmergeable_ifaces Hifacep Hifacec _ _ _ Hdomm).
        match goal with
        | Heq : Pointer.component pc1'' = Pointer.component pc1 |- _ =>
          rewrite Heq
        end.
        erewrite Register.invalidate_eq with (regs2 := regs1); last congruence.
        apply CS.Return; try congruence.
        eapply execution_invariant_to_linking; try eassumption;
          [ congruence
          | apply linkable_implies_linkable_mains; congruence
          | exact (is_program_component_in_domm Hcomp1 Hmerge1)
          ].
  Admitted.

  Lemma threeway_multisem_event_lockstep_program s1 s1'' e s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' s1 s1'' ->
    Step sem   s1   [e] s2   ->
    Step sem'' s1'' [e] s2'' ->
    Step sem'  (merge_states p c s1 s1'') [e] (merge_states p c s2 s2'') /\
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

  Lemma threeway_multisem_mergeable s1 s1'' t s2 s2'' :
    mergeable_states p c p' c' s1 s1'' ->
    Star sem   s1   t s2   ->
    Star sem'' s1'' t s2'' ->
    mergeable_states p c p' c' s2 s2''.
  Proof.
    intros Hmerg Hstar12 Hstar12''.
    inversion Hmerg
      as [? ? ? Hini Hini'' Hstar Hstar'']; subst.
    econstructor; eauto;
      eapply star_trans; eauto.
  Qed.

  Lemma threeway_multisem_star_E0 s1 s1'' s2 s2'':
    mergeable_states p c p' c' s1 s1'' ->
    Star sem   s1   E0 s2   ->
    Star sem'' s1'' E0 s2'' ->
    Star sem'  (merge_states p c s1 s1'') E0 (merge_states p c s2 s2'').
  Proof.
    intros Hmerg Hstar12 Hstar12''.
    inversion Hmerg
      as [? ? ? Hini Hini'' Hstar Hstar'']; subst.
    (* induction *)
  Admitted. (* RB: NOTE: JT will fill this in. *)

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
    Step sem'  (merge_states p c s1 s1'') [e] (merge_states p c s2 s2'') /\
    mergeable_states p c p' c' s2 s2''.
  Proof.
    intros Hmerge1 Hstep12 Hstep12''.
    destruct (CS.is_program_component s1 ic) eqn:Hcase.
    - now apply threeway_multisem_event_lockstep_program.
    - admit. (* Symmetric case. *)
  Admitted. (* RB: TODO: JT will factor the symmetric proofs. *)

  Theorem threeway_multisem_star_program s1 s1'' t s2 s2'' :
    CS.is_program_component s1 ic ->
    mergeable_states p c p' c' s1 s1'' ->
    Star sem   s1   t s2   ->
    Star sem'' s1'' t s2'' ->
    Star sem'  (merge_states p c s1 s1'') t (merge_states p c s2 s2'').
  Proof.
    simpl in *. intros Hcomp1 Hmerge1 Hstar12. revert s1'' s2'' Hcomp1 Hmerge1.
    apply star_iff_starR in Hstar12.
    induction Hstar12 as [s | s1 t1 s2 t2 s3 ? Hstar12 IHstar12' Hstep23]; subst;
      intros s1'' s2'' Hcomp1 Hmerge1 Hstar12''.
    - exact (context_epsilon_star_merge_states Hmerge1 Hcomp1 Hstar12'').
    - rename s2'' into s3''. rename Hstar12'' into Hstar13''.
      apply (star_app_inv (@CS.singleton_traces _)) in Hstar13''
        as [s2'' [Hstar12'' Hstar23'']].
      specialize (IHstar12' _ _ Hcomp1 Hmerge1 Hstar12'').
      (* Apply instantiated IH and case analyze step trace. *)
      apply star_trans with (t1 := t1) (s2 := merge_states p c s2 s2'') (t2 := t2);
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
    Star (CS.sem (program_link p  c')) (merge_states p c s1 s1'') t (merge_states p c s2 s2'').
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
      setoid_rewrite merge_states_sym at 1 2; try eassumption.
      unfold merge_states. rewrite Hifacep Hifacec.
      apply threeway_multisem_star_program with (p' := c).
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
  Admitted.

  (* RB: NOTE: Here, the existential is explicitly instantiated; the mergeability
     relation is also different than in standard "two-way" simulations. *)
  Theorem match_initial_states s s'' :
    initial_state sem   s   ->
    initial_state sem'' s'' ->
    initial_state sem'  (merge_states p c s s'') /\
    mergeable_states p c p' c' s s''.
  Admitted.

  Theorem match_final_states s s'' :
    mergeable_states p c p' c' s s'' ->
    final_state sem   s   ->
    final_state sem'' s'' ->
    final_state sem'  (merge_states p c s s'').
  Admitted.

  Theorem star_simulation s1 s1'' t s2 s2'' :
    mergeable_states p c p' c' s1 s1'' ->
    Star sem   s1   t s2   ->
    Star sem'' s1'' t s2'' ->
    Star sem'  (merge_states p c s1 s1'') t (merge_states p c s2 s2'') /\
    mergeable_states p c p' c' s2 s2''.
  Proof.
    intros. split.
    - now apply threeway_multisem_star.
    - eapply threeway_multisem_mergeable; eassumption.
  Qed.

  Corollary match_nostep s s'' :
    mergeable_states p c p' c' s s'' ->
    Nostep sem   s   ->
    Nostep sem'' s'' ->
    Nostep sem'  (merge_states p c s s'').
  Admitted.

  Corollary match_nofinal s s'' :
    mergeable_states p c p' c' s s'' ->
    ~ final_state sem   s   ->
    ~ final_state sem'' s'' ->
    ~ final_state sem'  (merge_states p c s s'').
  Admitted.
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
      apply program_runs with (s := merge_states p c s1 s1'');
        first assumption.
      apply state_terminates with (s' := merge_states p c s2 s2'');
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
      apply program_runs with (s := merge_states p c s1 s1'');
        first assumption.
      apply state_goes_wrong with (s' := merge_states p c s2 s2'');
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
