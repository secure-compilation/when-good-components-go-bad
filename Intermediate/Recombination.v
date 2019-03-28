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
  Definition merge_frames (f f'' : Pointer.t) :=
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

(* An "extensional" reading of program states a la Composition.
   RB: TODO: If the number, organization and order of parameters is confusing,
   look at alternatives, here and in the sections that use this. *)
Inductive mergeable_states (ic ip : Program.interface) (s s'' : CS.state)
  : Prop :=
  mergeable_states_intro : forall p c p' c' s0 s0'' t,
    mergeable_interfaces ip ic ->
    prog_interface p = ip ->
    prog_interface c = ic ->
    prog_interface p' = ip ->
    prog_interface c' = ic ->
    initial_state (CS.sem (program_link p  c )) s0   ->
    initial_state (CS.sem (program_link p' c')) s0'' ->
    Star (CS.sem (program_link p  c )) s0   t s   ->
    Star (CS.sem (program_link p' c')) s0'' t s'' ->
    mergeable_states ic ip s s''.

Definition merge_states (ic ip : Program.interface) (s s'' : CS.state)
  : CS.state :=
  PS.unpartialize (PS.merge_partial_states (PS.partialize s   ic)
                                           (PS.partialize s'' ip)).

Lemma mergeable_states_context_to_program ctx1 ctx2 s1 s2 :
  mergeable_states ctx1 ctx2 s1 s2 ->
  CS.is_context_component s1 ctx1 ->
  CS.is_program_component s2 ctx2.
Admitted.

Lemma mergeable_states_program_to_context ctx1 ctx2 s1 s2 :
  mergeable_states ctx1 ctx2 s1 s2 ->
  CS.is_program_component s1 ctx1 ->
  CS.is_context_component s2 ctx2.
Admitted.

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

  (* RB: NOTE: The structure follows closely that of
     threeway_multisem_star_program. *)
  Theorem threeway_multisem_mergeable_program s1 s1'' t s2 s2'' :
    CS.is_program_component s1 (prog_interface c) ->
    mergeable_states (prog_interface c) (prog_interface p) s1 s1'' ->
    Star (CS.sem (program_link p  c )) s1   t s2   ->
    Star (CS.sem (program_link p' c')) s1'' t s2'' ->
    mergeable_states (prog_interface c) (prog_interface p) s2 s2''.
  Admitted.

  Theorem threeway_multisem_star_E0_program s1 s1'' s2 s2'':
    CS.is_program_component s1 (prog_interface c) ->
    mergeable_states (prog_interface c) (prog_interface p) s1 s1'' ->
    Star (CS.sem (program_link p  c )) s1   E0 s2   ->
    Star (CS.sem (program_link p' c')) s1'' E0 s2'' ->
    Star (CS.sem (program_link p  c')) (merge_states s1 s1'') E0 (merge_states s2 s2'').
  Admitted.
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

  Lemma threeway_multisem_mergeable s1 s1'' t s2 s2'' :
    mergeable_states (prog_interface c) (prog_interface p) s1 s1'' ->
    Star (CS.sem (program_link p  c )) s1   t s2   ->
    Star (CS.sem (program_link p' c')) s1'' t s2'' ->
    mergeable_states (prog_interface c) (prog_interface p) s2 s2''.
  Admitted. (* Grade 1. *)

  Lemma threeway_multisem_star_E0 s1 s1'' s2 s2'':
    mergeable_states (prog_interface c) (prog_interface p) s1 s1'' ->
    Star (CS.sem (program_link p  c )) s1   E0 s2   ->
    Star (CS.sem (program_link p' c')) s1'' E0 s2'' ->
    Star (CS.sem (program_link p  c')) (merge_states s1 s1'') E0 (merge_states s2 s2'').
  Admitted. (* Grade 1. *)

  Theorem threeway_multisem_star_program s1 s1'' t s2 s2'' :
    CS.is_program_component s1 (prog_interface c) ->
    mergeable_states (prog_interface c) (prog_interface p) s1 s1'' ->
    Star (CS.sem (program_link p  c )) s1   t s2   ->
    Star (CS.sem (program_link p' c')) s1'' t s2'' ->
    Star (CS.sem (program_link p  c')) (merge_states s1 s1'') t (merge_states s2 s2'').
  Proof.
    simpl in *. intros Hcomp1 Hmerge1 Hstar12. revert s1'' s2'' Hcomp1 Hmerge1.
    apply star_iff_starR in Hstar12.
    induction Hstar12 as [s | s1 t1 s2 t2 s3 ? Hstar12 IHstar12' Hstep23]; subst;
      intros s1'' s2'' Hcomp1 Hmerge1 Hstar12''.
    - (* RB: TODO: We need a multi-semantics counterpart of PS context stars. *)
      (* pose proof PS.context_epsilon_star_is_silent Hcomp1' Hstar12'; subst s2'. *)
      (* now apply star_refl. *)
      admit.
    - rename s2'' into s3''. rename Hstar12'' into Hstar13''.
      apply (star_app_inv (@CS.singleton_traces _)) in Hstar13''
        as [s2'' [Hstar12'' Hstar23'']].
      specialize (IHstar12' _ _ Hcomp1 Hmerge1 Hstar12'').
      (* Apply instantiated IH and case analyze step trace. *)
      apply star_trans with (t1 := t1) (s2 := merge_states s2 s2'') (t2 := t2);
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
        (* RB: TODO: Here is where we depart from the multi-semantics and need to
           furnish our own version. We may save effort if, as is the case here, we only
           need to concern ourselves with visible steps. *)
        (* pose proof MultiSem.multi_step (prepare_global_env prog) Hstep23 Hstep23' *)
        (*   as Hmstep2. *)
        assert (Step (CS.sem (program_link p c'))
                     (merge_states s2 s2''1) [e2] (merge_states s3 s2''2))
          as Hstep23' by admit.
        (* Propagate mergeability, suffix star. *)
        (* pose proof MultiSem.mergeable_states_step_trans *)
        (*      wf1 wf2 main_linkability linkability mergeable_interfaces *)
        (*      Hmerge21 Hstep23 Hstep23' as Hmerge22. *)
        assert (mergeable_states (prog_interface c) (prog_interface p) s3 s2''2)
          as Hmerge22 by admit.
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
  Admitted.
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

  (* RB: NOTE: At the moment, this becomes the old threeway_multisem_star. *)
  Theorem threeway_multisem_star_simulation s1 s1'' t s2 s2'' :
    mergeable_states (prog_interface c) (prog_interface p) s1 s1'' ->
    Star (CS.sem (program_link p  c )) s1   t s2   ->
    Star (CS.sem (program_link p' c')) s1'' t s2'' ->
    Star (CS.sem (program_link p  c')) (merge_states s1 s1'') t (merge_states s2 s2'').
    (* /\ mergeable_states ip ic s2 s2'' *)
  Proof.
    intros Hmerge1 Hstar12 Hstar12''.
    destruct (CS.is_program_component s1 (prog_interface c)) eqn:Hcomp1.
    - now apply threeway_multisem_star_program.
    - apply negb_false_iff in Hcomp1.
      apply (mergeable_states_context_to_program Hmerge1) in Hcomp1.
      rewrite program_linkC; try assumption;
        last admit. (* Easy. *)
      apply threeway_multisem_star_program with (c := p') (p' := c);
        admit. (* Easy. *)
  Admitted. (* Grade 1. *)
End ThreewayMultisem3.

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

  (* RB: NOTE: Relocate lemmas on initial states when ready. *)
  Theorem initial_states_mergeability s s'' :
    initial_state (CS.sem (program_link p  c )) s   ->
    initial_state (CS.sem (program_link p' c')) s'' ->
    mergeable_states (prog_interface c) (prog_interface p) s s''.
  Admitted.

  (* RB: NOTE: Relocate lemmas on initial states when ready. *)
  Lemma initial_state_merge_after_linking s s'' :
    initial_state (CS.sem (program_link p  c )) s   ->
    initial_state (CS.sem (program_link p' c')) s'' ->
    initial_state (CS.sem (program_link p  c')) (merge_states s s'').
  Admitted.

  (* RB: NOTE: Possible improvements:
      - Get rid of asserts in FTbc case. (RB: TODO: Assigned to JT.)
      - Try to refactor case analysis in proof. *)
  Theorem recombination_prefix m :
    does_prefix (CS.sem (program_link p  c )) m ->
    does_prefix (CS.sem (program_link p' c')) m ->
    does_prefix (CS.sem (program_link p  c')) m.
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
      pose proof initial_states_mergeability Hini1 Hini1'' as Hmerge1.
      destruct (threeway_multisem_star_simulation Hmerge1 Hstar12 Hstar12'')
        as [s1' [s2' [Hs1' [Hs2' Hstar12']]]].
      apply program_runs with (s := s1'); first easy.
      apply state_terminates with (s' := s2'); easy.
    - destruct b   as [? | ? | ? | t  ]; try contradiction.
      destruct b'' as [? | ? | ? | t'']; try contradiction.
      simpl in Hprefix, Hprefix''. subst t t''.
      inversion Hst_beh   as [| | | ? s2   Hstar12   Hstep2   Hfinal2  ]; subst.
      inversion Hst_beh'' as [| | | ? s2'' Hstar12'' Hstep2'' Hfinal2'']; subst.
      exists (Goes_wrong tm). split; last reflexivity.
      pose proof initial_states_mergeability Hini1 Hini1'' as Hmerge1.
      destruct (threeway_multisem_star_simulation Hmerge1 Hstar12 Hstar12'')
        as [s1' [s2' [Hs1' [Hs2' Hstar12']]]].
      apply program_runs with (s := s1'); first easy.
      apply state_goes_wrong with (s' := s2'); easy.
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
      pose proof initial_states_mergeability Hini1_ Hini1''_ as Hmerge1.
      destruct (threeway_multisem_star_simulation Hmerge1 Hstar12 Hstar12'')
        as [ss1' [ss2' [Hss1' [Hss2' Hstar12']]]].
      eapply program_behaves_finpref_exists; last now apply Hstar12'.
      now destruct (initial_state_merge_after_linking Hini1 Hini1'').
  Qed.
End Recombination.
