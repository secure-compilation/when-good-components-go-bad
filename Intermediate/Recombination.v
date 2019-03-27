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

Definition merge_states (s s'' : CS.state) : CS.state :=
  s.

Lemma mergeable_states_context_to_program ctx1 ctx2 s1 s2 :
  mergeable_states ctx1 ctx2 s1 s2 ->
  CS.is_context_component s1 ctx1 ->
  CS.is_program_component s2 ctx2.
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

Section ThreewayMultisemProgram.
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

  Theorem threeway_multisem_mergeable_program s1 s1'' t s2 s2'' :
    CS.is_program_component s1 (prog_interface c) ->
    mergeable_states (prog_interface c) (prog_interface p) s1 s1'' ->
    Star (CS.sem (program_link p  c )) s1   t s2   ->
    Star (CS.sem (program_link p' c')) s1'' t s2'' ->
    mergeable_states (prog_interface c) (prog_interface p) s2 s2''.
  Admitted.

  Theorem threeway_multisem_star_program s1 s1'' t s2 s2'' :
    CS.is_program_component s1 (prog_interface c) ->
    mergeable_states (prog_interface c) (prog_interface p) s1 s1'' ->
    Star (CS.sem (program_link p  c )) s1   t s2   ->
    Star (CS.sem (program_link p' c')) s1'' t s2'' ->
    Star (CS.sem (program_link p  c')) (merge_states s1 s1'') t (merge_states s2 s2'').
  Admitted.
End ThreewayMultisemProgram.

Section ThreewayMultisem.
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
        last admit.
      apply threeway_multisem_star_program with (c := p') (p' := c).
  Admitted.
End ThreewayMultisem.

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
