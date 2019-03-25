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

Section BehaviorStar.
  Variables p c: program.

  Hypothesis wf1 : well_formed_program p.
  Hypothesis wf2 : well_formed_program c.

  Hypothesis mergeable_interfaces:
    mergeable_interfaces (prog_interface p) (prog_interface c).

  (* Hypothesis linkability: linkable (prog_interface p) (prog_interface c). *)
  Hypothesis main_linkability: linkable_mains p c.

  Hypothesis prog_is_closed:
    closed_program (program_link p c).

  (* RB: Could be phrased in terms of does_prefix. *)
  Theorem behavior_prefix_star b m :
    program_behaves (CS.sem (program_link p c)) b ->
    prefix m b ->
  exists s1 s2,
    CS.initial_state (program_link p c) s1 /\
    Star (CS.sem (program_link p c)) s1 (finpref_trace m) s2.
  Admitted.
End BehaviorStar.

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

  Inductive mergeable_states (iface1 iface2 : Program.interface) (s1 s2 : CS.state) : Prop.

  Definition merge_states (s1 s2 : CS.state) : option CS.state :=
    None.

  Theorem initial_states_mergeability s s'' :
    initial_state (CS.sem (program_link p  c )) s   ->
    initial_state (CS.sem (program_link p' c')) s'' ->
    mergeable_states (prog_interface p) (prog_interface c) s s''.
  Admitted.

  Lemma initial_state_merge_after_linking s s'' :
    initial_state (CS.sem (program_link p  c )) s   ->
    initial_state (CS.sem (program_link p' c')) s'' ->
  exists s',
    merge_states s s'' = Some s' /\
    initial_state (CS.sem (program_link p  c')) s'.
  Admitted.

  Theorem threeway_multisem_star_simulation s1 s1'' t s2 s2'' :
    mergeable_states (prog_interface p) (prog_interface c) s1 s1'' ->
    Star (CS.sem (program_link p  c )) s1   t s2   ->
    Star (CS.sem (program_link p' c')) s1'' t s2'' ->
  exists s1' s2',
    merge_states s1 s1'' = Some s1' /\
    merge_states s2 s2'' = Some s2' /\
    Star (CS.sem (program_link p  c')) s1' t s2'.
    (* /\ mergeable_states ip ic s2 s2'' *)
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
        destruct
          (behavior_prefix_star
             Hwfp Hwfc Hmergeable_ifaces Hmain_linkability Hprog_is_closed
             Hbeh Hprefix)
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
        destruct
          (behavior_prefix_star
             Hwfp' Hwfc' Hmergeable_ifaces Hmain_linkability' Hprog_is_closed'
             Hbeh'' Hprefix'')
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
