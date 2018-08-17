Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.

Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Linking.
Require Import Common.Blame.
Require Import Common.CompCertExtensions.

(* CH: Ideally all these imports would move to a different file
       together with the actual instances, see next comment below. *)
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Source.PS.
Require Import Intermediate.Machine.
Require Import Intermediate.PS.
Require Import Intermediate.Decomposition.
Require Import Intermediate.Composition.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import Definability.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* RB: Eventually, we may not want have these interfaces distracting from
       the high-level proof here.
   [CH: These interfaces explain the proved statement in a
        (relatively) self-contained way, so I don't see them as
        distractions! I think what should move to a different file are
        the instantiations of these parameters and hypotheses together
        with all the concrete imports at the top. This should be
        possible once the few abstraction leaks are fixed.]

   The repetition verbatim of theorem statements as axioms is particularly
   annoying; we will want to eliminate this duplication.
     [CH: Agreed, but easy to fix with some extra definitions.]

   Naming conventions can also be harmonized.

   The current proof is generic while still relying on our Common and
   CompCert's infrastructure. [CH: I find this just fine.] *)

(* CH: It seemed a bit strange that Program.interface is used
       concretely, instead of being just another parameter below.
       Same for linkable. It seems related to using everything in
       Common though, and so it's just fine for now. *)

Module Type Source_Sig.
  Parameter program : Type.

  Parameter prog_interface : program -> Program.interface.

  Parameter well_formed_program : program -> Prop.

  Parameter closed_program : program -> Prop.

  Parameter linkable_mains : program -> program -> Prop.

  Hypothesis linkable_mains_sym : forall prog1 prog2,
    linkable_mains prog1 prog2 ->
    linkable_mains prog2 prog1.

  Hypothesis linkable_disjoint_mains: forall prog1 prog2,
    well_formed_program prog1 ->
    well_formed_program prog2 ->
    linkable (prog_interface prog1) (prog_interface prog2) ->
    linkable_mains prog1 prog2.

  Parameter program_link : program -> program -> program.

  Hypothesis linking_well_formedness : forall p1 p2,
    well_formed_program p1 ->
    well_formed_program p2 ->
    linkable (prog_interface p1) (prog_interface p2) ->
    well_formed_program (program_link p1 p2).

  Hypothesis interface_preserves_closedness_l : forall p1 p2 p1',
    closed_program (program_link p1 p2) ->
    prog_interface p1 = prog_interface p1' ->
    well_formed_program p1 ->
    well_formed_program p1' ->
    closed_program (program_link p1' p2).

  Module CS.
    Parameter sem : program -> semantics.
  End CS.

  Hypothesis blame_program : forall p Cs t' P' m,
    well_formed_program p ->
    well_formed_program Cs ->
    linkable (prog_interface p) (prog_interface Cs) ->
    closed_program (program_link p Cs) ->
    program_behaves (CS.sem (program_link p Cs)) (Goes_wrong t') ->
    well_formed_program P' ->
    prog_interface P' = prog_interface p ->
    closed_program (program_link P' Cs) ->
    program_behaves (CS.sem (program_link P' Cs)) (Terminates (finpref_trace m)) ->
    not_wrong_finpref m ->
    trace_finpref_prefix t' m ->
    undef_in t' (prog_interface p).

End Source_Sig.

Module Source_Instance <: Source_Sig.
  Definition program :=
    @Source.program.

  Definition prog_interface :=
    @Source.prog_interface.

  Definition well_formed_program :=
    @Source.well_formed_program.

  Definition closed_program :=
    @Source.closed_program.

  Definition linkable_mains :=
    @Source.linkable_mains.

  Definition linkable_mains_sym :=
    @Source.linkable_mains_sym.

  Definition linkable_disjoint_mains :=
    @Source.linkable_disjoint_mains.

  Definition program_link :=
    @Source.program_link.

  Definition linking_well_formedness :=
    @Source.linking_well_formedness.

  Definition interface_preserves_closedness_l :=
    @Source.interface_preserves_closedness_l.

  Module CS.
    Definition sem :=
      @Source.CS.CS.sem.
  End CS.

  Definition blame_program :=
    @Source.PS.PS.blame_program.

End Source_Instance.

(* CH: The number of different well-formedness conditions seems a bit
       out of control here. *)

Module Type Intermediate_Sig.
  Parameter program : Type.

  Parameter prog_interface : program -> Program.interface.

  Parameter well_formed_program : program -> Prop.

  Parameter closed_program : program -> Prop.

  Parameter linkable_mains : program -> program -> Prop.

  Parameter matching_mains : program -> program -> Prop.

  Parameter program_link : program -> program -> program.

  Hypothesis linkable_mains_sym : forall p1 p2,
    linkable_mains p1 p2 -> linkable_mains p2 p1.

  Hypothesis program_linkC : forall p1 p2,
    well_formed_program p1 ->
    well_formed_program p2 ->
    linkable (prog_interface p1) (prog_interface p2) ->
    program_link p1 p2 = program_link p2 p1.

  Hypothesis linking_well_formedness : forall p1 p2,
    well_formed_program p1 ->
    well_formed_program p2 ->
    linkable (prog_interface p1) (prog_interface p2) ->
    well_formed_program (program_link p1 p2).

  Hypothesis interface_preserves_closedness_r : forall p1 p2 p2',
    well_formed_program p1 ->
    well_formed_program p2' ->
    prog_interface p2 = prog_interface p2' ->
    linkable (prog_interface p1) (prog_interface p2) ->
    closed_program (program_link p1 p2) ->
    linkable_mains p1 p2 ->
    matching_mains p2 p2' ->
    closed_program (program_link p1 p2').

  Module CS.
    Parameter sem : program -> semantics.
  End CS.

  Module PS.
    Parameter sem : program -> Program.interface -> semantics.
  End PS.

  Hypothesis decomposition_with_safe_behavior:
    forall p c,
      well_formed_program p ->
      well_formed_program c ->
      linkable (prog_interface p) (prog_interface c) ->
      linkable_mains p c ->
    forall beh,
      program_behaves (CS.sem (program_link p c)) beh ->
      not_wrong beh ->
      program_behaves (PS.sem p (prog_interface c)) beh.

  Hypothesis decomposition_with_refinement :
    forall p c,
      well_formed_program p ->
      well_formed_program c ->
      linkable (prog_interface p) (prog_interface c) ->
      linkable_mains p c ->
    forall beh1,
      program_behaves (CS.sem (program_link p c)) beh1 ->
    exists beh2,
      program_behaves (PS.sem p (prog_interface c)) beh2 /\
      behavior_improves beh1 beh2.

  Hypothesis composition_prefix :
    forall p c,
      well_formed_program p ->
      well_formed_program c ->
      linkable_mains p c ->
      closed_program (program_link p c) ->
      mergeable_interfaces (prog_interface p) (prog_interface c) ->
    forall b1 b2 m,
      program_behaves (PS.sem p (prog_interface c)) b1 ->
      program_behaves (PS.sem c (prog_interface p)) b2 ->
      prefix m b1 ->
      prefix m b2 ->
    exists b3,
      program_behaves (CS.sem (program_link p c)) b3 /\ prefix m b3.

  Hypothesis compose_mergeable_interfaces :
    forall p c,
      linkable (prog_interface p) (prog_interface c) ->
      closed_program (program_link p c) ->
      mergeable_interfaces (prog_interface p) (prog_interface c).
End Intermediate_Sig.

Module Intermediate_Instance <: Intermediate_Sig.
  Definition program :=
    @Intermediate.program.

  Definition prog_interface :=
    @Intermediate.prog_interface.

  Definition well_formed_program :=
    @Intermediate.well_formed_program.

  Definition closed_program :=
    @Intermediate.closed_program.

  Definition linkable_mains :=
    @Intermediate.linkable_mains.

  Definition matching_mains :=
    @Intermediate.matching_mains.

  Definition program_link :=
    @Intermediate.program_link.

  Definition linkable_mains_sym :=
    @Intermediate.linkable_mains_sym.

  Definition program_linkC :=
    @Intermediate.program_linkC.

  Definition linking_well_formedness :=
    @Intermediate.linking_well_formedness.

  Definition interface_preserves_closedness_r :=
    @Intermediate.interface_preserves_closedness_r.

  Module CS.
    Definition sem :=
      @Intermediate.CS.CS.sem.
  End CS.

  Module PS.
    Definition sem :=
      @Intermediate.PS.PS.sem.
    End PS.

  Definition decomposition_with_safe_behavior :=
    @Intermediate.Decomposition.decomposition_with_safe_behavior.

  Definition decomposition_with_refinement :=
    @Intermediate.Decomposition.decomposition_with_refinement.

  Definition composition_prefix :=
    @Intermediate.Composition.composition_prefix.

  Definition compose_mergeable_interfaces :=
    @Intermediate.compose_mergeable_interfaces.
End Intermediate_Instance.

Module Type S2I_Sig (Source : Source_Sig) (Intermediate : Intermediate_Sig).
  Parameter matching_mains : Source.program -> Intermediate.program -> Prop.

  Hypothesis matching_mains_equiv : forall p1 p2 p3,
    matching_mains p1 p2 ->
    matching_mains p1 p3 ->
    Intermediate.matching_mains p2 p3.
End S2I_Sig.

Module S2I_Instance <: S2I_Sig (Source_Instance) (Intermediate_Instance).
  Definition matching_mains :=
    @S2I.Definitions.matching_mains.

  Definition matching_mains_equiv :=
    @S2I.Definitions.matching_mains_equiv.
End S2I_Instance.

Module Type Linker_Sig
       (Source : Source_Sig)
       (Intermediate : Intermediate_Sig)
       (S2I : S2I_Sig Source Intermediate).
  Hypothesis definability_with_linking :
    forall p c b m,
      Intermediate.well_formed_program p ->
      Intermediate.well_formed_program c ->
      linkable (Intermediate.prog_interface p) (Intermediate.prog_interface c) ->
      Intermediate.closed_program (Intermediate.program_link p c) ->
      program_behaves (Intermediate.CS.sem (Intermediate.program_link p c)) b ->
      prefix m b ->
      not_wrong_finpref m ->
    exists p' c',
      Source.prog_interface p' = Intermediate.prog_interface p /\
      Source.prog_interface c' = Intermediate.prog_interface c /\
      S2I.matching_mains p' p /\
      S2I.matching_mains c' c /\
      Source.well_formed_program p' /\
      Source.well_formed_program c' /\
      Source.closed_program (Source.program_link p' c') /\
      program_behaves (Source.CS.sem (Source.program_link p' c')) (Terminates (finpref_trace m)) /\
      prefix m (Terminates (finpref_trace m)).
  (* CH: Do we really need to expose the `Terminates (finpref_trace m)`
         part here? It might hold for our instance, but I don't
         think the proof below needs it. *)
End Linker_Sig.

Module Linker_Instance <: Linker_Sig (Source_Instance)
                                     (Intermediate_Instance)
                                     (S2I_Instance).
  Definition definability_with_linking :=
    @RobustImp.Source.Definability.definability_with_linking.
End Linker_Instance.

Module Type Compiler_Sig
       (Source : Source_Sig)
       (Intermediate : Intermediate_Sig)
       (S2I : S2I_Sig Source Intermediate).
  Parameter compile_program : Source.program -> option Intermediate.program.

  Hypothesis well_formed_compilable :
    forall p,
      Source.well_formed_program p ->
    exists pc,
      compile_program p = Some pc.

  Hypothesis compilation_preserves_well_formedness : forall p p_compiled,
    Source.well_formed_program p ->
    compile_program p = Some p_compiled ->
    Intermediate.well_formed_program p_compiled.

  Hypothesis compilation_preserves_interface : forall p p_compiled,
    compile_program p = Some p_compiled ->
    Intermediate.prog_interface p_compiled = Source.prog_interface p.

  Hypothesis compilation_preserves_linkability : forall p p_compiled c c_compiled,
    Source.well_formed_program p ->
    Source.well_formed_program c ->
    linkable (Source.prog_interface p) (Source.prog_interface c) ->
    compile_program p = Some p_compiled ->
    compile_program c = Some c_compiled ->
    linkable (Intermediate.prog_interface p_compiled) (Intermediate.prog_interface c_compiled).

  Hypothesis compilation_preserves_linkable_mains : forall p1 p1' p2 p2',
    Source.well_formed_program p1 ->
    Source.well_formed_program p2 ->
    Source.linkable_mains p1 p2 ->
    compile_program p1 = Some p1' ->
    compile_program p2 = Some p2' ->
    Intermediate.linkable_mains p1' p2'.

  Hypothesis compilation_has_matching_mains : forall p p_compiled,
    Source.well_formed_program p ->
    compile_program p = Some p_compiled ->
    S2I.matching_mains p p_compiled.

  Hypothesis separate_compilation_weaker :
    forall p c pc_comp p_comp c_comp,
      Source.well_formed_program p ->
      Source.well_formed_program c ->
      linkable (Source.prog_interface p) (Source.prog_interface c) ->
      compile_program p = Some p_comp ->
      compile_program c = Some c_comp ->
      compile_program (Source.program_link p c) = Some pc_comp ->
    forall b : program_behavior,
      program_behaves (Intermediate.CS.sem pc_comp) b <->
      program_behaves (Intermediate.CS.sem (Intermediate.program_link p_comp c_comp)) b.

  Hypothesis I_simulates_S :
    forall p,
      Source.closed_program p ->
      Source.well_formed_program p ->
    forall tp,
      compile_program p = Some tp ->
      forward_simulation (Source.CS.sem p) (Intermediate.CS.sem tp).

  Hypothesis S_simulates_I:
    forall p,
      Source.closed_program p ->
      Source.well_formed_program p ->
    forall tp,
      compile_program p = Some tp ->
      backward_simulation (Source.CS.sem p) (Intermediate.CS.sem tp).
End Compiler_Sig.

Module Compiler_Instance <: Compiler_Sig Source_Instance
                                         Intermediate_Instance
                                         S2I_Instance.
  Definition compile_program :=
    @Compiler.compile_program.

  Definition matching_mains :=
    @S2I.Definitions.matching_mains.

  Definition matching_mains_trans :=
    @S2I.Definitions.matching_mains_trans.

  Definition well_formed_compilable :=
    @Compiler.well_formed_compilable.

  Definition compilation_preserves_well_formedness :=
    @Compiler.compilation_preserves_well_formedness.

  Definition compilation_preserves_interface :=
    @Compiler.compilation_preserves_interface.

  Definition compilation_preserves_linkability :=
    @Compiler.compilation_preserves_linkability.

  Definition compilation_preserves_linkable_mains :=
    @Compiler.compilation_preserves_linkable_mains.

  Definition compilation_has_matching_mains :=
    @Compiler.compilation_has_matching_mains.

  Definition separate_compilation_weaker :=
    @Compiler.separate_compilation_weaker.

  Definition I_simulates_S :=
    @Compiler.I_simulates_S.

  Definition S_simulates_I :=
    @Compiler.S_simulates_I.
End Compiler_Instance.

Module RSC_DC_MD_Gen
       (Source : Source_Sig)
       (Intermediate : Intermediate_Sig)
       (S2I : S2I_Sig Source Intermediate)
       (Compiler : Compiler_Sig Source Intermediate S2I)
       (Linker : Linker_Sig Source Intermediate S2I).

(* CH: We should actually introduce a definition for
       does_prefix and use it everywhere where it's
       possible, instead of unfolding it everywhere. *)
Definition does_prefix x m := exists b, program_behaves x b /\ prefix m b.
(* CH: Alternatively could define this in terms of Star and prove the
       predicate above as an alternative characterization. *)

(* CH: Here is a weaker assumption we should try to use in the
       proof below to closer match the paper argument. Here is a proof
       that it's indeed weaker than decomposition_with_refinement, so
       obtaining it for our instance is not an issue. *)
Lemma decomposition_prefix :
  forall p c m,
    Intermediate.well_formed_program p ->
    Intermediate.well_formed_program c ->
    linkable (Intermediate.prog_interface p) (Intermediate.prog_interface c) ->
    Intermediate.linkable_mains p c ->
    not_wrong_finpref m -> (* needed here, and will have it in main proof *)
    does_prefix (Intermediate.CS.sem (Intermediate.program_link p c)) m ->
    does_prefix (Intermediate.PS.sem p (Intermediate.prog_interface c)) m.
Proof.
  intros p c m Hwfp Hwfc Hl Hlm Hmsafe [b1 [Hb1 Hm]].
  destruct (Intermediate.decomposition_with_refinement Hwfp Hwfc Hl Hlm Hb1)
    as [b2 [Hb2 H12]].
  exists b2. split. exact Hb2.
  unfold behavior_improves in H12. destruct H12 as [|[t [H1 H2]]]; subst. assumption.
  unfold prefix in Hm. destruct m as [| t' | t']. tauto. simpl in Hmsafe; tauto.
  eapply behavior_prefix_goes_wrong_trans; eassumption.
Qed.

(* CH: Here is are other weaker assumptions we should try to use in
       the proof below to closer match the paper argument. *)

Lemma forward_simulation_same_safe_prefix:
  forall p p_compiled m,
    Source.closed_program p ->
    Source.well_formed_program p ->
    does_prefix (Source.CS.sem p) m ->
    not_wrong_finpref m ->
    Compiler.compile_program p = Some p_compiled ->
    does_prefix (Intermediate.CS.sem p_compiled) m.
Proof.
  intros p p_compiled m Hcp Hwfp [b [Hb Hmb]] Hsafem Hcmp.
  assert(Hbs : forward_simulation (Source.CS.sem p) (Intermediate.CS.sem p_compiled)).
    apply Compiler.I_simulates_S; assumption.
  apply (forward_simulation_behavior_improves Hbs) in Hb. clear Hbs.
  destruct Hb as [b' [Hb' [Hbb' | [t [H1 H2]]]]]; unfold does_prefix.
  - exists b. split; [| tauto]. subst. assumption.
  - exists b'. split. assumption. subst.
    destruct m as [| ? ?| t']; simpl in Hmb, Hsafem. tauto. tauto.
    simpl. eapply behavior_prefix_goes_wrong_trans; eassumption.
Qed.

Definition behavior_improves_finpref b m :=
  exists t, b = Goes_wrong t /\ trace_finpref_prefix t m.

Lemma backward_simulation_behavior_improves_prefix :
  forall p p_compiled m,
    Source.closed_program p ->
    Source.well_formed_program p ->
    Compiler.compile_program p = Some p_compiled ->
    does_prefix (Intermediate.CS.sem p_compiled) m ->
  exists b,
    program_behaves (Source.CS.sem p) b /\
    (prefix m b \/ behavior_improves_finpref b m).
Proof.
  intros p p_compiled m Hcp Hwfp Hcmp [b [Hb Hmb]].
  assert(Hbs : backward_simulation (Source.CS.sem p) (Intermediate.CS.sem p_compiled)).
    apply Compiler.S_simulates_I; assumption.
  apply (backward_simulation_behavior_improves Hbs) in Hb. clear Hbs.
  destruct Hb as [b' [Hb' Hb'b]]. exists b'. split. assumption.
  destruct Hb'b as [Hb'b | [t [Hb't Htb]]].
  - left. now subst.
  - unfold behavior_improves_finpref. subst b'.
    (* right. exists t. split. assumption. -- committing too early *)
    (* we start by combining behavior_prefix t b and prefix m b to get
       that t and m must be in the prefix relation one way or the other *)
    eapply behavior_prefix_comp' in Htb; [| exact Hmb].
    destruct Htb.
    + left. destruct m as [| |t']; simpl in H. tauto. tauto. simpl.
      destruct H as [t'' ?]. subst.
      exists (Goes_wrong t''). reflexivity.
    + right. exists t. split. reflexivity. assumption.
Qed.

Definition behavior_improves_blame b m p :=
  exists t, b = Goes_wrong t /\ trace_finpref_prefix t m /\
             undef_in t (Source.prog_interface p).

Section RSC_DC_MD_Section.
  Variable p: Source.program.
  Variable p_compiled: Intermediate.program.
  Variable Ct: Intermediate.program.

  (* Some reasonable assumptions about our programs *)

  Hypothesis well_formed_p : Source.well_formed_program p.
  Hypothesis successful_compilation : Compiler.compile_program p = Some p_compiled.
  Hypothesis well_formed_Ct : Intermediate.well_formed_program Ct.
  Hypothesis linkability : linkable (Source.prog_interface p) (Intermediate.prog_interface Ct).
  Hypothesis closedness :
    Intermediate.closed_program (Intermediate.program_link p_compiled Ct).
  Hypothesis mains : Intermediate.linkable_mains p_compiled Ct.

  (* Main Theorem *)

  Theorem RSC_DC_MD:
    forall m,
      does_prefix (Intermediate.CS.sem (Intermediate.program_link p_compiled Ct)) m ->
      not_wrong_finpref m -> 
    exists Cs beh,
      Source.prog_interface Cs = Intermediate.prog_interface Ct /\
      Source.well_formed_program Cs /\
      linkable (Source.prog_interface p) (Source.prog_interface Cs) /\
      Source.closed_program (Source.program_link p Cs) /\
      program_behaves (Source.CS.sem (Source.program_link p Cs)) beh /\
      (prefix m beh \/ behavior_improves_blame beh m p).
  Proof.
    intros m [t [Hbeh Hprefix0]] Hsafe_pref.

    (* Some auxiliary results. *)
    pose proof
      Compiler.compilation_preserves_well_formedness well_formed_p successful_compilation
      as well_formed_p_compiled.

    assert (linkability_pcomp_Ct :
              linkable (Intermediate.prog_interface p_compiled)
                       (Intermediate.prog_interface Ct)).
    {
      assert (sound_interface_p_Ct : sound_interface (unionm (Source.prog_interface p)
                                                             (Intermediate.prog_interface Ct)))
        by apply linkability.
      assert (fdisjoint_p_Ct : fdisjoint (domm (Source.prog_interface p))
                                         (domm (Intermediate.prog_interface Ct)))
        by apply linkability.
      constructor;
        apply Compiler.compilation_preserves_interface in successful_compilation;
        now rewrite successful_compilation.
    }

     assert (H_doesm: does_prefix (Intermediate.CS.sem (Intermediate.program_link p_compiled Ct)) m)
     by now exists t. 

    (* intermediate decomposition (for p_compiled) *)
    pose proof decomposition_prefix 
      well_formed_p_compiled well_formed_Ct linkability_pcomp_Ct mains
      Hsafe_pref H_doesm  as HP_decomp.

    (* CH: if we had undefined behavior above we would use this *)
    (* destruct (@decomposition_with_refinement p_compiled Ct *)
    (*             well_formed_p_compiled well_formed_Ct linkability_pcomp_Ct Hbeh) *)
    (*   as [beh' [Hbeh' Hbeh_improves]]. *)

    (* definability *)
    destruct (Linker.definability_with_linking
                well_formed_p_compiled well_formed_Ct
                linkability_pcomp_Ct closedness Hbeh Hprefix0 Hsafe_pref)
      as [P' [Cs
         [Hsame_iface1 [Hsame_iface2
         [Hmatching_mains_P'_p_compiled [Hmatching_mains_Cs_Ct
         [well_formed_P' [well_formed_Cs [HP'Cs_closed [HP'_Cs_beh Hprefix1]]]]]]]]]].

    move: HP'_Cs_beh Hprefix1.
    set beh := Terminates _.
    move=> HP'_Cs_beh Hprefix1.

    assert (Source.linkable_mains P' Cs) as HP'Cs_mains.
    { apply Source.linkable_disjoint_mains; trivial; congruence. }

    (* FCC *)

    (* the definability output can be split in two programs *)
    (* probably need partialize to obtain them *)

    (* At this point, we compile P' and Cs and establish their basic properties. *)
    destruct (Compiler.well_formed_compilable well_formed_P') as [P'_compiled HP'_compiles].
    pose proof Compiler.compilation_preserves_well_formedness well_formed_P' HP'_compiles
      as well_formed_P'_compiled.
    destruct (Compiler.well_formed_compilable well_formed_Cs) as [Cs_compiled HCs_compiles].
    pose proof Compiler.compilation_preserves_well_formedness well_formed_Cs HCs_compiles
      as well_formed_Cs_compiled.
    assert
      (linkable
         (Intermediate.prog_interface Cs_compiled)
         (Intermediate.prog_interface P'_compiled))
      as linkability'. {
      eapply @Compiler.compilation_preserves_linkability with (p:=Cs) (c:=P'); eauto.
      apply linkable_sym.
      (* RB: If [linkability] is not used for anything else, refactor these
         rewrites with the instance above, or craft a separate assumption. *)
      rewrite <- Hsame_iface1 in linkability_pcomp_Ct.
      rewrite <- Hsame_iface2 in linkability_pcomp_Ct.
      apply linkability_pcomp_Ct.
    }
    pose proof
      Intermediate.linkable_mains_sym
        (Compiler.compilation_preserves_linkable_mains
          well_formed_P' well_formed_Cs HP'Cs_mains HP'_compiles HCs_compiles)
      as mains'.
    assert (exists P'_Cs_compiled,
              Compiler.compile_program (Source.program_link P' Cs) = Some P'_Cs_compiled)
      as [P'_Cs_compiled HP'_Cs_compiles]. {
      rewrite <- Hsame_iface1 in linkability_pcomp_Ct.
      rewrite <- Hsame_iface2 in linkability_pcomp_Ct.
      pose proof Source.linking_well_formedness well_formed_P' well_formed_Cs linkability_pcomp_Ct
        as Hlinking_wf.
      apply Compiler.well_formed_compilable; assumption.
    }

    assert (forall b, program_behaves (Intermediate.CS.sem P'_Cs_compiled) b <->
                      program_behaves (Intermediate.CS.sem (Intermediate.program_link P'_compiled Cs_compiled)) b)
      as HP'_Cs_behaves. {
      apply Compiler.separate_compilation_weaker with (p:=P') (c:=Cs);
        try assumption;
        [congruence].
    }
    have well_formed_P'Cs : Source.well_formed_program (Source.program_link P' Cs).
      rewrite -Hsame_iface1 -Hsame_iface2 in linkability_pcomp_Ct.
      exact: Source.linking_well_formedness well_formed_P' well_formed_Cs linkability_pcomp_Ct.
    have HP'_Cs_compiled_beh : program_behaves (Intermediate.CS.sem P'_Cs_compiled) beh.
      have sim := Compiler.I_simulates_S HP'Cs_closed well_formed_P'Cs HP'_Cs_compiles.
      pose proof forward_simulation_same_safe_prefix.
      Print does_prefix.
      exact: (forward_simulation_same_safe_behavior sim).

    (* intermediate decomposition (for Cs_compiled) *)
    apply HP'_Cs_behaves in HP'_Cs_compiled_beh.
    apply Source.linkable_mains_sym in HP'Cs_mains. (* TODO: Check if this is used later. *)
    rewrite <- Intermediate.program_linkC in HP'_Cs_compiled_beh;
      [| (apply (Compiler.compilation_preserves_well_formedness well_formed_Cs HCs_compiles))
       | (apply (Compiler.compilation_preserves_well_formedness well_formed_P' HP'_compiles))
       | assumption ].

    have [beh2 [HCs_decomp HCs_beh_improves]] :=
         Intermediate.decomposition_with_refinement
           well_formed_Cs_compiled well_formed_P'_compiled
           linkability' mains' HP'_Cs_compiled_beh.
    have {HCs_beh_improves} ? : beh2 = beh by case: HCs_beh_improves => [<-|[? []]].
    subst beh2.

    (* intermediate composition *)
    assert (Intermediate.prog_interface Ct = Intermediate.prog_interface Cs_compiled)
      as Hctx_same_iface. {
      symmetry. erewrite Compiler.compilation_preserves_interface.
      - rewrite <- Hsame_iface2. reflexivity.
      - assumption.
    }
    rewrite Hctx_same_iface in HP_decomp.
    assert (Intermediate.prog_interface p_compiled = Intermediate.prog_interface P'_compiled) as Hprog_same_iface. {
      symmetry. erewrite Compiler.compilation_preserves_interface.
      - apply Hsame_iface1.
      - assumption.
    }
    rewrite <- Hprog_same_iface in HCs_decomp.

    assert (linkable (Intermediate.prog_interface p_compiled) (Intermediate.prog_interface Cs_compiled))
      as linkability''.
    {
      unfold linkable. split; try
        rewrite Hprog_same_iface;
        apply linkable_sym in linkability';
        now inversion linkability'.
    }
    assert (Intermediate.closed_program (Intermediate.program_link p_compiled Cs_compiled))
      as HpCs_compiled_closed.
    pose proof S2I.matching_mains_equiv
         Hmatching_mains_Cs_Ct
         (Compiler.compilation_has_matching_mains well_formed_Cs HCs_compiles)
         as Hctx_match_mains.
    now apply (Intermediate.interface_preserves_closedness_r
                 well_formed_p_compiled well_formed_Cs_compiled
                 Hctx_same_iface linkability_pcomp_Ct closedness mains Hctx_match_mains); auto.
    assert (Intermediate.well_formed_program (Intermediate.program_link p_compiled Cs_compiled))
      as HpCs_compiled_well_formed
        by (apply Intermediate.linking_well_formedness; assumption).

    assert (Intermediate.linkable_mains p_compiled Cs_compiled) as linkable_mains.
    {
      eapply (@Compiler.compilation_preserves_linkable_mains p _ Cs);
        try assumption.
      - rewrite <- Hsame_iface2 in linkability.
        eapply Source.linkable_disjoint_mains; assumption.
    }

    assert (mergeable_interfaces (Intermediate.prog_interface p_compiled)
                                 (Intermediate.prog_interface Cs_compiled))
      as Hmergeable_ifaces.
      by apply Intermediate.compose_mergeable_interfaces.

    destruct HP_decomp as [b1 [Hbehvesb1 Hprefixb1]].

    pose proof Intermediate.composition_prefix
         well_formed_p_compiled well_formed_Cs_compiled
         linkable_mains HpCs_compiled_closed
         Hmergeable_ifaces
         Hbehvesb1 HCs_decomp
         Hprefixb1 Hprefix1
      as HpCs_compiled_beh.
    destruct HpCs_compiled_beh as [b3 [HpCs_compiled_beh HpCs_compiled_prefix]].
    assert (Source.closed_program (Source.program_link p Cs)) as Hclosed_p_Cs. {
      apply (Source.interface_preserves_closedness_l HP'Cs_closed); trivial.
      apply Compiler.compilation_preserves_interface in HP'_compiles.
      apply Compiler.compilation_preserves_interface in successful_compilation.
      congruence.
    }
    assert (linkable (Source.prog_interface p) (Source.prog_interface Cs))
      as Hlinkable_p_Cs. {
      inversion linkability'' as [sound_interface_p_Cs fdisjoint_p_Cs].
      constructor;
        (apply Compiler.compilation_preserves_interface in HCs_compiles;
        apply Compiler.compilation_preserves_interface in successful_compilation;
        rewrite <- HCs_compiles; rewrite <- successful_compilation;
        assumption).
    }
    assert (Source.well_formed_program (Source.program_link p Cs)) as Hwf_p_Cs
      by (apply Source.linking_well_formedness; assumption).

    (* BCC *)
    assert (exists pCs_compiled,
               Compiler.compile_program (Source.program_link p Cs) = Some pCs_compiled)
      as [pCs_compiled HpCs_compiles]
      by now apply Compiler.well_formed_compilable.
    assert (forall b, program_behaves (Intermediate.CS.sem pCs_compiled) b <->
                      program_behaves (Intermediate.CS.sem (Intermediate.program_link p_compiled Cs_compiled)) b)
      as HpCs_compiled_behaves
      by now apply Compiler.separate_compilation_weaker with (p:=p) (c:=Cs).
    apply HpCs_compiled_behaves in HpCs_compiled_beh.
    assert (exists beh1,
               program_behaves (Source.CS.sem (Source.program_link p Cs)) beh1 /\
               behavior_improves beh1 b3) as HpCs_beh. {
      apply backward_simulation_behavior_improves
        with (L1:=Source.CS.sem (Source.program_link p Cs)) in HpCs_compiled_beh; auto.
      apply Compiler.S_simulates_I; assumption.
    }
    destruct HpCs_beh as [pCs_beh [HpCs_beh HpCs_beh_imp]].

    (* At this point we know:

       1. (HP'_Cs_beh) P' `union` Cs goes from s_i to s_f producing
          finpref_trace m, s_f is stuck and final.

       2. Either

          a. p `union` Cs goes from s_i' to s_f' producing a proper prefix of
             finpref_trace m, and s_f' is stuck and not final.

          b. p `union` Cs goes from s_i' to s_f' producing a super sequence of
             finpref_trace m.

       In (2.a), we should be able to conclude with parallel_exec.  This
       corresponds to the right side of the disjunction.

       In (2.b), we are in the left side of the disjunction.

     *)

    destruct HpCs_beh_imp as [Keq | [t' [Hwrong Klonger]]].
    + subst. exists Cs, b3.
      repeat (split; try now auto).
    + assert(finpref_trace_prefix m t' \/ trace_finpref_prefix t' m) as H
          by (eapply behavior_prefix_comp'; eauto).
      destruct H as [K | K].
      * exists Cs, pCs_beh. repeat (split; try now auto). left.
        subst. destruct m;
        inversion K. exists (Goes_wrong x). simpl. now rewrite H.
      * exists Cs, pCs_beh. repeat (split; try now auto).
        right. exists t'. repeat (split; try now auto).
        subst pCs_beh.
        unfold beh in HP'_Cs_beh.
        (* Close the diagram. *)
        assert (Hsame_iface3 : Source.prog_interface P' = Source.prog_interface p).
        {
          pose proof Compiler.compilation_preserves_interface successful_compilation
            as Hsame_iface3.
          congruence.
        }
        unfold behavior_improves_blame.
        exact (Source.blame_program well_formed_p well_formed_Cs
                                Hlinkable_p_Cs Hclosed_p_Cs HpCs_beh
                                well_formed_P' Hsame_iface3 HP'Cs_closed
                                HP'_Cs_beh Hsafe_pref K).
  Qed.

End RSC_DC_MD_Section.
End RSC_DC_MD_Gen.

Module RSC_DC_MD_Instance :=
  RSC_DC_MD_Gen
    Source_Instance Intermediate_Instance
    S2I_Instance
    Compiler_Instance Linker_Instance.

Definition RSC_DC_MD :=
  RSC_DC_MD_Instance.RSC_DC_MD.
