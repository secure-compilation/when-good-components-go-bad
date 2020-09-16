Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Linking.
Require Import Common.Blame.
Require Import Common.CompCertExtensions.
Require Import Common.TracesInform.
Require Import Common.Renaming.

Require Import RSC_DC_MD_Sigs.
Require Import Source.Definability.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.

Set Bullet Behavior "Strict Subproofs".

Module RSC_DC_MD_Gen
       (Source : Source_Sig)
       (Intermediate : Intermediate_Sig)
       (S2I : S2I_Sig Source Intermediate)
       (Compiler : Compiler_Sig Source Intermediate S2I)
       (Linker : Linker_Sig Source Intermediate S2I).

Definition behavior_improves_blame b (m: @finpref_behavior Events.event) p :=
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


  (* [DynShare]
     
     - Maybe we can get rid of the disjunction "... \/ behavior_improves_blame beh".
     - And also we should (instead of program_behaves) directly use 
       does_prefix (Source.CS.sem (Source.program_link p Cs)) m' 
       Notice that does_prefix is the "finite version" of "program_behaves", i.e., it still
       contains the cases of FTerminates and FGoesWrong.

     * Because our current S2I compiler does not seem to refine any undef behavior,
       we should be able to get rid of the blame disjunct.

   *)
  Theorem RSC_DC_MD:
    forall (m: @finpref_behavior (*TracesInform.event_inform*) Events.event),
      does_prefix (Intermediate.CS.sem(*_inform*)
                     (Intermediate.program_link p_compiled Ct)) m ->
      not_wrong_finpref m ->
      exists Cs (beh: @program_behavior Events.event) m'
             size_meta_m size_meta_m',
      Source.prog_interface Cs = Intermediate.prog_interface Ct /\
      Source.well_formed_program Cs /\
      linkable (Source.prog_interface p) (Source.prog_interface Cs) /\
      Source.closed_program (Source.program_link p Cs) /\
      program_behaves (Source.CS.sem (Source.program_link p Cs)) beh /\
      (prefix ((*Definability.project_finpref_behavior*) m') beh \/
       behavior_improves_blame beh ((*Definability.project_finpref_behavior*) m') p) /\
      behavior_rel_behavior_all_cids size_meta_m size_meta_m'
                            ((*Definability.project_finpref_behavior*) m) m'.
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

    assert (H_doesm_noninform: does_prefix
                                 (Intermediate.CS.sem
                                    (Intermediate.program_link p_compiled Ct)) m)
      by (now exists t).
                    
    assert (H_doesm': exists m_inform,
               does_prefix
                 (Intermediate.CS.sem_inform
                    (Intermediate.program_link p_compiled Ct)) m_inform).
    { admit. }

    destruct H_doesm' as [m_inform H_doesm].

    assert (m_m_inform: m = project_finpref_behavior m_inform).
    { admit. }

    Check project_finpref_behavior.
    Locate finpref_behavior.

    assert (Hbeh_inform': exists t_inform,
               program_behaves
                 (Intermediate.CS.sem_inform
                    (Intermediate.program_link p_compiled Ct)) t_inform
           ).
    { admit. }

    destruct Hbeh_inform' as [t_inform Hbeh_inform].
    
    assert (Hprefix0_inform: prefix m_inform t_inform).
    { admit. }

    assert (Hsafe_pref_inform: not_wrong_finpref m_inform).
    { admit. }
    
    (* intermediate decomposition (for p_compiled) *)
    (* pose proof Intermediate.decomposition_prefix  *)
    (*   well_formed_p_compiled well_formed_Ct linkability_pcomp_Ct mains *)
    (*   Hsafe_pref H_doesm  as HP_decomp. *)

    (* definability *)
    destruct (Linker.definability_with_linking
                well_formed_p_compiled well_formed_Ct
                linkability_pcomp_Ct closedness Hbeh_inform Hprefix0_inform Hsafe_pref_inform)
      as [P' [Cs [metadata_size [m'
         [Hsame_iface1 [Hsame_iface2
         [Hmatching_mains_P'_p_compiled [Hmatching_mains_Cs_Ct
         [well_formed_P' [well_formed_Cs [HP'Cs_closed [HP'_Cs_m' Hbeh_rel_beh]]]]]]]]]]]].

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
      rewrite <- Hsame_iface1 in linkability_pcomp_Ct.
      rewrite <- Hsame_iface2 in linkability_pcomp_Ct.
      apply linkability_pcomp_Ct.
    }
    assert (exists P'_Cs_compiled,
              Compiler.compile_program (Source.program_link P' Cs) = Some P'_Cs_compiled)
      as [P'_Cs_compiled HP'_Cs_compiles]. {
      rewrite <- Hsame_iface1 in linkability_pcomp_Ct.
      rewrite <- Hsame_iface2 in linkability_pcomp_Ct.
      pose proof Source.linking_well_formedness well_formed_P' well_formed_Cs linkability_pcomp_Ct
        as Hlinking_wf.
      apply Compiler.well_formed_compilable; assumption.
    }

    have well_formed_P'Cs : Source.well_formed_program (Source.program_link P' Cs).
      rewrite -Hsame_iface1 -Hsame_iface2 in linkability_pcomp_Ct.
      exact: Source.linking_well_formedness well_formed_P' well_formed_Cs linkability_pcomp_Ct.

      have HP'_Cs_compiled_doesm : does_prefix
                                     (Intermediate.CS.sem
                                        (Intermediate.program_link P'_compiled Cs_compiled))
                                     m'.
      {
        eapply Compiler.forward_simulation_same_safe_prefix; try eassumption. congruence.
        (* [DynShare] The subgoal remaining here is "not_wrong_finpref m'". This subgoal
         should follow from the fact that m' is produced by a back-translation.
         A back-translation should not go wrong because it mimics well-defined events, 
         and then directly terminates.
         *)
        (* However, right now it doesn't seem we have such a lemma? *)
        admit.
      }

    (* intermediate decomposition (for Cs_compiled) *)
    rewrite Intermediate.program_linkC in HP'_Cs_compiled_doesm;
       [| assumption |assumption | apply linkable_sym in linkability'; assumption].
    (* pose proof (Intermediate.decomposition_prefix *)
    (*        well_formed_Cs_compiled well_formed_P'_compiled *)
    (*        linkability' mains' Hsafe_pref HP'_Cs_compiled_doesm) as HCs_decomp. *)

    (* intermediate composition *)
    assert (Intermediate.prog_interface Ct = Intermediate.prog_interface Cs_compiled)
      as Hctx_same_iface. {
      symmetry. erewrite Compiler.compilation_preserves_interface.
      - rewrite <- Hsame_iface2. reflexivity.
      - assumption.
    }
    (* rewrite Hctx_same_iface in HP_decomp. *)
    assert (Intermediate.prog_interface p_compiled = Intermediate.prog_interface P'_compiled) as Hprog_same_iface. {
      symmetry. erewrite Compiler.compilation_preserves_interface.
      - apply Hsame_iface1.
      - assumption.
    }
    (* rewrite <- Hprog_same_iface in HCs_decomp. *)

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

    (* pose proof Intermediate.composition_prefix *)
    (*      well_formed_p_compiled well_formed_Cs_compiled *)
    (*      linkable_mains HpCs_compiled_closed *)
    (*      Hmergeable_ifaces *)
    (*      HP_decomp HCs_decomp *)
    (*   as HpCs_compiled_beh. *)
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

    assert (HP'Cs_compiled_closed :
              Intermediate.closed_program (Intermediate.program_link P'_compiled Cs_compiled)).
    {
      rewrite Intermediate.program_linkC; try easy; try now apply linkable_sym.
      apply Intermediate.interface_preserves_closedness_r with (p2 := p_compiled); eauto.
      apply linkable_sym; eauto.
      rewrite Intermediate.program_linkC; eauto.
      apply linkable_sym; eauto.
      apply Intermediate.linkable_mains_sym; eauto.
      eapply S2I.matching_mains_equiv; eauto.
      apply Compiler.compilation_has_matching_mains; eauto.
    }

    rewrite Intermediate.program_linkC in HP'_Cs_compiled_doesm; try assumption.
    rewrite <- Hctx_same_iface in Hmergeable_ifaces.

    assert (m_rel_m': behavior_rel_behavior_all_cids all_zeros_shift metadata_size m m').
    { admit. }

    pose proof Intermediate.recombination_prefix
         well_formed_p_compiled well_formed_Ct well_formed_P'_compiled well_formed_Cs_compiled
         Hmergeable_ifaces Hprog_same_iface Hctx_same_iface
         closedness HP'Cs_compiled_closed
         H_doesm_noninform HP'_Cs_compiled_doesm m_rel_m'
         as [size_m'' [m'' [HpCs_compiled_beh m''_rel_m]]].
    
    (* BCC *)
    assert (exists pCs_compiled,
               Compiler.compile_program (Source.program_link p Cs) = Some pCs_compiled)
      as [pCs_compiled HpCs_compiles].
      by now apply Compiler.well_formed_compilable.

    assert (exists beh1,
               program_behaves (Source.CS.sem (Source.program_link p Cs)) beh1 /\
               (prefix m'' beh1 \/ behavior_improves_finpref beh1 m'')) as HpCs_beh.
    {
      
      eapply Compiler.backward_simulation_behavior_improves_prefix in HpCs_compiled_beh;
        eauto.
    }
    destruct HpCs_beh as [pCs_beh [HpCs_beh HpCs_beh_imp]].

    assert (m_rel_m'': behavior_rel_behavior_all_cids all_zeros_shift size_m'' m m'').
    { (*[DynShare] This should follow from m''_rel_m *)
      admit.
    }
    (* Instantiate behavior, case analysis on improvement. *)
    exists Cs. eexists. eexists m''. eexists all_zeros_shift. eexists.
    destruct HpCs_beh_imp as [Keq | [t' [Hwrong Klonger]]].
    + repeat (split; try now eauto).
    + subst pCs_beh.
      repeat (split; try now auto).
      (* Blame the program and close the diagram. *)
      assert (Hsame_iface3 : Source.prog_interface P' = Source.prog_interface p).
      {
        pose proof Compiler.compilation_preserves_interface successful_compilation
          as Hsame_iface3.
        congruence.
      }
      unfold behavior_improves_blame.

      (* [DynShare] Continue here. *)
  Admitted.
(*      destruct (Source.blame_program well_formed_p well_formed_Cs
                              Hlinkable_p_Cs Hclosed_p_Cs HpCs_beh
                              well_formed_P' Hsame_iface3 HP'Cs_closed
                             HP'_Cs_m' Hsafe_pref Klonger) as [H|H]; by eauto.

  Qed.
*)
End RSC_DC_MD_Section.
End RSC_DC_MD_Gen.

Require Import RSC_DC_MD_Instance.

Module RSC_DC_MD_Instance :=
  RSC_DC_MD_Gen
    Source_Instance Intermediate_Instance
    S2I_Instance
    Compiler_Instance Linker_Instance.

Definition RSC_DC_MD :=
  RSC_DC_MD_Instance.RSC_DC_MD.
