Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.

Require Import Common.Definitions.
Require Import Common.Linking.
Require Import Common.Blame.
Require Import Common.CompCertExtensions.

Require Import RSC_DC_MD_Sigs.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Module RSC_DC_MD_Gen
       (Source : Source_Sig)
       (Intermediate : Intermediate_Sig)
       (S2I : S2I_Sig Source Intermediate)
       (Compiler : Compiler_Sig Source Intermediate S2I)
       (Linker : Linker_Sig Source Intermediate S2I).

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
    pose proof Intermediate.decomposition_prefix 
      well_formed_p_compiled well_formed_Ct linkability_pcomp_Ct mains
      Hsafe_pref H_doesm  as HP_decomp.

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
      have HP'_Cs_compiled_doesm : does_prefix (Intermediate.CS.sem P'_Cs_compiled) m.
      {
        eapply Compiler.forward_simulation_same_safe_prefix; try eassumption.
        exists beh. auto.
      }

      (*   have sim := Compiler.I_simulates_S HP'Cs_closed well_formed_P'Cs HP'_Cs_compiles. *)
      (*               pose proof forward_simulation_same_safe_prefix. *)
      (* Print does_prefix. *)
      (* exact: (forward_simulation_same_safe_prefix sim). *)

      (* intermediate decomposition (for Cs_compiled) *)

    destruct HP'_Cs_compiled_doesm as [beh1 [HP'_Cs_compiled_beh1 Hprefix2]].

    apply HP'_Cs_behaves in HP'_Cs_compiled_beh1.
    apply Source.linkable_mains_sym in HP'Cs_mains. (* TODO: Check if this is used later. *)
    rewrite <- Intermediate.program_linkC in HP'_Cs_compiled_beh1;
      [| (apply (Compiler.compilation_preserves_well_formedness well_formed_Cs HCs_compiles))
       | (apply (Compiler.compilation_preserves_well_formedness well_formed_P' HP'_compiles))
       | assumption ].

    have [beh2 [HCs_decomp HCs_beh_improves]] :=
         Intermediate.decomposition_with_refinement
           well_formed_Cs_compiled well_formed_P'_compiled
           linkability' mains' HP'_Cs_compiled_beh1.

    (* CA: the following should be no more true nor useful *)
    (* have {HCs_beh_improves} ? : beh2 = beh by case: HCs_beh_improves => [<-|[? []]]. *)
    (* subst beh2. *)

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

    assert (Hprefix_m_beh2 : prefix m beh2). (* beh2 improves beh1 and m < beh1 *)
    {
      inversion HCs_beh_improves as [| [t' [? Hbeh_prefix']]]; subst.
      - assumption.
      - eapply trace_behavior_prefix_trans.
        2: { eapply Hbeh_prefix'. }
        destruct m; try contradiction.
        inversion Hprefix2 as [x H].
        unfold behavior_app in H. destruct x; try inversion H.
        subst. simpl. unfold Events.trace_prefix. eauto.
    }

    pose proof Intermediate.composition_prefix
         well_formed_p_compiled well_formed_Cs_compiled
         linkable_mains HpCs_compiled_closed
         Hmergeable_ifaces
         Hbehvesb1 HCs_decomp
         Hprefixb1 Hprefix_m_beh2
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

Require Import RSC_DC_MD_Instance.

Module RSC_DC_MD_Instance :=
  RSC_DC_MD_Gen
    Source_Instance Intermediate_Instance
    S2I_Instance
    Compiler_Instance Linker_Instance.

Definition RSC_DC_MD :=
  RSC_DC_MD_Instance.RSC_DC_MD.
