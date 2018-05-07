Require Import Common.Definitions.
Require Import Common.Blame.
Require Import Common.CompCertExtensions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Source.PS.
Require Import Intermediate.Machine.
Require Import Intermediate.PS.
Require Import Intermediate.Decomposition.
Require Import Intermediate.Composition.
Require Import Source.Decomposition.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import Definability.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section RSC_DC_MD.
  Variable p: Source.program.
  Variable p_compiled: Intermediate.program.
  Variable Ct: Intermediate.program.

  (* Some reasonable assumptions about our programs *)

  Hypothesis well_formed_p : Source.well_formed_program p.
  Hypothesis successful_compilation : compile_program p = Some p_compiled.
  Hypothesis well_formed_Ct : Intermediate.well_formed_program Ct.
  Hypothesis linkability : linkable (Source.prog_interface p) (Intermediate.prog_interface Ct).
  Hypothesis closedness :
    Intermediate.closed_program (Intermediate.program_link p_compiled Ct).
  Hypothesis mains : Intermediate.linkable_mains p_compiled Ct.

  (* Main Theorem *)

  Theorem RSC_DC_MD:
    forall b m,
      program_behaves (I.CS.sem (Intermediate.program_link p_compiled Ct)) b ->
      prefix m b ->
      not_wrong b -> (* CH: could try to weaken this later to `nor_wrong m` *)
    exists Cs beh,
      Source.prog_interface Cs = Intermediate.prog_interface Ct /\
      Source.well_formed_program Cs /\
      linkable (Source.prog_interface p) (Source.prog_interface Cs) /\
      Source.closed_program (Source.program_link p Cs) /\
      program_behaves (S.CS.sem (Source.program_link p Cs)) beh /\
      (prefix m beh \/
      (exists t',
        beh = Goes_wrong t' /\ trace_finpref_prefix t' m /\
         undef_in t' (Source.prog_interface p))).
  Proof.
    intros t m Hbeh Hprefix0 Hsafe_beh.

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
        apply compilation_preserves_interface in successful_compilation;
        now rewrite successful_compilation.
    }

    assert (Hnot_wrong' : not_wrong_finpref m).
    { now destruct m, t; simpl; auto. }

    (* intermediate decomposition (for p_compiled) *)
    pose proof Intermediate.Decomposition.decomposition_with_safe_behavior
      well_formed_p_compiled well_formed_Ct linkability_pcomp_Ct Hbeh Hsafe_beh as HP_decomp.

    (* CH: if we had undefined behavior we would use this *)
    (* destruct (decomposition_with_refinement linkability Hbeh) *)
    (*   as [beh' [Hbeh' Hbeh_improves]]. *)

    (* definability *)
    destruct (definability_with_linking
                well_formed_p_compiled well_formed_Ct
                linkability_pcomp_Ct closedness Hbeh Hprefix0 Hnot_wrong')
      as [P' [Cs
         [Hsame_iface1 [Hsame_iface2
         [well_formed_P' [well_formed_Cs [HP'Cs_closed [HP'_Cs_beh Hprefix1]]]]]]]].

    move: HP'_Cs_beh Hprefix1.
    set beh := Terminates _.
    move=> HP'_Cs_beh Hprefix1.

    assert (Source.linkable_mains P' Cs) as HP'Cs_mains.
    { apply Source.linkable_disjoint_mains; trivial; congruence. }

    (* FCC *)

    (* the definability output can be split in two programs *)
    (* probably need partialize to obtain them *)

    (* At this point, we compile P' and Cs and establish their basic properties. *)
    destruct (well_formed_compilable _ well_formed_P') as [P'_compiled HP'_compiles].
    pose proof Compiler.compilation_preserves_well_formedness well_formed_P' HP'_compiles
      as well_formed_P'_compiled.
    destruct (well_formed_compilable _ well_formed_Cs) as [Cs_compiled HCs_compiles].
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
    assert (exists P'_Cs_compiled,
              compile_program (Source.program_link P' Cs) = Some P'_Cs_compiled)
      as [P'_Cs_compiled HP'_Cs_compiles]. {
      rewrite <- Hsame_iface1 in linkability_pcomp_Ct.
      rewrite <- Hsame_iface2 in linkability_pcomp_Ct.
      pose proof Source.linking_well_formedness well_formed_P' well_formed_Cs linkability_pcomp_Ct
        as Hlinking_wf.
      apply well_formed_compilable; assumption.
    }

    assert (forall b, program_behaves (I.CS.sem P'_Cs_compiled) b <->
                 program_behaves (I.CS.sem (Intermediate.program_link P'_compiled Cs_compiled)) b)
      as HP'_Cs_behaves. {
      apply Compiler.separate_compilation_weaker with (p:=P') (c:=Cs);
        try assumption;
        [congruence].
    }
    have HP'_Cs_compiled_beh : program_behaves (I.CS.sem P'_Cs_compiled) beh.
      rewrite -Hsame_iface1 -Hsame_iface2 in linkability_pcomp_Ct.
      have well_formed_P'Cs := Source.linking_well_formedness well_formed_P' well_formed_Cs linkability_pcomp_Ct.
      have sim := Compiler.I_simulates_S HP'Cs_closed well_formed_P'Cs HP'_Cs_compiles.
      exact: (forward_simulation_same_safe_behavior sim).

    (* intermediate decomposition (for Cs_compiled) *)
    apply HP'_Cs_behaves in HP'_Cs_compiled_beh.
    apply Source.linkable_mains_sym in HP'Cs_mains. (* TODO: Check if this is used later. *)
    rewrite <- Intermediate.program_linkC in HP'_Cs_compiled_beh;
      [| (apply (Compiler.compilation_preserves_well_formedness well_formed_Cs HCs_compiles))
       | (apply (Compiler.compilation_preserves_well_formedness well_formed_P' HP'_compiles))
       | assumption ].

    have [beh2 [HCs_decomp HCs_beh_improves]] :=
         Intermediate.Decomposition.decomposition_with_refinement
           well_formed_Cs_compiled well_formed_P'_compiled
           linkability' HP'_Cs_compiled_beh.
    have {HCs_beh_improves} ? : beh2 = beh by case: HCs_beh_improves => [<-|[? []]].
    subst beh2.

    (* intermediate composition *)
    assert (Intermediate.prog_interface Ct = Intermediate.prog_interface Cs_compiled)
      as Hctx_same_iface. {
      symmetry. erewrite compilation_preserves_interface.
      - rewrite <- Hsame_iface2. reflexivity.
      - assumption.
    }
    rewrite Hctx_same_iface in HP_decomp.
    assert (Intermediate.prog_interface p_compiled = Intermediate.prog_interface P'_compiled) as Hprog_same_iface. {
      symmetry. erewrite compilation_preserves_interface.
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
    now apply (Intermediate.interface_preserves_closedness_r
                 well_formed_p_compiled well_formed_Cs_compiled
                 Hctx_same_iface linkability_pcomp_Ct closedness mains); auto.
    assert (Intermediate.well_formed_program (Intermediate.program_link p_compiled Cs_compiled))
      as HpCs_compiled_well_formed
        by (apply Intermediate.linking_well_formedness; assumption).

    assert (Intermediate.linkable_mains p_compiled Cs_compiled) as linkable_mains.
    {
      eapply (Compiler.compilation_preserves_linkable_mains p _ Cs);
        try assumption.
      - rewrite <- Hsame_iface2 in linkability.
        eapply Source.linkable_disjoint_mains; assumption.
    }

    assert (PS.mergeable_interfaces (Intermediate.prog_interface p_compiled)
                                    (Intermediate.prog_interface Cs_compiled))
      as Hmergeable_ifaces.
    {
      split.
      - assumption.
      - by destruct HpCs_compiled_closed.
    }
    pose proof composition_prefix
         well_formed_p_compiled well_formed_Cs_compiled
         linkable_mains linkability'' HpCs_compiled_closed
         Hmergeable_ifaces
         HP_decomp HCs_decomp
         Hprefix0 Hprefix1
      as HpCs_compiled_beh.
    destruct HpCs_compiled_beh as [b3 [HpCs_compiled_beh HpCs_compiled_prefix]].
    assert (Source.closed_program (Source.program_link p Cs)) as Hclosed_p_Cs. {
      apply (Source.interface_preserves_closedness_l HP'Cs_closed); trivial.
      apply compilation_preserves_interface in HP'_compiles.
      apply compilation_preserves_interface in successful_compilation.
      congruence.
    }
    assert (linkable (Source.prog_interface p) (Source.prog_interface Cs))
      as Hlinkable_p_Cs. {
      inversion linkability'' as [sound_interface_p_Cs fdisjoint_p_Cs].
      constructor;
        (apply compilation_preserves_interface in HCs_compiles;
        apply compilation_preserves_interface in successful_compilation;
        rewrite <- HCs_compiles; rewrite <- successful_compilation;
        assumption).
    }
    assert (Source.well_formed_program (Source.program_link p Cs)) as Hwf_p_Cs
      by (apply Source.linking_well_formedness; assumption).

    (* BCC *)
    assert (exists pCs_compiled,
               compile_program (Source.program_link p Cs) = Some pCs_compiled)
      as [pCs_compiled HpCs_compiles]
      by now apply well_formed_compilable.
    assert (forall b, program_behaves (I.CS.sem pCs_compiled) b <->
                      program_behaves (I.CS.sem (Intermediate.program_link p_compiled Cs_compiled)) b)
      as HpCs_compiled_behaves
      by now apply Compiler.separate_compilation_weaker with (p:=p) (c:=Cs).
    apply HpCs_compiled_behaves in HpCs_compiled_beh.
    assert (exists beh1,
               program_behaves (S.CS.sem (Source.program_link p Cs)) beh1 /\
               behavior_improves beh1 b3) as HpCs_beh. {
      apply backward_simulation_behavior_improves
        with (L1:=S.CS.sem (Source.program_link p Cs)) in HpCs_compiled_beh; auto.
      apply S_simulates_I; assumption.
    }
    destruct HpCs_beh as [pCs_beh [HpCs_beh HpCs_beh_imp]].

    (* Source-level decompositions (p and P') and closure of the diagram. *)
    exists Cs. exists pCs_beh.
    split; [assumption |].
    split; [assumption |].
    split; [assumption |].
    split; [assumption |].
    inversion HpCs_beh_imp as [pCs_beh_ok|].
    - split.
      + subst pCs_beh. assumption.
      + left. subst. assumption.
    - destruct H as [t' [Hgoes_wrong Hprefix]].
      assert(finpref_trace_prefix m t' \/ trace_finpref_prefix t' m) as H
          by (eapply behavior_prefix_comp'; eauto).
      destruct H as [H | H].
      + split.
        * subst pCs_beh. assumption.
        * left. subst. eapply trace_behavior_prefix_trans.
          -- apply H.
          -- unfold behavior_prefix. exists (Goes_wrong []). simpl.
             setoid_rewrite <- app_nil_end. reflexivity.
      + split; first by subst pCs_beh.
        right. exists t'. do 2 (split; first now auto).
        rewrite Source.link_sym in HpCs_beh; try assumption.
        apply Source.Decomposition.decomposition_with_refinement_and_blame in HpCs_beh;
          [ | assumption | assumption | now apply linkable_sym
            | setoid_rewrite <- Source.link_sym; assumption].
        * setoid_rewrite Source.link_sym in HP'_Cs_beh; trivial; try congruence.
          eapply Source.Decomposition.decomposition_with_safe_behavior in HP'_Cs_beh;
            [| assumption | assumption | congruence |
               assert (linkable (Source.prog_interface P') (Source.prog_interface Cs))
                 as Hlink by congruence;
               rewrite <- (Source.closed_program_link_sym well_formed_P' well_formed_Cs Hlink);
               assumption
             | by [] ].
          (* destruct HP'_Cs_beh as [beh' [G1 G2]]. *)
          destruct HpCs_beh as [b [H1 H2]].
          eapply (@blame_program_fixed p Cs).
          -- assumption.
          -- assumption.
          -- assumption.
          -- assumption.
          -- pose proof (compilation_preserves_interface
                           p p_compiled successful_compilation) as HH.
             assert(Source.prog_interface P' = Source.prog_interface p) as HHH
               by congruence.
             rewrite <- HHH. apply HP'_Cs_beh.
          -- exact Hprefix1.
          -- exact Hgoes_wrong.
          -- exact H1.
          -- exact H2.
          -- eexists. split; eassumption.
  Qed.

End RSC_DC_MD.
