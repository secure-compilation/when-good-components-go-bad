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

Section RSC_DC_MD.
  Variable p: Source.program.
  Variable p_compiled: Intermediate.program.
  Variable Ct: Intermediate.program.

  (* Some reasonable assumptions about our programs *)

  Hypothesis well_formed_p : Source.well_formed_program p.
  Hypothesis successfull_compilation : compile_program p = Some p_compiled.
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
      not_wrong b -> (* CH: could try to remove this later *)
    exists Cs beh,
      Source.prog_interface Cs = Intermediate.prog_interface Ct /\
      Source.well_formed_program Cs /\
      linkable (Source.prog_interface p) (Source.prog_interface Cs) /\
      Source.closed_program (Source.program_link p Cs) /\
      program_behaves (S.CS.sem (Source.program_link p Cs)) beh /\
      (prefix m beh \/
      (exists t',
        beh = Goes_wrong t' /\ trace_finpref_prefix t' m /\
         undef_in Component.main t' (Source.prog_interface p))).
  Proof.
    intros t m Hbeh Hprefix0 Hsafe_beh.

    assert(sound_interface_p_Ct : sound_interface (unionm (Source.prog_interface p)
                                                          (Intermediate.prog_interface Ct)))
      by apply linkability.
    assert(fdisjoint_p_Ct : fdisjoint (domm (Source.prog_interface p))
                                      (domm (Intermediate.prog_interface Ct)))
      by apply linkability.

    assert(linkable (Intermediate.prog_interface p_compiled)
                    (Intermediate.prog_interface Ct)) as linkability'''. {
         constructor.
         - apply compilation_preserves_interface in successfull_compilation.
           rewrite successfull_compilation. assumption.
         - apply compilation_preserves_interface in successfull_compilation.
           rewrite successfull_compilation. assumption.
    }

    (* intermediate decomposition (for p_compiled) *)
    pose proof
      Compiler.compilation_preserves_well_formedness well_formed_p successfull_compilation
      as well_formed_p_compiled.
    pose proof Intermediate.Decomposition.decomposition_with_safe_behavior
      well_formed_p_compiled well_formed_Ct linkability''' Hbeh Hsafe_beh as HP_decomp.

    (* CH: if we had undefined behavior we would use this *)
    (* destruct (decomposition_with_refinement linkability Hbeh) *)
    (*   as [beh' [Hbeh' Hbeh_improves]]. *)

    assert (Hnot_wrong' : not_wrong_finpref m).
    { now destruct m, t; simpl; auto. }

    (* definability *)
    destruct (definability_with_linking well_formed_p_compiled well_formed_Ct linkability''' closedness Hbeh Hprefix0 Hnot_wrong')
      as [P' [Cs [beh [Hsame_iface1 [Hsame_iface2 [well_formed_P' [well_formed_Cs [HP'Cs_closed [HP'_Cs_beh Hprefix1]]]]]]]]].
    assert (Source.linkable_mains P' Cs) as HP'Cs_mains.
    { apply Source.linkable_disjoint_mains; trivial; congruence. }

    (* FCC *)

    assert (exists P'_compiled Cs_compiled P'Cs_compiled,
               compile_program P' = Some P'_compiled /\
               compile_program Cs = Some Cs_compiled /\
               compile_program (Source.program_link P' Cs) = Some P'Cs_compiled /\
               forall b, program_behaves (I.CS.sem P'Cs_compiled) b <->
                         program_behaves (I.CS.sem (Intermediate.program_link P'_compiled Cs_compiled)) b)

      as HP'_Cs_compiles. {
      (* the definability output can be splitted in two programs *)
      (* probably need partialize to obtain them *)
      assert (exists P'_compiled, compile_program P' = Some P'_compiled)
        as [P'_compiled HP'_compiles]
        by (now apply well_formed_compilable).
      assert (exists Cs_compiled, compile_program Cs = Some Cs_compiled)
        as [Cs_compiled HCs_compiles]
        by (now apply well_formed_compilable).
      assert (exists P'_Cs_compiled,
                 compile_program (Source.program_link P' Cs) = Some P'_Cs_compiled)
        as [P'_Cs_compiled HP'_Cs_compiles]. {
        rewrite <- Hsame_iface1 in linkability'''.
        rewrite <- Hsame_iface2 in linkability'''.
        pose proof Source.linking_well_formedness well_formed_P' well_formed_Cs linkability'''
          as Hlinking_wf.
        apply well_formed_compilable; assumption.
      }
      exists P'_compiled, Cs_compiled, P'_Cs_compiled.
      split; [assumption |].
      split; [assumption |].
      split; [assumption |].
      apply Compiler.separate_compilation_weaker with (p:=P') (c:=Cs);
        try assumption.
      - congruence.
    }
    destruct HP'_Cs_compiles
      as [P'_compiled [Cs_compiled [P'_Cs_compiled [HP'_compiles [HCs_compiles [HP'_Cs_compiles HP'_Cs_behaves]]]]]].
    assert (exists b', program_behaves (I.CS.sem P'_Cs_compiled) b' /\ prefix m b')
      as HP'_Cs_compiled_beh. {

      apply forward_simulation_behavior_improves
        with (L2:=I.CS.sem P'_Cs_compiled) in HP'_Cs_beh;
        simpl; eauto.
      - destruct HP'_Cs_beh as [b2 [H1 H2]]. exists b2. split.
        + assumption.
        + destruct H2 as [|[t' [H21 H22]]].
          * subst. assumption.
          * subst. unfold prefix in Hprefix1. destruct m as [? | m' | ?].
            ** destruct Hprefix1.
            ** subst m'. destruct H22 as [b22 H22]. subst b2.
               simpl in Hprefix0.
               destruct t as [? | ? | ? |t2]; try (inversion Hprefix0).
               *** subst t2. inversion Hsafe_beh.
            ** simpl. apply (behavior_prefix_goes_wrong_trans Hprefix1 H22).
      - apply Compiler.I_simulates_S; auto.
        apply Source.linking_well_formedness.
        * assumption.
        * assumption.
        * rewrite <- Hsame_iface1 in linkability'''.
          rewrite <- Hsame_iface2 in linkability'''.
          now apply linkability'''.
    }
    destruct HP'_Cs_compiled_beh as [t2 [HP'_Cs_compiled_beh HP'_Cs_compiled_prefix]].

    (* intermediate decomposition (for Cs_compiled) *)
    assert
      (linkable
         (Intermediate.prog_interface Cs_compiled)
         (Intermediate.prog_interface P'_compiled))
      as linkability'. {
      eapply @Compiler.compilation_preserves_linkability with (p:=Cs) (c:=P'); eauto.
      apply linkable_sym.
      (* RB: If [linkability] is not used for anything else, refactor these
         rewrites with the instance above, or craft a separate assumption. *)
      rewrite <- Hsame_iface1 in linkability'''.
      rewrite <- Hsame_iface2 in linkability'''.
      apply linkability'''.
    }
    apply HP'_Cs_behaves in HP'_Cs_compiled_beh.
    apply Source.linkable_mains_sym in HP'Cs_mains.
    rewrite <- Intermediate.link_sym in HP'_Cs_compiled_beh;
      [| (apply (Compiler.compilation_preserves_well_formedness well_formed_Cs HCs_compiles))
       | (apply (Compiler.compilation_preserves_well_formedness well_formed_P' HP'_compiles))
       | (apply (Compiler.compilation_preserves_linkable_mains Cs _ P'); assumption)
       | assumption ].
    pose proof Compiler.compilation_preserves_well_formedness well_formed_P' HP'_compiles
      as well_formed_P'_compiled.
    pose proof Compiler.compilation_preserves_well_formedness well_formed_Cs HCs_compiles
      as well_formed_Cs_compiled.
    pose proof Intermediate.Decomposition.decomposition_with_refinement
         well_formed_Cs_compiled well_formed_P'_compiled
         linkability' HP'_Cs_compiled_beh as [beh2 [HCs_decomp HCs_beh_improves]].

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
      as HpCs_compiled_closed
      by (apply (Intermediate.interface_preserves_closedness_r closedness Hctx_same_iface)).
    assert (Intermediate.well_formed_program (Intermediate.program_link p_compiled Cs_compiled))
      as HpCs_compiled_well_formed
        by (apply Intermediate.linking_well_formedness; assumption).

    assert (prefix m beh2) as Hpref_m_beh2. {
      unfold prefix in HP'_Cs_compiled_prefix.
      destruct m as [m' | m' | m'].
      - destruct t2 as [t2' | ? | ? | ?]; try (inversion HP'_Cs_compiled_prefix; fail).
        + subst t2'.
          destruct HCs_beh_improves as [Hterm | [t' [Hterm Hpref]]].
          * now subst beh2.
          * inversion Hterm.
      - simpl in Hprefix0.
        destruct t; try (inversion Hprefix0; fail).
        + inversion Hsafe_beh.
      - simpl.
        apply (behavior_prefix_improves_trans' HP'_Cs_compiled_prefix HCs_beh_improves).
    }
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
         Hprefix0 Hpref_m_beh2
      as HpCs_compiled_beh.
    destruct HpCs_compiled_beh as [b3 [HpCs_compiled_beh HpCs_compiled_prefix]].
    assert (Source.closed_program (Source.program_link p Cs)) as Hclosed_p_Cs. {
      apply (Source.interface_preserves_closedness_l HP'Cs_closed); trivial.
      apply compilation_preserves_interface in HP'_compiles.
      apply compilation_preserves_interface in successfull_compilation.
      congruence.
    }
    assert (linkable (Source.prog_interface p) (Source.prog_interface Cs))
      as Hlinkable_p_Cs. {
      inversion linkability'' as [sound_interface_p_Cs fdisjoint_p_Cs].
      constructor;
        (apply compilation_preserves_interface in HCs_compiles;
        apply compilation_preserves_interface in successfull_compilation;
        rewrite <- HCs_compiles; rewrite <- successfull_compilation;
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
      assert(finpref_trace_prefix m t' \/ trace_finpref_prefix t' m) as H by (eapply behavior_prefix_comp'; eauto).
      destruct H as [H | H].
      + split.
        * subst pCs_beh. assumption.
        * left. subst. eapply trace_behavior_prefix_trans.
          - apply H.
          - unfold behavior_prefix. exists (Goes_wrong []). simpl.
            setoid_rewrite <- app_nil_end. reflexivity.
      + split.
        * subst pCs_beh. assumption.
        * right. exists t'. repeat split; auto.
          (* blame UB -- Guglielmo working on proof *)
          rewrite Source.link_sym in HpCs_beh; try assumption.
          apply Source.Decomposition.decomposition_with_refinement_and_blame in HpCs_beh;
              try assumption.
          - setoid_rewrite Source.link_sym in HP'_Cs_beh; trivial; try congruence.
            eapply Source.Decomposition.decomposition_with_refinement in HP'_Cs_beh;
              [| assumption | assumption | congruence |];
              (* Retaining most of the structure of the proof, though we need to add a not
                 completely insignificant sub-proof here, to be harmonized. *)
              last by (
                assert (linkable (Source.prog_interface P') (Source.prog_interface Cs))
                  as Hlink by congruence;
                rewrite <- (Source.closed_program_link_sym well_formed_P' well_formed_Cs Hlink);
                assumption
              ).
            destruct HP'_Cs_beh as [beh' [G1 G2]].
            destruct HpCs_beh as [b [H1 [H2 | H2]]].
            + subst pCs_beh. subst b.
              eapply (@blame_program p Cs).
              * assumption.
              * assumption.
              * assumption.
              * assumption.
              * pose proof (compilation_preserves_interface p p_compiled
                                               successfull_compilation) as HH.
                assert(Source.prog_interface P' = Source.prog_interface p) as HHH
                    by congruence.
                rewrite <- HHH.
                now apply G1.
              * assumption.
              * assert(behavior_prefix t' beh) as H0. {
                  eapply trace_behavior_prefix_trans'.
                  - now apply H.
                  - assumption.
                }
                eapply behavior_prefix_improves_trans'.
                - now eapply H0.
                - assumption.
            + destruct H2 as [t'' [H21 [H22 H23]]].
              subst pCs_beh. injection H21; intro H21'. subst t''. assumption.
          - now apply linkable_sym.
          - setoid_rewrite <- Source.link_sym; assumption.
  Qed.

End RSC_DC_MD.
