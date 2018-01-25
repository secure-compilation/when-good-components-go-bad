Require Import Common.Definitions.
Require Import Common.Blame.
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

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

  Let slink := Source.program_link.
  Let ilink := Intermediate.program_link.

  (* Some facts (provable and to prove) about linking and compilation *)
  (* CH: worried about all these unproved(?) assumptions
         on top of the 8 admits in the proof *)

  (* This should be provable, although we may have to slightly change the compiler *)
  (* (e.g. procedure id & label generation should be local to the component *)
  (* CH: TODO requires reverting some of Andrew's changes to compiler,
              see Separate compilation in robust-imp-comments.org *)
  Hypothesis separate_compilation:
    forall p c p_comp c_comp,
      Source.linkable_programs p c ->
      compile_program p = Some p_comp ->
      compile_program c = Some c_comp ->
      compile_program (slink p c) = Some (ilink p_comp c_comp).
  (* CH: because of the Somes might also want something of the following form: *)
  (* CH: in general the use of options doesn't seem to make anything simpler,
         but maybe that's inherited from CompCert? *)
  Hypothesis separate_compilation':
    forall p c pc_comp,
      Source.linkable_programs p c ->
      compile_program (slink p c) = Some pc_comp ->
      exists p_comp c_comp,
        compile_program p = Some p_comp /\
        compile_program c = Some c_comp /\
        pc_comp = ilink p_comp c_comp.
  (* CH: anyway, this is a very strong notion of separate compilation;
         wondering whether in the general case we could do away with something weaker
         (anyway, just a thought for later, current version is simpler): *)
  (* Hypothesis separate_compilation_weaker: *)
  (*   forall p c pc_comp p_comp c_comp, *)
  (*     Source.linkable_programs p c -> *)
  (*     compile_program p = Some p_comp -> *)
  (*     compile_program c = Some c_comp -> *)
  (*     compile_program (slink p c) = Some pc_comp -> *)
  (*     forall b, program_behaves (I.CS.sem pc_comp) b <-> *)
  (*               program_behaves (I.CS.sem (ilink p_comp c_comp)) b. *)

  Hypothesis compilation_preserves_linkability:
    forall p p_compiled c c_compiled,
      Source.linkable_programs p c ->
      compile_program p = Some p_compiled ->
      compile_program c = Some c_compiled ->
      Intermediate.linkable_programs p_compiled c_compiled.

  (* CH: The following symmetry lemmas seem needed so that lemmas like
         decomposition don't have to be reproved for contexts
         (although in the general case they probably can be reproved
         if things were not perfectly symmetric)? *)
  Hypothesis ilink_sym: forall p c,
      Intermediate.linkable_programs p c ->
      ilink p c = ilink c p.
  Hypothesis slink_sym: forall p c,
      Source.linkable_programs p c ->
      slink p c = slink c p.
  Hypothesis linkability_sym : forall Cs p,
    Source.linkable_programs Cs p ->
    Source.linkable_programs p Cs.

  (* Definability *)
  (* CH: this should now be related to what Arthur proved:
         - TODO his proof is for complete programs, no linking
           + might need to use source decomposition too?
           + just disjointness + partialization of things might be enough? (weaker than decomposition)
         - TODO his current proof gives us at most the program_behaves conclusion,
           not the conclusions about interfaces and closedness,
           and linkability (maybe from previous point) *)

  Hypothesis definability_with_linking:
    forall p c t,
      Intermediate.linkable_programs p c ->
      Intermediate.closed_program (ilink p c) ->
      program_behaves (I.CS.sem (ilink p c)) (Terminates t) ->
        (* CH: last premise naive, it should instead take trace prefixes *)
    exists p' c',
      Source.prog_interface p' = Intermediate.prog_interface p /\
      Source.prog_interface c' = Intermediate.prog_interface c /\
      Source.linkable_programs p' c' /\
      Source.closed_program (slink p' c') /\
      program_behaves (S.CS.sem (slink p' c')) (Terminates t).

  (* FCC *)
  Hypothesis I_simulates_S:
    forall p,
      Source.closed_program p ->
      Source.well_formed_program p ->
    forall tp,
      compile_program p = Some tp ->
      forward_simulation (S.CS.sem p) (I.CS.sem tp).

  (* BCC *)
  (* We derive BCC from FCC as in CompCert *)
  Corollary S_simulates_I:
    forall p,
      Source.closed_program p ->
      Source.well_formed_program p ->
    forall tp,
      compile_program p = Some tp ->
      backward_simulation (S.CS.sem p) (I.CS.sem tp).
  Proof.
    intros.
    apply forward_to_backward_simulation.
    - apply I_simulates_S; auto.
    - apply S.CS.receptiveness.
    - apply I.CS.determinacy.
  Qed.

(* CH: TODO: turn all admits in the code into assumed lemmas *)

Hypothesis close_the_diagram : forall t t' p Cs,
  program_behaves (S.PS.sem Cs (Source.prog_interface p)) (Terminates t) ->
  program_behaves (S.PS.sem Cs (Source.prog_interface p)) (Goes_wrong t') ->
  behavior_prefix t' (Terminates t) ->
  undef_in (Source.main_comp (Source.program_link p Cs)) t'
           (Source.prog_interface p).

(* RB: I have pushed here a couple of details that maybe should be external:
    - The symmetry in prog_interface.
    - The lemma that if two intermediate interfaces coincide, the interfaces of
      their corresponding sources do as well.  *)
Hypothesis I_interface_preserves_S_closedness_l :
  forall p1 p1' p1_c p1'_c p2,
    Source.closed_program (slink p1 p2) ->
    compile_program p1 = Some p1_c ->
    compile_program p1' = Some p1'_c ->
    Intermediate.prog_interface p1'_c = Intermediate.prog_interface p1_c ->
    Source.closed_program (slink p1' p2).

Hypothesis I_interface_preserves_closedness_r :
  forall p1 p2 p2',
    Intermediate.closed_program (ilink p1 p2) ->
    Intermediate.prog_interface p2 = Intermediate.prog_interface p2' ->
    Intermediate.closed_program (ilink p1 p2').

Section RSC_DC_MD.
  Variable p: Source.program.
  Variable p_compiled: Intermediate.program.
  Variable Ct: Intermediate.program.

  (* Some reasonable assumptions about our programs *)

  Hypothesis successfull_compilation:
    compile_program p = Some p_compiled.

  Hypothesis linkability:
    Intermediate.linkable_programs p_compiled Ct.

  Hypothesis closedness:
    Intermediate.closed_program (ilink p_compiled Ct).

  (* Main Theorem *)

  Theorem RSC_DC_MD:
    forall t,
      program_behaves (I.CS.sem (ilink p_compiled Ct)) (Terminates t) ->
        (* CH: last premise naive, it should instead take trace prefixes *)
    exists Cs beh,
      Source.prog_interface Cs = Intermediate.prog_interface Ct /\
      Source.linkable_programs p Cs /\
      Source.closed_program (slink p Cs) /\
      program_behaves (S.CS.sem (Source.program_link p Cs)) beh /\
      exists t',
        (beh = Terminates t' /\ behavior_prefix t (Terminates t')) \/
          (* CH: last disjunct naive, should consider arbitrary behaviors *)
        (beh = Goes_wrong t' /\ behavior_prefix t' (Terminates t) /\
         undef_in (Source.main_comp (Source.program_link p Cs)) t' (Source.prog_interface p)).
  Proof.
    intros t Hbeh.

    (* intermediate decomposition (for p_compiled) *)
    assert (not_wrong (Terminates t)) as Hsafe_beh. { simpl. auto. }
    pose proof Intermediate.Decomposition.decomposition_with_safe_behavior
      linkability Hbeh Hsafe_beh as HP_decomp.

    (* CH: if we had undefined behavior we would use this *)
    (* destruct (decomposition_with_refinement linkability Hbeh) *)
    (*   as [beh' [Hbeh' Hbeh_improves]]. *)
    
    (* definability *)
    destruct (definability_with_linking linkability closedness Hbeh)
      as [P' [Cs [Hsame_iface1 [Hsame_iface2 [P'_Cs_linkability [P'_Cs_closedness HP'_Cs_beh]]]]]].

    (* FCC *)

    (* CH: When is a program compilable (compile_prog returns Some)?
           - Source.well_formed_program probably enough, and we have it from P'_Cs_linkability *)
    (* CH: Might use separate_compilation' for proving the assert below,
           but we don't know that compile_program (slink P' Cs) = Some something anyway ?
           Definability needs to give us enough to obtain that the program can be properly compiled. *)
    assert (exists P'_compiled Cs_compiled,
               compile_program P' = Some P'_compiled /\
               compile_program Cs = Some Cs_compiled /\
               compile_program (slink P' Cs) = Some (ilink P'_compiled Cs_compiled))
      as HP'_Cs_compiles. {
      (* the definability output can be splitted in two programs *)
      (* probably need partialize to obtain them *)
      admit.
    }
    destruct HP'_Cs_compiles
      as [P'_compiled [Cs_compiled [HP'_compiles [HCs_compiles HP'_Cs_compiles]]]].
    assert (program_behaves (I.CS.sem (ilink P'_compiled Cs_compiled)) (Terminates t))
      as HP'_Cs_compiled_beh. {
      apply forward_simulation_same_safe_behavior
        with (L2:=I.CS.sem (ilink P'_compiled Cs_compiled)) in HP'_Cs_beh;
        simpl; eauto.
      apply I_simulates_S; auto.
      - apply Source.linking_well_formedness; auto.
    }

    (* intermediate decomposition (for Cs_compiled) *)
    assert (Intermediate.linkable_programs Cs_compiled P'_compiled) as linkability'. {
      eapply compilation_preserves_linkability with (p:=Cs) (c:=P'); eauto.
      apply Source.linkable_sym. auto.
    }
    rewrite <- ilink_sym in HP'_Cs_compiled_beh; [| assumption].
    pose proof Intermediate.Decomposition.decomposition_with_safe_behavior
         linkability' HP'_Cs_compiled_beh Hsafe_beh as HCs_decomp.

    (* intermediate composition *)
    assert (Intermediate.prog_interface Ct = Intermediate.prog_interface Cs_compiled)
      as Hctx_same_iface. {
      symmetry. erewrite compilation_preserves_interface.
      rewrite <- Hsame_iface2. reflexivity. auto.
    }
    rewrite Hctx_same_iface in HP_decomp.
    assert (Intermediate.prog_interface p_compiled = Intermediate.prog_interface P'_compiled) as Hprog_same_iface. {
      symmetry. erewrite compilation_preserves_interface.
      apply Hsame_iface1. auto.
    }
    rewrite <- Hprog_same_iface in HCs_decomp.

    assert (Intermediate.linkable_programs p_compiled Cs_compiled)
      as linkability'' by admit.
    assert (Intermediate.closed_program (ilink p_compiled Cs_compiled))
      as HpCs_compiled_closed
      by (apply (I_interface_preserves_closedness_r closedness Hctx_same_iface)).
    assert (Intermediate.well_formed_program (ilink p_compiled Cs_compiled))
      as HpCs_compiled_well_formed
      by (apply Intermediate.linking_well_formedness; assumption).

    pose proof composition_for_termination linkability'' HpCs_compiled_closed
         HpCs_compiled_well_formed HP_decomp HCs_decomp as HpCs_compiled_beh.

    assert (Source.closed_program (slink p Cs)) as Hclosed_p_Cs
      by (apply (I_interface_preserves_S_closedness_l
                   P'_Cs_closedness HP'_compiles successfull_compilation
                   Hprog_same_iface)).
    assert (Source.linkable_programs p Cs) as Hlinkable_p_Cs by admit.
    assert (Source.well_formed_program (slink p Cs)) as Hwf_p_Cs
      by (apply Source.linking_well_formedness; assumption).

    (* BCC *)
    assert (exists beh1,
               program_behaves (S.CS.sem (slink p Cs)) beh1 /\
               behavior_improves beh1 (Terminates t)) as HpCs_beh. {
      apply backward_simulation_behavior_improves
        with (L1:=S.CS.sem (slink p Cs)) in HpCs_compiled_beh; auto.
      - apply S_simulates_I.
        + assumption.
        + assumption.
        + apply separate_compilation; try assumption.
    }
    destruct HpCs_beh as [pCs_beh [HpCs_beh HpCs_beh_imp]].
    exists Cs. exists pCs_beh.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    - inversion HpCs_beh_imp.
      + exists t. left. split. by auto.
        exists (Terminates E0). simpl. rewrite E0_right. reflexivity.
      + destruct H as [t' [Hgoes_wrong Hprefix]].
        exists t'. right. repeat split; auto.
       (* blame UB -- Guglielmo working on proof *)
        rewrite slink_sym in HpCs_beh; [| assumption].
        apply Source.Decomposition.decomposition_with_refinement_and_blame in HpCs_beh;
          try assumption.
        destruct HpCs_beh as [b [H1 [H2 | H2]]].
        + subst pCs_beh. subst b.
          eapply close_the_diagram.
          - pose proof (compilation_preserves_interface p p_compiled
                                           successfull_compilation) as HH.
            assert(Source.prog_interface P' = Source.prog_interface p) as HHH
                by congruence.
            rewrite <- HHH.
            eapply Source.Decomposition.decomposition_with_safe_behavior.
            + apply linkability_sym; assumption.
            + setoid_rewrite slink_sym. eassumption.
            + apply linkability_sym; assumption.
            + easy.
          - assumption.
          - assumption.
        + destruct H2 as [t'' [H21 [H22 H23]]].
          subst pCs_beh. injection H21; intro H21'. subst t''.
          setoid_rewrite slink_sym; assumption.
  Admitted.
End RSC_DC_MD.
