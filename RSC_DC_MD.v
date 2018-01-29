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

  (* RB: Add shortcuts for program_interface. *)
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
      Source.well_formed_program p ->
      Source.well_formed_program c ->
      linkable (Source.prog_interface p) (Source.prog_interface c) ->
      compile_program p = Some p_comp ->
      compile_program c = Some c_comp ->
      compile_program (slink p c) = Some (ilink p_comp c_comp).
  (* CH: because of the Somes might also want something of the following form: *)
  (* CH: in general the use of options doesn't seem to make anything simpler,
         but maybe that's inherited from CompCert? *)
  Hypothesis separate_compilation':
    forall p c pc_comp,
      Source.well_formed_program p ->
      Source.well_formed_program c ->
      linkable (Source.prog_interface p) (Source.prog_interface c) ->
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

  Hypothesis compilation_preserves_well_formedness:
    forall p p_compiled,
      Source.well_formed_program p ->
      compile_program p = Some p_compiled ->
      Intermediate.well_formed_program p_compiled.

  (* this should follow from preserving interfaces *)
  Hypothesis compilation_preserves_linkability:
    forall p p_compiled c c_compiled,
      Source.well_formed_program p ->
      Source.well_formed_program c ->
      linkable (Source.prog_interface p) (Source.prog_interface c) ->
      compile_program p = Some p_compiled ->
      compile_program c = Some c_compiled ->
      linkable (Intermediate.prog_interface p_compiled) (Intermediate.prog_interface c_compiled).

  (* RB: Restoring and correcting these. *)
  Hypothesis ilink_sym: forall p c,
      linkable (Intermediate.prog_interface p) (Intermediate.prog_interface c) ->
      ilink p c = ilink c p.
  Hypothesis slink_sym: forall p c,
      linkable (Source.prog_interface p) (Source.prog_interface c) ->
      slink p c = slink c p.

  (* Definability *)
  (* CH: this should now be related to what Arthur proved:
         - TODO his proof is for complete programs, no linking
           + might need to use source decomposition too?
           + just disjointness + partialization of things might be enough? (weaker than decomposition)
         - TODO his current proof gives us at most the program_behaves conclusion,
           not the conclusions about interfaces and closedness,
           and linkability (maybe from previous point) *)

  Hypothesis definability_with_linking:
    forall p c t m,
      Intermediate.well_formed_program p ->
      Intermediate.well_formed_program c ->
      linkable (Intermediate.prog_interface p) (Intermediate.prog_interface c) ->
      Intermediate.closed_program (ilink p c) ->
      program_behaves (I.CS.sem (ilink p c)) t ->
      behavior_prefix m t ->
        (* CH: last premise naive, it should instead take trace prefixes
           RB: working on it *)
    exists p' c' t',
      Source.prog_interface p' = Intermediate.prog_interface p /\
      Source.prog_interface c' = Intermediate.prog_interface c /\
      Source.well_formed_program p' /\
      Source.well_formed_program c' /\
      Source.closed_program (slink p' c') /\
      program_behaves (S.CS.sem (slink p' c')) t' /\
      behavior_prefix m t'.

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

  Hypothesis well_formed_p : Source.well_formed_program p.
  Hypothesis well_formed_Ct : Intermediate.well_formed_program Ct.
  Hypothesis sound_interface_p_Ct : sound_interface (unionm (Source.prog_interface p) (Intermediate.prog_interface Ct)).
  Hypothesis fdisjoint_p_Ct : fdisjoint (domm (Source.prog_interface p)) (domm (Intermediate.prog_interface Ct)).

  Lemma linkability: linkable (Intermediate.prog_interface p_compiled) (Intermediate.prog_interface Ct).
  Proof. constructor.
         - apply compilation_preserves_interface in successfull_compilation.
           rewrite successfull_compilation. assumption.
         - apply compilation_preserves_interface in successfull_compilation.
           rewrite successfull_compilation. assumption.
  Qed.

  Hypothesis closedness:
    Intermediate.closed_program (ilink p_compiled Ct).

  (* Main Theorem *)

  Theorem RSC_DC_MD:
    forall t m,
      program_behaves (I.CS.sem (ilink p_compiled Ct)) (Terminates t) ->
      trace_prefix m t ->
        (* CH: last premise naive, it should instead take trace prefixes
           RB: working on it, still not arbitrary behaviors *)
    exists Cs beh,
      Source.prog_interface Cs = Intermediate.prog_interface Ct /\
      Source.well_formed_program Cs /\
      linkable (Source.prog_interface p) (Source.prog_interface Cs) /\
      Source.closed_program (slink p Cs) /\
      program_behaves (S.CS.sem (Source.program_link p Cs)) beh /\
      exists t',
        (beh = Terminates t' /\ behavior_prefix m (Terminates t')) \/
          (* CH: last disjunct naive, should consider arbitrary behaviors *)
        (beh = Goes_wrong t' /\ behavior_prefix t' (Terminates t) /\
         undef_in (Source.main_comp (Source.program_link p Cs)) t' (Source.prog_interface p)).
  Proof.
    intros t Hbeh.
    pose proof linkability as linkability.

    (* intermediate decomposition (for p_compiled) *)
    assert (not_wrong (Terminates t)) as Hsafe_beh. { simpl. auto. }
    pose proof
      compilation_preserves_well_formedness well_formed_p successfull_compilation
      as well_formed_p_compiled.
    pose proof Intermediate.Decomposition.decomposition_with_safe_behavior
      well_formed_p_compiled well_formed_Ct linkability Hbeh Hsafe_beh as HP_decomp.

    (* CH: if we had undefined behavior we would use this *)
    (* destruct (decomposition_with_refinement linkability Hbeh) *)
    (*   as [beh' [Hbeh' Hbeh_improves]]. *)
    
    (* definability *)
    destruct (definability_with_linking well_formed_p_compiled well_formed_Ct linkability closedness Hbeh)
      as [P' [Cs [Hsame_iface1 [Hsame_iface2 [well_formed_P' [well_formed_Cs [HP'Cs_closed HP'_Cs_beh]]]]]]].

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
      - apply Source.linking_well_formedness.
        rewrite <- Hsame_iface1 in linkability.
        rewrite <- Hsame_iface2 in linkability.
        apply linkability.
    }

    (* intermediate decomposition (for Cs_compiled) *)
    assert
      (linkable
         (Intermediate.prog_interface Cs_compiled)
         (Intermediate.prog_interface P'_compiled))
      as linkability'. {
      eapply compilation_preserves_linkability with (p:=Cs) (c:=P'); eauto.
      apply linkable_sym.
      (* RB: If [linkability] is not used for anything else, refactor these
         rewrites with the instance above, or craft a separate assumption. *)
      rewrite <- Hsame_iface1 in linkability.
      rewrite <- Hsame_iface2 in linkability.
      apply linkability.
    }
    rewrite <- ilink_sym in HP'_Cs_compiled_beh; [| assumption].
    pose proof compilation_preserves_well_formedness well_formed_P' HP'_compiles
      as well_formed_P'_compiled.
    pose proof compilation_preserves_well_formedness well_formed_Cs HCs_compiles
      as well_formed_Cs_compiled.
    pose proof Intermediate.Decomposition.decomposition_with_safe_behavior
         well_formed_Cs_compiled well_formed_P'_compiled
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

    assert (linkable (Intermediate.prog_interface p_compiled) (Intermediate.prog_interface Cs_compiled))
      as linkability''.
    {
      unfold linkable. split; try
        rewrite Hprog_same_iface;
        apply linkable_sym in linkability';
        now inversion linkability'.
    }
    assert (Intermediate.closed_program (ilink p_compiled Cs_compiled))
      as HpCs_compiled_closed
      by (apply (I_interface_preserves_closedness_r closedness Hctx_same_iface)).
    assert (Intermediate.well_formed_program (ilink p_compiled Cs_compiled))
      as HpCs_compiled_well_formed
      by (apply Intermediate.linking_well_formedness; assumption).

    pose proof composition_for_termination
         well_formed_p_compiled well_formed_Cs_compiled
         linkability'' HpCs_compiled_closed
         HP_decomp HCs_decomp as HpCs_compiled_beh.

    assert (Source.closed_program (slink p Cs)) as Hclosed_p_Cs
      by (apply (I_interface_preserves_S_closedness_l
                   HP'Cs_closed HP'_compiles successfull_compilation
                   Hprog_same_iface)).
    assert (linkable (Source.prog_interface p) (Source.prog_interface Cs))
      as Hlinkable_p_Cs. {
      inversion linkability'' as [sound_interface_p_Cs fdisjoint_p_Cs].
        constructor;
        (apply compilation_preserves_interface in HCs_compiles;
        apply compilation_preserves_interface in successfull_compilation;
        rewrite <- HCs_compiles; rewrite <- successfull_compilation;
        assumption).
    }
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
    - inversion HpCs_beh_imp as [pCs_beh_ok|].
      + split.
        * subst pCs_beh. assumption.
        * exists t. left. split. by auto.
          exists (Terminates E0). simpl. rewrite E0_right. reflexivity.
      + destruct H as [t' [Hgoes_wrong Hprefix]]. split.
        * subst pCs_beh. assumption.
        * exists t'. right. repeat split; auto.
        (* blame UB -- Guglielmo working on proof *)
      + rewrite slink_sym in HpCs_beh; [| assumption].
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
            + assumption.
            + assumption.
            + apply linkable_sym. rewrite HHH. assumption.
            + setoid_rewrite slink_sym. eassumption.
            + apply linkable_sym. rewrite HHH. assumption.
            + easy.
          - assumption.
          - assumption.
        + destruct H2 as [t'' [H21 [H22 H23]]].
          subst pCs_beh. injection H21; intro H21'. subst t''.
          setoid_rewrite slink_sym; assumption.
  Admitted.
End RSC_DC_MD.
