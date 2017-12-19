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
Require Import S2I.Compiler.
Require Import S2I.Definitions.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RSC_DC_MD.
  Variable p: Source.program.
  Variable p_compiled: Intermediate.program.
  Variable Ct: Intermediate.program.

  Let slink := Source.program_link.
  Let ilink := Intermediate.program_link.

  (* Some reasonable assumptions about our programs *)

  Hypothesis successfull_compilation:
    compile_program p = Some p_compiled.

  Hypothesis linkability:
    Intermediate.linkable_programs p_compiled Ct.

  Hypothesis closedness:
    Intermediate.closed_program (ilink p_compiled Ct).

  (* some useful functions on closed programs *)

  Definition s_main_comp (p: Source.program): Component.id :=
    match Source.prog_main p with
    | Some (mainC, _) => mainC
    | None => 0
    end.

  Definition i_main_comp (p: Intermediate.program): Component.id :=
    match Intermediate.prog_main p with
    | Some (mainC, _) => mainC
    | None => 0
    end.

  (* Some facts (provable and to prove) about linking and compilation *)

  Hypothesis compilation_preserves_interface:
    forall p p_compiled,
      (*Source.prog_main p = None -> this is needed because of the main wrapping *)
      compile_program p = Some p_compiled ->
      Intermediate.prog_interface p_compiled = Source.prog_interface p.

  (* This should be provable, although we may have to slightly change the compiler *)
  (* (e.g. procedure id & label generation should be local to the component *)
  Hypothesis separate_compilation:
    forall p c p_comp c_comp,
      Source.linkable_programs p c ->
      compile_program p = Some p_comp ->
      compile_program c = Some c_comp ->
      compile_program (slink p c) = Some (ilink p_comp c_comp).

  Hypothesis compilation_preserves_linkability:
    forall p p_compiled c c_compiled,
      Source.linkable_programs p c ->
      compile_program p = Some p_compiled ->
      compile_program c = Some c_compiled ->
      Intermediate.linkable_programs p_compiled c_compiled.

  Hypothesis slink_sym:
    forall p c,
      slink p c = slink c p.

  Hypothesis ilink_sym:
    forall p c,
      ilink p c = ilink c p.

  (* Definability *)

  Hypothesis definability_with_linking:
    forall p c t,
      Intermediate.linkable_programs p c ->
      Intermediate.closed_program (ilink p c) ->
      program_behaves (I.CS.sem (ilink p c)) (Terminates t) ->
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

  (* Main Theorem *)

  Theorem RSC_DC_MD:
    forall t,
      program_behaves (I.CS.sem (ilink p_compiled Ct)) (Terminates t) ->
    exists Cs beh,
      Source.prog_interface Cs = Intermediate.prog_interface Ct /\
      program_behaves (S.CS.sem (Source.program_link p Cs)) beh /\
      exists t',
        (beh = Terminates t' /\ behavior_prefix t (Terminates t')) \/
        (beh = Goes_wrong t' /\ behavior_prefix t' (Terminates t) /\
         undef_in (s_main_comp (Source.program_link p Cs)) t' (Source.prog_interface p)).
  Proof.
    intros t Hbeh.

    (* decomposition *)
    destruct (decomposition_with_refinement linkability Hbeh)
      as [beh' [Hbeh' Hbeh_improves]].

    inversion Hbeh_improves; subst;
      try (destruct H as [? []]; discriminate).

    (* definability *)
    destruct (definability_with_linking linkability closedness Hbeh)
      as [P' [Cs [Hsame_iface1 [Hsame_iface2 [P'_Cs_linkability [P'_Cs_closedness HP'_Cs_beh]]]]]].

    (* forward simulation *)
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

    (* decomposition *)
    assert (not_wrong (Terminates t)) as Hsafe_beh. { simpl. auto. }
    pose proof decomposition_with_safe_behavior linkability Hbeh Hsafe_beh as HP_decomp.
    assert (Intermediate.linkable_programs Cs_compiled P'_compiled) as linkability'. {
      eapply compilation_preserves_linkability with (p:=Cs) (c:=P'); eauto.
      apply Source.linkable_sym. auto.
    }
    rewrite ilink_sym in HP'_Cs_compiled_beh.
    pose proof decomposition_with_safe_behavior linkability'
         HP'_Cs_compiled_beh Hsafe_beh as HCs_decomp.

    (* composition *)
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

    assert (Intermediate.linkable_programs Cs_compiled p_compiled) as linkability''. {
      admit.
    }
    enough (Intermediate.closed_program (ilink Cs_compiled p_compiled))
      as HpCs_compiled_closed.
    enough (Intermediate.well_formed_program (ilink Cs_compiled p_compiled))
      as HpCs_compiled_well_formed.
    pose proof composition_for_termination linkability'' HpCs_compiled_closed
         HpCs_compiled_well_formed HCs_decomp HP_decomp as HpCs_compiled_beh.

    (* backward simulation *)
    assert (exists beh1,
               program_behaves (S.CS.sem (slink Cs p)) beh1 /\
               behavior_improves beh1 (Terminates t)) as HpCs_beh. {
      apply backward_simulation_behavior_improves
        with (L1:=S.CS.sem (slink Cs p)) in HpCs_compiled_beh; auto.
      - apply S_simulates_I.
        + admit.
        + admit.
        + admit.
    }
    destruct HpCs_beh as [pCs_beh [HpCs_beh HpCs_beh_imp]].
    exists Cs. exists pCs_beh.
    repeat split; auto.
    - erewrite slink_sym. assumption.
    - inversion HpCs_beh_imp.
      + exists t. left. split. auto.
        exists (Terminates E0). simpl. rewrite E0_right. reflexivity.
      + destruct H as [t' [Hgoes_wrong Hprefix]].
        exists t'. right. repeat split; auto.
        (* blame UB *)
        admit.

    - admit.
    - admit.
  Admitted.
End RSC_DC_MD.