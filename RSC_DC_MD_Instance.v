Require Import RSC_DC_MD_Sigs.

Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Source.Blame.
Require Import Intermediate.Machine.
Require Import Intermediate.Recombination.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import Definability.

Set Bullet Behavior "Strict Subproofs".

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
    @Source.Blame.Blame.blame_program.

End Source_Instance.

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

  Definition compose_mergeable_interfaces :=
    @Intermediate.compose_mergeable_interfaces.

  Definition recombination_prefix :=
    @Intermediate.Recombination.recombination_prefix.
End Intermediate_Instance.

Module S2I_Instance <: S2I_Sig (Source_Instance) (Intermediate_Instance).
  Definition matching_mains :=
    @S2I.Definitions.matching_mains.

  Definition matching_mains_equiv :=
    @S2I.Definitions.matching_mains_equiv.
End S2I_Instance.

Module Linker_Instance <: Linker_Sig (Source_Instance)
                                     (Intermediate_Instance)
                                     (S2I_Instance).
  Definition definability_with_linking :=
    @RobustImp.Source.Definability.definability_with_linking'.
End Linker_Instance.

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

  (* Definition S_simulates_I := *)
  (*   @Compiler.S_simulates_I. *)

  Theorem forward_simulation_same_safe_prefix:
    forall p p_compiled c c_compiled m,
      linkable (Source.prog_interface p) (Source.prog_interface c) ->
      Source.closed_program (Source.program_link p c) ->
      Source.well_formed_program p ->
      Source.well_formed_program c ->
      CompCertExtensions.does_prefix (Source_Instance.CS.sem (Source.program_link p c)) m ->
      CompCertExtensions.not_wrong_finpref m ->
      compile_program p = Some p_compiled ->
      compile_program c = Some c_compiled ->
      CompCertExtensions.does_prefix (Intermediate_Instance.CS.sem (Intermediate.program_link p_compiled c_compiled)) m.
  Proof.
    intros p p_compiled c c_compiled m
           Hlinkable Hclosed Hwfp Hwfc Hprefix Hnot_wrong Hcompp Hcompc.
    pose proof Source.linking_well_formedness Hwfp Hwfc Hlinkable as Hwfpc.
    destruct (Compiler.well_formed_compilable _ Hwfpc) as [pc_compiled Hcomppc].
    pose proof Compiler.forward_simulation_same_safe_prefix _ _ _
         Hclosed Hwfpc Hprefix Hnot_wrong Hcomppc
      as [beh [Hbeh Hprefix_beh]].
    pose proof Compiler.separate_compilation_weaker _ _ _ _ _
         Hwfp Hwfc Hlinkable Hcompp Hcompc Hcomppc
      as Hsc.
    exists beh. split.
    - apply Hsc. exact Hbeh.
    - exact Hprefix_beh.
  Qed.
  
  Theorem backward_simulation_behavior_improves_prefix :
    forall p p_compiled c c_compiled m,
      linkable (Source.prog_interface p) (Source.prog_interface c) ->
      Source.closed_program (Source.program_link p c) ->
      Source.well_formed_program p ->
      Source.well_formed_program c ->
      compile_program p = Some p_compiled ->
      compile_program c = Some c_compiled ->
      CompCertExtensions.does_prefix (Intermediate_Instance.CS.sem (Intermediate.program_link p_compiled c_compiled)) m ->
    exists b,
      Behaviors.program_behaves (Source_Instance.CS.sem (Source.program_link p c)) b /\
      (CompCertExtensions.prefix m b \/ CompCertExtensions.behavior_improves_finpref b m).
  Proof.
    intros p p_compiled c c_compiled m
           Hlinkable Hclosed Hwfp Hwfc Hcompp Hcompc Hprefix.
    (* Auxiliary results, some used multiple times, some need to be in scope. *)
    pose proof Source.linking_well_formedness Hwfp Hwfc Hlinkable as Hwfpc.
    destruct (Compiler.well_formed_compilable _ Hwfpc) as [pc_compiled Hcomppc].
    pose proof Compiler.separate_compilation_weaker _ _ _ _ _
         Hwfp Hwfc Hlinkable Hcompp Hcompc Hcomppc
      as Hsc.
    eapply Compiler.backward_simulation_behavior_improves_prefix;
      try eassumption.
    - destruct Hprefix as [beh [Hbeh Hprefix_beh]].
      exists beh. split.
      + apply Hsc. exact Hbeh.
      + exact Hprefix_beh.
  Qed.
End Compiler_Instance.
