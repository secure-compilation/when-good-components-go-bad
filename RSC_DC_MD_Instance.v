Require Import RSC_DC_MD_Sigs.

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

  Definition decomposition_with_refinement :=
    @Intermediate.Decomposition.decomposition_with_refinement.

  Theorem decomposition_prefix :
    forall p c m,
      well_formed_program p ->
      well_formed_program c ->
      linkable (prog_interface p) (prog_interface c) ->
      linkable_mains p c ->
      CompCertExtensions.not_wrong_finpref m ->
      CompCertExtensions.does_prefix (CS.sem (program_link p c)) m ->
      CompCertExtensions.does_prefix (PS.sem p (prog_interface c)) m.
  Proof.
    (* We need some trivial reordering to match instance and interface. *)
    intros.
    now apply Intermediate.Decomposition.decomposition_prefix.
  Qed.

  Definition composition_prefix :=
    @Intermediate.Composition.composition_prefix.

  Definition compose_mergeable_interfaces :=
    @Intermediate.compose_mergeable_interfaces.
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
    @RobustImp.Source.Definability.definability_with_linking.
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

  Definition forward_simulation_same_safe_prefix :=
    @Compiler.forward_simulation_same_safe_prefix.

  Definition backward_simulation_behavior_improves_prefix :=
    @Compiler.backward_simulation_behavior_improves_prefix.
End Compiler_Instance.
