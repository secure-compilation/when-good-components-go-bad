Require Import Common.Definitions.
Require Import Common.Linking.
Require Import Common.Blame.
Require Import Common.CompCertExtensions.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

  Hypothesis decomposition_prefix :
    forall p c,
      well_formed_program p ->
      well_formed_program c ->
      linkable (prog_interface p) (prog_interface c) ->
      linkable_mains p c ->
    forall m,
      not_wrong_finpref m -> (* needed here, and will have it in main proof *)
      does_prefix (CS.sem (program_link p c)) m ->
      does_prefix (PS.sem p (prog_interface c)) m.

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

Module Type S2I_Sig (Source : Source_Sig) (Intermediate : Intermediate_Sig).
  Parameter matching_mains : Source.program -> Intermediate.program -> Prop.

  Hypothesis matching_mains_equiv : forall p1 p2 p3,
    matching_mains p1 p2 ->
    matching_mains p1 p3 ->
    Intermediate.matching_mains p2 p3.
End S2I_Sig.

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

(* CH: To match the paper this should be weakened even more to work with prefixes *)
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

  Hypothesis forward_simulation_same_safe_prefix:
    forall p p_compiled m,
      Source.closed_program p ->
      Source.well_formed_program p ->
      does_prefix (Source.CS.sem p) m ->
      not_wrong_finpref m ->
      compile_program p = Some p_compiled ->
      does_prefix (Intermediate.CS.sem p_compiled) m.

  Hypothesis backward_simulation_behavior_improves_prefix :
    forall p p_compiled m,
      Source.closed_program p ->
      Source.well_formed_program p ->
      compile_program p = Some p_compiled ->
      does_prefix (Intermediate.CS.sem p_compiled) m ->
    exists b,
      program_behaves (Source.CS.sem p) b /\
      (prefix m b \/ behavior_improves_finpref b m).

End Compiler_Sig.
