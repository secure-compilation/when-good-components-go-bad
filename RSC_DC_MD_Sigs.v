Require Import Common.Definitions.
Require Import Common.Linking.
Require Import Common.Blame.
Require Import Common.CompCertExtensions.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.SmallstepUB.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type Target_Sig.
  Parameter program : Type.

  Parameter prog_interface : program -> Program.interface.

  Parameter well_formed_program : program -> Prop.

  Parameter closed_program : program -> Prop.

  Parameter linkable_mains : program -> program -> Prop.

  Parameter matching_mains : program -> program -> Prop.

  Parameter program_link : program -> program -> program.

  Local Axiom linkable_mains_sym : forall p1 p2,
    linkable_mains p1 p2 -> linkable_mains p2 p1.

  Local Axiom program_linkC : forall p1 p2,
    well_formed_program p1 ->
    well_formed_program p2 ->
    linkable (prog_interface p1) (prog_interface p2) ->
    program_link p1 p2 = program_link p2 p1.

  Local Axiom linking_well_formedness : forall p1 p2,
    well_formed_program p1 ->
    well_formed_program p2 ->
    linkable (prog_interface p1) (prog_interface p2) ->
    well_formed_program (program_link p1 p2).

  Local Axiom interface_preserves_closedness_r : forall p1 p2 p2',
    well_formed_program p1 ->
    well_formed_program p2' ->
    prog_interface p2 = prog_interface p2' ->
    linkable (prog_interface p1) (prog_interface p2) ->
    closed_program (program_link p1 p2) ->
    linkable_mains p1 p2 ->
    matching_mains p2 p2' ->
    closed_program (program_link p1 p2').

  Local Axiom matching_mains_equiv : forall p1 p2 p3,
      matching_mains p1 p2 ->
      matching_mains p1 p3 ->
      matching_mains p2 p3.

  Module CS.
    Parameters state genvtype: Type.
    Parameter step1: genvtype -> state -> Events.trace -> state -> Prop.
    Parameter step2: genvtype -> state -> Events.trace -> state -> Prop.
    Parameter initial_state: forall (p: program), state -> Prop.
    Parameter final_state: forall (p: program), state -> Prop.
    Parameter globalenv: forall (p: program), genvtype.

    Parameter current_comp: state -> Component.id.

    Definition sem1 (p: program) := Semantics_gen step1 (initial_state p) (final_state p)
                                      (globalenv p).
    Definition sem2 (p: program) := Semantics_gen step2 (initial_state p) (final_state p)
                                      (globalenv p).
    Definition sem_restricted_UB (p: program) :=
      L_restricted_UB step1 step2 (initial_state p) (final_state p) (globalenv p).

  End CS.

  Definition allowed_UB (intf: Program.interface) (s: CS.state) :=
    CS.current_comp s \in domm intf.

  Local Axiom det_sem1 : forall p, determinate (CS.sem1 p).
  Local Axiom det_sem2 : forall p, determinate (CS.sem2 p).
  Local Axiom det_sem_restricted : forall p aUB, determinate (CS.sem_restricted_UB p aUB).

  Local Axiom initial_state_main :
    forall p s,
      (CS.initial_state p s) ->
      CS.current_comp s = Component.main.
  
  Local Axiom non_empty_trace_last_comp :
    forall p aUB g s s' t,
      t <> [] ->
      (star (step (CS.sem_restricted_UB p aUB))) g s t s' ->
      last_comp t = CS.current_comp s'.
  
  Local Axiom component_conservation_on_empty_trace :
    forall p aUB g s s',
      (star (step (CS.sem_restricted_UB p aUB))) g s [] s' ->
      CS.current_comp s = CS.current_comp s'.
  
  Local Axiom sem_restricted_UB_lem :
    forall p allowed_UB s t s',
      Step (CS.sem2 p) s t s' ->
      let sem := (CS.sem_restricted_UB p allowed_UB) in
      (Step sem s t s') \/ not (exists t s', Step sem s t s').
 
  Local Axiom sem_restricted_UB_generalises_sem2 :
    forall p allowed_UB g s s' t,
      (step (CS.sem_restricted_UB p allowed_UB)) g s t s' ->
      (step (CS.sem2 p)) g s t s'.

  Local Axiom compose_mergeable_interfaces :
    forall p c,
      linkable (prog_interface p) (prog_interface c) ->
      closed_program (program_link p c) ->
      mergeable_interfaces (prog_interface p) (prog_interface c).

  Local Axiom recombination_blame_prefix :
    forall p c p' c',
      well_formed_program p ->
      well_formed_program c ->
      well_formed_program p' ->
      well_formed_program c' ->
      mergeable_interfaces (prog_interface p) (prog_interface c) ->
      prog_interface p = prog_interface p' ->
      prog_interface c = prog_interface c' ->
      closed_program (program_link p c) ->
      closed_program (program_link p' c') ->
    forall m,
      does_prefix (CS.sem_restricted_UB (program_link p c) (allowed_UB (prog_interface c))) m ->
      does_prefix (CS.sem1 (program_link p' c')) m ->
      does_prefix (CS.sem1 (program_link p c')) m.

  Local Axiom recombination_blame_prefix_final_UB :
    forall p c p' c',
      well_formed_program p ->
      well_formed_program c ->
      well_formed_program p' ->
      well_formed_program c' ->
      mergeable_interfaces (prog_interface p) (prog_interface c) ->
      prog_interface p = prog_interface p' ->
      prog_interface c = prog_interface c' ->
      closed_program (program_link p c) ->
      closed_program (program_link p' c') ->
    forall m,
      does_prefix (CS.sem_restricted_UB (program_link p c) (allowed_UB (prog_interface c)))
        (FGoes_wrong m) ->
      does_prefix (CS.sem1 (program_link p' c')) (FTbc m) ->
      undef_in m (prog_interface p) ->
      does_prefix (CS.sem1 (program_link p c')) (FGoes_wrong m).

  Local Axiom state_component_on_linking :
    forall p aUB c g s s' t,
      well_formed_program p ->
      well_formed_program c ->
      linkable (prog_interface p) (prog_interface c) ->
      closed_program (program_link p c) ->
      ((CS.initial_state (program_link p c) s) \/ t <> []) ->
      (star (step (CS.sem_restricted_UB p aUB))) g s t s' ->
      (CS.current_comp s' \in (domm (prog_interface c)))
      \/ (CS.current_comp s' \in (domm (prog_interface p))).
  
  Local Axiom definability_with_linking :
    forall p c b m,
      well_formed_program p ->
      well_formed_program c ->
      linkable (prog_interface p) (prog_interface c) ->
      closed_program (program_link p c) ->
      program_behaves (CS.sem2 (program_link p c)) b ->
      prefix m b ->
      not_wrong_finpref m ->
    exists p' c',
      prog_interface p' = prog_interface p /\
      prog_interface c' = prog_interface c /\
      matching_mains p p' /\
      matching_mains c c' /\
      well_formed_program p' /\
      well_formed_program c' /\
      closed_program (program_link p' c') /\
      does_prefix (CS.sem1 (program_link p' c')) m.

End Target_Sig.
