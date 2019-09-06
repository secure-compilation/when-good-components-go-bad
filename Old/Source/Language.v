Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Lib.Extra.
Require Import Source.Language.
Import Source.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From extructures Require Import ord fset fmap.

Local Open Scope fset_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Module Source.

  Lemma program_linkKR p1 p2 :
    well_formed_program p1 ->
    well_formed_program p2 ->
    linkable (prog_interface p1) (prog_interface p2) ->
    program_unlink (domm (prog_interface p2)) (program_link p1 p2) = p2.
  Proof.
    move=> wf1 wf2 l12.
    rewrite link_sym // program_linkKL //.
    exact: linkable_sym.
  Qed.

  Lemma linked_programs_main_component_origin:
    forall p1 p2,
      well_formed_program p1 ->
      well_formed_program p2 ->
      linkable (prog_interface p1) (prog_interface p2) ->
      closed_program (program_link p1 p2) ->
      Component.main \in domm (prog_interface p1) \/
      Component.main \in domm (prog_interface p2).
  Proof.
    move=> p1 p2 wf1 wf2 [_ Hdis] Hclosed.
    have := cprog_main_existence Hclosed.
    rewrite /prog_main /find_procedure /= unionmE -!mem_domm.
    rewrite !wfprog_defined_procedures // !mem_domm.
    case: (prog_procedures p1 Component.main)=> [main_procs'|] //=; eauto.
    by case: (prog_procedures p2 Component.main)=> [main_procs'|] //=; eauto.
  Qed.

  Fixpoint initialize_buffer
           (Cmem: ComponentMemory.t) (b: Block.id) (values: list value)
    : ComponentMemory.t :=
    let fix init m vs i :=
        match vs with
        | [] => m
        | v :: vs' =>
          match ComponentMemory.store m b i v with
          | Some m' =>
            init m' vs' (1+i)%Z
          | None =>
            (* bad case that shouldn't happen, just return memory *)
            init m vs' (1+i)%Z
          end
        end
    in init Cmem values 0%Z.

End Source.
