Require Export Common.Maps.

Require Export Coq.Bool.Bool.
Require Export Coq.Lists.List.
Require Export Coq.Arith.Arith.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Numbers.BinNums.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export ListNotations.
Open Scope list_scope.

Module Procedure.
  Definition id := nat.

  Definition eqb (id1 id2 : id) := Nat.eqb id1 id2.

  Definition main : id := 0.
End Procedure.

Module Component.
  Definition id := nat.

  Record interface := mkCompInterface {
    export: {fset Procedure.id};
    import: {fset Component.id * Procedure.id}
  }.

  Definition is_importing CI C P : Prop := (C,P) \in import CI.
  Definition is_exporting CI P : Prop := P \in export CI.

  Definition eqb (id1 id2 : id) := Nat.eqb id1 id2.

  (* Used only as the main procedure for the source language. *)
  Definition main : id := 0.
End Component.

Module Program.
  Definition interface := NMap Component.interface.
  Definition has_component (Is: interface) (C: Component.id) (CI: Component.interface) :=
    getm Is C = Some CI.
  Definition has_component_id (Is: interface) (C: Component.id) :=
    C \in domm Is.
End Program.

Definition exported_procedure
           (Is : Program.interface)
           (C : Component.id) (P : Procedure.id) :=
  exists CI,
    Program.has_component Is C CI /\ Component.is_exporting CI P.

Definition imported_procedure
           (Is : Program.interface)
           (C C': Component.id) (P : Procedure.id) : Prop :=
  exists CI,
    Program.has_component Is C CI /\ Component.is_importing CI C' P.

Definition imported_procedure_b
           (Is : Program.interface)
           (C C': Component.id) (P : Procedure.id) : bool :=
  match getm Is C with
  | Some CI => (C', P) \in Component.import CI
  | None => false
  end.

Lemma imported_procedure_iff :
  forall Is C C' P,
    imported_procedure Is C C' P <-> imported_procedure_b Is C C' P = true.
Proof.
  intros Is C C' P.
  split.
  - intros Himport.
    destruct Himport as [CI [HCI Himport]].
    unfold Program.has_component in HCI.
    unfold Component.is_importing in Himport.
    unfold imported_procedure_b.
    rewrite HCI Himport.
    reflexivity.
  - intros Himport.
    unfold imported_procedure.
    unfold imported_procedure_b in Himport.
    destruct (Is C) eqn:Hfind;
      try discriminate.
    eexists.
    unfold Program.has_component, Component.is_importing.
    split; eassumption.
Qed.

Lemma has_component_in_domm_prog_interface Piface Cid Ciface :
  Program.has_component Piface Cid Ciface ->
  Cid \in domm Piface.
Proof.
  intros Hhas_comp.
  unfold Program.has_component in Hhas_comp.
  apply /dommP.
  eauto.
Qed.

Lemma imported_procedure_unionm_left :
  forall {Ciface C},
    C \notin domm Ciface ->
  forall {Piface P C'},
    imported_procedure (unionm Piface Ciface) C C' P =
    imported_procedure Piface C C' P.
Proof.
  intros Ciface C Hnotin Piface P C'.
  unfold imported_procedure, Program.has_component.
  rewrite unionmE.
  assert (HNone : Ciface C = None).
  { by apply /dommPn. }
  rewrite HNone.
  destruct (Piface C) eqn:Hcase;
    rewrite Hcase || idtac "ExStructures 0.1 legacy rewrite inactive";
    done.
Qed.

Class HasTurn A := {
  turn_of : A -> Program.interface -> bool
}.
