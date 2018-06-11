Require Import Common.Definitions.
Require Import Source.CS.
Require Import Source.PS.
Require Import Intermediate.CS.
Require Import Intermediate.PS.

Module S.
  Import Source.Language.
  Import Source.CS.
  Import Source.PS.
  Module CS := CS.
  Module PS := PS.
End S.

Module I.
  Import Intermediate.Machine.
  Import Intermediate.CS.
  Import Intermediate.PS.
  Module CS := CS.
  Module PS := PS.
End I.

Ltac simplify_turn :=
  S.PS.simplify_turn; I.PS.simplify_turn.

(* RB: The following should go into its own file. *)
Definition matching_mains (p1 : Language.Source.program)
                          (p2 : Machine.Intermediate.program) : Prop :=
  Language.Source.prog_main p1 = None <->
  Machine.Intermediate.prog_main p2 = None.

Require Import Intermediate.Machine.
Lemma matching_mains_trans : forall p1 p2 p3,
  matching_mains p1 p2 ->
  Intermediate.matching_mains p2 p3 ->
  matching_mains p1 p3.
Proof.
  unfold matching_mains, Intermediate.matching_mains.
  intros p1 p2 p3 H12 H23.
  split; intros HNone.
  - apply H12 in HNone.
    apply H23 in HNone.
    exact HNone.
  - apply H23 in HNone.
    apply H12 in HNone.
    exact HNone.
Qed.

Lemma matching_mains_equiv : forall p1 p2 p3,
  matching_mains p1 p2 ->
  matching_mains p1 p3 ->
  Intermediate.matching_mains p2 p3.
Proof.
  unfold matching_mains, Intermediate.matching_mains.
  intros p1 p2 p3 H12 H13.
  split; intros HNone.
  - apply H12 in HNone.
    apply H13 in HNone.
    exact HNone.
  - apply H13 in HNone.
    apply H12 in HNone.
    exact HNone.
Qed.
