Require Import Common.Definitions.
Require Import Source.CS.
Require Import Intermediate.CS.

(*Module S.
  Import Source.Language.
  Import Source.CS.
  Module CS := CS.
End S.

Module I.
  Import Intermediate.Machine.
  Import Intermediate.CS.
  Module CS := CS.
End I.
*)

(* RB: The following should go into its own file. *)
Definition matching_mains (p1 : Language.Source.program)
                          (p2 : Machine.Intermediate.program) : Prop :=
  Language.Source.prog_main p1 <->
  Machine.Intermediate.prog_main p2.

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
