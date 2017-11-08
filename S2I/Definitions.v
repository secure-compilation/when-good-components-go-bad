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
  unfold S.PS.is_program_component, S.PS.is_context_component in *;
  unfold I.PS.is_program_component, I.PS.is_context_component in *;
  unfold turn_of, S.PS.state_turn, I.PS.state_turn in *;
  simpl in *;
  auto.