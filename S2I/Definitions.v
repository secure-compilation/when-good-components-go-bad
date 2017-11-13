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