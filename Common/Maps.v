Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.Structures.OrdersAlt.

Module backNat_as_OT := Backport_OT Nat_as_OT.
Module NMap := FMapAVL.Make backNat_as_OT.
Module NMapExtra := WProperties_fun Nat_as_OT NMap.
Module NMapFacts := NMapExtra.F.