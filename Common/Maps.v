Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.Structures.OrdersAlt.

Module backZ_as_OT := Backport_OT Z_as_OT.
Module ZMap := FMapAVL.Make backZ_as_OT.
Module ZMapExtra := WProperties_fun Z_as_OT ZMap.
Module ZMapFacts := ZMapExtra.F.

Module N_as_OT := Backport_OT N_as_OT.
Module BinNatMap := FMapAVL.Make(N_as_OT).
Module BinNatMapExtra := WProperties_fun N_as_OT BinNatMap.
Module BinNatMapFacts := BinNatMapExtra.F.
