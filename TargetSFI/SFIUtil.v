(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import List.

Require Import Coq.Structures.Equalities.
Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNat.
Require Import Coq.PArith.BinPos.

Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.Structures.OrdersAlt.

Set Implicit Arguments.
Set Contextual Implicit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import CoqUtils.ord.

Module N_as_OT := Backport_OT N_as_OT.
Module BinNatMap := FMapAVL.Make(N_as_OT).
Module BinNatMapExtra := WProperties_fun N_as_OT BinNatMap.
Module BinNatMapFacts := BinNatMapExtra.F.

Module backPositive_as_OT := Backport_OT Positive_as_OT.
Module PMap := FMapAVL.Make backPositive_as_OT.
Module PMapExtra := WProperties_fun Positive_as_OT PMap.
Module PMapFacts := PMapExtra.F.


Module backNat_as_OT := Backport_OT Nat_as_OT.
Module NatMap := FMapAVL.Make backNat_as_OT.
Module NatMapExtra := WProperties_fun backNat_as_OT NatMap.
Module NatMapFacts := NatMapExtra.F.

Module ListUtil.

  (* TODO: I would like to avoid passing eqb *)
  (* AAA: This can be fixed by using fmap in CoqUtils *)
  Fixpoint get_by_key {K V:Type} (eqb : K->K->bool) (k : K)
           (l : list (K*V)) : option V :=
    match l with
    | nil  => None
    | (k1,v1)::ls =>
     if (eqb k k1) then (Some v1)
     else (get_by_key eqb k ls)
    end.

End ListUtil.


Module Log.

  Open Scope char_scope.

  Definition natToDigit (n : nat) : Ascii.ascii :=
    match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
  end.

Close Scope char_scope.


  Definition log_nat (n : nat) : string :=
  let fix log_nat_aux (time n : nat) (acc : string) : string :=
      let acc' := String (natToDigit (Nat.modulo n 10)) acc in
      match time with
      | 0 => acc'
      | S time' =>
        match Nat.div n 10 with
        | 0 => acc'
        | n' => log_nat_aux time' n' acc'
        end
      end in
  log_nat_aux n n EmptyString.

  Definition log_N (n : N) : string :=
    log_nat (N.to_nat n).

   Definition log_pos (n : positive) : string :=
    log_nat (Pos.to_nat n).

End Log.
