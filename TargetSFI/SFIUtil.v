(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import List.

Require Import Coq.Structures.Equalities.
Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNat.
Require Import Coq.PArith.BinPos.

Set Implicit Arguments.
Set Contextual Implicit.

Module ListUtil.

  Fixpoint get {A:Type} (pos:nat) (l : list A) : option A :=
    match (pos,l) with
    | (O, x::_) => Some x
    | (_,nil) => None
    | (S pos',_::ls) => get pos' ls
    end.

  (* TODO: I would like to avoid passing eqb *)
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