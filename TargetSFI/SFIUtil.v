(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import List.

Require Import Coq.Structures.Equalities.

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