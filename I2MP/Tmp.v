
Require Import Common.Definitions.

From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint.
From extructures Require Import fmap fset.
From CoqUtils Require Import word.

(* TL TODO: this is a very dirty implementation, ask Arthur anyway *)
Definition mapk {T T' : ordType} {S : Type} (f : T -> T') (map : {fmap T -> S})
  : {fmap T' -> S} :=
  foldl unionm emptym (unzip2 (mapim (fun k x => mkfmap [:: (f k, x)]) map)).

(* Codomain as seq (no need for ordType on images) *)

Definition codomm' {T : ordType} {S : Type} (map : {fmap T -> S}) : seq S := unzip2 map.