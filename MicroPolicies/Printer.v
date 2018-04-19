From mathcomp Require Import ssreflect ssrfun eqtype seq ssrint.
From CoqUtils Require Import fmap fset word.


Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Types.

Require Import Coq.Strings.String.
Require Export Extraction.Definitions.

Open Scope string_scope.

Axiom coqstring_of_word : forall {k}, word k -> string.
(* TL TODO: move this to Extraction.v *)
Extract Constant coqstring_of_word => "(fun _ w -> let Word x = Lazy.force w in coqstring_of_camlstring (Big.to_string x))".

Definition coqstring_of_ratom (a : ratom) : string := "TODO:ratom".

Definition coqstring_of_reg (r : reg mt * ratom) : string :=
  "reg " ++ coqstring_of_word (fst r) ++ " : " ++ coqstring_of_ratom (snd r).

Definition coqstring_of_regs (regs : { fmap reg mt -> ratom }) : string :=
  "{
" ++ foldl (fun s r => coqstring_of_reg r ++ "
" ++ s) "" regs ++ "}".
