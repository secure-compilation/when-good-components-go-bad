Require Import Common.Definitions.
Require Import Common.Memory.
Require Import Source.Language.
Require Import Source.CS.
Require Import Intermediate.Machine.
Require Import Intermediate.CS.
Require Import S2I.Compiler.
Require Import Source.Examples.
Require Import Lib.Monads.

Import MonadNotations.
Open Scope monad_scope.

Definition compile_and_run (p: Source.program) :=
  do compiled_p <- compile_program p;
  CS.run compiled_p (Int 3) 1000.

Definition run_compiled_fact := compile_and_run factorial.

(* extraction to Ocaml *)

(*
let rec nat2int = function
  | O -> 0
  | S n -> 1 + nat2int n;;

let rec z2int' = function
  | XH -> 1
  | XI p -> 2 * z2int' p + 1
  | XO p -> 2 * z2int' p

let z2int = function
  | Z0 -> 0
  | Zpos p -> z2int' p
  | Zneg p -> - z2int' p;;

match run_compiled_fact with
| None -> print_string "error\n"
| Some n -> print_int (nat2int n); print_newline ();;
*)

Extraction Language Ocaml.

Extract Inductive unit => "unit" [ "()" ].

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" ["true" "false"].

Extract Inductive prod => "(*)"  [ "(,)" ].

Extract Inductive list => "list" [ "[]" "(::)" ].

Extract Inductive option => "option" [ "Some" "None" ].

Extraction "/tmp/run_compiled_fact.ml" run_compiled_fact.