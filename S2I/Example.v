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

Definition compiled_fact :=
  match compile_program factorial with
  | Some p =>
    Some (map (fun '(C,procs) => (C, NMap.elements procs))
              (NMap.elements (Intermediate.prog_procedures p)))
  | None => None
  end.

Definition init_compiled_fact :=
  match compile_program factorial with
  | Some p => CS.init p 1 0
  | None => None
  end.

Definition run_compiled_fact := compile_and_run factorial.

(* extraction to Ocaml *)

(*
let rec nat2int = function
  | O -> 0
  | S n -> 1 + nat2int n;;

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

Extraction "/tmp/compile_fact.ml" compiled_fact run_compiled_fact init_compiled_fact.