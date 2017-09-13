Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Language.
Require Import Source.CS.
Require Import Lib.Tactics.
Require Import Lib.Monads.
Require Import CompCert.Smallstep.
Require Import CompCert.Events.

Import MonadNotations.
Open Scope monad_scope.

Import Source.
Import CS.

(* naive factorial *)

Open Scope Z_scope.

Definition factorial : program := {|
  prog_interface :=
    ZMapExtra.of_list [(1, {| Component.import := [(2, 0)];
                              Component.export := [1] |});
                       (2, {| Component.import := [];
                              Component.export := [1] |})];
  prog_buffers := ZMapExtra.of_list [(1, 1%nat); (2, 1%nat)];
  prog_procedures := ZMapExtra.of_list [
    (* NOTE the version with E_exit is the right one, but unfortunately it is difficult
            to debug with extraction. Hence, the second version without E_exit *)
    (*(1, NMapExtra.of_list [(0, E_seq (E_call 2 0 (E_val (Int 6))) E_exit)]);*)
    (1, ZMapExtra.of_list [(0, E_call 2 0 (E_val (Int 6)))]);
    (2, ZMapExtra.of_list [(0,
      E_if (E_binop Leq (E_deref E_local) (E_val (Int 1)))
        (E_val (Int 1))
        (E_binop Mul
                 (E_deref E_local)
                 (E_call 2 0 (E_binop Minus (E_deref E_local) (E_val (Int 1))))))])];
  prog_main := (1, 0)
|}.

(* this is super slow!!! it seems that maps are a problem *)
(*
Eval vm_compute in
  do (G, st) <- init factorial 1 0;
  match eval_kstep G st with
  | None => None
  | Some (_, (_, _, _, _, e)) => Some e
  end.
*)

Definition run_fact :=
  (* warning (Int 1) is not considered at the moment *)
  match run factorial (Int 1) 1000 with
  | Some (_, _, _, _, E_exit) => Some 0
  | Some (_, _, _, _, E_val (Int n)) => Some n
  | _ => None
  end.

(* Run with extraction to obtain a result *)
(*
let rec nat2int = function
  | O -> 0
  | S n -> 1 + nat2int n;;

match run_fact with
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

Extraction "/tmp/run_fact.ml" run_fact.