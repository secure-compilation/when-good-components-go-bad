Require Import Common.Definitions.

(* NOTE: add the following two lines at the start of the extracted file:
#load "nums.cma";;
open Big_int;;
*)

Axiom ocaml_int : Type.
Axiom ocaml_int_0 : ocaml_int.
Axiom ocaml_int_1: ocaml_int.
Axiom ocaml_int_2: ocaml_int.
Axiom ocaml_int_plus: ocaml_int -> ocaml_int -> ocaml_int.
Axiom ocaml_int_mul: ocaml_int -> ocaml_int -> ocaml_int.
Axiom ocaml_int_neg: ocaml_int -> ocaml_int.

Axiom print_ocaml_int: ocaml_int -> unit.

Axiom print_explicit_exit: unit -> unit.
Axiom print_error: ocaml_int -> unit.

Fixpoint pos2int (val: positive) : ocaml_int :=
  match val with
  | xH => ocaml_int_1
  | xI p => ocaml_int_plus (ocaml_int_mul ocaml_int_2 (pos2int p)) ocaml_int_1
  | xO p => ocaml_int_mul ocaml_int_2 (pos2int p)
  end.

Fixpoint z2int (val: Z) : ocaml_int :=
  match val with
  | Z0 => ocaml_int_0
  | Zpos p => pos2int p
  | Zneg p => ocaml_int_neg (pos2int p)
  end.

Extraction Language Ocaml.

Extract Inductive unit => "unit" [ "()" ].

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" ["true" "false"].

Extract Inductive prod => "(*)"  [ "(,)" ].

Extract Inductive list => "list" [ "[]" "(::)" ].

Extract Inductive option => "option" [ "Some" "None" ].

Extract Constant ocaml_int => "big_int".
Extract Constant ocaml_int_0 => "zero_big_int".
Extract Constant ocaml_int_1 => "unit_big_int".
Extract Constant ocaml_int_2 => "(succ_big_int Big_int.unit_big_int)".
Extract Constant ocaml_int_plus => "add_big_int".
Extract Constant ocaml_int_mul => "mult_big_int".
Extract Constant ocaml_int_neg => "minus_big_int".

Extract Constant print_ocaml_int => "(fun n -> print_string (string_of_big_int n); print_newline ())".

Extract Constant print_explicit_exit => "(fun _ -> print_string ""EXIT""; print_newline ())".
Extract Constant print_error => "(fun n -> print_string ""FAILED with ""; print_string (string_of_big_int n); print_newline ())".
