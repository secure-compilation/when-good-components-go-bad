From Coq Require Extraction.

Require Import Common.Definitions.
Require Import Common.Values.
From mathcomp Require Import ssrfun seq ssrint ssrnat.
Require Import Arith ZArith.
Require Import Coq.extraction.ExtrOcamlNatBigInt.
Require Import Coq.extraction.ExtrOcamlZBigInt.
Require Export Extraction.

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

Fixpoint nat2int (val : nat) : ocaml_int :=
  match val with
  | O => ocaml_int_0
  | S n => ocaml_int_plus (nat2int n) (ocaml_int_1)
  end.

Definition int2int (val : int) : ocaml_int :=
  match val with
  | Posz n => (nat2int n)
  | Negz n => ocaml_int_neg (nat2int n)
  end.

Extraction Language Ocaml.

Extract Inductive unit => "unit" [ "()" ].

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" ["true" "false"].
Extract Constant negb => "not".

Extract Inductive reflect => "bool" ["true" "false"].
Extract Constant introP   => "id".
Extract Constant sumboolP => "fun x -> x".
Extract Constant idP      => "fun x -> x".
Extract Constant idPn     => "not".
Extract Constant negP     => "not".
Extract Constant negPn    => "fun x -> x".
Extract Constant negPf    => "not".
Extract Constant andP     => "(&&)".
Extract Constant and3P    => "fun b1 b2 b3 -> b1 && b2 && b3".
Extract Constant and4P    => "fun b1 b2 b3 b4 -> b1 && b2 && b3 && b4".
Extract Constant and5P    => "fun b1 b2 b3 b4 b5 -> b1 && b2 && b3 && b4 && b5".
Extract Constant orP      => "(||)".
Extract Constant or3P     => "fun b1 b2 b3 -> b1 || b2 || b3".
Extract Constant or4P     => "fun b1 b2 b3 b4 -> b1 || b2 || b3 || b4".
Extract Constant nandP    => "fun b1 b2 -> not (b1 && b2)".
Extract Constant norP     => "fun b1 b2 -> not (b1 || b2)".
Extract Constant addbP    => "(<>)".

Extract Inductive prod => "(*)"  [ "(,)" ].

Extract Inductive list => "list" [ "[]" "(::)" ].

Extract Inductive option => "option" [ "Some" "None" ].

Extract Constant ocaml_int => "Big_int.big_int".
Extract Constant ocaml_int_0 => "Big_int.zero_big_int".
Extract Constant ocaml_int_1 => "Big_int.unit_big_int".
Extract Constant ocaml_int_2 => "(Big_int.succ_big_int Big_int.unit_big_int)".
Extract Constant ocaml_int_plus => "Big_int.add_big_int".
Extract Constant ocaml_int_mul => "Big_int.mult_big_int".
Extract Constant ocaml_int_neg => "Big_int.minus_big_int".

Extract Constant print_ocaml_int => "(fun n -> print_string (Big_int.string_of_big_int n); print_newline ())".

Extract Constant print_explicit_exit => "(fun _ -> print_string ""EXIT""; print_newline ())".
Extract Constant print_error => "(fun n -> print_string ""FAILED with ""; print_string (Big_int.string_of_big_int n); print_newline ())".

(* ssr nat *)
Extract Constant eqn             => "Big.eq".
Extract Constant addn_rec        => "Big.add".
Extract Constant addn            => "Big.add".
Extract Constant subn_rec        => "(fun x y -> Big.max (Big.sub x y) (Big.zero))".
Extract Constant subn            => "(fun x y -> Big.max (Big.sub x y) (Big.zero))".
Extract Constant leq             => "Big.le".
Extract Constant maxn            => "Big.max".
Extract Constant minn            => "Big.min".
Extract Constant muln_rec        => "Big.mult".
Extract Constant muln            => "Big.mult".
Extract Constant expn_rec        => "Big.power".
Extract Constant expn            => "Big.power".
Extract Constant nat_of_bool     => "(fun b -> if b then Big.one else Big.zero)".
Extract Constant odd             => "(fun n -> Big.eq (Big.modulo n Big.two) (Big.zero))".
Extract Constant double_rec      => "Big.mult_int 2".
Extract Constant double          => "Big.mult_int 2".
Extract Constant half            => "(fun n -> Big.div n Big.two)".
Extract Constant uphalf          => "(fun n -> Big.div (Big.succ n) Big.two)".
(* ssr div *)
Extract Constant div.edivn    => "Big.quomod".
Extract Constant div.divn     => "Big.div".
Extract Constant div.modn     => "Big.modulo".
Extract Constant div.gcdn_rec => "Big.gcd".
Extract Constant div.gcdn     => "Big.gcd".

(* Provide tail-recursive versions of functions *)
Extract Constant foldr => "
(fun f b l ->
  let rev l = 
    let rec revr acc = function
      | [] -> acc
      | hd::tl -> revr (hd::acc) tl
    in 
    revr [] l
  in
  let rev_l = rev l 
  in 
  let rec folder_rr acc = function
    | [] -> acc
    | hd::tl -> folder_rr (f hd acc) tl
  in 
  folder_rr b rev_l)".

Extract Constant map =>
"(fun f l -> 
  let rec mapr acc = function
    | [] -> acc
    | x::xs -> mapr ((f x)::acc) xs
  in
  mapr [] l)".

(* Workaround that allows the generated code to be compiled:
see [https://github.com/coq/coq/issues/4875] and [https://github.com/coq/coq/issues/6614] *)
Extraction Inline SimplPred.