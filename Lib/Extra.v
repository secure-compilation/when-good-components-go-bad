(* Complements to the standard Coq library and ssreflect *)

Require Import Coq.ZArith.ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Definition Z_eqMixin := EqMixin Z.eqb_spec.
Canonical Z_eqType := Eval hnf in EqType Z Z_eqMixin.
