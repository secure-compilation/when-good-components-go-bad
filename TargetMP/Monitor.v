
(* TODO: for now, ad hoc monitor implementing linear return capability.
   Longer term: symbolic machine instance                               *)

Require Import Common.Definitions.

(* TODO: is there a way to do that? *)
(* Inductive tag := pctag | regtag | metag. *)

(* Tags intended to be attached to values *)
Inductive vtag : Type :=
| Any : vtag
| Ret : nat -> vtag.

(* TODO: what's difference with {| |} notation? *)
(* Tags intended to be attached to memory location *)
Record ltag : Type :=
  { color : Component.id ; entry_for : list Component.id }.

Inductive pctag : Type :=
  Level : nat -> pctag.

Definition memtag : Type :=
  vtag * ltag.

Definition regtag := vtag.
