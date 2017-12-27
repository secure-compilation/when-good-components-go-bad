From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import lib.utils symbolic.types symbolic.machine.

Variable ccolor : eqType.

(* TL TODO: this mechanism of value tag and location tag moy be generalized *)

Inductive value_tag : Type := Ret : nat -> value_tag | Any : value_tag.

Module Import ValueTagEq.
Definition option_of_value_tag t :=
  match t with
  | Any => None
  | Ret n => Some n
  end.

Definition value_tag_of_option t :=
  match t with
  | None => Any
  | Some n => Ret n
  end.

Lemma option_of_value_tagK : cancel option_of_value_tag value_tag_of_option.
Proof. by case. Qed.

Definition value_tag_eqMixin := CanEqMixin option_of_value_tagK.
Canonical value_tag_eqType := EqType value_tag value_tag_eqMixin.
End ValueTagEq.

Inductive pc_tag : Type := Level : nat -> pc_tag.

Module Import PCTagEq.
Definition nat_of_pc_tag t :=
  match t with
  | Level n => n
  end.

Definition pc_tag_of_nat n := Level n.

Lemma nat_of_pc_tagK : cancel nat_of_pc_tag pc_tag_of_nat.
Proof. by case. Qed.

Definition pc_tag_eqMixin := CanEqMixin nat_of_pc_tagK.
Canonical pc_tag_eqType := EqType pc_tag pc_tag_eqMixin.
End PCTagEq.


Structure mem_tag : Type := MTag {
  vtag  : [eqType of value_tag];
  color : ccolor;
  entry : list ccolor;
}.


Module Import MemTagEq.
Definition tuple_of_mem_tag t := (vtag t, color t, entry t).
Definition mem_tag_of_tuple tp :=
  match tp with
  | (vt, c, e) => MTag vt c e
  end.

Lemma tuple_of_mem_tagK : cancel tuple_of_mem_tag mem_tag_of_tuple.
Proof. by case. Qed.

Definition mem_tag_eqMixin := CanEqMixin tuple_of_mem_tagK.
Canonical mem_tag_eqType := EqType mem_tag mem_tag_eqMixin.
End MemTagEq.

Import Symbolic.

Definition lrt_tags := {|
  pc_tag_type    := [eqType of pc_tag];
  reg_tag_type   := [eqType of value_tag];
  mem_tag_type   := [eqType of mem_tag];
  entry_tag_type := [eqType of unit];
|}.
