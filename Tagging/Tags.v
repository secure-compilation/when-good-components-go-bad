Require Import Common.Definitions.
Require Import Common.Util.
Require Export Common.Values.
Require Export Common.Linking.
Require Import Common.Memory.
Require Import Lib.Monads.
Require Import Lib.Extra.
Require Import Intermediate.Machine.

From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.
From extructures Require Import fmap.

Set Implicit Arguments.


(* Value tags and tags for code *)


Inductive value_tag : Type := Ret : nat -> value_tag | Other : value_tag.

Definition code_tag : Type := option (Procedure.id * seq Component.id).


(* Tag of Memory cell *)

Record mem_tag : Type := MTag
  { vtag : value_tag;
    color : Component.id }.

Definition def_mem_tag c := MTag Other c.

  Definition to_tagged_cell (c : Component.id) (v : value) : value * mem_tag := (v,def_mem_tag c).

  Definition to_tagged_block (c : Component.id) (l : list value) : list (value * mem_tag) := 
    map (to_tagged_cell c) l.


(* PC tag *)

Inductive pc_tag : Type := Level : nat -> pc_tag.

Definition level (pct : pc_tag) : nat := match pct with Level n => n end.

Definition inc_pc_tag (pct : pc_tag) : pc_tag := Level (level pct + 1).

(* Here: rather do an option thing? *)
Definition dec_pc_tag (pct : pc_tag) : pc_tag := Level (level pct - 1).





Module Register.
  Definition t : Type := NMap (value * value_tag).

  Definition to_nat (r : register) : nat :=
    match r with
    | R_ONE  => 0
    | R_COM  => 1
    | R_AUX1 => 2
    | R_AUX2 => 3
    | R_RA   => 4
    | R_SP   => 5
    | R_ARG  => 6
    end.

  Definition init :=
    mkfmap [(to_nat R_ONE, (Undef,Other));
            (to_nat R_COM, (Undef,Other));
            (to_nat R_AUX1, (Undef,Other));
            (to_nat R_AUX2, (Undef,Other));
            (to_nat R_RA, (Undef,Other));
            (to_nat R_SP, (Undef,Other));
            (to_nat R_ARG, (Undef,Other))].

  Definition get (r : register) (regs : t) : (value * value_tag) :=
    match getm regs (to_nat r) with
    | Some v => v
    (* this should never happen (i.e. regs should be well-formed) *)
    | None => (Undef,Other)
    end.

  Definition get_value (r : register) (regs : t) : value :=
    match getm regs (to_nat r) with
    | Some (v,_) => v
    (* this should never happen (i.e. regs should be well-formed) *)
    | None => Undef
    end.

  Definition get_tag (r : register) (regs : t) : option value_tag :=
    match getm regs (to_nat r) with
    | Some (_,vt) => Some vt
    (* this should never happen (i.e. regs should be well-formed) *)
    | None => None
    end.

  Definition set (r : register) (val : value) (vt : value_tag) (regs : t) : t :=
    setm regs (to_nat r) (val,vt).

Definition invalidate regs := 
[fmap (Register.to_nat R_ONE, (Undef,Other));(Register.to_nat R_COM, Register.get R_COM regs);
      (Register.to_nat R_AUX1, (Undef,Other));(Register.to_nat R_AUX2, (Undef,Other));(Register.to_nat R_RA, Register.get R_RA regs);
      (Register.to_nat R_SP, (Undef,Other));(Register.to_nat R_ARG, (Undef,Other))].

  Lemma invalidate_eq : forall regs1 regs2,
    get R_COM regs1 = get R_COM regs2 ->
    get R_RA regs1 = get R_RA regs2 ->
    invalidate regs1 = invalidate regs2.
  Proof.
    intros regs1 regs2 Hregs Hregs'.
    unfold invalidate.
     congruence.
  Qed.
End Register.