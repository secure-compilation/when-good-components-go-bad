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


Section Tags.


(* Value tags and tags for code *)


Inductive value_tag : Type := Ret : nat -> value_tag | Other : value_tag.

Definition code_tag : Type := option (Procedure.id * seq Component.id).


(* Tag of Memory cell *)

(* Record mem_tag : Type := MTag
  { vtag : value_tag;
    color : Component.id }.*)

Definition mem_tag := Component.id.

Definition def_mem_tag c : mem_tag := c.

End Tags.



(* PC tag *)
Section PC.

Inductive pc_tag : Type := Level : nat -> pc_tag.

Definition level (pct : pc_tag) : nat := match pct with Level n => n end.

Definition inc_pc_tag (pct : pc_tag) : pc_tag := Level (S (level pct)).

Definition dec_pc_tag (pct : pc_tag) : option pc_tag := match (level pct) with
 | 0 => None
 | S n => Some (Level n)
end.

Definition check_dec_pc_tag (pct : pc_tag) m : option pc_tag := match (level pct) with
 | 0 => None
 | S n => if Nat.eqb (S n) m then Some (Level n) else None
end.

Definition inc_ret (pct : pc_tag) := Ret (S (level pct)).


End PC.

Module Pointer.
  Definition t : Type := Block.id * Block.offset.

  Definition block (p : t) : Block.id :=
    let '(b, _) := p in b.

  Definition offset (p : t) : Block.offset :=
    let '(_, o) := p in o.

  Definition eq (p1 p2 : t) : bool :=
    let '( b1, o1) := p1 in
    let '( b2, o2) := p2 in
    (Nat.eqb b1 b2) && (Z.eqb o1 o2).

  Definition leq (p1 p2 : t) : option bool :=
    let '( b1, o1) := p1 in
    let '(b2, o2) := p2 in
    if (Nat.eqb b1 b2) then
      Some ((o1 <=? o2) % Z)
    else
      None.

  Definition add (ptr : t) (offset : Z) : t :=
    let '(b, o) := ptr in (b, (o+offset)%Z).

  Definition sub (ptr : t) (offset : Z) : t :=
    let '(b, o) := ptr in (b, (o-offset)%Z).

  Definition inc (ptr : t) : t := add ptr 1.


  Lemma add_preserves_block:
    forall p n, block (add p n) = block p.
  Proof.
    intros p n.
    destruct p as [b o].
    reflexivity.
  Qed.
  Lemma inc_preserves_block:
    forall p, block (inc p) = block p.
  Proof.
    intros p.
    destruct p as [b o].
    reflexivity.
  Qed.

  Lemma compose :
    forall ptr,
      (block ptr, offset ptr) = ptr.
  Proof.
    now intros [b o].
  Qed.
End Pointer.


Section Values.


  Inductive value : Type :=
  | Int : Z -> value
  | Ptr : Pointer.t -> value
  | Undef : value.

  Record tvalue := MVal
   { vtag : value_tag;
     val : value }.

  Definition to_tvalue (v : value) : tvalue := MVal Other v.

  Definition tUndef := to_tvalue Undef.

  Definition to_tagged_cell (c : Component.id) (v : value) : tvalue * mem_tag := (to_tvalue v,def_mem_tag c).

  Definition to_tagged_block (c : Component.id) (l : list value) : list (tvalue * mem_tag) := 
    map (to_tagged_cell c) l.

Definition eval_binop (op : binop) (v1 v2 : value) : value :=
  match op, v1, v2 with
  (* natural numbers *)
  | Add,   Int n1, Int n2 => Int (n1 + n2)
  | Minus, Int n1, Int n2 => Int (n1 - n2)
  | Mul,   Int n1, Int n2 => Int (n1 * n2)
  | Eq,    Int n1, Int n2 => Int (Util.Z.of_bool (n1  =? n2)%Z)
  | Leq,   Int n1, Int n2 => Int (Util.Z.of_bool (n1 <=? n2)%Z)
  (* pointer arithmetic *)
  | Add,   Ptr p,  Int n  => Ptr (Pointer.add p n)
  | Add,   Int n,  Ptr p  => Ptr (Pointer.add p n)
  | Minus, Ptr p1, Ptr p2 => let '(b1, o1) := p1 in
                             let '(b2, o2) := p2 in
                             if (Nat.eqb b1 b2) then
                               Int (o1 - o2)
                             else
                               Undef
  | Minus, Ptr p,  Int n  => Ptr (Pointer.sub p n)
  | Eq,    Ptr p1, Ptr p2 => Int (Util.Z.of_bool (Pointer.eq p1 p2))
  | Leq,   Ptr p1, Ptr p2 => match Pointer.leq p1 p2 with
                             | Some res => Int (Util.Z.of_bool res)
                             | None     => Undef
                             end
  (* undefined operations *)
  | _,     _,       _       => Undef
  end.

End Values.


Module Register.
  Definition t : Type := NMap tvalue.

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
    mkfmap [(to_nat R_ONE, tUndef);
            (to_nat R_COM, tUndef);
            (to_nat R_AUX1, tUndef);
            (to_nat R_AUX2, tUndef);
            (to_nat R_RA, tUndef);
            (to_nat R_SP, tUndef);
            (to_nat R_ARG, tUndef)].

  Definition get (r : register) (regs : t) : tvalue :=
    match getm regs (to_nat r) with
    | Some v => v
    (* this should never happen (i.e. regs should be well-formed) *)
    | None => tUndef
    end.

  Definition get_value (r : register) (regs : t) : value :=
    match getm regs (to_nat r) with
    | Some tv => val tv
    (* this should never happen (i.e. regs should be well-formed) *)
    | None => Undef
    end.

  Definition get_tag (r : register) (regs : t) : option value_tag :=
    match getm regs (to_nat r) with
    | Some tv => Some (vtag tv)
    (* this should never happen (i.e. regs should be well-formed) *)
    | None => None
    end.

  Definition set (r : register) (val : value) (vt : value_tag) (regs : t) : t :=
    setm regs (to_nat r) (MVal vt val).

  Definition tset (r : register) (tval : tvalue) (regs : t) : t :=
    setm regs (to_nat r) tval.

Definition invalidate regs := 
[fmap (Register.to_nat R_ONE, tUndef);(Register.to_nat R_COM, Register.get R_COM regs);
      (Register.to_nat R_AUX1, tUndef);(Register.to_nat R_AUX2, tUndef);(Register.to_nat R_RA, Register.get R_RA regs);
      (Register.to_nat R_SP, tUndef);(Register.to_nat R_ARG, tUndef)].

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