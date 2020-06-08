Require Import Common.Definitions.
Require Import Common.Util.

Require Import Lib.Extra.
From mathcomp Require Import ssreflect ssrnat eqtype.

Module Block.
  Definition id := nat.
  Definition offset := Z.
  Definition local : id := 0.
End Block.

Module Permission.
  Definition id := nat.
  Definition code : id := 0.
  Definition data : id := 1.
End Permission.

Module Pointer.
  Definition t : Type := Permission.id * Component.id * Block.id * Block.offset.

  Definition permission (p : t) : Permission.id :=
    let '(P, _, _, _) := p in P.
  
  Definition component (p : t) : Component.id :=
    let '(_, C, _, _) := p in C.

  Definition block (p : t) : Block.id :=
    let '(_, _, b, _) := p in b.

  Definition offset (p : t) : Block.offset :=
    let '(_, _, _, o) := p in o.

  Definition eq (p1 p2 : t) : bool :=
    let '(P1, C1, b1, o1) := p1 in
    let '(P2, C2, b2, o2) := p2 in
    (Nat.eqb P1 P2) && (Nat.eqb C1 C2) && (Nat.eqb b1 b2) && (Z.eqb o1 o2).

  Definition leq (p1 p2 : t) : option bool :=
    let '(P1, C1, b1, o1) := p1 in
    let '(P2, C2, b2, o2) := p2 in
    if (Nat.eqb P1 P2) && (Nat.eqb C1 C2) && (Nat.eqb b1 b2) then
      Some ((o1 <=? o2) % Z)
    else
      None.

  Definition add (ptr : t) (offset : Z) : t :=
    let '(P, C, b, o) := ptr in (P, C, b, (o+offset)%Z).

  Definition sub (ptr : t) (offset : Z) : t :=
    let '(P, C, b, o) := ptr in (P, C, b, (o-offset)%Z).

  Definition inc (ptr : t) : t := add ptr 1.

  Ltac preserves_proof_add := intros ?p ?n; destruct p as [[[P C] b] o]; reflexivity.
  Ltac preserves_proof_inc := intros ?p; destruct p as [[[P C] b] o]; reflexivity.
  
  Lemma add_preserves_permission:
    forall p n, permission (add p n) = permission p.
  Proof. preserves_proof_add. Qed.

  Lemma add_preserves_component:
    forall p n, component (add p n) = component p.
  Proof. preserves_proof_add. Qed.
  
  Lemma add_preserves_block:
    forall p n, block (add p n) = block p.
  Proof. preserves_proof_add. Qed.

  Lemma sub_preserves_permission:
    forall p n, permission (sub p n) = permission p.
  Proof. preserves_proof_add. Qed.

  Lemma sub_preserves_component:
    forall p n, component (sub p n) = component p.
  Proof. preserves_proof_add. Qed.
  
  Lemma sub_preserves_block:
    forall p n, block (sub p n) = block p.
  Proof. preserves_proof_add. Qed.

  Lemma inc_preserves_permission:
    forall p, permission (inc p) = permission p.
  Proof. preserves_proof_inc. Qed.

  Lemma inc_preserves_component:
    forall p, component (inc p) = component p.
  Proof. preserves_proof_inc. Qed.
  
  Lemma inc_preserves_block:
    forall p, block (inc p) = block p.
  Proof. preserves_proof_inc. Qed.

  Lemma compose :
    forall ptr,
      (permission ptr, component ptr, block ptr, offset ptr) = ptr.
  Proof.
    now intros [[[P C] b] o].
  Qed.
End Pointer.

(* Values. *)
Inductive value : Type :=
| Int : Z -> value
| Ptr : Pointer.t -> value
| Undef : value.

Definition eqvalue v1 v2 :=
  match v1, v2 with
  | Int z1, Int z2 => z1 == z2
  | Ptr p1, Ptr p2 => p1 == p2
  (* RB: TODO: From FG, however should Undef be equal to itself? *)
  | Undef, Undef => true
  | _, _ => false
  end.

Lemma eqvalueP : Equality.axiom eqvalue.
Proof.
  move; elim => [z1 | p1 |] [z2 | p2 |]//= ;
                 apply: (iffP idP); move => H; inversion H ; try constructor.
  by move: H => /Z.eqb_spec => H; rewrite H.
  done.
  by move: H => /pair_eqP => H; rewrite H.
  done.
Qed.

Definition value_eqMixin: Equality.mixin_of value := EqMixin eqvalueP.
Canonical value_eqType := Eval hnf in EqType value value_eqMixin.

(* Binary operations. *)
Inductive binop := Add | Minus | Mul | Eq | Leq.

Definition eval_binop (op : binop) (v1 v2 : value) : value :=
  match op, v1, v2 with
  (* natural numbers *)
  | Add,   Int n1, Int n2 => Int (n1 + n2)
  | Minus, Int n1, Int n2 => Int (n1 - n2)
  | Mul,   Int n1, Int n2 => Int (n1 * n2)
  | Eq,    Int n1, Int n2 => Int (Util.Z.of_bool (n1  =? n2)%Z)
  | Leq,   Int n1, Int n2 => Int (Util.Z.of_bool (n1 <=? n2)%Z)
  (* data-pointer arithmetic *)
  | Add,   Ptr p,  Int n  => Ptr (Pointer.add p n)
  | Add,   Int n,  Ptr p  => Ptr (Pointer.add p n)
  | Minus, Ptr p1, Ptr p2 => let '(P1, C1, b1, o1) := p1 in
                             let '(P2, C2, b2, o2) := p2 in
                             if (Nat.eqb P1 P2) && (Nat.eqb C1 C2) && (Nat.eqb b1 b2) then
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