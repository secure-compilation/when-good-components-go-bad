Require Import Common.Definitions.
Require Import Common.Util.

Module Block.
  Definition id := nat.
  Definition offset := Z.
  Definition local : id := 0.
End Block.

Module Pointer.
  Definition t : Type := Component.id * Block.id * Block.offset.

  Definition component (p : t) : Component.id :=
    let '(C, _, _) := p in C.

  Definition block (p : t) : Block.id :=
    let '(_, b, _) := p in b.

  Definition offset (p : t) : Block.offset :=
    let '(_, _, o) := p in o.

  Definition eq (p1 p2 : t) : bool :=
    let '(C1, b1, o1) := p1 in
    let '(C2, b2, o2) := p2 in
    (Nat.eqb C1 C2) && (Nat.eqb b1 b2) && (Z.eqb o1 o2).

  Definition leq (p1 p2 : t) : option bool :=
    let '(C1, b1, o1) := p1 in
    let '(C2, b2, o2) := p2 in
    if (Nat.eqb C1 C2) && (Nat.eqb b1 b2) then
      Some ((o1 <=? o2) % Z)
    else
      None.

  Definition add (ptr : t) (offset : Z) : t :=
    let '(C, b, o) := ptr in (C, b, (o+offset)%Z).

  Definition sub (ptr : t) (offset : Z) : t :=
    let '(C, b, o) := ptr in (C, b, (o-offset)%Z).

  Definition inc (ptr : t) : t := add ptr 1.

  Lemma add_preserves_component:
    forall p n, component (add p n) = component p.
  Proof.
    intros p n.
    destruct p as [[C b] o].
    reflexivity.
  Qed.

  Lemma add_preserves_block:
    forall p n, block (add p n) = block p.
  Proof.
    intros p n.
    destruct p as [[C b] o].
    reflexivity.
  Qed.

  Lemma inc_preserves_component:
    forall p, component (inc p) = component p.
  Proof.
    intros p.
    destruct p as [[C b] o].
    reflexivity.
  Qed.

  Lemma inc_preserves_block:
    forall p, block (inc p) = block p.
  Proof.
    intros p.
    destruct p as [[C b] o].
    reflexivity.
  Qed.

  Lemma compose :
    forall ptr,
      (component ptr, block ptr, offset ptr) = ptr.
  Proof.
    now intros [[C b] o].
  Qed.
End Pointer.

Inductive value : Type :=
| Int : Z -> value
| Ptr : Pointer.t -> value
| Undef : value.

Inductive binop := Add | Minus | Mul | Eq | Leq.

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
  | Minus, Ptr p1, Ptr p2 => let '(C1, b1, o1) := p1 in
                             let '(C2, b2, o2) := p2 in
                             if (Nat.eqb C1 C2) && (Nat.eqb b1 b2) then
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