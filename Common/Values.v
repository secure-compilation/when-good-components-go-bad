Require Import Common.Definitions.
Require Import Common.Util.
Require Import Lib.Extra.
From mathcomp Require Import
     ssreflect ssrnat eqtype.

Module Block.
  Definition id := nat.
  Definition offset := Z.
  (* local public buffer *)
  Definition public : id := 0.
  (* local private buffer *)
  Definition private : id := 1.
  (* RB: STATIC_READ: Missing definition, used later. To fix. *)
  Definition local : id := 2.

  Inductive buffer_kind : Type :=
  | pub : buffer_kind
  | priv : buffer_kind
  .
  Definition buffer_kind_to_block_id bk : id :=
    match bk with
    | pub => public
    | priv => private
    end.
  Definition block_id_to_buffer_kind (i:id) : option buffer_kind :=
    match i with
    | (* public *)  0 => Some pub
    | (* private *) 1 => Some priv
    | _ => None
    end.
End Block.

Module Pointer.
  Definition t : Type := Component.id * Block.id * Block.offset.

  Definition component (p : t) : Component.id :=
    let '(C, _, _) := p in C.

  Definition block (p : t) : Block.id :=
    let '(_, b, _) := p in b.

  Definition offset (p : t) : Block.offset :=
    let '(_, _, o) := p in o.

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

Definition eqvalue v1 v2 :=
  match v1, v2 with
  | Int z1, Int z2 => z1 == z2
  | Ptr p1, Ptr p2 =>  p1 == p2
  | Undef, Undef => true         (* should undef not be equal to itself ? Since it can be anything *)
  | _, _ => false
  end.

Lemma eqvalueP : Equality.axiom eqvalue.
Proof.
  move; elim => [z1 | p1 |] [z2 | p2|]//= ;
                 apply: (iffP idP); move => H; inversion H ; try constructor.
  by move: H => /Z.eqb_spec => H; rewrite H.
  done.
  by move: H => /pair_eqP => H; rewrite H.
  done.
Qed.

Definition value_eqMixin: Equality.mixin_of value := EqMixin eqvalueP.
Canonical value_eqType := Eval hnf in EqType value value_eqMixin.


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
  | Eq,    Ptr p1, Ptr p2 => Int (Util.Z.of_bool (p1 == p2))
  | Leq,   Ptr p1, Ptr p2 => match Pointer.leq p1 p2 with
                             | Some res => Int (Util.Z.of_bool res)
                             | None     => Undef
                             end
  (* undefined operations *)
  | _,     _,       _       => Undef
  end.

(* Should be place surely elsewhere, but it doesn't break the dependency tree that way *)
Definition buffer : Type := (nat + list value).
Definition buffer_size (buf : buffer) :=
  match buf with
  | inl n => n
  | inr seq => length seq
  end.

(* Simple predicate to avoid pointer passing for now *)
Definition is_transferable_value (v : value ) :=
  match v with
  | Int _ => true
  | Ptr _ => false
  | Undef => false (* Passing undef is not undefined ! *)
  end.
Hint Unfold is_transferable_value.
