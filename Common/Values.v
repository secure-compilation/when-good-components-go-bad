Require Import Common.Definitions.
Require Import Common.Util.

Require Import Lib.Extra.
From mathcomp Require Import ssreflect ssrnat eqtype.

Set Bullet Behavior "Strict Subproofs".

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

  Lemma eqP : Equality.axiom eq.
  Proof.
    intros [[[perm1 C1] b1] o1] [[[perm2 C2] b2] o2].
    simpl.
    destruct (perm1 =? perm2) eqn:Hcase1;
      move: Hcase1 => /eqP => Hcase1;
      destruct (C1 =? C2) eqn:Hcase2;
      move: Hcase2 => /eqP => Hcase2;
      destruct (b1 =? b2) eqn:Hcase3;
      move: Hcase3 => /eqP => Hcase3;
      destruct (o1 =? o2)%Z eqn:Hcase4;
      move: Hcase4 => /Z.eqb_spec => Hcase4;
      constructor;
      try injection; (* All cases (false) except all-true case. *)
      congruence.
  Qed.

  Definition eqMixin: Equality.mixin_of t := EqMixin eqP.
  Canonical eqType := Eval hnf in EqType t eqMixin.

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

Definition is_ptr (v : value) : bool :=
  match v with
  | Ptr _ => true
  | _ => false
  end.

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

Definition binop_eqb (op1 op2 : binop) : bool :=
  match op1, op2 with
  | Add, Add
  | Minus, Minus
  | Mul, Mul
  | Eq, Eq
  | Leq, Leq => true
  | _, _ => false
  end.

Lemma binopP : Equality.axiom binop_eqb.
Proof.
  intros [] []; by constructor.
Qed.

Definition binop_eqMixin: Equality.mixin_of binop := EqMixin binopP.
Canonical binop_eqType := Eval hnf in EqType binop binop_eqMixin.

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

Lemma eval_binop_ptr :
  forall op v1 v2 p,
    eval_binop op v1 v2 = Ptr p ->
    (exists p1 i1, ((v1 = Ptr p1 /\ v2 = Int i1) \/ (v2 = Ptr p1 /\ v1 = Int i1))
                /\
                Pointer.permission p = Pointer.permission p1 /\
                Pointer.component p = Pointer.component p1 /\
                Pointer.block p = Pointer.block p1
    ).
  intros op v1 v2 p Heval.
  unfold eval_binop in Heval.
  destruct op eqn:eop; destruct v1 eqn:e1; destruct v2 eqn:e2;
    try discriminate.
  - exists t. exists z. split.
    + right. intuition.
    + inversion Heval.
      split; last split.
      apply Pointer.add_preserves_permission.
      apply Pointer.add_preserves_component.
      apply Pointer.add_preserves_block.
  - exists t. exists z. split.
    + left. intuition.
    + inversion Heval.
      split; last split.
      apply Pointer.add_preserves_permission.
      apply Pointer.add_preserves_component.
      apply Pointer.add_preserves_block.
  - exists t. exists z. split.
    + left. intuition.
    + inversion Heval.
      split; last split.
      apply Pointer.sub_preserves_permission.
      apply Pointer.sub_preserves_component.
      apply Pointer.sub_preserves_block.
  - destruct t as [[[tp tc] tb] to].
    destruct t0 as [[[t0p t0c] t0b] t0o].
    destruct ((tp =? t0p) && (tc =? t0c) && (tb =? t0b)); discriminate.
  - destruct (Pointer.leq t t0); discriminate.
Qed.    

Lemma eval_binop_int :
  forall op v1 v2 i,
    eval_binop op v1 v2 = Int i ->
    (
      (exists i1 i2, v1 = Int i1 /\ v2 = Int i2)
      \/
      (exists p1 p2, v1 = Ptr p1 /\ v2 = Ptr p2 /\ op = Eq)
      \/
      (exists p1 p2, v1 = Ptr p1 /\ v2 = Ptr p2 /\
                     (
                       (op = Minus \/ op = Leq)
                       /\
                       (
                         Pointer.permission p1 = Pointer.permission p2 /\
                         Pointer.component p1 = Pointer.component p2 /\
                         Pointer.block p1 = Pointer.block p2
                       )
                     )
      )
    ).
Proof.
  intros op v1 v2 p Heval.
  unfold eval_binop in Heval.
  destruct op eqn:eop;
    destruct v1 as [i1 | [[[perm1 cid1] bid1] off1] |] eqn:e1;
    destruct v2 as [i2 | [[[perm2 cid2] bid2] off2] |] eqn:e2;
    try discriminate.
  - left; do 2 eexists; intuition.
  - left; do 2 eexists; intuition.
  - destruct ((perm1 =? perm2) && (cid1 =? cid2) && (bid1 =? bid2)) eqn:Heq;
      try discriminate.
    assert (perm1 = perm2 /\ cid1 = cid2 /\ bid1 = bid2) as [H1 [H2 H3]]; subst.
    { 
      pose proof andb_prop _ _ Heq as [Heq' H3].
      pose proof andb_prop _ _ Heq' as [H1 H2].
      intuition; by apply beq_nat_true.
    }
    right; right; do 2 eexists; eauto; intuition.
  - left; do 2 eexists; intuition.
  - left; do 2 eexists; intuition.
  - unfold Pointer.eq in *.
    right; left; do 2 eexists; eauto; intuition; discriminate.
  - left; do 2 eexists; intuition.
  - unfold Pointer.leq in *.
    destruct ((perm1 =? perm2) && (cid1 =? cid2) && (bid1 =? bid2)) eqn:Heq;
      try discriminate.
    assert (perm1 = perm2 /\ cid1 = cid2 /\ bid1 = bid2) as [H1 [H2 H3]]; subst.
    { 
      pose proof andb_prop _ _ Heq as [Heq' H3].
      pose proof andb_prop _ _ Heq' as [H1 H2].
      intuition; by apply beq_nat_true.
    }
    right; right; do 2 eexists; eauto; intuition.
Qed.

Lemma eval_binop_undef :
  forall op v1 v2,
    eval_binop op v1 v2 = Undef ->
    (
      v1 = Undef
      \/
      v2 = Undef
      \/
      (op = Mul /\ exists p1 p2, v1 = Ptr p1 /\ v2 = Ptr p2)
      \/
      (op = Add /\ exists p1 p2, v1 = Ptr p1 /\ v2 = Ptr p2)
      \/
      (op <> Add /\ exists i p, v1 = Int i /\ v2 = Ptr p)
      \/
      (op <> Add /\ op <> Minus /\ exists i p, v1 = Ptr p /\ v2 = Int i)
      \/
      (op = Leq /\ exists p1 p2, v1 = Ptr p1 /\ v2 = Ptr p2 /\
                                 Pointer.permission p1 =? Pointer.permission p2 = false)
      \/
      (op = Minus /\ exists p1 p2, v1 = Ptr p1 /\ v2 = Ptr p2 /\
                                 Pointer.permission p1 =? Pointer.permission p2 = false)
      \/
      (op = Leq /\ exists p1 p2, v1 = Ptr p1 /\ v2 = Ptr p2 /\
                                 Pointer.component p1 =? Pointer.component p2 = false)
      \/
      (op = Minus /\ exists p1 p2, v1 = Ptr p1 /\ v2 = Ptr p2 /\
                                 Pointer.component p1 =? Pointer.component p2 = false)
      \/
      (op = Leq /\ exists p1 p2, v1 = Ptr p1 /\ v2 = Ptr p2 /\
                                 Pointer.block p1 =? Pointer.block p2 = false)
      \/
      (op = Minus /\ exists p1 p2, v1 = Ptr p1 /\ v2 = Ptr p2 /\
                                 Pointer.block p1 =? Pointer.block p2 = false)
    ).
Proof.
  intros op v1 v2 Heval.
  unfold eval_binop in Heval.
  destruct op eqn:eop;
    destruct v1 as [i1 | [[[perm1 cid1] bid1] off1] |] eqn:e1;
    destruct v2 as [i2 | [[[perm2 cid2] bid2] off2] |] eqn:e2;
    try discriminate; intuition.
  (* 11 subgoals remain. *)
  - do 3 right. left. intuition. by do 2 eexists.
  - do 4 right. left. intuition; try discriminate. by do 2 eexists.
  - destruct ((perm1 =? perm2) && (cid1 =? cid2) && (bid1 =? bid2)) eqn:Hvalid;
      try discriminate.
    apply andb_false_iff in Hvalid as [H1 | H2].
    + apply andb_false_iff in H1 as [H1 | H2].
      * do 7 right; left; intuition; by do 2 eexists.
      * do 9 right; left; intuition; by do 2 eexists.
    + do 11 right; intuition; by do 2 eexists.
  - do 4 right. left. intuition; try discriminate. by do 2 eexists.
  - do 5 right. left. intuition; try discriminate. by do 2 eexists.
  - do 2 right. left. intuition. by do 2 eexists.
  - do 4 right. left. intuition; try discriminate. by do 2 eexists.
  - do 5 right. left. intuition; try discriminate. by do 2 eexists.
  - do 4 right. left. intuition; try discriminate. by do 2 eexists.
  - do 5 right. left. intuition; try discriminate. by do 2 eexists.
  - unfold Pointer.leq in Heval.
    destruct ((perm1 =? perm2) && (cid1 =? cid2) && (bid1 =? bid2)) eqn:Hvalid;
      try discriminate.
    apply andb_false_iff in Hvalid as [H1 | H2].
    + apply andb_false_iff in H1 as [H1 | H2].
      * do 6 right; left; intuition; by do 2 eexists.
      * do 8 right; left; intuition; by do 2 eexists.
    + do 10 right; left; intuition; by do 2 eexists.
Qed.

Lemma eval_binop_op1_Undef:
  forall op v, eval_binop op Undef v = Undef.
Proof. by destruct op; auto.
Qed.

Lemma eval_binop_op2_Undef:
  forall op v, eval_binop op v Undef = Undef.
Proof. by destruct op; destruct v; auto.
Qed.

(* RB: TODO: Where should this go? Probably not values
   NOTE: It may be good to give the buffer type an explicit definition. *)
Module Buffer.
  Definition t : Type := nat + list value.

  Definition nth_error (buf : (nat + list value)) (i : Z) : option value :=
    let read (i : nat) : option value :=
        match buf with
        | inl n => if i <? n then Some Undef else None
        | inr vs => List.nth_error vs i
        end
    in
    match i with
    | Zpos n => read (Pos.to_nat n)
    | Z0 => read 0
    | Zneg _ => None
    end.

  Definition well_formed_buffer (buf : (nat + list value)) : bool :=
    match buf with
    | inl n => 0 <? n
    | inr vs => (0 <? seq.size vs) && seq.all (fun v => ~~is_ptr v) vs
    end.

  Definition well_formed_buffer_opt (buf : option (nat + list value)) : bool :=
    match buf with
    | Some buf => well_formed_buffer buf
    | _ => true
    end.
End Buffer.
