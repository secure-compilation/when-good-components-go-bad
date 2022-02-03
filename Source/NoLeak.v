Require Import Lib.Extra.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import Common.Traces.
Require Import Common.TracesInform.
Require Import Common.RenamingOption.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.

Require Import Lia.

From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype seq.
From mathcomp Require ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Fixpoint has_no_local (e: expr) :=
  match e with
  | E_val v =>
      match v with
      | Ptr (Permission.data, _, 0, _) => False
      | _ => True
      end
  | E_local => False
  | E_binop b e1 e2 => has_no_local e1 /\ has_no_local e2
  | E_seq e1 e2 => has_no_local e2
  | E_if e1 e2 e3 => has_no_local e2 /\ has_no_local e3
  | E_alloc e1 => True
  | E_deref e1 => True
  | E_assign e1 e2 => True
  | E_call C P e1 => True
  | E_callptr e1 e2 => True
  | E_arg => True
  | E_funptr P => True
  | E_exit => True
  end.

Definition safe_value (v: value) :=
  match v with
  | Ptr (Permission.data, _, 0, _) => False
  | _ => True
  end.

Fixpoint safe_expr1 (e: expr) :=
  match e with
  | E_val v => safe_value v
  | E_local => True
  | E_binop b e1 e2 => safe_expr1 e1 /\ safe_expr1 e2
  | E_seq e1 e2 => safe_expr1 e1 /\ safe_expr1 e2
  | E_if e1 e2 e3 => safe_expr1 e1 /\ safe_expr1 e2 /\ safe_expr1 e3
  | E_alloc e1 => safe_expr1 e1
  | E_deref e1 => safe_expr1 e1
  | E_assign e1 e2 => safe_expr1 e1 /\ safe_expr1 e2 /\ has_no_local e2
  | E_call C P e1 => safe_expr1 e1
  | E_callptr e1 e2 => safe_expr1 e1 /\ safe_expr1 e2
  | E_arg => True
  | E_funptr P => True
  | E_exit => True
  end.

Fixpoint safe_cont1 (k: cont) :=
  match k with
  | Kstop => True
  | Kbinop1 _ e k => safe_expr1 e /\ safe_cont1 k
  | Kbinop2 _ _ k => safe_cont1 k
  | Kseq e k => safe_expr1 e /\ safe_cont1 k
  | Kif e1 e2 k => safe_expr1 e1 /\ safe_expr1 e2 /\ safe_cont1 k
  | Kalloc k => safe_cont1 k
  | Kderef k => safe_cont1 k
  | Kassign1 e k => safe_expr1 e /\ safe_cont1 k
  | Kassign2 _ k => safe_cont1 k
  | Kcall _ _ k => safe_cont1 k
  | Kcallptr1 e k => safe_expr1 e /\ safe_cont1 k
  | Kcallptr2 _ k => safe_cont1 k
  end.

(* Hope that: safe_expr e -> exists n, safe_cont_expr1 n Kstop e *)
(* k = Kassign1 e1 v and e = E_local -> safe_expr e /\ ~ safe_cont_expr1 n k e *)
Fixpoint size_expr (e: expr) :=
  match e with
  | E_val _ => 0
  | E_arg => 1
  | E_local => 1
  | E_binop b e1 e2 => 3 + size_expr e1 + size_expr e2
  | E_seq e1 e2 => 2 + size_expr e1 + size_expr e2
  | E_if e1 e2 e3 => 2 + size_expr e1 + size_expr e2 + size_expr e3
  | E_alloc e => 2 + size_expr e
  | E_deref e => 2 + size_expr e
  | E_assign e1 e2 => 3 + size_expr e1 + size_expr e2
  | E_call _ _ e => 2 + size_expr e
  | E_callptr e1 e2 => 4 + size_expr e1 + size_expr e2
  | E_funptr P => 1
  | E_exit => 1
  end.

Fixpoint size_cont (k: cont) :=
  match k with
  | Kstop => 0
  | Kbinop1 b e k => 2 + size_expr e + size_cont k
  | Kbinop2 b v k => 1 + size_cont k
  | Kseq e k => 1 + size_expr e + size_cont k
  | Kif e2 e3 k => 1 + size_expr e2 + size_expr e3 + size_cont k
  | Kalloc k => 1 + size_cont k
  | Kderef k => 1 + size_cont k
  | Kassign1 e k => 2 + size_expr e + size_cont k
  | Kassign2 v k => 1 + size_cont k
  | Kcall _ _ k => 1 + size_cont k
  | Kcallptr1 e k => 3 + size_expr e + size_cont k
  | Kcallptr2 v k => 2 + size_cont k
  end.

Inductive safe_cont_expr: cont -> expr -> Prop :=
| safe_cont_expr_E_local: forall k,
    (forall C, safe_cont_expr k (E_val (Ptr (Permission.data, C, Block.local, 0%Z)))) ->
    safe_cont_expr k E_local
| safe_cont_expr_E_binop: forall k b e1 e2,
    safe_cont_expr (Kbinop1 b e2 k) e1 ->
    safe_cont_expr k (E_binop b e1 e2)
| safe_cont_expr_E_seq: forall k e1 e2,
    safe_cont_expr (Kseq e2 k) e1 ->
    safe_cont_expr k (E_seq e1 e2)
| safe_cont_expr_E_if: forall k e1 e2 e3,
    safe_cont_expr (Kif e2 e3 k) e1 ->
    safe_cont_expr k (E_if e1 e2 e3)
| safe_cont_expr_E_alloc: forall k e1,
    safe_cont_expr (Kalloc k) e1 ->
    safe_cont_expr k (E_alloc e1)
| safe_cont_expr_E_deref: forall k e1,
    safe_cont_expr (Kderef k) e1 ->
    safe_cont_expr k (E_deref e1)
| safe_cont_expr_E_assign: forall k e1 e2,
    safe_cont_expr (Kassign1 e1 k) e2 ->
    safe_cont_expr k (E_assign e1 e2)
| safe_cont_expr_E_call: forall k C P e1,
    safe_cont_expr (Kcall C P k) e1 ->
    safe_cont_expr k (E_call C P e1)
| safe_cont_expr_E_callptr: forall k e1 e2,
    safe_cont_expr (Kcallptr1 e1 k) e2 ->
    safe_cont_expr k (E_callptr e1 e2)
| safe_cont_expr_E_arg: forall k,
    (forall v, safe_value v -> safe_cont_expr k (E_val v)) ->
    safe_cont_expr k E_arg
| safe_cont_expr_E_exit: forall k,
    safe_cont_expr k E_exit
| safe_cont_expr_E_funptr: forall k P,
    (forall v, safe_value v -> safe_cont_expr k (E_val v)) ->
    safe_cont_expr k (E_funptr P)
| safe_cont_expr_E_val_Kstop: forall v,
    safe_value v ->
    safe_cont_expr Kstop (E_val v)
| safe_cont_expr_E_val_Kbinop1: forall b e2 k v,
    safe_cont_expr (Kbinop2 b v k) e2 ->
    safe_cont_expr (Kbinop1 b e2 k) (E_val v)
| safe_cont_expr_E_val_Kbinop2: forall b v' k v,
    safe_cont_expr k (E_val (eval_binop b v' v)) ->
    safe_cont_expr (Kbinop2 b v' k) (E_val v)
| safe_cont_expr_E_val_Kseq: forall e k v,
    safe_cont_expr k e ->
    safe_cont_expr (Kseq e k) (E_val v)
| safe_cont_expr_E_val_Kif: forall e2 e3 k v,
    safe_cont_expr k e2 ->
    safe_cont_expr k e3 ->
    safe_cont_expr (Kif e2 e3 k) (E_val v)
| safe_cont_expr_E_val_Kalloc: forall k v,
    (forall v, safe_value v -> safe_cont_expr k (E_val v)) ->
    safe_cont_expr (Kalloc k) (E_val v)
| safe_cont_expr_E_val_Kderef: forall k v,
    (forall v, safe_value v -> safe_cont_expr k (E_val v)) ->
    safe_cont_expr (Kderef k) (E_val v)
| safe_cont_expr_E_val_Kassign1: forall e1 k v,
    safe_value v ->
    safe_cont_expr (Kassign2 v k) e1 ->
    safe_cont_expr (Kassign1 e1 k) (E_val v)
| safe_cont_expr_E_val_Kassign2: forall v' k v,
    safe_value v' ->
    safe_cont_expr k (E_val v') ->
    safe_cont_expr (Kassign2 v' k) (E_val v)
| safe_cont_expr_E_val_Kcall: forall C P k v,
    safe_value v ->
    (forall v', safe_value v' -> safe_cont_expr k (E_val v')) ->
    safe_cont_expr (Kcall C P k) (E_val v)
| safe_cont_expr_E_val_Kcallptr1: forall e1 k v,
    safe_value v ->
    safe_cont_expr (Kcallptr2 v k) e1 ->
    safe_cont_expr (Kcallptr1 e1 k) (E_val v)
| safe_cont_expr_E_val_Kcallptr2: forall v' k v,
    safe_value v' ->
    (forall C P, safe_cont_expr (Kcall C P k) (E_val v')) ->
    safe_cont_expr (Kcallptr2 v' k) (E_val v)
.

(* Require Import Coq.Program.Wf. *)
(* Program Fixpoint safe_cont_expr (k: cont) (e: expr) {measure (size_cont k + size_expr e)}:= *)
(*   match e with *)
(*   | E_val v => *)
(*       match k with *)
(*       | Kstop => safe_value v (* necessary because [Kstop] can mean: we're returning to another component *) *)
(*       | Kbinop1 b e2 k => safe_cont_expr (Kbinop2 b v k) e2 *)
(*       | Kbinop2 b v' k => safe_cont_expr k (E_val (eval_binop b v' v)) *)
(*       | Kseq e k => safe_cont_expr k e *)
(*       | Kif e2 e3 k => safe_cont_expr k e2 /\ *)
(*                         safe_cont_expr k e3 *)
(*       | Kalloc k => (forall v, safe_value v -> safe_cont_expr k (E_val v)) *)
(*       | Kderef k => (forall v, safe_value v -> safe_cont_expr k (E_val v)) *)
(*       | Kassign1 e1 k => safe_value v /\ safe_cont_expr (Kassign2 v k) e1 *)
(*       | Kassign2 v' k => safe_value v' /\ safe_cont_expr k (E_val v') *)
(*       | Kcall C P k => safe_value v /\ (forall v', safe_value v' -> safe_cont_expr k (E_val v')) *)
(*       | Kcallptr1 e1 k => safe_value v /\ safe_cont_expr (Kcallptr2 v k) e1 *)
(*       | Kcallptr2 v' k => safe_value v' /\ (forall C P, safe_cont_expr (Kcall C P k) (E_val v')) *)
(*       end *)
(*   | E_local => *)
(*       forall C, safe_cont_expr k (E_val (Ptr (Permission.data, C, Block.local, 0%Z))) *)
(*   | E_binop b e1 e2 => safe_cont_expr (Kbinop1 b e2 k) e1 *)
(*   | E_seq e1 e2 =>  safe_cont_expr (Kseq e2 k) e1 *)
(*   | E_if e1 e2 e3 => safe_cont_expr (Kif e2 e3 k) e1 *)
(*   | E_alloc e1 => safe_cont_expr (Kalloc k) e1 *)
(*   | E_deref e1 => safe_cont_expr (Kderef k) e1 *)
(*   | E_assign e1 e2 => safe_cont_expr (Kassign1 e1 k) e2 *)
(*   | E_call C P e1 => safe_cont_expr (Kcall C P k) e1 *)
(*   | E_callptr e1 e2 => safe_cont_expr (Kcallptr1 e1 k) e2 *)
(*   | E_arg => (forall v, safe_value v -> safe_cont_expr k (E_val v)) *)
(*   | E_funptr P => (forall v, safe_value v -> safe_cont_expr k (E_val v)) *)
(*   | E_exit => True *)
(*   end. *)
(* Next Obligation. simpl. lia. Defined. *)
(* Next Obligation. simpl. lia. Defined. *)
(* Next Obligation. simpl. lia. Defined. *)
(* Next Obligation. simpl. lia. Defined. *)
(* Next Obligation. simpl. lia. Defined. *)
(* Next Obligation. simpl. lia. Defined. *)
(* Next Obligation. simpl. lia. Defined. *)
(* Next Obligation. simpl. lia. Defined. *)
(* Next Obligation. simpl. lia. Defined. *)
(* Next Obligation. simpl. lia. Defined. *)
(* Next Obligation. simpl. lia. Defined. *)
(* Next Obligation. simpl. lia. Defined. *)
(* Next Obligation. simpl. lia. Defined. *)
(* Next Obligation. simpl. lia. Defined. *)
(* Next Obligation. simpl. lia. Defined. *)
(* Next Obligation. simpl. lia. Defined. *)
(* Next Obligation. simpl. lia. Defined. *)

(* Fixpoint safe_cont_expr1 (n: nat) (k: cont) (e: expr) := *)
(*   match n with *)
(*   | 0 => False *)
(*   | S n => *)
(*       match e with *)
(*       | E_val v => *)
(*           match k with *)
(*           | Kstop => safe_value v (* necessary because [Kstop] can mean: we're returning to another component *) *)
(*           | Kbinop1 b e2 k => safe_cont_expr1 n (Kbinop2 b v k) e2 *)
(*           | Kbinop2 b v' k => safe_cont_expr1 n k (E_val (eval_binop b v' v)) *)
(*           | Kseq e k => safe_cont_expr1 n k e *)
(*           | Kif e2 e3 k => safe_cont_expr1 n k e2 /\ *)
(*                             safe_cont_expr1 n k e3 *)
(*           | Kalloc k => (forall v, safe_value v -> safe_cont_expr1 n k (E_val v)) *)
(*           | Kderef k => (forall v, safe_value v -> safe_cont_expr1 n k (E_val v)) *)
(*           | Kassign1 e1 k => safe_value v /\ safe_cont_expr1 n (Kassign2 v k) e1 *)
(*           | Kassign2 v' k => safe_value v' /\ safe_cont_expr1 n k (E_val v') *)
(*           | Kcall C P k => safe_value v /\ (forall v', safe_value v' -> safe_cont_expr1 n k (E_val v')) *)
(*           | Kcallptr1 e1 k => safe_value v /\ safe_cont_expr1 n (Kcallptr2 v k) e1 *)
(*           | Kcallptr2 v' k => safe_value v' /\ (forall C P, safe_cont_expr1 n (Kcall C P k) (E_val v')) *)
(*           end *)
(*       | E_local => *)
(*           forall C, safe_cont_expr1 n k (E_val (Ptr (Permission.data, C, Block.local, 0%Z))) *)
(*       | E_binop b e1 e2 => safe_cont_expr1 n (Kbinop1 b e2 k) e1 *)
(*       | E_seq e1 e2 =>  safe_cont_expr1 n (Kseq e2 k) e1 *)
(*       | E_if e1 e2 e3 => safe_cont_expr1 n (Kif e2 e3 k) e1 *)
(*       | E_alloc e1 => safe_cont_expr1 n (Kalloc k) e1 *)
(*       | E_deref e1 => safe_cont_expr1 n (Kderef k) e1 *)
(*       | E_assign e1 e2 => safe_cont_expr1 n (Kassign1 e1 k) e2 *)
(*       | E_call C P e1 => safe_cont_expr1 n (Kcall C P k) e1 *)
(*       | E_callptr e1 e2 => safe_cont_expr1 n (Kcallptr1 e1 k) e2 *)
(*       | E_arg => (forall v, safe_value v -> safe_cont_expr1 n k (E_val v)) *)
(*       | E_funptr P => (forall v, safe_value v -> safe_cont_expr1 n k (E_val v)) *)
(*       | E_exit => True *)
(*       end *)
(*   end. *)
(* Arguments safe_cont_expr1: simpl nomatch. *)

(* Definition safe_expr_cont (e: expr) (k: cont) := *)
(*   safe_expr1 e /\ safe_cont1 k. *)

(* Lemma safe_S_n: forall n k e, *)
(*     safe_cont_expr1 n k e -> *)
(*     safe_cont_expr1 (S n) k e. *)
(* Proof. *)
(*   induction n. *)
(*   - intros. by []. *)
(*   - intros k e safe. *)
(*     destruct k, e; simpl in *; auto; *)
(*       (repeat (match goal with *)
(*                | H: _ /\ _ |- _ => destruct H *)
(*                | |- _ /\ _ => split *)
(*                end)); *)
(*       (repeat match goal with *)
(*               | H: safe_cont_expr1 n _ _ |- _ => apply IHn in H *)
(*               end); *)
(*       try (now auto); *)
(*       try now (intros v0 safe_v0; specialize (safe v0 safe_v0); apply IHn in safe; auto). *)
(*     (* + intros v; specialize (H0 v); apply IHn in H0; auto. *) *)
(*     (* + destruct v as [| [[[[]] []]] |]; auto. *) *)
(*     (*   apply IHn in safe; auto. *) *)
(*     + intros C. specialize (safe C); apply IHn in safe; auto. *)
(*     + intros C. specialize (safe C); apply IHn in safe; auto. *)
(*     + intros C. specialize (safe C); apply IHn in safe; auto. *)
(*     + intros C. specialize (safe C); apply IHn in safe; auto. *)
(*     + intros C. specialize (safe C); apply IHn in safe; auto. *)
(*     + intros C. specialize (safe C); apply IHn in safe; auto. *)
(*     + intros C. specialize (safe C); apply IHn in safe; auto. *)
(*     + intros C. specialize (safe C); apply IHn in safe; auto. *)
(*     + intros C0. specialize (safe C0); apply IHn in safe; auto. *)
(*     + intros C0. specialize (safe C0); apply IHn in safe; auto. *)
(*     (* + intros C0. specialize (safe C); apply IHn in safe; auto. *) *)
(*     + intros C. specialize (safe C); apply IHn in safe; auto. *)
(*     + intros C P. specialize (H0 C P); apply IHn in H0; auto. *)
(*     + intros C. specialize (safe C); apply IHn in safe; auto. *)
(* Qed. *)

Definition safe_memory (mem: Memory.t) :=
  forall ptr v,
    Memory.load mem ptr = Some v ->
    safe_value v.

Definition safe_stack (stk: CS.stack) :=
  List.Forall (fun frm => (forall v, safe_value v -> safe_cont_expr (CS.f_cont frm) (E_val v))
                       /\ safe_value (CS.f_arg frm)) stk.

Lemma safe_preserved_by_step (ge: global_env)
      (ge_good: forall C P expr,
          Source.find_procedure (genv_procedures ge) C P = Some expr ->
          safe_cont_expr Kstop expr):
  forall s1 s2 t0 t,
    safe_memory (CS.s_memory s1) ->
    (forall C n, Memory.next_block (CS.s_memory s1) C = Some n ->
            n > 0) ->
    safe_cont_expr (CS.s_cont s1) (CS.s_expr s1)->
    safe_stack (CS.s_stack s1) ->
    safe_value (CS.s_arg s1) ->
    good_trace_extensional (left_addr_good_for_shifting (uniform_shift 1)) t0 ->
    CS.kstep ge s1 t s2 ->
    safe_memory (CS.s_memory s2) /\
      (forall C n, Memory.next_block (CS.s_memory s2) C = Some n ->
              n > 0) /\
      safe_cont_expr (CS.s_cont s2) (CS.s_expr s2) /\
      safe_stack (CS.s_stack s2) /\
      safe_value (CS.s_arg s2) /\
    good_trace_extensional (left_addr_good_for_shifting (uniform_shift 1)) (t0 ** t).
Proof.
  intros s1 s2 t0' t0 safe_mem nextblock_mem
         safe_k_e safe_stk safe_arg good_trace step.
  destruct s1, s2; subst; simpl in *.
  inversion step; subst;
    (try rewrite E0_right);
    try (inversion safe_k_e; subst; eauto);
    try now intuition.
  - destruct (i != 0%Z); intuition.
  - (* Alloc *)
    intuition.
    + intros ptr' v Hload.
      case eC: (Pointer.component ptr == Pointer.component ptr');
        case eB: (Pointer.block ptr == Pointer.block ptr');
        move: eC => /eqP eC; subst;
                   move: eB => /eqP eB; subst.
      * erewrite Memory.load_after_alloc_eq in Hload; [| eassumption | auto].
        move: Hload; case _: ifP; last by [].
        case _: ifP; last by [].
        case _: ifP; last by [].
        by move=> _ _ _ [] <- //=.
      * erewrite Memory.load_after_alloc in Hload; [| eassumption | congruence].
        eapply safe_mem; eauto.
      * erewrite Memory.load_after_alloc in Hload; [| eassumption | congruence].
        eapply safe_mem; eauto.
      * erewrite Memory.load_after_alloc in Hload; [| eassumption | congruence].
        eapply safe_mem; eauto.
    + destruct (C == s_component0) eqn:eC;
        move: eC => /eqP eC; subst.
      * eapply Memory.next_block_alloc in H13 as [G1 G2].
        rewrite G2 in H; inversion H. rewrite ssrnat.addn1; lia.
      * erewrite Memory.next_block_alloc_neq in H; eauto.
    + eapply H1. eapply Memory.next_block_alloc in H13 as [G1 G2].
      eapply nextblock_mem in G1.
      destruct ptr as [[[[]] b]]; first by [].
      now destruct b.
  (* - intuition. *)
  - intuition. by eapply H1.
  - (* Store *)
    intuition.
    + intros ptr' v' Hload.
      destruct (Pointer.eqP (P', C', b', o') ptr') as [e | e].
      * subst.
        erewrite (Memory.load_after_store_eq _ _ v) in Hload; eauto.
        by inversion Hload; subst; clear Hload.
      * erewrite Memory.load_after_store_neq in Hload; eauto.
    + erewrite Memory.next_block_store_stable in H; eauto.
  - (* Calls *)
    intuition.
    + constructor; intuition.
  - intuition. (* Same case as previously *)
    + constructor; intuition.
    + constructor. unfold Eapp.
      replace (t0' ++ [:: ECall s_component P s_arg0 s_memory0 s_component0])%list
        with (t0' ++ [:: ECall s_component P s_arg0 s_memory0 s_component0]) by reflexivity.
      rewrite cats1.
      intros a shared.
      inversion shared; subst; clear shared.
      * find_rcons_rcons.
        inversion H2.
        -- inversion good_trace; subst; clear good_trace.
           simpl in H. destruct s_arg0 as [| [[[[]]]] |]; try by rewrite in_fset0 in H.
           destruct a; rewrite in_fset1 in H; move: H => /eqP ->.
           simpl in H1. now destruct i0.
        -- subst.
           destruct a as [cid' bid'].
           apply In_in in H3; apply ComponentMemory.load_block_load in H3 as [off' [off load]].
           assert (load': Memory.load s_memory0 (Permission.data, cid, bid, off) = Some (Ptr (Permission.data, cid', bid', off'))).
           { unfold Memory.load => //=.
             by rewrite H0. }
           eapply safe_mem in load'. simpl in *. now destruct bid'.
      * find_rcons_rcons.
        inversion H3.
        -- inversion good_trace; subst; clear good_trace.
           eapply H5; eauto. by rewrite in_fset1 in H; move: H => /eqP ->.
        -- subst.
           destruct a as [cid' bid'].
           apply In_in in H5; apply ComponentMemory.load_block_load in H5 as [off' [off load]].
           assert (load': Memory.load s_memory0 (Permission.data, cid, bid, off) = Some (Ptr (Permission.data, cid', bid', off'))).
           { unfold Memory.load => //=.
             by rewrite H2. }
           eapply safe_mem in load'. simpl in *. now destruct bid'.
  - inversion safe_stk; intuition.
  - inversion safe_stk; intuition.
    constructor. unfold Eapp.
    replace (t0' ++ [:: ERet s_component v s_memory0 s_component0])%list
      with (t0' ++ [:: ERet s_component v s_memory0 s_component0]) by reflexivity.
    rewrite cats1.
    intros a shared.
    inversion shared; subst; clear shared.
    + find_rcons_rcons.
      inversion H8.
      * inversion good_trace; subst; clear good_trace.
        simpl in H. destruct v as [| [[[[]]]] |]; try by rewrite in_fset0 in H.
        destruct a; rewrite in_fset1 in H; move: H => /eqP ->.
        simpl in H0. now destruct i0.
      * subst.
        destruct a as [cid' bid'].
        apply In_in in H2; apply ComponentMemory.load_block_load in H2 as [off' [off load]].
        assert (load': Memory.load s_memory0 (Permission.data, cid, bid, off) = Some (Ptr (Permission.data, cid', bid', off'))).
        { unfold Memory.load => //=.
          by rewrite H1. }
        eapply safe_mem in load'. simpl in *. now destruct bid'.
      + find_rcons_rcons.
        inversion H9.
        * inversion good_trace; subst; clear good_trace.
          eapply H2; eauto. by rewrite in_fset1 in H; move: H => /eqP ->.
        * subst.
          destruct a as [cid' bid'].
          apply In_in in H2; apply ComponentMemory.load_block_load in H2 as [off' [off load]].
           assert (load': Memory.load s_memory0 (Permission.data, cid, bid, off) = Some (Ptr (Permission.data, cid', bid', off'))).
           { unfold Memory.load => //=.
             by rewrite H1. }
           eapply safe_mem in load'. simpl in *. now destruct bid'.
Qed.

Lemma safe_preserved_by_star: forall (p: Source.program) (s : CS.state) (t : trace event),
    (forall C P expr,
        Source.find_procedure (Source.prog_procedures p) C P = Some expr ->
        safe_cont_expr Kstop expr) ->
    safe_memory (Source.prepare_buffers p) ->
    Star (CS.sem p) (CS.initial_machine_state p) t s ->
    safe_memory (CS.s_memory s) /\
    good_trace_extensional (left_addr_good_for_shifting (uniform_shift 1)) t.
Proof.
  intros p s t p_good safe_mem_prep star.
  unfold CS.initial_machine_state in star.
  destruct (Source.prog_main p) eqn:prog_main.
  - assert (ge_good: (forall (C : Component.id) (P : Procedure.id) (expr : expr),
                         Source.find_procedure (genv_procedures (prepare_global_env p)) C P = Some expr ->
                         safe_cont_expr Kstop expr)) by exact p_good.
    remember [CState Component.main, [::], Source.prepare_buffers p, Kstop, e, Int 0] as s0.
    assert (safe_mem: safe_memory (CS.s_memory s0)) by (subst s0; eauto).
    assert (safe_k_e: safe_cont_expr (CS.s_cont s0) (CS.s_expr s0)) by (subst s0; eauto).
    assert (safe_stk: safe_stack (CS.s_stack s0)) by (subst s0; constructor).
    assert (safe_arg: safe_value (CS.s_arg s0)) by (now subst s0).
    assert (nextblock_mem: forall (C : Component.id) (n : Block.id),
               Memory.next_block (CS.s_memory s0) C = Some n ->
               n > 0).
    { subst s0. simpl.
      move=> C n.
      rewrite /Memory.next_block /Source.prepare_buffers mapmE.
      case: (Source.prog_buffers p C) => //= ? [].
      rewrite ComponentMemory.nextblock_prealloc.
      case: n; [by [] | lia]. }
    assert (good_empty: good_trace_extensional (left_addr_good_for_shifting (uniform_shift 1)) [::]).
    { constructor. intros ? shared. inversion shared; now destruct t0. }
    clear Heqs0. apply star_iff_starR in star.
    assert (safe_memory (CS.s_memory s) /\
              (forall (C : Component.id) (n : Block.id), Memory.next_block (CS.s_memory s) C = Some n -> n > 0) /\
              safe_cont_expr (CS.s_cont s) (CS.s_expr s) /\
              safe_stack (CS.s_stack s) /\
              safe_value (CS.s_arg s) /\ good_trace_extensional (left_addr_good_for_shifting (uniform_shift 1)) t).
    { induction star.
      + intuition.
      + subst.
        specialize (IHstar safe_mem safe_k_e safe_stk safe_arg nextblock_mem) as [? [? [? [? [? ?]]]]].
        eapply safe_preserved_by_step in H as [? [? [? [? [? ?]]]]]; intuition. }
    intuition.
  - inversion star as [| ? ? ? ? ? ? step];
      last inversion step.
    subst. split.
    + intros [[[[]]]] v; first by [].
      rewrite /Memory.load //=.
    + constructor; intros ? shared; inversion shared; now destruct t.
Qed.

Lemma star_never_leaks: forall (p: Source.program),
    (forall C P expr,
        Source.find_procedure (Source.prog_procedures p) C P = Some expr ->
        safe_cont_expr Kstop expr) ->
    safe_memory (Source.prepare_buffers p) ->
    CS.CS.private_pointers_never_leak_S p (uniform_shift 1).
Proof.
  intros p p_good safe_mem s t star. (* p_good. safe_mem star. *)
  eapply safe_preserved_by_star in star as [G1 G2]; subst; intuition.
  rewrite /shared_locations_have_only_shared_values.
  intros ptr [cid bid] v load_ptr eq_addr; inversion eq_addr; subst; clear eq_addr.
  specialize (G1 _ _ load_ptr).
  destruct v as [| [[[[]] b]] |]; auto.
  rewrite /left_value_good_for_shifting /left_addr_good_for_shifting
          /left_block_id_good_for_shifting //=.
  simpl in G1; destruct b; first contradiction.
  unfold uniform_shift; by [].
Qed.
