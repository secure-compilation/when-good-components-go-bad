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

Fixpoint good_user_of_Elocal_expr (sz: Z) (e: expr): Prop :=
  match e with
  | E_deref E_local => True
  | E_deref (E_binop Add E_local (E_val (Int n))) => (n < sz)%Z
  | E_assign E_local e' =>
      good_user_of_Elocal_expr sz e'
  | E_assign (E_binop Add E_local (E_val (Int n))) e' =>
      (n < sz)%Z /\ good_user_of_Elocal_expr sz e'
  | E_val _ | E_arg | E_exit => True
  | E_binop Mul (E_val (Int 0)) E_local => True (* this evaluates to error, so this is good! *)
  | E_binop _ e1 e2 => good_user_of_Elocal_expr sz e1 /\
                        good_user_of_Elocal_expr sz e2
  | E_seq e1 e2 => good_user_of_Elocal_expr sz e1 /\
                    good_user_of_Elocal_expr sz e2
  | E_if e1 e2 e3 => good_user_of_Elocal_expr sz e1 /\
                      good_user_of_Elocal_expr sz e2 /\
                      good_user_of_Elocal_expr sz e3
  | E_alloc e1 => good_user_of_Elocal_expr sz e1
  | E_deref e1 => good_user_of_Elocal_expr sz e1
  | E_assign e1 e2 => good_user_of_Elocal_expr sz e1 /\
                       good_user_of_Elocal_expr sz e2
  | E_call C P e' => good_user_of_Elocal_expr sz e'
  | E_callptr e1 e2 => good_user_of_Elocal_expr sz e1 /\
                        good_user_of_Elocal_expr sz e2
  | E_funptr P => True
  | E_local => False
  end.

Definition unfold_buffer (b : (nat + list value)%type) : list value :=
  match b with
  | inl n  => nseq n Undef
  | inr vs => vs
  end.

Definition buffer_size p (C : Component.id) : nat :=
  match Source.prog_buffers p C with
  | Some buf => size (unfold_buffer buf)
  | None => 0 (* Should not happen *)
  end.

Definition good_Elocal_usage_program (p: Source.program) : Prop :=
    (forall (C : Component.id) (P : Procedure.id) (expr : expr),
      Source.find_procedure (Source.prog_procedures p) C P = Some expr ->
      good_user_of_Elocal_expr (Z.of_nat (buffer_size p C)) expr).

Lemma good_Elocal_usage_program_link (p c: Source.program):
  Source.well_formed_program p ->
  Source.well_formed_program c ->
  linkable (Source.prog_interface p) (Source.prog_interface c) ->
  good_Elocal_usage_program p ->
  good_Elocal_usage_program c ->
  good_Elocal_usage_program (Source.program_link p c).
Proof.
  intros Hwfp Hwfc Hlinkable Hp Hc.
  unfold good_Elocal_usage_program.
  intros ? ? ? Hfind.

  destruct (C \in domm (Source.prog_interface c)) eqn:Cc.
  - rewrite Source.link_sym in Hfind; auto.
    assert (C \in domm (Source.prog_interface c) /\
            Source.find_procedure (Source.prog_procedures c) C P = Some expr)
      as [_ G].
    {
      eapply Source.find_procedure_in_linked_programs with (p2 := p); eauto.
      - apply linkable_sym. assumption.
      - destruct Hlinkable as [? G].
        rewrite fdisjointC in G.
        pose proof (@fdisjointP _ _ _ G) as G2.
        apply G2 in Cc. assumption.
    }
    specialize (Hc _ _ _ G).
    rewrite (Source.wfprog_defined_buffers) in Cc; eauto.
    assert (eq:(buffer_size (Source.program_link p c) C) =
              (buffer_size c C)).
    { unfold buffer_size in *. simpl.
      rewrite unionmE.
      destruct Hlinkable as [? G'].
      rewrite !Source.wfprog_defined_buffers in G'; eauto.
        rewrite fdisjointC in G'.
        pose proof (@fdisjointP _ _ _ G') as G3.
      apply G3 in Cc. move: Cc => /dommPn -> //=.
    }
    rewrite eq. auto.
  - assert (C \in domm (Source.prog_interface p) /\
            Source.find_procedure (Source.prog_procedures p) C P = Some expr)
      as [G' G].
    { eapply Source.find_procedure_in_linked_programs; eauto. rewrite Cc. auto. }
    specialize (Hp _ _ _ G).
    rewrite (Source.wfprog_defined_buffers) in Cc; eauto.
    rewrite (Source.wfprog_defined_buffers) in G'; eauto.
    assert (eq:(buffer_size (Source.program_link p c) C) =
              (buffer_size p C)).
    { unfold buffer_size in *. simpl.
      rewrite unionmE.
      move: G' => /dommP [] ? -> //=.
    }
    rewrite eq. auto.
Qed.

Lemma good_Elocal_usage_program_unlink (p c: Source.program):
  Source.well_formed_program p ->
  Source.well_formed_program c ->
  linkable (Source.prog_interface p) (Source.prog_interface c) ->
  good_Elocal_usage_program (Source.program_link p c) ->
  good_Elocal_usage_program p.
Proof.
  intros Hwfp Hwfc Hlinkable Hdiscpc.
  intros ? ? ? Hfind.
  assert (G: Source.find_procedure (Source.prog_procedures p) C P = Some expr \/
             Source.find_procedure (Source.prog_procedures c) C P = Some expr).
  { left. assumption. }
  apply Source.linkable_programs_find_procedure in G; auto.
  apply Hdiscpc in G.
  assert (eq:(buffer_size (Source.program_link p c) C) =
               (buffer_size p C)).
  { unfold buffer_size. simpl.
    rewrite unionmE.
    assert (H: (Source.prog_buffers p C)).
    { unfold Source.find_procedure in Hfind.
      destruct (Source.prog_procedures p C) eqn:procs_p_C; last discriminate.
      assert (G': exists n, Source.prog_procedures p C = Some n) by eauto.
      move: G' => /dommP.
      rewrite -Source.wfprog_defined_procedures; eauto.
      rewrite Source.wfprog_defined_buffers; eauto.
      by move=> /dommP [] ? -> //=.
    }
    rewrite H. reflexivity.
  }
  rewrite -eq. assumption.
Qed.
