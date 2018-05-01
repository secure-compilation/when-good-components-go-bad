Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.CompCertExtensions.
Require Import Common.Traces.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Lib.Tactics.
Require Import Lib.Monads.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From mathcomp Require ssrnat.

Canonical ssrnat.nat_eqType.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import Source.

Inductive cont : Type :=
| Kstop
| Kbinop1 (op: binop) (re: expr) (k: cont)
| Kbinop2 (op: binop) (lv: value) (k: cont)
| Kseq (e: expr) (k: cont)
| Kif (e1: expr) (e2: expr) (k: cont)
| Kalloc (k: cont)
| Kderef (k: cont)
| Kassign1 (e: expr) (k: cont)
| Kassign2 (v: value) (k: cont)
| Kcall (C: Component.id) (P: Procedure.id) (k: cont).

Module CS.

Definition stack : Type := list (Component.id * value * cont).

Definition state : Type := Component.id * stack * Memory.t * cont * expr.

Ltac unfold_state st :=
  let C := fresh "C" in
  let s := fresh "s" in
  let mem := fresh "mem" in
  let k := fresh "k" in
  let e := fresh "e" in
  destruct st as [[[[C s] mem] k] e].

Ltac unfold_states :=
  repeat (match goal with
          | st: state |- _ => unfold_state st
          end).

Instance state_turn : HasTurn state := {
  turn_of s iface :=
    let '(C, _, _, _, _) := s in
    C \in domm iface
}.

Import MonadNotations.
Open Scope monad_scope.

Definition prepare_initial_memory (p: program) : Memory.t :=
  fst (prepare_buffers p).

Definition initial_machine_state (p: program) : state :=
  match prog_main p with
  | Some main_expr =>
    (Component.main, [], prepare_initial_memory p, Kstop, main_expr)
  | None =>
    (* this case shouldn't happen for a well formed p *)
    (0, [], emptym, Kstop, E_exit)
  end.

(* transition system *)

Definition initial_state (p: program) (st: state) : Prop :=
  st = initial_machine_state p.

Definition final_state (st: state) : Prop :=
  let '(C, s, mem, k, e) := st in
  e = E_exit \/ (exists v, e = E_val v /\ k = Kstop /\ s = []).

Inductive kstep (G: global_env) : state -> trace -> state -> Prop :=
| KS_Binop1 : forall C s mem k op e1 e2,
    kstep G (C, s, mem, k, E_binop op e1 e2) E0
            (C, s, mem, Kbinop1 op e2 k, e1)
| KS_Binop2 : forall C s mem k op v1 e2,
    kstep G (C, s, mem, Kbinop1 op e2 k, E_val v1) E0
            (C, s, mem, Kbinop2 op v1 k, e2)
| KS_BinopEval : forall C s mem k op v1 v2,
    kstep G (C, s, mem, Kbinop2 op v1 k, E_val v2) E0
            (C, s, mem, k, E_val (eval_binop op v1 v2))
| KS_Seq1 :  forall C s mem k e1 e2,
    kstep G (C, s, mem, k, E_seq e1 e2) E0
            (C, s, mem, Kseq e2 k, e1)
| KS_Seq2 : forall C s mem k v e2,
    kstep G (C, s, mem, Kseq e2 k, E_val v) E0
            (C, s, mem, k, e2)
| KS_If : forall C s mem k e1 e2 e3,
    kstep G (C, s, mem, k, E_if e1 e2 e3) E0
            (C, s, mem, Kif e2 e3 k, e1)
| KS_IfTrue : forall C s mem k e2 e3 i,
    (i <> 0) % Z ->
    kstep G (C, s, mem, Kif e2 e3 k, E_val (Int i)) E0
            (C, s, mem, k, e2)
| KS_IfFalse : forall C s mem k e2 e3,
    kstep G (C, s, mem, Kif e2 e3 k, E_val (Int 0)) E0
            (C, s, mem, k, e3)
| KS_LocalBuffer : forall C s mem k b,
    getm (genv_buffers G) C = Some b ->
    kstep G (C, s, mem, k, E_local) E0
            (C, s, mem, k, E_val (Ptr (C,b,0%Z)))
| KS_Alloc1 : forall C s mem k e,
    kstep G (C, s, mem, k, E_alloc e) E0
            (C, s, mem, Kalloc k, e)
| KS_AllocEval : forall C s mem mem' k size ptr,
    (size > 0) % Z ->
    Memory.alloc mem C (Z.to_nat size) = Some (mem', ptr) ->
    kstep G (C, s, mem, Kalloc k, E_val (Int size)) E0
            (C, s, mem', k, E_val (Ptr ptr))
| KS_Deref1 : forall C s mem k e,
    kstep G (C, s, mem, k, E_deref e) E0
            (C, s, mem, Kderef k, e)
| KS_DerefEval : forall C s mem k C' b' o' v,
    C = C' ->
    Memory.load mem (C',b',o') = Some v ->
    kstep G (C, s, mem, Kderef k, E_val (Ptr (C',b',o'))) E0
            (C, s, mem, k, E_val v)
| KS_Assign1 : forall C s mem k e1 e2,
    kstep G (C, s, mem, k, E_assign e1 e2) E0
            (C, s, mem, Kassign1 e1 k, e2)
| KS_Assign2 : forall C s mem k v e1,
    kstep G (C, s, mem, Kassign1 e1 k, E_val v) E0
            (C, s, mem, Kassign2 v k, e1)
| KS_AssignEval : forall C s mem mem' k v C' b' o',
    C = C' ->
    Memory.store mem (C', b', o') v = Some mem' ->
    kstep G (C, s, mem, Kassign2 v k, E_val (Ptr (C', b', o'))) E0
            (C, s, mem', k, E_val v)
| KS_InitCall : forall C s mem k C' P e,
    kstep G (C, s, mem, k, E_call C' P e) E0
            (C, s, mem, Kcall C' P k, e)
| KS_InternalCall : forall C s mem mem' k C' P v P_expr b b' old_call_arg,
    C = C' ->
    (* retrieve the procedure code *)
    find_procedure (genv_procedures G) C' P = Some P_expr ->
    (* save the old call argument *)
    getm (genv_buffers G) C = Some b ->
    Memory.load mem (C, b, 0%Z) = Some old_call_arg ->
    (* place the call argument in the target memory *)
    getm (genv_buffers G) C' = Some b' ->
    Memory.store mem (C', b', 0%Z) (Int v) = Some mem' ->
    kstep G (C, s, mem, Kcall C' P k, E_val (Int v)) E0
            (C', (C, old_call_arg, k) :: s, mem', Kstop, P_expr)
| KS_ExternalCall : forall C s mem mem' k C' P v P_expr b b' old_call_arg,
    C <> C' ->
    (* check permission *)
    imported_procedure (genv_interface G) C C' P  ->
    (* retrieve the procedure code *)
    find_procedure (genv_procedures G) C' P = Some P_expr ->
    (* save the old call argument *)
    getm (genv_buffers G) C = Some b ->
    Memory.load mem (C, b, 0%Z) = Some old_call_arg ->
    (* place the call argument in the target memory *)
    getm (genv_buffers G) C' = Some b' ->
    Memory.store mem (C', b', 0%Z) (Int v) = Some mem' ->
    kstep G (C, s, mem, Kcall C' P k, E_val (Int v))
            [ECall C P v C']
            (C', (C, old_call_arg, k) :: s, mem', Kstop, P_expr)
| KS_InternalReturn: forall C s mem mem' k v C' old_call_arg b,
    C = C' ->
    (* restore the old call argument *)
    getm (genv_buffers G) C' = Some b ->
    Memory.store mem (C', b, 0%Z) old_call_arg = Some mem' ->
    kstep G (C, (C', old_call_arg, k) :: s, mem, Kstop, E_val (Int v)) E0
            (C', s, mem', k, E_val (Int v))
| KS_ExternalReturn: forall C s mem mem' k v C' old_call_arg b,
    C <> C' ->
    (* restore the old call argument *)
    getm (genv_buffers G) C' = Some b ->
    Memory.store mem (C', b, 0%Z) old_call_arg = Some mem' ->
    kstep G (C, (C', old_call_arg, k) :: s, mem, Kstop, E_val (Int v))
            [ERet C v C']
            (C', s, mem', k, E_val (Int v)).

(* functional kstep *)

Definition eval_kstep (G : global_env) (st : state) : option (trace * state) :=
  let '(C, s, mem, k, e) := st in
  match e with
  (* pushing a new continuation *)
  | E_binop b_op e1 e2 =>
    ret (E0, (C, s, mem, Kbinop1 b_op e2 k, e1))
  | E_seq e1 e2 =>
    ret (E0, (C, s, mem, Kseq e2 k, e1))
  | E_if e1 e2 e3 =>
    ret (E0, (C, s, mem, Kif e2 e3 k, e1))
  | E_local =>
    do b <- getm (genv_buffers G) C;
    ret (E0, (C, s, mem, k, E_val (Ptr (C, b, 0%Z))))
  | E_alloc e =>
    ret (E0, (C, s, mem, Kalloc k, e))
  | E_deref e =>
    ret (E0, (C, s, mem, Kderef k, e))
  | E_assign e1 e2 =>
    ret (E0, (C, s, mem, Kassign1 e1 k, e2))
  | E_call C' P e =>
    ret (E0, (C, s, mem, Kcall C' P k, e))
  (* evaluating current continuation *)
  | E_val v =>
    match k with
    | Kbinop1 b_op e2 k' =>
      ret (E0, (C, s, mem, Kbinop2 b_op v k', e2))
    | Kbinop2 b_op v1 k' =>
      ret (E0, (C, s, mem, k', E_val (eval_binop b_op v1 v)))
    | Kseq e2 k' =>
      ret (E0, (C, s, mem, k', e2))
    | Kif e2 e3 k' =>
      match v with
      | Int 0 => ret (E0, (C, s, mem, k', e3))
      | Int i => ret (E0, (C, s, mem, k', e2))
      | _ => None
      end
    | Kalloc k' =>
      match v with
      | Int size =>
        if (size >? 0) % Z then
          do (mem',ptr) <- Memory.alloc mem C (Z.to_nat size);
          ret (E0, (C, s, mem', k', E_val (Ptr ptr)))
        else
          None
      | _ => None
      end
    | Kderef k' =>
      match v with
      | Ptr (C',b',o') =>
        if C == C' then
          do v <- Memory.load mem (C',b',o');
          ret (E0, (C, s, mem, k', E_val v))
        else
          None
      | _ => None
      end
    | Kassign1 e1 k' =>
      ret (E0, (C, s, mem, Kassign2 v k', e1))
    | Kassign2 v' k' =>
      match v with
      | Ptr (C',b',o') =>
        if C == C' then
          do mem' <- Memory.store mem (C',b',o') v';
          ret (E0, (C, s, mem', k', E_val v'))
        else
          None
      | _ => None
      end
    | Kcall C' P k' =>
      match v with
      | Int i =>
        if C == C' then
          (* retrieve the procedure code *)
          do P_expr <- find_procedure (genv_procedures G) C' P;
          (* save the old call argument *)
          do b <- getm (genv_buffers G) C;
          do old_call_arg <- Memory.load mem (C, b, 0%Z);
          (* place the call argument in the target memory *)
          do b' <- getm (genv_buffers G) C';
          do mem' <- Memory.store mem (C', b', 0%Z) (Int i);
          ret (E0, (C', (C, old_call_arg, k') :: s, mem', Kstop, P_expr))
        else if imported_procedure_b (genv_interface G) C C' P then
          (* retrieve the procedure code *)
          do P_expr <- find_procedure (genv_procedures G) C' P;
          (* save the old call argument *)
          do b <- getm (genv_buffers G) C;
          do old_call_arg <- Memory.load mem (C, b, 0%Z);
          (* place the call argument in the target memory *)
          do b' <- getm (genv_buffers G) C';
          do mem' <- Memory.store mem (C', b', 0%Z) (Int i);
          ret ([ECall C P i C'], (C', (C, old_call_arg, k') :: s, mem', Kstop, P_expr))
        else
          None
      | _ => None
      end
    | Kstop =>
      match v, s with
      | Int i, (C',old_call_arg,k') :: s' =>
        (* restore the old call argument *)
        do b <- getm (genv_buffers G) C';
        do mem' <- Memory.store mem (C', b, 0%Z) old_call_arg;
        let t := if C == C' then E0 else [ERet C i C'] in
        ret (t, (C', s', mem', k', E_val (Int i)))
      | _, _ => None
      end
    end
  | _ => None
  end.

Hint Unfold eval_kstep.

Fixpoint execN (n: nat) (G: global_env) (st: state) : option state :=
  match n with
  | O => None
  | S n' =>
    match eval_kstep G st with
    | None => Some st
    | Some (_, st') => execN n' G st'
    end
  end.

Close Scope monad_scope.

(* Semantics Properties *)

Theorem eval_kstep_complete:
  forall G st t st',
    kstep G st t st' -> eval_kstep G st = Some (t, st').
Proof.
  intros G st t st' Hkstep.
  inversion Hkstep; subst; simpl; auto;
    try (unfold Memory.store, Memory.load, Memory.alloc in *;
         repeat simplify_nat_equalities;
         repeat simplify_option;
         reflexivity).
  (* if expressions *)
  - destruct i eqn:Hi;
      try contradiction; auto.
  - assert (Hsize: (size >? 0) % Z = true). {
      destruct size; try inversion H; auto.
    }
    rewrite Hsize.
    rewrite H0. reflexivity.
  (* external calls *)
  - move/eqP/negbTE: H => ->.
    apply imported_procedure_iff in H0.
    rewrite H0 H1 H2 H3 H4 H5.
    reflexivity.
  (* internal calls *)
  - rewrite H0.
    unfold Memory.store in *. simpl in *.
    destruct (mem C'); try discriminate.
    destruct (ComponentMemory.store t b 0%Z old_call_arg); try discriminate.
    rewrite eqxx.
    inversion H1. subst.
    reflexivity.
  (* external return *)
  - rewrite H0.
    unfold Memory.store in *. simpl in *.
    destruct (mem C'); try discriminate.
    destruct (ComponentMemory.store t b 0%Z old_call_arg); try discriminate.
    move/eqP/negbTE: H => ->.
    inversion H1; subst.
    reflexivity.
Qed.

Theorem eval_kstep_sound:
  forall G st t st',
    eval_kstep G st = Some (t, st') -> kstep G st t st'.
Proof.
  intros.
  unfold_states.
  match goal with
  | H: eval_kstep _ _ = Some _ |- kstep _ (_, _, _, _, ?E) _ (_, _, _, _, _) =>
    destruct E; simpl in H;
      try discriminate;
      try (repeat simplify_option;
           econstructor; eauto;
           repeat simplify_nat_equalities;
           reflexivity)
  end.
  - repeat simplify_option.
    + case: (_ =P _) => [->|?]; econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
      * pose proof (Zgt_pos_0 p). omega.
    + econstructor; eauto.
      * pose proof (Zlt_neg_0 p). omega.
    + econstructor; eauto.
      * apply Zgt_is_gt_bool. assumption.
    + by econstructor; eauto; apply/eqP.
    + econstructor; eauto.
    + by econstructor; eauto; apply/eqP.
    + econstructor; eauto; exact/eqP.
    + econstructor; eauto; first exact/eqP/negbT.
      apply imported_procedure_iff. assumption.
Qed.

Theorem eval_kstep_correct:
  forall G st t st',
    eval_kstep G st = Some (t, st') <-> kstep G st t st'.
Proof.
  split.
  apply eval_kstep_sound.
  apply eval_kstep_complete.
Qed.

Corollary kstep_deterministic:
  forall G st t st1 st2,
    kstep G st t st1 -> kstep G st t st2 -> st1 = st2.
Proof.
  intros G st t st1 st2 Hkstep1 Hkstep2.
  apply eval_kstep_correct in Hkstep1.
  apply eval_kstep_correct in Hkstep2.
  rewrite Hkstep1 in Hkstep2.
  inversion Hkstep2.
  reflexivity.
Qed.

Section Semantics.
  Variable p: program.

  Hypothesis valid_program:
    well_formed_program p.

  Hypothesis complete_program:
    closed_program p.

  Let G := prepare_global_env p.

  Definition sem :=
    @Semantics_gen state global_env kstep (initial_state p) final_state G.

  Lemma receptiveness_step:
    forall s t1 s1 t2,
      kstep G s t1 s1 -> match_traces t1 t2 ->
      exists s2, kstep G s t2 s2.
  Proof.
    intros s t1 s1 t2.
    intros Hkstep Hmatch_traces.
    inversion Hkstep; subst;
    inversion Hmatch_traces; subst;
      try (eexists; apply Hkstep).
  Qed.

  Lemma singleton_traces:
    single_events sem.
  Proof.
    unfold single_events.
    intros s t s' Hstep.
    inversion Hstep; subst; simpl; auto.
  Qed.

  Theorem receptiveness:
    receptive sem.
  Proof.
    constructor.
    - apply receptiveness_step.
    - apply singleton_traces.
  Qed.

  Fixpoint unstutter (T : eqType) (x : T) (s : seq T) :=
    if s is x' :: s' then
      if x == x' then unstutter x s'
      else x' :: unstutter x' s'
    else [::].

  Definition stack_state_of (cs: state) : stack_state :=
    let '(curr, stk, _, _, _) := cs in
    StackState curr (unstutter curr (map (fun '(id, _, _) => id) stk)).

  Lemma trace_wb t cs cs' :
    Star sem cs t cs' ->
    well_bracketed_trace (stack_state_of cs) t.
  Proof.
    elim: cs t cs' / => //= s1 t1 s2 t2 s3 t Hstep Hstar IH -> {t}.
    case: s1 t1 s2 / Hstep Hstar IH=> //=.
    - (* Internal Return *)
      by move=> C stk mem mem' k _ P v P_expr b b' old <-; rewrite eqxx.
    - (* External Return *)
      move=> C stk mem mem' k C' P v P_expr b b' old.
      by rewrite eq_sym eqxx=> /eqP/negbTE -> /=.
    - (* Internal Call *)
      by move=> C stk mem mem' k v _ old b <-; rewrite eqxx.
    - (* External Call *)
      by move=> C stk mem mem' k v C' old b /eqP/negbTE ->; rewrite !eqxx.
  Qed.

  Lemma events_wf st t st' :
    Star sem st t st' ->
    All (well_formed_event (prog_interface p)) t.
  Proof.
  elim: st t st' / => // st1 t1 st2 t2 st3 t /= Hstep Hstar IH -> {t}.
  by rewrite All_cat; split=> // {IH Hstar t2 st3}; case: st1 t1 st2 / Hstep.
  Qed.

  Lemma trace_wf mainP t cs cs' :
    Star sem cs t cs' ->
    initial_state p cs ->
    prog_main p = Some mainP ->
    well_formed_program p ->
    well_formed_trace (prog_interface p) t.
  Proof.
    move=> Hstar Hinitial Hmain Hwf; rewrite /well_formed_trace.
    split; last by apply: events_wf; eauto.
    suffices <- : stack_state_of cs = StackState Component.main [].
      by apply: trace_wb; eauto.
    by move: Hinitial; rewrite /initial_state /initial_machine_state Hmain => ->.
  Qed.

  (* Several alternative formulations are possible. One may include the ERet event
     in the star, express the inclusion of ECall in the trace via In, etc. *)
  Lemma eret_from_initial_star_goes_after_ecall_cs s0 t s1 s2 C' v C :
    CS.initial_state p s0 ->
    Star sem s0 t s1 ->
    Step sem s1 [:: ERet C' v C] s2 ->
    exists t1 s s' t2 P v',
      Star sem s0 t1 s /\
      Step sem s [ECall C P v' C'] s' /\
      Star sem s' t2 s1 /\
      t = t1 ** [ECall C P v' C'] ** t2.
  Proof.
    move=> Hinitial Hstar Hstep.
    have {Hstep} /trace_wb : Star sem s0 (t ++ [:: ERet C' v C]) s2.
      apply: star_trans; eauto; exact: star_one.
    have -> : stack_state_of s0 = stack_state0.
      by rewrite Hinitial /= /CS.initial_machine_state /=; case: prog_main.
    case/well_bracketed_trace_inv=> t1 [P [arg [t2 e]]].
    move: Hstar; rewrite {}e -[seq.cat]/Eapp.
    (* AAA: Could maybe combine these two inversion lemmas into a single one. *)
    case/(star_app_inv singleton_traces)=> s1' [Hstar0].
    case/(star_cons_inv singleton_traces)=> s2' [s3' [Hstar1 [Hstep2 Hstar3]]].
    exists t1, s2', s3', t2, P, arg; repeat split=> //.
    by rewrite -[t1]E0_right; apply: star_trans; eauto.
  Qed.

End Semantics.

End CS.
