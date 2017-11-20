Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Lib.Tactics.
Require Import Lib.Monads.

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

Ltac unfold_state :=
  match goal with
  | H: state |- _ =>
    let C := fresh "C" in
    let s := fresh "s" in
    let mem := fresh "mem" in
    let k := fresh "k" in
    let e := fresh "e" in
    destruct H as [[[[C s] mem] k] e]
  end.

Inductive state_eq : state -> state -> Prop :=
| state_eq_intro: forall C1 s1 mem1 k1 e1 C2 s2 mem2 k2 e2,
    C1 = C2 ->
    s1 = s2 ->
    PMap.Equal mem1 mem2 ->
    k1 = k2 ->
    e1 = e2 ->
    state_eq (C1, s1, mem1, k1, e1) (C2, s2, mem2, k2, e2).

Lemma state_eq_refl:
  forall s,
    state_eq s s.
Proof.
  intros s.
  unfold_state.
  constructor; reflexivity.
Qed.

Lemma state_eq_sym:
  forall s1 s2,
    state_eq s1 s2 -> state_eq s2 s1.
Proof.
  intros s1 s2 H.
  inversion H; subst.
  constructor;
    try reflexivity;
    try symmetry; assumption.
Qed.

Lemma state_eq_trans:
  forall s1 s2 s3,
    state_eq s1 s2 -> state_eq s2 s3 -> state_eq s1 s3.
Proof.
  intros s1 s2 s3 H1 H2.
  inversion H1; subst; inversion H2; subst;
    constructor;
    try reflexivity;
    try etransitivity; eauto.
Qed.

Add Parametric Relation: (state) (state_eq)
    reflexivity proved by (state_eq_refl)
    symmetry proved by (state_eq_sym)
    transitivity proved by (state_eq_trans)
      as state_eq_rel.

Instance state_turn : HasTurn state := {
  turn_of s iface :=
    let '(C, _, _, _, _) := s in
    PMap.In C iface
}.

(* transition system *)

Definition initial_state (p: program) (st: state) : Prop :=
  let '(C, s, mem, k, e) := st in

  (* the executing component is the main one *)
  C = fst (prog_main p) /\

  (* the stack is empty *)
  s = [] /\

  (* mem exactly contains all components memories and it comes from the init routine *)
  (forall C, PMap.In C (prog_interface p) <-> PMap.In C mem) /\
  (let '(_, m) := init_all p in mem = m) /\

  (* the expression under evaluation is the main procedure *)
  (exists main_procs,
      PMap.find (fst (prog_main p)) (prog_procedures p) = Some main_procs /\
      PMap.find (snd (prog_main p)) main_procs = Some e) /\

  (* the continuation is stop *)
  k = Kstop.

Definition final_state (st: state) : Prop :=
  let '(C, s, mem, k, e) := st in
  e = E_exit \/ (exists v, e = E_val v /\ k = Kstop /\ s = []).

Inductive kstep (G: global_env) : state -> trace -> state -> Prop :=
| KS_Binop1 : forall C s mem k op e1 e2,
    let t := E0 in
    kstep G (C, s, mem, k, E_binop op e1 e2)
          t (C, s, mem, Kbinop1 op e2 k, e1)
| KS_Binop2 : forall C s mem k op v1 e2,
    let t := E0 in
    kstep G (C, s, mem, Kbinop1 op e2 k, E_val v1)
          t (C, s, mem, Kbinop2 op v1 k, e2)
| KS_BinopEval : forall C s mem k op v1 v2,
    let t := E0 in
    kstep G (C, s, mem, Kbinop2 op v1 k, E_val v2)
          t (C, s, mem, k, E_val (eval_binop op v1 v2))
| KS_Seq1 :  forall C s mem k e1 e2,
    let t := E0 in
    kstep G (C, s, mem, k, E_seq e1 e2)
          t (C, s, mem, Kseq e2 k, e1)
| KS_Seq2 : forall C s mem k v e2,
    let t := E0 in
    kstep G (C, s, mem, Kseq e2 k, E_val v)
          t (C, s, mem, k, e2)
| KS_If : forall C s mem k e1 e2 e3,
    let t := E0 in
    kstep G (C, s, mem, k, E_if e1 e2 e3)
          t (C, s, mem, Kif e2 e3 k, e1)
| KS_IfTrue : forall C s mem k e2 e3 i,
    i <> 0 ->
    let t := E0 in
    kstep G (C, s, mem, Kif e2 e3 k, E_val (Int i))
          t (C, s, mem, k, e2)
| KS_IfFalse : forall C s mem k e2 e3,
    let t := E0 in
    kstep G (C, s, mem, Kif e2 e3 k, E_val (Int 0))
          t (C, s, mem, k, e3)
| KS_LocalBuffer : forall C s mem k b,
    PMap.find C (genv_buffers G) = Some b ->
    let t := E0 in
    kstep G (C, s, mem, k, E_local)
          t (C, s, mem, k, E_val (Ptr (C,b,0)))
| KS_Alloc1 : forall C s mem k e,
    let t := E0 in
    kstep G (C, s, mem, k, E_alloc e)
          t (C, s, mem, Kalloc k, e)
| KS_AllocEval : forall C s mem mem' k size ptr,
    (size >= 0) ->
    Memory.alloc mem C (Z.to_nat size) = Some (mem', ptr) ->
    let t := E0 in
    kstep G (C, s, mem, Kalloc k, E_val (Int size))
          t (C, s, mem', k, E_val (Ptr ptr))
| KS_Deref1 : forall C s mem k e,
    let t := E0 in
    kstep G (C, s, mem, k, E_deref e)
          t (C, s, mem, Kderef k, e)
| KS_DerefEval : forall C s mem k C' b' o' v,
    C = C' ->
    Memory.load mem (C',b',o') = Some v ->
    let t := E0 in
    kstep G (C, s, mem, Kderef k, E_val (Ptr (C',b',o')))
          t (C, s, mem, k, E_val v)
| KS_Assign1 : forall C s mem k e1 e2,
    let t := E0 in
    kstep G (C, s, mem, k, E_assign e1 e2)
          t (C, s, mem, Kassign1 e1 k, e2)
| KS_Assign2 : forall C s mem k v e1,
    let t := E0 in
    kstep G (C, s, mem, Kassign1 e1 k, E_val v)
          t (C, s, mem, Kassign2 v k, e1)
| KS_AssignEval : forall C s mem mem' k v C' b' o',
    C = C' ->
    Memory.store mem (C',b',o') v = Some mem' ->
    let t := E0 in
    kstep G (C, s, mem, Kassign2 v k, E_val (Ptr (C',b',o')))
          t (C, s, mem', k, E_val v)
| KS_Call1 : forall C s mem k C' P e,
    imported_procedure (genv_interface G) C C' P \/ C = C' ->
    let t := E0 in
    kstep G (C, s, mem, k, E_call C' P e)
          t (C, s, mem, Kcall C' P k, e)
| KS_Call2 : forall C s mem mem' k C' P v C'_procs P_expr b b' old_call_arg,
    (* retrieve the procedure code *)
    PMap.find C' (genv_procedures G) = Some C'_procs ->
    PMap.find P C'_procs = Some P_expr ->
    (* save the old call argument *)
    PMap.find C (genv_buffers G) = Some b ->
    Memory.load mem (C,b,0) = Some old_call_arg ->
    (* place the call argument in the target memory *)
    PMap.find C' (genv_buffers G) = Some b' ->
    Memory.store mem (C',b',0) (Int v) = Some mem' ->
    let t := if Pos.eqb C C' then E0 else [ECall C P v C'] in
    kstep G (C, s, mem, Kcall C' P k, E_val (Int v))
          t (C', (C, old_call_arg, k) :: s, mem', Kstop, P_expr)
| KS_CallRet : forall C s mem mem' k v C' old_call_arg b,
    (* restore the old call argument *)
    PMap.find C' (genv_buffers G) = Some b ->
    Memory.store mem (C', b, 0) old_call_arg = Some mem' ->
    let t := if Pos.eqb C C' then E0 else [ERet C v C'] in
    kstep G (C, (C', old_call_arg, k) :: s, mem, Kstop, E_val (Int v))
          t (C', s, mem', k, E_val (Int v)).

(* functional kstep *)

Import MonadNotations.
Open Scope monad_scope.

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
    do b <- PMap.find C (genv_buffers G);
    ret (E0, (C, s, mem, k, E_val (Ptr (C,b,0))))
  | E_alloc e =>
    ret (E0, (C, s, mem, Kalloc k, e))
  | E_deref e =>
    ret (E0, (C, s, mem, Kderef k, e))
  | E_assign e1 e2 =>
    ret (E0, (C, s, mem, Kassign1 e1 k, e2))
  | E_call C' P e =>
    if (imported_procedure_b (genv_interface G) C C' P) || (Pos.eqb C C') then
      ret (E0, (C, s, mem, Kcall C' P k, e))
    else
      None
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
        if (size >=? 0) then
          do (mem',ptr) <- Memory.alloc mem C (Z.to_nat size);
          ret (E0, (C, s, mem', k', E_val (Ptr ptr)))
        else
          None
      | _ => None
      end
    | Kderef k' =>
      match v with
      | Ptr (C',b',o') =>
        if Pos.eqb C C' then
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
        if Pos.eqb C C' then
          do mem' <- Memory.store mem (C',b',o') v';
          ret (E0, (C, s, mem', k', E_val v'))
        else
          None
      | _ => None
      end
    | Kcall C' P k' =>
      match v with
      | Int i =>
        (* retrieve the procedure code *)
        do C'_procs <- PMap.find C' (genv_procedures G);
        do P_expr <- PMap.find P C'_procs;
        (* save the old call argument *)
        do b <- PMap.find C (genv_buffers G);
        do old_call_arg <- Memory.load mem (C,b,0);
        (* place the call argument in the target memory *)
        do b' <- PMap.find C' (genv_buffers G);
        do mem' <- Memory.store mem (C',b',0) (Int i);
        let t := if Pos.eqb C C' then E0 else [ECall C P i C'] in
        ret (t, (C', (C, old_call_arg, k') :: s, mem', Kstop, P_expr))
      | _ => None
      end
    | Kstop =>
      match v, s with
      | Int i, (C',old_call_arg,k') :: s' =>
        (* restore the old call argument *)
        do b <- PMap.find C' (genv_buffers G);
        do mem' <- Memory.store mem (C',b,0) old_call_arg;
        let t := if Pos.eqb C C' then E0 else [ERet C i C'] in
        ret (t, (C', s', mem', k', E_val (Int i)))
      | _, _ => None
      end
    end
  | _ => None
  end.

Hint Unfold eval_kstep.

Definition init (p: program) (input: value) : option (global_env * state) :=
  do procs <- PMap.find (fst (prog_main p)) (prog_procedures p);
  do main <- PMap.find (snd (prog_main p)) procs;
  let '(bufs, mem) := init_all p in
  let G := {| genv_interface := prog_interface p;
              genv_procedures := prog_procedures p;
              genv_buffers := bufs |} in
  do local_buf <- PMap.find (fst (prog_main p)) bufs;
  do mem' <- Memory.store mem (fst (prog_main p), local_buf, 0) input;
  ret (G, (fst (prog_main p), [], mem', Kstop, main)).

Fixpoint execN (n: nat) (G: global_env) (st: state) : option state :=
  match n with
  | O => None
  | S n' =>
    match eval_kstep G st with
    | None => Some st
    | Some (_, st') => execN n' G st'
    end
  end.

Definition run (p: program) (input: value) (fuel: nat) : option state :=
  do (G, st) <- init p input;
  execN fuel G st.

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
  - assert (Hsize: (size >=? 0) = true). { destruct size; auto. }
    rewrite Hsize.
    rewrite H0. reflexivity.
  - rewrite Pos.eqb_refl.
    repeat simplify_option.
    + unfold Memory.load in *. rewrite Heqo0, H1 in H0. inversion H0.
      reflexivity.
    + unfold Memory.load in *. rewrite Heqo in H0. discriminate.
  - rewrite Pos.eqb_refl.
    repeat simplify_option.
    + unfold Memory.store in *. rewrite Heqo0, Heqo in H0. inversion H0.
      reflexivity.
    + unfold Memory.store in *. rewrite Heqo in H0. discriminate.
  (* calls/returns *)
  - destruct H; subst.
    + unfold orb.
      destruct (imported_procedure_iff (genv_interface G) C C' P) as [H1 H2];
        rewrite H1; auto.
    + rewrite Pos.eqb_refl.
      rewrite orb_true_r.
      reflexivity.
Qed.

Theorem eval_kstep_sound:
  forall G st t st',
    eval_kstep G st = Some (t, st') -> kstep G st t st'.
Proof.
  intros.
  repeat unfold_state.
  match goal with
  | H: eval_kstep _ _ = Some _ |- kstep _ (_, _, _, _, ?E) _ (_, _, _, _, _) =>
    destruct E; simpl in H;
      try discriminate;
      try (repeat simplify_option;
           econstructor; eauto;
           repeat rewrite_memory_operations;
           repeat simplify_nat_equalities;
           reflexivity)
  end.
  - repeat simplify_option.
    + econstructor. eauto.
      unfold Memory.store.
      rewrite Heqo1, Heqo0.
      reflexivity.
    + econstructor.
    + econstructor.
    + econstructor.
    + econstructor.
    + econstructor.
      pose proof (Zgt_pos_0 p). omega.
    + econstructor.
      pose proof (Zlt_neg_0 p). omega.
    + econstructor.
      destruct z; auto.
      * omega.
      * pose proof (Zgt_pos_0 p). omega.
      * unfold Z.geb in Heqb. simpl in Heqb. discriminate.
      * auto.
    + econstructor; eauto.
      * apply Pos.eqb_eq; auto.
      * unfold Memory.load.
        rewrite Heqo1.
        eauto.
    + econstructor.
    + econstructor; eauto.
      * rewrite <- Pos.eqb_eq. auto.
      * unfold Memory.store.
        rewrite Heqo1. rewrite Heqo0.
        reflexivity.
    + econstructor; eauto.
      * unfold Memory.load.
        rewrite Heqo6. auto.
      * unfold Memory.store.
        rewrite Heqo5, Heqo4.
        auto.
  (* procedure call *)
  - repeat simplify_option.
    rewrite orb_true_iff in Heqb.
    rewrite Pos.eqb_eq in Heqb.
    econstructor.
    destruct Heqb; auto.
    left. apply imported_procedure_iff; auto.
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

  Let G := init_genv p.

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
    - eexists. rewrite <- H6 in Hkstep. apply Hkstep.
    - eexists. rewrite <- H6 in Hkstep. apply Hkstep.
    - eexists. rewrite <- H6 in Hkstep. apply Hkstep.
    - eexists. rewrite <- H2 in Hkstep. apply Hkstep.
    - eexists. rewrite <- H2 in Hkstep. apply Hkstep.
    - eexists. rewrite <- H2 in Hkstep. apply Hkstep.
  Qed.

  Lemma singleton_traces:
    single_events sem.
  Proof.
    unfold single_events.
    intros s t s' Hstep.
    inversion Hstep; subst t0; simpl; auto;
      try (destruct (Pos.eqb C C'); subst; simpl; auto).
  Qed.

  Theorem receptiveness:
    receptive sem.
  Proof.
    constructor.
    - apply receptiveness_step.
    - apply singleton_traces.
  Qed.
End Semantics.
End CS.