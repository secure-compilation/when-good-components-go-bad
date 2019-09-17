Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.CompCertExtensions.
Require Import Common.Traces.
Require Import Common.Blame.
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

Record frame : Type := Frame {
  f_component : Component.id;
  f_arg       : value;
  f_cont      : cont
}.

Definition stack : Type := list frame.

Record state : Type := State {
  s_component : Component.id;
  s_stack     : stack;
  s_memory    : Memory.t;
  s_cont      : cont;
  s_expr      : expr;
  s_arg       : value
}.

Notation "[ 'State' C , stk , mem , k , e , arg ]" :=
  (State C stk mem k e arg)
  (at level 0, format "[ 'State'  C ,  stk ,  mem ,  k ,  e ,  arg ]").

Ltac unfold_state st :=
  let C := fresh "C" in
  let s := fresh "s" in
  let mem := fresh "mem" in
  let k := fresh "k" in
  let e := fresh "e" in
  let arg := fresh "arg" in
  destruct st as [C s mem k e arg].

Ltac unfold_states :=
  repeat (match goal with
          | st: state |- _ => unfold_state st
          end).

Import MonadNotations.
Open Scope monad_scope.

Definition initial_machine_state (p: program) : state :=
  match prog_main p with
  | Some main_expr => State Component.main [::] (prepare_buffers p) Kstop main_expr (Int 0)
  | None =>
    (* this case shouldn't happen for a well formed p *)
    State Component.main [::] emptym Kstop E_exit (Int 0)
  end.

(* transition system *)

Definition initial_state (p: program) (st: state) : Prop :=
  st = initial_machine_state p.

Definition final_state (st: state) : Prop :=
  let: State C s mem k e arg := st in
  e = E_exit \/ (exists v, e = E_val v /\ k = Kstop /\ s = []).

Inductive kstep (G: global_env) : state -> trace -> state -> Prop :=
| KS_Binop1 : forall C s mem k op e1 e2 arg,
    kstep G [State C, s, mem, k, E_binop op e1 e2, arg] E0
            [State C, s, mem, Kbinop1 op e2 k, e1, arg]
| KS_Binop2 : forall C s mem k op v1 e2 arg,
    kstep G [State C, s, mem, Kbinop1 op e2 k, E_val v1, arg] E0
            [State C, s, mem, Kbinop2 op v1 k, e2, arg]
| KS_BinopEval : forall C s mem k op v1 v2 arg,
    kstep G [State C, s, mem, Kbinop2 op v1 k, E_val v2, arg] E0
            [State C, s, mem, k, E_val (eval_binop op v1 v2), arg]
| KS_Seq1 :  forall C s mem k e1 e2 arg,
    kstep G [State C, s, mem, k, E_seq e1 e2, arg] E0
            [State C, s, mem, Kseq e2 k, e1, arg]
| KS_Seq2 : forall C s mem k v e2 arg,
    kstep G [State C, s, mem, Kseq e2 k, E_val v, arg] E0
            [State C, s, mem, k, e2, arg]
| KS_If1 : forall C s mem k e1 e2 e3 arg,
    kstep G [State C, s, mem, k, E_if e1 e2 e3, arg] E0
            [State C, s, mem, Kif e2 e3 k, e1, arg]
| KS_If2 : forall C s mem k e2 e3 i arg,
    kstep G [State C, s, mem, Kif e2 e3 k, E_val (Int i), arg] E0
            [State C, s, mem, k, if i != 0%Z then e2 else e3, arg]
| KS_Arg : forall C s mem k i,
    kstep G [State C, s, mem, k, E_arg, Int i] E0
            [State C, s, mem, k, E_val (Int i), Int i]
| KS_LocalBuffer : forall C s mem k arg,
    kstep G [State C, s, mem, k, E_local, arg] E0
            [State C, s, mem, k, E_val (Ptr (C,Block.local,0%Z)), arg]
| KS_Alloc1 : forall C s mem k e arg,
    kstep G [State C, s, mem, k, E_alloc e, arg] E0
            [State C, s, mem, Kalloc k, e, arg]
| KS_AllocEval : forall C s mem mem' k size ptr arg,
    (size > 0) % Z ->
    Memory.alloc mem C (Z.to_nat size) = Some (mem', ptr) ->
    kstep G [State C, s, mem, Kalloc k, E_val (Int size), arg] E0
            [State C, s, mem', k, E_val (Ptr ptr), arg]
| KS_Deref1 : forall C s mem k e arg,
    kstep G [State C, s, mem, k, E_deref e, arg] E0
            [State C, s, mem, Kderef k, e, arg]
| KS_DerefEval : forall C s mem k C' b' o' v arg,
    C = C' ->
    Memory.load mem (C',b',o') = Some v ->
    kstep G [State C, s, mem, Kderef k, E_val (Ptr (C',b',o')), arg] E0
            [State C, s, mem, k, E_val v, arg]
| KS_Assign1 : forall C s mem k e1 e2 arg,
    kstep G [State C, s, mem, k, E_assign e1 e2, arg] E0
            [State C, s, mem, Kassign1 e1 k, e2, arg]
| KS_Assign2 : forall C s mem k v e1 arg,
    kstep G [State C, s, mem, Kassign1 e1 k, E_val v, arg] E0
            [State C, s, mem, Kassign2 v k, e1, arg]
| KS_AssignEval : forall C s mem mem' k v C' b' o' arg,
    C = C' ->
    Memory.store mem (C', b', o') v = Some mem' ->
    kstep G [State C, s, mem, Kassign2 v k, E_val (Ptr (C', b', o')), arg] E0
            [State C, s, mem', k, E_val v, arg]
| KS_InitCall : forall C s mem k C' P e arg,
    kstep G [State C, s, mem, k, E_call C' P e, arg] E0
            [State C, s, mem, Kcall C' P k, e, arg]
| KS_InternalCall : forall C s mem k C' P v P_expr old_call_arg,
    C = C' ->
    (* retrieve the procedure code *)
    find_procedure (genv_procedures G) C' P = Some P_expr ->
    kstep G [State C, s, mem, Kcall C' P k, E_val (Int v), old_call_arg] E0
            [State C', Frame C old_call_arg k :: s, mem, Kstop, P_expr, Int v]
| KS_ExternalCall : forall C s mem k C' P v P_expr old_call_arg,
    C <> C' ->
    (* check permission *)
    imported_procedure (genv_interface G) C C' P  ->
    (* retrieve the procedure code *)
    find_procedure (genv_procedures G) C' P = Some P_expr ->
    kstep G [State C, s, mem, Kcall C' P k, E_val (Int v), old_call_arg]
            [:: ECall C P v C']
            [State C', Frame C old_call_arg k :: s, mem, Kstop, P_expr, Int v]
| KS_InternalReturn: forall C s mem k v arg C' old_call_arg,
    C = C' ->
    kstep G [State C, Frame C' old_call_arg k :: s, mem, Kstop, E_val (Int v), arg] E0
            [State C', s, mem, k, E_val (Int v), old_call_arg]
| KS_ExternalReturn: forall C s mem k v arg C' old_call_arg,
    C <> C' ->
    kstep G [State C, Frame C' old_call_arg k :: s, mem, Kstop, E_val (Int v), arg]
            [:: ERet C v C']
            [State C', s, mem, k, E_val (Int v), old_call_arg].

Lemma kstep_component G s t s' :
  kstep G s t s' ->
  s_component s' =
  if t is e :: _ then next_comp_of_event e
  else s_component s.
Proof. by case: s t s' /. Qed.

Lemma final_state_stuck G (st: state) :
  final_state st ->
  forall t st', ~ kstep G st t st'.
Proof.
move=> Hfinal t st' Hstep.
case: st t st' / Hstep Hfinal => //= *;
by repeat match goal with
| H : _ \/ _ |- _ => case: H=> ?
| H : exists _, _ |- _ => case: H => ??
| H : _ /\ _ |- _ => case: H => ??
end.
Qed.

(* functional kstep *)

Definition eval_kstep (G : global_env) (st : state) : option (trace * state) :=
  let: State C s mem k e arg := st in
  match e with
  (* pushing a new continuation *)
  | E_binop b_op e1 e2 =>
    ret (E0, [State C, s, mem, Kbinop1 b_op e2 k, e1, arg])
  | E_seq e1 e2 =>
    ret (E0, [State C, s, mem, Kseq e2 k, e1, arg])
  | E_if e1 e2 e3 =>
    ret (E0, [State C, s, mem, Kif e2 e3 k, e1, arg])
  | E_arg =>
    if arg is Int v then
      ret (E0, [State C, s, mem, k, E_val (Int v), arg])
    else None
  | E_local =>
    ret (E0, [State C, s, mem, k, E_val (Ptr (C, Block.local, 0%Z)), arg])
  | E_alloc e =>
    ret (E0, [State C, s, mem, Kalloc k, e, arg])
  | E_deref e =>
    ret (E0, [State C, s, mem, Kderef k, e, arg])
  | E_assign e1 e2 =>
    ret (E0, [State C, s, mem, Kassign1 e1 k, e2, arg])
  | E_call C' P e =>
    ret (E0, [State C, s, mem, Kcall C' P k, e, arg])
  (* evaluating current continuation *)
  | E_val v =>
    match k with
    | Kbinop1 b_op e2 k' =>
      ret (E0, [State C, s, mem, Kbinop2 b_op v k', e2, arg])
    | Kbinop2 b_op v1 k' =>
      ret (E0, [State C, s, mem, k', E_val (eval_binop b_op v1 v), arg])
    | Kseq e2 k' =>
      ret (E0, [State C, s, mem, k', e2, arg])
    | Kif e2 e3 k' =>
      match v with
      | Int z => ret (E0, [State C, s, mem, k', if z != 0%Z then e2 else e3, arg])
      | _ => None
      end
    | Kalloc k' =>
      match v with
      | Int size =>
        if (size >? 0) % Z then
          do (mem',ptr) <- Memory.alloc mem C (Z.to_nat size);
          ret (E0, [State C, s, mem', k', E_val (Ptr ptr), arg])
        else
          None
      | _ => None
      end
    | Kderef k' =>
      match v with
      | Ptr (C',b',o') =>
        if C == C' then
          do v <- Memory.load mem (C',b',o');
          ret (E0, [State C, s, mem, k', E_val v, arg])
        else
          None
      | _ => None
      end
    | Kassign1 e1 k' =>
      ret (E0, [State C, s, mem, Kassign2 v k', e1, arg])
    | Kassign2 v' k' =>
      match v with
      | Ptr (C',b',o') =>
        if C == C' then
          do mem' <- Memory.store mem (C',b',o') v';
          ret (E0, [State C, s, mem', k', E_val v', arg])
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
          ret (E0, [State C', Frame C arg k' :: s, mem, Kstop, P_expr, Int i])
        else if imported_procedure_b (genv_interface G) C C' P then
          (* retrieve the procedure code *)
          do P_expr <- find_procedure (genv_procedures G) C' P;
          ret ([ECall C P i C'], [State C', Frame C arg k' :: s, mem, Kstop, P_expr, Int i])
        else
          None
      | _ => None
      end
    | Kstop =>
      match v, s with
      | Int i, Frame C' old_call_arg k' :: s' =>
        let t := if C == C' then E0 else [:: ERet C i C'] in
        ret (t, [State C', s', mem, k', E_val (Int i), old_call_arg])
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
  - assert (Hsize: (size >? 0) % Z = true). {
      destruct size; try inversion H; auto.
    }
    rewrite Hsize.
    rewrite H0. reflexivity.
  (* external calls *)
  - move/eqP/negbTE: H => ->.
    apply imported_procedure_iff in H0.
    rewrite H0 H1.
    reflexivity.
  (* external return *)
  - move/eqP/negbTE: H => ->.
    reflexivity.
Qed.

Theorem eval_kstep_sound:
  forall G st t st',
    eval_kstep G st = Some (t, st') -> kstep G st t st'.
Proof.
  intros.
  unfold_states.
  match goal with
  | H: eval_kstep _ _ = Some _ |- kstep _ [State _, _, _, _, ?E, _] _ [State _, _, _, _, _, _] =>
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
    + destruct z; econstructor; eauto; discriminate.
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

  Local Open Scope fset_scope.

  Definition stack_components (cs: state) : {fset Component.id} :=
    s_component cs |: fset [seq f_component f | f <- s_stack cs].

  Lemma stack_components_step cs t cs' :
    Step sem cs t cs' ->
    fsubset (stack_components cs) (domm (prog_interface p)) ->
    fsubset (stack_components cs') (domm (prog_interface p)).
  Proof.
  case: cs t cs' / => //=.
  - (* Internal Call *)
    move=> C stk mem k _ P v P_expr arg <-; rewrite /stack_components /=.
    by rewrite fset_cons fsetUA fsetUid.
  - (* External Call *)
    move=> C stk mem k C' P v P_expr arg _; rewrite /stack_components /=.
    rewrite (fsubU1set C') mem_domm fset_cons.
    by case/(cprog_closed_interface complete_program)=> CI [->].
  - (* Internal Return *)
    move=> C stk mem k v arg _ old <-; rewrite /stack_components /=.
    by rewrite fset_cons fsetUA fsetUid.
  - (* External Return *)
    move=> C stk mem k v arg C' old _; rewrite /stack_components /=.
    by rewrite (fsubU1set C) fset_cons; case/andP.
  Qed.

  Lemma stack_components_star cs t cs' :
    initial_state p cs ->
    Star sem cs t cs' ->
    fsubset (stack_components cs') (domm (prog_interface p)).
  Proof.
  move=> init star.
  have main_ok : Component.main \in domm (prog_interface p).
    have := cprog_main_existence complete_program.
    rewrite wfprog_defined_procedures // mem_domm /prog_main /find_procedure.
    by case: getm.
  have {init main_ok} cs_ok : fsubset (stack_components cs) (domm (prog_interface p)).
    rewrite init /initial_machine_state /stack_components.
    by case e_main: (prog_main p)=> [mainP|] /=; rewrite -fset0E fsetU0 fsub1set.
  elim: cs t cs' / star cs_ok=> // cs1 t1 cs2 t2 cs3 t step _ IH _ cs1_ok.
  by apply: IH; apply: stack_components_step cs1_ok; eauto.
  Qed.

  Fixpoint unstutter (T : eqType) (x : T) (s : seq T) :=
    if s is x' :: s' then
      if x == x' then unstutter x s'
      else x' :: unstutter x' s'
    else [::].

  Definition stack_state_of (cs: state) : stack_state :=
    let: State curr stk _ _ _ _ := cs in
    StackState curr (unstutter curr (map f_component stk)).

  Lemma star_component s1 t s2 :
    Star sem s1 t s2 ->
    s_component s2 =
    last (s_component s1) [seq next_comp_of_event e | e <- t].
  Proof.
  elim: s1 t s2 / => //= s1 t1 s2 t2 s3 _ Hstep _ -> ->.
  rewrite map_cat last_cat (kstep_component Hstep).
  move/singleton_traces: Hstep.
  by case: t1=> [|e [|e' t1]] //= *; omega.
  Qed.

  Lemma initial_state_exists:
    exists s, initial_state p s.
  Proof.
    unfold initial_state, initial_machine_state;
      by eauto.
  Qed.
End Semantics.

End CS.

Notation "[ 'CState' C , stk , mem , k , e , arg ]" :=
  (CS.State C stk mem k e arg)
  (at level 0, format "[ 'CState'  C ,  stk ,  mem ,  k ,  e ,  arg ]").
