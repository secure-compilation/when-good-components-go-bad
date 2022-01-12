Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.CompCertExtensions.
Require Import Common.Traces.
Require Import Common.RenamingOption.
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
| Kcall (C: Component.id) (P: Procedure.id) (k: cont)
| Kcallptr1 (funptr: expr) (k: cont)
| Kcallptr2 (arg: value) (k: cont)  
.

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

Inductive kstep (G: global_env) : state -> trace event -> state -> Prop :=
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
| KS_Arg : forall C s mem k v,
    kstep G [State C, s, mem, k, E_arg, v] E0
            [State C, s, mem, k, E_val v, v]
| KS_LocalBuffer : forall C s mem k arg,
    kstep G [State C, s, mem, k, E_local, arg] E0
            [State C, s, mem, k, E_val (Ptr (Permission.data,C,Block.local,0%Z)), arg]
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
| KS_DerefEval : forall C s mem k P' C' b' o' v arg,
    (* C = C' -> *)
    Memory.load mem (P',C',b',o') = Some v ->
    kstep G [State C, s, mem, Kderef k, E_val (Ptr (P',C',b',o')), arg] E0
          [State C, s, mem, k, E_val v, arg]
| KS_FunPtr : forall C s mem k P Pexpr arg,
    find_procedure (genv_procedures G) C P = Some Pexpr ->
    kstep G [State C, s, mem, k, E_funptr P, arg] E0
          [State C, s, mem, k, E_val (Ptr (Permission.code, C, P, 0%Z)), arg]
| KS_Assign1 : forall C s mem k e1 e2 arg,
    kstep G [State C, s, mem, k, E_assign e1 e2, arg] E0
            [State C, s, mem, Kassign1 e1 k, e2, arg]
| KS_Assign2 : forall C s mem k v e1 arg,
    kstep G [State C, s, mem, Kassign1 e1 k, E_val v, arg] E0
            [State C, s, mem, Kassign2 v k, e1, arg]
| KS_AssignEval : forall C s mem mem' k v P' C' b' o' arg,
    (* C = C' -> *)
    Memory.store mem (P', C', b', o') v = Some mem' ->
    kstep G [State C, s, mem, Kassign2 v k, E_val (Ptr (P', C', b', o')), arg] E0
          [State C, s, mem', k, E_val v, arg]
| KS_InitCall : forall C s mem k C' P e arg,
    kstep G [State C, s, mem, k, E_call C' P e, arg] E0
          [State C, s, mem, Kcall C' P k, e, arg]
| KS_InitCallPtr1 : forall C s mem k e1 e2 arg,
    kstep G [State C, s, mem, k, E_callptr e1 e2, arg] E0
          [State C, s, mem, Kcallptr1 e1 k, e2, arg]
| KS_InitCallPtr2 : forall C s mem k e1 v arg,
    kstep G [State C, s, mem, Kcallptr1 e1 k, E_val v, arg] E0
          [State C, s, mem, Kcallptr2 v k, e1, arg]
| KS_InitCallPtr3 : forall C s mem k v C' P arg,
    C = C' ->
    kstep G [State C, s, mem, Kcallptr2 v k, E_val (Ptr (Permission.code, C', P, 0%Z)),
             arg] E0
          [State C, s, mem, Kcall C' P k, E_val v, arg]
| KS_InternalCall : forall C s mem k C' P v P_expr old_call_arg,
    C = C' ->
    (* retrieve the procedure code *)
    find_procedure (genv_procedures G) C' P = Some P_expr ->
    kstep G [State C, s, mem, Kcall C' P k, E_val v, old_call_arg] E0
            [State C', Frame C old_call_arg k :: s, mem, Kstop, P_expr, v]
| KS_ExternalCall : forall C s mem k C' P v P_expr old_call_arg,
    C <> C' ->
    (* check permission *)
    imported_procedure (genv_interface G) C C' P  ->
    (* retrieve the procedure code *)
    find_procedure (genv_procedures G) C' P = Some P_expr ->
    kstep G [State C, s, mem, Kcall C' P k, E_val v, old_call_arg]
            [:: ECall C P v mem C']
            [State C', Frame C old_call_arg k :: s, mem, Kstop, P_expr, v]
| KS_InternalReturn: forall C s mem k v arg C' old_call_arg,
    C = C' ->
    kstep G [State C, Frame C' old_call_arg k :: s, mem, Kstop, E_val v, arg] E0
            [State C', s, mem, k, E_val v, old_call_arg]
| KS_ExternalReturn: forall C s mem k v arg C' old_call_arg,
    C <> C' ->
    kstep G [State C, Frame C' old_call_arg k :: s, mem, Kstop, E_val v, arg]
            [:: ERet C v mem C']
            [State C', s, mem, k, E_val v, old_call_arg].

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

Definition eval_kstep (G : global_env) (st : state) : option (trace event * state) :=
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
    (* if arg is Int v then *)
      ret (E0, [State C, s, mem, k, E_val arg(* (Int v) *), arg])
    (* else None *)
  | E_local =>
    ret (E0, [State C, s, mem, k, E_val (Ptr (Permission.data, C, Block.local, 0%Z)), arg])
  | E_alloc e =>
    ret (E0, [State C, s, mem, Kalloc k, e, arg])
  | E_deref e =>
    ret (E0, [State C, s, mem, Kderef k, e, arg])
  | E_funptr P =>
    match find_procedure (genv_procedures G) C P with
    | Some Pexpr => ret (E0, [State C, s, mem, k,
                              E_val (Ptr (Permission.code, C, P, 0%Z)), arg])
    | None => None
    end
  | E_assign e1 e2 =>
    ret (E0, [State C, s, mem, Kassign1 e1 k, e2, arg])
  | E_callptr e1 e2 =>
    ret (E0, [State C, s, mem, Kcallptr1 e1 k, e2, arg])
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
      | Ptr (P',C',b',o') =>
        (* if C == C' then *)
          do v <- Memory.load mem (P',C',b',o');
          ret (E0, [State C, s, mem, k', E_val v, arg])
        (* else *)
        (*   None *)
      | _ => None
      end
    | Kassign1 e1 k' =>
      ret (E0, [State C, s, mem, Kassign2 v k', e1, arg])
    | Kassign2 v' k' =>
      match v with
      | Ptr (P',C',b',o') =>
        (* if C == C' then *)
          do mem' <- Memory.store mem (P',C',b',o') v';
          ret (E0, [State C, s, mem', k', E_val v', arg])
        (* else *)
        (*   None *)
      | _ => None
      end
    | Kcallptr1 efunptr k' =>
      ret (E0, [State C, s, mem, Kcallptr2 v k', efunptr, arg])
    | Kcallptr2 varg k' =>
      match v with
      | Ptr (perm, C', P', 0%Z) =>
        if (Permission.eqb perm Permission.code) && (C' =? C) then
            ret (E0, [State C, s, mem, Kcall C' P' k', E_val varg, arg])
        else None
      | _ => None
      end
    | Kcall C' P k' =>
      (*match v with
      | Int i =>*)
        if C == C' then
          (* retrieve the procedure code *)
          do P_expr <- find_procedure (genv_procedures G) C' P;
          ret (E0, [State C', Frame C arg k' :: s, mem, Kstop, P_expr, v])
        else if imported_procedure_b (genv_interface G) C C' P then
          (* retrieve the procedure code *)
          do P_expr <- find_procedure (genv_procedures G) C' P;
          ret ([ECall C P v mem C'], [State C', Frame C arg k' :: s, mem, Kstop, P_expr, v])
        else
          None
      (*| _ => None
      end*)
    | Kstop =>
      match (*v,*) s with
      | (*Int i,*) Frame C' old_call_arg k' :: s' =>
        let t := if C == C' then E0 else [:: ERet C v mem C'] in
        ret (t, [State C', s', mem, k', E_val v, old_call_arg])
      | (*_,*) _ => None
      end
    end
  | E_exit => None
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
    + destruct (C0 == C) eqn:eC0.
      * assert (C0 = C). by apply/eqP. subst.
        eapply KS_InternalReturn; by auto.
      * econstructor. intros ?. subst. by rewrite eq_refl in eC0.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + destruct z; econstructor; eauto; discriminate.
    + econstructor; eauto.
      * apply Zgt_is_gt_bool. assumption.
    + by econstructor; eauto; apply/eqP.
    + econstructor; eauto.
    + by econstructor; eauto; apply/eqP.
    + econstructor; eauto. by apply/eqP.
    + econstructor; eauto; first exact/eqP/negbT.
      apply imported_procedure_iff. assumption.
    + econstructor; eauto.
    + move: Heqb => /andP.
      intros [Hperm HC].
      assert (i0 = Permission.code). by apply /Permission.eqP. subst.
      assert (i1 = C). by apply beq_nat_true. subst.
      by econstructor.
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
    @Semantics_gen event state global_env kstep (initial_state p) final_state G.

  Lemma receptiveness_step:
    forall s t1 s1 t2,
      kstep G s t1 s1 -> equal_and_nil_or_singleton t1 t2 ->
      exists s2, kstep G s t2 s2.
  Proof.
    intros s t1 s1 t2.
    intros Hkstep Hmatch_traces.
    inversion Hkstep; subst;
    inversion Hmatch_traces; subst;
      try (eexists; apply Hkstep);
      match goal with H: event_equal _ _ |- _ => apply event_equal_equal in H end;
      subst; eexists; exact Hkstep.
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

  Lemma load_component_prog_interface_intitial_state s ptr ptr':
    initial_state p s ->
    Memory.load (s_memory s) ptr = Some (Ptr ptr') ->
    Pointer.component ptr' \in domm (prog_interface p).
  Proof.
    intros Hini Hload.
    unfold initial_state, initial_machine_state in Hini.
    apply cprog_main_existence in complete_program as HisSome.
    destruct (prog_main p) eqn:emain; last discriminate. subst. simpl in *.
    unfold prepare_buffers, Memory.load in *. rewrite mapmE in Hload.
    find_if_inside_hyp Hload; last discriminate.
    destruct ((prog_buffers p (Pointer.component ptr))) as [buf|] eqn:ebuf;
      last discriminate.
    simpl in *. rewrite ComponentMemory.load_prealloc in Hload.
    find_if_inside_hyp Hload; last discriminate.
    destruct (setm emptym 0 buf (Pointer.block ptr)) as [buf'|] eqn:esetm;
      last discriminate.
    destruct buf'; first (find_if_inside_hyp Hload; discriminate).
    apply nth_error_In in Hload.
    rewrite setmE in esetm.
    find_if_inside_hyp esetm; last discriminate. inversion esetm; subst; clear esetm.
    assert (exists x, prog_interface p (Pointer.component ptr) = Some x) as [? H_].
    {
      apply/dommP. rewrite wfprog_defined_buffers; auto. apply/dommP; by eauto.
    }
    assert (H__: prog_interface p (Pointer.component ptr)). by rewrite H_.
    specialize (wfprog_well_formed_buffers valid_program H__) as [? Bwf].
    clear H_ H__. unfold Buffer.well_formed_buffer_opt in *.
    rewrite ebuf in Bwf. simpl in *. move : Bwf => /andP => [[_ Bwf]].
    apply In_in in Hload.
    assert (contra: exists2 x, x \in l & ~~ (fun v : value => ~~ is_ptr v) x).
    { by eauto. }
    move : contra => /allPn => contra. by rewrite Bwf in contra.
  Qed.

  Definition runtime_val_wf_wrt_prog_interface_ (v: value) : bool :=
    match v with
      | Ptr ptr => Pointer.component ptr \in domm (prog_interface p)
      | _ => true
    end.
  
  Fixpoint runtime_expr_struct_invariant
           (e: expr) (val_test: value -> bool) : bool :=
    match e with
    | E_val v => val_test v      
    | E_binop _ e1 e2 =>
      runtime_expr_struct_invariant e1 val_test &&
      runtime_expr_struct_invariant e2 val_test
    | E_seq e1 e2 =>
      runtime_expr_struct_invariant e1 val_test &&
      runtime_expr_struct_invariant e2 val_test
    | E_if e1 e2 e3 =>
      runtime_expr_struct_invariant e1 val_test &&
      runtime_expr_struct_invariant e2 val_test &&
      runtime_expr_struct_invariant e3 val_test
    | E_alloc e =>
      runtime_expr_struct_invariant e val_test
    | E_deref e =>
      runtime_expr_struct_invariant e val_test
    | E_assign e1 e2 =>
      runtime_expr_struct_invariant e1 val_test &&
      runtime_expr_struct_invariant e2 val_test
    | E_call _ _ e =>
      runtime_expr_struct_invariant e val_test
    | E_callptr e1 e2 =>
      runtime_expr_struct_invariant e1 val_test &&
      runtime_expr_struct_invariant e2 val_test
    | E_funptr _
    | E_arg
    | E_local
    | E_exit => true
    end.

  Fixpoint cont_struct_invariant (k: cont) (val_test: value -> bool) : bool :=
    match k with
    | Kbinop1 _ e k2 =>
      runtime_expr_struct_invariant e val_test &&
      cont_struct_invariant k2 val_test
    | Kbinop2 _ v k2 =>
      val_test v &&
      cont_struct_invariant k2 val_test
    | Kseq e k2 =>
      runtime_expr_struct_invariant e val_test &&
      cont_struct_invariant k2 val_test
    | Kif e1 e2 k3 =>
      runtime_expr_struct_invariant e1 val_test &&
      runtime_expr_struct_invariant e2 val_test &&
      cont_struct_invariant k3 val_test
    | Kalloc k2 =>
      cont_struct_invariant k2 val_test
    | Kderef k2 =>
      cont_struct_invariant k2 val_test
    | Kassign1 e k2 =>
      runtime_expr_struct_invariant e val_test &&
      cont_struct_invariant k2 val_test
    | Kassign2 v k2 =>
      val_test v &&
      cont_struct_invariant k2 val_test
    | Kcall _ _ k2 =>
      cont_struct_invariant k2 val_test
    | Kcallptr1 e k2 =>
      runtime_expr_struct_invariant e val_test &&
      cont_struct_invariant k2 val_test
    | Kcallptr2 v k2 =>
      val_test v &&
      cont_struct_invariant k2 val_test
    | Kstop => true
    end.

  Definition stack_wf_wrt_prog_interface (s: stack) (val_test: value -> bool) : bool :=
    all (fun frm =>
           (f_component frm \in domm (prog_interface p))
           &&
           val_test (f_arg frm) 
           &&
           cont_struct_invariant (f_cont frm) val_test 
        )
        s.
  
  Lemma values_are_integers_runtime_expr_wf_wrt_prog_interface e:
    values_are_integers e ->
    runtime_expr_struct_invariant e (runtime_val_wf_wrt_prog_interface_).
  Proof.
    induction e; auto; intros Hval; inversion Hval as [Hval'];
      try (
          move : Hval' => /andP => [[Hval1 Hval2]];
                                   specialize (IHe1 Hval1);
                                   specialize (IHe2 Hval2);
                                   simpl; by rewrite IHe1 IHe2
        ).
    - destruct v; by auto.
    - move : Hval' => /andP => [[Hval1 Hval_]].
      move : Hval_ => /andP => [[Hval2 Hval3]].
      specialize (IHe1 Hval1).
      specialize (IHe2 Hval2).
      specialize (IHe3 Hval3).
      simpl. by rewrite IHe1 IHe2 IHe3.
  Qed.

  Lemma well_formed_expr_runtime_expr_wf_wrt_prog_interface C e:
    well_formed_expr p C e ->
    runtime_expr_struct_invariant e runtime_val_wf_wrt_prog_interface_.
  Proof.
    unfold well_formed_expr. intros [_ [? _]].
    by apply values_are_integers_runtime_expr_wf_wrt_prog_interface.
  Qed.

  Lemma runtime_val_wf_wrt_prog_interface_eval_binop v1 v2 op:
    runtime_val_wf_wrt_prog_interface_ v1 ->
    runtime_val_wf_wrt_prog_interface_ v2 ->
    runtime_val_wf_wrt_prog_interface_ (eval_binop op v1 v2).
  Proof.
    intros Hv1 Hv2.
    destruct op; destruct v1 as [| [[[perm1 c1] b1] o1] |];
      destruct v2 as [| [[[perm2 c2] b2] o2] |]; simpl in *; auto.
    - find_if_inside_goal; by auto.
    - find_if_inside_goal; by auto.
  Qed.
  
  Lemma load_component_prog_interface_inductively_provable s t s':
    initial_state p s ->
    Star sem s t s' ->
    (
      (
        forall ptr ptr',
          Memory.load (s_memory s') ptr = Some (Ptr ptr') ->
          Pointer.component ptr' \in domm (prog_interface p)
      )
      /\
      runtime_expr_struct_invariant (s_expr s') runtime_val_wf_wrt_prog_interface_
      /\
      cont_struct_invariant (s_cont s') runtime_val_wf_wrt_prog_interface_
      /\
      runtime_val_wf_wrt_prog_interface_ (s_arg s')
      /\
      s_component s' \in domm (prog_interface p)
      /\
      stack_wf_wrt_prog_interface (s_stack s') runtime_val_wf_wrt_prog_interface_                   
    ).
  Proof.
    intros Hini Hstar.
    apply star_iff_starR in Hstar.
    revert Hini.
    induction Hstar as [| s1 t1 s2 t2 s3 ? Hstar12 IHHstar Hstep23];
      subst;
      intros Hini.
    - split; [intros ? ? Hload | split; [| ]].
      + by eapply load_component_prog_interface_intitial_state; eauto.
      + unfold initial_state, initial_machine_state in Hini.
        destruct (prog_main p) eqn:emain; subst; simpl; auto.
        unfold prog_main in emain.
        apply wfprog_well_formed_procedures in emain; auto.
        unfold well_formed_expr in *. destruct emain as [_ [G_ _]].
        by apply values_are_integers_runtime_expr_wf_wrt_prog_interface in G_.
      + unfold initial_state, initial_machine_state in Hini.
        destruct (prog_main p) eqn:emain; subst; simpl; auto.
        * rewrite wfprog_main_existence; auto; by rewrite emain.
        * specialize (cprog_main_existence complete_program) as contra.
          by rewrite emain in contra.
    - specialize (IHHstar Hini)
        as [IHload [IHexpr [IHcont [IHarg [IHcomp IHstack]]]]];
            simpl in *.
      split;
        [
          intros ? ? Hload; inversion Hstep23; subst;
          try (simpl in Hload; eapply IHload; by eauto)
        |].
      + (* Hload in context; case alloc *)
        simpl in *. 
        destruct ((Pointer.component ptr, Pointer.block ptr) ==
                  (Pointer.component ptr0, Pointer.block ptr0)) eqn:eqalloc.
        * move : eqalloc => /eqP => eqalloc.
          specialize (Memory.load_after_alloc_eq _ _ _ _ _ _ H0 eqalloc) as Hload'.
          rewrite Hload' in Hload. repeat (find_if_inside_hyp Hload; last discriminate).
          discriminate.
        * assert (Hneq: (Pointer.component ptr, Pointer.block ptr) <>
                        (Pointer.component ptr0, Pointer.block ptr0)).
          { unfold not. move => /eqP => contra. by rewrite contra in eqalloc. } 
          specialize (Memory.load_after_alloc _ _ _ _ _ _ H0 Hneq) as Hrewr.
          rewrite Hrewr in Hload. by eapply IHload; eauto.
      + (* Hload in context; case store *)
        simpl in *.
        specialize (Memory.load_after_store _ _ _ _ ptr H) as Hload'.
        rewrite Hload' in Hload.
        find_if_inside_hyp Hload.
        * inversion Hload; subst; clear Hload.
          simpl in IHcont. by move : IHcont => /andP => [[G_ _]].
        * eapply IHload; by eauto.
      + split; [inversion Hstep23; subst; simpl in *; auto;
                try (by move : IHexpr => /andP => [[? ?]]);
                try (by move : IHcont => /andP => [[? ?]])
               |].
        * apply runtime_val_wf_wrt_prog_interface_eval_binop; auto.
          by move : IHcont => /andP => [[? ?]].
        * move : IHexpr => /andP => [[G_ ?]].
          by move : G_ => /andP => [[? ?]].
        * move : IHcont => /andP => [[G_ ?]].
          move : G_ => /andP => [[? ?]].
          by find_if_inside_goal.
        * by apply Memory.component_of_alloc_ptr in H0; subst.
        * destruct v; auto. by eapply IHload; eauto.
        * apply wfprog_well_formed_procedures in H0; auto.
          by eapply well_formed_expr_runtime_expr_wf_wrt_prog_interface; eauto.
        * apply wfprog_well_formed_procedures in H1; auto.
          by eapply well_formed_expr_runtime_expr_wf_wrt_prog_interface; eauto.
        * split; [inversion Hstep23; subst; simpl in *; auto;
                try (move : IHexpr => /andP => [[IHe1 IHe2]]);
                try (move : IHcont => /andP => [[IHk1 IHk2]]);
                auto;
                try (
                    match goal with
                    | H1 : is_true (?X), H2: is_true (?Y) |-
                      is_true (andb ?X ?Y) => by rewrite H1 H2
                    end
                  )
               |].
          -- move : IHe1 => /andP => [[IHe1 IHe2_]].
             by rewrite IHe2_ IHe2 IHcont.
          -- move : IHstack => /andP => [[IHstack _]].
             by move : IHstack => /andP => [[_ ?]].
          -- move : IHstack => /andP => [[IHstack _]].
             by move : IHstack => /andP => [[_ ?]].
          -- split; [inversion Hstep23; subst; simpl in *; auto;
                     try (move : IHexpr => /andP => [[IHe1 IHe2]]);
                     try (move : IHcont => /andP => [[IHk1 IHk2]]);
                     auto;
                     try (
                         match goal with
                         | H1 : is_true (?X), H2: is_true (?Y) |-
                           is_true (andb ?X ?Y) => by rewrite H1 H2
                         end
                       )
                    |].
             ++ do 2 (move : IHstack => /andP => [[IHstack _]]).
                by move : IHstack => /andP => [[_ ?]].
             ++ do 2 (move : IHstack => /andP => [[IHstack _]]).
                by move : IHstack => /andP => [[_ ?]].
             ++ split; [inversion Hstep23; subst; simpl in *; auto |].
                ** by eapply find_procedure_prog_interface; eauto.
                ** by repeat (move : IHstack => /andP => [[IHstack _]]).
                ** inversion Hstep23; subst; simpl in *; auto.
                   --- by rewrite IHarg IHcont IHstack IHcomp.
                   --- by rewrite IHarg IHcont IHstack IHcomp.
                   --- by (move : IHstack => /andP => [[_ ?]]).
                   --- by (move : IHstack => /andP => [[_ ?]]).
  Qed.
  
  Lemma load_component_prog_interface s t s' ptr ptr' :
    initial_state p s ->
    Star sem s t s' ->
    Memory.load (s_memory s') ptr = Some (Ptr ptr') ->
    Pointer.component ptr' \in domm (prog_interface p).
  Proof.
    intros Hini Hstar.
    specialize (load_component_prog_interface_inductively_provable Hini Hstar);
      intuition.
    by eapply H1; eauto.
  Qed.

  
  
  (* TODO: Move to Common/Memory.v *)
  Lemma load_some_in_domm mem ptr v:
    Memory.load mem ptr = Some v ->
    Pointer.component ptr \in domm mem.
  Proof.
    unfold Memory.load. find_if_inside_goal; last discriminate.
    destruct (mem (Pointer.component ptr)) eqn:emem; last discriminate. intros _.
    apply/dommP. by eauto.
  Qed.

  Lemma initial_state_domm_s_memory s:
    initial_state p s ->
    domm (s_memory s) = domm (prog_interface p).
  Proof.
    unfold initial_state. intros. subst. unfold initial_machine_state.
    apply cprog_main_existence in complete_program as HisSome.
    destruct (prog_main p) eqn:emain; last discriminate. simpl.
    by apply domm_prepare_buffers.
  Qed.
  
  Lemma step_preserves_mem_domm s t s' :
    Step sem s t s' ->
    domm (s_memory s) = domm (s_memory s').
  Proof.
    intros Hstep.
    inversion Hstep; subst;
      try reflexivity. (* Most operations do not modify the memory. *)
    - (* Preservation by Memory.alloc. *)
      match goal with
      | Halloc : Memory.alloc _ _ _ = _ |- _ =>
        unfold Memory.alloc in Halloc;
          destruct (mem C) as [memC |] eqn:Hcase;
            [| discriminate];
          destruct (ComponentMemory.alloc memC (Z.to_nat size)) as [memC' b];
          inversion Halloc; subst; simpl;
          rewrite domm_set fsetU1in; [reflexivity |];
          apply /dommP; now eauto
      end.
    - (* Preservation by Memory.store. *)
      rename H into Hstore.
    match goal with
    | Hstore : Memory.store _ ?PTR ?V = _ |- _ =>
      unfold Memory.store in Hstore;
        destruct (Permission.eqb (Pointer.permission PTR) Permission.data) eqn:Hperm;
        [| discriminate];
        destruct (mem (Pointer.component PTR)) as [memC |] eqn:Hcase1;
        [| discriminate];
        destruct (ComponentMemory.store
                    memC (Pointer.block PTR) (Pointer.offset PTR) V)
          as [memC' |] eqn:Hcase2;
        [| discriminate];
        inversion Hstore as [Hsetm];
        simpl; rewrite domm_set fsetU1in;
          [reflexivity |];
          apply /dommP; now eauto
    end.
  Qed.

  Lemma comes_from_initial_state_mem_domm s t s' :
    initial_state p s ->
    Star sem s t s' ->
    domm (s_memory s') = domm (prog_interface p).
  Proof.
    intros Hini Hstar.
    apply star_iff_starR in Hstar.
    revert Hini.
    induction Hstar as [| s1 t1 s2 t2 s3 ? Hstar12 IHHstar Hstep23];
      subst;
      intros Hini.
    - by apply initial_state_domm_s_memory.
    - specialize (IHHstar Hini).
      apply step_preserves_mem_domm in Hstep23. congruence.
  Qed.
  
  Lemma load_component_prog_interface_addr s t s' ptr v :
    initial_state p s ->
    Star sem s t s' ->
    Memory.load (s_memory s') ptr = Some v ->
    Pointer.component ptr \in domm (prog_interface p).
  Proof.
    intros Hini Hstar.
    apply star_iff_starR in Hstar.
    revert Hini.
    induction Hstar as [| s1 t1 s2 t2 s3 ? Hstar12 IHHstar Hstep23];
      subst;
      intros Hini Hload.
    - apply load_some_in_domm in Hload.
      by erewrite <- initial_state_domm_s_memory; eauto.
    - specialize (IHHstar Hini).
      inversion Hstep23; subst;
        try (simpl in Hload; apply IHHstar; by auto);
        (
          apply load_some_in_domm in Hload; simpl in Hload;
          apply star_iff_starR in Hstar12;
          specialize (comes_from_initial_state_mem_domm Hini Hstar12) as G_; simpl in G_
        ).
      + apply Memory.domm_alloc in H0. by rewrite -G_ H0. 
      + apply Memory.domm_store in H. by rewrite -G_ H.
  Qed.

  Definition b_nextblock mem (v: value) : bool :=
    match v with
    | Ptr (Permission.data, C, b, o) =>
      match mem C with
      | Some Cmem => b <? ComponentMemory.next_block Cmem
      | None => false
      end
    | _ => true
    end.

  Lemma values_are_integers_b_nextblock e mem:
    values_are_integers e ->
    runtime_expr_struct_invariant e (b_nextblock mem).
  Proof.
    induction e; simpl; auto.
    - by destruct v; auto.
    - move => /andP [? ?]. rewrite IHe1; by auto.
    - move => /andP [? ?]. rewrite IHe1; by auto.
    - move => /andP [? H]. move : H => /andP => [[? ?]].
      rewrite IHe1; auto. rewrite IHe2; by auto.
    - move => /andP [? ?]. rewrite IHe1; by auto.
    - move => /andP [? ?]. rewrite IHe1; by auto.
  Qed.

  Lemma b_next_block_eval_binop mem v1 v2 op:
    b_nextblock mem v1 ->
    b_nextblock mem v2 ->
    b_nextblock mem (eval_binop op v1 v2).
  Proof.
    intros Hv1 Hv2.
    destruct op; destruct v1 as [| [[[perm1 c1] b1] o1] |];
      destruct v2 as [| [[[perm2 c2] b2] o2] |]; simpl in *; auto.
    - find_if_inside_goal; by auto.
    - find_if_inside_goal; by auto.
  Qed.
  
  Lemma load_data_next_block_initial_state s:
    initial_state p s ->
    forall ptr C b o,
      Memory.load (s_memory s) ptr = Some (Ptr (Permission.data, C, b, o)) ->
      exists Cmem,
        (s_memory s) C = Some Cmem /\
        b < ComponentMemory.next_block Cmem.
  Proof.
    intros Hinit ? ? ? ? Hload.
    unfold initial_state in Hinit. subst.
    unfold initial_machine_state in *.
    destruct (prog_main p) eqn:e; simpl in *.
    - unfold prepare_buffers, Memory.load in *.
      find_if_inside_hyp Hload; [|discriminate].
      rewrite mapmE in Hload.
      unfold omap, obind, oapp in *.
      destruct (prog_buffers p (Pointer.component ptr)) as [buf|] eqn:ebuf;
        [|discriminate].
      simpl in *. rewrite ComponentMemory.load_prealloc in Hload.
      find_if_inside_hyp Hload; [|discriminate].
      rewrite setmE in Hload.
      find_if_inside_hyp Hload; [|discriminate].
      destruct buf as [sz|chnk].
      + find_if_inside_hyp Hload; discriminate.
      + assert (exists x, prog_interface p (Pointer.component ptr) = Some x)
          as [? Hifc].
        {
          apply/dommP. specialize (wfprog_defined_buffers valid_program) as Hrewr.
          rewrite Hrewr. apply/dommP. by eauto.   
        }
        assert (Hifc_: prog_interface p (Pointer.component ptr)).
        { by rewrite Hifc. }
        specialize (wfprog_well_formed_buffers valid_program Hifc_) as Hwfbuf.
        rewrite ebuf in Hwfbuf.
        simpl in *. destruct Hwfbuf as [_ G_]. move : G_ => /andP => [[_ G_]].
        move : G_ => /allP => G_. apply nth_error_In, In_in, G_ in Hload.
        by simpl in *.
    - unfold Memory.load in *. find_if_inside_hyp Hload; [|discriminate].
      by rewrite emptymE in Hload.
  Qed.

  Lemma b_nextblock_alloc v (mem: Memory.t) C sz ptr mem':
    b_nextblock mem v ->
    Memory.alloc mem C (Z.to_nat sz) = Some (mem', ptr) ->
    b_nextblock mem' v.
  Proof.
    intros Hb Halloc. 
    destruct v as [ | [[[[] c] b] o] | ]; auto. simpl in *.
    unfold Memory.alloc in *.
    destruct (mem c) as [memc|] eqn:ememc; [|discriminate].
    destruct (mem C) as [memC|] eqn:ememC; [|discriminate].
    destruct (ComponentMemory.alloc memC (Z.to_nat sz))
      as [memC' b'] eqn:ememC'.
    inversion Halloc; subst. rewrite setmE.
    find_if_inside_goal.
    + move : e => /eqP => ?; subst.
      apply ComponentMemory.next_block_alloc in ememC' as [G1 G2]; subst; rewrite G2.
      apply Nat.ltb_lt. apply/ssrnat.leP. apply ssrnat.ltn_addr.
      apply/ssrnat.leP. apply Nat.ltb_lt.
      rewrite ememc in ememC. inversion ememC; subst. by rewrite Hb.
    + by rewrite ememc.
  Qed.
    
  Lemma b_nextblock_store (mem: Memory.t) v P C b o v' mem':
    b_nextblock mem v ->
    Memory.store mem (P, C, b, o) v' = Some mem' ->
    b_nextblock mem' v.
  Proof.
    intros Hb Hstore. 
    destruct v as [ | [[[[] c] bv] ov] | ]; auto. simpl in *.
    unfold Memory.store in *.
    destruct (mem c) as [memc|] eqn:ememc; [|discriminate].
    find_if_inside_hyp Hstore; [|discriminate]; simpl in *.
    destruct (mem C) as [memC|] eqn:ememC; [|discriminate].
    destruct (ComponentMemory.store memC b o v')
      as [memC'|] eqn:ememC'; [|discriminate].
    inversion Hstore; subst. rewrite setmE.
    find_if_inside_goal.
    + apply ComponentMemory.next_block_store_stable in ememC'. rewrite -ememC'.
      move : e0 => /eqP => ?; subst. rewrite ememc in ememC. inversion ememC. by subst.
    + by rewrite ememc.
  Qed.
  
  Lemma runtime_expr_struct_invariant_b_nextblock_alloc
        re (mem: Memory.t) C sz ptr mem':
    runtime_expr_struct_invariant re (b_nextblock mem) ->
    Memory.alloc mem C (Z.to_nat sz) = Some (mem', ptr) ->
    runtime_expr_struct_invariant re (b_nextblock mem').
  Proof.
    induction re; auto; intros Hre Halloc; simpl in *;
      try (move : Hre => /andP => [[H1 H2]]; apply/andP; by intuition).
    - by eapply b_nextblock_alloc; eauto.
    - move : Hre => /andP => [[H1 H2]]. apply/andP. intuition.
      move : H1 => /andP => [[? ?]]. apply/andP. by intuition.
  Qed. 
      
  Lemma runtime_expr_struct_invariant_b_nextblock_store
        re (mem: Memory.t) P C b o v' mem':
    runtime_expr_struct_invariant re (b_nextblock mem) ->
    Memory.store mem (P, C, b, o) v' = Some mem' ->
    runtime_expr_struct_invariant re (b_nextblock mem').
  Proof.
    induction re; auto; intros Hre Hstore; simpl in *;
      try (move : Hre => /andP => [[H1 H2]]; apply/andP; by intuition).
    - by eapply b_nextblock_store; eauto.
    - move : Hre => /andP => [[H1 H2]]. apply/andP. intuition.
      move : H1 => /andP => [[? ?]]. apply/andP. by intuition.
  Qed. 
  
  Lemma cont_struct_invariant_b_nextblock_alloc k (mem: Memory.t) C sz ptr mem' :
    cont_struct_invariant k (b_nextblock mem) ->
    Memory.alloc mem C (Z.to_nat sz) = Some (mem', ptr) ->
    cont_struct_invariant k (b_nextblock mem').
  Proof.
    induction k; auto; intros Hmem Halloc; simpl in *;
      move : Hmem => /andP => [[H1 H2]]; apply/andP; intuition;
                                try (by eapply b_nextblock_alloc; eauto);
                                try (by eapply runtime_expr_struct_invariant_b_nextblock_alloc; eauto).
    - apply/andP. move : H1 => /andP => [[? ?]].
      split; by eapply runtime_expr_struct_invariant_b_nextblock_alloc; eauto.
  Qed.

  Lemma cont_struct_invariant_b_nextblock_store k (mem: Memory.t) P C b o v mem':
    cont_struct_invariant k (b_nextblock mem) ->
    Memory.store mem (P, C, b, o) v = Some mem' ->
    cont_struct_invariant k (b_nextblock mem').
  Proof.
    induction k; auto; intros Hmem Hstore; simpl in *;
      move : Hmem => /andP => [[H1 H2]]; apply/andP; intuition;
                                try (by eapply b_nextblock_store; eauto);
                                try (by eapply runtime_expr_struct_invariant_b_nextblock_store; eauto).
    - apply/andP. move : H1 => /andP => [[? ?]].
      split; by eapply runtime_expr_struct_invariant_b_nextblock_store; eauto.
  Qed.

  Lemma stack_wf_wrt_prog_interface_b_nextblock_alloc
        s (mem: Memory.t) C size mem' ptr:
    stack_wf_wrt_prog_interface s (b_nextblock mem) ->
    Memory.alloc mem C (Z.to_nat size) = Some (mem', ptr) ->
    stack_wf_wrt_prog_interface s (b_nextblock mem').
  Proof.
    induction s using last_ind; auto. unfold stack_wf_wrt_prog_interface.
    rewrite !all_rcons. intros Hwf Halloc.
    repeat (let H := fresh "H" in move : Hwf => /andP => [[Hwf H]]).
    specialize (IHs H Halloc).
    apply/andP; split; [|assumption].
    apply/andP; split; [|by eapply cont_struct_invariant_b_nextblock_alloc; eauto].
    apply/andP; split; [assumption|by eapply b_nextblock_alloc; eauto].
  Qed.
    
  Lemma stack_wf_wrt_prog_interface_b_nextblock_store
        s (mem: Memory.t) P C b o v mem':
    stack_wf_wrt_prog_interface s (b_nextblock mem) ->
    Memory.store mem (P, C, b, o) v = Some mem' ->
    stack_wf_wrt_prog_interface s (b_nextblock mem').
  Proof.
    induction s using last_ind; auto. unfold stack_wf_wrt_prog_interface.
    rewrite !all_rcons. intros Hwf Hstore.
    repeat (let H := fresh "H" in move : Hwf => /andP => [[Hwf H]]).
    specialize (IHs H Hstore).
    apply/andP; split; [|assumption].
    apply/andP; split; [|by eapply cont_struct_invariant_b_nextblock_store; eauto].
    apply/andP; split; [assumption|by eapply b_nextblock_store; eauto].
  Qed.


  Lemma load_data_next_block_inductively_provable s t s' :
    initial_state p s ->
    Star sem s t s' ->
    (
      (
        forall ptr C b o,
          Memory.load (s_memory s') ptr = Some (Ptr (Permission.data, C, b, o)) ->
          exists Cmem,
            (* Memory.next_block (s_memory s') c = some b' /\ *)
            (s_memory s') C = Some Cmem /\
            b < ComponentMemory.next_block Cmem
      )
      /\
      runtime_expr_struct_invariant (s_expr s') (b_nextblock (s_memory s'))
      /\
      cont_struct_invariant (s_cont s') (b_nextblock (s_memory s'))
      /\
      b_nextblock (s_memory s') (s_arg s')
      /\
      (exists cmem,
          (s_memory s') (s_component s') = Some cmem
          /\
          Block.local <? ComponentMemory.next_block cmem
      )
      /\
      stack_wf_wrt_prog_interface (s_stack s') (b_nextblock (s_memory s'))
      /\
      (
        forall C',
          C' \in domm (prog_interface p) ->
          exists cmem : ComponentMemory.t,
            (s_memory s') C' = Some cmem /\
            Block.local <? ComponentMemory.next_block cmem
      )
    ).
  Proof.
    intros Hini Hstar.
    apply star_iff_starR in Hstar.
    revert Hini.
    induction Hstar as [| s1 t1 s2 t2 s3 ? Hstar12 IHHstar Hstep23];
      subst;
      intros Hini.
    - split; [intros ? ? ? ? Hload | split; [| ]].
      + by eapply load_data_next_block_initial_state; eauto.
      + unfold initial_state, initial_machine_state in Hini.
        destruct (prog_main p) eqn:emain; subst; simpl; auto.
        unfold prog_main in emain.
        apply wfprog_well_formed_procedures in emain; auto.
        unfold well_formed_expr in *. destruct emain as [_ [G_ _]].
          by eapply values_are_integers_b_nextblock in G_; eauto.
      + unfold initial_state, initial_machine_state in Hini.
        destruct (prog_main p) eqn:emain; subst; simpl; try by eauto; intuition.
        -- assert (exists cmem, prepare_buffers p Component.main = Some cmem) as [? ?].
           {
             apply/dommP. rewrite domm_prepare_buffers; auto.
             rewrite wfprog_main_existence; auto.
             by rewrite emain.
           }
           assert (G1: Block.local <? ComponentMemory.next_block x).
           {
             unfold prepare_buffers in H. rewrite mapmE in H.
             unfold omap, obind, oapp in *.
             destruct (prog_buffers p Component.main)
               as [buf|] eqn:ebuf; [|discriminate].
             inversion H; subst. by rewrite ComponentMemory.nextblock_prealloc.
           }
           intuition.
           ++ exists x; by intuition.
           ++ assert (exists cmem, prepare_buffers p C' = Some cmem) as [? ?].
              {
                apply/dommP. rewrite domm_prepare_buffers; auto.
              }
              eexists; intuition; eauto.
              unfold prepare_buffers in H1. rewrite mapmE in H1.
              unfold omap, obind, oapp in *.
              destruct (prog_buffers p C')
                as [buf|] eqn:ebuf; [|discriminate].
              inversion H1; subst. by rewrite ComponentMemory.nextblock_prealloc.
        -- intuition; destruct complete_program;
             by rewrite emain in cprog_main_existence0. 
    - specialize (IHHstar Hini)
        as [IHload [IHexpr [IHcont [IHarg [[compMem [HcompMem HcompMem2]] [IHstack IHfind]]]]]];
            simpl in *.
      split;
        [
          intros ? ? ? ? Hload; inversion Hstep23; subst;
          try (simpl in Hload; eapply IHload; by eauto)
         |]; simpl in *.
      + destruct ((Pointer.component ptr, Pointer.block ptr) ==
                  (Pointer.component ptr0, Pointer.block ptr0)) eqn:eptr.
        * move : eptr => /eqP => eptr.
          erewrite Memory.load_after_alloc_eq in Hload; eauto.
          repeat (find_if_inside_hyp Hload; [|discriminate]).
          by inversion Hload.
        * erewrite Memory.load_after_alloc in Hload; eauto.
          -- specialize (IHload _ _ _ _ Hload) as [? [? ?]].
             unfold Memory.alloc in *.
             destruct (mem C0) as [memC0|] eqn:eC0; [|discriminate].
             destruct (ComponentMemory.alloc memC0 (Z.to_nat size))
               as [memC' b'] eqn:ememC'.
             inversion H0; subst. rewrite setmE.
             find_if_inside_goal.
             ++ move : e => /eqP => ?; subst. rewrite eC0 in H1. inversion H1; subst.
                simpl in *. apply ComponentMemory.next_block_alloc in ememC' as [G1 G2].
                subst. exists memC'. intuition. 
                rewrite G2. apply/ssrnat.ltP. 
                apply ssrnat.ltn_addr. by apply/ssrnat.ltP.
             ++ rewrite H1. by eauto.
          -- apply/eqP. by rewrite eptr.
      + destruct (Pointer.eq (P', C', b', o') ptr) eqn:eptr.
        * move : eptr => /Pointer.eqP => eptr; subst.
          specialize (Memory.load_after_store_eq _ _ _ _ H) as H_.
          rewrite Hload in H_. inversion H_; subst. clear H_.
          simpl in *. move : IHcont => /andP => [[G1 G2]].
          unfold Memory.store in H. find_if_inside_hyp H; [simpl in *|discriminate].
          destruct (mem C') as [memC'|] eqn:ememC'; [|discriminate].
          destruct (ComponentMemory.store memC' b' o' (Ptr (Permission.data, C, b, o)))
            as [memC'_after|] eqn:ememC'_after; [|discriminate].
          inversion H; subst. clear H. move : e => /Permission.eqP => e. subst.
          rewrite setmE. find_if_inside_goal.
          -- move : e => /eqP => ?; subst. exists memC'_after; intuition.
             rewrite ememC' in G1.
             apply ComponentMemory.next_block_store_stable in ememC'_after.
             by rewrite -ememC'_after -Nat.ltb_lt. 
          -- destruct (mem C) as [memC|] eqn:ememC; [|discriminate].
             exists memC; intuition. by rewrite -Nat.ltb_lt.
        * move : eptr => /Pointer.eqP => eptr.
          erewrite (Memory.load_after_store_neq _ _ _ _ _ eptr) in Hload; eauto.
          specialize (IHload _ _ _ _ Hload) as [memC [ememC G1]].
          unfold Memory.store in H. find_if_inside_hyp H; [simpl in *|discriminate].
          destruct (mem C') as [memC'|] eqn:ememC'; [|discriminate].
          destruct (ComponentMemory.store memC' b' o' v)
            as [memC'_after|] eqn:ememC'_after; [|discriminate].
          inversion H; subst. clear H. move : e => /Permission.eqP => e. subst.
          rewrite setmE. find_if_inside_goal.
          -- move : e => /eqP => ?; subst. exists memC'_after; intuition.
             rewrite ememC' in ememC; inversion ememC; subst.
             apply ComponentMemory.next_block_store_stable in ememC'_after.
             by rewrite -ememC'_after. 
          -- by eexists; eauto.
      + split; [inversion Hstep23; subst; simpl in *; auto;
                try (by move : IHexpr => /andP => [[? ?]]);
                try (by move : IHcont => /andP => [[? ?]])
               |].
        * apply b_next_block_eval_binop; auto.
          by move : IHcont => /andP => [[? ?]].
        * move : IHexpr => /andP => [[G_ ?]].
          by move : G_ => /andP => [[? ?]].
        * move : IHcont => /andP => [[G_ ?]].
          move : G_ => /andP => [[? ?]].
          by find_if_inside_goal.
        * by rewrite HcompMem.
        * destruct ptr as [[[[] c] b] o]; auto.
          specialize (Memory.next_block_alloc _ _ _ _ _ H0) as [G1 G2].
          specialize (Memory.component_of_alloc_ptr _ _ _ _ _ H0). simpl; intros; subst.
          simpl in *. unfold Memory.next_block in *.
          rewrite HcompMem in G1.
          destruct (mem' C) as [mem'C|] eqn:emem'C; [|discriminate].
          inversion G1. subst. inversion G2 as [G3]. rewrite G3 ssrnat.addn1.
          by apply Nat.ltb_lt.
        * destruct v as [| [[[[] c] b] o] |]; auto.
          specialize (IHload _ _ _ _ H) as [? [G1 G2]]. simpl. rewrite G1. 
          by apply Nat.ltb_lt.
        * destruct v as [| [[[[] c] b] o] |]; auto.
          move : IHcont => /andP => [[G1 _]].
          simpl in *.
          assert (exists Cmem, mem' c = Some Cmem) as [memc ememc].
          { apply/ dommP. erewrite <- Memory.domm_store; eauto. apply/dommP.
            by destruct (mem c) as [memc|] eqn:ememc; [|discriminate]; eauto.
          }
          rewrite ememc. 
          specialize (Memory.next_block_store_stable _ _ _ _ c H) as Heq.
          destruct (mem c) as [memc_|] eqn:ememc_; [|discriminate].
          unfold Memory.next_block in *. rewrite ememc ememc_ in Heq.
          inversion Heq as [Hrewr]. by rewrite Hrewr.
        * apply values_are_integers_b_nextblock.
          eapply wfprog_well_formed_procedures in H0; auto.
          unfold well_formed_expr in *. by intuition.
        * apply values_are_integers_b_nextblock.
          eapply wfprog_well_formed_procedures in H1; auto.
          unfold well_formed_expr in *. by intuition.
        * split; [inversion Hstep23; subst; simpl in *; auto;
                try (move : IHexpr => /andP => [[IHe1 IHe2]]);
                try (move : IHcont => /andP => [[IHk1 IHk2]]);
                auto;
                try (
                    match goal with
                    | H1 : is_true (?X), H2: is_true (?Y) |-
                      is_true (andb ?X ?Y) => by rewrite H1 H2
                    end
                  )
               |].
          -- move : IHe1 => /andP => [[IHe1 IHe2_]].
             by rewrite IHe2_ IHe2 IHcont.
          -- by eapply cont_struct_invariant_b_nextblock_alloc; eauto.
          -- by eapply cont_struct_invariant_b_nextblock_store; eauto.
          -- move : IHstack => /andP => [[IHstack _]].
             by move : IHstack => /andP => [[_ ?]].
          -- move : IHstack => /andP => [[IHstack _]].
             by move : IHstack => /andP => [[_ ?]].
          -- split; [inversion Hstep23; subst; simpl in *; auto;
                     try (move : IHexpr => /andP => [[IHe1 IHe2]]);
                     try (move : IHcont => /andP => [[IHk1 IHk2]]);
                     auto;
                     try (
                         match goal with
                         | H1 : is_true (?X), H2: is_true (?Y) |-
                           is_true (andb ?X ?Y) => by rewrite H1 H2
                         end
                       )
                    |].
             ++ by eapply b_nextblock_alloc; eauto.
             ++ by eapply b_nextblock_store; eauto.
             ++ do 2 (move : IHstack => /andP => [[IHstack _]]).
                by move : IHstack => /andP => [[_ ?]].
             ++ do 2 (move : IHstack => /andP => [[IHstack _]]).
                by move : IHstack => /andP => [[_ ?]].
             ++ split; [inversion Hstep23; subst; simpl in *; auto;
                        try (by rewrite HcompMem; eauto)
                       |].
                ** specialize (@b_nextblock_alloc
                                 (Ptr (Permission.data, C, Block.local, 0%Z))
                                 mem C size ptr mem')
                    as G1.
                   assert (b_nextblock
                             mem (Ptr (Permission.data, C, Block.local, 0%Z))) as G2.
                   {
                     simpl. by rewrite HcompMem.
                   }
                   specialize (G1 G2 H0). simpl in G1.
                   destruct (mem' C); [|discriminate].
                   by eauto.
                ** specialize (@b_nextblock_store
                                 
                                 mem
                                 (Ptr (Permission.data, C, Block.local, 0%Z))
                                 P' C' b' o' v mem') as G1.
                   assert (b_nextblock
                             mem (Ptr (Permission.data, C, Block.local, 0%Z))) as G2.
                   {
                     simpl. by rewrite HcompMem.
                   }
                   specialize (G1 G2 H). simpl in G1.
                   destruct (mem' C); [|discriminate].
                   by eauto.
                ** eapply IHfind; eauto. by eapply find_procedure_prog_interface; eauto.
                ** repeat (move : IHstack => /andP => [[IHstack _]]).
                   by eapply IHfind; eauto.
                ** split; [inversion Hstep23; subst; simpl in *; auto |].
                   --- by eapply stack_wf_wrt_prog_interface_b_nextblock_alloc; eauto.
                   --- by eapply stack_wf_wrt_prog_interface_b_nextblock_store; eauto.
                   --- repeat (apply/andP; split; [|assumption]).
                       by eapply find_procedure_prog_interface; eauto.
                   --- repeat (apply/andP; split; [|assumption]).
                       assert (Hrewr: mem =
                                      s_memory [State C, s, mem,
                                                Kcall C' P k,
                                                E_val v, old_call_arg]) by auto.
                       erewrite <- comes_from_initial_state_mem_domm.
                       +++ apply/dommP. exists compMem. by erewrite <- Hrewr.
                       +++ eassumption.
                       +++ apply star_iff_starR. eassumption.
                   --- by (move : IHstack => /andP => [[_ ?]]).
                   --- by (move : IHstack => /andP => [[_ ?]]).
                   --- inversion Hstep23; subst; simpl in *; auto.
                       +++ intros ? Hdomm.
                           specialize (IHfind _ Hdomm) as [? [Ga Gb]].
                           specialize (@b_nextblock_alloc
                                         (Ptr (Permission.data, C', Block.local, 0%Z))
                                         mem C size ptr mem')
                             as G1.
                           assert (b_nextblock
                                     mem
                                     (Ptr (Permission.data, C', Block.local, 0%Z)))
                             as G2.
                           {
                             simpl. by rewrite Ga.
                           }
                           specialize (G1 G2 H0). simpl in G1.
                           destruct (mem' C'); [|discriminate].
                           by eauto.
                       +++ intros C'0 Hdomm.
                           specialize (IHfind _ Hdomm) as [? [Ga Gb]].
                           specialize (@b_nextblock_store
                                         mem
                                         (Ptr (Permission.data, C'0, Block.local, 0%Z))
                                         P' C' b' o' v mem') as G1.
                           assert (b_nextblock
                                     mem (Ptr (Permission.data, C'0, Block.local, 0%Z)))
                             as G2.
                           {
                             simpl. by rewrite Ga.
                           }
                           specialize (G1 G2 H). simpl in G1.
                           destruct (mem' C'0); [|discriminate].
                           by eauto.
  Qed.

  Lemma load_data_next_block:
      forall s t s' ptr C b o,
        initial_state p s ->
        Star sem s t s' ->
        Memory.load (CS.s_memory s') ptr = Some (Ptr (Permission.data, C, b, o)) ->
        exists Cmem : ComponentMemory.t,
          CS.s_memory s' C = Some Cmem /\ b < ComponentMemory.next_block Cmem.
  Proof.
    intros.
    specialize (load_data_next_block_inductively_provable H H0) as [G1 _].
    eapply G1; eauto.
  Qed.
  
  (* NOTE: Consider a CSInvariants for the Source *)
  Definition private_pointers_never_leak_S metadata_size :=
    forall (s : state) (t : Events.trace Events.event),
      Star sem (initial_machine_state p) t s ->
      good_trace_extensional (left_addr_good_for_shifting metadata_size) t /\
      (forall (mem : eqtype.Equality.sort Memory.Memory.t),
          s_memory s = mem ->
          shared_locations_have_only_shared_values mem metadata_size
      ).
End Semantics.

End CS.

Notation "[ 'CState' C , stk , mem , k , e , arg ]" :=
  (CS.State C stk mem k e arg)
  (at level 0, format "[ 'CState'  C ,  stk ,  mem ,  k ,  e ,  arg ]").
