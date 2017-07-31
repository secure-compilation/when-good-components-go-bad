Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Events.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Lib.Tactics.

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

Definition stack : Type := list (Component.id * value * cont).
Definition state : Type := Component.id * stack * Memory.t * cont * expr.

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
    NMap.find C (genv_buffers G) = Some b ->
    let t := E0 in
    kstep G (C, s, mem, k, E_local)
          t (C, s, mem, k, E_val (Ptr (C,b,0)))
| KS_Alloc1 : forall C s mem k e,
    let t := E0 in
    kstep G (C, s, mem, k, E_alloc e)
          t (C, s, mem, Kalloc k, e)
| KS_AllocEval : forall C s mem mem' k size ptr,
    Memory.alloc mem C size = Some (mem', ptr) ->
    let t := E0 in
    kstep G (C, s, mem, Kalloc k, E_val (Int size))
          t (C, s, mem', k, E_val (Ptr ptr))
| KS_Deref1 : forall C s mem k e,
    let t := E0 in
    kstep G (C, s, mem, k, E_deref e)
          t (C, s, mem, Kderef k, e)
| KS_DerefEval : forall C s mem k C' b' o' v,
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
    NMap.find C' (genv_procedures G) = Some C'_procs ->
    NMap.find P C'_procs = Some P_expr ->
    (* save the old call argument *)
    NMap.find C (genv_buffers G) = Some b ->
    Memory.load mem (C,b,0) = Some old_call_arg ->
    (* place the call argument in the target memory *)
    NMap.find C' (genv_buffers G) = Some b' ->
    Memory.store mem (C',b',0) (Int v) = Some mem' ->
    let t := [ECall C P v C'] in
    kstep G (C, s, mem, Kcall C' P k, E_val (Int v))
          t (C', (C, old_call_arg, k) :: s, mem', Kstop, P_expr)
| KS_CallRet : forall C s mem mem' k v C' old_call_arg b,
    (* restore the old call argument *)
    NMap.find C' (genv_buffers G) = Some b ->
    Memory.store mem (C', b, 0) old_call_arg = Some mem' ->
    let t := [ERet C v C'] in
    kstep G (C, (C', old_call_arg, k) :: s, mem, Kstop, E_val (Int v))
          t (C', s, mem', k, E_val (Int v)).

(* functional kstep *)

Definition eval_kstep (G : global_env) (st : state) : option (trace * state) :=
  let '(C, s, mem, k, e) := st in
  match e with
  (* pushing a new continuation *)
  | E_binop b_op e1 e2 =>
    Some (E0, (C, s, mem, Kbinop1 b_op e2 k, e1))
  | E_seq e1 e2 =>
    Some (E0, (C, s, mem, Kseq e2 k, e1))
  | E_if e1 e2 e3 =>
    Some (E0, (C, s, mem, Kif e2 e3 k, e1))
  | E_local =>
    match NMap.find C (genv_buffers G) with
    | Some b => Some (E0, (C, s, mem, k, E_val (Ptr (C,b,0))))
    | None => None
    end
  | E_alloc e =>
    Some (E0, (C, s, mem, Kalloc k, e))
  | E_deref e =>
    Some (E0, (C, s, mem, Kderef k, e))
  | E_assign e1 e2 =>
    Some (E0, (C, s, mem, Kassign1 e1 k, e2))
  | E_call C' P e =>
    if (imported_procedure_b (genv_interface G) C C' P) || (C =? C') then
      Some (E0, (C, s, mem, Kcall C' P k, e))
    else
      None
  (* evaluating current continuation *)
  | E_val v =>
    match k with
    | Kbinop1 b_op e2 k' =>
      Some (E0, (C, s, mem, Kbinop2 b_op v k', e2))
    | Kbinop2 b_op v1 k' =>
      Some (E0, (C, s, mem, k', E_val (eval_binop b_op v1 v)))
    | Kseq e2 k' =>
      Some (E0, (C, s, mem, k', e2))
    | Kif e2 e3 k' =>
      match v with
      | Int 0 => Some (E0, (C, s, mem, k', e3))
      | Int i => Some (E0, (C, s, mem, k', e2))
      | _ => None
      end
    | Kalloc k' =>
      match v with
      | Int size =>
        match Memory.alloc mem C size with
        | Some (mem',ptr) => Some (E0, (C, s, mem', k', E_val (Ptr ptr)))
        | None => None
        end
      | _ => None
      end
    | Kderef k' =>
      match v with
      | Ptr (C',b',o') =>
        match Memory.load mem (C',b',o') with
        | Some v => Some (E0, (C, s, mem, k', E_val v))
        | None => None
        end
      | _ => None
      end
    | Kassign1 e1 k' =>
      Some (E0, (C, s, mem, Kassign2 v k', e1))
    | Kassign2 v' k' =>
      match v with
      | Ptr (C',b',o') =>
        if C =? C' then
          match Memory.store mem (C',b',o') v' with
          | Some mem' => Some (E0, (C, s, mem', k', E_val v'))
          | None => None
          end
        else
          None
      | _ => None
      end
    | Kcall C' P k' =>
      match v with
      | Int i =>
        (* retrieve the procedure code *)
        match NMap.find C' (genv_procedures G) with
        | Some C'_procs =>
          match NMap.find P C'_procs with
          | Some P_expr =>
            (* save the old call argument *)
            match NMap.find C (genv_buffers G) with
            | Some b =>
              match Memory.load mem (C,b,0) with
              | Some old_call_arg =>
                (* place the call argument in the target memory *)
                match NMap.find C' (genv_buffers G) with
                | Some b' =>
                  match Memory.store mem (C',b',0) (Int i) with
                  | Some mem' =>
                    let t := [ECall C P i C'] in
                    Some (t, (C', (C, old_call_arg, k') :: s, mem', Kstop, P_expr))
                  | None => None
                  end
                | None => None
                end
              | None => None
              end
            | None => None
            end
          | None => None
          end
        | None => None
        end
      | _ => None
      end
    | Kstop =>
      match v, s with
      | Int i, (C',old_call_arg,k') :: s' =>
        (* restore the old call argument *)
        match NMap.find C' (genv_buffers G) with
        | Some b =>
          match Memory.store mem (C',b,0) old_call_arg with
          | Some mem' =>
            let t := [ERet C i C'] in
            Some (t, (C', s', mem', k', E_val (Int i)))
          | None => None
          end
        | None => None
        end
      | _, _ => None
      end
    end
  | _ => None
  end.

Ltac rewrite_equalities :=
  match goal with 
  | H: (_ =? _) = true |- _ => apply beq_nat_true_iff in H; rewrite H
  end.

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

Theorem eval_kstep_complete:
  forall G st t st',
    kstep G st t st' -> eval_kstep G st =  Some (t, st').
Proof.
  intros G st t st' Hkstep.
  inversion Hkstep; subst; simpl; auto.
  (* if expressions *)
  - apply beq_nat_false_iff in H.
    destruct i eqn:Hi; auto.
    + inversion H.
  (* local buffers *)
  - rewrite H. auto.
  (* memory allocs *)
  - rewrite H. auto.
  (* memory loads *)
  - unfold Memory.store, Memory.load, Memory.alloc in *.
    repeat simplify_options.
    reflexivity.
  (* memory stores *)
  - unfold Memory.store, Memory.load, Memory.alloc in *.
    rewrite <- beq_nat_refl.
    repeat simplify_options.
    reflexivity.
  (* calls/returns *)
  - destruct H.
    + destruct H as [CI [HCI Himport]].
      unfold Program.has_component in HCI.
      unfold Component.is_importing in Himport.
      unfold imported_procedure_b.
      apply NMap.find_1 in HCI. rewrite HCI.
      rewrite count_occ_In in Himport.
      inversion Himport.
      * rewrite <- H0. simpl. auto.
      * rewrite <- H. simpl. auto.
    + rewrite H. rewrite <- beq_nat_refl.
      rewrite orb_true_r. auto.
  - unfold Memory.store, Memory.load, Memory.alloc in *.
    repeat simplify_options.
    reflexivity.
  - unfold Memory.store, Memory.load, Memory.alloc in *.
    repeat simplify_options.
    reflexivity.
Qed.

Theorem eval_kstep_sound:
  forall G st t st',
    eval_kstep G st =  Some (t, st') -> kstep G st t st'.
Proof.
  intros.
  repeat unfold_state.
  match goal with
  | H: eval_kstep _ _ = Some _ |- kstep _ (_, _, _, _, ?E) _ (_, _, _, _, _) =>
    destruct E; simpl in H;
      try discriminate;
      try (repeat simplify_options;
           econstructor; eauto;
           repeat rewrite_memory_operations;
           repeat rewrite_equalities;
           reflexivity)
  end.
  - repeat simplify_options.
    rewrite orb_true_iff in Heqb.
    rewrite beq_nat_true_iff in Heqb.
    econstructor.
    destruct Heqb.
    + left.
      unfold imported_procedure.
      unfold Program.has_component, Component.is_importing.
      unfold imported_procedure_b in *.
      destruct (NMap.find (elt:=Component.interface) C (genv_interface G)) eqn:Hi;
        inversion H; try discriminate.
      exists i1. split.
      * apply (NMap.find_2 Hi).
      * destruct (count_occ procs_eqdec (Component.import i1) (i, i0) =? 0) eqn:Hcount;
           inversion H; try discriminate.
         apply count_occ_In with procs_eqdec.
         rewrite beq_nat_false_iff in Hcount.
         apply Nat.neq_0_lt_0 in Hcount.
         unfold gt. auto.
    + right. auto.
Qed.

Theorem eval_kstep_correct:
  forall G st t st',
    eval_kstep G st =  Some (t, st') <-> kstep G st t st'.
Proof.
  split.
  apply eval_kstep_sound.
  apply eval_kstep_complete.
Qed.

Theorem kstep_deterministic:
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
