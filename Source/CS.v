Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Events.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Source.Language.
Require Import Source.GlobalEnv.

(* small-step semantics with evaluation contexts *)

Inductive eval_context : Type :=
| EC_binop_left : binop -> expr -> eval_context
| EC_binop_right : binop -> value -> eval_context
| EC_seq_right : expr -> eval_context
| EC_if : expr -> expr -> eval_context
| EC_alloc : eval_context
| EC_deref : eval_context
| EC_assign_right : expr -> eval_context
| EC_assign_left : value -> eval_context
| EC_call : Component.id -> Procedure.id -> eval_context.

Definition kont : Type := list eval_context.
Definition stack : Type := list (Component.id * value * kont).
Definition state : Type := Component.id * stack * Memory.t * kont * expr.

Inductive step (G : global_env) : state -> trace -> state -> Prop :=
| S_binop_push_left:
    forall C s mem ks b_op e1 e2,
      let st := (C, s, mem, ks, E_binop b_op e1 e2) in
      let st' := (C, s, mem, EC_binop_left b_op e2 :: ks, e1) in
      step G st E0 st'
| S_binop_push_right:
    forall C s mem ks b_op v1 e2,
      let st := (C, s, mem, EC_binop_left b_op e2 :: ks, E_val v1) in
      let st' := (C, s, mem, EC_binop_right b_op v1 :: ks, e2) in
      step G st E0 st'
| S_binop_pop:
    forall C s mem ks b_op v1 v2,
      let st := (C, s, mem, EC_binop_right b_op v1 :: ks, E_val v2) in
      let st' := (C, s, mem, ks, E_val (eval_binop b_op v1 v2)) in
      step G st E0 st'
| S_seq_push:
    forall C s mem ks e1 e2,
      let st := (C, s, mem, ks, E_seq e1 e2) in
      let st' := (C, s, mem, EC_seq_right e2 :: ks, e1) in
      step G st E0 st'
| S_seq_pop:
    forall C s mem ks v e2,
      let st := (C, s, mem, EC_seq_right e2 :: ks, E_val v) in
      let st' := (C, s, mem, ks, e2) in
      step G st E0 st'
| S_if_push:
    forall C s mem ks e1 e2 e3,
      let st := (C, s, mem, ks, E_if e1 e2 e3) in
      let st' := (C, s, mem, EC_if e2 e3 :: ks, e1) in
      step G st E0 st'
| S_if_pop_conseq:
    forall C s mem ks e2 e3 i,
      let st := (C, s, mem, EC_if e2 e3 :: ks, E_val (Int i)) in
      i <> 0 ->
      let st' := (C, s, mem, ks, e2) in
      step G st E0 st'
| S_if_pop_alt:
    forall C s mem ks e2 e3,
      let st := (C, s, mem, EC_if e2 e3 :: ks, E_val (Int 0)) in
      let st' := (C, s, mem, ks, e3) in
      step G st E0 st'
| S_local_buffer:
    forall C s mem ks b,
      let st := (C, s, mem, ks, E_local) in
      NMap.find C (genv_buffers G) = Some b ->
      let st' := (C, s, mem, ks, E_val (Ptr (C,b,0))) in
      step G st E0 st'
| S_alloc_push:
    forall C s mem ks e,
      let st := (C, s, mem, ks, E_alloc e) in
      let st' := (C, s, mem, EC_alloc :: ks, e) in
      step G st E0 st'
| S_alloc_pop:
    forall C s mem mem' ks size ptr,
      let st := (C, s, mem, EC_alloc :: ks, E_val (Int size)) in
      Memory.alloc mem C size = Some (mem', ptr) ->
      let st' := (C, s, mem', ks, E_val (Ptr ptr)) in
      step G st E0 st'
| S_deref_push:
    forall C s mem ks e,
      let st := (C, s, mem, ks, E_deref e) in
      let st' := (C, s, mem, EC_deref :: ks, e) in
      step G st E0 st'
| S_deref_pop:
    forall C s mem ks C' b' o' v,
      let st := (C, s, mem, EC_deref :: ks, E_val (Ptr (C',b',o'))) in
      Memory.load mem (C',b',o') = Some v ->
      let st' := (C, s, mem, ks, E_val v) in
      step G st E0 st'
| S_assign_push_arg:
    forall C s mem ks e1 e2,
      let st := (C, s, mem, ks, E_assign e1 e2) in
      let st' := (C, s, mem, EC_assign_right e2 :: ks, e1) in
      step G st E0 st'
| S_assign_push_dest:
    forall C s mem ks v e2,
      let st := (C, s, mem, EC_assign_right e2 :: ks, E_val v) in
      let st' := (C, s, mem, EC_assign_left v :: ks, e2) in
      step G st E0 st'
| S_assign_pop:
    forall C s mem mem' ks v C' b' o',
      let st := (C, s, mem, EC_assign_left v :: ks, E_val (Ptr (C',b',o'))) in
      C = C' ->
      Memory.store mem (C',b',o') v = Some mem' ->
      let st' := (C, s, mem', ks, E_val v) in
      step G st E0 st'
| S_call_push_arg:
    forall C s mem ks C' P e,
      let st := (C, s, mem, ks, E_call C' P e) in
      imported_procedure (genv_interface G) C C' P \/ C = C' ->
      let st' := (C, s, mem, EC_call C' P :: ks, e) in
      step G st E0 st'
| S_call_push_proc:
    forall C s mem mem' ks C' P v C'_procs P_expr b b' old_call_arg,
      let st := (C, s, mem, EC_call C' P :: ks, E_val (Int v)) in
      (* retrieve the procedure code *)
      NMap.find C' (genv_procedures G) = Some C'_procs ->
      NMap.find P C'_procs = Some P_expr ->
      (* save the old call argument *)
      NMap.find C (genv_buffers G) = Some b ->
      Memory.load mem (C,b,0) = Some old_call_arg ->
      (* place the call argument in the target memory *)
      NMap.find C' (genv_buffers G) = Some b' ->
      Memory.store mem (C',b',0) (Int v) = Some mem' ->
      let st' := (C', (C, old_call_arg, ks) :: s, mem', [], P_expr) in
      let t := [ECall C P v C'] in
      step G st t st'
| S_call_pop:
    forall C s mem mem' ks v C' old_call_arg b,
      let st := (C, (C',old_call_arg,ks) :: s, mem, [], E_val (Int v)) in
      (* restore the old call argument *)
      NMap.find C' (genv_buffers G) = Some b ->
      Memory.store mem (C',b,0) old_call_arg = Some mem' ->
      let st' := (C', s, mem', ks, E_val (Int v)) in
      let t := [ERet C v C'] in
      step G st t st'.

(* functional version of step *)

Definition eval_step (G : global_env) (st : state) : option (trace * state) :=
  let '(C, s, mem, ks, e) := st in
  match e with
  (* pushing a new continuation *)
  | E_binop b_op e1 e2 =>
    Some (E0, (C, s, mem, EC_binop_left b_op e2 :: ks, e1))
  | E_seq e1 e2 =>
    Some (E0, (C, s, mem, EC_seq_right e2 :: ks, e1))
  | E_if e1 e2 e3 =>
    Some (E0, (C, s, mem, EC_if e2 e3 :: ks, e1))
  | E_local =>
    match NMap.find C (genv_buffers G) with
    | Some b => Some (E0, (C, s, mem, ks, E_val (Ptr (C,b,0))))
    | None => None
    end
  | E_alloc e =>
    Some (E0, (C, s, mem, EC_alloc :: ks, e))
  | E_deref e =>
    Some (E0, (C, s, mem, EC_deref :: ks, e))
  | E_assign e1 e2 =>
    Some (E0, (C, s, mem, EC_assign_right e2 :: ks, e1))
  | E_call C' P e =>
    if (imported_procedure_b (genv_interface G) C C' P) || (C =? C') then
      Some (E0, (C, s, mem, EC_call C' P :: ks, e))
    else
      None
  (* evaluating current continuation *)
  | E_val v =>
    match ks with
    | EC_binop_left b_op e2 :: ks' =>
      Some (E0, (C, s, mem, EC_binop_right b_op v :: ks', e2))
    | EC_binop_right b_op v1 :: ks' =>
      Some (E0, (C, s, mem, ks', E_val (eval_binop b_op v1 v)))
    | EC_seq_right e2 :: ks' =>
      Some (E0, (C, s, mem, ks', e2))
    | EC_if e2 e3 :: ks' =>
      match v with
      | Int 0 => Some (E0, (C, s, mem, ks', e3))
      | Int i => Some (E0, (C, s, mem, ks', e2))
      | _ => None
      end
    | EC_alloc :: ks' =>
      match v with
      | Int size =>
        match Memory.alloc mem C size with
        | Some (mem',ptr) => Some (E0, (C, s, mem', ks', E_val (Ptr ptr)))
        | None => None
        end
      | _ => None
      end
    | EC_deref :: ks' =>
      match v with
      | Ptr (C',b',o') =>
        match Memory.load mem (C',b',o') with
        | Some v => Some (E0, (C, s, mem, ks', E_val v))
        | None => None
        end
      | _ => None
      end
    | EC_assign_right e2 :: ks' =>
      Some (E0, (C, s, mem, EC_assign_left v :: ks', e2))
    | EC_assign_left v' :: ks' =>
      match v with
      | Ptr (C',b',o') =>
        if C =? C' then
          match Memory.store mem (C',b',o') v' with
          | Some mem' => Some (E0, (C, s, mem', ks', E_val v'))
          | None => None
          end
        else
          None
      | _ => None
      end
    | EC_call C' P :: ks' =>
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
                    Some (t, (C', (C, old_call_arg, ks') :: s, mem', [], P_expr))
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
    | [] =>
      match v, s with
      | Int i, (C',old_call_arg,ks) :: s' =>
        (* restore the old call argument *)
        match NMap.find C' (genv_buffers G) with
        | Some b =>
          match Memory.store mem (C',b,0) old_call_arg with
          | Some mem' =>
            let t := [ERet C i C'] in
            Some (t, (C', s', mem', ks, E_val (Int i)))
          | None => None
          end
        | None => None
        end
      | _, _ => None
      end
    end
  | _ => None
  end.

Theorem step_implies_eval_step:
  forall G st t st',
    step G st t st' -> eval_step G st =  Some (t, st').
Proof.
  intros G st t st' Hstep.
  inversion Hstep; subst; simpl; auto.
  (* if expressions *)
  - apply beq_nat_false_iff in H.
    destruct i eqn:Hi; auto.
    + inversion H.
  (* local buffers *)
  - rewrite H. auto.
  (* memory allocs *)
  - rewrite H. auto.
  (* memory loads *)
  - unfold Memory.load in H.
    destruct (NMap.find (elt:=ComponentMemory.t) C' mem) eqn:HC'mem.
    + rewrite H. auto.
    + inversion H.
  (* memory stores *)
  - rewrite <- beq_nat_refl.
    unfold Memory.store in H0.
    destruct (NMap.find (elt:=ComponentMemory.t) C' mem) eqn:HC'mem.
    + rewrite H0. auto.
    + inversion H0.
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
    + unfold st'0. rewrite H. rewrite <- beq_nat_refl.
      rewrite orb_true_r. auto.
  - rewrite H, H0, H1, H3.
    unfold Memory.load in H2.
    destruct (NMap.find (elt:=ComponentMemory.t) C mem) eqn:HCmem.
    + rewrite H2.
      unfold Memory.store in H4.
      destruct (NMap.find (elt:=ComponentMemory.t) C' mem) eqn:HC'mem.
      * inversion HCmem. subst. rewrite H4. auto.
      * inversion H4.
    + inversion H2.
  - rewrite H.
    unfold Memory.store in H0.
    destruct (NMap.find (elt:=ComponentMemory.t) C' mem) eqn:HC'mem.
    + rewrite H0. auto.
    + inversion H0.
Qed.

Theorem step_determinism:
  forall G st t st1 st2,
    step G st t st1 -> step G st t st2 -> st1 = st2.
Proof.
  intros G st t st1 st2 Hstep1 Hstep2.
  apply step_implies_eval_step in Hstep1.
  apply step_implies_eval_step in Hstep2.
  rewrite Hstep1 in Hstep2.
  inversion Hstep2.
  auto.
Qed.