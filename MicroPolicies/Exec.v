From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From CoqUtils Require Import hseq word.
From extructures Require Import fmap.
Require Import MicroPolicies.Utils MicroPolicies.Types MicroPolicies.Symbolic.
Require Import CompCert.Events.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Section WithClasses.

Context {mt : machine_types}
  {ops : machine_ops mt}.

Notation vovec_ev tty vop := (Symbolic.vovec tty vop * option event)%type.

Context {ttypes : Symbolic.tag_types}
  {transfer : forall iv : Symbolic.ivec ttypes, Symbolic.ev_inputs -> option (vovec_ev ttypes (Symbolic.op iv)) }
  {internal_state : eqType }.

Variable table : @Symbolic.syscall_table mt ttypes internal_state.

Import Symbolic.

Local Open Scope word_scope.
Local Notation "x .+1" := (x + 1).

Notation next_state_updates_and_pc := (@next_state_updates_and_pc mt ops ttypes transfer internal_state).

Notation next_state_updates := (@next_state_updates mt ops ttypes transfer internal_state).

Definition stepf (st : state ttypes internal_state) :
  option (state ttypes internal_state * option event) :=
  let 'State mem reg pc@tpc extra nc := st in
  match mem pc with
  | Some iti =>
    let: i@ti := iti in
    do! instr <- decode_instr i;
    match instr with
    | Nop =>
      let mvec := IVec NOP tpc ti [hseq] in
      next_state_updates st mvec [:: ]
    | Const n r =>
      do! old <- reg r;
      let: _@told := old in
      let ivec := IVec CONST tpc ti [hseq told] in
      next_state_updates st ivec [:: RegWrite r (swcast n)]
    | Mov r1 r2 =>
      do! a1 <- reg r1;
      let: w1@t1 := a1 in
      do! a2 <- reg r2;
      let: _@told := a2 in
      let mvec := IVec MOV tpc ti [hseq t1;told] in
      next_state_updates st mvec [:: RegRead r1 ; RegWrite r2 w1]
    | Binop op r1 r2 r3 =>
      do! a1 <- reg r1;
      let: w1@t1 := a1 in
      do! a2 <- reg r2;
      let: w2@t2 := a2 in
      do! a3 <- reg r3;
      let: _@told := a3 in
      let mvec := IVec (BINOP op) tpc ti [hseq t1;t2;told] in
      next_state_updates st mvec [:: RegRead r1 ; RegRead r2 ; RegWrite r3 (binop_denote op w1 w2)]
    | Load r1 r2 =>
      do! a1 <- reg r1;
      let: w1@t1 := a1 in
      do! amem <- mem w1;
      let: w2@t2 := amem in
      do! a2 <- reg r2;
      let: _@told := a2 in
      let mvec := IVec LOAD tpc ti [hseq t1;t2;told] in
      next_state_updates st mvec [:: RegRead r1 ; MemRead w1 ; RegWrite r2 w2]
    | Store r1 r2 =>
      do! a1 <- reg r1;
      let: w1@t1 := a1 in
      do! amem <- mem w1;
      let: _@told := amem in
      do! a2 <- reg r2;
      let: w2@t2 := a2 in
      let mvec := IVec STORE tpc ti [hseq t1;t2;told] in
      next_state_updates st mvec [:: RegRead r1 ; RegRead r2 ; MemWrite w1 w2]
    | Jump r =>
      do! a <- reg r;
      let: w@t1 := a in
      do! l <- reg_clear_list reg t1;
      let mvec := IVec JUMP tpc ti l in
      next_state_updates_and_pc st mvec ((RegRead r) :: reg_clear_read) w
    | Bnz r n =>
      do! a <- reg r;
      let: w@t1 := a in
      let pc' := pc + (if w == 0
                       then 1 else swcast n) in
      let ivec := IVec BNZ tpc ti [hseq t1] in
      next_state_updates_and_pc st ivec [:: RegRead r] pc'
    | Jal i =>
      do! oldtold <- reg ra;
      let: _@told := oldtold in
      do! l <- reg_clear_list reg told;
      let mvec := IVec JAL tpc ti l in
      let pc' := swcast i in
      next_state_updates_and_pc st mvec ((RegWrite ra (pc.+1)) :: reg_clear_read) pc'
    | JumpEpc | AddRule | GetTag _ _ | PutTag _ _ _ | Halt =>
      None
    end
  | None =>
    match mem pc with
    | None =>
      do! sc <- table pc;
      @run_syscall _ _ ttypes transfer internal_state sc st
    | Some _ =>
      None
    end
  end.

Lemma stepP :
  forall st st' ev,
    stepf st = Some (st', ev) <->
    @step _ _ _ transfer _ table st st' ev.
Proof.
  intros st st'. split; intros STEP.
  { destruct st as [mem reg [pc tpc] int].
    move: STEP => /=; case GET: (mem pc) => [[i ti]|] //= STEP;
    apply obind_inv in STEP.
    - destruct STEP as (instr & INSTR & STEP).
      destruct instr; try discriminate;
          repeat match goal with
             | STEP : (do! x <- ?t; _) = Some _ |- _ =>
               destruct t eqn:?; simpl in STEP; try discriminate
             | x : atom _ _ |- _ =>
               destruct x; simpl in *
             | rv : ovec _ |- _ =>
               destruct rv; simpl in *
             | H : Some _ = Some _ |- _ =>
               inversion H; subst; clear H
                 end; eauto.
      + econstructor; eauto.
      + eapply step_const; eauto.
      + eapply step_mov; eauto.
      + eapply step_binop; eauto.
      + eapply step_load; eauto.
      + eapply step_store; eauto.
      + eapply step_jump; eauto.
      + eapply step_bnz; eauto.
      + eapply step_jal; eauto.
      + destruct STEP as [sc [SYSCALL RUN]].
        eapply step_syscall; eauto.
  }
  { unfold stepf.
    inversion STEP; subst; rewrite PC; try (subst mv);
    simpl;
    repeat match goal with
             | [H: ?Expr = _ |- context[?Expr]] =>
               rewrite H; simpl
           end; by reflexivity.
  }
Qed.

(* Lemma stepP' : *)
(*   forall st st' ev, *)
(*     reflect (step table st st' ev) (stepf st == Some (st', ev)). *)
(* Proof. *)
(*   move => st st'. *)
(*   apply (iffP eqP); by move => /stepP. *)
(* Qed. *)

Definition build_k_ivec st : option (k_ivec ttypes)  :=
  match mem st (pcv st) with
    | Some i =>
      match decode_instr (vala i) with
        | Some op =>
          let part := @IVec ttypes (opcode_of op) (@pct _ _ internal_state st) (taga i) in
          match op return (hseq (tag_type ttypes) (inputs (opcode_of op)) ->
                           k_ivec ttypes) -> option (k_ivec ttypes) with
            | Nop => fun part => Some (part [hseq])
            | Const n r => fun part =>
                do! old <- regs st r;
                Some (part [hseq taga old])
            | Mov r1 r2 => fun part =>
              do! v1 <- regs st r1;
              do! v2 <- regs st r2;
              Some (part [hseq (taga v1); (taga v2)])
            | Binop _ r1 r2 r3 => fun part =>
              do! v1 <- regs st r1;
              do! v2 <- regs st r2;
              do! v3 <- regs st r3;
              Some (part [hseq (taga v1); (taga v2); (taga v3)])
            | Load  r1 r2 => fun part =>
              do! w1 <- regs st r1;
              do! w2 <- (mem st) (vala w1);
              do! old <- regs st r2;
              Some (part [hseq (taga w1); (taga w2); (taga old)])
            | Store  r1 r2 => fun part =>
              do! w1 <- regs st r1;
              do! w2 <- regs st r2;
              do! w3 <- mem st (vala w1);
              Some (part [hseq (taga w1); (taga w2); (taga w3)])
            | Jump  r => fun part =>
              do! w <- regs st r;
              do! l <- reg_clear_list (regs st) (taga w);
              Some (part l)
            | Bnz  r n => fun part =>
              do! w <- regs st r;
              Some (part [hseq taga w])
            | Jal  r => fun part =>
              do! old <- regs st ra;
              do! l <- reg_clear_list (regs st) (taga old);
              Some (part l)
            | JumpEpc => fun _ => None
            | AddRule => fun _ => None
            | GetTag _ _ => fun _ => None
            | PutTag _ _ _ => fun _ => None
            | Halt => fun _ => None
          end part
        | None => None
      end
    | None =>
      match table (pcv st) with
        | Some sc =>
          Some (IVec SERVICE (pct st) (entry_tag sc) [hseq])
        | None => None
      end
  end.

(* TL TODO: fix proof *)

(* Lemma step_build_ivec st st' : *)
(*   step table st st' -> *)
(*   exists ivec ovec, *)
(*     build_ivec st = Some ivec /\ *)
(*     transfer ivec = Some ovec. *)
(* Proof. *)
(*   move/stepP. *)
(*   rewrite {1}(state_eta st) /= /build_ivec. *)
(*   case: (getm _ _) => [[i ti]|] //=; last first. *)
(*     case: (getm _ _) => [sc|] //=. *)
(*     rewrite /run_syscall /=. *)
(*     case TRANS: (transfer _) => [ovec|] //= _. *)
(*     by eauto. *)
(*   case: (decode_instr i) => [instr|] //=. *)
(*   rewrite /next_state_updates /next_state_reg /next_state_reg_and_pc /next_state. *)
(*   by destruct instr; move=> STEP; match_inv; first [ eauto | discriminate ]. *)
(* Qed. *)

End WithClasses.
