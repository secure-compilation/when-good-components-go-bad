(** * Stage 1 — the reshaped Transitional semantics.

    See plan-i2t-redo.md §4 (Stage 1). This is a NEW file: [Transitional.v] is
    imported by [I2T_Correct.v], which is still in the build, so the reshaping
    happens here rather than in place. Nothing existing is modified.

    What changes, and why:

    1. **No stack.** [TS.state] is [Transitional.stackless]. [Transitional.state]
       carries a [list Pointer.t] that is pushed at [Call], never popped, and
       never read — an inherited [gps] field from [Intermediate/CS.v] that the
       port to an [R_RA] discipline left behind. It is NOT promoted to a ghost:
       §2.2 of the plan explains why (as enforcement it would make T stronger
       than the target and push the real theorem into Pass 2; as a ghost it is
       circular, since it would need "ghost head = R_RA", which is the theorem).

    2. **[Load] fixed.** [Transitional.step]'s [Load] writes the loaded cell back
       with [tvtag := Other] while [Transitional.eval_step] writes [ts']. The
       policy decides it: [LRC.instr_rules]' LOAD does
       [let (ts', td') := switch_val ts ts'], and [switch_val m v] replaces the
       cell's tag by [v] and hands the cell's OLD tag to the destination
       register. So the cell takes [ts'] — [eval_step] is right, the relational
       rule was wrong. (This is plan §3.1.)

    3. **[check_pc] added to [eval_step].** [check_pc] is the T-level shadow of
       the policy's [tni] argument: [LRC.instr_rules] receives the NEXT
       instruction cell's tag and every non-control opcode threads
       [check_belong current tni]. [Transitional.eval_step] omits it entirely,
       so it accepts runs the policy rejects. (Plan §3.2.)

    4. **[check_pc] added to both [Bnz] rules.** [Transitional.step] has it on
       [Nop/Label/Const/Mov/BinOp/Load/Store/Alloc] but not on [BnzZ]/[BnzNZ],
       even though LRC's BNZ rule does [check_belong current tni] like the
       others. Judgment call, flagged for Pass 2 to confirm against the MP
       machine's computation of [tni].

    The deliverable is [step_eval]: the relational and executable semantics
    agree. That is what "keep them in step with each other" means, and it is
    what makes the target DETERMINATE — a premise of
    [forward_to_backward_simulation], hence of [H_bwd_src] (plan §2.1). *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Intermediate.Machine.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Require Import Lib.Monads.
Import MonadNotations.
Open Scope monad_scope.

Require Import Coq.ZArith.ZArith.
Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.

Module TS.

Notation code := Transitional.code.
Notation tcode := (seq (Transitional.instr * mem_tag)).

(** The state: [Transitional.stackless]. No [gps], no ghost. *)
Definition state : Type := Transitional.stackless.

(* ================================================================== *)
(* [check_pc], decided                                                *)
(* ================================================================== *)

(** [check_pc cde pc tg] holds exactly when the cell at [Pointer.inc pc] exists
    in [pc]'s component. Deciding it is what lets [eval_step] enforce it. *)
Definition has_next (cde : code) (pc : Pointer.t) : bool :=
  let pc' := Pointer.inc pc in
  match cde (Pointer.component pc') with
  | Some C_code =>
      if (0 <=? Pointer.offset pc')%Z
      then if nth_error C_code (Z.to_nat (Pointer.offset pc')) is Some _
           then true else false
      else false
  | None => false
  end.

Lemma has_nextP cde pc tg :
  has_next cde pc -> Transitional.check_pc cde pc tg.
Proof.
  rewrite /has_next.
  case E: (cde (Pointer.component (Pointer.inc pc))) => [C_code|] //.
  case E0: (0 <=? Pointer.offset (Pointer.inc pc))%Z => //.
  case E1: (nth_error C_code _) => [[i tni]|] // _.
  apply: (@PcFall cde pc tg i tni (Pointer.component (Pointer.inc pc))).
  exists C_code. split; first by []. split; first by [].
  split; last exact: E1.
  by move: E0 => /Z.leb_le; lia.
Qed.

Lemma has_nextPn cde pc tg :
  Transitional.check_pc cde pc tg -> has_next cde pc.
Proof.
  case=> {}cde {}pc {}tg i tni c [C_code [Ec [Eg [Eo En]]]].
  rewrite /has_next Ec Eg.
  have -> : (0 <=? Pointer.offset (Pointer.inc pc))%Z = true
    by apply/Z.leb_le; lia.
  by rewrite En.
Qed.

(* ================================================================== *)
(* The relational semantics                                           *)
(* ================================================================== *)

(** ⚠ DEFECT (plan §3.6, found 2026-07-29 by the Stage-0 harness).
    [Transitional]'s cross-return uses [Register.invalidate], which KEEPS
    [R_RA]'s tvalue verbatim — so the just-CONSUMED return capability survives
    as a live-looking [Ret n] at [Level n]. The MP machine does not do that:
    [LRC.instr_rules]' JUMP return case outputs
    [(Invalidated :: Invalidated :: Other :: reg_invalidate_hseq)], and the
    first of those positions is the one JAL creates the capability at. So MP
    kills the spent capability and T must too, or T carries a capability MP has
    already destroyed — which would break Pass 2. *)
Definition invalidate_ret (rs : Transitional.Register.t)
  : Transitional.Register.t :=
  Transitional.Register.set R_RA
    (Transitional.val (Transitional.Register.get R_RA rs)) Invalidated
    (Transitional.Register.invalidate rs).

Inductive step (cde : code) : state -> trace -> state -> Prop :=
| Nop : forall mem regs pc tg c pct,
    Transitional.executing cde pc TrNop tg c ->
    Transitional.check_pc cde pc tg ->
    step cde (mem, regs, pc, pct) E0 (mem, regs, Pointer.inc pc, pct)

| Label : forall mem regs pc tg c pct l,
    Transitional.executing cde pc (TrLabel l) tg c ->
    Transitional.check_pc cde pc tg ->
    step cde (mem, regs, pc, pct) E0 (mem, regs, Pointer.inc pc, pct)

| Const : forall mem regs pc tg c pct r v,
    Transitional.executing cde pc (TrConst v r) tg c ->
    Transitional.check_pc cde pc tg ->
    step cde (mem, regs, pc, pct) E0
      (mem, Transitional.Register.set r (imm_to_val v) Other regs,
       Pointer.inc pc, pct)

| Mov : forall mem regs pc tg c pct r1 r2,
    Transitional.executing cde pc (TrMov r1 r2) tg c ->
    Transitional.check_pc cde pc tg ->
    step cde (mem, regs, pc, pct) E0
      (mem,
       Transitional.Register.set r1
         (Transitional.val (Transitional.Register.get r1 regs))
         (if is_address (tvtag (Transitional.Register.get r1 regs))
          then Invalidated else Other)
         (Transitional.Register.set r2
            (Transitional.val (Transitional.Register.get r1 regs))
            (tvtag (Transitional.Register.get r1 regs)) regs),
       Pointer.inc pc, pct)

| BinOp : forall mem regs pc tg c pct r1 r2 r3 op,
    Transitional.executing cde pc (TrBinOp op r1 r2 r3) tg c ->
    Transitional.check_pc cde pc tg ->
    tvtag (Transitional.Register.get r1 regs) = Other ->
    tvtag (Transitional.Register.get r2 regs) = Other ->
    step cde (mem, regs, pc, pct) E0
      (mem,
       Transitional.Register.set r3
         (eval_binop op (Transitional.val (Transitional.Register.get r1 regs))
                        (Transitional.val (Transitional.Register.get r2 regs)))
         Other regs,
       Pointer.inc pc, pct)

(* NB the cell is written back with [tvtag := ts'], matching [eval_step] and
   [LRC.instr_rules]' [switch_val] — NOT [Other] as [Transitional.step] had. *)
| Load : forall mem mem' regs pc tg c pct r1 r2 ptr v,
    Transitional.executing cde pc (TrLoad r1 r2) tg c ->
    Transitional.check_pc cde pc tg ->
    tvtag (Transitional.Register.get r1 regs) = Other ->
    Transitional.val (Transitional.Register.get r1 regs) = Ptr ptr ->
    Pointer.component ptr = c ->
    Transitional.Memory.load mem ptr = Some v ->
    Transitional.Memory.store mem ptr
      ({| Transitional.val := Transitional.val v.1;
          tvtag := if is_address (tvtag v.1) then Invalidated else Other |},
       {| vtag := if is_address (tvtag v.1) then Invalidated else Other;
          color := c; entry := None; is_code := false |}) = Some mem' ->
    step cde (mem, regs, pc, pct) E0
      (mem',
       Transitional.Register.set r2 (Transitional.val v.1) (tvtag v.1) regs,
       Pointer.inc pc, pct)

| Store : forall mem mem' regs pc tg c pct ptr r1 r2 vt,
    Transitional.executing cde pc (TrStore r1 r2) tg c ->
    Transitional.check_pc cde pc tg ->
    tvtag (Transitional.Register.get r1 regs) = Other ->
    Transitional.val (Transitional.Register.get r1 regs) = Ptr ptr ->
    Pointer.component ptr = c ->
    Transitional.Register.get_tag r2 regs = Some vt ->
    Transitional.Memory.store mem ptr
      (Transitional.Register.get r2 regs,
       {| vtag := vt; color := c; entry := None; is_code := false |})
      = Some mem' ->
    step cde (mem, regs, pc, pct) E0
      (mem',
       Transitional.Register.set r2
         (Transitional.val (Transitional.Register.get r2 regs))
         (if is_address vt then Invalidated else Other) regs,
       Pointer.inc pc, pct)

| Jal : forall mem regs pc tg c pct pc' l,
    Transitional.executing cde pc (TrJalNat l) tg c ->
    Transitional.find_label_in_comp cde c l = Some pc' ->
    Transitional.check_pc_jump cde tg pc' c ->
    step cde (mem, regs, pc, pct) E0
      (mem,
       Transitional.Register.set R_RA (Ptr (Pointer.inc pc)) InternalJump regs,
       pc', pct)

| Jump : forall mem regs pc tg c pct pc' r,
    Transitional.executing cde pc (TrJump r) tg c ->
    Transitional.Register.get r regs = MVal InternalJump (Ptr pc') ->
    Pointer.component pc' = Pointer.component pc ->
    Transitional.check_pc_jump cde tg pc' c ->
    step cde (mem, regs, pc, pct) E0 (mem, regs, pc', pct)

| JumpRet : forall mem regs pc tg c pct pc' r rcomval,
    Transitional.executing cde pc (TrJump r) tg c ->
    Transitional.val (Transitional.Register.get r regs) = Ptr pc' ->
    Pointer.component pc' <> Pointer.component pc ->
    Some pct = value_to_pc_tag (tvtag (Transitional.Register.get r regs)) ->
    Transitional.val (Transitional.Register.get R_COM regs) = Int rcomval ->
    Transitional.check_pc_jump cde tg pc' (Pointer.component pc') ->
    step cde (mem, regs, pc, pct)
      [ERet (Pointer.component pc) rcomval (Pointer.component pc')]
      (mem, invalidate_ret regs, pc', dec_pc_tag pct)

(* [check_pc] added on BOTH Bnz rules: LRC's BNZ threads
   [check_belong current tni] exactly like the other non-control opcodes. *)
| BnzNZ : forall mem regs pc tg c pct pc' r l v,
    Transitional.executing cde pc (TrBnz r l) tg c ->
    Transitional.check_pc cde pc tg ->
    tvtag (Transitional.Register.get r regs) = Other ->
    Transitional.val (Transitional.Register.get r regs) = Int v ->
    (v <> 0)%Z ->
    Transitional.find_label_in_comp cde c l = Some pc' ->
    Transitional.check_pc_jump cde tg pc' c ->
    step cde (mem, regs, pc, pct) E0 (mem, regs, pc', pct)

| BnzZ : forall mem regs pc tg c pct r l,
    Transitional.executing cde pc (TrBnz r l) tg c ->
    Transitional.check_pc cde pc tg ->
    tvtag (Transitional.Register.get r regs) = Other ->
    Transitional.val (Transitional.Register.get r regs) = Int 0 ->
    step cde (mem, regs, pc, pct) E0 (mem, regs, Pointer.inc pc, pct)

| Alloc : forall mem mem' regs pc tg c pct rsize rptr size ptr,
    Transitional.executing cde pc (TrAlloc rptr rsize) tg c ->
    Transitional.check_pc cde pc tg ->
    tvtag (Transitional.Register.get rsize regs) = Other ->
    Transitional.val (Transitional.Register.get rsize regs) = Int size ->
    (size > 0)%Z ->
    Transitional.Memory.alloc mem c (Z.to_nat size) = Some (mem', ptr) ->
    step cde (mem, regs, pc, pct) E0
      (mem', Transitional.Register.set rptr (Ptr ptr) Other regs,
       Pointer.inc pc, pct)

| Call : forall mem regs pc tg c pct pc' i tni c' pid call_arg n,
    Transitional.executing cde pc (TrJalProc (c', pid)) tg c ->
    Transitional.find_plabel_in_code cde c' pid = Some pc' ->
    Transitional.executing cde pc' i tni c' ->
    c <> c' ->
    Transitional.check_pc_call c tni pid ->
    pct = Level n ->
    Transitional.val (Transitional.Register.get R_COM regs) = Int call_arg ->
    step cde (mem, regs, pc, pct) [ECall c pid call_arg c']
      (mem,
       Transitional.Register.set R_RA (Ptr (Pointer.inc pc)) (Ret n)
         (Transitional.Register.invalidate regs),
       pc', inc_pc_tag pct).

(* ================================================================== *)
(* The executable semantics                                           *)
(* ================================================================== *)

(** [Transitional.eval_step] with [has_next] guards on every non-control
    opcode (plan §3.2 / point 3 above), and with [Bnz] guarded too (point 4). *)
Definition eval_step (cde : code) (s : state) : option (trace * state) :=
  let '(mem, regs, pc, pct) := s in
  if (Pointer.offset pc <? 0)%Z then None
  else
    do C_code <- cde (Pointer.component pc);
    do (i, tag) <- nth_error C_code (Z.to_nat (Pointer.offset pc));
    let fall r := if has_next cde pc then Some (E0, r) else None in
    match i with
    | TrLabel _ => fall (mem, regs, Pointer.inc pc, pct)
    | TrNop => fall (mem, regs, Pointer.inc pc, pct)
    | TrConst v r =>
        fall (mem, Transitional.Register.set r (imm_to_val v) Other regs,
              Pointer.inc pc, pct)
    | TrMov r1 r2 =>
        let tv := Transitional.Register.get r1 regs in
        let ts' := if is_address (tvtag tv) then Invalidated else Other in
        fall (mem,
              Transitional.Register.set r1 (Transitional.val tv) ts'
                (Transitional.Register.set r2 (Transitional.val tv) (tvtag tv)
                   regs),
              Pointer.inc pc, pct)
    | TrBinOp op r1 r2 r3 =>
        match tvtag (Transitional.Register.get r1 regs),
              tvtag (Transitional.Register.get r2 regs) with
        | Other, Other =>
            fall (mem,
                  Transitional.Register.set r3
                    (eval_binop op
                       (Transitional.val (Transitional.Register.get r1 regs))
                       (Transitional.val (Transitional.Register.get r2 regs)))
                    Other regs,
                  Pointer.inc pc, pct)
        | _, _ => None
        end
    | TrLoad r1 r2 =>
        match Transitional.Register.get r1 regs with
        | MVal Other (Ptr ptr) =>
            let c := Pointer.component ptr in
            if Component.eqb c (Pointer.component pc) then
              do v <- Transitional.Memory.load mem ptr;
              let ts' := if is_address (tvtag v.1) then Invalidated else Other in
              do mem' <- Transitional.Memory.store mem ptr
                   ({| Transitional.val := Transitional.val v.1;
                       tvtag := ts' |},
                    {| vtag := ts'; color := c; entry := None;
                       is_code := false |});
              fall (mem',
                    Transitional.Register.set r2 (Transitional.val v.1)
                      (tvtag v.1) regs,
                    Pointer.inc pc, pct)
            else None
        | _ => None
        end
    | TrStore r1 r2 =>
        match Transitional.Register.get r1 regs with
        | MVal Other (Ptr ptr) =>
            let c := Pointer.component ptr in
            if Component.eqb c (Pointer.component pc) then
              do vt <- Transitional.Register.get_tag r2 regs;
              do mem' <- Transitional.Memory.store mem ptr
                   (Transitional.Register.get r2 regs,
                    {| vtag := vt; color := c; entry := None;
                       is_code := false |});
              let ts' := if is_address vt then Invalidated else Other in
              fall (mem',
                    Transitional.Register.set r2
                      (Transitional.val (Transitional.Register.get r2 regs))
                      ts' regs,
                    Pointer.inc pc, pct)
            else None
        | _ => None
        end
    | TrAlloc rptr rsize =>
        match Transitional.Register.get rsize regs with
        | MVal Other (Int size) =>
            if (size <=? 0)%Z then None
            else
              do (mem', ptr) <- Transitional.Memory.alloc mem
                                  (Pointer.component pc) (Z.to_nat size);
              fall (mem', Transitional.Register.set rptr (Ptr ptr) Other regs,
                    Pointer.inc pc, pct)
        | _ => None
        end
    | TrBnz r l =>
        match Transitional.Register.get r regs with
        | MVal Other (Int 0) => fall (mem, regs, Pointer.inc pc, pct)
        | MVal Other (Int _) =>
            if has_next cde pc then
              do pc' <- Transitional.find_label_in_comp cde
                          (Pointer.component pc) l;
              Some (E0, (mem, regs, pc', pct))
            else None
        | _ => None
        end
    | TrJump r =>
        match Transitional.Register.get r regs with
        | MVal tag (Ptr pc') =>
            if Component.eqb (Pointer.component pc') (Pointer.component pc)
            then match tag with
                 | InternalJump => Some (E0, (mem, regs, pc', pct))
                 | _ => None
                 end
            else
              match tag, pct with
              | Ret n, Level m =>
                  if ((Pointer.offset pc' <? 0)%Z
                      || negb (ssrnat.eqn (S n) m))%bool then None
                  else
                    do C_code' <- cde (Pointer.component pc');
                    do ni <- nth_error C_code' (Z.to_nat (Pointer.offset pc'));
                    match Transitional.val
                            (Transitional.Register.get R_COM regs) with
                    | Int rcomval =>
                        Some ([ERet (Pointer.component pc) rcomval
                                 (Pointer.component pc')],
                              (mem, invalidate_ret regs, pc',
                               dec_pc_tag pct))
                    | _ => None
                    end
              | _, _ => None
              end
        | _ => None
        end
    | TrJalNat l =>
        do pc' <- Transitional.find_label_in_comp cde (Pointer.component pc) l;
        Some (E0, (mem,
                   Transitional.Register.set R_RA (Ptr (Pointer.inc pc))
                     InternalJump regs, pc', pct))
    | TrJalProc (c', pid) =>
        match Transitional.find_plabel_in_code cde c' pid with
        | Some pc' =>
            if Component.eqb (Pointer.component pc') (Pointer.component pc)
            then None
            else
              if (Pointer.offset pc' <? 0)%Z then None
              else
                do C_code' <- cde (Pointer.component pc');
                do nt <- nth_error C_code' (Z.to_nat (Pointer.offset pc'));
                match entry nt.2 with
                | Some (pid', lc) =>
                    if (Procedure.eqb pid pid'
                        && check_comp_belongs_b (Pointer.component pc) lc)%bool
                    then
                      match Transitional.val
                              (Transitional.Register.get R_COM regs), pct with
                      | Int rcomval, Level n =>
                          Some ([ECall (Pointer.component pc) pid rcomval
                                   (Pointer.component pc')],
                                (mem,
                                 Transitional.Register.set R_RA
                                   (Ptr (Pointer.inc pc)) (Ret n)
                                   (Transitional.Register.invalidate regs),
                                 pc', inc_pc_tag pct))
                      | _, _ => None
                      end
                    else None
                | _ => None
                end
        | None => None
        end
    | TrHalt => None
    end.

(* ================================================================== *)
(* Agreement: the relational and executable semantics coincide        *)
(* ================================================================== *)

(** Inversion helpers: casing these inductives directly fails when their
    indices are already in scope. *)
Lemma check_pc_jumpE cde tg pc' c0 :
  Transitional.check_pc_jump cde tg pc' c0 ->
  exists i tni c C_code,
    [/\ Pointer.component pc' = c, cde c = Some C_code,
        (Pointer.offset pc' >= 0)%Z
      & nth_error C_code (Z.to_nat (Pointer.offset pc')) = Some (i, tni)].
Proof.
  case=> {}cde {}tg {}pc' i tni c c1 [Cc [Ec [Eg [Eo En]]]] _.
  by exists i, tni, c, Cc.
Qed.

Lemma check_pc_callE c tni pid :
  Transitional.check_pc_call c tni pid ->
  exists l, entry tni = Some (pid, l) /\ check_comp_belongs c l.
Proof. case=> {}c {}tni {}pid l H1 H2. by exists l. Qed.

Lemma check_comp_belongsP c l :
  check_comp_belongs c l -> check_comp_belongs_b c l.
Proof.
  elim: l => //= x xs IH [->|H]; first by rewrite Nat.eqb_refl.
  by case: (Nat.eqb c x); [| exact: IH].
Qed.

(** Shared prologue: an [executing] hypothesis reduces [eval_step] past the
    fetch. *)
Ltac fetch :=
  match goal with
  | H : Transitional.executing _ ?pc _ _ _ |- _ =>
      let Cc := fresh "Cc" in let Ec := fresh "Ec" in let Eg := fresh "Eg" in
      let Eo := fresh "Eo" in let En := fresh "En" in
      case: H => [Cc [Ec [Eg [Eo En]]]];
      rewrite /eval_step Ec Eg;
      (have -> : (Pointer.offset pc <? 0)%Z = false
         by apply/Z.ltb_ge; lia);
      rewrite /= En /=
  end.

(** [check_pc] discharges the [has_next] guard. *)
Ltac hasnext :=
  match goal with
  | H : Transitional.check_pc _ _ _ |- _ => rewrite (has_nextPn H) //
  end.

Theorem step_eval cde s t s' :
  step cde s t s' -> eval_step cde s = Some (t, s').
Proof.
  case=> {s t s'}.
  - (* Nop *) move=> mem regs pc tg c pct Hex Hpc. fetch. by hasnext.
  - (* Label *) move=> mem regs pc tg c pct l Hex Hpc. fetch. by hasnext.
  - (* Const *) move=> mem regs pc tg c pct r v Hex Hpc. fetch. by hasnext.
  - (* Mov *) move=> mem regs pc tg c pct r1 r2 Hex Hpc. fetch. by hasnext.
  - (* BinOp *) move=> mem regs pc tg c pct r1 r2 r3 op Hex Hpc H1 H2.
    fetch. rewrite H1 H2. by hasnext.
  - (* Load *) move=> mem mem' regs pc tg c pct r1 r2 ptr v Hex Hpc Ht Hv Hcp
      Hld Hst.
    fetch.
    move: Ht Hv. case: (Transitional.Register.get r1 regs) => [vt vv] /= -> ->.
    rewrite Hcp /Component.eqb Nat.eqb_refl Hld /= Hst /=. by hasnext.
  - (* Store *) move=> mem mem' regs pc tg c pct ptr r1 r2 vt Hex Hpc Ht Hv Hcp
      Htg Hst.
    fetch.
    move: Ht Hv. case: (Transitional.Register.get r1 regs) => [t1 v1] /= -> ->.
    rewrite Hcp /Component.eqb Nat.eqb_refl Htg /= Hst /=. by hasnext.
  - (* Jal *) move=> mem regs pc tg c pct pc' l Hex Hlab Hj.
    fetch. by rewrite Hlab.
  - (* Jump *) move=> mem regs pc tg c pct pc' r Hex Hra Hcp Hj.
    fetch. by rewrite Hra /= Hcp Ec /Component.eqb Nat.eqb_refl.
  - (* JumpRet *) move=> mem regs pc tg c pct pc' r rcomval Hex Hv Hne Hpct
      Hcom Hj.
    fetch.
    move: Hv Hpct. case: (Transitional.Register.get r regs) => [vt vv] /= ->.
    case: vt => //= [n] [Epct].
    have Hne' : Component.eqb (Pointer.component pc') c = false
      by apply/Nat.eqb_neq; rewrite -Ec; exact: Hne.
    rewrite Hne' Epct /=.
    case: (check_pc_jumpE Hj) => [i0 [tni0 [c0 [Cc0 [Ec0 Eg0 Eo0 En0]]]]].
    have -> : (Pointer.offset pc' <? 0)%Z = false by apply/Z.ltb_ge; lia.
    by rewrite ssrnat.eqnE eqxx /= Ec0 Eg0 /= En0 /= Hcom.
  - (* BnzNZ *) move=> mem regs pc tg c pct pc' r l v Hex Hpc Ht Hv Hnz Hlab Hj.
    fetch.
    move: Ht Hv. case: (Transitional.Register.get r regs) => [vt vv] /= -> ->.
    case: v Hnz => [|p|p] //= _; rewrite (has_nextPn Hpc) // Hlab //.
  - (* BnzZ *) move=> mem regs pc tg c pct r l Hex Hpc Ht Hv.
    fetch.
    move: Ht Hv. case: (Transitional.Register.get r regs) => [vt vv] /= -> ->.
    by hasnext.
  - (* Alloc *) move=> mem mem' regs pc tg c pct rsize rptr size ptr Hex Hpc Ht
      Hv Hsz Hal.
    fetch.
    move: Ht Hv. case: (Transitional.Register.get rsize regs) => [vt vv] /= -> ->.
    have -> : (size <=? 0)%Z = false by apply/Z.leb_gt; lia.
    rewrite Hal /=. by hasnext.
  - (* Call *) move=> mem regs pc tg c pct pc' i tni c' pid call_arg n Hex Hlab
      Hex' Hne Hcall Hpct Hcom.
    fetch.
    rewrite Hlab.
    case: Hex' => [Cc' [Ec' [Eg' [Eo' En']]]].
    have Hne' : Component.eqb (Pointer.component pc') c = false.
    { apply/Nat.eqb_neq. rewrite Ec' => H. by apply: Hne; rewrite H. }
    rewrite Hne'.
    have -> : (Pointer.offset pc' <? 0)%Z = false by apply/Z.ltb_ge; lia.
    rewrite Ec' Eg' /= En' /=.
    case: (check_pc_callE Hcall) => [lc [Hent Hbel]].
    rewrite Hent /Procedure.eqb Nat.eqb_refl /=.
    have -> : check_comp_belongs_b c lc = true
      by apply: check_comp_belongsP.
    by rewrite Hcom Hpct.
Qed.

(** Determinacy of the target — a premise of [forward_to_backward_simulation],
    hence of [H_bwd_src] (plan §2.1). *)
Corollary step_deterministic cde s t1 s1 t2 s2 :
  step cde s t1 s1 -> step cde s t2 s2 -> t1 = t2 /\ s1 = s2.
Proof.
  move=> /step_eval H1 /step_eval H2.
  by move: H1; rewrite H2 => -[-> ->].
Qed.

End TS.
