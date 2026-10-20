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

Definition state : Type := Transitional.stackless.


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

Lemma has_nextPn cde pc tg :
  Transitional.check_pc cde pc tg -> has_next cde pc.
Proof.
  case=> {}cde {}pc {}tg i tni c [C_code [Ec [Eg [Eo En]]]].
  rewrite /has_next Ec Eg.
  have -> : (0 <=? Pointer.offset (Pointer.inc pc))%Z = true
    by apply/Z.leb_le; lia.
  by rewrite En.
Qed.


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
         (moved_tag (tvtag (Transitional.Register.get r1 regs)))
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

| Load : forall mem mem' regs pc tg c pct r1 r2 ptr v,
    Transitional.executing cde pc (TrLoad r1 r2) tg c ->
    Transitional.check_pc cde pc tg ->
    tvtag (Transitional.Register.get r1 regs) = Other ->
    Transitional.val (Transitional.Register.get r1 regs) = Ptr ptr ->
    Pointer.component ptr = c ->
    Transitional.Memory.load mem ptr = Some v ->
    Transitional.Memory.store mem ptr
      ({| Transitional.val := Transitional.val v.1;
          tvtag := moved_tag (tvtag v.1) |},
       {| vtag := moved_tag (tvtag v.1);
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
         (moved_tag vt) regs,
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
        let ts' := moved_tag (tvtag tv) in
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
              let ts' := moved_tag (tvtag v.1) in
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
              let ts' := moved_tag vt in
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

Ltac hasnext :=
  match goal with
  | H : Transitional.check_pc _ _ _ |- _ => rewrite (has_nextPn H) //
  end.

Theorem step_eval cde s t s' :
  step cde s t s' -> eval_step cde s = Some (t, s').
Proof.
  case=> {s t s'}.
  -  move=> mem regs pc tg c pct Hex Hpc. fetch. by hasnext.
  -  move=> mem regs pc tg c pct l Hex Hpc. fetch. by hasnext.
  -  move=> mem regs pc tg c pct r v Hex Hpc. fetch. by hasnext.
  -  move=> mem regs pc tg c pct r1 r2 Hex Hpc. fetch. by hasnext.
  -  move=> mem regs pc tg c pct r1 r2 r3 op Hex Hpc H1 H2.
    fetch. rewrite H1 H2. by hasnext.
  -  move=> mem mem' regs pc tg c pct r1 r2 ptr v Hex Hpc Ht Hv Hcp
      Hld Hst.
    fetch.
    move: Ht Hv. case: (Transitional.Register.get r1 regs) => [vt vv] /= -> ->.
    rewrite Hcp /Component.eqb Nat.eqb_refl Hld /= Hst /=. by hasnext.
  -  move=> mem mem' regs pc tg c pct ptr r1 r2 vt Hex Hpc Ht Hv Hcp
      Htg Hst.
    fetch.
    move: Ht Hv. case: (Transitional.Register.get r1 regs) => [t1 v1] /= -> ->.
    rewrite Hcp /Component.eqb Nat.eqb_refl Htg /= Hst /=. by hasnext.
  -  move=> mem regs pc tg c pct pc' l Hex Hlab Hj.
    fetch. by rewrite Hlab.
  -  move=> mem regs pc tg c pct pc' r Hex Hra Hcp Hj.
    fetch. by rewrite Hra /= Hcp Ec /Component.eqb Nat.eqb_refl.
  -  move=> mem regs pc tg c pct pc' r rcomval Hex Hv Hne Hpct
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
  -  move=> mem regs pc tg c pct pc' r l v Hex Hpc Ht Hv Hnz Hlab Hj.
    fetch.
    move: Ht Hv. case: (Transitional.Register.get r regs) => [vt vv] /= -> ->.
    case: v Hnz => [|p|p] //= _; rewrite (has_nextPn Hpc) // Hlab //.
  -  move=> mem regs pc tg c pct r l Hex Hpc Ht Hv.
    fetch.
    move: Ht Hv. case: (Transitional.Register.get r regs) => [vt vv] /= -> ->.
    by hasnext.
  -  move=> mem mem' regs pc tg c pct rsize rptr size ptr Hex Hpc Ht
      Hv Hsz Hal.
    fetch.
    move: Ht Hv. case: (Transitional.Register.get rsize regs) => [vt vv] /= -> ->.
    have -> : (size <=? 0)%Z = false by apply/Z.leb_gt; lia.
    rewrite Hal /=. by hasnext.
  -  move=> mem regs pc tg c pct pc' i tni c' pid call_arg n Hex Hlab
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

Corollary step_deterministic cde s t1 s1 t2 s2 :
  step cde s t1 s1 -> step cde s t2 s2 -> t1 = t2 /\ s1 = s2.
Proof.
  move=> /step_eval H1 /step_eval H2.
  by move: H1; rewrite H2 => -[-> ->].
Qed.

End TS.
