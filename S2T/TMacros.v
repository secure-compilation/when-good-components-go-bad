Require Import Common.Definitions.
Require Import Common.Values.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.
Require Import S2T.TMem.
Require Import S2T.TInv.
Require Import S2T.TLabel.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Require Import Coq.ZArith.ZArith.
Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.

Module TMacros.

Notation tcode := (seq (Transitional.instr * mem_tag)).

Lemma nth_error_cat_l' {A : Type} (l1 l2 : seq A) :
  List.nth_error (l1 ++ l2) (size l1) = List.nth_error l2 0.
Proof. by elim: l1. Qed.

Section WithCode.

Variable cde : Transitional.code.


Definition code_at (pc : Pointer.t) (c : tcode) : Prop :=
  exists C_code pre post,
    [/\ getm cde (Pointer.component pc) = Some C_code,
        C_code = pre ++ c ++ post
      & Pointer.offset pc = Z.of_nat (size pre)].

Lemma code_at_head pc i tg c :
  code_at pc ((i, tg) :: c) ->
  Transitional.executing cde pc i tg (Pointer.component pc).
Proof.
  move=> [C_code [pre [post [Hg Hc Hoff]]]].
  exists C_code. split; first by []. split; first by [].
  split; first by rewrite Hoff; lia.
  by rewrite Hoff Nat2Z.id Hc nth_error_cat_l'.
Qed.

Lemma code_at_tail pc x c :
  code_at pc (x :: c) -> code_at (Pointer.inc pc) c.
Proof.
  move=> [C_code [pre [post [Hg Hc Hoff]]]].
  exists C_code, (pre ++ [:: x]), post.
  split.
  - by rewrite Pointer.inc_preserves_component.
  - by rewrite Hc -catA.
  - rewrite /Pointer.inc. case: pc Hg Hoff => [[C b] o] /= _ ->.
    by rewrite size_cat /= Nat2Z.inj_add.
Qed.

Lemma check_pc_at pc x y c :
  code_at pc (x :: y :: c) -> Transitional.check_pc cde pc x.2.
Proof.
  move=> H. have H1 := code_at_tail H.
  case: y H H1 => i tg _ /code_at_head Hex.
  by apply: PcFall Hex.
Qed.


Definition code_at_I (C : Component.id) (pc : Pointer.t)
                     (c : Intermediate.Machine.code) : Prop :=
  code_at pc [seq Transitional.instr_to_transitional C i | i <- c].

Lemma code_at_I_head C pc i c :
  code_at_I C pc (i :: c) ->
  Transitional.executing cde pc
    (Transitional.instr_to_transitional C i).1
    (Transitional.instr_to_transitional C i).2 (Pointer.component pc).
Proof.
  rewrite /code_at_I /=.
  by case: (Transitional.instr_to_transitional C i) => x y /code_at_head.
Qed.

Lemma code_at_I_tail C pc i c :
  code_at_I C pc (i :: c) -> code_at_I C (Pointer.inc pc) c.
Proof. rewrite /code_at_I /=. exact: code_at_tail. Qed.

Lemma check_pc_at_I C pc i j c :
  code_at_I C pc (i :: j :: c) ->
  Transitional.check_pc cde pc (Transitional.instr_to_transitional C i).2.
Proof.
  rewrite /code_at_I /=.
  by case: (Transitional.instr_to_transitional C i) => x y /check_pc_at.
Qed.


Definition push_T (C : Component.id) (r : register) : tcode :=
  [seq Transitional.instr_to_transitional C i | i <- push r].

Definition pop_T (C : Component.id) (r : register) : tcode :=
  [seq Transitional.instr_to_transitional C i | i <- pop r].

Lemma code_at_I_push C pc r nxt rest :
  Pointer.component pc = C ->
  code_at_I C pc (push r ++ nxt :: rest) ->
  code_at pc (push_T (Pointer.component pc) r
              ++ Transitional.instr_to_transitional C nxt
                 :: [seq Transitional.instr_to_transitional C i | i <- rest]).
Proof. by move=> Hc; rewrite /code_at_I map_cat /= /push_T Hc. Qed.

Lemma code_at_I_pop C pc r nxt rest :
  Pointer.component pc = C ->
  code_at_I C pc (pop r ++ nxt :: rest) ->
  code_at pc (pop_T (Pointer.component pc) r
              ++ Transitional.instr_to_transitional C nxt
                 :: [seq Transitional.instr_to_transitional C i | i <- rest]).
Proof. by move=> Hc; rewrite /code_at_I map_cat /= /pop_T Hc. Qed.

Lemma code_at_I_label_find C pc c1 l rest :
  code_at_I C pc (c1 ++ ILabel l :: rest) ->
  Pointer.component pc = C ->
  (forall l0 C_code, getm cde C = Some C_code ->
     count (TLabel.is_tlabel l0) C_code <= 1) ->
  exists pcL,
    [/\ Transitional.find_label_in_comp cde C l = Some pcL,
        Pointer.component pcL = C
      & code_at_I C pcL (ILabel l :: rest)].
Proof.
  rewrite /code_at_I map_cat map_cons.
  move=> [C_code [pre [post [Hg Hc Hoff]]]] Hpc Hu.
  set img1 := [seq Transitional.instr_to_transitional C i | i <- c1].
  set imgr := [seq Transitional.instr_to_transitional C i | i <- rest].
  have HgC : getm cde C = Some C_code by rewrite -Hpc.
  have HcL : C_code = (pre ++ img1)
             ++ (Transitional.TrLabel (inl l), def_mem_tag C true)
                :: (imgr ++ post)
    by rewrite Hc -!catA.
  exists (C, 0, Z.of_nat (size (pre ++ img1))). split.
  - exact: (TLabel.find_label_in_comp_at HgC HcL (Hu l _ HgC)).
  - by [].
  - exists C_code, (pre ++ img1), post. by split.
Qed.


Lemma exec_push m rs pc pct r nxt c C0 fb0 sp m' vt :
  code_at pc (push_T (Pointer.component pc) r ++ nxt :: c) ->
  Transitional.Register.get_tag r rs = Some vt ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C0, fb0, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  R_SP <> r -> R_ONE <> r ->
  Pointer.component pc = C0 ->
  Transitional.Memory.store m (C0, fb0, sp)
    (Transitional.Register.get r rs,
     {| vtag := vt; color := C0; entry := None; is_code := false |})
    = Some m' ->
  plus TS.step cde (m, rs, pc, pct) E0
    (m',
     Transitional.Register.set R_SP (Ptr (C0, fb0, (sp + 1)%Z)) Other
       (Transitional.Register.set r
          (Transitional.val (Transitional.Register.get r rs))
          (moved_tag vt) rs),
     Pointer.inc (Pointer.inc pc), pct).
Proof.
  rewrite /push_T /= => Hcode Htag HSP HONE HrSP HrONE Hcomp Hstore.
  have Hc0 : code_at pc
    ((TrStore R_SP r, def_mem_tag (Pointer.component pc) true)
       :: (TrBinOp Add R_SP R_ONE R_SP,
           def_mem_tag (Pointer.component pc) true) :: nxt :: c)
    by exact: Hcode.
  eapply plus_left with (t1 := E0) (t2 := E0); [| | by []].
  - eapply TS.Store.
    + exact: (code_at_head Hc0).
    + exact: (check_pc_at Hc0).
    + by rewrite HSP.
    + by rewrite HSP.
    + by rewrite Hcomp.
    + exact: Htag.
    + by rewrite Hcomp in Hstore *; exact: Hstore.
  - apply: star_one.
    have Hc1 := code_at_tail Hc0.
    set rs1 := Transitional.Register.set r _ _ rs.
    have HSP1 : Transitional.Register.get R_SP rs1
              = MVal Other (Ptr (C0, fb0, sp))
      by rewrite /rs1 TInv.get_set_neq // HSP.
    have HONE1 : Transitional.Register.get R_ONE rs1 = MVal Other (Int 1)
      by rewrite /rs1 TInv.get_set_neq // HONE.
    have -> : Ptr (C0, fb0, (sp + 1)%Z)
            = eval_binop Add
                (Transitional.val (Transitional.Register.get R_SP rs1))
                (Transitional.val (Transitional.Register.get R_ONE rs1))
      by rewrite HSP1 HONE1.
    eapply TS.BinOp.
    + exact: (code_at_head Hc1).
    + exact: (check_pc_at Hc1).
    + by rewrite HSP1.
    + by rewrite HONE1.
Qed.


Lemma push_ra_macro L m rs pc pct nxt c C0 fb0 sp m' t :
  code_at pc (push_T (Pointer.component pc) R_RA ++ nxt :: c) ->
  Pointer.component pc = C0 ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C0, fb0, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  Transitional.Register.get_tag R_RA rs = Some t ->
  TInv.is_live t ->
  ~ List.In (TInv.CMem (C0, fb0, sp)) (TInv.sites L) ->
  Transitional.Memory.store m (C0, fb0, sp)
    (Transitional.Register.get R_RA rs,
     {| vtag := t; color := C0; entry := None; is_code := false |})
    = Some m' ->
  TInv.tag_inv ((TInv.CReg, t) :: L) m rs pct ->
  let rs' := Transitional.Register.set R_SP (Ptr (C0, fb0, (sp + 1)%Z)) Other
               (Transitional.Register.set R_RA
                  (Transitional.val (Transitional.Register.get R_RA rs))
                  (moved_tag t) rs) in
    plus TS.step cde (m, rs, pc, pct) E0
      (m', rs', Pointer.inc (Pointer.inc pc), pct)
    /\ TInv.tag_inv ((TInv.CMem (C0, fb0, sp), t) :: L) m' rs' pct.
Proof.
  move=> Hcode Hcomp HSP HONE Htag Hlive Hfresh Hstore HI.
  have Et : tvtag (Transitional.Register.get R_RA rs) = t.
  { move: Htag.
    rewrite /Transitional.Register.get_tag /Transitional.Register.get.
    by case: (getm rs _) => [tv|] //= [] ->. }
  rewrite /=. split.
  - exact: (@exec_push m rs pc pct R_RA nxt c C0 fb0 sp m' t
              Hcode Htag HSP HONE (ltac:(by [])) (ltac:(by []))
              Hcomp Hstore).
  - apply: TInv.tag_inv_setreg; first by [].
    exact: (TInv.tag_inv_push_ra Et Hfresh Hstore HI).
Qed.

Lemma exec_pop m rs pc pct r nxt c C0 fb0 sp v m' :
  code_at pc (pop_T (Pointer.component pc) r ++ nxt :: c) ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C0, fb0, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  Pointer.component pc = C0 ->
  Transitional.Memory.load m (C0, fb0, (sp - 1)%Z) = Some v ->
  Transitional.Memory.store m (C0, fb0, (sp - 1)%Z)
    ({| Transitional.val := Transitional.val v.1;
        tvtag := moved_tag (tvtag v.1) |},
     {| vtag := moved_tag (tvtag v.1);
        color := C0; entry := None; is_code := false |}) = Some m' ->
  plus TS.step cde (m, rs, pc, pct) E0
    (m',
     Transitional.Register.set r (Transitional.val v.1) (tvtag v.1)
       (Transitional.Register.set R_SP (Ptr (C0, fb0, (sp - 1)%Z)) Other rs),
     Pointer.inc (Pointer.inc pc), pct).
Proof.
  rewrite /pop_T /= => Hcode HSP HONE Hcomp Hload Hstore.
  have Hc0 : code_at pc
    ((TrBinOp Minus R_SP R_ONE R_SP,
      def_mem_tag (Pointer.component pc) true)
       :: (TrLoad R_SP r, def_mem_tag (Pointer.component pc) true)
       :: nxt :: c) by exact: Hcode.
  have Hcomp1 : Pointer.component (Pointer.inc pc) = C0
    by rewrite Pointer.inc_preserves_component.
  eapply plus_left with (t1 := E0) (t2 := E0); [| | by []].
  - eapply TS.BinOp.
    + exact: (code_at_head Hc0).
    + exact: (check_pc_at Hc0).
    + by rewrite HSP.
    + by rewrite HONE.
  - rewrite HSP HONE /=.
    apply: star_one.
    have Hc1 := code_at_tail Hc0.
    eapply TS.Load.
    + exact: (code_at_head Hc1).
    + exact: (check_pc_at Hc1).
    + by rewrite TInv.get_set_eq.
    + by rewrite TInv.get_set_eq.
    + by rewrite /= Hcomp1.
    + exact: Hload.
    + by rewrite Hcomp1; exact: Hstore.
Qed.

Lemma pop_ra_macro L m rs pc pct nxt c C0 fb0 sp v m' :
  code_at pc (pop_T (Pointer.component pc) R_RA ++ nxt :: c) ->
  Pointer.component pc = C0 ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C0, fb0, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  TInv.is_live (tvtag v.1) ->
  ~ List.In TInv.CReg (TInv.sites L) ->
  Transitional.Memory.load m (C0, fb0, (sp - 1)%Z) = Some v ->
  Transitional.Memory.store m (C0, fb0, (sp - 1)%Z)
    ({| Transitional.val := Transitional.val v.1; tvtag := moved_tag (tvtag v.1) |},
     {| vtag := moved_tag (tvtag v.1); color := C0; entry := None; is_code := false |})
    = Some m' ->
  TInv.tag_inv ((TInv.CMem (C0, fb0, (sp - 1)%Z), tvtag v.1) :: L) m rs pct ->
  let rs' := Transitional.Register.set R_RA (Transitional.val v.1) (tvtag v.1)
               (Transitional.Register.set R_SP
                  (Ptr (C0, fb0, (sp - 1)%Z)) Other rs) in
    plus TS.step cde (m, rs, pc, pct) E0
      (m', rs', Pointer.inc (Pointer.inc pc), pct)
    /\ TInv.tag_inv ((TInv.CReg, tvtag v.1) :: L) m' rs' pct.
Proof.
  move=> Hcode Hcomp HSP HONE Hlive HnotReg Hload Hstore HI.
  rewrite /=. split.
  - eapply exec_pop;
      [exact: Hcode | exact: HSP | exact: HONE | exact: Hcomp
      | exact: Hload | exact: Hstore].
  - apply: (TInv.tag_inv_pop_ra Hlive HnotReg Hload Hstore).
    by apply: TInv.tag_inv_setreg.
Qed.


Lemma push_data_macro L m rs pc pct r nxt c C0 fb0 sp m' :
  code_at pc (push_T (Pointer.component pc) r ++ nxt :: c) ->
  Pointer.component pc = C0 ->
  r <> R_RA -> R_SP <> r -> R_ONE <> r ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C0, fb0, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  Transitional.Register.get_tag r rs = Some Other ->
  ~ List.In (TInv.CMem (C0, fb0, sp)) (TInv.sites L) ->
  Transitional.Memory.store m (C0, fb0, sp)
    (Transitional.Register.get r rs,
     {| vtag := Other; color := C0; entry := None; is_code := false |})
    = Some m' ->
  TInv.tag_inv L m rs pct ->
  let rs' := Transitional.Register.set R_SP (Ptr (C0, fb0, (sp + 1)%Z)) Other
               (Transitional.Register.set r
                  (Transitional.val (Transitional.Register.get r rs))
                  Other rs) in
    plus TS.step cde (m, rs, pc, pct) E0
      (m', rs', Pointer.inc (Pointer.inc pc), pct)
    /\ TInv.tag_inv L m' rs' pct.
Proof.
  move=> Hcode Hcomp HrRA HSPr HONEr HSP HONE Htag Hfresh Hstore HI.
  have Et : tvtag (Transitional.Register.get r rs) = Other.
  { move: Htag.
    rewrite /Transitional.Register.get_tag /Transitional.Register.get.
    by case: (getm rs _) => [tv|] //= [] ->. }
  rewrite /=. split.
  -
    exact: (@exec_push m rs pc pct r nxt c C0 fb0 sp m' Other
              Hcode Htag HSP HONE HSPr HONEr Hcomp Hstore).
  - apply: TInv.tag_inv_setreg; first by [].
    apply: TInv.tag_inv_setreg; first exact: HrRA.
    apply: (TInv.tag_inv_store_data Hfresh _ Hstore HI).
    by rewrite /= Et.
Qed.

Lemma pop_data_macro L m rs pc pct r nxt c C0 fb0 sp v m' :
  code_at pc (pop_T (Pointer.component pc) r ++ nxt :: c) ->
  Pointer.component pc = C0 ->
  r <> R_RA ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C0, fb0, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  tvtag v.1 = Other ->
  ~ List.In (TInv.CMem (C0, fb0, (sp - 1)%Z)) (TInv.sites L) ->
  Transitional.Memory.load m (C0, fb0, (sp - 1)%Z) = Some v ->
  Transitional.Memory.store m (C0, fb0, (sp - 1)%Z)
    ({| Transitional.val := Transitional.val v.1; tvtag := Other |},
     {| vtag := Other; color := C0; entry := None; is_code := false |})
    = Some m' ->
  TInv.tag_inv L m rs pct ->
  let rs' := Transitional.Register.set r (Transitional.val v.1) Other
               (Transitional.Register.set R_SP
                  (Ptr (C0, fb0, (sp - 1)%Z)) Other rs) in
    plus TS.step cde (m, rs, pc, pct) E0
      (m', rs', Pointer.inc (Pointer.inc pc), pct)
    /\ TInv.tag_inv L m' rs' pct.
Proof.
  move=> Hcode Hcomp HrRA HSP HONE Ev Hfresh Hload Hstore HI.
  have Hstore' : Transitional.Memory.store m (C0, fb0, (sp - 1)%Z)
      ({| Transitional.val := Transitional.val v.1;
          tvtag := moved_tag (tvtag v.1) |},
       {| vtag := moved_tag (tvtag v.1);
          color := C0; entry := None; is_code := false |}) = Some m'
    by rewrite Ev /=; exact: Hstore.
  rewrite /=. split.
  - have H := @exec_pop m rs pc pct r nxt c C0 fb0 sp v m'
                Hcode HSP HONE Hcomp Hload Hstore'.
    rewrite Ev in H. exact: H.
  - apply: (TInv.tag_inv_load_data HrRA Ev Hfresh Hload Hstore).
    by apply: TInv.tag_inv_setreg.
Qed.



End WithCode.

End TMacros.
