Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Intermediate.Machine.
Require Import S2I.CompMonad.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import S2I.SimInject.
Require Import S2I.Simulation.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.
Require Import S2T.TMem.
Require Import S2T.TInv.
Require Import S2T.TStack.
Require Import S2T.TInject.
Require Import S2T.TMacros.
Require Import S2T.TStackMatch.
Require Import S2T.TMatch.
Require Import S2T.TDrain.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Require Import Coq.ZArith.ZArith.

Set Implicit Arguments.
Unset Strict Implicit.

Module TLeaf.

Notation icode := Intermediate.Machine.code.

Section WithProgram.

Variable cde : Transitional.code.
Variable iface : Program.interface.
Variable labelsP : NMap (NMap label).

Local Notation expr_inv := (TMatch.expr_inv cde iface labelsP).
Local Notation val_inv := (TMatch.val_inv cde iface labelsP).

Lemma compile_val_int C plm v s1 c s2 :
  compile_expr C (lbp C) (scr C) plm (E_val v) s1 = Some (c, s2) ->
  exists i, v = Int i /\ c = [:: IConst (IInt i) R_COM].
Proof. by case: v => [i|ptr|] //= [<- _]; exists i. Qed.

Lemma compile_arg C plm s1 c s2 :
  compile_expr C (lbp C) (scr C) plm E_arg s1 = Some (c, s2) ->
  c = [:: IMov R_ARG R_COM].
Proof. by move=> /= [<- _]. Qed.

Lemma compile_local C plm s1 c s2 :
  compile_expr C (lbp C) (scr C) plm E_local s1 = Some (c, s2) ->
  c = [:: IConst (IPtr (lbp C)) R_COM].
Proof. by move=> /= [<- _]. Qed.

Lemma ei_rest_cons a scrs C stk mem k e arg ret rtag Sl tmem tregs pct pc fb
      prot temps plm c rest s1 s2 cap :
  expr_inv a scrs C stk mem k e arg ret rtag Sl tmem tregs pct pc fb prot
           temps plm c rest s1 s2 cap ->
  exists i r, rest = i :: r.
Proof.
  move=> H. exact: (TDrain.cont_matchJ_cons (TMatch.ei_cont H)).
Qed.


Lemma leaf_val_run a scrs C stk mem k v arg ret rtag Sl tmem tregs pct pc fb
      prot temps plm c rest s1 s2 cap :
  expr_inv a scrs C stk mem k (E_val v) arg ret rtag Sl tmem tregs pct pc fb
           prot temps plm c rest s1 s2 cap ->
  exists i,
    [/\ v = Int i,
        TS.step cde (tmem, tregs, pc, pct) E0
          (tmem, Transitional.Register.set R_COM (Int i) Other tregs,
           Pointer.inc pc, pct)
      & val_inv a scrs C stk mem k v arg ret rtag Sl tmem
          (Transitional.Register.set R_COM (Int i) Other tregs) pct
          (Pointer.inc pc) fb prot temps plm rest cap].
Proof.
  move=> HI.
  have [i0 [r0 Er]] := ei_rest_cons HI.
  have [i [Ev Ec]] := compile_val_int (TMatch.ei_comp HI).
  have Hcode : TMacros.code_at_I cde C pc
                 (IConst (IInt i) R_COM :: i0 :: r0).
  { move: (TMatch.ei_code HI). by rewrite Ec Er. }
  exists i. rewrite Ev. split=> //.
  -
    have -> : Int i = imm_to_val (IInt i) by [].
    eapply TS.Const; [exact: (TMacros.code_at_I_head Hcode)
                     | exact: (TMacros.check_pc_at_I Hcode)].
  - apply: TMatch.ValInv;
    last by eauto using TMatch.ei_anchor, TMatch.vi_anchor.
    + exact: TMatch.ei_plm HI.
    + exact: TMatch.ei_dom HI.
    + exact: TMatch.ei_mem HI.
    + exact: TMatch.ei_scrs HI.
    + by rewrite TInv.get_set_neq //; exact: TMatch.ei_one HI.
    + by rewrite TInv.get_set_neq //; exact: TMatch.ei_sp HI.
    + by rewrite TInv.get_set_neq //; exact: TMatch.ei_arg HI.
    + by rewrite TInv.get_set_eq; exact: VI_int.
    + by rewrite TInv.get_set_neq //; exact: TMatch.ei_ra HI.
    + exact: TMatch.ei_rtag HI.
    + by rewrite Pointer.inc_preserves_component; exact: TMatch.ei_pc HI.
    + by rewrite Er; exact: (TMacros.code_at_I_tail Hcode).
    + exact: TMatch.ei_cont HI.
    + exact: TMatch.ei_uniq HI.
    + exact: TMatch.ei_priv HI.
    + exact: TMatch.ei_scrp HI.
    + exact: TMatch.ei_temps HI.
    + exact: TMatch.ei_cap HI.
    + apply: leq_trans (TMatch.ei_budget HI).
      by rewrite leq_add2l leq_maxr.
    + exact: TMatch.ei_prot HI.
    + exact: TMatch.ei_stack HI.
    + apply: TInv.tag_inv_setreg; first by [].
      exact: TMatch.ei_tag HI.
Qed.


Lemma leaf_arg_run a scrs C stk mem k arg ret rtag Sl tmem tregs pct pc fb
      prot temps plm c rest s1 s2 cap :
  expr_inv a scrs C stk mem k E_arg arg ret rtag Sl tmem tregs pct pc fb
           prot temps plm c rest s1 s2 cap ->
  let tregs' :=
    Transitional.Register.set R_ARG
      (Transitional.val (Transitional.Register.get R_ARG tregs)) Other
      (Transitional.Register.set R_COM
         (Transitional.val (Transitional.Register.get R_ARG tregs))
         Other tregs) in
    TS.step cde (tmem, tregs, pc, pct) E0 (tmem, tregs', Pointer.inc pc, pct)
    /\ val_inv a scrs C stk mem k arg arg ret rtag Sl tmem tregs' pct
         (Pointer.inc pc) fb prot temps plm rest cap.
Proof.
  move=> HI.
  have [i0 [r0 Er]] := ei_rest_cons HI.
  have Ec := compile_arg (TMatch.ei_comp HI).
  have Hcode : TMacros.code_at_I cde C pc (IMov R_ARG R_COM :: i0 :: r0).
  { move: (TMatch.ei_code HI). by rewrite Ec Er. }
  have Ht : tvtag (Transitional.Register.get R_ARG tregs) = Other.
  { apply: (TInv.ti_regs (TMatch.ei_tag HI)). by []. }
  rewrite /=. split.
  -
    move: (TS.Mov tmem tregs pct (TMacros.code_at_I_head Hcode)
                  (TMacros.check_pc_at_I Hcode)).
    rewrite Ht. exact: id.
  - apply: TMatch.ValInv;
    last by eauto using TMatch.ei_anchor, TMatch.vi_anchor.
    + exact: TMatch.ei_plm HI.
    + exact: TMatch.ei_dom HI.
    + exact: TMatch.ei_mem HI.
    + exact: TMatch.ei_scrs HI.
    + by rewrite !TInv.get_set_neq //; exact: TMatch.ei_one HI.
    + by rewrite !TInv.get_set_neq //; exact: TMatch.ei_sp HI.
    + by rewrite TInv.get_set_eq /=; exact: TMatch.ei_arg HI.
    + rewrite TInv.get_set_neq // TInv.get_set_eq /=.
      exact: TMatch.ei_arg HI.
    + by rewrite !TInv.get_set_neq //; exact: TMatch.ei_ra HI.
    + exact: TMatch.ei_rtag HI.
    + by rewrite Pointer.inc_preserves_component; exact: TMatch.ei_pc HI.
    + by rewrite Er; exact: (TMacros.code_at_I_tail Hcode).
    + exact: TMatch.ei_cont HI.
    + exact: TMatch.ei_uniq HI.
    + exact: TMatch.ei_priv HI.
    + exact: TMatch.ei_scrp HI.
    + exact: TMatch.ei_temps HI.
    + exact: TMatch.ei_cap HI.
    + apply: leq_trans (TMatch.ei_budget HI).
      by rewrite leq_add2l leq_maxr.
    + exact: TMatch.ei_prot HI.
    + exact: TMatch.ei_stack HI.
    + apply: TInv.tag_inv_setreg; first by [].
      apply: TInv.tag_inv_setreg; first by [].
      exact: TMatch.ei_tag HI.
Qed.


Lemma leaf_local_run a scrs C stk mem k arg ret rtag Sl tmem tregs pct pc fb
      prot temps plm c rest s1 s2 cap :
  expr_inv a scrs C stk mem k E_local arg ret rtag Sl tmem tregs pct pc fb
           prot temps plm c rest s1 s2 cap ->
  TS.step cde (tmem, tregs, pc, pct) E0
    (tmem, Transitional.Register.set R_COM (Ptr (lbp C)) Other tregs,
     Pointer.inc pc, pct)
  /\ val_inv a scrs C stk mem k (Ptr (C, Block.local, 0%Z)) arg ret rtag Sl
       tmem (Transitional.Register.set R_COM (Ptr (lbp C)) Other tregs) pct
       (Pointer.inc pc) fb prot temps plm rest cap.
Proof.
  move=> HI.
  have [i0 [r0 Er]] := ei_rest_cons HI.
  have Ec := compile_local (TMatch.ei_comp HI).
  have Hcode : TMacros.code_at_I cde C pc
                 (IConst (IPtr (lbp C)) R_COM :: i0 :: r0).
  { move: (TMatch.ei_code HI). by rewrite Ec Er. }
  split.
  - have -> : Ptr (lbp C) = imm_to_val (IPtr (lbp C)) by [].
    eapply TS.Const; [exact: (TMacros.code_at_I_head Hcode)
                     | exact: (TMacros.check_pc_at_I Hcode)].
  - apply: TMatch.ValInv;
    last by eauto using TMatch.ei_anchor, TMatch.vi_anchor.
    + exact: TMatch.ei_plm HI.
    + exact: TMatch.ei_dom HI.
    + exact: TMatch.ei_mem HI.
    + exact: TMatch.ei_scrs HI.
    + by rewrite TInv.get_set_neq //; exact: TMatch.ei_one HI.
    + by rewrite TInv.get_set_neq //; exact: TMatch.ei_sp HI.
    + by rewrite TInv.get_set_neq //; exact: TMatch.ei_arg HI.
    + rewrite TInv.get_set_eq /=. apply: VI_ptr.
      exact: (inj_local _ (TInject.mj_ok (TMatch.ei_mem HI))).
    + by rewrite TInv.get_set_neq //; exact: TMatch.ei_ra HI.
    + exact: TMatch.ei_rtag HI.
    + by rewrite Pointer.inc_preserves_component; exact: TMatch.ei_pc HI.
    + by rewrite Er; exact: (TMacros.code_at_I_tail Hcode).
    + exact: TMatch.ei_cont HI.
    + exact: TMatch.ei_uniq HI.
    + exact: TMatch.ei_priv HI.
    + exact: TMatch.ei_scrp HI.
    + exact: TMatch.ei_temps HI.
    + exact: TMatch.ei_cap HI.
    + apply: leq_trans (TMatch.ei_budget HI).
      by rewrite leq_add2l leq_maxr.
    + exact: TMatch.ei_prot HI.
    + exact: TMatch.ei_stack HI.
    + apply: TInv.tag_inv_setreg; first by [].
      exact: TMatch.ei_tag HI.
Qed.

End WithProgram.

End TLeaf.
