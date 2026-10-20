Require Import Common.Definitions.
Require Import Common.Values.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Source.Language.
Require Import Source.CS.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.
Require Import S2I.SimInject.
Require Import S2I.Simulation.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.
Require Import S2T.TInv.
Require Import S2T.TLabel.
Require Import S2T.TMacros.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Require Import Coq.ZArith.ZArith.

Set Implicit Arguments.
Unset Strict Implicit.

Module TDrain.


Lemma cat_nonempty (T : Type) (s1 s2 : seq T) :
  s2 <> [::] -> s1 ++ s2 <> [::].
Proof. by move=> H; case: s1. Qed.

Lemma nonempty_cons (T : Type) (s : seq T) :
  s <> [::] -> exists x r, s = x :: r.
Proof. by case: s => [|x r] // _; exists x, r. Qed.

Lemma cont_match_nonempty a C plm :
  (forall k rest temps, cont_match a C plm k rest temps -> rest <> [::])
  /\ (forall k rest temps, cont_matchJ a C plm k rest temps -> rest <> [::]).
Proof.
  apply: cont_match_combind; move=> *;
    cbn [Compiler.push Compiler.pop Compiler.store_arg Compiler.reload_sp];
    try by []; by apply: cat_nonempty.
Qed.

Lemma cont_matchJ_nonempty a C plm k rest temps :
  cont_matchJ a C plm k rest temps -> rest <> [::].
Proof. by case: (cont_match_nonempty a C plm) => [_ H]; exact: H. Qed.

Lemma cont_matchJ_cons a C plm k rest temps :
  cont_matchJ a C plm k rest temps ->
  exists i r, rest = i :: r.
Proof.
  move=> /cont_matchJ_nonempty. case: rest => [|i r] // _.
  by exists i, r.
Qed.


Section WithCode.

Variable cde : Transitional.code.

Definition labels_uniq (C : Component.id) : Prop :=
  forall l C_code, getm cde C = Some C_code ->
    count (TLabel.is_tlabel l) C_code <= 1.

Lemma cont_matchJ_drain a C plm k temps pc jrest :
  cont_matchJ a C plm k jrest temps ->
  TMacros.code_at_I cde C pc jrest ->
  Pointer.component pc = C ->
  labels_uniq C ->
  forall tmem tregs pct,
  Transitional.Register.get R_ONE tregs = MVal Other (Int 1) ->
  exists pc' rest,
    [/\ star TS.step cde (tmem, tregs, pc, pct) E0 (tmem, tregs, pc', pct),
        pc' = pc \/ plus TS.step cde (tmem, tregs, pc, pct) E0
                         (tmem, tregs, pc', pct),
        TMacros.code_at_I cde C pc' rest,
        Pointer.component pc' = C
      & cont_match a C plm k rest temps].
Proof.
  move=> Hcm; elim: Hcm pc
    => [k0 rest0 temps0 Hc
       | l k0 rest0 temps0 Hj IH
       | lend lc c2 k0 rest0 temps0 Hj IH] pc Hcode Hpc Hu tmem tregs pct HONE.
  -
    exists pc, rest0.
    split; [exact: star_refl | by left | exact: Hcode | exact: Hpc | exact: Hc].
  -
    have [i [r Er]] := cont_matchJ_cons Hj.
    have Hcode2 : TMacros.code_at_I cde C pc (ILabel l :: i :: r)
      by rewrite -Er.
    have SB : TS.step cde (tmem, tregs, pc, pct) E0
              (tmem, tregs, Pointer.inc pc, pct).
    { eapply TS.Label; [exact: (TMacros.code_at_I_head Hcode2)
                       | exact: (TMacros.check_pc_at_I Hcode2)]. }
    have HcT := TMacros.code_at_I_tail Hcode.
    have HpcT : Pointer.component (Pointer.inc pc) = C
      by rewrite Pointer.inc_preserves_component.
    case: (IH _ HcT HpcT Hu tmem tregs pct HONE)
      => [pc' [rest' [Sd Hor Hc' Ec Hcm']]].
    exists pc', rest'. split=> //.
    + eapply star_trans; [exact: star_one SB | exact: Sd | by []].
    + right. eapply plus_left; [exact: SB | exact: Sd | by []].
  -
    have Hcode2 : TMacros.code_at_I cde C pc
      (IBnz R_ONE lend :: ILabel lc :: c2 ++ ILabel lend :: rest0)
      by exact: Hcode.
    have HcodeL : TMacros.code_at_I cde C pc
      ((IBnz R_ONE lend :: ILabel lc :: c2) ++ ILabel lend :: rest0)
      by exact: Hcode.
    case: (TMacros.code_at_I_label_find HcodeL Hpc Hu)
      => [pcL [Hfind EcL HcL]].
    have SB : TS.step cde (tmem, tregs, pc, pct) E0
              (tmem, tregs, pcL, pct).
    { eapply TS.BnzNZ.
      - exact: (TMacros.code_at_I_head Hcode2).
      - exact: (TMacros.check_pc_at_I Hcode2).
      - by rewrite HONE.
      - by rewrite HONE.
      - by [].
      - by rewrite Hpc; exact: Hfind.
      - apply: PcJump; first exact: (TMacros.code_at_I_head HcL).
        by rewrite EcL Hpc. }
    case: (IH _ HcL EcL Hu tmem tregs pct HONE)
      => [pc' [rest' [Sd Hor Hc' Ec Hcm']]].
    exists pc', rest'. split=> //.
    + eapply star_trans; [exact: star_one SB | exact: Sd | by []].
    + right. eapply plus_left; [exact: SB | exact: Sd | by []].
Qed.

End WithCode.

End TDrain.
