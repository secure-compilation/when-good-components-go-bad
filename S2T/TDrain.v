(** * Stage 4, part 8 — `cont_matchJ_drain` at T.

    See plan-i2t-redo.md §4 (Stage 4).

    Port of `S2I/Simulation.v:1656`. `cont_matchJ` is `cont_match` up to leading
    JOIN JUNK — the if-emission's glue, either a bare join label or the
    else-branch's jump over the then-code — and this lemma drains that junk by
    silent target steps so the diagrams only ever face the canonical,
    syntax-directed `cont_match`.

    `cont_matchJ` itself needs **no port**: it mentions memory zero times, so
    the I-level relation is reused verbatim and only its consumption site moves
    from `code_at` to `code_at_I`.

    Two things differ from the I proof, and both come from the same place —
    T flattens a component's procedures into ONE array:

    - the `Bnz` resolves its label component-wide, so the uniqueness premise is
      component-wide rather than per-procedure (`S2T/TLabel.v`);
    - the `ILabel` step carries a `check_pc`, so the drain must know the array
      continues past the label. That is `cont_matchJ_nonempty` — every
      continuation's code is nonempty, which needs the MUTUAL induction because
      `CM_seq`'s code is `c2 ++ rest` with `c2` not obviously nonempty. *)

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

(* ================================================================== *)
(* Continuation code is nonempty                                      *)
(* ================================================================== *)

Lemma cat_nonempty (T : Type) (s1 s2 : seq T) :
  s2 <> [::] -> s1 ++ s2 <> [::].
Proof. by move=> H; case: s1. Qed.

Lemma nonempty_cons (T : Type) (s : seq T) :
  s <> [::] -> exists x r, s = x :: r.
Proof. by case: s => [|x r] // _; exists x, r. Qed.

(** Needed for the [check_pc] of the [ILabel] step: after the label there IS a
    next cell. Proved by the mutual induction — `CM_seq` is the case that
    forces it. *)
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

(* ================================================================== *)
(* The drain                                                          *)
(* ================================================================== *)

Section WithCode.

Variable cde : Transitional.code.

(** Component-wide label uniqueness of the T array. Stage 3 discharges it from
    `S2I/LabelUniq.v:834`'s `compiled_labels_unique`; stated here as the
    premise it will become. *)
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
  - (* CMJ_base — already canonical *)
    exists pc, rest0.
    split; [exact: star_refl | by left | exact: Hcode | exact: Hpc | exact: Hc].
  - (* CMJ_label — one administrative [ILabel] step *)
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
  - (* CMJ_bnzjoin — the else-branch's jump over the then-code *)
    have Hcode2 : TMacros.code_at_I cde C pc
      (IBnz R_ONE lend :: ILabel lc :: c2 ++ ILabel lend :: rest0)
      by exact: Hcode.
    (* where the join label is, and that the machine finds it there *)
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
