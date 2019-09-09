Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.CompCertExtensions.
Require Import Common.Traces.
Require Import Common.Blame.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Lib.Tactics.
Require Import Lib.Monads.
Require Import Lib.Extra.
Require Import Source.CS.
Import Source.CS.CS.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From mathcomp Require ssrnat.

Canonical ssrnat.nat_eqType.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import Source.

Module CS.

Instance state_turn : HasTurn state := {
  turn_of s iface := s_component s \in domm iface
}.

Corollary kstep_deterministic:
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

Section Semantics.

  Variable p: program.

  Hypothesis valid_program:
    well_formed_program p.

  Hypothesis complete_program:
    closed_program p.

  Let sem := sem p.

  Lemma trace_wb t cs cs' :
    Star sem cs t cs' ->
    well_bracketed_trace (stack_state_of cs) t.
  Proof.
    elim: cs t cs' / => //= s1 t1 s2 t2 s3 t Hstep Hstar IH -> {t}.
    case: s1 t1 s2 / Hstep Hstar IH=> //=.
    - (* Internal Return *)
      by move=> C stk mem k _ P v P_expr old <-; rewrite eqxx.
    - (* External Return *)
      move=> C stk mem k C' P v P_expr old.
      by rewrite eq_sym eqxx=> /eqP/negbTE -> /=.
    - (* Internal Call *)
      by move=> C stk mem k v _ _ old <-; rewrite eqxx.
    - (* External Call *)
      by move=> C stk mem k v _ C' old /eqP/negbTE ->; rewrite !eqxx.
  Qed.

  Lemma events_wf st t st' :
    Star sem st t st' ->
    all (well_formed_event (prog_interface p)) t.
  Proof.
  elim: st t st' / => // st1 t1 st2 t2 st3 t /= Hstep Hstar IH -> {t}.
  rewrite all_cat; case: st1 t1 st2 / Hstep {Hstar} => //=.
  - by move=> ????????? /eqP -> /imported_procedure_iff ->.
  - by move=> ????????  /eqP ->.
  Qed.

  Lemma trace_wf mainP t cs cs' :
    Star sem cs t cs' ->
    initial_state p cs ->
    prog_main p = Some mainP ->
    well_formed_program p ->
    well_formed_trace (prog_interface p) t.
  Proof.
    move=> Hstar Hinitial Hmain Hwf; rewrite /well_formed_trace.
    rewrite (events_wf Hstar) andbT.
    suffices <- : stack_state_of cs = stack_state0 by apply: trace_wb; eauto.
    by move: Hinitial; rewrite /initial_state /initial_machine_state Hmain => ->.
  Qed.

  (* Several alternative formulations are possible. One may include the ERet event
     in the star, express the inclusion of ECall in the trace via In, etc. *)
  Lemma eret_from_initial_star_goes_after_ecall_cs s0 t s1 s2 C' v C :
    CS.initial_state p s0 ->
    Star sem s0 t s1 ->
    Step sem s1 [:: ERet C' v C] s2 ->
    exists t1 s s' t2 P v',
      Star sem s0 t1 s /\
      Step sem s [ECall C P v' C'] s' /\
      Star sem s' t2 s1 /\
      t = t1 ** [ECall C P v' C'] ** t2.
  Proof.
    move=> Hinitial Hstar Hstep.
    have {Hstep} /trace_wb : Star sem s0 (t ++ [:: ERet C' v C]) s2.
      apply: star_trans; eauto; exact: star_one.
    have -> : stack_state_of s0 = stack_state0.
      by rewrite Hinitial /= /CS.initial_machine_state /=; case: prog_main.
    case/well_bracketed_trace_inv=> t1 [P [arg [t2 e]]].
    move: Hstar; rewrite {}e -[seq.cat]/Eapp.
    case/(star_middle1_inv (@singleton_traces p))=> s1' [s2' [Hstar1 [Hstep2 Hstar3]]].
    by exists t1, s1', s2', t2, P, arg; repeat split=> //.
  Qed.

End Semantics.

End CS.
