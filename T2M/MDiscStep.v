(** * T2M — [disc_step]: [disc_inv] is preserved along [TS.step],
    assembled from the per-case lemmas in MDiscStepA/A2/B/C/D. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import CompCert.Events.
Require Import CompCert.Smallstep.

Require Import Intermediate.Machine.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.
Require Import T2M.MSig.
Require T2M.MDefs.
Require Import T2M.MDisc.
Require Import T2M.MDiscStepA.
Require Import T2M.MDiscStepA2.
Require Import T2M.MDiscStepB.
Require Import T2M.MDiscStepC.
Require Import T2M.MDiscStepD.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section DiscStep.

Variable cde : Transitional.code.
Variable MM : Component.id -> seq sv.
Hypothesis HMM : forall c S,
  getm cde c = Some S -> comp_ok (c, 1, 0%Z) S (MM c).
Hypothesis Hcst : forall pc iv r tg c p,
  Transitional.executing cde pc (TrConst iv r) tg c ->
  iv = IPtr p ->
  p = (c, 0, 0%Z) \/
  ((p = (c, 1, 0%Z) \/ p = (c, 1, 1%Z)) /\ (r = R_AUX1 \/ r = R_AUX2)).
Hypothesis Huniq : forall (c : Component.id) (S : TS.tcode) (l : label)
    (m m' : nat) (t1 t2 : mem_tag),
  getm cde c = Some S ->
  nth_error S m = Some (TrLabel (inl l), t1) ->
  nth_error S m' = Some (TrLabel (inl l), t2) ->
  m = m'.

Local Notation svat := (MDisc.svat MM).
Local Notation asv := (MDisc.asv MM).
Local Notation in_window := (MDisc.in_window MM).
Local Notation sp_of := (MDisc.sp_of MM).
Local Notation topc := (MDisc.topc).
Local Notation topw := (MDisc.topw MM).
Local Notation carry0 := (MDisc.carry0 MM).
Local Notation scrpin := (MDisc.scrpin MM).
Local Notation cap := (MDisc.cap MM).
Local Notation dinv := (MDisc.dinv cde MM).
Local Notation disc_inv := (MDisc.disc_inv cde MM).

(* the preservation theorem, assembled from the per-case lemmas *)
Theorem disc_step (s1 : TS.state) (tr : trace) (s2 : TS.state) :
  TS.step cde s1 tr s2 -> disc_inv s1 -> disc_inv s2.
Proof.
case.
- move=> *; by eapply disc_step_nop; eauto.
- move=> *; by eapply disc_step_label; eauto.
- move=> *; by eapply disc_step_const; eauto.
- move=> *; by eapply disc_step_mov; eauto.
- move=> *; by eapply disc_step_binop; eauto.
- move=> *; by eapply disc_step_load; eauto.
- move=> *; by eapply disc_step_store; eauto.
- move=> *; by eapply disc_step_jal; eauto.
- move=> *; by eapply disc_step_jump; eauto.
- move=> *; by eapply disc_step_jumpret; eauto.
- move=> *; by eapply disc_step_bnznz; eauto.
- move=> *; by eapply disc_step_bnzz; eauto.
- move=> *; by eapply disc_step_alloc; eauto.
- move=> *; by eapply disc_step_call; eauto.
Qed.

End DiscStep.
