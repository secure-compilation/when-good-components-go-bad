(** * T2M — [disc_inv] at the initial state and its star corollaries:
    [disc_initial] establishes it at [TSim.t_initial_base] from the
    initial-memory layout facts; [disc_star]/[disc_t_initial] extend it. *)

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
Require Import S2T.TSim.
Require Import T2M.MSig.
Require T2M.MDefs.
Require Import T2M.MDisc.
Require Import T2M.MDiscStepA.
Require Import T2M.MDiscStepB.
Require Import T2M.MDiscStepC.
Require Import T2M.MDiscStepD.
Require Import T2M.MDiscStep.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section DiscInit.

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
Local Notation dinv := (MDisc.dinv cde MM).
Local Notation disc_inv := (MDisc.disc_inv cde MM).

Local Notation mem0 tp :=
  (Transitional.Memory.prepare_procedures_initial_memory tp).

Lemma dinv_initial (tp : Intermediate.program) (pc : Pointer.t) :
  Transitional.find_plabel_in_code cde Component.main Procedure.main
    = Some pc ->
  (forall c b j cv tg,
     cell_at (mem0 tp) c b j = Some (cv, tg) ->
     tvtag cv = Other /\
     (forall q, Transitional.val cv = Ptr q ->
        Pointer.component q = c /\ Pointer.block q = 0)) ->
  (forall c cm, getm (mem0 tp) c = Some cm ->
     2 <= Transitional.Memory.nextblock cm) ->
  (forall c cm, getm (mem0 tp) c = Some cm ->
     exists tg0 tg1,
       cell_at (mem0 tp) c 1 0 = Some (Transitional.tUndef, tg0)
       /\ cell_at (mem0 tp) c 1 1
          = Some (Transitional.to_tvalue (Int 0), tg1)) ->
  (forall c S, getm cde c = Some S ->
     exists cm, getm (mem0 tp) c = Some cm) ->
  dinv None [::] (fun _ => [::]) Undef (mem0 tp)
    Transitional.Register.init pc (Transitional.Level 0).
Proof.
move=> Hfl P1 P2 P3 P5.
have [Ecm EvT] := plabel_target HMM Hfl.
have Hg : forall r,
    Transitional.Register.get r Transitional.Register.init
    = Transitional.tUndef.
{ by case. }
have [C_code EgM] : exists C_code,
    getm cde Component.main = Some C_code.
{ move: Hfl. rewrite /Transitional.find_plabel_in_code.
  case E: (cde Component.main) => [Cc|] //. by exists Cc. }
have [cmM HcmM] := P5 _ _ EgM.
constructor.
* move=> r0 _. by rewrite Hg.
* move=> r0 _ _ _ _. rewrite Hg. by [].
* move=> w0; rewrite EvT => -[<-]. by [].
* move=> w0; rewrite EvT => -[<-]. by [].
* move=> w0; rewrite EvT => -[<-]. by [].
* move=> w0; rewrite EvT => -[<-] _. by [].
* move=> w0; rewrite EvT => -[<-] _. by rewrite Hg.
* move=> w0; rewrite EvT => -[<-] HP _. by case: HP.
* move=> w0 b0; rewrite EvT => -[<-]. by [].
* move=> w0; rewrite EvT => -[<-]. by [].
* move=> w0 b0; rewrite EvT => -[<-]. by [].
* move=> w0 b0 k1; rewrite EvT => -[<-]. by [].
* move=> w0; rewrite EvT => -[<-] _ _ _. by rewrite Hg.
* move=> c0 b0 j cv tg Hcell _.
  have [T1 T2] := P1 _ _ _ _ _ Hcell.
  split=> // _ q E.
  have [Ecq Ebq] := T2 q E.
  have [cm1 Hcm1] : exists cm1, getm (mem0 tp) c0 = Some cm1.
  { move: Hcell. rewrite /cell_at.
    case E1: (getm (mem0 tp) c0) => [cm1|] //.
    by exists cm1. }
  split.
  - by rewrite Ebq.
  - by rewrite Ebq.
  - exists cm1. split; first by rewrite Ecq.
    rewrite Ebq.
    have := P2 _ _ Hcm1. by lia.
* move=> c0 cm0 Hcm0.
  have [tg0 [tg1 [Hc10 Hc11]]] := P3 _ _ Hcm0.
  exists Transitional.tUndef, tg0. by split.
* move=> w0; rewrite EvT => -[<-] /=.
  rewrite Ecm.
  have [tg0 [tg1 [Hc10 Hc11]]] := P3 _ _ HcmM.
  exists Transitional.tUndef, tg0. by split.
* move=> w0 b0; rewrite EvT => -[<-]. by [].
* move=> c0 A _. by [].
* move=> i A. by case: i.
* move=> i A b0. by case: i.
* move=> i1 i2 A1 A2 _. by case: i1.
* move=> c0 b0. by [].
* move=> c0. by [].
* exact: P2.
* exact: P5.
* by [].
* move=> c0 cm0 Hcm0.
  have [tg0 [tg1 [Hc10 Hc11]]] := P3 _ _ Hcm0.
  exists (Transitional.to_tvalue (Int 0)), tg1.
  by split.
* move=> w0; rewrite EvT => -[<-]. by [].
* move=> i X. by case: i.
* move=> _. by [].
* move=> c0 S1 _ Hg1 _.
  have [cm0 Hcm0] := P5 _ _ Hg1.
  have [tg0 [tg1 [Hc10 Hc11]]] := P3 _ _ Hcm0.
  exists Transitional.tUndef, tg0. by split.
* move=> w0; rewrite EvT => -[<-] _. by [].
* move=> w0; rewrite EvT => -[<-] Hekw. by [].
* move=> i A. by case: i.
Qed.

Lemma disc_initial (tp : Intermediate.program) (S0 : TS.state) :
  TSim.t_initial_base cde tp S0 ->
  (forall c b j cv tg,
     cell_at (mem0 tp) c b j = Some (cv, tg) ->
     tvtag cv = Other /\
     (forall q, Transitional.val cv = Ptr q ->
        Pointer.component q = c /\ Pointer.block q = 0)) ->
  (forall c cm, getm (mem0 tp) c = Some cm ->
     2 <= Transitional.Memory.nextblock cm) ->
  (forall c cm, getm (mem0 tp) c = Some cm ->
     exists tg0 tg1,
       cell_at (mem0 tp) c 1 0 = Some (Transitional.tUndef, tg0)
       /\ cell_at (mem0 tp) c 1 1
          = Some (Transitional.to_tvalue (Int 0), tg1)) ->
  (forall c S, getm cde c = Some S ->
     exists cm, getm (mem0 tp) c = Some cm) ->
  disc_inv S0.
Proof.
move=> [pc [Hfl ->]] P1 P2 P3 P5.
exists None, [::], (fun _ => [::]), Undef.
exact: (dinv_initial Hfl P1 P2 P3 P5).
Qed.

(* the invariant is carried along any execution *)
Corollary disc_star (s1 : TS.state) (tr : trace) (s2 : TS.state) :
  star TS.step cde s1 tr s2 -> disc_inv s1 -> disc_inv s2.
Proof.
elim=> // s1' tr1 s2' tr2 s3' tr3 Hstep Hstar IH _ HI.
apply: IH.
exact: (disc_step HMM Hcst Huniq Hstep HI).
Qed.

(* ... in particular from any (star-closed) initial state *)
Corollary disc_t_initial (tp : Intermediate.program) (S : TS.state) :
  TSim.t_initial cde tp S ->
  (forall c b j cv tg,
     cell_at (mem0 tp) c b j = Some (cv, tg) ->
     tvtag cv = Other /\
     (forall q, Transitional.val cv = Ptr q ->
        Pointer.component q = c /\ Pointer.block q = 0)) ->
  (forall c cm, getm (mem0 tp) c = Some cm ->
     2 <= Transitional.Memory.nextblock cm) ->
  (forall c cm, getm (mem0 tp) c = Some cm ->
     exists tg0 tg1,
       cell_at (mem0 tp) c 1 0 = Some (Transitional.tUndef, tg0)
       /\ cell_at (mem0 tp) c 1 1
          = Some (Transitional.to_tvalue (Int 0), tg1)) ->
  (forall c S1, getm cde c = Some S1 ->
     exists cm, getm (mem0 tp) c = Some cm) ->
  disc_inv S.
Proof.
move=> [S1 [Hbase Hstar]] P1 P2 P3 P5.
apply: (disc_star Hstar).
exact: (disc_initial Hbase P1 P2 P3 P5).
Qed.

End DiscInit.
