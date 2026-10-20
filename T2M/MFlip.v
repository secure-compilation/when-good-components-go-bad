Require Import Common.Definitions.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
Require Import Coq.micromega.Lia.

Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.CompCertExtensions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section RunCompare.

Variable L : semantics.
Hypothesis DET : determinate L.

Lemma match_traces_eq (t1 t2 : trace) :
  match_traces t1 t2 -> t1 = t2.
Proof.
by case.
Qed.

Lemma star_run_compare (s : state L) (u : trace) (s1 : state L)
    (t : trace) (s2 : state L) :
  Star L s u s1 -> Star L s t s2 ->
  (exists t2, t = Eapp u t2 /\ Star L s1 t2 s2)
  \/ (exists u2, u = Eapp t u2 /\ Star L s2 u2 s1).
Proof.
move=> Hu.
elim: Hu t s2 => [s0|s0 t1 sb t2' s1' u' Hstep Hstar IH Eu] t s2 Ht.
- left. exists t. by rewrite E0_left.
- inversion Ht; subst.
  +
    right. exists (Eapp t1 t2'). rewrite E0_left. split=> //.
    apply: star_step; [exact: Hstep | exact: Hstar | by []].
  +
    have [MT Est] := sd_determ DET _ _ _ _ _ Hstep H.
    have Et13 : t1 = t0 := match_traces_eq MT.
    subst t0.
    have Esb : sb = s4 := Est (erefl _).
    subst s4.
    case: (IH _ _ H0) => [[tx [Etx HS]]|[ux [Eux HS]]].
    * left. exists tx. split=> //.
      by rewrite Etx Eapp_assoc.
    * right. exists ux. split=> //.
      by rewrite Eux Eapp_assoc.
Qed.

Lemma silent_starN_bound (n0 : nat) (s s_stop : state L) :
  starN (step L) (globalenv L) n0 s E0 s_stop ->
  (forall s', ~ Step L s_stop E0 s') ->
  forall (n : nat) (s1 : state L),
  starN (step L) (globalenv L) n s E0 s1 ->
  (n <= n0)%coq_nat.
Proof.
elim: n0 s => [|n0 IH] s Hstop Hnostep n s1 Hn.
-
  inversion Hstop; subst.
  case: n s1 Hn => [|n] s1 Hn; first by lia.
  inversion Hn; subst.
  have [E1 E2] := Eapp_E0_inv _ _ (esym H2). subst.
  by case: (Hnostep _ H0).
- inversion Hstop; subst.
  have [E1 E2] := Eapp_E0_inv _ _ (esym H2). subst.
  case: n s1 Hn => [|n] s1 Hn; first by lia.
  inversion Hn; subst.
  have [E1 E2] := Eapp_E0_inv _ _ (esym H5). subst.
  have [_ Est] := sd_determ DET _ _ _ _ _ H0 H3.
  have Es : s' = s'0 := Est (erefl _).
  subst s'0.
  have := IH _ H1 Hnostep _ _ H4.
  by lia.
Qed.

Lemma star_to_starN (s : state L) (t : trace) (s' : state L) :
  Star L s t s' ->
  exists n, starN (step L) (globalenv L) n s t s'.
Proof.
exact: star_starN.
Qed.

Lemma event_no_silent (s : state L) (e : event) (s1 s2 : state L) :
  Step L s [:: e] s1 -> Step L s E0 s2 -> False.
Proof.
move=> Hev Hsil.
have [MT _] := sd_determ DET _ _ _ _ _ Hev Hsil.
by have := match_traces_eq MT.
Qed.

Lemma forever_silent_starN (s : state L) :
  forever_silent (step L) (globalenv L) s ->
  forall n : nat, exists s',
    starN (step L) (globalenv L) n s E0 s' /\
    forever_silent (step L) (globalenv L) s'.
Proof.
move=> Hfs n.
elim: n s Hfs => [|n IH] s Hfs.
- exists s. split=> //. exact: starN_refl.
- inversion Hfs; subst.
  have [s' [HsN Hfs']] := IH _ H0.
  exists s'. split=> //.
  by apply: starN_step; [exact: H | exact: HsN | by []].
Qed.

Lemma starN_silent_trans (n m : nat) (s s1 s2 : state L) :
  starN (step L) (globalenv L) n s E0 s1 ->
  starN (step L) (globalenv L) m s1 E0 s2 ->
  starN (step L) (globalenv L) (n + m)%coq_nat s E0 s2.
Proof.
elim: n s => [|n IH] s Hn Hm.
- by inversion Hn; subst.
- inversion Hn; subst.
  have [E1 E2] := Eapp_E0_inv _ _ (esym H2). subst.
  apply: starN_step; [exact: H0 | exact: (IH _ H1 Hm) | by []].
Qed.

Lemma reactive_star_events (s : state L) (T : traceinf) :
  forever_reactive (step L) (globalenv L) s T ->
  forall k : nat, exists t' s',
    [/\ Star L s t' s', (k <= size t')%coq_nat
      & exists T', T = Eappinf t' T'].
Proof.
move=> Hfr k.
elim: k s T Hfr => [|k IH] s T Hfr.
- exists E0, s. split=> //; first exact: star_refl.
  by exists T.
- inversion Hfr; subst.
  have [t2 [s' [Hst2 Hk [T2 ET2]]]] := IH _ _ H1.
  exists (Eapp t t2), s'. split.
  + apply: star_trans; [exact: H | exact: Hst2 | by []].
  + rewrite size_cat.
    have Ht1 : (1 <= size t)%coq_nat.
    { case: t H0 {H Hfr} => [|ev tq] H0.
      - by move: (H0 (erefl _)).
      - by rewrite /=; lia. }
    by lia.
  + exists T2. by rewrite ET2 Eappinf_assoc.
Qed.

End RunCompare.

Lemma fsim_does_prefix (L1 L2 : semantics) (m : finpref_behavior) :
  forward_simulation L1 L2 ->
  does_prefix L1 m ->
  not_wrong_finpref m ->
  does_prefix L2 m.
Proof.
move=> FS [b1 [Hb1 Hpref]] Hnw.
have [b2 [Hb2 Himp]] := forward_simulation_behavior_improves FS Hb1.
exists b2. split=> //.
case: m Hpref Hnw => [tm| |tm] //= Hpref _.
-
  case: b1 Hpref Hb1 Himp => // t2 /= Etm _ Himp.
  subst t2.
  by case: Himp => [<-|[t [Ew _]]] //.
-
  exact: (behavior_prefix_improves_trans' Hpref Himp).
Qed.

Lemma improves_prefix_transfer (bS bT : program_behavior)
    (m : finpref_behavior) :
  behavior_improves bS bT ->
  prefix m bT \/ behavior_improves_finpref bT m ->
  prefix m bS \/ behavior_improves_finpref bS m.
Proof.
move=> [EbS|[t [EbS HtT]]] Hcase; first by subst bS.
subst bS.
case: Hcase => [Hpref|Himp].
- case: (behavior_prefix_comp' Hpref HtT) => [Hmt|Htm].
  + left.
    apply: (trace_behavior_prefix_trans Hmt).
    exists (Goes_wrong E0). by rewrite /= E0_right.
  + right. by exists t.
- case: Himp => [t' [EbT Ht'm]].
  subst bT.
  right. exists t. split=> //.
  case: HtT => b' Eb'.
  case: b' Eb' => [t2|t2|T2|t2] /= Eb'; try by case: Eb'.
  case: Eb' => Et'. subst t'.
  move: Ht'm.
  by case: m => tm /= [t3 Etm];
    exists (Eapp t2 t3); rewrite Etm Eapp_assoc.
Qed.
