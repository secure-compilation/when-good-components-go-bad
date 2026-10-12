Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Traces.
Require Import CompCert.Events.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import Backtranslation_ME_MP.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Definition pent : Type := (nat * nat * nat)%type.

Definition pend_step (st : seq pent) (pre : trace) (e : event) : seq pent :=
  match e with
  | ECall C0 _ _ C' => (C0, size (rp_events pre C0), C') :: st
  | ERet _ _ _ => behead st
  end.

Fixpoint pend_r (r : trace) : seq pent :=
  match r with
  | [::] => [::]
  | e :: r' => pend_step (pend_r r') (rev r') e
  end.

Definition pend (pre : trace) : seq pent := pend_r (rev pre).

Lemma pend_nil : pend [::] = [::].
Proof. by []. Qed.

Lemma pend_rcons pre e : pend (rcons pre e) = pend_step (pend pre) pre e.
Proof. by rewrite /pend rev_rcons /= revK. Qed.

Definition pcallee (x : pent) : nat := x.2.
Definition pcaller (x : pent) : nat := x.1.1.
Definition pidx (x : pent) : nat := x.1.2.

Definition topcomp (st : seq pent) : nat :=
  if st is x :: _ then pcallee x else Component.main.

Lemma rp_events_rcons pre e c :
  rp_events (rcons pre e) c
  = rp_events pre c ++ (if cur_comp_of_event e == c then [:: e] else [::]).
Proof. by rewrite /rp_events -cats1 filter_cat /=; case: ifP. Qed.

Lemma size_rp_events_rcons pre e c :
  size (rp_events (rcons pre e) c)
  = size (rp_events pre c) + (cur_comp_of_event e == c).
Proof. rewrite rp_events_rcons size_cat. by case: (cur_comp_of_event e == c). Qed.

Lemma run_trace_rcons s pre e : run_trace s (rcons pre e) = run_event (run_trace s pre) e.
Proof. exact: run_trace1. Qed.

Lemma wb_rcons pre e :
  well_bracketed_trace stack_state0 (rcons pre e) ->
  well_bracketed_trace stack_state0 pre
  /\ well_bracketed_trace (run_trace stack_state0 pre) [:: e].
Proof. rewrite -cats1 well_bracketed_trace_cat => /andP [H1 H2]. by split. Qed.

Fixpoint chained (st : seq pent) : bool :=
  if st is x :: st' then (pcaller x == topcomp st') && chained st' else true.

Lemma pend_inv pre :
  well_bracketed_trace stack_state0 pre ->
  [/\ cur_comp (run_trace stack_state0 pre) = topcomp (pend pre),
      callers (run_trace stack_state0 pre) = map pcaller (pend pre)
    & chained (pend pre)].
Proof.
elim/last_ind: pre => [|pre e IH]; first by [].
move=> /wb_rcons [Hwb He].
have [Hcur Hcal Hch] := IH Hwb.
rewrite run_trace_rcons pend_rcons.
move: He. rewrite /=.
case: e => [C0 P0 z C'|C0 z C'] /=.
- rewrite andbT => /eqP Hc. split=> //.
  + by rewrite Hcal.
  + by rewrite /pcaller /= -Hc Hcur eqxx Hch.
- case Ecl: (callers (run_trace stack_state0 pre)) => [|hd tl]; first by rewrite andbF.
  rewrite ?andbT. move=> /andP [/eqP Hc /eqP Hh].
  move: Hcal Hch. rewrite Ecl.
  case Ep: (pend pre) => [|x st] //= [Ehd Etl] /andP [/eqP Hx Hst].
  split=> //.
  by rewrite -Hh Ehd Hx.
Qed.

Definition calls_into (pre : trace) (X : nat) : bool :=
  has (fun e => if e is ECall _ _ _ C' then C' == X else false) pre.

Definition active (pre : trace) (X : nat) : bool :=
  (X == Component.main) || calls_into pre X.

Lemma active_rcons pre e X :
  active (rcons pre e) X
  = active pre X || (if e is ECall _ _ _ C' then C' == X else false).
Proof. by rewrite /active /calls_into -cats1 has_cat /= orbF orbA. Qed.

Definition frames (pre : trace) (X : nat) : seq (nat * pent) :=
  [seq ix <- zip (iota 0 (size (pend pre))) (rev (pend pre)) | pcallee ix.2 == X].

Lemma calls_into_rcons pre e X :
  calls_into (rcons pre e) X
  = calls_into pre X || (if e is ECall _ _ _ C' then C' == X else false).
Proof. by rewrite /calls_into -cats1 has_cat /= orbF. Qed.

Lemma pend_callee_called pre x : x \in pend pre -> calls_into pre (pcallee x).
Proof.
elim/last_ind: pre x => [//|pre e IH] x.
rewrite pend_rcons calls_into_rcons.
case: e => [C0 P0 z C'|C0 z C'] /=.
- rewrite inE => /orP [/eqP ->|Hx].
  + by rewrite /pcallee /= eqxx orbT.
  + by rewrite IH.
- move=> Hx. rewrite orbF. apply: IH.
  case: (pend pre) Hx => [//|y st] /= Hx. by rewrite inE Hx orbT.
Qed.

Lemma frames_push (st : seq pent) x X :
  [seq ix <- zip (iota 0 (size (x :: st))) (rev (x :: st)) | pcallee ix.2 == X]
  = [seq ix <- zip (iota 0 (size st)) (rev st) | pcallee ix.2 == X]
    ++ (if pcallee x == X then [:: (size st, x)] else [::]).
Proof.
rewrite rev_cons -cats1.
have -> : size (x :: st) = size st + 1 by rewrite addn1.
rewrite iotaD add0n zip_cat; last by rewrite size_iota size_rev.
rewrite filter_cat /=. by case: (pcallee x == X).
Qed.

Lemma frames_call pre C0 P0 z C' X :
  frames (rcons pre (ECall C0 P0 z C')) X
  = frames pre X ++ (if C' == X then [:: (size (pend pre), (C0, size (rp_events pre C0), C'))]
                     else [::]).
Proof. by rewrite /frames pend_rcons /= frames_push. Qed.

Lemma frames_ret pre C0 z C' X x st :
  pend pre = x :: st ->
  frames pre X = frames (rcons pre (ERet C0 z C')) X
                 ++ (if pcallee x == X then [:: (size st, x)] else [::]).
Proof. move=> E. by rewrite /frames pend_rcons E /= frames_push. Qed.

Lemma size_frames_le pre X : size (frames pre X) <= size (pend pre).
Proof.
rewrite /frames size_filter (leq_trans (count_size _ _)) //.
by rewrite size_zip size_iota geq_minl.
Qed.

Lemma size_pend_le pre : size (pend pre) <= size pre.
Proof.
elim/last_ind: pre => [//|pre e IH].
rewrite pend_rcons size_rcons. case: e => [? ? ? ?|? ? ?] /=.
- by rewrite ltnS.
- apply: leqW. apply: leq_trans IH. by rewrite size_behead leq_pred.
Qed.

Lemma frames_callee pre X fx : fx \in frames pre X -> fx.2 \in pend pre /\ pcallee fx.2 = X.
Proof.
rewrite /frames mem_filter => /andP [/eqP HX Hin]. split=> //.
have H2 : fx.2 \in unzip2 (zip (iota 0 (size (pend pre))) (rev (pend pre))).
{ apply/mapP. by exists fx. }
rewrite unzip2_zip ?size_iota ?size_rev // mem_rev in H2. exact: H2.
Qed.

Lemma pend_entry_call (d0 : event) pre x :
  x \in pend pre ->
  exists P0 z0,
    pidx x < size (rp_events pre (pcaller x))
    /\ nth d0 (rp_events pre (pcaller x)) (pidx x) = ECall (pcaller x) P0 z0 (pcallee x).
Proof.
elim/last_ind: pre x => [//|pre e IH] x.
have Hext : forall c i, i < size (rp_events pre c) ->
    i < size (rp_events (rcons pre e) c)
    /\ nth d0 (rp_events (rcons pre e) c) i = nth d0 (rp_events pre c) i.
{ move=> c i Hi. rewrite rp_events_rcons size_cat nth_cat Hi. split=> //.
  exact: ltn_addr. }
rewrite pend_rcons.
case: e Hext => [C0 P0 z0 C'|C0 z0 C'] Hext /=.
- rewrite inE => /orP [/eqP ->|Hx].
  + exists P0, z0. rewrite /pidx /pcaller /pcallee /=.
    rewrite rp_events_rcons /= eqxx size_cat /= addn1 nth_cat ltnn subnn /=. by split.
  + have [P1 [z1 [Hlt Hn]]] := IH x Hx. have [Hlt' Hn'] := Hext _ _ Hlt.
    exists P1, z1. by rewrite Hn'.
- move=> Hx.
  have Hx' : x \in pend pre by case: (pend pre) Hx => [//|y st] /= Hx; rewrite inE Hx orbT.
  have [P1 [z1 [Hlt Hn]]] := IH x Hx'. have [Hlt' Hn'] := Hext _ _ Hlt.
  exists P1, z1. by rewrite Hn'.
Qed.

Lemma topcomp_active pre : active pre (topcomp (pend pre)).
Proof.
rewrite /active /topcomp.
case E: (pend pre) => [|x st]; first by rewrite eqxx.
apply/orP; right. apply: pend_callee_called. by rewrite E mem_head.
Qed.

Lemma inactive_frames pre Y : ~~ active pre Y -> frames pre Y = [::].
Proof.
move=> Hna. case E: (frames pre Y) => [//|fx fs].
have Hfx : fx \in frames pre Y by rewrite E mem_head.
have [Hin Hc] := frames_callee Hfx.
have := pend_callee_called Hin. rewrite Hc => Hcall.
move: Hna. by rewrite /active Hcall orbT.
Qed.

Lemma inactive_events pre Y :
  well_bracketed_trace stack_state0 pre -> ~~ active pre Y -> rp_events pre Y = [::].
Proof.
elim/last_ind: pre => [//|pre e IH] /wb_rcons [Hwb He] Hna.
have Hna' : ~~ active pre Y.
{ apply/negP => H. move: Hna. by rewrite active_rcons H. }
rewrite rp_events_rcons (IH Hwb Hna') /=.
have [Hcur _ _] := pend_inv Hwb.
move: He => /= /andP [/eqP Hce _].
case: eqP => // HY.
exfalso. move: Hna'. by rewrite -HY -Hce Hcur topcomp_active.
Qed.

