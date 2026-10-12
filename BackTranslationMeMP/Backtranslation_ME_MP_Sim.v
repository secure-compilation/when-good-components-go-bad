Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Traces.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.CompCertExtensions.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq fintype.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.WordExtra.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.LabelScheme.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.BufferShape.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import MicroPolicies.Recomposition.EncodeCode.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import T2M.MMemBase.
Require Import T2M.MPos.
Require Import Backtranslation_ME_MP.
Require Import Backtranslation_ME_MP_Step.
Require Import Backtranslation_ME_MP_Seg.
Require Import Backtranslation_ME_MP_Alloc.
Require Import Backtranslation_ME_MP_Layout.
Require Import Backtranslation_ME_MP_Run.
Require Import Backtranslation_ME_MP_Pos.
Require Import Backtranslation_ME_MP_Trace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Lemma regs_ok_reg0 : regs_ok (reg0 (mt := mt)).
Proof.
move=> k. rewrite /rkeys !inE.
move=> /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|
        /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]]]]]]]]].
all: rewrite /reg0 mkfmapE /= !(won_eqE (small_lt_reg _) (small_lt_reg _)) //=.
all: by eexists.
Qed.

Lemma hasNIn (T : Type) (p : pred T) (s : seq T) :
  (forall x, List.In x s -> ~~ p x) -> ~~ has p s.
Proof.
elim: s => [//|y s IH] H /=. rewrite negb_or (H y (or_introl erefl)) /=.
apply: IH => x Hx. apply: H. by right.
Qed.

Lemma In_flatten_map (A B : Type) (f : A -> seq B) (l : seq A) x :
  List.In x (flatten (map f l)) -> exists a, List.In a l /\ List.In x (f a).
Proof.
elim: l => [//|a l IH] /= Hx.
case: (List.in_app_or _ _ _ Hx) => H; first by exists a; split; [left|].
have [a' [H1 H2]] := IH H. exists a'. split; [right|]; by [].
Qed.

Lemma mtr_star NC s tr s' :
  mtr NC s tr s' -> star (prog_step_me NC) tt s tr s'.
Proof.
elim=> [s0|s1 s2 tr0 s3 H _ IH|s1 s2 e tr0 s3 H _ IH].
- exact: star_refl.
- apply: (@star_step _ _ _ _ s1 [::] s2 tr0 s3 tr0 _ IH); [exact: H | exact: erefl].
- apply: (@star_step _ _ _ _ s1 [:: e] s2 tr0 s3 (e :: tr0) _ IH); [exact: H | exact: erefl].
Qed.

Lemma notin_take_index (T : eqType) (x : T) (s : seq T) : x \notin take (index x s) s.
Proof.
elim: s => [//|y s IH] /=. case: eqP => [_|Hne] //=.
rewrite inE negb_or IH andbT. apply/eqP => E. exact: Hne (esym E).
Qed.

Section Sim.

Variables (L P C NC : nat) (Ip Ic : Program.interface)
          (Bp Bc : NMap {fmap Block.id -> nat + seq value}) (t : trace).

Local Notation PI := (unionm Ip Ic).
Local Notation PB := (unionm Bp Bc).
Local Notation cc := (rp_comp_code L P C PI PB t).
Local Notation bp := (rp_program L P C PI PB t Ip Bp).
Local Notation bc := (rp_program L P C PI PB t Ic Bc).
Local Notation cde := (code bp ++ code bc).

Definition comps : seq nat := domm Ip ++ domm Ic.

Lemma cde_flat : cde = flatten [seq cc c | c <- comps].
Proof. by rewrite /comps map_cat flatten_cat. Qed.

Definition Apre (X : nat) := flatten [seq cc c | c <- take (index X comps) comps].
Definition Bpost (X : nat) := flatten [seq cc c | c <- drop (index X comps).+1 comps].

Lemma cde_split X : X \in comps -> cde = Apre X ++ cc X ++ Bpost X.
Proof.
move=> HX. rewrite cde_flat /Apre /Bpost.
have Hi : index X comps < size comps by rewrite index_mem.
rewrite -{1}(cat_take_drop (index X comps) comps) (drop_nth X Hi) nth_index //.
by rewrite map_cat flatten_cat /= catA.
Qed.

Local Notation WB := (unionm (prog_buffers bp) (prog_buffers bc)).
Local Notation pc0 := (size (initial_memory (mt := mt) WB)).

Definition ev0 : event := ERet 0 BinNums.Z0 0.

Definition zarg (e : event) : BinNums.Z :=
  match e with ECall _ _ z _ => z | ERet _ z _ => z end.

Definition retpos (cl k : nat) : nat :=
  (nCk L P C PI PB t cl (Apre cl) k + 4
   + size (rp_load (rp_word (zarg (nth ev0 (rp_events t cl) k))) R_COM R_ARG)).+1.

Definition frw (fx : nat * pent) : mword mt :=
  pcw (pc0 + retpos (pcaller fx.2) (pidx fx.2)).

Definition comp_mem (pre : trace) (m : {fmap mword mt -> matom}) (X : nat) : Prop :=
  if active pre X then
    [/\ m (pcw (rp_addr PB X)) = Some (Atom (ctrlw NC X) (MTag Other X None false)),
        m (ctrlw NC X) = Some (Atom (pcw (size (rp_events pre X))) (MTag Other X None false)),
        m (cellw NC X 1)
        = Some (Atom (cellw NC X (2 + size (frames pre X))) (MTag Other X None false)),
        (forall j fx, List.nth_error (frames pre X) j = Some fx ->
            m (cellw NC X (2 + j)) = Some (Atom (frw fx) (MTag (Ret fx.1) X None false)))
      & (forall j, j < size t ->
            exists v vt, m (cellw NC X (2 + j)) = Some (Atom v (MTag vt X None false)))]
  else
    m (pcw (rp_addr PB X)) = Some (Atom 0%w (MTag Other X None false))
    /\ (forall w, pfilterC NC X w -> m w = None).

Record MI (pre : trace) (m : {fmap mword mt -> matom}) : Prop := {
  mi_code : code_in cde pc0 m;
  mi_gap : m (pcw alloc_label) = None;
  mi_comp : forall X, X \in comps -> comp_mem pre m X
}.

Definition Disp (pre : trace) (s : mstate) : Prop :=
  exists m rg,
    [/\ s = @Symbolic.State mt lrc_tags unit m rg
              (Atom (pcw (pc0 + nD L P C PI PB t (topcomp (pend pre)) (Apre (topcomp (pend pre)))))
                    (LRC.Level (size (pend pre)) (topcomp (pend pre)))) tt,
        MI pre m
      & regs_ok rg].

Hypothesis Hcomp : forall X, X \in comps -> 1 + X < 2 ^ NC.
Hypothesis HNCws : NC <= word_size mt.
Hypothesis HKal : alloc_label < 2 ^ (word_size mt - NC).
Hypothesis HKt : (size t).+4 <= 2 ^ (word_size mt - NC).
Hypothesis Hstat : forall X, X \in comps ->
  linearize_bufs PB (X, rp_block PB X, 0) <> None.
Hypothesis HbufsW : bufs_shape WB = bufs_shape PB.
Hypothesis Hdata : size (linearize_bufs PB) < 2 ^ 14.

Definition zone (X : nat) (w : mword mt) : bool :=
  (w == pcw (rp_addr PB X)) || pfilterC NC X w.

Lemma rp_addr_lt X : X \in comps -> rp_addr PB X < 2 ^ 14.
Proof.
move=> HX.
have Hin : (X, rp_block PB X, 0) \in domm (linearize_bufs PB).
{ rewrite mem_domm. case E: (linearize_bufs PB _) => //. by have := Hstat HX. }
have H := nat_addr_lt Hin. rewrite /nat_addr add0n in H.
exact: ltn_trans H Hdata.
Qed.

Lemma static_val X : X \in comps ->
  (\val (pcw (rp_addr PB X) : mword mt) : nat) = rp_addr PB X.
Proof.
move=> HX. rewrite /word_of_nat valw_as_word. apply: modn_small.
apply: (ltn_trans (rp_addr_lt HX)). by rewrite word_size_mt ltn_exp2l.
Qed.

Lemma static_not_region X Y : X \in comps -> Y \in comps ->
  ~~ pfilterC NC Y (pcw (rp_addr PB X)).
Proof.
move=> HX HY. apply: (low_not_region HNCws (Hcomp HY)).
apply: (leq_ltn_trans (eq_leq (static_val HX))).
apply: (ltn_trans (rp_addr_lt HX)). exact: HKal.
Qed.

Lemma static_inj X Y : X \in comps -> Y \in comps ->
  pcw (rp_addr PB X) = pcw (rp_addr PB Y) :> mword mt -> X = Y.
Proof.
move=> HX HY.
have HinX : (X, rp_block PB X, 0) \in domm (linearize_bufs PB).
{ rewrite mem_domm. case E': (linearize_bufs PB _) => //. by have := Hstat HX. }
have HinY : (Y, rp_block PB Y, 0) \in domm (linearize_bufs PB).
{ rewrite mem_domm. case E': (linearize_bufs PB _) => //. by have := Hstat HY. }
move=> E.
have Ev := etrans (esym (static_val HX))
             (etrans (congr1 (fun w : mword mt => (\val w : nat)) E) (static_val HY)).
have H := nat_addr_inj HinX HinY. rewrite /nat_addr !add0n in H.
by case: (H Ev).
Qed.

Lemma zone_disj X Y w : X \in comps -> Y \in comps -> X <> Y -> zone X w -> zone Y w -> False.
Proof.
move=> HX HY Hne. rewrite /zone => /orP [/eqP Ex|Rx] /orP [/eqP Ey|Ry].
- exact: Hne (static_inj HX HY (etrans (esym Ex) Ey)).
- move: Ry. by rewrite Ex (negbTE (static_not_region HX HY)).
- move: Rx. by rewrite Ey (negbTE (static_not_region HY HX)).
- exact: Hne (region_disj HNCws (Hcomp HX) (Hcomp HY) Rx Ry).
Qed.

Lemma ctrlw_zone Y : Y \in comps -> zone Y (ctrlw NC Y).
Proof.
move=> HY. rewrite /zone. apply/orP; right.
apply: (region_key HNCws (Hcomp HY)). apply: leq_trans _ HKt. by [].
Qed.

Lemma cellw_zone Y j : Y \in comps -> j < size t + 2 -> zone Y (cellw NC Y j).
Proof.
move=> HY Hj. rewrite /zone. apply/orP; right.
apply: (cellw_region HNCws (Hcomp HY)). apply: leq_trans _ HKt. clear -Hj. lia.
Qed.

Lemma comp_mem_frame pre pre' (m m' : {fmap mword mt -> matom}) Y :
  Y \in comps -> size pre <= size t ->
  (forall w, zone Y w -> m' w = m w) ->
  active pre' Y = active pre Y ->
  size (rp_events pre' Y) = size (rp_events pre Y) ->
  frames pre' Y = frames pre Y ->
  comp_mem pre m Y -> comp_mem pre' m' Y.
Proof.
move=> HY Hpre Hz Ha Hc Hf. rewrite /comp_mem Ha Hc Hf.
have Hst : m' (pcw (rp_addr PB Y)) = m (pcw (rp_addr PB Y)).
{ apply: Hz. by rewrite /zone eqxx. }
case: (active pre Y).
- case=> H1 H2 H3 H4 H5. split.
  + by rewrite Hst.
  + by rewrite Hz ?ctrlw_zone.
  + rewrite Hz; first exact: H3. apply: cellw_zone HY _. by rewrite addn2.
  + move=> j fx Hj. rewrite Hz; first exact: H4 j fx Hj.
    apply: cellw_zone HY _.
    have Hjs : j < size (frames pre Y) := nth_error_size Hj.
    have := leq_trans (size_frames_le pre Y) (leq_trans (size_pend_le pre) Hpre).
    move=> Hle. rewrite addnC ltn_add2r. exact: leq_trans Hjs Hle.
  + move=> j Hj. rewrite Hz; first exact: H5 j Hj.
    apply: cellw_zone HY _. by rewrite addnC ltn_add2r.
- case=> H1 H2. split.
  + by rewrite Hst.
  + move=> w Hw. rewrite Hz; first exact: H2 w Hw. by rewrite /zone Hw orbT.
Qed.

Hypothesis Hdis : fdisjoint (domm Ip) (domm Ic).
Hypothesis Hcok : forall X, X \in comps -> comp_ok L P C PI t X.
Hypothesis Hcs : pc0 + size cde < alloc_label.
Hypothesis Hwb : well_bracketed_trace stack_state0 t.
Hypothesis Hcev : forall e, List.In e t ->
  (cur_comp_of_event e \in comps) && (next_comp_of_event e \in comps).
Hypothesis Ht14 : (size t).+4 < 2 ^ 14.

Lemma Hbound : pc0 + size cde < 2 ^ word_size mt.
Proof. apply: (ltn_trans Hcs). by rewrite word_size_mt /alloc_label ltn_exp2l. Qed.

Lemma Huniq : uniq (clabs cde).
Proof.
apply: code_uniq Hdis _ => c Hc. apply: Hcok. by rewrite /comps mem_cat.
Qed.

Lemma ev_split pre e suf X :
  t = pre ++ e :: suf -> X = topcomp (pend pre) ->
  [/\ cur_comp_of_event e = X,
      size (rp_events pre X) < size (rp_events t X),
      nth ev0 (rp_events t X) (size (rp_events pre X)) = e
    & X \in comps].
Proof.
move=> Et EX.
have Hwb' := Hwb. rewrite Et well_bracketed_trace_cat in Hwb'.
case/andP: Hwb' => Hwp Hws.
have [Hcur _ _] := pend_inv Hwp.
move: Hws => /= /andP [/eqP He _].
have Ece : cur_comp_of_event e = X by rewrite -He Hcur EX.
have HtX : rp_events t X = rp_events pre X ++ e :: rp_events suf X.
{ by rewrite Et /rp_events filter_cat /= Ece eqxx. }
have Hin : List.In e t.
{ rewrite Et. apply: List.in_or_app. right. by left. }
split.
- exact: Ece.
- by rewrite HtX size_cat /= addnS ltnS leq_addr.
- by rewrite HtX nth_cat ltnn subnn.
- have := Hcev Hin. by rewrite Ece => /andP [].
Qed.

Local Notation S m rg n lv cid :=
  (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (pc0 + n)) (LRC.Level lv cid)) tt).

Lemma nCs_le_nCk X k : nCs L P C PI PB t X (Apre X) <= nCk L P C PI PB t X (Apre X) k.
Proof. exact: leq_addr. Qed.

Lemma disp_case pre e suf s :
  t = pre ++ e :: suf -> Disp pre s ->
  exists m rg1,
    [/\ MI pre m,
        msil NC s
          (S (setm m (ctrlw NC (topcomp (pend pre)))
                (Atom (pcw (size (rp_events pre (topcomp (pend pre)))).+1)
                      (MTag Other (topcomp (pend pre)) None false)))
             rg1
             (nCk L P C PI PB t (topcomp (pend pre)) (Apre (topcomp (pend pre)))
                  (size (rp_events pre (topcomp (pend pre))))).+4
             (size (pend pre)) (topcomp (pend pre))),
        rg1 (rk R_AUX1) = Some (Atom (ctrlw NC (topcomp (pend pre))) Other)
      & regs_ok rg1].
Proof.
move=> Et [m [rg [-> HMI Hok]]].
set X := topcomp (pend pre).
set k := size (rp_events pre X).
have [Hce Hk Hnth HX] := ev_split Et (erefl X).
have Hact : active pre X := topcomp_active pre.
have Hcm := mi_comp HMI HX. rewrite /comp_mem Hact in Hcm.
case: Hcm => Hs Hctr H1 Hfr Hcells.
have Hsplit := cde_split HX.
have Hbd := blk_disp Hsplit.
have HA : rp_addr PB X < 2 ^ 14 := rp_addr_lt HX.
have Hne : size (rp_events t X) <= 2 ^ 14.
{ rewrite /rp_events size_filter. apply: ltnW. apply: (leq_ltn_trans (count_size _ _)).
  apply: leq_ltn_trans _ Ht14. by rewrite -addn4 leq_addr. }
have Hlab := lab_at_case Huniq Hsplit ev0 Hk.
have Hkp : nD L P C PI PB t X (Apre X) + size (rp_disp L X (rp_addr PB X) (size (rp_events t X)))
           <= nCk L P C PI PB t X (Apre X) k := nCs_le_nCk X k.
have [rg1 [Hs1 Ha1 Ha2 Hok1]] :=
  run_disp_hit NC Hbound Hcs (size (pend pre)) (mi_code HMI) Hbd Hok HA Hs Hctr Hk Hne Hlab Hkp.
have Hbc := blk_case Hsplit (ev0 := ev0) Hk.
have Hbody : 0 < size (rp_case_body L P C X (k, nth ev0 (rp_events t X) k).2).
{ rewrite /=. case: (nth ev0 _ k) => [? ? ? ?|? ? ?].
  - by rewrite /rp_case_body size_cat /= addn2.
  - by rewrite /rp_case_body /=. }
have [rg2 [Hs2 Ha3 Hok2]] := run_case_pro NC Hbound (size (pend pre)) (mi_code HMI) Hbc Hbody Hok1 Ha1 Ha2 Hctr.
exists m, rg2. split.
- exact: HMI.
- exact: msil_trans Hs1 Hs2.
- exact: Ha3.
- exact: Hok2.
Qed.

Hypothesis Hmain : Component.main \in comps.

Lemma calls_into_in pre suf X :
  t = pre ++ suf -> calls_into pre X -> X \in comps.
Proof.
move=> Et.
have Hsub : forall e, List.In e pre -> List.In e t.
{ move=> e He. rewrite Et. apply: List.in_or_app. by left. }
elim: pre Hsub {Et} => [//|e pre IH] Hsub /= /orP [He|Hr].
- case: e He Hsub => [C0 P0 z C'|//] /eqP <- Hsub.
  have := Hcev (Hsub _ (or_introl erefl)). by case/andP.
- apply: IH Hr => e' He'. apply: Hsub. by right.
Qed.

Lemma topcomp_in pre suf : t = pre ++ suf -> topcomp (pend pre) \in comps.
Proof.
move=> Et. rewrite /topcomp. case E: (pend pre) => [|x st]; first exact: Hmain.
apply: (calls_into_in Et). apply: pend_callee_called. by rewrite E mem_head.
Qed.

Lemma won_val_small (x : nat) : x < 2 ^ 14 ->
  (\val (pcw x : mword mt) : nat) = x.
Proof.
move=> Hx. rewrite /word_of_nat valw_as_word. apply: modn_small.
apply: (ltn_trans Hx). by rewrite word_size_mt ltn_exp2l.
Qed.

Lemma code_not_region Y w : Y \in comps -> pfilterC NC Y w -> encode_code cde pc0 w = None.
Proof.
move=> HY Hw. case E: (encode_code cde pc0 w) => [v|//]. exfalso.
have [n [Ew [Hn _]]] := encode_code_nth_inv E.
have Hlt : n + pc0 < 2 ^ 14.
{ apply: leq_ltn_trans _ Hcs. rewrite addnC leq_add2l. exact: ltnW. }
have Hlow := low_not_region HNCws (Hcomp HY)
               (leq_ltn_trans (eq_leq (won_val_small Hlt)) (ltn_trans Hlt HKal)).
move: Hlow. by rewrite -Ew Hw.
Qed.

Lemma pc0E : pc0 = size (linearize_bufs PB).
Proof.
have Ht : size (linearize_bufs WB) < 2 ^ word_size mt.
{ rewrite (total_shape HbufsW). apply: (ltn_trans Hdata). by rewrite word_size_mt ltn_exp2l. }
by rewrite (initial_memory_size_eq Ht) (total_shape HbufsW).
Qed.

Lemma static_not_code X : X \in comps -> encode_code cde pc0 (pcw (rp_addr PB X)) = None.
Proof.
move=> HX.
have Hin : (X, rp_block PB X, 0) \in domm (linearize_bufs PB).
{ rewrite mem_domm. case E': (linearize_bufs PB _) => //. by have := Hstat HX. }
have H := nat_addr_lt Hin. rewrite /nat_addr add0n in H.
case E: (encode_code cde pc0 _) => [v|//]. exfalso.
have [n [Ew [Hn _]]] := encode_code_nth_inv E.
have Hlt : n + pc0 < 2 ^ 14.
{ apply: leq_ltn_trans _ Hcs. rewrite addnC leq_add2l. exact: ltnW. }
have Ev := etrans (esym (won_val_small (rp_addr_lt HX)))
             (etrans (congr1 (fun w : mword mt => (\val w : nat)) Ew) (won_val_small Hlt)).
have Hp := pc0E. clear -Ev H Hp. rewrite /rp_addr in Ev. lia.
Qed.

Lemma no_alloc_label : findopt (is_label_def alloc_label) cde = None.
Proof.
apply: findopt_notIn_None => -[i tg] Hin. rewrite /is_label_def /=.
case: i Hin => // l Hin. apply/eqP => El. subst l.
have Hl : alloc_label \in clabs cde.
{ elim: (cde) Hin => [//|[i' tg'] cd IH] /= [Ex|Hx].
  - case: Ex => -> _. by rewrite /clabs /= mem_head.
  - have H := IH Hx. rewrite /clabs in H. rewrite /clabs /=.
    case: i' => //= l'. by rewrite inE H orbT. }
rewrite cde_flat clabs_flatten -map_comp in Hl.
case/flattenP: Hl => ls /mapP [c Hc ->] Hlc.
have [o|o] := clabs_owned (Hcok Hc) Hlc.
- case: o => j [_ E]. exact: mk_body_neq_alloc (esym E).
- case: o => p [_ E]. exact: mk_entry_neq_alloc (esym E).
Qed.

Lemma alloc_not_zone Y : Y \in comps -> ~~ zone Y (pcw alloc_label).
Proof.
move=> HY. rewrite /zone negb_or. apply/andP; split.
- apply/eqP => E.
  have Hal14 : alloc_label < 2 ^ 15 by rewrite /alloc_label ltn_exp2l.
  have Hv : (\val (pcw alloc_label : mword mt) : nat) = alloc_label.
  { rewrite /word_of_nat valw_as_word. apply: modn_small.
    apply: (ltn_trans Hal14). by rewrite word_size_mt ltn_exp2l. }
  have Ev := etrans (esym Hv) (etrans (congr1 (fun w : mword mt => (\val w : nat)) E)
                                      (won_val_small (rp_addr_lt HY))).
  have := rp_addr_lt HY. rewrite -Ev /alloc_label ltnn. by [].
- apply: (low_not_region HNCws (Hcomp HY)).
  have Hv : (\val (pcw alloc_label : mword mt) : nat) = alloc_label.
  { have Hal14 : alloc_label < 2 ^ 15 by rewrite /alloc_label ltn_exp2l.
    rewrite /word_of_nat valw_as_word. apply: modn_small.
    apply: (ltn_trans Hal14). by rewrite word_size_mt ltn_exp2l. }
  apply: (leq_ltn_trans (eq_leq Hv)). exact: HKal.
Qed.

Lemma blk_key_region Y B w v :
  Y \in comps -> B.+1 < 2 ^ (word_size mt - NC) ->
  mkfmap (blkseq NC Y B) w = Some v -> pfilterC NC Y w.
Proof.
move=> HY HB. rewrite mkfmapE /blkseq /mkseq.
have Hreg : forall n, n < B ->
    pfilterC NC Y (addw (rpre NC Y) (word.as_word (ssrint.Posz (n + 1)))).
{ move=> n Hn. rewrite addn1. apply: (region_key HNCws (Hcomp HY)). clear -Hn HB. lia. }
move=> Hget.
suff [n [Hn ->]] : exists n, n \in iota 0 B /\
    w = addw (rpre NC Y) (word.as_word (ssrint.Posz (n + 1))).
{ apply: Hreg. move: Hn. by rewrite mem_iota add0n. }
move: Hget. elim: (iota 0 B) => [//|n ns IH] /=.
case: eqP => [->|_] H.
- exists n. by rewrite mem_head.
- have [n' [Hn' E']] := IH H. exists n'. by rewrite inE Hn' orbT.
Qed.

Lemma setm_out (m : {fmap mword mt -> @matom mt}) a (v : @matom mt) w Y :
  zone Y a -> ~~ zone Y w -> setm m a v w = m w.
Proof.
move=> Ha Hw. rewrite setmE. case: eqP => // E. by rewrite E Ha in Hw.
Qed.

Lemma size_rp_init_pos L' t' cid A j : 0 < size (rp_init L' t' cid A j).
Proof. by rewrite /rp_init. Qed.

Lemma entry_land (m : {fmap mword mt -> matom}) (rg : rmap) lv Y i p cap l0 :
  Y \in comps ->
  List.nth_error (rp_exports PI Y) i = Some p ->
  code_in cde pc0 m -> regs_ok rg ->
  rg (wk 4) = Some (Atom cap (Ret l0)) ->
  exists rg',
    [/\ msil NC (S m rg (nE L PB t Y (Apre Y) i) lv Y)
                (S m rg' (nI L P C PI PB t Y (Apre Y)) lv Y),
        rg' (rk R_AUX2) = Some (Atom cap (Ret l0))
      & regs_ok rg'].
Proof.
move=> HY Hi Hc Hok Hra.
have Hsplit := cde_split HY.
have [Hcell Hbe Hf] := entry_cells Huniq Hsplit Hi.
have [Hmv Hgo] := blk_cons Hbe.
have [rc Hrc] := regs_ok_rk R_COM Hok.
have [i1 [tg1 [Hn1 Hc1]]] : nxt cde (nE L PB t Y (Apre Y) i).+1 Y := blk_nxt Hbe erefl.
have S1 := me_step_label NC Hbound lv Hc Hcell erefl erefl Hn1 Hc1 Hrc.
have Hra' : rg (rk R_RA) = Some (Atom cap (Ret l0)) := Hra.
have S2 := step_mov_blk NC Hbound lv Hc Hbe (blk_nxt Hgo erefl) Hok Hra'.
rewrite /= in S2.
set rg2 := setm (setm rg (rk R_RA) (Atom cap Invalidated)) (rk R_AUX2) (Atom cap (Ret l0)).
have Hok2 : regs_ok rg2 := regs_ok_setm _ _ (regs_ok_setm _ _ Hok).
have Hl3 := lab_at_3 Huniq Hsplit.
have HT := blk_T Hsplit.
have [_ HT1] := blk_cons HT.
have Hx3 : nxt cde (nE L PB t Y (Apre Y) i).+3 Y.
{ apply: (nxt_block Huniq Hsplit).
  - rewrite /nE. lia.
  - rewrite size_cc /nE.
    have Hi' : i < size (rp_exports PI Y) := nth_error_size Hi.
    have HTl : 0 < size (Tl L P C PB t Y) by [].
    clear -Hi' HTl. lia. }
have S3 := step_goto_blk NC Hbound Hcs lv Hc Hgo Hx3 Hl3 Hok2.
set rg3 := setm rg2 (wk 4) (Atom (pcw (pc0 + (nE L PB t Y (Apre Y) i).+3)) InternalJump).
have Hok3 : regs_ok rg3 := regs_ok_setm _ _ Hok2.
have HI : nxt cde (nT L P C PI PB t Y (Apre Y)).+1 Y.
{ apply: (blk_nxt HT1). rewrite size_cat.
  exact: (leq_trans (size_rp_init_pos L t Y _ 2) (leq_addr _ _)). }
have S4 := step_label_blk NC Hbound lv Hc HT HI Hok3.
exists rg3. split.
- apply: (msil_step S1). apply: (msil_step S2). apply: (msil_step S3). exact: msil_one S4.
- rewrite /rg3 setm_ne'; last exact: (wk_eq (erefl : 3 < 20) (erefl : 4 < 20)).
  rewrite /rg2 setmE (eqxx (rk R_AUX2)). exact: erefl.
- exact: Hok3.
Qed.

Lemma frames_lt_t pre e suf Y : t = pre ++ e :: suf -> size (frames pre Y) < size t.
Proof.
move=> Et. apply: (leq_ltn_trans (size_frames_le pre Y)).
apply: (leq_ltn_trans (size_pend_le pre)). by rewrite Et size_cat /= addnS ltnS leq_addr.
Qed.

Lemma act_active pre e suf (m1 : {fmap mword mt -> matom}) (rg : rmap) Y X P' z cap :
  t = pre ++ e :: suf -> e = ECall X P' z Y -> X <> Y -> Y \in comps ->
  code_in cde pc0 m1 -> m1 (pcw alloc_label) = None ->
  active pre Y -> comp_mem pre m1 Y ->
  regs_ok rg -> rg (rk R_AUX2) = Some (Atom cap (Ret (size (pend pre)))) ->
  cap = frw (size (pend pre), (X, size (rp_events pre X), Y)) ->
  exists m3 rg',
    [/\ msil NC (S m1 rg (nI L P C PI PB t Y (Apre Y)) (size (pend pre)).+1 Y)
                (S m3 rg' (nD L P C PI PB t Y (Apre Y)) (size (pend pre)).+1 Y),
        regs_ok rg',
        code_in cde pc0 m3 /\ m3 (pcw alloc_label) = None,
        (forall w, ~~ zone Y w -> m3 w = m1 w)
      & comp_mem (rcons pre e) m3 Y].
Proof.
move=> Et Ee HXY HY Hc Hgap Hact Hcm Hok Ha2 Hcap.
have Hsplit := cde_split HY.
move: Hcm. rewrite /comp_mem Hact => -[Hs Hctr H1 Hfr Hcells].
set lv := size (pend pre).
set d := size (frames pre Y).
have Hd : d < size t := frames_lt_t Y Et.
have HcY := Hcomp HY.
have HK2 : 2 <= 2 ^ (word_size mt - NC) by apply: leq_trans _ HKt.
have Hbi := blk_init2 Hsplit.
have Hba := blk_after_init Hsplit.
have Hxi : nxt cde (nPu L P C PI PB t Y (Apre Y)) Y.
{ apply: (blk_nxt Hba). by rewrite size_cat. }
have [rg1 [S1 Hr1 Hr2 Hok1]] :=
  run_init_skip NC Hbound Hcs (size (pend pre)).+1 Hc Hbi Hxi (lab_at_2 Huniq Hsplit) Hok
    (rp_addr_lt HY) Hs (ctrlw_neq0 HNCws HcY HK2).
rewrite Ha2 in Hr2.
have Hcl : 0 < size (rp_goto L Y 0 ++ rp_disp L Y (rp_addr PB Y) (size (rp_events t Y))
                    ++ flatten (cases_l L P C t Y) ++ [:: MrHalt]) by [].
have [vo [vto Hold]] := Hcells d Hd.
have Hjb : forall j, j < size t + 2 -> j.+2 <= 2 ^ (word_size mt - NC).
{ move=> j Hj. apply: leq_trans _ HKt. clear -Hj. lia. }
have Hd2 : 2 + d < size t + 2 by rewrite addnC ltn_add2r.
have Hne1 : (cellw NC Y 1 == cellw NC Y (2 + d)) = false.
{ apply: (cellw_ne HNCws HcY (Hjb 1 _) (Hjb _ Hd2)); first by rewrite addn2.
  move=> E. clear -E. lia. }
have Hncf : encode_code cde pc0 (cellw NC Y (2 + d)) = None.
{ apply: (code_not_region HY). exact: (@cellw_region NC HNCws Y (2 + d) HcY (Hjb _ Hd2)). }
have [rg2 [S2 Hr2' Hok2]] :=
  run_push NC Hbound (size (pend pre)).+1 Hc Hba Hcl Hok1 Hr1 Hr2 H1 Hold
    (negbT Hne1) Hncf.
set m3 := setm (setm m1 (cellw NC Y (2 + d)) (Atom cap (MTag (Ret lv) Y None false)))
               (cellw NC Y 1) (Atom (cellw NC Y (2 + d).+1) (MTag Other Y None false)).
have Hz1 : zone Y (cellw NC Y 1) by apply: cellw_zone HY _; rewrite addn2.
have Hzd : zone Y (cellw NC Y (2 + d)) by apply: cellw_zone HY Hd2.
have Hout : forall w, ~~ zone Y w -> m3 w = m1 w.
{ move=> w Hw. rewrite /m3 (setm_out _ _ Hz1 Hw). exact: setm_out _ _ Hzd Hw. }
have Hnc1 : encode_code cde pc0 (cellw NC Y 1) = None.
{ have H1b : 1 < size t + 2 by rewrite addn2.
  apply: (code_not_region HY). exact: (@cellw_region NC HNCws Y 1 HcY (Hjb 1 H1b)). }
have Hc3 : code_in cde pc0 m3.
{ apply: code_in_setm Hnc1. exact: code_in_setm Hncf. }
have EG : nG L P C PI PB t Y (Apre Y) = (nPu L P C PI PB t Y (Apre Y)).+4.+2.
{ rewrite /nG /=. lia. }
have Hbg := blk_after_push Hsplit. rewrite EG in Hbg.
have [_ Hbd] := blk_cons Hbg.
have S3 := step_goto_blk NC Hbound Hcs (size (pend pre)).+1 Hc3 Hbg (blk_nxt Hbd erefl)
             (lab_at_0 Huniq Hsplit) Hok2.
exists m3, (setm rg2 (wk 4) (Atom (pcw (pc0 + (nPu L P C PI PB t Y (Apre Y)).+4.+3))
                                   InternalJump)).
split.
- apply: (msil_trans S1). apply: (msil_trans S2). exact: msil_one S3.
- exact: regs_ok_setm.
- split; first exact: Hc3. rewrite (Hout _ (alloc_not_zone HY)). exact: Hgap.
- exact: Hout.
- have Ecnt : size (rp_events (rcons pre e) Y) = size (rp_events pre Y).
  { rewrite size_rp_events_rcons Ee /=.
    have -> : (X == Y) = false by apply/eqP. by rewrite addn0. }
  have Efr : frames (rcons pre e) Y
             = frames pre Y ++ [:: (lv, (X, size (rp_events pre X), Y))].
  { by rewrite Ee frames_call eqxx. }
  rewrite /comp_mem active_rcons Hact /= Ecnt Efr.
  have Nst : forall j, j < size t + 2 -> (pcw (rp_addr PB Y) == cellw NC Y j) = false.
  { move=> j Hj. apply/eqP => E. have := static_not_region HY HY.
    rewrite E. by rewrite (@cellw_region NC HNCws Y j HcY (Hjb j Hj)). }
  have Nct : forall j, 0 < j -> j < size t + 2 -> (ctrlw NC Y == cellw NC Y j) = false.
  { move=> j H0 Hj. rewrite eq_sym. exact: (ctrl_cell_ne HNCws HcY (Hjb j Hj) H0). }
  have H1b : 1 < size t + 2 by rewrite addn2.
  split.
  + rewrite /m3 setmE (Nst 1 H1b) setmE (Nst _ Hd2). exact: Hs.
  + rewrite /m3 setmE (@Nct 1 erefl H1b) setmE (@Nct (2 + d) erefl Hd2). exact: Hctr.
  + rewrite /m3 setmE (eqxx (cellw NC Y 1)).
    have -> : 2 + size (frames pre Y ++ [:: (lv, (X, size (rp_events pre X), Y))]) = (2 + d).+1.
    { by rewrite size_cat /= addn1 addnS. }
    exact: erefl.
  + move=> j fx Hj.
    have Hjs : j < size (frames pre Y ++ [:: (lv, (X, size (rp_events pre X), Y))])
      := nth_error_size Hj.
    rewrite size_cat /= addn1 in Hjs.
    have Hj2 : 2 + j < size t + 2 by rewrite addnC ltn_add2r; exact: leq_ltn_trans _ Hd.
    have N1 : (cellw NC Y (2 + j) == cellw NC Y 1) = false.
    { apply: (cellw_ne HNCws HcY (Hjb _ Hj2) (Hjb 1 H1b)). move=> E. clear -E. lia. }
    case: (ltnP j d) => Hjd.
    * rewrite nth_error_cat_l in Hj; last exact: Hjd.
      have N2 : (cellw NC Y (2 + j) == cellw NC Y (2 + d)) = false.
      { apply: (cellw_ne HNCws HcY (Hjb _ Hj2) (Hjb _ Hd2)). move=> E. clear -E Hjd. lia. }
      rewrite /m3 setmE N1 setmE N2. exact: Hfr j fx Hj.
    * have Ejd : j = d by apply/eqP; rewrite eqn_leq Hjd andbT -ltnS.
      subst j.
      rewrite -[d]addn0 nth_error_cat_r /= in Hj. case: Hj => <-.
      rewrite /m3 setmE N1 setmE (eqxx (cellw NC Y (2 + d))) Hcap. exact: erefl.
  + move=> j Hj.
    have Hj2 : 2 + j < size t + 2 by rewrite addnC ltn_add2r.
    have N1 : (cellw NC Y (2 + j) == cellw NC Y 1) = false.
    { apply: (cellw_ne HNCws HcY (Hjb _ Hj2) (Hjb 1 H1b)). move=> E. clear -E. lia. }
    rewrite /m3 setmE N1 setmE.
    case: eqP => [_|_]; first by exists cap, (Ret lv).
    exact: Hcells j Hj.
Qed.

Lemma wb_prefix pre suf : t = pre ++ suf -> well_bracketed_trace stack_state0 pre.
Proof. move=> Et. have := Hwb. rewrite Et well_bracketed_trace_cat. by case/andP. Qed.

Lemma act_fresh pre e suf (m1 : {fmap mword mt -> matom}) (rg : rmap) Y X P' z cap :
  t = pre ++ e :: suf -> e = ECall X P' z Y -> X <> Y -> Y \in comps ->
  code_in cde pc0 m1 -> m1 (pcw alloc_label) = None ->
  ~~ active pre Y -> comp_mem pre m1 Y ->
  regs_ok rg -> rg (rk R_AUX2) = Some (Atom cap (Ret (size (pend pre)))) ->
  cap = frw (size (pend pre), (X, size (rp_events pre X), Y)) ->
  exists m3 rg',
    [/\ msil NC (S m1 rg (nI L P C PI PB t Y (Apre Y)) (size (pend pre)).+1 Y)
                (S m3 rg' (nD L P C PI PB t Y (Apre Y)) (size (pend pre)).+1 Y),
        regs_ok rg',
        code_in cde pc0 m3 /\ m3 (pcw alloc_label) = None,
        (forall w, ~~ zone Y w -> m3 w = m1 w)
      & comp_mem (rcons pre e) m3 Y].
Proof.
move=> Et Ee HXY HY Hc Hgap Hna Hcm Hok Ha2 Hcap.
have Hsplit := cde_split HY.
have Hna' : active pre Y = false by apply/negbTE.
move: Hcm. rewrite /comp_mem Hna' => -[Hs Hreg].
set lv := size (pend pre).
have HcY := Hcomp HY.
have Hjb : forall j, j < size t + 2 -> j.+2 <= 2 ^ (word_size mt - NC).
{ move=> j Hj. apply: leq_trans _ HKt. clear -Hj. lia. }
have Hbi := blk_init2 Hsplit.
have Hba := blk_after_init Hsplit.
have Hxi : nxt cde (nPu L P C PI PB t Y (Apre Y)) Y.
{ apply: (blk_nxt Hba). by rewrite size_cat. }
have HB : (rp_blocks t).+2 <= 2 ^ (word_size mt - NC) by rewrite /rp_blocks addn2.
have HB14 : rp_blocks t < 2 ^ 14.
{ rewrite /rp_blocks. apply: leq_ltn_trans _ Ht14. by rewrite addn2 ltnW. }
have Hregnc : forall w, pfilterC NC Y w -> encode_code cde pc0 w = None.
{ move=> w Hw. exact: code_not_region HY Hw. }
have [rg1 [S1 Hr1 Hr2 Hok1]] :=
  run_init_alloc Hbound Hcs (size (pend pre)).+1 Hc Hbi Hxi Hok (rp_addr_lt HY) Hs
    (static_not_code HY) Hgap no_alloc_label HNCws HcY HB HB14 Hreg Hregnc
    (static_not_region HY HY).
rewrite Ha2 in Hr2.
set B := rp_blocks t.
set blk0 := mkfmap (blkseq NC Y B).
set m2 := setm (setm (unionm m1 blk0) (pcw (rp_addr PB Y))
                     (Atom (ctrlw NC Y) (MTag Other Y None false)))
               (addw (ctrlw NC Y) (pcw 1))
               (Atom (addw (ctrlw NC Y) (pcw 2)) (MTag Other Y None false)).
have H1b : 1 < size t + 2 by rewrite addn2.
have Ht0 : 0 < size t by rewrite Et size_cat /= addnS.
have H2b : 2 < size t + 2 by clear -Ht0; lia.
have Hrg : forall j, j < size t + 2 -> pfilterC NC Y (cellw NC Y j).
{ move=> j Hj. exact: (@cellw_region NC HNCws Y j HcY (Hjb j Hj)). }
have Hctl : pfilterC NC Y (ctrlw NC Y).
{ apply: (ctrlw_region HNCws HcY). apply: leq_trans _ HKt. by []. }
have Nst : forall w, pfilterC NC Y w -> (w == pcw (rp_addr PB Y)) = false.
{ move=> w Hw. apply/eqP => E. move: (static_not_region HY HY). by rewrite -E Hw. }
have N21 : (cellw NC Y 2 == addw (ctrlw NC Y) (pcw 1)) = false.
{ apply: (cellw_ne HNCws HcY (Hjb 2 H2b) (Hjb 1 H1b)). by []. }
have Hblk : forall j, j < B -> blk0 (cellw NC Y j)
                                = Some (Atom (word.as_word (ssrint.Posz 0) : mword mt) (def_mem_tag Y false)).
{ move=> j Hj. have H := blkseq_get NC Y Hj. rewrite -(cellwE NC Y j) in H. exact: H. }
have HB2 : 2 < B by rewrite /B /rp_blocks addn2.
have Hold2 : m2 (cellw NC Y (2 + 0))
             = Some (Atom (word.as_word (ssrint.Posz 0) : mword mt) (MTag Other Y None false)).
{ rewrite /m2. apply: (etrans (setm_ne' _ _ N21)).
  apply: (etrans (setm_ne' _ _ (Nst _ (Hrg 2 H2b)))).
  rewrite unionmE (Hreg _ (Hrg 2 H2b)) /=. exact: Hblk 2 HB2. }
have Hsp : m2 (addw (ctrlw NC Y) (pcw 1))
           = Some (Atom (addw (ctrlw NC Y) (pcw (2 + 0))) (MTag Other Y None false)).
{ rewrite /m2 setmE (eqxx (addw (ctrlw NC Y) (pcw 1))). exact: erefl. }
have Hc2 : code_in cde pc0 m2.
{ apply: code_in_setm (code_not_region HY (Hrg 1 H1b)).
  apply: code_in_setm (static_not_code HY). exact: code_in_unionm. }
have Hcl : 0 < size (rp_goto L Y 0 ++ rp_disp L Y (rp_addr PB Y) (size (rp_events t Y))
                    ++ flatten (cases_l L P C t Y) ++ [:: MrHalt]) by [].
have Hne1 : addw (ctrlw NC Y) (pcw 1) != addw (ctrlw NC Y) (pcw (2 + 0)).
{ rewrite eq_sym. exact: negbT N21. }
have [rg2 [S2 Hr2' Hok2]] :=
  run_push NC Hbound (size (pend pre)).+1 Hc2 Hba Hcl Hok1 Hr1 Hr2 Hsp Hold2 Hne1
    (code_not_region HY (Hrg 2 H2b)).
set m3 := setm (setm m2 (cellw NC Y (2 + 0)) (Atom cap (MTag (Ret lv) Y None false)))
               (cellw NC Y 1) (Atom (cellw NC Y (2 + 0).+1) (MTag Other Y None false)).
have Hz1 : zone Y (cellw NC Y 1) := cellw_zone HY H1b.
have Hz2 : zone Y (cellw NC Y (2 + 0)) := cellw_zone HY H2b.
have HzA : zone Y (pcw (rp_addr PB Y)) by rewrite /zone eqxx.
have Hout : forall w, ~~ zone Y w -> m3 w = m1 w.
{ move=> w Hw. rewrite /m3 (setm_out _ _ Hz1 Hw) (setm_out _ _ Hz2 Hw) /m2.
  rewrite (setm_out _ _ Hz1 Hw) (setm_out _ _ HzA Hw) unionmE.
  case E1: (m1 w) => [v|] //=.
  case E2: (blk0 w) => [v|//].
  have HBK : B.+1 < 2 ^ (word_size mt - NC).
  { apply: leq_ltn_trans _ HKt. by rewrite /B /rp_blocks addn2. }
  have Hr := blk_key_region HY HBK E2.
  exfalso. move: Hw. by rewrite /zone Hr orbT. }
have Hc3 : code_in cde pc0 m3.
{ apply: code_in_setm (code_not_region HY (Hrg 1 H1b)).
  exact: code_in_setm (code_not_region HY (Hrg 2 H2b)). }
have EG : nG L P C PI PB t Y (Apre Y) = (nPu L P C PI PB t Y (Apre Y)).+4.+2.
{ rewrite /nG /=. lia. }
have Hbg := blk_after_push Hsplit. rewrite EG in Hbg.
have [_ Hbd] := blk_cons Hbg.
have S3 := step_goto_blk NC Hbound Hcs (size (pend pre)).+1 Hc3 Hbg (blk_nxt Hbd erefl)
             (lab_at_0 Huniq Hsplit) Hok2.
exists m3, (setm rg2 (wk 4) (Atom (pcw (pc0 + (nPu L P C PI PB t Y (Apre Y)).+4.+3))
                                   InternalJump)).
split.
- apply: (msil_trans S1). apply: (msil_trans S2). exact: msil_one S3.
- exact: regs_ok_setm.
- split; first exact: Hc3. rewrite (Hout _ (alloc_not_zone HY)). exact: Hgap.
- exact: Hout.
- have Hwbp := wb_prefix Et.
  have Ecnt : size (rp_events (rcons pre e) Y) = 0.
  { rewrite size_rp_events_rcons Ee (inactive_events Hwbp Hna) /=.
    have -> : (X == Y) = false by apply/eqP. by []. }
  have Efr : frames (rcons pre e) Y = [:: (lv, (X, size (rp_events pre X), Y))].
  { by rewrite Ee frames_call eqxx (inactive_frames Hna). }
  have Hact' : active (rcons pre e) Y by rewrite active_rcons Ee /= eqxx orbT.
  rewrite /comp_mem Hact' Ecnt Efr.
  have Nst2 : forall j, j < size t + 2 -> (pcw (rp_addr PB Y) == cellw NC Y j) = false.
  { move=> j Hj. rewrite eq_sym. exact: Nst _ (Hrg j Hj). }
  have Nct : forall j, 0 < j -> j < size t + 2 -> (ctrlw NC Y == cellw NC Y j) = false.
  { move=> j H0 Hj. rewrite eq_sym. exact: (ctrl_cell_ne HNCws HcY (Hjb j Hj) H0). }
  have N12 : (cellw NC Y 1 == cellw NC Y (2 + 0)) = false.
  { rewrite eq_sym. exact: N21. }
  split.
  + rewrite /m3 setmE (Nst2 1 H1b) setmE (Nst2 _ H2b) /m2 setmE.
    rewrite (_ : (pcw (rp_addr PB Y) == addw (ctrlw NC Y) (pcw 1)) = false); last exact: Nst2 1 H1b.
    rewrite setmE (eqxx (pcw (rp_addr PB Y) : mword mt)). exact: erefl.
  + rewrite /m3 setmE (@Nct 1 erefl H1b) setmE (@Nct 2 erefl H2b) /m2 setmE.
    rewrite (_ : (ctrlw NC Y == addw (ctrlw NC Y) (pcw 1)) = false); last exact: (@Nct 1 erefl H1b).
    rewrite setmE (Nst _ Hctl) unionmE (Hreg _ Hctl) /=.
    exact: (blkseq_get NC Y (j := 0) (ltn_trans (erefl : 0 < 2) HB2)).
  + rewrite /m3 setmE (eqxx (cellw NC Y 1)). exact: erefl.
  + move=> j fx. case: j => [|j] /= Hj; last by case: j Hj.
    case: Hj => Efx. subst fx.
    have N201 : (cellw NC Y (2 + 0) == cellw NC Y 1) = false := N21.
    rewrite /m3 setmE N201 setmE (eqxx (cellw NC Y (2 + 0))) Hcap. exact: erefl.
  + move=> j Hj.
    have Hj2 : 2 + j < size t + 2 by rewrite addnC ltn_add2r.
    have N1 : (cellw NC Y (2 + j) == cellw NC Y 1) = false.
    { apply: (cellw_ne HNCws HcY (Hjb _ Hj2) (Hjb 1 H1b)). move=> E. clear -E. lia. }
    rewrite /m3 setmE N1 setmE.
    case: eqP => [_|Hne2]; first by exists cap, (Ret lv).
    rewrite /m2 setmE.
    rewrite (_ : (cellw NC Y (2 + j) == addw (ctrlw NC Y) (pcw 1)) = false); last exact: N1.
    rewrite setmE (Nst _ (Hrg _ Hj2)) unionmE (Hreg _ (Hrg _ Hj2)) /=.
    have HjB : 2 + j < B by rewrite /B /rp_blocks addnC ltn_add2r.
    rewrite (Hblk _ HjB). exists (word.as_word (ssrint.Posz 0) : mword mt), Other. exact: erefl.
Qed.

Lemma comp_mem_counter pre e (m : {fmap mword mt -> matom}) X :
  X \in comps -> active pre X -> cur_comp_of_event e = X ->
  frames (rcons pre e) X = frames pre X ->
  size pre <= size t ->
  comp_mem pre m X ->
  comp_mem (rcons pre e)
    (setm m (ctrlw NC X) (Atom (pcw (size (rp_events pre X)).+1) (MTag Other X None false))) X.
Proof.
move=> HX Hact Hce Hfr Hlt Hcm.
have Hact' : active (rcons pre e) X by rewrite active_rcons Hact.
have Ecnt : size (rp_events (rcons pre e) X) = (size (rp_events pre X)).+1.
{ by rewrite size_rp_events_rcons Hce eqxx addn1. }
move: Hcm. rewrite /comp_mem Hact Hact' Ecnt Hfr => -[Hs Hctr H1 Hfrm Hcells].
have HcX := Hcomp HX.
have Hjb : forall j, j < size t + 2 -> j.+2 <= 2 ^ (word_size mt - NC).
{ move=> j Hj. apply: leq_trans _ HKt. clear -Hj. lia. }
have Hctl : pfilterC NC X (ctrlw NC X).
{ apply: (ctrlw_region HNCws HcX). apply: leq_trans _ HKt. by []. }
have Nst : (pcw (rp_addr PB X) == ctrlw NC X) = false.
{ apply/eqP => E. move: (static_not_region HX HX). by rewrite E Hctl. }
have Ncl : forall j, 0 < j -> j < size t + 2 -> (cellw NC X j == ctrlw NC X) = false.
{ move=> j H0 Hj. exact: (ctrl_cell_ne HNCws HcX (Hjb j Hj) H0). }
have H1b : 1 < size t + 2 by rewrite addn2.
split.
- by rewrite setmE Nst.
- rewrite setmE (eqxx (ctrlw NC X)). exact: erefl.
- rewrite setmE (@Ncl 1 erefl H1b). exact: H1.
- move=> j fx Hj.
  have Hjs := nth_error_size Hj.
  have Hj2 : 2 + j < size t + 2.
  { rewrite addnC ltn_add2r. apply: (leq_trans Hjs).
    apply: (leq_trans (size_frames_le _ _)). exact: (leq_trans (size_pend_le _) Hlt). }
  rewrite setmE (@Ncl (2 + j) erefl Hj2). exact: Hfrm j fx Hj.
- move=> j Hj. have Hj2 : 2 + j < size t + 2 by rewrite addnC ltn_add2r.
  rewrite setmE (@Ncl (2 + j) erefl Hj2). exact: Hcells j Hj.
Qed.

Hypothesis Hz : forall e, List.In e t ->
  Z.le (Z.opp (Z.pow 2 31)) (zarg e) /\ Z.lt (zarg e) (Z.pow 2 31).
Hypothesis Hcalls : forall C0 P0 z0 C', List.In (ECall C0 P0 z0 C') t ->
  [/\ P0 \in rp_exports PI C', C0 <> C'
    & C0 \in odflt [::] (omap snd (entry (Transitional.head_tag_gen PI C' P0)))].

Lemma call_step pre X P' z Y suf s :
  t = pre ++ ECall X P' z Y :: suf -> Disp pre s ->
  exists s', mtr NC s [:: ECall X P' z Y] s' /\ Disp (rcons pre (ECall X P' z Y)) s'.
Proof.
move=> Et Hd.
set e := ECall X P' z Y.
have Hin : List.In e t by rewrite Et; apply: List.in_or_app; right; left.
have [Hexp HXY Hlst] := Hcalls Hin.
have [Hce Hk Hnth HX] := ev_split Et (erefl (topcomp (pend pre))).
have EX : topcomp (pend pre) = X by rewrite -Hce.
rewrite EX in Hk Hnth HX.
have HY : Y \in comps by have := Hcev Hin; case/andP.
have [m [rg1 [HMI S1 Ha1 Hok1]]] := disp_case Et Hd.
rewrite EX in S1 Ha1.
set k := size (rp_events pre X) in S1 Hk Hnth.
set lv := size (pend pre) in S1.
set m1 := setm m (ctrlw NC X) (Atom (pcw k.+1) (MTag Other X None false)) in S1.
have HcX := Hcomp HX.
have Hctl : pfilterC NC X (ctrlw NC X).
{ apply: (ctrlw_region HNCws HcX). apply: leq_trans _ HKt. by []. }
have HzX : zone X (ctrlw NC X) by rewrite /zone Hctl orbT.
have Hc1 : code_in cde pc0 m1 := code_in_setm _ (mi_code HMI) (code_not_region HX Hctl).
have Hgap1 : m1 (pcw alloc_label) = None.
{ rewrite /m1 (setm_out _ _ HzX (alloc_not_zone HX)). exact: mi_gap HMI. }
have HsplitX := cde_split HX.
have Hbc := blk_case HsplitX (ev0 := ev0) Hk.
rewrite Hnth in Hbc.
have Hbb : blk cde (nCk L P C PI PB t X (Apre X) k).+4 X (rp_case_body L P C X e).
{ have [_ H] := blk_cat Hbc. by rewrite -addn4. }
have Hi : List.nth_error (rp_exports PI Y) (index P' (rp_exports PI Y)) = Some P'.
{ rewrite (nth_error_nth' P'); last by rewrite index_mem. by rewrite nth_index. }
have HsplitY := cde_split HY.
have [Hcell Hbe Hf] := entry_cells Huniq HsplitY Hi.
have HYX : Y != X by apply/eqP => E; apply: HXY; rewrite E.
have [rg2 [S2 Hra2 Hok2]] :=
  run_call NC Hbound Hcs lv Hc1 Hbb Hok1 Hf Hcell HYX Hlst (Hz Hin).
have [rg3 [S3 Ha3 Hok3]] := entry_land lv.+1 HY Hi Hc1 Hok2 Hra2.
have Hcap : pcw (pc0 + ((nCk L P C PI PB t X (Apre X) k).+4
                        + size (rp_load (rp_word z) R_COM R_ARG)).+1)
            = frw (lv, (X, k, Y)).
{ have Er : ((nCk L P C PI PB t X (Apre X) k).+4 + size (rp_load (rp_word z) R_COM R_ARG)).+1
             = retpos X k.
  { have Ez : zarg e = z := erefl.
    rewrite /retpos.
    rewrite Hnth.
    rewrite Ez.
    lia. }
  exact: (f_equal (fun x => pcw (pc0 + x) : mword mt) Er). }
have Hzone_m1 : forall w, ~~ zone X w -> m1 w = m w.
{ move=> w Hw. exact: setm_out _ _ HzX Hw. }
have Hpre : size pre <= size t by rewrite Et size_cat leq_addr.
have HcmY : comp_mem pre m1 Y.
{ apply: (comp_mem_frame HY Hpre _ erefl erefl erefl (mi_comp HMI HY)).
  move=> w Hw. apply: Hzone_m1. apply/negP => HwX.
  exact: zone_disj HX HY HXY HwX Hw. }
have [m3 [rg4 [S4 Hok4 [Hc3 Hg3] Hout HcmY']]] :
  exists m3 rg',
    [/\ msil NC (S m1 rg3 (nI L P C PI PB t Y (Apre Y)) lv.+1 Y)
                (S m3 rg' (nD L P C PI PB t Y (Apre Y)) lv.+1 Y),
        regs_ok rg',
        code_in cde pc0 m3 /\ m3 (pcw alloc_label) = None,
        (forall w, ~~ zone Y w -> m3 w = m1 w)
      & comp_mem (rcons pre e) m3 Y].
{ rewrite Hcap in Ha3.
  case Hact: (active pre Y).
  - exact: act_active Et erefl HXY HY Hc1 Hgap1 Hact HcmY Hok3 Ha3 erefl.
  - exact: act_fresh Et erefl HXY HY Hc1 Hgap1 (negbT Hact) HcmY Hok3 Ha3 erefl. }
exists (S m3 rg4 (nD L P C PI PB t Y (Apre Y)) lv.+1 Y). split.
- exact: (mtr_trans (msil_mtr S1) (mtr_trans S2 (mtr_trans (msil_mtr S3) (msil_mtr S4)))).
- have Hpre' : size (rcons pre e) <= size t by rewrite Et size_rcons size_cat /= addnS ltnS leq_addr.
  have HactX : active pre X by rewrite -EX; exact: topcomp_active.
  exists m3, rg4. split; [rewrite pend_rcons; exact: erefl | | exact: Hok4].
  constructor; [exact: Hc3 | exact: Hg3 |].
  move=> Z HZ.
  case: (Z =P Y) => [->|HZY]; first exact: HcmY'.
  have HYZ : (Y == Z) = false by apply/eqP => E; apply: HZY; rewrite E.
  have HoutZ : forall w, zone Z w -> m3 w = m1 w.
  { move=> w Hw. apply: Hout. apply/negP => HwY. exact: zone_disj HZ HY HZY Hw HwY. }
  case: (Z =P X) => [->|HZX].
  + have Hfr : frames (rcons pre e) X = frames pre X.
    { have HYX' : (Y == X) = false by apply/negbTE.
      by rewrite frames_call HYX' cats0. }
    have Hc := comp_mem_counter (e := e) HX HactX erefl Hfr Hpre (mi_comp HMI HX).
    apply: (comp_mem_frame HX Hpre' _ erefl erefl erefl Hc).
    move=> w Hw. apply: Hout. apply/negP => HwY. exact: zone_disj HX HY HXY Hw HwY.
  + have HXZ : (X == Z) = false by apply/eqP => E; apply: HZX; rewrite E.
    apply: (comp_mem_frame HZ Hpre _ _ _ _ (mi_comp HMI HZ)).
    * move=> w Hw. rewrite (HoutZ w Hw). apply: Hzone_m1.
      apply/negP => HwX. exact: zone_disj HZ HX HZX Hw HwX.
    * by rewrite active_rcons /= HYZ orbF.
    * by rewrite size_rp_events_rcons /= HXZ addn0.
    * by rewrite frames_call HYZ cats0.
Qed.

Lemma ret_land (m : {fmap mword mt -> matom}) (rg : rmap) cl kc P0 z0 X lv :
  cl \in comps -> kc < size (rp_events t cl) ->
  nth ev0 (rp_events t cl) kc = ECall cl P0 z0 X ->
  code_in cde pc0 m -> regs_ok rg ->
  [/\ retpos cl kc < size cde,
      (exists iw vtw etw icw,
      m (pcw (pc0 + retpos cl kc)) = Some (Atom iw (MTag vtw cl etw icw)))
  & exists rg', msil NC (S m rg (retpos cl kc) lv cl)
                        (S m rg' (nD L P C PI PB t cl (Apre cl)) lv cl) /\ regs_ok rg'].
Proof.
move=> Hcl Hk Hnth Hc Hok.
have Hsplit := cde_split Hcl.
have Hbc := blk_case Hsplit (ev0 := ev0) Hk.
have Hnx := nxt_after_case Hsplit ev0 Hk.
rewrite Hnth in Hbc Hnx.
have [_ Hbody] := blk_cat Hbc.
have [_ Hb2] := blk_cat Hbody.
have [_ Hb3] := blk_cons Hb2.
have Eret : (nCk L P C PI PB t cl (Apre cl) kc + size [:: MrLabel (rp_lab L cl (4 + kc));
              rp_const 1 R_ONE; MrBinop Add R_AUX2 R_ONE R_AUX2; MrStore R_AUX1 R_AUX2]
             + size (rp_load (rp_word z0) R_COM R_ARG)).+1 = retpos cl kc.
{ rewrite /retpos Hnth. exact: erefl. }
rewrite Eret in Hb3.
have [Hj _] := blk_cons Hb3.
have [[vv vt] [Hv /= Ht _]] := me_fetch Hbound Hc Hj.
subst vt.
split.
- exact: nth_error_size Hj.
- by exists vv, Other, None, true.
- have Hnx' : nxt cde (retpos cl kc).+1 cl.
  { have E2 : nCk L P C PI PB t cl (Apre cl) kc + size (rp_case L P C cl (kc, ECall cl P0 z0 X))
              = (retpos cl kc).+1.
    { rewrite -Eret /rp_case /rp_case_body !size_cat /=. lia. }
    rewrite -E2. exact: Hnx. }
  have S1 := step_goto_blk NC Hbound Hcs lv Hc Hb3 Hnx' (lab_at_0 Huniq Hsplit) Hok.
  eexists. split; first exact: msil_one S1. exact: regs_ok_setm.
Qed.

Hypothesis Hrets : forall C0 z0 C', List.In (ERet C0 z0 C') t -> C0 <> C'.

Lemma ret_step pre X z C'' suf s :
  t = pre ++ ERet X z C'' :: suf -> Disp pre s ->
  exists s', mtr NC s [:: ERet X z C''] s' /\ Disp (rcons pre (ERet X z C'')) s'.
Proof.
move=> Et Hd.
set e := ERet X z C''.
have Hin : List.In e t by rewrite Et; apply: List.in_or_app; right; left.
have HXC := Hrets Hin.
have [Hce Hk Hnth HX] := ev_split Et (erefl (topcomp (pend pre))).
have EX : topcomp (pend pre) = X by rewrite -Hce.
rewrite EX in Hk Hnth HX.
have Hwbp := wb_prefix Et.
have [Hcur Hcal Hch] := pend_inv Hwbp.
have Hwbe : well_bracketed_trace (run_trace stack_state0 pre) [:: e].
{ have := Hwb. rewrite Et well_bracketed_trace_cat => /andP [_ H].
  move: H => /=. case: (callers _) => [|hd tl]; first by rewrite andbF.
  move=> /andP [H1 /andP [H2 _]]. by rewrite /= H1 H2. }
move: Hwbe => /=. rewrite Hcal.
case Ep: (pend pre) => [|[[cl kc] ce] st]; first by rewrite andbF.
move=> /andP [_ /andP [/eqP Ecl _]].
rewrite /pcaller /= in Ecl. subst cl.
have Ece : ce = X by move: EX; rewrite Ep.
subst ce.
move: Hch. rewrite Ep /= => /andP [/eqP Htop Hchst].
rewrite /pcaller /= in Htop.
have [m [rg1 [HMI S1 Ha1 Hok1]]] := disp_case Et Hd.
rewrite EX Ep in S1 Ha1.
set k := size (rp_events pre X) in S1 Hk Hnth.
set m1 := setm m (ctrlw NC X) (Atom (pcw k.+1) (MTag Other X None false)) in S1.
have HcX := Hcomp HX.
have Hjb : forall j, j < size t + 2 -> j.+2 <= 2 ^ (word_size mt - NC).
{ move=> j Hj. apply: leq_trans _ HKt. clear -Hj. lia. }
have Hctl : pfilterC NC X (ctrlw NC X).
{ apply: (ctrlw_region HNCws HcX). apply: leq_trans _ HKt. by []. }
have HzX : zone X (ctrlw NC X) by rewrite /zone Hctl orbT.
have Hc1 : code_in cde pc0 m1 := code_in_setm _ (mi_code HMI) (code_not_region HX Hctl).
have Hact : active pre X by rewrite -EX; exact: topcomp_active.
have Hcm := mi_comp HMI HX. rewrite /comp_mem Hact in Hcm.
case: Hcm => Hs Hctr H1 Hfr Hcells.
set F := frames (rcons pre e) X.
have EF : frames pre X = F ++ [:: (size st, (C'', kc, X))].
{ by rewrite (@frames_ret pre X z C'' X _ _ Ep) /pcallee /= eqxx. }
set d := size F.
have Hpre : size pre <= size t by rewrite Et size_cat leq_addr.
have Hdt : d < size t.
{ have := frames_lt_t X Et. by rewrite EF size_cat /= addn1 => /ltnW. }
have Hd2 : 2 + d < size t + 2 by rewrite addnC ltn_add2r.
have H1b : 1 < size t + 2 by rewrite addn2.
have Nc : forall j, 0 < j -> j < size t + 2 -> (cellw NC X j == ctrlw NC X) = false.
{ move=> j H0 Hj. exact: (ctrl_cell_ne HNCws HcX (Hjb j Hj) H0). }
have H1' : m1 (cellw NC X 1) = Some (Atom (cellw NC X (2 + d).+1) (MTag Other X None false)).
{ rewrite /m1 setmE (@Nc 1 erefl H1b) H1 EF size_cat /= addn1 addnS. exact: erefl. }
have Hfr' : m1 (cellw NC X (2 + d))
            = Some (Atom (frw (size st, (C'', kc, X))) (MTag (Ret (size st)) X None false)).
{ rewrite /m1 setmE (@Nc (2 + d) erefl Hd2). apply: Hfr.
  rewrite EF -[d]addn0 nth_error_cat_r. exact: erefl. }
have HC'' : C'' \in comps by have := Hcev Hin; case/andP.
have Hxin : (C'', kc, X) \in pend pre by rewrite Ep mem_head.
have [P0 [z0 [Hkc Hnc]]] := pend_entry_call ev0 Hxin.
rewrite /pcaller /pidx /pcallee /= in Hkc Hnc.
have HtC : rp_events t C'' = rp_events pre C'' ++ rp_events (e :: suf) C''.
{ by rewrite Et /rp_events filter_cat. }
have Hkc' : kc < size (rp_events t C'') by rewrite HtC size_cat ltn_addr.
have Hnc' : nth ev0 (rp_events t C'') kc = ECall C'' P0 z0 X by rewrite HtC nth_cat Hkc.
have [Hrsz [iw [vtw [etw [icw Hcapm]]]] _] :=
  ret_land 0 HC'' Hkc' Hnc' (mi_code HMI) Hok1.
set cap := frw (size st, (C'', kc, X)).
have Hcaplow : forall Y, Y \in comps -> ~~ pfilterC NC Y cap.
{ move=> Y HY. apply: (low_not_region HNCws (Hcomp HY)).
  have Hl : pc0 + retpos C'' kc < 2 ^ 14.
  { apply: ltn_trans _ Hcs. by rewrite ltn_add2l. }
  apply: (leq_ltn_trans (eq_leq (won_val_small Hl))). exact: ltn_trans Hl HKal. }
have Ncap : forall w, pfilterC NC X w -> (w == cap) = false.
{ move=> w Hw. apply/eqP => E. move: (Hcaplow X HX). by rewrite -E Hw. }
have Hcap1 : m1 cap = Some (Atom iw (MTag vtw C'' etw icw)).
{ rewrite /m1 setmE. rewrite eq_sym (Ncap _ Hctl). exact: Hcapm. }
have Hrg : forall j, j < size t + 2 -> pfilterC NC X (cellw NC X j).
{ move=> j Hj. exact: (@cellw_region NC HNCws X j HcX (Hjb j Hj)). }
have Hbc := blk_case (cde_split HX) (ev0 := ev0) Hk.
rewrite Hnth in Hbc.
have Hbb : blk cde (nCk L P C PI PB t X (Apre X) k).+4 X (rp_case_body L P C X e).
{ have [_ H] := blk_cat Hbc. by rewrite -addn4. }
have Hne1 : addw (ctrlw NC X) (pcw 1) != addw (ctrlw NC X) (pcw (2 + d)).
{ have H1ne : 1 <> 2 + d by move=> E'; clear -E'; lia.
  exact: (negbT (cellw_ne HNCws HcX (Hjb 1 H1b) (Hjb _ Hd2) H1ne)). }
have [rg2 [S2 Hok2]] :=
  run_ret NC Hbound Hcs Hc1 Hbb Hok1 Ha1 H1' Hfr' Hne1
    (code_not_region HX (Hrg 1 H1b)) (code_not_region HX (Hrg _ Hd2)) Hcap1
    (negbT (Ncap _ (Hrg 1 H1b))) (negbT (Ncap _ (Hrg _ Hd2)))
    (introN eqP (fun E => HXC (esym E))) (Hz Hin).
set m2 := setm (setm m1 (addw (ctrlw NC X) (pcw 1))
                   (Atom (addw (ctrlw NC X) (pcw (2 + d))) (MTag Other X None false)))
               (addw (ctrlw NC X) (pcw (2 + d))) (Atom cap (MTag Invalidated X None false)).
have Hc2 : code_in cde pc0 m2.
{ apply: code_in_setm (code_not_region HX (Hrg _ Hd2)).
  exact: code_in_setm (code_not_region HX (Hrg 1 H1b)). }
have [_ _ [rg3 [S3 Hok3]]] := ret_land (size st) HC'' Hkc' Hnc' Hc2 Hok2.
have Hz1 : zone X (cellw NC X 1) by rewrite /zone (Hrg 1 H1b) orbT.
have Hzd : zone X (cellw NC X (2 + d)) by rewrite /zone (Hrg _ Hd2) orbT.
have Hout : forall w, ~~ zone X w -> m2 w = m w.
{ move=> w Hw. rewrite /m2 (setm_out _ _ Hzd Hw) (setm_out _ _ Hz1 Hw).
  exact: setm_out _ _ HzX Hw. }
exists (S m2 rg3 (nD L P C PI PB t C'' (Apre C'')) (size st) C''). split.
- exact: (mtr_trans (msil_mtr S1) (mtr_trans S2 (msil_mtr S3))).
- have Hpre' : size (rcons pre e) <= size t.
  { by rewrite Et size_rcons size_cat /= addnS ltnS leq_addr. }
  exists m2, rg3. split; [rewrite pend_rcons Ep /= -Htop; exact: erefl | | exact: Hok3].
  constructor.
  + exact: Hc2.
  + rewrite (Hout _ (alloc_not_zone HX)). exact: mi_gap HMI.
  + move=> Z HZ. case: (Z =P X) => [->|HZX].
    * have Ecnt : size (rp_events (rcons pre e) X) = k.+1.
      { by rewrite size_rp_events_rcons /= eqxx addn1. }
      have Hact' : active (rcons pre e) X by rewrite active_rcons Hact.
      rewrite /comp_mem Hact' Ecnt -/F.
      have Nd1 : (cellw NC X (2 + d) == cellw NC X 1) = false.
      { apply: (cellw_ne HNCws HcX (Hjb _ Hd2) (Hjb 1 H1b)). move=> E'; clear -E'; lia. }
      have Nst : forall j, j < size t + 2 -> (pcw (rp_addr PB X) == cellw NC X j) = false.
      { move=> j Hj. apply/eqP => E. move: (static_not_region HX HX). by rewrite E (Hrg j Hj). }
      have Nsc : (pcw (rp_addr PB X) == ctrlw NC X) = false.
      { apply/eqP => E. move: (static_not_region HX HX). by rewrite E Hctl. }
      split.
      -- rewrite /m2 setmE (Nst _ Hd2) setmE (Nst 1 H1b) /m1 setmE Nsc. exact: Hs.
      -- rewrite /m2 setmE.
         rewrite (_ : (ctrlw NC X == addw (ctrlw NC X) (pcw (2 + d))) = false);
           last by rewrite eq_sym; exact: (@Nc (2 + d) erefl Hd2).
         rewrite setmE.
         rewrite (_ : (ctrlw NC X == addw (ctrlw NC X) (pcw 1)) = false);
           last by rewrite eq_sym; exact: (@Nc 1 erefl H1b).
         rewrite /m1 setmE (eqxx (ctrlw NC X)). exact: erefl.
      -- rewrite /m2 setmE.
         rewrite (_ : (cellw NC X 1 == addw (ctrlw NC X) (pcw (2 + d))) = false);
           last by rewrite eq_sym; exact: Nd1.
         rewrite setmE (eqxx (cellw NC X 1)). exact: erefl.
      -- move=> j fx Hj.
         have Hjd : j < d := nth_error_size Hj.
         have Hj2 : 2 + j < size t + 2 by rewrite addnC ltn_add2r; exact: ltn_trans Hjd Hdt.
         have Nj1 : (cellw NC X (2 + j) == cellw NC X 1) = false.
         { apply: (cellw_ne HNCws HcX (Hjb _ Hj2) (Hjb 1 H1b)). move=> E'; clear -E'; lia. }
         have Njd : (cellw NC X (2 + j) == cellw NC X (2 + d)) = false.
         { apply: (cellw_ne HNCws HcX (Hjb _ Hj2) (Hjb _ Hd2)). move=> E'; clear -E' Hjd; lia. }
         rewrite /m2 setmE Njd setmE Nj1 /m1 setmE (@Nc (2 + j) erefl Hj2).
         apply: Hfr. rewrite EF nth_error_cat_l //.
      -- move=> j Hj.
         have Hj2 : 2 + j < size t + 2 by rewrite addnC ltn_add2r.
         have Nj1 : (cellw NC X (2 + j) == cellw NC X 1) = false.
         { apply: (cellw_ne HNCws HcX (Hjb _ Hj2) (Hjb 1 H1b)). move=> E'; clear -E'; lia. }
         rewrite /m2 setmE.
         case: eqP => [_|_]; first by exists cap, Invalidated.
         rewrite setmE Nj1 /m1 setmE (@Nc (2 + j) erefl Hj2). exact: Hcells j Hj.
    * apply: (comp_mem_frame HZ Hpre _ _ _ _ (mi_comp HMI HZ)).
      -- move=> w Hw. apply: Hout. apply/negP => HwX. exact: zone_disj HZ HX HZX Hw HwX.
      -- by rewrite active_rcons orbF.
      -- have HXZ : (X == Z) = false by apply/eqP => E; apply: HZX; rewrite E.
         by rewrite size_rp_events_rcons /= HXZ addn0.
      -- have HXZ : (X == Z) = false by apply/eqP => E; apply: HZX; rewrite E.
         by rewrite (@frames_ret pre X z C'' Z _ _ Ep) /pcallee /= HXZ cats0.
Qed.

Lemma disp_halt s : Disp t s -> exists s', msil NC s s' /\ final_halt_code s'.
Proof.
move=> [m [rg [-> HMI Hok]]].
set X := topcomp (pend t).
have HX : X \in comps := topcomp_in (suf := [::]) (esym (cats0 t)).
have Hact : active t X := topcomp_active t.
have Hcm := mi_comp HMI HX. rewrite /comp_mem Hact in Hcm.
case: Hcm => Hs Hctr H1 Hfr Hcells.
have Hsplit := cde_split HX.
have Hbd := blk_disp Hsplit.
have HA : rp_addr PB X < 2 ^ 14 := rp_addr_lt HX.
have Hne : size (rp_events t X) < 2 ^ 14.
{ rewrite /rp_events size_filter. apply: (leq_ltn_trans (count_size _ _)).
  apply: leq_ltn_trans _ Ht14. by rewrite -addn4 leq_addr. }
have [rg' [k [Hs' Hf]]] :=
  run_disp_halt NC Hbound Hcs (size (pend t)) (mi_code HMI) Hbd Hok HA Hs Hctr Hne.
by exists (S m rg' k (size (pend t)) X).
Qed.

Lemma replay_from suf pre s :
  t = pre ++ suf -> Disp pre s -> exists s', mtr NC s suf s' /\ final_halt_code s'.
Proof.
elim: suf pre s => [|e suf IH] pre s Et Hd.
- rewrite cats0 in Et. subst pre.
  have [s' [Hs Hf]] := disp_halt Hd. exists s'. split=> //. exact: msil_mtr.
- have Et' : t = rcons pre e ++ suf by rewrite Et cat_rcons.
  case: e Et Et' => [X P' z Y|X z Y] Et Et'.
  + have [s1 [Hs1 Hd1]] := call_step Et Hd.
    have [s' [Hs' Hf]] := IH _ _ Et' Hd1.
    exists s'. split=> //. exact: (mtr_trans Hs1 Hs').
  + have [s1 [Hs1 Hd1]] := ret_step Et Hd.
    have [s' [Hs' Hf]] := IH _ _ Et' Hd1.
    exists s'. split=> //. exact: (mtr_trans Hs1 Hs').
Qed.

Lemma start_disp (m : {fmap mword mt -> matom}) (rg : rmap) :
  code_in cde pc0 m -> m (pcw alloc_label) = None ->
  (forall X, X \in comps ->
     m (pcw (rp_addr PB X)) = Some (Atom 0%w (MTag Other X None false))
     /\ (forall w, pfilterC NC X w -> m w = None)) ->
  regs_ok rg ->
  exists s', msil NC (S m rg (size (Apre Component.main)) 0 Component.main) s' /\ Disp [::] s'.
Proof.
move=> Hc Hgap Hst Hok.
set M := Component.main.
have Hsplit := cde_split Hmain.
have Hb := blk_start Hsplit (erefl M).
move: Hb => /blk_cat [Hbi Hbg].
have Hxi : nxt cde (size (Apre M) + size (rp_init L t M (rp_addr PB M) 1)) M.
{ exact: blk_nxt Hbg erefl. }
have [Hs Hreg] := Hst M Hmain.
have HcM := Hcomp Hmain.
have Hjb : forall j, j < size t + 2 -> j.+2 <= 2 ^ (word_size mt - NC).
{ move=> j Hj. apply: leq_trans _ HKt. clear -Hj. lia. }
have HB : (rp_blocks t).+2 <= 2 ^ (word_size mt - NC) by rewrite /rp_blocks addn2.
have HB14 : rp_blocks t < 2 ^ 14.
{ rewrite /rp_blocks. apply: leq_ltn_trans _ Ht14. by rewrite addn2 ltnW. }
have Hregnc : forall w, pfilterC NC M w -> encode_code cde pc0 w = None.
{ move=> w Hw. exact: code_not_region Hmain Hw. }
have [rg1 [S1 Hr1 Hr2 Hok1]] :=
  run_init_alloc Hbound Hcs 0 Hc Hbi Hxi Hok (rp_addr_lt Hmain) Hs
    (static_not_code Hmain) Hgap no_alloc_label HNCws HcM HB HB14 Hreg Hregnc
    (static_not_region Hmain Hmain).
set B := rp_blocks t.
set blk0 := mkfmap (blkseq NC M B).
set m2 := setm (setm (unionm m blk0) (pcw (rp_addr PB M))
                     (Atom (ctrlw NC M) (MTag Other M None false)))
               (addw (ctrlw NC M) (pcw 1))
               (Atom (addw (ctrlw NC M) (pcw 2)) (MTag Other M None false)).
have H1b : 1 < size t + 2 by rewrite addn2.
have Hrg : forall j, j < size t + 2 -> pfilterC NC M (cellw NC M j).
{ move=> j Hj. exact: (@cellw_region NC HNCws M j HcM (Hjb j Hj)). }
have Hctl : pfilterC NC M (ctrlw NC M).
{ apply: (ctrlw_region HNCws HcM). apply: leq_trans _ HKt. by []. }
have Nst : forall w, pfilterC NC M w -> (w == pcw (rp_addr PB M)) = false.
{ move=> w Hw. apply/eqP => E. move: (static_not_region Hmain Hmain). by rewrite -E Hw. }
have Hblk : forall j, j < B -> blk0 (cellw NC M j)
                                = Some (Atom (word.as_word (ssrint.Posz 0) : mword mt) (def_mem_tag M false)).
{ move=> j Hj. have H := blkseq_get NC M Hj. rewrite -(cellwE NC M j) in H. exact: H. }
have Hc2 : code_in cde pc0 m2.
{ apply: code_in_setm (code_not_region Hmain (Hrg 1 H1b)).
  apply: code_in_setm (static_not_code Hmain). exact: code_in_unionm. }
have Hz1 : zone M (cellw NC M 1) := cellw_zone Hmain H1b.
have HzA : zone M (pcw (rp_addr PB M)) by rewrite /zone eqxx.
have Hout : forall w, ~~ zone M w -> m2 w = m w.
{ move=> w Hw. rewrite /m2 (setm_out _ _ Hz1 Hw) (setm_out _ _ HzA Hw) unionmE.
  case E1: (m w) => [v|] //=.
  case E2: (blk0 w) => [v|//].
  have HBK : B.+1 < 2 ^ (word_size mt - NC).
  { apply: leq_ltn_trans _ HKt. by rewrite /B /rp_blocks addn2. }
  have Hr := blk_key_region Hmain HBK E2.
  exfalso. move: Hw. by rewrite /zone Hr orbT. }
have Hxg : nxt cde (size (Apre M) + size (rp_init L t M (rp_addr PB M) 1)).+1 M.
{ apply: (nxt_block Huniq Hsplit).
  - rewrite -addnS. exact: leq_addr.
  - have EM : (M == Component.main) = true := eqxx M.
    have HTl : 0 < size (Tl L P C PB t M) by [].
    rewrite size_cc /Sc EM size_tagged size_cat (_ : size (rp_goto L M 0) = 1) //.
    move: (size (Tl L P C PB t M)) HTl => a Ha. rewrite /M. clear -Ha. lia. }
have S2 := step_goto_blk NC Hbound Hcs 0 Hc2 Hbg Hxg (lab_at_0 Huniq Hsplit) Hok1.
exists (S m2 (setm rg1 (wk 4) (Atom (pcw (pc0 + (size (Apre M)
                    + size (rp_init L t M (rp_addr PB M) 1)).+1)) InternalJump))
          (nD L P C PI PB t M (Apre M)) 0 M).
split; first exact: (msil_trans S1 (msil_one S2)).
exists m2, (setm rg1 (wk 4) (Atom (pcw (pc0 + (size (Apre M)
                    + size (rp_init L t M (rp_addr PB M) 1)).+1)) InternalJump)).
split.
- exact: erefl.
- split.
  + exact: Hc2.
  + rewrite (Hout _ (alloc_not_zone Hmain)). exact: Hgap.
  + move=> X HX. case: (eqVneq X M) => [EX|HXM].
    * subst X. rewrite /comp_mem (_ : active [::] M = true); last by rewrite /active eqxx.
      have Nst2 : forall j, j < size t + 2 -> (pcw (rp_addr PB M) == cellw NC M j) = false.
      { move=> j Hj. rewrite eq_sym. exact: Nst _ (Hrg j Hj). }
      have Nct : forall j, 0 < j -> j < size t + 2 -> (ctrlw NC M == cellw NC M j) = false.
      { move=> j H0 Hj. rewrite eq_sym. exact: (ctrl_cell_ne HNCws HcM (Hjb j Hj) H0). }
      split.
      -- rewrite /m2 setmE.
         rewrite (_ : (pcw (rp_addr PB M) == addw (ctrlw NC M) (pcw 1)) = false); last exact: Nst2 1 H1b.
         rewrite setmE (eqxx (pcw (rp_addr PB M) : mword mt)). exact: erefl.
      -- rewrite /m2 setmE.
         rewrite (_ : (ctrlw NC M == addw (ctrlw NC M) (pcw 1)) = false); last exact: (@Nct 1 erefl H1b).
         rewrite setmE (Nst _ Hctl) unionmE (Hreg _ Hctl) /=.
         have HB0 : 0 < B by rewrite /B /rp_blocks addn2.
         exact: (blkseq_get NC M (j := 0) HB0).
      -- rewrite /m2 setmE (eqxx (addw (ctrlw NC M) (pcw 1))). exact: erefl.
      -- move=> j fx. by case: j.
      -- move=> j Hj.
         have Hj2 : 2 + j < size t + 2 by rewrite addnC ltn_add2r.
         have N1 : (cellw NC M (2 + j) == addw (ctrlw NC M) (pcw 1)) = false.
         { apply: (cellw_ne HNCws HcM (Hjb _ Hj2) (Hjb 1 H1b)). move=> E. clear -E. lia. }
         rewrite /m2 setmE N1 setmE (Nst _ (Hrg _ Hj2)) unionmE (Hreg _ (Hrg _ Hj2)) /=.
         have HjB : 2 + j < B by rewrite /B /rp_blocks addnC ltn_add2r.
         rewrite (Hblk _ HjB). exists (word.as_word (ssrint.Posz 0) : mword mt), Other.
         exact: erefl.
    * have Ha : active [::] X = false.
      { rewrite /active /calls_into /= orbF. exact: negbTE HXM. }
      rewrite /comp_mem Ha.
      have [HsX HrX] := Hst X HX.
      have Hnz : forall w, zone X w -> ~~ zone M w.
      { have HXM' : X <> M by apply/eqP.
        move=> w Hw. apply/negP => Hw'. exact: zone_disj HX Hmain HXM' Hw Hw'. }
      split.
      -- rewrite Hout; first exact: HsX. apply: Hnz. by rewrite /zone eqxx.
      -- move=> w Hw. rewrite Hout; first exact: HrX w Hw. apply: Hnz. by rewrite /zone Hw orbT.
- exact: regs_ok_setm.
Qed.

Lemma main_pos :
  find (fun '(_, tag) => color tag == Component.main) cde = size (Apre Component.main).
Proof.
rewrite (cde_split Hmain) find_cat.
have Hna : ~~ has (fun '(_, tag) => color tag == Component.main) (Apre Component.main).
{ apply: hasNIn => -[i tg] Hin. rewrite /Apre in Hin.
  have [c [Hc Hx]] := In_flatten_map Hin.
  have Hcol : color tg = c := cc_color Hx.
  rewrite /= Hcol. apply/eqP => Ec. rewrite Ec in Hc.
  exact: (negP (notin_take_index Component.main comps) (List_In_mem Hc)). }
rewrite (negbTE Hna).
have Hpos : 0 < size (rp_comp_code L P C PI PB t Component.main).
{ rewrite size_cc. have HTl : 0 < size (Tl L P C PB t Component.main) by [].
  move: (size (Tl L P C PB t Component.main)) HTl => a Ha. clear -Ha. lia. }
case Ecc: (rp_comp_code L P C PI PB t Component.main) Hpos => [|x l] Hpos; first by [].
have Hx : color x.2 = Component.main.
{ apply: (@cc_color L P C PI PB t Component.main). rewrite Ecc. by left. }
clear Hpos. case: x Hx Ecc => i tg /= Hx _. rewrite Hx eqxx. exact: addn0.
Qed.

Local Notation M0 := (unionm (encode_code cde pc0) (initial_memory (mt := mt) WB)).

Lemma Htot : size (linearize_bufs WB) < 2 ^ 14.
Proof. rewrite (total_shape HbufsW). exact: Hdata. Qed.

Lemma HbW : size (linearize_bufs WB) < 2 ^ word_size mt.
Proof. apply: (ltn_trans Htot). by rewrite word_size_mt ltn_exp2l. Qed.

Lemma init_code : code_in cde pc0 M0.
Proof. move=> w v E. by rewrite unionmE E. Qed.

Lemma init_gap : M0 (pcw alloc_label) = None.
Proof.
have Enc : encode_code cde pc0 (pcw alloc_label) = None.
{ case E: (encode_code cde pc0 _) => [v|//]. exfalso.
  have [n [Ew [Hn _]]] := encode_code_nth_inv E.
  have Hlt : n + pc0 < 2 ^ 14.
  { apply: leq_ltn_trans _ Hcs. rewrite addnC leq_add2l. exact: ltnW. }
  have Hal14 : alloc_label < 2 ^ 15 by rewrite /alloc_label ltn_exp2l.
  have Hv : (\val (pcw alloc_label : mword mt) : nat) = alloc_label.
  { rewrite /word_of_nat valw_as_word. apply: modn_small.
    apply: (ltn_trans Hal14). by rewrite word_size_mt ltn_exp2l. }
  have Ev := etrans (esym Hv) (etrans (congr1 (fun w : mword mt => (\val w : nat)) Ew)
                                      (won_val_small Hlt)).
  move: Hlt. by rewrite -Ev /alloc_label ltnn. }
rewrite unionmE Enc.
exact: (alloc_label_not_in_initial_memory_bl HbW Htot).
Qed.

Lemma init_static X : X \in comps ->
  M0 (pcw (rp_addr PB X)) = Some (Atom 0%w (MTag Other X None false))
  /\ (forall w, pfilterC NC X w -> M0 w = None).
Proof.
move=> HX. split.
- rewrite unionmE (static_not_code HX).
  have EW : WB X = omap (mapm (fun x => inl (bsize x))) (PB X).
  { rewrite !unionmE /= !mapmE. by case: (Bp X). }
  have Hk : linearize_bufs WB (X, rp_block PB X, 0) = Some (Undef, def_mem_tag X false).
  { have H := Hstat HX. move: H. rewrite !linearize_bufsE /linearize_buf EW.
    case: (PB X) => [map|] //=. rewrite mapmE.
    case: (map (rp_block PB X)) => [blk|] //=.
    case: blk => [n|l] /=.
    - case: n => [|n] /= H; first by case: H. by [].
    - case: l => [|v l] /= H; first by case: H. by []. }
  have Ea : nat_addr WB (X, rp_block PB X, 0) = rp_addr PB X.
  { by rewrite /nat_addr add0n (bl_base_shape HbufsW). }
  rewrite -Ea (initial_memory_atE HbW Hk). exact: erefl.
- move=> w Hw. rewrite unionmE (code_not_region HX Hw).
  case E: (initial_memory WB w) => [d|]; last exact: erefl.
  exfalso. have [k [cell [Hk' _ Ew]]] := initial_memory_invE E.
  have Hkin : k \in domm (linearize_bufs WB) by apply/dommP; exists cell.
  have Hlt : nat_addr WB k < 2 ^ 14 := ltn_trans (nat_addr_lt Hkin) Htot.
  have := low_not_region HNCws (Hcomp HX)
            (leq_ltn_trans (eq_leq (won_val_small Hlt)) (ltn_trans Hlt HKal)).
  by rewrite -Ew Hw.
Qed.

Theorem replay_initial (pi : Program.interface) :
  exists s', mtr NC (initial_state cde WB pi) t s' /\ final_halt_code s'.
Proof.
have [s1 [S1 D1]] := start_disp init_code init_gap init_static regs_ok_reg0.
have [s' [S' F']] := replay_from (pre := [::]) (erefl t) D1.
exists s'. split; last exact: F'.
change (initial_state cde WB pi)
  with (S M0 (reg0 (mt := mt)) (find (fun '(_, tag) => color tag == Component.main) cde)
          0 Component.main).
rewrite main_pos.
exact: (mtr_trans (msil_mtr S1) S').
Qed.

Theorem replay_behaves :
  program_behaves (me_sem NC (Definitions.program_link bp bc)) (Terminates t).
Proof.
have [s' [H F]] := replay_initial (unionm Ip Ic).
have Hst : star (prog_step_me NC) tt (initial_state cde WB (unionm Ip Ic)) t s' := mtr_star H.
econstructor; first exact: erefl.
econstructor; [exact: Hst | exact: F].
Qed.

Theorem replay_prefix (m0 : finpref_behavior) :
  finpref_trace m0 = t -> not_wrong_finpref m0 ->
  does_prefix (me_sem NC (Definitions.program_link bp bc)) m0.
Proof.
move=> Et Hnw. exists (Terminates t). split; first exact: replay_behaves.
case: m0 Et Hnw => t0 /= Et0 Hnw; subst t0.
- exact: erefl.
- by [].
- exists (Terminates E0). by rewrite /= E0_right.
Qed.

End Sim.
