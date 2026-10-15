Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import CompCert.Events.
From Stdlib Require Import ZArith.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From mathcomp Require Import zify.
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
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Utils.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.OffsetWord.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import T2M.MMemBase.
Require Import T2M.MPos.
Require Import Backtranslation_ME_MP.
Require Import Backtranslation_ME_MP_Step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Notation minstr := (@Merged.instr mt).

Lemma word_of_natM (k a b : nat) :
  mulw (@word_of_nat k a) (@word_of_nat k b) = @word_of_nat k (a * b).
Proof.
apply: word_nat_inj. by rewrite /mulw /word_of_nat !valw_as_word modnMm.
Qed.

Lemma to_nat_lt20 (r : register) : Intermediate.Register.to_nat r < 20.
Proof. by case: r. Qed.

Lemma rk_neq (r1 r2 : register) : r1 <> r2 -> (rk r1 == rk r2) = false.
Proof.
move=> H. rewrite (wk_eq (to_nat_lt20 r1) (to_nat_lt20 r2)).
apply/eqP => E. apply: H. by case: r1 r2 E => [] [].
Qed.

Lemma regs_ok_rk (rg : rmap) (r : register) :
  regs_ok rg -> exists a, rg (rk r) = Some a.
Proof.
move=> H. apply: H. by case: r.
Qed.

Inductive msil (NC : nat) : mstate -> mstate -> Prop :=
| msil_refl s : msil NC s s
| msil_step s1 s2 s3 : step_me (NC := NC) s1 s2 None -> msil NC s2 s3 -> msil NC s1 s3.

Lemma msil_trans NC s1 s2 s3 : msil NC s1 s2 -> msil NC s2 s3 -> msil NC s1 s3.
Proof.
elim=> [//|a b c Hab _ IH] H. exact: msil_step Hab (IH H).
Qed.

Lemma msil_one NC s1 s2 : step_me (NC := NC) s1 s2 None -> msil NC s1 s2.
Proof. move=> H. exact: msil_step H (msil_refl _ _). Qed.

Inductive mtr (NC : nat) : mstate -> trace -> mstate -> Prop :=
| mtr_refl s : mtr NC s [::] s
| mtr_sil s1 s2 t s3 : step_me (NC := NC) s1 s2 None -> mtr NC s2 t s3 -> mtr NC s1 t s3
| mtr_ev s1 s2 e t s3 :
    step_me (NC := NC) s1 s2 (Some e) -> mtr NC s2 t s3 -> mtr NC s1 (e :: t) s3.

Lemma mtr_trans NC s1 t1 s2 t2 s3 :
  mtr NC s1 t1 s2 -> mtr NC s2 t2 s3 -> mtr NC s1 (t1 ++ t2) s3.
Proof.
elim=> [//|a b t c Hab _ IH|a b e t c Hab _ IH] H.
- exact: mtr_sil Hab (IH H).
- exact: mtr_ev Hab (IH H).
Qed.

Lemma msil_mtr NC s1 s2 : msil NC s1 s2 -> mtr NC s1 [::] s2.
Proof. elim=> [s|a b c Hab _ IH]; [exact: mtr_refl | exact: mtr_sil Hab IH]. Qed.

Notation St m rg n lv cid :=
  (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (_ + n)) (Level lv cid)) tt) (only parsing).

Section Seg.

Variable NC : nat.
Variable cde : @Merged.code mt.
Variable pc0 : nat.
Hypothesis Hbound : pc0 + size cde < 2 ^ word_size mt.
Hypothesis Hsmall : pc0 + size cde < alloc_label.

Local Notation S m rg n lv cid :=
  (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (pc0 + n)) (Level lv cid)) tt).

Definition blk (n cid : nat) (l : seq minstr) : Prop :=
  forall i, i < size l ->
    List.nth_error cde (n + i) = Some (nth (@MrNop mt) l i, def_mem_tag cid true).

Definition nxt (n cid : nat) : Prop :=
  exists i tg, List.nth_error cde n = Some (i, tg) /\ color tg = cid.

Lemma blk_cons n cid i l :
  blk n cid (i :: l) ->
  List.nth_error cde n = Some (i, def_mem_tag cid true) /\ blk n.+1 cid l.
Proof.
move=> H. split.
- have := H 0 erefl. by rewrite addn0.
- move=> j Hj. have := H j.+1 Hj. by rewrite addnS.
Qed.

Lemma blk_cat n cid l1 l2 :
  blk n cid (l1 ++ l2) -> blk n cid l1 /\ blk (n + size l1) cid l2.
Proof.
move=> H. split.
- move=> j Hj. have := H j. rewrite size_cat nth_cat Hj.
  move=> -> //. exact: ltn_addr.
- move=> j Hj.
  have Hj' : size l1 + j < size (l1 ++ l2) by rewrite size_cat ltn_add2l.
  have := H _ Hj'. rewrite nth_cat addnA.
  have -> : (size l1 + j < size l1) = false by rewrite ltnNge leq_addr.
  by rewrite addKn.
Qed.

Lemma blk_nxt n cid l : blk n cid l -> 0 < size l -> nxt n cid.
Proof.
case: l => [//|i l] H _. have [H0 _] := blk_cons H.
by exists i, (def_mem_tag cid true).
Qed.

Lemma step_const_blk m (rg : rmap) n lv cid imm r l :
  code_in cde pc0 m ->
  blk n cid (MrConst imm r :: l) -> nxt n.+1 cid ->
  regs_ok rg ->
  step_me (NC := NC) (S m rg n lv cid)
    (S m (setm rg (rk r) (Atom (swcast imm) Other)) n.+1 lv cid) None.
Proof.
move=> Hc Hb [i1 [tg1 [Hn1 Hc1]]] Hok.
have [Hn _] := blk_cons Hb.
have [rc Hrc] := regs_ok_rk R_COM Hok.
have [old Hold] := regs_ok_rk r Hok.
exact: (me_step_const NC Hbound lv Hc Hn erefl erefl Hn1 Hc1 Hrc Hold).
Qed.

Lemma step_binop_blk m (rg : rmap) n lv cid b r1 r2 r3 w1 w2 l :
  code_in cde pc0 m ->
  blk n cid (MrBinop b r1 r2 r3 :: l) -> nxt n.+1 cid ->
  regs_ok rg ->
  rg (rk r1) = Some (Atom w1 Other) ->
  rg (rk r2) = Some (Atom w2 Other) ->
  step_me (NC := NC) (S m rg n lv cid)
    (S m (setm rg (rk r3) (Atom (binop_denote (binop_trans b) w1 w2) Other)) n.+1 lv cid)
    None.
Proof.
move=> Hc Hb [i1 [tg1 [Hn1 Hc1]]] Hok H1 H2.
have [Hn _] := blk_cons Hb.
have [rc Hrc] := regs_ok_rk R_COM Hok.
have [old Hold] := regs_ok_rk r3 Hok.
exact: (me_step_binop NC Hbound lv Hc Hn erefl erefl Hn1 Hc1 Hrc H1 H2 Hold).
Qed.

Lemma imm_small_lt (x : nat) : x < 2 ^ 14 -> x < 2 ^ imm_size mt.
Proof. move=> H. rewrite imm_size_mt. apply: (ltn_trans H). by rewrite ltn_exp2l. Qed.

Lemma run_digits m (rg : rmap) lv cid n r tmp ds acc :
  code_in cde pc0 m ->
  blk n cid (flatten [seq [:: rp_const (2 ^ 7) tmp; MrBinop Mul r tmp r;
                            rp_const d tmp; MrBinop Add r tmp r] | d <- ds]) ->
  nxt (n + 4 * size ds) cid ->
  regs_ok rg -> r <> tmp -> all (fun d => d < 2 ^ 7) ds ->
  rg (rk r) = Some (Atom (pcw acc) Other) ->
  exists rg',
    [/\ msil NC (S m rg n lv cid) (S m rg' (n + 4 * size ds) lv cid),
        rg' (rk r) = Some (Atom (pcw (foldl (fun a d => a * 2 ^ 7 + d) acc ds)) Other),
        (forall k, (k == rk r) = false -> (k == rk tmp) = false -> rg' k = rg k)
      & regs_ok rg'].
Proof.
elim: ds n acc rg => [|d ds IH] n acc rg Hc Hb Hx Hok Hrt Hd Hr.
- exists rg. rewrite muln0 addn0. split; [exact: msil_refl | exact: Hr | by [] | exact: Hok].
- move: Hd => /= /andP [Hd Hds].
  have Hneq : (rk r == rk tmp) = false := rk_neq Hrt.
  have Hneq' : (rk tmp == rk r) = false by rewrite eq_sym.
  have Hb0 := Hb.
  have [_ Hb1] := blk_cons Hb0.
  have [_ Hb2] := blk_cons Hb1.
  have [_ Hb3] := blk_cons Hb2.
  have [_ Hb4] := blk_cons Hb3.
  have Hx4 : nxt n.+4 cid.
  { case Eds: ds Hb4 => [|d' ds'] Hb4'.
    - move: Hx. by rewrite Eds /= muln1 addn4.
    - exact: blk_nxt Hb4' erefl. }
  have H128 : 2 ^ 7 < 2 ^ imm_size mt by apply: imm_small_lt; rewrite ltn_exp2l.
  have Hdi : d < 2 ^ imm_size mt by apply: imm_small_lt; apply: (ltn_trans Hd); rewrite ltn_exp2l.
  set rg1 := setm rg (rk tmp) (Atom (pcw (2 ^ 7)) Other).
  have S1 : step_me (NC := NC) (S m rg n lv cid) (S m rg1 n.+1 lv cid) None.
  { rewrite /rg1 -(swcast_small H128). exact: step_const_blk Hc Hb0 (blk_nxt Hb1 erefl) Hok. }
  have Hok1 : regs_ok rg1 := regs_ok_setm _ _ Hok.
  have Hr1 : rg1 (rk r) = Some (Atom (pcw acc) Other) by rewrite /rg1 setmE Hneq.
  have Ht1 : rg1 (rk tmp) = Some (Atom (pcw (2 ^ 7)) Other).
  { rewrite /rg1 setmE. rewrite (eqxx (rk tmp)). exact: erefl. }
  set rg2 := setm rg1 (rk r) (Atom (pcw (acc * 2 ^ 7)) Other).
  have S2 : step_me (NC := NC) (S m rg1 n.+1 lv cid) (S m rg2 n.+2 lv cid) None.
  { have E : pcw (acc * 2 ^ 7)
             = binop_denote (binop_trans Mul) (pcw acc) (pcw (2 ^ 7)) :=
      esym (word_of_natM _ _ _).
    rewrite /rg2 E.
    exact: (step_binop_blk lv Hc Hb1 (blk_nxt Hb2 erefl) Hok1 Hr1 Ht1). }
  have Hok2 : regs_ok rg2 := regs_ok_setm _ _ Hok1.
  set rg3 := setm rg2 (rk tmp) (Atom (pcw d) Other).
  have S3 : step_me (NC := NC) (S m rg2 n.+2 lv cid) (S m rg3 n.+3 lv cid) None.
  { rewrite /rg3 -(swcast_small Hdi). exact: step_const_blk Hc Hb2 (blk_nxt Hb3 erefl) Hok2. }
  have Hok3 : regs_ok rg3 := regs_ok_setm _ _ Hok2.
  have Hr3 : rg3 (rk r) = Some (Atom (pcw (acc * 2 ^ 7)) Other).
  { rewrite /rg3 setmE Hneq /rg2 setmE (eqxx (rk r)). exact: erefl. }
  have Ht3 : rg3 (rk tmp) = Some (Atom (pcw d) Other).
  { rewrite /rg3 setmE (eqxx (rk tmp)). exact: erefl. }
  set rg4 := setm rg3 (rk r) (Atom (pcw (acc * 2 ^ 7 + d)) Other).
  have S4 : step_me (NC := NC) (S m rg3 n.+3 lv cid) (S m rg4 n.+4 lv cid) None.
  { have E : pcw (acc * 2 ^ 7 + d)
             = binop_denote (binop_trans Add) (pcw (acc * 2 ^ 7)) (pcw d) :=
      esym (pcw_add _ _).
    rewrite /rg4 E.
    exact: (step_binop_blk lv Hc Hb3 Hx4 Hok3 Hr3 Ht3). }
  have Hok4 : regs_ok rg4 := regs_ok_setm _ _ Hok3.
  have Hr4 : rg4 (rk r) = Some (Atom (pcw (acc * 2 ^ 7 + d)) Other).
  { rewrite /rg4 setmE (eqxx (rk r)). exact: erefl. }
  have Hx' : nxt (n.+4 + 4 * size ds) cid.
  { move: Hx. by rewrite /= mulnS addnA addn4. }
  have [rg' [Hs' Hr' Hk' Hok']] := IH n.+4 (acc * 2 ^ 7 + d) rg4 Hc Hb4 Hx' Hok4 Hrt Hds Hr4.
  exists rg'. split.
  + apply: (msil_step S1). apply: (msil_step S2). apply: (msil_step S3).
    apply: (msil_step S4).
    have E : n + 4 * size (d :: ds) = n.+4 + 4 * size ds.
    { rewrite [size (d :: ds)]/=. lia. }
    rewrite E. exact: Hs'.
  + exact: Hr'.
  + move=> k Hk1 Hk2. rewrite Hk' //.
    by rewrite /rg4 /rg3 /rg2 /rg1 !setmE Hk1 Hk2.
  + exact: Hok'.
Qed.

Lemma step_div (N X : nat) :
  N %/ (X * 2 ^ 7) * 2 ^ 7 + (N %/ X) %% 2 ^ 7 = N %/ X.
Proof. rewrite divnMA. exact: esym (divn_eq _ _). Qed.

Lemma digits_rec (N : nat) :
  foldl (fun a d => a * 2 ^ 7 + d) (N %/ 2 ^ 28)
        [:: (N %/ 2 ^ 21) %% 2 ^ 7; (N %/ 2 ^ 14) %% 2 ^ 7;
            (N %/ 2 ^ 7) %% 2 ^ 7; N %% 2 ^ 7] = N.
Proof.
rewrite /=.
have E28 : 2 ^ 28 = 2 ^ 21 * 2 ^ 7 by rewrite -expnD.
have E21 : 2 ^ 21 = 2 ^ 14 * 2 ^ 7 by rewrite -expnD.
have E14 : 2 ^ 14 = 2 ^ 7 * 2 ^ 7 by rewrite -expnD.
rewrite {1}E28 step_div {1}E21 step_div {1}E14 step_div.
exact: esym (divn_eq _ _).
Qed.

Lemma run_load m (rg : rmap) lv cid n N r tmp :
  code_in cde pc0 m ->
  blk n cid (rp_load N r tmp) -> nxt (n + size (rp_load N r tmp)) cid ->
  regs_ok rg -> r <> tmp -> N < 2 ^ 32 ->
  exists rg',
    [/\ msil NC (S m rg n lv cid) (S m rg' (n + size (rp_load N r tmp)) lv cid),
        rg' (rk r) = Some (Atom (pcw N) Other),
        (forall k, (k == rk r) = false -> (k == rk tmp) = false -> rg' k = rg k)
      & regs_ok rg'].
Proof.
move=> Hc Hb Hx Hok Hrt HN.
move: Hb Hx. rewrite /rp_load. case: ifP => Hs Hb Hx.
- have HN15 : N < 2 ^ imm_size mt := imm_small_lt Hs.
  rewrite [n + size _](_ : _ = n.+1) in Hx *; last by rewrite addn1.
  exists (setm rg (rk r) (Atom (pcw N) Other)). split.
  + apply: msil_one. rewrite -(swcast_small HN15).
    exact: (step_const_blk lv Hc Hb Hx Hok).
  + rewrite setmE (eqxx (rk r)). exact: erefl.
  + move=> k Hk _. by rewrite setmE Hk.
  + exact: regs_ok_setm.
- rewrite /rp_digits in Hb Hx.
  rewrite [n + size _](_ : _ = n.+1 + 4 * 4) in Hx *; last by rewrite /=; lia.
  have [_ Hb1] := blk_cons Hb.
  have Hd4 : N %/ 2 ^ 28 < 2 ^ imm_size mt.
  { have H28 : 0 < 2 ^ 28 by rewrite expn_gt0.
    rewrite imm_size_mt (ltn_divLR _ _ H28) -expnD.
    apply: (ltn_trans HN). by rewrite ltn_exp2l. }
  set rg1 := setm rg (rk r) (Atom (pcw (N %/ 2 ^ 28)) Other).
  have S1 : step_me (NC := NC) (S m rg n lv cid) (S m rg1 n.+1 lv cid) None.
  { rewrite /rg1 -(swcast_small Hd4).
    exact: (step_const_blk lv Hc Hb (blk_nxt Hb1 erefl) Hok). }
  have Hok1 : regs_ok rg1 := regs_ok_setm _ _ Hok.
  have Hr1 : rg1 (rk r) = Some (Atom (pcw (N %/ 2 ^ 28)) Other).
  { rewrite /rg1 setmE (eqxx (rk r)). exact: erefl. }
  have Hall : all (fun d => d < 2 ^ 7)
      [:: (N %/ 2 ^ 21) %% 2 ^ 7; (N %/ 2 ^ 14) %% 2 ^ 7;
          (N %/ 2 ^ 7) %% 2 ^ 7; N %% 2 ^ 7].
  { have H7 : 0 < 2 ^ 7 by rewrite expn_gt0.
    rewrite /= !(ltn_pmod _ H7). exact: erefl. }
  have [rg' [Hs' Hr' Hk' Hok']] := run_digits lv Hc Hb1 Hx Hok1 Hrt Hall Hr1.
  rewrite digits_rec in Hr'.
  exists rg'. split.
  + apply: (msil_step S1).
    exact: Hs'.
  + exact: Hr'.
  + move=> k Hk1 Hk2. rewrite Hk' // /rg1 setmE Hk1. exact: erefl.
  + exact: Hok'.
Qed.

End Seg.

From mathcomp Require Import ssralg ssrint.

Lemma Zof_nat_expn2 (k : nat) : Z.of_nat (2 ^ k) = Z.pow 2 (Z.of_nat k).
Proof.
elim: k => [//|k IH]. rewrite expnS Nat2Z.inj_succ Z.pow_succ_r; last by lia.
rewrite -IH. by lia.
Qed.

Lemma convert_subz' (a b : nat) :
  Symbolic.convert ((a%:Z) - (b%:Z))%R = Z.sub (Z.of_nat a) (Z.of_nat b).
Proof.
case: (leqP b a) => H.
- rewrite (subzn H) /=. by lia.
- have -> : ((a%:Z) - (b%:Z))%R = Negz (b - a).-1 by lia.
  rewrite /=. by lia.
Qed.

Lemma rp_word_lt (z : Z) : rp_word z < 2 ^ 32.
Proof.
rewrite /rp_word.
apply/ltP. apply/Nat2Z.inj_lt. rewrite Zof_nat_expn2 Z2Nat.id.
- have := Z.mod_pos_bound z (Z.pow 2 32). by lia.
- have := Z.mod_pos_bound z (Z.pow 2 32). by lia.
Qed.

Lemma convert_rp_word (z : Z) :
  Z.le (Z.opp (Z.pow 2 31)) z /\ Z.lt z (Z.pow 2 31) ->
  Symbolic.convert (int_of_word (pcw (rp_word z) : mword mt)) = z.
Proof.
move=> Hz.
have HN := rp_word_lt z.
have Hv : fintype.nat_of_ord (ord_of_word (pcw (rp_word z) : mword mt)) = rp_word z.
{ rewrite /word_of_nat valw_as_word word_size_mt. exact: modn_small. }
have EN : Z.of_nat (rp_word z) = Z.modulo z (Z.pow 2 32).
{ rewrite /rp_word Z2Nat.id //. have := Z.mod_pos_bound z (Z.pow 2 32). by lia. }
have H32 := Zof_nat_expn2 32. have H31 := Zof_nat_expn2 31.
rewrite /int_of_word Hv word_size_mt /=.
case: ifP => Hlt.
- rewrite /=. rewrite EN.
  have Hlt' : Z.lt (Z.of_nat (rp_word z)) (Z.pow 2 31).
  { rewrite -H31. apply/Nat2Z.inj_lt. apply/ltP. exact: Hlt. }
  rewrite EN in Hlt'.
  clear Hv HN EN H32 H31 Hlt.
  have Hm : Z.le 0 z.
  { case: (Z.le_gt_cases 0 z) => [//|Hneg].
    exfalso.
    have E : Z.modulo z (Z.pow 2 32) = Z.add z (Z.pow 2 32).
    { rewrite -(Z.mod_add z 1 (Z.pow 2 32)); last by clear; lia.
      rewrite Z.mod_small; first by clear; lia.
      clear -Hneg Hz. lia. }
    rewrite E in Hlt'. clear -Hlt' Hz. lia. }
  apply: Z.mod_small. clear -Hm Hz. lia.
- rewrite convert_subz' EN H32.
  have Hge : Z.le (Z.pow 2 31) (Z.of_nat (rp_word z)).
  { rewrite -H31. apply/Nat2Z.inj_le. apply/leP. rewrite leqNgt Hlt. exact: erefl. }
  rewrite EN in Hge.
  clear Hv HN EN H32 H31 Hlt.
  have Hneg : Z.lt z 0.
  { case: (Z.lt_ge_cases z 0) => [//|Hpos].
    exfalso. rewrite Z.mod_small in Hge; first by clear -Hge Hz; lia.
    clear -Hpos Hz. lia. }
  have E : Z.modulo z (Z.pow 2 32) = Z.add z (Z.pow 2 32).
  { rewrite -(Z.mod_add z 1 (Z.pow 2 32)); last by clear; lia.
    rewrite Z.mod_small; first by clear; lia.
    clear -Hneg Hz. lia. }
  rewrite E. clear. lia.
Qed.
