Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import CompCert.Events.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From mathcomp Require ssralg.
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
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import MicroPolicies.Recomposition.LabelScheme.
Require Import T2M.MMemBase.
Require Import T2M.MPos.
Require Import Backtranslation_ME_MP.
Require Import Backtranslation_ME_MP_Step.
Require Import Backtranslation_ME_MP_Seg.
Require Import Backtranslation_ME_MP_Alloc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Notation minstr := (@Merged.instr mt).

Lemma lt14_ws (x : nat) : x < 2 ^ 14 -> x < 2 ^ word_size mt.
Proof. move=> H. apply: (ltn_trans H). by rewrite word_size_mt ltn_exp2l. Qed.

Lemma pcw_eqE (a b : nat) :
  a < 2 ^ 14 -> b < 2 ^ 14 -> (pcw a == pcw b) = (a == b).
Proof. move=> Ha Hb. exact: (won_eqE (lt14_ws Ha) (lt14_ws Hb)). Qed.

Lemma one_neq0 : (pcw 1 : mword mt) != 0%w.
Proof.
have H1 : 1 < 2 ^ 14 by rewrite -[X in X < _](expn0 2) ltn_exp2l.
have H0 : 0 < 2 ^ 14 by rewrite expn_gt0.
have -> : (0%w : mword mt) = pcw 0 by [].
by rewrite (pcw_eqE H1 H0).
Qed.

Section Run.

Variable NC : nat.
Variable cde : @Merged.code mt.
Variable pc0 : nat.
Hypothesis Hbound : pc0 + size cde < 2 ^ word_size mt.
Hypothesis Hsmall : pc0 + size cde < alloc_label.

Local Notation S m rg n lv cid :=
  (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (pc0 + n)) (Level lv cid)) tt).

Lemma step_load_blk m (rg : rmap) n lv cid r1 r2 w1 w2 vt2 e2 l :
  code_in cde pc0 m ->
  blk cde n cid (MrLoad r1 r2 :: l) -> nxt cde n.+1 cid ->
  regs_ok rg ->
  rg (rk r1) = Some (Atom w1 Other) ->
  m w1 = Some (Atom w2 (MTag vt2 cid e2 false)) ->
  step_me (NC := NC) (S m rg n lv cid)
    (S (setm m w1 (Atom w2 (MTag (if is_address vt2 then Invalidated else Other) cid e2 false)))
       (setm rg (rk r2) (Atom w2 vt2)) n.+1 lv cid) None.
Proof.
move=> Hc Hb [i1 [tg1 [Hn1 Hc1]]] Hok H1 Hm.
have [Hn _] := blk_cons Hb.
have [rc Hrc] := regs_ok_rk R_COM Hok.
have [old Hold] := regs_ok_rk r2 Hok.
exact: (me_step_load NC Hbound lv Hc Hn erefl erefl Hn1 Hc1 Hrc H1 Hm Hold).
Qed.

Lemma step_store_blk m (rg : rmap) n lv cid r1 r2 w1 w2 t2 wo vto eo l :
  code_in cde pc0 m ->
  blk cde n cid (MrStore r1 r2 :: l) -> nxt cde n.+1 cid ->
  regs_ok rg ->
  rg (rk r1) = Some (Atom w1 Other) ->
  rg (rk r2) = Some (Atom w2 t2) ->
  m w1 = Some (Atom wo (MTag vto cid eo false)) ->
  step_me (NC := NC) (S m rg n lv cid)
    (S (setm m w1 (Atom w2 (MTag t2 cid eo false)))
       (setm rg (rk r2) (Atom w2 (if is_address t2 then Invalidated else Other))) n.+1 lv cid)
    None.
Proof.
move=> Hc Hb [i1 [tg1 [Hn1 Hc1]]] Hok H1 H2 Hm.
have [Hn _] := blk_cons Hb.
have [rc Hrc] := regs_ok_rk R_COM Hok.
exact: (me_step_store NC Hbound lv Hc Hn erefl erefl Hn1 Hc1 Hrc H1 H2 Hm).
Qed.

Lemma step_mov_blk m (rg : rmap) n lv cid (r1 r2 : register) w1 t1 l :
  code_in cde pc0 m ->
  blk cde n cid (MrMov (inl r1) (inl r2) :: l) -> nxt cde n.+1 cid ->
  regs_ok rg ->
  rg (rk r1) = Some (Atom w1 t1) ->
  step_me (NC := NC) (S m rg n lv cid)
    (S m (setm (setm rg (rk r1) (Atom w1 (if is_address t1 then Invalidated else Other)))
               (rk r2) (Atom w1 t1)) n.+1 lv cid) None.
Proof.
move=> Hc Hb [i1 [tg1 [Hn1 Hc1]]] Hok H1.
have [Hn _] := blk_cons Hb.
have [rc Hrc] := regs_ok_rk R_COM Hok.
have [old Hold] := regs_ok_rk r2 Hok.
exact: (me_step_mov NC Hbound lv Hc Hn erefl erefl Hn1 Hc1 Hrc H1 Hold).
Qed.

Lemma step_label_blk m (rg : rmap) n lv cid lab l :
  code_in cde pc0 m ->
  blk cde n cid (MrLabel lab :: l) -> nxt cde n.+1 cid ->
  regs_ok rg ->
  step_me (NC := NC) (S m rg n lv cid) (S m rg n.+1 lv cid) None.
Proof.
move=> Hc Hb [i1 [tg1 [Hn1 Hc1]]] Hok.
have [Hn _] := blk_cons Hb.
have [rc Hrc] := regs_ok_rk R_COM Hok.
exact: (me_step_label NC Hbound lv Hc Hn erefl erefl Hn1 Hc1 Hrc).
Qed.

Definition lab_at (lab k cid : nat) : Prop :=
  findopt (is_label_def lab) cde = Some k /\
  List.nth_error cde k = Some (MrLabel lab, def_mem_tag cid true).

Lemma step_bnz_taken_blk m (rg : rmap) n lv cid r lab k w l :
  code_in cde pc0 m ->
  blk cde n cid (MrBnz r lab :: l) ->
  lab_at lab k cid -> n < k ->
  regs_ok rg ->
  rg (rk r) = Some (Atom w Other) -> w != 0%w ->
  step_me (NC := NC) (S m rg n lv cid) (S m rg k lv cid) None.
Proof.
move=> Hc Hb [Hf Hk] Hnk Hok H1 Hw.
have [Hn _] := blk_cons Hb.
have [rc Hrc] := regs_ok_rk R_COM Hok.
exact: (me_step_bnz_taken NC Hbound Hsmall lv Hc Hn erefl erefl Hf Hnk Hk erefl Hrc H1 Hw).
Qed.

Lemma step_bnz_fall_blk m (rg : rmap) n lv cid r lab l :
  code_in cde pc0 m ->
  blk cde n cid (MrBnz r lab :: l) -> nxt cde n.+1 cid ->
  regs_ok rg ->
  rg (rk r) = Some (Atom 0%w Other) ->
  step_me (NC := NC) (S m rg n lv cid) (S m rg n.+1 lv cid) None.
Proof.
move=> Hc Hb [i1 [tg1 [Hn1 Hc1]]] Hok H1.
have [Hn _] := blk_cons Hb.
have [rc Hrc] := regs_ok_rk R_COM Hok.
exact: (me_step_bnz_fall NC Hbound lv Hc Hn erefl erefl Hn1 Hc1 Hrc H1).
Qed.

Lemma step_goto_blk m (rg : rmap) n lv cid lab k l :
  code_in cde pc0 m ->
  blk cde n cid (MrJal lab :: l) -> nxt cde n.+1 cid ->
  lab_at lab k cid ->
  regs_ok rg ->
  step_me (NC := NC) (S m rg n lv cid)
    (S m (setm rg (wk 4) (Atom (pcw (pc0 + n.+1)) InternalJump)) k lv cid) None.
Proof.
move=> Hc Hb [i1 [tg1 [Hn1 Hc1]]] [Hf Hk] Hok.
have [Hn _] := blk_cons Hb.
have Hksz : k < size cde := nth_error_size Hk.
have Hlt : pc0 + k < 2 ^ imm_size mt.
{ apply: (imm_lt Hsmall). rewrite leq_add2l. exact: ltnW. }
have Hlp : code_label_pos cde pc0 lab (pc0 + n) = pc0 + k by rewrite /code_label_pos Hf.
have [[vk tk] [Hvk /= Htk _]] := me_fetch Hbound Hc Hk.
apply: (me_step_jal_int NC Hbound lv Hc Hn erefl erefl Hn1 Hc1 Hlp Hlt _ Hok).
by rewrite Hvk /= Htk.
Qed.

Variables L P C : nat.

Lemma lt14_32 (x : nat) : x < 2 ^ 14 -> x < 2 ^ 32.
Proof. move=> H. apply: (ltn_trans H). by rewrite ltn_exp2l. Qed.

Lemma eq_word_false (a b : nat) :
  a < 2 ^ 14 -> b < 2 ^ 14 -> a != b ->
  binop_denote (binop_trans Eq) (pcw a : mword mt) (pcw b) = 0%w.
Proof.
move=> Ha Hb Hab. rewrite /= (pcw_eqE Ha Hb) (negbTE Hab). exact: erefl.
Qed.

Lemma eq_word_true (a : nat) :
  a < 2 ^ 14 ->
  binop_denote (binop_trans Eq) (pcw a : mword mt) (pcw a) = pcw 1.
Proof. move=> Ha. rewrite /= (pcw_eqE Ha Ha) eqxx. exact: erefl. Qed.

Lemma size_rp_test cid j :
  size (rp_test L cid j) = (size (rp_load j R_ARG R_COM)).+2.
Proof. by rewrite /rp_test size_cat /= addn2. Qed.

Lemma run_test_fail m (rg : rmap) n lv cid j cnt :
  code_in cde pc0 m ->
  blk cde n cid (rp_test L cid j) -> nxt cde (n + size (rp_test L cid j)) cid ->
  regs_ok rg -> rg (rk R_AUX2) = Some (Atom (pcw cnt) Other) ->
  cnt != j -> cnt < 2 ^ 14 -> j < 2 ^ 14 ->
  exists rg',
    [/\ msil NC (S m rg n lv cid) (S m rg' (n + size (rp_test L cid j)) lv cid),
        (forall k, (k == rk R_ARG) = false -> (k == rk R_COM) = false -> rg' k = rg k)
      & regs_ok rg'].
Proof.
move=> Hc Hb Hx Hok H2 Hne Hcnt Hj.
move: Hb. rewrite /rp_test => /blk_cat [Hb1 Hb2].
have Hx1 := blk_nxt Hb2 erefl.
have [rg1 [Hs1 Ha1 Hk1 Hok1]] :=
  run_load NC Hbound Hsmall lv Hc Hb1 Hx1 Hok (fun E => match E with end) (lt14_32 Hj).
have Hneq2a : (rk R_AUX2 == rk R_ARG) = false by apply: rk_neq.
have Hneq2c : (rk R_AUX2 == rk R_COM) = false by apply: rk_neq.
have H2' : rg1 (rk R_AUX2) = Some (Atom (pcw cnt) Other) by rewrite Hk1.
have [_ Hb3] := blk_cons Hb2.
have S2 := step_binop_blk NC Hbound lv Hc Hb2 (blk_nxt Hb3 erefl) Hok1 H2' Ha1.
rewrite (eq_word_false Hcnt Hj Hne) in S2.
set rg2 := setm rg1 (rk R_ARG) (Atom 0%w Other).
have Hok2 : regs_ok rg2 := regs_ok_setm _ _ Hok1.
have Ha2 : rg2 (rk R_ARG) = Some (Atom 0%w Other).
{ rewrite /rg2 setmE (eqxx (rk R_ARG)). exact: erefl. }
have Epos : n + size (rp_test L cid j) = (n + size (rp_load j R_ARG R_COM)).+2
  by rewrite size_rp_test addnS addnS.
rewrite Epos in Hx *.
have S3 := step_bnz_fall_blk lv Hc Hb3 Hx Hok2 Ha2.
exists rg2. split.
- apply: (msil_trans Hs1). apply: (msil_step S2). exact: msil_one S3.
- move=> k Hka Hkc. by rewrite /rg2 setmE Hka Hk1.
- exact: Hok2.
Qed.

Lemma run_test_hit m (rg : rmap) n lv cid j kp :
  code_in cde pc0 m ->
  blk cde n cid (rp_test L cid j) ->
  lab_at (rp_lab L cid (4 + j)) kp cid ->
  n + size (rp_test L cid j) <= kp ->
  regs_ok rg -> rg (rk R_AUX2) = Some (Atom (pcw j) Other) ->
  j < 2 ^ 14 ->
  exists rg',
    [/\ msil NC (S m rg n lv cid) (S m rg' kp lv cid),
        (forall k, (k == rk R_ARG) = false -> (k == rk R_COM) = false -> rg' k = rg k)
      & regs_ok rg'].
Proof.
move=> Hc Hb Hlab Hkp Hok H2 Hj.
move: Hb. rewrite /rp_test => /blk_cat [Hb1 Hb2].
have Hx1 := blk_nxt Hb2 erefl.
have [rg1 [Hs1 Ha1 Hk1 Hok1]] :=
  run_load NC Hbound Hsmall lv Hc Hb1 Hx1 Hok (fun E => match E with end) (lt14_32 Hj).
have Hneq2a : (rk R_AUX2 == rk R_ARG) = false by apply: rk_neq.
have Hneq2c : (rk R_AUX2 == rk R_COM) = false by apply: rk_neq.
have H2' : rg1 (rk R_AUX2) = Some (Atom (pcw j) Other) by rewrite Hk1.
have [_ Hb3] := blk_cons Hb2.
have S2 := step_binop_blk NC Hbound lv Hc Hb2 (blk_nxt Hb3 erefl) Hok1 H2' Ha1.
rewrite (eq_word_true Hj) in S2.
set rg2 := setm rg1 (rk R_ARG) (Atom (pcw 1) Other).
have Hok2 : regs_ok rg2 := regs_ok_setm _ _ Hok1.
have Ha2 : rg2 (rk R_ARG) = Some (Atom (pcw 1) Other).
{ rewrite /rg2 setmE (eqxx (rk R_ARG)). exact: erefl. }
have Hlt : (n + size (rp_load j R_ARG R_COM)).+1 < kp.
{ move: Hkp. by rewrite size_rp_test addnS addnS. }
have S3 := step_bnz_taken_blk lv Hc Hb3 Hlab Hlt Hok2 Ha2 one_neq0.
exists rg2. split.
- apply: (msil_trans Hs1). apply: (msil_step S2). exact: msil_one S3.
- move=> k Hka Hkc. by rewrite /rg2 setmE Hka Hk1.
- exact: Hok2.
Qed.

Lemma run_tests_fail m (rg : rmap) n lv cid ks cnt :
  code_in cde pc0 m ->
  blk cde n cid (flatten [seq rp_test L cid k | k <- ks]) ->
  nxt cde (n + size (flatten [seq rp_test L cid k | k <- ks])) cid ->
  regs_ok rg -> rg (rk R_AUX2) = Some (Atom (pcw cnt) Other) ->
  cnt \notin ks -> cnt < 2 ^ 14 -> all (fun k => k < 2 ^ 14) ks ->
  exists rg',
    [/\ msil NC (S m rg n lv cid)
          (S m rg' (n + size (flatten [seq rp_test L cid k | k <- ks])) lv cid),
        (forall k, (k == rk R_ARG) = false -> (k == rk R_COM) = false -> rg' k = rg k)
      & regs_ok rg'].
Proof.
elim: ks n rg => [|j ks IH] n rg Hc Hb Hx Hok H2 Hnin Hcnt Hall.
- exists rg. rewrite addn0. split; [exact: msil_refl | by [] | exact: Hok].
- move: Hall => /= /andP [Hj Hall].
  move: Hnin; rewrite inE negb_or => /andP [Hne Hnin].
  move: Hb Hx => /=. move=> /blk_cat [Hb1 Hb2] Hx.
  rewrite size_cat addnA in Hx.
  have Hx1 : nxt cde (n + size (rp_test L cid j)) cid.
  { case Eks: ks Hb2 => [|j' ks'] Hb2'.
    - move: Hx. by rewrite Eks /= addn0.
    - apply: (blk_nxt Hb2'). by rewrite /= size_cat size_rp_test. }
  have [rg1 [Hs1 Hk1 Hok1]] := run_test_fail lv Hc Hb1 Hx1 Hok H2 Hne Hcnt Hj.
  have H2' : rg1 (rk R_AUX2) = Some (Atom (pcw cnt) Other).
  { rewrite Hk1 //; exact: rk_neq. }
  have [rg' [Hs' Hk' Hok']] := IH _ rg1 Hc Hb2 Hx Hok1 H2' Hnin Hcnt Hall.
  have Epos : n + size (flatten [seq rp_test L cid k | k <- j :: ks])
              = n + size (rp_test L cid j) + size (flatten [seq rp_test L cid k | k <- ks]).
  { by rewrite [flatten _]/= size_cat addnA. }
  exists rg'. split.
  + rewrite Epos. exact: msil_trans Hs1 Hs'.
  + move=> k Hka Hkc. by rewrite Hk' // Hk1.
  + exact: Hok'.
Qed.

Lemma iota_split_at (cnt ne : nat) :
  cnt < ne -> iota 0 ne = iota 0 cnt ++ cnt :: iota cnt.+1 (ne - cnt.+1).
Proof.
move=> H. rewrite -{1}(subnKC (ltnW H)) iotaD add0n.
have -> : ne - cnt = (ne - cnt.+1).+1 by rewrite subnS prednK // subn_gt0.
by [].
Qed.

Lemma all_iota_lt (a b B : nat) : a + b <= B -> all (fun k => k < B) (iota a b).
Proof.
move=> H. apply/allP => k. rewrite mem_iota => /andP [_ Hk].
exact: (leq_trans Hk H).
Qed.

Lemma run_disp_pre m (rg : rmap) n lv cid A ctrl cnt ne e1 e2 :
  code_in cde pc0 m ->
  blk cde n cid (rp_disp L cid A ne) ->
  regs_ok rg ->
  A < 2 ^ 14 ->
  m (pcw A) = Some (Atom ctrl (MTag Other cid e1 false)) ->
  m ctrl = Some (Atom (pcw cnt) (MTag Other cid e2 false)) ->
  exists rg',
    [/\ msil NC (S m rg n lv cid) (S m rg' n.+4 lv cid),
        rg' (rk R_AUX1) = Some (Atom ctrl Other),
        rg' (rk R_AUX2) = Some (Atom (pcw cnt) Other)
      & regs_ok rg'].
Proof.
move=> Hc Hb Hok HA Hm1 Hm2.
have [_ Hb1] := blk_cons Hb.
have [_ Hb2] := blk_cons Hb1.
have [_ Hb3] := blk_cons Hb2.
have [_ Hb4] := blk_cons Hb3.
have Hx4 : nxt cde n.+4 cid.
{ apply: (blk_nxt Hb4). by rewrite size_cat /= addnS. }
have S0 := step_label_blk lv Hc Hb (blk_nxt Hb1 erefl) Hok.
have HA15 : A < 2 ^ imm_size mt by apply: imm_small_lt.
set rg1 := setm rg (rk R_SP) (Atom (pcw A) Other).
have S1 : step_me (NC := NC) (S m rg n.+1 lv cid) (S m rg1 n.+2 lv cid) None.
{ rewrite /rg1 -(swcast_small HA15). exact: step_const_blk Hc Hb1 (blk_nxt Hb2 erefl) Hok. }
have Hok1 : regs_ok rg1 := regs_ok_setm _ _ Hok.
have Hsp : rg1 (rk R_SP) = Some (Atom (pcw A) Other).
{ rewrite /rg1 setmE (eqxx (rk R_SP)). exact: erefl. }
have S2 := step_load_blk lv Hc Hb2 (blk_nxt Hb3 erefl) Hok1 Hsp Hm1.
rewrite /= (setm_id Hm1) in S2.
set rg2 := setm rg1 (rk R_AUX1) (Atom ctrl Other).
have Hok2 : regs_ok rg2 := regs_ok_setm _ _ Hok1.
have Ha1 : rg2 (rk R_AUX1) = Some (Atom ctrl Other).
{ rewrite /rg2 setmE (eqxx (rk R_AUX1)). exact: erefl. }
have S3 := step_load_blk lv Hc Hb3 Hx4 Hok2 Ha1 Hm2.
rewrite /= (setm_id Hm2) in S3.
set rg3 := setm rg2 (rk R_AUX2) (Atom (pcw cnt) Other).
exists rg3. split.
- apply: (msil_step S0). apply: (msil_step S1). apply: (msil_step S2). exact: msil_one S3.
- rewrite /rg3 setmE (rk_neq (r1 := R_AUX1) (r2 := R_AUX2) (fun E => match E with end)).
  exact: Ha1.
- rewrite /rg3 setmE (eqxx (rk R_AUX2)). exact: erefl.
- exact: regs_ok_setm.
Qed.

Lemma blk_disp_tests n cid A ne :
  blk cde n cid (rp_disp L cid A ne) ->
  blk cde n.+4 cid (flatten [seq rp_test L cid k | k <- iota 0 ne] ++ [:: MrHalt]).
Proof. rewrite /rp_disp => /blk_cat [_ H]. by rewrite -addn4. Qed.

Lemma size_rp_disp cid A ne :
  size (rp_disp L cid A ne) = size (flatten [seq rp_test L cid k | k <- iota 0 ne]) + 5.
Proof. rewrite /rp_disp !size_cat /=. lia. Qed.

Lemma run_disp_hit m (rg : rmap) n lv cid A ctrl cnt ne e1 e2 kp :
  code_in cde pc0 m ->
  blk cde n cid (rp_disp L cid A ne) ->
  regs_ok rg ->
  A < 2 ^ 14 ->
  m (pcw A) = Some (Atom ctrl (MTag Other cid e1 false)) ->
  m ctrl = Some (Atom (pcw cnt) (MTag Other cid e2 false)) ->
  cnt < ne -> ne <= 2 ^ 14 ->
  lab_at (rp_lab L cid (4 + cnt)) kp cid ->
  n + size (rp_disp L cid A ne) <= kp ->
  exists rg',
    [/\ msil NC (S m rg n lv cid) (S m rg' kp lv cid),
        rg' (rk R_AUX1) = Some (Atom ctrl Other),
        rg' (rk R_AUX2) = Some (Atom (pcw cnt) Other)
      & regs_ok rg'].
Proof.
move=> Hc Hb Hok HA Hm1 Hm2 Hcnt Hne Hlab Hkp.
have [rg1 [Hs1 Ha1 Ha2 Hok1]] := run_disp_pre lv Hc Hb Hok HA Hm1 Hm2.
have Hbt := blk_disp_tests Hb.
have Efc : forall (A : Type) (x : seq A) (xs : seq (seq A)),
    flatten (x :: xs) = x ++ flatten xs by [].
rewrite (iota_split_at Hcnt) map_cat flatten_cat map_cons Efc -catA -catA in Hbt.
move: Hbt => /blk_cat [Hbf Hbr].
move: Hbr => /blk_cat [Hbh _].
have Hcnt14 : cnt < 2 ^ 14 := leq_trans Hcnt Hne.
have Hxf : nxt cde (n.+4 + size (flatten [seq rp_test L cid k | k <- iota 0 cnt])) cid.
{ apply: (blk_nxt Hbh). by rewrite size_rp_test. }
have Hnin : cnt \notin iota 0 cnt by rewrite mem_iota ltnn andbF.
have Hall : all (fun k => k < 2 ^ 14) (iota 0 cnt).
{ apply: all_iota_lt. rewrite add0n. exact: ltnW. }
have [rg2 [Hs2 Hk2 Hok2]] := run_tests_fail lv Hc Hbf Hxf Hok1 Ha2 Hnin Hcnt14 Hall.
have Ha2' : rg2 (rk R_AUX2) = Some (Atom (pcw cnt) Other).
{ rewrite Hk2 //; exact: rk_neq. }
have Hkp' : n.+4 + size (flatten [seq rp_test L cid k | k <- iota 0 cnt])
            + size (rp_test L cid cnt) <= kp.
{ apply: (leq_trans _ Hkp). rewrite size_rp_disp (iota_split_at Hcnt) map_cat flatten_cat /=.
  rewrite !size_cat. lia. }
have [rg3 [Hs3 Hk3 Hok3]] := run_test_hit lv Hc Hbh Hlab Hkp' Hok2 Ha2' Hcnt14.
exists rg3. split.
- exact: msil_trans Hs1 (msil_trans Hs2 Hs3).
- rewrite Hk3; try exact: rk_neq. rewrite Hk2; try exact: rk_neq. exact: Ha1.
- rewrite Hk3; try exact: rk_neq. exact: Ha2'.
- exact: Hok3.
Qed.

Lemma run_disp_halt m (rg : rmap) n lv cid A ctrl ne e1 e2 :
  code_in cde pc0 m ->
  blk cde n cid (rp_disp L cid A ne) ->
  regs_ok rg ->
  A < 2 ^ 14 ->
  m (pcw A) = Some (Atom ctrl (MTag Other cid e1 false)) ->
  m ctrl = Some (Atom (pcw ne) (MTag Other cid e2 false)) ->
  ne < 2 ^ 14 ->
  exists rg' k,
    msil NC (S m rg n lv cid) (S m rg' k lv cid) /\
    final_halt_code (S m rg' k lv cid).
Proof.
move=> Hc Hb Hok HA Hm1 Hm2 Hne.
have [rg1 [Hs1 Ha1 Ha2 Hok1]] := run_disp_pre lv Hc Hb Hok HA Hm1 Hm2.
have Hbt := blk_disp_tests Hb.
move: Hbt => /blk_cat [Hbf Hbh].
have [Hh _] := blk_cons Hbh.
have Hxf : nxt cde (n.+4 + size (flatten [seq rp_test L cid k | k <- iota 0 ne])) cid.
{ by exists MrHalt, (def_mem_tag cid true). }
have Hnin : ne \notin iota 0 ne by rewrite mem_iota ltnn andbF.
have Hall : all (fun k => k < 2 ^ 14) (iota 0 ne).
{ apply: all_iota_lt. by rewrite add0n ltnW. }
have [rg2 [Hs2 Hk2 Hok2]] := run_tests_fail lv Hc Hbf Hxf Hok1 Ha2 Hnin Hne Hall.
exists rg2, (n.+4 + size (flatten [seq rp_test L cid k | k <- iota 0 ne])).
split.
- exact: msil_trans Hs1 Hs2.
- exact: (me_final_halt Hbound rg2 _ Hc Hh erefl).
Qed.

Lemma addw_pcwA (x : mword mt) a b : addw (addw x (pcw a)) (pcw b) = addw x (pcw (a + b)).
Proof. by rewrite -addwA pcw_add. Qed.

Lemma subw_pcw (x : mword mt) a : subw (addw x (pcw a.+1)) (pcw 1) = addw x (pcw a).
Proof.
have E1 : pcw a.+1 = addw (pcw a) (pcw 1) :> mword mt :=
  esym (etrans (pcw_add a 1) (f_equal (fun k => pcw k) (addn1 a))).
have E : addw x (pcw a.+1) = addw (addw x (pcw a)) (pcw 1) :=
  etrans (f_equal (addw x) E1) (addwA x (pcw a) (pcw 1)).
apply: (etrans (f_equal (fun y => subw y (pcw 1)) E)).
exact: (etrans (esym (addwA (addw x (pcw a)) (pcw 1) (oppw (pcw 1))))
          (etrans (f_equal (addw (addw x (pcw a))) (addwN (pcw 1)))
                  (addw0 (addw x (pcw a))))).
Qed.

Lemma run_case_pro m (rg : rmap) n lv cid lab ctrl cnt e l :
  code_in cde pc0 m ->
  blk cde n cid ([:: MrLabel lab; rp_const 1 R_ONE; MrBinop Add R_AUX2 R_ONE R_AUX2;
                     MrStore R_AUX1 R_AUX2] ++ l) ->
  0 < size l ->
  regs_ok rg ->
  rg (rk R_AUX1) = Some (Atom ctrl Other) ->
  rg (rk R_AUX2) = Some (Atom (pcw cnt) Other) ->
  m ctrl = Some (Atom (pcw cnt) (MTag Other cid e false)) ->
  exists rg',
    [/\ msil NC (S m rg n lv cid)
          (S (setm m ctrl (Atom (pcw cnt.+1) (MTag Other cid e false))) rg' n.+4 lv cid),
        rg' (rk R_AUX1) = Some (Atom ctrl Other)
      & regs_ok rg'].
Proof.
move=> Hc Hb Hl Hok H1 H2 Hm.
have [_ Hb1] := blk_cons Hb.
have [_ Hb2] := blk_cons Hb1.
have [_ Hb3] := blk_cons Hb2.
have [_ Hb4] := blk_cons Hb3.
have S0 := step_label_blk lv Hc Hb (blk_nxt Hb1 erefl) Hok.
have H1i : 1 < 2 ^ imm_size mt by rewrite imm_size_mt -[X in X < _](expn0 2) ltn_exp2l.
set rg1 := setm rg (rk R_ONE) (Atom (pcw 1) Other).
have S1 : step_me (NC := NC) (S m rg n.+1 lv cid) (S m rg1 n.+2 lv cid) None.
{ rewrite /rg1 -(swcast_small H1i). exact: step_const_blk Hc Hb1 (blk_nxt Hb2 erefl) Hok. }
have Hok1 : regs_ok rg1 := regs_ok_setm _ _ Hok.
have Hn1 : (rk R_AUX2 == rk R_ONE) = false by apply: rk_neq.
have Hn1' : (rk R_AUX1 == rk R_ONE) = false by apply: rk_neq.
have H2' : rg1 (rk R_AUX2) = Some (Atom (pcw cnt) Other) by rewrite /rg1 setmE Hn1.
have Ho : rg1 (rk R_ONE) = Some (Atom (pcw 1) Other).
{ rewrite /rg1 setmE (eqxx (rk R_ONE)). exact: erefl. }
have S2 := step_binop_blk NC Hbound lv Hc Hb2 (blk_nxt Hb3 erefl) Hok1 H2' Ho.
have Esum : binop_denote (binop_trans Add) (pcw cnt) (pcw 1) = pcw cnt.+1 :> mword mt.
{ by rewrite /= pcw_add addn1. }
rewrite Esum in S2.
set rg2 := setm rg1 (rk R_AUX2) (Atom (pcw cnt.+1) Other).
have Hok2 : regs_ok rg2 := regs_ok_setm _ _ Hok1.
have Hn2 : (rk R_AUX1 == rk R_AUX2) = false by apply: rk_neq.
have H1' : rg2 (rk R_AUX1) = Some (Atom ctrl Other) by rewrite /rg2 /rg1 !setmE Hn2 Hn1'.
have H2'' : rg2 (rk R_AUX2) = Some (Atom (pcw cnt.+1) Other).
{ rewrite /rg2 setmE (eqxx (rk R_AUX2)). exact: erefl. }
have S3 := step_store_blk lv Hc Hb3 (blk_nxt Hb4 Hl) Hok2 H1' H2'' Hm.
exists (setm rg2 (rk R_AUX2) (Atom (pcw cnt.+1) (if is_address Other then Invalidated else Other))).
split.
- apply: (msil_step S0). apply: (msil_step S1). apply: (msil_step S2). exact: msil_one S3.
- by rewrite setmE Hn2.
- exact: regs_ok_setm.
Qed.

Lemma size_rp_load_pos N r t : 0 < size (rp_load N r t).
Proof. rewrite /rp_load. by case: ifP. Qed.

Lemma code_in_setm m a v :
  code_in cde pc0 m -> encode_code cde pc0 a = None -> code_in cde pc0 (setm m a v).
Proof.
move=> Hc Ha w x Hw. rewrite setmE. case: eqP => [Ew|_]; last exact: Hc.
by rewrite Ew Ha in Hw.
Qed.

Lemma run_push m (rg : rmap) n lv cid ctrl d cap tc old vo e1 e2 l :
  code_in cde pc0 m ->
  blk cde n cid (rp_push ++ l) -> 0 < size l ->
  regs_ok rg ->
  rg (rk R_AUX1) = Some (Atom ctrl Other) ->
  rg (rk R_AUX2) = Some (Atom cap tc) ->
  m (addw ctrl (pcw 1)) = Some (Atom (addw ctrl (pcw (2 + d))) (MTag Other cid e1 false)) ->
  m (addw ctrl (pcw (2 + d))) = Some (Atom old (MTag vo cid e2 false)) ->
  addw ctrl (pcw 1) != addw ctrl (pcw (2 + d)) ->
  encode_code cde pc0 (addw ctrl (pcw (2 + d))) = None ->
  exists rg',
    [/\ msil NC (S m rg n lv cid)
          (S (setm (setm m (addw ctrl (pcw (2 + d))) (Atom cap (MTag tc cid e2 false)))
                   (addw ctrl (pcw 1))
                   (Atom (addw ctrl (pcw (2 + d).+1)) (MTag Other cid e1 false)))
             rg' n.+4.+2 lv cid),
        rg' (rk R_AUX1) = Some (Atom ctrl Other)
      & regs_ok rg'].
Proof.
move=> Hc Hb Hl Hok H1 H2 Hsp Hold Hne Hnc.
have [_ Hb1] := blk_cons Hb.
have [_ Hb2] := blk_cons Hb1.
have [_ Hb3] := blk_cons Hb2.
have [_ Hb4] := blk_cons Hb3.
have [_ Hb5] := blk_cons Hb4.
have [_ Hb6] := blk_cons Hb5.
have H1i : 1 < 2 ^ imm_size mt by rewrite imm_size_mt -[X in X < _](expn0 2) ltn_exp2l.
set rg1 := setm rg (rk R_ONE) (Atom (pcw 1) Other).
have S1 : step_me (NC := NC) (S m rg n lv cid) (S m rg1 n.+1 lv cid) None.
{ rewrite /rg1 -(swcast_small H1i). exact: step_const_blk Hc Hb (blk_nxt Hb1 erefl) Hok. }
have Hok1 : regs_ok rg1 := regs_ok_setm _ _ Hok.
have H11 : rg1 (rk R_AUX1) = Some (Atom ctrl Other) by rewrite /rg1 setmE rk_neq.
have Ho1 : rg1 (rk R_ONE) = Some (Atom (pcw 1) Other).
{ rewrite /rg1 setmE (eqxx (rk R_ONE)). exact: erefl. }
have S2 := step_binop_blk NC Hbound lv Hc Hb1 (blk_nxt Hb2 erefl) Hok1 H11 Ho1.
set rg2 := setm rg1 (rk R_SP) (Atom (binop_denote (binop_trans Add) ctrl (pcw 1)) Other).
have Hok2 : regs_ok rg2 := regs_ok_setm _ _ Hok1.
have Hs2 : rg2 (rk R_SP) = Some (Atom (addw ctrl (pcw 1)) Other).
{ rewrite /rg2 setmE (eqxx (rk R_SP)). exact: erefl. }
have S3 := step_load_blk lv Hc Hb2 (blk_nxt Hb3 erefl) Hok2 Hs2 Hsp.
rewrite /= (setm_id Hsp) in S3.
set rg3 := setm rg2 (rk R_ARG) (Atom (addw ctrl (pcw (2 + d))) Other).
have Hok3 : regs_ok rg3 := regs_ok_setm _ _ Hok2.
have Ha3 : rg3 (rk R_ARG) = Some (Atom (addw ctrl (pcw (2 + d))) Other).
{ rewrite /rg3 setmE (eqxx (rk R_ARG)). exact: erefl. }
have H23 : rg3 (rk R_AUX2) = Some (Atom cap tc).
{ by rewrite /rg3 /rg2 /rg1 !setmE !rk_neq. }
have S4 := step_store_blk lv Hc Hb3 (blk_nxt Hb4 erefl) Hok3 Ha3 H23 Hold.
set m1 := setm m (addw ctrl (pcw (2 + d))) (Atom cap (MTag tc cid e2 false)).
set rg4 := setm rg3 (rk R_AUX2) (Atom cap (if is_address tc then Invalidated else Other)).
have Hok4 : regs_ok rg4 := regs_ok_setm _ _ Hok3.
have Ha4 : rg4 (rk R_ARG) = Some (Atom (addw ctrl (pcw (2 + d))) Other).
{ by rewrite /rg4 setmE rk_neq. }
have Ho4 : rg4 (rk R_ONE) = Some (Atom (pcw 1) Other).
{ rewrite /rg4 setmE rk_neq; last by [].
  rewrite /rg3 setmE rk_neq; last by [].
  rewrite /rg2 setmE rk_neq; last by [].
  exact: Ho1. }
have Hc1 : code_in cde pc0 m1 := code_in_setm _ Hc Hnc.
have S5 := step_binop_blk NC Hbound lv Hc1 Hb4 (blk_nxt Hb5 erefl) Hok4 Ha4 Ho4.
set rg5 := setm rg4 (rk R_ARG)
             (Atom (binop_denote (binop_trans Add) (addw ctrl (pcw (2 + d))) (pcw 1)) Other).
have Hok5 : regs_ok rg5 := regs_ok_setm _ _ Hok4.
have Ea5 : binop_denote (binop_trans Add) (addw ctrl (pcw (2 + d))) (pcw 1)
           = addw ctrl (pcw (2 + d).+1) :> mword mt.
{ exact: (etrans (addw_pcwA ctrl (2 + d) 1) (f_equal (fun k => addw ctrl (pcw k)) (addn1 _))). }
have Ha5 : rg5 (rk R_ARG) = Some (Atom (addw ctrl (pcw (2 + d).+1)) Other).
{ rewrite /rg5 setmE (eqxx (rk R_ARG)).
  exact: (f_equal (fun w => Some (Atom w Other)) Ea5). }
have Hs5 : rg5 (rk R_SP) = Some (Atom (addw ctrl (pcw 1)) Other).
{ rewrite /rg5 setmE rk_neq; last by [].
  rewrite /rg4 setmE rk_neq; last by [].
  rewrite /rg3 setmE rk_neq; last by [].
  exact: Hs2. }
have Hsp1 : m1 (addw ctrl (pcw 1)) = Some (Atom (addw ctrl (pcw (2 + d))) (MTag Other cid e1 false)).
{ by rewrite /m1 setmE (negbTE Hne). }
have Hx6 : nxt cde n.+4.+2 cid := blk_nxt Hb6 Hl.
have S6 := step_store_blk lv Hc1 Hb5 Hx6 Hok5 Hs5 Ha5 Hsp1.
exists (setm rg5 (rk R_ARG)
          (Atom (addw ctrl (pcw (2 + d).+1)) (if is_address Other then Invalidated else Other))).
split.
- apply: (msil_step S1). apply: (msil_step S2). apply: (msil_step S3).
  apply: (msil_step S4). apply: (msil_step S5).
  exact: msil_one S6.
- rewrite setmE rk_neq; last by [].
  rewrite /rg5 setmE rk_neq; last by [].
  rewrite /rg4 setmE rk_neq; last by [].
  rewrite /rg3 setmE rk_neq; last by [].
  rewrite /rg2 setmE rk_neq; last by [].
  exact: H11.
- exact: regs_ok_setm.
Qed.

Lemma run_ret m (rg : rmap) n n' cid ctrl d cap z cid' C'' iw vtw etw icw e1 e2 :
  code_in cde pc0 m ->
  blk cde n cid (rp_case_body L P C cid (ERet cid' z C'')) ->
  regs_ok rg ->
  rg (rk R_AUX1) = Some (Atom ctrl Other) ->
  m (addw ctrl (pcw 1)) = Some (Atom (addw ctrl (pcw (2 + d).+1)) (MTag Other cid e1 false)) ->
  m (addw ctrl (pcw (2 + d))) = Some (Atom cap (MTag (Ret n') cid e2 false)) ->
  addw ctrl (pcw 1) != addw ctrl (pcw (2 + d)) ->
  encode_code cde pc0 (addw ctrl (pcw 1)) = None ->
  encode_code cde pc0 (addw ctrl (pcw (2 + d))) = None ->
  m cap = Some (Atom iw (MTag vtw C'' etw icw)) ->
  addw ctrl (pcw 1) != cap -> addw ctrl (pcw (2 + d)) != cap ->
  C'' != cid ->
  Z.le (Z.opp (Z.pow 2 31)) z /\ Z.lt z (Z.pow 2 31) ->
  exists rg',
    [/\ mtr NC (S m rg n n'.+1 cid) [:: ERet cid z C'']
          (@Symbolic.State mt lrc_tags unit
             (setm (setm m (addw ctrl (pcw 1))
                         (Atom (addw ctrl (pcw (2 + d))) (MTag Other cid e1 false)))
                   (addw ctrl (pcw (2 + d))) (Atom cap (MTag Invalidated cid e2 false)))
             rg' (Atom cap (Level n' C'')) tt)
      & regs_ok rg'].
Proof.
move=> Hc Hb Hok H1 Hsp Hfr Hne Hnc1 Hnc2 Hcap Hnc3 Hnc4 HC Hz.
move: Hb. rewrite /rp_case_body => Hb.
have Eb : [:: rp_const 1 R_ONE; MrBinop Add R_AUX1 R_ONE R_SP; MrLoad R_SP R_ARG;
              MrBinop Minus R_ARG R_ONE R_ARG; MrStore R_SP R_ARG; MrLoad R_ARG R_RA]
          ++ rp_load (rp_word z) R_COM R_ARG ++ [:: MrJump R_RA]
          = rp_const 1 R_ONE :: MrBinop Add R_AUX1 R_ONE R_SP :: MrLoad R_SP R_ARG
            :: MrBinop Minus R_ARG R_ONE R_ARG :: MrStore R_SP R_ARG :: MrLoad R_ARG R_RA
            :: (rp_load (rp_word z) R_COM R_ARG ++ [:: MrJump R_RA]) by [].
rewrite Eb in Hb.
have [_ Hb1] := blk_cons Hb.
have [_ Hb2] := blk_cons Hb1.
have [_ Hb3] := blk_cons Hb2.
have [_ Hb4] := blk_cons Hb3.
have [_ Hb5] := blk_cons Hb4.
have [_ Hb6] := blk_cons Hb5.
move: Hb6 => /blk_cat [Hbl Hbj].
have H1i : 1 < 2 ^ imm_size mt by rewrite imm_size_mt -[X in X < _](expn0 2) ltn_exp2l.
set rg1 := setm rg (rk R_ONE) (Atom (pcw 1) Other).
have S1 : step_me (NC := NC) (S m rg n n'.+1 cid) (S m rg1 n.+1 n'.+1 cid) None.
{ rewrite /rg1 -(swcast_small H1i). exact: step_const_blk Hc Hb (blk_nxt Hb1 erefl) Hok. }
have Hok1 : regs_ok rg1 := regs_ok_setm _ _ Hok.
have H11 : rg1 (rk R_AUX1) = Some (Atom ctrl Other).
{ rewrite /rg1 setmE rk_neq; last by []. exact: H1. }
have Ho1 : rg1 (rk R_ONE) = Some (Atom (pcw 1) Other).
{ rewrite /rg1 setmE (eqxx (rk R_ONE)). exact: erefl. }
have S2 := step_binop_blk NC Hbound n'.+1 Hc Hb1 (blk_nxt Hb2 erefl) Hok1 H11 Ho1.
set rg2 := setm rg1 (rk R_SP) (Atom (binop_denote (binop_trans Add) ctrl (pcw 1)) Other).
have Hok2 : regs_ok rg2 := regs_ok_setm _ _ Hok1.
have Hs2 : rg2 (rk R_SP) = Some (Atom (addw ctrl (pcw 1)) Other).
{ rewrite /rg2 setmE (eqxx (rk R_SP)). exact: erefl. }
have S3 := step_load_blk n'.+1 Hc Hb2 (blk_nxt Hb3 erefl) Hok2 Hs2 Hsp.
rewrite /= (setm_id Hsp) in S3.
set rg3 := setm rg2 (rk R_ARG) (Atom (addw ctrl (pcw (2 + d).+1)) Other).
have Hok3 : regs_ok rg3 := regs_ok_setm _ _ Hok2.
have Ha3 : rg3 (rk R_ARG) = Some (Atom (addw ctrl (pcw (2 + d).+1)) Other).
{ rewrite /rg3 setmE (eqxx (rk R_ARG)). exact: erefl. }
have Ho3 : rg3 (rk R_ONE) = Some (Atom (pcw 1) Other).
{ rewrite /rg3 setmE rk_neq; last by [].
  rewrite /rg2 setmE rk_neq; last by []. exact: Ho1. }
have S4 := step_binop_blk NC Hbound n'.+1 Hc Hb3 (blk_nxt Hb4 erefl) Hok3 Ha3 Ho3.
have Esub : binop_denote (binop_trans Minus) (addw ctrl (pcw (2 + d).+1)) (pcw 1)
            = addw ctrl (pcw (2 + d)) :> mword mt := subw_pcw ctrl (2 + d).
set rg4 := setm rg3 (rk R_ARG)
             (Atom (binop_denote (binop_trans Minus) (addw ctrl (pcw (2 + d).+1)) (pcw 1)) Other).
have Hok4 : regs_ok rg4 := regs_ok_setm _ _ Hok3.
have Ha4 : rg4 (rk R_ARG) = Some (Atom (addw ctrl (pcw (2 + d))) Other).
{ rewrite /rg4 setmE (eqxx (rk R_ARG)).
  exact: (f_equal (fun w => Some (Atom w Other)) Esub). }
have Hs4 : rg4 (rk R_SP) = Some (Atom (addw ctrl (pcw 1)) Other).
{ rewrite /rg4 setmE rk_neq; last by [].
  rewrite /rg3 setmE rk_neq; last by []. exact: Hs2. }
have S5 := step_store_blk n'.+1 Hc Hb4 (blk_nxt Hb5 erefl) Hok4 Hs4 Ha4 Hsp.
set m1 := setm m (addw ctrl (pcw 1)) (Atom (addw ctrl (pcw (2 + d))) (MTag Other cid e1 false)).
set rg5 := setm rg4 (rk R_ARG) (Atom (addw ctrl (pcw (2 + d)))
                                  (if is_address Other then Invalidated else Other)).
have Hok5 : regs_ok rg5 := regs_ok_setm _ _ Hok4.
have Hc1 : code_in cde pc0 m1 := code_in_setm _ Hc Hnc1.
have Ha5 : rg5 (rk R_ARG) = Some (Atom (addw ctrl (pcw (2 + d))) Other).
{ rewrite /rg5 setmE (eqxx (rk R_ARG)). exact: erefl. }
have Hfr1 : m1 (addw ctrl (pcw (2 + d))) = Some (Atom cap (MTag (Ret n') cid e2 false)).
{ rewrite /m1 setmE eq_sym (negbTE Hne). exact: Hfr. }
have Hx6 : nxt cde n.+4.+2 cid := blk_nxt Hbl (size_rp_load_pos _ _ _).
have S6 := step_load_blk n'.+1 Hc1 Hb5 Hx6 Hok5 Ha5 Hfr1.
rewrite /= in S6.
set m2 := setm m1 (addw ctrl (pcw (2 + d))) (Atom cap (MTag Invalidated cid e2 false)).
set rg6 := setm rg5 (rk R_RA) (Atom cap (Ret n')).
have Hok6 : regs_ok rg6 := regs_ok_setm _ _ Hok5.
have Hc2 : code_in cde pc0 m2 := code_in_setm _ Hc1 Hnc2.
have Hxl : nxt cde (n.+4.+2 + size (rp_load (rp_word z) R_COM R_ARG)) cid :=
  blk_nxt Hbj erefl.
have [rg7 [Hs7 Hc7 Hk7 Hok7]] :=
  run_load NC Hbound Hsmall n'.+1 Hc2 Hbl Hxl Hok6 (fun E => match E with end) (rp_word_lt z).
have [Hj _] := blk_cons Hbj.
have Hra7 : rg7 (wk 4) = Some (Atom cap (Ret n')).
{ have -> : wk 4 = rk R_RA by [].
  rewrite Hk7; [|exact: rk_neq|exact: rk_neq].
  rewrite /rg6 setmE (eqxx (rk R_RA)). exact: erefl. }
have Hcom7 : rg7 (wk 1) = Some (Atom (pcw (rp_word z)) Other) := Hc7.
have Hcap2 : m2 cap = Some (Atom iw (MTag vtw C'' etw icw)).
{ rewrite /m2 setmE eq_sym (negbTE Hnc4) /m1 setmE eq_sym (negbTE Hnc3). exact: Hcap. }
have [rg8 [S8 _ Hok8]] := me_step_jump_ret NC Hbound Hc2 Hj erefl erefl Hra7 Hcap2 HC Hcom7 Hok7.
rewrite (convert_rp_word Hz) in S8.
exists rg8. split; last exact: Hok8.
apply: (mtr_sil S1). apply: (mtr_sil S2). apply: (mtr_sil S3).
apply: (mtr_sil S4). apply: (mtr_sil S5). apply: (mtr_sil S6).
apply: (mtr_trans (msil_mtr Hs7) (t2 := [:: ERet cid z C''])).
exact: (mtr_ev S8 (mtr_refl _ _)).
Qed.

Lemma run_call m (rg : rmap) n lv cid z cid' P' C' ep iep vt' lst ic' :
  code_in cde pc0 m ->
  blk cde n cid (rp_case_body L P C cid (ECall cid' P' z C')) ->
  regs_ok rg ->
  findopt (is_label_def (mk_entry L P C C' P')) cde = Some ep ->
  List.nth_error cde ep = Some (iep, MTag vt' C' (Some (P', lst)) ic') ->
  C' != cid -> cid \in lst ->
  Z.le (Z.opp (Z.pow 2 31)) z /\ Z.lt z (Z.pow 2 31) ->
  exists rg',
    [/\ mtr NC (S m rg n lv cid) [:: ECall cid P' z C']
          (@Symbolic.State mt lrc_tags unit m rg' (Atom (pcw (pc0 + ep)) (Level lv.+1 C')) tt),
        rg' (wk 4) = Some (Atom (pcw (pc0 + (n + size (rp_load (rp_word z) R_COM R_ARG)).+1))
                                (Ret lv))
      & regs_ok rg'].
Proof.
move=> Hc Hb Hok Hf Hep HC Hl Hz.
move: Hb. rewrite /rp_case_body => /blk_cat [Hbl Hbj].
have [Hj Hbg] := blk_cons Hbj.
have Hxl : nxt cde (n + size (rp_load (rp_word z) R_COM R_ARG)) cid := blk_nxt Hbj erefl.
have [rg1 [Hs1 Hc1 Hk1 Hok1]] :=
  run_load NC Hbound Hsmall lv Hc Hbl Hxl Hok (fun E => match E with end) (rp_word_lt z).
have [i1 [tg1 [Hn1 Hcol1]]] : nxt cde (n + size (rp_load (rp_word z) R_COM R_ARG)).+1 cid :=
  blk_nxt Hbg erefl.
have Hksz : ep < size cde := nth_error_size Hep.
have Hlt : pc0 + ep < 2 ^ imm_size mt.
{ apply: (imm_lt Hsmall). rewrite leq_add2l. exact: ltnW. }
have Hlp : code_label_pos cde pc0 (mk_entry L P C C' P')
             (pc0 + (n + size (rp_load (rp_word z) R_COM R_ARG))) = pc0 + ep
  by rewrite /code_label_pos Hf.
have [[vep tep] [Hvep /= Htep _]] := me_fetch Hbound Hc Hep.
subst tep.
have Hcom1 : rg1 (wk 1) = Some (Atom (pcw (rp_word z)) Other) := Hc1.
have [rg' [S2 Hra Hcom' Hok']] :=
  me_step_jal_call NC Hbound lv Hc Hj erefl erefl Hn1 Hcol1 Hlp Hlt Hvep HC Hl Hcom1 Hok1.
rewrite (convert_rp_word Hz) in S2.
exists rg'. split; [|exact: Hra|exact: Hok'].
apply: (mtr_trans (msil_mtr Hs1) (t2 := [:: ECall cid P' z C'])).
exact: (mtr_ev S2 (mtr_refl _ _)).
Qed.

Variable t : trace.

Definition init_pre (cid A j : nat) : seq minstr :=
  [:: rp_const A R_SP; MrLoad R_SP R_AUX1; MrBnz R_AUX1 (rp_lab L cid j)]
  ++ rp_load (rp_blocks t) R_ARG R_ONE
  ++ [:: MrMov (inl R_ARG) (inr R_SC_ARG1); MrJal alloc_label;
         MrMov (inr R_SC_RET) (inl R_AUX1); MrStore R_SP R_AUX1;
         rp_const 2 R_ARG; MrBinop Add R_AUX1 R_ARG R_ARG;
         rp_const 1 R_ONE; MrBinop Add R_AUX1 R_ONE R_SP; MrStore R_SP R_ARG].

Lemma rp_init_split cid A j :
  rp_init L t cid A j = init_pre cid A j ++ [:: MrLabel (rp_lab L cid j)].
Proof. by rewrite /rp_init /init_pre -!catA. Qed.

Lemma run_init_skip m (rg : rmap) n lv cid A j ctrl e :
  code_in cde pc0 m ->
  blk cde n cid (rp_init L t cid A j) ->
  nxt cde (n + size (rp_init L t cid A j)) cid ->
  lab_at (rp_lab L cid j) (n + size (init_pre cid A j)) cid ->
  regs_ok rg -> A < 2 ^ 14 ->
  m (pcw A) = Some (Atom ctrl (MTag Other cid e false)) -> ctrl != 0%w ->
  exists rg',
    [/\ msil NC (S m rg n lv cid) (S m rg' (n + size (rp_init L t cid A j)) lv cid),
        rg' (rk R_AUX1) = Some (Atom ctrl Other),
        rg' (rk R_AUX2) = rg (rk R_AUX2)
      & regs_ok rg'].
Proof.
move=> Hc Hb Hx Hlab Hok HA Hm Hne.
have Hb' := Hb. rewrite rp_init_split in Hb'.
move: Hb' => /blk_cat [Hbp Hbl].
have [_ Hb1] := blk_cons Hbp.
have [_ Hb2] := blk_cons Hb1.
have HA15 : A < 2 ^ imm_size mt by apply: imm_small_lt.
set rg1 := setm rg (rk R_SP) (Atom (pcw A) Other).
have S1 : step_me (NC := NC) (S m rg n lv cid) (S m rg1 n.+1 lv cid) None.
{ rewrite /rg1 -(swcast_small HA15). exact: step_const_blk Hc Hbp (blk_nxt Hb1 erefl) Hok. }
have Hok1 : regs_ok rg1 := regs_ok_setm _ _ Hok.
have Hs1 : rg1 (rk R_SP) = Some (Atom (pcw A) Other).
{ rewrite /rg1 setmE (eqxx (rk R_SP)). exact: erefl. }
have S2 := step_load_blk lv Hc Hb1 (blk_nxt Hb2 erefl) Hok1 Hs1 Hm.
rewrite /= (setm_id Hm) in S2.
set rg2 := setm rg1 (rk R_AUX1) (Atom ctrl Other).
have Hok2 : regs_ok rg2 := regs_ok_setm _ _ Hok1.
have Ha2 : rg2 (rk R_AUX1) = Some (Atom ctrl Other).
{ rewrite /rg2 setmE (eqxx (rk R_AUX1)). exact: erefl. }
have Hlt : n.+2 < n + size (init_pre cid A j).
{ rewrite /init_pre !size_cat /=. lia. }
have S3 := step_bnz_taken_blk lv Hc Hb2 Hlab Hlt Hok2 Ha2 Hne.
have [Hlb _] := blk_cons Hbl.
have Hx' : nxt cde (n + size (init_pre cid A j)).+1 cid.
{ move: Hx. by rewrite rp_init_split size_cat addnA addn1. }
have S4 := step_label_blk lv Hc Hbl Hx' Hok2.
have E : n + size (rp_init L t cid A j) = (n + size (init_pre cid A j)).+1.
{ by rewrite rp_init_split size_cat addnA addn1. }
exists rg2. split.
- apply: (msil_step S1). apply: (msil_step S2). apply: (msil_step S3).
  rewrite E. exact: msil_one S4.
- exact: Ha2.
- rewrite /rg2 setmE rk_neq; last by [].
  rewrite /rg1 setmE rk_neq; last by []. exact: erefl.
- exact: Hok2.
Qed.

Lemma int_of_word_small (B : nat) :
  B < 2 ^ 14 -> int_of_word (pcw B : mword mt) = ssrint.Posz B.
Proof.
move=> HB.
have Hv : fintype.nat_of_ord (ord_of_word (pcw B : mword mt)) = B.
{ rewrite /word_of_nat valw_as_word. exact: modn_small (lt14_ws HB). }
rewrite /int_of_word Hv.
have -> : B < 2 ^ (word_size mt).-1.
{ apply: (ltn_trans HB). by rewrite word_size_mt ltn_exp2l. }
by [].
Qed.

Lemma setm_ne' (T : ordType) (V : Type) (mm : {fmap T -> V}) k v k' :
  (k' == k) = false -> setm mm k v k' = mm k'.
Proof. move=> H. by rewrite setmE H. Qed.

Lemma code_in_unionm m m2 : code_in cde pc0 m -> code_in cde pc0 (unionm m m2).
Proof. move=> Hc w v Hw. by rewrite unionmE (Hc _ _ Hw). Qed.

Lemma step_movs_blk m (rg : rmap) n lv cid (r1 r2 : register + sys_reg) w1 t1 l :
  code_in cde pc0 m ->
  blk cde n cid (MrMov r1 r2 :: l) -> nxt cde n.+1 cid ->
  regs_ok rg ->
  rg (@word_of_nat (reg_field_size mt) (to_nat_bis r1)) = Some (Atom w1 t1) ->
  (exists old, rg (@word_of_nat (reg_field_size mt) (to_nat_bis r2)) = Some old) ->
  step_me (NC := NC) (S m rg n lv cid)
    (S m (setm (setm rg (@word_of_nat (reg_field_size mt) (to_nat_bis r1))
                    (Atom w1 (if is_address t1 then Invalidated else Other)))
               (@word_of_nat (reg_field_size mt) (to_nat_bis r2)) (Atom w1 t1)) n.+1 lv cid)
    None.
Proof.
move=> Hc Hb [i1 [tg1 [Hn1 Hc1]]] Hok H1 [old Hold].
have [Hn _] := blk_cons Hb.
have [rc Hrc] := regs_ok_rk R_COM Hok.
exact: (me_step_mov NC Hbound lv Hc Hn erefl erefl Hn1 Hc1 Hrc H1 Hold).
Qed.

Lemma run_init_alloc m (rg : rmap) n lv cid A j e :
  code_in cde pc0 m ->
  blk cde n cid (rp_init L t cid A j) ->
  nxt cde (n + size (rp_init L t cid A j)) cid ->
  regs_ok rg -> A < 2 ^ 14 ->
  m (pcw A) = Some (Atom 0%w (MTag Other cid e false)) ->
  encode_code cde pc0 (pcw A) = None ->
  m (pcw alloc_label) = None ->
  findopt (is_label_def alloc_label) cde = None ->
  NC <= word_size mt -> 1 + cid < 2 ^ NC ->
  (rp_blocks t).+2 <= 2 ^ (word_size mt - NC) ->
  rp_blocks t < 2 ^ 14 ->
  (forall w, pfilterC NC cid w -> m w = None) ->
  (forall w, pfilterC NC cid w -> encode_code cde pc0 w = None) ->
  ~~ pfilterC NC cid (pcw A) ->
  exists rg',
    [/\ msil NC (S m rg n lv cid)
          (S (setm (setm (unionm m (mkfmap (blkseq NC cid (rp_blocks t))))
                         (pcw A) (Atom (ctrlw NC cid) (MTag Other cid e false)))
                   (addw (ctrlw NC cid) (pcw 1))
                   (Atom (addw (ctrlw NC cid) (pcw 2)) (MTag Other cid None false)))
             rg' (n + size (rp_init L t cid A j)) lv cid),
        rg' (rk R_AUX1) = Some (Atom (ctrlw NC cid) Other),
        rg' (rk R_AUX2) = rg (rk R_AUX2)
      & regs_ok rg'].
Proof.
move=> Hc Hb Hx Hok HA Hm HAnc Hgap Hnoal HNCws Hcid HB HB14 Hreg Hregnc HAreg.
have Hb' := Hb. rewrite rp_init_split in Hb'.
move: Hb' => /blk_cat [Hbp Hbl].
have [_ Hb1] := blk_cons Hbp.
have [_ Hb2] := blk_cons Hb1.
have [_ Hb3] := blk_cons Hb2.
move: Hb3 => /blk_cat [Hbld Hbr].
set p := n.+3 + size (rp_load (rp_blocks t) R_ARG R_ONE).
have [_ Hr1] := blk_cons Hbr.
have [_ Hr2] := blk_cons Hr1.
have [_ Hr3] := blk_cons Hr2.
have [_ Hr4] := blk_cons Hr3.
have [_ Hr5] := blk_cons Hr4.
have [_ Hr6] := blk_cons Hr5.
have [_ Hr7] := blk_cons Hr6.
have [_ Hr8] := blk_cons Hr7.
have [_ Hr9] := blk_cons Hr8.
have Eend : n + size (rp_init L t cid A j) = p.+4.+4.+2.
{ rewrite rp_init_split /init_pre !size_cat /p /=. lia. }
have Elab : n + size (init_pre cid A j) = p.+4.+4.+1.
{ rewrite /init_pre !size_cat /p /=. lia. }
rewrite Elab in Hbl.
rewrite Eend in Hx *.
have HA15 : A < 2 ^ imm_size mt by apply: imm_small_lt.
set rg1 := setm rg (rk R_SP) (Atom (pcw A) Other).
have S1 : step_me (NC := NC) (S m rg n lv cid) (S m rg1 n.+1 lv cid) None.
{ rewrite /rg1 -(swcast_small HA15). exact: step_const_blk Hc Hbp (blk_nxt Hb1 erefl) Hok. }
have Hok1 : regs_ok rg1 := regs_ok_setm _ _ Hok.
have Hs1 : rg1 (rk R_SP) = Some (Atom (pcw A) Other).
{ rewrite /rg1 setmE (eqxx (rk R_SP)). exact: erefl. }
have S2 := step_load_blk lv Hc Hb1 (blk_nxt Hb2 erefl) Hok1 Hs1 Hm.
rewrite /= (setm_id Hm) in S2.
set rg2 := setm rg1 (rk R_AUX1) (Atom 0%w Other).
have Hok2 : regs_ok rg2 := regs_ok_setm _ _ Hok1.
have Ha2 : rg2 (rk R_AUX1) = Some (Atom 0%w Other).
{ rewrite /rg2 setmE (eqxx (rk R_AUX1)). exact: erefl. }
have S3 := step_bnz_fall_blk lv Hc Hb2 (blk_nxt Hbld (size_rp_load_pos _ _ _)) Hok2 Ha2.
have [rg4 [S4 Hc4 Hk4 Hok4]] :=
  run_load NC Hbound Hsmall lv Hc Hbld (blk_nxt Hbr erefl) Hok2
    (fun E => match E with end) (lt14_32 HB14).
rewrite -/p in S4.
have Hsp4 : rg4 (rk R_SP) = Some (Atom (pcw A) Other).
{ rewrite Hk4; [|exact: rk_neq|exact: rk_neq].
  rewrite /rg2 setmE rk_neq; last by []. exact: Hs1. }
have [o17 Ho17] : exists a, rg4 (wk 17) = Some a := Hok4 17 erefl.
have S5 := step_movs_blk (r1 := inl R_ARG) (r2 := inr R_SC_ARG1) lv Hc Hbr (blk_nxt Hr1 erefl)
             Hok4 Hc4 (ex_intro _ o17 Ho17).
rewrite /= in S5.
set rg5 := setm (setm rg4 (rk R_ARG) (Atom (pcw (rp_blocks t)) Other))
                (wk 17) (Atom (pcw (rp_blocks t)) Other).
have Hok5 : regs_ok rg5 := regs_ok_setm _ _ (regs_ok_setm _ _ Hok4).
have Hlp : code_label_pos cde pc0 alloc_label (pc0 + p.+1) = alloc_label.
{ by rewrite /code_label_pos Hnoal eqxx. }
have Hal15 : alloc_label < 2 ^ imm_size mt by rewrite imm_size_mt /alloc_label ltn_exp2l.
have [Hj6 _] := blk_cons Hr1.
have [i7 [tg7 [Hn7 Hcol7]]] : nxt cde p.+2 cid := blk_nxt Hr2 erefl.
have S6 : step_me (NC := NC) (S m rg5 p.+1 lv cid)
            (@Symbolic.State mt lrc_tags unit m
               (setm rg5 (wk 4) (Atom (pcw (pc0 + p.+2)) InternalJump))
               (Atom (pcw alloc_label) (Level lv cid)) tt) None.
{ apply: (me_step_jal_int NC Hbound lv Hc Hj6 erefl erefl Hn7 Hcol7 Hlp Hal15 _ Hok5).
  by rewrite Hgap. }
set rg6 := setm rg5 (wk 4) (Atom (pcw (pc0 + p.+2)) InternalJump).
have Hok6 : regs_ok rg6 := regs_ok_setm _ _ Hok5.
have [Hc7 _] := blk_cons Hr2.
have [[v7 t7] [Hv7 /= Ht7 _]] := me_fetch Hbound Hc Hc7.
subst t7.
have Hra6 : rg6 (wk 4) = Some (Atom (pcw (pc0 + p.+2)) InternalJump).
{ rewrite /rg6 setmE (eqxx (wk 4)). exact: erefl. }
have Ha17 : rg6 (wk 17) = Some (Atom (pcw (rp_blocks t)) Other).
{ rewrite /rg6 setmE (wk_eq (erefl : 17 < 20) (erefl : 4 < 20)) /=.
  rewrite /rg5 setmE (eqxx (wk 17)). exact: erefl. }
have [a16 H16] : exists a, rg6 (wk 16) = Some a := Hok6 16 erefl.
have [rc6 Hrc6] : exists a, rg6 (wk 1) = Some a := Hok6 1 erefl.
have Hlen0 : 0 < rp_blocks t by rewrite /rp_blocks addn2.
have Hlen1 : rp_blocks t + 1 <= 2 ^ (word_size mt - NC).
{ apply: (leq_trans _ HB). by rewrite addn1. }
have Hfit : pfilterC NC cid (addw (maxaddr NC m cid)
                                 (word.as_word (ssrint.Posz (rp_blocks t + 1)))).
{ rewrite (maxaddr_empty Hreg) addn1.
  exact: (region_key HNCws Hcid (leq_trans (ltnSn _) HB)). }
have Hal := alloc_fun_spec (st := @Symbolic.State mt lrc_tags unit m rg6
                                    (Atom (pcw alloc_label) (Level lv cid)) tt)
              (c0 := cid) (lvl := lv) (wret := pcw (pc0 + p.+2)) (wsz := pcw (rp_blocks t))
              (len := rp_blocks t) (rc := Atom v7 (def_mem_tag cid true)) (a16 := a16)
              erefl Hra6 Hv7 erefl erefl Ha17 (int_of_word_small HB14) H16 Hlen0 Hlen1 Hcid Hfit.
rewrite (maxaddr_empty Hreg) in Hal.
have S7 := me_step_syscall Hgap Hrc6 Hal.
set m7 := unionm m (mkfmap (blkseq NC cid (rp_blocks t))).
set rg7 := setm rg6 (wk 16) (Atom (ctrlw NC cid) Other).
have Hc7m : code_in cde pc0 m7 := code_in_unionm _ Hc.
have Hok7 : regs_ok rg7 := regs_ok_setm _ _ Hok6.
have H16c : rg7 (wk 16) = Some (Atom (ctrlw NC cid) Other).
{ rewrite /rg7 setmE (eqxx (wk 16)). exact: erefl. }
have [oa1 Hoa1] : exists a, rg7 (rk R_AUX1) = Some a := regs_ok_rk R_AUX1 Hok7.
have S8 := step_movs_blk (r1 := inr R_SC_RET) (r2 := inl R_AUX1) lv Hc7m Hr2 (blk_nxt Hr3 erefl)
             Hok7 H16c (ex_intro _ oa1 Hoa1).
rewrite /= in S8.
set rg8 := setm (setm rg7 (wk 16) (Atom (ctrlw NC cid) Other))
                (rk R_AUX1) (Atom (ctrlw NC cid) Other).
have Hok8 : regs_ok rg8 := regs_ok_setm _ _ (regs_ok_setm _ _ Hok7).
have Ha8 : rg8 (rk R_AUX1) = Some (Atom (ctrlw NC cid) Other).
{ rewrite /rg8 setmE (eqxx (rk R_AUX1)). exact: erefl. }
have Hsp8 : rg8 (rk R_SP) = Some (Atom (pcw A) Other).
{ have E1 : (rk R_SP == rk R_AUX1) = false by apply: rk_neq.
  have E2 : (rk R_SP == wk 16) = false := wk_eq (erefl : 5 < 20) (erefl : 16 < 20).
  have E3 : (rk R_SP == wk 4) = false := wk_eq (erefl : 5 < 20) (erefl : 4 < 20).
  have E4 : (rk R_SP == wk 17) = false := wk_eq (erefl : 5 < 20) (erefl : 17 < 20).
  have E5 : (rk R_SP == rk R_ARG) = false by apply: rk_neq.
  rewrite /rg8 setmE E1 setmE E2 /rg7 setmE E2 /rg6 setmE E3 /rg5 setmE E4 setmE E5.
  exact: Hsp4. }
have HmA7 : m7 (pcw A) = Some (Atom 0%w (MTag Other cid e false)).
{ by rewrite /m7 unionmE Hm. }
have S9 := step_store_blk lv Hc7m Hr3 (blk_nxt Hr4 erefl) Hok8 Hsp8 Ha8 HmA7.
set m9 := setm m7 (pcw A) (Atom (ctrlw NC cid) (MTag Other cid e false)).
set rg9 := setm rg8 (rk R_AUX1) (Atom (ctrlw NC cid) (if is_address Other then Invalidated else Other)).
have Hc9 : code_in cde pc0 m9 := code_in_setm _ Hc7m HAnc.
have Hok9 : regs_ok rg9 := regs_ok_setm _ _ Hok8.
have Ha9 : rg9 (rk R_AUX1) = Some (Atom (ctrlw NC cid) Other).
{ rewrite /rg9 setmE (eqxx (rk R_AUX1)). exact: erefl. }
have H2i : 2 < 2 ^ imm_size mt by rewrite imm_size_mt -[X in X < _](expn1 2) ltn_exp2l.
have H1i : 1 < 2 ^ imm_size mt by rewrite imm_size_mt -[X in X < _](expn0 2) ltn_exp2l.
set rg10 := setm rg9 (rk R_ARG) (Atom (pcw 2) Other).
have S10 : step_me (NC := NC) (S m9 rg9 p.+4 lv cid) (S m9 rg10 p.+4.+1 lv cid) None.
{ rewrite /rg10 -(swcast_small H2i). exact: step_const_blk Hc9 Hr4 (blk_nxt Hr5 erefl) Hok9. }
have Hok10 : regs_ok rg10 := regs_ok_setm _ _ Hok9.
have Ha10 : rg10 (rk R_AUX1) = Some (Atom (ctrlw NC cid) Other).
{ rewrite /rg10 setmE rk_neq; last by []. exact: Ha9. }
have Hg10 : rg10 (rk R_ARG) = Some (Atom (pcw 2) Other).
{ rewrite /rg10 setmE (eqxx (rk R_ARG)). exact: erefl. }
have S11 := step_binop_blk NC Hbound lv Hc9 Hr5 (blk_nxt Hr6 erefl) Hok10 Ha10 Hg10.
set rg11 := setm rg10 (rk R_ARG)
              (Atom (binop_denote (binop_trans Add) (ctrlw NC cid) (pcw 2)) Other).
have Hok11 : regs_ok rg11 := regs_ok_setm _ _ Hok10.
set rg12 := setm rg11 (rk R_ONE) (Atom (pcw 1) Other).
have S12 : step_me (NC := NC) (S m9 rg11 p.+4.+2 lv cid) (S m9 rg12 p.+4.+3 lv cid) None.
{ rewrite /rg12 -(swcast_small H1i). exact: step_const_blk Hc9 Hr6 (blk_nxt Hr7 erefl) Hok11. }
have Hok12 : regs_ok rg12 := regs_ok_setm _ _ Hok11.
have Ha12 : rg12 (rk R_AUX1) = Some (Atom (ctrlw NC cid) Other).
{ rewrite /rg12 setmE rk_neq; last by [].
  rewrite /rg11 setmE rk_neq; last by []. exact: Ha10. }
have Ho12 : rg12 (rk R_ONE) = Some (Atom (pcw 1) Other).
{ rewrite /rg12 setmE (eqxx (rk R_ONE)). exact: erefl. }
have S13 := step_binop_blk NC Hbound lv Hc9 Hr7 (blk_nxt Hr8 erefl) Hok12 Ha12 Ho12.
set rg13 := setm rg12 (rk R_SP)
              (Atom (binop_denote (binop_trans Add) (ctrlw NC cid) (pcw 1)) Other).
have Hok13 : regs_ok rg13 := regs_ok_setm _ _ Hok12.
have Hs13 : rg13 (rk R_SP) = Some (Atom (addw (ctrlw NC cid) (pcw 1)) Other).
{ rewrite /rg13 setmE (eqxx (rk R_SP)). exact: erefl. }
have Hg13 : rg13 (rk R_ARG) = Some (Atom (addw (ctrlw NC cid) (pcw 2)) Other).
{ rewrite /rg13 setmE rk_neq; last by [].
  rewrite /rg12 setmE rk_neq; last by [].
  rewrite /rg11 setmE (eqxx (rk R_ARG)). exact: erefl. }
have Ectl1 : addw (ctrlw NC cid) (pcw 1) = addw (rpre NC cid) (pcw 2) :> mword mt :=
  esym (etrans (f_equal (addw (rpre NC cid)) (esym (pcw_add 1 1))) (addwA _ _ _)).
have HB1 : 1 < rp_blocks t by rewrite /rp_blocks addn2.
have Hreg1 : pfilterC NC cid (addw (ctrlw NC cid) (pcw 1)).
{ rewrite Ectl1. exact: (region_key HNCws Hcid (leq_trans _ HB)). }
have Hm9c : m9 (addw (ctrlw NC cid) (pcw 1))
            = Some (Atom (word.as_word (ssrint.Posz 0) : mword mt) (def_mem_tag cid false)).
{ rewrite /m9 setmE.
  have -> : (addw (ctrlw NC cid) (pcw 1) == pcw A) = false.
  { apply/eqP => E. move: HAreg. by rewrite -E Hreg1. }
  rewrite /m7 unionmE (Hreg _ Hreg1) /=.
  rewrite Ectl1. exact: blkseq_get HB1. }
have S14 := step_store_blk lv Hc9 Hr8 (blk_nxt Hbl erefl) Hok13 Hs13 Hg13 Hm9c.
set m14 := setm m9 (addw (ctrlw NC cid) (pcw 1))
             (Atom (addw (ctrlw NC cid) (pcw 2)) (MTag Other cid None false)).
have Hc14 : code_in cde pc0 m14 := code_in_setm _ Hc9 (Hregnc _ Hreg1).
set rg14 := setm rg13 (rk R_ARG)
              (Atom (addw (ctrlw NC cid) (pcw 2)) (if is_address Other then Invalidated else Other)).
have Hok14 : regs_ok rg14 := regs_ok_setm _ _ Hok13.
have S15 := step_label_blk lv Hc14 Hbl Hx Hok14.
exists rg14. split.
- apply: (msil_step S1). apply: (msil_step S2). apply: (msil_step S3).
  apply: (msil_trans S4). apply: (msil_step S5). apply: (msil_step S6).
  apply: (msil_step S7). apply: (msil_step S8). apply: (msil_step S9).
  apply: (msil_step S10). apply: (msil_step S11). apply: (msil_step S12).
  apply: (msil_step S13). apply: (msil_step S14). exact: msil_one S15.
- have N1 : (rk R_AUX1 == rk R_ARG) = false by apply: rk_neq.
  have N2 : (rk R_AUX1 == rk R_SP) = false by apply: rk_neq.
  have N3 : (rk R_AUX1 == rk R_ONE) = false by apply: rk_neq.
  exact: (etrans (@setm_ne' _ _ _ _ _ _ N1) (etrans (@setm_ne' _ _ _ _ _ _ N2) (etrans (@setm_ne' _ _ _ _ _ _ N3)
           (etrans (@setm_ne' _ _ _ _ _ _ N1) (etrans (@setm_ne' _ _ _ _ _ _ N1) Ha9))))).
- have M1 : (rk R_AUX2 == rk R_ARG) = false by apply: rk_neq.
  have M2 : (rk R_AUX2 == rk R_SP) = false by apply: rk_neq.
  have M3 : (rk R_AUX2 == rk R_ONE) = false by apply: rk_neq.
  have M4 : (rk R_AUX2 == rk R_AUX1) = false by apply: rk_neq.
  have M16 : (rk R_AUX2 == wk 16) = false := wk_eq (erefl : 3 < 20) (erefl : 16 < 20).
  have M17 : (rk R_AUX2 == wk 17) = false := wk_eq (erefl : 3 < 20) (erefl : 17 < 20).
  have M5 : (rk R_AUX2 == wk 4) = false := wk_eq (erefl : 3 < 20) (erefl : 4 < 20).
  have H4' : rg4 (rk R_AUX2) = rg2 (rk R_AUX2) := Hk4 _ M1 M3.
  exact: (etrans (@setm_ne' _ _ _ _ _ _ M1) (etrans (@setm_ne' _ _ _ _ _ _ M2) (etrans (@setm_ne' _ _ _ _ _ _ M3)
           (etrans (@setm_ne' _ _ _ _ _ _ M1) (etrans (@setm_ne' _ _ _ _ _ _ M1)
           (etrans (@setm_ne' _ _ _ _ _ _ M4) (etrans (@setm_ne' _ _ _ _ _ _ M4) (etrans (@setm_ne' _ _ _ _ _ _ M16)
           (etrans (@setm_ne' _ _ _ _ _ _ M16) (etrans (@setm_ne' _ _ _ _ _ _ M5) (etrans (@setm_ne' _ _ _ _ _ _ M17)
           (etrans (@setm_ne' _ _ _ _ _ _ M1) (etrans H4'
           (etrans (@setm_ne' _ _ _ _ _ _ M4) (@setm_ne' _ _ _ _ _ _ M2))))))))))))))).
- exact: Hok14.
Qed.

End Run.
