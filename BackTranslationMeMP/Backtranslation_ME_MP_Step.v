Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import CompCert.Events.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
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
Require Import MicroPolicies.Recomposition.TraceWF.
Require Import MicroPolicies.Recomposition.TraceBracket.
Require Import T2M.MMemBase.
Require Import T2M.MPos.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Notation mstate := (@Symbolic.state mt lrc_tags unit).
Notation rk r := (@word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r)).
Notation pcw n := (@word_of_nat (word_size mt) n).

Lemma setm_id (T : ordType) (S : Type) (m : {fmap T -> S}) k v :
  m k = Some v -> setm m k v = m.
Proof.
move=> Hk. apply/eq_fmap => k'. rewrite setmE.
case: eqP => [->|//]. by rewrite Hk.
Qed.

Definition rkeys : seq nat := [:: 0; 1; 2; 3; 4; 5; 6; 7; 16; 17; 18; 19].

Notation rmap := {fmap reg mt -> atom (mword mt) (tag_type lrc_tags R)}.

Definition regs_ok (rg : rmap) : Prop :=
  forall k, k \in rkeys -> exists a, rg (@word_of_nat (reg_field_size mt) k) = Some a.

Lemma regs_ok_setm rg k a : regs_ok rg -> regs_ok (setm rg k a).
Proof.
move=> H j Hj. rewrite setmE. case: eqP => _; first by eexists.
exact: H.
Qed.

Lemma reg_clear_aux_some (l : seq nat) (rg : rmap) top :
  (forall k, k \in l -> exists a, rg (@word_of_nat (reg_field_size mt) k) = Some a) ->
  exists h, reg_clear_list_aux l rg top = Some h.
Proof.
elim: l top => [|e l IH] top Hl /=; first by eexists.
have [a Ha] := Hl e (mem_head _ _).
have -> : rg (word.as_word (ssrint.Posz e)) = Some a := Ha.
have [h Hh] := IH (taga a) (fun k Hk => Hl k ltac:(by rewrite inE Hk orbT)).
rewrite /= Hh /=. by eexists.
Qed.

Lemma reg_clear_aux_shape (e : nat) (l : seq nat) (rg : rmap) top h :
  reg_clear_list_aux (e :: l) rg top = Some h ->
  exists a h', [/\ rg (@word_of_nat (reg_field_size mt) e) = Some a,
                   reg_clear_list_aux l rg (taga a) = Some h'
                 & h = HSeqCons top h'].
Proof.
rewrite /=.
case Ea: (rg (word.as_word (ssrint.Posz e))) => [a|] //=.
case Eh: (reg_clear_list_aux l rg (taga a)) => [h'|] //= [<-].
by exists a, h'.
Qed.

Lemma regs_ok_clear rg top :
  regs_ok rg -> exists h, reg_clear_list rg top = Some h.
Proof.
move=> H. apply: reg_clear_aux_some => k Hk. apply: H.
have Hsub : all (fun k => k \in rkeys) reg_list := erefl.
exact: (allP Hsub) k Hk.
Qed.

Lemma ndsu_invalidate (st : mstate) (t : value_tag) (l : seq nat) :
  (forall k, k \in l -> exists a, regs st (@word_of_nat (reg_field_size mt) k) = Some a) ->
  exists st',
    [/\ next_state_do_updates st (make_hseq (size l) t)
          [seq RegRead (word.as_word (ssrint.Posz k)) | k <- l] = Some st',
        [/\ mem st' = mem st, pc st' = pc st & internal st' = internal st],
        (forall k, k \notin [seq @word_of_nat (reg_field_size mt) j | j <- l] ->
                   regs st' k = regs st k)
      & (forall k, regs st k <> None -> regs st' k <> None)].
Proof.
elim: l st => [|e l IH] st Hl /=.
- exists st. split; [exact: erefl | by split | by [] | by []].
- have [a Ha] := Hl e (mem_head _ _).
  set st1 := @Symbolic.State mt lrc_tags unit (mem st)
               (setm (regs st) (word.as_word (ssrint.Posz e)) (Atom (vala a) t))
               (pc st) (internal st).
  have Hl1 : forall k, k \in l ->
      exists a, regs st1 (@word_of_nat (reg_field_size mt) k) = Some a.
  { move=> k Hk. rewrite /st1 /= setmE. case: eqP => _; first by eexists.
    apply: Hl. by rewrite inE Hk orbT. }
  have [st' [Hu [Hm Hp Hi] Hr Hd]] := IH st1 Hl1.
  exists st'. split.
  + have -> : regs st (word.as_word (ssrint.Posz e)) = Some a := Ha.
    rewrite /= /updm.
    have -> : regs st (word.as_word (ssrint.Posz e)) = Some a := Ha.
    exact: Hu.
  + split; [by rewrite Hm | by rewrite Hp | by rewrite Hi].
  + move=> k Hk. rewrite Hr; last first.
    { apply/negP => Hin. move: Hk. by rewrite inE Hin orbT. }
    rewrite /st1 /= setmE.
    case: eqP => [Ek|] //.
    subst k. move: Hk. by rewrite /= inE eqxx.
  + move=> k Hk. apply: Hd. rewrite /st1 /= setmE.
    by case: eqP.
Qed.

Lemma swcast_small (x : nat) :
  x < 2 ^ imm_size mt ->
  @swcast (imm_size mt) (word_size mt) (@word_of_nat (imm_size mt) x) = pcw x.
Proof. move=> H. by rewrite /swcast /word_of_nat (as_wordK H). Qed.

Lemma pcw_add a b : addw (pcw a) (pcw b) = pcw (a + b).
Proof. by rewrite /word_of_nat as_word_addwD. Qed.

Definition rest_keys : seq nat := [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19].

Lemma rest_keys_lt k : k \in rest_keys -> k < 20.
Proof.
have Hall : all (fun k => k < 20) rest_keys := erefl.
exact: (allP Hall) k.
Qed.

Lemma key_notin_rest (x : nat) :
  x \notin rest_keys -> x < 20 ->
  @word_of_nat (reg_field_size mt) x
    \notin [seq @word_of_nat (reg_field_size mt) j | j <- rest_keys].
Proof.
move=> Hx Hx20. apply/mapP => -[j Hj Ej].
have Hj20 := rest_keys_lt Hj.
have E := won_inj (small_lt_reg (ltn_trans Hx20 (erefl : 20 < 32)))
                  (small_lt_reg (ltn_trans Hj20 (erefl : 20 < 32))) Ej.
subst j. by rewrite Hj in Hx.
Qed.

Lemma regkey_ne (x y : nat) :
  x <> y -> x < 20 -> y < 20 ->
  (@word_of_nat (reg_field_size mt) x == @word_of_nat (reg_field_size mt) y) = false.
Proof.
move=> Hxy Hx Hy. apply/eqP => E. apply: Hxy.
exact: (won_inj (small_lt_reg (ltn_trans Hx (erefl : 20 < 32)))
                (small_lt_reg (ltn_trans Hy (erefl : 20 < 32))) E).
Qed.

Lemma rest_ok (rg : rmap) :
  regs_ok rg ->
  forall k, k \in rest_keys -> exists a, rg (@word_of_nat (reg_field_size mt) k) = Some a.
Proof.
move=> H k Hk. apply: H.
have Hsub : all (fun k => k \in rkeys) rest_keys := erefl.
exact: (allP Hsub) k Hk.
Qed.

Notation wk k := (word.as_word (ssrint.Posz k) : reg mt).

Lemma wk_eq (a b : nat) : a < 20 -> b < 20 -> (wk a == wk b) = (a == b).
Proof.
move=> Ha Hb.
exact: (won_eqE (small_lt_reg (ltn_trans Ha (erefl : 20 < 32)))
                (small_lt_reg (ltn_trans Hb (erefl : 20 < 32)))).
Qed.

Lemma regs_ok_atoms (rg : rmap) :
  regs_ok rg ->
  exists a0 a1 a2 a3 a4 a5 a6 a7 a16 a17 a18 a19,
    [/\ [/\ rg (wk 0) = Some a0, rg (wk 1) = Some a1, rg (wk 2) = Some a2
          & rg (wk 3) = Some a3],
        [/\ rg (wk 4) = Some a4, rg (wk 5) = Some a5, rg (wk 6) = Some a6
          & rg (wk 7) = Some a7]
      & [/\ rg (wk 16) = Some a16, rg (wk 17) = Some a17, rg (wk 18) = Some a18
          & rg (wk 19) = Some a19]].
Proof.
move=> H.
have [a0 H0] := H 0 erefl. have [a1 H1] := H 1 erefl.
have [a2 H2] := H 2 erefl. have [a3 H3] := H 3 erefl.
have [a4 H4] := H 4 erefl. have [a5 H5] := H 5 erefl.
have [a6 H6] := H 6 erefl. have [a7 H7] := H 7 erefl.
have [a16 H16] := H 16 erefl. have [a17 H17] := H 17 erefl.
have [a18 H18] := H 18 erefl. have [a19 H19] := H 19 erefl.
by exists a0, a1, a2, a3, a4, a5, a6, a7, a16, a17, a18, a19.
Qed.

Lemma reg_clear_split (rg : rmap) told :
  regs_ok rg ->
  exists a1 h2,
    [/\ rg (@word_of_nat (reg_field_size mt) 1) = Some a1,
        reg_clear_list_aux rest_keys rg (taga a1) = Some h2
      & reg_clear_list rg told = Some (HSeqCons told h2)].
Proof.
move=> Hok.
have [h Hh] := regs_ok_clear told Hok.
have [a1 [h2 [Ha1 Hh2 Eh]]] := reg_clear_aux_shape Hh.
exists a1, h2. split; [exact: Ha1 | exact: Hh2 | by rewrite Hh Eh].
Qed.

Section MEStep.

Variable NC : nat.
Variable cde : @Merged.code mt.
Variable pc0 : nat.

Hypothesis Hbound : pc0 + size cde < 2 ^ word_size mt.

Definition code_in (m : {fmap mword mt -> matom}) : Prop :=
  forall w v, encode_code cde pc0 w = Some v -> m w = Some v.

Lemma me_fetch (m : {fmap mword mt -> matom}) n (i : @Merged.instr mt) tg :
  code_in m ->
  List.nth_error cde n = Some (i, tg) ->
  exists v : matom,
    [/\ m (pcw (pc0 + n)) = Some v, taga v = tg
      & decode_instr (vala v)
        = Some (instr_merged_to_mp i (code_label_pos cde pc0) (pc0 + n))].
Proof.
move=> Hc Hn.
have [v [Hv [Ht Hval]]] := encode_code_fetch Hbound Hn.
exists v. split.
- rewrite addnC. exact: (Hc _ _ Hv).
- exact: Ht.
- rewrite Hval /encode_instr_mp. by rewrite encodeK.
Qed.

Lemma addw_pcw_one n : addw (pcw n) onew = pcw n.+1.
Proof.
have -> : (onew : mword mt) = pcw 1 by [].
rewrite /word_of_nat as_word_addwD.
congr word.as_word. by lia.
Qed.

Lemma me_step_const (m : {fmap mword mt -> matom}) (rg : rmap)
    lv cid n (imm : imm mt) (r : register) tg i1 tg1 old rc :
  code_in m ->
  List.nth_error cde n = Some (MrConst imm r, tg) ->
  is_code tg -> color tg = cid ->
  List.nth_error cde n.+1 = Some (i1, tg1) -> color tg1 = cid ->
  rg (rk R_COM) = Some rc ->
  rg (rk r) = Some old ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (pc0 + n)) (Level lv cid)) tt)
    (@Symbolic.State mt lrc_tags unit m (setm rg (rk r) (Atom (swcast imm) Other))
                    (Atom (pcw (pc0 + n.+1)) (Level lv cid)) tt)
    None.
Proof.
move=> Hc Hn Hic Hcol Hn1 Hcol1 Hrc Hold.
have [[vv vt] [Hv /= Htv Hdec]] := me_fetch Hc Hn.
subst vt.
have [[vv1 vt1] [Hv1 /= Htv1 _]] := me_fetch Hc Hn1.
subst vt1.
case: old Hold => vo to Hold.
case: rc Hrc => vr tr Hrc.
case: tg Hn Hic Hcol Hv => vtg ctg etg [] Hn //= _ Hcol Hv.
subst ctg.
case: tg1 Hn1 Hcol1 Hv1 => vtg1 ctg1 etg1 ictg1 Hn1 /= Hcol1 Hv1.
subst ctg1.
rewrite addnS -addw_pcw_one.
rewrite /step_me.
eapply (@Symbolic.step_const mt ops lrc_tags Merged.transfer unit (table (NC := NC)) _ _ _
          m rg (pcw (pc0 + n)) (Level lv cid) vv (MTag vtg cid etg true)
          imm (rk r) vo to tt).
- exact: erefl.
- exact: Hv.
- exact: Hdec.
- exact: Hold.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite addnS -addw_pcw_one in Hv1.
  rewrite Hv1.
  rewrite /Symbolic.next_state /Symbolic.evi.
  have -> : (rcom : reg mt) = rk R_COM by [].
  rewrite Hrc /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /= eqxx /=.
  rewrite /check_belong /belong /= eqxx /=.
  rewrite /updm Hold /=.
  by [].
Qed.

Lemma me_step_label (m : {fmap mword mt -> matom}) (rg : rmap)
    lv cid n (l : nat) tg i1 tg1 rc :
  code_in m ->
  List.nth_error cde n = Some (MrLabel l, tg) ->
  is_code tg -> color tg = cid ->
  List.nth_error cde n.+1 = Some (i1, tg1) -> color tg1 = cid ->
  rg (rk R_COM) = Some rc ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (pc0 + n)) (Level lv cid)) tt)
    (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (pc0 + n.+1)) (Level lv cid)) tt)
    None.
Proof.
move=> Hc Hn Hic Hcol Hn1 Hcol1 Hrc.
have [[vv vt] [Hv /= Htv Hdec]] := me_fetch Hc Hn.
subst vt.
have [[vv1 vt1] [Hv1 /= Htv1 _]] := me_fetch Hc Hn1.
subst vt1.
case: rc Hrc => vr tr Hrc.
case: tg Hn Hic Hcol Hv => vtg ctg etg [] Hn //= _ Hcol Hv.
subst ctg.
case: tg1 Hn1 Hcol1 Hv1 => vtg1 ctg1 etg1 ictg1 Hn1 /= Hcol1 Hv1.
subst ctg1.
rewrite addnS -addw_pcw_one.
rewrite /step_me.
eapply (@Symbolic.step_nop mt ops lrc_tags Merged.transfer unit (table (NC := NC)) _ _ _
          m rg (pcw (pc0 + n)) (Level lv cid) vv (MTag vtg cid etg true) tt).
- exact: erefl.
- exact: Hv.
- exact: Hdec.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite addnS -addw_pcw_one in Hv1.
  rewrite Hv1.
  rewrite /Symbolic.next_state /Symbolic.evi.
  have -> : (rcom : reg mt) = rk R_COM by [].
  rewrite Hrc /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /= eqxx /=.
  rewrite /check_belong /belong /= eqxx /=.
  by [].
Qed.

Notation rkb x := (@word_of_nat (reg_field_size mt) (to_nat_bis x)).

Lemma me_step_mov (m : {fmap mword mt -> matom}) (rg : rmap)
    lv cid n (r1 r2 : register + sys_reg) tg i1 tg1 rc w1 t1 old :
  code_in m ->
  List.nth_error cde n = Some (MrMov r1 r2, tg) ->
  is_code tg -> color tg = cid ->
  List.nth_error cde n.+1 = Some (i1, tg1) -> color tg1 = cid ->
  rg (rk R_COM) = Some rc ->
  rg (rkb r1) = Some (Atom w1 t1) ->
  rg (rkb r2) = Some old ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (pc0 + n)) (Level lv cid)) tt)
    (@Symbolic.State mt lrc_tags unit m
       (setm (setm rg (rkb r1) (Atom w1 (moved_tag t1)))
             (rkb r2) (Atom w1 t1))
       (Atom (pcw (pc0 + n.+1)) (Level lv cid)) tt)
    None.
Proof.
move=> Hc Hn Hic Hcol Hn1 Hcol1 Hrc H1 Hold.
have [[vv vt] [Hv /= Htv Hdec]] := me_fetch Hc Hn.
subst vt.
have [[vv1 vt1] [Hv1 /= Htv1 _]] := me_fetch Hc Hn1.
subst vt1.
case: old Hold => vo to Hold.
case: rc Hrc => vr tr Hrc.
case: tg Hn Hic Hcol Hv => vtg ctg etg [] Hn //= _ Hcol Hv.
subst ctg.
case: tg1 Hn1 Hcol1 Hv1 => vtg1 ctg1 etg1 ictg1 Hn1 /= Hcol1 Hv1.
subst ctg1.
rewrite addnS -addw_pcw_one.
rewrite /step_me.
eapply (@Symbolic.step_mov mt ops lrc_tags Merged.transfer unit (table (NC := NC)) _ _ _
          m rg (pcw (pc0 + n)) (Level lv cid) vv (MTag vtg cid etg true)
          (rkb r1) w1 t1 (rkb r2) vo to tt).
- exact: erefl.
- exact: Hv.
- exact: Hdec.
- exact: H1.
- exact: Hold.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite addnS -addw_pcw_one in Hv1.
  rewrite Hv1.
  rewrite /Symbolic.next_state /Symbolic.evi.
  have -> : (rcom : reg mt) = rk R_COM by [].
  rewrite Hrc /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /= eqxx /=.
  rewrite /check_belong /belong /= eqxx /=.
  rewrite /updm H1 /= setmE.
  case: (rkb r2 == rkb r1) => /=; last rewrite Hold /=; by [].
Qed.

Lemma me_step_binop (m : {fmap mword mt -> matom}) (rg : rmap)
    lv cid n b (r1 r2 r3 : register) tg i1 tg1 rc w1 w2 old :
  code_in m ->
  List.nth_error cde n = Some (MrBinop b r1 r2 r3, tg) ->
  is_code tg -> color tg = cid ->
  List.nth_error cde n.+1 = Some (i1, tg1) -> color tg1 = cid ->
  rg (rk R_COM) = Some rc ->
  rg (rk r1) = Some (Atom w1 Other) ->
  rg (rk r2) = Some (Atom w2 Other) ->
  rg (rk r3) = Some old ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (pc0 + n)) (Level lv cid)) tt)
    (@Symbolic.State mt lrc_tags unit m
       (setm rg (rk r3) (Atom (binop_denote (binop_trans b) w1 w2) Other))
       (Atom (pcw (pc0 + n.+1)) (Level lv cid)) tt)
    None.
Proof.
move=> Hc Hn Hic Hcol Hn1 Hcol1 Hrc H1 H2 Hold.
have [[vv vt] [Hv /= Htv Hdec]] := me_fetch Hc Hn.
subst vt.
have [[vv1 vt1] [Hv1 /= Htv1 _]] := me_fetch Hc Hn1.
subst vt1.
case: old Hold => vo to Hold.
case: rc Hrc => vr tr Hrc.
case: tg Hn Hic Hcol Hv => vtg ctg etg [] Hn //= _ Hcol Hv.
subst ctg.
case: tg1 Hn1 Hcol1 Hv1 => vtg1 ctg1 etg1 ictg1 Hn1 /= Hcol1 Hv1.
subst ctg1.
rewrite addnS -addw_pcw_one.
rewrite /step_me.
eapply (@Symbolic.step_binop mt ops lrc_tags Merged.transfer unit (table (NC := NC)) _ _ _
          m rg (pcw (pc0 + n)) (Level lv cid) vv (MTag vtg cid etg true)
          (binop_trans b) (rk r1) (rk r2) (rk r3) w1 w2 Other Other vo to tt).
- exact: erefl.
- exact: Hv.
- exact: Hdec.
- exact: H1.
- exact: H2.
- exact: Hold.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite addnS -addw_pcw_one in Hv1.
  rewrite Hv1.
  rewrite /Symbolic.next_state /Symbolic.evi.
  have -> : (rcom : reg mt) = rk R_COM by [].
  rewrite Hrc /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /= eqxx /=.
  rewrite /check_belong /belong /= eqxx /=.
  rewrite /updm H1 /= (setm_id H1) H2 /= (setm_id H2) Hold /=.
  by [].
Qed.

Lemma me_step_load (m : {fmap mword mt -> matom}) (rg : rmap)
    lv cid n (r1 r2 : register) tg i1 tg1 rc w1 w2 vt2 e2 old :
  code_in m ->
  List.nth_error cde n = Some (MrLoad r1 r2, tg) ->
  is_code tg -> color tg = cid ->
  List.nth_error cde n.+1 = Some (i1, tg1) -> color tg1 = cid ->
  rg (rk R_COM) = Some rc ->
  rg (rk r1) = Some (Atom w1 Other) ->
  m w1 = Some (Atom w2 (MTag vt2 cid e2 false)) ->
  rg (rk r2) = Some old ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (pc0 + n)) (Level lv cid)) tt)
    (@Symbolic.State mt lrc_tags unit
       (setm m w1 (Atom w2 (MTag (moved_tag vt2) cid e2 false)))
       (setm rg (rk r2) (Atom w2 vt2))
       (Atom (pcw (pc0 + n.+1)) (Level lv cid)) tt)
    None.
Proof.
move=> Hc Hn Hic Hcol Hn1 Hcol1 Hrc H1 Hm1 Hold.
have [[vv vt] [Hv /= Htv Hdec]] := me_fetch Hc Hn.
subst vt.
have [[vv1 vt1] [Hv1 /= Htv1 _]] := me_fetch Hc Hn1.
subst vt1.
case: old Hold => vo to Hold.
case: rc Hrc => vr tr Hrc.
case: tg Hn Hic Hcol Hv => vtg ctg etg [] Hn //= _ Hcol Hv.
subst ctg.
case: tg1 Hn1 Hcol1 Hv1 => vtg1 ctg1 etg1 ictg1 Hn1 /= Hcol1 Hv1.
subst ctg1.
rewrite addnS -addw_pcw_one.
rewrite /step_me.
eapply (@Symbolic.step_load mt ops lrc_tags Merged.transfer unit (table (NC := NC)) _ _ _
          m rg (pcw (pc0 + n)) (Level lv cid) vv (MTag vtg cid etg true)
          (rk r1) (rk r2) w1 w2 Other (MTag vt2 cid e2 false) vo to tt).
- exact: erefl.
- exact: Hv.
- exact: Hdec.
- exact: H1.
- exact: Hm1.
- exact: Hold.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite addnS -addw_pcw_one in Hv1.
  rewrite Hv1.
  rewrite /Symbolic.next_state /Symbolic.evi.
  have -> : (rcom : reg mt) = rk R_COM by [].
  rewrite Hrc /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /= eqxx /=.
  rewrite /check_belong /belong /= eqxx /=.
  rewrite /updm H1 /= (setm_id H1) Hm1 /= Hold /=.
  by [].
Qed.

Lemma me_step_store (m : {fmap mword mt -> matom}) (rg : rmap)
    lv cid n (r1 r2 : register) tg i1 tg1 rc w1 w2 t2 wo vto eo :
  code_in m ->
  List.nth_error cde n = Some (MrStore r1 r2, tg) ->
  is_code tg -> color tg = cid ->
  List.nth_error cde n.+1 = Some (i1, tg1) -> color tg1 = cid ->
  rg (rk R_COM) = Some rc ->
  rg (rk r1) = Some (Atom w1 Other) ->
  rg (rk r2) = Some (Atom w2 t2) ->
  m w1 = Some (Atom wo (MTag vto cid eo false)) ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (pc0 + n)) (Level lv cid)) tt)
    (@Symbolic.State mt lrc_tags unit
       (setm m w1 (Atom w2 (MTag t2 cid eo false)))
       (setm rg (rk r2) (Atom w2 (moved_tag t2)))
       (Atom (pcw (pc0 + n.+1)) (Level lv cid)) tt)
    None.
Proof.
move=> Hc Hn Hic Hcol Hn1 Hcol1 Hrc H1 H2 Hm1.
have [[vv vt] [Hv /= Htv Hdec]] := me_fetch Hc Hn.
subst vt.
have [[vv1 vt1] [Hv1 /= Htv1 _]] := me_fetch Hc Hn1.
subst vt1.
case: rc Hrc => vr tr Hrc.
case: tg Hn Hic Hcol Hv => vtg ctg etg [] Hn //= _ Hcol Hv.
subst ctg.
case: tg1 Hn1 Hcol1 Hv1 => vtg1 ctg1 etg1 ictg1 Hn1 /= Hcol1 Hv1.
subst ctg1.
rewrite addnS -addw_pcw_one.
rewrite /step_me.
eapply (@Symbolic.step_store mt ops lrc_tags Merged.transfer unit (table (NC := NC)) _ _ _
          m rg (pcw (pc0 + n)) vv (rk r1) (rk r2) w1 w2 (Level lv cid)
          (MTag vtg cid etg true) Other t2 wo (MTag vto cid eo false) tt).
- exact: erefl.
- exact: Hv.
- exact: Hdec.
- exact: H1.
- exact: H2.
- exact: Hm1.
- rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /=.
  rewrite addnS -addw_pcw_one in Hv1.
  rewrite Hv1.
  rewrite /Symbolic.next_state /Symbolic.evi.
  have -> : (rcom : reg mt) = rk R_COM by [].
  rewrite Hrc /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /= eqxx /=.
  rewrite /check_belong /belong /= eqxx /=.
  rewrite /updm H1 /= (setm_id H1) H2 /= Hm1 /=.
  by [].
Qed.

Hypothesis Hsmall : pc0 + size cde < alloc_label.

Lemma imm_lt x : x <= pc0 + size cde -> x < 2 ^ imm_size mt.
Proof.
move=> Hx. rewrite imm_size_mt.
apply: (leq_ltn_trans Hx). apply: (ltn_trans Hsmall).
by rewrite /alloc_label ltn_exp2l.
Qed.

Lemma me_step_bnz_fall (m : {fmap mword mt -> matom}) (rg : rmap)
    lv cid n (r : register) l tg i1 tg1 rc :
  code_in m ->
  List.nth_error cde n = Some (MrBnz r l, tg) ->
  is_code tg -> color tg = cid ->
  List.nth_error cde n.+1 = Some (i1, tg1) -> color tg1 = cid ->
  rg (rk R_COM) = Some rc ->
  rg (rk r) = Some (Atom 0%w Other) ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (pc0 + n)) (Level lv cid)) tt)
    (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (pc0 + n.+1)) (Level lv cid)) tt)
    None.
Proof.
move=> Hc Hn Hic Hcol Hn1 Hcol1 Hrc H1.
have [[vv vt] [Hv /= Htv Hdec]] := me_fetch Hc Hn.
subst vt.
have [[vv1 vt1] [Hv1 /= Htv1 _]] := me_fetch Hc Hn1.
subst vt1.
case: rc Hrc => vr tr Hrc.
case: tg Hn Hic Hcol Hv => vtg ctg etg [] Hn //= _ Hcol Hv.
subst ctg.
case: tg1 Hn1 Hcol1 Hv1 => vtg1 ctg1 etg1 ictg1 Hn1 /= Hcol1 Hv1.
subst ctg1.
rewrite addnS -addw_pcw_one.
rewrite /step_me.
eapply (@Symbolic.step_bnz mt ops lrc_tags Merged.transfer unit (table (NC := NC)) _ _ _
          m rg (pcw (pc0 + n)) vv (rk r) _ 0%w (Level lv cid) (MTag vtg cid etg true)
          Other tt).
- exact: erefl.
- exact: Hv.
- exact: Hdec.
- exact: H1.
- rewrite /Symbolic.next_state_updates_and_pc /= eqxx.
  rewrite addnS -addw_pcw_one in Hv1.
  rewrite Hv1.
  rewrite /Symbolic.next_state /Symbolic.evi.
  have -> : (rcom : reg mt) = rk R_COM by [].
  rewrite Hrc /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /= eqxx /=.
  rewrite /check_belong /belong /= eqxx /=.
  rewrite /updm H1 /= (setm_id H1).
  by [].
Qed.

Lemma me_step_bnz_taken (m : {fmap mword mt -> matom}) (rg : rmap)
    lv cid n (r : register) l tg k ik tgk rc w :
  code_in m ->
  List.nth_error cde n = Some (MrBnz r l, tg) ->
  is_code tg -> color tg = cid ->
  findopt (is_label_def l) cde = Some k -> n < k ->
  List.nth_error cde k = Some (ik, tgk) -> color tgk = cid ->
  rg (rk R_COM) = Some rc ->
  rg (rk r) = Some (Atom w Other) -> w != 0%w ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (pc0 + n)) (Level lv cid)) tt)
    (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (pc0 + k)) (Level lv cid)) tt)
    None.
Proof.
move=> Hc Hn Hic Hcol Hk Hnk Hnk' Hcolk Hrc H1 Hw.
have [[vv vt] [Hv /= Htv Hdec]] := me_fetch Hc Hn.
subst vt.
have [[vvk vtk] [Hvk /= Htvk _]] := me_fetch Hc Hnk'.
subst vtk.
have Hksz : k < size cde := nth_error_size Hnk'.
case: rc Hrc => vr tr Hrc.
case: tg Hn Hic Hcol Hv => vtg ctg etg [] Hn //= _ Hcol Hv.
subst ctg.
case: tgk Hnk' Hcolk Hvk => vtgk ctgk etgk ictgk Hnk' /= Hcolk Hvk.
subst ctgk.
move: Hdec. rewrite /= /code_label_pos Hk => Hdec.
have Eoff : pc0 + k - (pc0 + n) = k - n by rewrite subnDl.
rewrite Eoff in Hdec.
have Hkn : k - n < 2 ^ imm_size mt.
{ apply: imm_lt. apply: (leq_trans (leq_subr n k)). apply: (leq_trans (ltnW Hksz)).
  exact: leq_addl. }
have Epc : addw (pcw (pc0 + n)) (@swcast (imm_size mt) (word_size mt) (@word_of_nat (imm_size mt) (k - n)))
           = pcw (pc0 + k).
{ rewrite (swcast_small Hkn) pcw_add. congr (pcw _). rewrite -addnA subnKC //. exact: ltnW. }
rewrite /step_me.
eapply (@Symbolic.step_bnz mt ops lrc_tags Merged.transfer unit (table (NC := NC)) _ _ _
          m rg (pcw (pc0 + n)) vv (rk r) _ w (Level lv cid) (MTag vtg cid etg true)
          Other tt).
- exact: erefl.
- exact: Hv.
- exact: Hdec.
- exact: H1.
- rewrite /Symbolic.next_state_updates_and_pc /= (negbTE Hw) Epc.
  rewrite Hvk.
  rewrite /Symbolic.next_state /Symbolic.evi.
  have -> : (rcom : reg mt) = rk R_COM by [].
  rewrite Hrc /=.
  rewrite /Merged.transfer /Merged.instr_rules /=.
  rewrite /LRC.instr_rules /= eqxx /=.
  rewrite /check_belong /belong /= eqxx /=.
  rewrite /updm H1 /= (setm_id H1).
  by [].
Qed.

Lemma me_step_jal_int (m : {fmap mword mt -> matom}) (rg : rmap)
    lv cid n l tg i1 tg1 tgt :
  code_in m ->
  List.nth_error cde n = Some (MrJal l, tg) ->
  is_code tg -> color tg = cid ->
  List.nth_error cde n.+1 = Some (i1, tg1) -> color tg1 = cid ->
  code_label_pos cde pc0 l (pc0 + n) = tgt ->
  tgt < 2 ^ imm_size mt ->
  match m (pcw tgt) with None => True | Some a => color (taga a) = cid end ->
  regs_ok rg ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (pc0 + n)) (Level lv cid)) tt)
    (@Symbolic.State mt lrc_tags unit m
       (setm rg (wk 4) (Atom (pcw (pc0 + n.+1)) InternalJump))
       (Atom (pcw tgt) (Level lv cid)) tt)
    None.
Proof.
move=> Hc Hn Hic Hcol Hn1 Hcol1 Hlp Htgt Htc Hok.
have [[vv vt] [Hv /= Htv Hdec]] := me_fetch Hc Hn.
subst vt.
have [[vv1 vt1] [Hv1 /= Htv1 _]] := me_fetch Hc Hn1.
subst vt1.
case: tg Hn Hic Hcol Hv => vtg ctg etg [] Hn //= _ Hcol Hv.
subst ctg.
case: tg1 Hn1 Hcol1 Hv1 => vtg1 ctg1 etg1 ictg1 Hn1 /= Hcol1 Hv1.
subst ctg1.
have [a0 [a1 [a2 [a3 [a4 [a5 [a6 [a7 [a16 [a17 [a18 [a19
       [[H0 H1 H2 H3] [H4 H5 H6 H7] [H16 H17 H18 H19]]]]]]]]]]]]]] :=
  regs_ok_atoms Hok.
case: a0 H0 => w0 t0 H0. case: a1 H1 => w1 t1 H1.
case: a2 H2 => w2 t2 H2. case: a3 H3 => w3 t3 H3.
case: a4 H4 => w4 t4 H4. case: a5 H5 => w5 t5 H5.
case: a6 H6 => w6 t6 H6. case: a7 H7 => w7 t7 H7.
case: a16 H16 => w16 t16 H16. case: a17 H17 => w17 t17 H17.
case: a18 H18 => w18 t18 H18. case: a19 H19 => w19 t19 H19.
have Hclear : reg_clear_list rg t4
  = Some [hseq t4; t1; t0; t2; t3; t5; t6; t7; t16; t17; t18; t19].
{ rewrite /reg_clear_list /=.
  by rewrite H1 /= H0 /= H2 /= H3 /= H5 /= H6 /= H7 /= H16 /= H17 /= H18 /= H19 /=. }
move: Hdec. rewrite /= Hlp => Hdec.
rewrite addnS -addw_pcw_one in Hv1.
rewrite addnS -addw_pcw_one.
set A := Atom (addw (pcw (pc0 + n)) onew) InternalJump.
have HB : forall k a, (wk k == wk 4) = false -> rg (wk k) = Some a ->
    setm rg (wk 4) A (wk k) = Some a.
{ move=> k a Hk Ha. by rewrite setmE Hk. }
have HB1 := HB 1 _ erefl H1. have HB0 := HB 0 _ erefl H0.
have HB2 := HB 2 _ erefl H2. have HB3 := HB 3 _ erefl H3.
have HB5 := HB 5 _ erefl H5. have HB6 := HB 6 _ erefl H6.
have HB7 := HB 7 _ erefl H7. have HB16 := HB 16 _ erefl H16.
have HB17 := HB 17 _ erefl H17. have HB18 := HB 18 _ erefl H18.
have HB19 := HB 19 _ erefl H19.
rewrite /step_me.
eapply (@Symbolic.step_jal mt ops lrc_tags Merged.transfer unit (table (NC := NC)) _ _ _
          m rg (pcw (pc0 + n)) vv (@word_of_nat (imm_size mt) tgt) (Level lv cid)
          (MTag vtg cid etg true) w4 t4 tt
          [hseq t4; t1; t0; t2; t3; t5; t6; t7; t16; t17; t18; t19]
          vv1 (MTag vtg1 cid etg1 ictg1)).
- exact: erefl.
- exact: Hv.
- exact: Hv1.
- exact: Hdec.
- exact: H4.
- exact: Hclear.
- rewrite /Symbolic.next_state_updates_and_pc (swcast_small Htgt).
  rewrite /Symbolic.next_state /Symbolic.evi.
  have -> : (rcom : reg mt) = wk 1 by [].
  case Et: (m (pcw tgt)) Htc => [[it tt0]|] Htc.
  + case: tt0 Et Htc => vt0 ct0 et0 ic0 Et /= Htc. subst ct0.
    rewrite H1 /=.
    rewrite /Merged.transfer /Merged.instr_rules /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite /check_belong /belong /= ?eqxx /=.
    rewrite /updm Hv1 /= (setm_id Hv1) H4 /=.
    rewrite HB1 /= (setm_id HB1) HB0 /= (setm_id HB0) HB2 /= (setm_id HB2).
    rewrite HB3 /= (setm_id HB3) HB5 /= (setm_id HB5) HB6 /= (setm_id HB6).
    rewrite HB7 /= (setm_id HB7) HB16 /= (setm_id HB16) HB17 /= (setm_id HB17).
    rewrite HB18 /= (setm_id HB18) HB19 /= (setm_id HB19).
    by [].
  + rewrite H1 /=.
    rewrite /Merged.transfer /Merged.instr_rules /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite /check_belong /belong /= eqxx /=.
    rewrite /updm Hv1 /= (setm_id Hv1) H4 /=.
    rewrite HB1 /= (setm_id HB1) HB0 /= (setm_id HB0) HB2 /= (setm_id HB2).
    rewrite HB3 /= (setm_id HB3) HB5 /= (setm_id HB5) HB6 /= (setm_id HB6).
    rewrite HB7 /= (setm_id HB7) HB16 /= (setm_id HB16) HB17 /= (setm_id HB17).
    rewrite HB18 /= (setm_id HB18) HB19 /= (setm_id HB19).
    by [].
Qed.

Lemma me_step_jal_call (m : {fmap mword mt -> matom}) (rg : rmap)
    lv cid n l tg i1 tg1 tgt it vt' cid' p lst ic' vc :
  code_in m ->
  List.nth_error cde n = Some (MrJal l, tg) ->
  is_code tg -> color tg = cid ->
  List.nth_error cde n.+1 = Some (i1, tg1) -> color tg1 = cid ->
  code_label_pos cde pc0 l (pc0 + n) = tgt ->
  tgt < 2 ^ imm_size mt ->
  m (pcw tgt) = Some (Atom it (MTag vt' cid' (Some (p, lst)) ic')) ->
  cid' != cid -> cid \in lst ->
  rg (wk 1) = Some (Atom vc Other) ->
  regs_ok rg ->
  exists rg',
    [/\ step_me (NC := NC)
          (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (pc0 + n)) (Level lv cid)) tt)
          (@Symbolic.State mt lrc_tags unit m rg' (Atom (pcw tgt) (Level lv.+1 cid')) tt)
          (Some (ECall cid p (convert (int_of_word vc)) cid')),
        rg' (wk 4) = Some (Atom (pcw (pc0 + n.+1)) (Ret lv)),
        rg' (wk 1) = Some (Atom vc Other)
      & regs_ok rg'].
Proof.
move=> Hc Hn Hic Hcol Hn1 Hcol1 Hlp Htgt Htc Hne Hlst Hrc Hok.
have [[vv vt] [Hv /= Htv Hdec]] := me_fetch Hc Hn.
subst vt.
have [[vv1 vt1] [Hv1 /= Htv1 _]] := me_fetch Hc Hn1.
subst vt1.
case: tg Hn Hic Hcol Hv => vtg ctg etg [] Hn //= _ Hcol Hv.
subst ctg.
case: tg1 Hn1 Hcol1 Hv1 => vtg1 ctg1 etg1 ictg1 Hn1 /= Hcol1 Hv1.
subst ctg1.
have [a0 [a1 [a2 [a3 [a4 [a5 [a6 [a7 [a16 [a17 [a18 [a19
       [[H0 H1 H2 H3] [H4 H5 H6 H7] [H16 H17 H18 H19]]]]]]]]]]]]]] :=
  regs_ok_atoms Hok.
rewrite H1 in Hrc. case: Hrc => Ea1. subst a1. rename H1 into Hrc.
case: a0 H0 => w0 t0 H0.
case: a2 H2 => w2 t2 H2. case: a3 H3 => w3 t3 H3.
case: a4 H4 => w4 t4 H4. case: a5 H5 => w5 t5 H5.
case: a6 H6 => w6 t6 H6. case: a7 H7 => w7 t7 H7.
case: a16 H16 => w16 t16 H16. case: a17 H17 => w17 t17 H17.
case: a18 H18 => w18 t18 H18. case: a19 H19 => w19 t19 H19.
have Hclear : reg_clear_list rg t4
  = Some [hseq t4; Other; t0; t2; t3; t5; t6; t7; t16; t17; t18; t19].
{ rewrite /reg_clear_list /=.
  by rewrite Hrc /= H0 /= H2 /= H3 /= H5 /= H6 /= H7 /= H16 /= H17 /= H18 /= H19 /=. }
move: Hdec. rewrite /= Hlp => Hdec.
rewrite addnS -addw_pcw_one in Hv1.
rewrite addnS -addw_pcw_one.
have Hmem : mem_seq lst cid = true := Hlst.
have Hneb : (cid == cid') = false by apply/negbTE; rewrite eq_sym.
eexists. split.
- rewrite /step_me.
  eapply (@Symbolic.step_jal mt ops lrc_tags Merged.transfer unit (table (NC := NC)) _ _ _
            m rg (pcw (pc0 + n)) vv (@word_of_nat (imm_size mt) tgt) (Level lv cid)
            (MTag vtg cid etg true) w4 t4 tt
            [hseq t4; Other; t0; t2; t3; t5; t6; t7; t16; t17; t18; t19]
            vv1 (MTag vtg1 cid etg1 ictg1)).
  + exact: erefl.
  + exact: Hv.
  + exact: Hv1.
  + exact: Hdec.
  + exact: H4.
  + exact: Hclear.
  + rewrite /Symbolic.next_state_updates_and_pc (swcast_small Htgt) Htc.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt) = wk 1 by [].
    rewrite Hrc /=.
    rewrite /Merged.transfer /Merged.instr_rules /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite /check_belong /belong /= ?eqxx /= Hneb /= Hmem /=.
    rewrite /updm Hv1 /= (setm_id Hv1) H4 /=.
    rewrite !setmE !wk_eq //= Hrc /=.
    rewrite !setmE !wk_eq //= H0 /=.
    rewrite !setmE !wk_eq //= H2 /=.
    rewrite !setmE !wk_eq //= H3 /=.
    rewrite !setmE !wk_eq //= H5 /=.
    rewrite !setmE !wk_eq //= H6 /=.
    rewrite !setmE !wk_eq //= H7 /=.
    rewrite !setmE !wk_eq //= H16 /=.
    rewrite !setmE !wk_eq //= H17 /=.
    rewrite !setmE !wk_eq //= H18 /=.
    rewrite !setmE !wk_eq //= H19 /=.
    by [].
- by rewrite !setmE !wk_eq.
- by rewrite !setmE !wk_eq.
- by do 12 apply: regs_ok_setm.
Qed.

Lemma me_step_jump_ret (m : {fmap mword mt -> matom}) (rg : rmap)
    n' cid n tg w iw vtw cid' etw icw vc :
  code_in m ->
  List.nth_error cde n = Some (MrJump R_RA, tg) ->
  is_code tg -> color tg = cid ->
  rg (wk 4) = Some (Atom w (Ret n')) ->
  m w = Some (Atom iw (MTag vtw cid' etw icw)) ->
  cid' != cid ->
  rg (wk 1) = Some (Atom vc Other) ->
  regs_ok rg ->
  exists rg',
    [/\ step_me (NC := NC)
          (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (pc0 + n)) (Level n'.+1 cid)) tt)
          (@Symbolic.State mt lrc_tags unit m rg' (Atom w (Level n' cid')) tt)
          (Some (ERet cid (convert (int_of_word vc)) cid')),
        rg' (wk 1) = Some (Atom vc Other)
      & regs_ok rg'].
Proof.
move=> Hc Hn Hic Hcol Hra Hw Hne Hrc Hok.
have [[vv vt] [Hv /= Htv Hdec]] := me_fetch Hc Hn.
subst vt.
case: tg Hn Hic Hcol Hv => vtg ctg etg [] Hn //= _ Hcol Hv.
subst ctg.
have [a0 [a1 [a2 [a3 [a4 [a5 [a6 [a7 [a16 [a17 [a18 [a19
       [[H0 H1 H2 H3] [H4 H5 H6 H7] [H16 H17 H18 H19]]]]]]]]]]]]]] :=
  regs_ok_atoms Hok.
rewrite H1 in Hrc. case: Hrc => Ea1. subst a1. rename H1 into Hrc.
rewrite H4 in Hra. case: Hra => Ea4. subst a4. rename H4 into Hra.
case: a0 H0 => w0 t0 H0.
case: a2 H2 => w2 t2 H2. case: a3 H3 => w3 t3 H3.
case: a5 H5 => w5 t5 H5.
case: a6 H6 => w6 t6 H6. case: a7 H7 => w7 t7 H7.
case: a16 H16 => w16 t16 H16. case: a17 H17 => w17 t17 H17.
case: a18 H18 => w18 t18 H18. case: a19 H19 => w19 t19 H19.
have Hclear : reg_clear_list rg (Ret n')
  = Some [hseq Ret n'; Other; t0; t2; t3; t5; t6; t7; t16; t17; t18; t19].
{ rewrite /reg_clear_list /=.
  by rewrite Hrc /= H0 /= H2 /= H3 /= H5 /= H6 /= H7 /= H16 /= H17 /= H18 /= H19 /=. }
have Hneb : (cid == cid') = false by apply/negbTE; rewrite eq_sym.
eexists. split.
- rewrite /step_me.
  eapply (@Symbolic.step_jump mt ops lrc_tags Merged.transfer unit (table (NC := NC)) _ _ _
            m rg (pcw (pc0 + n)) vv (wk 4) w (Level n'.+1 cid)
            (MTag vtg cid etg true) (Ret n') tt
            [hseq Ret n'; Other; t0; t2; t3; t5; t6; t7; t16; t17; t18; t19]
            w (Ret n')).
  + exact: erefl.
  + exact: Hv.
  + exact: Hdec.
  + exact: Hra.
  + exact: Hra.
  + exact: Hclear.
  + rewrite /Symbolic.next_state_updates_and_pc Hw.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt) = wk 1 by [].
    rewrite Hrc /=.
    rewrite /Merged.transfer /Merged.instr_rules /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite /check_belong /belong /= Hneb /= eqxx /=.
    rewrite /updm Hra /=.
    rewrite !setmE !wk_eq //=.
    rewrite !setmE !wk_eq //= Hrc /=.
    rewrite !setmE !wk_eq //= H0 /=.
    rewrite !setmE !wk_eq //= H2 /=.
    rewrite !setmE !wk_eq //= H3 /=.
    rewrite !setmE !wk_eq //= H5 /=.
    rewrite !setmE !wk_eq //= H6 /=.
    rewrite !setmE !wk_eq //= H7 /=.
    rewrite !setmE !wk_eq //= H16 /=.
    rewrite !setmE !wk_eq //= H17 /=.
    rewrite !setmE !wk_eq //= H18 /=.
    rewrite !setmE !wk_eq //= H19 /=.
    by [].
- by rewrite !setmE !wk_eq.
- by do 13 apply: regs_ok_setm.
Qed.

Lemma me_step_syscall (m : {fmap mword mt -> matom}) (rg : rmap) tpc rc st' :
  m (pcw alloc_label) = None ->
  rg (wk 1) = Some rc ->
  LRC.alloc_fun (NC := NC)
    (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw alloc_label) tpc) tt) = Some st' ->
  step_me (NC := NC)
    (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw alloc_label) tpc) tt) st' None.
Proof.
move=> Hm Hrc Hal.
rewrite /step_me.
eapply (@Symbolic.step_syscall mt ops lrc_tags Merged.transfer unit (table (NC := NC)) _ _ _
          m rg (pcw alloc_label)
          (@Symbolic.Syscall mt lrc_tags unit tt (LRC.alloc_fun (NC := NC))) tpc tt).
- exact: erefl.
- exact: Hm.
- by rewrite /table mkfmapE /= eqxx.
- rewrite /Symbolic.run_syscall /Symbolic.evi.
  have -> : (rcom : reg mt) = wk 1 by [].
  rewrite Hrc /=.
  by rewrite Hal.
Qed.

Lemma me_final_halt (m : {fmap mword mt -> matom}) (rg : rmap)
    tpc n tg :
  code_in m ->
  List.nth_error cde n = Some (@MrHalt mt, tg) ->
  is_code tg ->
  final_halt_code (@Symbolic.State mt lrc_tags unit m rg (Atom (pcw (pc0 + n)) tpc) tt).
Proof.
move=> Hc Hn Hic.
have [[vv vt] [Hv /= Htv Hdec]] := me_fetch Hc Hn.
subst vt.
rewrite /final_halt_code Hv. split; [exact: Hdec | exact: Hic].
Qed.

End MEStep.
