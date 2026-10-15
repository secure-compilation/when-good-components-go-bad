Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div fintype ssrint seq path.
From mathcomp Require Import ssralg intdiv zify.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import MicroPolicies.Types.
Require Import MicroPolicies.WordExtra.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.OffsetWord.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Section Alloc.

Variable NC : nat.
Hypothesis HNCws : NC <= word_size mt.

Lemma prefix_val (m : nat) :
  m < 2 ^ NC ->
  (\val (LRC.component_memory_prefix (NC := NC) (ssrint.Posz m)
        : word (word_size mt)) : nat)
  = m * 2 ^ (word_size mt - NC).
Proof.
move=> Hm.
have Hsub : word_size mt - NC < 2 ^ (word_size mt)
  by apply: (leq_ltn_trans (leq_subr NC (word_size mt))); apply: ltn_expl.
have Hmw : m < 2 ^ (word_size mt) by apply: (leq_trans Hm); rewrite leq_exp2l.
have Hprod : m * 2 ^ (word_size mt - NC) < 2 ^ (word_size mt).
{ rewrite -{2}(subnK HNCws) expnD [X in _ < X]mulnC ltn_mul2r expn_gt0 /=.
  exact: Hm. }
rewrite /LRC.component_memory_prefix.
set wm := word.as_word (ssrint.Posz m).
set sh := word.as_word (ssrint.Posz (word_size mt - NC)).
rewrite valw_shlw.
have Evm : (\val wm : nat) = m
  by rewrite /wm valw_as_word modn_small.
have Evsh : (\val sh : nat) = word_size mt - NC
  by rewrite /sh valw_as_word modn_small.
apply: (eq_trans
          (y := (m * 2 ^ (word_size mt - NC)) %% 2 ^ word_size mt)).
- congr (_ %% _).
  congr (_ * 2 ^ _).
  + exact: Evm.
  + exact: Evsh.
- exact: modn_small Hprod.
Qed.

Lemma andw_mask_val (w : word (word_size mt)) :
  (\val (word.andw w (LRC.mask (NC := NC))) : nat)
  = \val w %/ 2 ^ (word_size mt - NC) * 2 ^ (word_size mt - NC).
Proof.
have NatpowE : forall a b, Nat.pow a b = expn a b.
{ move=> a; elim => [|b IH]; first by rewrite expn0.
  by rewrite expnS /= IH. }
have Hmone : (word.as_word (Nat.sub (Nat.pow 2 (word_size mt)) 1)
              : word (word_size mt)) = monew.
{ rewrite NatpowE. apply: mone_as_word. }
rewrite /LRC.mask.
set sh := word.as_word (ssrint.Posz (word_size mt - NC)).
rewrite Hmone.
rewrite val_andw_shlw_mone.
have Hsub : word_size mt - NC < 2 ^ word_size mt
  by apply: (leq_ltn_trans (leq_subr NC (word_size mt))); apply: ltn_expl.
have Evsh : (\val sh : nat) = word_size mt - NC
  by rewrite /sh valw_as_word modn_small.
congr (_ %/ 2 ^ _ * 2 ^ _).
- exact: Evsh.
- exact: Evsh.
Qed.

Lemma pfilter_val (c0 : nat) (w : word (word_size mt)) :
  1 + c0 < 2 ^ NC ->
  (word.andw w (LRC.mask (NC := NC))
   == LRC.component_memory_prefix (NC := NC) (ssrint.Posz (1 + c0)))
  = ((1 + c0) * 2 ^ (word_size mt - NC) <= \val w)
    && (\val w < (2 + c0) * 2 ^ (word_size mt - NC)).
Proof.
move=> Hc.
have Hk : 0 < 2 ^ (word_size mt - NC) by rewrite expn_gt0.
apply/idP/idP.
- move=> /eqP E.
  have Ev : (\val (word.andw w (LRC.mask (NC := NC))) : nat)
            = \val (LRC.component_memory_prefix (NC := NC)
                      (ssrint.Posz (1 + c0)) : word (word_size mt))
    by rewrite E.
  have Ev2 := eq_trans (eq_trans (esym (andw_mask_val w)) Ev)
                (prefix_val Hc).
  have Hq : \val w %/ 2 ^ (word_size mt - NC) = 1 + c0.
  { move: Ev2 => /eqP Ev3.
    rewrite (eqn_pmul2r Hk) in Ev3.
    apply/eqP. exact: Ev3. }
  apply/andP; split; by lia.
- move=> /andP[H1 H2].
  have Hle1 : \val w %/ 2 ^ (word_size mt - NC) < 2 + c0
    by rewrite ltn_divLR //.
  have Hle2 : 1 + c0 <= \val w %/ 2 ^ (word_size mt - NC)
    by rewrite leq_divRL //.
  have Hq : \val w %/ 2 ^ (word_size mt - NC) = 1 + c0 by lia.
  apply/eqP.
  apply: word_nat_inj.
  have Emid : \val w %/ 2 ^ (word_size mt - NC) * 2 ^ (word_size mt - NC)
              = (1 + c0) * 2 ^ (word_size mt - NC).
  { by rewrite Hq. }
  exact: (eq_trans (eq_trans (andw_mask_val w) Emid)
            (esym (prefix_val Hc))).
Qed.

Definition pfilterC (c0 : nat) : pred (mword mt) :=
  fun mw => word.andw mw (LRC.mask (NC := NC))
            == LRC.component_memory_prefix (NC := NC)
                 (ssrint.Posz (1 + c0)).

Lemma List_filter_seq (T : Type) (p : pred T) (l : seq T) :
  List.filter p l = filter p l.
Proof. by elim: l => //= a l ->. Qed.

Lemma List_last_seq (T : Type) (d : T) (l : seq T) :
  List.last l d = last d l.
Proof.
elim: l d => [|a l IH] d //.
case: l IH => [|b l'] IH //.
have E1 : List.last [:: a, b & l'] d = List.last (b :: l') d by [].
by rewrite E1 (IH d).
Qed.

Definition maxaddr (m : {fmap mword mt -> atom (mword mt) mem_tag})
    (c0 : nat) : mword mt :=
  List.last
    (List.filter (pfilterC c0) (domm m))
    (LRC.component_memory_prefix (NC := NC) (ssrint.Posz (1 + c0))).

Lemma maxaddr_empty (m : {fmap mword mt -> atom (mword mt) mem_tag}) (c0 : nat) :
  (forall w, pfilterC c0 w -> m w = None) ->
  maxaddr m c0 = LRC.component_memory_prefix (NC := NC) (ssrint.Posz (1 + c0)).
Proof.
move=> H. rewrite /maxaddr List_filter_seq List_last_seq.
have -> : filter (pfilterC c0) (domm m) = [::].
{ apply/eqP. rewrite -[_ == _]negbK -has_filter. apply/hasP => -[w Hw Hp].
  move: Hw. by rewrite mem_domm (H w Hp). }
by [].
Qed.

Lemma alloc_fun_spec (st : @Symbolic.state mt lrc_tags unit)
    (c0 lvl : nat) (wret wsz : mword mt) (len : nat)
    (rc : atom (mword mt) mem_tag) (a16 : @ratom mt) :
  taga (Symbolic.pc st) = LRC.Level lvl c0 ->
  Symbolic.regs st (ra : reg mt) = Some (Atom wret InternalJump) ->
  Symbolic.mem st wret = Some rc ->
  is_code (taga rc) ->
  color (taga rc) = c0 ->
  Symbolic.regs st (syscall_arg1 : reg mt) = Some (Atom wsz Other) ->
  word.int_of_word wsz = ssrint.Posz len ->
  Symbolic.regs st (syscall_ret : reg mt) = Some a16 ->
  0 < len ->
  len + 1 <= 2 ^ (word_size mt - NC) ->
  1 + c0 < 2 ^ NC ->
  pfilterC c0 (word.addw (maxaddr (Symbolic.mem st) c0)
                 (word.as_word (ssrint.Posz (len + 1)))) ->
  LRC.alloc_fun (NC := NC) st
  = Some (@Symbolic.State mt lrc_tags unit
            (unionm (Symbolic.mem st)
               (mkfmap (mkseq (fun n =>
                  (word.addw (maxaddr (Symbolic.mem st) c0)
                     (word.as_word (ssrint.Posz (n + 1))),
                   Atom (word.as_word 0) (def_mem_tag c0 false))) len)))
            (setm (Symbolic.regs st) (syscall_ret : reg mt)
               (Atom (word.addw (maxaddr (Symbolic.mem st) c0)
                        (word.as_word (ssrint.Posz 1))) Other))
            (Atom wret (LRC.Level lvl c0))
            tt).
Proof.
move=> Hpct Hra Hrc Hic Hcol Hsz Hint Hret Hpos Hlen Hc Hfit.
case: len Hint Hpos Hlen Hfit => [|len0] // Hint _ Hlen Hfit.
have obE : forall (S T : Type) (f : S -> option T) (y : S),
    obind f (Some y) = f y by [].
have EIJ : LRC.is_jump InternalJump = Some tt by [].
have EIO : LRC.is_other Other = Some tt by [].
rewrite /LRC.alloc_fun.
rewrite Hpct.
cbv beta iota zeta.
rewrite Hra obE.
cbv beta.
rewrite EIJ obE.
cbv beta.
rewrite Hrc obE.
cbv beta.
rewrite Hic Hcol eqxx.
cbv beta iota.
rewrite obE.
cbv beta.
rewrite Hsz obE.
cbv beta.
rewrite EIO obE.
cbv beta.
rewrite Hint.
cbv beta iota.
rewrite obE.
cbv beta.
rewrite Hlen.
cbv beta iota.
rewrite obE.
cbv beta.
case: ifP => [Hneg|Hneg].
- exfalso.
  move: Hfit; rewrite /pfilterC /maxaddr => Hfit.
  by rewrite Hfit in Hneg.
- rewrite /updm Hret.
  cbv beta iota.
  by congr Some.
Qed.

Lemma val_addw_small (w : word (word_size mt)) (n : nat) :
  \val w + n < 2 ^ word_size mt ->
  (\val (addw w (word.as_word (ssrint.Posz n))) : nat) = \val w + n.
Proof.
move=> H.
have HnW : n < 2 ^ word_size mt by lia.
by rewrite valw_addw valw_as_word modnDmr (modn_small H).
Qed.

Lemma region_key (c0 k : nat) :
  1 + c0 < 2 ^ NC ->
  k.+1 < 2 ^ (word_size mt - NC) ->
  pfilterC c0 (addw (LRC.component_memory_prefix (NC := NC) (ssrint.Posz (1 + c0)))
                    (word.as_word (ssrint.Posz k.+1))).
Proof.
move=> Hc Hk.
have HK : 0 < 2 ^ (word_size mt - NC) by rewrite expn_gt0.
have H2 : 2 + c0 <= 2 ^ NC by lia.
have Htop : (2 + c0) * 2 ^ (word_size mt - NC) <= 2 ^ word_size mt.
{ rewrite -{2}(subnK HNCws) expnD mulnC leq_mul2l. by rewrite H2 orbT. }
have Hv := prefix_val Hc.
have Hsum : \val (LRC.component_memory_prefix (NC := NC) (ssrint.Posz (1 + c0))
                  : word (word_size mt)) + k.+1 < 2 ^ word_size mt.
{ rewrite Hv. apply: (leq_trans _ Htop). rewrite mulnDl mul1n. rewrite addnC ltn_add2r.
  done. }
rewrite /pfilterC pfilter_val // (val_addw_small Hsum) Hv.
apply/andP. split.
- exact: leq_addr.
- rewrite !mulnDl mul1n. set X := c0 * _. clear -Hk. lia.
Qed.

Lemma getm_def_allv (T : ordType) (S : Type) (v : S) (s : seq (T * S)) k :
  (forall p, List.In p s -> p.2 = v) ->
  List.In k [seq p.1 | p <- s] ->
  getm_def s k = Some v.
Proof.
elim: s => [//|[k0 w] s IH] Hall /= Hin.
case E: (k == k0).
- congr Some. exact: (Hall (k0, w) (or_introl erefl)).
- apply: IH.
  + move=> p Hp. exact: Hall p (or_intror Hp).
  + case: Hin => [Ek|//]. by rewrite Ek eqxx in E.
Qed.

Lemma getm_def_const (T : ordType) (S : Type) (f : nat -> T) (v : S) len j :
  j < len -> getm_def (mkseq (fun n => (f n, v)) len) (f j) = Some v.
Proof.
move=> Hj. apply: getm_def_allv.
- move=> p. rewrite /mkseq => /List.in_map_iff [x [<- _]]. by [].
- rewrite /mkseq -map_comp. apply/List.in_map_iff. exists j. split=> //.
  apply/List.in_seq. split; first by apply/leP.
  rewrite /=. apply/ltP. exact: Hj.
Qed.

Definition rpre (c0 : nat) : mword mt :=
  LRC.component_memory_prefix (NC := NC) (ssrint.Posz (1 + c0)).

Definition blkseq (c0 B : nat) : seq (mword mt * atom (mword mt) mem_tag) :=
  mkseq (fun n => (word.addw (rpre c0) (word.as_word (ssrint.Posz (n + 1))),
                   Atom (word.as_word 0 : mword mt) (def_mem_tag c0 false))) B.

Definition ctrlw (c0 : nat) : mword mt := addw (rpre c0) (@word_of_nat (word_size mt) 1).

Lemma blkseq_get (c0 B j : nat) :
  j < B ->
  mkfmap (blkseq c0 B) (addw (rpre c0) (@word_of_nat (word_size mt) j.+1))
  = Some (Atom (word.as_word 0 : mword mt) (def_mem_tag c0 false)).
Proof.
move=> Hj. rewrite mkfmapE.
have H := getm_def_const
            (fun n => word.addw (rpre c0) (word.as_word (ssrint.Posz (n + 1))))
            (Atom (word.as_word 0 : mword mt) (def_mem_tag c0 false)) Hj.
rewrite addn1 in H. exact: H.
Qed.

Definition cellw (c0 j : nat) : mword mt := addw (ctrlw c0) (@word_of_nat (word_size mt) j).

Lemma won_add (a b : nat) :
  addw (@word_of_nat (word_size mt) a) (@word_of_nat (word_size mt) b)
  = @word_of_nat (word_size mt) (a + b).
Proof. by rewrite /word_of_nat as_word_addwD. Qed.

Lemma cellwE (c0 j : nat) : cellw c0 j = addw (rpre c0) (@word_of_nat (word_size mt) j.+1).
Proof.
exact: (etrans (esym (addwA (rpre c0) (@word_of_nat (word_size mt) 1)
                             (@word_of_nat (word_size mt) j)))
               (f_equal (addw (rpre c0))
                  (etrans (won_add 1 j) (f_equal (fun k => @word_of_nat (word_size mt) k)
                                                 (add1n j))))).
Qed.

Lemma cellw_val (c0 j : nat) :
  1 + c0 < 2 ^ NC -> j.+2 <= 2 ^ (word_size mt - NC) ->
  (\val (cellw c0 j) : nat) = (1 + c0) * 2 ^ (word_size mt - NC) + j.+1.
Proof.
move=> Hc Hj.
have HK : 0 < 2 ^ (word_size mt - NC) by rewrite expn_gt0.
have H2 : 2 + c0 <= 2 ^ NC by lia.
have Htop : (2 + c0) * 2 ^ (word_size mt - NC) <= 2 ^ word_size mt.
{ rewrite -{2}(subnK HNCws) expnD mulnC leq_mul2l. by rewrite H2 orbT. }
have Hv := prefix_val Hc.
rewrite cellwE. rewrite /word_of_nat.
rewrite val_addw_small /rpre Hv //.
apply: (leq_trans _ Htop). rewrite mulnDl mul1n. set X := c0 * _. clear -Hj. lia.
Qed.

Lemma ctrlw_val (c0 : nat) :
  1 + c0 < 2 ^ NC -> 2 <= 2 ^ (word_size mt - NC) ->
  (\val (ctrlw c0) : nat) = (1 + c0) * 2 ^ (word_size mt - NC) + 1.
Proof.
move=> Hc Hj.
have HK : 0 < 2 ^ (word_size mt - NC) by rewrite expn_gt0.
have H2 : 2 + c0 <= 2 ^ NC by lia.
have Htop : (2 + c0) * 2 ^ (word_size mt - NC) <= 2 ^ word_size mt.
{ rewrite -{2}(subnK HNCws) expnD mulnC leq_mul2l. by rewrite H2 orbT. }
have Hv := prefix_val Hc.
rewrite /ctrlw /word_of_nat val_addw_small /rpre Hv //.
apply: (leq_trans _ Htop). rewrite mulnDl mul1n. set X := c0 * _. clear -Hj. lia.
Qed.

Lemma ctrl_cell_ne (c0 j : nat) :
  1 + c0 < 2 ^ NC -> j.+2 <= 2 ^ (word_size mt - NC) -> 0 < j ->
  (cellw c0 j == ctrlw c0) = false.
Proof.
move=> Hc Hj Hj0. apply/eqP => E.
have H2 : 2 <= 2 ^ (word_size mt - NC) by apply: leq_trans _ Hj.
have H := etrans (esym (cellw_val Hc Hj))
            (etrans (congr1 (fun w : mword mt => (\val w : nat)) E) (ctrlw_val Hc H2)).
clear -H Hj0. lia.
Qed.

Lemma cellw_ne (c0 j j' : nat) :
  1 + c0 < 2 ^ NC -> j.+2 <= 2 ^ (word_size mt - NC) -> j'.+2 <= 2 ^ (word_size mt - NC) ->
  j <> j' -> (cellw c0 j == cellw c0 j') = false.
Proof.
move=> Hc Hj Hj' Hne. apply/eqP => E.
have H := etrans (esym (cellw_val Hc Hj))
            (etrans (congr1 (fun w : mword mt => (\val w : nat)) E) (cellw_val Hc Hj')).
apply: Hne. clear -H. lia.
Qed.

Lemma ctrlw_neq0 (c0 : nat) :
  1 + c0 < 2 ^ NC -> 2 <= 2 ^ (word_size mt - NC) -> ctrlw c0 != 0%w.
Proof.
move=> Hc H2. apply/eqP => E.
have H := etrans (esym (ctrlw_val Hc H2)) (congr1 (fun w : mword mt => (\val w : nat)) E).
have Z : (\val (0%w : mword mt) : nat) = 0 by rewrite valw_zero'.
have H' := etrans H Z. clear -H'. lia.
Qed.

Lemma ctrlw_region (c0 : nat) :
  1 + c0 < 2 ^ NC -> 2 < 2 ^ (word_size mt - NC) -> pfilterC c0 (ctrlw c0).
Proof. move=> Hc H. exact: (region_key (k := 0) Hc (ltn_trans (erefl : 1 < 2) H)). Qed.

Lemma cellw_region (c0 j : nat) :
  1 + c0 < 2 ^ NC -> j.+2 <= 2 ^ (word_size mt - NC) -> pfilterC c0 (cellw c0 j).
Proof. move=> Hc Hj. rewrite cellwE. exact: (region_key Hc Hj). Qed.

Lemma region_disj (c1 c2 : nat) (w : mword mt) :
  1 + c1 < 2 ^ NC -> 1 + c2 < 2 ^ NC ->
  pfilterC c1 w -> pfilterC c2 w -> c1 = c2.
Proof.
move=> H1 H2 Hp1 Hp2.
move: Hp1. rewrite /pfilterC (pfilter_val w H1) => /andP [A1 B1].
move: Hp2. rewrite /pfilterC (pfilter_val w H2) => /andP [A2 B2].
have HK : 0 < 2 ^ (word_size mt - NC) by rewrite expn_gt0.
set K := 2 ^ (word_size mt - NC) in A1 B1 A2 B2 HK.
have E1 : \val w %/ K = 1 + c1.
{ apply/eqP. rewrite eqn_leq. apply/andP; split.
  - by rewrite -ltnS ltn_divLR.
  - by rewrite leq_divRL. }
have E2 : \val w %/ K = 1 + c2.
{ apply/eqP. rewrite eqn_leq. apply/andP; split.
  - by rewrite -ltnS ltn_divLR.
  - by rewrite leq_divRL. }
lia.
Qed.

Lemma low_not_region (c0 : nat) (w : mword mt) :
  1 + c0 < 2 ^ NC -> (\val w : nat) < 2 ^ (word_size mt - NC) -> ~~ pfilterC c0 w.
Proof.
move=> Hc Hw. rewrite /pfilterC pfilter_val //.
apply/negP => /andP [H1 _].
have HK : 0 < 2 ^ (word_size mt - NC) by rewrite expn_gt0.
set K := 2 ^ (word_size mt - NC) in Hw H1 HK.
have : K <= (1 + c0) * K by rewrite leq_pmull.
lia.
Qed.

End Alloc.
