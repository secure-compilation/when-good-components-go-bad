From mathcomp Require Import
  ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype bigop finfun tuple binomial ssrint ssralg intdiv.
From mathcomp Require Import zify.
From CoqUtils Require Import word.
Require Import Coq.micromega.Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section WordBitsKernel.

Variable k : nat.
Implicit Types (w x y : word k).

Lemma valw_as_word (m : nat) : val (as_word m : word k) = m %% 2 ^ k :> nat.
Proof. by rewrite /= modz_nat absz_nat modn_mod. Qed.

Lemma valw_shlw w (n : word k) :
  val (shlw w n) = (val w * 2 ^ val n) %% 2 ^ k :> nat.
Proof. by rewrite /shlw valw_as_word. Qed.

Lemma valw_addw w (y : word k) :
  val (addw w y) = (val w + val y) %% 2 ^ k :> nat.
Proof. by rewrite /addw valw_as_word. Qed.

Lemma valw_zero' : val (zerow : word k) = 0 :> nat.
Proof. by rewrite /zerow valw_as_word mod0n. Qed.

Lemma valw_monew : val (monew : word k) = (2 ^ k).-1 :> nat.
Proof.
rewrite /monew /oppw /onew !valw_as_word.
have h2 : 0 < 2 ^ k by rewrite expn_gt0.
case: (posnP k) => [-> //| Hk].
have h1 : 1 %% 2 ^ k = 1.
{ by rewrite modn_small // -[1]/(2 ^ 0) ltn_exp2l. }
rewrite h1 modn_small; lia.
Qed.

Lemma mone_as_word : as_word (Posz (2 ^ k - 1)) = (monew : word k).
Proof.
apply: val_inj; apply: ord_inj.
rewrite valw_as_word valw_monew modn_small; lia.
Qed.

Lemma as_word_pred1 : as_word (Posz (2 ^ k) - 1)%R = (monew : word k).
Proof.
rewrite -mone_as_word; congr as_word.
rewrite subzn ?expn_gt0 //.
Qed.

Lemma word_nat_inj (x y : word k) : val x = val y :> nat -> x = y.
Proof. move=> H; apply: val_inj; exact: ord_inj H. Qed.

Lemma valw_shlw_small (c m : nat) :
  m <= k -> c * 2 ^ m < 2 ^ k ->
  val (shlw (as_word (Posz c)) (as_word (Posz m)) : word k) = c * 2 ^ m :> nat.
Proof.
move=> Hm Hcm.
rewrite valw_shlw !valw_as_word.
have Hmk : m %% 2 ^ k = m.
{ rewrite modn_small //; apply: leq_ltn_trans Hm _; exact: ltn_expl. }
have Hc : c < 2 ^ k.
{ apply: leq_ltn_trans Hcm; rewrite -{1}[c]muln1 leq_mul2l expn_gt0 orbT //. }
by rewrite Hmk (modn_small Hc) (modn_small Hcm).
Qed.

Lemma bits_of_wordE w (i : 'I_k) : bits_of_word w i = odd (val w %/ 2 ^ i).
Proof. by rewrite /bits_of_word -lock ffunE. Qed.

Lemma bits_andw x y (i : 'I_k) :
  bits_of_word (andw x y) i = bits_of_word x i && bits_of_word y i.
Proof. by rewrite /andw /bitwise2 word_of_bitsK ffunE. Qed.

Lemma sum_bits_low (x : nat) (m : nat) :
  \sum_(i < m) odd (x %/ 2 ^ i) * 2 ^ i = x %% 2 ^ m.
Proof.
elim: m => [|m IH]; first by rewrite big_ord0 expn0 modn1.
rewrite big_ord_recr /= IH expnS -modn2.
rewrite {3}(divn_eq x (2 ^ m)) -modnDml -muln_modl.
have -> : ((x %/ 2 ^ m) %% 2 * 2 ^ m + x %% 2 ^ m) %% (2 * 2 ^ m)
        = (x %/ 2 ^ m) %% 2 * 2 ^ m + x %% 2 ^ m.
{ apply: modn_small.
  have : (x %/ 2 ^ m) %% 2 < 2 by apply: ltn_pmod.
  have : x %% 2 ^ m < 2 ^ m by apply: ltn_pmod; rewrite expn_gt0.
  have : 0 < 2 ^ m by rewrite expn_gt0.
  nia. }
by rewrite addnC.
Qed.

Lemma sum_bits_bound (bs : {ffun pred 'I_k}) :
  \sum_(i < k) bs i * 2 ^ i < 2 ^ k.
Proof.
rewrite -[2 ^ k]prednK ?expn_gt0 // predn_exp mul1n ltnS leq_sum // => i _.
by case: (bs i); rewrite // ?mul1n ?mul0n leqnn.
Qed.

Lemma valw_word_of_bits (bs : {ffun pred 'I_k}) :
  val (word_of_bits bs) = \sum_(i < k) bs i * 2 ^ i :> nat.
Proof. by rewrite /word_of_bits valw_as_word modn_small // sum_bits_bound. Qed.

Lemma shlw_mone_val (n : nat) :
  ((2 ^ k - 1) * 2 ^ n) %% 2 ^ k = 2 ^ k - 2 ^ minn n k.
Proof.
case: (leqP n k) => [Hle | Hgt].
- have He : 2 ^ n <= 2 ^ k by rewrite leq_exp2l.
  have h2n : 0 < 2 ^ n by rewrite expn_gt0.
  have h2k : 0 < 2 ^ k by rewrite expn_gt0.
  have -> : (2 ^ k - 1) * 2 ^ n = (2 ^ n - 1) * 2 ^ k + (2 ^ k - 2 ^ n) by nia.
  rewrite modnMDl modn_small //; lia.
- rewrite subnn.
  have -> : 2 ^ n = 2 ^ (n - k) * 2 ^ k by rewrite -expnD subnK // ltnW.
  by rewrite mulnA modnMl.
Qed.

Lemma odd_pow2B (mu i : nat) :
  mu <= k -> i < k -> odd ((2 ^ k - 2 ^ mu) %/ 2 ^ i) = (mu <= i).
Proof.
move=> Hmu Hi.
case: (leqP mu i) => [Hle | Hgt].
- have -> : 2 ^ k - 2 ^ mu = (2 ^ (k - i) - 1) * 2 ^ i + (2 ^ i - 2 ^ mu).
  { have e1 : 2 ^ (k - i) * 2 ^ i = 2 ^ k by rewrite -expnD subnK // ltnW.
    have e2 : 2 ^ mu <= 2 ^ i by rewrite leq_exp2l.
    have e3 : 2 ^ i <= 2 ^ k by rewrite leq_exp2l // ltnW.
    have e4 : 0 < 2 ^ mu by rewrite expn_gt0.
    nia. }
  rewrite divnMDl ?expn_gt0 // divn_small; last first.
  { have e2 : 2 ^ mu <= 2 ^ i by rewrite leq_exp2l.
    have e4 : 0 < 2 ^ mu by rewrite expn_gt0.
    have e5 : 0 < 2 ^ i by rewrite expn_gt0.
    lia. }
  rewrite addn0 oddB ?expn_gt0 // oddX -[odd 2]/false -[odd 1]/true orbF addbT.
  by rewrite subn_eq0 -ltnNge Hi.
- have -> : 2 ^ k - 2 ^ mu = (2 ^ (k - i) - 2 ^ (mu - i)) * 2 ^ i.
  { have e1 : 2 ^ (k - i) * 2 ^ i = 2 ^ k by rewrite -expnD subnK // ltnW.
    have e2 : 2 ^ (mu - i) * 2 ^ i = 2 ^ mu by rewrite -expnD subnK // ltnW.
    nia. }
  rewrite mulnK ?expn_gt0 //.
  rewrite oddB; last by rewrite leq_exp2l // leq_sub2r.
  rewrite !oddX -![odd 2]/false !orbF !subn_eq0.
  have HkiF : (k <= i) = false by rewrite leqNgt Hi.
  have HmuiF : (mu <= i) = false by rewrite leqNgt Hgt.
  by rewrite HkiF HmuiF.
Qed.

Lemma bits_shlw_mone (n : word k) (i : 'I_k) :
  bits_of_word (shlw monew n) i = (val n <= i).
Proof.
rewrite bits_of_wordE valw_shlw valw_monew.
rewrite -subn1 shlw_mone_val odd_pow2B ?geq_minr ?ltn_ord //.
case: (leqP (val n) k) => [Hle | Hgt]; first by [].
by rewrite leqNgt (ltn_ord i) leqNgt (ltn_trans (ltn_ord i) Hgt).
Qed.

Lemma andw_shlw_mone x (n : word k) :
  andw x (shlw monew n) = as_word (Posz ((val x %/ 2 ^ val n) * 2 ^ val n)).
Proof.
apply: bits_of_word_inj; apply/ffunP => i.
rewrite bits_andw bits_shlw_mone !bits_of_wordE valw_as_word.
have Hx : val x < 2 ^ k by apply: ltn_ord.
case: (leqP (val n) k) => [Hnk | Hnk]; last first.
- rewrite [val x %/ 2 ^ val n]divn_small; last first.
  { apply: (ltn_trans Hx); by rewrite ltn_exp2l. }
  rewrite mul0n mod0n div0n -[odd 0]/false.
  have -> : (val n <= i) = false by rewrite leqNgt (ltn_trans (ltn_ord i) Hnk).
  by rewrite andbF.
- rewrite modn_small; last first.
  { apply: leq_ltn_trans Hx; exact: leq_trunc_div. }
  case: (leqP (val n) (val i)) => [Hni | Hni] /=.
  + rewrite andbT.
    have -> : 2 ^ (val i) = 2 ^ (val n) * 2 ^ (val i - val n)
      by rewrite -expnD subnKC.
    by rewrite !divnMA mulnK ?expn_gt0.
  + rewrite andbF.
    have -> : 2 ^ (val n) = 2 ^ (val i) * 2 ^ (val n - val i)
      by rewrite -expnD subnKC // ltnW.
    rewrite [2 ^ val i * _]mulnC mulnA mulnK ?expn_gt0 //.
    rewrite oddM oddX -[odd 2]/false orbF subn_eq0.
    have -> : (val n <= val i) = false by rewrite leqNgt Hni.
    by rewrite andbF.
Qed.

Lemma val_andw_shlw_mone x (n : word k) :
  val (andw x (shlw monew n)) = (val x %/ 2 ^ val n) * 2 ^ val n :> nat.
Proof.
rewrite andw_shlw_mone valw_as_word.
have Hx : val x < 2 ^ k by apply: ltn_ord.
case: (leqP (val n) k) => [Hnk | Hnk].
- rewrite modn_small //.
  apply: leq_ltn_trans Hx; exact: leq_trunc_div.
- rewrite divn_small ?mul0n ?mod0n //.
  apply: (ltn_trans Hx); by rewrite ltn_exp2l.
Qed.

Lemma shlw_zero' (n : word k) : shlw (zerow : word k) n = zerow.
Proof.
apply: word_nat_inj.
by rewrite valw_shlw valw_zero' mul0n mod0n.
Qed.

Lemma shlw_all_one' (w n : word k) :
  andw (shlw w n) (shlw (as_word (Posz (2 ^ k - 1))) n) = shlw w n.
Proof.
rewrite mone_as_word.
apply: word_nat_inj; rewrite val_andw_shlw_mone valw_shlw.
case: (leqP (val n) k) => [Hnk | Hnk].
- apply: divnK.
  have Hsplit : 2 ^ k = 2 ^ val n * 2 ^ (k - val n) by rewrite -expnD subnKC.
  rewrite [in X in _ %% X]Hsplit.
  by rewrite mulnC -muln_modr; exact: dvdn_mulr (dvdnn _).
- have -> : 2 ^ val n = 2 ^ k * 2 ^ (val n - k) by rewrite -expnD subnKC // ltnW.
  have -> : (val w * (2 ^ k * 2 ^ (val n - k))) %% 2 ^ k = 0.
  { by rewrite mulnCA mulnC modnMl. }
  by rewrite div0n mul0n.
Qed.

End WordBitsKernel.

Lemma divn_between (a b c E Q : nat) :
  a %/ E = Q -> (a + c) %/ E = Q -> b <= c -> (a + b) %/ E = Q.
Proof.
move=> Ha Hc Hbc.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- by rewrite -Hc leq_div2r // leq_add2l.
- by rewrite -Ha leq_div2r // leq_addr.
Qed.
