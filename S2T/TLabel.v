Require Import Common.Definitions.
Require Import Common.Values.
Require Import Intermediate.Machine.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Require Import Coq.ZArith.ZArith.
Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.

Module TLabel.

Notation tcode := (seq (Transitional.instr * mem_tag)).

Definition is_tlabel (l : label) (x : Transitional.instr * mem_tag) : bool :=
  if x.1 is Transitional.TrLabel (inl l') then Nat.eqb l l' else false.

Lemma is_tlabel_here l tg :
  is_tlabel l (Transitional.TrLabel (inl l), tg).
Proof. by rewrite /is_tlabel /= Nat.eqb_refl. Qed.


Fixpoint tfaux (cd : tcode) (l : label) (o : Z) : option Z :=
  match cd with
  | [::] => None
  | (Transitional.TrLabel (inl l'), _) :: cd' =>
      if Nat.eqb l l' then Some o else tfaux cd' l (1 + o)%Z
  | _ :: cd' => tfaux cd' l (1 + o)%Z
  end.

Lemma find_label_tfaux cd l : Transitional.find_label cd l = tfaux cd l 0%Z.
Proof.
  rewrite /Transitional.find_label.
  elim: cd (0%Z) => [|[i tg] cd IH] o //=.
  by case: i => [|[l'|[c' p']]|v r|r1 r2|op r1 r2 r3|r1 r2|r1 r2|r1 r2
                |r l0|r|l0|lp|] /=; rewrite -?IH; case: cd {IH}.
Qed.


Lemma tfaux_cat_notin pre l tg post o :
  count (is_tlabel l) pre = 0 ->
  tfaux (pre ++ (Transitional.TrLabel (inl l), tg) :: post) l o
  = Some (Z.of_nat (size pre) + o)%Z.
Proof.
  elim: pre o => [|[i tg'] pre IH] o Hc.
  - by rewrite /= Nat.eqb_refl ?Z.add_0_l.
  - have Ho : (Z.of_nat (size ((i, tg') :: pre)) + o)%Z
            = (Z.of_nat (size pre) + (1 + o))%Z
      by rewrite [size (_ :: _)]/= Nat2Z.inj_succ; lia.
    have [Hh Ht] : is_tlabel l (i, tg') = false /\ count (is_tlabel l) pre = 0.
    { move: Hc => /eqP. rewrite /= addn_eq0 => /andP [H1 /eqP H2].
      split; last exact: H2.
      by move: H1; case: (is_tlabel l (i, tg')). }
    rewrite Ho cat_cons -(IH (1 + o)%Z Ht).
    move: {Hc Ho} Hh; rewrite /is_tlabel /=.
    by case: i => [|[l'|[c' p']]|v r|r1 r2|op r1 r2 r3|r1 r2|r1 r2|r1 r2
                  |r l0|r|l0|lp|] //= ->.
Qed.

Lemma find_label_at pre l tg post :
  count (is_tlabel l) pre = 0 ->
  Transitional.find_label (pre ++ (Transitional.TrLabel (inl l), tg) :: post) l
  = Some (Z.of_nat (size pre)).
Proof.
  move=> H. rewrite find_label_tfaux tfaux_cat_notin //.
  by rewrite Z.add_0_r.
Qed.

Lemma find_label_uniq pre l tg post :
  count (is_tlabel l)
        (pre ++ (Transitional.TrLabel (inl l), tg) :: post) <= 1 ->
  Transitional.find_label (pre ++ (Transitional.TrLabel (inl l), tg) :: post) l
  = Some (Z.of_nat (size pre)).
Proof.
  rewrite count_cat /= is_tlabel_here add1n addnS ltnS leqn0 addn_eq0.
  by move=> /andP [/eqP H _]; exact: find_label_at.
Qed.

Lemma find_label_in_comp_at (cde : Transitional.code) C C_code pre l tg post :
  getm cde C = Some C_code ->
  C_code = pre ++ (Transitional.TrLabel (inl l), tg) :: post ->
  count (is_tlabel l) C_code <= 1 ->
  Transitional.find_label_in_comp cde C l
  = Some (C, 0, Z.of_nat (size pre)).
Proof.
  move=> Hg EC Hu. rewrite /Transitional.find_label_in_comp Hg EC.
  have Hu' : count (is_tlabel l)
               (pre ++ (Transitional.TrLabel (inl l), tg) :: post) <= 1
    by rewrite -EC.
  by rewrite (find_label_uniq Hu').
Qed.

End TLabel.
