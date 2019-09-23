(* Complements to the standard Coq library, ssreflect, and Coq utils *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From extructures Require Import ord fset fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition Z_eqMixin := EqMixin Z.eqb_spec.
Canonical Z_eqType := Eval hnf in EqType Z Z_eqMixin.

Section FMap.

Variables (T : ordType) (S S' : Type).
Implicit Types (m : {fmap T -> S}) (x : T).

(* FIXME: Move to CoqUtils *)

Lemma domm_mapi (f : T -> S -> S') m : domm (mapim f m) = domm m.
Proof.
by apply/eq_fset=> x; rewrite !mem_domm mapimE; case: (m x).
Qed.

Lemma domm_map (f : S -> S') m : domm (mapm f m) = domm m.
Proof. exact: domm_mapi. Qed.

Lemma unionmK m1 m2 : filterm (fun k _ => m1 k) (unionm m1 m2) = m1.
Proof.
apply/eq_fmap=> k; rewrite filtermE unionmE.
by case: (m1 k) (m2 k)=> //= - [].
Qed.

Lemma emptymP m : reflect (m = emptym) (domm m == fset0).
Proof.
apply/(iffP eqP); last by move=> ->; rewrite domm0.
move=> e; apply/eq_fmap => x; rewrite emptymE.
by case: (altP (@dommPn T S m x))=> //; rewrite e.
Qed.

Lemma domm_mkfmap' (kvs : seq (T * S)) : domm (mkfmap kvs) = fset (unzip1 kvs).
Proof.
  rewrite -eq_fset.
  (* would be nice to use domm_mkfmap. would it be possible to use it with in_fset ? *)
  (* for the time being, taking example on proof of domm_mkfmap *)

  move=> k; rewrite mem_domm.
  elim: kvs => [|kv kvs IH] //=.
  - rewrite <- fset0E. apply (in_fset0 k).
  - rewrite !inE setmE fset_cons in_fsetU1.
    by case : (_ == _).
Qed.

End FMap.

Section Lists.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [::] => True
  | x :: l' => P x /\ All P l'
  end.

Lemma All_cat {T : Type} (P : T -> Prop) (s1 s2 : seq T) :
  All P (s1 ++ s2) <-> All P s1 /\ All P s2.
Proof.
elim: s1=> /= [|x s1 IH]; first by intuition.
by rewrite IH and_assoc.
Qed.

Fixpoint list_upd {T : Type} (data : list T) (offset : nat) (x : T) : option (list T) :=
  match data with
  | [::] => None (* store out of bounds *)
  | x' :: rest =>
    match offset with
    | O => Some (x :: rest)
    | S offset' =>
      match list_upd rest offset' x with
      | Some rest' => Some (x' :: rest')
      | None       => None (* propagate store out of bounds *)
      end
    end
  end.

Lemma list_upd_nth_error_same {T : Type}:
  forall (blk:seq T) o v blk',
    list_upd blk o v = Some blk' ->
    List.nth_error blk' o = Some v.
Proof.
elim=> [|x blk IH] //= [? ? [<-]|o] //=.
by move=> v blk'; case e: list_upd=> [blk''|] //= [<-]; eauto.
Qed.

Lemma list_upd_nth_error_other {T : Type}:
  forall (blk : seq T) o v o' blk',
    list_upd blk o v = Some blk' ->
    o <> o' ->
    List.nth_error blk' o' = List.nth_error blk o'.
Proof.
elim=> [|x blk IH] //= [? [|o'] ? [<-] //|o].
move=> v [|o'] blk'; case e: list_upd=> [blk''|] //= [<-] // ne.
by apply: (IH _ _ _ _ e); congruence.
Qed.

Lemma size_length {T : Type}:
  forall l:seq T, size l = length l.
Proof. reflexivity. Qed.

Lemma nseq_add {T:Type} (n1 n2:nat) (x:T) : nseq (n1+n2) x = nseq n1 x ++ nseq n2 x.
Proof.
    by elim: n1 => //= n1 IHn1 ; rewrite IHn1.
Qed.

Lemma cat_app {T:Type} (l1 l2:list T) :
  app l1 l2 = cat l1 l2.
Proof. by elim: l1. Qed.

(* Coq or ssr conventions (cat/app, length/size) ? *)
Lemma combine_cat {A B : Type} : forall (beg1 end1:list A), forall (beg2 end2:list B),
      size beg1 = size beg2 ->
      (* Not useful *)
      (* size end1 = size end2 -> *)
      combine (beg1 ++ end1) (beg2 ++ end2) = combine beg1 beg2 ++ combine end1 end2.
Proof.
  induction beg1 as [|a1 beg1' IHbeg1'] => end1 beg2 end2 Hbeg.
  - by inversion Hbeg as [Hsize0] ; symmetry in Hsize0 ;
      apply size0nil in Hsize0 ; subst.
  - destruct beg2 as [| a2 beg2'] => //.
    inversion Hbeg as [Hsize]. apply (IHbeg1' end1 _ end2) in Hsize => /=.
      by rewrite Hsize.
Qed.

Lemma In_in (T : eqType) (x : T) (s : seq T) : x \in s <-> List.In x s.
Proof.
by elim: s=> //= x' s <-; rewrite inE; split => [/orP [/eqP ->|]|[->|->]];
eauto; rewrite ?eqxx ?orbT.
Qed.

(* FIXME: This can be expressed in terms of drop and find. *)
Fixpoint drop_while {T : Type} (a : pred T) (s : seq T) :=
  if s is x :: s' then
    if a x then drop_while a s' else s
  else [::].

Lemma eq_drop_while T (a1 a2 : T -> bool) :
  a1 =1 a2 -> drop_while a1 =1 drop_while a2.
Proof. by move=> e_a; elim=> [//|x s /= ->]; rewrite e_a. Qed.

Lemma rev_inj {T:Type} : injective (@rev T).
Proof. by apply (can_inj revK). Qed.

Lemma all_subseq {T:eqType} (s ss : seq T) (a : pred T) :
  all a s -> subseq ss s -> all a ss.
Proof.
    by move => /all_filterP <- ; rewrite subseq_filter => /andP [? _].
Qed.

End Lists.
