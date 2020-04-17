From extructures Require Export ord fmap fset.
From mathcomp Require Export ssrbool. (* TODO, strange *)
From mathcomp Require Import ssreflect ssrfun seq.
Require Import Lib.Extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Definition NMap T := {fmap nat -> T}.

Definition elementsm {A: Type} : NMap A -> list (nat * A).
Proof.
     exact (@FMap.fmval nat_ordType A _)
  ||
     idtac "ExStructures 0.1 legacy definition inactive";
     exact (@FMap.fmval nat_ordType A).
Defined.

(* RB: TODO: These lemmas, with their clean proofs, probably belong in CoqUtils. *)

Lemma mapm_empty: forall (T : ordType) (S S' : Type) (f : S -> S'),
  mapm f (@emptym T S) = emptym.
Proof.
    by move => T S S' f; apply /eq_fmap => n; rewrite emptymE.
Qed.

Lemma mapm_unionm (T T' : Type) (m1 m2 : NMap T) (f : T -> T') :
  mapm f (unionm m1 m2) = unionm (mapm f m1) (mapm f m2).
Proof.
  apply /eq_fmap => n. rewrite !(mapmE, unionmE). by case: (m1 n).
Qed.

Lemma filterm_predT (T : Type) (m : NMap T) :
  filterm (fun (k : nat) (_ : T) => true) m = m.
Proof.
  apply /eq_fmap => n. rewrite filtermE. by case: (m n).
Qed.

Lemma filterm_predF (T : Type) (m : NMap T) :
  filterm (fun (k : nat) (_ : T) => false) m = emptym.
Proof.
  apply /eq_fmap => n. rewrite filtermE. by case: (m n).
Qed.

Lemma eq_in_filterm (T:Type) f1 f2 (m : NMap T) :
  (forall k v, m k = Some v -> f1 k v = f2 k v) ->
  filterm f1 m = filterm f2 m.
Proof.
  move=> e. apply/eq_fmap=> k. rewrite 2!filtermE.
  case H : (m k) => [v|] //=.
  now rewrite e.
Qed.

Lemma fdisjoint_filterm_full (T T' : Type) (m1 : NMap T) (m2 : NMap T') :
  fdisjoint (domm m1) (domm m2) ->
  filterm (fun (k : nat) (_ : T) => k \notin domm m2) m1 = m1.
Proof.
  move => /fdisjointP H.
  rewrite -[RHS]filterm_predT. apply eq_in_filterm => k v kv.
  apply H. apply /dommP. by exists v.
Qed.

(* RB: TODO: Fix name! There is no disjointness condition here, even though its
   counterpart does have it. *)
Lemma fdisjoint_filterm_empty (T : Type) (m1 m2 : NMap T) :
  domm m1 = domm m2 ->
  filterm (fun (k : nat) (_ : T) => k \notin domm m1) m2 = emptym.
Proof.
  move => H.
  rewrite -[RHS](filterm_predF m2). apply eq_in_filterm => k v kv.
  apply negbTE. apply /negPn. rewrite H. apply /dommP. by exists v.
Qed.

(* RB: NOTE: This generalizes the above result. *)
Lemma fsubset_filterm_domm_emptym (T : Type) (m1 m2 : NMap T) :
  fsubset (domm m2) (domm m1) ->
  filterm (fun (k : nat) (_ : T) => k \notin domm m1) m2 = emptym.
Proof.
  move=> H.
  rewrite -[RHS](filterm_predF m2). apply eq_in_filterm => k v kv.
  apply negbTE. apply /negPn.
  apply /fsubsetP. apply H. apply /dommP. by exists v.
Qed.

Lemma fdisjoint_filterm_mapm_empty (T T' : Type) (m : NMap T) (f : T -> T') :
  filterm (fun (k : nat) (_ : T') => k \notin domm m) (mapm f m) = emptym.
Proof.
  rewrite -[RHS](filterm_predF (mapm f m)). apply eq_in_filterm => k v kv.
  rewrite -(domm_map f).
  apply negbTE. apply /negPn. apply /dommP. by exists v.
Qed.

Lemma fdisjoint_filterm_mapm_unionm (T T' : Type) (m1 m2 : NMap T) (f : T -> T') :
  fdisjoint (domm m1) (domm m2) ->
  filterm (fun (k : nat) (_ : T') => k \notin domm m2) (mapm f (unionm m1 m2)) =
  filterm (fun (k : nat) (_ : T') => k \notin domm m2) (mapm f m1).
Proof.
  move => Hdisjoint. rewrite mapm_unionm filterm_union.
  - by rewrite -(fdisjoint_filterm_full Hdisjoint) fdisjoint_filterm_mapm_empty unionm0.
  - by rewrite! domm_map.
Qed.

(* Filter has no effect on reads outside its domain. *)
Lemma getm_filterm_notin_domm :
  forall (T T' : Type) (m1 : NMap T) (m2 : NMap T') k,
    k \notin domm m1 ->
    (filterm (fun (k : nat) (_ : T') => k \notin domm m1) m2) k = m2 k.
Proof.
  intros T T' m1 m2 k Hnotin.
  rewrite filtermE Hnotin.
  destruct (m2 k) as [v |] eqn:Hcase;
    rewrite Hcase || idtac "ExStructures 0.1 legacy rewrite inactive";
    done.
Qed.

(* Set and filter commute if the key is outside the domain of filter. *)
Lemma setm_filterm_notin_domm :
  forall (T T' : Type) (m1 : NMap T) (m2 : NMap T') k (v : T'),
    k \notin domm m1 ->
    setm (filterm (fun (k : nat_ordType) (_ : T') => k \notin domm m1) m2) k v =
    filterm (fun (k : nat_ordType) (_ : T') => k \notin domm m1) (setm m2 k v).
Proof.
  intros T T' m1 m2 k v Hnotin.
  apply /eq_fmap => n.
  rewrite filtermE !setmE filtermE.
  destruct (eqtype.eq_op n k) eqn:Hcase.
  - pose proof eqtype.eqP Hcase; subst n. now rewrite Hnotin.
  - reflexivity.
Qed.

(* RB: NOTE: filterm_union, a related lemma, does not include the final 'm' in
   its name. *)
(* JT: this proof needs a lot of cleaning *)
Lemma filterm_domm_unionm (T T' : Type) (m : NMap T) (m1 m2 : NMap T') :
  filterm (fun (k : nat) (_ : T) => k \notin domm m1)
          (filterm (fun (k : nat) (_ : T) => k \notin domm m2) m) =
  filterm (fun (k : nat) (_ : T) => k \notin domm (unionm m1 m2)) m.
Proof.
  apply /eq_fmap => n.
  rewrite !filtermE.
  unfold obind. unfold oapp.
  destruct (m n) eqn:Hcase;
    rewrite Hcase || idtac "ExStructures 0.1 legacy rewrite inactive".
  -  destruct (n \notin domm m2) eqn:Hcase'; rewrite Hcase'.
     + destruct (n \notin domm m1) eqn:Hcase''; rewrite Hcase''.
       ++ assert (n \notin domm (unionm m1 m2)).
          rewrite domm_union.
          apply /fsetUP /orP.
          apply Bool.negb_true_iff in Hcase'; apply Bool.negb_true_iff in Hcase''.
          rewrite Hcase' Hcase''. by [].
            by rewrite H.
       ++ assert (n \notin domm (unionm m1 m2) = false).
          rewrite domm_union.
          apply /fsetUP /orP.
          apply Bool.negb_false_iff in Hcase''; rewrite Hcase''. by [].
          by rewrite H.
    + destruct (n \notin domm (unionm m1 m2)) eqn:Hcase''; rewrite Hcase''.
      ++ rewrite domm_union in Hcase''.
         move: Hcase''. move=> /fsetUP Hcase''.
         destruct (n \in domm m2) eqn:Hcase'''.
         +++ move: Hcase''. move=> /orP. rewrite orbC. simpl. by [].
         +++ by [].
      ++ by reflexivity.
  - by reflexivity.
Qed.

(* CA: not really needed *)
Lemma mapm_id : forall (T : Type) (i: NMap T), mapm id i = i.
Proof.
  move=> T i. apply /eq_fmap => n.
  rewrite mapmE. unfold omap, obind, oapp.
  remember (i n) as v; simpl in *;
    rewrite <- Heqv || idtac "ExStructures 0.1 legacy rewrite inactive".
  now destruct v.
Qed.

(* needed in the proof of domm_filterm_fdisjoint_unionm *)
Lemma filterm_id : forall (T : Type) (i : NMap T) p,

    domm (filterm p i) = domm (filterm p (mapm id i)).
Proof.
  move => T i. by rewrite mapm_id.
Qed.

Lemma domm_filterm_fdisjoint_unionm
      (T T' : Type) (i1 i2 : NMap T) (m : NMap T') :
  fdisjoint (domm i1) (domm i2) ->
  domm m = domm (unionm i1 i2) ->
  domm (filterm (fun (k : nat) (_ : T') => k \notin domm i2) m) = domm i1.
Proof.
  rewrite domm_union => Hdisjoint Hunion.
  have HH: domm (filterm (fun (k : nat) (_ : T') => k \notin domm i2) m) =
           domm (filterm (fun (k : nat) (_ : T) => k \notin domm i2) (unionm i1 i2))
  by admit.
  rewrite HH filterm_id fdisjoint_filterm_mapm_unionm; auto.
  rewrite -filterm_id fdisjoint_filterm_full; auto.
  Grab Existential Variables.
  (* have HHH: domm m = (domm i1 :|: domm i2)%fset -> exists m1 m2, m = unionm m1 m2 /\ *)
  (*                                                          domm m1 = domm i1 /\ domm m2 = domm i2 *)
  (*       by admit. *)
  (* specialize (HHH Hunion). destruct HHH as [m1 [m2 [Hu [H1 H2]]]]. *)
  (* subst. Search _ domm filterm unionm. *)
  rewrite filterm_union.
  rewrite (@fdisjoint_filterm_empty T i2 i2). rewrite unionm0.
  rewrite (@fdisjoint_filterm_full T T).
  have HHH: exists m1 m2, m = unionm m1 m2 /\ domm m1 = domm i1 /\ domm m2 = domm i2 by admit.
  destruct HHH as [m1 [m2 [Hu [H1 H2]]]].
  rewrite Hu. rewrite <- H2.
  rewrite filterm_id.
  rewrite fdisjoint_filterm_mapm_unionm. rewrite <- filterm_id.
  rewrite fdisjoint_filterm_full.

  assumption. rewrite H1 H2; assumption. rewrite H1 H2; assumption.
  assumption.
  reflexivity. assumption.
  Grab Existential Variables.
  exists (filterm (fun (k : nat) (_ : T') => in_mem k (mem (domm i1))) m).
  exists (filterm (fun (k : nat) (_ : T') => in_mem k (mem (domm i2))) m).
  (* exists (filterm (fun (k : nat) (_ : T') => k \notin domm i1) m). *)
  split; try split.
Admitted.

Lemma domm_eq_filterm (T T' T'' : Type) (i1 : NMap T) (m1 : NMap T') (m2 : NMap T''):
    domm m1 = domm m2 ->
    domm (filterm (fun (k : nat) (_ : T') => k \notin domm i1) m1) =
    domm (filterm (fun (k : nat) (_ : T'') => k \notin domm i1) m2).
Proof.
  move=> H.
  set (fn := fun (k0 : nat) (_ : T') => k0 \notin domm i1) in *.
  set (fn' := fun (k0 : nat) (_ : T'') => k0 \notin domm i1) in *.

  (* Attempt *)
  apply /eq_fset => k.
  (* subst fn. *)
  destruct (k \notin domm i1) eqn:Heq;
    destruct (k \in domm (filterm fn m1)) eqn:Heq1;
    destruct (k \in domm (filterm fn' m2)) eqn:Heq2;
    try now auto.
  - subst fn fn'.
    rewrite mem_domm in Heq1.
    erewrite getm_filterm_notin_domm in Heq1; last eauto.
    rewrite mem_domm in Heq2.
    erewrite getm_filterm_notin_domm in Heq2; last eauto.
    (* contradiction: the domain of m1 and m2 is the same *)
    move: Heq1 Heq2.
    rewrite -2!mem_domm.
    rewrite H; move=> ? ?; eauto.
  - subst fn fn'.
    rewrite mem_domm in Heq1.
    erewrite getm_filterm_notin_domm in Heq1; last eauto.
    rewrite mem_domm in Heq2.
    erewrite getm_filterm_notin_domm in Heq2; last eauto.
    move: Heq1 Heq2; rewrite -2!mem_domm H => ? ?; eauto.
  - subst fn fn'.
    rewrite mem_domm in Heq1; rewrite mem_domm in Heq2.
    move: Heq1 Heq2. rewrite 2!filtermE. unfold obind. unfold oapp.
    destruct (m1 k) eqn:H';
      rewrite H' || idtac "ExStructures 0.1 legacy rewrite inactive";
      rewrite Heq => //=.
  - subst fn fn'.
    rewrite mem_domm in Heq1; rewrite mem_domm in Heq2.
    move: Heq1 Heq2. rewrite 2!filtermE. unfold obind. unfold oapp.
    destruct (m2 k) eqn:H';
      rewrite H' || idtac "ExStructures 0.1 legacy rewrite inactive";
      rewrite Heq => //=.
Qed.


Lemma domm_filterm_partial_memory
      (T T' : Type) (i1 i2 : NMap T) (m0 m1 m2 : NMap T') :
  fdisjoint (domm i1) (domm i2) ->
  domm m0 = domm m1 ->
  domm m2 = domm (unionm i1 i2) ->
  filterm (fun (k : nat) (_ : T') => k \notin domm i1) m0 =
  filterm (fun (k : nat) (_ : T') => k \notin domm i1) m2 ->
  domm (filterm (fun (k : nat) (_ : T') => k \notin domm i1) m1) = domm i2.
Proof.
  move=> H H0 H1 H2.
  symmetry in H0.
  rewrite (domm_eq_filterm _ H0).
  rewrite H2.
  rewrite (domm_eq_filterm _ H1).
  rewrite filterm_union; last assumption.
  rewrite fdisjoint_filterm_empty; last reflexivity.
  rewrite fdisjoint_filterm_full. reflexivity.
  now rewrite fdisjointC.
Qed.


Lemma filterm_partial_memory_fsubset
      (T T' : Type) (i1 i2 : NMap T) (m0 m1 m2 : NMap T') :
  fdisjoint (domm i1) (domm i2) ->
  domm m0 = domm m1 ->
  domm m2 = domm (unionm i1 i2) ->
  filterm (fun (k : nat) (_ : T') => k \notin domm i1) m0 =
  filterm (fun (k : nat) (_ : T') => k \notin domm i1) m2 ->
  fsubset (domm m1) (domm m2).
Proof.
  move => disj_i1_i2 m0_eq_m2 m2_eq_union Hfilter.
  rewrite m2_eq_union -m0_eq_m2 domm_union.
  apply (* /fsubsetU /orP. *) /fsubsetP => x Hx.
  assert (x \in (domm i1) \/ x \notin (domm i1)).
  { apply /orP. by destruct (x \in domm i1). } (* CA: do we have classical reasoning? *)   
  case: H => H.  
  move: H. apply /fsubsetP /fsubsetU /orP. 
  left. by apply: fsubsetxx.
      
  have x_in_i2 : x \in domm i2.
  { have x_in_m2 : x\in domm m2 by admit.
    move: x_in_m2.
    rewrite m2_eq_union domm_union.
    case /fsetUP => [| //].
    move: H => /negP //. 
  } (*CA: by Hfilter deduce x \in domm m2
               then by m2_eq_union, x \in domm i1 \/x \in domm i2 
               together with H we get x \in domm i2
              *)
   move: x_in_i2. apply /fsubsetP /fsubsetU /orP.    
   right. by apply: fsubsetxx. 
Admitted.     
    
(* RB: NOTE: This is not a map lemma proper. More generally, absorption on
   arbitrary subsets. *)
Lemma fsetU1in (T : ordType) (x : T) (s : {fset T}) :
  x \in s -> (x |: s)%fset = s.
Proof.
  rewrite -eq_fset.
  move => x_in_s x0.
  case: (@in_fsetU1 T x0 x s) => H0.
  destruct (x0 \in s) eqn: Hx0.
     by rewrite H0 orbT.
  rewrite H0 orbF.
  destruct (eqtype.eq_op x0 x) eqn: Hx0_x; auto.
    rewrite -(eqtype.eqP Hx0_x) in x_in_s.
    now inversion x_in_s.
Qed.

(* notation filtermI isn't quite right since idempotent (in SSReflect
   conventions) applies to binary operators *)
(* Since a function is pure in coq, this should hold *)
Lemma filtermIdempotent (T : ordType) (S : Type) p (m : {fmap T -> S}) :
  filterm p (filterm p m) = filterm p m.
Proof.
  apply/eq_fmap=> k; rewrite !filtermE.
  case get_k: (m k)=> [v|] //=.
  case: ifP => //= pkv ; by rewrite pkv.
Qed.

Lemma domm_map_zip_unzip_same_length_is_equal (T : ordType) (U V : Type) (l : list (T * U)) (l' : list V) :
  length l = length l' ->
  domm (mkfmap (T := T) (seq.zip (seq.unzip1 l) l')) = domm (mkfmap (T := T) l).
Proof.
  generalize dependent l'.
  induction l; intros l' H.
  - now destruct l'.
  - destruct l'; inversion H.
    simpl.
    rewrite 2!domm_set. rewrite IHl. reflexivity.
    assumption.
Qed.
