(* EncodeCode.v — [encode_code] structure lemmas extracted from RecompositionInit (program-generic;
   global Merged/Instance defs only). [word_of_nat_inj] = the one numeric assumption. *)
Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.SmallstepUB.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq fintype ssralg ssrint.
From mathcomp Require Import zify.
From CoqUtils Require Import hseq word.
From extructures Require Import fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Import MicroPolicies.Int32.
Require Import MicroPolicies.WordExtra.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Equality.
From Coq Require Import Btauto.
Require Import MicroPolicies.Utils.
Import DoNotation.
Import Types.

Section EncodeCode.
Hypothesis word_of_nat_inj: forall a b,
    a < 2^(word_size mt) -> b < 2^(word_size mt) ->
    word_of_nat (k := word_size mt) a = word_of_nat b -> a = b.

Lemma foldl_unionm_In: forall {T : ordType} {S : Type} (ms : seq {fmap T -> S}) k v,
  foldl unionm emptym ms k = Some v ->
  exists mi, List.In mi ms /\ mi k = Some v.
Proof.
  intros T0 S0 ms. induction ms as [| m0 ms IH] using last_ind.
  - intros k0 v0. simpl. rewrite emptymE. discriminate.
  - intros k0 v0. rewrite foldl_rcons.
    rewrite unionmE.
    case Hacc: (foldl unionm emptym m0 k0) => [v' |].
    + (* accumulator has a value — it came from ms *)
      move=> [<-].
      destruct (IH _ _ Hacc) as [mi [Hmi Hmi_k]].
      exists mi. split; [| exact Hmi_k].
      rewrite -cats1.
      apply List.in_or_app. left. exact Hmi.
    + (* accumulator is None — value comes from m0 *)
      move=> Hm0. simpl in Hm0.
      eexists; split; [| eassumption].
      rewrite -cats1.
      apply List.in_or_app. right. left. reflexivity.
Qed.

Lemma In_unzip2_exists: forall {T: ordType} {S: Type} (m: {fmap T -> S}) v,
    List.In v (unzip2 m) -> exists k, List.In (k, v) m.
Proof.
  intros T0 S0 m v Hin.
  destruct m as [s Hs]. simpl in *.
  induction s as [| [k0 v0] rest IH].
  - contradiction.
  - simpl in Hin. destruct Hin as [<- | Hin].
    + exists k0. left. reflexivity.
    + destruct (IH) as [k1 Hk1].
      simpl in Hs. eapply path.path_sorted; eauto.
      eauto.
      exists k1. right. exact Hk1.
Qed.

Lemma In_fmap_getm: forall {T: ordType} {S: Type} (m: {fmap T -> S}) k v,
    List.In (k, v) m -> m k = Some v.
Proof.
  intros T0 S0 m k v Hin.
  destruct m as [s Hs]. simpl in *.
  (* s is a sorted list of (T0 * S0) pairs, Hin : List.In (k, v) s *)
  (* getm_def scans left-to-right: if k == p.1 then Some p.2 else recurse *)
  (* Since s is sorted with unique keys, (k, v) in s means getm_def finds it *)
  induction s as [| [k0 v0] rest IH].
  - contradiction.
  - simpl. simpl in Hin. destruct Hin as [Heq | Hin].
    + injection Heq => <- <-.
      rewrite /getm. simpl. rewrite eqxx. reflexivity.
    + rewrite /getm. simpl.
      case Hkeq: (k == k0).
      * (* k = k0 but (k, v) is in rest — contradicts sorted/unique *)
        move/eqP : Hkeq => Hkeq. subst k0.
        exfalso.
        have Hpath := Hs.
        (* path.sorted Ord.lt (k :: unzip1 rest) — since unzip1 ((k,v0)::rest) = k :: unzip1 rest *)
        simpl in Hpath.
        (* Hpath should be: path Ord.lt k (unzip1 rest) *)
        (* From (k, v) ∈ rest, k ∈ unzip1 rest *)
        have Hkin: List.In k (unzip1 rest).
        { clear -Hin. induction rest as [| [k1 v1] rest' IH].
          - contradiction.
          - simpl in *. destruct Hin as [[= -> ->] | Hin].
            + left. reflexivity.
            + right. exact (IH Hin). }
        (* Convert to \in *)
        apply Extra.In_in in Hkin.
        (* Hs gives path Ord.lt k (unzip1 rest) *)
        simpl in Hs.
        have := path.order_path_min (@Ord.lt_trans T0) Hs.
        move=> /allP /(_ _ Hkin).
        by rewrite Ord.ltxx.
      * eapply IH. eauto.
        Unshelve.
        simpl in Hs. eapply path.path_sorted. eauto.
Qed.

Lemma mapk_Some: forall {T T' : ordType} {S : Type}
                   (f : T -> T') (m : {fmap T -> S}) k' v,
  Tmp.mapk f m k' = Some v -> exists k, f k = k' /\ m k = Some v.
Proof.
  intros T0 T0' S0 f m k' v.
  unfold Tmp.mapk.
  intros H. apply foldl_unionm_In in H as [mi [Hmi Hmi_k']].
  (* Hmi : List.In mi (unzip2 (mapim (fun k x => mkfmap [:: (f k, x)]) m)) *)
  (* Hmi_k' : mi k' = Some v *)
  set mm := mapim (fun k x => mkfmap [:: (f k, x)]) m in Hmi.
  destruct (In_unzip2_exists Hmi) as [k0 Hpair].
  apply In_fmap_getm in Hpair.
  (* move/getmP : Hpair => Hpair. *)
  (* Hpair : mm k0 = Some mi *)
  rewrite /mm mapimE in Hpair.
  destruct (m k0) as [x0 |] eqn:Hmk0; simpl in Hpair; [| discriminate].
  injection Hpair => Hmi_eq.
  (* mi = mkfmap [:: (f k0, x0)] *)
  rewrite -Hmi_eq /= in Hmi_k'.
  rewrite setmE in Hmi_k'.
  (* rewrite -Hmi_eq mkfmapE /= in Hmi_k'. *)
  (* Hmi_k' : (if k' == f k0 then Some x0 else None) = Some v *)
  case: ifP Hmi_k' => [/eqP Hfk | //].
  move=> [<-].
  exists k0. split.
  - symmetry. exact Hfk.
  - exact Hmk0.
Qed.

Lemma getm_In: forall {T : ordType} {S : Type} (m : {fmap T -> S}) k v,
    m k = Some v -> List.In (k, v) m.
Proof.
  move=> T0 S0 [s Hs] k v. rewrite /getm /=. clear Hs. elim: s => [|[k0 v0] s IH] //=.
  case Hkeq: (k == k0).
  - move/eqP: Hkeq => ->. by move=> [->]; left.
  - by move=> H; right; apply: IH.
Qed.

Lemma domm_foldl_unionm_In: forall {T : ordType} {S : Type} (ms : seq {fmap T -> S}) mi j,
    List.In mi ms -> j \in domm mi -> j \in domm (foldl unionm emptym ms).
Proof.
  intros T0 S0 ms. induction ms as [| ms0 m0 IH] using last_ind.
  - intros mi j Hin. contradiction.
  - intros mi j Hin Hj. rewrite foldl_rcons domm_union in_fsetU.
    move: Hin; rewrite -cats1 => Hin.
    apply List.in_app_or in Hin. case: Hin => [Hin | Hin].
    + apply/orP; left. exact: (IH mi j Hin Hj).
    + apply/orP; right. move: Hin => /= [Heq | F]; [subst mi; exact Hj | exact (False_ind _ F)].
Qed.

Lemma mapk_Some_inv: forall {T T' : ordType} {S : Type} (f : T -> T') (m : {fmap T -> S}) k v,
  {in domm m &, injective f} -> m k = Some v -> Tmp.mapk f m (f k) = Some v.
Proof.
  move=> T0 T0' S0 f m k v Hinj Hmk.
  have Hkdom : k \in domm m by apply/dommP; exists v.
  have Hfkdom : f k \in domm (Tmp.mapk f m).
  { rewrite /Tmp.mapk.
    apply: (domm_foldl_unionm_In (mi := mkfmap [:: (f k, v)])).
    - have Hmm : (mapim (fun k0 x => mkfmap [:: (f k0, x)]) m) k = Some (mkfmap [:: (f k, v)]).
      { by rewrite mapimE Hmk. }
      have Hpair := getm_In Hmm.
      exact: (List.in_map snd _ _ Hpair).
    - by rewrite (domm_mkfmap [:: (f k, v)]) in_cons eqxx. }
  move/dommP: Hfkdom => [v' Hv']. rewrite Hv'.
  destruct (mapk_Some Hv') as [k0 [Hfk0 Hmk0]].
  have Hk0dom : k0 \in domm m by apply/dommP; exists v'.
  have Hk0k : k0 = k by apply: Hinj; [exact Hk0dom | exact Hkdom | exact Hfk0].
  subst k0. rewrite Hmk0 in Hmk. by case: Hmk => ->.
Qed.

Lemma nth_map_Some_nth_error: forall {A} (l : list A) n v,
    nth None (map Some l) n = Some v -> nth_error l n = Some v.
Proof.
  intros A l. induction l as [| x xs IH]; intros n v.
  - destruct n; simpl; discriminate.
  - destruct n; simpl.
    + move=> [->]. reflexivity.
    + exact (IH n v).
Qed.

Lemma nth_error_Some_ex: forall {A} (l : list A) n,
  n < length l -> exists v, nth_error l n = Some v.
Proof.
  intros A l. induction l as [| x xs IH]; intros n Hlt.
  - by [].
  - destruct n.
    + exists x. reflexivity.
    + simpl in Hlt. apply IH. exact Hlt.
Qed.

Lemma nth_error_nth_map_Some: forall {A} (l : list A) n v,
  nth_error l n = Some v -> nth None (map Some l) n = Some v.
Proof.
  intros A l. induction l as [| x xs IH]; intros n v.
  - destruct n; simpl; discriminate.
  - destruct n; simpl.
    + move=> [->]. reflexivity.
    + exact (IH n v).
Qed.

Lemma encode_code_foldr_counter: forall cde lp offset,
  (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
    (encode_instr_atom x lp (offset - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) cde).2
  = size cde.
Proof.
  intros cde. induction cde as [| [i0 t0] cde' IH]; intros lp offset.
  - reflexivity.
  - simpl. f_equal. exact (IH lp offset).
Qed.

Lemma encode_code_foldr_nth: forall cde lp offset n v,
  nth_error (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
    (encode_instr_atom x lp (offset - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) cde).1 n = Some v ->
  exists i t, nth_error cde n = Some (i, t) /\
              taga v = t /\
              vala v = encode_instr_mp (instr_merged_to_mp i lp (offset - 1 - (size cde - 1 - n))).
Proof.
  intros cde. induction cde as [| [i0 t0] cde' IH]; intros lp offset n v Hnth.
  - simpl in Hnth. destruct n; discriminate.
  - simpl in Hnth.
    destruct n as [| n'].
    + set acc := (foldr _ _ cde') in Hnth.
      simpl in Hnth. injection Hnth => <-.
      exists i0, t0.
      split; [reflexivity |]. split.
      * unfold encode_instr_atom. simpl. reflexivity.
      * unfold encode_instr_atom, encode_instr. simpl.
        (* pos = offset - 1 - acc.2 = offset - 1 - size cde' (by foldr_counter) *)
        (* conclusion wants: offset - 1 - (size (i0,t0 :: cde') - 1 - 0) = offset - 1 - size cde' *)
        rewrite subn0. simpl size.
        replace ((size cde').+1 - 1) with (size cde').
        2: { rewrite subn1 //=. }
        have -> : acc.2 = size cde' by exact (encode_code_foldr_counter cde' lp offset).
        reflexivity.
    + simpl in Hnth.
      destruct (IH lp offset n' v Hnth) as [i' [t' [Hin' [Htag' Hval']]]].
      exists i', t'. split; [exact Hin' |]. split; [exact Htag' |].
      (* Hval' has: offset - 1 - (size cde' - 1 - n') *)
      (* need: offset - 1 - (size (i0,t0 :: cde') - 1 - n'.+1) *)
      (* size (i0,t0 :: cde') - 1 - n'.+1 = (size cde').+1 - 1 - n'.+1 = size cde' - 1 - n' *)
      simpl size.
      replace (offset - 1 - ((size cde').+1 - 1 - n'.+1)) with (offset - 1 - (size cde' - 1 - n')).
      exact Hval'.
      { replace (size cde' - 1 - n') with (((size cde').+1 - 1 - n'.+1)); auto.
        rewrite !subn1. simpl. rewrite -addn1 addnC. rewrite subnDA. rewrite subn1. auto. }
Qed.

Lemma encode_code_foldr_size: forall cde lp offset,
  size (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
    (encode_instr_atom x lp (offset - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) cde).1
  = size cde.
Proof.
  intros cde. induction cde as [| [i0 t0] cde' IH]; intros lp offset.
  - simpl. reflexivity.
  - simpl. f_equal. exact (IH lp offset).
Qed.

Lemma encode_code_nth: forall cde pc0 n v,
  pc0 + size cde < 2 ^ (word_size mt) ->
  let list := (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
    (encode_instr_atom x
      (fun l default => match findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) cde
       with Some m => pc0 + m | None => if l == alloc_label then l else default end)
      (pc0 + size cde - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) cde).1 in
  nth_error list n = Some v ->
  encode_code cde pc0 (word_of_nat (n + pc0)) = Some v.
Proof.
  intros cde pc0 n v Hbound list Hnth.
  unfold encode_code.
  apply nth_error_nth_map_Some in Hnth.
  simpl in *.
  rewrite -fmap_of_seqE in Hnth.
  eapply mapk_Some_inv with (f := (fun x : nat => word_of_nat (x + pc0)))
    in Hnth; eauto.
  (* on-domm injectivity of the position relabel: positions are < size cde, so a+pc0,b+pc0
     stay < 2^word and word_of_nat is injective there. *)
  move=> a b Ha Hb H.
  have Hsz : size list = size cde by exact: encode_code_foldr_size.
  have Halt : a < size cde.
  { rewrite -Hsz ltnNge; apply/negP => Hge.
    move: Ha; rewrite mem_domm fmap_of_seqE.
    rewrite nth_default; last by rewrite size_map. by []. }
  have Hblt : b < size cde.
  { rewrite -Hsz ltnNge; apply/negP => Hge.
    move: Hb; rewrite mem_domm fmap_of_seqE.
    rewrite nth_default; last by rewrite size_map. by []. }
  have Ha2 : a + pc0 < 2 ^ (word_size mt).
  { rewrite addnC. apply: (ltn_trans _ Hbound). by rewrite ltn_add2l. }
  have Hb2 : b + pc0 < 2 ^ (word_size mt).
  { rewrite addnC. apply: (ltn_trans _ Hbound). by rewrite ltn_add2l. }
  have Hab := word_of_nat_inj Ha2 Hb2 H.
  lia.
Qed.

Lemma encode_code_nth_inv: forall cde pc0 w v,
  encode_code cde pc0 w = Some v ->
  exists n, w = word_of_nat (n + pc0) /\
  n < size cde /\
  nth_error (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
    (encode_instr_atom x
      (fun l default => match findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) cde
       with Some m => pc0 + m | None => if l == alloc_label then l else default end)
      (pc0 + size cde - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) cde).1 n = Some v.
Proof.
  intros cde pc0 w v Henc.
  unfold encode_code in Henc.
  apply mapk_Some in Henc. destruct Henc as [k [Hk Hfmap]].
  exists k. split.
  - symmetry. exact Hk.
  - rewrite fmap_of_seqE in Hfmap.
    apply nth_map_Some_nth_error in Hfmap.
    split.
    + have Hsize := encode_code_foldr_size cde
        (fun l default => match findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) cde
         with Some m => pc0 + m | None => if l == alloc_label then l else default end)
        (pc0 + size cde).
      rewrite -Hsize.
      apply /ltP.
      apply List.nth_error_Some. intros Habs.
      rewrite Habs in Hfmap. congruence.
    + exact Hfmap.
Qed.

End EncodeCode.
