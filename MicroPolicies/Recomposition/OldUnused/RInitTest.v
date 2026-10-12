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

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From CoqUtils Require Import hseq word.
From extructures Require Import fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Equality.

Require Import MicroPolicies.Utils.
Import DoNotation.
Import Types.

Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.PreservationLemmas.
(* Require Import MicroPolicies.Recomposition.StepSilentStrong. *)
(* Require Import MicroPolicies.Recomposition.StepEventReturn. *)
(* Require Import MicroPolicies.Recomposition.StepEventCall. *)

Module RInitTest (S: RecompositionContext).

  Module Defs := RecompositionDefinitions S.
  Module Pres := Preservation S.
  Include Pres.

  (* Module Strong := StepStrong S. *)
  (* Import Strong. *)
  (*** Diagrams ***)

  (* Bridge: x \in domm m -> In x (domm m). Uses Extra.In_in. *)
  Lemma mem_In_domm: forall {T: ordType} {S: Type} (m: {fmap T -> S}) x,
    x \in domm m -> In x (domm m).
  Proof. intros. apply Extra.In_in. exact H. Qed.

  (* Tmp.mapk preserves values: if mapk f m k' = Some v, then
     exists k such that f k = k' and m k = Some v *)
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

  Lemma List_In_mem: forall {T: eqType} (l: seq T) x,
      List.In x l -> x \in l.
  Proof.
    intros T0 l x. induction l as [| a rest IH].
    - intro. contradiction.
    - simpl. intros [<- | Hin].
      + rewrite in_cons. apply/orP. left. exact (eq_refl _).
      + rewrite in_cons. apply/orP. right. exact (IH Hin).
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

  (* Converse: if m k = Some v and f is injective, then mapk f m (f k) = Some v *)
  Lemma mapk_Some_inv: forall {T T' : ordType} {S : Type} (f : T -> T') (m : {fmap T -> S}) k v,
    injective f -> m k = Some v -> Tmp.mapk f m (f k) = Some v.
  Proof. Admitted.

  (* All entries in linearize_buf have tag def_mem_tag c false *)
  Lemma linearize_buf_tag: forall pb c b n vt,
    nth_error (linearize_buf pb c b) n = Some vt ->
    snd vt = def_mem_tag c false.
  Proof.
    intros pb c0 b n vt.
    unfold linearize_buf.
    destruct (getm pb c0) as [map |] eqn:Hc; simpl; [| destruct n; discriminate].
    destruct (getm map b) as [block |] eqn:Hb; simpl; [| destruct n; discriminate].
    destruct block as [sz | vals].
    - move=> Hnth.
      have := nth_error_In _ _ Hnth.
      intros H. eapply repeat_spec in H. subst. simpl. reflexivity.
    - move=> Hnth.
      have := nth_error_In _ _ Hnth.
      rewrite in_map_iff. move=> [x [<- _]]. reflexivity.
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

  (* All values in linearize_bufs have tag def_mem_tag c false for some c *)
  Lemma linearize_bufs_tag: forall pb k val_tag,
    linearize_bufs pb k = Some val_tag ->
    exists c, snd val_tag = def_mem_tag c false.
  Proof.
    intros pb k val_tag.
    unfold linearize_bufs.
    (* Chain: mapk -> uncurrym -> mapm -> mapim -> fmap_of_seq -> linearize_buf *)
    intros H. apply mapk_Some in H.
    destruct H as [k0 [? Hk0]].
    move: Hk0. rewrite uncurrymE mapmE.
    destruct k0 as [k1 k2].
    simpl.
    (* Need to destruct the nested lookups *)
    destruct (mapim (fun c map =>
      mapim (fun b _ => fmap_of_seq (linearize_buf pb c b)) map) pb k1)
      as [inner_map |] eqn:Hinner; simpl; [| try discriminate].
    - rewrite mapimE in Hinner.
      destruct k2 as [k2 k3]. subst k.
      destruct (pb k1) as [pb_map |] eqn:Hpb; simpl in Hinner; [| try discriminate].
      + rewrite Hpb in Hinner. simpl in Hinner.
        inversion Hinner. simpl in *.
        rewrite mapimE. rewrite Hpb. simpl. rewrite H0.
        rewrite uncurrymE. simpl.
        rewrite <- H0.
        destruct (mapim (fun b _ => fmap_of_seq (linearize_buf pb k1 b)) pb_map k2)
          as [inner2 |] eqn:Hinner2; simpl; [| try discriminate].
        * rewrite mapimE in Hinner2.
          destruct (pb_map k2) as [block |] eqn:Hblock; simpl in Hinner2; [| discriminate].
          inversion Hinner2. rewrite mapimE. rewrite Hblock. simpl.
          rewrite fmap_of_seqE.
          intros G.
          exists k1.
          eapply nth_map_Some_nth_error in G.
          apply linearize_buf_tag in G. eauto.
        * simpl in *. rewrite mapimE in Hinner2.
          rewrite mapimE.
          destruct (pb_map k2) as [block |]; simpl in *; try congruence.
      + simpl in *.
        rewrite mapimE. rewrite Hpb. simpl. congruence.
    - simpl in *.
      rewrite mapimE. rewrite mapimE in Hinner.
      destruct (pb k1) as [pb_map |] eqn:Hpb; simpl in *.
      rewrite Hpb in Hinner; simpl in Hinner; try congruence.
      rewrite Hpb. simpl. congruence.
  Qed.

  (* All initial_memory values have tag (def_mem_tag c false) for some c *)
  Lemma initial_memory_tag: forall pb w v,
    @initial_memory mt pb w = Some v ->
    exists c, taga v = def_mem_tag c false.
  Proof.
    intros pb w v Hmem.
    unfold initial_memory in Hmem.
    apply mapk_Some in Hmem. destruct Hmem as [k [_ Hmem]].
    rewrite mapmE in Hmem.
    destruct (linearize_bufs pb k) as [val_tag |] eqn:Hbufs; simpl in Hmem; [| discriminate].
    injection Hmem => <-. simpl.
    exact (linearize_bufs_tag Hbufs).
  Qed.

  Lemma initial_memory_domm: forall b,
      domm (@initial_memory mt b) = fset (map word_of_nat (List.seq 0 (size (@initial_memory mt b)))).
  Proof.
    intros.
  Admitted.

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

  (* Stronger version: the n-th output entry corresponds to the n-th input entry *)
  (* The foldr counter: after processing n entries from the right, acc.2 = n *)
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

  Hypothesis word_of_nat_inj: forall a b,
      a < 2^(word_size mt) -> b < 2^(word_size mt) ->
      word_of_nat (k := word_size mt) a = word_of_nat b -> a = b.

  Lemma encode_code_nth: forall cde pc0 n v,
    let list := (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
      (encode_instr_atom x
        (fun l default => match findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) cde
         with Some m => pc0 + m | None => if l == alloc_label then l else default end)
        (pc0 + size cde - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) cde).1 in
    nth_error list n = Some v ->
    encode_code cde pc0 (word_of_nat (n + pc0)) = Some v.
  Proof.
    intros cde pc0 n v ? Hnth.
    unfold encode_code.
    apply nth_error_nth_map_Some in Hnth.
    simpl in *.
    rewrite -fmap_of_seqE in Hnth.
    eapply mapk_Some_inv with (f := (fun x : nat => word_of_nat (x + pc0)))
      in Hnth; eauto.
    intros a b H.
    eapply word_of_nat_inj in H.
    admit.
  Admitted.


  (* The foldr output has size = size of input *)
  Lemma encode_code_foldr_size: forall cde lp offset,
    size (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
      (encode_instr_atom x lp (offset - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) cde).1
    = size cde.
  Proof.
    intros cde. induction cde as [| [i0 t0] cde' IH]; intros lp offset.
    - simpl. reflexivity.
    - simpl. f_equal. exact (IH lp offset).
  Qed.

  (* Converse: encode_code lookup at word_of_nat (n + pc0) gives the n-th atom *)
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

  (* Every atom in the foldr output has a tag from some input entry *)
  Lemma encode_code_foldr_tag: forall cde lp offset n v,
    nth_error (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
      (encode_instr_atom x lp (offset - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) cde).1 n = Some v ->
    exists i t, List.In (i, t) cde /\ taga v = t.
  Proof.
    intros cde. induction cde as [| [i0 t0] cde' IH]; intros lp offset n v Hnth.
    - simpl in Hnth. destruct n; discriminate.
    - simpl in Hnth.
      (* output = encode_instr_atom (i0,t0) lp (...) :: (foldr ... cde').1 *)
      set acc := (foldr _ _ cde') in Hnth.
      destruct n as [| n'].
      + (* n = 0: v is the head, from (i0, t0) *)
        simpl in Hnth. injection Hnth => <-.
        exists i0, t0. split.
        * left. reflexivity.
        * (* taga (encode_instr_atom (i0,t0) lp _) = t0 *)
          unfold encode_instr_atom. simpl. reflexivity.
      + (* n > 0: v is in the tail, which comes from foldr on cde' *)
        simpl in Hnth.
        destruct (IH lp offset n' v Hnth) as [i' [t' [Hin' Htag']]].
        exists i', t'. split.
        * right. exact Hin'.
        * exact Htag'.
  Qed.

  (* All atoms produced by encode_code have their tag from the input code entries.
     encode_instr_atom x lp pos = (encode_instr (fst x) lp pos) @ (snd x),
     so taga = snd x where x ∈ (cde ++ [:: (MrHalt, MTag Other Component.main None true)]) *)
  Lemma encode_code_tag: forall cde pc0 w v,
    encode_code cde pc0 w = Some v ->
    exists i t,
      List.In (i, t) cde /\
      taga v = t.
  Proof.
    intros cde pc0 w v Henc.
    unfold encode_code in Henc.
    apply mapk_Some in Henc. destruct Henc as [k [_ Hk]].
    rewrite fmap_of_seqE in Hk.
    apply nth_map_Some_nth_error in Hk.
    destruct (encode_code_foldr_tag Hk) as [i [t [Hin Htag]]].
    exists i, t. split; [exact Hin | exact Htag].
  Qed.

  Lemma code_tags_wf_all: forall (cde: list (Merged.instr (mt := mt) * mem_tag)) i t,
    (forall i t, List.In (i, t) cde -> is_code t = true /\ vtag t = Other) ->
    List.In (i, t) cde ->
    is_code t = true /\ vtag t = Other.
  Proof.
    intros cde i t Hwf Hin.
    eapply Hwf. eauto.
  Qed.

  (* For any program code that satisfies code_tags_wf, encode_code produces is_code = true *)
  Lemma encode_code_is_code: forall cde pc w v,
    (forall i t, List.In (i, t) cde -> is_code t = true /\ vtag t = Other) ->
    encode_code cde pc w = Some v ->
    is_code (taga v) = true.
  Proof.
    intros cde pc w v Hwf H.
    destruct (encode_code_tag H) as [i [t [Hin Htag]]].
    rewrite Htag. exact (code_tags_wf_all Hwf Hin).1.
  Qed.


  (* For addresses below alloc_label, the high bits (mask) are 0 *)
  Lemma small_addr_mask_zero: forall x,
      x < alloc_label ->
      andw (@word_of_nat (word_size mt) x) (@mask mt NC) = 0%w.
  Proof.
    (* mask = shlw (as_word (2^word_size - 1)) (word_size - NC).
       word_of_nat x = as_word (Posz x).
       andw extracts high bits. For x < alloc_label = 2^14 < 2^(word_size - NC),
       the high bits are 0. *)
    admit.
  Admitted.

  Lemma encode_code_initial_memory_disjoint: forall cde pb w v,
    initial_memory (mt := mt) pb w = Some v ->
    encode_code cde (size (@initial_memory mt pb)) w = None.
  Proof.
  Admitted.

  Lemma encode_code_prefix: forall cde pc0 w v,
      pc0 + size cde < alloc_label ->
      encode_code cde pc0 w = Some v ->
      andw w (@mask mt NC) = @component_memory_prefix mt NC (ssrint.Posz 0).
  Proof.
    intros cde pc0 w v Hbound Henc.
    destruct (encode_code_nth_inv Henc) as [n [Hw [Hlt Hnth]]].
    rewrite Hw.
    rewrite component_memory_prefix_zero.
    apply small_addr_mask_zero.
    have Hle: n <= size cde.
    { move: Hlt. rewrite /=. eauto. }
    have G: n + pc0 <= pc0 + size cde. { rewrite addnC leq_add2l. exact Hle. }
    eapply (leq_ltn_trans G Hbound).
  Qed.

  Lemma component_memory_prefix_inj: forall c1 c2,
      @component_memory_prefix mt NC c1 = @component_memory_prefix mt NC c2 ->
      c1 = c2.
  Proof.
  Admitted.

  Lemma code_prefix_neq_data_prefix: forall c0,
      @component_memory_prefix mt NC (ssrint.Posz 0) <>
        @component_memory_prefix mt NC (ssrint.Posz (1 + c0)).
  Proof.
    intros c0 Heq.
    apply component_memory_prefix_inj in Heq.
    discriminate.
  Qed.

  Lemma initial_memory_not_code: forall pb w v,
      initial_memory (mt := mt) pb w = Some v ->
      is_code (taga v) = false.
  Proof.
    intros pb w v Hmem.
    have [c Htag] := initial_memory_tag Hmem.
    by rewrite Htag.
  Qed.


  (* The color of a linearize_bufs entry is a key of pb *)
  Lemma linearize_bufs_color: forall pb k val_tag,
    linearize_bufs pb k = Some val_tag ->
    exists c, snd val_tag = def_mem_tag c false /\ c \in domm pb.
  Proof.
    intros pb k val_tag.
    unfold linearize_bufs.
    intros H. apply mapk_Some in H.
    destruct H as [k0 [? Hk0]].
    move: Hk0. rewrite uncurrymE mapmE.
    destruct k0 as [k1 k2].
    simpl.
    (* Need to destruct the nested lookups *)
    destruct (mapim (fun c map =>
      mapim (fun b _ => fmap_of_seq (linearize_buf pb c b)) map) pb k1)
      as [inner_map |] eqn:Hinner; simpl; [| try discriminate].
    - rewrite mapimE in Hinner.
      destruct k2 as [k2 k3]. subst k.
      destruct (pb k1) as [pb_map |] eqn:Hpb; simpl in Hinner; [| try discriminate].
      + rewrite Hpb in Hinner. simpl in Hinner.
        inversion Hinner. simpl in *.
        rewrite mapimE. rewrite Hpb. simpl. rewrite H0.
        rewrite uncurrymE. simpl.
        rewrite <- H0.
        destruct (mapim (fun b _ => fmap_of_seq (linearize_buf pb k1 b)) pb_map k2)
          as [inner2 |] eqn:Hinner2; simpl; [| try discriminate].
        * rewrite mapimE in Hinner2.
          destruct (pb_map k2) as [block |] eqn:Hblock; simpl in Hinner2; [| discriminate].
          inversion Hinner2. rewrite mapimE. rewrite Hblock. simpl.
          rewrite fmap_of_seqE.
          intros G.
          exists k1.
          eapply nth_map_Some_nth_error in G.
          apply linearize_buf_tag in G. eauto.
          rewrite mem_domm Hpb. eauto.
        * simpl in *. rewrite mapimE in Hinner2.
          rewrite mapimE.
          destruct (pb_map k2) as [block |]; simpl in *; try congruence.
      + simpl in *.
        rewrite mapimE. rewrite Hpb. simpl. congruence.
    - simpl in *.
      rewrite mapimE. rewrite mapimE in Hinner.
      destruct (pb k1) as [pb_map |] eqn:Hpb; simpl in *.
      rewrite Hpb in Hinner; simpl in Hinner; try congruence.
      rewrite Hpb. simpl. congruence.
  Qed.

  Lemma initial_memory_prefix_zero: forall pb w v,
      size (initial_memory (mt := mt) pb) < alloc_label ->
      initial_memory (mt := mt) pb w = Some v -> 
      andw w (mask (NC := NC)) = component_memory_prefix (NC := NC) (ssrint.Posz 0).
  Admitted.
    
  (* Lemma initial_memory_prefix: forall pb w v, *)
  (*     initial_memory (mt := mt) pb w = Some v -> *)
  (*     andw w (@mask mt NC) = *)
  (*       @component_memory_prefix mt NC (ssrint.Posz (1 + color (taga v))). *)
  (* Proof. *)
  (*   intros pb w v Hmem. *)
  (*   unfold initial_memory in Hmem. *)
  (*   apply mapk_Some in Hmem. destruct Hmem as [k [Hw Hmem]]. *)
  (*   rewrite mapmE in Hmem. *)
  (*   destruct (linearize_bufs pb k) as [val_tag |] eqn:Hbufs; simpl in Hmem; [| discriminate]. *)
  (*   injection Hmem => <-. simpl. *)
  (*   (* Hw : f k = w, where f maps (c,b,o) triples to word addresses *) *)
  (*   (* taga = snd val_tag = def_mem_tag c false, so color = c *) *)
  (*   have [c0 [Htag Hdom]] := linearize_bufs_color Hbufs. *)
  (*   rewrite Htag. simpl. *)
  (*   destruct k as [p o]. *)
  (*   destruct p as [c b]. *)
  (*   simpl in *. *)
  (*   (* Goal: andw w mask = component_memory_prefix (Posz (1 + c0)) *) *)
  (*   (* w = as_word (concretize (k, Z.of_nat ...)) *) *)
  (*   (* Need: the address computation puts c0's data in c0's prefix region *) *)
  (*   admit. *)
  (* Admitted. *)
  Lemma findopt_bound: forall {A} (pred : A -> bool) (l : seq A) m,
      findopt pred l = Some m -> m < size l.
  Proof.
    intros A pred0 l. unfold findopt.
    induction l as [| x rest IH]; intros m Hfind.
    - simpl in Hfind. discriminate.
    - simpl in Hfind.
      destruct (foldr _ None rest) as [n |] eqn:Hrest.
      + (* rest returned Some n *)
        inv Hfind.
        specialize (IH n Logic.eq_refl).
        (* m = n + 1 *)
        simpl. rewrite ltnS. rewrite addn1.
        eauto.
      + (* rest returned None *)
        destruct (pred0 x) eqn:Hpred.
        * injection Hfind => <-. (* m = 0 *)
          simpl. done. (* 0 < size (x :: rest) *)
        * discriminate.
  Qed.
  
  Hypothesis code_jal_labels_resolved: forall cde n l t,
      nth_error cde n = Some (@MrJal mt l, t) ->
      l <> alloc_label ->
      exists m, findopt (fun p : @Merged.instr mt * mem_tag =>
                      match p.1 with MrLabel l0 => l == l0 | _ => false end) cde = Some m.

  Hypothesis code_bnz_labels_resolved: forall cde n r l t,
      nth_error cde n = Some (@MrBnz mt r l, t) ->
      exists m, findopt (fun p : @Merged.instr mt * mem_tag =>
                      match p.1 with MrLabel l0 => l == l0 | _ => false end) cde = Some m.
  
  Hypothesis alloc_label_lt_imm: alloc_label < 2 ^ (imm_size mt).
  Hypothesis alloc_label_lt_w: alloc_label < 2 ^ (word_size mt).

  (* find_rank succeeds for Component.main in each program's code *)
  Hypothesis find_rank_main_prog: exists start,
    find_rank (fun '(_,tag) => color tag == Component.main) (code prog) = Some start.
  Hypothesis find_rank_main_prog': exists start,
    find_rank (fun '(_,tag) => color tag == Component.main) (code prog') = Some start.
  Hypothesis find_rank_main_prog'': exists start,
    find_rank (fun '(_,tag) => color tag == Component.main) (code prog'') = Some start.
  
  Lemma encode_code_bnz_target: forall cde pc0 w v r n,
      (forall i t, List.In (i, t) cde -> is_code t = true /\ vtag t = Other) ->
      pc0 + size cde < alloc_label ->
      encode_code cde pc0 w = Some v ->
      decode_instr (vala v) = Some (Bnz r n) ->
      exists v', encode_code cde pc0 (addw w (swcast n)) = Some v'
            /\ is_code (taga v') = true.
  Proof.
    intros cde pc0 w v r n0 Hwf Hsize Henc Hdec.
    destruct (encode_code_nth_inv Henc) as [k [Hw [Hlt Hnth]]].
    destruct (encode_code_foldr_nth Hnth) as [i [t [Hnth_cde [Htag Hval]]]].
    rewrite Hval in Hdec.
    rewrite /instr_merged_to_mp /encode_instr_mp encodeK in Hdec.
    destruct i; simpl in Hdec; try discriminate.
    injection Hdec => Hn Hr.
    destruct (findopt (fun p0 : Merged.instr * mem_tag =>
      match p0.1 with MrLabel l0 => l == l0 | _ => false end) cde)
      as [m |] eqn:Hfind.
    - have Hm_bound: m < size cde.
      { eapply findopt_bound. eauto. }
      set (g := pc0 +
                   size cde
                     ).
      have Hm_bound2: m < size (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
             (encode_instr_atom x (fun l default : nat =>
                   match
                     findopt
                       (fun p : Merged.instr * mem_tag => match p.1 with
                                                          | MrLabel l0 => l == l0
                                                          | _ => false
                                                          end)
                       cde
                   with
                   | Some m => pc0 + m
                   | None => if l == alloc_label then l else default
                   end) (g - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) cde).1.
      { rewrite encode_code_foldr_size. exact Hm_bound. }
      destruct (nth_error_Some_ex Hm_bound2) as [v' Hv'].
      have Henc_m := encode_code_nth Hv'.
      (* Case split: k <= m (forward jump) or m < k (backward, wraps to 0) *)
      (* rewrite Hfind in Hn. *)
      have Hk_bound: k < size cde := Hlt.
      have HX: pc0 + size cde - 1 - (size cde - 1 - k) = k + pc0.
      { rewrite subnBA.
        - rewrite addnC.
          have ->: pc0 + size cde - 1 = pc0 + (size cde - 1).
          { rewrite addnBA //. rewrite /= //.
            eapply leq_ltn_trans with k. eauto. eauto. }
          rewrite addnA addnK. done.
        - rewrite subn1.
          rewrite -ltnS prednK. eauto.
          rewrite /=.
          eapply leq_ltn_trans with k. eauto. eauto. }
      have Hoff: pc0 + m - (k + pc0) = m - k.
      { rewrite (addnC k pc0). rewrite subnDl. reflexivity. }
      case: (leqP k m) => [Hkm | Hmk].
      + (* k <= m: forward jump — target is at position m *)
        exists v'. split.
        * suffices Heq: (w + swcast n0)%w = word_of_nat (m + pc0) by rewrite Heq.
          rewrite Hw -Hn HX Hoff.
          replace (swcast (word_of_nat (m - k))) with (@word_of_nat (word_size mt) (m - k)).
          2: { symmetry. apply val_inj. apply fintype.ord_inj. simpl.
            congr div.modn. congr ssrint.absz. congr intdiv.modz. congr ssrint.Posz.
            rewrite intdiv.modz_nat ssrint.absz_nat div.modn_mod.
            rewrite (div.modn_small (d := 2 ^ imm_size mt)); [done |].
            have H6: m - k < size cde := leq_ltn_trans (leq_subr k m) Hm_bound.
            have Hcde_alloc: pc0 + size cde <= alloc_label.
            { eauto. }
            have H7: size cde < 2 ^ imm_size mt.
            { have H8: size cde <= pc0 + size cde by rewrite addnC; exact (leq_addr pc0 (size cde)).
              exact (leq_ltn_trans (leq_trans H8 Hcde_alloc) alloc_label_lt_imm). }
            exact (ltn_trans H6 H7). }
          apply val_inj. rewrite /addw /onew /=. apply fintype.ord_inj. simpl.
          rewrite !intdiv.modz_nat.
          congr div.modn. congr ssrint.absz. congr ssrint.Posz. congr div.modn.
          rewrite !ssrint.absz_nat !div.modn_mod !div.modn_small.
          -- rewrite (addnC k pc0) -addnA subnKC; [rewrite addnC; reflexivity | exact Hkm].
          -- have H6: m - k < size cde := leq_ltn_trans (leq_subr k m) Hm_bound.
             have Hcde_alloc: pc0 + size cde <= alloc_label.
             { eauto. }
             have H8: size cde <= pc0 + size cde by rewrite addnC; exact (leq_addr pc0 (size cde)).
             exact (ltn_trans H6 (leq_ltn_trans (leq_trans H8 Hcde_alloc) alloc_label_lt_w)).
          -- have Hcde_alloc: pc0 + size cde <= alloc_label. { eauto. }
             have H8: k + pc0 <= pc0 + size cde by rewrite addnC leq_add2l; exact (ltnW Hk_bound).
             exact (leq_ltn_trans H8 (leq_ltn_trans Hcde_alloc alloc_label_lt_w)).
        * destruct (encode_code_foldr_tag Hv') as [i' [t' [Hin' Htag']]].
          rewrite Htag'. exact (code_tags_wf_all Hwf Hin').1.
      + (* m < k: backward jump — m - k = 0, target is w itself *)
        have Hmk0: m - k = 0 by apply/eqP; rewrite subn_eq0; exact (ltnW Hmk).
        exists v. split.
        * rewrite Hw -Hn HX Hoff Hmk0.
          (* (word_of_nat (k + pc0) + swcast (word_of_nat 0))%w = word_of_nat (k + pc0) *)
          (* swcast 0 = 0, x + 0 = x *)
          replace (swcast (@word_of_nat (imm_size mt) 0)) with (@zerow (word_size mt)).
          2: { rewrite /word_of_nat /zerow /swcast.
               apply val_inj. simpl. done. }
          rewrite addw0.
          rewrite -Hw. eauto.
        * exact (encode_code_is_code Hwf Henc).
    - exfalso.
      have [m' Hfind'] := code_bnz_labels_resolved Hnth_cde.
      rewrite Hfind' in Hfind. discriminate.
  Qed.

  Lemma encode_code_jal_target: forall cde pc0 w v n,
      (forall i t, List.In (i, t) cde -> is_code t = true /\ vtag t = Other) ->
      pc0 + size cde < alloc_label ->
      encode_code cde pc0 w = Some v ->
      decode_instr (vala v) = Some (Jal n) ->
      (exists v', encode_code cde pc0 (swcast n) = Some v'
             /\ is_code (taga v') = true)
      \/ (word_of_nat alloc_label = n).
  Proof.
    intros cde pc0 w v n0 Hwf Hsize Henc Hdec.
    destruct (encode_code_nth_inv Henc) as [k [Hw [Hlt Hnth]]].
    destruct (encode_code_foldr_nth Hnth) as [i [t [Hnth_cde [Htag Hval]]]].
    rewrite Hval in Hdec.
    rewrite /instr_merged_to_mp /encode_instr_mp encodeK in Hdec.
    destruct i; simpl in Hdec; try discriminate.
    injection Hdec => Hn.
    set lp := (fun l0 default : nat =>
      match findopt (fun p : Merged.instr * mem_tag => match p.1 with MrLabel l1 => l0 == l1 | _ => false end) cde
      with Some m => pc0 + m | None => if l0 == alloc_label then l0 else default end).
    destruct (findopt (fun p : Merged.instr * mem_tag => match p.1 with MrLabel l1 => l == l1 | _ => false end) cde)
      as [m |] eqn:Hfind.
    (* rewrite Hfind in Hn. *)
    - left.
      have Hm_bound: m < size cde.
      { eapply findopt_bound; eauto. }
       set (g := pc0 + size cde).
      have Hm_bound2: m < size (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
             (encode_instr_atom x (fun l default : nat =>
                   match
                     findopt
                       (fun p : Merged.instr * mem_tag => match p.1 with
                                                          | MrLabel l0 => l == l0
                                                          | _ => false
                                                          end)
                       cde
                   with
                   | Some m => pc0 + m
                   | None => if l == alloc_label then l else default
                   end) (g - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) cde).1.
      { rewrite encode_code_foldr_size. exact Hm_bound. }
      (* change (m < length (foldr _ ([::], 0) cde').1) in Hm_bound2. *)
      destruct (nth_error_Some_ex Hm_bound2) as [v' Hv'].
      (* encode_code at word_of_nat (m + pc0) = Some v' *)
      have Henc_m := encode_code_nth Hv'.
      (* n0 = word_of_nat (pc0 + m), swcast n0 = word_of_nat (pc0 + m) at word_size *)
      exists v'. split.
      + rewrite -Hn.
        (* swcast (word_of_nat (pc0 + m)) = word_of_nat (m + pc0) *)
        rewrite addnC in Henc_m.
        replace (swcast (word_of_nat (pc0 + m))) with (@word_of_nat (word_size mt) (pc0 + m)); eauto.
        unfold swcast. simpl. unfold word_of_nat.
        congr (fun x => @as_word (word_size mt) (ssrint.Posz x)).
        rewrite intdiv.modz_nat ssrint.absz_nat !div.modn_mod.
        symmetry. apply div.modn_small.
        have Hle: m <= size cde.
        { move: Hm_bound. rewrite /=. eauto. }
        have H1: pc0 + m <= pc0 + size cde by rewrite leq_add2l.
        have H2 := leq_ltn_trans H1 Hsize.
        exact (ltn_trans H2 alloc_label_lt_imm).
      + (* is_code (taga v') *)
        destruct (encode_code_foldr_tag Hv') as [i' [t' [Hin' Htag']]].
        rewrite Htag'. exact (code_tags_wf_all Hwf Hin').1.
    - (* findopt didn't find the label *)
      simpl in Hn.
      destruct (l == alloc_label) eqn:Halloc.
      + (* l = alloc_label *)
        right.
        move/eqP : Halloc => Halloc. subst l.
        eauto.
      + (* l != alloc_label: fallback to default = pos *)
        exfalso.
        have Hneq: l <> alloc_label by move/eqP: Halloc.
        have [m' Hfind'] := code_jal_labels_resolved Hnth_cde Hneq.
        rewrite Hfind' in Hfind. discriminate.
  Qed.
  
  (* Lemma encode_code_end_condition: forall cde pc0 w v, *)
  (*   (forall i t, List.In (i, t) cde -> is_code t = true /\ vtag t = Other) -> *)
  (*   encode_code cde pc0 w = Some v -> *)
  (*   is_code (taga v) -> *)
  (*   (decode_instr (vala v) = Some (Halt _)) \/ *)
  (*   (exists v', encode_code cde pc0 (w + 1)%w = Some v' *)
  (*          /\ is_code (taga v') = true). *)
  (* Proof. *)
  (*   intros cde pc0 w v Hwf Henc Hcode. *)
  (*   destruct (encode_code_nth_inv Henc) as [n [Hw [Hlt Hnth]]]. *)
  (*   set cde' := cde ++ [:: (@MrHalt mt, MTag Other Component.main None true)] in Hlt, Hnth. *)
  (*   (* n < size cde', and nth_error (foldr ...) n = Some v *) *)
  (*   (* Case: is n the last entry (n = size cde' - 1) or not? *) *)
  (*   destruct (Nat.eq_dec n (size cde' - 1)) as [Hlast | Hnotlast]. *)
  (*   - (* n is the last entry: it's the appended Halt *) *)
  (*     left. *)
  (*     (* v is the n-th entry where n = size cde' - 1 = last position. *)
  (*        The last entry in cde' = cde ++ [halt] is (MrHalt, MTag ...). *)
  (*        encode_instr_atom (MrHalt, _) lp pos = (encode_instr_mp (Halt mt)) @ _. *)
  (*        decode_instr (encode_instr_mp (Halt mt)) = Some (Halt mt) by encodeK. *) *)
  (*     destruct (encode_code_foldr_nth Hnth) as [i [t [Hnth_cde [Htag Hval]]]]. *)
  (*     (* Hnth_cde : nth_error cde' n = Some (i, t), with n = size cde' - 1 *) *)
  (*     (* The last entry of cde' is (MrHalt, ...) *) *)
  (*     have Hlast_entry: nth_error cde' (size cde' - 1) = Some (@MrHalt mt, MTag Other Component.main None true). *)
  (*     { subst cde'. *)
  (*       rewrite size_cat /= addnK. *)
  (*       rewrite nth_error_app2; [| done]. *)
  (*       rewrite Nat.sub_diag /=. reflexivity. } *)
  (*     rewrite Hlast in Hnth_cde. rewrite Hlast_entry in Hnth_cde. *)
  (*     inversion Hnth_cde as [[Hi Ht]]. subst i. *)
  (*     (* i = MrHalt, so instr_merged_to_mp MrHalt lp pos = Halt mt *) *)
  (*     rewrite Hval. rewrite encodeK. done. *)
  (*   - (* n is not the last: n+1 < size cde', so successor exists *) *)
  (*     right. *)
  (*     assert (Hlt' : n + 1 < size cde'). *)
  (*     { rewrite addn1 ltn_neqAle Hlt andbT. *)
  (*       apply /eqP => Heq. apply Hnotlast. *)
  (*       rewrite -Heq. rewrite subn1 succnK. reflexivity. } *)
  (*     (* nth_error (foldr ...) (n+1) = Some v' for some v' *) *)
  (*     set (f := (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) => *)
  (*              (encode_instr_atom x *)
  (*                 (fun l default : nat => *)
  (*                  match *)
  (*                    findopt *)
  (*                      (fun p : Merged.instr * mem_tag => *)
  (*                       match p.1 with *)
  (*                       | MrLabel l0 => l == l0 *)
  (*                       | _ => false *)
  (*                       end) cde' *)
  (*                  with *)
  (*                  | Some m => pc0 + m *)
  (*                  | None => if l == alloc_label then l else default *)
  (*                  end) (pc0 + size cde' - 1 - acc.2) :: acc.1, acc.2.+1))). *)
  (*     assert (Hnth' : exists v', nth_error (foldr f ([::], 0) cde').1 (n+1) = Some v'). *)
  (*     { apply nth_error_Some_ex. *)
  (*       change (n + 1 < size (foldr f ([::], 0) cde').1). *)
  (*       rewrite /f encode_code_foldr_size. exact Hlt'. } *)
  (*     destruct Hnth' as [v' Hv']. *)
  (*     exists v'. split. *)
  (*     + (* encode_code cde pc0 (w + 1) = Some v' *) *)
  (*       rewrite Hw. *)
  (*       (* word_of_nat (n + pc0) + 1 = word_of_nat ((n+1) + pc0) *) *)
  (*       replace ((word_of_nat (n + pc0) + 1)%w) with (@word_of_nat (word_size mt) (n + 1 + pc0)). *)
  (*       2: { (* word_of_nat (n + pc0) + 1 = word_of_nat (n + 1 + pc0) *) *)
  (*         rewrite /word_of_nat. *)
  (*         apply val_inj. *)
  (*         rewrite /addw /onew. simpl. *)
  (*         (* congr fintype.Ordinal. *) *)
  (*         (* rewrite val_as_word. *) *)
  (*         rewrite !intdiv.modz_nat !ssrint.absz_nat. *)
  (*         rewrite div.modnDmr div.modnDml. *)
  (*         rewrite addnAC. *)
  (*         apply fintype.ord_inj. simpl. *)
  (*         rewrite !div.modn_mod. *)
  (*         rewrite -div.modnDm. done. } *)
  (*       apply (encode_code_nth (pc0 := pc0)). *)
  (*       rewrite /f in Hv'. exact Hv'. *)
  (*     + (* is_code (taga v') = true *) *)
  (*       destruct (encode_code_foldr_tag Hv') as [i' [t' [Hin' Htag']]]. *)
  (*       rewrite Htag'. exact (code_tags_wf_all Hwf Hin').1. *)
  (* Qed. *)
  
  Lemma encode_code_color: forall cde pc0 w v,
    (forall i t, List.In (i, t) cde -> is_code t = true /\ vtag t = Other) ->
    (forall i t, List.In (i, t) cde -> In (color t) (domm ip) \/ In (color t) (domm ic)) ->
    encode_code cde pc0 w = Some v ->
    In (color (taga v)) (domm ip) \/ In (color (taga v)) (domm ic).
  Proof.
    intros cde pc0 w v Hwf Hcolor H.
    destruct (encode_code_tag H) as [i [t [Hin Htag]]].
    rewrite Htag.
    - exact (Hcolor i t Hin).
  Qed.

  (* The color of initial_memory values comes from the prog_buffers domain *)
  Lemma initial_memory_color_gen: forall pb w v,
    initial_memory (mt := mt) pb w = Some v ->
    color (taga v) \in domm pb.
  Proof.
    intros pb w v Hmem.
    unfold initial_memory in Hmem.
    apply mapk_Some in Hmem. destruct Hmem as [k [_ Hmem]].
    rewrite mapmE in Hmem.
    destruct (linearize_bufs pb k) as [val_tag |] eqn:Hbufs; simpl in Hmem; [| discriminate].
    injection Hmem => <-. simpl.
    have [c0 [Htag Hdom]] := linearize_bufs_color Hbufs.
    by rewrite Htag.
  Qed.

  Lemma initial_memory_color: forall (pb1 pb2 : NMap {fmap Block.id -> nat + seq value}) w v,
    initial_memory (mt := mt) (unionm pb1 pb2) w = Some v ->
    In (color (taga v)) (domm pb1)
    \/ In (color (taga v)) (domm pb2).
  Proof.
    intros pb1 pb2 w v Hmem.
    have Hdom := initial_memory_color_gen Hmem.
    rewrite domm_union in_fsetU in Hdom.
    move: Hdom => /orP [H1 | H2].
    - left. eapply Extra.In_in; eauto.
    - right. eapply Extra.In_in; eauto.
  Qed.
  
  Lemma initial_memory_no_entry: forall pb w v,
      initial_memory (mt := mt) pb w = Some v -> entry (taga v) = None.
  Proof.
    intros pb w v Hmem.
    have [c Htag] := initial_memory_tag Hmem.
    by rewrite Htag.
  Qed.

  Lemma encode_code_vtag_other: forall cde pc0 w v,
    (forall i t, List.In (i, t) cde -> is_code t = true /\ vtag t = Other) ->
    encode_code cde pc0 w = Some v ->
    vtag (taga v) = Other.
  Proof.
    intros cde pc0 w v Hwf H.
    destruct (encode_code_tag H) as [i [t [Hin Htag]]].
    rewrite Htag. exact (code_tags_wf_all Hwf Hin).2.
  Qed.

  (* code_tags_wf_prog/prog'/prog'' and convenience wrappers defined after Hypotheses below *)

  Lemma encode_code_vtag_not_ret: forall cde pc0 w v,
    (forall i t, List.In (i, t) cde -> is_code t = true /\ vtag t = Other) ->
    encode_code cde pc0 w = Some v ->
    forall n, vtag (taga v) <> Ret n.
  Proof.
    intros cde pc0 w v Hwf H. rewrite (encode_code_vtag_other Hwf H). discriminate.
  Qed.
  
  Lemma initial_memory_vtag_other: forall pb w v,
      initial_memory (mt := mt) pb w = Some v -> vtag (taga v) = Other.
  Proof.
    intros pb w v Hmem.
    have [c Htag] := initial_memory_tag Hmem.
    by rewrite Htag.
  Qed.

  (* All code tags in the programs have is_code = true and vtag = Other.
     This holds for code produced by the compilation pipeline (def_mem_tag c true). *)
  Hypothesis code_tags_wf_p : forall i t, List.In (i, t) (code p) -> is_code t = true /\ vtag t = Other.
  Hypothesis code_tags_wf_c : forall i t, List.In (i, t) (code c) -> is_code t = true /\ vtag t = Other.
  Hypothesis code_tags_wf_p' : forall i t, List.In (i, t) (code p') -> is_code t = true /\ vtag t = Other.
  Hypothesis code_tags_wf_c' : forall i t, List.In (i, t) (code c') -> is_code t = true /\ vtag t = Other.

  Hypothesis code_color_p : forall i t, List.In (i, t) (code p) -> color t \in domm ip.
  Hypothesis code_color_c : forall i t, List.In (i, t) (code c) -> color t \in domm ic.
  Hypothesis code_color_p' : forall i t, List.In (i, t) (code p') -> color t \in domm ip.
  Hypothesis code_color_c' : forall i t, List.In (i, t) (code c') -> color t \in domm ic.

  Hypothesis alloc_label_not_in_encode_code: forall cde pc0,
      pc0 + size cde < alloc_label ->
      encode_code cde pc0 (word_of_nat alloc_label) = None.
    
  Hypothesis alloc_label_not_in_initial_memory: forall pb,
      size (initial_memory (mt := mt) pb) < alloc_label ->
      initial_memory (mt := mt) pb (word_of_nat alloc_label) = None.
  
  Hypothesis memory_size:
    size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c))) +
      size (code p ++ code c) < alloc_label.
  Lemma memory_size_wo_code:
    size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c)))
    < alloc_label.
  Proof.
  Admitted.

  Hypothesis memory_size':
    size (initial_memory (mt := mt) (unionm (prog_buffers p') (prog_buffers c'))) +
      size (code p' ++ code c') < alloc_label.
  Lemma memory_size'_wo_code:
    size (initial_memory (mt := mt) (unionm (prog_buffers p') (prog_buffers c')))
    < alloc_label.
  Proof.
  Admitted.

  Hypothesis memory_size'':
    size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c'))) +
      size (code p ++ code c') < alloc_label.
  Lemma memory_size''_wo_code:
    size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c')))
    < alloc_label.
  Proof.
  Admitted.

  Hypothesis find_rank_main_shared:                                                                                                                                                                     
    find_rank (fun '(_,tag) => color tag == Component.main) (code prog) =
      find_rank (fun '(_,tag) => color tag == Component.main) (code prog'').
  
  Hypothesis domm_buffers_p: domm (prog_buffers p) = domm ip.
  Hypothesis domm_buffers_c: domm (prog_buffers c) = domm ic.
  Hypothesis domm_buffers_p': domm (prog_buffers p') = domm ip.
  Hypothesis domm_buffers_c': domm (prog_buffers c') = domm ic.

  Lemma code_tags_wf_prog: forall i t, List.In (i, t) (code prog) -> is_code t = true /\ vtag t = Other.
  Proof. simpl. intros i t H. apply List.in_app_iff in H. destruct H; [exact (code_tags_wf_p H) | exact (code_tags_wf_c H)]. Qed.
  Lemma code_tags_wf_prog': forall i t, List.In (i, t) (code prog') -> is_code t = true /\ vtag t = Other.
  Proof. simpl. intros i t H. apply List.in_app_iff in H. destruct H; [exact (code_tags_wf_p' H) | exact (code_tags_wf_c' H)]. Qed.
  Lemma code_tags_wf_prog'': forall i t, List.In (i, t) (code prog'') -> is_code t = true /\ vtag t = Other.
  Proof. simpl. intros i t H. apply List.in_app_iff in H. destruct H; [exact (code_tags_wf_p H) | exact (code_tags_wf_c' H)]. Qed.

  Lemma encode_code_is_code_prog: forall pc w v, encode_code (code prog) pc w = Some v -> is_code (taga v) = true.
  Proof. intros. exact (encode_code_is_code code_tags_wf_prog H). Qed.
  Lemma encode_code_is_code_prog': forall pc w v, encode_code (code prog') pc w = Some v -> is_code (taga v) = true.
  Proof. intros. exact (encode_code_is_code code_tags_wf_prog' H). Qed.
  Lemma encode_code_is_code_prog'': forall pc w v, encode_code (code prog'') pc w = Some v -> is_code (taga v) = true.
  Proof. intros. exact (encode_code_is_code code_tags_wf_prog'' H). Qed.

  Lemma encode_code_vtag_other_prog: forall pc w v, encode_code (code prog) pc w = Some v -> vtag (taga v) = Other.
  Proof. intros. exact (encode_code_vtag_other code_tags_wf_prog H). Qed.
  Lemma encode_code_vtag_other_prog': forall pc w v, encode_code (code prog') pc w = Some v -> vtag (taga v) = Other.
  Proof. intros. exact (encode_code_vtag_other code_tags_wf_prog' H). Qed.
  Lemma encode_code_vtag_other_prog'': forall pc w v, encode_code (code prog'') pc w = Some v -> vtag (taga v) = Other.
  Proof. intros. exact (encode_code_vtag_other code_tags_wf_prog'' H). Qed.

  Lemma code_color_prog: forall i t, List.In (i, t) (code prog) -> In (color t) (domm ip) \/ In (color t) (domm ic).
  Proof.
    intros. simpl in H.
    apply in_app_or in H as [H | H].
    left. eapply code_color_p in H. now eapply Extra.In_in.
    right. eapply code_color_c in H. now eapply Extra.In_in.
  Qed.

  Lemma code_color_prog': forall i t, List.In (i, t) (code prog') -> In (color t) (domm ip) \/ In (color t) (domm ic).
  Proof.
    intros. simpl in H.
    apply in_app_or in H as [H | H].
    left. eapply code_color_p' in H. now eapply Extra.In_in.
    right. eapply code_color_c' in H. now eapply Extra.In_in.
  Qed.

  Lemma code_color_prog'': forall i t, List.In (i, t) (code prog'') -> In (color t) (domm ip) \/ In (color t) (domm ic).
  Proof.
    intros. simpl in H.
    apply in_app_or in H as [H | H].
    left. eapply code_color_p in H. now eapply Extra.In_in.
    right. eapply code_color_c' in H. now eapply Extra.In_in.
  Qed.

  Lemma encode_code_color_prog: forall pc w v, encode_code (code prog) pc w = Some v -> In (color (taga v)) (domm ip) \/ In (color (taga v)) (domm ic).
  Proof. intros. exact (encode_code_color code_tags_wf_prog code_color_prog H). Qed.
  Lemma encode_code_color_prog': forall pc w v, encode_code (code prog') pc w = Some v -> In (color (taga v)) (domm ip) \/ In (color (taga v)) (domm ic).
  Proof. intros. exact (encode_code_color code_tags_wf_prog' code_color_prog' H). Qed.
  Lemma encode_code_color_prog'': forall pc w v, encode_code (code prog'') pc w = Some v -> In (color (taga v)) (domm ip) \/ In (color (taga v)) (domm ic).
  Proof. intros. exact (encode_code_color code_tags_wf_prog'' code_color_prog'' H). Qed.

  Hypothesis prog_buffers_p_p': prog_buffers p = prog_buffers p'.
  Hypothesis prog_buffers_c_c': prog_buffers c = prog_buffers c'.


  Lemma word_of_nat_offset: forall (A B : nat),
      @word_of_nat (word_size mt) A =
        (@word_of_nat (word_size mt) B + as_word (encode_int (Z.of_nat A - Z.of_nat B)))%w.
  Proof.
    admit.
  Admitted.

  
  Lemma size_domm_fmap: forall (T: ordType) (S: Type) (m: {fmap T -> S}),
      size (domm m) = size m.
  Proof.
  Admitted.

  
  Lemma combined_codes_forward: forall w v t off,
      color t \in domm ip ->
      offset1 (color t) = Some off ->
      is_code t ->
      encode_code (code prog) (size (initial_memory (mt := mt) (prog_buffers prog))) w = Some v@t ->
      exists v',
        decode_match
          (mem (initial_state (code prog) (prog_buffers prog) (prog_interface prog)))
          (mem (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'')))
          v v' /\
          (mem (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'')))
            (w + as_word off)%w = Some v'@t.
  Proof.
    intros w v t off Hrel Hoff Hcode Henc.
    set pc0 := size (@initial_memory mt (prog_buffers prog)).
    set pc0'' := size (@initial_memory mt (prog_buffers prog'')).
    (* Step 1: get position k *)
    destruct (encode_code_nth_inv Henc) as [k [Hw [Hlt Hnth]]].
    (* Step 2: get the instruction and tag at position k *)
    destruct (encode_code_foldr_nth Hnth) as [i [t' [Hnth_cde [Htag Hval]]]].
    (* Step 3: k < size (code p) since color t ∈ domm ip *)
    (* code prog = code p ++ code c. Entry k has color t ∈ domm ip. *)
    (* Entries from code c have color ∈ domm ic (disjoint from domm ip). *)
    (* So entry k must be from code p, hence k < size (code p). *)
    have Hk_in_p: k < size (code p).
    { (* code p is shadowed by Merged.code. Use prog instead. *)
      (* code prog = code p ++ code c, so size (code p) <= size (code prog) *)
      (* Hlt : k < size (code prog). If k >= size (code p), entry is from code c. *)

    { case Hk_p: (k < size (code p)); [auto |].
      exfalso.
      move/negbT: Hk_p. rewrite -leqNgt => Hk_ge_p.
      (* Hk_ge_p : size (code p) <= k *)
      (* Entry at position k in code prog = code p ++ code c is from code c *)
      have Hnth_c: nth_error (code c) (k - size (code p)) = Some (i, t').
      { have: nth_error (code prog) k = Some (i, t').
        auto.
        simpl. rewrite nth_error_app2; [done | apply/leP; exact Hk_ge_p]. }
      (* color t' ∈ domm ic *)
      have Hic: color t' \in domm ic.
      { eapply code_color_c. apply nth_error_In in Hnth_c. exact Hnth_c. }
      (* But color t = color t' ∈ domm ip (Hrel), contradiction by disjointness *)
      simpl in Htag. rewrite -Htag in Hic.
      pose proof Hmergeable_ifaces as [[G H] ?].
      have := fdisjointP H _ Hrel.
      by rewrite Hic. } }
    (* Step 4: same entry at position k in code prog'' *)
    have Hnth_prog'': nth_error (code prog'') k = Some (i, t').
    { (* code prog'' = code p ++ code c'. k < size (code p). *)
      simpl. rewrite nth_error_app1; [| apply/ltP; exact Hk_in_p].
      have: nth_error (code prog) k = Some (i, t').
      { eauto. }
      simpl. rewrite nth_error_app1; [done | apply/ltP; exact Hk_in_p]. }
    (* Step 5: get the foldr entry at position k for prog'' *)
    have Hk_lt'': k < size (code prog'').
    { simpl. rewrite size_cat. eapply (ltn_addr _ _). }
    have Hk_lt2: k < size (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
      (encode_instr_atom x (fun l default => match findopt (fun p0 => match p0.1 with MrLabel l0 => l == l0 | _ => false end) (code prog'') with Some m => pc0'' + m | None => if l == alloc_label then l else default end) (pc0'' + size (code prog'') - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) (code prog'')).1.
    { (* change (k < size (foldr _ ([::], 0) (code prog'')).1). *)
      rewrite encode_code_foldr_size. exact Hk_lt''. }
    destruct (nth_error_Some_ex Hk_lt2) as [v'' Hv''].
    have Henc'' := encode_code_nth Hv''.
    (* Henc'' : encode_code (code prog'') pc0'' (word_of_nat (k + pc0'')) = Some v'' *)
    (* Step 6: show v'' has the same tag t *)
    destruct (encode_code_foldr_nth Hv'') as [i'' [t'' [Hnth_cde2 [Htag'' Hval'']]]].
    rewrite Hnth_prog'' in Hnth_cde2. injection Hnth_cde2 => Ht'' Hi''.
    subst i'' t''.
    (* Step 7: show w + as_word off = word_of_nat (k + pc0'') *)
    have Haddr: (w + as_word off)%w = word_of_nat (k + pc0'').
    { rewrite Hw.

      
      (* word_of_nat (k + pc0) + as_word off = word_of_nat (k + pc0'') *)
      (* off = encode_int (p0 prog'' (color t) - p0 prog (color t)) *)
      (* p0 prog (color t) = start + pc0, p0 prog'' (color t) = start + pc0'' *)
      (* (same start since main is in shared code p prefix) *)
      (* So off = encode_int (pc0'' - pc0), and word_of_nat_offset gives the result *)
      (* Step 1: unfold off from Hoff *)
      unfold offset1 in Hoff. rewrite mkfmapfpE in Hoff.
      rewrite Hrel /= in Hoff.
      unfold p0 in Hoff.
      (* Hoff should now have find_rank for prog and prog'' *)
      destruct (find_rank (fun '(_, tag) => color tag == color t) (code prog)) as [start |] eqn:Hfr;
        [| simpl in Hoff].
      destruct (find_rank (fun '(_, tag) => color tag == color t) (code prog'')) as [start'' |] eqn:Hfr'';
        [| simpl in Hoff; discriminate].
      simpl in Hoff. injection Hoff => Hoff_eq.
      (* Hoff_eq : off = encode_int (Z.of_nat (start'' + pc0'') - Z.of_nat (start + pc0)) *)

      (* Step 2: show start = start'' (same position in shared code p prefix) *)
      have Hstart_eq: start = start''.
      { (* find_rank for (color t) in code prog = code p ++ code c
     and code prog'' = code p ++ code c'.
     color t ∈ domm ip, so first match is in code p (shared prefix).
     find_rank scans left-to-right, finds same position. *)
        admit. }
      subst start''.

      (* Step 3: word arithmetic *)
      (* off = encode_int (Z.of_nat (start + pc0'') - Z.of_nat (start + pc0)) *)
      have Hpc_eq: pc0'' = pc0.
      { rewrite /pc0'' /pc0. congr size. congr initial_memory. congr unionm.
        now rewrite prog_buffers_c_c'. }
      rewrite Hpc_eq. unfold pc0.
      rewrite -Hoff_eq.
      rewrite prog_buffers_c_c'.
      rewrite Z.sub_diag.
      replace (as_word (encode_int 0))%w with (zerow (k := word_size mt))%w.
      2: { reflexivity. }
      now rewrite addw0.
      admit. }
    (* Step 8: construct v' and decode_match *)
    exists (vala v'').
    split.
    - (* decode_match: case on instruction type *)
      destruct i; try (
        apply decode_match_no_JAL;
        [ rewrite Hval /instr_merged_to_mp /encode_instr_mp; move=> imm; rewrite encodeK; discriminate
        | rewrite Hval'' /instr_merged_to_mp /encode_instr_mp; move=> imm; rewrite encodeK; discriminate
        | rewrite Hval Hval''; reflexivity ]);
        admit. (* MrJal and MrBnz cases *)
    - (* mem prog'' (w + as_word off) = Some (vala v'')@t *)
      rewrite Haddr. simpl.
      rewrite unionmE Henc'' /=.
      simpl in Htag. rewrite Htag. destruct v''. subst. simpl. eauto.
  Admitted.

  

End RInitTest.
