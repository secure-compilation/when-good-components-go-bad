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
Set Warnings "-declaration-outside-section".

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

Require Import MicroPolicies.Recomposition.OffsetWord.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.BufferShape.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.PreservationLemmas.
Require Import MicroPolicies.Recomposition.StepEventReturn.

Module RecInit (S: RecompositionContext) (A: AlignmentFacts S).

  Include StepEventReturn S.

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

  Lemma linearize_bufs_tag: forall pb k val_tag,
    linearize_bufs pb k = Some val_tag ->
    exists c, snd val_tag = def_mem_tag c false.
  Proof.
    intros pb k val_tag.
    unfold linearize_bufs.
    intros H. apply mapk_Some in H.
    destruct H as [k0 [? Hk0]].
    move: Hk0. rewrite uncurrymE mapmE.
    destruct k0 as [k1 k2].
    simpl.
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

  Lemma seqE : forall len start, List.seq start len = iota start len.
  Proof. elim=> [|len IH] start; first by []. by rewrite /= IH. Qed.

  Lemma initial_memory_domm: forall b,
      size (linearize_bufs b) < alloc_label ->
      domm (@initial_memory mt b) = fset (map word_of_nat (List.seq 0 (size (@initial_memory mt b)))).
  Proof.
    move=> b Htot.
    have Haw : alloc_label < 2 ^ (word_size mt) by rewrite /alloc_label ltn_exp2l.
    have Hb : size (linearize_bufs b) < 2 ^ (word_size mt)
      by exact: (ltn_trans Htot Haw).
    rewrite (initial_memory_size_eq Hb) seqE.
    exact: (initial_memory_domm_iota Hb).
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

  Lemma nth_error_nth {A} (d : A) l n x : nth_error l n = Some x -> nth d l n = x.
  Proof. elim: l n => [|y l IH] [|n] //=; first by move=> [= ->]. exact: IH. Qed.

  Lemma nth_error_lt {A} (l : seq A) : forall n x, nth_error l n = Some x -> n < size l.
  Proof. elim: l => [|y l IH] [|n] x //= H. rewrite ltnS. exact: (IH n x H). Qed.

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
          rewrite subn0. simpl size.
          replace ((size cde').+1 - 1) with (size cde').
          2: { rewrite subn1 //=. }
          have -> : acc.2 = size cde' by exact (encode_code_foldr_counter cde' lp offset).
          reflexivity.
      + simpl in Hnth.
        destruct (IH lp offset n' v Hnth) as [i' [t' [Hin' [Htag' Hval']]]].
        exists i', t'. split; [exact Hin' |]. split; [exact Htag' |].
        simpl size.
        replace (offset - 1 - ((size cde').+1 - 1 - n'.+1)) with (offset - 1 - (size cde' - 1 - n')).
        exact Hval'.
        { replace (size cde' - 1 - n') with (((size cde').+1 - 1 - n'.+1)); auto.
          rewrite !subn1. simpl. rewrite -addn1 addnC. rewrite subnDA. rewrite subn1. auto. }
  Qed.

  Lemma word_of_nat_inj: forall a b,
      a < 2^(word_size mt) -> b < 2^(word_size mt) ->
      word_of_nat (k := word_size mt) a = word_of_nat b -> a = b.
  Proof. move=> a b Ha Hb. exact: (won_inj Ha Hb). Qed.

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

  Lemma encode_code_foldr_tag: forall cde lp offset n v,
    nth_error (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
      (encode_instr_atom x lp (offset - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) cde).1 n = Some v ->
    exists i t, List.In (i, t) cde /\ taga v = t.
  Proof.
    intros cde. induction cde as [| [i0 t0] cde' IH]; intros lp offset n v Hnth.
    - simpl in Hnth. destruct n; discriminate.
    - simpl in Hnth.
      set acc := (foldr _ _ cde') in Hnth.
      destruct n as [| n'].
      +
        simpl in Hnth. injection Hnth => <-.
        exists i0, t0. split.
        * left. reflexivity.
        *
          unfold encode_instr_atom. simpl. reflexivity.
      +
        simpl in Hnth.
        destruct (IH lp offset n' v Hnth) as [i' [t' [Hin' Htag']]].
        exists i', t'. split.
        * right. exact Hin'.
        * exact Htag'.
  Qed.

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

  Lemma encode_code_is_code: forall cde pc w v,
    (forall i t, List.In (i, t) cde -> is_code t = true /\ vtag t = Other) ->
    encode_code cde pc w = Some v ->
    is_code (taga v) = true.
  Proof.
    intros cde pc w v Hwf H.
    destruct (encode_code_tag H) as [i [t [Hin Htag]]].
    rewrite Htag. exact (code_tags_wf_all Hwf Hin).1.
  Qed.


  Lemma valw_won (k n : nat) : val (@word_of_nat k n) = n %% 2 ^ k :> nat.
  Proof. by rewrite /word_of_nat valw_as_word. Qed.

  Lemma small_addr_mask_zero: forall x,
      x < alloc_label ->
      andw (@word_of_nat (word_size mt) x) (@mask mt NC) = 0%w.
  Proof.
    move=> x Hx. apply: andw_mask_low. rewrite valw_won.
    have Hx32 : x < 2 ^ word_size mt.
    { rewrite word_size_mt. apply: (leq_trans Hx). rewrite /alloc_label leq_exp2l //. }
    rewrite (modn_small Hx32). apply: (leq_trans Hx). exact: ltnW alloc_label_lt_word_NC.
  Qed.

  Lemma encode_code_initial_memory_disjoint: forall cde pb w v,
    size (linearize_bufs pb) + size cde < alloc_label ->
    initial_memory (mt := mt) pb w = Some v ->
    encode_code cde (size (@initial_memory mt pb)) w = None.
  Proof.
    move=> cde pb w v Hszl Hmem.
    have Haw : alloc_label < 2 ^ (word_size mt) by rewrite /alloc_label ltn_exp2l.
    have Htot : size (linearize_bufs pb) < alloc_label
      by apply: (leq_ltn_trans _ Hszl); exact: leq_addr.
    have Hb : size (linearize_bufs pb) < 2 ^ (word_size mt) by exact: (ltn_trans Htot Haw).
    have Hse := initial_memory_size_eq Hb.
    have Hsz : size (initial_memory (mt := mt) pb) + size cde < alloc_label by rewrite Hse.
    have Hsz2 : size (initial_memory (mt := mt) pb) + size cde < 2 ^ word_size mt.
    { apply: (leq_trans Hsz). apply: (leq_trans (ltnW alloc_label_lt_word_NC)).
      rewrite leq_exp2l //; exact: leq_subr. }
    have Hwd : w \in domm (initial_memory (mt := mt) pb) by apply/dommP; exists v.
    move: Hwd; rewrite (initial_memory_domm Htot) in_fset => /mapP[n Hn Hw].
    have Hnlt : n < size (initial_memory (mt := mt) pb)
      by move: Hn; rewrite seqE mem_iota add0n => /andP[_].
    case Henc: (encode_code cde (size (initial_memory (mt := mt) pb)) w) => [v'|] //.
    exfalso.
    destruct (encode_code_nth_inv Henc) as [m [Hwm [Hltm _]]].
    rewrite Hw in Hwm.
    have Hb1 : n < 2 ^ word_size mt by lia.
    have Hb2 : m + size (initial_memory (mt := mt) pb) < 2 ^ word_size mt by lia.
    have He := word_of_nat_inj Hb1 Hb2 Hwm.
    move: Hnlt; rewrite He; lia.
  Qed.

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

  Lemma component_memory_prefix_inj: forall n1 n2,
      n1 < 2 ^ NC -> n2 < 2 ^ NC ->
      @component_memory_prefix mt NC (ssrint.Posz n1) = @component_memory_prefix mt NC (ssrint.Posz n2) ->
      n1 = n2.
  Proof.
    move=> n1 n2 H1 H2 H.
    apply: component_memory_prefix_inj;
      [ exact: ltnW NC_lt_word | exact: H1 | exact: H2 | exact: H ].
  Qed.

  Lemma code_prefix_neq_data_prefix: forall c0,
      1 + c0 < 2 ^ NC ->
      @component_memory_prefix mt NC (ssrint.Posz 0) <>
        @component_memory_prefix mt NC (ssrint.Posz (1 + c0)).
  Proof.
    intros c0 Hb Heq.
    have H0 : 0 < 2 ^ NC by rewrite expn_gt0.
    move: (component_memory_prefix_inj H0 Hb Heq) => Habs.
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
      size (linearize_bufs pb) < alloc_label ->
      initial_memory (mt := mt) pb w = Some v ->
      andw w (mask (NC := NC)) = component_memory_prefix (NC := NC) (ssrint.Posz 0).
  Proof.
    move=> pb w v Htot Hmem.
    have Haw : alloc_label < 2 ^ (word_size mt) by rewrite /alloc_label ltn_exp2l.
    have Hb : size (linearize_bufs pb) < 2 ^ (word_size mt) by exact: (ltn_trans Htot Haw).
    have Hse := initial_memory_size_eq Hb.
    have Hsz : size (initial_memory (mt := mt) pb) < alloc_label by rewrite Hse.
    rewrite component_memory_prefix_zero.
    have Hwd : w \in domm (initial_memory (mt := mt) pb) by apply/dommP; exists v.
    move: Hwd; rewrite (initial_memory_domm Htot) in_fset => /mapP[n Hn ->].
    apply: small_addr_mask_zero.
    move: Hn; rewrite seqE mem_iota add0n => /andP[_ Hn].
    exact: (leq_trans Hn (ltnW Hsz)).
  Qed.
    
  Lemma findopt_bound: forall {A} (pred : A -> bool) (l : seq A) m,
      findopt pred l = Some m -> m < size l.
  Proof.
    intros A pred0 l. unfold findopt.
    induction l as [| x rest IH]; intros m Hfind.
    - simpl in Hfind. discriminate.
    - simpl in Hfind.
      destruct (foldr _ None rest) as [n |] eqn:Hrest.
      +
        inv Hfind.
        specialize (IH n Logic.eq_refl).
        simpl. rewrite ltnS. rewrite addn1.
        eauto.
      +
        destruct (pred0 x) eqn:Hpred.
        * injection Hfind => <-.
          simpl. done.
        * discriminate.
  Qed.
  

  Definition labels_disjoint_prefix := A.labels_disjoint_prefix.

  Lemma alloc_label_lt_imm: alloc_label < 2 ^ (imm_size mt).
  Proof. by rewrite /alloc_label ltn_exp2l. Qed.
  Lemma alloc_label_lt_w: alloc_label < 2 ^ (word_size mt).
  Proof. by rewrite /alloc_label ltn_exp2l. Qed.

  Lemma main_side :
    (Component.main \in domm ip
       /\ has (fun '(_,tag) => color tag == Component.main) (code p)
       /\ has (fun '(_,tag) => color tag == Component.main) (code p'))
    \/ (Component.main \in domm ic
       /\ has (fun '(_,tag) => color tag == Component.main) (code c)
       /\ has (fun '(_,tag) => color tag == Component.main) (code c')).
  Proof.
    have Hmn : prog_main p || prog_main c
      by exact: (cprog_main_existence Hprog_is_closed).
    case/orP: Hmn => Hm.
    - left.
      have Hin : Component.main \in domm ip
        by apply (wfprog_main_existence Hwfp); exact Hm.
      have Hin' : Component.main \in domm (prog_interface p') by rewrite -Hifacep.
      split=> //. split.
      + exact: (wf_color_has Hwfp Hin).
      + exact: (wf_color_has Hwfp' Hin').
    - right.
      have Hin : Component.main \in domm ic
        by apply (wfprog_main_existence Hwfc); exact Hm.
      have Hin' : Component.main \in domm (prog_interface c') by rewrite -Hifacec.
      split=> //. split.
      + exact: (wf_color_has Hwfc Hin).
      + exact: (wf_color_has Hwfc' Hin').
  Qed.

  Lemma find_rank_main_prog: exists start,
    find_rank (fun '(_,tag) => color tag == Component.main) (code prog) = Some start.
  Proof.
    have Hh : has (fun '(_,tag) => color tag == Component.main) (code prog).
    { rewrite /prog /= has_cat.
      case: main_side => [[_ [Hp _]]|[_ [Hc _]]]; [by rewrite Hp | by rewrite Hc orbT]. }
    have := find_rank_isSome Hh.
    by case: (find_rank _ _) => [st|] //; exists st.
  Qed.
  Lemma find_rank_main_prog': exists start,
    find_rank (fun '(_,tag) => color tag == Component.main) (code prog') = Some start.
  Proof.
    have Hh : has (fun '(_,tag) => color tag == Component.main) (code prog').
    { rewrite /prog' /= has_cat.
      case: main_side => [[_ [_ Hp']]|[_ [_ Hc']]]; [by rewrite Hp' | by rewrite Hc' orbT]. }
    have := find_rank_isSome Hh.
    by case: (find_rank _ _) => [st|] //; exists st.
  Qed.
  Lemma find_rank_main_prog'': exists start,
    find_rank (fun '(_,tag) => color tag == Component.main) (code prog'') = Some start.
  Proof.
    have Hh : has (fun '(_,tag) => color tag == Component.main) (code prog'').
    { rewrite /prog'' /= has_cat.
      case: main_side => [[_ [Hp _]]|[_ [_ Hc']]]; [by rewrite Hp | by rewrite Hc' orbT]. }
    have := find_rank_isSome Hh.
    by case: (find_rank _ _) => [st|] //; exists st.
  Qed.

  Lemma last_halt_cat (l1 l2 : @Merged.code mt) t :
    nth_error l2 (size l2 - 1) = Some (@MrHalt mt, t) ->
    nth_error (l1 ++ l2) (size (l1 ++ l2) - 1) = Some (@MrHalt mt, t).
  Proof.
    move=> H2.
    have Hl2 : 0 < size l2 by case: l2 H2.
    rewrite size_cat nth_error_app2; last by apply/leP; rewrite size_length; lia.
    rewrite -H2. congr nth_error. rewrite size_length. by lia.
  Qed.

  Lemma code_last_halt_prog :
    exists t, nth_error (code prog)   (size (code prog)   - 1) = Some (@MrHalt mt, t).
  Proof.
    case: (low_last_halt A.lin_wf_c) => [Hc0 | [t Ht]]; last first.
    - exists t. rewrite /prog /=. exact: (last_halt_cat _ Ht).
    - rewrite /prog /= Hc0 cats0.
      case: (low_last_halt A.lin_wf_p) => [Hp0 | [t Ht]]; last by exists t.
      exfalso. case: main_side => [[_ [Hp _]]|[_ [Hc _]]].
      + by rewrite Hp0 in Hp.
      + by rewrite Hc0 in Hc.
  Qed.
  Lemma code_last_halt_prog' :
    exists t, nth_error (code prog')  (size (code prog')  - 1) = Some (@MrHalt mt, t).
  Proof.
    case: (low_last_halt A.lin_wf_c') => [Hc0 | [t Ht]]; last first.
    - exists t. rewrite /prog' /=. exact: (last_halt_cat _ Ht).
    - rewrite /prog' /= Hc0 cats0.
      case: (low_last_halt A.lin_wf_p') => [Hp0 | [t Ht]]; last by exists t.
      exfalso. case: main_side => [[_ [_ Hp']]|[_ [_ Hc']]].
      + by rewrite Hp0 in Hp'.
      + by rewrite Hc0 in Hc'.
  Qed.
  Lemma code_last_halt_prog'' :
    exists t, nth_error (code prog'') (size (code prog'') - 1) = Some (@MrHalt mt, t).
  Proof.
    case: (low_last_halt A.lin_wf_c') => [Hc0 | [t Ht]]; last first.
    - exists t. rewrite /prog'' /=. exact: (last_halt_cat _ Ht).
    - rewrite /prog'' /= Hc0 cats0.
      case: (low_last_halt A.lin_wf_p) => [Hp0 | [t Ht]]; last by exists t.
      exfalso. case: main_side => [[_ [Hp _]]|[_ [_ Hc']]].
      + by rewrite Hp0 in Hp.
      + by rewrite Hc0 in Hc'.
  Qed.

  Lemma word_of_natDall (k a b : nat) :
    (@word_of_nat k a + @word_of_nat k b)%w = @word_of_nat k (a + b).
  Proof.
    apply: word_nat_inj. rewrite /addw.
    move: (valw_won k a) (valw_won k b) => Ea Eb. rewrite Ea Eb.
    rewrite (valw_won k (a + b)) valw_as_word. by rewrite modnDm.
  Qed.

  Lemma onew_word_of_nat : @onew (word_size mt) = @word_of_nat (word_size mt) 1.
  Proof. rewrite /onew /word_of_nat. congr as_word. Qed.

  Lemma swcast_word_of_nat_id : forall x,
      x < alloc_label ->
      @swcast _ (word_size mt) (@word_of_nat (imm_size mt) x) = @word_of_nat (word_size mt) x.
  Proof.
    move=> x Hx. have H15 : x < 2 ^ imm_size mt.
    { rewrite imm_size_mt. apply: (leq_trans Hx). rewrite /alloc_label leq_exp2l //. }
    by rewrite /swcast /word_of_nat (as_wordK H15).
  Qed.

  Lemma addw_word_of_nat_swcast : forall a b,
      a + b < alloc_label ->
      (@word_of_nat (word_size mt) a + @swcast _ (word_size mt) (@word_of_nat (imm_size mt) b))%w
        = @word_of_nat (word_size mt) (a + b).
  Proof.
    move=> a b Hab. have Hb : b < alloc_label by apply: (leq_ltn_trans (leq_addl a b) Hab).
    rewrite (swcast_word_of_nat_id Hb) word_of_natDall. by [].
  Qed.

  Lemma swcast_word_of_nat_zero :
      @swcast _ (word_size mt) (@word_of_nat (imm_size mt) 0) = zerow.
  Proof.
    have H : 0 < 2 ^ imm_size mt by rewrite imm_size_mt expn_gt0.
    rewrite /swcast /word_of_nat (as_wordK H) /zerow. exact: erefl.
  Qed.

  Lemma word_of_nat_succ : forall a,
      (@word_of_nat (word_size mt) a + 1)%w = @word_of_nat (word_size mt) (a + 1).
  Proof.
    move=> a. rewrite onew_word_of_nat word_of_natDall. by [].
  Qed.

  Lemma encode_code_bnz_target: forall cde pc0 w v r n,
      (forall i t, List.In (i, t) cde -> is_code t = true /\ vtag t = Other) ->
      (forall n r l t, nth_error cde n = Some (@MrBnz mt r l, t) ->
         exists m, findopt (fun p : @Merged.instr mt * mem_tag =>
                        match p.1 with MrLabel l0 => l == l0 | _ => false end) cde = Some m) ->
      pc0 + size cde < alloc_label ->
      encode_code cde pc0 w = Some v ->
      decode_instr (vala v) = Some (Bnz r n) ->
      exists v', encode_code cde pc0 (addw w (swcast n)) = Some v'
            /\ is_code (taga v') = true.
  Proof.
    intros cde pc0 w v r n0 Hwf Hres Hsize Henc Hdec.
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
      have Henc_m := encode_code_nth (ltn_trans Hsize alloc_label_lt_w) Hv'.
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
      +
        exists v'. split.
        * suffices Heq: (w + swcast n0)%w = word_of_nat (m + pc0) by rewrite Heq.
          rewrite Hw.
          have Hn' : n0 = word_of_nat (m - k).
          { rewrite -Hn. congr word_of_nat. by rewrite HX Hoff. }
          rewrite Hn'.
          have Hbound : (k + pc0) + (m - k) < alloc_label.
          { move/leP: Hkm => Hkm'.
            have Hpm : (pc0 + m < alloc_label)%coq_nat.
            { apply/ltP. apply: (ltn_trans _ Hsize). by rewrite ltn_add2l. }
            apply/ltP. lia. }
          rewrite addw_word_of_nat_swcast; last exact Hbound.
          congr word_of_nat. move/leP: Hkm => Hkm'. lia.
        * destruct (encode_code_foldr_tag Hv') as [i' [t' [Hin' Htag']]].
          rewrite Htag'. exact (code_tags_wf_all Hwf Hin').1.
      +
        have Hmk0: m - k = 0 by apply/eqP; rewrite subn_eq0; exact (ltnW Hmk).
        exists v. split.
        * have Hn0 : n0 = word_of_nat 0.
          { rewrite -Hn. congr word_of_nat. by rewrite HX Hoff Hmk0. }
          rewrite Hn0 swcast_word_of_nat_zero addw0. exact Henc.
        * exact (encode_code_is_code Hwf Henc).
    - exfalso.
      have [m' Hfind'] := Hres _ _ _ _ Hnth_cde.
      rewrite Hfind' in Hfind. discriminate.
  Qed.

  Lemma encode_code_jal_target: forall cde pc0 w v n,
      (forall i t, List.In (i, t) cde -> is_code t = true /\ vtag t = Other) ->
      (forall n l t, nth_error cde n = Some (@MrJal mt l, t) -> l <> alloc_label ->
         exists m, findopt (fun p : @Merged.instr mt * mem_tag =>
                        match p.1 with MrLabel l0 => l == l0 | _ => false end) cde = Some m) ->
      pc0 + size cde < alloc_label ->
      encode_code cde pc0 w = Some v ->
      decode_instr (vala v) = Some (Jal n) ->
      (exists v', encode_code cde pc0 (swcast n) = Some v'
             /\ is_code (taga v') = true)
      \/ (word_of_nat alloc_label = n).
  Proof.
    intros cde pc0 w v n0 Hwf Hres Hsize Henc Hdec.
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
      destruct (nth_error_Some_ex Hm_bound2) as [v' Hv'].
      have Henc_m := encode_code_nth (ltn_trans Hsize alloc_label_lt_w) Hv'.
      exists v'. split.
      + have Hpm : pc0 + m < alloc_label.
        { apply: (ltn_trans _ Hsize). by rewrite ltn_add2l. }
        rewrite -Hn (swcast_word_of_nat_id Hpm) (addnC pc0 m). exact Henc_m.
      +
        destruct (encode_code_foldr_tag Hv') as [i' [t' [Hin' Htag']]].
        rewrite Htag'. exact (code_tags_wf_all Hwf Hin').1.
    -
      simpl in Hn.
      destruct (l == alloc_label) eqn:Halloc.
      +
        right.
        move/eqP : Halloc => Halloc. subst l.
        eauto.
      +
        exfalso.
        have Hneq: l <> alloc_label by move/eqP: Halloc.
        have [m' Hfind'] := Hres _ _ _ Hnth_cde Hneq.
        rewrite Hfind' in Hfind. discriminate.
  Qed.
  
  
  Lemma encode_code_last_is_halt : forall cde pc0 v,
    pc0 + size cde < 2 ^ (word_size mt) ->
    (exists t, nth_error cde (size cde - 1) = Some (@MrHalt mt, t)) ->
    encode_code cde pc0 (word_of_nat ((size cde - 1) + pc0)) = Some v ->
    decode_instr (vala v) = Some (Halt _).
  Proof.
    move=> cde pc0 v Hsz [t Ht] Henc.
    destruct (encode_code_nth_inv Henc) as [n [Hw [Hlt Hnth]]].
    have Hn : n = size cde - 1.
    { have Hb1 : (size cde - 1) + pc0 < 2 ^ word_size mt by lia.
      have Hb2 : n + pc0 < 2 ^ word_size mt by lia.
      have He := word_of_nat_inj Hb1 Hb2 Hw. lia. }
    subst n.
    destruct (encode_code_foldr_nth Hnth) as [i [t' [Hnth_cde [Htag Hval]]]].
    move: Hnth_cde; rewrite Ht => -[= Hi _]. subst i.
    by rewrite Hval /instr_merged_to_mp /encode_instr_mp encodeK.
  Qed.

  Lemma encode_code_end_condition: forall cde pc0 w v,
    (forall i t, List.In (i, t) cde -> is_code t = true /\ vtag t = Other) ->
    (exists t, nth_error cde (size cde - 1) = Some (@MrHalt mt, t)) ->
    encode_code cde pc0 w = Some v ->
    is_code (taga v) ->
    pc0 + size cde < 2 ^ (word_size mt) ->
    (decode_instr (vala v) = Some (Halt _)) \/
    (exists v', encode_code cde pc0 (w + 1)%w = Some v'
           /\ is_code (taga v') = true).
  Proof.
    intros cde pc0 w v Hwf Hlast Henc Hcode Hsz_ec.
    destruct (encode_code_nth_inv Henc) as [n [Hw [Hlt Hnth]]].
    case: (ltnP (n + 1) (size cde)) => [Hlt' | Hge].
    -
      right.
      have Hlt2 : n + 1 < size (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
        (encode_instr_atom x
          (fun l default => match findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) cde
           with Some m => pc0 + m | None => if l == alloc_label then l else default end)
          (pc0 + size cde - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) cde).1.
      { rewrite encode_code_foldr_size. exact Hlt'. }
      destruct (nth_error_Some_ex Hlt2) as [v' Hv'].
      have Henc_succ := encode_code_nth Hsz_ec Hv'.
      exists v'. split.
      + rewrite Hw word_of_nat_succ.
        have -> : (n + pc0) + 1 = n + 1 + pc0 by lia.
        exact Henc_succ.
      + destruct (encode_code_foldr_tag Hv') as [i' [t' [Hin' Htag']]].
        rewrite Htag'. exact (code_tags_wf_all Hwf Hin').1.
    -
      left.
      have Hnlast : n = size cde - 1.
      { move/ltP: Hlt => ?. move/leP: Hge => ?. lia. }
      apply: (encode_code_last_is_halt Hsz_ec Hlast).
      rewrite Hw Hnlast in Henc. exact Henc.
  Qed.

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

  Definition code_tags_wf_p := low_tags A.lin_wf_p.
  Definition code_tags_wf_c := low_tags A.lin_wf_c.
  Definition code_tags_wf_p' := low_tags A.lin_wf_p'.
  Definition code_tags_wf_c' := low_tags A.lin_wf_c'.

  Lemma code_color_p : forall i t, List.In (i, t) (code p) -> color t \in domm ip.
  Proof. exact: (low_colors A.lin_wf_p). Qed.
  Lemma code_color_c : forall i t, List.In (i, t) (code c) -> color t \in domm ic.
  Proof. exact: (low_colors A.lin_wf_c). Qed.
  Lemma code_color_p' : forall i t, List.In (i, t) (code p') -> color t \in domm ip.
  Proof. rewrite /ip Hifacep. exact: (low_colors A.lin_wf_p'). Qed.
  Lemma code_color_c' : forall i t, List.In (i, t) (code c') -> color t \in domm ic.
  Proof. rewrite /ic Hifacec. exact: (low_colors A.lin_wf_c'). Qed.

  Lemma alloc_label_not_in_encode_code: forall cde pc0,
      pc0 + size cde < alloc_label ->
      encode_code cde pc0 (word_of_nat alloc_label) = None.
  Proof.
    move=> cde pc0 Hsz.
    case Henc: (encode_code cde pc0 (word_of_nat alloc_label)) => [v|] //.
    exfalso.
    have [m [Hwm [Hltm _]]] := encode_code_nth_inv Henc.
    have Hb1 : alloc_label < 2 ^ (word_size mt) by exact: alloc_label_lt_w.
    have Hb2 : m + pc0 < 2 ^ (word_size mt).
    { apply: (ltn_trans _ Hb1). by lia. }
    have He := word_of_nat_inj Hb1 Hb2 Hwm.
    by lia.
  Qed.
    
  Lemma alloc_label_not_in_initial_memory: forall pb,
      size (linearize_bufs pb) < alloc_label ->
      initial_memory (mt := mt) pb (word_of_nat alloc_label) = None.
  Proof.
    move=> pb Htot.
    have Hb : size (linearize_bufs pb) < 2 ^ (word_size mt)
      by exact: (ltn_trans Htot alloc_label_lt_w).
    exact: (alloc_label_not_in_initial_memory_bl Hb Htot).
  Qed.
  
  Lemma memory_size:
    size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c))) +
      size (code p ++ code c) < alloc_label.
  Proof.
    have Hlin := A.memory_size_lin.
    have Hb : size (linearize_bufs (unionm (prog_buffers p) (prog_buffers c))) < 2 ^ (word_size mt).
    { apply: (ltn_trans _ alloc_label_lt_w). by lia. }
    by rewrite (initial_memory_size_eq Hb).
  Qed.

  Lemma memory_size':
    size (initial_memory (mt := mt) (unionm (prog_buffers p') (prog_buffers c'))) +
      size (code p' ++ code c') < alloc_label.
  Proof.
    have Hlin := A.memory_size_lin'.
    have Hb : size (linearize_bufs (unionm (prog_buffers p') (prog_buffers c'))) < 2 ^ (word_size mt).
    { apply: (ltn_trans _ alloc_label_lt_w). by lia. }
    by rewrite (initial_memory_size_eq Hb).
  Qed.

  Lemma memory_size'':
    size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c'))) +
      size (code p ++ code c') < alloc_label.
  Proof.
    have Hlin := A.memory_size_lin''.
    have Hb : size (linearize_bufs (unionm (prog_buffers p) (prog_buffers c'))) < 2 ^ (word_size mt).
    { apply: (ltn_trans _ alloc_label_lt_w). by lia. }
    by rewrite (initial_memory_size_eq Hb).
  Qed.

  Lemma lin_size_wo_code:
    size (linearize_bufs (unionm (prog_buffers p) (prog_buffers c))) < alloc_label.
  Proof. apply: (leq_ltn_trans _ A.memory_size_lin). exact: leq_addr. Qed.
  Lemma lin_size_wo_code':
    size (linearize_bufs (unionm (prog_buffers p') (prog_buffers c'))) < alloc_label.
  Proof. apply: (leq_ltn_trans _ A.memory_size_lin'). exact: leq_addr. Qed.
  Lemma lin_size_wo_code'':
    size (linearize_bufs (unionm (prog_buffers p) (prog_buffers c'))) < alloc_label.
  Proof. apply: (leq_ltn_trans _ A.memory_size_lin''). exact: leq_addr. Qed.

  Lemma domm_buffers_p: domm (prog_buffers p) = domm ip.
  Proof. exact: (esym (wfprog_defined_buffers Hwfp)). Qed.
  Lemma domm_buffers_c: domm (prog_buffers c) = domm ic.
  Proof. exact: (esym (wfprog_defined_buffers Hwfc)). Qed.
  Lemma domm_buffers_p': domm (prog_buffers p') = domm ip.
  Proof. rewrite /ip Hifacep. exact: (esym (wfprog_defined_buffers Hwfp')). Qed.
  Lemma domm_buffers_c': domm (prog_buffers c') = domm ic.
  Proof. rewrite /ic Hifacec. exact: (esym (wfprog_defined_buffers Hwfc')). Qed.

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

  Definition bufs_shape_p_p' : bufs_shape (prog_buffers p) = bufs_shape (prog_buffers p')
    := A.bufs_shape_p_p'.
  Definition bufs_shape_c_c' : bufs_shape (prog_buffers c) = bufs_shape (prog_buffers c')
    := A.bufs_shape_c_c'.

  Lemma bufs_shape_prog_prog'' :
    bufs_shape (prog_buffers prog) = bufs_shape (prog_buffers prog'').
  Proof.
    rewrite /prog /prog'' /program_link /=.
    exact: (bufs_shape_unionm_r _ bufs_shape_c_c').
  Qed.

  Lemma bufs_shape_prog'_prog'' :
    bufs_shape (prog_buffers prog') = bufs_shape (prog_buffers prog'').
  Proof.
    rewrite /prog' /prog'' /program_link /=.
    exact: (bufs_shape_unionm_l _ (esym bufs_shape_p_p')).
  Qed.

  Lemma total_bound_prog : size (linearize_bufs (prog_buffers prog)) < 2 ^ (word_size mt).
  Proof. apply: (ltn_trans _ alloc_label_lt_w). exact: lin_size_wo_code. Qed.

  Lemma total_bound_prog' : size (linearize_bufs (prog_buffers prog')) < 2 ^ (word_size mt).
  Proof. apply: (ltn_trans _ alloc_label_lt_w). exact: lin_size_wo_code'. Qed.

  Lemma align_data_size: size (initial_memory (mt := mt) (prog_buffers prog'))
                       = size (initial_memory (mt := mt) (prog_buffers prog'')).
  Proof. exact: (initial_memory_shape_size bufs_shape_prog'_prog'' total_bound_prog'). Qed.

  Lemma align_data_size_left: size (initial_memory (mt := mt) (prog_buffers prog))
                            = size (initial_memory (mt := mt) (prog_buffers prog'')).
  Proof. exact: (initial_memory_shape_size bufs_shape_prog_prog'' total_bound_prog). Qed.

  Lemma align_data_domm: domm (initial_memory (mt := mt) (prog_buffers prog'))
                       = domm (initial_memory (mt := mt) (prog_buffers prog'')).
  Proof. exact: (initial_memory_shape_domm bufs_shape_prog'_prog'' total_bound_prog'). Qed.

  Lemma align_data_domm_left: domm (initial_memory (mt := mt) (prog_buffers prog))
                            = domm (initial_memory (mt := mt) (prog_buffers prog'')).
  Proof. exact: (initial_memory_shape_domm bufs_shape_prog_prog'' total_bound_prog). Qed.

  Lemma align_data_domm_u :
    domm (@initial_memory mt (unionm (prog_buffers p') (prog_buffers c')))
    = domm (@initial_memory mt (unionm (prog_buffers p) (prog_buffers c'))).
  Proof. exact: align_data_domm. Qed.

  Lemma align_data_domm_left_u :
    domm (@initial_memory mt (unionm (prog_buffers p) (prog_buffers c)))
    = domm (@initial_memory mt (unionm (prog_buffers p) (prog_buffers c'))).
  Proof. exact: align_data_domm_left. Qed.

  Lemma align_data_domm_12_u :
    domm (@initial_memory mt (unionm (prog_buffers p') (prog_buffers c')))
    = domm (@initial_memory mt (unionm (prog_buffers p) (prog_buffers c))).
  Proof. by rewrite align_data_domm_u -align_data_domm_left_u. Qed.

  Lemma init_data_left_31 : forall w (d : atom (mword mt) mem_tag),
    color (taga d) \in domm ip ->
    @initial_memory mt (unionm (prog_buffers p) (prog_buffers c')) w = Some d ->
    @initial_memory mt (unionm (prog_buffers p) (prog_buffers c)) w = Some d.
  Proof.
    move=> w d Hcol Hinit.
    have Hbp : color (taga d) \in domm (prog_buffers p) by rewrite domm_buffers_p.
    apply: (initial_memory_shape_agree _ _ Hinit).
    - exact: (bufs_shape_unionm_r _ (esym bufs_shape_c_c')).
    - apply: (ltn_trans _ alloc_label_lt_w). exact: lin_size_wo_code''.
    - exact: (unionm_agree_l (prog_buffers c') (prog_buffers c) Hbp).
  Qed.

  Lemma init_data_left_13 : forall w (d : atom (mword mt) mem_tag),
    color (taga d) \in domm ip ->
    @initial_memory mt (unionm (prog_buffers p) (prog_buffers c)) w = Some d ->
    @initial_memory mt (unionm (prog_buffers p) (prog_buffers c')) w = Some d.
  Proof.
    move=> w d Hcol Hinit.
    have Hbp : color (taga d) \in domm (prog_buffers p) by rewrite domm_buffers_p.
    apply: (initial_memory_shape_agree _ _ Hinit).
    - exact: (bufs_shape_unionm_r _ bufs_shape_c_c').
    - apply: (ltn_trans _ alloc_label_lt_w). exact: lin_size_wo_code.
    - exact: (unionm_agree_l (prog_buffers c) (prog_buffers c') Hbp).
  Qed.

  Lemma init_data_right_32 : forall w (d : atom (mword mt) mem_tag),
    color (taga d) \in domm ic ->
    @initial_memory mt (unionm (prog_buffers p) (prog_buffers c')) w = Some d ->
    @initial_memory mt (unionm (prog_buffers p') (prog_buffers c')) w = Some d.
  Proof.
    move=> w d Hcol Hinit.
    pose proof Hmergeable_ifaces as [[_ Hdis] _].
    have HD : color (taga d) \notin domm ip.
    { move: Hdis. rewrite fdisjointC => /fdisjointP HDd. exact: (HDd _ Hcol). }
    have Hnp : color (taga d) \notin domm (prog_buffers p) by rewrite domm_buffers_p.
    have Hnp' : color (taga d) \notin domm (prog_buffers p') by rewrite domm_buffers_p'.
    apply: (initial_memory_shape_agree _ _ Hinit).
    - exact: (bufs_shape_unionm_l _ bufs_shape_p_p').
    - apply: (ltn_trans _ alloc_label_lt_w). exact: lin_size_wo_code''.
    - exact: (unionm_agree_r (prog_buffers c') Hnp Hnp').
  Qed.

  Lemma init_data_right_23 : forall w (d : atom (mword mt) mem_tag),
    color (taga d) \in domm ic ->
    @initial_memory mt (unionm (prog_buffers p') (prog_buffers c')) w = Some d ->
    @initial_memory mt (unionm (prog_buffers p) (prog_buffers c')) w = Some d.
  Proof.
    move=> w d Hcol Hinit.
    pose proof Hmergeable_ifaces as [[_ Hdis] _].
    have HD : color (taga d) \notin domm ip.
    { move: Hdis. rewrite fdisjointC => /fdisjointP HDd. exact: (HDd _ Hcol). }
    have Hnp : color (taga d) \notin domm (prog_buffers p) by rewrite domm_buffers_p.
    have Hnp' : color (taga d) \notin domm (prog_buffers p') by rewrite domm_buffers_p'.
    apply: (initial_memory_shape_agree _ _ Hinit).
    - exact: (bufs_shape_unionm_l _ (esym bufs_shape_p_p')).
    - apply: (ltn_trans _ alloc_label_lt_w). exact: lin_size_wo_code'.
    - exact: (unionm_agree_r (prog_buffers c') Hnp' Hnp).
  Qed.

  Lemma encode_int_of_nat : forall n, encode_int (Z.of_nat n) = ssrint.Posz n.
  Proof. case=> [//|m] /=. by rewrite nat_of_pos_succ. Qed.

  
  Lemma size_domm_fmap: forall (T: ordType) (S: Type) (m: {fmap T -> S}),
      size (domm m) = size m.
  Proof. by move=> T S m; rewrite val_domm size_map. Qed.

  Lemma find_rank'_cat {T} (f: pred T) (l1 l2: seq T) n:
    find_rank' f (l1 ++ l2) n =
    if find_rank' f l1 n is Some m then Some m else find_rank' f l2 (n + size l1).
  Proof.
    elim: l1 n => [|x l1 IH] n /=.
    - by rewrite addn0.
    - case: (f x) => //. by rewrite IH addnS addSn.
  Qed.

  Lemma find_rank'_none {T} (f: pred T) (l: seq T) n:
    (forall x, List.In x l -> ~~ f x) -> find_rank' f l n = None.
  Proof.
    elim: l n => [|x l IH] n //= Hno.
    have Hfx : f x = false. { apply/negbTE. apply: Hno. simpl. by left. }
    rewrite Hfx /=. apply: IH => y Hy. apply: Hno. simpl. by right.
  Qed.

  Lemma find_rank_app_no_match {T} (f: pred T) (l1 l2: seq T):
    (forall x, List.In x l2 -> ~~ f x) -> find_rank f (l1 ++ l2) = find_rank f l1.
  Proof.
    move=> Hno. rewrite /find_rank find_rank'_cat.
    have Hnone : find_rank' f l2 (0 + size l1) = None.
    { apply: find_rank'_none. exact Hno. }
    rewrite Hnone. by case: (find_rank' f l1 0).
  Qed.

  Lemma find_rank'E {T} (f: pred T) (l: seq T) k:
    find_rank' f l k = if has f l then Some (k + seq.find f l) else None.
  Proof.
    elim: l k => [|x l IH] k //=.
    case: (f x) => /=.
    - by rewrite addn0.
    - by rewrite IH addnS.
  Qed.

  Lemma find_rankE {T} (f: pred T) (l: seq T):
    find_rank f l = if has f l then Some (seq.find f l) else None.
  Proof. by rewrite /find_rank find_rank'E add0n. Qed.

  Lemma find_rank_Some_find {T} (f: pred T) (l: seq T) n:
    find_rank f l = Some n -> seq.find f l = n /\ n < size l.
  Proof.
    rewrite find_rankE; case: ifP => Hhas // [<-]. split=> //. by rewrite -has_find.
  Qed.

  Lemma findopt_cons T (pred : T -> bool) x s :
    findopt pred (x :: s)
    = if findopt pred s is Some n then Some (n + 1) else if pred x then Some 0 else None.
  Proof. rewrite /findopt /=. by case: (foldr _ _ s). Qed.

  Lemma findopt_cat T (pred : T -> bool) s1 s2 :
    findopt pred (s1 ++ s2)
    = if findopt pred s2 is Some n then Some (size s1 + n) else findopt pred s1.
  Proof.
    elim: s1 => [|x s1 IH].
    - by rewrite cat0s; case: (findopt pred s2) => [n|].
    - rewrite cat_cons !findopt_cons IH.
      case: (findopt pred s2) => [n|] //=.
      by congr Some; lia.
  Qed.

  Lemma findopt_cat_defined T (pred : T -> bool) (s1 s2 : seq T) :
    (exists m, findopt pred s1 = Some m) \/ (exists m, findopt pred s2 = Some m) ->
    exists m, findopt pred (s1 ++ s2) = Some m.
  Proof.
    rewrite findopt_cat. case E: (findopt pred s2) => [n|].
    - move=> _. by exists (size s1 + n).
    - case=> [[m Hm]|[m Hm]]; first by exists m.
      by rewrite Hm in E.
  Qed.

  Lemma cat_cell_split (l1 l2 : @Merged.code mt) k i t :
    nth_error (l1 ++ l2) k = Some (i, t) ->
    (k < size l1 /\ nth_error l1 k = Some (i, t))
    \/ (size l1 <= k /\ nth_error l2 (k - size l1) = Some (i, t)).
  Proof.
    move=> Hk.
    case Hlt : (k < size l1).
    - left. split=> //. move: Hk. rewrite nth_error_app1 //.
      by apply/ltP; rewrite size_length.
    - right. have Hge : size l1 <= k by rewrite leqNgt Hlt.
      split=> //. move: Hk. rewrite nth_error_app2;
        last by apply/leP; rewrite size_length.
      by [].
  Qed.

  Lemma bnz_resolved_prog : forall n r l t,
      nth_error (code prog) n = Some (@MrBnz mt r l, t) ->
      exists m, findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog) = Some m.
  Proof.
    move=> n r l t Hn.
    have Hn' : nth_error (code p ++ code c) n = Some (@MrBnz mt r l, t) by exact Hn.
    have -> : code prog = code p ++ code c by [].
    apply: findopt_cat_defined.
    case: (cat_cell_split Hn') => [[_ Hcell] | [_ Hcell]].
    - left. exact: (low_bnz_resolved A.lin_wf_p Hcell).
    - right. exact: (low_bnz_resolved A.lin_wf_c Hcell).
  Qed.
  Lemma bnz_resolved_prog' : forall n r l t,
      nth_error (code prog') n = Some (@MrBnz mt r l, t) ->
      exists m, findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog') = Some m.
  Proof.
    move=> n r l t Hn.
    have Hn' : nth_error (code p' ++ code c') n = Some (@MrBnz mt r l, t) by exact Hn.
    have -> : code prog' = code p' ++ code c' by [].
    apply: findopt_cat_defined.
    case: (cat_cell_split Hn') => [[_ Hcell] | [_ Hcell]].
    - left. exact: (low_bnz_resolved A.lin_wf_p' Hcell).
    - right. exact: (low_bnz_resolved A.lin_wf_c' Hcell).
  Qed.
  Lemma bnz_resolved_prog'' : forall n r l t,
      nth_error (code prog'') n = Some (@MrBnz mt r l, t) ->
      exists m, findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog'') = Some m.
  Proof.
    move=> n r l t Hn.
    have Hn' : nth_error (code p ++ code c') n = Some (@MrBnz mt r l, t) by exact Hn.
    have -> : code prog'' = code p ++ code c' by [].
    apply: findopt_cat_defined.
    case: (cat_cell_split Hn') => [[_ Hcell] | [_ Hcell]].
    - left. exact: (low_bnz_resolved A.lin_wf_p Hcell).
    - right. exact: (low_bnz_resolved A.lin_wf_c' Hcell).
  Qed.

  Lemma jal_resolved_prog : forall n l t,
      nth_error (code prog) n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      exists m, findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog) = Some m.
  Proof.
    move=> n l t Hn Hne.
    have Hn' : nth_error (code p ++ code c) n = Some (@MrJal mt l, t) by exact Hn.
    have -> : code prog = code p ++ code c by [].
    apply: findopt_cat_defined.
    case: (cat_cell_split Hn') => [[_ Hcell] | [_ Hcell]].
    - case Hloc : (findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code p)) => [m|].
      + left. by exists m.
      + right.
        have [mc [mc' [ic_ [i_ [tc [Hfc _ _ _]]]]]] := A.jal_cross_p Hcell Hne Hloc.
        exists mc. exact: Hfc.
    - case Hloc : (findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code c)) => [m|].
      + right. by exists m.
      + left.
        have [mp Hmp] := A.jal_cross_cone Hcell Hne Hloc.
        exists mp. exact: Hmp.
  Qed.
  Lemma jal_resolved_prog' : forall n l t,
      nth_error (code prog') n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      exists m, findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog') = Some m.
  Proof.
    move=> n l t Hn Hne.
    have Hn' : nth_error (code p' ++ code c') n = Some (@MrJal mt l, t) by exact Hn.
    have -> : code prog' = code p' ++ code c' by [].
    apply: findopt_cat_defined.
    case: (cat_cell_split Hn') => [[_ Hcell] | [_ Hcell]].
    - case Hloc : (findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code p')) => [m|].
      + left. by exists m.
      + right.
        have [mc Hmc] := A.jal_cross_p'one Hcell Hne Hloc.
        exists mc. exact: Hmc.
    - case Hloc : (findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code c')) => [m|].
      + right. by exists m.
      + left.
        have [mp' [mp [ip_ [i_ [tp [Hfp' _ _ _]]]]]] := A.jal_cross_c' Hcell Hne Hloc.
        exists mp'. exact: Hfp'.
  Qed.
  Lemma jal_resolved_prog'' : forall n l t,
      nth_error (code prog'') n = Some (@MrJal mt l, t) -> l <> alloc_label ->
      exists m, findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog'') = Some m.
  Proof.
    move=> n l t Hn Hne.
    have Hn' : nth_error (code p ++ code c') n = Some (@MrJal mt l, t) by exact Hn.
    have -> : code prog'' = code p ++ code c' by [].
    apply: findopt_cat_defined.
    case: (cat_cell_split Hn') => [[_ Hcell] | [_ Hcell]].
    - case Hloc : (findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code p)) => [m|].
      + left. by exists m.
      + right.
        have [mc [mc' [ic_ [i_ [tc [_ Hfc' _ _]]]]]] := A.jal_cross_p Hcell Hne Hloc.
        exists mc'. exact: Hfc'.
    - case Hloc : (findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code c')) => [m|].
      + right. by exists m.
      + left.
        have [mp' [mp [ip_ [i_ [tp [_ Hfp _ _]]]]]] := A.jal_cross_c' Hcell Hne Hloc.
        exists mp. exact: Hfp.
  Qed.


  Lemma bnz_findopt_shared: forall k r l t,
      k < size (code p) ->
      nth_error (code prog) k = Some (@MrBnz mt r l, t) ->
      findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog)
      = findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog'').
  Proof.
    move=> k r l t Hkp Hk.
    have Hkp_p : nth_error (code p) k = Some (@MrBnz mt r l, t).
    { move: Hk. have ->: code prog = code p ++ code c by [].
      rewrite nth_error_app1; last by apply/ltP; exact: Hkp. by []. }
    have [m0 Hm0] := low_bnz_resolved A.lin_wf_p Hkp_p.
    have [Hnc Hnc'] :
      findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code c) = None
      /\ findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code c') = None.
    { apply: labels_disjoint_prefix. by rewrite Hm0. }
    have ->: code prog = code p ++ code c by [].
    have ->: code prog'' = code p ++ code c' by [].
    by rewrite !findopt_cat Hnc Hnc'.
  Qed.

  Lemma bnz_findopt_shared': forall k k'' r l t m' m'',
      size (code p') <= k ->
      k'' = size (code p) + (k - size (code p')) ->
      nth_error (code prog') k = Some (@MrBnz mt r l, t) ->
      findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog') = Some m' ->
      findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog'') = Some m'' ->
      m' - k = m'' - k''.
  Proof.
    move=> k k'' r l t m' m'' Hsfx Hk''eq Hk Hfo' Hfo''.
    have Hj : nth_error (code c') (k - size (code p')) = Some (@MrBnz mt r l, t).
    { move: Hk. have ->: code prog' = code p' ++ code c' by [].
      rewrite nth_error_app2; last by apply/leP; exact: Hsfx. by []. }
    have [n Hn] := low_bnz_resolved A.lin_wf_c' Hj.
    have Em' : m' = size (code p') + n.
    { move: Hfo'. have ->: code prog' = code p' ++ code c' by [].
      rewrite findopt_cat Hn => -[<-]. by []. }
    have Em'' : m'' = size (code p) + n.
    { move: Hfo''. have ->: code prog'' = code p ++ code c' by [].
      rewrite findopt_cat Hn => -[<-]. by []. }
    subst m' m''. rewrite Hk''eq. lia.
  Qed.

  Lemma no_mrlabel_alloc_prog :
    findopt (fun p : Merged.instr * mem_tag => match p.1 with MrLabel l0 => alloc_label == l0 | _ => false end) (code prog) = None.
  Proof.
    rewrite /prog /= findopt_cat.
    have -> := (low_no_alloc A.lin_wf_c). exact: (low_no_alloc A.lin_wf_p).
  Qed.
  Lemma no_mrlabel_alloc_prog' :
    findopt (fun p : Merged.instr * mem_tag => match p.1 with MrLabel l0 => alloc_label == l0 | _ => false end) (code prog') = None.
  Proof.
    rewrite /prog' /= findopt_cat.
    have -> := (low_no_alloc A.lin_wf_c'). exact: (low_no_alloc A.lin_wf_p').
  Qed.
  Lemma no_mrlabel_alloc_prog'' :
    findopt (fun p : Merged.instr * mem_tag => match p.1 with MrLabel l0 => alloc_label == l0 | _ => false end) (code prog'') = None.
  Proof.
    rewrite /prog'' /= findopt_cat.
    have -> := (low_no_alloc A.lin_wf_c'). exact: (low_no_alloc A.lin_wf_p).
  Qed.

  Lemma word_of_nat_inj_imm: forall a b,
      a < 2 ^ (imm_size mt) -> b < 2 ^ (imm_size mt) ->
      @word_of_nat (imm_size mt) a = word_of_nat b -> a = b.
  Proof. move=> a b Ha Hb. exact: (won_inj Ha Hb). Qed.

  Lemma jal_alloc_iff : forall cde pc0 k l t a n,
    pc0 + size cde < alloc_label ->
    findopt (fun p : Merged.instr * mem_tag => match p.1 with MrLabel l0 => alloc_label == l0 | _ => false end) cde = None ->
    nth_error cde k = Some (MrJal l, t) ->
    encode_code cde pc0 (word_of_nat (k + pc0)) = Some a ->
    decode_instr (vala a) = Some (Jal n) ->
    (word_of_nat alloc_label = n) <-> (l = alloc_label).
  Proof.
    intros cde pc0 k l t a n Hsize Hno Hnth_cde Henc Hdec.
    have Hk_lt : k < size cde.
    { apply/ltP. apply (proj1 (nth_error_Some cde k)). by rewrite Hnth_cde. }
    have HsizeP : (pc0 + size cde < alloc_label)%coq_nat by apply/ltP.
    have Hk_ltP : (k < size cde)%coq_nat by apply/ltP.
    have Halloc_wP : (alloc_label < 2 ^ word_size mt)%coq_nat by apply/ltP; exact alloc_label_lt_w.
    have Halloc_iP : (alloc_label < 2 ^ imm_size mt)%coq_nat by apply/ltP; exact alloc_label_lt_imm.
    destruct (encode_code_nth_inv Henc) as [k0 [Hw0 [Hlt0 Hnth0]]].
    have Hlt0P : (k0 < size cde)%coq_nat by apply/ltP.
    have Hk0 : k0 = k.
    { have Hbk : k + pc0 < 2 ^ word_size mt by apply/ltP; lia.
      have Hbk0 : k0 + pc0 < 2 ^ word_size mt by apply/ltP; lia.
      have := word_of_nat_inj Hbk Hbk0 Hw0. lia. }
    subst k0.
    destruct (encode_code_foldr_nth Hnth0) as [i [t0 [Hnth_cde0 [Htag0 Hval]]]].
    rewrite Hnth_cde in Hnth_cde0. injection Hnth_cde0 => Ht0 Hi. subst i t0.
    rewrite Hval /instr_merged_to_mp /encode_instr_mp encodeK in Hdec.
    simpl in Hdec. injection Hdec => Hn.
    set POS := pc0 + size cde - 1 - (size cde - 1 - k) in Hn.
    have HposP : (POS < alloc_label)%coq_nat by (rewrite /POS; apply/ltP; lia).
    destruct (findopt (fun p : Merged.instr * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) cde) as [m | ] eqn:Hfind.
    -
      simpl in Hn.
      have Hm_ltP : (m < size cde)%coq_nat by (apply/ltP; exact (findopt_bound Hfind)).
      split.
      + move=> Hae. exfalso.
        have Hbm : pc0 + m < 2 ^ imm_size mt by apply/ltP; lia.
        have Heq : alloc_label = pc0 + m.
        { apply (word_of_nat_inj_imm alloc_label_lt_imm Hbm). rewrite Hae. symmetry. exact Hn. }
        lia.
      + move=> Hla. exfalso. subst l. rewrite Hfind in Hno. discriminate.
    -
      case Hla: (l == alloc_label).
      + move/eqP: Hla => Hla. subst l.
        rewrite eqxx in Hn.
        split; [done | move=> _; exact Hn].
      + rewrite Hla in Hn.
        split.
        * move=> Hae. exfalso.
          have HbP : POS < 2 ^ imm_size mt by lia.
          have Heq : alloc_label = POS.
          { apply (word_of_nat_inj_imm alloc_label_lt_imm HbP). rewrite Hae. symmetry. exact Hn. }
          lia.
        * move=> Hla'. rewrite Hla' eqxx in Hla. discriminate.
  Qed.

  Lemma swcast_alloc : @swcast _ (word_size mt) (word_of_nat alloc_label : imm mt) = word_of_nat alloc_label.
  Proof.
    have H15 : alloc_label < 2 ^ imm_size mt by rewrite imm_size_mt /alloc_label ltn_exp2l //.
    by rewrite /swcast /word_of_nat (as_wordK H15).
  Qed.

  Lemma as_word_encode_int_zero : as_word (encode_int 0) = zerow :> mword mt.
  Proof. rewrite /encode_int /zerow. congr as_word. Qed.

  Lemma offset1_is_zero : forall (t : mem_tag) off,
      color t \in domm ip -> offset1 (color t) = Some off -> off = encode_int 0.
  Proof.
    intros t off Hrel Hoff.
    unfold offset1 in Hoff. rewrite mkfmapfpE in Hoff.
    rewrite Hrel /= in Hoff.
    unfold p0 in Hoff.
    destruct (find_rank (fun '(_, tag) => color tag == color t) (code prog'')) as [start'' |] eqn:Hfr'';
      [| simpl in Hoff; discriminate].
    destruct (find_rank (fun '(_, tag) => color tag == color t) (code prog)) as [start |] eqn:Hfr;
      [| simpl in Hoff; discriminate].
    simpl in Hoff. injection Hoff => Hoff_eq.
    have Hstart_eq: start = start''.
    { have Hprog : find_rank (fun '(_, tag) => color tag == color t) (code prog)
                 = find_rank (fun '(_, tag) => color tag == color t) (code p).
      { have ->: code prog = code p ++ code c by [].
        apply: find_rank_app_no_match => -[i0 tag0] Hin /=.
        apply/negP => /eqP Hcl.
        have Hic : color tag0 \in domm ic. { apply: code_color_c. exact Hin. }
        rewrite Hcl in Hic.
        pose proof Hmergeable_ifaces as [[_ Hdis] _].
        have Hnotic := fdisjointP Hdis _ Hrel.
        by rewrite Hic in Hnotic. }
      have Hprog'' : find_rank (fun '(_, tag) => color tag == color t) (code prog'')
                   = find_rank (fun '(_, tag) => color tag == color t) (code p).
      { have ->: code prog'' = code p ++ code c' by [].
        apply: find_rank_app_no_match => -[i0 tag0] Hin /=.
        apply/negP => /eqP Hcl.
        have Hic : color tag0 \in domm ic. { apply: code_color_c'. exact Hin. }
        rewrite Hcl in Hic.
        pose proof Hmergeable_ifaces as [[_ Hdis] _].
        have Hnotic := fdisjointP Hdis _ Hrel.
        by rewrite Hic in Hnotic. }
      have Heq : Some start = Some start''
        by rewrite -Hfr -Hfr'' Hprog Hprog''.
      congruence. }
    subst start''.
    have HD : size (domm (@initial_memory mt (prog_buffers prog'')))
            = size (domm (@initial_memory mt (prog_buffers prog))).
    { by rewrite align_data_domm_left. }
    rewrite -Hoff_eq HD int_diffE GRing.subrr. by [].
  Qed.

  Lemma valjal : forall (cde : @Merged.code mt) (pc0 m k : nat) l (t' : mem_tag) (b : matom),
    k < size cde ->
    pc0 + size cde < 2 ^ word_size mt ->
    nth_error cde k = Some (@MrJal mt l, t') ->
    findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) cde = Some m ->
    encode_code cde pc0 (word_of_nat (k + pc0)) = Some b ->
    vala b = encode_instr_mp (Jal (word_of_nat (pc0 + m))).
  Proof.
    move=> cde pc0 m k l t' b Hksz Hsz Hjal Hfo Hb.
    destruct (encode_code_nth_inv Hb) as [n [Hwn [Hltn Hnthn]]].
    have Hn : n = k.
    { have B1 : k + pc0 < 2 ^ word_size mt by lia.
      have B2 : n + pc0 < 2 ^ word_size mt by lia.
      have He : k + pc0 = n + pc0 by exact: (word_of_nat_inj B1 B2 Hwn).
      lia. }
    subst n.
    destruct (encode_code_foldr_nth Hnthn) as [i [t [Hnth_cde [Htag Hval]]]].
    move: Hnth_cde; rewrite Hjal => -[= Hi Ht]. subst i t.
    rewrite Hval. congr encode_instr_mp. rewrite /instr_merged_to_mp.
    cbn beta iota. by rewrite Hfo.
  Qed.

  Lemma jal_target_corresp : forall k l (t' : mem_tag) (v v'' : matom) (n n'' : imm mt) d d',
    nth_error (code prog)   k = Some (MrJal l, t') ->
    nth_error (code prog'') k = Some (MrJal l, t') ->
    k < size (code p) ->
    encode_code (code prog)   (size (initial_memory (mt := mt) (prog_buffers prog)))
      (word_of_nat (k + size (initial_memory (mt := mt) (prog_buffers prog))))   = Some v ->
    encode_code (code prog'') (size (initial_memory (mt := mt) (prog_buffers prog'')))
      (word_of_nat (k + size (initial_memory (mt := mt) (prog_buffers prog'')))) = Some v'' ->
    decode_instr (vala v)   = Some (Jal n) ->
    decode_instr (vala v'') = Some (Jal n'') ->
    encode_code (code prog)   (size (initial_memory (mt := mt) (prog_buffers prog)))   (@swcast _ (word_size mt) n)   = Some d ->
    encode_code (code prog'') (size (initial_memory (mt := mt) (prog_buffers prog''))) (@swcast _ (word_size mt) n'') = Some d' ->
    taga d = taga d' /\
    (side_of (color (taga d)) = Left ->
     forall off0, get_offset (side_of (color (taga d))) (color (taga d)) = Some off0 ->
                  @swcast _ (word_size mt) n'' = (@swcast _ (word_size mt) n + as_word off0)%w).
  Proof.
    move=> k l t' v v'' n n'' d d' Hp Hp'' Hkp Hev Hev'' Hdv Hdv'' Hd Hd'.
    set pc0   := size (initial_memory (mt := mt) (prog_buffers prog))   in Hev Hd.
    set pc0'' := size (initial_memory (mt := mt) (prog_buffers prog'')) in Hev'' Hd'.
    have Hpc : pc0'' = pc0.
    { rewrite /pc0 /pc0''. exact: (esym align_data_size_left). }
    have Hk2   : k < size (code prog)   by rewrite /prog /program_link /= size_cat; apply: (leq_trans Hkp); exact: leq_addr.
    have Hk2'' : k < size (code prog'') by rewrite /prog'' /program_link /= size_cat; apply: (leq_trans Hkp); exact: leq_addr.
    have Hsz   : pc0  + size (code prog)   < alloc_label by exact memory_size.
    have Hsz'' : pc0'' + size (code prog'') < alloc_label by exact memory_size''.
    have Hb    : pc0  + size (code prog)   < 2 ^ word_size mt by apply: (ltn_trans Hsz)   alloc_label_lt_w.
    have Hb''  : pc0'' + size (code prog'') < 2 ^ word_size mt by apply: (ltn_trans Hsz'') alloc_label_lt_w.
    clearbody pc0 pc0''.
    have Hp_p : nth_error (code p) k = Some (MrJal l, t').
    { move: Hp. have ->: code prog = code p ++ code c by [].
      rewrite nth_error_app1; last by apply/ltP; exact: Hkp. by []. }
    have Hne : l <> alloc_label.
    { move=> Hl.
      have I := jal_alloc_iff Hsz no_mrlabel_alloc_prog Hp Hev Hdv.
      have Hna : word_of_nat alloc_label = n by apply (proj2 I).
      move: Hd; rewrite -Hna swcast_alloc => Hdd.
      have [kd [Hwd [Hltd _]]] := encode_code_nth_inv Hdd.
      have Hb2 : kd + pc0 < 2 ^ word_size mt by lia.
      have Heq : alloc_label = kd + pc0 by apply: (word_of_nat_inj alloc_label_lt_w Hb2 Hwd).
      lia. }
    case Hloc : (findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code p)) => [m|]; last first.
    {
      have Hloc' : findopt (is_label_def l) (code p) = None by exact Hloc.
      have [mc [mc' [ic_ [i_ [tc [Hfc Hfc' [Hnthc Hnthc'] [Hictc Hcoltc]]]]]]]
        := A.jal_cross_p Hp_p Hne Hloc'.
      have Hfc2 : findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code c) = Some mc by exact Hfc.
      have Hfc'2 : findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code c') = Some mc' by exact Hfc'.
      have Hmc_lt : mc < size (code c) by apply: (findopt_bound Hfc2).
      have Hmc'_lt : mc' < size (code c') by apply: (findopt_bound Hfc'2).
      have Hmp : findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog) = Some (size (code p) + mc).
      { have ->: code prog = code p ++ code c by []. by rewrite findopt_cat Hfc2. }
      have Hmp'' : findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog'') = Some (size (code p) + mc').
      { have ->: code prog'' = code p ++ code c' by []. by rewrite findopt_cat Hfc'2. }
      have Hmprog : size (code p) + mc < size (code prog)
        by rewrite /prog /program_link /= size_cat ltn_add2l.
      have Hmprog'' : size (code p) + mc' < size (code prog'')
        by rewrite /prog'' /program_link /= size_cat ltn_add2l.
      have Hvv   := valjal Hk2   Hb   Hp   Hmp   Hev.
      have Hvv'' := valjal Hk2'' Hb'' Hp'' Hmp'' Hev''.
      rewrite Hvv   /encode_instr_mp encodeK in Hdv.
      rewrite Hvv'' /encode_instr_mp encodeK in Hdv''.
      have En   : n   = word_of_nat (pc0  + (size (code p) + mc))
        by injection Hdv  as HE;  rewrite HE.
      have En'' : n'' = word_of_nat (pc0'' + (size (code p) + mc'))
        by injection Hdv'' as HE''; rewrite HE''.
      have Hpm   : pc0  + (size (code p) + mc)  < alloc_label by lia.
      have Hpm'' : pc0'' + (size (code p) + mc') < alloc_label by lia.
      have Hsw   : @swcast _ (word_size mt) n   = word_of_nat (pc0  + (size (code p) + mc)).
      { rewrite En.   exact: (swcast_word_of_nat_id Hpm). }
      have Hsw'' : @swcast _ (word_size mt) n'' = word_of_nat (pc0'' + (size (code p) + mc')).
      { rewrite En''. exact: (swcast_word_of_nat_id Hpm''). }
      rewrite Hsw   (addnC pc0  (size (code p) + mc))  in Hd.
      rewrite Hsw'' (addnC pc0'' (size (code p) + mc')) in Hd'.
      have [kd  [Hwd  [Hltd  Hfd ]]] := encode_code_nth_inv Hd.
      have [kd' [Hwd' [Hltd' Hfd']]] := encode_code_nth_inv Hd'.
      have Hkdm  : kd  = size (code p) + mc
        by have B := word_of_nat_inj (a := (size (code p) + mc) + pc0)  (b := kd  + pc0)  ltac:(lia) ltac:(lia) Hwd;  lia.
      have Hkdm' : kd' = size (code p) + mc'
        by have B := word_of_nat_inj (a := (size (code p) + mc') + pc0'') (b := kd' + pc0'') ltac:(lia) ltac:(lia) Hwd'; lia.
      subst kd kd'.
      have [id  [td  [Hnth_d  [Htag_d  _]]]] := encode_code_foldr_nth Hfd.
      have [id' [td' [Hnth_d' [Htag_d' _]]]] := encode_code_foldr_nth Hfd'.
      have Hpref : nth_error (code prog) (size (code p) + mc) = nth_error (code c) mc.
      { have ->: code prog = code p ++ code c by [].
        rewrite nth_error_app2; last by apply/leP; rewrite size_length; lia.
        congr nth_error. rewrite size_length. by lia. }
      have Hpref'' : nth_error (code prog'') (size (code p) + mc') = nth_error (code c') mc'.
      { have ->: code prog'' = code p ++ code c' by [].
        rewrite nth_error_app2; last by apply/leP; rewrite size_length; lia.
        congr nth_error. rewrite size_length. by lia. }
      have E1 : nth_error (code c) mc = Some (id, td)     by rewrite -Hpref;   exact: Hnth_d.
      have E2 : nth_error (code c') mc' = Some (id', td') by rewrite -Hpref''; exact: Hnth_d'.
      have Htd  : td = tc  by move: E1; rewrite Hnthc  => -[_ ->].
      have Htd' : td' = tc by move: E2; rewrite Hnthc' => -[_ ->].
      split.
      - by rewrite Htag_d Htag_d' Htd Htd'.
      - move=> Hside.
        have Hcol2 : color tc \in domm ic by exact Hcoltc.
        have Hnotip : (color tc \in domm ip) = false.
        { apply: negbTE. apply/negP => E.
          pose proof Hmergeable_ifaces as [[_ Hdis] _].
          have Hnic := fdisjointP Hdis _ E.
          by rewrite Hcol2 in Hnic. }
        rewrite Htag_d Htd /side_of Hnotip /= in Hside.
        discriminate Hside. }
    have Hm : findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code p) = Some m := Hloc.
    have Hm_lt : m < size (code p) by apply: (findopt_bound Hm).
    have Hmprog   : m < size (code prog)   by rewrite /prog /program_link /= size_cat; apply: (leq_trans Hm_lt); exact: leq_addr.
    have Hmprog'' : m < size (code prog'') by rewrite /prog'' /program_link /= size_cat; apply: (leq_trans Hm_lt); exact: leq_addr.
    have [Hnc Hnc'] :
      findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code c) = None
      /\ findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code c') = None.
    { apply: labels_disjoint_prefix. by rewrite Hm. }
    have Hmp : findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog) = Some m.
    { have ->: code prog = code p ++ code c by []. by rewrite findopt_cat Hnc Hm. }
    have Hmp'' : findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog'') = Some m.
    { have ->: code prog'' = code p ++ code c' by []. by rewrite findopt_cat Hnc' Hm. }
    have Hvv   := valjal Hk2   Hb   Hp   Hmp   Hev.
    have Hvv'' := valjal Hk2'' Hb'' Hp'' Hmp'' Hev''.
    rewrite Hvv   /encode_instr_mp encodeK in Hdv.
    rewrite Hvv'' /encode_instr_mp encodeK in Hdv''.
    have En   : n   = word_of_nat (pc0  + m) by injection Hdv  as HE;  rewrite HE.
    have En'' : n'' = word_of_nat (pc0'' + m) by injection Hdv'' as HE''; rewrite HE''.
    have Hpm   : pc0  + m < alloc_label by lia.
    have Hpm'' : pc0'' + m < alloc_label by lia.
    have Hsw   : @swcast _ (word_size mt) n   = word_of_nat (pc0  + m).
    { rewrite En.   exact: (swcast_word_of_nat_id Hpm). }
    have Hsw'' : @swcast _ (word_size mt) n'' = word_of_nat (pc0'' + m).
    { rewrite En''. exact: (swcast_word_of_nat_id Hpm''). }
    rewrite Hsw   (addnC pc0  m) in Hd.
    rewrite Hsw'' (addnC pc0'' m) in Hd'.
    have [kd  [Hwd  [Hltd  Hfd ]]] := encode_code_nth_inv Hd.
    have [kd' [Hwd' [Hltd' Hfd']]] := encode_code_nth_inv Hd'.
    have Hkdm  : kd  = m by have B := word_of_nat_inj (a := m + pc0)  (b := kd  + pc0)  ltac:(lia) ltac:(lia) Hwd;  lia.
    have Hkdm' : kd' = m by have B := word_of_nat_inj (a := m + pc0'') (b := kd' + pc0'') ltac:(lia) ltac:(lia) Hwd'; lia.
    subst kd kd'.
    have [id  [td  [Hnth_d  [Htag_d  _]]]] := encode_code_foldr_nth Hfd.
    have [id' [td' [Hnth_d' [Htag_d' _]]]] := encode_code_foldr_nth Hfd'.
    have Hpref   : nth_error (code prog)   m = nth_error (code p) m.
    { have ->: code prog = code p ++ code c by [].
      rewrite nth_error_app1; [done | apply/ltP; exact: Hm_lt]. }
    have Hpref'' : nth_error (code prog'') m = nth_error (code p) m.
    { have ->: code prog'' = code p ++ code c' by [].
      rewrite nth_error_app1; [done | apply/ltP; exact: Hm_lt]. }
    have E1 : nth_error (code p) m = Some (id, td)   by rewrite -Hpref;   exact: Hnth_d.
    have E2 : nth_error (code p) m = Some (id', td')  by rewrite -Hpref''; exact: Hnth_d'.
    have HSS : Some (id, td) = Some (id', td') := etrans (esym E1) E2.
    have Htdeq : td = td' by injection HSS as _ Htd; exact: Htd.
    have Htag_eq : taga d = taga d'.
    { rewrite Htag_d Htag_d'. exact: Htdeq. }
    split; first exact: Htag_eq.
    move=> _ off0 Hoff0.
    have HIn : List.In (id, td) (code p) by apply: (nth_error_In _ _ E1).
    have Hcolp : color td \in domm ip by apply: code_color_p; exact: HIn.
    have Hside : side_of (color td) = Left by rewrite /side_of Hcolp.
    rewrite Htag_d Hside in Hoff0.
    have Hz := offset1_is_zero Hcolp Hoff0.
    rewrite Hsw Hsw'' Hpc Hz as_word_encode_int_zero.
    by apply: esym; exact: addw0.
  Qed.

  Lemma valbnz : forall (cde : @Merged.code mt) (pc0 m k : nat) r l (t' : mem_tag) (b : matom),
    k < size cde ->
    pc0 + size cde < 2 ^ word_size mt ->
    nth_error cde k = Some (@MrBnz mt r l, t') ->
    findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) cde = Some m ->
    encode_code cde pc0 (word_of_nat (k + pc0)) = Some b ->
    vala b = encode_instr_mp (instr_merged_to_mp (@MrBnz mt r l) (fun (_ _ : nat) => m) k).
  Proof.
    move=> cde pc0 m k r l t' b Hksz Hsz Hbnz Hfo Hb.
    destruct (encode_code_nth_inv Hb) as [n [Hwn [Hltn Hnthn]]].
    have Hn : n = k.
    { have B1 : k + pc0 < 2 ^ word_size mt by lia.
      have B2 : n + pc0 < 2 ^ word_size mt by lia.
      have He : k + pc0 = n + pc0 by exact: (word_of_nat_inj B1 B2 Hwn).
      lia. }
    subst n.
    destruct (encode_code_foldr_nth Hnthn) as [i [t [Hnth_cde [Htag Hval]]]].
    move: Hnth_cde; rewrite Hbnz => -[= Hi Ht]. subst i t.
    rewrite Hval.
    have Hpos : (pc0 + size cde) - 1 - (size cde - 1 - k) = pc0 + k by lia.
    rewrite Hpos. congr encode_instr_mp. rewrite /instr_merged_to_mp.
    cbn beta iota. rewrite Hfo. cbn iota. by rewrite subnDl.
  Qed.

  Lemma bnz_encoding_aligned : forall k r l (t' : mem_tag) (a a'' : matom),
    nth_error (code prog)   k = Some (MrBnz r l, t') ->
    nth_error (code prog'') k = Some (MrBnz r l, t') ->
    k < size (code p) ->
    encode_code (code prog)   (size (initial_memory (mt := mt) (prog_buffers prog)))
      (word_of_nat (k + size (initial_memory (mt := mt) (prog_buffers prog))))   = Some a ->
    encode_code (code prog'') (size (initial_memory (mt := mt) (prog_buffers prog'')))
      (word_of_nat (k + size (initial_memory (mt := mt) (prog_buffers prog'')))) = Some a'' ->
    vala a = vala a''.
  Proof.
    move=> k r l t' a a'' Hk Hk'' Hkp Ha Ha''.
    destruct (bnz_resolved_prog Hk) as [m Hfo].
    have Hfo'' : findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog'') = Some m.
    { by rewrite -(bnz_findopt_shared Hkp Hk). }
    have Hk2 : k < size (code prog).
    { rewrite /prog /program_link /= size_cat. apply: (leq_trans Hkp). exact: leq_addr. }
    have Hk2'' : k < size (code prog'').
    { rewrite /prog'' /program_link /= size_cat. apply: (leq_trans Hkp). exact: leq_addr. }
    have Hb : size (initial_memory (mt := mt) (prog_buffers prog)) + size (code prog) < 2 ^ word_size mt.
    { apply: (ltn_trans _ alloc_label_lt_w). rewrite /prog /program_link /=. exact memory_size. }
    have Hb'' : size (initial_memory (mt := mt) (prog_buffers prog'')) + size (code prog'') < 2 ^ word_size mt.
    { apply: (ltn_trans _ alloc_label_lt_w). rewrite /prog'' /program_link /=. exact memory_size''. }
    rewrite (valbnz Hk2 Hb Hk Hfo Ha) (valbnz Hk2'' Hb'' Hk'' Hfo'' Ha'').
    reflexivity.
  Qed.

  Lemma jal_resolution_consistent : forall k l (t' : mem_tag) (a a'' : matom) (n n'' : imm mt),
    nth_error (code prog)   k = Some (MrJal l, t') ->
    nth_error (code prog'') k = Some (MrJal l, t') ->
    encode_code (code prog)   (size (initial_memory (mt := mt) (prog_buffers prog)))
      (word_of_nat (k + size (initial_memory (mt := mt) (prog_buffers prog))))   = Some a ->
    encode_code (code prog'') (size (initial_memory (mt := mt) (prog_buffers prog'')))
      (word_of_nat (k + size (initial_memory (mt := mt) (prog_buffers prog'')))) = Some a'' ->
    decode_instr (vala a) = Some (Jal n) ->
    decode_instr (vala a'') = Some (Jal n'') ->
    (word_of_nat alloc_label = n) <-> (word_of_nat alloc_label = n'').
  Proof.
    intros k l t' a a'' n n'' Hp Hp'' Hep Hep'' Hdp Hdp''.
    have I1 := jal_alloc_iff memory_size   no_mrlabel_alloc_prog   Hp   Hep   Hdp.
    have I2 := jal_alloc_iff memory_size'' no_mrlabel_alloc_prog'' Hp'' Hep'' Hdp''.
    split => H; [exact (proj2 I2 (proj1 I1 H)) | exact (proj2 I1 (proj1 I2 H))].
  Qed.


  Lemma offset2_val : forall cc, cc \in domm ic ->
    offset2 cc = Some ((ssrint.Posz (size (code p)) - ssrint.Posz (size (code p')))%R).
  Proof.
    move=> cc Hcic.
    have Hcic' : cc \in domm (prog_interface c') by rewrite -Hifacec.
    have Hhas : has (fun '(_, tag) => color tag == cc) (code c')
      by exact: (wf_color_has Hwfc' Hcic').
    pose proof Hmergeable_ifaces as [[_ Hdis] _].
    have Hnp : find_rank' (fun '(_, tag) => color tag == cc) (code p) 0 = None.
    { apply: find_rank'_none => -[i0 t0] Hin /=. apply/negP => /eqP Hcl.
      have Hip : color t0 \in domm ip by apply: code_color_p; exact Hin.
      rewrite Hcl in Hip. have Hnotic := fdisjointP Hdis _ Hip. by rewrite Hcic in Hnotic. }
    have Hnp' : find_rank' (fun '(_, tag) => color tag == cc) (code p') 0 = None.
    { apply: find_rank'_none => -[i0 t0] Hin /=. apply/negP => /eqP Hcl.
      have Hip : color t0 \in domm ip by apply: code_color_p'; exact Hin.
      rewrite Hcl in Hip. have Hnotic := fdisjointP Hdis _ Hip. by rewrite Hcic in Hnotic. }
    have Hfr'' : find_rank (fun '(_, tag) => color tag == cc) (code prog'')
               = Some (size (code p) + seq.find (fun '(_, tag) => color tag == cc) (code c')).
    { have ->: code prog'' = code p ++ code c' by [].
      by rewrite /find_rank find_rank'_cat Hnp add0n find_rank'E Hhas. }
    have Hfr' : find_rank (fun '(_, tag) => color tag == cc) (code prog')
              = Some (size (code p') + seq.find (fun '(_, tag) => color tag == cc) (code c')).
    { have ->: code prog' = code p' ++ code c' by [].
      by rewrite /find_rank find_rank'_cat Hnp' add0n find_rank'E Hhas. }
    have HD : size (domm (@initial_memory mt (prog_buffers prog'')))
            = size (domm (@initial_memory mt (prog_buffers prog'))).
    { by rewrite align_data_domm. }
    rewrite /offset2 mkfmapfpE Hcic /= /p0 Hfr'' Hfr' /= HD.
    congr Some. exact: int_diff_cancel2.
  Qed.


  Lemma combined_codes_forward: forall w v t off,
      color t \in domm ip ->
      offset1 (color t) = Some off ->
      is_code t ->
      encode_code (code prog) (size (initial_memory (mt := mt) (prog_buffers prog))) w = Some v@t ->
      exists v',
        decode_match Left
          (mem (initial_state (code prog) (prog_buffers prog) (prog_interface prog)))
          (mem (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'')))
          v v' /\
          (mem (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'')))
            (w + as_word off)%w = Some v'@t.
  Proof.
    intros w v t off Hrel Hoff Hcode Henc.
    set pc0 := size (@initial_memory mt (prog_buffers prog)).
    set pc0'' := size (@initial_memory mt (prog_buffers prog'')).
    destruct (encode_code_nth_inv Henc) as [k [Hw [Hlt Hnth]]].
    destruct (encode_code_foldr_nth Hnth) as [i [t' [Hnth_cde [Htag Hval]]]].
    have Hk_in_p: k < size (code p).
    {

    { case Hk_p: (k < size (code p)); [auto |].
      exfalso.
      move/negbT: Hk_p. rewrite -leqNgt => Hk_ge_p.
      have Hnth_c: nth_error (code c) (k - size (code p)) = Some (i, t').
      { have: nth_error (code prog) k = Some (i, t').
        auto.
        simpl. rewrite nth_error_app2; [done | apply/leP; exact Hk_ge_p]. }
      have Hic: color t' \in domm ic.
      { eapply code_color_c. apply nth_error_In in Hnth_c. exact Hnth_c. }
      simpl in Htag. rewrite -Htag in Hic.
      pose proof Hmergeable_ifaces as [[G H] ?].
      have := fdisjointP H _ Hrel.
      by rewrite Hic. } }
    have Hnth_prog'': nth_error (code prog'') k = Some (i, t').
    {
      simpl. rewrite nth_error_app1; [| apply/ltP; exact Hk_in_p].
      have: nth_error (code prog) k = Some (i, t').
      { eauto. }
      simpl. rewrite nth_error_app1; [done | apply/ltP; exact Hk_in_p]. }
    have Hk_lt'': k < size (code prog'').
    { simpl. rewrite size_cat. move/ltP: Hk_in_p => ?. apply/ltP. lia. }
    have Hk_lt2: k < size (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
      (encode_instr_atom x (fun l default => match findopt (fun p0 => match p0.1 with MrLabel l0 => l == l0 | _ => false end) (code prog'') with Some m => pc0'' + m | None => if l == alloc_label then l else default end) (pc0'' + size (code prog'') - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) (code prog'')).1.
    {
      rewrite encode_code_foldr_size. exact Hk_lt''. }
    destruct (nth_error_Some_ex Hk_lt2) as [v'' Hv''].
    have Henc'' := encode_code_nth (ltn_trans memory_size'' alloc_label_lt_w) Hv''.
    destruct (encode_code_foldr_nth Hv'') as [i'' [t'' [Hnth_cde2 [Htag'' Hval'']]]].
    rewrite Hnth_prog'' in Hnth_cde2. injection Hnth_cde2 => Ht'' Hi''.
    subst i'' t''.
    have Haddr: (w + as_word off)%w = word_of_nat (k + pc0'').
    { rewrite Hw.

      
      unfold offset1 in Hoff. rewrite mkfmapfpE in Hoff.
      rewrite Hrel /= in Hoff.
      unfold p0 in Hoff.
      destruct (find_rank (fun '(_, tag) => color tag == color t) (code prog)) as [start |] eqn:Hfr;
        [| simpl in Hoff].
      destruct (find_rank (fun '(_, tag) => color tag == color t) (code prog'')) as [start'' |] eqn:Hfr'';
        [| simpl in Hoff; discriminate].
      simpl in Hoff. injection Hoff => Hoff_eq.

      have Hstart_eq: start = start''.
      {
        have Hprog : find_rank (fun '(_, tag) => color tag == color t) (code prog)
                   = find_rank (fun '(_, tag) => color tag == color t) (code p).
        { have ->: code prog = code p ++ code c by [].
          apply: find_rank_app_no_match => -[i0 tag0] Hin /=.
          apply/negP => /eqP Hcl.
          have Hic : color tag0 \in domm ic. { apply: code_color_c. exact Hin. }
          rewrite Hcl in Hic.
          pose proof Hmergeable_ifaces as [[_ Hdis] _].
          have Hnotic := fdisjointP Hdis _ Hrel.
          by rewrite Hic in Hnotic. }
        have Hprog'' : find_rank (fun '(_, tag) => color tag == color t) (code prog'')
                     = find_rank (fun '(_, tag) => color tag == color t) (code p).
        { have ->: code prog'' = code p ++ code c' by [].
          apply: find_rank_app_no_match => -[i0 tag0] Hin /=.
          apply/negP => /eqP Hcl.
          have Hic : color tag0 \in domm ic. { apply: code_color_c'. exact Hin. }
          rewrite Hcl in Hic.
          pose proof Hmergeable_ifaces as [[_ Hdis] _].
          have Hnotic := fdisjointP Hdis _ Hrel.
          by rewrite Hic in Hnotic. }
        have Heq : Some start = Some start''
          by rewrite -Hfr -Hfr'' Hprog Hprog''.
        congruence. }
      subst start''.

      have Hpc_eq: pc0'' = pc0.
      { rewrite /pc0'' /pc0. exact: (esym align_data_size_left). }
      rewrite Hpc_eq. unfold pc0.
      rewrite -Hoff_eq.
      rewrite align_data_domm_left_u.
      rewrite int_diffE GRing.subrr.
      rewrite as_word_int0. apply: addw0.
      exfalso. move: Hoff.
      by case: (find_rank (fun '(_, tag) => color tag == color t) (code p ++ code c')) => [a|].
      }
    exists (vala v'').
    split.
    -
      destruct i.
      9: {
        apply decode_match_no_JAL.
        - move=> imm; rewrite (Hval : v = _) encodeK; discriminate.
        - rewrite Hval''; move=> imm; rewrite encodeK; discriminate.
        - rewrite Hw in Henc.
          exact: (bnz_encoding_aligned Hnth_cde Hnth_prog'' Hk_in_p Henc Henc''). }
      9: {
        have [n Dv] : exists n, decode_instr v = Some (Jal n).
        { rewrite (Hval : v = _); eexists; apply encodeK. }
        have [n'' Dv''] : exists n'', decode_instr (vala v'') = Some (Jal n'').
        { rewrite Hval''; eexists; apply encodeK. }
        have JT  := encode_code_jal_target code_tags_wf_prog   jal_resolved_prog   memory_size   Henc   Dv.
        have JT'' := encode_code_jal_target code_tags_wf_prog'' jal_resolved_prog'' memory_size'' Henc'' Dv''.
        case: JT => [[d [Hd Hcd]] | Halloc]; case: JT'' => [[d' [Hd' Hcd']] | Halloc''].
        -
          rewrite Hw in Henc.
          have [Htagd Hreld] := jal_target_corresp Hnth_cde Hnth_prog'' Hk_in_p Henc Henc'' Dv Dv'' Hd Hd'.
          eapply decode_match_JAL.
          + exact Dv.
          + exact Dv''.
          + by rewrite unionmE Hd.
          + by rewrite unionmE Hd'.
          + exact Hcd.
          + exact Htagd.
          + exact Hreld.
        -
          exfalso.
          rewrite Hw in Henc.
          have Hcons := jal_resolution_consistent Hnth_cde Hnth_prog'' Henc Henc'' Dv Dv''.
          have Hna : word_of_nat alloc_label = n := proj2 Hcons Halloc''.
          have HN := @alloc_label_not_in_encode_code (code prog)
                       (size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c)))) memory_size.
          move: Hd. rewrite -Hna swcast_alloc => Hd.
          rewrite HN in Hd. discriminate.
        -
          exfalso.
          rewrite Hw in Henc.
          have Hcons := jal_resolution_consistent Hnth_cde Hnth_prog'' Henc Henc'' Dv Dv''.
          have Hna : word_of_nat alloc_label = n'' := proj1 Hcons Halloc.
          have HN := @alloc_label_not_in_encode_code (code prog'')
                       (size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c')))) memory_size''.
          move: Hd'. rewrite -Hna swcast_alloc => Hd'.
          rewrite HN in Hd'. discriminate.
        -
          apply decode_match_alloc_JAL.
          + by rewrite Dv Halloc.
          + by rewrite Dv'' Halloc''. }
      all: apply decode_match_no_JAL;
        [ move=> imm; rewrite (Hval : v = _) encodeK; discriminate
        | rewrite Hval''; move=> imm; rewrite encodeK; discriminate
        | rewrite Hval''; exact Hval ].
    -
      rewrite Haddr. simpl.
      rewrite unionmE Henc'' /=.
      simpl in Htag. rewrite Htag. destruct v''. subst. simpl. eauto.
  Qed.

  Lemma combined_codes_backward: forall w v t off,
      color t \in domm ip ->
      offset1 (color t) = Some off ->
      is_code t ->
      encode_code (code prog'') (size (initial_memory (mt := mt) (prog_buffers prog''))) (w + as_word off)%w = Some v@t ->
      exists v',
        decode_match Left
          (mem (initial_state (code prog) (prog_buffers prog) (prog_interface prog)))
          (mem (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'')))
          v' v /\
          (mem (initial_state (code prog) (prog_buffers prog) (prog_interface prog)))
            w = Some v'@t.
  Proof.
    intros w v t off Hrel Hoff Hcode Henc''.
    set pc0 := size (@initial_memory mt (prog_buffers prog)).
    set pc0'' := size (@initial_memory mt (prog_buffers prog'')).
    destruct (encode_code_nth_inv Henc'') as [k [Hwk [Hlt'' Hnth_f'']]].
    destruct (encode_code_foldr_nth Hnth_f'') as [i [t' [Hnth_prog'' [Htag Hval_g]]]].
    have Hk_in_p: k < size (code p).
    { case Hk_p: (k < size (code p)); [auto |].
      exfalso.
      move/negbT: Hk_p. rewrite -leqNgt => Hk_ge_p.
      have Hnth_c': nth_error (code c') (k - size (code p)) = Some (i, t').
      { have: nth_error (code prog'') k = Some (i, t').
        auto.
        simpl. rewrite nth_error_app2; [done | apply/leP; exact Hk_ge_p]. }
      have Hic: color t' \in domm ic.
      { eapply code_color_c'. apply nth_error_In in Hnth_c'. exact Hnth_c'. }
      simpl in Htag. rewrite -Htag in Hic.
      pose proof Hmergeable_ifaces as [[G H] ?].
      have := fdisjointP H _ Hrel.
      by rewrite Hic. }
    have Hnth_cde: nth_error (code prog) k = Some (i, t').
    { simpl. rewrite nth_error_app1; [| apply/ltP; exact Hk_in_p].
      have: nth_error (code prog'') k = Some (i, t').
      { eauto. }
      simpl. rewrite nth_error_app1; [done | apply/ltP; exact Hk_in_p]. }
    have Hk_lt: k < size (code prog).
    { simpl. rewrite size_cat. move/ltP: Hk_in_p => ?. apply/ltP. lia. }
    have Hk_lt2: k < size (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
      (encode_instr_atom x (fun l default => match findopt (fun p0 => match p0.1 with MrLabel l0 => l == l0 | _ => false end) (code prog) with Some m => pc0 + m | None => if l == alloc_label then l else default end) (pc0 + size (code prog) - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) (code prog)).1.
    { rewrite encode_code_foldr_size. exact Hk_lt. }
    destruct (nth_error_Some_ex Hk_lt2) as [v' Hv'].
    have Henc := encode_code_nth (ltn_trans memory_size alloc_label_lt_w) Hv'.
    destruct (encode_code_foldr_nth Hv') as [i' [t'2 [Hnth_cde2 [Htag_c Hval_c]]]].
    rewrite Hnth_cde in Hnth_cde2. injection Hnth_cde2 => Ht'2 Hi'.
    subst i' t'2.
    have Hwaddr: w = word_of_nat (k + pc0).
    { have Hoff0 := offset1_is_zero Hrel Hoff.
      have Hpc_eq: size (@initial_memory mt (prog_buffers prog'')) = pc0.
      { rewrite /pc0. exact: (esym align_data_size_left). }
      move: Hwk. rewrite Hoff0 Hpc_eq => Hwk'.
      rewrite as_word_encode_int_zero addw0 in Hwk'. exact Hwk'. }
    exists (vala v').
    split.
    - destruct i.
      9: {
        apply decode_match_no_JAL.
        - move=> imm; rewrite Hval_c encodeK; discriminate.
        - rewrite (Hval_g : v = _); move=> imm; rewrite encodeK; discriminate.
        - rewrite Hwk in Henc''.
          exact: (bnz_encoding_aligned Hnth_cde Hnth_prog'' Hk_in_p Henc Henc''). }
      9: {
        have [n Dv] : exists n, decode_instr (vala v') = Some (Jal n).
        { rewrite Hval_c; eexists; apply encodeK. }
        have [n'' Dv''] : exists n'', decode_instr v = Some (Jal n'').
        { rewrite (Hval_g : v = _); eexists; apply encodeK. }
        have JT  := encode_code_jal_target code_tags_wf_prog   jal_resolved_prog   memory_size   Henc   Dv.
        have JT'' := encode_code_jal_target code_tags_wf_prog'' jal_resolved_prog'' memory_size'' Henc'' Dv''.
        case: JT => [[d [Hd Hcd]] | Halloc]; case: JT'' => [[d' [Hd' Hcd']] | Halloc''].
        -
          rewrite Hwk in Henc''.
          have [Htagd Hreld] := jal_target_corresp Hnth_cde Hnth_prog'' Hk_in_p Henc Henc'' Dv Dv'' Hd Hd'.
          eapply decode_match_JAL.
          + exact Dv.
          + exact Dv''.
          + by rewrite unionmE Hd.
          + by rewrite unionmE Hd'.
          + exact Hcd.
          + exact Htagd.
          + exact Hreld.
        -
          exfalso.
          rewrite Hwk in Henc''.
          have Hcons := jal_resolution_consistent Hnth_cde Hnth_prog'' Henc Henc'' Dv Dv''.
          have Hna : word_of_nat alloc_label = n := proj2 Hcons Halloc''.
          have HN := @alloc_label_not_in_encode_code (code prog)
                       (size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c)))) memory_size.
          move: Hd. rewrite -Hna swcast_alloc => Hd.
          rewrite HN in Hd. discriminate.
        -
          exfalso.
          rewrite Hwk in Henc''.
          have Hcons := jal_resolution_consistent Hnth_cde Hnth_prog'' Henc Henc'' Dv Dv''.
          have Hna : word_of_nat alloc_label = n'' := proj1 Hcons Halloc.
          have HN := @alloc_label_not_in_encode_code (code prog'')
                       (size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c')))) memory_size''.
          move: Hd'. rewrite -Hna swcast_alloc => Hd'.
          rewrite HN in Hd'. discriminate.
        -
          apply decode_match_alloc_JAL.
          + by rewrite Dv Halloc.
          + by rewrite Dv'' Halloc''. }
      all: apply decode_match_no_JAL;
        [ move=> imm; rewrite Hval_c encodeK; discriminate
        | rewrite (Hval_g : v = _); move=> imm; rewrite encodeK; discriminate
        | rewrite (Hval_g : v = _); exact Hval_c ].
    -
      rewrite Hwaddr. simpl.
      rewrite unionmE Henc /=.
      simpl in Htag. rewrite Htag. destruct v'. subst. simpl. eauto.
  Qed.

  Lemma jal_target_corresp' : forall k k'' l (t' : mem_tag) (v v'' : matom) (n n'' : imm mt) d d',
    nth_error (code prog')  k   = Some (MrJal l, t') ->
    nth_error (code prog'') k'' = Some (MrJal l, t') ->
    size (code p') <= k ->
    k'' = size (code p) + (k - size (code p')) ->
    encode_code (code prog')  (size (initial_memory (mt := mt) (prog_buffers prog')))
      (word_of_nat (k   + size (initial_memory (mt := mt) (prog_buffers prog'))))  = Some v ->
    encode_code (code prog'') (size (initial_memory (mt := mt) (prog_buffers prog'')))
      (word_of_nat (k'' + size (initial_memory (mt := mt) (prog_buffers prog'')))) = Some v'' ->
    decode_instr (vala v)   = Some (Jal n) ->
    decode_instr (vala v'') = Some (Jal n'') ->
    encode_code (code prog')  (size (initial_memory (mt := mt) (prog_buffers prog')))  (@swcast _ (word_size mt) n)   = Some d ->
    encode_code (code prog'') (size (initial_memory (mt := mt) (prog_buffers prog''))) (@swcast _ (word_size mt) n'') = Some d' ->
    taga d = taga d' /\
    (side_of (color (taga d)) = Right ->
     forall off0, get_offset (side_of (color (taga d))) (color (taga d)) = Some off0 ->
                  @swcast _ (word_size mt) n'' = (@swcast _ (word_size mt) n + as_word off0)%w).
  Proof.
    move=> k k'' l t' v v'' n n'' d d' Hp' Hp'' Hsfx Hk''eq Hev Hev'' Hdv Hdv'' Hd Hd'.
    set pc0'  := size (initial_memory (mt := mt) (prog_buffers prog'))  in Hev Hd.
    set pc0'' := size (initial_memory (mt := mt) (prog_buffers prog'')) in Hev'' Hd'.
    have Hpc : pc0'' = pc0'.
    { rewrite /pc0' /pc0''. exact: (esym align_data_size). }
    have Hk2'  : k   < size (code prog')  by exact: (nth_error_lt Hp').
    have Hk2'' : k'' < size (code prog'') by exact: (nth_error_lt Hp'').
    have Hsz'  : pc0'  + size (code prog')  < alloc_label by exact: memory_size'.
    have Hsz'' : pc0'' + size (code prog'') < alloc_label by exact: memory_size''.
    have Hb'   : pc0'  + size (code prog')  < 2 ^ word_size mt by apply: (ltn_trans Hsz')  alloc_label_lt_w.
    have Hb''  : pc0'' + size (code prog'') < 2 ^ word_size mt by apply: (ltn_trans Hsz'') alloc_label_lt_w.
    have Hcp'  : size (code prog')  = size (code p') + size (code c') by rewrite /prog' /program_link /= size_cat.
    have Hcp'' : size (code prog'') = size (code p)  + size (code c') by rewrite /prog'' /program_link /= size_cat.
    clearbody pc0' pc0''.
    have Hj : nth_error (code c') (k - size (code p')) = Some (MrJal l, t').
    { move: Hp'. have ->: code prog' = code p' ++ code c' by [].
      rewrite nth_error_app2; last by apply/leP; exact: Hsfx. by []. }
    have Hne : l <> alloc_label.
    { move=> Hl.
      have I := jal_alloc_iff Hsz' no_mrlabel_alloc_prog' Hp' Hev Hdv.
      have Hna : word_of_nat alloc_label = n by apply (proj2 I).
      move: Hd; rewrite -Hna swcast_alloc => Hdd.
      have [kd [Hwd [Hltd _]]] := encode_code_nth_inv Hdd.
      have Hbk : kd + pc0' < 2 ^ word_size mt by lia.
      have Heq : alloc_label = kd + pc0' by apply: (word_of_nat_inj alloc_label_lt_w Hbk Hwd).
      lia. }
    case Hloc : (findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code c')) => [mc|]; last first.
    {
      have Hloc' : findopt (is_label_def l) (code c') = None by exact Hloc.
      have [mp' [mp [ip_ [i_ [tp [Hfp' Hfp [Hnthp' Hnthp] [Hiptp Hcoltp]]]]]]]
        := A.jal_cross_c' Hj Hne Hloc'.
      have Hfp'2 : findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code p') = Some mp' by exact Hfp'.
      have Hfp2  : findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code p)  = Some mp  by exact Hfp.
      have Hmp'_lt : mp' < size (code p') by apply: (findopt_bound Hfp'2).
      have Hmp_lt  : mp  < size (code p)  by apply: (findopt_bound Hfp2).
      have Hfo' : findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog') = Some mp'.
      { have ->: code prog' = code p' ++ code c' by []. by rewrite findopt_cat Hloc Hfp'2. }
      have Hfo'' : findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog'') = Some mp.
      { have ->: code prog'' = code p ++ code c' by []. by rewrite findopt_cat Hloc Hfp2. }
      have Hvv'  := valjal Hk2'  Hb'  Hp'  Hfo'  Hev.
      have Hvv'' := valjal Hk2'' Hb'' Hp'' Hfo'' Hev''.
      rewrite Hvv'  /encode_instr_mp encodeK in Hdv.
      rewrite Hvv'' /encode_instr_mp encodeK in Hdv''.
      have En'  : n   = word_of_nat (pc0'  + mp') by injection Hdv  as HE;  rewrite HE.
      have En'' : n'' = word_of_nat (pc0'' + mp)  by injection Hdv'' as HE''; rewrite HE''.
      have HmprogY' : mp' < size (code prog')
        by rewrite Hcp'; apply: (leq_trans Hmp'_lt); exact: leq_addr.
      have HmprogY'' : mp < size (code prog'')
        by rewrite Hcp''; apply: (leq_trans Hmp_lt); exact: leq_addr.
      have Hpm'  : pc0'  + mp' < alloc_label by lia.
      have Hpm'' : pc0'' + mp  < alloc_label by lia.
      have Hsw'  : @swcast _ (word_size mt) n   = word_of_nat (pc0'  + mp').
      { rewrite En'.  exact: (swcast_word_of_nat_id Hpm'). }
      have Hsw'' : @swcast _ (word_size mt) n'' = word_of_nat (pc0'' + mp).
      { rewrite En''. exact: (swcast_word_of_nat_id Hpm''). }
      rewrite Hsw'  (addnC pc0'  mp') in Hd.
      rewrite Hsw'' (addnC pc0'' mp)  in Hd'.
      have [kd  [Hwd  [Hltd  Hfd ]]] := encode_code_nth_inv Hd.
      have [kd' [Hwd' [Hltd' Hfd']]] := encode_code_nth_inv Hd'.
      have Hkdm  : kd  = mp'
        by have B := word_of_nat_inj (a := mp' + pc0')  (b := kd  + pc0')  ltac:(lia) ltac:(lia) Hwd;  lia.
      have Hkdm' : kd' = mp
        by have B := word_of_nat_inj (a := mp + pc0'') (b := kd' + pc0'') ltac:(lia) ltac:(lia) Hwd'; lia.
      subst kd kd'.
      have [id  [td  [Hnth_d  [Htag_d  _]]]] := encode_code_foldr_nth Hfd.
      have [id' [td' [Hnth_d' [Htag_d' _]]]] := encode_code_foldr_nth Hfd'.
      have Hpref : nth_error (code prog') mp' = nth_error (code p') mp'.
      { have ->: code prog' = code p' ++ code c' by [].
        rewrite nth_error_app1; [done | apply/ltP; exact: Hmp'_lt]. }
      have Hpref'' : nth_error (code prog'') mp = nth_error (code p) mp.
      { have ->: code prog'' = code p ++ code c' by [].
        rewrite nth_error_app1; [done | apply/ltP; exact: Hmp_lt]. }
      have E1 : nth_error (code p') mp' = Some (id, td)  by rewrite -Hpref;   exact: Hnth_d.
      have E2 : nth_error (code p)  mp  = Some (id', td') by rewrite -Hpref''; exact: Hnth_d'.
      have Htd  : td = tp  by move: E1; rewrite Hnthp' => -[_ ->].
      have Htd' : td' = tp by move: E2; rewrite Hnthp  => -[_ ->].
      split.
      - by rewrite Htag_d Htag_d' Htd Htd'.
      - move=> Hside.
        have Hcol2 : color tp \in domm ip by exact Hcoltp.
        rewrite Htag_d Htd /side_of Hcol2 /= in Hside.
        discriminate Hside. }
    have Hmc : findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code c') = Some mc := Hloc.
    have Hmc_lt : mc < size (code c') by apply: (findopt_bound Hmc).
    have Hfo' : findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog') = Some (size (code p') + mc).
    { have ->: code prog' = code p' ++ code c' by []. by rewrite findopt_cat Hmc. }
    have Hfo'' : findopt (fun p : @Merged.instr mt * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code prog'') = Some (size (code p) + mc).
    { have ->: code prog'' = code p ++ code c' by []. by rewrite findopt_cat Hmc. }
    have Hvv'  := valjal Hk2'  Hb'  Hp'  Hfo'  Hev.
    have Hvv'' := valjal Hk2'' Hb'' Hp'' Hfo'' Hev''.
    rewrite Hvv'  /encode_instr_mp encodeK in Hdv.
    rewrite Hvv'' /encode_instr_mp encodeK in Hdv''.
    have En'  : n   = word_of_nat (pc0'  + (size (code p') + mc)) by injection Hdv  as HE;  rewrite HE.
    have En'' : n'' = word_of_nat (pc0'' + (size (code p)  + mc)) by injection Hdv'' as HE''; rewrite HE''.
    have Hpm'  : pc0'  + (size (code p') + mc) < alloc_label by lia.
    have Hpm'' : pc0'' + (size (code p)  + mc) < alloc_label by lia.
    have Hsw'  : @swcast _ (word_size mt) n   = word_of_nat (pc0'  + (size (code p') + mc)).
    { rewrite En'.  exact: (swcast_word_of_nat_id Hpm'). }
    have Hsw'' : @swcast _ (word_size mt) n'' = word_of_nat (pc0'' + (size (code p)  + mc)).
    { rewrite En''. exact: (swcast_word_of_nat_id Hpm''). }
    rewrite Hsw'  (addnC pc0'  (size (code p') + mc)) in Hd.
    rewrite Hsw'' (addnC pc0'' (size (code p)  + mc)) in Hd'.
    have [kd  [Hwd  [Hltd  Hfd ]]] := encode_code_nth_inv Hd.
    have [kd' [Hwd' [Hltd' Hfd']]] := encode_code_nth_inv Hd'.
    have Hkdm  : kd  = size (code p') + mc by have B := word_of_nat_inj (a := (size (code p') + mc) + pc0')  (b := kd  + pc0')  ltac:(lia) ltac:(lia) Hwd;  lia.
    have Hkdm' : kd' = size (code p)  + mc by have B := word_of_nat_inj (a := (size (code p)  + mc) + pc0'') (b := kd' + pc0'') ltac:(lia) ltac:(lia) Hwd'; lia.
    subst kd kd'.
    have [id  [td  [Hnth_d  [Htag_d  _]]]] := encode_code_foldr_nth Hfd.
    have [id' [td' [Hnth_d' [Htag_d' _]]]] := encode_code_foldr_nth Hfd'.
    have Hpref  : nth_error (code prog')  (size (code p') + mc) = nth_error (code c') mc.
    { have ->: code prog' = code p' ++ code c' by [].
      rewrite nth_error_app2; last by apply/leP; exact: leq_addr.
      congr nth_error. have ->: length (code p') = size (code p') by []. by lia. }
    have Hpref'' : nth_error (code prog'') (size (code p) + mc) = nth_error (code c') mc.
    { have ->: code prog'' = code p ++ code c' by [].
      rewrite nth_error_app2; last by apply/leP; exact: leq_addr.
      congr nth_error. have ->: length (code p) = size (code p) by []. by lia. }
    have E1 : nth_error (code c') mc = Some (id, td)   by rewrite -Hpref;   exact: Hnth_d.
    have E2 : nth_error (code c') mc = Some (id', td')  by rewrite -Hpref''; exact: Hnth_d'.
    have HSS : Some (id, td) = Some (id', td') := etrans (esym E1) E2.
    have Htdeq : td = td' by injection HSS as _ Htd; exact: Htd.
    have Htag_eq : taga d = taga d'.
    { rewrite Htag_d Htag_d'. exact: Htdeq. }
    split; first exact: Htag_eq.
    move=> _ off0 Hoff0.
    have HIn : List.In (id, td) (code c') by apply: (nth_error_In _ _ E1).
    have Hcic : color td \in domm ic by apply: code_color_c'; exact: HIn.
    have Hside : side_of (color td) = Right.
    { rewrite /side_of; case E: (color td \in domm ip); last by [].
      pose proof Hmergeable_ifaces as [[_ Hdis] _].
      by move: (fdisjointP Hdis _ E); rewrite Hcic. }
    have H1 : offset2 (color td) = Some off0.
    { move: Hoff0; rewrite Htag_d Hside => H; exact: H. }
    have Hz : off0 = ((ssrint.Posz (size (code p)) - ssrint.Posz (size (code p')))%R).
    { have H2 := offset2_val Hcic. rewrite H1 in H2. by injection H2 as Hi; exact: Hi. }
    rewrite Hsw' Hsw'' Hpc Hz.
    have -> : pc0' + (size (code p) + mc) = (pc0' + mc) + size (code p) by lia.
    have -> : pc0' + (size (code p') + mc) = (pc0' + mc) + size (code p') by lia.
    rewrite /word_of_nat. exact: as_word_shiftAB.
  Qed.

  Lemma bnz_encoding_aligned' : forall k k'' r l (t' : mem_tag) (a a'' : matom),
    nth_error (code prog')  k   = Some (MrBnz r l, t') ->
    nth_error (code prog'') k'' = Some (MrBnz r l, t') ->
    size (code p') <= k ->
    k'' = size (code p) + (k - size (code p')) ->
    encode_code (code prog')  (size (initial_memory (mt := mt) (prog_buffers prog')))
      (word_of_nat (k   + size (initial_memory (mt := mt) (prog_buffers prog'))))  = Some a ->
    encode_code (code prog'') (size (initial_memory (mt := mt) (prog_buffers prog'')))
      (word_of_nat (k'' + size (initial_memory (mt := mt) (prog_buffers prog'')))) = Some a'' ->
    vala a = vala a''.
  Proof.
    move=> k k'' r l t' a a'' Hk Hk'' Hsfx Hk''eq Ha Ha''.
    destruct (bnz_resolved_prog' Hk) as [m' Hfo'].
    destruct (bnz_resolved_prog'' Hk'') as [m'' Hfo''].
    have Hrel : m' - k = m'' - k'' by exact: (bnz_findopt_shared' Hsfx Hk''eq Hk Hfo' Hfo'').
    have Hk2 : k < size (code prog') by exact: (nth_error_lt Hk).
    have Hk2'' : k'' < size (code prog'') by exact: (nth_error_lt Hk'').
    have Hb : size (initial_memory (mt := mt) (prog_buffers prog')) + size (code prog') < 2 ^ word_size mt.
    { apply: (ltn_trans _ alloc_label_lt_w). rewrite /prog' /program_link /=. exact memory_size'. }
    have Hb'' : size (initial_memory (mt := mt) (prog_buffers prog'')) + size (code prog'') < 2 ^ word_size mt.
    { apply: (ltn_trans _ alloc_label_lt_w). rewrite /prog'' /program_link /=. exact memory_size''. }
    rewrite (valbnz Hk2 Hb Hk Hfo' Ha) (valbnz Hk2'' Hb'' Hk'' Hfo'' Ha'').
    congr encode_instr_mp. rewrite /instr_merged_to_mp. cbn beta. congr Bnz. congr word_of_nat.
    exact Hrel.
  Qed.

  Lemma jal_resolution_consistent' : forall k k'' l (t' : mem_tag) (a a'' : matom) (n n'' : imm mt),
    nth_error (code prog')  k   = Some (MrJal l, t') ->
    nth_error (code prog'') k'' = Some (MrJal l, t') ->
    encode_code (code prog')  (size (initial_memory (mt := mt) (prog_buffers prog')))
      (word_of_nat (k   + size (initial_memory (mt := mt) (prog_buffers prog'))))  = Some a ->
    encode_code (code prog'') (size (initial_memory (mt := mt) (prog_buffers prog'')))
      (word_of_nat (k'' + size (initial_memory (mt := mt) (prog_buffers prog'')))) = Some a'' ->
    decode_instr (vala a)   = Some (Jal n) ->
    decode_instr (vala a'') = Some (Jal n'') ->
    (word_of_nat alloc_label = n) <-> (word_of_nat alloc_label = n'').
  Proof.
    intros k k'' l t' a a'' n n'' Hp' Hp'' Hep' Hep'' Hdp' Hdp''.
    have I1 := jal_alloc_iff memory_size'  no_mrlabel_alloc_prog'  Hp'  Hep'  Hdp'.
    have I2 := jal_alloc_iff memory_size'' no_mrlabel_alloc_prog'' Hp'' Hep'' Hdp''.
    split => H; [exact (proj2 I2 (proj1 I1 H)) | exact (proj2 I1 (proj1 I2 H))].
  Qed.

  Lemma offset2_addr_corresp : forall (i : Merged.instr) (t' : mem_tag) off k k'',
    color t' \in domm ic ->
    offset2 (color t') = Some off ->
    nth_error (code prog')  k   = Some (i, t') ->
    nth_error (code prog'') k'' = Some (i, t') ->
    size (code p') <= k ->
    k'' = size (code p) + (k - size (code p')) ->
    (@word_of_nat (word_size mt) (k + size (initial_memory (mt := mt) (prog_buffers prog'))) + as_word off)%w
      = @word_of_nat (word_size mt) (k'' + size (initial_memory (mt := mt) (prog_buffers prog''))).
  Proof.
    move=> i t' off k k'' Hcic Hoff Hk Hk'' Hsfx Hk''eq.
    move: Hoff; rewrite (offset2_val Hcic) => -[<-].
    rewrite Hk''eq -align_data_size.
    set D := size (initial_memory (mt := mt) (prog_buffers prog')).
    have -> : k + D = ((k - size (code p')) + D) + size (code p') by lia.
    have -> : size (code p) + (k - size (code p')) + D
            = ((k - size (code p')) + D) + size (code p) by lia.
    rewrite /word_of_nat. exact (esym (as_word_shiftAB _ _ _ _)).
  Qed.

  Lemma addwIr : forall (x y a : mword mt), (x + a)%w = (y + a)%w -> x = y.
  Proof. move=> x y a H. apply: (GRing.addIr a). exact: H. Qed.

  Lemma offset2_addr_corresp_bwd : forall (i : Merged.instr) (t' : mem_tag) off k k'' w,
    color t' \in domm ic ->
    offset2 (color t') = Some off ->
    nth_error (code prog')  k   = Some (i, t') ->
    nth_error (code prog'') k'' = Some (i, t') ->
    size (code p') <= k ->
    k'' = size (code p) + (k - size (code p')) ->
    (w + as_word off)%w = @word_of_nat (word_size mt) (k'' + size (initial_memory (mt := mt) (prog_buffers prog''))) ->
    w = @word_of_nat (word_size mt) (k + size (initial_memory (mt := mt) (prog_buffers prog'))).
  Proof.
    intros i t' off k k'' w Hc Hoff Hp' Hp'' Hkge Hidx Hwk.
    have Hfwd := offset2_addr_corresp Hc Hoff Hp' Hp'' Hkge Hidx.
    have Heq : (w + as_word off)%w =
               (@word_of_nat (word_size mt) (k + size (initial_memory (mt := mt) (prog_buffers prog'))) + as_word off)%w.
    { rewrite Hwk. symmetry. exact Hfwd. }
    exact (addwIr Heq).
  Qed.

  Lemma combined_codes_forward': forall w v t off,
      color t \in domm ic ->
      offset2 (color t) = Some off ->
      is_code t ->
      encode_code (code prog') (size (initial_memory (mt := mt) (prog_buffers prog'))) w = Some v@t ->
      exists v',
        decode_match Right
          (mem (initial_state (code prog') (prog_buffers prog') (prog_interface prog')))
          (mem (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'')))
          v v' /\
          (mem (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'')))
            (w + as_word off)%w = Some v'@t.
  Proof.
    intros w v t off Hrel Hoff Hcode Henc.
    set pc0' := size (@initial_memory mt (prog_buffers prog')).
    set pc0'' := size (@initial_memory mt (prog_buffers prog'')).
    destruct (encode_code_nth_inv Henc) as [k [Hw [Hlt Hnth]]].
    destruct (encode_code_foldr_nth Hnth) as [i [t' [Hnth_prog' [Htag Hval]]]].
    have Hk_ge: size (code p') <= k.
    { case Hk_p: (size (code p') <= k); [auto |].
      exfalso.
      move/negbT: Hk_p. rewrite -ltnNge => Hk_lt_p'.
      have Hnth_p': nth_error (code p') k = Some (i, t').
      { have: nth_error (code prog') k = Some (i, t').
        auto.
        simpl. rewrite nth_error_app1; [done | apply/ltP; exact Hk_lt_p']. }
      have Hip: color t' \in domm ip.
      { eapply code_color_p'. apply nth_error_In in Hnth_p'. exact Hnth_p'. }
      simpl in Htag. rewrite -Htag in Hip.
      pose proof Hmergeable_ifaces as [[_ Hdis] _].
      have := fdisjointP Hdis _ Hip.
      by rewrite Hrel. }
    have Hk_tot: k < size (code p') + size (code c').
    { move: Hlt. simpl. by rewrite size_cat. }
    have Hj_lt: k - size (code p') < size (code c').
    { move/leP: Hk_ge => ?. move/ltP: Hk_tot => ?. apply/ltP. lia. }
    have Hnth_c': nth_error (code c') (k - size (code p')) = Some (i, t').
    { have: nth_error (code prog') k = Some (i, t').
      auto.
      simpl. rewrite nth_error_app2; [done | apply/leP; exact Hk_ge]. }
    set k'' := size (code p) + (k - size (code p')).
    have Hkp' : size (code p') <= k := Hk_ge.
    have Hidx : k'' = size (code p) + (k - size (code p')) by rewrite /k''.
    have Hnth_prog'': nth_error (code prog'') k'' = Some (i, t').
    { simpl. rewrite nth_error_app2.
      - have ->: (k'' - Datatypes.length (code p))%coq_nat = k - size (code p').
        { rewrite /k''. change (Datatypes.length (code p)) with (size (code p)).
          by rewrite minusE addKn. }
        exact Hnth_c'.
      - rewrite /k''. apply/leP. exact: leq_addr. }
    have Hk_lt'': k'' < size (code prog'').
    { simpl. rewrite size_cat /k''. move/ltP: Hj_lt => ?. apply/ltP. lia. }
    have Hk_lt2: k'' < size (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
      (encode_instr_atom x (fun l default => match findopt (fun p0 => match p0.1 with MrLabel l0 => l == l0 | _ => false end) (code prog'') with Some m => pc0'' + m | None => if l == alloc_label then l else default end) (pc0'' + size (code prog'') - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) (code prog'')).1.
    { rewrite encode_code_foldr_size. exact Hk_lt''. }
    destruct (nth_error_Some_ex Hk_lt2) as [v'' Hv''].
    have Henc'' := encode_code_nth (ltn_trans memory_size'' alloc_label_lt_w) Hv''.
    destruct (encode_code_foldr_nth Hv'') as [i'' [t'' [Hnth_cde2 [Htag'' Hval'']]]].
    rewrite Hnth_prog'' in Hnth_cde2. injection Hnth_cde2 => Ht'' Hi''.
    subst i'' t''.
    have Haddr: (w + as_word off)%w = word_of_nat (k'' + pc0'').
    { have Et : t = t' := Htag.
      rewrite Hw. rewrite Et in Hrel Hoff.
      exact: (offset2_addr_corresp Hrel Hoff Hnth_prog' Hnth_prog'' Hkp' Hidx). }
    exists (vala v'').
    split.
    - destruct i.
      9: {
        apply decode_match_no_JAL.
        - move=> imm; rewrite (Hval : v = _) encodeK; discriminate.
        - rewrite Hval''; move=> imm; rewrite encodeK; discriminate.
        - rewrite Hw in Henc.
          exact: (bnz_encoding_aligned' Hnth_prog' Hnth_prog'' Hkp' Hidx Henc Henc''). }
      9: {
        have [n Dv] : exists n, decode_instr v = Some (Jal n).
        { rewrite (Hval : v = _); eexists; apply encodeK. }
        have [n'' Dv''] : exists n'', decode_instr (vala v'') = Some (Jal n'').
        { rewrite Hval''; eexists; apply encodeK. }
        have JT  := encode_code_jal_target code_tags_wf_prog'  jal_resolved_prog'  memory_size'  Henc   Dv.
        have JT'' := encode_code_jal_target code_tags_wf_prog'' jal_resolved_prog'' memory_size'' Henc'' Dv''.
        case: JT => [[d [Hd Hcd]] | Halloc]; case: JT'' => [[d' [Hd' Hcd']] | Halloc''].
        -
          rewrite Hw in Henc.
          have [Htagd Hreld] := jal_target_corresp' Hnth_prog' Hnth_prog'' Hkp' Hidx Henc Henc'' Dv Dv'' Hd Hd'.
          eapply decode_match_JAL.
          + exact Dv.
          + exact Dv''.
          + by rewrite unionmE Hd.
          + by rewrite unionmE Hd'.
          + exact Hcd.
          + exact Htagd.
          + exact Hreld.
        -
          exfalso.
          rewrite Hw in Henc.
          have Hcons := jal_resolution_consistent' Hnth_prog' Hnth_prog'' Henc Henc'' Dv Dv''.
          have Hna : word_of_nat alloc_label = n := proj2 Hcons Halloc''.
          move: Hd. rewrite -Hna swcast_alloc => Hd.
          have HN := @alloc_label_not_in_encode_code (code prog')
                       (size (initial_memory (mt := mt) (unionm (prog_buffers p') (prog_buffers c')))) memory_size'.
          rewrite HN in Hd. discriminate.
        -
          exfalso.
          rewrite Hw in Henc.
          have Hcons := jal_resolution_consistent' Hnth_prog' Hnth_prog'' Henc Henc'' Dv Dv''.
          have Hna : word_of_nat alloc_label = n'' := proj1 Hcons Halloc.
          move: Hd'. rewrite -Hna swcast_alloc => Hd'.
          have HN := @alloc_label_not_in_encode_code (code prog'')
                       (size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c')))) memory_size''.
          rewrite HN in Hd'. discriminate.
        -
          apply decode_match_alloc_JAL.
          + by rewrite Dv Halloc.
          + by rewrite Dv'' Halloc''. }
      all: apply decode_match_no_JAL;
        [ move=> imm; rewrite (Hval : v = _) encodeK; discriminate
        | rewrite Hval''; move=> imm; rewrite encodeK; discriminate
        | rewrite Hval''; exact Hval ].
    -
      rewrite Haddr. simpl.
      rewrite unionmE Henc'' /=.
      simpl in Htag. rewrite Htag. destruct v''. subst. simpl. eauto.
  Qed.

  Lemma combined_codes_backward': forall w v t off,
      color t \in domm ic ->
      offset2 (color t) = Some off ->
      is_code t ->
      encode_code (code prog'') (size (initial_memory (mt := mt) (prog_buffers prog''))) (w + as_word off)%w = Some v@t ->
      exists v',
        decode_match Right
          (mem (initial_state (code prog') (prog_buffers prog') (prog_interface prog')))
          (mem (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'')))
          v' v /\
          (mem (initial_state (code prog') (prog_buffers prog') (prog_interface prog')))
            w = Some v'@t.
  Proof.
    intros w v t off Hrel Hoff Hcode Henc''.
    set pc0' := size (@initial_memory mt (prog_buffers prog')).
    set pc0'' := size (@initial_memory mt (prog_buffers prog'')).
    destruct (encode_code_nth_inv Henc'') as [k'' [Hwk [Hlt'' Hnth_f'']]].
    destruct (encode_code_foldr_nth Hnth_f'') as [i [t' [Hnth_prog'' [Htag Hval_g]]]].
    have Hk_ge: size (code p) <= k''.
    { case Hk_p: (size (code p) <= k''); [auto |].
      exfalso.
      move/negbT: Hk_p. rewrite -ltnNge => Hk_lt_p.
      have Hnth_p: nth_error (code p) k'' = Some (i, t').
      { have: nth_error (code prog'') k'' = Some (i, t').
        auto.
        simpl. rewrite nth_error_app1; [done | apply/ltP; exact Hk_lt_p]. }
      have Hip: color t' \in domm ip.
      { eapply code_color_p. apply nth_error_In in Hnth_p. exact Hnth_p. }
      simpl in Htag. rewrite -Htag in Hip.
      pose proof Hmergeable_ifaces as [[_ Hdis] _].
      have := fdisjointP Hdis _ Hip.
      by rewrite Hrel. }
    have Hk_tot: k'' < size (code p) + size (code c').
    { move: Hlt''. simpl. by rewrite size_cat. }
    have Hj_lt: k'' - size (code p) < size (code c').
    { move/leP: Hk_ge => ?. move/ltP: Hk_tot => ?. apply/ltP. lia. }
    have Hnth_c': nth_error (code c') (k'' - size (code p)) = Some (i, t').
    { have: nth_error (code prog'') k'' = Some (i, t').
      auto.
      simpl. rewrite nth_error_app2; [done | apply/leP; exact Hk_ge]. }
    set k := size (code p') + (k'' - size (code p)).
    have Hkp' : size (code p') <= k. { rewrite /k. exact: leq_addr. }
    have Hidx : k'' = size (code p) + (k - size (code p')).
    { rewrite /k. move/leP: Hk_ge => ?. lia. }
    have Hnth_prog': nth_error (code prog') k = Some (i, t').
    { simpl. rewrite nth_error_app2.
      - have ->: (k - Datatypes.length (code p'))%coq_nat = k'' - size (code p).
        { rewrite /k. change (Datatypes.length (code p')) with (size (code p')).
          by rewrite minusE addKn. }
        exact Hnth_c'.
      - rewrite /k. apply/leP. exact: leq_addr. }
    have Hk_lt: k < size (code prog').
    { simpl. rewrite size_cat /k. move/ltP: Hj_lt => ?. apply/ltP. lia. }
    have Hk_lt2: k < size (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
      (encode_instr_atom x (fun l default => match findopt (fun p0 => match p0.1 with MrLabel l0 => l == l0 | _ => false end) (code prog') with Some m => pc0' + m | None => if l == alloc_label then l else default end) (pc0' + size (code prog') - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) (code prog')).1.
    { rewrite encode_code_foldr_size. exact Hk_lt. }
    destruct (nth_error_Some_ex Hk_lt2) as [v' Hv'].
    have Henc := encode_code_nth (ltn_trans memory_size' alloc_label_lt_w) Hv'.
    destruct (encode_code_foldr_nth Hv') as [i' [t'2 [Hnth_cde2 [Htag_c Hval_c]]]].
    rewrite Hnth_prog' in Hnth_cde2. injection Hnth_cde2 => Ht'2 Hi'.
    subst i' t'2.
    have Hwaddr: w = word_of_nat (k + pc0').
    { have Et : t = t' := Htag.
      rewrite Et in Hrel Hoff.
      exact: (offset2_addr_corresp_bwd Hrel Hoff Hnth_prog' Hnth_prog'' Hkp' Hidx Hwk). }
    exists (vala v').
    split.
    - destruct i.
      9: {
        apply decode_match_no_JAL.
        - move=> imm; rewrite Hval_c encodeK; discriminate.
        - rewrite (Hval_g : v = _); move=> imm; rewrite encodeK; discriminate.
        - rewrite Hwk in Henc''.
          exact: (bnz_encoding_aligned' Hnth_prog' Hnth_prog'' Hkp' Hidx Henc Henc''). }
      9: {
        have [n Dv] : exists n, decode_instr (vala v') = Some (Jal n).
        { rewrite Hval_c; eexists; apply encodeK. }
        have [n'' Dv''] : exists n'', decode_instr v = Some (Jal n'').
        { rewrite (Hval_g : v = _); eexists; apply encodeK. }
        have JT  := encode_code_jal_target code_tags_wf_prog'  jal_resolved_prog'  memory_size'  Henc   Dv.
        have JT'' := encode_code_jal_target code_tags_wf_prog'' jal_resolved_prog'' memory_size'' Henc'' Dv''.
        case: JT => [[d [Hd Hcd]] | Halloc]; case: JT'' => [[d' [Hd' Hcd']] | Halloc''].
        -
          rewrite Hwk in Henc''.
          have [Htagd Hreld] := jal_target_corresp' Hnth_prog' Hnth_prog'' Hkp' Hidx Henc Henc'' Dv Dv'' Hd Hd'.
          eapply decode_match_JAL.
          + exact Dv.
          + exact Dv''.
          + by rewrite unionmE Hd.
          + by rewrite unionmE Hd'.
          + exact Hcd.
          + exact Htagd.
          + exact Hreld.
        -
          exfalso.
          rewrite Hwk in Henc''.
          have Hcons := jal_resolution_consistent' Hnth_prog' Hnth_prog'' Henc Henc'' Dv Dv''.
          have Hna : word_of_nat alloc_label = n := proj2 Hcons Halloc''.
          move: Hd. rewrite -Hna swcast_alloc => Hd.
          have HN := @alloc_label_not_in_encode_code (code prog')
                       (size (initial_memory (mt := mt) (unionm (prog_buffers p') (prog_buffers c')))) memory_size'.
          rewrite HN in Hd. discriminate.
        -
          exfalso.
          rewrite Hwk in Henc''.
          have Hcons := jal_resolution_consistent' Hnth_prog' Hnth_prog'' Henc Henc'' Dv Dv''.
          have Hna : word_of_nat alloc_label = n'' := proj1 Hcons Halloc.
          move: Hd'. rewrite -Hna swcast_alloc => Hd'.
          have HN := @alloc_label_not_in_encode_code (code prog'')
                       (size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c')))) memory_size''.
          rewrite HN in Hd'. discriminate.
        -
          apply decode_match_alloc_JAL.
          + by rewrite Dv Halloc.
          + by rewrite Dv'' Halloc''. }
      all: apply decode_match_no_JAL;
        [ move=> imm; rewrite Hval_c encodeK; discriminate
        | rewrite (Hval_g : v = _); move=> imm; rewrite encodeK; discriminate
        | rewrite (Hval_g : v = _); exact Hval_c ].
    -
      clear Hidx Hkp'.
      rewrite Hwaddr. simpl.
      rewrite unionmE Henc /=.
      simpl in Htag. rewrite Htag. destruct v'. subst. simpl. eauto.
  Qed.

  Lemma register_domm_reg0 : register_domm reg0.
  Proof.
    rewrite /register_domm.
    apply/eq_fset => x.
    rewrite in_fset domm_mkfmap.
    have ->: ra = word_of_nat 4 by rewrite /ra /word_of_nat; congr as_word.
    rewrite /reg_list !inE. cbn [fst]. btauto.
  Qed.

  Lemma register_address_correctness_reg0 i (s : state) :
    regs s = reg0 -> register_address_correctness i s.
  Proof.
    move=> Hs v r. rewrite Hs /reg0 !setmE.
    repeat (case: ifP => /= _; [move=> [<-] //= |]).
    by [].
  Qed.

  Lemma initial_pc_pos : forall pr n,
      n < size (code pr) ->
      size (initial_memory (mt := mt) (prog_buffers pr)) + size (code pr) < 2 ^ (word_size mt) ->
      (forall i t, List.In (i, t) (code pr) -> is_code t = true /\ vtag t = Other) ->
      exists v,
        (unionm (encode_code (code pr) (size (initial_memory (mt := mt) (prog_buffers pr))))
                (initial_memory (mt := mt) (prog_buffers pr)))
          (@word_of_nat (word_size mt) (size (initial_memory (mt := mt) (prog_buffers pr)) + n)) = Some v
        /\ is_code (taga v).
  Proof.
    move=> pr n Hn Hsz_pc Hwf.
    have Hlt : n < size (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
      (encode_instr_atom x
         (fun l default => match findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code pr)
          with Some m => size (initial_memory (mt := mt) (prog_buffers pr)) + m
          | None => if l == alloc_label then l else default end)
         (size (initial_memory (mt := mt) (prog_buffers pr)) + size (code pr) - 1 - acc.2)
       :: acc.1, acc.2.+1)) ([::], 0) (code pr)).1.
    { rewrite encode_code_foldr_size. exact Hn. }
    destruct (nth_error_Some_ex Hlt) as [v0 Hv0].
    have Henc0 := encode_code_nth Hsz_pc Hv0.
    rewrite addnC in Henc0.
    exists v0. split; first by rewrite unionmE Henc0 /=.
    exact: (encode_code_is_code Hwf Henc0).
  Qed.

  Lemma mem_code_encode : forall pr w d,
    is_code (taga d) ->
    (mem (initial_state (code pr) (prog_buffers pr) (prog_interface pr))) w = Some d ->
    encode_code (code pr) (size (initial_memory (mt := mt) (prog_buffers pr))) w = Some d.
  Proof.
    move=> pr w d Hcd Hmem. simpl in Hmem. move: Hmem. rewrite unionmE.
    case Henc: (encode_code (code pr) (size (initial_memory (mt := mt) (prog_buffers pr))) w) => [v_code | ] /=.
    - move=> H; exact H.
    - move=> Hinit. exfalso. have Hnc := initial_memory_not_code Hinit. rewrite Hnc in Hcd. discriminate.
  Qed.

  Lemma prog''_cell_split : forall k i t,
    nth_error (code prog'') k = Some (i, t) ->
    (k < size (code p) /\ nth_error (code p) k = Some (i, t))
    \/ (size (code p) <= k /\ nth_error (code c') (k - size (code p)) = Some (i, t)).
  Proof.
    move=> k i t Hk.
    case Hlt : (k < size (code p)).
    - left. split=> //. move: Hk. rewrite /prog'' /= nth_error_app1 //.
      by apply/ltP; rewrite size_length.
    - right. have Hge : size (code p) <= k by rewrite leqNgt Hlt.
      split=> //. move: Hk. rewrite /prog'' /= nth_error_app2;
        last by apply/leP; rewrite size_length.
      by [].
  Qed.

  Lemma entry_tag_unique : forall k1 k2 i1 t1 i2 t2 (e1 e2 : Procedure.id * list Component.id),
    nth_error (code prog'') k1 = Some (i1, t1) -> nth_error (code prog'') k2 = Some (i2, t2) ->
    color t1 = color t2 ->
    entry t1 = Some e1 -> entry t2 = Some e2 -> e1.1 = e2.1 -> k1 = k2.
  Proof.
    move=> k1 k2 i1 t1 i2 t2 e1 e2 H1 H2 Hcol He1 He2 Hpe.
    have Hdis : fdisjoint (domm ip) (domm ic)
      by case: Hmergeable_ifaces => [[_ Hd] _].
    case: (prog''_cell_split H1) => [[Hk1 Hp1] | [Hk1 Hc1]];
      case: (prog''_cell_split H2) => [[Hk2 Hp2] | [Hk2 Hc2]].
    -
      have Ht12 : t1 = t2
        := low_entry_det A.lin_wf_p (nth_error_In _ _ Hp1) (nth_error_In _ _ Hp2) Hcol He1 He2 Hpe.
      have Hee : Some e1 = Some e2 by rewrite -He1 -He2 Ht12.
      case: Hee => Hee. rewrite -Hee in He2.
      exact: (wfprog_unique_entry_points Hwfp (Logic.eq_refl (color t1)) (esym Hcol)
                He1 He2 Hp1 Hp2).
    -
      exfalso.
      have Hin1 : color t1 \in domm ip by apply: code_color_p; exact: (nth_error_In _ _ Hp1).
      have Hin2 : color t2 \in domm ic by apply: code_color_c'; exact: (nth_error_In _ _ Hc2).
      by move: (fdisjointP Hdis _ Hin1); rewrite Hcol Hin2.
    -
      exfalso.
      have Hin1 : color t1 \in domm ic by apply: code_color_c'; exact: (nth_error_In _ _ Hc1).
      have Hin2 : color t2 \in domm ip by apply: code_color_p; exact: (nth_error_In _ _ Hp2).
      by move: (fdisjointP Hdis _ Hin2); rewrite -Hcol Hin1.
    -
      have Ht12 : t1 = t2
        := low_entry_det A.lin_wf_c' (nth_error_In _ _ Hc1) (nth_error_In _ _ Hc2) Hcol He1 He2 Hpe.
      have Hee : Some e1 = Some e2 by rewrite -He1 -He2 Ht12.
      case: Hee => Hee. rewrite -Hee in He2.
      have Hk12 : k1 - size (code p) = k2 - size (code p).
      { exact: (wfprog_unique_entry_points Hwfc' (Logic.eq_refl (color t1)) (esym Hcol)
                  He1 He2 Hc1 Hc2). }
      by lia.
  Qed.

  Lemma entry_addr_eq_left :
    forall c w w' (d d' : atom (mword mt) mem_tag) proc l l',
      c \in domm ip ->
      (mem (initial_state (code prog) (prog_buffers prog) (prog_interface prog))) w = Some d ->
      (mem (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog''))) w' = Some d' ->
      is_code (taga d) -> is_code (taga d') ->
      color (taga d) = c -> color (taga d') = c ->
      entry (taga d) = Some (proc, l) -> entry (taga d') = Some (proc, l') ->
      w' = w.
  Proof.
    intros cc w w' d d' proc l l' Hcc Hmem Hmem' Hcd Hcd' Hcol Hcol' Hent Hent'.
    have Hde  := mem_code_encode Hcd  Hmem.
    have Hde' := mem_code_encode Hcd' Hmem'.
    destruct (encode_code_nth_inv Hde)  as [k   [Hwk  [Hltk  Hnthk]]].
    destruct (encode_code_foldr_nth Hnthk)   as [i   [t   [Hnth_cde   [Htag   _]]]].
    destruct (encode_code_nth_inv Hde') as [k'' [Hwk'' [Hltk'' Hnthk'']]].
    destruct (encode_code_foldr_nth Hnthk'')  as [i'' [t'' [Hnth_cde'' [Htag'' _]]]].
    have Hct  : color t  = cc by rewrite -Htag.
    have Hct'' : color t'' = cc by rewrite -Htag''.
    have Hkp : k < size (code p).
    { case Hk: (k < size (code p)); [auto |].
      exfalso. move/negbT: Hk. rewrite -leqNgt => Hge.
      have Hin : nth_error (code c) (k - size (code p)) = Some (i, t).
      { have: nth_error (code prog) k = Some (i, t). auto.
        simpl. rewrite nth_error_app2; [done | apply/leP; exact Hge]. }
      have Hcic : color t \in domm ic by (apply: code_color_c; apply nth_error_In in Hin; exact Hin).
      move: Hcic. rewrite Hct => Hcic.
      pose proof Hmergeable_ifaces as [[_ Hdis] _].
      have := fdisjointP Hdis _ Hcc. by rewrite Hcic. }
    have Hkp'' : k'' < size (code p).
    { case Hk: (k'' < size (code p)); [auto |].
      exfalso. move/negbT: Hk. rewrite -leqNgt => Hge.
      have Hin : nth_error (code c') (k'' - size (code p)) = Some (i'', t'').
      { have: nth_error (code prog'') k'' = Some (i'', t''). auto.
        simpl. rewrite nth_error_app2; [done | apply/leP; exact Hge]. }
      have Hcic : color t'' \in domm ic by (apply: code_color_c'; apply nth_error_In in Hin; exact Hin).
      move: Hcic. rewrite Hct'' => Hcic.
      pose proof Hmergeable_ifaces as [[_ Hdis] _].
      have := fdisjointP Hdis _ Hcc. by rewrite Hcic. }
    have Hshared : nth_error (code prog'') k = Some (i, t).
    { simpl. rewrite nth_error_app1; [| apply/ltP; exact Hkp].
      have: nth_error (code prog) k = Some (i, t). auto.
      simpl. rewrite nth_error_app1; [done | apply/ltP; exact Hkp]. }
    have Hkeq : k = k''.
    { apply: (entry_tag_unique Hshared Hnth_cde'').
      - by rewrite Hct Hct''.
      - rewrite -Htag.  exact Hent.
      - rewrite -Htag''. exact Hent'.
      - reflexivity. }
    have Hpc : size (initial_memory (mt := mt) (prog_buffers prog''))
             = size (initial_memory (mt := mt) (prog_buffers prog)).
    { exact: (esym align_data_size_left). }
    rewrite Hwk Hwk'' -Hkeq Hpc. reflexivity.
  Qed.

  Lemma entry_addr_corresp_right :
    forall c w w' (d d' : atom (mword mt) mem_tag) proc l l' off,
      c \in domm ic ->
      (mem (initial_state (code prog') (prog_buffers prog') (prog_interface prog'))) w = Some d ->
      (mem (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog''))) w' = Some d' ->
      is_code (taga d) -> is_code (taga d') ->
      color (taga d) = c -> color (taga d') = c ->
      entry (taga d) = Some (proc, l) -> entry (taga d') = Some (proc, l') ->
      offset2 c = Some off ->
      w' = (w + as_word off)%w.
  Proof.
    move=> c w w' d d' proc l l' off Hc Hmem Hmem' Hcd Hcd' Hcol Hcol' Hent Hent' Hoff.
    have Hde  := mem_code_encode Hcd  Hmem.
    have Hde' := mem_code_encode Hcd' Hmem'.
    destruct (encode_code_nth_inv Hde)  as [k   [Hwk  [Hltk  Hnthk]]].
    destruct (encode_code_foldr_nth Hnthk)   as [i   [t   [Hnth_cde   [Htag   _]]]].
    destruct (encode_code_nth_inv Hde') as [k'' [Hwk'' [Hltk'' Hnthk'']]].
    destruct (encode_code_foldr_nth Hnthk'')  as [i'' [t'' [Hnth_cde'' [Htag'' _]]]].
    have Hct  : color t  = c by rewrite -Htag.
    have Hct'' : color t'' = c by rewrite -Htag''.
    have Hent_t : entry t = Some (proc, l) by rewrite -Htag.
    have Hent_t'' : entry t'' = Some (proc, l') by rewrite -Htag''.
    have Hkp : size (code p') <= k.
    { case Hk: (size (code p') <= k); [done |].
      exfalso. move/negbT: Hk. rewrite -ltnNge => Hlt.
      have Hin : nth_error (code p') k = Some (i, t).
      { move: Hnth_cde. rewrite /prog' /program_link /= nth_error_app1; [done | apply/ltP; exact Hlt]. }
      have Hcip : color t \in domm ip by (apply: code_color_p'; apply nth_error_In in Hin; exact Hin).
      move: Hcip. rewrite Hct => Hcip.
      pose proof Hmergeable_ifaces as [[_ Hdis] _].
      have := fdisjointP Hdis _ Hcip. by rewrite Hc. }
    have Hkp'' : size (code p) <= k''.
    { case Hk: (size (code p) <= k''); [done |].
      exfalso. move/negbT: Hk. rewrite -ltnNge => Hlt.
      have Hin : nth_error (code p) k'' = Some (i'', t'').
      { move: Hnth_cde''. rewrite /prog'' /program_link /= nth_error_app1; [done | apply/ltP; exact Hlt]. }
      have Hcip : color t'' \in domm ip by (apply: code_color_p; apply nth_error_In in Hin; exact Hin).
      move: Hcip. rewrite Hct'' => Hcip.
      pose proof Hmergeable_ifaces as [[_ Hdis] _].
      have := fdisjointP Hdis _ Hcip. by rewrite Hc. }
    have Hc'cell : nth_error (code c') (k - size (code p')) = Some (i, t).
    { move: Hnth_cde. rewrite /prog' /program_link /= nth_error_app2; [done | apply/leP; exact Hkp]. }
    have Hprog''_d : nth_error (code prog'') (size (code p) + (k - size (code p'))) = Some (i, t).
    { rewrite /prog'' /program_link /= nth_error_app2; last by apply/leP; exact: leq_addr.
      rewrite -Hc'cell. congr nth_error.
      have Hlen : length (code p) = size (code p) by []. rewrite Hlen. lia. }
    have Hk''eq : size (code p) + (k - size (code p')) = k''.
    { apply: (entry_tag_unique Hprog''_d Hnth_cde'').
      - by rewrite Hct Hct''.
      - exact Hent_t.
      - exact Hent_t''.
      - reflexivity. }
    have Hoff0 : off = ((ssrint.Posz (size (code p)) - ssrint.Posz (size (code p')))%R)
      by move: (offset2_val Hc); rewrite Hoff; move=> [->].
    rewrite Hoff0 Hwk Hwk'' -Hk''eq -align_data_size.
    set D := size (initial_memory (mt := mt) (prog_buffers prog')).
    have -> : k + D = ((k - size (code p')) + D) + size (code p') by lia.
    have -> : size (code p) + (k - size (code p')) + D
            = ((k - size (code p')) + D) + size (code p) by lia.
    rewrite /word_of_nat. exact (as_word_shiftAB _ _ _ _).
  Qed.

  Lemma entry_points_offset_init :
    forall c w w' (d d' : atom (mword mt) mem_tag) proc l l',
      c \in domm ip ->
      (mem (initial_state (code prog) (prog_buffers prog) (prog_interface prog))) w = Some d ->
      (mem (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog''))) w' = Some d' ->
      is_code (taga d) -> is_code (taga d') ->
      color (taga d) = c -> color (taga d') = c ->
      entry (taga d) = Some (proc, l) -> entry (taga d') = Some (proc, l') ->
      exists off, offset1 c = Some off /\ w' = (w + as_word off)%w.
  Proof.
    move=> c w w' d d' proc l l' Hc Hmem Hmem' Hcd Hcd' Hcol Hcol' Hent Hent'.
    have [off Hoff] : exists off, offset1 c = Some off.
    { apply/dommP. rewrite offset1_domm. exact Hc. }
    exists off. split; [exact Hoff |].
    have Hz : off = encode_int 0.
    { have Hc' : color (taga d) \in domm ip by rewrite Hcol.
      have Hoff' : offset1 (color (taga d)) = Some off by rewrite Hcol.
      exact: (@offset1_is_zero (taga d) off Hc' Hoff'). }
    have Hww : w' = w.
    { exact: (entry_addr_eq_left Hc Hmem Hmem' Hcd Hcd' Hcol Hcol' Hent Hent'). }
    rewrite Hww Hz. by rewrite as_word_encode_int_zero addw0.
  Qed.

  Lemma entry_points_offset_init' :
    forall c w w' (d d' : atom (mword mt) mem_tag) proc l l',
      c \in domm ic ->
      (mem (initial_state (code prog') (prog_buffers prog') (prog_interface prog'))) w = Some d ->
      (mem (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog''))) w' = Some d' ->
      is_code (taga d) -> is_code (taga d') ->
      color (taga d) = c -> color (taga d') = c ->
      entry (taga d) = Some (proc, l) -> entry (taga d') = Some (proc, l') ->
      exists off, offset2 c = Some off /\ w' = (w + as_word off)%w.
  Proof.
    move=> c w w' d d' proc l l' Hc Hmem Hmem' Hcd Hcd' Hcol Hcol' Hent Hent'.
    have [off Hoff] : exists off, offset2 c = Some off.
    { apply/dommP. rewrite offset2_domm. exact Hc. }
    exists off. split; [exact Hoff |].
    exact: (entry_addr_corresp_right Hc Hmem Hmem' Hcd Hcd' Hcol Hcol' Hent Hent' Hoff).
  Qed.

  Lemma same_pc_right_init :
    Component.main \in domm ic ->
    same_pc Right (initial_state (code prog') (prog_buffers prog') (prog_interface prog'))
                  (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'')).
  Proof.
    move=> Hmain_ic.
    destruct find_rank_main_prog'' as [start'' Hfr''].
    destruct find_rank_main_prog' as [start' Hfr'].
    have [Hfind' Hstart_lt'] := find_rank_Some_find Hfr'.
    have [Hfind'' Hstart_lt''] := find_rank_Some_find Hfr''.
    have Hfind_lt' : seq.find (fun '(_, tag) => color tag == Component.main) (code prog') < size (code prog')
      by rewrite Hfind'.
    have [v Hv] := initial_pc_pos Hfind_lt' (ltn_trans memory_size' alloc_label_lt_w)
                     code_tags_wf_prog'.
    eapply same_pc_normal.
    * exact Hv.
    * simpl. unfold get_offset, offset2.
      rewrite mkfmapfpE Hmain_ic /=.
      unfold p0. rewrite Hfr'' Hfr' /=. eauto.
    * simpl. rewrite Hfind' Hfind''.
      have Hd1 : size (domm (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c'))))
               = size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c')))
        by apply size_domm_fmap.
      have Hd2 : size (domm (initial_memory (mt := mt) (unionm (prog_buffers p') (prog_buffers c'))))
               = size (initial_memory (mt := mt) (unionm (prog_buffers p') (prog_buffers c')))
        by apply size_domm_fmap.
      rewrite Hd1 Hd2 (addnC start'') (addnC start') /word_of_nat int_diffE.
      exact (as_word_shiftD _ _ _).
  Qed.

  Lemma initial_state_pc_cell : forall cde pb pi,
    has (fun '(_, tag) => color tag == Component.main) cde ->
    size (initial_memory (mt := mt) pb) + size cde < 2 ^ word_size mt ->
    pc_code_color (initial_state cde pb pi).
  Proof.
    move=> cde pb pi Hhas Hsz d.
    set pc0 := size (initial_memory (mt := mt) pb).
    set mp := find (fun '(_, tag) => color tag == Component.main) cde.
    have Hmp : mp < size cde by rewrite /mp -has_find.
    have Hcol : color_of (initial_state cde pb pi) = Component.main by [].
    have Hpcv : vala (pc (initial_state cde pb pi)) = word_of_nat (pc0 + mp) by [].
    have Hmem : mem (initial_state cde pb pi)
              = unionm (encode_code cde pc0) (initial_memory (mt := mt) pb) by [].
    rewrite Hcol Hmem Hpcv unionmE.
    case Henc: (encode_code cde pc0 (word_of_nat (pc0 + mp))) => [v|] /=.
    - move=> [= <-] _.
      destruct (encode_code_nth_inv Henc) as [n [Hwn [Hltn Hnthn]]].
      have Hn : n = mp.
      { have Hb1 : pc0 + mp < 2 ^ word_size mt by lia.
        have Hb2 : n + pc0 < 2 ^ word_size mt by lia.
        have He : pc0 + mp = n + pc0 by exact: (word_of_nat_inj Hb1 Hb2 Hwn).
        lia. }
      subst n.
      destruct (encode_code_foldr_nth Hnthn) as [i [t [Hnth_cde [Htag _]]]].
      rewrite Htag.
      have Hnn : nth (i, t) cde mp = (i, t) by apply: nth_error_nth; exact Hnth_cde.
      apply/eqP. move: (@nth_find _ (i, t) _ cde Hhas). by rewrite -/mp Hnn.
    - move=> Hinit Hcd2.
      exfalso. have Hnc := initial_memory_not_code Hinit. rewrite Hnc in Hcd2. discriminate.
  Qed.

  Lemma initial_pc_code_color :
    forall s1 s2,
      Smallstep.initial_state sem s1 -> Smallstep.initial_state sem' s2 ->
      pc_code_color s1 /\ pc_code_color s2.
  Proof.
    move=> s1 s2 init1 init2.
    unfold Smallstep.initial_state, sem, sem' in init1, init2.
    simpl in init1, init2. unfold initial_state1, initial_state2 in *.
    subst s1 s2. split.
    - apply: initial_state_pc_cell.
      + have Hmain := cprog_main_existence Hprog_is_closed.
        move: Hmain; rewrite /prog /program_link /= => /orP[Hmp | Hmc].
        * have Hin := proj2 (wfprog_main_existence Hwfp) Hmp.
          rewrite /prog /program_link /= has_cat; apply/orP; left.
          exact: (@wf_color_has p Component.main Hwfp Hin).
        * have Hin := proj2 (wfprog_main_existence Hwfc) Hmc.
          rewrite /prog /program_link /= has_cat; apply/orP; right.
          exact: (@wf_color_has c Component.main Hwfc Hin).
      + rewrite /prog /program_link /=. exact: (ltn_trans memory_size alloc_label_lt_w).
    - apply: initial_state_pc_cell.
      + have Hmain := cprog_main_existence Hprog_is_closed'.
        move: Hmain; rewrite /prog' /program_link /= => /orP[Hmp | Hmc].
        * have Hin := proj2 (wfprog_main_existence Hwfp') Hmp.
          rewrite /prog' /program_link /= has_cat; apply/orP; left.
          exact: (@wf_color_has p' Component.main Hwfp' Hin).
        * have Hin := proj2 (wfprog_main_existence Hwfc') Hmc.
          rewrite /prog' /program_link /= has_cat; apply/orP; right.
          exact: (@wf_color_has c' Component.main Hwfc' Hin).
      + rewrite /prog' /program_link /=. exact: (ltn_trans memory_size' alloc_label_lt_w).
  Qed.

  Lemma gmc_initial (pb1 pb2 : NMap {fmap Block.id -> nat + seq value}) (cde : @Merged.code mt) :
    (forall i t, List.In (i, t) cde -> is_code t = true /\ vtag t = Other) ->
    (forall i t, List.In (i, t) cde -> In (color t) (domm ip) \/ In (color t) (domm ic)) ->
    (forall n r l t, nth_error cde n = Some (@MrBnz mt r l, t) ->
       exists m, findopt (fun p : @Merged.instr mt * mem_tag =>
                            match p.1 with MrLabel l0 => l == l0 | _ => false end) cde = Some m) ->
    (forall n l t, nth_error cde n = Some (@MrJal mt l, t) -> l <> alloc_label ->
       exists m, findopt (fun p : @Merged.instr mt * mem_tag =>
                            match p.1 with MrLabel l0 => l == l0 | _ => false end) cde = Some m) ->
    (exists t, nth_error cde (size cde - 1) = Some (@MrHalt mt, t)) ->
    size (initial_memory (mt := mt) (unionm pb1 pb2)) + size cde < alloc_label ->
    size (linearize_bufs (unionm pb1 pb2)) + size cde < alloc_label ->
    domm (initial_memory (mt := mt) (unionm pb1 pb2))
      = domm (initial_memory (mt := mt) (prog_buffers prog)) ->
    domm pb1 = domm ip ->
    domm pb2 = domm ic ->
    general_memory_correctness
      (unionm (encode_code cde (size (initial_memory (mt := mt) (unionm pb1 pb2))))
              (initial_memory (mt := mt) (unionm pb1 pb2))).
  Proof.
    move=> Hwf Hccol Hbnz Hjal Hhalt Hsz Hlin Hdom Hd1 Hd2.
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
    - move=> c0 w v. rewrite unionmE.
      case Henc: (encode_code cde (size (initial_memory (unionm pb1 pb2))) w) => [v_code | ] /=.
      + move=> [<-] _ Hnot_code. exfalso. apply: Hnot_code. exact: (encode_code_is_code Hwf Henc).
      + move=> Hinit _ _. right. by rewrite -Hdom mem_domm Hinit.
    - move=> c0 w v Hbound. rewrite unionmE.
      case Henc: (encode_code cde (size (initial_memory (unionm pb1 pb2))) w) => [v_code | ] /=.
      + move=> [<-] Hprefix. exfalso.
        rewrite (encode_code_prefix Hsz Henc) in Hprefix.
        exact: (code_prefix_neq_data_prefix Hbound Hprefix).
      + move=> Hinit Hprefix. exfalso.
        have Hpref0 : andw w (mask (NC := NC)) = @component_memory_prefix mt NC (ssrint.Posz 0).
        { apply: (initial_memory_prefix_zero _ Hinit).
          exact: (leq_ltn_trans (leq_addr _ _) Hlin). }
        rewrite Hpref0 in Hprefix.
        exact: (code_prefix_neq_data_prefix Hbound Hprefix).
    - move=> w v. rewrite unionmE.
      case Henc: (encode_code cde (size (initial_memory (unionm pb1 pb2))) w) => [v_code | ] /=.
      + move=> [<-] Hcode. apply/eqP. exact: (encode_code_prefix Hsz Henc).
      + move=> Hinit Hcode. exfalso.
        have Hnc := initial_memory_not_code Hinit. rewrite Hnc in Hcode. discriminate.
    - rewrite /alloc_empty unionmE alloc_label_not_in_encode_code /=.
      + rewrite alloc_label_not_in_initial_memory //.
        exact: (leq_ltn_trans (leq_addr _ _) Hlin).
      + exact: Hsz.
    - move=> w v. rewrite unionmE.
      case Henc: (encode_code cde (size (initial_memory (unionm pb1 pb2))) w) => [v_code | ].
      + move=> [<-] Hcode.
        case Hdec: (decode_instr (vala v_code)) => [i | ] //=.
        destruct i => //=.
        * have [v' [Hv' Hcode']] := encode_code_bnz_target Hwf Hbnz Hsz Henc Hdec.
          exists v'. split; [| exact Hcode'].
          rewrite unionmE Hv' //.
        * have [[v' [Hv' Hcode']] | Halloc] := encode_code_jal_target Hwf Hjal Hsz Henc Hdec.
          -- left. exists v'. split; [| exact Hcode'].
             rewrite unionmE Hv' //.
          -- right. exact Halloc.
      + move=> Hinit Hcode. exfalso.
        have Hnc := initial_memory_not_code Hinit. rewrite Hnc in Hcode. discriminate.
    - move=> w v. rewrite unionmE.
      case Henc: (encode_code cde (size (initial_memory (unionm pb1 pb2))) w) => [v_code | ].
      + move=> [<-] Hcode.
        have [Hhalt' | [v' [Hv' Hcode']]] :=
          encode_code_end_condition Hwf Hhalt Henc Hcode (ltn_trans Hsz alloc_label_lt_w).
        * left. by rewrite Hhalt'.
        * right. exists v'. split; [| exact Hcode'].
          rewrite unionmE Hv' //.
      + move=> Hinit Hcode. exfalso.
        have Hnc := initial_memory_not_code Hinit. rewrite Hnc in Hcode. discriminate.
    - move=> w d. rewrite unionmE.
      case Henc: (encode_code cde (size (initial_memory (unionm pb1 pb2))) w) => [v_code | ] /=.
      + move=> [<-]. exact: (encode_code_color Hwf Hccol Henc).
      + move=> Hinit. have := initial_memory_color Hinit. by rewrite Hd1 Hd2.
    - move=> w d e. rewrite unionmE.
      case Henc: (encode_code cde (size (initial_memory (unionm pb1 pb2))) w) => [v_code | ] /=.
      + move=> [<-] Hentry. exact: (encode_code_is_code Hwf Henc).
      + move=> Hinit Hentry. eapply initial_memory_no_entry in Hinit. congruence.
    - move=> w v. rewrite unionmE.
      case Henc: (encode_code cde (size (initial_memory (unionm pb1 pb2))) w) => [v_code | ] /=.
      + move=> [<-] Hcode. exact: (encode_code_vtag_other Hwf Henc).
      + move=> Hinit Hcode. exfalso.
        have Hnc := initial_memory_not_code Hinit. rewrite Hnc in Hcode. discriminate.
  Qed.

  Lemma cap_initial ws (cde : @Merged.code mt) pb pi :
    (forall i t, List.In (i, t) cde -> is_code t = true /\ vtag t = Other) ->
    capability_correctness [] ws (initial_state cde pb pi).
  Proof.
    move=> Hwf v n p1.
    case: p1 => //=.
    - intros r Hr. exfalso.
      simpl in Hr. move: Hr.
      rewrite /reg0. rewrite !setmE.
      repeat (case: ifP => /=); try congruence.
      intros. now simpl in Hr.
    - intros w Hw. exfalso.
      destruct Hw as [t [Hmem Hvtag]].
      simpl in Hmem.
      move: Hmem. rewrite unionmE.
      case Henc: (encode_code cde (size (initial_memory pb)) w) => [v_code | ] /=.
      + move=> [Heq].
        eapply (encode_code_vtag_not_ret Hwf). subst. eauto. subst. eauto.
      + move=> Hinit.
        eapply initial_memory_vtag_other in Hinit. inv Hinit.
        congruence.
  Qed.

  Lemma match_initial_states:
  forall s1, Smallstep.initial_state sem s1 ->
  forall s2, Smallstep.initial_state sem' s2 ->
  exists s3 M, Smallstep.initial_state sem'' s3 /\ match_states M s1 s2 s3.
  Proof.
    intros s1 init1 s2 init2.
    unfold Smallstep.initial_state, sem, sem' in init1, init2. simpl in init1. unfold initial_state1, initial_state2 in *.
    remember (initial_state (code prog'') (prog_buffers prog'') (prog_interface prog'')) as s3.
    rename Heqs3 into init3.
    exists s3. exists [].
    split; try (simpl; unfold initial_state3; done).
    remember (prog_main p) as main.
    have Hce : common_equiv [] s1 s2 s3.
    { eapply common_equiv_def; eauto.
      + unfold initial_state in init1. simpl in init1. destruct s1. inv init1. simpl. done.
      + unfold initial_state in init2. simpl in init2. destruct s2. inv init2. simpl. done.
      + unfold initial_state in init3. simpl in init3. destruct s3. inv init3. simpl. done.
      + rewrite init3. simpl. econstructor.
      + inv init1. exact: register_domm_reg0.
      + inv init2. exact: register_domm_reg0.
      + inv init3. exact: register_domm_reg0.
      + subst s1. exact: (gmc_initial code_tags_wf_prog code_color_prog bnz_resolved_prog
          jal_resolved_prog code_last_halt_prog memory_size A.memory_size_lin erefl
          domm_buffers_p domm_buffers_c).
      + subst s2. exact: (gmc_initial code_tags_wf_prog' code_color_prog' bnz_resolved_prog'
          jal_resolved_prog' code_last_halt_prog' memory_size' A.memory_size_lin'
          align_data_domm_12_u domm_buffers_p' domm_buffers_c').
      + subst s3. exact: (gmc_initial code_tags_wf_prog'' code_color_prog'' bnz_resolved_prog''
          jal_resolved_prog'' code_last_halt_prog'' memory_size'' A.memory_size_lin''
          (esym align_data_domm_left_u) domm_buffers_p domm_buffers_c').
      + subst s1. apply: cap_initial. exact: code_tags_wf_prog.
      + subst s2. apply: cap_initial. exact: code_tags_wf_prog'.
      + subst s3. apply: cap_initial. exact: code_tags_wf_prog''.
      + unfold combined_codes.
        { intros w v t off c Hrel Hoff Hcode Hcolor. split.
          - intros Hmem1.
            subst s1 s3. simpl in *.
            move: Hmem1. rewrite unionmE.
            case Henc1: (encode_code (code prog)
                           (size (initial_memory (prog_buffers prog))) w) => [v1 | ] /=.
            + move=> [] ?; subst.
              exact: (combined_codes_forward Hrel Hoff Hcode Henc1).
            + move=> Hinit.
              exfalso.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate.
          - intros Hmem3.
            subst s1 s3. simpl in *.
            move: Hmem3. rewrite unionmE.
            case Henc3: (encode_code (code prog'')
                           (size (initial_memory (prog_buffers prog''))) (addw w (as_word off))) => [v3 | ] /=.
            + move=> [] ?; subst.
              exact: (combined_codes_backward Hrel Hoff Hcode Henc3).
            + move=> Hinit.
              exfalso.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
      + unfold combined_codes.
        { intros w v t off c Hrel Hoff Hcode Hcolor. split.
          - intros Hmem2.
            subst s2 s3. simpl in *.
            move: Hmem2. rewrite unionmE.
            case Henc2: (encode_code (code prog')
                           (size (initial_memory (prog_buffers prog'))) w) => [v2 | ] /=.
            + move=> [] ?; subst.
              exact: (combined_codes_forward' Hrel Hoff Hcode Henc2).
            + move=> Hinit.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate.
          - intros Hmem3.
            subst s2 s3. simpl in *.
            move: Hmem3. rewrite unionmE.
            case Henc3: (encode_code (code prog'')
                           (size (initial_memory (prog_buffers prog''))) (addw w (as_word off))) => [v3 | ] /=.
            + move=> [] ?; subst.
              exact: (combined_codes_backward' Hrel Hoff Hcode Henc3).
            + move=> Hinit.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
      + apply/orP. destruct main.
        * left. apply (wfprog_main_existence Hwfp). symmetry. exact Heqmain.
        * right. have Hpm := cprog_main_existence Hprog_is_closed.
          simpl in Hpm. rewrite -Heqmain /= in Hpm.
          apply (wfprog_main_existence Hwfc). exact Hpm.
      + exact: (proj1 (initial_pc_code_color init1 init2)).
      + exact: (proj2 (initial_pc_code_color init1 init2)). }
    have HmacL1 : memory_address_correctness Left s1.
    { unfold memory_address_correctness. intros v0 w Hrel Hmem.
        subst s1. simpl in Hmem. unfold address_correctness.
        move: Hmem. rewrite unionmE.
        case Henc: (encode_code (code prog)
          (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.
        * move=> [<-]. rewrite (encode_code_vtag_other_prog Henc). exact I.
        * move=> Hinit. rewrite (initial_memory_vtag_other Hinit). exact I. }
    have HmacL3 : memory_address_correctness Left s3.
    { unfold memory_address_correctness. intros v0 w Hrel Hmem.
        subst s3. simpl in Hmem. unfold address_correctness.
        move: Hmem. rewrite unionmE.
        case Henc: (encode_code (code prog'')
          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
        * move=> [<-]. rewrite (encode_code_vtag_other_prog'' Henc). exact I.
        * move=> Hinit. rewrite (initial_memory_vtag_other Hinit). exact I. }
    have HepoL : entry_points_offset Left (mem s1) (mem s3).
    { unfold entry_points_offset. intros c w w' d d' proc l l'.
        intros Hrel Hmem1 Hmem3 Hcode1 Hcode3 Hcolor1 Hcolor3 Hentry1 Hentry3.
        subst s1 s3. simpl in *.
        exact: (entry_points_offset_init Hrel Hmem1 Hmem3 Hcode1 Hcode3 Hcolor1 Hcolor3 Hentry1 Hentry3). }
    have HmmL : memory_match Left [] s1 s3.
    { unfold memory_match. intros w d Hnotcode Hrel.
        subst s1 s3. simpl in *.
        split.
        * { intros Hmem3.
            move: Hmem3. rewrite unionmE.
            case Henc: (encode_code (code prog'')
              (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
            - move=> [] ?; subst v_code. exfalso. apply Hnotcode.
              exact (encode_code_is_code_prog'' Henc).
            - move=> Hinit.
              { exists d. split.
                - unfold data_match'. destruct d as [vv tt]. simpl.
                  split; [reflexivity |].
                  split; [reflexivity |].
                  have Hvtag := initial_memory_vtag_other Hinit.
                  rewrite Hvtag. reflexivity.
                - rewrite unionmE.
                  have Henc_none: encode_code (code p ++ code c)
                                    (size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c)))) w = None.
                  { eapply encode_code_initial_memory_disjoint;
      first by [exact A.memory_size_lin | exact A.memory_size_lin' | exact A.memory_size_lin''].
                    exact: (init_data_left_31 Hrel Hinit). }
                  rewrite Henc_none /=.
                  exact: (init_data_left_31 Hrel Hinit). } }
        * { intros Hmem1.
            move: Hmem1. rewrite unionmE.
            case Henc: (encode_code (code prog)
              (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.
            - move=> [] ?; subst v_code. exfalso. apply Hnotcode.
              exact (encode_code_is_code_prog Henc).
            - move=> Hinit.
              { exists d. split.
                - unfold data_match'. destruct d as [vv tt]. simpl.
                  split; [reflexivity |].
                  split; [reflexivity |].
                  have Hvtag := initial_memory_vtag_other Hinit.
                  rewrite Hvtag. reflexivity.
                - rewrite unionmE.
                  have Henc_none: encode_code (code p ++ code c')
                    (size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c')))) w = None.
                  { eapply encode_code_initial_memory_disjoint;
      first by [exact A.memory_size_lin | exact A.memory_size_lin' | exact A.memory_size_lin''].
                    exact: (init_data_left_13 Hrel Hinit). }
                  rewrite Henc_none /=.
                  exact: (init_data_left_13 Hrel Hinit). } } }
    have HmacR2 : memory_address_correctness Right s2.
    { unfold memory_address_correctness. intros v0 w Hrel Hmem.
        subst s2. simpl in Hmem. unfold address_correctness.
        move: Hmem. rewrite unionmE.
        case Henc: (encode_code (code prog')
          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
        * move=> [<-]. rewrite (encode_code_vtag_other_prog' Henc). exact I.
        * move=> Hinit. rewrite (initial_memory_vtag_other Hinit). exact I. }
    have HmacR3 : memory_address_correctness Right s3.
    { unfold memory_address_correctness. intros v0 w Hrel Hmem.
        subst s3. simpl in Hmem. unfold address_correctness.
        move: Hmem. rewrite unionmE.
        case Henc: (encode_code (code prog'')
          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
        * move=> [<-]. rewrite (encode_code_vtag_other_prog'' Henc). exact I.
        * move=> Hinit. rewrite (initial_memory_vtag_other Hinit). exact I. }
    have HepoR : entry_points_offset Right (mem s2) (mem s3).
    { unfold entry_points_offset. intros c w w' d d' proc l l'.
        intros Hrel Hmem2 Hmem3 Hcode2 Hcode3 Hcolor2 Hcolor3 Hentry2 Hentry3.
        subst s2 s3. simpl in *.
        exact: (entry_points_offset_init' Hrel Hmem2 Hmem3 Hcode2 Hcode3 Hcolor2 Hcolor3 Hentry2 Hentry3). }
    have HmmR : memory_match Right [] s2 s3.
    { unfold memory_match. intros w d Hnotcode Hrel.
        subst s2 s3. simpl in *.
        split.
        * { intros Hmem3.
            move: Hmem3. rewrite unionmE.
            case Henc: (encode_code (code prog'')
              (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
            - move=> [] ?. subst v_code. exfalso. apply Hnotcode.
              exact (encode_code_is_code_prog'' Henc).
            - move=> Hinit.
              { exists d. split.
                - unfold data_match'. destruct d as [vv tt]. simpl.
                  split; [reflexivity |].
                  split; [reflexivity |].
                  have Hvtag := initial_memory_vtag_other Hinit.
                  rewrite Hvtag. reflexivity.
                - rewrite unionmE.
                  have Henc_none: encode_code (code p' ++ code c')
                    (size (initial_memory (mt := mt) (unionm (prog_buffers p') (prog_buffers c')))) w = None.
                  { eapply encode_code_initial_memory_disjoint;
      first by [exact A.memory_size_lin | exact A.memory_size_lin' | exact A.memory_size_lin''].
                    exact: (init_data_right_32 Hrel Hinit). }
                  rewrite Henc_none /=.
                  exact: (init_data_right_32 Hrel Hinit). } }
        * { intros Hmem2.
            move: Hmem2. rewrite unionmE.
            case Henc: (encode_code (code prog')
              (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
            - move=> [] ?; subst v_code. exfalso. apply Hnotcode.
              exact (encode_code_is_code_prog' Henc).
            - move=> Hinit.
              { exists d. split.
                - unfold data_match'. destruct d as [vv tt]. simpl.
                  split; [reflexivity |].
                  split; [reflexivity |].
                  have Hvtag := initial_memory_vtag_other Hinit.
                  rewrite Hvtag. reflexivity.
                - rewrite unionmE.
                  have Henc_none: encode_code (code p ++ code c')
                    (size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c')))) w = None.
                  { eapply encode_code_initial_memory_disjoint;
      first by [exact A.memory_size_lin | exact A.memory_size_lin' | exact A.memory_size_lin''].
                    exact: (init_data_right_23 Hrel Hinit). }
                  rewrite Henc_none /=.
                  exact: (init_data_right_23 Hrel Hinit). } } }
    destruct main; [eapply match_states_left | eapply match_states_right].
    - exact: Hce.
    - constructor.
      + destruct find_rank_main_prog'' as [start'' Hfr''].
        destruct find_rank_main_prog as [start Hfr].
        have [Hfind Hstart_lt] := find_rank_Some_find Hfr.
        have [Hfind'' Hstart_lt''] := find_rank_Some_find Hfr''.
        have Hfind_lt : seq.find (fun '(_, tag) => color tag == Component.main) (code prog) < size (code prog)
          by rewrite Hfind.
        have [v Hv] := initial_pc_pos Hfind_lt (ltn_trans memory_size alloc_label_lt_w)
                         code_tags_wf_prog.
        eapply same_pc_normal.
        * rewrite init1. exact Hv.
        * subst s1. simpl.
          unfold get_offset, offset1.
          rewrite mkfmapfpE.
          have Hmain: Component.main \in domm ip.
          { apply (wfprog_main_existence Hwfp). symmetry. exact Heqmain. }
          rewrite Hmain /=.
          unfold p0.
          rewrite Hfr'' Hfr /=. eauto.
        * subst s1 s3. simpl.
          rewrite Hfind Hfind''.
          have Hd1 : size (domm (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c'))))
                   = size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c')))
            by apply size_domm_fmap.
          have Hd2 : size (domm (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c))))
                   = size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c)))
            by apply size_domm_fmap.
          rewrite Hd1 Hd2 (addnC start'') (addnC start) /word_of_nat int_diffE.
          exact (as_word_shiftD _ _ _).
      +
        subst s1 s3. simpl. reflexivity.
      +
        subst s1. simpl. unfold side_of.
        have Hmain: Component.main \in domm ip.
        { apply (wfprog_main_existence Hwfp). symmetry. exact Heqmain. }
        by rewrite Hmain.
      + exact: HmacL1.
      + exact: HmacL3.
      + exact: HepoL.
      +
        subst s1. apply: register_address_correctness_reg0; exact: erefl.
      +
        subst s3. apply: register_address_correctness_reg0; exact: erefl.
      + exact: HmmL.
      +
        unfold registers_match. intros w d.
        subst s1 s3. simpl. split.
        * intros Hd. exists d. split; [| exact Hd].
          unfold data_match. destruct d as [vv tt]. simpl.
          split; [reflexivity |].
          destruct tt; simpl; try reflexivity;
            move: Hd; rewrite /reg0 !setmE;
            repeat (case: ifP => /= _; [move=> [] _ //= |]);
            by [].
        * intros Hd. exists d. split; [| exact Hd].
          unfold data_match. destruct d as [vv tt]. simpl.
          split; [reflexivity |].
          destruct tt; simpl; try reflexivity;
            move: Hd; rewrite /reg0 !setmE;
            repeat (case: ifP => /= _; [move=> [] _ //= |]);
            by [].
    -
      constructor.
      +
        subst s2 s3. simpl. reflexivity.
      +
        subst s2. simpl. unfold side_of.
        have Hmain: Component.main \in domm ip.
        { apply (wfprog_main_existence Hwfp). symmetry. exact Heqmain. }
        by rewrite Hmain.
      + exact: HmacR2.
      + exact: HmacR3.
      + exact: HepoR.
      + exact: HmmR.
    - exact: Hce.
    -
      constructor.
      + subst s1 s3. simpl. reflexivity.
      +
        subst s1. simpl. unfold side_of.
        case Hmain: (Component.main \in domm ip).
        *
          exfalso.
          pose proof wfprog_main_existence Hwfp.
          rewrite -Heqmain in H. apply H in Hmain. congruence.
        * done.
      + exact: HmacL1.
      + exact: HmacL3.
      + exact: HepoL.
      + exact: HmmL.
    -
      constructor.
      + have Hmain_ic : Component.main \in domm ic.
        { have Hpm := cprog_main_existence Hprog_is_closed.
          simpl in Hpm. rewrite -Heqmain /= in Hpm.
          apply (wfprog_main_existence Hwfc). exact Hpm. }
        subst s2 s3. exact: (same_pc_right_init Hmain_ic).
      + subst s2 s3. simpl. reflexivity.
      +
        subst s2. simpl. unfold side_of.
        case Hmain: (Component.main \in domm ip).
        * exfalso.
          pose proof wfprog_main_existence Hwfp.
          rewrite -Heqmain in H. apply H in Hmain. congruence.
        * done.
      + exact: HmacR2.
      + exact: HmacR3.
      + exact: HepoR.
      +
        subst s2. apply: register_address_correctness_reg0; exact: erefl.
      +
        subst s3. apply: register_address_correctness_reg0; exact: erefl.
      + exact: HmmR.
      +
        unfold registers_match. intros w d.
        subst s2 s3. simpl. split.
        * intros Hd. exists d. split; [| exact Hd].
          unfold data_match. destruct d as [vv tt]. simpl.
          split; [reflexivity |].
          destruct tt; simpl; try reflexivity;
            move: Hd; rewrite /reg0 !setmE;
            repeat (case: ifP => /= _; [move=> [] _ //= |]);
            by [].
        * intros Hd. exists d. split; [| exact Hd].
          unfold data_match. destruct d as [vv tt]. simpl.
          split; [reflexivity |].
          destruct tt; simpl; try reflexivity;
            move: Hd; rewrite /reg0 !setmE;
            repeat (case: ifP => /= _; [move=> [] _ //= |]);
            by [].
  Qed.

End RecInit.
