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

  (* Chain off StepEventReturn: this pulls the WHOLE diagram (step_silent_strong1/2,
     step_silent_weak1/2, step_event_call, step_event_return) into one shared Defs instance,
     so RecompositionTop can assemble [tsim_properties_match_states]. *)
  Include StepEventReturn S.

  (*** Diagrams ***)

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

  Lemma seqE : forall len start, List.seq start len = iota start len.
  Proof. elim=> [|len IH] start; first by []. by rewrite /= IH. Qed.

  (* Buffer-layout correctness, isolated as ONE clearly-true assumption (per the admit policy this is
     allowed plumbing): [initial_memory] lays its cells contiguously at addresses [word_of_nat 0..size-1]
     by construction ([base_adress]/[concretize] partition [0,size)).  A deep cardinality fact over the
     inline [linearize_bufs] structure — Phase-5 / padding dischargeable.  The two memory leaves below
     ([initial_memory_prefix_zero], [encode_code_initial_memory_disjoint]) are PROVEN from it. *)
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


  (* The foldr output has size = size of input *)
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


  (* val of [word_of_nat] (abstract size: no nesting, no divergent conversion). *)
  Lemma valw_won (k n : nat) : val (@word_of_nat k n) = n %% 2 ^ k :> nat.
  Proof. by rewrite /word_of_nat valw_as_word. Qed.

  (* For addresses below alloc_label, the high bits (mask) are 0 *)
  Lemma small_addr_mask_zero: forall x,
      x < alloc_label ->
      andw (@word_of_nat (word_size mt) x) (@mask mt NC) = 0%w.
  Proof.
    move=> x Hx. apply: andw_mask_low. rewrite valw_won.
    have Hx32 : x < 2 ^ word_size mt.
    { rewrite word_size_mt. apply: (leq_trans Hx). rewrite /alloc_label leq_exp2l //. }
    rewrite (modn_small Hx32). apply: (leq_trans Hx). exact: ltnW alloc_label_lt_word_NC.
  Qed.

  (* The size bound is essential: code sits at [size(initmem), size(initmem)+size cde) and data
     at [0, size(initmem)); without [size(initmem)+size cde < alloc_label] the code region is not
     pinned to the low (< alloc_label, mask-0) range, so it could wrap/extend onto a data address.
     The bound is exactly memory_size{,',''}; the mask separation alone does NOT suffice since
     component_memory_prefix 0 = 0 (component-0 data shares the code mask). *)
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

  (* component_memory_prefix puts [c] in the top NC bits, so it is injective ONLY on the
     [< 2^NC] range (component ids).  Unbounded it wraps: prefix 0 = prefix (2^NC). *)
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
  
  (* The old [∀cde] label-resolution Hypotheses are GONE (they were FALSE as stated, and
     silently excluded cross-side calls).  Per-side BNZ resolution comes from the linearizer
     ([low_bnz_resolved]); JAL labels resolve at the LINKED level (locally, or in the other
     side via the [A.jal_cross_*] fields) — see [bnz_resolved_prog*]/[jal_resolved_prog*]
     after the [findopt] helpers below. *)

  (* LABEL DISJOINTNESS (linearizer property; padding preserves but cannot create it).  A label
     defined in the shared prefix [code p] does not also appear in [code c] or [code c'].  This is
     needed because [findopt] resolves to the RIGHTMOST match (see [findopt_cat] below): without
     disjointness a suffix re-definition in [c]/[c'] would shadow the prefix label.  With it, the
     prefix [Bnz]/[Jal] labels resolve identically in [code prog] (= p+c) and [code prog''] (= p+c').
     [bnz_findopt_shared] (prefix) is now a LEMMA derived from this; [bnz_findopt_shared'] (suffix)
     needs NO disjointness (the suffix-priority of [findopt] works in its favour) — both are below,
     after the [findopt] helpers. *)
  (* lifted to the [AlignmentFacts] parameter [A] (linearizer-output spec). *)
  Definition labels_disjoint_prefix := A.labels_disjoint_prefix.

  (* NO code-size alignment is assumed: the recomposition is offset-general.
     [align_data_size]/[align_data_size_left] are LEMMAS (derived from the group-C buffer
     equalities [prog_buffers_p_p']/[prog_buffers_c_c'] below); see after those hypotheses.
     [offset2_val] (after [offset1_is_zero] below) computes the Right offset as the faithful
     prefix-size difference |code p| - |code p'|. *)

  Lemma alloc_label_lt_imm: alloc_label < 2 ^ (imm_size mt).
  Proof. by rewrite /alloc_label ltn_exp2l. Qed.
  Lemma alloc_label_lt_w: alloc_label < 2 ^ (word_size mt).
  Proof. by rewrite /alloc_label ltn_exp2l. Qed.
  (* [NC < word_size mt] ([NC_lt_word]) and [alloc_label < 2^(word_size - NC)]
     ([alloc_label_lt_word_NC]) now come from [RecompositionContext] (via [Include S]), since the
     [LRC] prefix lemmas / [mask_alloc_label] need them upstream of this file. *)

  (* Which side owns main: derived from closedness + per-side wf.  Gives the main-coloured
     code cell in EVERY program variant of that side. *)
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

  (* Compiler invariant: each program's code ends in an MrHalt (the trailing Halt per block).
     This is what makes [encode_code_last_is_halt] sound — it is NOT derivable from the
     generic is_code/Other well-formedness of an arbitrary [cde]. *)
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

  (* word/bitwise leaves (per policy).  REWRITE DISCIPLINE (rocq-9.1, [mt] opaque): rewriting
     [valw_as_word]/[as_wordK] on a [val (as_word X)] where [X] itself contains a [val (as_word _)]
     makes the engine try to match the OUTER occurrence, forcing a divergent conversion on
     [2 ^ word_size mt].  So: (1) compute inner [val]s as CONCRETE [move:]-ed equations
     ([valw_won]) and rewrite those first; (2) never close a word goal with [//]/[done]/[exact: id]
     while residual [val (as_word _)] remain ([done] computes [2^32]); (3) cancel via [GRing.addIr]
     ([addw] = the word zmod [+%R]) — [rewrite addwA] alone diverges on the ring instance. *)

  (* [word_of_nat] is additive modulo [2^k] (unconditional). *)
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

  (* word (per policy): successor commutes with word_of_nat — TRUE unconditionally since
     addw is modular (addw (a mod 2^k) 1 = (a+1) mod 2^k). reflexivity over words hangs. *)
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
      + (* m < k: backward jump — m - k = 0, target is w itself *)
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
      have Henc_m := encode_code_nth (ltn_trans Hsize alloc_label_lt_w) Hv'.
      (* n0 = word_of_nat (pc0 + m), swcast n0 = word_of_nat (pc0 + m) at word_size *)
      exists v'. split.
      + have Hpm : pc0 + m < alloc_label.
        { apply: (ltn_trans _ Hsize). by rewrite ltn_add2l. }
        rewrite -Hn (swcast_word_of_nat_id Hpm) (addnC pc0 m). exact Henc_m.
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
        have [m' Hfind'] := Hres _ _ _ Hnth_cde Hneq.
        rewrite Hfind' in Hfind. discriminate.
  Qed.
  
  
  (* Well-formedness leaf (per policy): the last cell of well-formed code is a Halt — the
     compiler emits a trailing Halt per code block; not derivable from code_tags_wf alone. *)
  (* Given the trailing-Halt premise, the last encoded cell decodes to Halt.  (Residual
     admit is only the encode-position/no-wrap bookkeeping, as in encode_code_nth.) *)
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
    - (* n+1 < size cde: the successor cell exists and is code *)
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
    - (* n is the last cell: it decodes to Halt *)
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
    
  (* RESTATED on the pre-collapse buffer total (BufferLayout); the three use sites all sit
     under [memory_size*]-derived bounds, which are total-based via [A.memory_size_lin*]. *)
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

  (* [find_rank_main_shared] is GONE: the init match is offset-general ([as_word_shiftD]). *)

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

  (* the linked buffer unions of the three runs are SHAPE-equal (contents on
     the primed sides may differ — cf. BufferShape.v) *)
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

  (* pre-collapse totals fit the word (from the size premises) *)
  Lemma total_bound_prog : size (linearize_bufs (prog_buffers prog)) < 2 ^ (word_size mt).
  Proof. apply: (ltn_trans _ alloc_label_lt_w). exact: lin_size_wo_code. Qed.

  Lemma total_bound_prog' : size (linearize_bufs (prog_buffers prog')) < 2 ^ (word_size mt).
  Proof. apply: (ltn_trans _ alloc_label_lt_w). exact: lin_size_wo_code'. Qed.

  (* DATA-SIZE alignment: the data-segment size is shape-determined. *)
  Lemma align_data_size: size (initial_memory (mt := mt) (prog_buffers prog'))
                       = size (initial_memory (mt := mt) (prog_buffers prog'')).
  Proof. exact: (initial_memory_shape_size bufs_shape_prog'_prog'' total_bound_prog'). Qed.

  Lemma align_data_size_left: size (initial_memory (mt := mt) (prog_buffers prog))
                            = size (initial_memory (mt := mt) (prog_buffers prog'')).
  Proof. exact: (initial_memory_shape_size bufs_shape_prog_prog'' total_bound_prog). Qed.

  (* domain agreement of the data segments *)
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

  (* Transported data cells: the data segments agree pointwise on the cells
     of the side whose buffers are content-equal, because the OTHER side is
     shape-equal (BufferShape.initial_memory_shape_agree). *)
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

  (* [align_find_rank_main_right] is GONE: the Right init match is offset-general. *)

  Lemma encode_int_of_nat : forall n, encode_int (Z.of_nat n) = ssrint.Posz n.
  Proof. case=> [//|m] /=. by rewrite nat_of_pos_succ. Qed.

  
  Lemma size_domm_fmap: forall (T: ordType) (S: Type) (m: {fmap T -> S}),
      size (domm m) = size m.
  Proof. by move=> T S m; rewrite val_domm size_map. Qed.

  (* --- generic find_rank lemmas (recomposition infrastructure) --- *)
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

  (* find_rank (Recomposition, first-match, option) relates to mathcomp seq.find. *)
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

  (* --- findopt helpers (copied locally; PaddingCorrect.v builds AFTER this file). [findopt]
     (Merged.v) returns the RIGHTMOST match's index. --- *)
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

  (* LINKED-level BNZ resolution: a Bnz cell of a linked program resolves its label in that
     program (its side resolves it, findopt over the concatenation keeps it defined). *)
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

  (* LINKED-level JAL resolution: locally, or — for a FOREIGN label — in the other side
     (the [A.jal_cross_*] fields), which is part of the same linked program. *)
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


  (* [bnz_findopt_shared] (was a Hypothesis): a Bnz in the shared prefix [code p] resolves its
     label identically in [code prog] and [code prog''].  Both share [code p]; the label is in
     [code p] ([code_bnz_labels_resolved] on [code p]) and — by [labels_disjoint_prefix] — absent
     from [code c]/[code c'], so [findopt] (suffix-first) falls through to the prefix in both. *)
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

  (* [bnz_findopt_shared'] (was a Hypothesis): a Bnz in the shared c' SUFFIX.  No disjointness
     needed — the label is in [code c'] ([code_bnz_labels_resolved] on [code c']), and [findopt]'s
     suffix-priority returns that occurrence in both [code prog'] (=p'+c') and [code prog''] (=p+c'),
     shifted by [size (code p')] resp. [size (code p)]; the relative offset is preserved. *)
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

  (* Minimal alignment postulate: the allocator label is never a code MrLabel (alloc is a
     reserved syscall), so [findopt] never resolves it inside the code. *)
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

  (* word/bitwise (per policy): word_of_nat is injective below 2^imm_size (JAL immediates). *)
  Lemma word_of_nat_inj_imm: forall a b,
      a < 2 ^ (imm_size mt) -> b < 2 ^ (imm_size mt) ->
      @word_of_nat (imm_size mt) a = word_of_nat b -> a = b.
  Proof. move=> a b Ha Hb. exact: (won_inj Ha Hb). Qed.

  (* A MrJal l resolves to the allocator immediate iff its label IS the allocator label.
     PROVEN from no_mrlabel_alloc + word_of_nat_inj + the address ceiling (cluster A). *)
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
    - (* findopt found l at m: target is pc0 + m < alloc, so n is NOT the allocator,
         and l = alloc_label is impossible (would be a MrLabel alloc) *)
      simpl in Hn.
      have Hm_ltP : (m < size cde)%coq_nat by (apply/ltP; exact (findopt_bound Hfind)).
      split.
      + move=> Hae. exfalso.
        have Hbm : pc0 + m < 2 ^ imm_size mt by apply/ltP; lia.
        have Heq : alloc_label = pc0 + m.
        { apply (word_of_nat_inj_imm alloc_label_lt_imm Hbm). rewrite Hae. symmetry. exact Hn. }
        lia.
      + move=> Hla. exfalso. subst l. rewrite Hfind in Hno. discriminate.
    - (* findopt failed: target is (l if l=alloc else POS) *)
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

  (* ALIGNMENT INTERFACE (JAL targets; Left/shared-prefix cut; discharged by the Phase-4 NOP-padding
     pass — see project-label-alignment-padding).  This is the cross-component analogue of
     [combined_codes_forward], specialised to the JAL targets of a MrJal sitting in the shared code-p
     prefix.  Cross-component transfer is entry-only (ICall -> MrJal (make_label)) and local labels are
     component-namespaced, so the SAME jump (pinned by the two nth_error premises at the SAME index k)
     has its target cell at corresponding addresses: the two target cells carry the same tag, and their
     addresses differ exactly by the target component's offset [get_offset].  Stated conclusion-shaped
     as the file's other layout facts ([offset2_val], [bnz_findopt_shared']); the linearizer pins
     every procedure entry to the same relative position, which is what makes it a theorem. *)
  (* word: alloc_label < 2^imm so the sign-cast preserves it *)
  Lemma swcast_alloc : @swcast _ (word_size mt) (word_of_nat alloc_label : imm mt) = word_of_nat alloc_label.
  Proof.
    have H15 : alloc_label < 2 ^ imm_size mt by rewrite imm_size_mt /alloc_label ltn_exp2l //.
    by rewrite /swcast /word_of_nat (as_wordK H15).
  Qed.

  Lemma as_word_encode_int_zero : as_word (encode_int 0) = zerow :> mword mt.
  Proof. rewrite /encode_int /zerow. congr as_word. Qed.

  (* The Left-side offset is genuinely 0: a colour in [domm ip] resolves (via [find_rank])
     into the *shared* [code p] prefix of both [code prog] and [code prog''] at the same
     index, and the data segments have equal size ([prog_buffers_c_c']). Pure find_rank/Z
     reasoning — no word arithmetic.  (Moved up: used by [jal_target_corresp].) *)
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

  (* [jal_findopt_shared]: a Jal in the shared prefix [code p] resolves its label identically in
     [code prog] and [code prog''] (mirror of [bnz_findopt_shared]; extra [alloc_label] case where
     [findopt] is [None] on both via [no_mrlabel_alloc_prog{,''}]). *)

  (* [valjal]: the encoded value of a Jal cell whose label resolves to [findopt = Some m] is
     [Jal (word_of_nat (pc0 + m))] (absolute target; unlike [valbnz] the [pos] argument is unused).
     Mirror of [valbnz]. *)
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

  (* [jal_target_corresp] (was a Hypothesis): a Jal in the shared prefix [code p].  Its label is in
     [code p] ([code_jal_labels_resolved] + [labels_disjoint_prefix] ⇒ not shadowed), so it resolves
     to the same position [m < size (code p)] in both runs ([jal_findopt_shared] / [findopt_cat]).
     Hence [n = n'' = word_of_nat (pc0 + m)] ([valjal]), the targets are the same shared-prefix cell
     ([taga d = taga d']), and the target colour is in [ip] so its offset is 0 ([offset1_is_zero]).
     The [alloc_label] case is impossible — its target is out of code range ([jal_alloc_iff]). *)
  Lemma jal_target_corresp : forall k l (t' : mem_tag) (v v'' : matom) (n n'' : imm mt) d d',
    nth_error (code prog)   k = Some (MrJal l, t') ->
    nth_error (code prog'') k = Some (MrJal l, t') ->
    k < size (code p) ->   (* pins position k to the SHARED code-p prefix (same cell in both) *)
    (* v, v'' are the MrJal cells at position k, and n, n'' THEIR resolved immediates: *)
    encode_code (code prog)   (size (initial_memory (mt := mt) (prog_buffers prog)))
      (word_of_nat (k + size (initial_memory (mt := mt) (prog_buffers prog))))   = Some v ->
    encode_code (code prog'') (size (initial_memory (mt := mt) (prog_buffers prog'')))
      (word_of_nat (k + size (initial_memory (mt := mt) (prog_buffers prog'')))) = Some v'' ->
    decode_instr (vala v)   = Some (Jal n) ->
    decode_instr (vala v'') = Some (Jal n'') ->
    (* d, d' are the cells those immediates point at: *)
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
    (* make [pc0]/[pc0''] OPAQUE: their [set] bodies are [size (initial_memory …)]; if left as
       let-bindings, [lia]/[zify] unfolds them into huge terms and diverges.  All facts needing the
       bodies ([Hpc], [Hsz], [Hb], …) are already established above. *)
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
    { (* FOREIGN: cross-side call — the label lives in c/c'; both targets are the callee's
         entry cells, which carry the SAME interface-determined tag of a RIGHT colour, so the
         Left-guarded offset field is vacuous. *)
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
    (* explicit [done | …] dispatch: a bare [//]/[done] on the [nth_error_app1] side goal
       [m < length (code p)] sends [done] into a [trivial]/[assumption] scan over the huge
       context and DIVERGES.  [done] on the main goal (reflexivity) is fine. *)
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
    (* avoid [rewrite addw0] (diverges on the word ring) and reflexivity on word terms *)
    rewrite Hsw Hsw'' Hpc Hz as_word_encode_int_zero.
    by apply: esym; exact: addw0.
  Qed.

  (* the encoded value of a Bnz cell: its RELATIVE target [findopt l − k] (pc0 cancels).
     Stated via [instr_merged_to_mp ... (fun _ _ => m) k] to avoid naming the section-local
     [to_nat] notation — both sides unfold to [Bnz (to_nat r) (word_of_nat (m − k))]. *)
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
    k < size (code p) ->   (* pins position k to the SHARED code-p prefix *)
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

  (* same MrJal l (pinned by nth_error) resolves to the allocator on one side iff on the
     other — the alloc disjunct happens exactly when l = alloc_label, which is shared.
     (NOTE: the old [jal_imm_aligned] concluding [n = n''] was UNSOUND — false for a
     cross-component JAL whose target sits in code c vs code c'.) *)
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


  (* [offset2_val]: a c'-component's Right offset is the (possibly NEGATIVE) prefix-size
     difference |code p| - |code p'|.  Mirror of [offset1_is_zero] for the SUFFIX.  [cc ∈ ic]
     colours no cell of [code p]/[code p'] (disjoint from [ip]), so its rank in
     [code prog'' = code p ++ code c'] is [size (code p) + rank-in-c'] and in
     [code prog' = code p' ++ code c'] is [size (code p') + rank-in-c'].  The common rank-in-c'
     and the equal data sizes cancel, leaving the prefix-size difference.  NO alignment assumed. *)
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
    { simpl. rewrite size_cat. move/ltP: Hk_in_p => ?. apply/ltP. lia. }
    have Hk_lt2: k < size (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
      (encode_instr_atom x (fun l default => match findopt (fun p0 => match p0.1 with MrLabel l0 => l == l0 | _ => false end) (code prog'') with Some m => pc0'' + m | None => if l == alloc_label then l else default end) (pc0'' + size (code prog'') - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) (code prog'')).1.
    { (* change (k < size (foldr _ ([::], 0) (code prog'')).1). *)
      rewrite encode_code_foldr_size. exact Hk_lt''. }
    destruct (nth_error_Some_ex Hk_lt2) as [v'' Hv''].
    have Henc'' := encode_code_nth (ltn_trans memory_size'' alloc_label_lt_w) Hv''.
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
      { (* color t ∈ domm ip; code c / code c' entries have colour in domm ic
           (disjoint), so the first match is in the shared code p prefix. *)
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

      (* Step 3: word arithmetic *)
      (* off = encode_int (Z.of_nat (start + pc0'') - Z.of_nat (start + pc0)) *)
      have Hpc_eq: pc0'' = pc0.
      { rewrite /pc0'' /pc0. exact: (esym align_data_size_left). }
      rewrite Hpc_eq. unfold pc0.
      rewrite -Hoff_eq.
      rewrite align_data_domm_left_u.
      rewrite int_diffE GRing.subrr.
      (* goal: word_of_nat (k+pc0) + as_word 0 = word_of_nat (k+pc0).
         Close via apply: addw0 (NOT reflexivity — that converts the big word term and hangs). *)
      rewrite as_word_int0. apply: addw0.
      (* find_rank (code prog) = None branch: Hoff is (obind (fun _ => None) _) = Some off, contradictory *)
      exfalso. move: Hoff.
      by case: (find_rank (fun '(_, tag) => color tag == color t) (code p ++ code c')) => [a|].
      }
    (* Step 8: construct v' and decode_match *)
    exists (vala v'').
    split.
    - (* decode_match: case on instruction type *)
      destruct i.
      9: { (* MrBnz: local branch — Bnz decodes (not Jal); v = v'' since the relative
              target resolves identically (the label is in the shared code p prefix). *)
        apply decode_match_no_JAL.
        - move=> imm; rewrite (Hval : v = _) encodeK; discriminate.
        - rewrite Hval''; move=> imm; rewrite encodeK; discriminate.
        - rewrite Hw in Henc.
          exact: (bnz_encoding_aligned Hnth_cde Hnth_prog'' Hk_in_p Henc Henc''). }
      9: { (* MrJal: cross-component jump — decode_match_JAL relates the two targets
              (which sit at offset get_offset(target-component) apart). *)
        have [n Dv] : exists n, decode_instr v = Some (Jal n).
        { rewrite (Hval : v = _); eexists; apply encodeK. }
        have [n'' Dv''] : exists n'', decode_instr (vala v'') = Some (Jal n'').
        { rewrite Hval''; eexists; apply encodeK. }
        have JT  := encode_code_jal_target code_tags_wf_prog   jal_resolved_prog   memory_size   Henc   Dv.
        have JT'' := encode_code_jal_target code_tags_wf_prog'' jal_resolved_prog'' memory_size'' Henc'' Dv''.
        case: JT => [[d [Hd Hcd]] | Halloc]; case: JT'' => [[d' [Hd' Hcd']] | Halloc''].
        - (* both targets are code cells: decode_match_JAL via the c/c' correspondence *)
          rewrite Hw in Henc.
          have [Htagd Hreld] := jal_target_corresp Hnth_cde Hnth_prog'' Hk_in_p Henc Henc'' Dv Dv'' Hd Hd'.
          eapply decode_match_JAL.
          + exact Dv.
          + exact Dv''.
          + by rewrite unionmE Hd.        (* mem prog (swcast n) = Some d *)
          + by rewrite unionmE Hd'.       (* mem prog'' (swcast n'') = Some d' *)
          + exact Hcd.                     (* is_code (taga d) *)
          + exact Htagd.                   (* taga d = taga d' *)
          + exact Hreld.                   (* the (guarded) offset relation *)
        - (* prog code, prog'' alloc — vacuous: l = alloc_label resolves alike in both *)
          exfalso.
          rewrite Hw in Henc.
          have Hcons := jal_resolution_consistent Hnth_cde Hnth_prog'' Henc Henc'' Dv Dv''.
          have Hna : word_of_nat alloc_label = n := proj2 Hcons Halloc''.
          have HN := @alloc_label_not_in_encode_code (code prog)
                       (size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c)))) memory_size.
          move: Hd. rewrite -Hna swcast_alloc => Hd.
          rewrite HN in Hd. discriminate.
        - (* prog alloc, prog'' code — symmetric *)
          exfalso.
          rewrite Hw in Henc.
          have Hcons := jal_resolution_consistent Hnth_cde Hnth_prog'' Henc Henc'' Dv Dv''.
          have Hna : word_of_nat alloc_label = n'' := proj1 Hcons Halloc.
          have HN := @alloc_label_not_in_encode_code (code prog'')
                       (size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c')))) memory_size''.
          move: Hd'. rewrite -Hna swcast_alloc => Hd'.
          rewrite HN in Hd'. discriminate.
        - (* both alloc: jump to the allocator entry *)
          apply decode_match_alloc_JAL.
          + by rewrite Dv Halloc.
          + by rewrite Dv'' Halloc''. }
      all: apply decode_match_no_JAL;
        [ move=> imm; rewrite (Hval : v = _) encodeK; discriminate
        | rewrite Hval''; move=> imm; rewrite encodeK; discriminate
        | rewrite Hval''; exact Hval ].
    - (* mem prog'' (w + as_word off) = Some (vala v'')@t *)
      rewrite Haddr. simpl.
      rewrite unionmE Henc'' /=.
      simpl in Htag. rewrite Htag. destruct v''. subst. simpl. eauto.
  Qed.

  (* Backward (Right→Left) companion of combined_codes_forward: code encoded in prog''
     at (w + off) with color in domm ip corresponds to code in prog at w.
     Symmetric to combined_codes_forward (shared code-p prefix); encoding/layout per policy. *)
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
    (* Step 1: position k of the given prog'' cell *)
    destruct (encode_code_nth_inv Henc'') as [k [Hwk [Hlt'' Hnth_f'']]].
    destruct (encode_code_foldr_nth Hnth_f'') as [i [t' [Hnth_prog'' [Htag Hval_g]]]].
    (* Step 2: k < size (code p) since color t ∈ domm ip (entry in shared code p prefix) *)
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
    (* Step 3: same entry at position k in code prog *)
    have Hnth_cde: nth_error (code prog) k = Some (i, t').
    { simpl. rewrite nth_error_app1; [| apply/ltP; exact Hk_in_p].
      have: nth_error (code prog'') k = Some (i, t').
      { eauto. }
      simpl. rewrite nth_error_app1; [done | apply/ltP; exact Hk_in_p]. }
    (* Step 4: construct the prog cell at position k *)
    have Hk_lt: k < size (code prog).
    { simpl. rewrite size_cat. move/ltP: Hk_in_p => ?. apply/ltP. lia. }
    have Hk_lt2: k < size (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
      (encode_instr_atom x (fun l default => match findopt (fun p0 => match p0.1 with MrLabel l0 => l == l0 | _ => false end) (code prog) with Some m => pc0 + m | None => if l == alloc_label then l else default end) (pc0 + size (code prog) - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) (code prog)).1.
    { rewrite encode_code_foldr_size. exact Hk_lt. }
    destruct (nth_error_Some_ex Hk_lt2) as [v' Hv'].
    have Henc := encode_code_nth (ltn_trans memory_size alloc_label_lt_w) Hv'.
    (* Henc : encode_code (code prog) pc0 (word_of_nat (k + pc0)) = Some v' *)
    destruct (encode_code_foldr_nth Hv') as [i' [t'2 [Hnth_cde2 [Htag_c Hval_c]]]].
    rewrite Hnth_cde in Hnth_cde2. injection Hnth_cde2 => Ht'2 Hi'.
    subst i' t'2.
    (* Step 5: w = word_of_nat (k + pc0) — the offset is 0 (shared prefix, equal data) *)
    have Hwaddr: w = word_of_nat (k + pc0).
    { have Hoff0 := offset1_is_zero Hrel Hoff.
      have Hpc_eq: size (@initial_memory mt (prog_buffers prog'')) = pc0.
      { rewrite /pc0. exact: (esym align_data_size_left). }
      move: Hwk. rewrite Hoff0 Hpc_eq => Hwk'.
      (* Hwk' : (w + as_word (encode_int 0))%w = word_of_nat (k + pc0).
         Rewrite in the hypothesis + exact (NOT reflexivity over the big word term). *)
      rewrite as_word_encode_int_zero addw0 in Hwk'. exact Hwk'. }
    (* Step 6: construct v' and decode_match *)
    exists (vala v').
    split.
    - destruct i.
      9: { (* MrBnz *)
        apply decode_match_no_JAL.
        - move=> imm; rewrite Hval_c encodeK; discriminate.
        - rewrite (Hval_g : v = _); move=> imm; rewrite encodeK; discriminate.
        - rewrite Hwk in Henc''.
          exact: (bnz_encoding_aligned Hnth_cde Hnth_prog'' Hk_in_p Henc Henc''). }
      9: { (* MrJal *)
        have [n Dv] : exists n, decode_instr (vala v') = Some (Jal n).
        { rewrite Hval_c; eexists; apply encodeK. }
        have [n'' Dv''] : exists n'', decode_instr v = Some (Jal n'').
        { rewrite (Hval_g : v = _); eexists; apply encodeK. }
        have JT  := encode_code_jal_target code_tags_wf_prog   jal_resolved_prog   memory_size   Henc   Dv.
        have JT'' := encode_code_jal_target code_tags_wf_prog'' jal_resolved_prog'' memory_size'' Henc'' Dv''.
        case: JT => [[d [Hd Hcd]] | Halloc]; case: JT'' => [[d' [Hd' Hcd']] | Halloc''].
        - (* both code *)
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
        - (* prog code, prog'' alloc — vacuous: l = alloc_label resolves alike in both *)
          exfalso.
          rewrite Hwk in Henc''.
          have Hcons := jal_resolution_consistent Hnth_cde Hnth_prog'' Henc Henc'' Dv Dv''.
          have Hna : word_of_nat alloc_label = n := proj2 Hcons Halloc''.
          have HN := @alloc_label_not_in_encode_code (code prog)
                       (size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c)))) memory_size.
          move: Hd. rewrite -Hna swcast_alloc => Hd.
          rewrite HN in Hd. discriminate.
        - (* prog alloc, prog'' code — vacuous *)
          exfalso.
          rewrite Hwk in Henc''.
          have Hcons := jal_resolution_consistent Hnth_cde Hnth_prog'' Henc Henc'' Dv Dv''.
          have Hna : word_of_nat alloc_label = n'' := proj1 Hcons Halloc.
          have HN := @alloc_label_not_in_encode_code (code prog'')
                       (size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c')))) memory_size''.
          move: Hd'. rewrite -Hna swcast_alloc => Hd'.
          rewrite HN in Hd'. discriminate.
        - (* both alloc *)
          apply decode_match_alloc_JAL.
          + by rewrite Dv Halloc.
          + by rewrite Dv'' Halloc''. }
      all: apply decode_match_no_JAL;
        [ move=> imm; rewrite Hval_c encodeK; discriminate
        | rewrite (Hval_g : v = _); move=> imm; rewrite encodeK; discriminate
        | rewrite (Hval_g : v = _); exact Hval_c ].
    - (* mem prog w = Some (vala v')@t *)
      rewrite Hwaddr. simpl.
      rewrite unionmE Henc /=.
      simpl in Htag. rewrite Htag. destruct v'. subst. simpl. eauto.
  Qed.

  (* ALIGNMENT INTERFACE (JAL targets; Right/c'-suffix cut; discharged by the Phase-4 NOP-padding pass).
     Same padding justification as the Left [jal_target_corresp], adapted to the prog'↔prog'' cut where
     [code c'] is a SUFFIX sitting at different offsets (after [code p'] resp. [code p]), so the same c'
     entry has DIFFERENT positions k (in prog') and k'' (in prog''); the padding equalises the prefixes
     so the targets correspond. *)
  (* [jal_target_corresp'] (was a Hypothesis): a Jal in the shared c' SUFFIX.  Mirror of
     [jal_target_corresp]: the label is in [code c'] (so NO disjointness needed — [findopt]'s
     suffix-priority finds it), resolving at the SAME relative index [mc] in both runs; the targets
     are the same c'-cell ([taga d = taga d']); the target colour is in [ic] (side Right) so its
     offset is the prefix-size difference ([offset2_val]); [as_word_shiftAB] does the word arithmetic. *)
  Lemma jal_target_corresp' : forall k k'' l (t' : mem_tag) (v v'' : matom) (n n'' : imm mt) d d',
    nth_error (code prog')  k   = Some (MrJal l, t') ->
    nth_error (code prog'') k'' = Some (MrJal l, t') ->
    size (code p') <= k ->                          (* k is in the c' SUFFIX of prog'     *)
    k'' = size (code p) + (k - size (code p')) ->   (* k'' is the SAME c'-index in prog'' *)
    (* v, v'' are the MrJal cells at positions k / k'', and n, n'' THEIR immediates: *)
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
    (* the c' suffix cell (mirror of [bnz_findopt_shared'] extraction) *)
    have Hj : nth_error (code c') (k - size (code p')) = Some (MrJal l, t').
    { move: Hp'. have ->: code prog' = code p' ++ code c' by [].
      rewrite nth_error_app2; last by apply/leP; exact: Hsfx. by []. }
    (* l <> alloc_label (else target out of code range, no d) *)
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
    { (* FOREIGN: the c'-label lives in p'/p; both targets are the callee's entry cells with
         the SAME interface-determined tag of a LEFT colour, so the Right-guarded offset
         field is vacuous. *)
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
    (* findopt: suffix-priority resolves into c' on BOTH runs (no disjointness needed) *)
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
    (* both targets land on c'-index [mc] *)
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
    (* [side_of (color td) = Right]: explicit branch handling — a bare [//] would run [done] on
       the [color td ∈ ip] (true) branch goal [Left = Right], which [done] cannot close by
       reflexivity and then DIVERGES scanning the huge context. *)
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
    size (code p') <= k ->                          (* same c' cell, suffix index *)
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

  (* same MrJal l (pinned by nth_error) resolves to the allocator on one side iff on the
     other — the label is in the shared c', so it is found in both or neither. *)
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

  (* Right-side address correspondence (per policy, padding-justified): the same c' entry
     (positions k in prog', k'' in prog'') has prog''-address = prog'-address + offset2, since
     offset2 (color t') = encode_int of the uniform suffix shift size(code p) - size(code p'). *)
  Lemma offset2_addr_corresp : forall (i : Merged.instr) (t' : mem_tag) off k k'',
    color t' \in domm ic ->
    offset2 (color t') = Some off ->
    nth_error (code prog')  k   = Some (i, t') ->
    nth_error (code prog'') k'' = Some (i, t') ->
    size (code p') <= k ->                          (* same c' cell at the same suffix index *)
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

  (* word right-cancellation: [addw] is the word zmod [+%R], so this is [GRing.addIr].
     ([rewrite addwA] alone diverges on the ring instance, hence the GRing route.) *)
  Lemma addwIr : forall (x y a : mword mt), (x + a)%w = (y + a)%w -> x = y.
  Proof. move=> x y a H. apply: (GRing.addIr a). exact: H. Qed.

  (* Backward read of the same correspondence: recover the prog' address from the prog'' one.
     PROVEN from the forward version by right-cancelling [as_word off]. *)
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

  (* Right-side (c'-shared) companions: prog' and prog'' share code c'. offset2/domm ic.
     Symmetric to the Left combined_codes_forward/backward; encoding/layout per policy. *)
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
    (* Step 1: position k of the given prog' cell *)
    destruct (encode_code_nth_inv Henc) as [k [Hw [Hlt Hnth]]].
    destruct (encode_code_foldr_nth Hnth) as [i [t' [Hnth_prog' [Htag Hval]]]].
    (* Step 2: size (code p') <= k — a colour-ic entry is in the code c' suffix *)
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
    (* Step 3: the same c' entry sits at k'' = size (code p) + (k - size (code p')) in prog'' *)
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
    (* Step 4: construct the prog'' cell at k'' *)
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
    (* Step 5: address correspondence — off = offset2 encodes (k''+pc0'')-(k+pc0') *)
    have Haddr: (w + as_word off)%w = word_of_nat (k'' + pc0'').
    { have Et : t = t' := Htag.
      rewrite Hw. rewrite Et in Hrel Hoff.
      exact: (offset2_addr_corresp Hrel Hoff Hnth_prog' Hnth_prog'' Hkp' Hidx). }
    (* Step 6: construct v'' and decode_match *)
    exists (vala v'').
    split.
    - destruct i.
      9: { (* MrBnz: relative branch — same displacement, so same bits *)
        apply decode_match_no_JAL.
        - move=> imm; rewrite (Hval : v = _) encodeK; discriminate.
        - rewrite Hval''; move=> imm; rewrite encodeK; discriminate.
        - rewrite Hw in Henc.
          exact: (bnz_encoding_aligned' Hnth_prog' Hnth_prog'' Hkp' Hidx Henc Henc''). }
      9: { (* MrJal *)
        have [n Dv] : exists n, decode_instr v = Some (Jal n).
        { rewrite (Hval : v = _); eexists; apply encodeK. }
        have [n'' Dv''] : exists n'', decode_instr (vala v'') = Some (Jal n'').
        { rewrite Hval''; eexists; apply encodeK. }
        have JT  := encode_code_jal_target code_tags_wf_prog'  jal_resolved_prog'  memory_size'  Henc   Dv.
        have JT'' := encode_code_jal_target code_tags_wf_prog'' jal_resolved_prog'' memory_size'' Henc'' Dv''.
        case: JT => [[d [Hd Hcd]] | Halloc]; case: JT'' => [[d' [Hd' Hcd']] | Halloc''].
        - (* both code *)
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
        - (* prog' code, prog'' alloc — vacuous: l resolves consistently *)
          exfalso.
          rewrite Hw in Henc.
          have Hcons := jal_resolution_consistent' Hnth_prog' Hnth_prog'' Henc Henc'' Dv Dv''.
          have Hna : word_of_nat alloc_label = n := proj2 Hcons Halloc''.
          move: Hd. rewrite -Hna swcast_alloc => Hd.
          have HN := @alloc_label_not_in_encode_code (code prog')
                       (size (initial_memory (mt := mt) (unionm (prog_buffers p') (prog_buffers c')))) memory_size'.
          rewrite HN in Hd. discriminate.
        - (* prog' alloc, prog'' code — vacuous *)
          exfalso.
          rewrite Hw in Henc.
          have Hcons := jal_resolution_consistent' Hnth_prog' Hnth_prog'' Henc Henc'' Dv Dv''.
          have Hna : word_of_nat alloc_label = n'' := proj1 Hcons Halloc.
          move: Hd'. rewrite -Hna swcast_alloc => Hd'.
          have HN := @alloc_label_not_in_encode_code (code prog'')
                       (size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c')))) memory_size''.
          rewrite HN in Hd'. discriminate.
        - (* both alloc *)
          apply decode_match_alloc_JAL.
          + by rewrite Dv Halloc.
          + by rewrite Dv'' Halloc''. }
      all: apply decode_match_no_JAL;
        [ move=> imm; rewrite (Hval : v = _) encodeK; discriminate
        | rewrite Hval''; move=> imm; rewrite encodeK; discriminate
        | rewrite Hval''; exact Hval ].
    - (* mem prog'' (w + as_word off) = Some (vala v'')@t *)
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
    (* Step 1: position k'' of the given prog'' cell *)
    destruct (encode_code_nth_inv Henc'') as [k'' [Hwk [Hlt'' Hnth_f'']]].
    destruct (encode_code_foldr_nth Hnth_f'') as [i [t' [Hnth_prog'' [Htag Hval_g]]]].
    (* Step 2: size (code p) <= k'' — colour-ic entry is in the code c' suffix of prog'' *)
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
    (* Step 3: the same c' entry sits at k = size (code p') + (k'' - size (code p)) in prog' *)
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
    (* Step 4: construct the prog' cell at k *)
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
    (* Step 5: address — w = word_of_nat (k + pc0') (offset2 + suffix shift) *)
    have Hwaddr: w = word_of_nat (k + pc0').
    { have Et : t = t' := Htag.
      rewrite Et in Hrel Hoff.
      exact: (offset2_addr_corresp_bwd Hrel Hoff Hnth_prog' Hnth_prog'' Hkp' Hidx Hwk). }
    (* Step 6: construct v' and decode_match *)
    exists (vala v').
    split.
    - destruct i.
      9: { (* MrBnz *)
        apply decode_match_no_JAL.
        - move=> imm; rewrite Hval_c encodeK; discriminate.
        - rewrite (Hval_g : v = _); move=> imm; rewrite encodeK; discriminate.
        - rewrite Hwk in Henc''.
          exact: (bnz_encoding_aligned' Hnth_prog' Hnth_prog'' Hkp' Hidx Henc Henc''). }
      9: { (* MrJal *)
        have [n Dv] : exists n, decode_instr (vala v') = Some (Jal n).
        { rewrite Hval_c; eexists; apply encodeK. }
        have [n'' Dv''] : exists n'', decode_instr v = Some (Jal n'').
        { rewrite (Hval_g : v = _); eexists; apply encodeK. }
        have JT  := encode_code_jal_target code_tags_wf_prog'  jal_resolved_prog'  memory_size'  Henc   Dv.
        have JT'' := encode_code_jal_target code_tags_wf_prog'' jal_resolved_prog'' memory_size'' Henc'' Dv''.
        case: JT => [[d [Hd Hcd]] | Halloc]; case: JT'' => [[d' [Hd' Hcd']] | Halloc''].
        - (* both code *)
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
        - (* prog' code, prog'' alloc — vacuous *)
          exfalso.
          rewrite Hwk in Henc''.
          have Hcons := jal_resolution_consistent' Hnth_prog' Hnth_prog'' Henc Henc'' Dv Dv''.
          have Hna : word_of_nat alloc_label = n := proj2 Hcons Halloc''.
          move: Hd. rewrite -Hna swcast_alloc => Hd.
          have HN := @alloc_label_not_in_encode_code (code prog')
                       (size (initial_memory (mt := mt) (unionm (prog_buffers p') (prog_buffers c')))) memory_size'.
          rewrite HN in Hd. discriminate.
        - (* prog' alloc, prog'' code — vacuous *)
          exfalso.
          rewrite Hwk in Henc''.
          have Hcons := jal_resolution_consistent' Hnth_prog' Hnth_prog'' Henc Henc'' Dv Dv''.
          have Hna : word_of_nat alloc_label = n'' := proj1 Hcons Halloc.
          move: Hd'. rewrite -Hna swcast_alloc => Hd'.
          have HN := @alloc_label_not_in_encode_code (code prog'')
                       (size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c')))) memory_size''.
          rewrite HN in Hd'. discriminate.
        - (* both alloc *)
          apply decode_match_alloc_JAL.
          + by rewrite Dv Halloc.
          + by rewrite Dv'' Halloc''. }
      all: apply decode_match_no_JAL;
        [ move=> imm; rewrite Hval_c encodeK; discriminate
        | rewrite (Hval_g : v = _); move=> imm; rewrite encodeK; discriminate
        | rewrite (Hval_g : v = _); exact Hval_c ].
    - (* mem prog' w = Some (vala v')@t *)
      clear Hidx Hkp'.
      rewrite Hwaddr. simpl.
      rewrite unionmE Henc /=.
      simpl in Htag. rewrite Htag. destruct v'. subst. simpl. eauto.
  Qed.

  (* fmap-domm plumbing (per policy): domm reg0 = fset (ra :: map word_of_nat reg_list).
     Same 12 keys on both sides, reordered. Used for the register_domm conjuncts. *)
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

  (* encoding/layout (per policy): the initial PC = first code address
     (word_of_nat (size data)) points to the first encoded instruction
     whenever the code is non-empty. *)
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

  (* Routing: a code cell in the initial memory comes from encode_code (the data segment
     [initial_memory] holds no code cells). *)
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

  (* Well-formedness postulate (per policy): entry tags are unique per procedure — each proc
     has a single entry instruction, so two entry cells for the same proc are the same cell. *)
  (* Restricted to the actual code prog'', AND requiring the same component [color t1 = color t2]:
     Procedure.id is per-component, so without the color a proc-id shared by p and c' would be a
     counterexample.  Same component + same proc-id ⇒ one entry instruction ⇒ same position. *)
  (* Index-splitting of a prog''-cell into its p / c' part. *)
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
    - (* both in p *)
      have Ht12 : t1 = t2
        := low_entry_det A.lin_wf_p (nth_error_In _ _ Hp1) (nth_error_In _ _ Hp2) Hcol He1 He2 Hpe.
      have Hee : Some e1 = Some e2 by rewrite -He1 -He2 Ht12.
      case: Hee => Hee. rewrite -Hee in He2.
      exact: (wfprog_unique_entry_points Hwfp (Logic.eq_refl (color t1)) (esym Hcol)
                He1 He2 Hp1 Hp2).
    - (* p vs c': colour clash *)
      exfalso.
      have Hin1 : color t1 \in domm ip by apply: code_color_p; exact: (nth_error_In _ _ Hp1).
      have Hin2 : color t2 \in domm ic by apply: code_color_c'; exact: (nth_error_In _ _ Hc2).
      by move: (fdisjointP Hdis _ Hin1); rewrite Hcol Hin2.
    - (* c' vs p: colour clash *)
      exfalso.
      have Hin1 : color t1 \in domm ic by apply: code_color_c'; exact: (nth_error_In _ _ Hc1).
      have Hin2 : color t2 \in domm ip by apply: code_color_p; exact: (nth_error_In _ _ Hp2).
      by move: (fdisjointP Hdis _ Hin2); rewrite -Hcol Hin1.
    - (* both in c' *)
      have Ht12 : t1 = t2
        := low_entry_det A.lin_wf_c' (nth_error_In _ _ Hc1) (nth_error_In _ _ Hc2) Hcol He1 He2 Hpe.
      have Hee : Some e1 = Some e2 by rewrite -He1 -He2 Ht12.
      case: Hee => Hee. rewrite -Hee in He2.
      have Hk12 : k1 - size (code p) = k2 - size (code p).
      { exact: (wfprog_unique_entry_points Hwfc' (Logic.eq_refl (color t1)) (esym Hcol)
                  He1 He2 Hc1 Hc2). }
      by lia.
  Qed.

  (* The entry cell for a procedure of a component c ∈ domm ip sits in the SHARED code-p
     prefix, hence at the SAME address in prog and prog''.  PROVEN: shared prefix +
     entry_tag_unique + equal data segments (offset1 is 0). *)
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

  (* Right-side encoding leaf: the entry cell for a component c ∈ domm ic sits in the
     shared code-c' SUFFIX, so its prog''-address = prog'-address + offset2 c (the uniform
     suffix shift). Padding-justified, per policy. *)
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
    (* d's cell sits in the shared c' suffix (else color t ∈ ip, contradicting c ∈ ic) *)
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
    (* d's c'-suffix cell, viewed as a [code prog''] cell.  [seq.nth_error_app2] keeps everything
       in ssrnat (the [List] version drops into coq_nat + [length] and makes the index arithmetic
       intractable). *)
    have Hc'cell : nth_error (code c') (k - size (code p')) = Some (i, t).
    { move: Hnth_cde. rewrite /prog' /program_link /= nth_error_app2; [done | apply/leP; exact Hkp]. }
    have Hprog''_d : nth_error (code prog'') (size (code p) + (k - size (code p'))) = Some (i, t).
    { rewrite /prog'' /program_link /= nth_error_app2; last by apply/leP; exact: leq_addr.
      rewrite -Hc'cell. congr nth_error.
      have Hlen : length (code p) = size (code p) by []. rewrite Hlen. lia. }
    (* entry_tag_unique pins both c'-entry cells to the same suffix position *)
    have Hk''eq : size (code p) + (k - size (code p')) = k''.
    { apply: (entry_tag_unique Hprog''_d Hnth_cde'').
      - by rewrite Hct Hct''.
      - exact Hent_t.
      - exact Hent_t''.
      - reflexivity. }
    (* off = 0 (alignment), and w' = w: the suffix index matches and prefix/data sizes are equal *)
    have Hoff0 : off = ((ssrint.Posz (size (code p)) - ssrint.Posz (size (code p')))%R)
      by move: (offset2_val Hc); rewrite Hoff; move=> [->].
    rewrite Hoff0 Hwk Hwk'' -Hk''eq -align_data_size.
    set D := size (initial_memory (mt := mt) (prog_buffers prog')).
    have -> : k + D = ((k - size (code p')) + D) + size (code p') by lia.
    have -> : size (code p) + (k - size (code p')) + D
            = ((k - size (code p')) + D) + size (code p) by lia.
    rewrite /word_of_nat. exact (as_word_shiftAB _ _ _ _).
  Qed.

  (* encoding/layout: two code entries for the same component c ∈ domm ip, with the same
     entry point, in prog and prog'' (which share code p), sit at addresses related by
     offset1 c — which is 0 on the Left (shared prefix, equal data). *)
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

  (* Right-side companion of entry_points_offset_init: prog' and prog'' share code c';
     entries for c ∈ domm ic are related by offset2 c (the suffix shift, generally ≠ 0). *)
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

  (* The initial PCs of prog' and prog'' (which share code c', with main ∈ domm ic in
     the right case) are main's entry, related by offset2 main = word_of_nat_offset. *)
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

  (* The pc of any initial state points at the main entry — [find]'s first colour-[main] code
     cell — which [encode_code] lays down as a CODE cell coloured [Component.main] = [color_of].
     So [pc_code_color] holds of each initial state.  Mirrors [initial_pc_pos]. *)
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
    destruct main; [eapply match_states_left | eapply match_states_right].
    - eapply common_equiv_def; eauto.
      (* try (eapply common_equiv_def || econstructor); simpl. *)
      + unfold initial_state in init1. simpl in init1. destruct s1. inv init1. simpl. done.
      + unfold initial_state in init2. simpl in init2. destruct s2. inv init2. simpl. done.
      + unfold initial_state in init3. simpl in init3. destruct s3. inv init3. simpl. done.
      + rewrite init3. simpl. econstructor.
      + inv init1. exact: register_domm_reg0.
      + inv init2. exact: register_domm_reg0.
      + inv init3. exact: register_domm_reg0.
      + unfold general_memory_correctness.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
        * unfold memory_prefix_condition. intros c w v.                                                                                                                                                       
          inv init1. simpl.                                                                                                                                                                                   
          rewrite unionmE.                                                                                                                                                                                    
          case Henc: (encode_code (code prog)                                                                                                                                                                 
                        (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.                                                                                                                                   
          -- (* w in encode_code: value is code, contradicts not is_code *)                                                                                                                                    
            move=> [<-] _ Hnot_code. right.                                                                                                                                                                     
            exfalso. apply Hnot_code.                                                                                                                                                                         
            eapply encode_code_is_code_prog in Henc; eauto.
          -- (* w only in initial_memory *)
            move=> Hinit _ _.
            right. by rewrite mem_domm Hinit.

        * unfold memory_prefix_condition'. simpl.
          { intros c0 w v Hbound Hmem Hprefix.
            subst s1. simpl in Hmem.
            move: Hmem. rewrite unionmE.
            case Henc: (encode_code (code prog)
                          (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.
            - move=> [<-].
              exfalso.
              have Hcode_prefix := encode_code_prefix memory_size Henc.
              rewrite Hcode_prefix in Hprefix.
              exact (code_prefix_neq_data_prefix Hbound Hprefix).
            - move=> Hinit.
              exfalso.
              have Hpref0: andw w (mask (NC := NC)) = @component_memory_prefix mt NC (ssrint.Posz 0).
              { intros.
                eapply initial_memory_prefix_zero; eauto.
                eapply lin_size_wo_code. }
              rewrite Hpref0 in Hprefix.
              eapply (code_prefix_neq_data_prefix Hbound) in Hprefix. auto.
          }
        * { unfold code_prefix_condition. intros w v.
            subst s1. simpl.
            rewrite unionmE.
            case Henc: (encode_code (code prog)
                          (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.
            - move=> [<-] Hcode.
              apply/eqP.
              exact (encode_code_prefix memory_size Henc).
            - (* w in initial_memory *)
              move=> Hinit Hcode.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
        * unfold alloc_empty. simpl.
          subst s1. simpl.
          rewrite unionmE.
          rewrite alloc_label_not_in_encode_code /=.
          -- rewrite alloc_label_not_in_initial_memory //=.
             by apply (leq_ltn_trans (leq_addr _ _) A.memory_size_lin).
          -- by apply memory_size.
        * { unfold BNZ_correctness. intros w v.
            subst s1.
            rewrite unionmE.
            case Henc: (encode_code (code prog)
                          (size (initial_memory (prog_buffers prog))) w) => [v_code | ].
            - move=> [<-] Hcode.
              case Hdec: (decode_instr (vala v_code)) => [i | ] //=.
              destruct i => //=.
              + have [v' [Hv' Hcode']] := encode_code_bnz_target code_tags_wf_prog bnz_resolved_prog memory_size Henc Hdec.
                exists v'. split; [| exact Hcode'].
                rewrite unionmE Hv' //.
              + have [[v' [Hv' Hcode']] | Halloc] := encode_code_jal_target code_tags_wf_prog jal_resolved_prog memory_size Henc Hdec.
                * left. exists v'. split; [| exact Hcode'].
                  rewrite unionmE Hv' //.
                * right. exact Halloc.
            - move=> Hinit Hcode.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
        * unfold end_condition.
          { intros w v.
            subst s1.
            rewrite unionmE.
            case Henc: (encode_code (code prog)
                          (size (initial_memory (prog_buffers prog))) w) => [v_code | ].
            - move=> [<-] Hcode.
              have [Hhalt | [v' [Hv' Hcode']]] := encode_code_end_condition code_tags_wf_prog code_last_halt_prog Henc Hcode (ltn_trans memory_size alloc_label_lt_w).
              + left. by rewrite Hhalt.
              + right. exists v'. split; [| exact Hcode'].
                rewrite unionmE Hv' //.
            - move=> Hinit Hcode.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
        * unfold color_in_memory. simpl.
          { intros w d.
            subst s1. simpl.
            rewrite unionmE.
            case Henc: (encode_code (code prog)
                          (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.
            - move=> [<-].
              eapply encode_code_color_prog; eauto.
            - move=> Hinit.
              eapply initial_memory_color in Hinit; eauto.
              rewrite domm_buffers_p domm_buffers_c in Hinit.
              eauto. }
        * { unfold entry_is_code. intros w d e.
            subst s1. simpl.
            rewrite unionmE.
            case Henc: (encode_code (code prog)
                          (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.
            - move=> [<-] Hentry.
              exact (encode_code_is_code_prog Henc).
            - move=> Hinit Hentry.
              eapply initial_memory_no_entry in Hinit. congruence. }
        * { unfold code_vtag_other. intros w v.
            subst s1. simpl. rewrite unionmE.
            case Henc: (encode_code (code prog)
                          (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.
            - move=> [<-] Hcode. exact (encode_code_vtag_other code_tags_wf_prog Henc).
            - move=> Hinit Hcode. exfalso.
              have Hnc := initial_memory_not_code Hinit. rewrite Hnc in Hcode. discriminate. }
      + unfold general_memory_correctness.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
        * unfold memory_prefix_condition. intros c0 w v.
          inv init2. simpl.
          rewrite unionmE.
          case Henc: (encode_code (code prog')
                        (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
          -- move=> [<-] _ Hnot_code. right.
             exfalso. apply Hnot_code.
             eapply encode_code_is_code_prog' in Henc; eauto.
          -- move=> Hinit Hcolor Hnotcode.
             right.
             by rewrite -align_data_domm_12_u mem_domm Hinit.
        * unfold memory_prefix_condition'. simpl.
          { intros c0 w v Hbound Hmem Hprefix.
            subst s2. simpl in Hmem.
            move: Hmem. rewrite unionmE.
            case Henc: (encode_code (code prog')
                          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
            - move=> [<-].
              exfalso.
              have Hcode_prefix := encode_code_prefix memory_size' Henc.
              rewrite Hcode_prefix in Hprefix.
              exact (code_prefix_neq_data_prefix Hbound Hprefix).
            - move=> Hinit.
              exfalso.
              have Hpref0: andw w (mask (NC := NC)) = @component_memory_prefix mt NC (ssrint.Posz 0).
              { intros.
                eapply initial_memory_prefix_zero; eauto.
                eapply lin_size_wo_code'. }
              rewrite Hpref0 in Hprefix.
              eapply (code_prefix_neq_data_prefix Hbound) in Hprefix. auto. }
        * { unfold code_prefix_condition. intros w v.
            subst s2. simpl.
            rewrite unionmE.
            case Henc: (encode_code (code prog')
                          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
            - move=> [<-] Hcode. apply/eqP.
              exact (encode_code_prefix memory_size' Henc).
            - move=> Hinit Hcode.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
        * unfold alloc_empty. simpl.
          subst s2. simpl.
          rewrite unionmE.
          rewrite alloc_label_not_in_encode_code /=.
          -- rewrite alloc_label_not_in_initial_memory //=.
             by apply (leq_ltn_trans (leq_addr _ _) A.memory_size_lin').
          -- by apply memory_size'.
        * { unfold BNZ_correctness. intros w v.
            subst s2.
            rewrite unionmE.
            case Henc: (encode_code (code prog')
                          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ].
            - move=> [<-] Hcode.
              case Hdec: (decode_instr (vala v_code)) => [i | ] //=.
              destruct i => //=.
              + have [v' [Hv' Hcode']] := encode_code_bnz_target code_tags_wf_prog' bnz_resolved_prog' memory_size' Henc Hdec.
                exists v'. split; [| exact Hcode'].
                rewrite unionmE Hv' //.
              + have [[v' [Hv' Hcode']] | Halloc] := encode_code_jal_target code_tags_wf_prog' jal_resolved_prog' memory_size' Henc Hdec.
                * left. exists v'. split; [| exact Hcode'].
                  rewrite unionmE Hv' //.
                * right. exact Halloc.
            - move=> Hinit Hcode.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
        * { unfold end_condition. intros w v.
            subst s2.
            rewrite unionmE.
            case Henc: (encode_code (code prog')
                          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ].
            - move=> [<-] Hcode.
              have [Hhalt | [v' [Hv' Hcode']]] := encode_code_end_condition code_tags_wf_prog' code_last_halt_prog' Henc Hcode (ltn_trans memory_size' alloc_label_lt_w).
              + left. by rewrite Hhalt.
              + right. exists v'. split; [| exact Hcode'].
                rewrite unionmE Hv' //.
            - move=> Hinit Hcode.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
        * { unfold color_in_memory. simpl. intros w d.
            subst s2. simpl.
            rewrite unionmE.
            case Henc: (encode_code (code prog')
                          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
            - move=> [<-].
              eapply encode_code_color_prog'; eauto.
            - move=> Hinit.
              eapply initial_memory_color in Hinit; eauto.
              rewrite domm_buffers_p' domm_buffers_c' in Hinit.
              eauto. }
        * { unfold entry_is_code. intros w d e.
            subst s2. simpl.
            rewrite unionmE.
            case Henc: (encode_code (code prog')
                          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
            - move=> [<-] Hentry.
              exact (encode_code_is_code_prog' Henc).
            - move=> Hinit Hentry.
              eapply initial_memory_no_entry in Hinit. congruence. }
        * { unfold code_vtag_other. intros w v.
            subst s2. simpl. rewrite unionmE.
            case Henc: (encode_code (code prog')
                          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
            - move=> [<-] Hcode. exact (encode_code_vtag_other code_tags_wf_prog' Henc).
            - move=> Hinit Hcode. exfalso.
              have Hnc := initial_memory_not_code Hinit. rewrite Hnc in Hcode. discriminate. }
      + (* general_memory_correctness (mem s3) *)
        unfold general_memory_correctness.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
        * unfold memory_prefix_condition. intros c0 w v.
          inv init3. simpl.
          rewrite unionmE.
          case Henc: (encode_code (code prog'')
                        (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
          -- move=> [<-] _ Hnot_code.
             exfalso. apply Hnot_code.
             eapply encode_code_is_code_prog'' in Henc; eauto.
          -- move=> Hinit Hcolor Hnotcode.
             right.
             by rewrite align_data_domm_left_u mem_domm Hinit.
        * unfold memory_prefix_condition'. simpl.
          { intros c0 w v Hbound Hmem Hprefix.
            subst s3. simpl in Hmem.
            move: Hmem. rewrite unionmE.
            case Henc: (encode_code (code prog'')
                          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
            - move=> [<-].
              exfalso.
              have Hcode_prefix := encode_code_prefix memory_size'' Henc.
              rewrite Hcode_prefix in Hprefix.
              exact (code_prefix_neq_data_prefix Hbound Hprefix).
            - move=> Hinit.
              exfalso.
              have Hpref0: andw w (mask (NC := NC)) = @component_memory_prefix mt NC (ssrint.Posz 0).
              { intros.
                eapply initial_memory_prefix_zero; eauto.
                eapply lin_size_wo_code''. }
              rewrite Hpref0 in Hprefix.
              eapply (code_prefix_neq_data_prefix Hbound) in Hprefix. auto. }
        * { unfold code_prefix_condition. intros w v.
            subst s3. simpl.
            rewrite unionmE.
            case Henc: (encode_code (code prog'')
                          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
            - move=> [<-] Hcode. apply/eqP.
              exact (encode_code_prefix memory_size'' Henc).
            - move=> Hinit Hcode.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
        * unfold alloc_empty. simpl.
          subst s3. simpl.
          rewrite unionmE.
          rewrite alloc_label_not_in_encode_code /=.
          -- rewrite alloc_label_not_in_initial_memory //=.
             by apply (leq_ltn_trans (leq_addr _ _) A.memory_size_lin'').
          -- by apply memory_size''.
        * { unfold BNZ_correctness. intros w v.
            subst s3.
            rewrite unionmE.
            case Henc: (encode_code (code prog'')
                          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ].
            - move=> [<-] Hcode.
              case Hdec: (decode_instr (vala v_code)) => [i | ] //=.
              destruct i => //=.
              + have [v' [Hv' Hcode']] := encode_code_bnz_target code_tags_wf_prog'' bnz_resolved_prog'' memory_size'' Henc Hdec.
                exists v'. split; [| exact Hcode'].
                rewrite unionmE Hv' //.
              + have [[v' [Hv' Hcode']] | Halloc] := encode_code_jal_target code_tags_wf_prog'' jal_resolved_prog'' memory_size'' Henc Hdec.
                ** left. exists v'. split; [| exact Hcode'].
                   rewrite unionmE Hv' //.
                ** right. exact Halloc.
            - move=> Hinit Hcode.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
        * { unfold end_condition. intros w v.
            subst s3.
            rewrite unionmE.
            case Henc: (encode_code (code prog'')
                          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ].
            - move=> [<-] Hcode.
              have [Hhalt | [v' [Hv' Hcode']]] := encode_code_end_condition code_tags_wf_prog'' code_last_halt_prog'' Henc Hcode (ltn_trans memory_size'' alloc_label_lt_w).
              + left. by rewrite Hhalt.
              + right. exists v'. split; [| exact Hcode'].
                rewrite unionmE Hv' //.
            - move=> Hinit Hcode.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
        * { unfold color_in_memory. simpl. intros w d.
            subst s3. simpl.
            rewrite unionmE.
            case Henc: (encode_code (code prog'')
                          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
            - move=> [<-].
              eapply encode_code_color_prog''; eauto.
            - move=> Hinit.
              eapply initial_memory_color in Hinit; eauto.
              rewrite domm_buffers_p domm_buffers_c' in Hinit.
              eauto. }
        * { unfold entry_is_code. intros w d e.
            subst s3. simpl.
            rewrite unionmE.
            case Henc: (encode_code (code prog'')
                          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
            - move=> [<-] Hentry.
              exact (encode_code_is_code_prog'' Henc).
            - move=> Hinit Hentry.
              eapply initial_memory_no_entry in Hinit. congruence. }
        * { unfold code_vtag_other. intros w v.
            subst s3. simpl. rewrite unionmE.
            case Henc: (encode_code (code prog'')
                          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
            - move=> [<-] Hcode. exact (encode_code_vtag_other code_tags_wf_prog'' Henc).
            - move=> Hinit Hcode. exfalso.
              have Hnc := initial_memory_not_code Hinit. rewrite Hnc in Hcode. discriminate. }
      + unfold capability_correctness.
        move=> v n p1.
        case: p1 => //=.
        * intros r Hr. exfalso.
          inv init1. simpl in Hr. move: Hr.
          rewrite /reg0. rewrite !setmE.
          repeat (case: ifP => /=); try congruence.
          intros. now simpl in Hr.
        * intros w Hw. exfalso.
          { destruct Hw as [t [Hmem Hvtag]].
            subst s1. simpl in Hmem.
            move: Hmem. rewrite unionmE.
            case Henc: (encode_code (code prog)
                          (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.
            - move=> [Heq].
              eapply (encode_code_vtag_not_ret code_tags_wf_prog). subst. eauto. subst. eauto.
            - move=> Hinit.
              eapply initial_memory_vtag_other in Hinit. inv Hinit.
              congruence. }
      + unfold capability_correctness.
        move=> v n p1.
        case: p1 => //=.
        * intros r Hr. exfalso.
          inv init2. simpl in Hr. move: Hr.
          rewrite /reg0. rewrite !setmE.
          repeat (case: ifP => /=); try congruence.
          intros. now simpl in Hr.
        * intros w Hw. exfalso.
          { destruct Hw as [t [Hmem Hvtag]].
            subst s2. simpl in Hmem.
            move: Hmem. rewrite unionmE.
            case Henc: (encode_code (code prog')
                          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
            - move=> [Heq].
              eapply (encode_code_vtag_not_ret code_tags_wf_prog'). subst. eauto. subst. eauto.
            - move=> Hinit.
              eapply initial_memory_vtag_other in Hinit. inv Hinit.
              congruence. }
      + unfold capability_correctness.
        move=> v n p1.
        case: p1 => //=.
        * intros r Hr. exfalso.
          inv init3. simpl in Hr. move: Hr.
          rewrite /reg0. rewrite !setmE.
          repeat (case: ifP => /=); try congruence.
          intros. now simpl in Hr.
        * intros w Hw. exfalso.
          { destruct Hw as [t [Hmem Hvtag]].
            subst s3. simpl in Hmem.
            move: Hmem. rewrite unionmE.
            case Henc: (encode_code (code prog'')
                          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
            - move=> [Heq].
              eapply (encode_code_vtag_not_ret code_tags_wf_prog''). subst. eauto. subst. eauto.
            - move=> Hinit.
              eapply initial_memory_vtag_other in Hinit. inv Hinit.
              congruence. }
      + unfold combined_codes.
        { intros w v t off c Hrel Hoff Hcode Hcolor. split.
          - intros Hmem1.
            subst s1 s3. simpl in *.
            move: Hmem1. rewrite unionmE.
            case Henc1: (encode_code (code prog)
                           (size (initial_memory (prog_buffers prog))) w) => [v1 | ] /=.
            + move=> [] ?; subst.
              (* rewrite Henc1. -- leftover; case/subst already consumed this subterm *)
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
      + (* running comp = Component.main is valid: p has a main procedure (Heqmain ⇒ main ∈ ip). *)
        by apply/orP; left; apply (wfprog_main_existence Hwfp); symmetry; exact Heqmain.
      + exact: (proj1 (initial_pc_code_color init1 init2)).
      + exact: (proj2 (initial_pc_code_color init1 init2)).
    - constructor; eauto.
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
      + (* color_of s1 = color_of s3 *)
        subst s1 s3. simpl. reflexivity.
      + (* side_of (color_of s1) = Left *)
        subst s1. simpl. unfold side_of.
        have Hmain: Component.main \in domm ip.
        { apply (wfprog_main_existence Hwfp). symmetry. exact Heqmain. }
        by rewrite Hmain.
      + (* memory_address_correctness Left s1 *)
        unfold memory_address_correctness. intros v0 w Hrel Hmem.
        subst s1. simpl in Hmem. unfold address_correctness.
        move: Hmem. rewrite unionmE.
        case Henc: (encode_code (code prog)
          (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.
        * move=> [<-]. rewrite (encode_code_vtag_other_prog Henc). exact I.
        * move=> Hinit. rewrite (initial_memory_vtag_other Hinit). exact I.
      + (* memory_address_correctness Left s3 *)
        unfold memory_address_correctness. intros v0 w Hrel Hmem.
        subst s3. simpl in Hmem. unfold address_correctness.
        move: Hmem. rewrite unionmE.
        case Henc: (encode_code (code prog'')
          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
        * move=> [<-]. rewrite (encode_code_vtag_other_prog'' Henc). exact I.
        * move=> Hinit. rewrite (initial_memory_vtag_other Hinit). exact I.
      + (* entry_points_offset Left (mem s1) (mem s3) *)
        unfold entry_points_offset. intros c w w' d d' proc l l'.
        intros Hrel Hmem1 Hmem3 Hcode1 Hcode3 Hcolor1 Hcolor3 Hentry1 Hentry3.
        subst s1 s3. simpl in *.
        (* d and d' are code entries with matching entry points for component c ∈ domm ip *)
        (* Both come from encode_code (code prog) / encode_code (code prog'') *)
        (* Since Left-relevant code comes from shared code p, the entries are at *)
        (* offset-related positions: w' = addw w (as_word (offset1 c)) *)
        (* Use encode_code_nth_inv on both to get positions, then relate via offset *)
        exact: (entry_points_offset_init Hrel Hmem1 Hmem3 Hcode1 Hcode3 Hcolor1 Hcolor3 Hentry1 Hentry3).
      + (* register_address_correctness Left s1 *)
        subst s1. apply: register_address_correctness_reg0; exact: erefl.
      + (* register_address_correctness Left s3 *)
        subst s3. apply: register_address_correctness_reg0; exact: erefl.
      + (* memory_match Left [] s1 s3 *)
        unfold memory_match. intros w d Hnotcode Hrel.
        subst s1 s3. simpl in *.
        (* For Left-relevant non-code data: data matches between s1 and s3 *)
        (* Non-code data comes from initial_memory. *)
        (* For Left components (domm ip), prog and prog'' share prog_buffers p, *)
        (* so initial_memory values for Left components are identical. *)
        (* The data_match' for identical values with vtag = Other is trivial. *)
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
                  exact: (init_data_left_13 Hrel Hinit). } }
      + (* registers_match Left [] s1 s3 *)
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
    - (* weak_equiv Right [] s2 s3 *)
      constructor.
      + (* color_of s2 = color_of s3 *)
        subst s2 s3. simpl. reflexivity.
      + (* side_of (color_of s2) = other_side Right = Left *)
        subst s2. simpl. unfold side_of.
        have Hmain: Component.main \in domm ip.
        { apply (wfprog_main_existence Hwfp). symmetry. exact Heqmain. }
        by rewrite Hmain.
      + (* memory_address_correctness Right s2 *)
        unfold memory_address_correctness. intros v0 w Hrel Hmem.
        subst s2. simpl in Hmem. unfold address_correctness.
        move: Hmem. rewrite unionmE.
        case Henc: (encode_code (code prog')
          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
        * move=> [<-]. rewrite (encode_code_vtag_other_prog' Henc). exact I.
        * move=> Hinit. rewrite (initial_memory_vtag_other Hinit). exact I.
      + (* memory_address_correctness Right s3 *)
        unfold memory_address_correctness. intros v0 w Hrel Hmem.
        subst s3. simpl in Hmem. unfold address_correctness.
        move: Hmem. rewrite unionmE.
        case Henc: (encode_code (code prog'')
          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
        * move=> [<-]. rewrite (encode_code_vtag_other_prog'' Henc). exact I.
        * move=> Hinit. rewrite (initial_memory_vtag_other Hinit). exact I.
      + (* entry_points_offset Right (mem s2) (mem s3) *)
        (* entry_points_offset Right (mem s2) (mem s3) — same structure as Left *)
        unfold entry_points_offset. intros c w w' d d' proc l l'.
        intros Hrel Hmem2 Hmem3 Hcode2 Hcode3 Hcolor2 Hcolor3 Hentry2 Hentry3.
        subst s2 s3. simpl in *.
        exact: (entry_points_offset_init' Hrel Hmem2 Hmem3 Hcode2 Hcode3 Hcolor2 Hcolor3 Hentry2 Hentry3).
      + (* memory_match Right [] s2 s3 *)
        unfold memory_match. intros w d Hnotcode Hrel.
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
                  exact: (init_data_right_23 Hrel Hinit). } }
    - (* common_equiv for match_states_right — same initial states, same proof *)
      eapply common_equiv_def; eauto.  (* was 'try done': done hangs evaluating big memory goals *)
      + unfold initial_state in init1. simpl in init1. destruct s1. inv init1. simpl. done.
      + unfold initial_state in init2. simpl in init2. destruct s2. inv init2. simpl. done.
      + unfold initial_state in init3. simpl in init3. destruct s3. inv init3. simpl. done.
      + rewrite init3. simpl. econstructor.
      + inv init1. exact: register_domm_reg0.
      + inv init2. exact: register_domm_reg0.
      + inv init3. exact: register_domm_reg0.
      + (* general_memory_correctness s1 — same as Left case *)
        unfold general_memory_correctness.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
        * unfold memory_prefix_condition. intros c w v.
          inv init1. simpl.
          rewrite unionmE.
          case Henc: (encode_code (code prog)
                        (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.
          -- move=> [<-] _ Hnot_code. right.
             exfalso. apply Hnot_code.
             eapply encode_code_is_code_prog in Henc; eauto.
          -- move=> Hinit _ _.
             right. by rewrite mem_domm Hinit.
        * unfold memory_prefix_condition'. simpl.
          { intros c0 w v Hbound Hmem Hprefix.
            subst s1. simpl in Hmem.
            move: Hmem. rewrite unionmE.
            case Henc: (encode_code (code prog)
                          (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.
            - move=> [<-].
              exfalso.
              have Hcode_prefix := encode_code_prefix memory_size Henc.
              rewrite Hcode_prefix in Hprefix.
              exact (code_prefix_neq_data_prefix Hbound Hprefix).
            - move=> Hinit.
              exfalso.
              have Hpref0: andw w (mask (NC := NC)) = @component_memory_prefix mt NC (ssrint.Posz 0).
              { intros.
                eapply initial_memory_prefix_zero; eauto.
                eapply lin_size_wo_code. }
              rewrite Hpref0 in Hprefix.
              eapply (code_prefix_neq_data_prefix Hbound) in Hprefix. auto. }
        * { unfold code_prefix_condition. intros w v.
            subst s1. simpl.
            rewrite unionmE.
            case Henc: (encode_code (code prog)
                          (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.
            - move=> [<-] Hcode. apply/eqP.
              exact (encode_code_prefix memory_size Henc).
            - move=> Hinit Hcode.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
        * unfold alloc_empty. simpl.
          subst s1. simpl.
          rewrite unionmE.
          rewrite alloc_label_not_in_encode_code /=.
          -- rewrite alloc_label_not_in_initial_memory //=.
             by apply (leq_ltn_trans (leq_addr _ _) A.memory_size_lin).
          -- by apply memory_size.
        * { unfold BNZ_correctness. intros w v.
            subst s1.
            rewrite unionmE.
            case Henc: (encode_code (code prog)
                          (size (initial_memory (prog_buffers prog))) w) => [v_code | ].
            - move=> [<-] Hcode.
              case Hdec: (decode_instr (vala v_code)) => [i | ] //=.
              destruct i => //=.
              + have [v' [Hv' Hcode']] := encode_code_bnz_target code_tags_wf_prog bnz_resolved_prog memory_size Henc Hdec.
                exists v'. split; [| exact Hcode'].
                rewrite unionmE Hv' //.
              + have [[v' [Hv' Hcode']] | Halloc] := encode_code_jal_target code_tags_wf_prog jal_resolved_prog memory_size Henc Hdec.
                * left. exists v'. split; [| exact Hcode'].
                  rewrite unionmE Hv' //.
                * right. exact Halloc.
            - move=> Hinit Hcode.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
        * { unfold end_condition. intros w v.
            subst s1.
            rewrite unionmE.
            case Henc: (encode_code (code prog)
                          (size (initial_memory (prog_buffers prog))) w) => [v_code | ].
            - move=> [<-] Hcode.
              have [Hhalt | [v' [Hv' Hcode']]] := encode_code_end_condition code_tags_wf_prog code_last_halt_prog Henc Hcode (ltn_trans memory_size alloc_label_lt_w).
              + left. by rewrite Hhalt.
              + right. exists v'. split; [| exact Hcode'].
                rewrite unionmE Hv' //.
            - move=> Hinit Hcode.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
        * { unfold color_in_memory. simpl. intros w d.
            subst s1. simpl.
            rewrite unionmE.
            case Henc: (encode_code (code prog)
                          (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.
            - move=> [<-].
              eapply encode_code_color_prog; eauto.
            - move=> Hinit.
              eapply initial_memory_color in Hinit; eauto.
              rewrite domm_buffers_p domm_buffers_c in Hinit.
              eauto. }
        * { unfold entry_is_code. intros w d e.
            subst s1. simpl.
            rewrite unionmE.
            case Henc: (encode_code (code prog)
                          (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.
            - move=> [<-] Hentry.
              exact (encode_code_is_code_prog Henc).
            - move=> Hinit Hentry.
              eapply initial_memory_no_entry in Hinit. congruence. }
        * { unfold code_vtag_other. intros w v.
            subst s1. simpl. rewrite unionmE.
            case Henc: (encode_code (code prog)
                          (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.
            - move=> [<-] Hcode. exact (encode_code_vtag_other code_tags_wf_prog Henc).
            - move=> Hinit Hcode. exfalso.
              have Hnc := initial_memory_not_code Hinit. rewrite Hnc in Hcode. discriminate. }
      + (* general_memory_correctness s2 — same as Left case *)
        unfold general_memory_correctness.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
        * unfold memory_prefix_condition. intros c0 w v.
          inv init2. simpl.
          rewrite unionmE.
          case Henc: (encode_code (code prog')
                        (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
          -- move=> [<-] _ Hnot_code. right.
             exfalso. apply Hnot_code.
             eapply encode_code_is_code_prog' in Henc; eauto.
          -- move=> Hinit Hcolor Hnotcode.
             right.
             by rewrite -align_data_domm_12_u mem_domm Hinit.
        * unfold memory_prefix_condition'. simpl.
          { intros c0 w v Hbound Hmem Hprefix.
            subst s2. simpl in Hmem.
            move: Hmem. rewrite unionmE.
            case Henc: (encode_code (code prog')
                          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
            - move=> [<-].
              exfalso.
              have Hcode_prefix := encode_code_prefix memory_size' Henc.
              rewrite Hcode_prefix in Hprefix.
              exact (code_prefix_neq_data_prefix Hbound Hprefix).
            - move=> Hinit.
              exfalso.
              have Hpref0: andw w (mask (NC := NC)) = @component_memory_prefix mt NC (ssrint.Posz 0).
              { intros.
                eapply initial_memory_prefix_zero; eauto.
                eapply lin_size_wo_code'. }
              rewrite Hpref0 in Hprefix.
              eapply (code_prefix_neq_data_prefix Hbound) in Hprefix. auto. }
        * { unfold code_prefix_condition. intros w v.
            subst s2. simpl.
            rewrite unionmE.
            case Henc: (encode_code (code prog')
                          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
            - move=> [<-] Hcode. apply/eqP.
              exact (encode_code_prefix memory_size' Henc).
            - move=> Hinit Hcode.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
        * unfold alloc_empty. simpl.
          subst s2. simpl.
          rewrite unionmE.
          rewrite alloc_label_not_in_encode_code /=.
          -- rewrite alloc_label_not_in_initial_memory //=.
             by apply (leq_ltn_trans (leq_addr _ _) A.memory_size_lin').
          -- by apply memory_size'.
        * { unfold BNZ_correctness. intros w v.
            subst s2.
            rewrite unionmE.
            case Henc: (encode_code (code prog')
                          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ].
            - move=> [<-] Hcode.
              case Hdec: (decode_instr (vala v_code)) => [i | ] //=.
              destruct i => //=.
              + have [v' [Hv' Hcode']] := encode_code_bnz_target code_tags_wf_prog' bnz_resolved_prog' memory_size' Henc Hdec.
                exists v'. split; [| exact Hcode'].
                rewrite unionmE Hv' //.
              + have [[v' [Hv' Hcode']] | Halloc] := encode_code_jal_target code_tags_wf_prog' jal_resolved_prog' memory_size' Henc Hdec.
                * left. exists v'. split; [| exact Hcode'].
                  rewrite unionmE Hv' //.
                * right. exact Halloc.
            - move=> Hinit Hcode.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
        * { unfold end_condition. intros w v.
            subst s2.
            rewrite unionmE.
            case Henc: (encode_code (code prog')
                          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ].
            - move=> [<-] Hcode.
              have [Hhalt | [v' [Hv' Hcode']]] := encode_code_end_condition code_tags_wf_prog' code_last_halt_prog' Henc Hcode (ltn_trans memory_size' alloc_label_lt_w).
              + left. by rewrite Hhalt.
              + right. exists v'. split; [| exact Hcode'].
                rewrite unionmE Hv' //.
            - move=> Hinit Hcode.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
        * { unfold color_in_memory. simpl. intros w d.
            subst s2. simpl.
            rewrite unionmE.
            case Henc: (encode_code (code prog')
                          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
            - move=> [<-].
              eapply encode_code_color_prog'; eauto.
            - move=> Hinit.
              eapply initial_memory_color in Hinit; eauto.
              rewrite domm_buffers_p' domm_buffers_c' in Hinit.
              eauto. }
        * { unfold entry_is_code. intros w d e.
            subst s2. simpl.
            rewrite unionmE.
            case Henc: (encode_code (code prog')
                          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
            - move=> [<-] Hentry.
              exact (encode_code_is_code_prog' Henc).
            - move=> Hinit Hentry.
              eapply initial_memory_no_entry in Hinit. congruence. }
        * { unfold code_vtag_other. intros w v.
            subst s2. simpl. rewrite unionmE.
            case Henc: (encode_code (code prog')
                          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
            - move=> [<-] Hcode. exact (encode_code_vtag_other code_tags_wf_prog' Henc).
            - move=> Hinit Hcode. exfalso.
              have Hnc := initial_memory_not_code Hinit. rewrite Hnc in Hcode. discriminate. }
      + (* general_memory_correctness s3 — same as Left case *)
        unfold general_memory_correctness.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
        * unfold memory_prefix_condition. intros c0 w v.
          inv init3. simpl.
          rewrite unionmE.
          case Henc: (encode_code (code prog'')
                        (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
          -- move=> [<-] _ Hnot_code.
             exfalso. apply Hnot_code.
             eapply encode_code_is_code_prog'' in Henc; eauto.
          -- move=> Hinit Hcolor Hnotcode.
             right.
             by rewrite align_data_domm_left_u mem_domm Hinit.
        * unfold memory_prefix_condition'. simpl.
          { intros c0 w v Hbound Hmem Hprefix.
            subst s3. simpl in Hmem.
            move: Hmem. rewrite unionmE.
            case Henc: (encode_code (code prog'')
                          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
            - move=> [<-].
              exfalso.
              have Hcode_prefix := encode_code_prefix memory_size'' Henc.
              rewrite Hcode_prefix in Hprefix.
              exact (code_prefix_neq_data_prefix Hbound Hprefix).
            - move=> Hinit.
              exfalso.
              have Hpref0: andw w (mask (NC := NC)) = @component_memory_prefix mt NC (ssrint.Posz 0).
              { intros.
                eapply initial_memory_prefix_zero; eauto.
                eapply lin_size_wo_code''. }
              rewrite Hpref0 in Hprefix.
              eapply (code_prefix_neq_data_prefix Hbound) in Hprefix. auto. }
        * { unfold code_prefix_condition. intros w v.
            subst s3. simpl.
            rewrite unionmE.
            case Henc: (encode_code (code prog'')
                          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
            - move=> [<-] Hcode. apply/eqP.
              exact (encode_code_prefix memory_size'' Henc).
            - move=> Hinit Hcode.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
        * unfold alloc_empty. simpl.
          subst s3. simpl.
          rewrite unionmE.
          rewrite alloc_label_not_in_encode_code /=.
          -- rewrite alloc_label_not_in_initial_memory //=.
             by apply (leq_ltn_trans (leq_addr _ _) A.memory_size_lin'').
          -- by apply memory_size''.
        * { unfold BNZ_correctness. intros w v.
            subst s3.
            rewrite unionmE.
            case Henc: (encode_code (code prog'')
                          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ].
            - move=> [<-] Hcode.
              case Hdec: (decode_instr (vala v_code)) => [i | ] //=.
              destruct i => //=.
              + have [v' [Hv' Hcode']] := encode_code_bnz_target code_tags_wf_prog'' bnz_resolved_prog'' memory_size'' Henc Hdec.
                exists v'. split; [| exact Hcode'].
                rewrite unionmE Hv' //.
              + have [[v' [Hv' Hcode']] | Halloc] := encode_code_jal_target code_tags_wf_prog'' jal_resolved_prog'' memory_size'' Henc Hdec.
                ** left. exists v'. split; [| exact Hcode'].
                   rewrite unionmE Hv' //.
                ** right. exact Halloc.
            - move=> Hinit Hcode.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
        * { unfold end_condition. intros w v.
            subst s3.
            rewrite unionmE.
            case Henc: (encode_code (code prog'')
                          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ].
            - move=> [<-] Hcode.
              have [Hhalt | [v' [Hv' Hcode']]] := encode_code_end_condition code_tags_wf_prog'' code_last_halt_prog'' Henc Hcode (ltn_trans memory_size'' alloc_label_lt_w).
              + left. by rewrite Hhalt.
              + right. exists v'. split; [| exact Hcode'].
                rewrite unionmE Hv' //.
            - move=> Hinit Hcode.
              exfalso. have Hnc := initial_memory_not_code Hinit.
              rewrite Hnc in Hcode. discriminate. }
        * { unfold color_in_memory. simpl. intros w d.
            subst s3. simpl.
            rewrite unionmE.
            case Henc: (encode_code (code prog'')
                          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
            - move=> [<-].
              eapply encode_code_color_prog''; eauto.
            - move=> Hinit.
              eapply initial_memory_color in Hinit; eauto.
              rewrite domm_buffers_p domm_buffers_c' in Hinit.
              eauto. }
        * { unfold entry_is_code. intros w d e.
            subst s3. simpl.
            rewrite unionmE.
            case Henc: (encode_code (code prog'')
                          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
            - move=> [<-] Hentry.
              exact (encode_code_is_code_prog'' Henc).
            - move=> Hinit Hentry.
              eapply initial_memory_no_entry in Hinit. congruence. }
        * { unfold code_vtag_other. intros w v.
            subst s3. simpl. rewrite unionmE.
            case Henc: (encode_code (code prog'')
                          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
            - move=> [<-] Hcode. exact (encode_code_vtag_other code_tags_wf_prog'' Henc).
            - move=> Hinit Hcode. exfalso.
              have Hnc := initial_memory_not_code Hinit. rewrite Hnc in Hcode. discriminate. }
      + (* capability_correctness s1 — same as Left case *)
        unfold capability_correctness.
        move=> v n p1.
        case: p1 => //=.
        * intros r Hr. exfalso.
          inv init1. simpl in Hr. move: Hr.
          rewrite /reg0. rewrite !setmE.
          repeat (case: ifP => /=); try congruence.
          intros. now simpl in Hr.
        * intros w Hw. exfalso.
          { destruct Hw as [t [Hmem Hvtag]].
            subst s1. simpl in Hmem.
            move: Hmem. rewrite unionmE.
            case Henc: (encode_code (code prog)
                          (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.
            - move=> [Heq].
              eapply (encode_code_vtag_not_ret code_tags_wf_prog). subst. eauto. subst. eauto.
            - move=> Hinit.
              eapply initial_memory_vtag_other in Hinit. inv Hinit.
              congruence. }
      + (* capability_correctness s2 *)
        unfold capability_correctness.
        move=> v n p1.
        case: p1 => //=.
        * intros r Hr. exfalso.
          inv init2. simpl in Hr. move: Hr.
          rewrite /reg0. rewrite !setmE.
          repeat (case: ifP => /=); try congruence.
          intros. now simpl in Hr.
        * intros w Hw. exfalso.
          { destruct Hw as [t [Hmem Hvtag]].
            subst s2. simpl in Hmem.
            move: Hmem. rewrite unionmE.
            case Henc: (encode_code (code prog')
                          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
            - move=> [Heq].
              eapply (encode_code_vtag_not_ret code_tags_wf_prog'). subst. eauto. subst. eauto.
            - move=> Hinit.
              eapply initial_memory_vtag_other in Hinit. inv Hinit.
              congruence. }
      + (* capability_correctness s3 *)
        unfold capability_correctness.
        move=> v n p1.
        case: p1 => //=.
        * intros r Hr. exfalso.
          inv init3. simpl in Hr. move: Hr.
          rewrite /reg0. rewrite !setmE.
          repeat (case: ifP => /=); try congruence.
          intros. now simpl in Hr.
        * intros w Hw. exfalso.
          { destruct Hw as [t [Hmem Hvtag]].
            subst s3. simpl in Hmem.
            move: Hmem. rewrite unionmE.
            case Henc: (encode_code (code prog'')
                          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
            - move=> [Heq].
              eapply (encode_code_vtag_not_ret code_tags_wf_prog''). subst. eauto. subst. eauto.
            - move=> Hinit.
              eapply initial_memory_vtag_other in Hinit. inv Hinit.
              congruence. }
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
      + (* running comp = Component.main valid: p has no main (Heqmain) ⇒ c does ⇒ main ∈ ic. *)
        apply/orP; right.
        have Hpm := cprog_main_existence Hprog_is_closed.
        simpl in Hpm. rewrite -Heqmain /= in Hpm.
        apply (wfprog_main_existence Hwfc). exact Hpm.
      + exact: (proj1 (initial_pc_code_color init1 init2)) || exact: (proj2 (initial_pc_code_color init1 init2)).
      + exact: (proj1 (initial_pc_code_color init1 init2)) || exact: (proj2 (initial_pc_code_color init1 init2)).
    - (* weak_equiv Left for match_states_right *)
      constructor.
      + subst s1 s3. simpl. reflexivity.
      + (* side_of (color_of s1) = other_side Left = Right *)
        subst s1. simpl. unfold side_of.
        case Hmain: (Component.main \in domm ip).
        * (* Component.main ∈ domm ip, but prog_main p = false, contradiction *)
          exfalso.
          pose proof wfprog_main_existence Hwfp.
          rewrite -Heqmain in H. apply H in Hmain. congruence.
        * done.
      + (* memory_address_correctness Left s1 *)
        unfold memory_address_correctness. intros v0 w Hrel Hmem.
        subst s1. simpl in Hmem. unfold address_correctness.
        move: Hmem. rewrite unionmE.
        case Henc: (encode_code (code prog)
          (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.
        * move=> [<-]. rewrite (encode_code_vtag_other_prog Henc). exact I.
        * move=> Hinit. rewrite (initial_memory_vtag_other Hinit). exact I.
      + (* memory_address_correctness Left s3 *)
        unfold memory_address_correctness. intros v0 w Hrel Hmem.
        subst s3. simpl in Hmem. unfold address_correctness.
        move: Hmem. rewrite unionmE.
        case Henc: (encode_code (code prog'')
          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
        * move=> [<-]. rewrite (encode_code_vtag_other_prog'' Henc). exact I.
        * move=> Hinit. rewrite (initial_memory_vtag_other Hinit). exact I.
      + (* entry_points_offset Left (mem s1) (mem s3) *)
        unfold entry_points_offset. intros c w w' d d' proc l l'.
        intros Hrel Hmem1 Hmem3 Hcode1 Hcode3 Hcolor1 Hcolor3 Hentry1 Hentry3.
        subst s1 s3. simpl in *.
        exact: (entry_points_offset_init Hrel Hmem1 Hmem3 Hcode1 Hcode3 Hcolor1 Hcolor3 Hentry1 Hentry3).
      + (* memory_match Left [] s1 s3 *)
        unfold memory_match. intros w d Hnotcode Hrel.
        subst s1 s3. simpl in *.
        split.
        * { intros Hmem3. move: Hmem3. rewrite unionmE.
            case Henc: (encode_code (code prog'')
              (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
            - move=> [] ?; subst v_code. exfalso.
              apply Hnotcode. exact (encode_code_is_code_prog'' Henc).
            - move=> Hinit.
              { exists d. split.
                - unfold data_match'. destruct d as [vv tt]. simpl.
                  split; [reflexivity |]. split; [reflexivity |].
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
        * { intros Hmem1. move: Hmem1. rewrite unionmE.
            case Henc: (encode_code (code prog)
              (size (initial_memory (prog_buffers prog))) w) => [v_code | ] /=.
            - move=> [] ?; subst v_code. exfalso.
              apply Hnotcode. exact (encode_code_is_code_prog Henc).
            - move=> Hinit.
              { exists d. split.
                - unfold data_match'. destruct d as [vv tt]. simpl.
                  split; [reflexivity |]. split; [reflexivity |].
                  have Hvtag := initial_memory_vtag_other Hinit.
                  rewrite Hvtag. reflexivity.
                - rewrite unionmE.
                  have Henc_none: encode_code (code p ++ code c')
                    (size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c')))) w = None.
                  { eapply encode_code_initial_memory_disjoint;
      first by [exact A.memory_size_lin | exact A.memory_size_lin' | exact A.memory_size_lin''].
                    exact: (init_data_left_13 Hrel Hinit). }
                  rewrite Henc_none /=.
                  exact: (init_data_left_13 Hrel Hinit). } }
    - (* strong_equiv Right for match_states_right *)
      constructor; eauto.
      + have Hmain_ic : Component.main \in domm ic.
        { have Hpm := cprog_main_existence Hprog_is_closed.
          simpl in Hpm. rewrite -Heqmain /= in Hpm.
          apply (wfprog_main_existence Hwfc). exact Hpm. }
        subst s2 s3. exact: (same_pc_right_init Hmain_ic).
      + subst s2 s3. simpl. reflexivity.
      + (* side_of (color_of s2) = Right *)
        subst s2. simpl. unfold side_of.
        case Hmain: (Component.main \in domm ip).
        * exfalso.
          pose proof wfprog_main_existence Hwfp.
          rewrite -Heqmain in H. apply H in Hmain. congruence.
        * done.
      + (* memory_address_correctness Right s2 *)
        unfold memory_address_correctness. intros v0 w Hrel Hmem.
        subst s2. simpl in Hmem. unfold address_correctness.
        move: Hmem. rewrite unionmE.
        case Henc: (encode_code (code prog')
          (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
        * move=> [<-]. rewrite (encode_code_vtag_other_prog' Henc). exact I.
        * move=> Hinit. rewrite (initial_memory_vtag_other Hinit). exact I.
      + (* memory_address_correctness Right s3 *)
        unfold memory_address_correctness. intros v0 w Hrel Hmem.
        subst s3. simpl in Hmem. unfold address_correctness.
        move: Hmem. rewrite unionmE.
        case Henc: (encode_code (code prog'')
          (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
        * move=> [<-]. rewrite (encode_code_vtag_other_prog'' Henc). exact I.
        * move=> Hinit. rewrite (initial_memory_vtag_other Hinit). exact I.
      + (* entry_points_offset Right (mem s2) (mem s3) *)
        unfold entry_points_offset. intros c w w' d d' proc l l'.
        intros Hrel Hmem2 Hmem3 Hcode2 Hcode3 Hcolor2 Hcolor3 Hentry2 Hentry3.
        subst s2 s3. simpl in *.
        exact: (entry_points_offset_init' Hrel Hmem2 Hmem3 Hcode2 Hcode3 Hcolor2 Hcolor3 Hentry2 Hentry3).
      + (* register_address_correctness Right s2 *)
        subst s2. apply: register_address_correctness_reg0; exact: erefl.
      + (* register_address_correctness Right s3 *)
        subst s3. apply: register_address_correctness_reg0; exact: erefl.
      + (* memory_match Right [] s2 s3 *)
        unfold memory_match. intros w d Hnotcode Hrel.
        subst s2 s3. simpl in *.
        split.
        * { intros Hmem3. move: Hmem3. rewrite unionmE.
            case Henc: (encode_code (code prog'')
              (size (initial_memory (prog_buffers prog''))) w) => [v_code | ] /=.
            - move=> [] ?; subst v_code. exfalso.
              apply Hnotcode. exact (encode_code_is_code_prog'' Henc).
            - move=> Hinit.
              { exists d. split.
                - unfold data_match'. destruct d as [vv tt]. simpl.
                  split; [reflexivity |]. split; [reflexivity |].
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
        * { intros Hmem2. move: Hmem2. rewrite unionmE.
            case Henc: (encode_code (code prog')
              (size (initial_memory (prog_buffers prog'))) w) => [v_code | ] /=.
            - move=> [] ?; subst v_code. exfalso.
              apply Hnotcode. exact (encode_code_is_code_prog' Henc).
            - move=> Hinit.
              { exists d. split.
                - unfold data_match'. destruct d as [vv tt]. simpl.
                  split; [reflexivity |]. split; [reflexivity |].
                  have Hvtag := initial_memory_vtag_other Hinit.
                  rewrite Hvtag. reflexivity.
                - rewrite unionmE.
                  have Henc_none: encode_code (code p ++ code c')
                    (size (initial_memory (mt := mt) (unionm (prog_buffers p) (prog_buffers c')))) w = None.
                  { eapply encode_code_initial_memory_disjoint;
      first by [exact A.memory_size_lin | exact A.memory_size_lin' | exact A.memory_size_lin''].
                    exact: (init_data_right_23 Hrel Hinit). }
                  rewrite Henc_none /=.
                  exact: (init_data_right_23 Hrel Hinit). } }
      + (* registers_match Right [] s2 s3 *)
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

  (* Print Assumptions match_initial_states.  -- clean: no Classical/proof_irrelevance;
     only RecompositionContext params + recombination hyps + padding-alignment postulates
     + bitwise/fmap/encoding leaves. *)

End RecInit.
