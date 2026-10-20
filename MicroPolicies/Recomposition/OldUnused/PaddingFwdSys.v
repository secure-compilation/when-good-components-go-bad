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

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq fintype path.
From mathcomp Require Import zify.
From CoqUtils Require Import hseq word.
From extructures Require Import fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Coq.micromega.Lia.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.WordExtra.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Exec.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Utils.
Import DoNotation.
Import Types.

Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.Padding.
Require Import MicroPolicies.Recomposition.EncodeCode.
Require Import MicroPolicies.Recomposition.PaddingCorrect.
Require Import MicroPolicies.Recomposition.PaddingSim.
Import PaddingSim.

Section CodeShiftFwdSys.

Variables q q' : program.
Local Notation pc0 := (size (@Merged.initial_memory mt (prog_buffers q))).
Local Notation padc := ((pad_code (code q) (code q')).1).
Local Notation sizes := (pad_block_sizes (code q) (code q')).
Local Notation lpf c :=
  (fun (l d : nat) =>
     match findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) c with
     | Some m => pc0 + m | None => if l == alloc_label then l else d end).

Hypothesis word_of_nat_inj : forall a b,
    a < 2 ^ (word_size mt) -> b < 2 ^ (word_size mt) ->
    @word_of_nat (word_size mt) a = word_of_nat b -> a = b.
Hypothesis Hcount  : size (proc_split (code q)) = size (proc_split (code q')).
Hypothesis Hbound  : pc0 + size (code q) < alloc_label.
Hypothesis Hbound' : pc0 + size padc < alloc_label.
Hypothesis code_tags_wf_q    : forall w a, encode_code (code q) pc0 w = Some a -> is_code (taga a).
Hypothesis code_tags_wf_padc : forall w a, encode_code padc pc0 w = Some a -> is_code (taga a).
Hypothesis fallthrough_aligned : forall n i t,
  n.+1 < size (code q) -> nth_error (code q) n = Some (i, t) -> is_term i = false ->
  shift_pos sizes (n.+1) = (shift_pos sizes n).+1.
Hypothesis code_last_term : forall n i t,
  n.+1 = size (code q) -> nth_error (code q) n = Some (i, t) -> is_term i = true.
Hypothesis bnz_labels_resolved : forall n r l t,
  nth_error (code q) n = Some (MrBnz r l, t) ->
  exists m, findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code q) = Some m.

Variable NC : nat.

Hypothesis alloc_label_lt_NC : alloc_label < 2 ^ (word_size mt - NC).

Hypothesis code_colors_bounded : forall w a,
  encode_code (code q) pc0 w = Some a -> 1 + color (taga a) < 2 ^ NC.

Local Notation st := (@Symbolic.state mt lrc_tags unit).

Local Notation match_pad  := (@PaddingSim.match_pad q q').
Local Notation pad_valid  := (@PaddingSim.pad_valid q q').
Local Notation phia       := (@PaddingSim.phia q q').
Local Notation rel_v      := (@PaddingSim.rel_v q q').
Local Notation addr_ok    := (@PaddingSim.addr_ok q q').
Local Notation memwk      := (@PaddingSim.memwk q q').
Local Notation memwk_bwd  := (@PaddingSim.memwk_bwd q q').
Local Notation wregs      := (@PaddingSim.wregs q q').

Local Notation code_cell_q      := (PaddingSim.code_cell_q Hcount Hbound Hbound').
Local Notation phia_addr_code   := (PaddingSim.phia_addr_code Hcount Hbound Hbound').
Local Notation pc_succ_corr     := (PaddingSim.pc_succ_corr Hcount Hbound Hbound' fallthrough_aligned).
Local Notation jal_corr         := (PaddingSim.jal_corr Hcount Hbound Hbound').
Local Notation bnz_corr         := (PaddingSim.bnz_corr Hcount Hbound Hbound').
Local Notation size_code_le_padc := (PaddingSim.size_code_le_padc Hcount).
Local Notation code_cell_padc   := (PaddingSim.code_cell_padc word_of_nat_inj Hcount Hbound Hbound').
Local Notation jump_target_corr := (PaddingSim.jump_target_corr word_of_nat_inj Hcount Hbound Hbound' code_tags_wf_q).
Local Notation jump_belong_corr := (PaddingSim.jump_belong_corr word_of_nat_inj Hcount Hbound Hbound' code_tags_wf_q).
Local Notation encode_code_dom  := (PaddingSim.encode_code_dom word_of_nat_inj).
Local Notation nonterm_succ_lt  := (PaddingSim.nonterm_succ_lt code_last_term).

Local Opaque PaddingSim.rel_v.

Lemma unionm_get {T : ordType} {S : Type} (m1 m2 : {fmap T -> S}) k v :
  unionm m1 m2 k = Some v -> m1 k = Some v \/ (m1 k = None /\ m2 k = Some v).
Proof. rewrite unionmE; case: (m1 k) => [a|] /= H; [left|right]; [exact H | split; [reflexivity|exact H]]. Qed.

Lemma unionm_getL {T : ordType} {S : Type} (m1 m2 : {fmap T -> S}) k v :
  m1 k = Some v -> unionm m1 m2 k = Some v.
Proof. move=> H; rewrite unionmE H //. Qed.

Lemma alloc_block_const_value {T : ordType} {S : eqType}
      (f : nat -> T) (a : S) (k : nat) (w : T) (d : S) :
  mkfmap (mkseq (fun n => (f n, a)) k) w = Some d -> d = a.
Proof. move=> H; move/mkfmap_Some: H; rewrite /mkseq => /mapP[x _ [= _ ->]] //. Qed.

Lemma obindE A B (f : A -> option B) a : obind f (Some a) = f a.
Proof. by []. Qed.
Lemma is_jumpE : is_jump InternalJump = Some tt.
Proof. by []. Qed.
Lemma is_otherE : is_other Other = Some tt.
Proof. by []. Qed.

Lemma andw_last_component_prefix (C : Component.id) (m : {fmap mword mt -> atom (mword mt) mem_tag}) :
  andw (List.last (List.filter (fun mw => andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz C)) (domm m))
          (@component_memory_prefix mt NC (ssrint.Posz C))) (@mask mt NC)
  = @component_memory_prefix mt NC (ssrint.Posz C).
Proof.
  generalize (domm m) as fs. destruct fs as [l sorted]. simpl. clear sorted.
  induction l.
  - simpl. unfold mask, component_memory_prefix.
    replace (@andw 32) with (@andw (word_size mt)) by reflexivity.
    pose proof shlw_all_one (k := (word_size mt)) (as_word (ssrint.Posz C))
      (as_word (ssrint.Posz (word_size mt - NC))).
    rewrite <- H at 2.
    repeat (try (eapply congr2 || eapply congr1)).
    1-3,5-7: reflexivity.
    clear. remember (word_size mt) as n. clear.
    induction n; auto. simpl.
    unfold expn in *. simpl. rewrite <- IHn.
    destruct n; auto; simpl.
  - simpl. case: ifP => /eqP H.
    + simpl. match goal with |- context [List.filter ?p l] =>
        move: IHl; generalize (List.filter p l) as fl; intros fl IHl end.
      by destruct fl; [exact H | exact IHl].
    + eauto.
Qed.

Local Opaque LRC.mask LRC.component_memory_prefix.

Lemma phia_alloc_fixed : phia (word_of_nat alloc_label) = word_of_nat alloc_label.
Proof.
  rewrite /PaddingSim.phia val_word_of_nat; last exact: alloc_label_lt_word.
  congr word_of_nat. rewrite /PaddingSim.phia_nat.
  case: ifP => [Hlt|_]; first by (exfalso; move: Hbound Hlt; lia).
  case: ifP => [Hlt2|_]; first by (exfalso; move: Hbound Hlt2; lia).
  by [].
Qed.

Lemma high_not_code_l (s1 s2 : st) (w : mword mt) (a : matom) :
  match_pad s1 s2 -> alloc_label <= (val w : nat) ->
  Symbolic.mem s1 w = Some a -> is_code (taga a) = false.
Proof.
  move=> [_ [_ [_ [_ [Hc1 [_ [_ [_ _]]]]]]]] Hge Hw.
  case Eic: (is_code (taga a)) => //. exfalso.
  have Henc := Hc1 w a Hw Eic.
  have [n [Hwn [Hnlt _]]] := encode_code_nth_inv Henc.
  have Hbw : pc0 + size (code q) < 2 ^ word_size mt by exact: (ltn_trans Hbound alloc_label_lt_word).
  have Hb : n + pc0 < 2 ^ word_size mt by (move: Hnlt Hbw; lia).
  have Hvw : (val w : nat) = n + pc0 by rewrite Hwn (val_word_of_nat Hb).
  move: Hge; rewrite Hvw. move: Hnlt Hbound; lia.
Qed.

Lemma high_not_code_r (s1 s2 : st) (w : mword mt) (a : matom) :
  match_pad s1 s2 -> alloc_label <= (val w : nat) ->
  Symbolic.mem s2 w = Some a -> is_code (taga a) = false.
Proof.
  move=> [_ [_ [_ [_ [_ [_ [Hc2 [_ _]]]]]]]] Hge Hw.
  case Eic: (is_code (taga a)) => //. exfalso.
  have Henc := Hc2 w a Hw Eic.
  have [n [Hwn [Hnlt _]]] := encode_code_nth_inv Henc.
  have Hbw : pc0 + size padc < 2 ^ word_size mt by exact: (ltn_trans Hbound' alloc_label_lt_word).
  have Hb : n + pc0 < 2 ^ word_size mt by (move: Hnlt Hbw; lia).
  have Hvw : (val w : nat) = n + pc0 by rewrite Hwn (val_word_of_nat Hb).
  move: Hge; rewrite Hvw. move: Hnlt Hbound'; lia.
Qed.

Lemma NC_le_word : NC <= word_size mt.
Proof.
  have Hpos : 0 < alloc_label by rewrite /alloc_label expn_gt0.
  rewrite leqNgt; apply/negP => Hgt.
  have H0 : word_size mt - NC = 0 by lia.
  move: alloc_label_lt_NC; rewrite H0 expn0. by move: Hpos; lia.
Qed.

Lemma prefix_match_high (w : mword mt) (C : Component.id) :
  1 + C < 2 ^ NC ->
  andw w (@mask mt NC) = @component_memory_prefix mt NC (ssrint.Posz (1 + C)) ->
  alloc_label <= (val w : nat).
Proof.
  move=> HCb Hpf. rewrite leqNgt; apply/negP => Hlt.
  have Hsmall : (val w : nat) < 2 ^ (word_size mt - NC) by move: Hlt alloc_label_lt_NC; lia.
  have Hz := andw_mask_low w Hsmall.
  have Hz0 : @component_memory_prefix mt NC (ssrint.Posz (1 + C)) = @component_memory_prefix mt NC (ssrint.Posz 0).
  { rewrite -Hpf Hz. exact: (esym component_memory_prefix_zero). }
  exact: (component_memory_prefix_succ_not_zero C NC_le_word HCb Hz0).
Qed.

Lemma padc_filter_domm_eq (s1 s2 : st) (C : Component.id) :
  1 + C < 2 ^ NC -> match_pad s1 s2 ->
  List.filter (fun mw => andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz (1 + C)))
              (domm (Symbolic.mem s1))
  = List.filter (fun mw => andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz (1 + C)))
              (domm (Symbolic.mem s2)).
Proof.
  move=> HCb Hmp.
  have [_ [_ [_ [_ [_ [_ [_ [_ [Hmwk Hmwkb]]]]]]]]] := Hmp.
  set p := (fun mw => andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz (1 + C))).
  have FE : forall l : seq (mword mt), List.filter p l = [seq mw <- l | p mw]
    by elim => [|x l IH] //=; rewrite IH.
  rewrite !FE.
  apply: (irr_sorted_eq (leT := @Ord.lt _) (@Ord.lt_trans _) (@Ord.ltxx _)).
  - apply: (sorted_filter (@Ord.lt_trans _)); apply: (valP (domm (Symbolic.mem s1))).
  - apply: (sorted_filter (@Ord.lt_trans _)); apply: (valP (domm (Symbolic.mem s2))).
  - move=> w; rewrite !mem_filter.
    case Hpw: (p w) => //=.
    move: Hpw; rewrite /p => /eqP Hpw.
    have Hge := prefix_match_high HCb Hpw.
    apply/idP/idP => /dommP [d Hd]; apply/dommP.
    + have Hnc := high_not_code_l Hmp Hge Hd.
      have [v2 [Hd' _]] := Hmwk w d Hd Hnc. by exists (v2 @ (taga d)).
    + have Hnc := high_not_code_r Hmp Hge Hd.
      have [a0 [Hd' _]] := Hmwkb w d Hd Hnc. by exists a0.
Qed.

Lemma alloc_bloc_props (c : Component.id) (len : nat) (max_addr : mword mt) :
   1 + c < 2 ^ NC ->
   andw max_addr (@mask mt NC) = @component_memory_prefix mt NC (ssrint.Posz (1 + c)) ->
   andw (addw max_addr (@as_word (word_size mt) (ssrint.Posz (len + 1)))) (@mask mt NC)
     = @component_memory_prefix mt NC (ssrint.Posz (1 + c)) ->
   len + 1 <= 2 ^ (word_size mt - NC) ->
   forall w a, mkfmap (mkseq (fun n => (addw max_addr (@as_word (word_size mt) (ssrint.Posz (n + 1))),
                                        (@as_word (word_size mt) (ssrint.Posz 0)) @ (def_mem_tag c false))) len) w = Some a ->
     a = (@as_word (word_size mt) (ssrint.Posz 0)) @ (def_mem_tag c false) /\ alloc_label <= (val w : nat).
Proof.
  move=> HCb Hstart Hend Hsz w a Hbl.
  split; first exact: (alloc_block_const_value Hbl).
  move/mkfmap_Some: Hbl; rewrite /mkseq => /mapP[k Hk [= Hwk _]].
  apply: (prefix_match_high HCb). rewrite Hwk.
  apply: (@mask_range mt NC max_addr len (ssrint.Posz (1 + c)) Hsz Hstart Hend); exact: Hk.
Qed.

Local Opaque alloc_fun.
Local Opaque unionm setm mkfmap mkfmapfp.

Lemma pad_step_fwd_sys :
  forall mem0 reg pcw tpc0 extra sc (s2 s1' : st) (ev : option event),
  match_pad (@Symbolic.State mt lrc_tags unit mem0 reg (pcw @ tpc0) extra) s2 ->
  pad_valid (@Symbolic.State mt lrc_tags unit mem0 reg (pcw @ tpc0) extra) ->
  mem0 pcw = None ->
  Instance.table (NC := NC) pcw = Some sc ->
  @Symbolic.run_syscall mt ops lrc_tags Merged.transfer unit sc
     (@Symbolic.State mt lrc_tags unit mem0 reg (pcw @ tpc0) extra) = Some (s1', ev) ->
  exists s2', step_me (NC := NC) s2 s2' ev /\ match_pad s1' s2'.
Proof.
  move=> mem0 reg pcw tpc0 extra sc s2 s1' ev Hm Hvalid PC GETCALL CALL.
  have Hsem : Symbolic.sem sc = alloc_fun (NC := NC).
  { move: GETCALL; rewrite /Instance.table /Merged.table mkfmapE /=.
    case: ifP => [_ [= <-] //|_]. by move=> [=]. }
  have Hent : Symbolic.entry_tag sc = tt by case: (Symbolic.entry_tag sc).
  have Hpcw : pcw = word_of_nat alloc_label.
  { move: GETCALL; rewrite /Instance.table /Merged.table mkfmapE /=. by case: ifP => [/eqP|]. }
  have [Halloc1 Hev] : alloc_fun (NC := NC) (@Symbolic.State mt lrc_tags unit mem0 reg (pcw @ tpc0) extra) = Some s1'
                       /\ ev = None.
  { move: CALL; rewrite /run_syscall Hsem Hent /=.
    case Hevi: (Symbolic.evi _) => [i|] //=.
    rewrite /Merged.transfer /=.
    case Halloc: (alloc_fun (NC := NC) _) => [s|] //=. by move=> [= <- <-]. }
  subst ev.
  destruct tpc0 as [level ctpc].
  Local Transparent alloc_fun.
  move: Halloc1; rewrite {1}/alloc_fun /= => H1.
  case: (obind_inv H1) => ra_val [Hra1 {}H1].
  case: (obind_inv H1) => u1 [Hjmp1 {}H1].
  case: (obind_inv H1) => reta1 [Hreta1 {}H1].
  case: (obind_inv H1) => uret [Hretchk1 {}H1].
  move: Hretchk1; case: ifP => Hretc1 Hretc1'; last by [].
  case: (obind_inv H1) => sz1 [Hsz1 {}H1].
  case: (obind_inv H1) => uoth [Hoth1 {}H1].
  case: (obind_inv H1) => len1 [Hlen1 {}H1].
  case: (obind_inv H1) => ulen [Hlenchk1 {}H1].
  move: H1; case: ifP => // Hpf1 H1.
  case: (obind_inv H1) => addr1 [Haddr1 {}H1].
  case: (obind_inv H1) => regs1' [Hregs1' {}H1].
  move: H1 => [= Hs1'].
  Local Opaque alloc_fun.
  have Hmp := Hm.
  move: Hm => [Hpcv0 [Hpct [Hint [Hreg [Hc1 [Hc1' [Hc2 [Hc2' [Hmwk Hmwkb]]]]]]]]].
  have Hraj : taga ra_val = InternalJump := is_jump_invE Hjmp1.
  have Hothz : taga sz1 = Other := is_other_invE Hoth1.
  move: Hretc1 => /andP [Hretcode /eqP Hretcol].
  have Hretenc : encode_code (code q) pc0 (vala ra_val) = Some reta1 := Hc1 _ _ Hreta1 Hretcode.
  have HctpcB : 1 + ctpc < 2 ^ NC by rewrite -Hretcol; exact: (code_colors_bounded Hretenc).
  have Hra1' : Symbolic.regs (@Symbolic.State mt lrc_tags unit mem0 reg
                 (pcw @ (Level level ctpc)) extra) ra = Some ((vala ra_val) @ (taga ra_val))
    by rewrite /= Hra1 atom_etaE.
  have [vra2 [Hra2 Hra2v]] := reg_get Hreg Hra1'.
  have Hra2val : vra2 = phia (vala ra_val).
  { have HnI : taga ra_val <> Invalidated by rewrite Hraj.
    rewrite (Hra2v HnI) Hraj. exact: rel_v_InternalJump. }
  have [reta2 [Hreta2 Hretat]] := jump_target_corr Hc1 Hc1' Hc2' Hmwk Hreta1.
  have Hsz1' : Symbolic.regs (@Symbolic.State mt lrc_tags unit mem0 reg
                 (pcw @ (Level level ctpc)) extra) syscall_arg1 = Some ((vala sz1) @ Other)
    by rewrite /= Hsz1 -Hothz atom_etaE.
  have Hsz2 : Symbolic.regs s2 syscall_arg1 = Some ((vala sz1) @ Other) := reg_otherE Hreg Hsz1' erefl.
  have Hmaddr :
    List.last (List.filter (fun mw => andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz (1 + ctpc))) (domm mem0))
              (@component_memory_prefix mt NC (ssrint.Posz (1 + ctpc)))
    = List.last (List.filter (fun mw => andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz (1 + ctpc))) (domm (Symbolic.mem s2)))
              (@component_memory_prefix mt NC (ssrint.Posz (1 + ctpc))).
  { by rewrite (padc_filter_domm_eq HctpcB Hmp). }
  have Hpct2 : taga (Symbolic.pc s2) = Level level ctpc by rewrite Hpct.
  have Hra2j : Symbolic.regs s2 ra = Some (vra2 @ InternalJump) by rewrite Hra2 Hraj.
  have Hretm2 : Symbolic.mem s2 vra2 = Some reta2 by rewrite Hra2val.
  have Hck2 : is_code (taga reta2) && (color (taga reta2) == ctpc) = true
    by rewrite Hretat Hretcode Hretcol eqxx.
  have Hszval : word.int_of_word (vala ((vala sz1) @ Other)) = word.int_of_word (vala sz1)
    by rewrite vala_at.
  have Hpcwv : (val pcw : nat) = alloc_label by rewrite Hpcw (val_word_of_nat alloc_label_lt_word).
  have Hmem2none : Symbolic.mem s2 pcw = None.
  { case E: (Symbolic.mem s2 pcw) => [a|] //. exfalso.
    have Hge : alloc_label <= (val pcw : nat) by rewrite Hpcwv.
    have Hnc := high_not_code_r Hmp Hge E.
    have [a0 [Ha0 _]] := Hmwkb pcw a E Hnc. by rewrite Ha0 in PC. }
  have [retv1 Hretv1] : exists rv, reg syscall_ret = Some rv.
  { case E: (reg syscall_ret) => [rv|]; first by exists rv.
    move: Hregs1'; rewrite /updm E /= => H; discriminate H. }
  have Hretv1' : Symbolic.regs (@Symbolic.State mt lrc_tags unit mem0 reg
                   (pcw @ (Level level ctpc)) extra) syscall_ret = Some retv1 by [].
  have [rv2 Hret2'] := reg_some Hreg Hretv1'.
  Local Transparent alloc_fun.
  have [s2' Halloc2] : exists s2', alloc_fun (NC := NC) s2 = Some s2'.
  { rewrite {1}/alloc_fun.
    rewrite Hpct2 Hra2j obindE is_jumpE obindE.
    rewrite vala_at Hretm2 obindE Hck2 obindE.
    rewrite Hsz2 obindE is_otherE obindE.
    rewrite vala_at Hlen1 obindE Hlenchk1 obindE.
    rewrite -Hmaddr Hpf1 Haddr1 obindE.
    rewrite /updm Hret2' obindE. by eexists. }
  Local Opaque alloc_fun.
  have [i1 Hevi1] : exists i, Symbolic.evi (@Symbolic.State mt lrc_tags unit mem0 reg
                     (pcw @ (Level level ctpc)) extra) = Some i.
  { move: CALL; rewrite /run_syscall; case E: (Symbolic.evi _) => [i|] //= _; by exists i. }
  have [a1 Ha1] : exists a, reg rcom = Some a.
  { case E: (reg rcom) => [a|]; first by exists a.
    move: Hevi1; rewrite /Symbolic.evi /= E /= => H; discriminate H. }
  have [vrc Hrc2] := reg_some Hreg Ha1.
  have [i2 Hevi2] : exists i, Symbolic.evi s2 = Some i.
  { rewrite /Symbolic.evi Hrc2 /=. by eexists. }
  have Hpc2val : vala (Symbolic.pc s2) = pcw.
  { rewrite Hpcv0 /= Hpcw. exact: phia_alloc_fixed. }
  have Hrun2 : @Symbolic.run_syscall mt ops lrc_tags Merged.transfer unit sc s2 = Some (s2', None).
  { rewrite /run_syscall Hsem Hent Hevi2 /= /Merged.transfer /=. by rewrite Halloc2. }
  exists s2'. split.
  - eapply step_syscall.
    + exact: (Symbolic.state_eta s2).
    + rewrite /Symbolic.pcv Hpc2val. exact: Hmem2none.
    + rewrite /Symbolic.pcv Hpc2val. exact: GETCALL.
    + exact: Hrun2.
  -
    Local Transparent alloc_fun.
    move: Halloc2; rewrite {1}/alloc_fun Hpct2 Hra2j obindE is_jumpE obindE vala_at Hretm2 obindE
      Hck2 obindE Hsz2 obindE is_otherE obindE vala_at Hlen1 obindE Hlenchk1 obindE
      -Hmaddr Hpf1 Haddr1 obindE /updm Hret2' obindE => -[= Hs2eq].
    Local Opaque alloc_fun.
    have Hregs1eq : regs1' = setm reg syscall_ret (addr1 @ Other).
    { move: Hregs1'; rewrite /updm Hretv1 => -[= H]; by rewrite -H. }
    have HlenB : len1 + 1 <= 2 ^ (word_size mt - NC).
    { move: Hlenchk1; case: ifP => // Hb _; exact: Hb. }
    have Hstart := andw_last_component_prefix (1 + ctpc) mem0.
    have Hend : andw (addw (List.last (List.filter (fun mw => andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz (1 + ctpc))) (domm mem0)) (@component_memory_prefix mt NC (ssrint.Posz (1 + ctpc)))) (@as_word (word_size mt) (ssrint.Posz (len1 + 1)))) (@mask mt NC) = @component_memory_prefix mt NC (ssrint.Posz (1 + ctpc)).
    { by apply/eqP; move: Hpf1; rewrite /=; case: (_ == _). }
    have Hbloc := alloc_bloc_props HctpcB Hstart Hend HlenB.
    rewrite -Hs1' -Hs2eq Hregs1eq.
    split; first exact: Hra2val.
    split; first by [].
    split; first by [].
    split; first by rewrite /=; exact: (wregs_setm_other Hreg).
    split.
    { move=> w a; rewrite /= => Hw Hic. case: (unionm_get Hw) => [Hm0|[_ Hbl]].
      - exact: (Hc1 _ _ Hm0 Hic).
      - have [Hav _] := Hbloc _ _ Hbl. by rewrite Hav in Hic. }
    split.
    { move=> w a He. rewrite /=. apply: unionm_getL. exact: (Hc1' _ _ He). }
    split.
    { move=> w a; rewrite /= => Hw Hic. case: (unionm_get Hw) => [Hm2|[_ Hbl]].
      - exact: (Hc2 _ _ Hm2 Hic).
      - have [Hav _] := Hbloc _ _ Hbl. by rewrite Hav in Hic. }
    split.
    { move=> w a He. rewrite /=. apply: unionm_getL. exact: (Hc2' _ _ He). }
    split.
    { move=> w a; rewrite /= => Hw Hnc. case: (unionm_get Hw) => [Hm0|[Hm0n Hbl]].
      - have [v2 [Hs2w Hrel]] := Hmwk _ _ Hm0 Hnc. exists v2; split; [ apply: unionm_getL; exact: Hs2w | exact: Hrel ].
      - have [Hav Hge] := Hbloc _ _ Hbl.
        have Hs2none : Symbolic.mem s2 w = None.
        { case E2: (Symbolic.mem s2 w) => [b|]; last by [].
          have Hncb : is_code (taga b) = false.
          { case Eic: (is_code (taga b)); last by []. exfalso.
            have [n [Hwn [Hnlt _]]] := encode_code_nth_inv (Hc2 w b E2 Eic).
            have Hbw : pc0 + size padc < 2 ^ word_size mt by exact: (ltn_trans Hbound' alloc_label_lt_word).
            have Hb : n + pc0 < 2 ^ word_size mt by (move: Hnlt Hbw; lia).
            have Hvw : (val w : nat) = n + pc0 by rewrite Hwn (val_word_of_nat Hb).
            move: Hge; rewrite Hvw; move: Hnlt Hbound'; lia. }
          have [a0 [Ha0 _]] := Hmwkb _ _ E2 Hncb. by rewrite Ha0 in Hm0n. }
        exists (vala a). split.
        + by rewrite /= (unionmE (Symbolic.mem s2)) Hs2none /= Hbl (atom_etaE a).
        + move=> _. rewrite Hav /=. exact: (esym (@PaddingSim.rel_v_Other q q' (as_word (ssrint.Posz 0)))). }
    { move=> w a; rewrite /= => Hw Hnc. case: (unionm_get Hw) => [Hm2|[Hm2n Hbl]].
      - have [a0 [Hm0w [Ht Hrel]]] := Hmwkb _ _ Hm2 Hnc. exists a0; split; [ apply: unionm_getL; exact: Hm0w | split; [exact: Ht | exact: Hrel] ].
      - have [Hav Hge] := Hbloc _ _ Hbl.
        have Hm0none : mem0 w = None.
        { case E1: (mem0 w) => [b|]; last by [].
          have Hncb : is_code (taga b) = false.
          { case Eic: (is_code (taga b)); last by []. exfalso.
            have [n [Hwn [Hnlt _]]] := encode_code_nth_inv (Hc1 w b E1 Eic).
            have Hbw : pc0 + size (code q) < 2 ^ word_size mt by exact: (ltn_trans Hbound alloc_label_lt_word).
            have Hb : n + pc0 < 2 ^ word_size mt by (move: Hnlt Hbw; lia).
            have Hvw : (val w : nat) = n + pc0 by rewrite Hwn (val_word_of_nat Hb).
            move: Hge; rewrite Hvw; move: Hnlt Hbound; lia. }
          have [v2 [Hs2w _]] := Hmwk _ _ E1 Hncb. by rewrite Hs2w in Hm2n. }
        exists a. split.
        + rewrite /= (unionmE mem0) Hm0none /=. exact: Hbl.
        + split; first by []. move=> _. rewrite Hav /=. exact: (esym (@PaddingSim.rel_v_Other q q' (as_word (ssrint.Posz 0)))). }
Qed.


Lemma rel_v_addr (t : value_tag) (v : mword mt) :
  is_address t -> t <> Invalidated -> rel_v t v = phia v.
Proof.
  case: t => [n| | |] Haddr Hni.
  - exact: PaddingSim.rel_v_Ret.
  - by [].
  - exact: PaddingSim.rel_v_InternalJump.
  - by case: (Hni erefl).
Qed.

Lemma reg_reflect_bwd_cptr (s1 s2 : st) (r : reg mt) (w : mword mt) (t : value_tag) :
  match_pad s1 s2 -> Symbolic.regs s2 r = Some (w @ t) -> is_address t -> t <> Invalidated ->
  exists w', Symbolic.regs s1 r = Some (w' @ t) /\ w = phia w'.
Proof.
  move=> Hmp Hr2 Haddr Hninv.
  have [_ [_ [_ [Hreg _]]]] := Hmp.
  move: (Hreg r); case Hr1: (Symbolic.regs s1 r) => [a|] /=; last by rewrite Hr2.
  move=> [v2 [Hr2' Hrel]].
  have Hta : taga a = t by move: Hr2'; rewrite Hr2 => [= _ ->].
  have Hv2 : v2 = w by move: Hr2'; rewrite Hr2 => [= -> _].
  have Hni : taga a <> Invalidated by rewrite Hta.
  have Hwv : w = phia (vala a)
    by rewrite -Hv2 (Hrel Hni) Hta (rel_v_addr (vala a) Haddr Hninv).
  exists (vala a); split; last exact: Hwv.
  congr Some. by rewrite -(atom_etaE a) Hta.
Qed.

Lemma reg_reflect_bwd_other (s1 s2 : st) (r : reg mt) (w : mword mt) :
  match_pad s1 s2 -> Symbolic.regs s2 r = Some (w @ Other) ->
  Symbolic.regs s1 r = Some (w @ Other).
Proof.
  move=> Hmp Hr2.
  have [_ [_ [_ [Hreg _]]]] := Hmp.
  move: (Hreg r); case Hr1: (Symbolic.regs s1 r) => [a|] /=; last by rewrite Hr2.
  move=> [v2 [Hr2' Hrel]].
  have Hta : taga a = Other by move: Hr2'; rewrite Hr2 => [= _ ->].
  have Hv2 : v2 = w by move: Hr2'; rewrite Hr2 => [= -> _].
  have Hvw : vala a = w.
  { have Hni : taga a <> Invalidated by rewrite Hta.
    by rewrite -Hv2 (Hrel Hni) Hta PaddingSim.rel_v_Other. }
  congr Some. by rewrite -(atom_etaE a) Hta Hvw.
Qed.

Lemma reg_reflect_bwd (s1 s2 : st) (r : reg mt) (w2 : mword mt) (t : value_tag) :
  match_pad s1 s2 -> Symbolic.regs s2 r = Some (w2 @ t) ->
  exists w1, Symbolic.regs s1 r = Some (w1 @ t).
Proof.
  move=> Hmp Hr2.
  have [_ [_ [_ [Hreg _]]]] := Hmp.
  move: (Hreg r); case Hr1: (Symbolic.regs s1 r) => [a|] /=; last by rewrite Hr2.
  move=> [v2 [Hr2' _]].
  have Ht : taga a = t by move: Hr2'; rewrite Hr2 => [= _ ->].
  by exists (vala a); rewrite -Ht; congr Some; exact: (esym (atom_etaE a)).
Qed.

Lemma jump_target_corr_bwd (s1 s2 : st) (w : mword mt) (celltgt2 : matom) :
  match_pad s1 s2 -> addr_ok (Symbolic.mem s1) w -> Symbolic.mem s2 (phia w) = Some celltgt2 ->
  exists celltgt1, Symbolic.mem s1 w = Some celltgt1 /\ taga celltgt1 = taga celltgt2.
Proof.
  move=> Hmp Hok Hm2.
  have [_ [_ [_ [_ [Hc1 [Hc1' [Hc2 [Hc2' [Hnc1 Hnc2]]]]]]]]] := Hmp.
  case Hmw: (Symbolic.mem s1 w) => [celltgt1|].
  - have [celltgt2' [Hm2' Ht2]] := jump_target_corr Hc1 Hc1' Hc2' Hnc1 Hmw.
    exists celltgt1; split; first by []. move: Hm2; rewrite Hm2' => [= <-]; by rewrite Ht2.
  - exfalso.
    have Hout : pc0 + size padc <= val w \/ (val w : nat) < pc0.
    { case: Hok => [[c0 Hc0]|H]; [by rewrite Hmw in Hc0 | exact: H]. }
    have Hpid : phia w = w.
    { rewrite /PaddingSim.phia; case: (ltnP (val w) pc0) => Hlo.
      - by rewrite (PaddingSim.phia_nat_id_lo q' Hlo); exact: valwK.
      - have Hge : pc0 + size (code q) <= val w
          by case: Hout => H; [ have := size_code_le_padc; lia | move: Hlo H; lia ].
        rewrite (PaddingSim.phia_nat_id_hi Hcount Hbound Hbound' Hge); exact: valwK. }
    move: Hm2; rewrite Hpid => Hm2.
    case Hcc: (is_code (taga celltgt2)).
    + have Henc := Hc2 _ _ Hm2 Hcc.
      have Hbw' : pc0 + size padc < 2 ^ word_size mt by exact: (ltn_trans Hbound' alloc_label_lt_word).
      have [k [Hwk [Hklt _]]] := encode_code_nth_inv Henc.
      have Hb2 : k + pc0 < 2 ^ word_size mt by move: Hklt Hbw'; lia.
      have Hval : (val w : nat) = k + pc0 by rewrite Hwk (val_word_of_nat Hb2).
      move: Hout; rewrite Hval; lia.
    + have [a0 [Ha0 _]] := Hnc2 _ _ Hm2 Hcc. by rewrite Ha0 in Hmw.
Qed.

Lemma phia_inj_alloc (w : mword mt) :
  phia w = word_of_nat alloc_label -> w = word_of_nat alloc_label.
Proof.
  move=> H.
  have Hbw : pc0 + size padc < 2 ^ word_size mt := ltn_trans Hbound' alloc_label_lt_word.
  case: (ltnP (val w) pc0) => H1.
  - have Hpid : phia w = w.
    { rewrite /PaddingSim.phia (PaddingSim.phia_nat_id_lo q' H1). exact: valwK. }
    by rewrite -Hpid.
  - case: (ltnP (val w) (pc0 + size (code q))) => H2; last first.
    + have Hpid : phia w = w.
      { rewrite /PaddingSim.phia (PaddingSim.phia_nat_id_hi Hcount Hbound Hbound' H2). exact: valwK. }
      by rewrite -Hpid.
    + exfalso.
      have Hk : (val w : nat) - pc0 < size (code q) by move: H2 H1; lia.
      have Hwk : w = word_of_nat (((val w : nat) - pc0) + pc0).
      { have -> : ((val w : nat) - pc0) + pc0 = (val w : nat) by move: H1; lia.
        exact: (esym (valwK w)). }
      move: H; rewrite {1}Hwk (PaddingSim.phia_addr_code Hcount Hbound Hbound' Hk) => Hsh.
      have Hlt : shift_pos sizes ((val w : nat) - pc0) + pc0 < 2 ^ word_size mt
        by have := phi_lt_padc Hcount Hk; move: Hbw; lia.
      have Heq := word_of_nat_inj Hlt alloc_label_lt_word Hsh.
      have := phi_lt_padc Hcount Hk. move: Hbound' Heq; lia.
Qed.

Lemma pad_nostep_syscall (s1 s2 : st)
   (mem2 : {fmap mword mt -> matom}) (reg2 : {fmap reg mt -> ratom})
   (pcw2 : mword mt) (tpc2 : tag_type lrc_tags Symbolic.P) (extra2 : unit)
   (sc : @Symbolic.syscall mt lrc_tags unit) (s2' : st) (ev : option event) :
   match_pad s1 s2 -> pad_valid s1 ->
   s2 = @Symbolic.State mt lrc_tags unit mem2 reg2 (pcw2 @ tpc2) extra2 ->
   mem2 pcw2 = None ->
   Instance.table (NC := NC) pcw2 = Some sc ->
   @Symbolic.run_syscall mt ops lrc_tags Merged.transfer unit sc s2 = Some (s2', ev) ->
   exists s1' ev', step_me (NC := NC) s1 s1' ev'.
Proof.
  move=> Hmp Hvalid Hs2 PC GETCALL CALL.
  have Hsem : Symbolic.sem sc = alloc_fun (NC := NC).
  { move: GETCALL; rewrite /Instance.table /Merged.table mkfmapE /=.
    case: ifP => [_ [= <-] //|_]. by move=> [=]. }
  have Hent : Symbolic.entry_tag sc = tt by case: (Symbolic.entry_tag sc).
  have Hpcw : pcw2 = word_of_nat alloc_label.
  { move: GETCALL; rewrite /Instance.table /Merged.table mkfmapE /=. by case: ifP => [/eqP|]. }
  have [Halloc2 Hev] : alloc_fun (NC := NC) s2 = Some s2' /\ ev = None.
  { move: CALL; rewrite /run_syscall Hsem Hent /=.
    case Hevi: (Symbolic.evi _) => [i|] //=.
    rewrite /Merged.transfer /=.
    case Halloc: (alloc_fun (NC := NC) _) => [s|] //=. by move=> [= <- <-]. }
  have Htpc2 : taga (Symbolic.pc s2) = tpc2 by rewrite Hs2.
  destruct tpc2 as [level ctpc].
  Local Transparent alloc_fun.
  move: Halloc2; rewrite {1}/alloc_fun Htpc2 => H2.
  case: (obind_inv H2) => ra_val2 [Hra2 {}H2].
  case: (obind_inv H2) => u1 [Hjmp2 {}H2].
  case: (obind_inv H2) => reta2 [Hreta2 {}H2].
  case: (obind_inv H2) => uret [Hretchk2 {}H2].
  move: Hretchk2; case: ifP => Hretc2 Hretc2'; last by [].
  case: (obind_inv H2) => sz2 [Hsz2 {}H2].
  case: (obind_inv H2) => uoth [Hoth2 {}H2].
  case: (obind_inv H2) => len2 [Hlen2 {}H2].
  case: (obind_inv H2) => ulen [Hlenchk2 {}H2].
  move: H2; case: ifP => // Hpf2 H2.
  case: (obind_inv H2) => addr2 [Haddr2 {}H2].
  case: (obind_inv H2) => regs2' [Hregs2' {}H2].
  Local Opaque alloc_fun.
  have Hraj : taga ra_val2 = InternalJump := is_jump_invE Hjmp2.
  have Hothz : taga sz2 = Other := is_other_invE Hoth2.
  move: Hretc2 => /andP [Hretcode /eqP Hretcol].
  have Hra2a : Symbolic.regs s2 ra = Some ((vala ra_val2) @ InternalJump)
    by rewrite Hra2 -Hraj atom_etaE.
  have [rav1 [Hra1 Hrav]] := reg_reflect_bwd_cptr Hmp Hra2a isT (fun H => ltac:(discriminate H)).
  have Hok : addr_ok (Symbolic.mem s1) rav1.
  { have [Hav _] := Hvalid. apply: (Hav _ _ _ Hra1). by []. }
  have Hm2tgt : Symbolic.mem s2 (phia rav1) = Some reta2 by rewrite -Hrav.
  have [reta1 [Hretm1 Hretat]] := jump_target_corr_bwd Hmp Hok Hm2tgt.
  have Hcode1 : is_code (taga reta1) by rewrite Hretat.
  have Hcol1 : color (taga reta1) = ctpc by rewrite Hretat.
  have [_ [_ [_ [_ [Hc1 _]]]]] := Hmp.
  have Hretenc : encode_code (code q) pc0 rav1 = Some reta1 := Hc1 _ _ Hretm1 Hcode1.
  have HctpcB : 1 + ctpc < 2 ^ NC by rewrite -Hcol1; exact: (code_colors_bounded Hretenc).
  have Hsz2a : Symbolic.regs s2 syscall_arg1 = Some ((vala sz2) @ Other)
    by rewrite Hsz2 -Hothz atom_etaE.
  have Hsz1 : Symbolic.regs s1 syscall_arg1 = Some ((vala sz2) @ Other)
    := reg_reflect_bwd_other Hmp Hsz2a.
  have [rv2 Hret2] : exists rv, reg2 syscall_ret = Some rv.
  { case E: (reg2 syscall_ret) => [rv|]; first by exists rv.
    move: Hregs2'; rewrite /updm Hs2 /= E /= => Hd; discriminate Hd. }
  have Hret2' : Symbolic.regs s2 syscall_ret = Some rv2 by rewrite Hs2.
  rewrite -(atom_etaE rv2) in Hret2'.
  have [rv1 Hret1] := reg_reflect_bwd Hmp Hret2'.
  have Hmaddr :
    List.last (List.filter (fun mw => andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz (1 + ctpc))) (domm (Symbolic.mem s1)))
              (@component_memory_prefix mt NC (ssrint.Posz (1 + ctpc)))
    = List.last (List.filter (fun mw => andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz (1 + ctpc))) (domm (Symbolic.mem s2)))
              (@component_memory_prefix mt NC (ssrint.Posz (1 + ctpc))).
  { by rewrite (padc_filter_domm_eq HctpcB Hmp). }
  have [Hpcv0 _] := Hmp.
  have Hpc1alloc : vala (Symbolic.pc s1) = pcw2.
  { rewrite Hpcw. apply: phia_inj_alloc. rewrite -Hpcv0 Hs2 /=. exact: Hpcw. }
  have [_ [Hpct _]] := Hmp.
  have Htpc1 : taga (Symbolic.pc s1) = Level level ctpc by rewrite -Hpct Hs2.
  have Hmem1none : Symbolic.mem s1 pcw2 = None.
  { case E: (Symbolic.mem s1 pcw2) => [a|] //. exfalso.
    have Hge : alloc_label <= (val pcw2 : nat) by rewrite Hpcw (val_word_of_nat alloc_label_lt_word).
    have Hnc := high_not_code_l Hmp Hge E.
    have [_ [_ [_ [_ [_ [_ [_ [_ [Hmwk _]]]]]]]]] := Hmp.
    have [v2 [Hs2w _]] := Hmwk pcw2 a E Hnc. by rewrite Hs2 /= PC in Hs2w. }
  Local Transparent alloc_fun.
  have [s1' Halloc1] : exists s1', alloc_fun (NC := NC) s1 = Some s1'.
  { rewrite {1}/alloc_fun Htpc1 Hra1 obindE is_jumpE obindE.
    rewrite vala_at Hretm1 obindE.
    have Hck1 : is_code (taga reta1) && (color (taga reta1) == ctpc) = true
      by rewrite Hcode1 Hcol1 eqxx.
    rewrite Hck1 obindE Hsz1 obindE is_otherE obindE.
    rewrite vala_at Hlen2 obindE Hlenchk2 obindE.
    rewrite Hmaddr Hpf2 Haddr2 obindE.
    rewrite /updm Hret1 obindE. by eexists. }
  Local Opaque alloc_fun.
  have [iev Hevi2] : exists i, Symbolic.evi s2 = Some i.
  { move: CALL; rewrite Hs2 /run_syscall; case E: (Symbolic.evi _) => [i|] //= _; by exists i. }
  have [a1 Ha1] : exists a, Symbolic.regs s2 rcom = Some a.
  { case E: (Symbolic.regs s2 rcom) => [a|]; first by exists a.
    move: Hevi2; rewrite /Symbolic.evi E /= => Hd; discriminate Hd. }
  have Hrcom2' : Symbolic.regs s2 rcom = Some ((vala a1) @ (taga a1)) by rewrite Ha1 atom_etaE.
  have [w1 Hrcom1] := reg_reflect_bwd Hmp Hrcom2'.
  have [i1 Hevi1] : exists i, Symbolic.evi s1 = Some i by rewrite /Symbolic.evi Hrcom1 /=; eexists.
  have Hrun1 : @Symbolic.run_syscall mt ops lrc_tags Merged.transfer unit sc s1 = Some (s1', None).
  { rewrite /run_syscall Hsem Hent Hevi1 /= /Merged.transfer /=. by rewrite Halloc1. }
  exists s1', None. eapply step_syscall.
  - exact: (Symbolic.state_eta s1).
  - rewrite /Symbolic.pcv Hpc1alloc. exact: Hmem1none.
  - rewrite /Symbolic.pcv Hpc1alloc. exact: GETCALL.
  - exact: Hrun1.
Qed.


End CodeShiftFwdSys.
