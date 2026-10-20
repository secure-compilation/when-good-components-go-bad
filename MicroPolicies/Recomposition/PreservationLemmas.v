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

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
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

Require Import MicroPolicies.Utils.
Import DoNotation.
Import Types.

Require Import MicroPolicies.Recomposition.Definitions.
Require MicroPolicies.Recomposition.TraceWF MicroPolicies.Recomposition.TraceBracket.
Import TraceWF(ndsu1_mem_noM, ndsu_mem_noM, table_sem_alloc, no_mw_reg_clear_read, no_mr_reg_clear_read, jal_head_tret, mem_unchanged_jal).
Import TraceBracket(reg_index_neq, jal_do_updates_result, jump_do_updates_result, nsu_silent_extract, mkfmap_const_val, check_belong_color, store_transfer, load_transfer, load_guard, switch_val_color, switch_val_iscode, switch_val_entry, switch_val_vtag).

Opaque andw shlw as_word word_of_nat.

Module Preservation (S: RecompositionContext).

  Module M := RecompositionDefinitions S.
  Include S. Include M.
  (* Import S. Export M. *)

  Lemma obindE A B (f : A -> option B) a : obind f (Some a) = f a.
  Proof. by []. Qed.
  Lemma is_jumpE : is_jump InternalJump = Some tt.
  Proof. by []. Qed.
  Lemma is_otherE : is_other Other = Some tt.
  Proof. by []. Qed.

  Lemma data_match_taga i cc m d d' :
    data_match i cc m d d' -> taga d = taga d'.
  Proof. by case: d => v t; case: d' => v' t' => -[-> _]. Qed.

  Lemma data_match_other_val i cc m d d' :
    taga d = Other -> data_match i cc m d d' -> vala d = vala d'.
  Proof. by case: d => v t; case: d' => v' t' /= -> -[_ ->]. Qed.

  (* Let ip := prog_interface p. *)
  (* Let ic := prog_interface c. *)
  (* Let prog   := program_link p  c. *)
  (* Let prog'  := program_link p'  c'. *)
  (* Let prog'' := program_link p c'. *)

  (* Let state := @Symbolic.state mt LRC.lrc_tags [eqType of unit]. *)
  (* Let genvtype := unit. *)
  (* Let step1 := (fun (ge: genvtype) s t s' => match t with *)
  (*                                      | [::] => step_me s s' None *)
  (*                                      | e :: [::] => step_me s s' (Some e) *)
  (*                                      | _ => False *)
  (*                                      end). *)
  (* Let step2 := (fun (ge: genvtype) s t s' => match t with *)
  (*                                      | [::] => step_mp s s' None *)
  (*                                      | e :: [::] => step_mp s s' (Some e) *)
  (*                                      | _ => False *)
  (*                                      end). *)

  Ltac import_context :=
   pose proof Hwfp as Hwfp;
   pose proof Hwfc as Hwfc;
   pose proof Hwfp' as Hwfp';
   pose proof Hwfc' as Hwfc';
   pose proof Hmergeable_ifaces as Hmergeable_ifaces;
   pose proof Hifacep as Hifacep;
   pose proof Hifacec as Hifacec;
   pose proof Hprog_is_closed as Hprog_is_closed;
   pose proof Hprog_is_closed' as Hprog_is_closed'.

Lemma color_of_pc_eq : forall (s s' : state), pc s' = pc s -> color_of s' = color_of s.
Proof. by move=> [? ? [? ?] ?] [? ? [? ?] ?] /= [= _ ->]. Qed.

Lemma color_of_taga_eq : forall (s s' : state), taga (pc s') = taga (pc s) -> color_of s' = color_of s.
Proof. by move=> [? ? [? ?] ?] [? ? [? ?] ?] /= ->. Qed.

Lemma color_ofE : forall (s : state), color_of s = match taga (pc s) with Level _ c => c end.
Proof. by move=> [? ? [? ?] ?]. Qed.

Lemma pc_code_color_write : forall (s s' : state) w v,
    mem s' = setm (mem s) w v -> ~ is_code (taga v) -> pc s' = pc s ->
    pc_code_color s -> pc_code_color s'.
Proof.
  move=> s s' w v Hmem Hncv Hpc Hpcc d.
  have Hcol := color_of_pc_eq Hpc.
  rewrite Hmem Hpc setmE.
  case: eqP => [Heq | Hne].
  - move=> [= Hdv] Hcode. subst d. by case: (Hncv Hcode).
  - move=> Hd Hcode. rewrite Hcol. exact: (Hpcc d Hd Hcode).
Qed.

Lemma pc_code_color_cong : forall (s s' : state),
    mem s' = mem s -> pc s' = pc s -> pc_code_color s -> pc_code_color s'.
Proof.
  move=> s s' Hm Hpc Hpcc d.
  have Hcol := color_of_pc_eq Hpc.
  rewrite Hm Hpc => Hd Hcode. rewrite Hcol. exact: (Hpcc d Hd Hcode).
Qed.

Lemma pc_code_color_alloc : forall (s s' : state) blk (a : mword mt) ret,
    mem s' = unionm (mem s) blk -> mem s a = Some ret ->
    vala (pc s') = a -> taga (pc s') = taga (pc s) ->
    (is_code (taga ret) && (color (taga ret) == match taga (pc s) with Level _ c => c end)) ->
    pc_code_color s'.
Proof.
  move=> s s' blk a ret Hmem Hret Hpc Htag Hchk d.
  have Hcol := color_of_taga_eq Htag.
  rewrite Hmem Hpc unionmE Hret /= => -[= Hd] Hcode. subst d.
  move: Hchk => /andP [_ /eqP Hc].
  by rewrite Hcol (color_ofE s).
Qed.

Lemma silent_transfer_belong :
  forall (op : opcode) tpc ti (ts : hseq (tag_type lrc_tags) (inputs op)) tni evi (ov : ovec lrc_tags op),
    LRC.transfer (IVec (OP op) tpc ti ts tni) evi = Some (ov, None) ->
    belong (match tpc with Level _ c => c end) tni.
Proof.
  move=> op; destruct op; move=> tpc ti ts tni evi ov;
    rewrite /LRC.transfer /LRC.instr_rules_mp; case: tpc => [level current']; cbv zeta;
    move=> Htr; case: (obind_inv Htr) => u [Hg Hrest]; clear Htr; move: Hg; case Heq: (_ == current') => // _;
    move/eqP: Heq => <-;
    set cur := (match ti with {| color := c |} => c end) in Hrest *;
    have cbE : (forall u', check_belong cur tni = Some u' -> belong cur tni)
      by (move=> u'; rewrite /check_belong; case: (belong cur tni));
    cbn -[check_belong belong is_other is_jump get_tni_color check_ret] in Hrest.
  all: try by [].
  -  rewrite (hseq0 ts) /= in Hrest.
    by case: (obind_inv Hrest) => u' [Hcb _]; exact: (cbE _ Hcb).
  -  case: ts Hrest => t0 ts Hrest; rewrite (hseq0 ts) /= in Hrest.
    by case: (obind_inv Hrest) => u' [Hcb _]; exact: (cbE _ Hcb).
  -  case: ts Hrest => t0 [t1 ts] Hrest; rewrite (hseq0 ts) /= in Hrest.
    by case: (obind_inv Hrest) => u' [Hcb _]; exact: (cbE _ Hcb).
  -  case: ts Hrest => t0 [t1 [t2 ts]] Hrest; rewrite (hseq0 ts) /= in Hrest.
    by case: (obind_inv Hrest) => u' [Hcb _]; exact: (cbE _ Hcb).
  -  case: ts Hrest => t0 [t1 [t2 ts]] Hrest; rewrite (hseq0 ts) /= in Hrest.
    case: (obind_inv Hrest) => ? [_ {}Hrest].
    by case: (obind_inv Hrest) => u' [Hcb _]; exact: (cbE _ Hcb).
  -  case: ts Hrest => t0 [t1 [t2 ts]] Hrest; rewrite (hseq0 ts) /= in Hrest.
    case: (obind_inv Hrest) => ? [_ {}Hrest].
    by case: (obind_inv Hrest) => u' [Hcb _]; exact: (cbE _ Hcb).
  -
    case: ts Hrest => tra [tp [trcom next]] Hrest.
    move: Hrest; case Hb: (belong cur tni) => Hrest; first by [].
    exfalso; case: (obind_inv Hrest) => ? [_ {}Hrest]; case: (obind_inv Hrest) => ? [_ {}Hrest].
    case: (obind_inv Hrest) => ? [_ {}Hrest]; by move: Hrest => [= _].
  -  case: ts Hrest => t0 ts Hrest; rewrite (hseq0 ts) /= in Hrest.
    by case: (obind_inv Hrest) => u' [Hcb _]; exact: (cbE _ Hcb).
  -
    case: ts Hrest => tnext [tra [trcom next]] Hrest.
    case: (obind_inv Hrest) => ? [_ {}Hrest].
    move: Hrest; case Hb: (belong cur tni) => Hrest; first by [].
    exfalso; case: (obind_inv Hrest) => ? [_ {}Hrest].
    case: (obind_inv Hrest) => c' [Htc {}Hrest]; case: (obind_inv Hrest) => ? [Hce {}Hrest].
    move: Hrest => [= _ Hev]; move: Htc Hce Hev; clear cbE Hb.
    rewrite /get_tni_color /check_entry /get_proc_name.
    case: tni => [t|] //; case: t => vt ct et bt; by case: et => [[p l]|].
Qed.

(*** Equivalence preservation lemmas ***)

Lemma preserves_equiv_left_pc_incr :
  forall s1 s2 s3 M s1' s3' pc1' tpc1' pc3' tpc3',
    strong_equiv Left M s1 s3
    /\ weak_equiv Right M s2 s3
    /\ common_equiv M s1 s2 s3 ->
    s1' = State _ _ (mem s1) (regs s1) (pc1'@tpc1') tt ->
    s3' = State _ _ (mem s3) (regs s3) (pc3'@tpc3') tt ->
    same_pc Left s1' s3' ->
    tpc1' = taga (pc s1) ->
    tpc3' = taga (pc s3) ->
    pc_code_color s1' ->
    strong_equiv Left M s1' s3'
    /\ weak_equiv Right M s2 s3'
    /\ common_equiv M s1' s2 s3'.
Proof.
  intros s1 s2 s3 M s1' s3' pc1' tpc1' pc3' tpc3' equiv eq_s1' eq_s3' pc1'_pc3' pc1_tag pc3_tag Hpcc1'.
  destruct equiv as [strong [weak common]].
  split; [|split].
  - destruct strong as [? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match].
    econstructor; destruct s, s', pc0, pc1; try (subst; intros; auto; done); try congruence.
  - destruct weak as [? ? ? color_eq side_s'  s'_mem_cor entry_off s'_reg_cor mem_match].
    econstructor; try (rewrite eq_s3'; simpl; auto; done); try (subst; intros; auto; done); try congruence.
    subst. destruct s, s', pc0, pc1. simpl in *. trivial.
  - destruct common as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          [mem_pref_cond_s1 [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 col_mem1]]]]]
                          [mem_pref_cond_s2 [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 col_mem2]]]]]
                          [mem_pref_cond_s3 [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 col_mem3]]]]] code_left code_right Hval wpcc1 wpcc2].
    eapply common_equiv_def with (n := n) (c := c0);
      try ((rewrite eq_s1' eq_s3' || rewrite eq_s1' || rewrite eq_s3'); simpl; auto; done); try congruence; try done.
    + rewrite eq_s1'. rewrite pc1_tag. simpl. exact tag_pc1.
    + rewrite eq_s3'. rewrite pc3_tag. simpl. exact tag_pc3.
Qed.

  Definition capability_correctness' ws (s: state) m v t :=
    match t with
    | Ret n =>
        (forall v w t, vtag t = Ret n -> (mem s) w <> Some (v @ t))
        /\ (forall v r, (regs s) r <> Some (v @ (Ret n)))
        /\ in_stack m ws v n
    | _ => True
    end.


  Lemma convert_int_of_word_inj: forall k (v v': word k),
      convert (int_of_word v) = convert (int_of_word v') ->
      v = v'.
  Proof.
    move=> k v v' H.
    have H' : int_of_word v = int_of_word v' by exact: (convert_inj H).
    by rewrite -(int_of_wordK v) -(int_of_wordK v') H'.
  Qed.

  Lemma preserves_equiv_left_mem_write:
    forall s1 s2 s3 M s1' s3' w v v' m1' m3' i,
      strong_equiv Left M s1 s3
      /\ weak_equiv Right M s2 s3
      /\ common_equiv M s1 s2 s3 ->
      data_match' Left M v v' ->
      (color (taga v)) = (color (taga v')) ->
      (color (taga v)) = color_of s1 ->
      entry (taga v) = None ->
      is_relevant_comp Left (color (taga v)) ->
      (forall v', (mem s1 w) = Some v' \/ (mem s3 w) = Some v' -> (color (taga v)) = (color (taga v'))) ->
      (exists d, mem s3 w = Some d /\ not (is_code (taga d))) ->
      (exists d, mem s1 w = Some d /\ not (is_code (taga d))) ->
      mem s1 (vala (pc s1)) = Some i ->
      is_code (taga i) ->
      not (is_code (taga v)) ->
      not (is_code (taga v')) ->
      capability_correctness' WS_S1 s1 M (vala v) (vtag (taga v )) ->
      capability_correctness' WS_S3 s3 M (vala v') (vtag (taga v')) ->
      address_correctness Left (vala v) (vtag (taga v)) (mem s1) ->
      address_correctness Left (vala v') (vtag (taga v')) (mem s3) ->
      updm (mem s1) w v = Some m1' ->
      updm (mem s3) w v' = Some m3' ->
      s1' = State _ _ m1' (regs s1) (pc s1) tt ->
      s3' = State _ _ m3' (regs s3) (pc s3) tt ->
      strong_equiv Left M s1' s3'
      /\ weak_equiv Right M s2 s3'
      /\ common_equiv M s1' s2 s3'.
  Proof.
    import_context.

    intros s1 s2 s3 M s1' s3' w v v' m1' m3' i equiv v_match v_color M_color no_entry v_relevant same_color no_code_w_s3 no_code_w_s1
      i_is_pc code_i no_code_v no_code_v' capa_prop1 capa_prop3 correct_v correct_v'  eq_m1 eq_m3 eq_s1' eq_s3'.
    destruct equiv as [strong [weak common]].
    pose proof (updm_set eq_m1). pose proof (updm_set eq_m3). subst m1' m3'.
    split; [|split].
    - destruct strong as [? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match];
      econstructor; destruct s, s', pc0, pc1; try (rewrite eq_s1' eq_s3'; simpl; auto; done); try congruence.
      + destruct common as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                            [mem_pref_cond_s1 [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 [entry_code1 cvo1]]]]]]]
                            [mem_pref_cond_s2 [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 [entry_code2 cvo2]]]]]]]
                            [mem_pref_cond_s3 [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 [entry_code3 cvo3]]]]]]]
                            capa_cor1 capa_cor2 capa_cor3 code_left code_right Hcval].
        destruct pc_s1_s3 as [? ? ? eq_none|? ? ? ? eq_comp eq_off pc_s1_s3].
        * destruct eq_none as [eq_none1 eq_none3].
          eapply same_pc_alloc; try rewrite eq_s1'; try rewrite eq_s3'; simpl; auto.
          split.
          -- rewrite setmE. case: ifP => [/eqP eqw | _]; last exact: eq_none1.
             exfalso. subst w.
             destruct no_code_w_s1 as [d [d_eq d_nocode]]. rewrite d_eq in eq_none1. done.
          -- rewrite setmE. case: ifP => [/eqP eqw | _]; last exact: eq_none3.
             exfalso. subst w.
             destruct no_code_w_s3 as [d [d_eq d_nocode]]. rewrite d_eq in eq_none3. done.
        * eapply same_pc_normal.
          -- split.
             ++ subst s1'. simpl. rewrite setmE.
                rewrite i_is_pc. eapply (@eq_trans _ _ (Some (if (Types.vala (pc s) == w) then v else i))).
                ** by case: ifP.
                ** reflexivity.
             ++ destruct (Types.vala (pc s) == w) eqn:eqw; last exact: code_i.
                exfalso. move/eqP in eqw. destruct no_code_w_s1 as [d [d_eq d_nocode]].
                apply: d_nocode. rewrite -eqw i_is_pc in d_eq.
                by case: d_eq => <-.
          -- subst s1'. destruct s, pc0. simpl in *. exact eq_off.
          -- rewrite eq_s1' eq_s3'. simpl. done.
      + subst. trivial.
      + subst. intros d w' rel deq. simpl. destruct d as [vd [vt ? ? ?]]. simpl.
        remember (@eq_op _ w' w) as cond.
        remember (@eq_op _ vd w) as cond1.
        simpl in *. rewrite setmE in deq. try (rewrite <- Heqcond in deq).
        destruct cond; destruct vt; simpl; auto; rewrite setmE; simpl in *; try (rewrite <- Heqcond1); destruct cond1;
          convert_eq_op; try (simplify_some; simpl in *; auto).
        all: try (rewrite - Heqcond1 /=).
        all: try exact correct_v.
        all: try exact (s_mem_cor _ w' rel deq).
        all: try (destruct correct_v as [? [eq1 imp1]]; destruct no_code_w_s1 as [? [eq2 no_code]];
                  rewrite eq1 in eq2; simplify_some; exfalso; eapply no_code; eapply imp1;
                  rewrite <- (same_color _ (or_introl eq1)); trivial).
        all: try eapply (s_mem_cor _ w' _ deq).
        all: try (eapply modusponens; [eapply (s_mem_cor _ w' _ deq) | ]; simpl; intros [v'' [v''eq v''code]];
                  destruct no_code_w_s1 as [d' [d'eq d'code]]; rewrite d'eq in v''eq; simplify_some;
                  exfalso; eapply d'code; eapply v''code; rewrite <- (same_color _ (or_introl d'eq)); trivial).
      + subst. intros d w' rel deq. simpl. destruct d as [vd [vt ? ? ?]]. simpl.
        remember (@eq_op _ w' w) as cond.
        remember (@eq_op _ vd w) as cond1.
        simpl in *. rewrite setmE in deq. try (rewrite <- Heqcond in deq).
        destruct cond; destruct vt; simpl; auto; rewrite setmE; simpl in *; try (rewrite <- Heqcond1); destruct cond1;
          convert_eq_op; try (simplify_some; simpl in *; auto).
        all: try (rewrite - Heqcond1 /=).
        all: try exact correct_v'.
        all: try exact (s'_mem_cor _ w' rel deq).
        all: try (destruct correct_v' as [? [eq1 imp1]]; destruct no_code_w_s3 as [? [eq2 no_code]];
                  rewrite eq1 in eq2; simplify_some; exfalso; eapply no_code; eapply imp1;
                  rewrite <- (same_color _ (or_intror eq1)); trivial).
        all: try eapply (s'_mem_cor _ w' _ deq).
        all: try (eapply modusponens; [eapply (s'_mem_cor _ w' _ deq) | ]; simpl; intros [v'' [v''eq v''code]];
                  destruct no_code_w_s3 as [d' [d'eq d'code]]; rewrite d'eq in v''eq; simplify_some;
                  exfalso; eapply d'code; eapply v''code; rewrite <- (same_color _ (or_intror d'eq)); trivial).
      + subst. simpl. intros col w' w'' d d' proc l l' rel eqw' eqw'' dcode d'code dcol d'col d_e_eq d'_e_eq.
        rewrite setmE in eqw'. rewrite setmE in eqw''.
        unfold_match' eqw'; try convert_eq_op; try simplify_some; try contradiction.
        unfold_match' eqw''; try convert_eq_op; try simplify_some; try contradiction.
        eapply (entry_off); eauto.
      + subst. intros d w' deq. simpl. destruct d as [vd vt].
        remember (@eq_op _ vd w) as cond.
        destruct vt; simpl; auto; rewrite setmE; simpl in *; destruct cond; rewrite -?Heqcond /=;
          convert_eq_op;
          try eapply (s_reg_cor _ w' deq);
          try (eapply modusponens; [eapply (s_reg_cor _ w' deq) | ]; simpl; intros [v'' [v''eq v''code]];
                  destruct no_code_w_s1 as [d' [d'eq d'code]]; rewrite d'eq in v''eq; simplify_some;
                  exfalso; eapply d'code; eapply v''code; rewrite <- (same_color _ (or_introl d'eq)); trivial).
      + subst. intros d w' deq. simpl. destruct d as [vd vt].
        remember (@eq_op _ vd w) as cond.
        destruct vt; simpl; auto; rewrite setmE; simpl in *; destruct cond; rewrite -?Heqcond /=;
          convert_eq_op;
          try eapply (s'_reg_cor _ w' deq);
          try (eapply modusponens; [eapply (s'_reg_cor _ w' deq) | ]; simpl; intros [v'' [v''eq v''code]];
                  destruct no_code_w_s3 as [d' [d'eq d'code]]; rewrite d'eq in v''eq; simplify_some;
                  exfalso; eapply d'code; eapply v''code; rewrite <- (same_color _ (or_intror d'eq)); trivial).
      + unfold memory_match in *. rewrite eq_s1' eq_s3'. simpl.
        intros.
        rewrite setmE. rewrite setmE.
        remember (@eq_op _ w0 w) as cond. destruct cond; rewrite -?Heqcond /=.
        * split; intro eq; inv eq; eexists; split; first [exact v_match | reflexivity].
        * apply mem_match; auto.
    - destruct weak as [? ? ? color_eq side_s' s_mem_cor s'_mem_cor entry_off  mem_match];
      econstructor; destruct s, s', pc0, pc1; subst; auto.
      + subst.
        rewrite /memory_address_correctness; simpl.
        intros d w' rel deq. simpl in *.
        rewrite /address_correctness. rewrite setmE.
        destruct d as [vd [vt ? ? ?]]. simpl.
        destruct vt; auto.
        * move: deq. rewrite setmE.
          case: ifP => /eqP.
          -- move=> ?; subst w. intros H. inv H. simpl in *.
             rewrite <- v_color in rel.
             exfalso.
             eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _
                       (domm ip) (domm ic)); eauto. 
             inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto.
          -- simpl in rel.
             move=> ? H.
             case: ifP => /eqP.
             ++ move=> ?; subst w.
                eexists; split; eauto. simpl.
                intros ?. rewrite <- v_color in H0.
                exfalso.
                eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _
                          (domm ip) (domm ic)).
                inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto.
                eapply H0.
                eauto.
             ++ move=> ?.
                eapply s'_mem_cor in H. simpl in *. eauto.
                simpl. eauto.
        * move: deq. rewrite setmE.
          case: ifP => /eqP.
          -- move=> ?; subst w. intros H. inv H. simpl in *.
             rewrite <- v_color in rel.
             exfalso.
             eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _
                       (domm ip) (domm ic)); eauto. 
             inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto.
          -- simpl in rel.
             move=> ? H.
             case: ifP => /eqP.
             ++ move=> ?; subst w.
                eexists; split; eauto. simpl.
                intros ?. rewrite <- v_color in H0.
                exfalso.
                eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _
                          (domm ip) (domm ic)).
                inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto.
                eapply H0.
                eauto.
             ++ move=> ?.
                eapply s'_mem_cor in H. simpl in *. eauto.
                simpl. eauto.
      + subst. simpl. intros col w' w'' d d' proc l l' rel eqw' eqw'' dcode d'code dcol d'col d_e_eq d'_e_eq.
        rewrite setmE in eqw''.
        unfold_match' eqw''; try convert_eq_op; try simplify_some; try contradiction.
        eapply (entry_off); eauto.
      + unfold memory_match in *. simpl.
        intros.
        rewrite setmE.
        case: eqP => [eq_w | Hne] /=.
        * subst w0.
          have Hip : color (Types.taga v') \in domm ip by rewrite -v_color.
          inversion Hmergeable_ifaces as [[_ fdisj] _].
          split; move=> eq; exfalso.
          -- injection eq as ?; subst d.
             eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
          -- pose proof (mem_match w d H H0) as [_ d_impl].
             destruct (d_impl eq) as [d' [d_d'_match eq_d']].
             have d'_color: color (Types.taga v) = color (Types.taga d') by (eapply same_color; auto).
             have d'_color_bis: color (Types.taga d') = color (Types.taga d).
             { destruct d, d'; simpl; unfold data_match' in d_d'_match; destruct d_d'_match; subst; done. }
             rewrite -d'_color_bis -d'_color in H0.
             eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
        * apply mem_match; auto.
    - destruct common
        as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
              [mem_pref_cond_s1 [mem_pref_cond_s1' [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 [entry_code1 cvo1]]]]]]]]
              [mem_pref_cond_s2 [mem_pref_cond_s2' [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 [entry_code2 cvo2]]]]]]]]
              [mem_pref_cond_s3 [mem_pref_cond_s3' [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 [entry_code3 cvo3]]]]]]]]
              capa_cor1 capa_cor2 capa_cor3 code_left code_right Hcval wpcc1 wpcc2].
      eapply common_equiv_def with (n := n) (c := c0).
      all: try (match goal with |- pc_code_color _ =>
                  rewrite eq_s1'; apply: (pc_code_color_write (s := s1) (w := w) (v := v));
                  first [ exact no_code_v | exact wpcc1 | reflexivity | done ] end).
      all: try ((rewrite eq_s1' eq_s3' || rewrite eq_s1' || rewrite eq_s3'); assumption).
      all: try assumption.
      all: try (split; [|split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]]).
      all: try assumption.
      + rewrite eq_s3'. simpl. clear strong weak code_left code_right v_match tag_pc1 tag_pc2 tag_pc3 capa_cor1 capa_cor2 capa_cor3.
        clear capa_prop1 capa_prop3.
        simpl in *.
        induction wfst; intros.
        * eapply wf_stack_empty; eauto.
        * eapply wf_stack_cons_left; eauto.
          -- rewrite eq_s1'. simpl.
             unfold points_to_comp_code'. rewrite setmE.
             case: eqP => [eq_w | _] /=; last exact PTS_CODE1.
             subst v1.
             exfalso. unfold points_to_comp_code' in PTS_CODE1.
             oapp_False.
             destruct PTS_CODE1 as [color_a [[_ side_of_C] | code_a]].
             ++ simpl in SIDE. unfold side_of in *. rewrite SIDE in side_of_C. inv side_of_C.
             ++ destruct no_code_w_s1 as [d [d_eq d_nocode]]. rewrite d_eq in HeqH. simplify_some. done.
          -- simpl.
             unfold points_to_comp_code. rewrite setmE.
             case: eqP => [eq_w | _] /=; last exact PTS_CODE3.
             subst w.
             exfalso. unfold points_to_comp_code in PTS_CODE3.
             oapp_False.
             destruct PTS_CODE3 as [color_a code_a].
             destruct no_code_w_s3 as [d [d_eq d_nocode]]. rewrite d_eq in HeqH. simplify_some. done.
        * eapply wf_stack_cons_right; eauto.
          -- rewrite eq_s1'. simpl.
             unfold points_to_comp_code'. rewrite setmE.
             case: eqP => [eq_w | _] /=; last exact PTS_CODE1.
             subst v1. simpl.
             unfold points_to_comp_code' in PTS_CODE1.
             oapp_False.
             rewrite (same_color a); try left; auto. destruct PTS_CODE1 as [eqC disj]. split; (try rewrite <- v_color); auto.
             left. split; auto. simpl in SIDE.
             assert (cond_eq: C \in domm ip = false).
             { assert (~ C \in domm ip). intro.
               { eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
                 inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. }
               remember (C \in domm ip) as cond. destruct cond; auto. destruct H. done. }
             unfold side_of in *.
             rewrite cond_eq. done.
          -- simpl.
             unfold points_to_comp_code. rewrite setmE.
             case: eqP => [eq_w | _] /=; last exact PTS_CODE3.
             subst w.
             exfalso. unfold points_to_comp_code in PTS_CODE3.
             oapp_False.
             destruct PTS_CODE3 as [color_a code_a].
             destruct no_code_w_s3 as [d [d_eq d_nocode]]. rewrite d_eq in HeqH. simplify_some. done.
      + clear -same_color no_code_v no_code_w_s1 eq_m1 eq_s1' mem_pref_cond_s1.
        subst s1'.
        move: mem_pref_cond_s1.
        simpl.
        rewrite /memory_prefix_condition => H c w' v'.
        rewrite setmE.
        case: ifP => /eqP; [| move=> _; apply H].
        move=> -> [] <- color_v _.
        destruct no_code_w_s1 as [d [mem_s1_w no_code]].
        eapply H; eauto. rewrite <- same_color; eauto.
      + clear -same_color no_code_v no_code_w_s1 eq_m1 eq_s1' mem_pref_cond_s1'.
        subst s1'.
        move: mem_pref_cond_s1'.
        simpl.
        rewrite /memory_prefix_condition' => H c w' v' Hb.
        rewrite setmE.
        case: ifP => /eqP; [| move=> _; apply (H _ _ _ Hb)].
        move=> -> [] <- G.
        destruct no_code_w_s1 as [d [mem_s1_w no_code]].
        specialize (H _ _ _ Hb mem_s1_w G) as [H1 H2].
        split; [ by rewrite (same_color d (or_introl mem_s1_w)) | exact no_code_v ].
      + clear -same_color no_code_v no_code_w_s1 eq_m1 eq_s1' code_pref_cond_s1.
        subst s1'.
        move: code_pref_cond_s1.
        simpl.
        rewrite /code_prefix_condition => H w' v'.
        rewrite setmE. case: ifP => /eqP.
        * move=> ? [] ?; subst. contradiction.
        * move=> _.
          apply H.
      + unfold alloc_empty in *. subst. simpl in *. rewrite setmE.
        case: eqP => [eq_al | _]; last exact alloc_mem_s1.
        exfalso. subst w.
        unfold updm in eq_m1. rewrite alloc_mem_s1 in eq_m1. simpl in eq_m1. inversion eq_m1.
      + intros d w' deq dcode. subst. simpl in deq. rewrite setmE in deq.
        move: deq. case: eqP => [eq_d | _] deq.
        { move: deq => [= ?]; subst w'; contradiction. }
        pose proof (bnz_s1 d w' deq dcode). simpl in *. unfold_bind. simpl.
        goal_match_bind_step; try done; try destruct H as [? [eq1 ?]].
        -- rewrite setmE; case: eqP => [eq1' | _].
           ++ destruct no_code_w_s1 as [? [eq2 ?]]. rewrite eq1' in eq1. rewrite eq1 in eq2. simplify_some. contradiction.
           ++ eexists; split; [exact eq1 | done].
        -- destruct H as [[? [eq1 ?]] | eq_alloc]; try (right; done).
           left. rewrite setmE; case: eqP => [eq1' | _].
           ++ destruct no_code_w_s1 as [? [eq2 ?]]. rewrite eq1' in eq1. rewrite eq1 in eq2. simplify_some. contradiction.
           ++ eexists; split; [exact eq1 | done].
      + unfold end_condition in *. intros w0 v0 v0_eq v0_code.
        rewrite eq_s1' in v0_eq. simpl in v0_eq. rewrite setmE in v0_eq.
        move: v0_eq. case: eqP => [eq_w0 | _] v0_eq.
        * move: v0_eq => [= ?]; subst v0; contradiction.
        * destruct (end_s1 w0 v0 v0_eq v0_code); [left | right]; auto. destruct H as [v1 [v1_eq v1_code]].
          exists v1. rewrite eq_s1'. rewrite setmE.
          case: eqP => [eq_next | _]; last (split; done).
          exfalso. rewrite eq_next in v1_eq. destruct no_code_w_s1 as [? [eq no_code]].
          rewrite eq in v1_eq. simplify_some. contradiction.
      + intros w' d deq. subst. simpl in deq.
        rewrite setmE in deq. unfold_match' deq; try convert_eq_op; try simplify_some.
        simpl in v_relevant. left. eapply ((fst (Extra.In_in _ _)) v_relevant).
        eapply col_mem1; eauto.
      + intros w' d e deq dent.
        rewrite eq_s1' in deq. rewrite setmE in deq. unfold_match' deq.
        * exfalso. convert_eq_op. simplify_some. rewrite no_entry in dent. inversion dent.
        * eapply entry_code1; eauto.
      +
        intros w' d deq dcode.
        rewrite eq_s1' in deq. rewrite setmE in deq. unfold_match' deq.
        * exfalso. convert_eq_op. simplify_some. exact: (no_code_v dcode).
        * eapply cvo1; eauto.
      + clear -same_color no_code_v' v_color no_code_w_s3 eq_m3 eq_s3' mem_pref_cond_s3.
        subst s3'.
        move: mem_pref_cond_s3.
        simpl.
        rewrite /memory_prefix_condition => H c w0 v0.
        rewrite setmE.
        case: ifP => /eqP; [| move=> _; apply H].
        move=> -> [] <- color_v _.
        destruct no_code_w_s3 as [d [mem_s3_w no_code]].
        eapply H; eauto. rewrite <- same_color, v_color; eauto.
      + clear -same_color no_code_v' v_color no_code_w_s3 eq_m3 eq_s3' mem_pref_cond_s3'.
        subst s3'.
        move: mem_pref_cond_s3'.
        simpl.
        rewrite /memory_prefix_condition' => H c w0 v0 Hb.
        rewrite setmE.
        case: ifP => /eqP; [| move=> _; apply (H _ _ _ Hb)].
        move=> -> [] <- G.
        destruct no_code_w_s3 as [d [mem_s3_w no_code]].
        specialize (H _ _ _ Hb mem_s3_w G) as [H1 H2].
        split; [ by rewrite -v_color (same_color d (or_intror mem_s3_w)) | exact no_code_v' ].
      + clear -same_color no_code_v' no_code_w_s3 eq_m3 eq_s3' code_pref_cond_s3.
        subst s3'.
        move: code_pref_cond_s3.
        simpl.
        rewrite /code_prefix_condition => H w' v''.
        rewrite setmE. case: ifP => /eqP.
        * move=> ? [] ?; subst. contradiction.
        * move=> _.
          apply H.
      + unfold alloc_empty in *. subst. simpl in *. rewrite setmE.
        case: eqP => [eq_al | _]; last exact alloc_mem_s3.
        exfalso. subst w.
        unfold updm in eq_m3. rewrite alloc_mem_s3 in eq_m3. simpl in eq_m3. inversion eq_m3.
      + intros d w' deq dcode. subst. simpl in deq. rewrite setmE in deq.
        move: deq. case: eqP => [eq_d | _] deq.
        { move: deq => [= ?]; subst w'; contradiction. }
        pose proof (bnz_s3 d w' deq dcode). simpl in *. unfold_bind. simpl.
        goal_match_bind_step; try done; try destruct H as [? [eq1 ?]].
        -- rewrite setmE; case: eqP => [eq1' | _].
           ++ destruct no_code_w_s3 as [? [eq2 ?]]. rewrite eq1' in eq1. rewrite eq1 in eq2. simplify_some. contradiction.
           ++ eexists; split; [exact eq1 | done].
        -- destruct H as [[? [eq1 ?]] | eq_alloc]; try (right; done).
           left. rewrite setmE; case: eqP => [eq1' | _].
           ++ destruct no_code_w_s3 as [? [eq2 ?]]. rewrite eq1' in eq1. rewrite eq1 in eq2. simplify_some. contradiction.
           ++ eexists; split; [exact eq1 | done].
      + unfold end_condition in *. intros w0 v0 v0_eq v0_code.
        rewrite eq_s3' in v0_eq. simpl in v0_eq. rewrite setmE in v0_eq.
        move: v0_eq. case: eqP => [eq_w0 | _] v0_eq.
        * move: v0_eq => [= ?]; subst v0; contradiction.
        * destruct (end_s3 w0 v0 v0_eq v0_code); [left | right]; auto. destruct H as [v1 [v1_eq v1_code]].
          exists v1. rewrite eq_s3'. rewrite setmE.
          case: eqP => [eq_next | _]; last (split; done).
          exfalso. rewrite eq_next in v1_eq. destruct no_code_w_s3 as [? [eq no_code]].
          rewrite eq in v1_eq. simplify_some. contradiction.
      + intros w' d deq. subst. simpl in deq.
        rewrite setmE in deq. unfold_match' deq; try convert_eq_op; try simplify_some.
        rewrite v_color in v_relevant. simpl in v_relevant. left. eapply ((fst (Extra.In_in _ _)) v_relevant).
        eapply col_mem3; eauto.
      + intros w' d e deq dent.
        rewrite eq_s3' in deq. rewrite setmE in deq. unfold_match' deq.
        * exfalso. convert_eq_op. simplify_some. destruct v, d. destruct v_match as [tag_eq ?]. rewrite <- tag_eq in dent.
          rewrite no_entry in dent. inversion dent.
        * eapply entry_code3; eauto.
      +
        intros w' d deq dcode.
        rewrite eq_s3' in deq. rewrite setmE in deq. unfold_match' deq.
        * exfalso. convert_eq_op. simplify_some. exact: (no_code_v' dcode).
        * eapply cvo3; eauto.
      + rewrite eq_s1'. unfold capability_correctness. simpl. intros d q r r_cap.
        destruct r as [r|w'].
        { pose proof (capa_cor1 d q (inl r) r_cap) as cor. destruct cor as [[sv1 [sv2 [col in_m]]] unicity].
          split; [unfold in_stack; eauto|]. intros r' v''. destruct r' as [r'| w']. eapply (unicity (inl _)); eauto.
          rewrite setmE. intros [t' [v''eq t'cap]]. unfold_match' v''eq; [| eapply (unicity (inr _)); eauto].
          convert_eq_op. simplify_some. rewrite t'cap in capa_prop1. destruct capa_prop1 as [limp [rimp ?]].
          eapply rimp; eauto. }
        { rewrite setmE in r_cap. destruct r_cap as [t [dt_eq t_cap]].
          unfold_match' dt_eq.
          - convert_eq_op. simplify_some. rewrite t_cap in capa_prop1. destruct capa_prop1 as [limp [rimp v_in_m]].
            split; auto. intros r' v''. destruct r' as [r'| w']. eapply rimp; eauto.
            rewrite setmE. intros [t' [v''t'_eq t'_capa]]. unfold_match' v''t'_eq; [convert_eq_op; trivial | exfalso].
            eapply limp; eauto.
          - pose proof (capa_cor1 d q (inr w')) as cor. simpl in cor.
            destruct (cor (ex_intro _ t (conj dt_eq t_cap))) as [[sv1 [sv2 [col in_m]]] unicity].
            split; [unfold in_stack; eauto|]. intros r' v''. destruct r' as [r'| w'']. eapply (unicity (inl _)); eauto.
            rewrite setmE. intros [t' [v''eq t'cap]]. unfold_match' v''eq; [| eapply (unicity (inr _)); eauto].
            convert_eq_op. simplify_some. exfalso. rewrite t'cap in capa_prop1. destruct capa_prop1 as [limp rimp].
            eapply (limp _ w' t); eauto. }
      + rewrite eq_s3'. unfold capability_correctness. simpl. intros d q r r_cap.
        destruct r as [r|w'].
        { pose proof (capa_cor3 d q (inl r) r_cap) as cor. destruct cor as [[sv1 [sv2 [col in_m]]] unicity].
          split; [unfold in_stack; eauto|]. intros r' v''. destruct r' as [r'| w']. eapply (unicity (inl _)); eauto.
          rewrite setmE. intros [t' [v''eq t'cap]]. unfold_match' v''eq; [| eapply (unicity (inr _)); eauto].
          convert_eq_op. simplify_some. rewrite t'cap in capa_prop3. destruct capa_prop3 as [limp [rimp ?]].
          eapply rimp; eauto. }
        { rewrite setmE in r_cap. destruct r_cap as [t [dt_eq t_cap]].
          unfold_match' dt_eq.
          - convert_eq_op. simplify_some. rewrite t_cap in capa_prop3. destruct capa_prop3 as [limp [rimp v_in_m]].
            split; auto. intros r' v''. destruct r' as [r'| w']. eapply rimp; eauto.
            rewrite setmE. intros [t' [v''t'_eq t'_capa]]. unfold_match' v''t'_eq; [convert_eq_op; trivial | exfalso].
            eapply limp; eauto.
          - pose proof (capa_cor3 d q (inr w')) as cor. simpl in cor.
            destruct (cor (ex_intro _ t (conj dt_eq t_cap))) as [[sv1 [sv2 [col in_m]]] unicity].
            split; [unfold in_stack; eauto|]. intros r' v''. destruct r' as [r'| w'']. eapply (unicity (inl _)); eauto.
            rewrite setmE. intros [t' [v''eq t'cap]]. unfold_match' v''eq; [| eapply (unicity (inr _)); eauto].
            convert_eq_op. simplify_some. exfalso. rewrite t'cap in capa_prop3. destruct capa_prop3 as [limp rimp].
            eapply (limp _ w' t); eauto. }
      + unfold combined_codes. intros w' d t off comp relevant_comp offset v'_code v'_color.
        remember (addw w' (as_word off)) as w''. subst s1' s3'. simpl.
        repeat rewrite setmE.
        destruct v as [? vt], v' as [? vt']. inversion v_match. subst vt'.
        pose proof (code_left w' d t off comp relevant_comp offset v'_code v'_color) as [impll implr].
        case: (w'' =P w) => [Hc1 | Hc1]; case: (w' =P w) => [Hc2 | Hc2]; simpl; split; intro eq; try simplify_some; subst.
        all: try contradiction.
        * destruct (impll eq) as [? [? eq1]]. destruct no_code_w_s3 as [? [eq2 ?]]. rewrite eq1 in eq2. simplify_some. contradiction.
        * destruct (implr eq) as [? [? eq1]]. destruct no_code_w_s1 as [? [eq2 ?]]. rewrite eq1 in eq2. simplify_some. contradiction.
        * destruct (impll eq) as [d' [decode_d' d'_eq]]. exists d'. split; auto.
          inversion decode_d'; subst.
          -- econstructor; trivial.
          -- eapply decode_match_alloc_JAL; trivial.
          -- eapply decode_match_JAL. exact H. exact H1.
             rewrite setmE. case: eqP => [Heq | _]; last exact H2.
             exfalso. subst w. destruct no_code_w_s1 as [? [eq1 ?]].
             rewrite H2 in eq1. simplify_some. match goal with Hc : is_true (is_code ?t) |- _ => match goal with Hnc : ~ is_true (is_code t) |- _ => exact (Hnc Hc) end end.
             rewrite setmE. case: eqP => [Heq | _]; last exact H3.
             exfalso. subst w. destruct no_code_w_s3 as [? [eq1 ?]].
             rewrite H3 in eq1. simplify_some. rewrite H5 in H4. match goal with Hc : is_true (is_code ?t) |- _ => match goal with Hnc : ~ is_true (is_code t) |- _ => exact (Hnc Hc) end end.
             all: trivial.
        * destruct (implr eq) as [d' [decode_d' d'_eq]]. exists d'. split; auto.
          inversion decode_d'; subst.
          -- econstructor; trivial.
          -- eapply decode_match_alloc_JAL; trivial.
          -- eapply decode_match_JAL. exact H. exact H1.
             rewrite setmE. case: eqP => [Heq | _]; last exact H2.
             exfalso. subst w. destruct no_code_w_s1 as [? [eq1 ?]].
             rewrite H2 in eq1. simplify_some. match goal with Hc : is_true (is_code ?t) |- _ => match goal with Hnc : ~ is_true (is_code t) |- _ => exact (Hnc Hc) end end.
             rewrite setmE. case: eqP => [Heq | _]; last exact H3.
             exfalso. subst w. destruct no_code_w_s3 as [? [eq1 ?]].
             rewrite H3 in eq1. simplify_some. rewrite H5 in H4. match goal with Hc : is_true (is_code ?t) |- _ => match goal with Hnc : ~ is_true (is_code t) |- _ => exact (Hnc Hc) end end.
             all: trivial.
      +  unfold combined_codes. intros w' d t off comp relevant_comp offset v'_code v'_color.
        remember (addw w' (as_word off)) as w''. subst s1' s3'. simpl.
        repeat rewrite setmE.
        destruct v as [? vt], v' as [? vt']. inversion v_match. subst vt'.
        pose proof (code_right w' d t off comp relevant_comp offset v'_code v'_color) as [impll implr].
        case: (w'' =P w) => [Hc | Hc]; simpl; split; intro eq; try simplify_some; subst.
        all: try contradiction.
        destruct (impll eq) as [? [? eq1]]. destruct no_code_w_s3 as [? [eq2 ?]]. rewrite eq1 in eq2. simplify_some. contradiction.
        * destruct (impll eq) as [d' [decode_d' d'_eq]]. exists d'. split; auto.
          inversion decode_d'; subst.
          -- econstructor; trivial.
          -- eapply decode_match_alloc_JAL; trivial.
          -- eapply decode_match_JAL. exact H. exact H1.
             exact H2.
             rewrite setmE. case: eqP => [Heq | _]; last exact H3.
             exfalso. subst w. destruct no_code_w_s3 as [? [eq1 ?]].
             rewrite H3 in eq1. simplify_some. rewrite H5 in H4. match goal with Hc : is_true (is_code ?t) |- _ => match goal with Hnc : ~ is_true (is_code t) |- _ => exact (Hnc Hc) end end.
             all: trivial.
        * destruct (implr eq) as [d' [decode_d' d'_eq]]. exists d'. split; auto.
          inversion decode_d'; subst.
          -- econstructor; trivial.
          -- eapply decode_match_alloc_JAL; trivial.
          -- eapply decode_match_JAL. exact H. exact H1.
             exact H2.
             rewrite setmE. case: eqP => [Heq | _]; last exact H3.
             exfalso. subst w. destruct no_code_w_s3 as [? [eq1 ?]].
             rewrite H3 in eq1. simplify_some. rewrite H5 in H4. match goal with Hc : is_true (is_code ?t) |- _ => match goal with Hnc : ~ is_true (is_code t) |- _ => exact (Hnc Hc) end end.
             all: trivial.
             Unshelve.
             all: simpl; eauto.
             all: unfold ip, ic.
             all: eapply proj1 in Hmergeable_ifaces.
             all: eapply proj2 in Hmergeable_ifaces; eauto.
  Qed.

  Lemma preserves_equiv_left_reg_write :
    forall s1 s2 s3 M s1' s3' r v v'  r1' r3',
      strong_equiv Left M s1 s3
      /\ weak_equiv Right M s2 s3
      /\ common_equiv M s1 s2 s3 ->
      data_match Left (color_of s1) M v v' ->
      capability_correctness' WS_S1 s1 M (vala v ) (taga v ) ->
      capability_correctness' WS_S3 s3 M (vala v') (taga v') ->
      address_correctness Left (vala v) (taga v) (mem s1) ->
      address_correctness Left (vala v') (taga v') (mem s3) ->
      updm (regs s1) r v = Some r1' ->
      updm (regs s3) r v' = Some r3' ->
      s1' = State _ _ (mem s1) r1' (pc s1) tt ->
      s3' = State _ _ (mem s3) r3' (pc s3) tt ->
      strong_equiv Left M s1' s3'
      /\ weak_equiv Right M s2 s3'
      /\ common_equiv M s1' s2 s3'.
  Proof.
    intros s1 s2 s3 M s1' s3' r v v' r1' r3' equiv v_match
      capa_prop1 capa_prop3 correct_v correct_v'  eq_r1 eq_r3 eq_s1' eq_s3'.
    destruct equiv as [strong [weak common]].
    destruct common as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          [mem_pref_cond_s1 [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 [entry_code1 cvo1]]]]]]]
                          [mem_pref_cond_s2 [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 [entry_code2 cvo2]]]]]]]
                          [mem_pref_cond_s3 [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 [entry_code3 cvo3]]]]]]]
                          capa_cor1 capa_cor2 capa_cor3 code_left code_right Hcval wpcc1 wpcc2].
    pose proof (updm_set eq_r1). pose proof (updm_set eq_r3). subst r1' r3'.
    split; [|split].
    - destruct strong as [? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match].
      econstructor; destruct s, s', pc0, pc1; try (rewrite eq_s1' eq_s3'; simpl; auto; done); try (subst; simpl; trivial; done); try congruence.
      + destruct pc_s1_s3 as [? ? ? eq_none|? ? ? ? eq_comp eq_off pc_s1_s3].
        * eapply same_pc_alloc; try rewrite eq_s1'; try rewrite eq_s3'; auto.
        * eapply same_pc_normal. subst. simpl. exact eq_comp.
          subst. simpl. destruct s, pc0. exact eq_off.
          rewrite eq_s1' eq_s3'. simpl. done.
      + subst. intros d w' deq. simpl in *.
        move: deq; rewrite setmE; case: eqP => [_ | _] deq.
        -- move: deq => [= <-]; exact correct_v.
        -- exact (s_reg_cor _ w' deq).
      + subst. intros d w' deq. simpl in *.
        move: deq; rewrite setmE; case: eqP => [_ | _] deq.
        -- move: deq => [= <-]; exact correct_v'.
        -- exact (s'_reg_cor _ w' deq).
      + unfold registers_match in *. rewrite eq_s1' eq_s3'. simpl.
        intros. rewrite setmE. rewrite setmE.
        case: eqP => [_ | _] /=.
        * split; intro eq; inv eq; eexists; split; first [exact v_match | reflexivity].
        * apply reg_match; auto.
    - destruct weak as [? ? s3 color_eq side_s' s_mem_cor s'_mem_cor entry_off  mem_match].
      econstructor; try (rewrite eq_s3'; simpl; auto; done); try congruence.
      destruct s, s3, pc0, pc1. subst. simpl. auto.
      trivial.
    - eapply common_equiv_def with (n := n) (c := c0);
        try ((rewrite eq_s1' eq_s3' || rewrite eq_s1' || rewrite eq_s3'); simpl; auto; done); try congruence; try done.
      all: try (match goal with |- pc_code_color _ =>
                  rewrite eq_s1'; apply: (pc_code_color_cong (s := s1));
                  first [ exact wpcc1 | reflexivity | done ] end).
      + subst. unfold register_domm. simpl. rewrite domm_set.
        unfold register_domm in *. simpl in *. unfold updm in eq_r1. unfold_match' eq_r1.
        clear -Heqa reg_domm1.
        rewrite fsetU1in //= mem_domm //=.
      + subst. unfold register_domm. simpl. rewrite domm_set.
        unfold register_domm in *. simpl in *. unfold updm in eq_r3. unfold_match' eq_r3.
        clear -Heqa reg_domm3.
        rewrite fsetU1in //= mem_domm //=.
      + rewrite eq_s1'. unfold capability_correctness. simpl. intros d q w w_cap.
        destruct w as [r'|w'].
        { rewrite setmE in w_cap. unfold_match' w_cap.
          - convert_eq_op. simplify_some. destruct capa_prop1 as [limp [rimp v_in_m]].
            split; auto. intros r' v''. destruct r' as [r'| w'].
            rewrite setmE. intro r_r'_eq. unfold_match' r_r'_eq; convert_eq_op; trivial.
            exfalso. eapply rimp; eauto.
            intros [t' [v''eq t'capa]]. eapply limp; eauto.
          - pose proof (capa_cor1 d q (inl r') w_cap) as [is_in cor]. simpl in cor.
            split; auto. intros w' v''. destruct w' as [r''|w'].
            { intro eq. rewrite setmE in eq. unfold_match' eq; convert_eq_op; try simplify_some.
              exfalso. unfold capability_correctness' in capa_prop1. simpl in capa_prop1.
              pose proof ((fst (snd capa_prop1)) d r') as eq. eapply eq; eauto.
              eapply (cor (inl _)); eauto. } eapply (cor (inr _)). }
        { pose proof (capa_cor1 d q (inr w') w_cap) as cor. destruct cor as [[sv1 [sv2 [col in_m]]] unicity].
          split; [unfold in_stack; eauto|]. intros r' v''. destruct r' as [r'| w''].
          rewrite setmE. intros v''eq. unfold_match' v''eq; [| eapply (unicity (inl _)); eauto].
          convert_eq_op. simplify_some. destruct capa_prop1 as [limp [rimp ?]].
          destruct w_cap as [t [teq tcapa]]. eapply limp; eauto.
          eapply (unicity (inr _)); eauto.  }
      + rewrite eq_s3'. unfold capability_correctness. simpl. intros d q w w_cap.
        destruct w as [r'|w'].
        { rewrite setmE in w_cap. unfold_match' w_cap.
          - convert_eq_op. simplify_some. destruct capa_prop3 as [limp [rimp v_in_m]].
            split; auto. intros r' v''. destruct r' as [r'| w'].
            rewrite setmE. intro r_r'_eq. unfold_match' r_r'_eq; convert_eq_op; trivial.
            exfalso. eapply rimp; eauto.
            intros [t' [v''eq t'capa]]. eapply limp; eauto.
          - pose proof (capa_cor3 d q (inl r') w_cap) as [is_in cor]. simpl in cor.
            split; auto. intros w' v''. destruct w' as [r''|w'].
            { intro eq. rewrite setmE in eq. unfold_match' eq; convert_eq_op; try simplify_some.
              exfalso. unfold capability_correctness' in capa_prop3. simpl in capa_prop3.
              pose proof ((fst (snd capa_prop3)) d r') as eq. eapply eq; eauto.
              eapply (cor (inl _)); eauto. } eapply (cor (inr _)). }
        { pose proof (capa_cor3 d q (inr w') w_cap) as cor. destruct cor as [[sv1 [sv2 [col in_m]]] unicity].
          split; [unfold in_stack; eauto|]. intros r' v''. destruct r' as [r'| w''].
          rewrite setmE. intros v''eq. unfold_match' v''eq; [| eapply (unicity (inl _)); eauto].
          convert_eq_op. simplify_some. destruct capa_prop3 as [limp [rimp ?]].
          destruct w_cap as [t [teq tcapa]]. eapply limp; eauto.
          eapply (unicity (inr _)); eauto.  }
  Qed.


  Lemma reg_read_update_id :
    forall (st : state) (k : reg mt) (a : atom (mword mt) (tag_type ttypes R)),
      regs st k = Some a ->
      next_state_do_update st (taga a) (RegRead k) = Some st.
  Proof.
    move=> st k [va ta] Hk. rewrite /next_state_do_update /= Hk /= /updm Hk /=.
    have Es : setm (regs st) k (va@ta) = regs st.
    { apply/eq_fmap => k'; rewrite setmE; case: eqP => [-> | _]; by rewrite ?Hk. }
    rewrite Es; clear Hk Es; by case: st.
  Qed.

  Local Opaque next_state_do_update.
  Lemma reg_clear_do_updates_id :
    forall (l : seq nat) (st : state) (k0 : reg mt)
           (a0 : atom (mword mt) (tag_type ttypes R))
           (tags : hseq (tag_type ttypes) (nseq (S (size l)) R)),
      regs st k0 = Some a0 ->
      reg_clear_list_aux l (regs st) (taga a0) = Some tags ->
      next_state_do_updates st tags
        (RegRead k0 :: map (fun n => RegRead (as_word (ssrint.Posz n))) l) = Some st.
  Proof.
    elim => [|e l' IH] st k0 a0 tags Hk0.
    - move=> /= [= <-] /=. by rewrite (reg_read_update_id Hk0).
    - rewrite /=.
      case Hve : (regs st (as_word (ssrint.Posz e))) => [ve|] //=.
      case Hl'' : (reg_clear_list_aux l' (regs st) (taga ve)) => [l''|] //=.
      move=> [= <-] /=. rewrite (reg_read_update_id Hk0) /=.
      exact: (IH st (as_word (ssrint.Posz e)) ve l'' Hve Hl'').
  Qed.

  Local Transparent next_state_do_update.
  Lemma mem_read_update_id :
    forall (st : state) (w : mword mt) (a : atom (mword mt) (tag_type ttypes M)),
      mem st w = Some a ->
      next_state_do_update st (taga a) (MemRead w) = Some st.
  Proof.
    move=> st w [va ta] Hw. rewrite /next_state_do_update /= Hw /= /updm Hw /=.
    have Es : setm (mem st) w (va@ta) = mem st.
    { apply/eq_fmap => w'; rewrite setmE; case: eqP => [-> | _]; by rewrite ?Hw. }
    rewrite Es; clear Hw Es; by case: st.
  Qed.

  Lemma register_index_bound : (20 < 2 ^ reg_field_size mt)%nat.
  Proof. by rewrite reg_field_size_mt. Qed.

  Lemma reg_clear_list_aux_setm_irrel :
    forall (l : seq nat) (rs : {fmap reg mt -> atom (mword mt) (tag_type ttypes R)})
           (k : reg mt) (v : atom (mword mt) (tag_type ttypes R)) (top : tag_type ttypes R),
      (forall n, n \in l -> as_word (ssrint.Posz n) <> k) ->
      reg_clear_list_aux l (setm rs k v) top = reg_clear_list_aux l rs top.
  Proof.
    elim => [|e l' IH] rs k v top Hne //=.
    have Hek : as_word (ssrint.Posz e) <> k by (apply: (Hne e); rewrite in_cons eqxx).
    rewrite setmE (introF eqP Hek) /=.
    case: (rs (as_word (ssrint.Posz e))) => [a|] //=.
    by rewrite IH // => n Hn; apply: Hne; rewrite in_cons Hn orbT.
  Qed.

  Local Transparent next_state_do_update.

  Lemma ndsu_cons :
    forall (st : state) (tk : tag_kind) (tks : seq tag_kind)
           (t : tag_type ttypes tk) (tags : hseq (tag_type ttypes) tks)
           (u : update) (us : seq update),
      next_state_do_updates st (HSeqCons t tags : hseq (tag_type ttypes) (tk :: tks)) (u :: us)
      = obind (fun st' => next_state_do_updates st' tags us)
              (next_state_do_update st t u).
  Proof. by []. Qed.

  Lemma reg_clear_list_aux_cons :
    forall (e : nat) (l' : seq nat)
           (rs : {fmap reg mt -> atom (mword mt) (tag_type ttypes R)})
           (top : tag_type ttypes R),
      reg_clear_list_aux (e :: l') rs top
      = obind (fun v => obind (fun l'' => Some (HSeqCons top l''))
                              (reg_clear_list_aux l' rs (taga v)))
              (rs (as_word (ssrint.Posz e))).
  Proof. move=> e l' rs top /=. by case: (rs (as_word (ssrint.Posz e))). Qed.

  Local Transparent next_state_do_updates reg_clear_list_aux.

  Lemma reg_clear_list_head :
    forall (rs : {fmap reg mt -> atom (mword mt) (tag_type ttypes R)}) t l,
      reg_clear_list rs t = Some l -> hshead l = t.
  Proof.
    Local Opaque reg_clear_list_aux.
    move=> rs t l. rewrite /reg_clear_list /reg_list reg_clear_list_aux_cons.
    case: (rs (as_word (ssrint.Posz 1))) => [v1|] //=.
    case: (reg_clear_list_aux [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19] rs (taga v1)) => [ll|] //=.
    move=> [= Hl]. by rewrite -Hl.
  Qed.
  Local Transparent reg_clear_list_aux.

  Lemma reg_clear_list_aux_total :
    forall (l : seq nat) (rs : {fmap reg mt -> atom (mword mt) (tag_type ttypes R)})
           (t : tag_type ttypes R),
      (forall e, e \in l -> exists a, rs (as_word (ssrint.Posz e)) = Some a) ->
      exists ll, reg_clear_list_aux l rs t = Some ll.
  Proof.
    elim => [|e l' IH] rs t Hmem.
    - by exists (HSeqCons t HSeqNil).
    - rewrite reg_clear_list_aux_cons.
      have [a Ha] : exists a, rs (as_word (ssrint.Posz e)) = Some a
        by (apply: (Hmem e); rewrite in_cons eqxx).
      rewrite Ha /=.
      have Hmem' : forall e', e' \in l' -> exists a0, rs (as_word (ssrint.Posz e')) = Some a0
        by (move=> e' He'; apply: Hmem; rewrite in_cons He' orbT).
      have [ll Hll] := IH rs (taga a) Hmem'.
      by rewrite Hll /=; exists (HSeqCons t ll).
  Qed.

  Lemma reg_clear_list_total :
    forall (rs : {fmap reg mt -> atom (mword mt) (tag_type ttypes R)}) (t : tag_type ttypes R),
      domm rs = fset (ra :: [seq word_of_nat i | i <- reg_list]) ->
      exists l, reg_clear_list rs t = Some l.
  Proof.
    move=> rs t Hdom. rewrite /reg_clear_list. apply: reg_clear_list_aux_total.
    move=> e He. apply/dommP. rewrite Hdom in_fset in_cons.
    apply/orP; right. apply/mapP. by exists e.
  Qed.

  Lemma andw_last_component_prefix: forall C (m: {fmap mword mt -> atom (mword mt) (tag_type ttypes M)}),
      andw
        (List.last (List.filter (fun mw => andw mw (@mask mt NC) == @component_memory_prefix mt NC C)
                      (domm m))
           (@component_memory_prefix mt NC C))
        (@mask mt NC) = @component_memory_prefix mt NC C.
  Proof.
    intros C m.
    generalize (domm m) as fs.
    destruct fs as [l sorted]. simpl. clear sorted.
    induction l.
    - simpl. unfold mask, component_memory_prefix.
      (* Set Printing Implicit. *)
      replace (@andw 32) with (@andw (word_size mt)) by reflexivity.
      pose proof shlw_all_one (k := (word_size mt))
        (as_word C)
        (as_word (ssrint.Posz (word_size mt - NC))).
      rewrite <- H at 2.
      repeat (try (eapply congr2 || eapply congr1)).
      1-3,5-7: reflexivity.
      clear. remember (word_size mt) as n. clear.
      induction n; auto. simpl.
      unfold expn in *. simpl. rewrite <- IHn.
      destruct n; auto; simpl.
    - simpl.
      case: ifP => /eqP H.
      + simpl.
        match goal with |- context [List.filter ?p l] =>
          move: IHl; generalize (List.filter p l) as fl; intros fl IHl end.
        destruct fl; [exact H | exact IHl].
      + eauto.
  Qed.

  Lemma is_relevant_comp_of_side i c :
    (c \in domm ip) || (c \in domm ic) -> side_of c = i -> is_relevant_comp i c.
  Proof.
    rewrite /is_relevant_comp /side_of => Hval.
    case: i; case Hp: (c \in domm ip) => //=.
    by move=> _; move: Hval; rewrite Hp orFb.
  Qed.

  Lemma match_mem_pref_condition_filter_eq i m s s' c:
    is_relevant_comp i c ->
    memory_match i m s s' ->
    memory_prefix_condition' (mem s) ->
    memory_prefix_condition' (mem s') ->
    List.filter
      (fun mw : word 32 =>
         andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz (1 + c)))
      (domm (mem s)) =
      List.filter
        (fun mw : word 32 =>
           andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz (1 + c)))
        (domm (mem s')).
  Proof.
    move=> Hrel.
    have Hc : 1 + c < 2 ^ NC.
    { apply: colors_bounded; move: Hrel; rewrite /is_relevant_comp /ip /ic.
      by case: i => H; rewrite H ?orbT. }
    move=> Hmatch Hmpcs Hmpcs'.
    set p := (fun mw : word 32 =>
                andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz (1 + c))).
    have FE : forall l : seq (word 32), List.filter p l = [seq mw <- l | p mw]
      by elim => [|x l IH] //=; rewrite IH.
    rewrite !FE.
    apply: (irr_sorted_eq (leT := @Ord.lt _) (@Ord.lt_trans _) (@Ord.ltxx _)).
    - apply: (sorted_filter (@Ord.lt_trans _)); apply: (valP (domm (mem s))).
    - apply: (sorted_filter (@Ord.lt_trans _)); apply: (valP (domm (mem s'))).
    - move=> w; rewrite !mem_filter.
      case Hpw: (p w) => //=.
      move: Hpw; rewrite /p => /eqP Hpw.
      apply/idP/idP => /dommP [d Hd]; apply/dommP.
      + have [Hcol Hnc] := Hmpcs c w d Hc Hd Hpw.
        have Hrel' : is_relevant_comp i (color (taga d)) by rewrite Hcol.
        have [_ Hfwd] := Hmatch w d Hnc Hrel'.
        by have [d' [_ Hd']] := Hfwd Hd; exists d'.
      + have [Hcol Hnc] := Hmpcs' c w d Hc Hd Hpw.
        have Hrel' : is_relevant_comp i (color (taga d)) by rewrite Hcol.
        have [Hbwd _] := Hmatch w d Hnc Hrel'.
        by have [d' [_ Hd']] := Hbwd Hd; exists d'.
  Qed.

  Lemma mask_alloc_label:
          andw (word_of_nat alloc_label) (@mask mt NC) = 0%w.
  Proof.
    apply: andw_mask_low.
    rewrite valw_as_word modn_small;
      [ exact: alloc_label_lt_word_NC
      | apply: (leq_trans alloc_label_lt_word_NC); rewrite leq_exp2l //; exact: leq_subr ].
  Qed.

  Lemma swcast_word_of_nat_alloc_label :
    @swcast _ (word_size mt) (@word_of_nat (imm_size mt) alloc_label) = word_of_nat alloc_label.
  Proof.
    Local Transparent swcast word_of_nat as_word.
    unfold swcast, word_of_nat. simpl. unfold alloc_label. rewrite div.modn_small; trivial.
  Qed.
  Local Opaque swcast word_of_nat as_word.

  Global Opaque mt.
  Global Opaque word_size.
  Global Opaque reg_field_size.
  Global Opaque imm_size.

  Strategy opaque [mt word_size reg_field_size imm_size].

  Lemma color_of_pc_tag : forall st, color_of st = match taga (pc st) with Level _ c => c end.
  Proof. by case=> ? ? [? ?] ?. Qed.

  Lemma congr2 {A B C} (f : A -> B -> C) (a a' : A) (b b' : B) :
    a = a' -> b = b' -> f a b = f a' b'.
  Proof. by move=> -> ->. Qed.

  Lemma unionm_get {T : ordType} {S : Type} (m1 m2 : {fmap T -> S}) k v :
    unionm m1 m2 k = Some v -> m1 k = Some v \/ (m1 k = None /\ m2 k = Some v).
  Proof.
    rewrite unionmE; case: (m1 k) => [a|] /= H; [left|right].
    - exact H.
    - split; [reflexivity | exact H].
  Qed.

  Lemma unionm_getL {T : ordType} {S : Type} (m1 m2 : {fmap T -> S}) k v :
    m1 k = Some v -> unionm m1 m2 k = Some v.
  Proof. move=> H; rewrite unionmE H //. Qed.

  Lemma alloc_block_const_value {T : ordType} {S : eqType}
        (f : nat -> T) (a : S) (k : nat) (w : T) (d : S) :
    mkfmap (mkseq (fun n => (f n, a)) k) w = Some d -> d = a.
  Proof.
    move=> H; move/mkfmap_Some: H; rewrite /mkseq => /mapP[x _ [= _ ->]] //.
  Qed.

  Lemma component_memory_prefix_zero :
    @component_memory_prefix mt NC (ssrint.Posz 0) = (0%w : word (word_size mt)).
  Proof. rewrite /component_memory_prefix. apply shlw_zero. Qed.

  Opaque mask component_memory_prefix.
  Opaque unionm setm mkfmap mkfmapfp.

  Ltac xblk H :=
    try (match goal with
         | Hb : ?b = mkfmap (mkseq _ _) |- _ =>
             match type of H with context[b] => rewrite Hb in H end
         end).
  Ltac xblkc H := xblk H; move/alloc_block_const_value in H.

  Lemma alloc_fun_strong:
    forall s1 s2 s3 M s1' s3',
      strong_equiv Left M s1 s3
      /\ weak_equiv Right M s2 s3
      /\ common_equiv M s1 s2 s3 ->
      alloc_fun s1 (NC := NC) = Some s1' ->
      alloc_fun s3 (NC := NC) = Some s3' ->
      strong_equiv Left M s1' s3'.
  Proof.
    import_context.

    intros s1 s2 s3 M s1' s3' equiv eq_s1' eq_s3'.
    destruct equiv as [strong [weak common]].
    unfold alloc_fun in eq_s1', eq_s3'; cbv zeta in eq_s1', eq_s3'.
    apply obind_inv in eq_s1'; destruct eq_s1' as (a1 & Heqa4 & eq_s1'); symmetry in Heqa4.
    apply obind_inv in eq_s1'; destruct eq_s1' as (wj1 & Hg & eq_s1');
      unfold is_jump in Hg; destruct (taga a1) eqn:Heqa7; try discriminate Hg;
      symmetry in Heqa7; clear Hg wj1.
    apply obind_inv in eq_s1'; destruct eq_s1' as (ret1 & Hret1 & eq_s1').
    apply obind_inv in eq_s1'; destruct eq_s1' as (uret1 & Hretchk1 & eq_s1');
      move: Hretchk1; case: ifP => Hretcol1 Hretchk1; last by []; clear uret1 Hretchk1.
    apply obind_inv in eq_s1'; destruct eq_s1' as (sz1 & Heqa6 & eq_s1'); destruct sz1 as [v' tg1].
    apply obind_inv in eq_s1'; destruct eq_s1' as (wo1 & Hg & eq_s1');
      unfold is_other in Hg; destruct tg1; try discriminate Hg; clear Hg wo1; symmetry in Heqa6.
    apply obind_inv in eq_s1'; destruct eq_s1' as (n' & Hg & eq_s1');
      destruct (int_of_word (vala (v'@Other))) as [m1|] eqn:Heqa3; try rewrite Heqa3 in Hg; simpl in Hg;
        [ move: Hg => [= ?]; subst m1 | discriminate Hg ];
      cbn [vala] in Heqa3; symmetry in Heqa3.
    apply obind_inv in eq_s1'; destruct eq_s1' as (uchk1 & Hszchk1 & eq_s1').
    destruct (leq (n' + 1) (expn 2 (word_size mt - NC))) eqn:Hszbound1;
      [ clear uchk1 Hszchk1 | discriminate Hszchk1 ].
    match type of eq_s1' with (if ?b then _ else _) = _ => destruct b eqn:Heqa10 end;
      [ discriminate eq_s1' | ]; symmetry in Heqa10.
    apply obind_inv in eq_s1'; destruct eq_s1' as (ad1 & Hg & eq_s1');
      apply obind_inv in Hg; destruct Hg as (p2 & Heqa13 & Hg); symmetry in Heqa13;
      move: Hg => [= ?]; subst ad1.
    apply obind_inv in eq_s1'; destruct eq_s1' as (rg1 & Hg & eq_s1');
      move: (updm_set Hg) => Hg2; subst rg1; clear Hg.
    apply obind_inv in eq_s3'; destruct eq_s3' as (ra3 & Heqa & eq_s3'); destruct ra3 as [v tgr3].
    apply obind_inv in eq_s3'; destruct eq_s3' as (wj3 & Hg & eq_s3');
      unfold is_jump in Hg; destruct tgr3; try discriminate Hg; clear Hg wj3; symmetry in Heqa.
    apply obind_inv in eq_s3'; destruct eq_s3' as (ret3 & Hret3 & eq_s3').
    apply obind_inv in eq_s3'; destruct eq_s3' as (uret3 & Hretchk3 & eq_s3');
      move: Hretchk3; case: ifP => Hretcol3 Hretchk3; last by []; clear uret3 Hretchk3.
    apply obind_inv in eq_s3'; destruct eq_s3' as (a0 & Heqa1 & eq_s3'); symmetry in Heqa1.
    apply obind_inv in eq_s3'; destruct eq_s3' as (wo3 & Hg & eq_s3');
      unfold is_other in Hg; destruct (taga a0) eqn:Heqa8; try discriminate Hg;
      symmetry in Heqa8; clear Hg wo3.
    apply obind_inv in eq_s3'; destruct eq_s3' as (n1 & Hg & eq_s3');
      destruct (int_of_word (vala a0)) as [m3|] eqn:Heqa12; try rewrite Heqa12 in Hg; simpl in Hg;
        [ move: Hg => [= ?]; subst m3 | discriminate Hg ]; symmetry in Heqa12.
    apply obind_inv in eq_s3'; destruct eq_s3' as (uchk3 & Hszchk3 & eq_s3').
    destruct (leq (n1 + 1) (expn 2 (word_size mt - NC))) eqn:Hszbound3;
      [ clear uchk3 Hszchk3 | discriminate Hszchk3 ].
    match type of eq_s3' with (if ?b then _ else _) = _ => destruct b eqn:Heqa9 end;
      [ discriminate eq_s3' | ]; symmetry in Heqa9.
    apply obind_inv in eq_s3'; destruct eq_s3' as (ad3 & Hg & eq_s3');
      apply obind_inv in Hg; destruct Hg as (p1 & Heqa11 & Hg); symmetry in Heqa11;
      move: Hg => [= ?]; subst ad3.
    apply obind_inv in eq_s3'; destruct eq_s3' as (rg3 & Hg & eq_s3');
      move: (updm_set Hg) => Hg2; subst rg3; clear Hg.
    inversion common as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          [mem_pref_cond_s1 [mem_pref_cond_s1' [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 [entry_code1 cvo1]]]]]]]]
                          [mem_pref_cond_s2 [mem_pref_cond_s2' [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 [entry_code2 cvo2]]]]]]]]
                          [mem_pref_cond_s3 [mem_pref_cond_s3' [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 [entry_code3 cvo3]]]]]]]]
                          capa_cor1 capa_cor2 capa_cor3 code_left code_right Hcval wpcc1 wpcc2].
    subst m s0 s4 s5.
    assert (n1 = n').
    { destruct strong as [? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match].
      destruct (reg_match (as_word (ssrint.Posz 17)) v'@Other) as [_ impl].
      destruct (impl (esym Heqa6)) as [? [dmatch eq1]]. simpl in *.
      rewrite eq1 in Heqa1. inv Heqa1.
      destruct x.
      inv dmatch. simpl in *.
      clear -Heqa3 Heqa12.
      congruence. }
    subst n1.
    set blk1 := (mkfmap (mkseq _ n')) in eq_s1'.
    try (set blk3 := (mkfmap (mkseq _ n')) in eq_s3').
    pose proof (erefl blk1) as Hblk1; unfold blk1 in Hblk1 at 2.
    try (pose proof (erefl blk3) as Hblk3; unfold blk3 in Hblk3 at 2).
    clearbody blk1; try clearbody blk3.
    move: eq_s1' => [= Hs1]; subst s1'.
    try (move: eq_s3' => [= Hs3]; subst s3').
    destruct strong as [? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match].
      econstructor; try (destruct s, s', pc0, pc1; try (rewrite eq_s1' eq_s3'; simpl; auto; done); try congruence; simpl; done).
      + pose proof ((fst (reg_match _ v@InternalJump)) (esym Heqa)) as [d' [d'match d'eq]].
        have Hd : Some a1 = Some d' by (transitivity (regs s (as_word (ssrint.Posz 4))); [exact Heqa4 | exact d'eq]).
        move: Hd => [= ?]; subst a1. destruct d' as [? taga1].
        destruct d'match as [? ?]. subst taga1. oapp_False.
        pose proof (s_reg_cor _ _ (esym Heqa4)). destruct H as [? [eq ?]].
        eapply same_pc_normal.
        * split.
          -- rewrite ?unionmE; cbn [Symbolic.pc Types.vala]; rewrite eq /=; reflexivity.
          --
             have Hic1 : is_code (taga ret1) by case/andP: Hretcol1 => Hic _.
             rewrite eq in Hret1. case: Hret1 => ->. exact: Hic1.
        * match goal with |- get_offset _ (color_of ?st) = _ => rewrite (color_of_pc_tag st) end.
          cbn [Symbolic.pc Types.taga]. rewrite -(color_of_pc_tag s). exact (esym HeqH).
        * cbn [Symbolic.pc Types.vala]; exact H0.
      + intros d w rel d_eq.
        rewrite /address_correctness.
        case Et: (vtag (taga d)) => [r| | |] //.
        all: cbn [Symbolic.mem] in d_eq.
        all: apply unionm_get in d_eq;
             case: d_eq => [d_eq | [_ d_eq]];
               last (xblkc d_eq; subst d; discriminate Et).
        all: pose proof (s_mem_cor d w rel d_eq) as Hac; rewrite Et in Hac.
        all: destruct Hac as [vv [mem_s_v Hv]].
        all: exists vv; split; [cbn [Symbolic.mem]; apply unionm_getL; exact mem_s_v | exact Hv].
      + intros d w rel d_eq.
        rewrite /address_correctness.
        case Et: (vtag (taga d)) => [r| | |] //.
        all: cbn [Symbolic.mem] in d_eq.
        all: apply unionm_get in d_eq;
             case: d_eq => [d_eq | [_ d_eq]];
               last (xblkc d_eq; subst d; discriminate Et).
        all: pose proof (s'_mem_cor d w rel d_eq) as Hac; rewrite Et in Hac.
        all: destruct Hac as [vv [mem_s_v Hv]].
        all: exists vv; split; [cbn [Symbolic.mem]; apply unionm_getL; exact mem_s_v | exact Hv].
      + intros col w' w'' d d' proc l l' rel eqw' eqw'' dcode d'code dcol d'col d_e_eq d'_e_eq.
        cbn [Symbolic.mem] in eqw', eqw''.
        apply unionm_get in eqw';
          case: eqw' => [eqw' | [_ eqw']];
          last (xblkc eqw'; subst d; discriminate dcode).
        apply unionm_get in eqw'';
          case: eqw'' => [eqw'' | [_ eqw'']];
          last (xblkc eqw''; subst d'; discriminate d'code).
        exact (entry_off col w' w'' d d' proc l l' rel eqw' eqw'' dcode d'code dcol d'col d_e_eq d'_e_eq).
      + intros d w d_eq.
        rewrite /address_correctness.
        case Et: (taga d) => [r| | |] //.
        all: move: d_eq; rewrite setmE.
        all: case: eqP => [_ | _] d_eq.
        1,3: move: d_eq => [= Hd]; rewrite -Hd in Et; discriminate Et.
        all: pose proof (s_reg_cor d w d_eq) as Hac; rewrite Et in Hac.
        all: destruct Hac as [vv [mem_s_v Hv]].
        all: exists vv; split; [apply unionm_getL; exact mem_s_v | exact Hv].
      + intros d w d_eq.
        rewrite /address_correctness.
        case Et: (taga d) => [r| | |] //.
        all: move: d_eq; rewrite setmE.
        all: case: eqP => [_ | _] d_eq.
        1,3: move: d_eq => [= Hd]; rewrite -Hd in Et; discriminate Et.
        all: pose proof (s'_reg_cor d w d_eq) as Hac; rewrite Et in Hac.
        all: destruct Hac as [vv [mem_s_v Hv]].
        all: exists vv; split; [apply unionm_getL; exact mem_s_v | exact Hv].
      + intros w d no_code rel.
        cbn [Symbolic.mem].
        split.
        * move=> H; apply unionm_get in H; case: H => [H | [Hs'None Hfresh]].
          -- destruct (mem_match w d no_code rel) as [impl _].
             destruct (impl H) as [d' [d'match d'eq]].
             exists d'; split; [exact d'match | apply unionm_getL; exact d'eq].
          --
             have w_prefix : andw w (@mask mt NC)
                             = @component_memory_prefix mt NC (ssrint.Posz (1 + c0)).
             { xblk Hfresh; clear -Hfresh Heqa9 tag_pc3 Hszbound1 Hszbound3.
               symmetry in Heqa9.
               move: Heqa9 => /negb_false_iff /eqP; rewrite tag_pc3 => /= Hend.
               move: (Hfresh) => /mkfmap_Some; rewrite /mkseq tag_pc3 => /mapP[x x_in_iota] [= -> _] /=.
               pose proof (andw_last_component_prefix (ssrint.Posz (1 + c0)) (mem s')) as Hstart.
               eapply mask_range; [ by [exact Hszbound1 | exact Hszbound3] | exact Hstart | exact Hend | exact x_in_iota ]. }
             have Hcs : color_of s = c0 by rewrite (color_of_pc_tag s) tag_pc1.
             have side_c0 : side_of c0 = Left by rewrite -Hcs.
             have HsNone : mem s w = None.
             { clear -w_prefix mem_pref_cond_s1' mem_match Hs'None side_c0.
               case E: (mem s w) => [a|]; last by []. exfalso.
               have Hin : c0 \in domm ip.
               { case Hd: (c0 \in domm ip); first reflexivity.
                 have Hs := side_c0. rewrite /side_of Hd /= in Hs. discriminate Hs. }
               have Hbnd : 1 + c0 < 2 ^ NC.
               { apply: colors_bounded. apply/orP. by left. }
               have [color_a no_code_a] := mem_pref_cond_s1' c0 w a Hbnd E w_prefix.
               have Hrel : is_relevant_comp Left (color (taga a)).
               { rewrite color_a. move: side_c0.
                 by rewrite /side_of /is_relevant_comp; case: (c0 \in domm ip). }
               have [d' [_ Hd'eq]] := proj2 (mem_match w a no_code_a Hrel) E.
               by rewrite Hs'None in Hd'eq. }
             exists d. split.
             ++
                xblk Hfresh; move: Hfresh => /alloc_block_const_value ->. by repeat split.
             ++
                abstract (
                  rewrite unionmE HsNone /=;
                  rewrite -Hfresh;
                  apply congr2; last by [];
                  try rewrite Hblk1; try rewrite Hblk3;
                  apply congr1;
                  apply congr2; last by [];
                  apply FunctionalExtensionality.functional_extensionality => x;
                  rewrite tag_pc1 tag_pc3 /=;
                  apply congr2; last by [];
                  congr (_ + _)%w;
                  congr (List.last _ _);
                  eapply match_mem_pref_condition_filter_eq with (i := Left);
                    [ by move: side_c0; rewrite /is_relevant_comp /side_of; case: (c0 \in domm ip)
                    | exact mem_match | exact mem_pref_cond_s1' | exact mem_pref_cond_s3' ]).
        * move=> H; apply unionm_get in H; case: H => [H | [HsNone Hfresh]].
          -- destruct (mem_match w d no_code rel) as [_ impl].
             destruct (impl H) as [d' [d'match d'eq]].
             exists d'; split; [exact d'match | apply unionm_getL; exact d'eq].
          --
             have w_prefix : andw w (@mask mt NC)
                             = @component_memory_prefix mt NC (ssrint.Posz (1 + c0)).
             { xblk Hfresh; clear -Hfresh Heqa10 tag_pc1 Hszbound1 Hszbound3.
               symmetry in Heqa10.
               move: Heqa10 => /negb_false_iff /eqP; rewrite tag_pc1 => /= Hend.
               move: (Hfresh) => /mkfmap_Some; rewrite /mkseq tag_pc1 => /mapP[x x_in_iota] [= -> _] /=.
               pose proof (andw_last_component_prefix (ssrint.Posz (1 + c0)) (mem s)) as Hstart.
               eapply mask_range; [ by [exact Hszbound1 | exact Hszbound3] | exact Hstart | exact Hend | exact x_in_iota ]. }
             have Hcs : color_of s = c0 by rewrite (color_of_pc_tag s) tag_pc1.
             have side_c0 : side_of c0 = Left by rewrite -Hcs.
             have Hs'None : mem s' w = None.
             { clear -w_prefix mem_pref_cond_s3' mem_match HsNone side_c0.
               case E: (mem s' w) => [a|]; last by []. exfalso.
               have Hin : c0 \in domm ip.
               { case Hd: (c0 \in domm ip); first reflexivity.
                 have Hs := side_c0. rewrite /side_of Hd /= in Hs. discriminate Hs. }
               have Hbnd : 1 + c0 < 2 ^ NC.
               { apply: colors_bounded. apply/orP. by left. }
               have [color_a no_code_a] := mem_pref_cond_s3' c0 w a Hbnd E w_prefix.
               have Hrel : is_relevant_comp Left (color (taga a)).
               { rewrite color_a. move: side_c0.
                 by rewrite /side_of /is_relevant_comp; case: (c0 \in domm ip). }
               have [d' [_ Hd'eq]] := proj1 (mem_match w a no_code_a Hrel) E.
               by rewrite HsNone in Hd'eq. }
             exists d. split.
             ++ xblk Hfresh; move: Hfresh => /alloc_block_const_value ->. by repeat split.
             ++ abstract (
                  rewrite unionmE Hs'None /=;
                  rewrite -Hfresh;
                  apply congr2; last by [];
                  try rewrite Hblk1; try rewrite Hblk3;
                  apply congr1;
                  apply congr2; last by [];
                  apply FunctionalExtensionality.functional_extensionality => x;
                  rewrite tag_pc1 tag_pc3 /=;
                  apply congr2; last by [];
                  congr (_ + _)%w;
                  congr (List.last _ _);
                  symmetry;
                  eapply match_mem_pref_condition_filter_eq with (i := Left);
                    [ by move: side_c0; rewrite /is_relevant_comp /side_of; case: (c0 \in domm ip)
                    | exact mem_match | exact mem_pref_cond_s1' | exact mem_pref_cond_s3' ]).
      + intros w d.
        cbn [Symbolic.regs].
        have G : p1.1 = p2.1.
        { rewrite tag_pc1 in Heqa13; rewrite tag_pc3 in Heqa11.
          have c0_Left : is_relevant_comp Left c0.
          { simpl. clear -side_eq tag_pc1.
            unfold side_of in side_eq.
            destruct s as [? ? [] ?]; simpl in *; subst.
            case: (c0 \in domm ip) side_eq => //. }
          clear -Heqa11 Heqa13 mem_match c0_Left mem_pref_cond_s1' mem_pref_cond_s3'.
          move: Heqa11 Heqa13; rewrite /mkseq /=.
          case: n' => // _ [= ->] [= ->] /=.
          congr (_ + _)%w; congr (List.last _ _).
          symmetry.
          eapply match_mem_pref_condition_filter_eq with (i := Left);
            [ exact c0_Left | exact mem_match
            | exact mem_pref_cond_s1' | exact mem_pref_cond_s3' ]. }
        match goal with |- context[color_of ?st] =>
          have Hcol : color_of st = color_of s by
            rewrite (color_of_pc_tag st) (color_of_pc_tag s); cbn [Symbolic.pc Types.taga] end.
        rewrite !Hcol !setmE.
        case: eqP => [_ | _]; last exact (reg_match w d).
        split.
        * move=> [= <-]. exists (p2.1@Other).
          split; [split; [reflexivity | exact (esym G)] | reflexivity].
        * move=> [= <-]. exists (p1.1@Other).
          split; [split; [reflexivity | exact (esym G)] | reflexivity].
  Qed.

  Lemma alloc_fun_weak:
    forall s1 s2 s3 M s1' s3',
      strong_equiv Left M s1 s3
      /\ weak_equiv Right M s2 s3
      /\ common_equiv M s1 s2 s3 ->
      alloc_fun s1 (NC := NC) = Some s1' ->
      alloc_fun s3 (NC := NC) = Some s3' ->
      weak_equiv Right M s2 s3'.
  Proof.
    import_context.

    intros s1 s2 s3 M s1' s3' equiv eq_s1' eq_s3'.
    destruct equiv as [strong [weak common]].
    unfold alloc_fun in eq_s1', eq_s3'; cbv zeta in eq_s1', eq_s3'.
    apply obind_inv in eq_s1'; destruct eq_s1' as (a1 & Heqa4 & eq_s1'); symmetry in Heqa4.
    apply obind_inv in eq_s1'; destruct eq_s1' as (wj1 & Hg & eq_s1');
      unfold is_jump in Hg; destruct (taga a1) eqn:Heqa7; try discriminate Hg;
      symmetry in Heqa7; clear Hg wj1.
    apply obind_inv in eq_s1'; destruct eq_s1' as (ret1 & Hret1 & eq_s1').
    apply obind_inv in eq_s1'; destruct eq_s1' as (uret1 & Hretchk1 & eq_s1');
      move: Hretchk1; case: ifP => Hretcol1 Hretchk1; last by []; clear uret1 Hretchk1.
    apply obind_inv in eq_s1'; destruct eq_s1' as (sz1 & Heqa6 & eq_s1'); destruct sz1 as [v' tg1].
    apply obind_inv in eq_s1'; destruct eq_s1' as (wo1 & Hg & eq_s1');
      unfold is_other in Hg; destruct tg1; try discriminate Hg; clear Hg wo1; symmetry in Heqa6.
    apply obind_inv in eq_s1'; destruct eq_s1' as (n' & Hg & eq_s1');
      destruct (int_of_word (vala (v'@Other))) as [m1|] eqn:Heqa3; try rewrite Heqa3 in Hg; simpl in Hg;
        [ move: Hg => [= ?]; subst m1 | discriminate Hg ];
      cbn [vala] in Heqa3; symmetry in Heqa3.
    apply obind_inv in eq_s1'; destruct eq_s1' as (uchk1 & Hszchk1 & eq_s1').
    destruct (leq (n' + 1) (expn 2 (word_size mt - NC))) eqn:Hszbound1;
      [ clear uchk1 Hszchk1 | discriminate Hszchk1 ].
    match type of eq_s1' with (if ?b then _ else _) = _ => destruct b eqn:Heqa10 end;
      [ discriminate eq_s1' | ]; symmetry in Heqa10.
    apply obind_inv in eq_s1'; destruct eq_s1' as (ad1 & Hg & eq_s1');
      apply obind_inv in Hg; destruct Hg as (p2 & Heqa13 & Hg); symmetry in Heqa13;
      move: Hg => [= ?]; subst ad1.
    apply obind_inv in eq_s1'; destruct eq_s1' as (rg1 & Hg & eq_s1');
      move: (updm_set Hg) => Hg2; subst rg1; clear Hg.
    apply obind_inv in eq_s3'; destruct eq_s3' as (ra3 & Heqa & eq_s3'); destruct ra3 as [v tgr3].
    apply obind_inv in eq_s3'; destruct eq_s3' as (wj3 & Hg & eq_s3');
      unfold is_jump in Hg; destruct tgr3; try discriminate Hg; clear Hg wj3; symmetry in Heqa.
    apply obind_inv in eq_s3'; destruct eq_s3' as (ret3 & Hret3 & eq_s3').
    apply obind_inv in eq_s3'; destruct eq_s3' as (uret3 & Hretchk3 & eq_s3');
      move: Hretchk3; case: ifP => Hretcol3 Hretchk3; last by []; clear uret3 Hretchk3.
    apply obind_inv in eq_s3'; destruct eq_s3' as (a0 & Heqa1 & eq_s3'); symmetry in Heqa1.
    apply obind_inv in eq_s3'; destruct eq_s3' as (wo3 & Hg & eq_s3');
      unfold is_other in Hg; destruct (taga a0) eqn:Heqa8; try discriminate Hg;
      symmetry in Heqa8; clear Hg wo3.
    apply obind_inv in eq_s3'; destruct eq_s3' as (n1 & Hg & eq_s3');
      destruct (int_of_word (vala a0)) as [m3|] eqn:Heqa12; try rewrite Heqa12 in Hg; simpl in Hg;
        [ move: Hg => [= ?]; subst m3 | discriminate Hg ]; symmetry in Heqa12.
    apply obind_inv in eq_s3'; destruct eq_s3' as (uchk3 & Hszchk3 & eq_s3').
    destruct (leq (n1 + 1) (expn 2 (word_size mt - NC))) eqn:Hszbound3;
      [ clear uchk3 Hszchk3 | discriminate Hszchk3 ].
    match type of eq_s3' with (if ?b then _ else _) = _ => destruct b eqn:Heqa9 end;
      [ discriminate eq_s3' | ]; symmetry in Heqa9.
    apply obind_inv in eq_s3'; destruct eq_s3' as (ad3 & Hg & eq_s3');
      apply obind_inv in Hg; destruct Hg as (p1 & Heqa11 & Hg); symmetry in Heqa11;
      move: Hg => [= ?]; subst ad3.
    apply obind_inv in eq_s3'; destruct eq_s3' as (rg3 & Hg & eq_s3');
      move: (updm_set Hg) => Hg2; subst rg3; clear Hg.
    inversion common as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          [mem_pref_cond_s1 [mem_pref_cond_s1' [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 [entry_code1 cvo1]]]]]]]]
                          [mem_pref_cond_s2 [mem_pref_cond_s2' [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 [entry_code2 cvo2]]]]]]]]
                          [mem_pref_cond_s3 [mem_pref_cond_s3' [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 [entry_code3 cvo3]]]]]]]]
                          capa_cor1 capa_cor2 capa_cor3 code_left code_right Hcval wpcc1 wpcc2].
    subst m s0 s4 s5.
    assert (n1 = n').
    { destruct strong as [? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match].
      destruct (reg_match (as_word (ssrint.Posz 17)) v'@Other) as [_ impl].
      destruct (impl (esym Heqa6)) as [? [dmatch eq1]]. simpl in *.
      rewrite eq1 in Heqa1. inv Heqa1.
      destruct x.
      inv dmatch. simpl in *.
      clear -Heqa3 Heqa12.
      congruence. }
    subst n1.
    set blk1 := (mkfmap (mkseq _ n')) in eq_s1'.
    try (set blk3 := (mkfmap (mkseq _ n')) in eq_s3').
    pose proof (erefl blk1) as Hblk1; unfold blk1 in Hblk1 at 2.
    try (pose proof (erefl blk3) as Hblk3; unfold blk3 in Hblk3 at 2).
    clearbody blk1; try clearbody blk3.
    move: eq_s1' => [= Hs1]; subst s1'.
    try (move: eq_s3' => [= Hs3]; subst s3').
    destruct weak as [? ? s3 color_eq side_s' s_mem_cor s'_mem_cor entry_off  mem_match].
      econstructor; try (rewrite eq_s3'; simpl; auto; done); try congruence; simpl; try done.
      + destruct s, s3, pc0, pc1. simpl. trivial.
      + intros d w rel d_eq.
        rewrite /address_correctness.
        case Et: (vtag (taga d)) => [r| | |] //.
        all: cbn [Symbolic.mem] in d_eq.
        all: apply unionm_get in d_eq;
             case: d_eq => [d_eq | [_ d_eq]];
               last (xblkc d_eq; subst d; discriminate Et).
        all: pose proof (s'_mem_cor d w rel d_eq) as Hac; rewrite Et in Hac.
        all: destruct Hac as [vv [mem_s_v Hv]].
        all: exists vv; split; [cbn [Symbolic.mem]; apply unionm_getL; exact mem_s_v | exact Hv].
      + intros col w' w'' d d' proc l l' rel eqw' eqw'' dcode d'code dcol d'col d_e_eq d'_e_eq.
        cbn [Symbolic.mem] in eqw''.
        apply unionm_get in eqw'';
          case: eqw'' => [eqw'' | [_ eqw'']];
          last (xblkc eqw''; subst d'; discriminate d'code).
        exact (entry_off col w' w'' d d' proc l l' rel eqw' eqw'' dcode d'code dcol d'col d_e_eq d'_e_eq).
      + intros w d no_code rel.
        cbn [Symbolic.mem].
        split.
        * move=> H; apply unionm_get in H; case: H => [H | [Hs3None Hfresh]].
          -- destruct (mem_match w d no_code rel) as [impl _].
             destruct (impl H) as [d' [d'match d'eq]].
             exists d'; split; [exact d'match | exact d'eq].
          --
             exfalso.
             move: rel; xblk Hfresh; move: Hfresh => /alloc_block_const_value ->.
             rewrite /= tag_pc3 /is_relevant_comp => Hic.
             have Hip : c0 \in domm ip.
             { move: side_s'; rewrite /side_of (color_of_pc_tag s) tag_pc2 /=.
               by case: (c0 \in domm ip). }
             inversion Hmergeable_ifaces as [[_ fdisj] _].
             move/fdisjointP: fdisj => fdisj'.
             by move: (fdisj' c0 Hip); rewrite Hic.
        * move=> H.
          destruct (mem_match w d no_code rel) as [_ impl].
          destruct (impl H) as [d' [d'match d'eq]].
          exists d'; split; [exact d'match | apply unionm_getL; exact d'eq].
  Qed.

  Lemma alloc_fun_common:
    forall s1 s2 s3 M s1' s3',
      strong_equiv Left M s1 s3
      /\ weak_equiv Right M s2 s3
      /\ common_equiv M s1 s2 s3 ->
      alloc_fun s1 (NC := NC) = Some s1' ->
      alloc_fun s3 (NC := NC) = Some s3' ->
      common_equiv M s1' s2 s3'.
  Proof.
    import_context.

    intros s1 s2 s3 M s1' s3' equiv eq_s1' eq_s3'.
    destruct equiv as [strong [weak common]].
    unfold alloc_fun in eq_s1', eq_s3'; cbv zeta in eq_s1', eq_s3'.
    apply obind_inv in eq_s1'; destruct eq_s1' as (a1 & Heqa4 & eq_s1'); symmetry in Heqa4.
    apply obind_inv in eq_s1'; destruct eq_s1' as (wj1 & Hg & eq_s1');
      unfold is_jump in Hg; destruct (taga a1) eqn:Heqa7; try discriminate Hg;
      symmetry in Heqa7; clear Hg wj1.
    apply obind_inv in eq_s1'; destruct eq_s1' as (ret1 & Hret1 & eq_s1').
    apply obind_inv in eq_s1'; destruct eq_s1' as (uret1 & Hretchk1 & eq_s1');
      move: Hretchk1; case: ifP => Hretcol1 Hretchk1; last by []; clear uret1 Hretchk1.
    apply obind_inv in eq_s1'; destruct eq_s1' as (sz1 & Heqa6 & eq_s1'); destruct sz1 as [v' tg1].
    apply obind_inv in eq_s1'; destruct eq_s1' as (wo1 & Hg & eq_s1');
      unfold is_other in Hg; destruct tg1; try discriminate Hg; clear Hg wo1; symmetry in Heqa6.
    apply obind_inv in eq_s1'; destruct eq_s1' as (n' & Hg & eq_s1');
      destruct (int_of_word (vala (v'@Other))) as [m1|] eqn:Heqa3; try rewrite Heqa3 in Hg; simpl in Hg;
        [ move: Hg => [= ?]; subst m1 | discriminate Hg ];
      cbn [vala] in Heqa3; symmetry in Heqa3.
    apply obind_inv in eq_s1'; destruct eq_s1' as (uchk1 & Hszchk1 & eq_s1').
    destruct (leq (n' + 1) (expn 2 (word_size mt - NC))) eqn:Hszbound1;
      [ clear uchk1 Hszchk1 | discriminate Hszchk1 ].
    match type of eq_s1' with (if ?b then _ else _) = _ => destruct b eqn:Heqa10 end;
      [ discriminate eq_s1' | ]; symmetry in Heqa10.
    apply obind_inv in eq_s1'; destruct eq_s1' as (ad1 & Hg & eq_s1');
      apply obind_inv in Hg; destruct Hg as (p2 & Heqa13 & Hg); symmetry in Heqa13;
      move: Hg => [= ?]; subst ad1.
    apply obind_inv in eq_s1'; destruct eq_s1' as (rg1 & Hg & eq_s1');
      move: (updm_set Hg) => Hg2; subst rg1; clear Hg.
    apply obind_inv in eq_s3'; destruct eq_s3' as (ra3 & Heqa & eq_s3'); destruct ra3 as [v tgr3].
    apply obind_inv in eq_s3'; destruct eq_s3' as (wj3 & Hg & eq_s3');
      unfold is_jump in Hg; destruct tgr3; try discriminate Hg; clear Hg wj3; symmetry in Heqa.
    apply obind_inv in eq_s3'; destruct eq_s3' as (ret3 & Hret3 & eq_s3').
    apply obind_inv in eq_s3'; destruct eq_s3' as (uret3 & Hretchk3 & eq_s3');
      move: Hretchk3; case: ifP => Hretcol3 Hretchk3; last by []; clear uret3 Hretchk3.
    apply obind_inv in eq_s3'; destruct eq_s3' as (a0 & Heqa1 & eq_s3'); symmetry in Heqa1.
    apply obind_inv in eq_s3'; destruct eq_s3' as (wo3 & Hg & eq_s3');
      unfold is_other in Hg; destruct (taga a0) eqn:Heqa8; try discriminate Hg;
      symmetry in Heqa8; clear Hg wo3.
    apply obind_inv in eq_s3'; destruct eq_s3' as (n1 & Hg & eq_s3');
      destruct (int_of_word (vala a0)) as [m3|] eqn:Heqa12; try rewrite Heqa12 in Hg; simpl in Hg;
        [ move: Hg => [= ?]; subst m3 | discriminate Hg ]; symmetry in Heqa12.
    apply obind_inv in eq_s3'; destruct eq_s3' as (uchk3 & Hszchk3 & eq_s3').
    destruct (leq (n1 + 1) (expn 2 (word_size mt - NC))) eqn:Hszbound3;
      [ clear uchk3 Hszchk3 | discriminate Hszchk3 ].
    match type of eq_s3' with (if ?b then _ else _) = _ => destruct b eqn:Heqa9 end;
      [ discriminate eq_s3' | ]; symmetry in Heqa9.
    apply obind_inv in eq_s3'; destruct eq_s3' as (ad3 & Hg & eq_s3');
      apply obind_inv in Hg; destruct Hg as (p1 & Heqa11 & Hg); symmetry in Heqa11;
      move: Hg => [= ?]; subst ad3.
    apply obind_inv in eq_s3'; destruct eq_s3' as (rg3 & Hg & eq_s3');
      move: (updm_set Hg) => Hg2; subst rg3; clear Hg.
    inversion common as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          [mem_pref_cond_s1 [mem_pref_cond_s1' [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 [entry_code1 cvo1]]]]]]]]
                          [mem_pref_cond_s2 [mem_pref_cond_s2' [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 [entry_code2 cvo2]]]]]]]]
                          [mem_pref_cond_s3 [mem_pref_cond_s3' [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 [entry_code3 cvo3]]]]]]]]
                          capa_cor1 capa_cor2 capa_cor3 code_left code_right Hcval wpcc1 wpcc2].
    subst m s0 s4 s5.
    assert (n1 = n').
    { destruct strong as [? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match].
      destruct (reg_match (as_word (ssrint.Posz 17)) v'@Other) as [_ impl].
      destruct (impl (esym Heqa6)) as [? [dmatch eq1]]. simpl in *.
      rewrite eq1 in Heqa1. inv Heqa1.
      destruct x.
      inv dmatch. simpl in *.
      clear -Heqa3 Heqa12.
      congruence. }
    subst n1.
    set blk1 := (mkfmap (mkseq _ n')) in eq_s1'.
    try (set blk3 := (mkfmap (mkseq _ n')) in eq_s3').
    pose proof (erefl blk1) as Hblk1; unfold blk1 in Hblk1 at 2.
    try (pose proof (erefl blk3) as Hblk3; unfold blk3 in Hblk3 at 2).
    clearbody blk1; try clearbody blk3.
    move: eq_s1' => [= Hs1]; subst s1'.
    try (move: eq_s3' => [= Hs3]; subst s3').
    have Hside_s1 : side_of (color_of s1) = Left by inversion strong.
    have Hc0_dom : c0 \in domm ip.
    { move: Hside_s1; rewrite (color_of_pc_tag s1) tag_pc1 /side_of /=.
      case Hd: (c0 \in domm ip); first (move=> _; reflexivity).
      move=> Hcon; discriminate Hcon. }
    have Hbnd_c0 : 1 + c0 < 2 ^ NC.
    { apply: colors_bounded. apply/orP. by left. }
    eapply common_equiv_def with (n := n) (c := c0).
      18: exact wpcc2.
      17: { apply: (pc_code_color_alloc (s := s1) (a := vala a1) (ret := ret1));
              [ reflexivity | exact Hret1 | reflexivity | reflexivity | exact Hretcol1 ]. }
      all: try (cbn [Symbolic.pc Types.taga]; eassumption).
      all: try exact (conj mem_pref_cond_s2 (conj mem_pref_cond_s2' (conj code_pref_cond_s2
              (conj alloc_mem_s2 (conj bnz_s2 (conj end_s2 (conj col_mem2 (conj entry_code2 cvo2)))))))).
      all: try eassumption.
      + simpl. clear strong common weak code_left code_right tag_pc1 tag_pc2 tag_pc3 capa_cor1 capa_cor2 capa_cor3.
        simpl in *.
        induction wfst; intros.
        * eapply wf_stack_empty; eauto.
        * eapply wf_stack_cons_left; eauto.
          -- unfold points_to_comp_code' in *. rewrite unionmE.
             oapp_False. simpl. done.
          -- unfold points_to_comp_code in *. rewrite unionmE.
             oapp_False. simpl. done.
        * eapply wf_stack_cons_right; eauto.
          -- unfold points_to_comp_code' in *. rewrite unionmE.
             oapp_False. simpl. done.
          -- unfold points_to_comp_code in *. rewrite unionmE.
             oapp_False. simpl. done.
      + unfold register_domm. simpl. rewrite domm_set.
        unfold register_domm in *. simpl in *. clear -reg_domm1.
        unfold "|:", val.
        rewrite //= reg_domm1 //=.
        rewrite <- eq_fset.
        intros x. rewrite 2!in_fset in_cons in_fset.
        case x_16: eq_op => //=.
        move: x_16 => /eqP -> //=.
      + unfold register_domm. simpl. rewrite domm_set.
        unfold register_domm in *. simpl in *. clear -reg_domm3.
        unfold "|:", val.
        rewrite //= reg_domm3 //=.
        rewrite <- eq_fset.
        intros x. rewrite 2!in_fset in_cons in_fset.
        case x_16: eq_op => //=.
        move: x_16 => /eqP -> //=.
      + split; [|split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]];
          unfold memory_prefix_condition, code_prefix_condition, alloc_empty, BNZ_correctness, end_condition in *;
          simpl; repeat rewrite unionmE.
        * clear -mem_pref_cond_s1 tag_pc1 Heqa10 blk1 blk3 Hblk1 Hblk3 Hszbound1 Hszbound3.
          rename Heqa10 into Hend.
          move: mem_pref_cond_s1.
          simpl.
          rewrite /memory_prefix_condition => H c w' v'.
          rewrite unionmE.
          case: ifP => _; [apply H|].
          move=> Hmkf; xblk Hmkf; move: Hmkf => /mkfmap_Some /=.
          rewrite /mkseq tag_pc1; move=> /mapP [] x x_in_iota /= [] H1 H2.
          intros. left.
          subst v'. simpl in H0. rewrite <- H0.
          { pose proof (andw_last_component_prefix (ssrint.Posz (1 + c0)) (mem s1)) as Hstart.
            symmetry in Hend.
            move: Hend => /negb_false_iff /eqP.
            rewrite tag_pc1 => /= Hend.
            subst w'.
            eapply mask_range with
              (x := (List.last
                        (List.filter
                           (fun mw : word 32 =>
                              andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz (1 + c0)))
                           (domm (mem s1))) (@component_memory_prefix mt NC (ssrint.Posz (1 + c0)))));
              [by [exact Hszbound1 | exact Hszbound3] | eapply Hstart | eapply Hend | assumption]. }
        * clear -mem_pref_cond_s1 mem_pref_cond_s1' tag_pc1 Heqa10 blk1 blk3 Hblk1 Hblk3 Hszbound1 Hszbound3 Hbnd_c0.
          rename Heqa10 into Hend.
          move: mem_pref_cond_s1'.
          simpl.
          rewrite /memory_prefix_condition' => H c w' v' Hb.
          rewrite unionmE.
          case: ifP => _; [apply (H _ _ _ Hb)|].
          move=> Hmkf; xblk Hmkf; move: Hmkf => /mkfmap_Some /=.
          rewrite /mkseq tag_pc1; move=> /mapP [] x x_in_iota /= [] H1 H2 H3 /=.
          rewrite H2 /=; split; auto.
          assert (andw w' (@mask mt NC) = @component_memory_prefix mt NC (ssrint.Posz (1 + c0))).
          { pose proof (andw_last_component_prefix (ssrint.Posz (1 + c0)) (mem s1)) as Hstart.
            symmetry in Hend.
            move: Hend => /negb_false_iff /eqP.
            rewrite tag_pc1 => /= Hend.
            subst w'.
            eapply mask_range with
              (x := (List.last
                        (List.filter
                           (fun mw : word 32 =>
                              andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz (1 + c0)))
                           (domm (mem s1))) (@component_memory_prefix mt NC (ssrint.Posz (1 + c0)))));
              [by [exact Hszbound1 | exact Hszbound3] | eapply Hstart | eapply Hend | assumption]. }
          rewrite H3 in H0.
          eapply (component_memory_prefix_inj _ _ (ltnW NC_lt_word) Hb Hbnd_c0) in H0.
          eapply addnI; eauto.
        * clear -code_pref_cond_s1 blk1 blk3 Hblk1 Hblk3.
          move=> w v; rewrite unionmE.
          case: ifP => /= _; [eapply code_pref_cond_s1; eauto|].
          move=> Hmkf; xblk Hmkf; move: Hmkf => /mkfmap_Some /=.
          rewrite /mkseq; move=> /mapP [] x x_in_iota /= [] H1 H2.
          move=> Hcode; rewrite H2 in Hcode; discriminate Hcode.
        * rewrite alloc_mem_s1. simpl. try rewrite Hblk1; try rewrite Hblk3. rewrite tag_pc1.
          clear -Heqa10 tag_pc1 Hbnd_c0 Hszbound1 Hszbound3.
          destruct (mkfmap _ _) eqn:H; auto.
          apply mkfmap_Some in H.
          move: H => /=. rewrite /mkseq.
          move=> /mapP [] x x_in_iota.
          remember (word_of_nat alloc_label) as w.
          move=> [] H1 _.

          assert (w_prefix: andw w (@mask mt NC) ==
                              @component_memory_prefix mt NC (ssrint.Posz (1 + c0))).
          { pose proof (andw_last_component_prefix (ssrint.Posz (1 + c0)) (mem s1)) as Hstart.
            apply /eqP. clear Heqw.
            symmetry in Heqa10.
            move: Heqa10 => /negb_false_iff /eqP.
            rewrite tag_pc1 => /= Hend.
            subst w.
            eapply mask_range with
              (x := (List.last
                        (List.filter
                           (fun mw : word 32 =>
                              andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz (1 + c0)))
                           (domm (mem s1))) (@component_memory_prefix mt NC (ssrint.Posz (1 + c0)))));
              [by [exact Hszbound1 | exact Hszbound3] | eapply Hstart | eapply Hend | assumption]. }
          clear H1. subst w.
          pose proof mask_alloc_label as H.
          (* assert (andw (word_of_nat alloc_label) (@mask mt NC) = 0%w). *)
          (* { admit. } *)
          rewrite H in w_prefix.
          exfalso. move/eqP: w_prefix => w_prefix.
          apply (component_memory_prefix_succ_not_zero (NC := NC) c0 (ltnW NC_lt_word) Hbnd_c0).
          transitivity (0%w : word (word_size mt));
            [ exact (esym w_prefix) | exact (esym component_memory_prefix_zero) ].
        * intros w d deq dcode. goal_match_bind_step.
          rewrite unionmE in deq. unfold_match' deq.
          all: auto.
          { (pose proof (bnz_s1 w d deq dcode) as cor; unfold decode_instr, ops, concrete_int_32_ops in cor).
            simpl in cor; rewrite <- Heqa0 in cor. destruct i; auto; simpl; rewrite unionmE.
            + destruct cor as [? [eq ?]]. rewrite eq. simpl. eauto.
            + destruct cor as [[? [eq ?] ]| ]. rewrite eq. simpl. eauto.
              rewrite H. right. done. }
          { assert (eq: d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s1) false)).
             { xblk deq; clear -deq tag_pc1. rename deq into H.
               apply (@mkfmap_Some _ _ _ w d) in H.
               move: H => /=. rewrite /mkseq tag_pc1.
               move=> /mapP [] x x_in_iota [] H -> //=.
               case: s1 tag_pc1 {H} => /= _ _ [] /= _ taga _ -> //=. }
            rewrite eq in Heqa0. exfalso. clear -Heqa0. simpl in *. unfold_all. rewrite wunpackS in Heqa.
            unfold hnth in *. simpl in *. inv Heqa. }
        * intros w d deq dcode.
          cbn [Symbolic.mem] in deq.
          apply unionm_get in deq; case: deq => [deq | [_ deq]];
            last (xblkc deq; subst d; discriminate dcode).
          destruct (end_s1 w d deq dcode) as [Hhalt | [d' [d'eq Hd']]].
          -- left; exact Hhalt.
          -- right. exists d'. split; [cbn [Symbolic.mem]; apply unionm_getL; exact d'eq | exact Hd'].
        * intros w d deq. rewrite unionmE in deq. unfold_match' deq.
          -- eapply col_mem1; eauto.
          -- xblk deq; move: deq => /mkfmap_Some /=.
             rewrite /mkseq; move=> /mapP [] x x_in_iota /= [] H1 H2.
             subst d. rewrite tag_pc1. simpl.
             left; eapply Extra.In_in.
             clear -tag_pc1 strong.
             inv strong.
             destruct s1 as [?? [] ?]; simpl in *; subst.
             move: H1; rewrite /side_of; case: ifP => //=.
        * intros w d e deq dent. rewrite unionmE in deq. unfold_match' deq.
          -- eapply entry_code1; eauto.
          -- exfalso.
             assert (eq: d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s1) false)).
             { xblk deq; clear -deq tag_pc1. rename deq into H.
               apply (@mkfmap_Some _ _ _ w d) in H.
               move: H => /=. rewrite /mkseq tag_pc1.
               move=> /mapP [] x x_in_iota [] H -> //=.
               case: s1 tag_pc1 {H} => /= _ _ [] /= _ taga _ -> //=. }
             rewrite eq in dent. simpl in dent. inversion dent.
        *
          intros w d deq dcode. rewrite unionmE in deq. unfold_match' deq.
          -- eapply cvo1; eauto.
          -- exfalso.
             assert (eq: d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s1) false)).
             { xblk deq; clear -deq tag_pc1. rename deq into H.
               apply (@mkfmap_Some _ _ _ w d) in H.
               move: H => /=. rewrite /mkseq tag_pc1.
               move=> /mapP [] x x_in_iota [] H -> //=.
               case: s1 tag_pc1 {H} => /= _ _ [] /= _ taga _ -> //=. }
             rewrite eq in dcode. simpl in dcode. inversion dcode.
      + split; [|split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]];
          unfold memory_prefix_condition, code_prefix_condition, alloc_empty, BNZ_correctness, end_condition in *;
          simpl; repeat rewrite unionmE.
        * clear -mem_pref_cond_s3 tag_pc3 Heqa9 blk1 blk3 Hblk1 Hblk3 Hszbound1 Hszbound3.
          rename Heqa9 into Hend.
          move: mem_pref_cond_s3.
          simpl.
          rewrite /memory_prefix_condition => H c w' v'.
          rewrite unionmE.
          case: ifP => _; [apply H|].
          move=> Hmkf; xblk Hmkf; move: Hmkf => /mkfmap_Some /=.
          rewrite /mkseq tag_pc3; move=> /mapP [] x x_in_iota /= [] H1 H2.
          intros. left.
          subst v'. simpl in H0. rewrite <- H0.
          { pose proof (andw_last_component_prefix (ssrint.Posz (1 + c0)) (mem s3)) as Hstart.
            symmetry in Hend.
            move: Hend => /negb_false_iff /eqP.
            rewrite tag_pc3 => /= Hend.
            subst w'.
            eapply mask_range with
              (x := (List.last
                        (List.filter
                           (fun mw : word 32 =>
                              andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz (1 + c0)))
                           (domm (mem s3))) (@component_memory_prefix mt NC (ssrint.Posz (1 + c0)))));
              [by [exact Hszbound1 | exact Hszbound3] | eapply Hstart | eapply Hend | assumption]. }
        * clear -mem_pref_cond_s3 mem_pref_cond_s3' tag_pc3 Heqa9 blk1 blk3 Hblk1 Hblk3 Hszbound1 Hszbound3 Hbnd_c0.
          rename Heqa9 into Hend.
          move: mem_pref_cond_s3'.
          simpl.
          rewrite /memory_prefix_condition' => H c w' v' Hb.
          rewrite unionmE.
          case: ifP => _; [apply (H _ _ _ Hb)|].
          move=> Hmkf; xblk Hmkf; move: Hmkf => /mkfmap_Some /=.
          rewrite /mkseq tag_pc3; move=> /mapP [] x x_in_iota /= [] H1 H2 H3 /=.
          rewrite H2 /=; split; auto.
          assert (andw w' (@mask mt NC) = @component_memory_prefix mt NC (ssrint.Posz (1 + c0))).
          { pose proof (andw_last_component_prefix (ssrint.Posz (1 + c0)) (mem s3)) as Hstart.
            symmetry in Hend.
            move: Hend => /negb_false_iff /eqP.
            rewrite tag_pc3 => /= Hend.
            subst w'.
            eapply mask_range with
              (x := (List.last
                        (List.filter
                           (fun mw : word 32 =>
                              andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz (1 + c0)))
                           (domm (mem s3))) (@component_memory_prefix mt NC (ssrint.Posz (1 + c0)))));
              [by [exact Hszbound1 | exact Hszbound3] | eapply Hstart | eapply Hend | assumption]. }
          rewrite H3 in H0.
          eapply (component_memory_prefix_inj _ _ (ltnW NC_lt_word) Hb Hbnd_c0) in H0.
          eapply addnI; eauto.
        * clear -code_pref_cond_s3 blk1 blk3 Hblk1 Hblk3.
          move=> w v; rewrite unionmE.
          case: ifP => /= _; [eapply code_pref_cond_s3; eauto|].
          move=> Hmkf; xblk Hmkf; move: Hmkf => /mkfmap_Some /=.
          rewrite /mkseq; move=> /mapP [] x x_in_iota /= [] H1 H2.
          move=> Hcode; rewrite H2 in Hcode; discriminate Hcode.
        (* * rewrite alloc_mem_s3. simpl. admit. *)
        * rewrite alloc_mem_s3. simpl. try rewrite Hblk1; try rewrite Hblk3. rewrite tag_pc3.
          clear -Heqa9 tag_pc3 Hbnd_c0 Hszbound1 Hszbound3.
          destruct (mkfmap _ _) eqn:H; auto.
          apply mkfmap_Some in H.
          move: H => /=. rewrite /mkseq.
          move=> /mapP [] x x_in_iota.
          remember (word_of_nat alloc_label) as w.
          move=> [] H1 _.

          assert (w_prefix: andw w (@mask mt NC) ==
                              @component_memory_prefix mt NC (ssrint.Posz (1 + c0))).
          { pose proof (andw_last_component_prefix (ssrint.Posz (1 + c0)) (mem s3)) as Hstart.
            apply /eqP. clear Heqw.
            symmetry in Heqa9.
            move: Heqa9 => /negb_false_iff /eqP.
            rewrite tag_pc3 => /= Hend.
            subst w.
            eapply mask_range with
              (x := (List.last
                        (List.filter
                           (fun mw : word 32 =>
                              andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz (1 + c0)))
                           (domm (mem s3))) (@component_memory_prefix mt NC (ssrint.Posz (1 + c0)))));
              [by [exact Hszbound1 | exact Hszbound3] | eapply Hstart | eapply Hend | assumption]. }
          clear H1. subst w.
          pose proof mask_alloc_label as H.
          (* assert (andw (word_of_nat alloc_label) (@mask mt NC) = 0%w). *)
          (* { admit. } *)
          rewrite H in w_prefix.
          exfalso. move/eqP: w_prefix => w_prefix.
          apply (component_memory_prefix_succ_not_zero (NC := NC) c0 (ltnW NC_lt_word) Hbnd_c0).
          transitivity (0%w : word (word_size mt));
            [ exact (esym w_prefix) | exact (esym component_memory_prefix_zero) ].
        * intros w d deq dcode. goal_match_bind_step.
          rewrite unionmE in deq. unfold_match' deq.
          all: auto.
          { (pose proof (bnz_s3 w d deq dcode) as cor; unfold decode_instr, ops, concrete_int_32_ops in cor).
            simpl in cor; rewrite <- Heqa0 in cor. destruct i; auto; simpl; rewrite unionmE.
            + destruct cor as [? [eq ?]]. rewrite eq. simpl. eauto.
            + destruct cor as [[? [eq ?] ]| ]. rewrite eq. simpl. eauto.
              rewrite H. right. done. }
          assert (eq: d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)).
          { xblk deq; clear -deq tag_pc3. rename deq into H.
            apply (@mkfmap_Some _ _ _ w d) in H.
            move: H => /=. rewrite /mkseq tag_pc3.
            move=> /mapP [] x x_in_iota [] H -> //=.
            case: s3 tag_pc3 {H} => /= _ _ [] /= _ taga _ -> //=. }
          rewrite eq in Heqa0. exfalso. clear -Heqa0. simpl in *. unfold_all. rewrite wunpackS in Heqa.
          inv Heqa.
        * intros w d deq dcode.
          cbn [Symbolic.mem] in deq.
          apply unionm_get in deq; case: deq => [deq | [_ deq]];
            last (xblkc deq; subst d; discriminate dcode).
          destruct (end_s3 w d deq dcode) as [Hhalt | [d' [d'eq Hd']]].
          -- left; exact Hhalt.
          -- right. exists d'. split; [cbn [Symbolic.mem]; apply unionm_getL; exact d'eq | exact Hd'].
        * intros w d deq. rewrite unionmE in deq. unfold_match' deq.
          -- eapply col_mem3; eauto.
          -- xblk deq; move: deq => /mkfmap_Some /=.
             rewrite /mkseq; move=> /mapP [] x x_in_iota /= [] H1 H2.
             subst d. rewrite tag_pc3. simpl.
             left; eapply Extra.In_in.
             clear -tag_pc3 strong.
             inv strong.
             destruct s3 as [?? [] ?]; simpl in *; subst.
             move: H1; rewrite /side_of; case: ifP => //=.
        * intros w d e deq dent. rewrite unionmE in deq. unfold_match' deq.
          -- eapply entry_code3; eauto.
          -- exfalso.
             assert (eq: d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)).
             { xblk deq; clear -deq tag_pc3. rename deq into H.
               apply (@mkfmap_Some _ _ _ w d) in H.
               move: H => /=. rewrite /mkseq tag_pc3.
               move=> /mapP [] x x_in_iota [] H -> //=.
               case: s3 tag_pc3 {H} => /= _ _ [] /= _ taga _ -> //=. }
             rewrite eq in dent. simpl in dent. inversion dent.
        *
          intros w d deq dcode. rewrite unionmE in deq. unfold_match' deq.
          -- eapply cvo3; eauto.
          -- exfalso.
             assert (eq: d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)).
             { xblk deq; clear -deq tag_pc3. rename deq into H.
               apply (@mkfmap_Some _ _ _ w d) in H.
               move: H => /=. rewrite /mkseq tag_pc3.
               move=> /mapP [] x x_in_iota [] H -> //=.
               case: s3 tag_pc3 {H} => /= _ _ [] /= _ taga _ -> //=. }
             rewrite eq in dcode. simpl in dcode. inversion dcode.
      + intros d q r req. destruct r as [r | w]; repeat (rewrite unionmE || rewrite setmE);
          repeat (rewrite unionmE in req || rewrite setmE in req); simpl; simpl in req.
        { unfold_match' req. pose proof (capa_cor1 d q (inl r) req) as [is_in unicity].
          split; auto. intros r' d'.
          destruct r' as [r' | w']; simpl; repeat (rewrite unionmE || rewrite setmE).
          { intro req'. unfold_match' req'. eapply (unicity (inl _)); eauto. }
          { intros [t' [t'eq t'capa]]. unfold_match' t'eq. eapply (unicity (inr _)); eauto.
            assert (eq: d'@t' = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s1) false)).
            { xblk t'eq; clear -t'eq tag_pc1. rename t'eq into H.
              apply (@mkfmap_Some _ _ _ w' d'@t') in H.
              move: H => /=. rewrite /mkseq tag_pc1.
              move=> /mapP [] x x_in_iota [] H -> //=.
              case: s1 tag_pc1 {H} => /= _ _ [] /= _ taga _ -> -> //=. }
            destruct t'. simpl in t'capa. rewrite t'capa in eq. inv eq. } }
        { destruct req as [t [teq tcapa]]. unfold_match' teq.
          { pose proof (capa_cor1 d q (inr w) (ex_intro _ t (conj teq tcapa))) as [is_in unicity].
            split; auto. intros r' d'.
            destruct r' as [r' | w']; simpl; repeat (rewrite unionmE || rewrite setmE).
            { intro req'. unfold_match' req'. eapply (unicity (inl _)); eauto. }
            { intros [t' [t'eq t'capa]]. unfold_match' t'eq. eapply (unicity (inr _)); eauto.
              assert (eq: d'@t' = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s1) false)).
              { xblk t'eq; clear -t'eq tag_pc1. rename t'eq into H.
                apply (@mkfmap_Some _ _ _ w' d'@t') in H.
                move: H => /=. rewrite /mkseq tag_pc1.
                move=> /mapP [] x x_in_iota [] H -> //=.
                case: s1 tag_pc1 {H} => /= _ _ [] /= _ taga _ -> -> //=. }
              destruct t'. simpl in t'capa. rewrite t'capa in eq. inv eq. } }
          { assert (eq: d@t = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s1) false)).
            { xblk teq; clear -teq tag_pc1. rename teq into H.
              apply (@mkfmap_Some _ _ _ w d@t) in H.
              move: H => /=. rewrite /mkseq tag_pc1.
              move=> /mapP [] x x_in_iota [] H -> //=.
              case: s1 tag_pc1 {H} => /= _ _ [] /= _ taga _ -> -> //=. }
            destruct t. simpl in tcapa. rewrite tcapa in eq. inv eq. } }
        + intros d q r req. destruct r as [r | w]; repeat (rewrite unionmE || rewrite setmE);
          repeat (rewrite unionmE in req || rewrite setmE in req); simpl; simpl in req.
        { unfold_match' req. pose proof (capa_cor3 d q (inl r) req) as [is_in unicity].
          split; auto. intros r' d'.
          destruct r' as [r' | w']; simpl; repeat (rewrite unionmE || rewrite setmE).
          { intro req'. unfold_match' req'. eapply (unicity (inl _)); eauto. }
          { intros [t' [t'eq t'capa]]. unfold_match' t'eq. eapply (unicity (inr _)); eauto.
            assert (eq: d'@t' = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)).
            { xblk t'eq; clear -t'eq tag_pc3. rename t'eq into H.
              apply (@mkfmap_Some _ _ _ w' d'@t') in H.
              move: H => /=. rewrite /mkseq tag_pc3.
              move=> /mapP [] x x_in_iota [] H -> //=.
              case: s3 tag_pc3 {H} => /= _ _ [] /= _ taga _ -> -> //=. }
            destruct t'. simpl in t'capa. rewrite t'capa in eq. inv eq. } }
        { destruct req as [t [teq tcapa]]. unfold_match' teq.
          { pose proof (capa_cor3 d q (inr w) (ex_intro _ t (conj teq tcapa))) as [is_in unicity].
            split; auto. intros r' d'.
            destruct r' as [r' | w']; simpl; repeat (rewrite unionmE || rewrite setmE).
            { intro req'. unfold_match' req'. eapply (unicity (inl _)); eauto. }
            { intros [t' [t'eq t'capa]]. unfold_match' t'eq. eapply (unicity (inr _)); eauto.
              assert (eq: d'@t' = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)).
              { xblk t'eq; clear -t'eq tag_pc3. rename t'eq into H.
                apply (@mkfmap_Some _ _ _ w' d'@t') in H.
                move: H => /=. rewrite /mkseq tag_pc3.
                move=> /mapP [] x x_in_iota [] H -> //=.
                case: s3 tag_pc3 {H} => /= _ _ [] /= _ taga _ -> -> //=. }
              destruct t'. simpl in t'capa. rewrite t'capa in eq. inv eq. } }
          { assert (eq: d@t = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)).
            { xblk teq; clear -teq tag_pc3. rename teq into H.
              apply (@mkfmap_Some _ _ _ w d@t) in H.
              move: H => /=. rewrite /mkseq tag_pc3.
              move=> /mapP [] x x_in_iota [] H -> //=.
              case: s3 tag_pc3 {H} => /= _ _ [] /= _ taga _ -> -> //=. }
            destruct t. simpl in tcapa. rewrite tcapa in eq. inv eq. } }
      +
        intros w vd t off cc rel eq_off codet colt.
        split.
        * move=> Hmem; cbn [Symbolic.mem] in Hmem.
          apply unionm_get in Hmem; case: Hmem => [Hs1 | [_ Hfr]];
            last (exfalso; xblk Hfr; move: Hfr => /alloc_block_const_value [= _ Ht];
                  rewrite Ht in codet; discriminate codet).
          have [vr [vmatch veq]] := (fst (code_left w vd t off cc rel eq_off codet colt)) Hs1.
          exists vr. split; last by cbn [Symbolic.mem]; apply unionm_getL; exact veq.
          inversion vmatch as [? ? ? | ? ? | imm imm' dd dd' Hdec Hdec' Hmem Hmem' Hcode Htag Hoff]; subst.
          -- by apply decode_match_no_JAL.
          -- by apply decode_match_alloc_JAL.
          -- eapply decode_match_JAL;
               [ exact Hdec | exact Hdec'
               | cbn [Symbolic.mem]; apply unionm_getL; exact Hmem
               | cbn [Symbolic.mem]; apply unionm_getL; exact Hmem'
               | exact Hcode | exact Htag | exact Hoff ].
        * move=> Hmem; cbn [Symbolic.mem] in Hmem.
          apply unionm_get in Hmem; case: Hmem => [Hs3 | [_ Hfr]];
            last (exfalso; xblk Hfr; move: Hfr => /alloc_block_const_value [= _ Ht];
                  rewrite Ht in codet; discriminate codet).
          have [vr [vmatch veq]] := (snd (code_left w vd t off cc rel eq_off codet colt)) Hs3.
          exists vr. split; last by cbn [Symbolic.mem]; apply unionm_getL; exact veq.
          inversion vmatch as [? ? ? | ? ? | imm imm' dd dd' Hdec Hdec' Hmem Hmem' Hcode Htag Hoff]; subst.
          -- by apply decode_match_no_JAL.
          -- by apply decode_match_alloc_JAL.
          -- eapply decode_match_JAL;
               [ exact Hdec | exact Hdec'
               | cbn [Symbolic.mem]; apply unionm_getL; exact Hmem
               | cbn [Symbolic.mem]; apply unionm_getL; exact Hmem'
               | exact Hcode | exact Htag | exact Hoff ].
      +
        intros w vd t off cc rel eq_off codet colt.
        split.
        * move=> Hmem.
          have [vr [vmatch veq]] := (fst (code_right w vd t off cc rel eq_off codet colt)) Hmem.
          exists vr. split; last by cbn [Symbolic.mem]; apply unionm_getL; exact veq.
          inversion vmatch as [? ? ? | ? ? | imm imm' dd dd' Hdec Hdec' Hmem0 Hmem' Hcode Htag Hoff]; subst.
          -- by apply decode_match_no_JAL.
          -- by apply decode_match_alloc_JAL.
          -- eapply decode_match_JAL;
               [ exact Hdec | exact Hdec'
               | exact Hmem0
               | cbn [Symbolic.mem]; apply unionm_getL; exact Hmem'
               | exact Hcode | exact Htag | exact Hoff ].
        * move=> Hmem; cbn [Symbolic.mem] in Hmem.
          apply unionm_get in Hmem; case: Hmem => [Hs3 | [_ Hfr]];
            last (exfalso; xblk Hfr; move: Hfr => /alloc_block_const_value [= _ Ht];
                  rewrite Ht in codet; discriminate codet).
          have [vr [vmatch veq]] := (snd (code_right w vd t off cc rel eq_off codet colt)) Hs3.
          exists vr. split; last by exact veq.
          inversion vmatch as [? ? ? | ? ? | imm imm' dd dd' Hdec Hdec' Hmem0 Hmem' Hcode Htag Hoff]; subst.
          -- by apply decode_match_no_JAL.
          -- by apply decode_match_alloc_JAL.
          -- eapply decode_match_JAL;
               [ exact Hdec | exact Hdec'
               | exact Hmem0
               | cbn [Symbolic.mem]; apply unionm_getL; exact Hmem'
               | exact Hcode | exact Htag | exact Hoff ].
  Qed.

  Lemma preserves_equiv_left_alloc_fun:
    forall s1 s2 s3 M s1' s3',
      strong_equiv Left M s1 s3
      /\ weak_equiv Right M s2 s3
      /\ common_equiv M s1 s2 s3 ->
      alloc_fun s1 (NC := NC) = Some s1' ->
      alloc_fun s3 (NC := NC) = Some s3' ->
      strong_equiv Left M s1' s3'
      /\ weak_equiv Right M s2 s3'
      /\ common_equiv M s1' s2 s3'.
  Proof.
    intros s1 s2 s3 M s1' s3' equiv eq_s1' eq_s3'.
    split; [|split].
    - exact (alloc_fun_strong equiv eq_s1' eq_s3').
    - exact (alloc_fun_weak equiv eq_s1' eq_s3').
    - exact (alloc_fun_common equiv eq_s1' eq_s3').
  Qed.


  Lemma simpl_as_word_equal:
    forall x y,
      0 <= x < 20 ->
      0 <= y < 20 ->
      x <> y ->
      as_word (k := reg_field_size mt) (ssrint.Posz x) == as_word (ssrint.Posz y) = false.
  Proof.
    clear.
    intros.
    apply /idP => C.
    move: C => /eqP C.
    eapply H1.
    rewrite <- (as_wordK (k := 5) (n := x)).
    rewrite <- (as_wordK (k := 5) (n := y)).
    f_equal. f_equal. auto.
    eapply leq_trans with (n := 20); eauto.
    eapply leq_trans with (n := 20); eauto.
  Qed.

  Module PCCM.

  Local Transparent next_state_do_update next_state_do_updates reg_clear_list_aux.

  Lemma op_silent_trpc :
    forall (op : opcode) (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
           (ts : hseq (tag_type lrc_tags) (inputs op)) (tni : option (tag_type lrc_tags Symbolic.M))
           (evinp : ev_inputs) (ov : ovec lrc_tags op) (ev : option event),
      LRC.transfer (IVec (OP op) tpc ti ts tni) evinp = Some (ov, ev) ->
      ev = None ->
      trpc ov = tpc.
  Proof.
    move=> op tpc ti ts tni evinp ov ev.
    rewrite /LRC.transfer /LRC.instr_rules_mp.
    case: tpc => level current'.
    move: ts ov; case: op => [|||b||||||||||] ts ov; cbv zeta; move=> H Hev; subst ev.
    -
      rewrite (hseq0 ts) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      move: H => [= <-].
      exact: erefl.
    -
      rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      move: H => [= <-]; exact: erefl.
    -
      rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq0 (hsbehead (hsbehead ts))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      move: H => [= <-]; exact: erefl.
    -
      rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts)))
              (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      move: H => [= <-]; exact: erefl.
    -
      rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts)))
              (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => u2 [_ {}H].
      move: H. case: ifP => // _ H.
      move: H. case E: (switch_val _ _) => [a c] /=.
      move=> [= <-]; exact: erefl.
    -
      rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts)))
              (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => u3 [_ {}H].
      move: H. case: ifP => // _ H.
      move: H. case E: (switch_val _ _) => [a c] /=.
      move=> [= <-]; exact: erefl.
    -
      rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts))) in H.
      case: (obind_inv H) => u0 [_ {}H].
      move: H. case: ifP => _ H.
      + case: (obind_inv H) => u1 [_ {}H]. move: H => [= <-]; exact: erefl.
      + case: (obind_inv H) => u1 [_ {}H]. case: (obind_inv H) => u2 [_ {}H].
        case: (obind_inv H) => u3 [_ {}H]. by move: H => [=].
    -
      rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      move: H => [= <-]; exact: erefl.
    -
      rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      move: H. case: ifP => _ H.
      + move: H => [= <-]; exact: erefl.
      + case: (obind_inv H) => u2 [_ {}H].
        case: (obind_inv H) => u3 [Hgc {}H].
        case: (obind_inv H) => u4 [Hce {}H].
        move: H => [= _ Hev2].
        move: Hgc Hce Hev2. case: tni => [td0|]; last by move=> Hgc'; discriminate Hgc'.
        case: td0 => vtg ctg etg ictg.
        case: etg => [[pp ll]|] /=.
        * by move=> _ _ Hev2; discriminate Hev2.
        * by move=> _ Hce' _; discriminate Hce'.
    -  by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    -  by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    -  by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    -  by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    -  by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
  Qed.

  Lemma updm_domm (T : ordType) (S : Type) (m m' : {fmap T -> S}) k v :
    updm m k v = Some m' -> domm m' = domm m.
  Proof.
    rewrite /updm. case E: (getm m k) => [a|] //= [<-]. rewrite domm_set.
    have Hk : k \in domm m by apply/dommP; exists a.
    apply/eqP. by rewrite eqEfsubset fsubUset fsub1set Hk fsubsetxx fsubsetUr.
  Qed.

  Lemma run_syscall_alloc : forall pc0 sc (s s' : state) ev,
    Instance.table (NC:=NC) pc0 = Some sc ->
    @run_syscall _ _ lrc_tags LRC.transfer unit sc s = Some (s', ev) ->
    alloc_fun (NC:=NC) s = Some s'.
  Proof.
    move=> pc0 sc s s' ev Htbl Hrun.
    have Hsem : Symbolic.sem sc = alloc_fun (NC := NC).
    { move: Htbl. rewrite /Instance.table /Merged.table mkfmapE /=.
      case: ifP => [_ [= <-] // | _]. by move=> [=]. }
    move: Hrun. rewrite /run_syscall Hsem /= => H.
    case: (obind_inv H) => i [_ {}H].
    by case: (obind_inv H) => s0 [Hs0] [= <-].
  Qed.

  Lemma run_syscall_sem_gen : forall (tf : _) sc (s s' : state) ev,
    @run_syscall _ _ lrc_tags tf unit sc s = Some (s', ev) -> Symbolic.sem sc s = Some s'.
  Proof.
    move=> tf sc s s' ev; rewrite /run_syscall.
    case: (evi s) => [i|] //=. case: (tf _ i) => [vv|] //=.
    by case Es: (Symbolic.sem sc s) => [s0|] //= [= <- _].
  Qed.

  Lemma alloc_pc_code_color : forall (s s' : state),
    alloc_fun (NC:=NC) s = Some s' -> pc_code_color s'.
  Proof.
    move=> s s' H. move: H. rewrite /alloc_fun. cbv zeta. move=> H.
    case: (obind_inv H) => ra_val [Hra {}H].
    case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => ret_addr [Hret {}H].
    case: (obind_inv H) => uret [Hretchk {}H].
    move: Hretchk; case: ifP => Hretcol Hretchk; last by []; clear uret Hretchk.
    case: (obind_inv H) => sz [Hsz {}H].
    case: (obind_inv H) => u2 [_ {}H].
    case: (obind_inv H) => len [Hlen {}H].
    case: (obind_inv H) => u3 [_ {}H].
    move: H. case: ifP => // _ H.
    case: (obind_inv H) => addr [Haddr {}H].
    case: (obind_inv H) => regs' [Hregs' {}H].
    move: H => [= HSt]. subst s'.
    apply: (pc_code_color_alloc (s := s) (a := vala ra_val) (ret := ret_addr));
      [ reflexivity | exact Hret | reflexivity | reflexivity | exact Hretcol ].
  Qed.


  Lemma weak_store_facts : forall (s1 s1' : state)
      (mem0 : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags Symbolic.M)})
      (regs0 : {fmap Types.reg mt -> atom (mword mt) (tag_type lrc_tags R)})
      (pc0 : mword mt) (tpc0 : tag_type lrc_tags P) (extra : unit)
      (r1 r2 : Types.reg mt) (w1 w2 : mword mt)
      (t1 t2 : tag_type lrc_tags R) (told ti0 : tag_type lrc_tags Symbolic.M) (oldv : mword mt),
    s1 = {| mem := mem0; regs := regs0; pc := pc0 @ tpc0; internal := extra |} ->
    mem0 w1 = Some (oldv @ told) ->
    @next_state_updates mt ops lrc_tags LRC.transfer unit s1
       (IVec STORE tpc0 ti0 [hseq t1; t2; told])
       [:: RegRead r1; RegRead r2; MemWrite w1 w2] = Some (s1', None) ->
    exists v old,
      mem s1 w1 = Some old /\ mem s1' = setm (mem s1) w1 v /\
      taga (pc s1') = taga (pc s1) /\
      color (taga v) = color_of s1 /\ color (taga old) = color_of s1 /\
      ~ is_code (taga v) /\ ~ is_code (taga old) /\
      entry (taga v) = entry (taga old).
  Proof.
    move=> s1 s1' mem0 regs0 pc0 tpc0 extra r1 r2 w1 w2 t1 t2 told ti0 oldv Hs1 Hmw0 NEXT.
    have Hmems1 : mem s1 = mem0 by rewrite Hs1.
    have Htpcs1 : taga (pc s1) = tpc0 by rewrite Hs1.
    have Hcols : color_of s1 = match tpc0 with Level _ c => c end
      by rewrite color_of_pc_tag Htpcs1.
    move: NEXT.
    rewrite /next_state_updates /next_state_updates_and_pc /next_state.
    case Hevi: (evi s1) => [i|] //=.
    case Hpc': (mem s1 (vala (pc s1) + 1)%w) => [ni|]; rewrite /=; move=> Hgoal;
      ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
        case: ov_ev Htr Hk => ov ev Htr Hk;
        have [Hev [Htrpc [Htrov [Hcoltd Hncd]]]] := store_transfer Htr;
        subst ev; move: Hk;
        cbn -[updm setm regs mem pc internal];
        rewrite Htrpc Htrov;
        cbn -[updm setm regs mem pc internal];
        move=> Hk0;
        case: (obind_inv Hk0) => stf [Hndsu Hfin];
        case: (obind_inv Hndsu) => sta [Hia Hr1];
        case: (obind_inv Hr1) => stb [Hib Hr2];
        case: (obind_inv Hr2) => stc [Hic Hr3];
        move: Hr3 => [= Estf]; subst stf;
        case: (obind_inv Hia) => av1 [_ {}Hia];
        case: (obind_inv Hia) => rv1 [_ {}Hia]; move: Hia => [= Esta];
        case: (obind_inv Hib) => av2 [_ {}Hib];
        case: (obind_inv Hib) => rv2 [_ {}Hib]; move: Hib => [= Estb];
        case: (obind_inv Hic) => mv1 [Hmv1 {}Hic]; move: Hic => [= Estc];
        (have Estab : mem stb = mem s1 by rewrite -Estb -Esta; exact: erefl);
        (have Hmc : mem stc = setm (mem s1) w1 (w2 @ (switch_val told t2).1)
          by rewrite -Estc (updm_set Hmv1) Estab; exact: erefl);
        move: Hfin => [= Hfins1]; subst s1';
        exists (w2 @ (switch_val told t2).1), (oldv @ told);
        split; [by (rewrite Hmems1; exact: Hmw0)|];
        split; [by (rewrite /= Hmc)|];
        split; [by (rewrite /= Htpcs1)|];
        split; [by (rewrite /= switch_val_color Hcoltd Hcols)|];
        split; [by (rewrite /= Hcoltd Hcols)|];
        split; [by (rewrite /= switch_val_iscode; apply/negP)|];
        split; [by (rewrite /=; apply/negP)|];
        by (rewrite /= switch_val_entry) ).
  Qed.

  Lemma weak_load_facts : forall (s1 s1' : state)
      (mem0 : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags Symbolic.M)})
      (regs0 : {fmap Types.reg mt -> atom (mword mt) (tag_type lrc_tags R)})
      (pc0 : mword mt) (tpc0 : tag_type lrc_tags P) (extra : unit)
      (r1 r2 : Types.reg mt) (w1 w2 : mword mt)
      (t1 td : tag_type lrc_tags R) (t2 ti0 : tag_type lrc_tags Symbolic.M),
    s1 = {| mem := mem0; regs := regs0; pc := pc0 @ tpc0; internal := extra |} ->
    mem0 w1 = Some (w2 @ t2) ->
    @next_state_updates mt ops lrc_tags LRC.transfer unit s1
       (IVec LOAD tpc0 ti0 [hseq t1; t2; td])
       [:: RegRead r1; MemRead w1; RegWrite r2 w2] = Some (s1', None) ->
    mem s1 w1 = Some (w2 @ t2) /\
    mem s1' = setm (mem s1) w1
                (w2 @ (switch_val t2 (moved_tag (vtag t2))).1) /\
    taga (pc s1') = taga (pc s1) /\
    (is_code t2 \/ color t2 = color_of s1).
  Proof.
    move=> s1 s1' mem0 regs0 pc0 tpc0 extra r1 r2 w1 w2 t1 td t2 ti0 Hs1 Hmw1 NEXT.
    have Hmems1 : mem s1 = mem0 by rewrite Hs1.
    have Htpcs1 : taga (pc s1) = tpc0 by rewrite Hs1.
    move: NEXT.
    rewrite /next_state_updates /next_state_updates_and_pc /next_state.
    case Hevi: (evi s1) => [i|] //=.
    case Hpc': (mem s1 (vala (pc s1) + 1)%w) => [ni|]; rewrite /=; move=> Hgoal;
      ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
        case: ov_ev Htr Hk => ov ev Htr Hk;
        have [Hev [Htrpc Htrov]] := load_transfer Htr;
        have Hguard := load_guard Htr;
        subst ev; move: Hk;
        cbn -[updm setm regs mem pc internal];
        rewrite Htrpc Htrov;
        cbn -[updm setm regs mem pc internal];
        move=> Hk0;
        case: (obind_inv Hk0) => stf [Hndsu Hfin];
        case: (obind_inv Hndsu) => sta [Hia Hr1];
        case: (obind_inv Hr1) => stb [Hib Hr2];
        case: (obind_inv Hr2) => stc [Hic Hr3];
        move: Hr3 => [= Estf]; subst stf;
        case: (obind_inv Hia) => av1 [_ {}Hia];
        case: (obind_inv Hia) => rv1 [_ {}Hia]; move: Hia => [= Esta];
        case: (obind_inv Hib) => av2 [Hav2 {}Hib];
        case: (obind_inv Hib) => mv2 [Hmv2 {}Hib]; move: Hib => [= Estb];
        case: (obind_inv Hic) => rv3 [_ {}Hic]; move: Hic => [= Estc];
        (have Hsta : mem sta = mem s1 by rewrite -Esta; exact: erefl);
        (have Hav2' : av2 = w2 @ t2 by move: Hav2; rewrite Hsta Hmems1 Hmw1; congruence);
        (have Hstb : mem stb = setm (mem s1) w1
            (w2 @ (switch_val t2 (moved_tag (vtag t2))).1)
          by rewrite -Estb /= (updm_set Hmv2) Hsta Hav2'; exact: erefl);
        move: Hfin => [= Hfins1]; subst s1';
        split; [by (rewrite Hmems1; exact: Hmw1)|];
        split; [by (rewrite /= -Estc /= Hstb)|];
        split; [by (rewrite /= Htpcs1)|];
        (have Hcols1 : color_of s1 = match tpc0 with Level _ c => c end by rewrite Hs1);
        rewrite Hcols1; exact: Hguard ).
  Qed.

  Ltac nomw :=
    let w := fresh "w" in let v := fresh "v" in let Hin := fresh "Hin" in
    move=> w v Hin; cbn in Hin;
    repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
    by (case: Hin || exact: (no_mw_reg_clear_read w v Hin)).

  Ltac nomr :=
    let w := fresh "w" in let Hin := fresh "Hin" in
    move=> w Hin; cbn in Hin;
    repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
    by (case: Hin || exact: (no_mr_reg_clear_read w Hin)).

  Lemma silent_next_pc_belong :
    forall (st s' : state) op tpc ti (ts : hseq (tag_type lrc_tags) (inputs op)) updts pc',
      @next_state_updates_and_pc mt ops lrc_tags LRC.transfer unit st
        (IVec (OP op) tpc ti ts) updts pc' = Some (s', None) ->
      pc s' = pc'@tpc /\
      belong (match tpc with Level _ c => c end)
             (match mem st pc' with Some ni => Some (taga ni) | None => None end).
  Proof.
    move=> st s' op tpc ti ts updts pc'.
    rewrite /next_state_updates_and_pc /next_state.
    case Hevi: (evi st) => [evinp|] //=.
    case Hm: (mem st pc') => [ni|] /= Hgoal;
      ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
        case: ov_ev Htr Hk => ov ev Htr Hk;
        case: (obind_inv Hk) => st0 [Hdsu Hfin];
        move: Hfin => [= Hs Hev]; subst ev;
        have Htrpc := op_silent_trpc Htr (erefl None);
        have Hbel := silent_transfer_belong Htr;
        split; by [ rewrite -Hs /= Htrpc | exact: Hbel ] ).
  Qed.

  Lemma pc_code_color_combine : forall (s' : state)
      (mpre : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags Symbolic.M)}) pc' tpc,
    pc s' = pc'@tpc ->
    (forall d, mem s' (vala (pc s')) = Some d -> is_code (taga d) ->
       exists d0, mpre pc' = Some d0 /\ color (taga d0) = color (taga d) /\ is_code (taga d0)) ->
    belong (match tpc with Level _ c => c end)
           (match mpre pc' with Some ni => Some (taga ni) | None => None end) ->
    pc_code_color s'.
  Proof.
    move=> s' mpre pc' tpc Hpc Hrel Hbel d Hd Hcode.
    have Hcol : color_of s' = match tpc with Level _ c => c end by rewrite color_of_pc_tag Hpc.
    case: (Hrel d Hd Hcode) => [d0 [Hd0 [Hcol0 _]]].
    move: Hbel Hcol0; rewrite Hd0 /belong.
    case Et: (taga d0) => [vt ct et bt] /= /eqP Hbel Hcol0.
    by rewrite Hcol Hbel Hcol0.
  Qed.

  Lemma silent_step_pc_code_color :
    forall (s s' : state), step_mp (NC := NC) s s' None -> pc_code_color s'.
  Proof.
    move=> s s' Hstep. inversion Hstep.
    -
      rewrite /next_state_updates in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmm : mem s' = mem s.
      { move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]].
        rewrite Hmem (ndsu_mem_noM (st := s) _ _ Edsu); [ by rewrite ST | nomw | nomr ]. }
      apply: (pc_code_color_combine Hpc _ Hbel) => d Hd Hcode.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    -
      rewrite /next_state_updates in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmm : mem s' = mem s.
      { move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]].
        rewrite Hmem (ndsu_mem_noM (st := s) _ _ Edsu); [ by rewrite ST | nomw | nomr ]. }
      apply: (pc_code_color_combine Hpc _ Hbel) => d Hd Hcode.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    -
      rewrite /next_state_updates in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmm : mem s' = mem s.
      { move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]].
        rewrite Hmem (ndsu_mem_noM (st := s) _ _ Edsu); [ by rewrite ST | nomw | nomr ]. }
      apply: (pc_code_color_combine Hpc _ Hbel) => d Hd Hcode.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    -
      rewrite /next_state_updates in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmm : mem s' = mem s.
      { move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]].
        rewrite Hmem (ndsu_mem_noM (st := s) _ _ Edsu); [ by rewrite ST | nomw | nomr ]. }
      apply: (pc_code_color_combine Hpc _ Hbel) => d Hd Hcode.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    -
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have [Hw0 [Hmem' [Htag Hguard]]] := weak_load_facts ST MEM1 NEXT.
      apply: (pc_code_color_combine Hpc _ Hbel) => d Hd.
      move: Hd; rewrite Hpc /= Hmem' setmE => Hd Hcode.
      move: Hd; case: eqP => [Heq | Hne].
      + move=> [= Hdeq]. exists (w2 @ t2). rewrite Heq Hw0.
        split; [ reflexivity | ]. move: Hcode; rewrite -Hdeq /= switch_val_color switch_val_iscode => Hcode.
        by split.
      + move=> Hd. by exists d.
    -
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have [vnew [oldd [Hw0 [Hmem' [Htag [_ [_ [Hncv _]]]]]]]] := weak_store_facts ST OLD NEXT.
      apply: (pc_code_color_combine Hpc _ Hbel) => d Hd.
      move: Hd; rewrite Hpc /= Hmem' setmE => Hd Hcode.
      move: Hd; case: eqP => [Heq | Hne].
      + move=> [= Hdeq]. subst d. by move: Hcode; rewrite (introF idP Hncv).
      + move=> Hd. by exists d.
    -
      unfold mvec in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmm : mem s' = mem s.
      { move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]].
        rewrite Hmem (ndsu_mem_noM (st := s) _ _ Edsu); [ by rewrite ST | nomw | nomr ]. }
      apply: (pc_code_color_combine Hpc _ Hbel) => d Hd Hcode.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    -
      unfold mvec, pc' in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmm : mem s' = mem s.
      { move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]].
        rewrite Hmem (ndsu_mem_noM (st := s) _ _ Edsu); [ by rewrite ST | nomw | nomr ]. }
      apply: (pc_code_color_combine Hpc _ Hbel) => d Hd Hcode.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    -
      unfold mvec, pc' in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmemcell : mem s (pc0 + 1)%w = Some (vret @ tret) by rewrite ST.
      have Hmm : mem s' = mem s.
      { move: NEXT. rewrite /next_state_updates_and_pc /next_state.
        case Hevi: (evi s) => [evinp|] //=.
        case Hpc'2: (mem s (swcast imm)) => [ni|]; rewrite /=; move=> Hgoal;
          ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
            case: ov_ev Htr Hk => ov ev Htr Hk;
            have Hhead := jal_head_tret Htr;
            move: Hk => /= Hk;
            case: (obind_inv Hk) => st' [Hndsu Hfin];
            move: Hfin => [= Hfins _]; rewrite -Hfins /=;
            apply: (@mem_unchanged_jal s st' (pc0+1)%w vret tret (nseq 12 R) (tr ov)
                      (RegWrite ra (pc0+1)%w :: reg_clear_read) Hmemcell Hhead _ _ Hndsu);
            [ by (move=> w' v' Hin; cbn in Hin;
                  repeat (move: Hin => [Hin|Hin]; [by discriminate|]); case: Hin)
            | by (move=> w' Hin; cbn in Hin;
                  repeat (move: Hin => [Hin|Hin]; [by discriminate|]); case: Hin) ] ). }
      apply: (pc_code_color_combine Hpc _ Hbel) => d Hd Hcode.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    -
      have Halloc := run_syscall_alloc GETCALL CALL.
      exact: (alloc_pc_code_color Halloc).
  Qed.

  Lemma silent_step_color_preserved : forall (s s' : state),
    step_mp (NC := NC) s s' None -> color_of s' = color_of s.
  Proof.
    move=> s s' Hstep.
    suff Htag : taga (pc s') = taga (pc s) by rewrite !color_of_pc_tag Htag.
    inversion Hstep.
    - rewrite /next_state_updates in NEXT. have [Hpc _] := silent_next_pc_belong NEXT. by rewrite Hpc /= ST.
    - rewrite /next_state_updates in NEXT. have [Hpc _] := silent_next_pc_belong NEXT. by rewrite Hpc /= ST.
    - rewrite /next_state_updates in NEXT. have [Hpc _] := silent_next_pc_belong NEXT. by rewrite Hpc /= ST.
    - rewrite /next_state_updates in NEXT. have [Hpc _] := silent_next_pc_belong NEXT. by rewrite Hpc /= ST.
    - have [Hpc _] := silent_next_pc_belong NEXT. by rewrite Hpc /= ST.
    - have [Hpc _] := silent_next_pc_belong NEXT. by rewrite Hpc /= ST.
    - unfold mvec in NEXT. have [Hpc _] := silent_next_pc_belong NEXT. by rewrite Hpc /= ST.
    - unfold mvec, pc' in NEXT. have [Hpc _] := silent_next_pc_belong NEXT. by rewrite Hpc /= ST.
    - unfold mvec, pc' in NEXT. have [Hpc _] := silent_next_pc_belong NEXT. by rewrite Hpc /= ST.
    -
      have Halloc := run_syscall_alloc GETCALL CALL. move: Halloc.
      rewrite /alloc_fun. cbv zeta. move=> H.
      case: (obind_inv H) => ra_val [Hra {}H].
      case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => ret_addr [Hret {}H].
      case: (obind_inv H) => uret [Hretchk {}H].
      move: Hretchk; case: ifP => Hretcol Hretchk; last by []; clear uret Hretchk.
      case: (obind_inv H) => sz [Hsz {}H].
      case: (obind_inv H) => u2 [_ {}H].
      case: (obind_inv H) => len [Hlen {}H].
      case: (obind_inv H) => u3 [_ {}H].
      move: H. case: ifP => // _ H.
      case: (obind_inv H) => addr [Haddr {}H].
      case: (obind_inv H) => regs' [Hregs' {}H].
      by move: H => [= <-].
  Qed.

  Lemma belong_some_eq : forall c (t : tag_type lrc_tags Symbolic.M),
    belong c (Some t) -> c = color t.
  Proof. by move=> c t; case: t => vt ct et bt /= /eqP. Qed.

  Lemma silent_step_pre_pcc : forall (s sfull : state),
    step_mp (NC := NC) s sfull None ->
    forall d, mem s (vala (pc sfull)) = Some d -> is_code (taga d) -> color (taga d) = color_of s.
  Proof.
    move=> s sfull Hstep d.
    have close : forall pc' tpc,
        pc sfull = pc'@tpc -> tpc = taga (pc s) ->
        belong (match tpc with Level _ c => c end)
               (match mem s pc' with Some ni => Some (taga ni) | None => None end) ->
        mem s (vala (pc sfull)) = Some d -> color (taga d) = color_of s.
    { move=> pc' tpc Hpcf Htpc Hbel Hdd.
      move: Hdd; rewrite Hpcf /= => Hdd.
      move: Hbel; rewrite Hdd /= => Hbel.
      have Hbel2 := belong_some_eq Hbel.
      by rewrite (color_of_pc_tag s) -Htpc -Hbel2. }
    inversion Hstep.
    - rewrite /next_state_updates in NEXT. have [Hpc Hbel] := silent_next_pc_belong NEXT.
      move=> Hd _; apply: (close _ _ Hpc _ Hbel Hd); by rewrite ST.
    - rewrite /next_state_updates in NEXT. have [Hpc Hbel] := silent_next_pc_belong NEXT.
      move=> Hd _; apply: (close _ _ Hpc _ Hbel Hd); by rewrite ST.
    - rewrite /next_state_updates in NEXT. have [Hpc Hbel] := silent_next_pc_belong NEXT.
      move=> Hd _; apply: (close _ _ Hpc _ Hbel Hd); by rewrite ST.
    - rewrite /next_state_updates in NEXT. have [Hpc Hbel] := silent_next_pc_belong NEXT.
      move=> Hd _; apply: (close _ _ Hpc _ Hbel Hd); by rewrite ST.
    - have [Hpc Hbel] := silent_next_pc_belong NEXT.
      move=> Hd _; apply: (close _ _ Hpc _ Hbel Hd); by rewrite ST.
    - have [Hpc Hbel] := silent_next_pc_belong NEXT.
      move=> Hd _; apply: (close _ _ Hpc _ Hbel Hd); by rewrite ST.
    - unfold mvec in NEXT. have [Hpc Hbel] := silent_next_pc_belong NEXT.
      move=> Hd _; apply: (close _ _ Hpc _ Hbel Hd); by rewrite ST.
    - unfold mvec, pc' in NEXT. have [Hpc Hbel] := silent_next_pc_belong NEXT.
      move=> Hd _; apply: (close _ _ Hpc _ Hbel Hd); by rewrite ST.
    - unfold mvec, pc' in NEXT. have [Hpc Hbel] := silent_next_pc_belong NEXT.
      move=> Hd _; apply: (close _ _ Hpc _ Hbel Hd); by rewrite ST.
    -
      move=> Hd Hcode. have Halloc := run_syscall_alloc GETCALL CALL. move: Halloc.
      rewrite /alloc_fun. cbv zeta. move=> H.
      case: (obind_inv H) => ra_val [Hra {}H].
      case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => ret_addr [Hret {}H].
      case: (obind_inv H) => uret [Hretchk {}H].
      move: Hretchk; case: ifP => Hretcol Hretchk; last by []; clear uret Hretchk.
      case: (obind_inv H) => sz [Hsz {}H].
      case: (obind_inv H) => u2 [_ {}H].
      case: (obind_inv H) => len [Hlen {}H].
      case: (obind_inv H) => u3 [_ {}H].
      move: H. case: ifP => // _ H.
      case: (obind_inv H) => addr [Haddr {}H].
      case: (obind_inv H) => regs' [Hregs' {}H].
      move: H => [= HSt]. subst sfull.
      move: Hd; rewrite /= Hret => -[= Hdeq]; subst d.
      move: Hretcol => /andP [_ /eqP Hc].
      by rewrite Hc (color_ofE s).
  Qed.

  Lemma pc_incr_pcc : forall (s sfull s' : state),
    step_mp (NC := NC) s sfull None ->
    mem s' = mem s -> vala (pc s') = vala (pc sfull) -> taga (pc s') = taga (pc s) ->
    pc_code_color s'.
  Proof.
    move=> s sfull s' Hstep Hmem Hvala Htaga d.
    rewrite Hmem Hvala => Hd Hcode.
    rewrite (color_of_pc_tag s') Htaga -(color_of_pc_tag s).
    exact: (silent_step_pre_pcc Hstep Hd Hcode).
  Qed.

  Lemma merged_transfer_lrc :
    forall (iv : ivec lrc_tags) (i : ev_inputs)
           (r : vovec lrc_tags (op iv) * option event),
      Merged.transfer iv i = Some r -> LRC.transfer iv i = Some r.
  Proof.
    intros iv i r. destruct iv as [vop tpc ti ts tni]. destruct i as [rc].
    simpl in r. revert ts ti r. destruct vop as [op0|]; intros ts ti r.
    - cbn [Merged.transfer Merged.instr_rules].
      move=> H. apply obind_inv in H. destruct H as [out [Hir Hr]].
      apply obind_inv in Hir. destruct Hir as [u1 [_ Hir]].
      apply obind_inv in Hir. destruct Hir as [u2 [_ Hir]].
      apply obind_inv in Hir. destruct Hir as [o [Hlrc Ho]].
      case: o Hlrc Ho => ov0 ev0 Hlrc Ho.
      case: ov0 Hlrc Ho => t' r' Hlrc Ho.
      move: Ho => /= [= Hout]; subst out.
      move: Hr => /= [= Hr]; subst r.
      apply: LRC.instr_rules_mp_of_strict. exact: Hlrc.
    - by rewrite /Merged.transfer /LRC.transfer.
  Qed.

  Lemma nsu_and_pc_bridge :
    forall (st : state) (kiv : k_ivec lrc_tags) (updts : seq update)
           (pc' : mword mt) (res : _),
      @next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit st kiv updts pc' = Some res ->
      @next_state_updates_and_pc mt ops lrc_tags LRC.transfer    unit st kiv updts pc' = Some res.
  Proof.
    move=> st kiv updts pc' res.
    rewrite /next_state_updates_and_pc /next_state.
    case: (evi st) => [i|] //=.
    case E: (Merged.transfer _ i) => [ov|] //=.
    by rewrite (merged_transfer_lrc E).
  Qed.

  Lemma nsu_bridge :
    forall (st : state) (kiv : k_ivec lrc_tags) (updts : seq update) (res : _),
      @next_state_updates mt ops lrc_tags Merged.transfer unit st kiv updts = Some res ->
      @next_state_updates mt ops lrc_tags LRC.transfer    unit st kiv updts = Some res.
  Proof. move=> st kiv updts res. exact: nsu_and_pc_bridge. Qed.

  Lemma run_syscall_bridge :
    forall (sc : syscall lrc_tags unit) (st : state) (res : _),
      @run_syscall mt ops lrc_tags Merged.transfer unit sc st = Some res ->
      @run_syscall mt ops lrc_tags LRC.transfer    unit sc st = Some res.
  Proof. move=> sc st res. rewrite /run_syscall. by case: (evi st) => [i|] //=. Qed.

  Lemma step_me_mp : forall (s s' : state) ev,
      step_me (NC:=NC) s s' ev -> step_mp (NC:=NC) s s' ev.
  Proof.
    move=> s s' ev H. inversion H;
      [ eapply step_nop | eapply step_const | eapply step_mov | eapply step_binop
      | eapply step_load | eapply step_store | eapply step_jump | eapply step_bnz
      | eapply step_jal | eapply step_syscall ];
      eauto using nsu_bridge, nsu_and_pc_bridge, run_syscall_bridge.
  Qed.

  End PCCM.

End Preservation.
