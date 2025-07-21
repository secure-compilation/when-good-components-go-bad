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

Module Preservation (S: RecompositionContext).

  Module M := RecompositionDefinitions S.
  Include S. Include M.
  (* Import S. Export M. *)

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
    strong_equiv Left M s1' s3'
    /\ weak_equiv Right M s2 s3'
    /\ common_equiv M s1' s2 s3'.
Proof.
  intros s1 s2 s3 M s1' s3' pc1' tpc1' pc3' tpc3' equiv eq_s1' eq_s3' pc1'_pc3' pc1_tag pc3_tag.
  destruct equiv as [strong [weak common]].
  split; [|split].
  - destruct strong as [? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match].
    econstructor; destruct s, s', pc0, pc1; try (subst; intros; auto; done); try congruence.
  - destruct weak as [? ? ? color_eq side_s' s_mem_cor s'_mem_cor entry_off s'_reg_cor mem_match].
    econstructor; try (rewrite eq_s3'; simpl; auto; done); try (subst; intros; auto; done); try congruence.
    subst. destruct s, s', pc0, pc1. simpl in *. trivial.
  - destruct common as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          [mem_pref_cond_s1 [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 col_mem1]]]]]
                          [mem_pref_cond_s2 [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 col_mem2]]]]]
                          [mem_pref_cond_s3 [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 col_mem3]]]]] code_left code_right].
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
      address_correctness Right (vala v') (vtag (taga v')) (mem s3) ->
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
      i_is_pc code_i no_code_v no_code_v' capa_prop1 capa_prop3 correct_v correct_v' correct_v'' eq_m1 eq_m3 eq_s1' eq_s3'.
    destruct equiv as [strong [weak common]].
    pose proof (updm_set eq_m1). pose proof (updm_set eq_m3). subst m1' m3'.
    split; [|split].
    - destruct strong as [? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match];
      econstructor; destruct s, s', pc0, pc1; try (rewrite eq_s1' eq_s3'; simpl; auto; done); try congruence.
      + destruct common as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                            [mem_pref_cond_s1 [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 entry_code1]]]]]]
                            [mem_pref_cond_s2 [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 entry_code2]]]]]]
                            [mem_pref_cond_s3 [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 entry_code3]]]]]]
                            capa_cor1 capa_cor2 capa_cor3 code_left code_right].
        destruct pc_s1_s3 as [? ? ? eq_none|? ? ? ? eq_comp eq_off pc_s1_s3].
        * eapply same_pc_alloc; try rewrite eq_s1'; try rewrite eq_s3'; simpl; auto.
          rewrite setmE.
          remember (@eq_op (Ord.eqType _) (Types.vala (pc s)) w) as cond. simpl in *. rewrite <- Heqcond.
          destruct cond; simpl; auto.
          exfalso. assert (eqw: Types.vala (pc s) = w) by eq_op_to_eq. subst w.
          destruct no_code_w_s1 as [d [d_eq d_nocode]]. rewrite d_eq in eq_none. done.
        * eapply same_pc_normal; eauto.
          -- subst s1'. simpl. rewrite setmE. remember (@eq_op (Ord.eqType _) (Types.vala (pc s)) w) as cond. simpl in *.
             rewrite i_is_pc. rewrite <- Heqcond. eapply (@eq_trans _ _ (Some (if cond then v else i))).
             destruct cond; trivial. subst cond. reflexivity.
          -- subst s1'. destruct s, pc0. simpl in *. exact eq_off.
          -- rewrite eq_s1' eq_s3'. simpl. done.
      + subst. trivial.
      + subst. intros d w' rel deq. simpl. destruct d as [vd [vt ? ? ?]]. simpl.
        remember (@eq_op (Ord.eqType _) w' w) as cond.
        remember (@eq_op (Ord.eqType _) vd w) as cond1.
        simpl in *. rewrite setmE in deq. rewrite <- Heqcond in deq.
        destruct cond; destruct vt; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond1; destruct cond1;
          convert_eq_op; try (simplify_some; simpl in *; auto).
        all: try (destruct correct_v as [? [eq1 imp1]]; destruct no_code_w_s1 as [? [eq2 no_code]];
                  rewrite eq1 in eq2; simplify_some; exfalso; eapply no_code; eapply imp1;
                  rewrite <- (same_color _ (or_introl eq1)); trivial).
        all: try eapply (s_mem_cor _ w' _ deq).
        all: try (eapply modusponens; [eapply (s_mem_cor _ w' _ deq) | ]; simpl; intros [v'' [v''eq v''code]];
                  destruct no_code_w_s1 as [d' [d'eq d'code]]; rewrite d'eq in v''eq; simplify_some;
                  exfalso; eapply d'code; eapply v''code; rewrite <- (same_color _ (or_introl d'eq)); trivial).
      + subst. intros d w' rel deq. simpl. destruct d as [vd [vt ? ? ?]]. simpl.
        remember (@eq_op (Ord.eqType _) w' w) as cond.
        remember (@eq_op (Ord.eqType _) vd w) as cond1.
        simpl in *. rewrite setmE in deq. rewrite <- Heqcond in deq.
        destruct cond; destruct vt; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond1; destruct cond1;
          convert_eq_op; try (simplify_some; simpl in *; auto).
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
        remember (@eq_op (Ord.eqType _) vd w) as cond.
        destruct vt; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond; destruct cond;
          convert_eq_op;
          try eapply (s_reg_cor _ w' deq);
          try (eapply modusponens; [eapply (s_reg_cor _ w' deq) | ]; simpl; intros [v'' [v''eq v''code]];
                  destruct no_code_w_s1 as [d' [d'eq d'code]]; rewrite d'eq in v''eq; simplify_some;
                  exfalso; eapply d'code; eapply v''code; rewrite <- (same_color _ (or_introl d'eq)); trivial).
      + subst. intros d w' deq. simpl. destruct d as [vd vt].
        remember (@eq_op (Ord.eqType _) vd w) as cond.
        destruct vt; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond; destruct cond;
          convert_eq_op;
          try eapply (s'_reg_cor _ w' deq);
          try (eapply modusponens; [eapply (s'_reg_cor _ w' deq) | ]; simpl; intros [v'' [v''eq v''code]];
                  destruct no_code_w_s3 as [d' [d'eq d'code]]; rewrite d'eq in v''eq; simplify_some;
                  exfalso; eapply d'code; eapply v''code; rewrite <- (same_color _ (or_intror d'eq)); trivial).
      + unfold memory_match in *. rewrite eq_s1' eq_s3'. simpl.
        intros.
        rewrite setmE. rewrite setmE.
        remember (@eq_op (Ord.eqType _) w0 w) as cond. destruct cond.
        * split; intro eq; inv eq; eexists; split; eauto.
        * apply mem_match; auto.
    - destruct weak as [? ? ? color_eq side_s' s_mem_cor s'_mem_cor entry_off s'_reg_cor mem_match];
      econstructor; destruct s, s', pc0, pc1; subst; auto.
      + subst. intros d w' rel deq. simpl. destruct d as [vd [vt ? ? ?]]. simpl.
        remember (@eq_op (Ord.eqType _) w' w) as cond.
        remember (@eq_op (Ord.eqType _) vd w) as cond1.
        simpl in *. rewrite setmE in deq. rewrite <- Heqcond in deq.
        destruct cond; destruct vt; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond1; destruct cond1;
          convert_eq_op; try (simplify_some; simpl in *; auto).
        all: try (destruct correct_v'' as [? [eq1 imp1]]; destruct no_code_w_s3 as [? [eq2 no_code]];
                  rewrite eq1 in eq2; simplify_some; exfalso; eapply no_code; eapply imp1;
                  rewrite <- (same_color _ (or_intror eq1)); congruence).
        all: try eapply (s'_mem_cor _ w' _ deq).
        all: try (eapply modusponens; [eapply (s'_mem_cor _ w' _ deq) | ]; simpl; intros [v'' [v''eq v''code]];
                  destruct no_code_w_s3 as [d' [d'eq d'code]]; rewrite d'eq in v''eq; simplify_some;
                  eexists; split;[eauto|]; intro in_ic; rewrite v_color in v_relevant; exfalso;
                  eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto;
                  inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto).
      + subst. simpl. intros col w' w'' d d' proc l l' rel eqw' eqw'' dcode d'code dcol d'col d_e_eq d'_e_eq.
        rewrite setmE in eqw''.
        unfold_match' eqw''; try convert_eq_op; try simplify_some; try contradiction.
        eapply (entry_off); eauto.
      + subst. intros d w' deq. simpl. destruct d as [vd vt].
        remember (@eq_op (Ord.eqType _) vd w) as cond.
        destruct vt; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond; destruct cond; convert_eq_op.
          all: try eapply (s'_reg_cor _ w' deq).
          all: try (eapply modusponens; [eapply (s'_reg_cor _ w' deq) | ]; simpl; intros [v'' [v''eq v''code]];
                    destruct no_code_w_s3 as [d' [d'eq d'code]]; rewrite d'eq in v''eq; simplify_some).
          all: eexists; split; [eauto |]; intro v_in_ic; exfalso;
            eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic) _ (color (Types.taga v)));
            inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto; rewrite v_color; eauto.
      + unfold memory_match in *. simpl.
        intros.
        rewrite setmE.
        remember (@eq_op (Ord.eqType _) w0 w) as cond. destruct cond.
        * assert (eq_w: w0 = w) by eq_op_to_eq.
          subst. simpl in *. split; intro eq; inv eq; exfalso.
          -- remember (mem1 w) as v_opt. destruct v_opt as [d'|].
             ++ assert (color (Types.taga d) = color (Types.taga d')) by (rewrite <- v_color; eapply same_color; auto). simpl in v_relevant.
                { eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
                  inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. rewrite <- v_color. auto. }
             ++ simpl in v_relevant.
                { eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
                  inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. rewrite <- v_color. auto. }
          -- pose proof (mem_match w d H H0) as [_ d_impl].
             destruct (d_impl H2) as [d' [d_d'_match eq_d']].
             assert (d'_color: color (Types.taga v) = color (Types.taga d')) by (eapply same_color; auto).
             rewrite d'_color in v_relevant. assert (d'_color_bis: (color (Types.taga d') = color (Types.taga d))).
             { destruct d, d'. simpl. unfold data_match' in d_d'_match. destruct d_d'_match. subst. done. }
             rewrite <- d'_color_bis in H0. simpl in *.
             { eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
               inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. }
        * apply mem_match; auto.
    - destruct common as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                            [mem_pref_cond_s1 [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 entry_code1]]]]]]
                            [mem_pref_cond_s2 [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 entry_code2]]]]]]
                            [mem_pref_cond_s3 [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 entry_code3]]]]]]
                            capa_cor1 capa_cor2 capa_cor3 code_left code_right].
      eapply common_equiv_def with (n := n) (c := c0);
        try ((rewrite eq_s1' eq_s3' || rewrite eq_s1' || rewrite eq_s3'); simpl; auto; done); try congruence; try done;
        try (split; [|split; [|split; [|split; [|split; [|split]]]]]).
      + rewrite eq_s3'. simpl. clear strong weak code_left code_right v_match tag_pc1 tag_pc2 tag_pc3 capa_cor1 capa_cor2 capa_cor3.
        clear capa_prop1 capa_prop3.
        simpl in *.
        induction wfst; intros.
        * eapply wf_stack_empty; eauto.
        * eapply wf_stack_cons_left; eauto.
          -- rewrite eq_s1'. simpl.
             unfold points_to_comp_code'. rewrite setmE.
             remember (@eq_op (Ord.eqType _) v1 w) as cond. unfold mt, concrete_int_32_mt, word_size in Heqcond.
             destruct cond; try exact PTS_CODE1.
             assert (eq_w: v1 = w) by eq_op_to_eq. subst v1.
             exfalso. unfold points_to_comp_code' in PTS_CODE1.
             oapp_False.
             destruct PTS_CODE1 as [color_a [[_ side_of_C] | code_a]].
             ++ simpl in SIDE. unfold side_of in *. rewrite SIDE in side_of_C. inv side_of_C.
             ++ destruct no_code_w_s1 as [d [d_eq d_nocode]]. rewrite d_eq in HeqH. simplify_some. done.
          -- simpl.
             unfold points_to_comp_code. rewrite setmE.
             remember (@eq_op (Ord.eqType _) v3 w) as cond. unfold mt, concrete_int_32_mt, word_size in Heqcond.
             destruct cond; try exact PTS_CODE3.
             assert (eq_w: v3 = w) by eq_op_to_eq. subst w.
             exfalso. unfold points_to_comp_code in PTS_CODE3.
             oapp_False.
             destruct PTS_CODE3 as [color_a code_a].
             destruct no_code_w_s3 as [d [d_eq d_nocode]]. rewrite d_eq in HeqH. simplify_some. done.
        * eapply wf_stack_cons_right; eauto.
          -- rewrite eq_s1'. simpl.
             unfold points_to_comp_code'. rewrite setmE.
             remember (@eq_op (Ord.eqType _) v1 w) as cond. unfold mt, concrete_int_32_mt, word_size in Heqcond.
             destruct cond; try exact PTS_CODE1.
             assert (eq_w: v1 = w) by eq_op_to_eq. subst v1. simpl.
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
             remember (@eq_op (Ord.eqType _) v3 w) as cond. unfold mt, concrete_int_32_mt, word_size in Heqcond.
             destruct cond; try exact PTS_CODE3.
             assert (eq_w: v3 = w) by eq_op_to_eq. subst w.
             exfalso. unfold points_to_comp_code in PTS_CODE3.
             oapp_False.
             destruct PTS_CODE3 as [color_a code_a].
             destruct no_code_w_s3 as [d [d_eq d_nocode]]. rewrite d_eq in HeqH. simplify_some. done.
      + clear -same_color no_code_v no_code_w_s1 eq_m1 eq_s1' mem_pref_cond_s1.
        subst s1'.
        move: mem_pref_cond_s1.
        simpl.
        rewrite /memory_prefix_condition => H c.
        move: {H} (H c) => //=.
        assert (H: domm (mem s1) = domm (setm (mem s1) w v)).
        { apply eq_fset => x. rewrite !mem_domm.
          rewrite setmE; case: ifP => //=.
          move=> /eqP ->.
          move: eq_m1; rewrite /updm.
          case: ifP => //=. }
        rewrite H. move=> ->.
        move: H => /eq_fset H.
        assert (G: domm
                  (filterm (fun=> (fun v0 : atom (mword mt) mem_tag => (color (taga v0) == c) && ~~ is_code (taga v0))) (mem s1)) =
                  domm
                    (filterm (fun=> (fun v0 : atom (mword mt) mem_tag => (color (taga v0) == c) && ~~ is_code (taga v0))) (setm (mem s1) w v))).
        { apply eq_fset => x; rewrite !mem_domm.
          rewrite !filtermE.
          destruct (mem s1 x) eqn:mem_s1_x; specialize (H x); rewrite !mem_domm in H.
          - rewrite mem_s1_x; rewrite mem_s1_x in H; destruct (setm (mem s1) w v x) eqn:mem_s1'_x; inv H.
            specialize (same_color a).
            rewrite mem_s1'_x. simpl.
            move: mem_s1'_x mem_s1_x.
            rewrite setmE. case: ifP => /eqP.
            + intros eq0; subst.
              move=> [] eq1; subst.
              intros mem_s1_w.
              destruct no_code_w_s1 as [d [? no_code_w]].
              assert (a = d) by congruence; subst d.
              move: no_code_w => /negP ->.
              move: no_code_v => /negP ->.
              rewrite same_color; eauto.
              case: ifP => //=.
            + move=> _ ? ?; assert (a0 = a) by congruence; now subst a0.
          - rewrite mem_s1_x; rewrite mem_s1_x in H; destruct (setm (mem s1) w v x) eqn:mem_s1'_x; inv H.
            rewrite mem_s1'_x. simpl. reflexivity. }
        now rewrite G.
      + clear -same_color no_code_v no_code_w_s1 eq_m1 eq_s1' code_pref_cond_s1.
        subst s1'.
        move: code_pref_cond_s1.
        simpl.
        rewrite /code_prefix_condition => H w' v'.
        rewrite setmE. case: ifP => /eqP.
        * move=> ? [] ?; subst. now auto.
        * move=> _.
          apply H.
      + unfold alloc_empty in *. subst. simpl in *. rewrite setmE.
        remember (@eq_op (Ord.eqType _) (word_of_nat alloc_label) w) as cond.
        destruct cond; try (eapply (alloc_mem_s1)). exfalso.
        rewrite eq_sym in Heqcond. convert_eq_op.
        unfold updm in eq_m1. rewrite alloc_mem_s1 in eq_m1. simpl in eq_m1. inversion eq_m1.
      + intros d w' deq dcode. subst. simpl in deq. rewrite setmE in deq.
        remember (@eq_op (Ord.eqType _) d w) as cond. simpl in *. rewrite <- Heqcond in deq.
        destruct cond; try (simplify_some; contradiction).
        (pose proof (bnz_s1 d w' deq dcode)). simpl in *. unfold_bind. simpl.
        goal_match_bind_step; try done; try destruct H as [? [eq1 ?]].
        -- remember (@eq_op (Ord.eqType _) (d + swcast i0)%w w) as cond1; destruct cond1;
             eexists; simpl in *; rewrite setmE; rewrite <- Heqcond1.
           ++ destruct no_code_w_s1 as [? [eq2 ?]]. convert_eq_op. rewrite eq2 in eq1. simplify_some. contradiction.
           ++ split; [exact eq1 | done].
        -- destruct H as [[? [eq1 ?]] | eq_alloc]; try (right; done).
            left; remember (@eq_op (Ord.eqType _) (swcast i0)%w w) as cond1; destruct cond1;
             eexists; simpl in *; rewrite setmE; rewrite <- Heqcond1.
          ++ destruct no_code_w_s1 as [? [eq2 ?]]. convert_eq_op. rewrite eq2 in eq1. simplify_some. contradiction.
          ++ split; [exact eq1 | done].
      + unfold end_condition in *. intros w0 v0 v0_eq v0_code.
        rewrite eq_s1' in v0_eq. simpl in v0_eq. rewrite setmE in v0_eq.
        remember (@eq_op (Ord.eqType _) w0 w) as cond. simpl in Heqcond. rewrite <- Heqcond in v0_eq. destruct cond.
        * simplify_some. contradiction.
        * destruct (end_s1 w0 v0 v0_eq v0_code); [left | right]; auto. destruct H as [v1 [v1_eq v1_code]].
          exists v1. rewrite eq_s1'. rewrite setmE.
          remember (@eq_op (Ord.eqType _) (addw w0 onew) w) as cond. destruct cond; try (split; done).
          exfalso. assert ((addw w0 onew) = w) by eq_op_to_eq. subst w.
          destruct no_code_w_s1 as [? [eq no_code]]. rewrite eq in v1_eq. simplify_some. done.
      + intros w' d deq. subst. simpl in deq.
        rewrite setmE in deq. unfold_match' deq; try convert_eq_op; try simplify_some.
        simpl in v_relevant. left. eapply ((fst (Extra.In_in _ _)) v_relevant).
        eapply col_mem1; eauto.
      + intros w' d e deq dent.
        rewrite eq_s1' in deq. rewrite setmE in deq. unfold_match' deq.
        * exfalso. convert_eq_op. simplify_some. rewrite no_entry in dent. inversion dent.
        * eapply entry_code1; eauto.
      + clear -same_color no_code_v' v_color no_code_w_s3 eq_m3 eq_s3' mem_pref_cond_s3.
        subst s3'.
        move: mem_pref_cond_s3.
        simpl.
        rewrite /memory_prefix_condition => H c.
        move: {H} (H c) => //=.
        assert (H: domm (mem s3) = domm (setm (mem s3) w v')).
        { apply eq_fset => x. rewrite !mem_domm.
          rewrite setmE; case: ifP => //=.
          move=> /eqP ->.
          move: eq_m3; rewrite /updm.
          case: ifP => //=. }
        rewrite H. move=> ->.
        move: H => /eq_fset H.
        assert (G: domm
                  (filterm (fun=> (fun v0 : atom (mword mt) mem_tag => (color (taga v0) == c) && ~~ is_code (taga v0))) (mem s3)) =
                  domm
                    (filterm (fun=> (fun v0 : atom (mword mt) mem_tag => (color (taga v0) == c) && ~~ is_code (taga v0))) (setm (mem s3) w v'))).
        { apply eq_fset => x; rewrite !mem_domm.
          rewrite !filtermE.
          destruct (mem s3 x) eqn:mem_s3_x; specialize (H x); rewrite !mem_domm in H.
          - rewrite mem_s3_x; rewrite mem_s3_x in H; destruct (setm (mem s3) w v' x) eqn:mem_s3'_x; inv H.
            specialize (same_color a).
            rewrite mem_s3'_x. simpl.
            move: mem_s3'_x mem_s3_x.
            rewrite setmE. case: ifP => /eqP.
            + intros eq0; subst.
              move=> [] eq3; subst.
              intros mem_s3_w.
              destruct no_code_w_s3 as [d [? no_code_w]].
              assert (a = d) by congruence; subst d.
              move: no_code_w => /negP ->.
              move: no_code_v' => /negP ->.
              rewrite v_color in same_color.
              rewrite same_color; eauto.
              case: ifP => //=.
            + move=> _ ? ?; assert (a0 = a) by congruence; now subst a0.
          - rewrite mem_s3_x; rewrite mem_s3_x in H; destruct (setm (mem s3) w v' x) eqn:mem_s3'_x; inv H.
            rewrite mem_s3'_x. simpl. reflexivity. }
        now rewrite G.
      + clear -same_color no_code_v' no_code_w_s3 eq_m3 eq_s3' code_pref_cond_s3.
        subst s3'.
        move: code_pref_cond_s3.
        simpl.
        rewrite /code_prefix_condition => H w' v''.
        rewrite setmE. case: ifP => /eqP.
        * move=> ? [] ?; subst. now auto.
        * move=> _.
          apply H.
      + unfold alloc_empty in *. subst. simpl in *. rewrite setmE.
        remember (@eq_op (Ord.eqType _) (word_of_nat alloc_label) w) as cond.
        destruct cond; try (eapply (alloc_mem_s3)). exfalso.
        rewrite eq_sym in Heqcond. convert_eq_op.
        unfold updm in eq_m1. rewrite alloc_mem_s1 in eq_m1. simpl in eq_m1. inversion eq_m1.
      + intros d w' deq dcode. subst. simpl in deq. rewrite setmE in deq.
        remember (@eq_op (Ord.eqType _) d w) as cond. simpl in *. rewrite <- Heqcond in deq.
        destruct cond; try (simplify_some; contradiction).
        (pose proof (bnz_s3 d w' deq dcode)). simpl in *. unfold_bind. simpl.
        goal_match_bind_step; try done; try destruct H as [? [eq1 ?]].
        -- remember (@eq_op (Ord.eqType _) (d + swcast i0)%w w) as cond1; destruct cond1;
             eexists; simpl in *; rewrite setmE; rewrite <- Heqcond1.
           ++ destruct no_code_w_s3 as [? [eq2 ?]]. convert_eq_op. rewrite eq2 in eq1. simplify_some. contradiction.
           ++ split; [exact eq1 | done].
        -- destruct H as [[? [eq1 ?]] | eq_alloc]; try (right; done).
           left; remember (@eq_op (Ord.eqType _) (swcast i0)%w w) as cond1; destruct cond1;
             eexists; simpl in *; rewrite setmE; rewrite <- Heqcond1.
          ++ destruct no_code_w_s3 as [? [eq2 ?]]. convert_eq_op. rewrite eq2 in eq1. simplify_some. contradiction.
          ++ split; [exact eq1 | done].
      + unfold end_condition in *. intros w0 v0 v0_eq v0_code.
        rewrite eq_s3' in v0_eq. simpl in v0_eq. rewrite setmE in v0_eq.
        remember (@eq_op (Ord.eqType _) w0 w) as cond. simpl in Heqcond. rewrite <- Heqcond in v0_eq. destruct cond.
        * simplify_some. contradiction.
        * destruct (end_s3 w0 v0 v0_eq v0_code); [left | right]; auto. destruct H as [v1 [v1_eq v1_code]].
          exists v1. rewrite eq_s3'. rewrite setmE.
          remember (@eq_op (Ord.eqType _) (addw w0 onew) w) as cond. destruct cond; try (split; done).
          exfalso. assert ((addw w0 onew) = w) by eq_op_to_eq. subst w.
          destruct no_code_w_s3 as [? [eq no_code]]. rewrite eq in v1_eq. simplify_some. done.
      + intros w' d deq. subst. simpl in deq.
        rewrite setmE in deq. unfold_match' deq; try convert_eq_op; try simplify_some.
        rewrite v_color in v_relevant. simpl in v_relevant. left. eapply ((fst (Extra.In_in _ _)) v_relevant).
        eapply col_mem3; eauto.
      + intros w' d e deq dent.
        rewrite eq_s3' in deq. rewrite setmE in deq. unfold_match' deq.
        * exfalso. convert_eq_op. simplify_some. destruct v, d. destruct v_match as [tag_eq ?]. rewrite <- tag_eq in dent.
          rewrite no_entry in dent. inversion dent.
        * eapply entry_code3; eauto.
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
        remember (@eq_op (Ord.eqType _) w'' w) as cond1.
        remember (@eq_op (Ord.eqType _) w' w) as cond2.
        unfold mt, concrete_int_32_mt, word_size in Heqcond1, Heqcond2.
        simpl in Heqcond1, Heqcond2.
        rewrite <- Heqcond1, <- Heqcond2.
        destruct v as [? vt], v' as [? vt']. inversion v_match. subst vt'.
        pose proof (code_left w' d t off comp relevant_comp offset v'_code v'_color) as [impll implr].
        destruct cond1; destruct cond2; convert_eq_op; simpl; split; intro eq; try simplify_some; subst.
        all: try contradiction.
        * destruct (impll eq) as [? [? eq1]]. destruct no_code_w_s3 as [? [eq2 ?]]. rewrite eq1 in eq2. simplify_some. contradiction.
        * destruct (implr eq) as [? [? eq1]]. destruct no_code_w_s1 as [? [eq2 ?]]. rewrite eq1 in eq2. simplify_some. contradiction.
        * destruct (impll eq) as [d' [decode_d' d'_eq]]. exists d'. split; auto.
          inversion decode_d'; subst.
          -- econstructor; trivial.
          -- eapply decode_match_alloc_JAL; trivial.
          -- eapply decode_match_JAL. exact H. exact H1.
             rewrite setmE.
             destruct (@eq_op (Ord.eqType _) (swcast imm) w) eqn:cond1; repeat simplify_some.
             { exfalso. pose proof (esym cond1). convert_eq_op. destruct no_code_w_s1 as [? [eq1 ?]].
               rewrite H2 in eq1. simplify_some. tauto. }
             { exact H2. }
             rewrite setmE.
             destruct (@eq_op (Ord.eqType _) (swcast imm') w) eqn:cond1; repeat simplify_some.
             { exfalso. pose proof (esym cond1). convert_eq_op. destruct no_code_w_s3 as [? [eq1 ?]].
               rewrite H3 in eq1. simplify_some. rewrite H5 in H4. tauto. }
             { exact H3. }
             all: trivial.
        * destruct (implr eq) as [d' [decode_d' d'_eq]]. exists d'. split; auto.
          inversion decode_d'; subst.
          -- econstructor; trivial.
          -- eapply decode_match_alloc_JAL; trivial.
          -- eapply decode_match_JAL. exact H. exact H1.
             rewrite setmE.
             destruct (@eq_op (Ord.eqType _) (swcast imm) w) eqn:cond1; repeat simplify_some.
             { exfalso. pose proof (esym cond1). convert_eq_op. destruct no_code_w_s1 as [? [eq1 ?]].
               rewrite H2 in eq1. simplify_some. tauto. }
             { exact H2. }
             rewrite setmE.
             destruct (@eq_op (Ord.eqType _) (swcast imm') w) eqn:cond1; repeat simplify_some.
             { exfalso. pose proof (esym cond1). convert_eq_op. destruct no_code_w_s3 as [? [eq1 ?]].
               rewrite H3 in eq1. simplify_some. rewrite H5 in H4. tauto. }
             { exact H3. }
             all: trivial.
      +  unfold combined_codes. intros w' d t off comp relevant_comp offset v'_code v'_color.
        remember (addw w' (as_word off)) as w''. subst s1' s3'. simpl.
        repeat rewrite setmE.
        remember (@eq_op (Ord.eqType _) w'' w) as cond. unfold mt, concrete_int_32_mt, word_size in Heqcond.
        simpl in Heqcond.
        rewrite <- Heqcond.
        destruct v as [? vt], v' as [? vt']. inversion v_match. subst vt'.
        pose proof (code_right w' d t off comp relevant_comp offset v'_code v'_color) as [impll implr].
        destruct cond; convert_eq_op; simpl; split; intro eq; try simplify_some; subst.
        all: try contradiction.
        destruct (impll eq) as [? [? eq1]]. destruct no_code_w_s3 as [? [eq2 ?]]. rewrite eq1 in eq2. simplify_some. contradiction.
        * destruct (impll eq) as [d' [decode_d' d'_eq]]. exists d'. split; auto.
          inversion decode_d'; subst.
          -- econstructor; trivial.
          -- eapply decode_match_alloc_JAL; trivial.
          -- eapply decode_match_JAL. exact H. exact H1.
             exact H2.
             rewrite setmE.
             destruct (@eq_op (Ord.eqType _) (swcast imm') w) eqn:cond1; repeat simplify_some.
             { exfalso. pose proof (esym cond1). convert_eq_op. destruct no_code_w_s3 as [? [eq1 ?]].
               rewrite H3 in eq1. simplify_some. rewrite H5 in H4. tauto. }
             { exact H3. }
             all: trivial.
        * destruct (implr eq) as [d' [decode_d' d'_eq]]. exists d'. split; auto.
          inversion decode_d'; subst.
          -- econstructor; trivial.
          -- eapply decode_match_alloc_JAL; trivial.
          -- eapply decode_match_JAL. exact H. exact H1.
             exact H2.
             rewrite setmE.
             destruct (@eq_op (Ord.eqType _) (swcast imm') w) eqn:cond1; repeat simplify_some.
             { exfalso. pose proof (esym cond1). convert_eq_op. destruct no_code_w_s3 as [? [eq1 ?]].
               rewrite H3 in eq1. simplify_some. rewrite H5 in H4. tauto. }
             { exact H3. }
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
      address_correctness Right (vala v') (taga v') (mem s3) ->
      updm (regs s1) r v = Some r1' ->
      updm (regs s3) r v' = Some r3' ->
      s1' = State _ _ (mem s1) r1' (pc s1) tt ->
      s3' = State _ _ (mem s3) r3' (pc s3) tt ->
      strong_equiv Left M s1' s3'
      /\ weak_equiv Right M s2 s3'
      /\ common_equiv M s1' s2 s3'.
  Proof.
    intros s1 s2 s3 M s1' s3' r v v' r1' r3' equiv v_match
      capa_prop1 capa_prop3 correct_v correct_v' correct_v'' eq_r1 eq_r3 eq_s1' eq_s3'.
    destruct equiv as [strong [weak common]].
    destruct common as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          [mem_pref_cond_s1 [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 entry_code1]]]]]]
                          [mem_pref_cond_s2 [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 entry_code2]]]]]]
                          [mem_pref_cond_s3 [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 entry_code3]]]]]]
                          capa_cor1 capa_cor2 capa_cor3 code_left code_right].
    pose proof (updm_set eq_r1). pose proof (updm_set eq_r3). subst r1' r3'.
    split; [|split].
    - destruct strong as [? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match].
      econstructor; destruct s, s', pc0, pc1; try (rewrite eq_s1' eq_s3'; simpl; auto; done); try (subst; simpl; trivial; done); try congruence.
      + destruct pc_s1_s3 as [? ? ? eq_none|? ? ? ? eq_comp eq_off pc_s1_s3].
        * eapply same_pc_alloc; try rewrite eq_s1'; try rewrite eq_s3'; auto.
        * eapply same_pc_normal; eauto. subst. simpl. exact eq_comp.
          subst. simpl. destruct s, pc0. exact eq_off.
          rewrite eq_s1' eq_s3'. simpl. done.
      + subst. intros d w' deq. simpl in *. auto. destruct d as [vd vt].
        rewrite setmE in deq. remember (@eq_op (Ord.eqType _) w' r) as cond.
        destruct vt; simpl; auto; destruct cond;
          try eapply (s_reg_cor _ w' deq).
          try (convert_eq_op; try simplify_some; eapply correct_v).
          convert_eq_op. simplify_some. simpl in correct_v. done.
      + subst. intros d w' deq. simpl in *. auto. destruct d as [vd vt].
        rewrite setmE in deq. remember (@eq_op (Ord.eqType _) w' r) as cond.
        destruct vt; simpl; auto; destruct cond;
          try eapply (s'_reg_cor _ w' deq);
          try (convert_eq_op; try simplify_some; eapply correct_v').
      + unfold registers_match in *. rewrite eq_s1' eq_s3'. simpl.
        intros. rewrite setmE. rewrite setmE.
        remember (@eq_op (Ord.eqType _) w r) as cond. destruct cond.
        * split; intro eq; simplify_some; eauto.
        * apply reg_match; auto.
    - destruct weak as [? ? s3 color_eq side_s' s_mem_cor s'_mem_cor entry_off s'_reg_cor mem_match].
      econstructor; try (rewrite eq_s3'; simpl; auto; done); try congruence.
      destruct s, s3, pc0, pc1. subst. simpl. auto. trivial.
      + intros d r' deq. subst. rewrite setmE in deq. unfold_match' deq.
        convert_eq_op. simpl. simplify_some. trivial.
        eapply (s'_reg_cor d r' deq).
    - eapply common_equiv_def with (n := n) (c := c0);
        try ((rewrite eq_s1' eq_s3' || rewrite eq_s1' || rewrite eq_s3'); simpl; auto; done); try congruence; try done.
      + subst. unfold register_domm. simpl. rewrite domm_set.
        unfold register_domm, reg_field_size in *. simpl in *. unfold updm in eq_r1. unfold_match' eq_r1.
        clear -Heqa reg_domm1.
        rewrite fsetU1in //= mem_domm //=.
      + subst. unfold register_domm. simpl. rewrite domm_set.
        unfold register_domm, reg_field_size in *. simpl in *. unfold updm in eq_r3. unfold_match' eq_r3.
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
      1-4,6-9: reflexivity.
      clear. remember (word_size mt) as n. clear.
      induction n; auto. simpl.
      unfold expn in *. simpl. rewrite <- IHn.
      destruct n; auto; simpl.
    - simpl.
      case: ifP => /eqP H.
      + simpl.
        destruct List.filter eqn:? => //=.
      + eauto.
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

    import_context.

    intros s1 s2 s3 M s1' s3' equiv eq_s1' eq_s3'.
    destruct equiv as [strong [weak common]].
    unfold alloc_fun in *.
    repeat (unfold_all || unfold_match).
    unfold is_jump, is_other in *.
    repeat (unfold_all || unfold_match).
    destruct a as [v tmp]. destruct a2 as [v' tmp']. simpl in *. subst tmp tmp'.
    rename n into n'.
    inversion common as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          [mem_pref_cond_s1 [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 entry_code1]]]]]]
                          [mem_pref_cond_s2 [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 entry_code2]]]]]]
                          [mem_pref_cond_s3 [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 entry_code3]]]]]]
                          capa_cor1 capa_cor2 capa_cor3 code_left code_right].
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
    split; [|split].
    - destruct strong as [? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match].
      econstructor; try (destruct s, s', pc0, pc1; try (rewrite eq_s1' eq_s3'; simpl; auto; done); try congruence; simpl; done).
      + pose proof ((fst (reg_match _ v@InternalJump)) (esym Heqa)) as [d' [d'match d'eq]].
        simpl in *. rewrite <- Heqa4 in d'eq. simplify_some. destruct d' as [? taga1].
        destruct d'match as [? ?]. subst taga1. oapp_False.
        pose proof (s_reg_cor _ _ (esym Heqa4)). destruct H as [? [eq ?]].
        eapply same_pc_normal; simpl; try done; eauto.
        rewrite unionmE. rewrite eq. simpl. trivial.
        destruct s, s', pc0, pc1. rewrite HeqH. simpl. trivial.
      + intros d w rel d_eq. simpl. destruct d as [vd td]. destruct td.
        destruct vtag; simpl; auto.
        all: rewrite unionmE; rewrite unionmE in d_eq; simpl in *.
        all: remember (mem s w) as cond; simpl in *.
        all: rewrite <- Heqcond in d_eq; destruct cond; simpl in *.
        all: try (pose proof (s_mem_cor a w ); simplify_some; simpl in *;
                  pose proof (H rel (esym Heqcond)) as [d' [d'eq d'cond]];
                  rewrite d'eq; simpl; eauto).
        all: exfalso; clear - d_eq.
        all: unfold mkfmap, mkseq, foldr, map in *.
        all: remember (iota 0 n') as l; clear Heql.
        all: induction l; simpl in *; try (inversion d_eq; done).
        all: rewrite setmE in d_eq; unfold_match; simpl in *; auto.
      + intros d w rel d_eq. simpl. destruct d as [vd td]. destruct td.
        destruct vtag; simpl; auto.
        all: rewrite unionmE; rewrite unionmE in d_eq; simpl in *.
        all: remember (mem s' w) as cond; simpl in *.
        all: rewrite <- Heqcond in d_eq; destruct cond; simpl in *.
        all: try (pose proof (s'_mem_cor a w ); simplify_some; simpl in *;
                  pose proof (H rel (esym Heqcond)) as [d' [d'eq d'cond]];
                  rewrite d'eq; simpl; eauto).
        all: exfalso; clear - d_eq.
        all: unfold mkfmap, mkseq, foldr, map in *.
        all: remember (iota 0 n') as l; clear Heql.
        all: induction l; simpl in *; try (inversion d_eq; done).
        all: rewrite setmE in d_eq; unfold_match; simpl in *; auto.
      + subst. simpl. intros col w' w'' d d' proc l l' rel eqw' eqw'' dcode d'code dcol d'col d_e_eq d'_e_eq.
        rewrite unionmE in eqw'. rewrite unionmE in eqw''.
        unfold_match' eqw'; unfold_match' eqw''.
        * eapply entry_off; eauto.
        * assert (~ (is_code (taga d'))).
          { apply (@mkfmap_Some _ _ _ w'' d') in eqw''.
            move: eqw'' => //=. rewrite /mkseq.
            move=> /mapP [] x x_in_iota [] w''_eq -> //=. }
          tauto.
        * assert (~ (is_code (taga d))).
          {
            apply (@mkfmap_Some _ _ _ w' d) in eqw'.
            move: eqw' => //=. rewrite /mkseq.
            move=> /mapP [] x x_in_iota [] w'_eq -> //=. }
          tauto.
        * assert (~ (is_code (taga d'))).
          { clear -eqw''.
            apply (@mkfmap_Some _ _ _ w'' d') in eqw''.
            move: eqw'' => //=. rewrite /mkseq.
            move=> /mapP [] x x_in_iota [] w''_eq -> //=. }
          tauto.
      + intros d w d_eq. simpl in *. destruct d as [vd td].
        destruct td; simpl; auto.
        all: rewrite unionmE; rewrite setmE in d_eq; simpl in *.
        all: remember (@eq_op (Ord.eqType _) w (as_word (ssrint.Posz 16))) as cond; simpl in *.
        all: destruct cond; simpl in *.
        all: try simplify_some.
        all: pose proof (s_reg_cor _ w d_eq) as H; simpl in H; destruct H as [d' [? ?]].
        all: rewrite H; simpl; eauto.
      + intros d w d_eq. simpl in *. destruct d as [vd td].
        destruct td; simpl; auto.
        all: rewrite unionmE; rewrite setmE in d_eq; simpl in *.
        all: remember (@eq_op (Ord.eqType _) w (as_word (ssrint.Posz 16))) as cond; simpl in *.
        all: destruct cond; simpl in *.
        all: try simplify_some.
        all: pose proof (s'_reg_cor _ w d_eq) as H; simpl in H; destruct H as [d' [? ?]].
        all: rewrite H; simpl; eauto.
      + intros w d no_code rel. simpl. repeat rewrite unionmE.
        split.
        * remember (mem s' w) as cond. simpl in *. rewrite <- Heqcond. destruct cond; simpl.
          -- intro. simplify_some.
             pose proof (mem_match w d) as [impl _]; auto; simpl.
             destruct (impl (esym Heqcond)) as [d' [d'match d'eq]].
             rewrite d'eq. simpl. exists d'. done.
          -- intro. exists d.
             assert (d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s') false)).
             { clear -H tag_pc3.
               apply (@mkfmap_Some _ _ _ w d) in H.
               move: H => //=. rewrite /mkseq tag_pc3.
               move=> /mapP [] x x_in_iota [] H -> //=.
               case: s' tag_pc3 {H} => //= _ _ [] //= _ taga _ -> //=. }
             subst d. split; simpl; try done. simpl in *.
             remember (mem s w) as cond. destruct cond.
             { setoid_rewrite <- Heqcond0 => //=.

               (* pose proof (mem_match w a) as [_ impl]; auto; simpl; try (rewrite code; done). *)
               (* { clear -code_pref_cond_s1 Heqcond0. *)
               (*   (* setoid_rewrite <- Heqcond0 => //=. rewrite -Heqcond0. *) *)
               (*   intros is_code. *)
               (*   specialize (code_pref_cond_s1 w a (Logic.eq_sym Heqcond0) is_code). *)

               (*   comp_num *)

               (*   exfalso. admit. } *)
               (*   clear -w_prefix rel code Heqcond0 mem_pref_cond_s1. *)
               (*   assert (color (taga a) = color_of s') as eq. *)
               (*   { unfold color_of. *)
               (*     destruct s'. destruct pc0. simpl. *)
               (*     destruct taga. simpl in *. *)
               (*     admit. } *)
               (*   now rewrite eq. } *)

               assert (w_prefix: andw w (@mask mt NC) ==
                                    @component_memory_prefix mt NC (ssrint.Posz (1 + color_of s'))).
               { clear -H Heqa9 tag_pc3.
                 symmetry in Heqa9.

                 move: Heqa9 => /negb_false_iff /eqP. rewrite tag_pc3 => //= Hend.
                 apply (@mkfmap_Some _ _ _ w (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s') false)) in H.
                 move: H => //=. rewrite /mkseq tag_pc3.
                 move=> /mapP [] x x_in_iota [] H -> //=.

                 pose proof (andw_last_component_prefix (ssrint.Posz (1 + c0)) (mem s')) as Hstart.
                 apply /eqP.
                 subst w.
                 eapply mask_range with
                   (x0 := (List.last
                             (List.filter
                                (fun mw : word 32 =>
                                   andw mw (@mask mt NC) == @component_memory_prefix mt NC (ssrint.Posz (1 + c0)))
                                (domm (mem s'))) (@component_memory_prefix mt NC (ssrint.Posz (1 + c0)))));
                   [eapply Hstart | eapply Hend | eauto].
               }

               destruct (is_code (taga a)) eqn:code.
               { clear -w_prefix code_pref_cond_s1 Heqcond0 code.
                 setoid_rewrite <- Heqcond0 => //=.
                 specialize (code_pref_cond_s1 w a (Logic.eq_sym Heqcond0) code).
                 simpl in code_pref_cond_s1.
                 exfalso.
                 move: code_pref_cond_s1 w_prefix => /eqP H1 /eqP H2.
                 rewrite H2 in H1; clear -H1.
                 eapply component_memory_prefix_not_zero.
                 exact H1. }

               pose proof (mem_match w a) as [_ impl]; auto; simpl; try (rewrite code; done).
               {
                 clear -w_prefix rel code Heqcond0 mem_pref_cond_s1.
                 assert (color (taga a) = color_of s') as eq.
                 { unfold color_of.
                   destruct s'. destruct pc0. simpl.
                   destruct taga. simpl in *.
                   admit. }
                 now rewrite eq. }
               destruct (impl (esym Heqcond0)) as [d' [d'match d'eq]]. simpl in *.
               rewrite <- Heqcond in d'eq. inversion d'eq. }
             simpl in *. rewrite <- Heqcond0. simpl.
             (* assert (eq: comp_num s = comp_num s') by done. rewrite eq. *)
             rewrite tag_pc1. rewrite tag_pc3 in H.
             rewrite -H.
             clear -mem_pref_cond_s1. admit.
        * remember (mem s w) as cond. simpl in *. rewrite <- Heqcond. destruct cond; simpl.
          -- intro. simplify_some.
             pose proof (mem_match w d) as [_ impl]; auto; simpl.
             destruct (impl (esym Heqcond)) as [d' [d'match d'eq]].
             rewrite d'eq. simpl. exists d'. done.
          -- intro. exists d.
             assert (d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s) false)).
             { clear -H tag_pc1.
               apply (@mkfmap_Some _ _ _ w d) in H.
               move: H => //=. rewrite /mkseq tag_pc1.
               move=> /mapP [] x x_in_iota [] H -> //=.
               case: s tag_pc1 {H} => //= _ _ [] //= _ taga _ -> //=. }
             subst d. split; simpl; try done. simpl in *.
             remember (mem s' w) as cond. destruct cond.
             { assert (w_prefix: (andw w (@mask mt NC) ==
                                    @component_memory_prefix mt NC (ssrint.Posz (1 + color_of s)))).
               { clear -H tag_pc1.
                 apply (@mkfmap_Some _ _ _ w  (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s) false)) in H.
                 move: H => //=. rewrite /mkseq tag_pc1.
                 move=> /mapP [] x x_in_iota [] H -> //=.
                 admit. }
               destruct (is_code (taga a)) eqn:code.
               { clear -code_pref_cond_s3 Heqcond0 code w_prefix. exfalso. admit. }
               pose proof (mem_match w a) as [impl _]; auto; simpl; try (rewrite code; done).
               { clear -w_prefix rel code Heqcond0 mem_pref_cond_s3.
                 assert (color (taga a) = color_of s) as eq by admit. rewrite eq. done. }
               destruct (impl (esym Heqcond0)) as [d' [d'match d'eq]]. simpl in *.
               rewrite <- Heqcond in d'eq. inversion d'eq. }
             simpl in *. rewrite <- Heqcond0. simpl.
             rewrite tag_pc3. rewrite tag_pc1 in H. clear -H mem_pref_cond_s3. admit.
      + intros w d. simpl. repeat rewrite setmE.
        remember (@eq_op (Ord.eqType _) w (as_word (ssrint.Posz 16))) as cond.
        assert (p1 = p2).
        { rewrite tag_pc1 in Heqa13. rewrite tag_pc3 in Heqa10.
          clear -Heqa10 Heqa13. admit. }
        subst p2.
        simpl in *. rewrite <- Heqcond. destruct cond; simpl.
        split; intro; simplify_some; eexists; split; eauto.
        all: destruct s, pc0; try eapply reg_match.
        all: simpl in *; split; auto.
    - destruct weak as [? ? s3 color_eq side_s' s_mem_cor s'_mem_cor entry_off s'_reg_cor mem_match].
      econstructor; try (rewrite eq_s3'; simpl; auto; done); try congruence; simpl; try done.
      + destruct s, s3, pc0, pc1. simpl. trivial.
      + intros d w rel d_eq. simpl. destruct d as [vd td]. destruct td.
        destruct vtag; simpl; auto.
        all: rewrite unionmE; rewrite unionmE in d_eq; simpl in *.
        all: remember (mem s3 w) as cond; simpl in *.
        all: rewrite <- Heqcond in d_eq; destruct cond; simpl in *.
        all: try (pose proof (s'_mem_cor a w ); simplify_some; simpl in *;
                  pose proof (H rel (esym Heqcond)) as [d' [d'eq d'cond]];
                  rewrite d'eq; simpl; eauto).
        all: exfalso; clear - d_eq.
        all: unfold mkfmap, mkseq, foldr, map in *.
        all: remember (iota 0 n') as l; clear Heql.
        all: induction l; simpl in *; try (inversion d_eq; done).
        all: rewrite setmE in d_eq; unfold_match; simpl in *; auto.
      + subst. simpl. intros col w' w'' d d' proc l l' rel eqw' eqw'' dcode d'code dcol d'col d_e_eq d'_e_eq.
        rewrite unionmE in eqw''.
        unfold_match' eqw''.
        * eapply entry_off; eauto.
        * assert (~ (is_code (taga d'))) by admit. tauto.
      + intros d r deq. rewrite setmE in deq. unfold_match' deq.
        * pose proof (s'_reg_cor d r deq) as add_corr.
          destruct d as [dv dt]. simpl. destruct dt; simpl; trivial.
          all: rewrite unionmE; destruct add_corr as [? [eq1 code]].
          all: rewrite eq1; simpl; eauto.
      + intros w d no_code rel. simpl. repeat rewrite unionmE.
        split.
        * remember (mem s3 w) as cond. simpl in *. rewrite <- Heqcond. destruct cond; simpl.
          -- intro. simplify_some.
             pose proof (mem_match w d) as [impl _]; auto; simpl.
          -- intro. exfalso.
             assert (w_prefix: (andw w (@mask mt NC) ==
                                  @component_memory_prefix mt NC (ssrint.Posz (1 + color_of s3)))).
             { clear -H. admit. }
             assert (d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)) by admit.
             subst d. simpl in rel.
             unfold side_of in side_s'. unfold_match' side_s'.
             eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
             inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto.
             clear -color_eq Heqa0. rewrite <- color_eq. rewrite <- Heqa0. trivial.
        * remember (mem s w) as cond. simpl in *. rewrite <- Heqcond. destruct cond; simpl; intro eq; try (inversion eq; done).
          simplify_some.
          pose proof (mem_match w d) as [_ impl]; auto; simpl. destruct (impl (esym Heqcond)) as [? [? ?]]. rewrite H0.
          simpl. eauto.
    - eapply common_equiv_def with (n := n) (c := c0);
        try ((rewrite eq_s1' eq_s3' || rewrite eq_s1' || rewrite eq_s3'); simpl; auto; done); try congruence; simpl; try done.
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
        unfold register_domm, reg_field_size in *. simpl in *. clear -reg_domm1. admit.
      + unfold register_domm. simpl. rewrite domm_set.
        unfold register_domm, reg_field_size in *. simpl in *. clear -reg_domm3. admit.
      + split; [|split; [|split; [|split; [|split; [|split]]]]];
          unfold memory_prefix_condition, code_prefix_condition, alloc_empty, BNZ_correctness, end_condition in *;
          simpl; repeat rewrite unionmE.
        * admit.
        * admit.
        * rewrite alloc_mem_s1. simpl. admit.
        * intros w d deq dcode. goal_match_bind_step.
          rewrite unionmE in deq. unfold_match' deq.
          all: auto.
          { (pose proof (bnz_s1 w d deq dcode) as cor; unfold decode_instr, ops, concrete_int_32_ops in cor).
            simpl in *; rewrite <- Heqa0 in cor. destruct i; auto; simpl; rewrite unionmE.
            + destruct cor as [? [eq ?]]. rewrite eq. simpl. eauto.
            + destruct cor as [[? [eq ?] ]| ]. rewrite eq. simpl. eauto.
              rewrite H. right. done. }
          { assert (eq: d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s1) false)) by admit.
            rewrite eq in Heqa0. exfalso. clear -Heqa0. simpl in *. unfold_all. rewrite wunpackS in Heqa.
            unfold hnth in *. simpl in *. lazy in Heqa. inv Heqa. }
        * intros w d deq dcode. rewrite unionmE in deq.
          remember (mem s1 (w)) as cond. simpl in *. rewrite <- Heqcond in deq. destruct cond.
          { simpl in deq. simplify_some. destruct (end_s1 _ _ (esym Heqcond)); auto.
            right. destruct H as [d' [d'eq ?]]. exists d'.
            rewrite unionmE. rewrite d'eq. simpl. done. }
          { assert (eq: d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s1) false)) by admit.
            subst d. simpl in dcode. inversion dcode. }
        * intros w d deq. rewrite unionmE in deq. unfold_match' deq.
          -- eapply col_mem1; eauto.
          -- admit.
        * intros w d e deq dent. rewrite unionmE in deq. unfold_match' deq.
          -- eapply entry_code1; eauto.
          -- exfalso.
             assert (eq: d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s1) false)) by admit.
             rewrite eq in dent. simpl in dent. inversion dent.
      + split; [|split; [|split; [|split; [|split; [|split]]]]];
          unfold memory_prefix_condition, code_prefix_condition, alloc_empty, BNZ_correctness, end_condition in *;
          simpl; repeat rewrite unionmE.
        * admit.
        * admit.
        * rewrite alloc_mem_s3. simpl. admit.
        * intros w d deq dcode. goal_match_bind_step.
          rewrite unionmE in deq. unfold_match' deq.
          all: auto.
          { (pose proof (bnz_s3 w d deq dcode) as cor; unfold decode_instr, ops, concrete_int_32_ops in cor).
            simpl in *; rewrite <- Heqa0 in cor. destruct i; auto; simpl; rewrite unionmE.
            + destruct cor as [? [eq ?]]. rewrite eq. simpl. eauto.
            + destruct cor as [[? [eq ?] ]| ]. rewrite eq. simpl. eauto.
              rewrite H. right. done. }
          { assert (eq: d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)) by admit.
            rewrite eq in Heqa0. exfalso. clear -Heqa0. simpl in *. unfold_all. rewrite wunpackS in Heqa.
            lazy in Heqa. inv Heqa. }
        * intros w d deq dcode. rewrite unionmE in deq.
          remember (mem s3 (w)) as cond. simpl in *. rewrite <- Heqcond in deq. destruct cond.
          { simpl in deq. simplify_some. destruct (end_s3 _ _ (esym Heqcond)); auto.
            right. destruct H as [d' [d'eq ?]]. exists d'.
            rewrite unionmE. rewrite d'eq. simpl. done. }
          { assert (eq: d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)) by admit.
            subst d. simpl in dcode. inversion dcode. }
        * intros w d deq. rewrite unionmE in deq. unfold_match' deq.
          -- eapply col_mem3; eauto.
          -- admit.
        * intros w d e deq dent. rewrite unionmE in deq. unfold_match' deq.
          -- eapply entry_code3; eauto.
          -- exfalso.
             assert (eq: d = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)) by admit.
             rewrite eq in dent. simpl in dent. inversion dent.
      + intros d q r req. destruct r as [r | w]; repeat (rewrite unionmE || rewrite setmE);
          repeat (rewrite unionmE in req || rewrite setmE in req); simpl; simpl in req.
        { unfold_match' req. pose proof (capa_cor1 d q (inl r) req) as [is_in unicity].
          split; auto. intros r' d'.
          destruct r' as [r' | w']; simpl; repeat (rewrite unionmE || rewrite setmE).
          { intro req'. unfold_match' req'. eapply (unicity (inl _)); eauto. }
          { intros [t' [t'eq t'capa]]. unfold_match' t'eq. eapply (unicity (inr _)); eauto.
            assert (eq: d'@t' = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s1) false)) by admit.
            destruct t'. simpl in t'capa. rewrite t'capa in eq. inv eq. } }
        { destruct req as [t [teq tcapa]]. unfold_match' teq.
          { pose proof (capa_cor1 d q (inr w) (ex_intro _ t (conj teq tcapa))) as [is_in unicity].
            split; auto. intros r' d'.
            destruct r' as [r' | w']; simpl; repeat (rewrite unionmE || rewrite setmE).
            { intro req'. unfold_match' req'. eapply (unicity (inl _)); eauto. }
            { intros [t' [t'eq t'capa]]. unfold_match' t'eq. eapply (unicity (inr _)); eauto.
              assert (eq: d'@t' = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s1) false)) by admit.
              destruct t'. simpl in t'capa. rewrite t'capa in eq. inv eq. } }
          { assert (eq: d@t = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s1) false)) by admit.
            destruct t. simpl in tcapa. rewrite tcapa in eq. inv eq. } }
        + intros d q r req. destruct r as [r | w]; repeat (rewrite unionmE || rewrite setmE);
          repeat (rewrite unionmE in req || rewrite setmE in req); simpl; simpl in req.
        { unfold_match' req. pose proof (capa_cor3 d q (inl r) req) as [is_in unicity].
          split; auto. intros r' d'.
          destruct r' as [r' | w']; simpl; repeat (rewrite unionmE || rewrite setmE).
          { intro req'. unfold_match' req'. eapply (unicity (inl _)); eauto. }
          { intros [t' [t'eq t'capa]]. unfold_match' t'eq. eapply (unicity (inr _)); eauto.
            assert (eq: d'@t' = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)) by admit.
            destruct t'. simpl in t'capa. rewrite t'capa in eq. inv eq. } }
        { destruct req as [t [teq tcapa]]. unfold_match' teq.
          { pose proof (capa_cor3 d q (inr w) (ex_intro _ t (conj teq tcapa))) as [is_in unicity].
            split; auto. intros r' d'.
            destruct r' as [r' | w']; simpl; repeat (rewrite unionmE || rewrite setmE).
            { intro req'. unfold_match' req'. eapply (unicity (inl _)); eauto. }
            { intros [t' [t'eq t'capa]]. unfold_match' t'eq. eapply (unicity (inr _)); eauto.
              assert (eq: d'@t' = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)) by admit.
              destruct t'. simpl in t'capa. rewrite t'capa in eq. inv eq. } }
          { assert (eq: d@t = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)) by admit.
            destruct t. simpl in tcapa. rewrite tcapa in eq. inv eq. } }
      + unfold combined_codes in *. simpl in *.
        intros w d t off col rel eq_off dcode dcol. repeat rewrite unionmE.
        remember (mem s3 (addw w (as_word off))) as cond1.
        remember (mem s1 w) as cond2.
        simpl in *.
        rewrite <- Heqcond1. rewrite <- Heqcond2.
        destruct cond1; destruct cond2; split; simpl; intro Heq; try simplify_some; subst; simpl.
        -- rewrite Heqcond1. destruct ((fst (code_left w d t off _ rel eq_off dcode (Logic.eq_refl))) (esym Heqcond2)) as [x [xmatch xeq]].
           exists x. split; auto.
           inversion xmatch; subst.
           ++ econstructor; eauto.
           ++ eapply decode_match_alloc_JAL; eauto.
           ++ eapply decode_match_JAL. exact H. exact H0.
              rewrite unionmE. rewrite H1. simpl. eauto.
              rewrite unionmE. rewrite H2. simpl. eauto.
              all: trivial.
        -- rewrite Heqcond2. destruct ((snd (code_left w d t off _ rel eq_off dcode (Logic.eq_refl))) (esym Heqcond1)) as [x [xmatch xeq]].
           exists x. split; auto.
           inversion xmatch; subst.
           ++ econstructor; eauto.
           ++ eapply decode_match_alloc_JAL; eauto.
           ++ eapply decode_match_JAL. exact H. exact H0.
              rewrite unionmE. rewrite H1. simpl. eauto.
              rewrite unionmE. rewrite H2. simpl. eauto.
              all: trivial.
        -- assert (eq: d@t = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s1) false)) by admit.
           inv eq. exfalso. discriminate.
        -- destruct ((snd (code_left w d t off _ rel eq_off dcode (Logic.eq_refl))) (esym Heqcond1)) as [? [? eq1]].
           exfalso. congruence.
        -- destruct ((fst (code_left w d t off _ rel eq_off dcode (Logic.eq_refl))) (esym Heqcond2)) as [? [? eq1]].
           exfalso. congruence.
        -- assert (eq: d@t = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)) by admit.
           inv eq. exfalso. discriminate.
        -- assert (eq: d@t = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s1) false)) by admit.
           inv eq. exfalso. discriminate.
        -- assert (eq: d@t = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)) by admit.
           inv eq. exfalso. discriminate.
      + unfold combined_codes in *. simpl in *.
        intros w d t off col rel eq_off dcode dcol. repeat rewrite unionmE.
        remember (mem s3 (addw w (as_word off))) as cond1.
        remember (mem s2 w) as cond2.
        simpl in *. rewrite <- Heqcond1. rewrite <- Heqcond2.
        destruct cond1; destruct cond2; split; simpl; intro Heq; try simplify_some; subst; simpl; try (inversion Heq; done).
        -- rewrite Heqcond1. destruct ((fst (code_right w d t off _ rel eq_off dcode (Logic.eq_refl))) (esym Heqcond2)) as [x [xmatch xeq]].
           exists x. split; auto.
           inversion xmatch; subst.
           ++ econstructor; eauto.
           ++ eapply decode_match_alloc_JAL; eauto.
           ++ eapply decode_match_JAL. exact H. exact H0.
              exact H1.
              rewrite unionmE. rewrite H2. simpl. eauto.
              all: trivial.
        -- rewrite Heqcond2. destruct ((snd (code_right w d t off _ rel eq_off dcode (Logic.eq_refl))) (esym Heqcond1)) as [x [xmatch xeq]].
           exists x. split; auto.
           inversion xmatch; subst.
           ++ econstructor; eauto.
           ++ eapply decode_match_alloc_JAL; eauto.
           ++ eapply decode_match_JAL. exact H. exact H0.
              exact H1.
              rewrite unionmE. rewrite H2. simpl. eauto.
              all: trivial.
        -- destruct ((snd (code_right w d t off _ rel eq_off dcode (Logic.eq_refl))) (esym Heqcond1)) as [? [? eq1]].
           exfalso. congruence.
        -- destruct ((fst (code_right w d t off _ rel eq_off dcode (Logic.eq_refl))) (esym Heqcond2))
             as [? [? eq1]].
           exfalso. congruence.
        -- assert (eq: d@t = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)) by admit.
           inv eq. exfalso. discriminate.
        -- assert (eq: d@t = (as_word (ssrint.Posz 0))@(def_mem_tag (color_of s3) false)) by admit.
           inv eq. exfalso. discriminate.
  Admitted.

End Preservation.
