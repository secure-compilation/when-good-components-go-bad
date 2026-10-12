Require Import Common.Definitions.
Require Import Lib.Extra.
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
Require Import MicroPolicies.Recomposition.StepSilentStrong.

(* The s2/RIGHT strong silent-step diagram square — the dual of [StepSilentStrong]'s
   [step_silent_strong1].  Here s2 (= prog', L2) takes a silent step while RIGHT-matched
   (s2 is the strongly-related side), and the recomposed run s3 (= prog'') takes a matching
   Plus step.  Admitted (a genuine remaining diagram obligation). *)

Module StepStrong2 (S: RecompositionContext).

  (* Chain off StepStrong so the whole recomposition shares ONE Defs instance. *)
  Include StepStrong S.

  (* Bridge used pervasively on the RIGHT side: from [color_in_memory] of a run's
     memory + a cell at [w] whose colour is RIGHT-sided, derive membership in [ic]
     (i.e. [is_relevant_comp Right]).  On the Left side this was free from [side_eq]
     alone; on the Right one must rule out [domm ip] via the colour's validity. *)
  Lemma side_right_in_ic : forall (m: @memory mt) w d c,
      color_in_memory m -> m w = Some d -> color (taga d) = c ->
      side_of c = Right ->
      c \in domm ic.
  Proof.
    move=> m w d c Hcim Hmw Hcol Hside. subst c.
    have HCm := Hcim w d Hmw.
    case: HCm => [/In_in HCm | /In_in HCm].
    - exfalso. move: Hside. by rewrite /side_of HCm.
    - exact: HCm.
  Qed.

  (* ===================================================================== *)
  (*  RIGHT-side mirror of the four [preserves_equiv_left_*] lemmas from     *)
  (*  [PreservationLemmas].  Convention here: the *strongly-matched /        *)
  (*  stepping* run is [s1] (RIGHT-related), the *weak* run is [s2]          *)
  (*  (LEFT-related); since [common_equiv]'s first argument is the           *)
  (*  LEFT-related state, the common hypothesis is [common_equiv M s2 s1 s3] *)
  (*  (weak [s2] first).  The strong run therefore sits in common-position 2 *)
  (*  so its witness-set is [WS_S2] (was [WS_S1] on the Left).               *)
  (* ===================================================================== *)

  Lemma preserves_equiv_right_pc_incr :
    forall s1 s2 s3 M s1' s3' pc1' tpc1' pc3' tpc3',
      strong_equiv Right M s1 s3
      /\ weak_equiv Left M s2 s3
      /\ common_equiv M s2 s1 s3 ->
      s1' = State _ _ (mem s1) (regs s1) (pc1'@tpc1') tt ->
      s3' = State _ _ (mem s3) (regs s3) (pc3'@tpc3') tt ->
      same_pc Right s1' s3' ->
      tpc1' = taga (pc s1) ->
      tpc3' = taga (pc s3) ->
      pc_code_color s1' ->
      strong_equiv Right M s1' s3'
      /\ weak_equiv Left M s2 s3'
      /\ common_equiv M s2 s1' s3'.
  Proof.
    intros s1 s2 s3 M s1' s3' pc1' tpc1' pc3' tpc3' equiv eq_s1' eq_s3' pc1'_pc3' pc1_tag pc3_tag Hpcc1'.
    destruct equiv as [strong [weak common]].
    split; [|split].
    - destruct strong as [? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match].
      econstructor; destruct s, s', pc0, pc1; try (subst; intros; auto; done); try congruence.
    - destruct weak as [? ? ? color_eq side_s' s'_mem_cor entry_off s'_reg_cor mem_match].
      econstructor; try (rewrite eq_s3'; simpl; auto; done); try (subst; intros; auto; done); try congruence.
      subst. destruct s, s', pc0, pc1. simpl in *. trivial.
    - destruct common as [? ? ? ? n ? tag_pc2 tag_pc1 tag_pc3 wfst reg_domm2 reg_domm1 reg_domm3
                            [mem_pref_cond_s2 [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 col_mem2]]]]]
                            [mem_pref_cond_s1 [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 col_mem1]]]]]
                            [mem_pref_cond_s3 [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 col_mem3]]]]] code_right code_left Hval wpcc2 wpcc1].
      eapply common_equiv_def with (n := n) (c := c0);
        try ((rewrite eq_s1' eq_s3' || rewrite eq_s1' || rewrite eq_s3'); simpl; auto; done); try congruence; try done.
      + rewrite eq_s1'. rewrite pc1_tag. simpl. exact tag_pc1.
      + rewrite eq_s3'. rewrite pc3_tag. simpl. exact tag_pc3.
  Qed.

  Lemma preserves_equiv_right_mem_write:
    forall s1 s2 s3 M s1' s3' w v v' m1' m3' i,
      strong_equiv Right M s1 s3
      /\ weak_equiv Left M s2 s3
      /\ common_equiv M s2 s1 s3 ->
      data_match' Right M v v' ->
      (color (taga v)) = (color (taga v')) ->
      (color (taga v)) = color_of s1 ->
      entry (taga v) = None ->
      is_relevant_comp Right (color (taga v)) ->
      (forall v', (mem s1 w) = Some v' \/ (mem s3 w) = Some v' -> (color (taga v)) = (color (taga v'))) ->
      (exists d, mem s3 w = Some d /\ not (is_code (taga d))) ->
      (exists d, mem s1 w = Some d /\ not (is_code (taga d))) ->
      mem s1 (vala (pc s1)) = Some i ->
      is_code (taga i) ->
      not (is_code (taga v)) ->
      not (is_code (taga v')) ->
      capability_correctness' WS_S2 s1 M (vala v) (vtag (taga v )) ->
      capability_correctness' WS_S3 s3 M (vala v') (vtag (taga v')) ->
      address_correctness Right (vala v) (vtag (taga v)) (mem s1) ->
      address_correctness Right (vala v') (vtag (taga v')) (mem s3) ->
      updm (mem s1) w v = Some m1' ->
      updm (mem s3) w v' = Some m3' ->
      s1' = State _ _ m1' (regs s1) (pc s1) tt ->
      s3' = State _ _ m3' (regs s3) (pc s3) tt ->
      strong_equiv Right M s1' s3'
      /\ weak_equiv Left M s2 s3'
      /\ common_equiv M s2 s1' s3'.
  Proof.
    import_context.

    intros s1 s2 s3 M s1' s3' w v v' m1' m3' i equiv v_match v_color M_color no_entry v_relevant same_color no_code_w_s3 no_code_w_s1
      i_is_pc code_i no_code_v no_code_v' capa_prop1 capa_prop3 correct_v correct_v' (* correct_v'' *) eq_m1 eq_m3 eq_s1' eq_s3'.
    destruct equiv as [strong [weak common]].
    pose proof (updm_set eq_m1). pose proof (updm_set eq_m3). subst m1' m3'.
    split; [|split].
    - destruct strong as [? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match];
      econstructor; destruct s, s', pc0, pc1; try (rewrite eq_s1' eq_s3'; simpl; auto; done); try congruence.
      + destruct common as [? ? ? ? n ? tag_pc2 tag_pc1 tag_pc3 wfst reg_domm2 reg_domm1 reg_domm3
                            [mem_pref_cond_s2 [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 [entry_code2 cvo2]]]]]]]
                            [mem_pref_cond_s1 [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 [entry_code1 cvo1]]]]]]]
                            [mem_pref_cond_s3 [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 [entry_code3 cvo3]]]]]]]
                            capa_cor2 capa_cor1 capa_cor3 code_right code_left Hcval wpcc2 wpcc1].
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
    - destruct weak as [? ? ? color_eq side_s' s_mem_cor s'_mem_cor entry_off (* s'_reg_cor *) mem_match];
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
                          (domm ip) (domm ic)); eauto.
                inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto.
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
                          (domm ip) (domm ic)); eauto.
                inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto.
             ++ move=> ?.
                eapply s'_mem_cor in H. simpl in *. eauto.
                simpl. eauto.
      + subst. simpl. intros col w' w'' d d' proc l l' rel eqw' eqw'' dcode d'code dcol d'col d_e_eq d'_e_eq.
        rewrite setmE in eqw''.
        unfold_match' eqw''; try convert_eq_op; try simplify_some; try contradiction.
        eapply (entry_off); eauto.
      (* + subst. intros d w' deq. simpl. destruct d as [vd vt]. *)
      (*   remember (@eq_op _ vd w) as cond. *)
      (*   destruct vt; simpl; auto; rewrite setmE; simpl in *; try (rewrite <- Heqcond); destruct cond; convert_eq_op. *)
      (*     all: try eapply (s'_reg_cor _ w' deq). *)
      (*     all: try (eapply modusponens; [eapply (s'_reg_cor _ w' deq) | ]; simpl; intros [v'' [v''eq v''code]]; *)
      (*               destruct no_code_w_s3 as [d' [d'eq d'code]]; rewrite d'eq in v''eq; simplify_some). *)
      (*     all: eexists; split; [eauto |]; intro v_in_ic; exfalso; *)
      (*       eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic) _ (color (Types.taga v))); *)
      (*       inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto; rewrite v_color; eauto. *)
      + unfold memory_match in *. simpl.
        intros.
        rewrite setmE.
        case: eqP => [eq_w | Hne] /=.
        * subst w0.
          have Hip : color (Types.taga v') \in domm ic by rewrite -v_color.
          inversion Hmergeable_ifaces as [[_ fdisj] _].
          split; move=> eq; exfalso.
          -- injection eq as ?; subst d.
             eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
          -- pose proof (mem_match w d H H0) as [_ d_impl].
             destruct (d_impl eq) as [d' [d_d'_match eq_d']].
             have d'_color: color (Types.taga v) = color (Types.taga d') by (eapply same_color; auto).
             have d'_color_bis: color (Types.taga d') = color (Types.taga d).
             { destruct d, d'; simpl; unfold data_match' in d_d'_match; destruct d_d'_match; subst; done. }
             rewrite -d'_color_bis -d'_color v_color in H0.
             eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
        * apply mem_match; auto.
    - destruct common
        as [? ? ? ? n ? tag_pc2 tag_pc1 tag_pc3 wfst reg_domm2 reg_domm1 reg_domm3
              [mem_pref_cond_s2 [mem_pref_cond_s2' [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 [entry_code2 cvo2]]]]]]]]
              [mem_pref_cond_s1 [mem_pref_cond_s1' [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 [entry_code1 cvo1]]]]]]]]
              [mem_pref_cond_s3 [mem_pref_cond_s3' [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 [entry_code3 cvo3]]]]]]]]
              capa_cor2 capa_cor1 capa_cor3 code_right code_left Hcval wpcc2 wpcc1].
      eapply common_equiv_def with (n := n) (c := c0).
      (* pc_code_color s2 (unchanged) closed by [wpcc2] via [try assumption]; pc_code_color s1'
         is the last goal, discharged by the dedicated final bullet below. *)
      all: try ((rewrite eq_s1' eq_s3' || rewrite eq_s1' || rewrite eq_s3'); assumption).
      all: try assumption.
      all: try (split; [|split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]]).
      all: try assumption.
      + rewrite eq_s3'. simpl. clear strong weak code_left code_right v_match tag_pc1 tag_pc2 tag_pc3 capa_cor1 capa_cor2 capa_cor3.
        clear capa_prop1 capa_prop3.
        simpl in *.
        induction wfst; intros.
        * eapply wf_stack_empty; eauto.
        (* RIGHT: common is [M s2 s1' s3'], so wf_stack m1=mem s2 (unchanged, points_to_comp_code',
           auto-discharged by eauto), m2=mem s1' (MODIFIED), m3=mem s3' (MODIFIED).  Both modified
           runs use the regular [points_to_comp_code] (only m1 uses the primed one), so the two
           cons cases are identical and simpler than on the Left (no side_of reasoning). *)
        * eapply wf_stack_cons_left; eauto.
          -- rewrite eq_s1'. simpl.
             unfold points_to_comp_code. rewrite setmE.
             case: eqP => [eq_w | _] /=; last exact PTS_CODE2.
             subst w.
             exfalso. unfold points_to_comp_code in PTS_CODE2.
             oapp_False.
             destruct PTS_CODE2 as [color_a code_a].
             destruct no_code_w_s1 as [d [d_eq d_nocode]]. rewrite d_eq in HeqH. simplify_some. done.
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
             unfold points_to_comp_code. rewrite setmE.
             case: eqP => [eq_w | _] /=; last exact PTS_CODE2.
             subst w.
             exfalso. unfold points_to_comp_code in PTS_CODE2.
             oapp_False.
             destruct PTS_CODE2 as [color_a code_a].
             destruct no_code_w_s1 as [d [d_eq d_nocode]]. rewrite d_eq in HeqH. simplify_some. done.
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
        pose proof (bnz_s1 d w' deq dcode) as Hbnz. simpl in *. unfold_bind. simpl.
        goal_match_bind_step; try done; try destruct Hbnz as [? [eq1 ?]].
        -- rewrite setmE; case: eqP => [eq1' | _].
           ++ destruct no_code_w_s1 as [? [eq2 ?]]. rewrite eq1' in eq1. rewrite eq1 in eq2. simplify_some. contradiction.
           ++ eexists; split; [exact eq1 | done].
        -- destruct Hbnz as [[? [eq1 ?]] | eq_alloc]; try (right; done).
           left. rewrite setmE; case: eqP => [eq1' | _].
           ++ destruct no_code_w_s1 as [? [eq2 ?]]. rewrite eq1' in eq1. rewrite eq1 in eq2. simplify_some. contradiction.
           ++ eexists; split; [exact eq1 | done].
      + unfold end_condition in *. intros w0 v0 v0_eq v0_code.
        rewrite eq_s1' in v0_eq. simpl in v0_eq. rewrite setmE in v0_eq.
        move: v0_eq. case: eqP => [eq_w0 | _] v0_eq.
        * move: v0_eq => [= ?]; subst v0; contradiction.
        * destruct (end_s1 w0 v0 v0_eq v0_code) as [? | [v1 [v1_eq v1_code]]]; [left; auto | right].
          exists v1. rewrite eq_s1'. rewrite setmE.
          case: eqP => [eq_next | _]; last (split; done).
          exfalso. rewrite eq_next in v1_eq. destruct no_code_w_s1 as [? [eq no_code]].
          rewrite eq in v1_eq. simplify_some. contradiction.
      + intros w' d deq. subst. simpl in deq.
        rewrite setmE in deq. unfold_match' deq; try convert_eq_op; try simplify_some.
        simpl in v_relevant. right. eapply ((fst (Extra.In_in _ _)) v_relevant).
        eapply col_mem1; eauto.
      + intros w' d e deq dent.
        rewrite eq_s1' in deq. rewrite setmE in deq. unfold_match' deq.
        * exfalso. convert_eq_op. simplify_some. rewrite no_entry in dent. inversion dent.
        * eapply entry_code1; eauto.
      + (* code_vtag_other (mem s1'): the written cell [v] is non-code *)
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
        pose proof (bnz_s3 d w' deq dcode) as Hbnz. simpl in *. unfold_bind. simpl.
        goal_match_bind_step; try done; try destruct Hbnz as [? [eq1 ?]].
        -- rewrite setmE; case: eqP => [eq1' | _].
           ++ destruct no_code_w_s3 as [? [eq2 ?]]. rewrite eq1' in eq1. rewrite eq1 in eq2. simplify_some. contradiction.
           ++ eexists; split; [exact eq1 | done].
        -- destruct Hbnz as [[? [eq1 ?]] | eq_alloc]; try (right; done).
           left. rewrite setmE; case: eqP => [eq1' | _].
           ++ destruct no_code_w_s3 as [? [eq2 ?]]. rewrite eq1' in eq1. rewrite eq1 in eq2. simplify_some. contradiction.
           ++ eexists; split; [exact eq1 | done].
      + unfold end_condition in *. intros w0 v0 v0_eq v0_code.
        rewrite eq_s3' in v0_eq. simpl in v0_eq. rewrite setmE in v0_eq.
        move: v0_eq. case: eqP => [eq_w0 | _] v0_eq.
        * move: v0_eq => [= ?]; subst v0; contradiction.
        * destruct (end_s3 w0 v0 v0_eq v0_code) as [? | [v1 [v1_eq v1_code]]]; [left; auto | right].
          exists v1. rewrite eq_s3'. rewrite setmE.
          case: eqP => [eq_next | _]; last (split; done).
          exfalso. rewrite eq_next in v1_eq. destruct no_code_w_s3 as [? [eq no_code]].
          rewrite eq in v1_eq. simplify_some. contradiction.
      + intros w' d deq. subst. simpl in deq.
        rewrite setmE in deq. unfold_match' deq; try convert_eq_op; try simplify_some.
        rewrite v_color in v_relevant. simpl in v_relevant. right. eapply ((fst (Extra.In_in _ _)) v_relevant).
        eapply col_mem3; eauto.
      + intros w' d e deq dent.
        rewrite eq_s3' in deq. rewrite setmE in deq. unfold_match' deq.
        * exfalso. convert_eq_op. simplify_some. destruct v, d. destruct v_match as [tag_eq ?]. rewrite <- tag_eq in dent.
          rewrite no_entry in dent. inversion dent.
        * eapply entry_code3; eauto.
      + (* code_vtag_other (mem s3'): the written cell [v'] is non-code *)
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
      + (* pc_code_color s1': the data write at [w] (non-code [v]) doesn't touch the code pc cell.
           In this Right lemma the updated run is built from [s2] (eq_m1 / wpcc1 are about s2). *)
        rewrite eq_s1'. apply: (pc_code_color_write (s := s2) (w := w) (v := v));
          [ reflexivity | exact no_code_v | reflexivity | exact wpcc1 ].
  Qed.

  Lemma preserves_equiv_right_reg_write :
    forall s1 s2 s3 M s1' s3' r v v'  r1' r3',
      strong_equiv Right M s1 s3
      /\ weak_equiv Left M s2 s3
      /\ common_equiv M s2 s1 s3 ->
      data_match Right (color_of s1) M v v' ->
      capability_correctness' WS_S2 s1 M (vala v ) (taga v ) ->
      capability_correctness' WS_S3 s3 M (vala v') (taga v') ->
      address_correctness Right (vala v) (taga v) (mem s1) ->
      address_correctness Right (vala v') (taga v') (mem s3) ->
      updm (regs s1) r v = Some r1' ->
      updm (regs s3) r v' = Some r3' ->
      s1' = State _ _ (mem s1) r1' (pc s1) tt ->
      s3' = State _ _ (mem s3) r3' (pc s3) tt ->
      strong_equiv Right M s1' s3'
      /\ weak_equiv Left M s2 s3'
      /\ common_equiv M s2 s1' s3'.
  Proof.
    intros s1 s2 s3 M s1' s3' r v v' r1' r3' equiv v_match
      capa_prop1 capa_prop3 correct_v correct_v' (* correct_v'' *) eq_r1 eq_r3 eq_s1' eq_s3'.
    destruct equiv as [strong [weak common]].
    destruct common as [? ? ? ? n ? tag_pc2 tag_pc1 tag_pc3 wfst reg_domm2 reg_domm1 reg_domm3
                          [mem_pref_cond_s2 [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 [entry_code2 cvo2]]]]]]]
                          [mem_pref_cond_s1 [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 [entry_code1 cvo1]]]]]]]
                          [mem_pref_cond_s3 [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 [entry_code3 cvo3]]]]]]]
                          capa_cor2 capa_cor1 capa_cor3 code_right code_left Hcval wpcc2 wpcc1].
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
    - destruct weak as [? ? s3 color_eq side_s' s_mem_cor s'_mem_cor entry_off (* s'_reg_cor *) mem_match].
      econstructor; try (rewrite eq_s3'; simpl; auto; done); try congruence.
      destruct s, s3, pc0, pc1. subst. simpl. auto.
      trivial.
      (* + intros d r' deq. subst. rewrite setmE in deq. unfold_match' deq. *)
      (*   simpl. convert_eq_op. simpl. simplify_some. trivial. *)
      (*   eapply (s'_reg_cor d r' deq). *)
    - eapply common_equiv_def with (n := n) (c := c0);
        try ((rewrite eq_s1' eq_s3' || rewrite eq_s1' || rewrite eq_s3'); simpl; auto; done); try congruence; try done.
      (* pc_code_color s1': register write leaves mem and pc untouched (updated run from s2). *)
      all: try (match goal with |- pc_code_color _ =>
                  rewrite eq_s1'; apply: (pc_code_color_cong (s := s2));
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

  Lemma alloc_fun_strong_r:
    forall s1 s2 s3 M s1' s3',
      strong_equiv Right M s1 s3
      /\ weak_equiv Left M s2 s3
      /\ common_equiv M s2 s1 s3 ->
      alloc_fun s1 (NC := NC) = Some s1' ->
      alloc_fun s3 (NC := NC) = Some s3' ->
      strong_equiv Right M s1' s3'.
  Proof.
    import_context.

    intros s1 s2 s3 M s1' s3' equiv eq_s1' eq_s3'.
    destruct equiv as [strong [weak common]].
    (* ---- Peel [alloc_fun] on both sides with [obind_inv]: the post-state stays
       inside [eq_s1']/[eq_s3'] as a hypothesis — never [destruct]ed nor [subst]ed
       here — so no expanded block is baked into the proof term (that bake is what
       made the old inversion-cascade peel hang at [Qed]).  We reproduce exactly the
       hypothesis names the conjunct proof below relies on. ---- *)
    unfold alloc_fun in eq_s1', eq_s3'; cbv zeta in eq_s1', eq_s3'.
    (* left (s1): keep ra as the atom [a1]; split size into [v'@Other] *)
    apply obind_inv in eq_s1'; destruct eq_s1' as (a1 & Heqa4 & eq_s1'); symmetry in Heqa4.
    apply obind_inv in eq_s1'; destruct eq_s1' as (wj1 & Hg & eq_s1');
      unfold is_jump in Hg; destruct (taga a1) eqn:Heqa7; try discriminate Hg;
      symmetry in Heqa7; clear Hg wj1.
    (* ret_addr: mem-read at the RA value + the JAL-return check [is_code && colour] that
       [alloc_fun] gained (the block these two peels cover was added after this lemma). *)
    apply obind_inv in eq_s1'; destruct eq_s1' as (reta1 & Hreta1 & eq_s1'); symmetry in Hreta1.
    apply obind_inv in eq_s1'; destruct eq_s1' as (uretchk1 & Hretchk1 & eq_s1');
      move: Hretchk1; case: ifP => Hretcol1; [ move=> _ | discriminate ]; clear uretchk1.
    apply obind_inv in eq_s1'; destruct eq_s1' as (sz1 & Heqa6 & eq_s1'); destruct sz1 as [v' tg1].
    apply obind_inv in eq_s1'; destruct eq_s1' as (wo1 & Hg & eq_s1');
      unfold is_other in Hg; destruct tg1; try discriminate Hg; clear Hg wo1; symmetry in Heqa6.
    apply obind_inv in eq_s1'; destruct eq_s1' as (n' & Hg & eq_s1');
      destruct (int_of_word (vala (v'@Other))) as [m1|] eqn:Heqa3; try rewrite Heqa3 in Hg; simpl in Hg;
        [ move: Hg => [= ?]; subst m1 | discriminate Hg ];
      cbn [vala] in Heqa3; symmetry in Heqa3.
    (* peel the allocator's block-size check: [alloc_fun = Some] gives [n'+1 <= 2^(word-NC)] *)
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
    (* right (s3): split ra into [v@InternalJump]; keep size as the atom [a0] *)
    apply obind_inv in eq_s3'; destruct eq_s3' as (ra3 & Heqa & eq_s3'); destruct ra3 as [v tgr3].
    apply obind_inv in eq_s3'; destruct eq_s3' as (wj3 & Hg & eq_s3');
      unfold is_jump in Hg; destruct tgr3; try discriminate Hg; clear Hg wj3; symmetry in Heqa.
    apply obind_inv in eq_s3'; destruct eq_s3' as (reta3 & Hreta3 & eq_s3'); symmetry in Hreta3.
    apply obind_inv in eq_s3'; destruct eq_s3' as (uretchk3 & Hretchk3 & eq_s3');
      move: Hretchk3; case: ifP => Hretcol3; [ move=> _ | discriminate ]; clear uretchk3.
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
    inversion common as [? ? ? ? n ? tag_pc2 tag_pc1 tag_pc3 wfst reg_domm2 reg_domm1 reg_domm3
                          [mem_pref_cond_s2 [mem_pref_cond_s2' [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 [entry_code2 cvo2]]]]]]]]
                          [mem_pref_cond_s1 [mem_pref_cond_s1' [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 [entry_code1 cvo1]]]]]]]]
                          [mem_pref_cond_s3 [mem_pref_cond_s3' [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 [entry_code3 cvo3]]]]]]]]
                          capa_cor2 capa_cor1 capa_cor3 code_right code_left Hcval wpcc2 wpcc1].
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
    (* inject+subst onto the *block-abstracted* (hence compact) post-state: the
       eq_rect the [subst] bakes now carries [blk1]/[blk3], not the expanded mkseq. *)
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
          -- (* the allocator's own return-cell check gives code-ness *)
             have Hic1 : is_code (taga reta1) by case/andP: Hretcol1 => Hicc _.
             move: Hreta1; rewrite eq => -[Hrx]. rewrite -Hrx. exact: Hic1.
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
          -- (* d is the cell freshly allocated in s'; w is one of the fresh
                addresses, so its mask is the block prefix. *)
             have w_prefix : andw w (@mask mt NC)
                             = @component_memory_prefix mt NC (ssrint.Posz (1 + c0)).
             { xblk Hfresh; clear -Hfresh Heqa9 tag_pc3 Hszbound1 Hszbound3.
               symmetry in Heqa9.
               move: Heqa9 => /negb_false_iff /eqP; rewrite tag_pc3 => /= Hend.
               move: (Hfresh) => /mkfmap_Some; rewrite /mkseq tag_pc3 => /mapP[x x_in_iota] [= -> _] /=.
               pose proof (andw_last_component_prefix (ssrint.Posz (1 + c0)) (mem s')) as Hstart.
               eapply mask_range; [ by [exact Hszbound1 | exact Hszbound3] | exact Hstart | exact Hend | exact x_in_iota ]. }
             have Hcs : color_of s = c0 by rewrite (color_of_pc_tag s) tag_pc1.
             have side_c0 : side_of c0 = Right by rewrite -Hcs.
             (* w is a fresh address, so it is not in the (pre-existing) memory of s:
                a cell there would carry the new colour and contradict mem_match. *)
             have Hval : (c0 \in domm ip) || (c0 \in domm ic).
             { apply/orP; right.
               have Hcd : color (taga d) = c0.
               { move: Hfresh; rewrite Hblk3 => /mkfmap_Some /mapP [x _] [= _ Hd].
                 by rewrite Hd /= tag_pc3. }
               by move: rel; rewrite Hcd /is_relevant_comp. }
             have HsNone : mem s w = None.
             { clear -w_prefix mem_pref_cond_s1' mem_match Hs'None side_c0 Hval.
               case E: (mem s w) => [a|]; last by []. exfalso.
               have Hin : c0 \in domm ic.
               { case/orP: Hval => [Hip | //]. exfalso. move: side_c0. by rewrite /side_of Hip. }
               have Hbnd : 1 + c0 < 2 ^ NC by (apply: colors_bounded; exact Hval).
               have [color_a no_code_a] := mem_pref_cond_s1' c0 w a Hbnd E w_prefix.
               have Hrel : is_relevant_comp Right (color (taga a)) by (rewrite color_a; exact Hin).
               have [d' [_ Hd'eq]] := proj2 (mem_match w a no_code_a Hrel) E.
               by rewrite Hs'None in Hd'eq. }
             exists d. split.
             ++ (* both cells are the same zero/Other cell *)
                xblk Hfresh; move: Hfresh => /alloc_block_const_value ->. by repeat split.
             ++ (* the two allocated blocks coincide at w *)
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
                  eapply match_mem_pref_condition_filter_eq with (i := Right);
                    [ exact: (is_relevant_comp_of_side Hval side_c0)
                    | exact mem_match | exact mem_pref_cond_s1' | exact mem_pref_cond_s3' ]).
        * move=> H; apply unionm_get in H; case: H => [H | [HsNone Hfresh]].
          -- destruct (mem_match w d no_code rel) as [_ impl].
             destruct (impl H) as [d' [d'match d'eq]].
             exists d'; split; [exact d'match | apply unionm_getL; exact d'eq].
          -- (* d is the cell freshly allocated in s (mirror of the s' case). *)
             have w_prefix : andw w (@mask mt NC)
                             = @component_memory_prefix mt NC (ssrint.Posz (1 + c0)).
             { xblk Hfresh; clear -Hfresh Heqa10 tag_pc1 Hszbound1 Hszbound3.
               symmetry in Heqa10.
               move: Heqa10 => /negb_false_iff /eqP; rewrite tag_pc1 => /= Hend.
               move: (Hfresh) => /mkfmap_Some; rewrite /mkseq tag_pc1 => /mapP[x x_in_iota] [= -> _] /=.
               pose proof (andw_last_component_prefix (ssrint.Posz (1 + c0)) (mem s)) as Hstart.
               eapply mask_range; [ by [exact Hszbound1 | exact Hszbound3] | exact Hstart | exact Hend | exact x_in_iota ]. }
             have Hcs : color_of s = c0 by rewrite (color_of_pc_tag s) tag_pc1.
             have side_c0 : side_of c0 = Right by rewrite -Hcs.
             have Hval : (c0 \in domm ip) || (c0 \in domm ic).
             { apply/orP; right.
               have Hcd : color (taga d) = c0.
               { move: Hfresh; rewrite Hblk1 => /mkfmap_Some /mapP [x _] [= _ Hd].
                 by rewrite Hd /= tag_pc1. }
               by move: rel; rewrite Hcd /is_relevant_comp. }
             have Hs'None : mem s' w = None.
             { clear -w_prefix mem_pref_cond_s3' mem_match HsNone side_c0 Hval.
               case E: (mem s' w) => [a|]; last by []. exfalso.
               have Hin : c0 \in domm ic.
               { case/orP: Hval => [Hip | //]. exfalso. move: side_c0. by rewrite /side_of Hip. }
               have Hbnd : 1 + c0 < 2 ^ NC by (apply: colors_bounded; exact Hval).
               have [color_a no_code_a] := mem_pref_cond_s3' c0 w a Hbnd E w_prefix.
               have Hrel : is_relevant_comp Right (color (taga a)) by (rewrite color_a; exact Hin).
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
                  eapply match_mem_pref_condition_filter_eq with (i := Right);
                    [ exact: (is_relevant_comp_of_side Hval side_c0)
                    | exact mem_match | exact mem_pref_cond_s1' | exact mem_pref_cond_s3' ]).
      + intros w d.
        cbn [Symbolic.regs].
        (* register 16 holds the allocated base pointer, which coincides on both
           sides because the allocations coincide (match_mem_pref_condition_filter_eq). *)
        have G : p1.1 = p2.1.
        { rewrite tag_pc1 in Heqa13; rewrite tag_pc3 in Heqa11.
          (* RIGHT: [match_mem_pref_condition_filter_eq]'s side premise is [side_of c0 = Right]
             (not is_relevant_comp), so it follows from [side_eq] directly — no validity bridge. *)
          have Hsc0 : side_of c0 = Right.
          { have Hc : color_of s = c0 by rewrite (color_of_pc_tag s) tag_pc1. by rewrite -Hc. }
          clear -Heqa11 Heqa13 mem_match Hsc0 Hcval mem_pref_cond_s1' mem_pref_cond_s3'.
          move: Heqa11 Heqa13; rewrite /mkseq /=.
          case: n' => // _ [= ->] [= ->] /=.
          congr (_ + _)%w; congr (List.last _ _).
          symmetry.
          eapply match_mem_pref_condition_filter_eq with (i := Right);
            [ exact: (is_relevant_comp_of_side Hcval Hsc0) | exact mem_match
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

  Lemma alloc_fun_weak_r:
    forall s1 s2 s3 M s1' s3',
      strong_equiv Right M s1 s3
      /\ weak_equiv Left M s2 s3
      /\ common_equiv M s2 s1 s3 ->
      alloc_fun s1 (NC := NC) = Some s1' ->
      alloc_fun s3 (NC := NC) = Some s3' ->
      weak_equiv Left M s2 s3'.
  Proof.
    import_context.

    intros s1 s2 s3 M s1' s3' equiv eq_s1' eq_s3'.
    destruct equiv as [strong [weak common]].
    (* ---- Peel [alloc_fun] on both sides with [obind_inv]: the post-state stays
       inside [eq_s1']/[eq_s3'] as a hypothesis — never [destruct]ed nor [subst]ed
       here — so no expanded block is baked into the proof term (that bake is what
       made the old inversion-cascade peel hang at [Qed]).  We reproduce exactly the
       hypothesis names the conjunct proof below relies on. ---- *)
    unfold alloc_fun in eq_s1', eq_s3'; cbv zeta in eq_s1', eq_s3'.
    (* left (s1): keep ra as the atom [a1]; split size into [v'@Other] *)
    apply obind_inv in eq_s1'; destruct eq_s1' as (a1 & Heqa4 & eq_s1'); symmetry in Heqa4.
    apply obind_inv in eq_s1'; destruct eq_s1' as (wj1 & Hg & eq_s1');
      unfold is_jump in Hg; destruct (taga a1) eqn:Heqa7; try discriminate Hg;
      symmetry in Heqa7; clear Hg wj1.
    (* ret_addr: mem-read at the RA value + the JAL-return check [is_code && colour] that
       [alloc_fun] gained (the block these two peels cover was added after this lemma). *)
    apply obind_inv in eq_s1'; destruct eq_s1' as (reta1 & Hreta1 & eq_s1'); symmetry in Hreta1.
    apply obind_inv in eq_s1'; destruct eq_s1' as (uretchk1 & Hretchk1 & eq_s1');
      move: Hretchk1; case: ifP => Hretcol1; [ move=> _ | discriminate ]; clear uretchk1.
    apply obind_inv in eq_s1'; destruct eq_s1' as (sz1 & Heqa6 & eq_s1'); destruct sz1 as [v' tg1].
    apply obind_inv in eq_s1'; destruct eq_s1' as (wo1 & Hg & eq_s1');
      unfold is_other in Hg; destruct tg1; try discriminate Hg; clear Hg wo1; symmetry in Heqa6.
    apply obind_inv in eq_s1'; destruct eq_s1' as (n' & Hg & eq_s1');
      destruct (int_of_word (vala (v'@Other))) as [m1|] eqn:Heqa3; try rewrite Heqa3 in Hg; simpl in Hg;
        [ move: Hg => [= ?]; subst m1 | discriminate Hg ];
      cbn [vala] in Heqa3; symmetry in Heqa3.
    (* peel the allocator's block-size check: [alloc_fun = Some] gives [n'+1 <= 2^(word-NC)] *)
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
    (* right (s3): split ra into [v@InternalJump]; keep size as the atom [a0] *)
    apply obind_inv in eq_s3'; destruct eq_s3' as (ra3 & Heqa & eq_s3'); destruct ra3 as [v tgr3].
    apply obind_inv in eq_s3'; destruct eq_s3' as (wj3 & Hg & eq_s3');
      unfold is_jump in Hg; destruct tgr3; try discriminate Hg; clear Hg wj3; symmetry in Heqa.
    apply obind_inv in eq_s3'; destruct eq_s3' as (reta3 & Hreta3 & eq_s3'); symmetry in Hreta3.
    apply obind_inv in eq_s3'; destruct eq_s3' as (uretchk3 & Hretchk3 & eq_s3');
      move: Hretchk3; case: ifP => Hretcol3; [ move=> _ | discriminate ]; clear uretchk3.
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
    inversion common as [? ? ? ? n ? tag_pc2 tag_pc1 tag_pc3 wfst reg_domm2 reg_domm1 reg_domm3
                          [mem_pref_cond_s2 [mem_pref_cond_s2' [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 [entry_code2 cvo2]]]]]]]]
                          [mem_pref_cond_s1 [mem_pref_cond_s1' [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 [entry_code1 cvo1]]]]]]]]
                          [mem_pref_cond_s3 [mem_pref_cond_s3' [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 [entry_code3 cvo3]]]]]]]]
                          capa_cor2 capa_cor1 capa_cor3 code_right code_left Hcval wpcc2 wpcc1].
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
    (* inject+subst onto the *block-abstracted* (hence compact) post-state: the
       eq_rect the [subst] bakes now carries [blk1]/[blk3], not the expanded mkseq. *)
    move: eq_s1' => [= Hs1]; subst s1'.
    try (move: eq_s3' => [= Hs3]; subst s3').
    destruct weak as [? ? s3 color_eq side_s' s_mem_cor s'_mem_cor entry_off (* s'_reg_cor *) mem_match].
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
          -- (* the freshly-allocated cell carries the Right colour c0, so a
                Left-relevance claim [rel] about it is impossible. *)
             exfalso.
             move: rel; xblk Hfresh; move: Hfresh => /alloc_block_const_value ->.
             rewrite /= tag_pc3 /is_relevant_comp => Hic.
             (* RIGHT: [rel] claims [c0 \in ip], but [side_s'] gives [side_of c0 = Right] ⇒
                [c0 \notin ip] — a direct contradiction (no validity bridge / fdisjoint needed). *)
             move: side_s'; rewrite /side_of (color_of_pc_tag s) tag_pc2 Hic //.
        * move=> H.
          destruct (mem_match w d no_code rel) as [_ impl].
          destruct (impl H) as [d' [d'match d'eq]].
          exists d'; split; [exact d'match | apply unionm_getL; exact d'eq].
  Qed.

  Lemma alloc_fun_common_r:
    forall s1 s2 s3 M s1' s3',
      strong_equiv Right M s1 s3
      /\ weak_equiv Left M s2 s3
      /\ common_equiv M s2 s1 s3 ->
      alloc_fun s1 (NC := NC) = Some s1' ->
      alloc_fun s3 (NC := NC) = Some s3' ->
      common_equiv M s2 s1' s3'.
  Proof.
    import_context.

    intros s1 s2 s3 M s1' s3' equiv eq_s1' eq_s3'.
    destruct equiv as [strong [weak common]].
    (* ---- Peel [alloc_fun] on both sides with [obind_inv]: the post-state stays
       inside [eq_s1']/[eq_s3'] as a hypothesis — never [destruct]ed nor [subst]ed
       here — so no expanded block is baked into the proof term (that bake is what
       made the old inversion-cascade peel hang at [Qed]).  We reproduce exactly the
       hypothesis names the conjunct proof below relies on. ---- *)
    unfold alloc_fun in eq_s1', eq_s3'; cbv zeta in eq_s1', eq_s3'.
    (* left (s1): keep ra as the atom [a1]; split size into [v'@Other] *)
    apply obind_inv in eq_s1'; destruct eq_s1' as (a1 & Heqa4 & eq_s1'); symmetry in Heqa4.
    apply obind_inv in eq_s1'; destruct eq_s1' as (wj1 & Hg & eq_s1');
      unfold is_jump in Hg; destruct (taga a1) eqn:Heqa7; try discriminate Hg;
      symmetry in Heqa7; clear Hg wj1.
    (* ret_addr: mem-read at the RA value + the JAL-return check [is_code && colour] that
       [alloc_fun] gained (the block these two peels cover was added after this lemma). *)
    apply obind_inv in eq_s1'; destruct eq_s1' as (reta1 & Hreta1 & eq_s1'); symmetry in Hreta1.
    apply obind_inv in eq_s1'; destruct eq_s1' as (uretchk1 & Hretchk1 & eq_s1');
      move: Hretchk1; case: ifP => Hretcol1; [ move=> _ | discriminate ]; clear uretchk1.
    apply obind_inv in eq_s1'; destruct eq_s1' as (sz1 & Heqa6 & eq_s1'); destruct sz1 as [v' tg1].
    apply obind_inv in eq_s1'; destruct eq_s1' as (wo1 & Hg & eq_s1');
      unfold is_other in Hg; destruct tg1; try discriminate Hg; clear Hg wo1; symmetry in Heqa6.
    apply obind_inv in eq_s1'; destruct eq_s1' as (n' & Hg & eq_s1');
      destruct (int_of_word (vala (v'@Other))) as [m1|] eqn:Heqa3; try rewrite Heqa3 in Hg; simpl in Hg;
        [ move: Hg => [= ?]; subst m1 | discriminate Hg ];
      cbn [vala] in Heqa3; symmetry in Heqa3.
    (* peel the allocator's block-size check: [alloc_fun = Some] gives [n'+1 <= 2^(word-NC)] *)
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
    (* right (s3): split ra into [v@InternalJump]; keep size as the atom [a0] *)
    apply obind_inv in eq_s3'; destruct eq_s3' as (ra3 & Heqa & eq_s3'); destruct ra3 as [v tgr3].
    apply obind_inv in eq_s3'; destruct eq_s3' as (wj3 & Hg & eq_s3');
      unfold is_jump in Hg; destruct tgr3; try discriminate Hg; clear Hg wj3; symmetry in Heqa.
    apply obind_inv in eq_s3'; destruct eq_s3' as (reta3 & Hreta3 & eq_s3'); symmetry in Hreta3.
    apply obind_inv in eq_s3'; destruct eq_s3' as (uretchk3 & Hretchk3 & eq_s3');
      move: Hretchk3; case: ifP => Hretcol3; [ move=> _ | discriminate ]; clear uretchk3.
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
    inversion common as [? ? ? ? n ? tag_pc2 tag_pc1 tag_pc3 wfst reg_domm2 reg_domm1 reg_domm3
                          [mem_pref_cond_s2 [mem_pref_cond_s2' [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 [entry_code2 cvo2]]]]]]]]
                          [mem_pref_cond_s1 [mem_pref_cond_s1' [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 [entry_code1 cvo1]]]]]]]]
                          [mem_pref_cond_s3 [mem_pref_cond_s3' [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 [entry_code3 cvo3]]]]]]]]
                          capa_cor2 capa_cor1 capa_cor3 code_right code_left Hcval wpcc2 wpcc1].
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
    (* inject+subst onto the *block-abstracted* (hence compact) post-state: the
       eq_rect the [subst] bakes now carries [blk1]/[blk3], not the expanded mkseq. *)
    move: eq_s1' => [= Hs1]; subst s1'.
    try (move: eq_s3' => [= Hs3]; subst s3').
    (* The allocating component c0 (= color_of s1, the Right running component) is a valid
       interface component, so 1+c0 < 2^NC (colors_bounded).  Derived here, before the
       per-conjunct [clear]s, and threaded into the two memory_prefix_condition bullets that
       need it to discharge the (now bounded) component_memory_prefix_succ_not_zero. *)
    (* RIGHT: the running component c0 is valid by the new [common_equiv] invariant [Hcval];
       feed it straight to [colors_bounded] (no side_of trick, which only gives [c0 \notin ip]). *)
    have Hbnd_c0 : 1 + c0 < 2 ^ NC by (apply: colors_bounded; exact Hcval).
    eapply common_equiv_def with (n := n) (c := c0).
      (* pc_code_color s2 (unchanged, [wpcc2]) and pc_code_color s1' (the alloc result whose pc is
         the running-coloured return address [reta1], a code cell by [Hretcol1]). *)
      all: try (match goal with |- pc_code_color _ =>
                  first [ exact wpcc2
                        | apply: (pc_code_color_alloc (s := s1) (a := vala a1) (ret := reta1));
                            [ reflexivity | exact (esym Hreta1) | reflexivity | reflexivity | exact Hretcol1 ] ] end).
      (* Search-free dispatcher: close the cheap obligations (the three pc-tag
         goals and the unchanged s2 invariants) explicitly, leaving exactly the
         nine substantive goals for the bullets below.  No auto/congruence/done. *)
      all: try (cbn [Symbolic.pc Types.taga]; eassumption).
      all: try exact (conj mem_pref_cond_s2 (conj mem_pref_cond_s2' (conj code_pref_cond_s2
              (conj alloc_mem_s2 (conj bnz_s2 (conj end_s2 (conj col_mem2 (conj entry_code2 cvo2)))))))).
      all: try eassumption.
      + simpl. clear strong common weak code_left code_right tag_pc1 tag_pc2 tag_pc3 capa_cor1 capa_cor2 capa_cor3.
        simpl in *.
        induction wfst; intros.
        * eapply wf_stack_empty; eauto.
        * eapply wf_stack_cons_left; eauto.
          -- unfold points_to_comp_code in *. rewrite unionmE.
             (* RIGHT alloc: m2=mem s1' / m3=mem s3' (both unionm'd); pick the matching PTS hyp
                by the goal's memory lookup.  The fresh-block else-branch is vacuous: a stack
                address lies in the pre-state, so its lookup is [Some]. *)
             first
               [ (move: PTS_CODE2; case: (mem s1 v2) => [d|]; [ move=> Hd; exact Hd | move=> Hf; case: Hf ])
               | (move: PTS_CODE3; case: (mem s3 v3) => [d|]; [ move=> Hd; exact Hd | move=> Hf; case: Hf ]) ].
          -- unfold points_to_comp_code in *. rewrite unionmE.
             (* RIGHT alloc: m2=mem s1' / m3=mem s3' (both unionm'd); pick the matching PTS hyp
                by the goal's memory lookup.  The fresh-block else-branch is vacuous: a stack
                address lies in the pre-state, so its lookup is [Some]. *)
             first
               [ (move: PTS_CODE2; case: (mem s1 v2) => [d|]; [ move=> Hd; exact Hd | move=> Hf; case: Hf ])
               | (move: PTS_CODE3; case: (mem s3 v3) => [d|]; [ move=> Hd; exact Hd | move=> Hf; case: Hf ]) ].
        * eapply wf_stack_cons_right; eauto.
          -- unfold points_to_comp_code in *. rewrite unionmE.
             (* RIGHT alloc: m2=mem s1' / m3=mem s3' (both unionm'd); pick the matching PTS hyp
                by the goal's memory lookup.  The fresh-block else-branch is vacuous: a stack
                address lies in the pre-state, so its lookup is [Some]. *)
             first
               [ (move: PTS_CODE2; case: (mem s1 v2) => [d|]; [ move=> Hd; exact Hd | move=> Hf; case: Hf ])
               | (move: PTS_CODE3; case: (mem s3 v3) => [d|]; [ move=> Hd; exact Hd | move=> Hf; case: Hf ]) ].
          -- unfold points_to_comp_code in *. rewrite unionmE.
             (* RIGHT alloc: m2=mem s1' / m3=mem s3' (both unionm'd); pick the matching PTS hyp
                by the goal's memory lookup.  The fresh-block else-branch is vacuous: a stack
                address lies in the pre-state, so its lookup is [Some]. *)
             first
               [ (move: PTS_CODE2; case: (mem s1 v2) => [d|]; [ move=> Hd; exact Hd | move=> Hf; case: Hf ])
               | (move: PTS_CODE3; case: (mem s3 v3) => [d|]; [ move=> Hd; exact Hd | move=> Hf; case: Hf ]) ].
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
             (* RIGHT: alloc cell coloured c0; c0 is valid (Hcval) and side=Right ⇒ c0∈ic. *)
             right; eapply Extra.In_in.
             case/orP: Hcval => [Hip | Hic]; last exact Hic.
             exfalso.
             have side_c0 : side_of (color_of s1) = Right by (destruct strong).
             by move: side_c0; rewrite (color_of_pc_tag s1) tag_pc1 /side_of Hip.
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
        * (* code_vtag_other: old via cvo1; new cells [def_mem_tag _ false] non-code *)
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
             (* RIGHT: alloc cell coloured c0; c0 is valid (Hcval) and side=Right ⇒ c0∈ic. *)
             right; eapply Extra.In_in.
             case/orP: Hcval => [Hip | Hic]; last exact Hic.
             exfalso.
             have side_c0 : side_of (color_of s1) = Right by (destruct strong).
             by move: side_c0; rewrite (color_of_pc_tag s1) tag_pc1 /side_of Hip.
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
        * (* code_vtag_other: old via cvo3; new cells [def_mem_tag _ false] non-code *)
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
      + (* combined_codes Left s2 s3': like the Right case, but the middle run
           s2 is unchanged (no unionm on that side). *)
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
      + (* combined_codes Right s1' s3': the matched (code) cells are unchanged by
           the alloc (fresh cells are non-code), and decode_match transports
           through the unionm. *)
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
  Qed.


  Lemma preserves_equiv_right_alloc_fun:
    forall s1 s2 s3 M s1' s3',
      strong_equiv Right M s1 s3
      /\ weak_equiv Left M s2 s3
      /\ common_equiv M s2 s1 s3 ->
      alloc_fun s1 (NC := NC) = Some s1' ->
      alloc_fun s3 (NC := NC) = Some s3' ->
      strong_equiv Right M s1' s3'
      /\ weak_equiv Left M s2 s3'
      /\ common_equiv M s2 s1' s3'.
  Proof.
    intros s1 s2 s3 M s1' s3' equiv eq_s1' eq_s3'.
    split; [|split].
    - exact (alloc_fun_strong_r equiv eq_s1' eq_s3').
    - exact (alloc_fun_weak_r equiv eq_s1' eq_s3').
    - exact (alloc_fun_common_r equiv eq_s1' eq_s3').
  Qed.

  (* [deduce_equality]'s [combined_codes] branch (Definitions.v) needs a
     [true = (c \in domm ic)] hypothesis on the RIGHT (the Left proof got
     [true = (c \in domm ip)] for free from [side_eq]).  [mk_ic] synthesises it
     from [Heqa4 : false = (c \in domm ip)] + a strong-run code cell + that run's
     [color_in_memory], and [deduce_equality_r] wraps the original tactic with it. *)
  Ltac mk_ic :=
    (* Pick a cell [Hpc] coloured [c] in a map [m] that [color_in_memory] knows.  [getm ?m ?w]
       binds the *raw* map, forcing [Hcm] and [Hpc] to share it (pre-[subst] the only aligned
       pair may be [col_mem3 + mem_s3], not [col_mem1 + PC]); [unify] filters cells whose tag
       is a [mem_tag] coloured [c] (register cells fail the [color (taga d)] typing). *)
    match goal with
    | Hc4 : false = (?c \in domm ip),
      Hcm : color_in_memory ?m,
      Hpc : getm ?m ?w = Some ?d |- _ =>
        unify (color (taga d)) c;
        let Hside := fresh "Hside" in
        let Hic := fresh "Hic" in
        assert (Hside : side_of c = Right) by (rewrite /side_of -Hc4; done);
        have Hic : true = (c \in domm ic) :=
          esym (side_right_in_ic Hcm Hpc (erefl _) Hside)
    end.

  (* For a DATA cell (is_code false) [deduce_equality] takes its [memory_match] branch,
     whose Left-specific side-condition discharge leaks an unclosed [c \in domm ic] goal
     on the Right.  [mk_ic] has already put [Hic : true = (c \in domm ic)] in scope; close
     any such stray with it. *)
  (* [mk_ic] only matches when [Heqa3 : false = (c \in domm ip)] is present (the alt2 stray),
     so it fails fast on ordinary goals; on the stray it adds [Hic], which closes the goal. *)
  Ltac close_ic :=
    mk_ic; match goal with H : true = (_ \in domm ic) |- _ => exact (esym H) end.

  Ltac deduce_equality_r s_eq := try mk_ic; deduce_equality s_eq; try close_ic.

  Local Opaque pc_code_color.
  (* Discharge a [preserves_equiv_right_pc_incr] call's [pc_code_color s1'] obligation, mirroring
     StepSilentStrong's [pcc_close]: [s1']'s mem is [mem s1] (PRE), its pc-value the step's new pc
     ([congr addw] modulo word-notation), its pc-tag the running tag ([stt = ST]).  The LRC step is
     [step_me_mp step_1] (the Merged step transferred to an LRC step). *)
  Ltac pcc_close2 stp stt :=
    apply: (PCCM.pc_incr_pcc stp);
    [ by []
    | first [ by congr addw | by congr swcast | by congr word_of_nat
            | by (rewrite /=; congr addw) | by (rewrite /=; congr swcast)
            | by (rewrite /=; congr word_of_nat) | by [] ]
    | first [ by [] | by rewrite stt | by (rewrite stt /=) | by congruence | congruence ] ].

  Lemma step_silent_strong2:
    forall s2 s2', Step sem' s2 E0 s2' ->
    forall s1 s3 M, strong_equiv Right M s2 s3 ->
             weak_equiv Left M s1 s3 ->
             common_equiv M s1 s2 s3 ->
    exists s3' M', Plus sem'' s3 E0 s3' /\
             strong_equiv Right M' s2' s3' /\
             weak_equiv Left M' s1 s3' /\
             common_equiv M' s1 s2' s3'.
  Proof.
    import_context.
    intros s1 s1' step_s1 s2 s3 M strong weak common. simpl in step_s1.
    (* [sem'] steps via [step1] directly (no UB restriction): [step_s1] IS the [step_1] the
       Left proof recovered from the [step_UB_disallowed] branch, and there is no UB
       ([step_UB_allowed]) case to discharge on the Right. *)
    pose proof step_s1 as step_1.
    remember (id s3) as s3'; simpl in Heqs3'; destruct s3' as [mem3 regs3 [pc3_val pc3_tag] internal3].
      rewrite Heqs3' in strong weak common; rewrite Heqs3'. pose proof (esym Heqs3') as eq_s3.
      inversion strong as [? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor _ s_reg_cor s'_reg_cor mem_match reg_match].
      inversion common as [? ? ? ? n ? tag_pc2 tag_pc1 tag_pc3 wfst reg_domm2 reg_domm1 reg_domm3
                          [mem_pref_cond_s2 [mem_pref_cond_s2' [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 [entry_code2 cvo2]]]]]]]]
                          [mem_pref_cond_s1 [mem_pref_cond_s1' [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 [entry_code1 cvo1]]]]]]]]
                          [mem_pref_cond_s3 [mem_pref_cond_s3' [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 [entry_code3 cvo3]]]]]]]]
                          capa_cor2 capa_cor1 capa_cor3 code_right code_left Hcval wpcc2 wpcc1].
      subst s s' s0 s4 s5 m m0.
      inversion step_1; unfold step1.
      + unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        unfold_all; try unfold_match; unfold_all.
        all: try (clear -Heqa2; repeat unfold_match' Heqa2; done); simpl in *. (* eliminates many goals *)
        try (rewrite ST in PC_None; unfold color_of in PC_None; rewrite PC in PC_None; try (inversion PC_None; done || clear PC_None)).
        try (assert (tpc1 = tpc0) by (clear -Heqa2; unfold_match' Heqa2); subst tpc1).
        try (assert (ts0 = (ts (mvec None)) ) by
                 (unfold mvec in *; simpl; clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                  destruct Heqa2 as [_ _ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ts0).
        try (unfold mvec in *; assert (ti1 = ti0) by
                    (clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                     destruct Heqa2 as [_ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ti1).
        try (rewrite ST in end_s1 Heqa2; simpl in end_s1, Heqa2;
                  destruct (end_s1 pc0 _ PC) as [ instr_is_halt | [[i' ti'] [Heqi' code_i']]];
                  [destruct ti0; simpl in *; auto; try unfold_match' Heqa5; try done |
                    (match goal with
                     | op: _ = op_of_word _, inst: instr_of_args _ = _ |- _
                       => simpl in instr_is_halt;  rewrite <- op in instr_is_halt; simpl in instr_is_halt;
                         rewrite inst in instr_is_halt; done end) |
                    simpl in Heqi'; try (rewrite Heqi' in Heqa2; inversion Heqa2) ] ).
        unfold check_belong, belong, reg_clear_list in *.
        simpl in *; unfold_all.
        (* 7-8: (match (type of Heqa2) with *)
        (*         (_ = match ?m ?w with _ => _ end) *)
        (*         => eapply (@modusponens (exists res, m w = Some res /\ *)
        (*                                          (LRC.color (taga res) \in domm ip -> *)
        (*                                           is_code (taga res)))); *)
        (*           [|intros [res [res_eq res_code]]; rewrite res_eq in Heqa2] *)
        (*       end). *)
        (* 11: remember (mem0 pc') as next_pc_content; destruct next_pc_content. *)
        try (match goal with
                    |- exists _ _, _ => repeat (unfold_all || unfold_match || rewrite orb_false_r in Heqa4, Heqa16) end).
        convert_eq_op.
        unfold is_jump in *; try (unfold_match; subst t1).
        unfold hshead in *; simpl in *.
        try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3. (* trick to keep an equality on s1 and s3 *)
        try (pose proof (esym Heqa3) as PC; clear Heqa3).
        try (match goal with c: Component.id |- _ => rename c into color end).
        try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                  [exfalso; subst; simpl in *; rewrite (proj1 eq_none) in PC; done |]).
        try (assert (color_of s1 = c0) as eq by (unfold color_of; subst; simpl; clear -tag_pc1; destruct tpc0; simpl in *; congruence);
                  subst c0).
        try (destruct tpc0; unfold_all).
        try (unfold compatible in *; rewrite eq in m_compat).
        try rewrite m_compat in side_eq.

        edestruct (code_left pc0) as [X _].
        { instantiate (1 := i0). unfold is_relevant_comp.
          (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ]). }
        { instantiate (1 := off). rewrite ST in eq_off; eauto. }
        { instantiate (1 := {| vtag := vtag; color := i0; entry := entry; is_code := true |}); eauto. }
        { eauto. }
        rewrite ST in X. simpl in X.
        specialize (X PC) as [v' [match_dec mem_s3]].

        edestruct (code_left (pc0 + 1)%w) as [X' _].
        { instantiate (1 := i0). unfold is_relevant_comp.
          (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ]). }
        { instantiate (1 := off). rewrite ST in eq_off; eauto. }
        { instantiate (1 := {| vtag := vtag0; color := i0; entry := entry0; is_code := is_code0 |}); eauto. }
        { eauto. }
        rewrite ST in X'. simpl in X'.
        specialize (X' Heqi') as [v'' [match_dec' mem_s3']].
        
        exists (@State mt lrc_tags _ mem3 regs3 ((addw (addw pc0 (as_word off)) onew)@(Level n (color_of s1))) tt); exists M. simpl.
        split.
        * eapply plus_one. try eapply step_nop; eauto.
          -- rewrite eq_s3 in pc_s1_s3.
             simpl in pc_s1_s3. subst pc3_val. rewrite ST. simpl. rewrite eq_s3 in mem_s3. rewrite mem_s3. reflexivity.
          -- inversion match_dec.
             ++ subst v'.
                decode_instr_eq.
             ++ assert (decode_instr i = Some (Nop mt)) by decode_instr_eq.
                congruence.
             ++ assert (decode_instr i = Some (Nop mt)) by decode_instr_eq.
                congruence.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. simpl. unfold_bind.
             deduce_reg reg_match.
             (* assert (mem3 (addw pc3_val onew) = mem0 (addw pc0 onew)). *)
             (* eapply (etrans _ (esym Heqi')). *)
             rewrite eq_s3. simpl.

             rewrite eq_s3 in pc_s1_s3.
             simpl in pc_s1_s3. subst pc3_val. rewrite ST. simpl. rewrite eq_s3 in mem_s3'. simpl in mem_s3'.
             Locate "+".
             rewrite -addwA in mem_s3'. rewrite (addwC 1%w _) in mem_s3'. rewrite addwA in mem_s3'.
             rewrite !mem_s3'. simpl.
             rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3.
             clear tag_pc1. rewrite ST. unfold color_of. simpl. rewrite eq_refl. simpl.
             unfold check_belong, belong. rewrite eq_refl. simpl. reflexivity.
        * eapply (preserves_equiv_right_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)) (tpc1' := (taga (pc s1)))
                                                     (pc3' := (addw (vala (pc s3)) onew)) (tpc3' := (taga (pc s3))); eauto; try (pcc_close2 (PCCM.step_me_mp step_1) ST).
          -- rewrite ST. simpl. done.
          -- try rewrite eq_s3. simpl.
             rewrite eq_s3 in pc_s1_s3.
             simpl in pc_s1_s3. subst pc3_val.
             rewrite eq_s3 in tag_pc3; simpl in tag_pc3; rewrite tag_pc3.
             rewrite ST. unfold color_of. simpl. reflexivity.
          -- rewrite ST. simpl.
             eapply same_pc_normal. simpl. split; [exact Heqi' | exact code_i'].
             ++ subst. unfold color_of. simpl. exact eq_off.
             ++ subst. simpl.
                exact (eq_trans (esym (addwA pc0 (as_word off) onew))
                         (eq_trans (f_equal (addw pc0) (addwC (as_word off) onew))
                            (addwA pc0 onew (as_word off)))).
      + unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        unfold_all; try unfold_match; unfold_all.
        all: try (clear -Heqa2; repeat unfold_match' Heqa2; done); simpl in *. (* eliminates many goals *)
        try (rewrite ST in PC_None; unfold color_of in PC_None; rewrite PC in PC_None; try (inversion PC_None; done || clear PC_None)).
        try (assert (tpc1 = tpc0) by (clear -Heqa2; unfold_match' Heqa2); subst tpc1).
        try (assert (ts0 = (ts (mvec None)) ) by
                 (unfold mvec in *; simpl; clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                  destruct Heqa2 as [_ _ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ts0).
        try (unfold mvec in *; assert (ti1 = ti0) by
                    (clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                     destruct Heqa2 as [_ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ti1).
        try (rewrite ST in end_s1 Heqa2; simpl in end_s1, Heqa2;
                  destruct (end_s1 pc0 _ PC) as [ instr_is_halt | [[i' ti'] [Heqi' code_i']]];
                  [destruct ti0; simpl in *; auto; try unfold_match' Heqa5; try done |
                    (match goal with
                     | op: _ = op_of_word _, inst: instr_of_args _ = _ |- _
                       => simpl in instr_is_halt;  rewrite <- op in instr_is_halt; simpl in instr_is_halt;
                         rewrite inst in instr_is_halt; done end) |
                    simpl in Heqi'; try (rewrite Heqi' in Heqa2; inversion Heqa2) ] ).
        unfold check_belong, belong, reg_clear_list in *.
        simpl in *; unfold_all.
        (* 7-8: (match (type of Heqa2) with *)
        (*         (_ = match ?m ?w with _ => _ end) *)
        (*         => eapply (@modusponens (exists res, m w = Some res /\ *)
        (*                                          (LRC.color (taga res) \in domm ip -> *)
        (*                                           is_code (taga res)))); *)
        (*           [|intros [res [res_eq res_code]]; rewrite res_eq in Heqa2] *)
        (*       end). *)
        (* 11: remember (mem0 pc') as next_pc_content; destruct next_pc_content. *)
        try (match goal with
                    |- exists _ _, _ => repeat (unfold_all || unfold_match || rewrite orb_false_r in Heqa4, Heqa16) end).
        convert_eq_op.
        unfold is_jump in *; try (unfold_match; subst t1).
        unfold hshead in *; simpl in *.
        try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3. (* trick to keep an equality on s1 and s3 *)
        try (pose proof (esym Heqa3) as PC; clear Heqa3).
        try (match goal with c: Component.id |- _ => rename c into color end).
        try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                  [exfalso; subst; simpl in *; rewrite (proj1 eq_none) in PC; done |]).
        try (assert (color_of s1 = c0) as eq by (unfold color_of; subst; simpl; clear -tag_pc1; destruct tpc0; simpl in *; congruence);
                  subst c0).
        try (destruct tpc0; unfold_all).
        try (unfold compatible in *; rewrite eq in m_compat).
        try rewrite m_compat in side_eq.


        edestruct (code_left pc0) as [X _].
        { instantiate (1 := i0). unfold is_relevant_comp.
          (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ]). }
        { instantiate (1 := off). rewrite ST in eq_off; eauto. }
        { instantiate (1 := {| vtag := vtag; color := i0; entry := entry; is_code := true |}); eauto. }
        { eauto. }
        rewrite ST in X. simpl in X.
        specialize (X PC) as [v' [match_dec mem_s3]].

        edestruct (code_left (pc0 + 1)%w) as [X' _].
        { instantiate (1 := i0). unfold is_relevant_comp.
          (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ]). }
        { instantiate (1 := off). rewrite ST in eq_off; eauto. }
        { instantiate (1 := {| vtag := vtag0; color := i0; entry := entry0; is_code := is_code0 |}); eauto. }
        { eauto. }
        rewrite ST in X'. simpl in X'.
        specialize (X' Heqi') as [v'' [match_dec' mem_s3']].
        
        destruct (reg_match r old@told) as [X Y].
        rewrite ST eq_s3 in Y; simpl in Y. specialize (Y OLD).
        destruct Y as [[vr3 tr3] [Y Z]].

        
        exists (@State mt lrc_tags _ mem3 (setm regs3 r ((swcast n0)@Other)) ((addw (addw pc0 (as_word off)) onew)@(Level n (color_of s1))) tt); exists M. simpl.
        split.
        * eapply plus_one; try eapply step_const; eauto.
          -- rewrite eq_s3 in pc_s1_s3.
             simpl in pc_s1_s3. subst pc3_val. rewrite ST. simpl. rewrite eq_s3 in mem_s3. rewrite mem_s3. reflexivity.
          -- inversion match_dec.
             ++ subst v'.
                decode_instr_eq.
             ++ assert (decode_instr i = Some (Const n0 r)) by decode_instr_eq.
                congruence.
             ++ assert (decode_instr i = Some (Const n0 r)) by decode_instr_eq.
                congruence.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_all.
             deduce_reg reg_match.
             rewrite eq_s3. simpl.
             rewrite eq_s3 in pc_s1_s3.
             simpl in pc_s1_s3. subst pc3_val. rewrite ST. simpl. rewrite eq_s3 in mem_s3'. simpl in mem_s3'.
             Locate "+".
             rewrite -addwA in mem_s3'. rewrite (addwC 1%w _) in mem_s3'. rewrite addwA in mem_s3'.
             rewrite !mem_s3'. simpl.
             rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3.
             clear tag_pc1. rewrite ST. unfold color_of. simpl. rewrite eq_refl. simpl.
             (let H := fresh "H" in
               let v := fresh "v" in
               match goal with
               | |- context [updm ?r ?w _] =>
                   assert (exists v, (r w = Some v)) as [v H]; [| unfold updm; rewrite H; clear H] end).
             { eauto. }
             (* { subst. deduce_reg reg_match. eauto. } *)
             unfold check_belong, belong. rewrite eq_refl. simpl. reflexivity.
        * (* equiv-conjunct (strong/weak/common preservation) for Const — GENUINE.
             reg_write (the new value) then pc_incr, then discharge the 10 premises with the
             `all: lazymatch` dispatcher below: capability/address = exact I (True for Other),
             data_match = refl, same_pc via word_ac, updm via reg_match/Z, and the 2 reg-write
             state-eqs via ST (s1 side) / eq_s3+tag_pc3+pc_s1_s3 (s3 side). No admit. *)
          eapply preserves_equiv_right_reg_write with (r := r) (v := (swcast n0)@Other) (v' := (swcast n0)@Other); auto.
          eapply (preserves_equiv_right_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)) (tpc1' := (taga (pc s1)))
                                                     (pc3' := (addw (vala (pc s3)) onew)) (tpc3' := (taga (pc s3))); eauto; try (pcc_close2 (PCCM.step_me_mp step_1) ST).
          (* discharge the 10 reg_write+pc_incr premises, NO admit (see close_reg_equiv note above) *)
          all: lazymatch goal with
               | |- capability_correctness' _ _ _ _ _ => exact I
               | |- address_correctness _ _ _ _ => exact I
               | |- data_match _ _ _ _ _ => simpl; split; reflexivity
               | |- same_pc _ _ _ =>
                   rewrite ST; simpl; eapply same_pc_normal;
                   [ simpl; split; [exact Heqi' | exact code_i']
                   | subst; unfold color_of; simpl; exact eq_off
                   | rewrite ST in pc_s1_s3; simpl in pc_s1_s3; simpl; rewrite pc_s1_s3; word_ac ]
               | |- updm ?rr ?ww _ = Some _ =>
                   let Hu := fresh in let Hs3 := fresh in
                   assert (Hs3 : regs s3 ww = Some (vr3@tr3)) by (rewrite eq_s3; simpl; exact Z);
                   assert (exists w, rr ww = Some w) as [? Hu] by
                     (simpl; first [ eexists; exact Hs3
                                   | destruct (proj1 (reg_match ww _) Hs3) as [? [_ ?]]; eexists; eassumption ]);
                   unfold updm; rewrite Hu; reflexivity
               | |- _ =>
                   first [ solve [ rewrite ST; simpl; reflexivity ]
                         | solve [ rewrite eq_s3; simpl;
                                   rewrite eq_s3 in pc_s1_s3; simpl in pc_s1_s3; subst pc3_val;
                                   rewrite eq_s3 in tag_pc3; simpl in tag_pc3; rewrite tag_pc3;
                                   rewrite ST; unfold color_of; simpl; reflexivity ] ]
               end.
      (* PORT+SPEED TODO (2026-05-30): the 8 remaining opcodes (Mov/Binop/Load/Store/Bnz/Jump/
         Jal/Jal2/syscall) are admitted so the file COMPILES FAST end-to-end. Their original
         proof bodies are preserved verbatim in the block comment below; finishing each means
         applying the validated recipe (concrete s3' + plus_one + step reflexivity + close_equiv)
         plus the 9.1 port fixes (e.g. `Ord.eqType`). Nop and Const above are genuine + fast.
         The per-opcode `+ admit.` bullets live AFTER the END marker below, so opcodes can be
         un-commented and proven one at a time from the top of this block (moving the BEGIN
         marker past each finished opcode and dropping one admit). *)
      (* ----- Mov opcode (un-commented, being converted) ----- *)
      + unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        unfold_all; try unfold_match; unfold_all.
        all: try (clear -Heqa2; repeat unfold_match' Heqa2; done); simpl in *. (* eliminates many goals *)
        try (rewrite ST in PC_None; unfold color_of in PC_None; rewrite PC in PC_None; try (inversion PC_None; done || clear PC_None)).
        try (assert (tpc1 = tpc0) by (clear -Heqa2; unfold_match' Heqa2); subst tpc1).
        try (assert (ts0 = (ts (mvec None)) ) by
                 (unfold mvec in *; simpl; clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                  destruct Heqa2 as [_ _ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ts0).
        try (unfold mvec in *; assert (ti1 = ti0) by
                    (clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                     destruct Heqa2 as [_ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ti1).
        try (rewrite ST in end_s1 Heqa2; simpl in end_s1, Heqa2;
                  destruct (end_s1 pc0 _ PC) as [ instr_is_halt | [[i' ti'] [Heqi' code_i']]];
                  [destruct ti0; simpl in *; auto; try unfold_match' Heqa5; try done |
                    (match goal with
                     | op: _ = op_of_word _, inst: instr_of_args _ = _ |- _
                       => simpl in instr_is_halt;  rewrite <- op in instr_is_halt; simpl in instr_is_halt;
                         rewrite inst in instr_is_halt; done end) |
                    simpl in Heqi'; try (rewrite Heqi' in Heqa2; inversion Heqa2) ] ).
        unfold check_belong, belong, reg_clear_list in *.
        simpl in *; unfold_all.
        (* 7-8: (match (type of Heqa2) with *)
        (*         (_ = match ?m ?w with _ => _ end) *)
        (*         => eapply (@modusponens (exists res, m w = Some res /\ *)
        (*                                          (LRC.color (taga res) \in domm ip -> *)
        (*                                           is_code (taga res)))); *)
        (*           [|intros [res [res_eq res_code]]; rewrite res_eq in Heqa2] *)
        (*       end). *)
        (* 11: remember (mem0 pc') as next_pc_content; destruct next_pc_content. *)
        try (match goal with
                    |- exists _ _, _ => repeat (unfold_all || unfold_match || rewrite orb_false_r in Heqa4, Heqa16) end).
        convert_eq_op.
        unfold is_jump in *; try (unfold_match; subst t1).
        unfold hshead in *; simpl in *.
        try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3. (* trick to keep an equality on s1 and s3 *)
        try (pose proof (esym Heqa3) as PC; clear Heqa3).
        try (match goal with c: Component.id |- _ => rename c into color end).
        try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                  [exfalso; subst; simpl in *; rewrite (proj1 eq_none) in PC; done |]).
        try (assert (color_of s1 = c0) as eq by (unfold color_of; subst; simpl; clear -tag_pc1; destruct tpc0; simpl in *; congruence);
                  subst c0).
        try (destruct tpc0; unfold_all).
        try (unfold compatible in *; rewrite eq in m_compat).
        try rewrite m_compat in side_eq.
        deduce_equality_r OLD.
        deduce_equality_r R1W.

        edestruct (code_left pc0) as [X _].
        { instantiate (1 := i0). unfold is_relevant_comp.
          (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ]). }
        { instantiate (1 := off). rewrite ST in eq_off; eauto. }
        { instantiate (1 := {| vtag := vtag; color := i0; entry := entry; is_code := true |}); eauto. }
        { eauto. }
        rewrite ST in X. simpl in X.
        specialize (X PC) as [vpc [match_dec mem_s3]].

        edestruct (code_left (pc0 + 1)%w) as [X' _].
        { instantiate (1 := i0). unfold is_relevant_comp.
          (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ]). }
        { instantiate (1 := off). rewrite ST in eq_off; eauto. }
        { instantiate (1 := {| vtag := vtag0; color := i0; entry := entry0; is_code := is_code0 |}); eauto. }
        { eauto. }
        rewrite ST in X'. simpl in X'.
        specialize (X' Heqi') as [vpc' [match_dec' mem_s3']].


        
        exists (@State mt lrc_tags _ mem3
                  (setm (setm regs3 r1 (v1@(if is_address t0 then Invalidated else Other))) r2 (v1@t0))
                  ((addw pc3_val onew)@(Level n i0)) tt); exists M. simpl.
        remember (r2 == r1) as cond.
        split.
        * eapply plus_one; try eapply step_mov. eauto.
          -- rewrite eq_s3 in pc_s1_s3.
             simpl in pc_s1_s3. subst pc3_val. rewrite ST. simpl. rewrite eq_s3 in mem_s3. rewrite mem_s3. reflexivity.
          -- inversion match_dec.
             ++ subst vpc.
                decode_instr_eq.
             ++ assert (decode_instr i = Some (Mov r1 r2)) by decode_instr_eq.
                congruence.
             ++ assert (decode_instr i = Some (Mov r1 r2)) by decode_instr_eq.
                congruence.
          -- rewrite eq_s3 in vt_eq0. eauto.
          -- rewrite eq_s3 in vt_eq. eauto.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_all.
             deduce_reg reg_match.
             subst s3 s1. simpl in *. simpl in *.
             unfold side_of in side_eq. unfold_match' side_eq.
             deduce_equality_r Heqi'.
             rewrite vt_eq1. simpl.
             unfold check_belong, belong. rewrite eq_refl. simpl.
             unfold updm. rewrite vt_eq0. simpl.
             try rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3. try rewrite ST. unfold color_of. simpl. rewrite eq_refl. simpl.
             repeat rewrite setmE. simpl in Heqcond.
             match goal with |- context [@eq_op ?T r2 r1] => destruct (@eq_op T r2 r1) eqn:Hcd end.
             ++ reflexivity.
             ++ destruct (proj2 (reg_match r2 _) OLD) as [? [_ Hr2]];
                simpl in Hr2; rewrite Hr2; reflexivity.
        * inversion vt_match0 as [? _]. subst t0. unfold_all.
          rewrite ST in Heqa11. simpl in Heqa11. rewrite R1W in Heqa11. simplify_some.
          rewrite ST. simpl. remember (if is_address t1 then Invalidated else Other) as new_t1.
          eapply preserves_equiv_right_reg_write with (r := r2) (v := w1@t1) (v' := v1@t1)
            (s1 := @State mt lrc_tags _ (mem s1) (setm (regs s1) r1 (w1@new_t1)) ((addw (vala (pc s1)) onew)@(taga (pc s1))) tt)
            (s3 := @State mt lrc_tags _ (mem s3) (setm (regs s3) r1 (v1@new_t1)) ((addw (vala (pc s3)) onew)@(taga (pc s3))) tt).
          eapply preserves_equiv_right_reg_write with (r := r1) (v := w1@new_t1) (v' := (v1@new_t1))
            (s1 := @State mt lrc_tags _ (mem s1) (regs s1) ((addw (vala (pc s1)) onew)@(taga (pc s1))) tt)
            (s3 := @State mt lrc_tags _ (mem s3) (regs s3) ((addw (vala (pc s3)) onew)@(taga (pc s3))) tt).
          eapply (preserves_equiv_right_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)) (tpc1' := (taga (pc s1)))
                                                     (pc3' := (addw (vala (pc s3)) onew)) (tpc3' := (taga (pc s3))); auto. eauto.
          (* pass 1: resolve the reg_write/pc_incr state-eqs (reflexivity), instantiating the
             nested pre-state evars ?s1/?s3 so the value premises below can reduce *)
          all: try (solve [ reflexivity | (rewrite ST; simpl; reflexivity) | (rewrite eq_s3; simpl; reflexivity)
                          | (rewrite eq_s3; simpl; rewrite eq_s3 in pc_s1_s3; simpl in pc_s1_s3; subst pc3_val;
                             rewrite eq_s3 in tag_pc3; simpl in tag_pc3; rewrite tag_pc3; rewrite ST; unfold color_of; simpl; reflexivity)
                          | done ]).
          (* pass 2: the value premises, now with evars resolved *)
          all: try (lazymatch goal with
                    | |- pc_code_color _ => pcc_close2 (PCCM.step_me_mp step_1) ST
                    | |- same_pc _ _ _ =>
                        subst; simpl; eapply same_pc_normal;
                        [ simpl; split; [exact Heqi' | exact code_i']
                        | subst; unfold color_of; simpl; exact eq_off
                        | simpl in *; rewrite pc_s1_s3; simpl; word_ac ]
                    | |- updm _ _ _ = Some _ =>
                        unfold updm;
                        solve [ (rewrite ST R1W; simpl; done)
                              | (rewrite vt_eq0; done)
                              | (repeat rewrite setmE; match goal with |- context [@eq_op ?T ?a ?b] => destruct (@eq_op T a b) end; subst; simpl; try done; rewrite OLD; simpl; done)
                              | (repeat rewrite setmE; match goal with |- context [@eq_op ?T ?a ?b] => destruct (@eq_op T a b) end; subst; simpl; try done; deduce_reg reg_match; done) ]
                    | |- address_correctness _ _ _ _ =>
                        solve [ exact I
                              | (try (subst new_t1); destruct t1; simpl; auto)
                              | (subst; simpl; eapply (s_reg_cor _ _ R1W))
                              | (subst; simpl; eapply (s'_reg_cor _ _ vt_eq0)) ]
                    | |- capability_correctness' _ _ _ _ _ =>
                        (* closes capability for new_t1 (Invalidated/Other ⇒ True) and non-Ret w1@t1;
                           the 2 Ret-case w1@t1 / v1@t1 capability goals are left for the explicit
                           capa_cor1/capa_cor3 closer below (they need the global uniqueness fact). *)
                        first [ exact I | solve [ destruct t1; try (rewrite Heqnew_t1); simpl; trivial ] ]
                    | |- data_match _ _ _ _ _ =>
                        solve [ (simpl; split; reflexivity)
                              | (split; auto; subst; destruct t1; simpl; auto; try (destruct vt_match0; auto))
                              | (destruct vt_match0; subst; unfold color_of in *; simpl in *; split; trivial) ]
                    end).
          (* The two passes above close 17 of the 19 reg_write/pc_incr premises GENUINELY
             (same_pc, all data_match, all address, all updm×4, both state-eqs, and the
             new_t1 + non-Ret w1@t1 capabilities).  The 2 remaining are the Ret-case w1@t1 /
             v1@t1 capability_correctness' premises (state = reg-write intermediate with r1
             invalidated; mem unchanged).  Closed GENUINELY below by the global capability
             uniqueness facts capa_cor1 (s1) / capa_cor3 (s3) from [inversion common]: r1 held
             the unique Ret n0 capability (R1W / vt_eq0), so (A) no memory cell can hold it,
             (B) no register OTHER than r1 holds it and r1 is now invalidated, (C) it is in the
             stack metadata.  This is the original capa_cor1/capa_cor3 argument, made
             order-independent (the only port issue was the hardcoded fresh [Heqa3] name, here
             replaced by [case: eqP]/[case: ifP]). *)
          (* goal 1 = WS_S1 (s1, w1, R1W, capa_cor1); goal 2 = WS_S3 (s3, v1, vt_eq0, capa_cor3) *)
          1:{ destruct t1 as [n0 | | |]; simpl; trivial.
              assert (RR : regs s1 r1 = Some (w1 @ (Ret n0))) by
                  (first [ exact R1W | (rewrite ST; exact R1W) | (rewrite ST in R1W; exact R1W)
                         | (rewrite -ST; exact R1W) ]).
              move: (capa_cor1 w1 n0 (inl r1) RR) => [is_in unicity].
              split.
              - intros v'' w t' t'eq memeq.
                move: (capa_cor1 v'' n0 (inr w) (ex_intro _ t' (conj memeq t'eq))) => [_ unicity2].
                exact (unicity2 (inl r1) w1 RR).
              - split.
                + intros v'' r' req; move: req; rewrite setmE.
                  case: ifP => Hrr.
                  * move=> Heq; rewrite Heqnew_t1 in Heq; discriminate Heq.
                  * move=> req; move: (unicity (inl r') v'' req) => Hr1r;
                    move: Hrr; rewrite Hr1r eqxx; discriminate.
                + exact is_in. }
          1:{ destruct t1 as [n0 | | |]; simpl; trivial.
              assert (RR : regs s3 r1 = Some (v1 @ (Ret n0))) by
                  (first [ exact vt_eq0 | (rewrite ST; exact vt_eq0) | (rewrite ST in vt_eq0; exact vt_eq0)
                         | (rewrite -ST; exact vt_eq0) ]).
              move: (capa_cor3 v1 n0 (inl r1) RR) => [is_in unicity].
              split.
              - intros v'' w t' t'eq memeq.
                move: (capa_cor3 v'' n0 (inr w) (ex_intro _ t' (conj memeq t'eq))) => [_ unicity2].
                exact (unicity2 (inl r1) v1 RR).
              - split.
                + intros v'' r' req; move: req; rewrite setmE.
                  case: ifP => Hrr.
                  * move=> Heq; rewrite Heqnew_t1 in Heq; discriminate Heq.
                  * move=> req; move: (unicity (inl r') v'' req) => Hr1r;
                    move: Hrr; rewrite Hr1r eqxx; discriminate.
                + exact is_in. }
(* ORIGINAL MOV EQUIV BULLETS (reference; being replaced by the dispatcher above):
          -- subst. simpl. eapply same_pc_normal;
             [ simpl; split; [exact Heqi' | exact code_i']
             | subst; unfold color_of; simpl; exact eq_off
             | simpl in *; rewrite pc_s1_s3; simpl; word_ac ].
          -- split; auto. subst. destruct t1; simpl; auto. destruct vt_match0. auto.
          -- subst. destruct t1; simpl; auto.
          -- subst. destruct t1; simpl; auto.
          -- subst new_t1. destruct t1; simpl; trivial.
          -- subst new_t1. destruct t1; simpl; trivial.
          (* -- subst new_t1. destruct t1; simpl; trivial. *)
          -- rewrite ST R1W. simpl. done.
          -- rewrite vt_eq0. done.
          -- destruct vt_match0. subst. unfold color_of in *. simpl in *. split; trivial.
          -- destruct t1; simpl; trivial. split.
             ++ intros v'' w t' t'eq memeq. pose proof (capa_cor1 v'' n0 (inr w) (ex_intro _ t' (conj memeq t'eq))) as [is_in unicity].
                eapply (unicity (inl _)); eauto. subst. exact R1W.
             ++ rewrite ST in capa_cor1. pose proof (capa_cor1 w1 n0 (inl r1) R1W) as [is_in unicity]. split; auto.
                intros v'' r' req. rewrite setmE in req. unfold_match' req. simplify_some. subst new_t1. inv H2.
                rewrite (unicity (inl r') _ req) in Heqa3. rewrite eq_refl in Heqa3. inv Heqa3.
          -- destruct t1; simpl; trivial. split.
             ++ intros v'' w t' t'eq memeq. pose proof (capa_cor3 v'' n0 (inr w) (ex_intro _ t' (conj memeq t'eq))) as [is_in unicity].
                eapply (unicity (inl _)); eauto.
             ++ pose proof (capa_cor3 v1 n0 (inl r1) vt_eq0) as [is_in unicity]. split; auto.
                intros v'' r' req. rewrite setmE in req. unfold_match' req. simplify_some. subst new_t1. inv H2.
                rewrite (unicity (inl r') _ req) in Heqa3. rewrite eq_refl in Heqa3. inv Heqa3.
          -- subst. simpl. eapply (s_reg_cor _ _ R1W).
          -- subst. simpl. eapply (s'_reg_cor _ _ vt_eq0).
          (* -- inversion weak as [? ? ? _ _ _ _ s'_reg_cor' _]. *)
          (*    subst. simpl. eapply (s'_reg_cor' _ _ vt_eq0). *)
          -- repeat rewrite setmE. match goal with |- context [@eq_op ?T r2 r1] => destruct (@eq_op T r2 r1) end; subst; simpl; try done.
             rewrite OLD. simpl. done.
          -- repeat rewrite setmE. match goal with |- context [@eq_op ?T r2 r1] => destruct (@eq_op T r2 r1) end; subst; simpl; try done.
             deduce_reg reg_match. done.
          -- simpl. subst. trivial.
          -- subst. simpl. trivial.
   END ORIGINAL MOV EQUIV BULLETS *)
      (* ----- Binop opcode (un-commented, being converted) ----- *)
      + unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        unfold_all; try unfold_match; unfold_all.
        all: try (clear -Heqa2; repeat unfold_match' Heqa2; done); simpl in *. (* eliminates many goals *)
        try (rewrite ST in PC_None; unfold color_of in PC_None; rewrite PC in PC_None; try (inversion PC_None; done || clear PC_None)).
        try (assert (tpc1 = tpc0) by (clear -Heqa2; unfold_match' Heqa2); subst tpc1).
        try (assert (ts0 = (ts (mvec None)) ) by
                 (unfold mvec in *; simpl; clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                  destruct Heqa2 as [_ _ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ts0).
        try (unfold mvec in *; assert (ti1 = ti0) by
                    (clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                     destruct Heqa2 as [_ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ti1).
        try (rewrite ST in end_s1 Heqa2; simpl in end_s1, Heqa2;
                  destruct (end_s1 pc0 _ PC) as [ instr_is_halt | [[i' ti'] [Heqi' code_i']]];
                  [destruct ti0; simpl in *; auto; try unfold_match' Heqa5; try done |
                    (match goal with
                     | op: _ = op_of_word _, inst: instr_of_args _ = _ |- _
                       => simpl in instr_is_halt;  rewrite <- op in instr_is_halt; simpl in instr_is_halt;
                         rewrite inst in instr_is_halt; done end) |
                    simpl in Heqi'; try (rewrite Heqi' in Heqa2; inversion Heqa2) ] ).
        unfold check_belong, belong, reg_clear_list in *.
        simpl in *; unfold_all.
        (* 7-8: (match (type of Heqa2) with *)
        (*         (_ = match ?m ?w with _ => _ end) *)
        (*         => eapply (@modusponens (exists res, m w = Some res /\ *)
        (*                                          (LRC.color (taga res) \in domm ip -> *)
        (*                                           is_code (taga res)))); *)
        (*           [|intros [res [res_eq res_code]]; rewrite res_eq in Heqa2] *)
        (*       end). *)
        (* 11: remember (mem0 pc') as next_pc_content; destruct next_pc_content. *)
        try (match goal with
                    |- exists _ _, _ => repeat (unfold_all || unfold_match || rewrite orb_false_r in Heqa4, Heqa16) end).
        convert_eq_op.
        unfold is_jump in *; try (unfold_match; subst t1).
        unfold hshead in *; simpl in *.
        try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3. (* trick to keep an equality on s1 and s3 *)
        try (pose proof (esym Heqa3) as PC; clear Heqa3).
        try (match goal with c: Component.id |- _ => rename c into color end).
        try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                  [exfalso; subst; simpl in *; rewrite (proj1 eq_none) in PC; done |]).
        try (assert (color_of s1 = c0) as eq by (unfold color_of; subst; simpl; clear -tag_pc1; destruct tpc0; simpl in *; congruence);
                  subst c0).
        try (destruct tpc0; unfold_all).
        try (unfold compatible in *; rewrite eq in m_compat).
        try rewrite m_compat in side_eq.


        edestruct (code_left pc0) as [X _].
        { instantiate (1 := i0). unfold is_relevant_comp.
          (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ]). }
        { instantiate (1 := off). rewrite ST in eq_off; eauto. }
        { instantiate (1 := {| vtag := vtag; color := i0; entry := entry; is_code := true |}); eauto. }
        { eauto. }
        rewrite ST in X. simpl in X.
        specialize (X PC) as [vpc [match_dec mem_s3]].

        edestruct (code_left (pc0 + 1)%w) as [X' _].
        { instantiate (1 := i0). unfold is_relevant_comp.
          (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ]). }
        { instantiate (1 := off). rewrite ST in eq_off; eauto. }
        { instantiate (1 := {| vtag := vtag0; color := i0; entry := entry0; is_code := is_code0 |}); eauto. }
        { eauto. }
        rewrite ST in X'. simpl in X'.
        specialize (X' Heqi') as [vpc' [match_dec' mem_s3']].
        
        deduce_equality_r OLD.
        deduce_equality_r R1W.
        deduce_equality_r R2W.
        remember (r2 == r1) as cond.
        remember (r3 == r1) as cond1.
        remember (r3 == r2) as cond2.
        destruct vt_match0 as [? match_t1]. subst t0. destruct t1; unfold is_other in *; try congruence. subst v1.
        destruct vt_match1 as [? match_t3]. subst t2. destruct t3; unfold is_other in *; try congruence. subst v2.
        exists (@State mt lrc_tags _ mem3
                  (setm (setm (setm regs3 r1 (w1@Other)) r2 (w2@Other)) r3 ((binop_denote op0 w1 w2)@Other))
                  ((addw pc3_val onew)@(Level n i0)) tt); exists M. simpl.
        split.
        * eapply plus_one; try eapply step_binop. eauto.
          -- rewrite eq_s3 in pc_s1_s3.
             simpl in pc_s1_s3. subst pc3_val. rewrite ST. simpl. rewrite eq_s3 in mem_s3. rewrite mem_s3. reflexivity.
          -- inversion match_dec.
             ++ subst vpc.
                decode_instr_eq.
             ++ assert (decode_instr i = Some (Binop op0 r1 r2 r3)) by decode_instr_eq.
                congruence.
             ++ assert (decode_instr i = Some (Binop op0 r1 r2 r3)) by decode_instr_eq.
                congruence.
          -- rewrite eq_s3 in vt_eq0. eauto.
          -- rewrite eq_s3 in vt_eq1. eauto.
          -- rewrite eq_s3 in vt_eq. eauto.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_all.
             deduce_reg reg_match.
             unfold side_of in side_eq. unfold_match' side_eq. subst s1 s3. simpl in *. deduce_equality_r Heqi'.
             rewrite vt_eq2. simpl.
             unfold check_belong, belong. rewrite eq_refl. simpl.
             unfold updm. rewrite vt_eq0. simpl.
             try rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3. try rewrite ST. unfold color_of. simpl. rewrite eq_refl. simpl.
             repeat rewrite setmE. simpl in Heqcond, Heqcond1, Heqcond2. unfold stack_value in *. simpl in *. rewrite <- vt_eq0.
             repeat rewrite setmE;
             match goal with |- context [@eq_op ?T r2 r1] => destruct (@eq_op T r2 r1) eqn:Hc0 end; simpl;
             [ move/eqP: Hc0 => r_eq; rewrite r_eq in vt_eq1 | idtac ];
             rewrite vt_eq1; simpl;
             repeat rewrite setmE;
             repeat (match goal with |- context [@eq_op ?T r3 ?x] => destruct (@eq_op T r3 x) eqn:? end; simpl);
             try (rewrite vt_eq); simpl; reflexivity.
        * rewrite ST in Heqa11. simpl in Heqa11. rewrite R1W in Heqa11. simplify_some.
          repeat rewrite setmE in Heqa12. simpl in Heqa12.
          assert (eq_a: a = w2@Other).
          { subst s1; rewrite R2W in Heqa12;
            match type of Heqa12 with context [@eq_op ?T r2 r1] => destruct (@eq_op T r2 r1) eqn:Hcd end;
            simplify_some;
            [ move/eqP: Hcd => r_eq; subst r2; congruence | reflexivity ]. }
          destruct a as [w' t']. inversion eq_a. clear eq_a. subst t'. rewrite <- H1. simpl.
          remember (binop_denote op0 w1 w2) as new_w.
          eapply preserves_equiv_right_reg_write with (r := r3) (v := new_w@Other) (v' := new_w@Other)
            (s1 := @State mt lrc_tags _ (mem s1) (setm (setm (regs s1) r1 (w1@Other)) r2 (w'@Other)) ((addw (vala (pc s1)) onew)@(taga (pc s1))) tt)
            (s3 := @State mt lrc_tags _ (mem s3) (setm (setm (regs s3) r1 (w1@Other)) r2 (w2@Other)) ((addw (vala (pc s3)) onew)@(taga (pc s3))) tt).
          eapply preserves_equiv_right_reg_write with (r := r2) (v := w'@Other) (v' := w2@Other)
            (s1 := @State mt lrc_tags _ (mem s1) (setm (regs s1) r1 (w1@Other)) ((addw (vala (pc s1)) onew)@(taga (pc s1))) tt)
            (s3 := @State mt lrc_tags _ (mem s3) (setm (regs s3) r1 (w1@Other)) ((addw (vala (pc s3)) onew)@(taga (pc s3))) tt).
          eapply preserves_equiv_right_reg_write with (r := r1) (v := w1@Other) (v' := w1@Other)
            (s1 := @State mt lrc_tags _ (mem s1) (regs s1) ((addw (vala (pc s1)) onew)@(taga (pc s1))) tt)
            (s3 := @State mt lrc_tags _ (mem s3) (regs s3) ((addw (vala (pc s3)) onew)@(taga (pc s3))) tt).
          eapply (preserves_equiv_right_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)) (tpc1' := (taga (pc s1)))
                                                     (pc3' := (addw (vala (pc s3)) onew)) (tpc3' := (taga (pc s3))); auto. eauto.
          (* pass 1: state-eqs (explicit states above make them first-order) *)
          all: try (solve [ reflexivity | (rewrite ST; simpl; reflexivity) | (rewrite eq_s3; simpl; reflexivity)
                          | (rewrite eq_s3; simpl; rewrite eq_s3 in pc_s1_s3; simpl in pc_s1_s3; subst pc3_val;
                             rewrite eq_s3 in tag_pc3; simpl in tag_pc3; rewrite tag_pc3; rewrite ST; unfold color_of; simpl; reflexivity)
                          | done ]).
          (* pass 2: value premises (all @Other ⇒ capability/address = exact I, NO uniqueness) *)
          all: try (lazymatch goal with
                    | |- pc_code_color _ => pcc_close2 (PCCM.step_me_mp step_1) ST
                    | |- same_pc _ _ _ =>
                        subst; simpl; eapply same_pc_normal;
                        [ simpl; split; [exact Heqi' | exact code_i']
                        | subst; unfold color_of; simpl; exact eq_off
                        | simpl in *; rewrite pc_s1_s3; simpl; word_ac ]
                    | |- capability_correctness' _ _ _ _ _ => exact I
                    | |- address_correctness _ _ _ _ => exact I
                    | |- data_match _ _ _ _ _ => simpl; split; reflexivity
                    | |- updm ?rr ?ww _ = Some _ =>
                        let Hu := fresh in
                        assert (exists w, rr ww = Some w) as [? Hu] by
                          (simpl; repeat rewrite setmE; simpl;
                           repeat (match goal with |- context [@eq_op ?T ?a ?b] => destruct (@eq_op T a b) end; simpl);
                           first [ eexists; reflexivity
                                 | eexists; (first [exact vt_eq0 | exact vt_eq1 | exact vt_eq])
                                 | (destruct (proj1 (reg_match _ _) vt_eq0) as [? [_ ?]]; eexists; eassumption)
                                 | (destruct (proj1 (reg_match _ _) vt_eq1) as [? [_ ?]]; eexists; eassumption)
                                 | (destruct (proj1 (reg_match _ _) vt_eq) as [? [_ ?]]; eexists; eassumption) ]);
                        unfold updm; rewrite Hu; rewrite ?ST; rewrite ?eq_s3;
                        try (rewrite Heqnew_w); try (rewrite <- H1); simpl; reflexivity
                    end).
(* ===== BEGIN ADMITTED OPCODE BODIES (Load .. syscall) — see TODO above =====
      + unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        unfold_all; try unfold_match; unfold_all.
        all: try (clear -Heqa2; repeat unfold_match' Heqa2; done); simpl in *. (* eliminates many goals *)
        try (rewrite ST in PC_None; unfold color_of in PC_None; rewrite PC in PC_None; try (inversion PC_None; done || clear PC_None)).
        try (assert (tpc1 = tpc0) by (clear -Heqa2; unfold_match' Heqa2); subst tpc1).
        try (assert (ts0 = (ts (mvec None)) ) by
                 (unfold mvec in *; simpl; clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                  destruct Heqa2 as [_ _ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ts0).
        try (unfold mvec in *; assert (ti1 = ti0) by
                    (clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                     destruct Heqa2 as [_ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ti1).
        try (rewrite ST in end_s1 Heqa2; simpl in end_s1, Heqa2;
                  destruct (end_s1 pc0 _ PC) as [ instr_is_halt | [[i' ti'] [Heqi' code_i']]];
                  [destruct ti0; simpl in *; auto; try unfold_match' Heqa5; try done |
                    (match goal with
                     | op: _ = op_of_word _, inst: instr_of_args _ = _ |- _
                       => simpl in instr_is_halt;  rewrite <- op in instr_is_halt; simpl in instr_is_halt;
                         rewrite inst in instr_is_halt; done end) |
                    simpl in Heqi'; try (rewrite Heqi' in Heqa2; inversion Heqa2) ] ).
        unfold check_belong, belong, reg_clear_list in *.
        simpl in *; unfold_all.
        (* 7-8: (match (type of Heqa2) with *)
        (*         (_ = match ?m ?w with _ => _ end) *)
        (*         => eapply (@modusponens (exists res, m w = Some res /\ *)
        (*                                          (LRC.color (taga res) \in domm ip -> *)
        (*                                           is_code (taga res)))); *)
        (*           [|intros [res [res_eq res_code]]; rewrite res_eq in Heqa2] *)
        (*       end). *)
        (* 11: remember (mem0 pc') as next_pc_content; destruct next_pc_content. *)
        try (match goal with
                    |- exists _ _, _ => repeat (unfold_all || unfold_match || rewrite orb_false_r in Heqa4, Heqa16) end).
        convert_eq_op.
        unfold is_jump in *; try (unfold_match; subst t1).
        unfold hshead in *; simpl in *.
        try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3. (* trick to keep an equality on s1 and s3 *)
        try (pose proof (esym Heqa3) as PC; clear Heqa3).
        try (match goal with c: Component.id |- _ => rename c into color end).
        try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                  [exfalso; subst; simpl in *; rewrite (proj1 eq_none) in PC; done |]).
        try (assert (color_of s1 = c0) as eq by (unfold color_of; subst; simpl; clear -tag_pc1; destruct tpc0; simpl in *; congruence);
                  subst c0).
        try (destruct tpc0; unfold_all).
        try (unfold compatible in *; rewrite eq in m_compat).
        try rewrite m_compat in side_eq.
        rewrite ST in tag_pc1. inversion tag_pc1. subst n1 i1.

        edestruct (code_left pc0) as [X _].
        { instantiate (1 := color). unfold is_relevant_comp.
          (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ]). }
        { instantiate (1 := off). rewrite ST in eq_off; eauto. }
        { instantiate (1 := {| vtag := vtag; color := color; entry := entry; is_code := true |}); eauto. }
        { eauto. }
        rewrite ST in X. simpl in X.
        specialize (X PC) as [vpc [match_dec mem_s3]].

        edestruct (code_left (pc0 + 1)%w) as [X' _].
        { instantiate (1 := color). unfold is_relevant_comp.
          (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ]). }
        { instantiate (1 := off). rewrite ST in eq_off; eauto. }
        { instantiate (1 := {| vtag := vtag0; color := color; entry := entry0; is_code := is_code0 |}); eauto. }
        { eauto. }
        rewrite ST in X'. simpl in X'.
        specialize (X' Heqi') as [vpc' [match_dec' mem_s3']].

        deduce_equality_r R1W.
        deduce_equality_r MEM1.
        deduce_equality_r OLD.
        destruct vt_match as [? match_t]. subst t. destruct t1; unfold is_other in *; try congruence. subst v0.
        eexists; exists M. simpl.
        split.
        * eapply (plus_left _ [::]); try eapply step_load; eauto.
          -- rewrite eq_s3 in pc_s1_s3.
             simpl in pc_s1_s3. subst pc3_val. rewrite ST. simpl. rewrite eq_s3 in mem_s3. rewrite mem_s3. reflexivity.
          -- inversion match_dec.
             ++ subst vpc.
                decode_instr_eq.
             ++ assert (decode_instr i = Some (Load r1 r2)) by decode_instr_eq.
                congruence.
             ++ assert (decode_instr i = Some (Load r1 r2)) by decode_instr_eq.
                congruence.
          -- rewrite eq_s3 in vt_eq. eauto.
          -- rewrite eq_s3 in vt_eq0. eauto.
          -- rewrite eq_s3 in vt_eq1. eauto.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_bind. deduce_reg reg_match.
             rewrite eq_s3. simpl.

             rewrite eq_s3 in pc_s1_s3.
             simpl in pc_s1_s3. subst pc3_val. rewrite ST. simpl. rewrite eq_s3 in mem_s3'. simpl in mem_s3'.
             rewrite -addwA in mem_s3'. rewrite (addwC 1%w _) in mem_s3'. rewrite addwA in mem_s3'.
             rewrite !mem_s3'. simpl.
             rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3.
             destruct vt_match0. subst t0. simpl. rewrite eq_refl. simpl.
             unfold check_belong, belong. rewrite eq_refl. simpl.
             try rewrite eq_s3 in tag_pc3. simpl in *.
             try rewrite ST. simpl.
             subst s3.
             rewrite vt_eq. simpl. unfold updm. rewrite vt_eq. simpl. rewrite vt_eq0. simpl.
             repeat rewrite setmE. unfold stack_value in *. simpl in *.
             remember (r2 == r1) as cond. simpl in Heqcond.
             (* rewrite <- Heqcond. *)
             destruct cond.
             ++ assert (r_eq: r2 = r1) by (eq_op_to_eq). simpl. reflexivity.
             ++ rewrite vt_eq1. simpl. done.
          -- eapply star_refl.
          -- done.
        * simpl in *.
          remember (if is_address vtag1 then Invalidated else Other) as new_t2.
          rewrite ST in Heqa12, Heqa13. rewrite R1W in Heqa12. rewrite MEM1 in Heqa13.
          do 2 simplify_some. simpl.
          remember ({| vtag := new_t2; color := color; entry := entry1; is_code := false |}) as t2'.
          eapply preserves_equiv_right_reg_write with (r := r2) (v := w2@vtag1) (v' := v1@vtag1).
          eapply preserves_equiv_right_mem_write with (v := w2@t2') (v' := v1@t2') (w := w1).
          eapply preserves_equiv_right_reg_write with (r := r1) (v := w1@Other) (v' := w1@Other).
          eapply (preserves_equiv_right_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)) (tpc1' := (taga (pc s1)))
                                                     (pc3' := (addw (vala (pc s3)) onew)) (tpc3' := (taga (pc s3))); auto. eauto.

          all: simpl.
          all: try (match goal with | |- ( @Logic.eq (@Symbolic.state _ _ _) ?s _) => trivial end).
          all: simpl.
          all: try (match goal with
                      |- context[updm _ _] =>
                        unfold updm;
                        simpl; try ((rewrite ST OLD) ||  (rewrite ST R1W) || (rewrite ST MEM1));
                        try (rewrite vt_eq1 || rewrite vt_eq || rewrite vt_eq0); simpl; done
                    end).
          all: try subst t2'; simpl; trivial.
          all: try (subst; destruct vtag1; simpl; (exact Heqi' || auto); done).
          all: try done.
          -- rewrite ST. eapply same_pc_normal; simpl; eauto.
             ++ unfold color_of in *. subst. simpl in *. eauto.
             ++ rewrite pc_s1_s3 ST. simpl. rewrite <- (addwA pc0 _). rewrite (addwC (as_word _) onew). rewrite addwA. done.
          -- split; trivial. simpl. split; auto. subst. destruct vtag1; simpl; auto. destruct vt_match0. simpl in *.
             destruct H1. done.
          -- destruct entry1; auto. exfalso. rewrite ST in entry_code1.
             pose proof (entry_code1 _ _ _ MEM1 Logic.eq_refl). simpl in H. inversion H.
          -- unfold side_of, color_of in side_eq. rewrite ST in side_eq. simpl in side_eq. unfold_match.
          -- rewrite ST. intros v' disj. destruct disj.
             ++ simpl in *. rewrite MEM1 in H. simplify_some. done.
             ++ rewrite vt_eq0 in H. simplify_some. destruct vt_match0. subst. auto.
          -- simpl. eexists; split; eauto. destruct vt_match0. subst. auto.
          -- simpl. eexists; split; eauto. destruct vt_match0. subst. simpl. rewrite MEM1. done.
             destruct vt_match0. subst. auto.
          -- destruct vt_match0. subst. split; auto. simpl in *. destruct H1. auto.
          -- destruct vtag1; simpl; trivial. split.
             ++ intros v' w t teq weq. rewrite setmE in weq. unfold_match' weq.
                { inv weq. inversion teq. } rewrite ST in capa_cor1.
                pose proof (capa_cor1 v' n0 (inr w) (ex_intro _ t (conj weq teq))) as [is_in unicity]. simpl in unicity.
                pose proof (unicity (inr w1) w2). simpl in H. rewrite H in Heqa3. rewrite eq_refl in Heqa3. inv Heqa3.
                eexists. split. exact MEM1. trivial.
             ++ pose proof (capa_cor1 w2 n0 (inr w1)). simpl in H.
                destruct H as [is_in unicity]. { eexists. split. subst. exact MEM1. trivial. }
                split; auto. intros v' r req. rewrite setmE in req. unfold_match' req. subst.
                eapply (unicity (inl _)); eauto.
          -- destruct vtag1; simpl; trivial. split.
             ++ intros v' w t teq weq. rewrite setmE in weq. unfold_match' weq.
                { inv weq. inversion teq. }
                pose proof (capa_cor3 v' n0 (inr w) (ex_intro _ t (conj weq teq))) as [is_in unicity]. simpl in unicity.
                pose proof (unicity (inr w1) v1). simpl in H. rewrite H in Heqa3. rewrite eq_refl in Heqa3. inv Heqa3.
                eexists. split. subst. exact vt_eq0. destruct vt_match0. subst. trivial.
             ++ pose proof (capa_cor3 v1 n0 (inr w1)). simpl in H.
                destruct H as [is_in unicity]. { eexists. split. subst. exact vt_eq0. destruct vt_match0. subst. trivial. }
                split; auto. intros v' r req. rewrite setmE in req. unfold_match' req. subst.
                eapply (unicity (inl _)); eauto.
          -- subst. unfold memory_address_correctness in *. simpl in *. remember (@eq_op (Ord.eqType _) w2 w1) as cond.
             destruct vtag1; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond; destruct cond; simpl; convert_eq_op.
               all:try (eapply (s_mem_cor _ _ _ MEM1)).
               all:try (eapply modusponens; [eapply (s_mem_cor _ _ _ MEM1)| simpl; intros [? [eq1 no_code]]]; rewrite MEM1 in eq1;
                    simplify_some; simpl in *; eexists; split; [eauto|]; intro in_ip; eapply no_code; eauto).
          -- inversion weak as [? ? ? _ _ (* s_mem_cor' *) s'_mem_cor' _ _].
             subst. unfold memory_address_correctness in *. simpl in *. remember (@eq_op (Ord.eqType _) v1 w1) as cond.
             destruct vtag1; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond; destruct cond; simpl; convert_eq_op.
             all:try (destruct vt_match0; subst t0; eapply (s'_mem_cor _ _ _ vt_eq0)).
             all:try (destruct vt_match0; subst t0; eapply modusponens;
                      [eapply (s'_mem_cor _ _ _ vt_eq0)| simpl; intros [? [eq1 no_code]]]; rewrite vt_eq0 in eq1;
                    simplify_some; simpl in *; eexists; split; [eauto|]; intro in_ip; eapply no_code; eauto).
          (* -- inversion weak as [? ? ? _ _ s_mem_cor' s'_mem_cor' _ s'_reg_cor' _]. *)
          (*    subst. *)
          (*    unfold register_address_correctness, memory_address_correctness in *. *)
          (*    simpl in *. *)
          (*    rewrite /address_correctness. destruct vtag1; auto. *)
          (*    ++ admit. *)
          (*    ++ rewrite setmE. *)
          (*       case: ifP => /eqP cond. *)
          (*       ** subst v1. admit. *)
          (*       ** simpl. *)
          (*          eapply s'_mem_cor in vt_eq0. *)
          (*          unfold address_correctness in vt_eq0. *)
          (*          destruct vt_match0 as [? [? ?]]. *)
          (*          subst. simpl in *. *)
          (*          destruct vt_eq0 as [? [? ?]]; eexists; split; eauto. *)
          (*          intros. simpl in H4. *)
          (*          { eexists; split; eauto. eauto. } *)
          (*    simpl in *. remember (@eq_op (Ord.eqType _) v1 w1) as cond. *)
          (* -- *)
          (* (* -- inversion weak as [? ? ? _ _ s_mem_cor' s'_mem_cor' _ _ _]. *) *)
          (* (*    subst. unfold memory_address_correctness in *. simpl in *. *) *)

          (* (*    remember (@eq_op (Ord.eqType _) v1 w1) as cond. *) *)
          (* (*    destruct vtag1; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond; destruct cond; simpl; convert_eq_op. *) *)
          (* (*    { eexists; split; eauto. *) *)
          (* (*      simpl. *) *)
          (* (*      unfold side_of, color_of in side_eq. simpl in side_eq. unfold_match. *) *)
          (* (*      admit. } *) *)
          (* (*    { destruct vt_match0; subst t0. *) *)
          (* (*      simpl in H1; destruct H1. *) *)
          (* (*      destruct H1 as [sv' [comp' INM]]. *) *)
          (* (*      assert (forall mem1 mem2 mem3 M n sv sv' v1 t1 comp', *) *)
          (* (*                 In (sv, sv', v1@t1, comp') M -> *) *)
          (* (*              wf_stack mem1 mem2 mem3 n M -> *) *)
          (* (*              exists v0, mem3 v1 = Some v0 /\ is_code (taga v0)). *) *)
          (* (*      { clear. *) *)
          (* (*        intros mem1 mem2 mem3 M. *) *)
          (* (*        induction M. *) *)
          (* (*        - intros; inv H. *) *)
          (* (*        - intros. *) *)
          (* (*          inv H. *) *)
          (* (*          + inv H0. *) *)
          (* (*            * unfold points_to_comp_code in PTS_CODE3. *) *)
          (* (*              destruct (mem3 (v0 + as_word off)%w); simpl in *; try contradiction. *) *)
          (* (*              destruct PTS_CODE3; eauto. *) *)
          (* (*            * unfold points_to_comp_code in PTS_CODE3. *) *)
          (* (*              destruct (mem3 (v2 + as_word off)%w); simpl in *; try contradiction. *) *)
          (* (*              destruct PTS_CODE3; eauto. *) *)
          (* (*          + inv H0. *) *)
          (* (*            * eapply IHM; eauto. *) *)
          (* (*            * eapply IHM; eauto. } *) *)
          (* (*      edestruct H1 as [res [? ?]]; eauto. } *) *)
          (* (*    { eexists; split; eauto. *) *)
          (* (*      simpl. *) *)
          (* (*      unfold side_of, color_of in side_eq. simpl in side_eq. unfold_match. *) *)
          (* (*      admit. } *) *)
          (* (*    (* all:try (destruct vt_match0; subst t0; eapply (s'_mem_cor _ _ _ vt_eq0)). *) *) *)
          (* (*    (* all:try (destruct vt_match0; subst t0; eapply modusponens; *) *) *)
          (* (*    (*          [eapply (s'_mem_cor' _ _ _ vt_eq0)| simpl; intros [? [eq1 no_code]]]; rewrite vt_eq0 in eq1; *) *) *)
          (* (*    (*        simplify_some; simpl in *; eexists; split; [eauto|]; intro in_ip; eapply no_code; eauto). *) *) *)
          (* (*    { destruct vt_match0; subst t0. *) *)
          (* (*      have vt_eq0' := vt_eq0. *) *)
          (* (*      eapply s'_mem_cor in vt_eq0. *) *)
          (* (*      move: vt_eq0. rewrite /address_correctness. simpl. *) *)
          (* (*      2: { simpl. admit. } *) *)
          (* (*      move=> [v0 [-> code]]. *) *)
          (* (*      eexists; split; eauto. *) *)
          (* (*      simpl in H1; destruct H1. *) *)
          (* (*      (* assert ( *) *) *)
          (* (*      (*     is_true (LRC.color (taga *) *) *)
          (* (*      (*                           {| vala := (w2 + as_word off)%w; *) *) *)
          (* (*      (*                             taga := {| vtag := InternalJump; color := color; entry := entry1; is_code := false |} |}) \in domm ip)). *) *) *)
          (* (*      (* admit. *) *) *)
          (* (*      eapply s'_mem_cor' in vt_eq0' _ _ _ vt_eq0'). *) *)
          (* (*      simpl in H1. destruct H1. *) *)
          (* (*      eexists; split. eauto. *) *)
          (* (*      (* use data_match' *) *) *)
          (* (*      move=> ?. *) *)
               
               
          (* (*      intros H3. *) *)
          (* (*      eapply s'_mem_cor' in H3. unfold address_correctness in H3. *) *)
          (* (*      edestruct (s'_mem_cor _ _ H vt_eq0). *) *)

          (* (*      simpl in H2.eapply H2. *) *)
          (* (*      eapply s'_mem_cor. *) *)
          (* (*      destruct H1 as [sv' [comp' INM]]. *) *)
          (* (*      assert (forall mem1 mem2 mem3 M n sv sv' v1 t1 comp', *) *)
          (* (*                 In (sv, sv', v1@t1, comp') M -> *) *)
          (* (*              wf_stack mem1 mem2 mem3 n M -> *) *)
          (* (*              exists v0, mem3 v1 = Some v0 /\ is_code (taga v0)). *) *)
          (* (*      { clear. *) *)
          (* (*        intros mem1 mem2 mem3 M. *) *)
          (* (*        induction M. *) *)
          (* (*        - intros; inv H. *) *)
          (* (*        - intros. *) *)
          (* (*          inv H. *) *)
          (* (*          + inv H0. *) *)
          (* (*            * unfold points_to_comp_code in PTS_CODE3. *) *)
          (* (*              destruct (mem3 (v0 + as_word off)%w); simpl in *; try contradiction. *) *)
          (* (*              destruct PTS_CODE3; eauto. *) *)
          (* (*            * unfold points_to_comp_code in PTS_CODE3. *) *)
          (* (*              destruct (mem3 (v2 + as_word off)%w); simpl in *; try contradiction. *) *)
          (* (*              destruct PTS_CODE3; eauto. *) *)
          (* (*          + inv H0. *) *)
          (* (*            * eapply IHM; eauto. *) *)
          (* (*            * eapply IHM; eauto. } *) *)
          (* (*      edestruct H1 as [res [? ?]]; eauto. } *) *)
          (* (*      } *) *)
               
          (* (*    } *) *)
          (* (*    all:try (destruct vt_match0; subst t0; eapply (s'_mem_cor' _ _ _ vt_eq0)). *) *)
          (* (*    all:try (destruct vt_match0; subst t0; eapply modusponens; *) *)
          (* (*             [eapply (s'_mem_cor' _ _ _ vt_eq0)| simpl; intros [? [eq1 no_code]]]; rewrite vt_eq0 in eq1; *) *)
          (* (*           simplify_some; simpl in *; eexists; split; [eauto|]; intro in_ip; eapply no_code; eauto). *) *)
          -- unfold updm. rewrite setmE. remember (@eq_op (Ord.eqType _) r2 r1) as cond. simpl in *.
             destruct cond; try done. rewrite OLD. simpl. done.
          -- unfold updm. rewrite setmE. remember (@eq_op (Ord.eqType _) r2 r1) as cond. simpl in *.
             destruct cond; try done. subst. simpl. trivial. rewrite vt_eq1. simpl. subst. done.
             Unshelve.
             all: simpl; eauto.
             all: unfold side_of, color_of in side_eq;
               simpl in side_eq;
               unfold_match.
          -- subst s3. simpl. simpl in pc_s1_s3; rewrite pc_s1_s3.
             rewrite ST; simpl. reflexivity.
      + unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        unfold_all; try unfold_match; unfold_all.
        all: try (clear -Heqa2; repeat unfold_match' Heqa2; done); simpl in *. (* eliminates many goals *)
        try (rewrite ST in PC_None; unfold color_of in PC_None; rewrite PC in PC_None; try (inversion PC_None; done || clear PC_None)).
        try (assert (tpc1 = tpc0) by (clear -Heqa2; unfold_match' Heqa2); subst tpc1).
        try (assert (ts0 = (ts (mvec None)) ) by
                 (unfold mvec in *; simpl; clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                  destruct Heqa2 as [_ _ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ts0).
        try (unfold mvec in *; assert (ti1 = ti0) by
                    (clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                     destruct Heqa2 as [_ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ti1).
        try (rewrite ST in end_s1 Heqa2; simpl in end_s1, Heqa2;
                  destruct (end_s1 pc0 _ PC) as [ instr_is_halt | [[i' ti'] [Heqi' code_i']]];
                  [destruct ti0; simpl in *; auto; try unfold_match' Heqa5; try done |
                    (match goal with
                     | op: _ = op_of_word _, inst: instr_of_args _ = _ |- _
                       => simpl in instr_is_halt;  rewrite <- op in instr_is_halt; simpl in instr_is_halt;
                         rewrite inst in instr_is_halt; done end) |
                    simpl in Heqi'; try (rewrite Heqi' in Heqa2; inversion Heqa2) ] ).
        unfold check_belong, belong, reg_clear_list in *.
        simpl in *; unfold_all.
        (* 7-8: (match (type of Heqa2) with *)
        (*         (_ = match ?m ?w with _ => _ end) *)
        (*         => eapply (@modusponens (exists res, m w = Some res /\ *)
        (*                                          (LRC.color (taga res) \in domm ip -> *)
        (*                                           is_code (taga res)))); *)
        (*           [|intros [res [res_eq res_code]]; rewrite res_eq in Heqa2] *)
        (*       end). *)
        (* 11: remember (mem0 pc') as next_pc_content; destruct next_pc_content. *)
        try (match goal with
                    |- exists _ _, _ => repeat (unfold_all || unfold_match || rewrite orb_false_r in Heqa4, Heqa16) end).
        convert_eq_op.
        unfold is_jump in *; try (unfold_match; subst t1).
        unfold hshead in *; simpl in *.
        try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3. (* trick to keep an equality on s1 and s3 *)
        try (pose proof (esym Heqa3) as PC; clear Heqa3).
        try (match goal with c: Component.id |- _ => rename c into color end).
        try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                  [exfalso; subst; simpl in *; rewrite (proj1 eq_none) in PC; done |]).
        try (assert (color_of s1 = c0) as eq by (unfold color_of; subst; simpl; clear -tag_pc1; destruct tpc0; simpl in *; congruence);
                  subst c0).
        try (destruct tpc0; unfold_all).
        try (unfold compatible in *; rewrite eq in m_compat).
        try rewrite m_compat in side_eq.
        rewrite ST in tag_pc1. inversion tag_pc1. subst n1 i1.
        deduce_equality_r R2W.
        deduce_equality_r R1W.
        deduce_equality_r OLD.
        destruct vt_match0 as [? match_t1]. subst t0. destruct t1; unfold is_other in *; try congruence. subst v1.

        (* TODO!!! HERE!!! *)
        edestruct (code_left pc0) as [X _].
        { instantiate (1 := (color_of s1)).
          simpl in side_eq.  unfold side_of in side_eq. unfold is_relevant_comp.
          eauto.
          move: side_eq; case: ((color_of s1) \in domm ip) => //=. }
        { instantiate (1 := off). eauto. }
        { instantiate (1 := {| vtag := vtag; color := color_of s1; entry := entry; is_code := true |}); eauto. }
        { eauto. }
        rewrite ST in X. simpl in X.
        specialize (X PC) as [vpc [match_dec mem_s3]].

        edestruct (code_left (pc0 + 1)%w) as [X' _].
        { instantiate (1 := (color_of s1)).
          simpl in side_eq.  unfold side_of in side_eq. unfold is_relevant_comp.
          (* rewrite ST in side_eq. simpl in side_eq.  unfold side_of in side_eq. unfold is_relevant_comp. *)
          move: side_eq; case: (color_of s1 \in domm ip) => //=. }
        { instantiate (1 := off). eauto. }
        { instantiate (1 := {| vtag := vtag1;
                              color := color_of s1;
                              entry := entry1; is_code := is_code1 |}); eauto. }
        { eauto. }
        rewrite ST in X'. simpl in X'.
        specialize (X' Heqi') as [vpc' [match_dec' mem_s3']].
        
        eexists; exists M. simpl.
        split.
        * eapply (plus_left _ [::]); try eapply step_store; eauto.
          -- rewrite eq_s3 in pc_s1_s3.
             simpl in pc_s1_s3. subst pc3_val. rewrite ST. simpl. rewrite eq_s3 in mem_s3. rewrite mem_s3. reflexivity.
          -- inversion match_dec.
             ++ subst vpc.
                decode_instr_eq.
             ++ assert (decode_instr i = Some (Store r1 r2)) by decode_instr_eq.
                congruence.
             ++ assert (decode_instr i = Some (Store r1 r2)) by decode_instr_eq.
                congruence.
          (* -- eapply (etrans _ (PC)). *)
          (* -- decode_instr_eq. *)
          -- rewrite eq_s3 in vt_eq0. eauto.
          -- rewrite eq_s3 in vt_eq. eauto.
          -- rewrite eq_s3 in vt_eq1. eauto.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_bind. deduce_reg reg_match.

             rewrite eq_s3. simpl.

             rewrite eq_s3 in pc_s1_s3.
             simpl in pc_s1_s3. subst pc3_val. rewrite ST. simpl. rewrite eq_s3 in mem_s3'. simpl in mem_s3'.
             rewrite -addwA in mem_s3'. rewrite (addwC 1%w _) in mem_s3'. rewrite addwA in mem_s3'.
             rewrite !mem_s3'. simpl.
             rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3.
             unfold check_belong, belong. rewrite eq_refl. simpl.
             destruct vt_match1. subst t3. simpl. rewrite eq_refl. simpl.
             subst s3.
             rewrite vt_eq0. simpl.
             (let H := fresh "H" in
               let v := fresh "v" in
               match goal with
               | |- context [updm ?r ?w _] =>
                   assert (exists v, (r w = Some v)) as [v H]; [| unfold updm; rewrite H; clear H] end).
             { subst. deduce_reg reg_match. eauto. }
             simpl.
             (* try rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3. try rewrite ST. rewrite eq_refl. simpl. *)
             repeat rewrite setmE. unfold stack_value in *. simpl in *. rewrite <- vt_eq0.
             remember (r2 == r1) as cond. simpl in Heqcond.
             destruct cond.
             ++ assert (r_eq: r2 = r1) by (eq_op_to_eq). rewrite r_eq in vt_eq. rewrite vt_eq. simpl. rewrite vt_eq1.
                simpl. done.
             ++ rewrite vt_eq. simpl. rewrite vt_eq1. simpl in *. done.
          -- eapply star_refl.
          -- done.
        * simpl in *. remember ({| vtag := t2; color := color ; entry := entry0; is_code := false |}) as t2'.
          remember (if is_address t2 then Invalidated else Other) as new_t2.
          eapply preserves_equiv_right_mem_write with (v := w2@t2') (v' := v0@t2') (w := w1). (* moved to erase the capacity first *)
          eapply preserves_equiv_right_reg_write with (r := r2) (v := w2@new_t2) (v' := v0@new_t2).
          eapply preserves_equiv_right_reg_write with (r := r1) (v := w1@Other) (v' := w1@Other).
          eapply (preserves_equiv_right_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)) (tpc1' := (taga (pc s1)))
                                                     (pc3' := (addw (vala (pc s3)) onew)) (tpc3' := (taga (pc s3))); auto. eauto.
          all: simpl.
          all: try (match goal with | |- ( @Logic.eq (@Symbolic.state _ _ _) ?s _) => trivial end).
          all: simpl.
          all: try (match goal with
                      |- context[updm _ _] =>
                        unfold updm;
                             simpl; try ((rewrite ST OLD) ||  (rewrite ST R1W) || (rewrite ST R2W));
                             try (rewrite vt_eq1 || rewrite vt_eq || rewrite vt_eq0); simpl; done
                    end).
          all: try subst t2'; simpl; trivial.
          all: try done.
          -- rewrite ST. eapply same_pc_normal; simpl; eauto.
             ++ unfold color_of in *. subst. simpl in *. eauto.
             ++ rewrite pc_s1_s3 ST. simpl. rewrite <- (addwA pc0 _). rewrite (addwC (as_word _) onew). rewrite addwA. done.
          -- inversion vt_match. subst. destruct t; simpl; split; trivial.
          -- subst. destruct t2; simpl; trivial.
          -- subst. destruct t2; simpl; trivial.
          -- subst. destruct t2; simpl; trivial.
          -- subst. destruct t2; simpl; trivial.
          (* -- subst. destruct t2; simpl; trivial. *)
          -- unfold updm. rewrite setmE. remember (@eq_op (Ord.eqType _) r2 r1) as cond. simpl in *.
             destruct cond; try done. rewrite R2W. done.
          -- unfold updm. rewrite setmE. remember (@eq_op (Ord.eqType _) r2 r1) as cond. simpl in *.
             destruct cond; try done. rewrite vt_eq. simpl. done.
          -- split; simpl; trivial. inversion vt_match; subst; auto.
          -- subst. simpl. trivial.
          -- destruct entry0; auto. exfalso. rewrite ST in entry_code1.
             pose proof (entry_code1 _ _ _ OLD Logic.eq_refl). simpl in H. inversion H.
          -- subst. clear -side_eq. unfold color_of, side_of in *. inv side_eq. unfold_match.
          -- rewrite ST. intros v' disj. destruct disj.
             ++ simpl in *. rewrite OLD in H. simplify_some. done.
             ++ rewrite vt_eq1 in H. simplify_some. destruct vt_match1. subst. auto.
          -- simpl. eexists; split; eauto. destruct vt_match1. subst. auto.
          -- rewrite ST. simpl. eexists; split; eauto.
          -- subst. simpl. exact Heqi'.
          -- simpl. trivial.
          -- destruct t2; simpl; trivial. split.
             ++ intros v' w t' t'eq memeq.
                pose proof (capa_cor1 v' n0 (inr w) (ex_intro _ t' (conj memeq t'eq))) as [is_in unicity]. simpl in unicity.
                eapply (unicity (inl _)); eauto. subst. exact R2W.
             ++ subst. pose proof (capa_cor1 w2 n0 (inl r2) R2W) as [is_in unicity]. simpl in unicity. split; auto.
                intros v' r req. repeat rewrite setmE in req. repeat unfold_match' req.
                rewrite (unicity (inl r) v' req) in Heqa3. rewrite eq_refl in Heqa3. inversion Heqa3.
          -- destruct t2; simpl; trivial. split.
             ++ intros v' w t' t'eq memeq.
                pose proof (capa_cor3 v' n0 (inr w) (ex_intro _ t' (conj memeq t'eq))) as [is_in unicity]. simpl in unicity.
                eapply (unicity (inl _)); eauto. subst. destruct vt_match; subst t; exact vt_eq.
             ++ destruct vt_match; subst. pose proof (capa_cor3 v0 n0 (inl r2) vt_eq) as [is_in unicity]. simpl in unicity. split; auto.
                intros v' r req. repeat rewrite setmE in req. repeat unfold_match' req.
                rewrite (unicity (inl r) v' req) in Heqa3. rewrite eq_refl in Heqa3. inversion Heqa3.
          -- subst. simpl. eapply (s_reg_cor _ _ R2W).
          -- subst. simpl. destruct vt_match. subst. eapply (s'_reg_cor _ _ vt_eq).
          (* -- inversion weak as [? ? ? _ _ _ _ _ s'_reg_cor' _]. *)
          (*    subst. simpl. destruct vt_match. subst. eapply (s'_reg_cor' _ _ vt_eq). *)
          -- subst. simpl. trivial. rewrite R1W in Heqa12. simplify_some. simpl.
             rewrite setmE in Heqa13. unfold_match' Heqa13; convert_eq_op; try rewrite R2W in Heqa13; simplify_some; simpl; trivial.
             rewrite R1W in R2W. simplify_some. trivial.
          -- subst s3. simpl. simpl in *. subst pc3_val.
             subst s1. simpl.
             destruct vt_match. subst. trivial.
      + unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        unfold_all; try unfold_match; unfold_all.
        all: try (clear -Heqa2; repeat unfold_match' Heqa2; done); simpl in *. (* eliminates many goals *)
        try (rewrite ST in PC_None; unfold color_of in PC_None; rewrite PC in PC_None; try (inversion PC_None; done || clear PC_None)).
        try (assert (tpc1 = tpc0) by (clear -Heqa2; unfold_match' Heqa2); subst tpc1).
        try (assert (ts0 = (ts (mvec None)) ) by
                 (unfold mvec in *; simpl; clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                  destruct Heqa2 as [_ _ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ts0).
        try (unfold mvec in *; assert (ti1 = ti0) by
                    (clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                     destruct Heqa2 as [_ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ti1).
        try (rewrite ST in end_s1 Heqa2; simpl in end_s1, Heqa2;
                  destruct (end_s1 pc0 _ PC) as [ instr_is_halt | [[i' ti'] [Heqi' code_i']]];
                  [destruct ti0; simpl in *; auto; try unfold_match' Heqa5; try done |
                    (match goal with
                     | op: _ = op_of_word _, inst: instr_of_args _ = _ |- _
                       => simpl in instr_is_halt;  rewrite <- op in instr_is_halt; simpl in instr_is_halt;
                         rewrite inst in instr_is_halt; done end) |
                    simpl in Heqi'; try (rewrite Heqi' in Heqa2; inversion Heqa2) ] ).
        unfold check_belong, belong, reg_clear_list in *.
        simpl in *; unfold_all.
        (match (type of Heqa2) with
           (_ = match ?m ?w with _ => _ end)
           => eapply (@modusponens (exists res, m w = Some res /\
                                            (LRC.color (taga res) \in domm ip ->
                                             is_code (taga res))));
             [|intros [res [res_eq res_code]]; rewrite res_eq in Heqa2]
         end).
        { (* 11: remember (mem0 pc') as next_pc_content; destruct next_pc_content. *)
        try (match goal with
                    |- exists _ _, _ => repeat (unfold_all || unfold_match || rewrite orb_false_r in Heqa4, Heqa16) end).
        convert_eq_op.
        unfold is_jump in *; try (unfold_match; subst t1).
        unfold hshead in *; simpl in *.
        try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3. (* trick to keep an equality on s1 and s3 *)
        try (pose proof (esym Heqa3) as PC; clear Heqa3).
        try (match goal with c: Component.id |- _ => rename c into color end).
        try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                  [exfalso; subst; simpl in *; rewrite (proj1 eq_none) in PC; done |]).
        try (assert (color_of s1 = c0) as eq by (unfold color_of; subst; simpl; clear -tag_pc1; destruct tpc0; simpl in *; congruence);
                  subst c0).
        try (destruct tpc0; unfold_all).
        try (unfold compatible in *; rewrite eq in m_compat).
        try rewrite m_compat in side_eq.
        subst. pose proof (s_reg_cor _ _ RW) as cor_RW. simpl in cor_RW.
        assert (Hyp: t1 = InternalJump \/ exists n, t1 = Ret n).
        { clear - Heqa7; repeat (unfold check_ret in *; (unfold_all || unfold_match)); eauto. }
        remember t1 as t1'.
        destruct t1; subst t1'; try (destruct Hyp as [?|Hyp]; try destruct Hyp; done);
          simpl in cor_RW; destruct cor_RW as [? [? ?]]; eauto. }
        (* 11: remember (mem0 pc') as next_pc_content; destruct next_pc_content. *)
        try (match goal with
                    |- exists _ _, _ => repeat (unfold_all || unfold_match || rewrite orb_false_r in Heqa4, Heqa16) end).
        convert_eq_op.
        unfold is_jump in *; try (unfold_match; subst t1).
        unfold hshead in *; simpl in *.
        try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3. (* trick to keep an equality on s1 and s3 *)
        try (pose proof (esym Heqa3) as PC; clear Heqa3).
        try (match goal with c: Component.id |- _ => rename c into color end).
        try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                  [exfalso; subst; simpl in *; rewrite (proj1 eq_none) in PC; done |]).
        try (assert (color_of s1 = c0) as eq by (unfold color_of; subst; simpl; clear -tag_pc1; destruct tpc0; simpl in *; congruence);
                  subst c0).
        try (destruct tpc0; unfold_all).
        try (unfold compatible in *; rewrite eq in m_compat).
        try rewrite m_compat in side_eq.
        repeat
          (let va := fresh "va" in
           let ta := fresh "ta" in
           match goal with
             a: atom _ value_tag |- _ => destruct a as [va ta]
           end).
        simpl in *.
        repeat
          (match goal with
             H: Some _ = getm (setm _ _ _) _ |- _ =>
               repeat (rewrite setmE in H; unfold as_word in H; simpl in H)
           end).
        repeat
          (match goal with
             H: Some _ = match (eq_op (_ (_ ((_ (_ ?a _)) _ _))) _) with _ => _ end,
               H' : Some _ = getm _ (as_word (_ ?a))
             |- _ => idtac a; unfold as_word in H'; rewrite ST in H; simpl in H', H; rewrite <- H' in H
           end).
        rewrite ST RA in Heqa22. simplify_some. subst va22 ta22.
        deduce_equality_r RW.
        deduce_equality_r RA.
        deduce_equality_r (esym Heqa9).
        deduce_equality_r (esym Heqa6).
        deduce_equality_r (esym Heqa11).
        deduce_equality_r (esym Heqa12).
        deduce_equality_r (esym Heqa13).
        deduce_equality_r (esym Heqa14).
        deduce_equality_r (esym Heqa15).
        deduce_equality_r (esym Heqa16).
        deduce_equality_r (esym Heqa17).
        deduce_equality_r (esym Heqa18).
        deduce_equality_r (esym Heqa19).

        edestruct (code_left pc0) as [X _].
        { instantiate (1 := (color_of s1)).
          simpl in side_eq.  unfold side_of in side_eq. unfold is_relevant_comp.
          eauto.
          move: side_eq; case: ((color_of s1) \in domm ip) => //=. }
        { instantiate (1 := off). eauto. }
        { instantiate (1 := {| vtag := vtag; color := color_of s1; entry := entry; is_code := true |}); eauto. }
        { eauto. }
        rewrite ST in X. simpl in X.
        specialize (X PC) as [vpc [match_dec mem_s3]].
        
        eexists. exists M.
        split.
        * eapply (plus_left _ [::]); try eapply step_jump. eauto.
          -- rewrite eq_s3 in pc_s1_s3.
             simpl in pc_s1_s3. subst pc3_val. rewrite ST. simpl. rewrite eq_s3 in mem_s3. rewrite mem_s3. reflexivity.
          -- inversion match_dec.
             ++ subst vpc.
                decode_instr_eq.
             ++ assert (decode_instr i = Some (Jump r)) by decode_instr_eq.
                congruence.
             ++ assert (decode_instr i = Some (Jump r)) by decode_instr_eq.
                congruence.
          -- rewrite eq_s3 in vt_eq. eauto.
          -- rewrite eq_s3 in vt_eq0. eauto.
          -- unfold reg_clear_list, reg_list. simpl. unfold as_word. subst. simpl.
             repeat
               (match goal with
                | H: _ ?w = _  |- context[_ ?w] => rewrite H; simpl
                end). trivial.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_all. rewrite vt_eq1.
             subst s1 s3. simpl in *.
             inversion vt_match. subst t. oapp_False. destruct res as [resv rest]. subst v0.
             inversion Heqa2. subst rest. unfold side_of in side_eq. unfold_match' side_eq.
             match type of (res_eq) with (_ = Some (_@?t)) => assert (res_col: color t = i0) by (inversion Heqa2; done) end.
             match type of (res_eq) with (_ = Some (_@?t)) => assert (res_code': LRC.is_code t);
                                                             [eapply res_code; simpl in *; unfold Component.id; rewrite <- Heqa4; done|]
             end.
             assert (rel: is_relevant_comp Right i0). { clear - Heqa4. simpl in *. unfold Component.id. rewrite <- Heqa4. trivial. }
             assert (eq_off': get_offset Right i0 = Some off).
             { simpl; auto. rewrite -HeqH eq_off. auto. }
             pose proof ((fst (code_left w resv _ off _ rel eq_off' res_code' res_col))) as impl.
             simpl in impl. pose proof (impl (res_eq)) as [? [? pc3'eq]]. simpl.
             simpl in HeqH. rewrite eq_off in HeqH. simplify_some. rewrite pc3'eq. simpl.
             subst pc3_tag. simpl. rewrite eq_refl. simpl.
             Local Transparent mt.
             Local Transparent word_size.
             Local Transparent reg_field_size.
             Local Transparent imm_size.
             unfold updm. simpl in pc3'eq. unfold as_word.
             try rewrite eq_s3 in tag_pc3. simpl in *. try rewrite ST. simpl.
             repeat
             (repeat
                (match goal with
                 | H: getm ?r ?w = _  |- context[getm ?r ?w] => rewrite H; simpl
                 end);
              (*automatically transforms setm in if (_ == _) then _ else _*)
              repeat rewrite setmE; simpl;
              (*destruct the (_ == _) condition *)
              try
                (let cond := fresh "cond" in
                 match goal with
                 | |- context[@eq_op ?t ?a ?r] =>
                     remember (@eq_op t a r) as cond; destruct cond;
                     [convert_eq_op; simpl in *|]; simpl
                 end)).
             13: reflexivity. (* most general case, to be treated first *)
             all: unfold as_word in *; simpl in *.
             all: repeat (rewrite setmxx || (rewrite (setmC _ (_@InternalJump)); [|done]) ).
             all: (match (type of vt_eq) with
                   | ?ls = ?rs =>
                       revert vt_eq;
                       (match goal with
                          Heq: ls = Some (?a) |- _ =>
                            intro vt_eq; rewrite Heq in vt_eq; simplify_some; subst; simpl
                        end)
                   end).
             Local Opaque mt.
             Local Opaque word_size.
             Local Opaque reg_field_size.
             Local Opaque imm_size.
             all: trivial.
          -- eapply star_refl.
          -- done.
        * destruct vt_match. oapp_False. subst. simpl in *.
          rewrite eq_off in HeqH2. simplify_some.
          repeat match goal with
            H: getm regs3 ?r = Some ?v |- context[setm regs3 ?r ?v] =>
              idtac H; rewrite (setmI H)
          end.
          (match goal with
             |- (_ _ _ ?s _) /\ _ => assert(eq_tmp: regs s = reg); [|simpl in eq_tmp; rewrite eq_tmp; clear eq_tmp]
           end).

          { repeat match goal with
              | H: context[Word (fintype.Ordinal (div.ltn_pmod (ssrint.absz (intdiv.modz ?n (ssrint.Posz (2 ^ (reg_field_size mt))))) (exp2_gt0 (reg_field_size mt))))] |- _ =>
                  fold (@as_word (reg_field_size mt) n) in H
            end.

            assert (G: forall x y,
                       0 <= x < 20 ->
                       0 <= y < 20 ->
                       x <> y ->
                       as_word (k := reg_field_size mt) (ssrint.Posz x) == as_word (ssrint.Posz y) = false).
            { clear.
              Local Transparent reg_field_size mt.
              intros.
              apply /idP => C.
              move: C => /eqP C.
              eapply H1.
              (* Local Opaque reg_field_size mt. *)
              rewrite <- (as_wordK (k := 5) (n := x)).
              rewrite <- (as_wordK (k := 5) (n := y)).
              f_equal. f_equal. auto.
              eapply leq_trans with (n := 20); eauto.
              eapply leq_trans with (n := 20); eauto.
            }
            repeat (match goal with
                    | H: context [as_word ?x == as_word ?y] |- _ =>
                        rewrite G in H; [eauto | eauto | eauto | lia]
                    end
                   ).

            simpl. rewrite (setmI RA).
            simpl. rewrite eq_sym in Heqa23.
            unfold_match' Heqa23; convert_eq_op; repeat simplify_some; subst; simpl.
            { simpl in Heqa24.
              simpl in *. repeat simplify_some. subst. (* unfold as_word in *. *)
              rewrite RW in RA. simplify_some. subst. rewrite (setmI RW).
              repeat (match goal with
                      | H: context [as_word ?x == as_word ?y] |- _ =>
                          rewrite G in H; [eauto | eauto | eauto | lia]
                      end
                     ).
              repeat (match goal with
                      | H: Some (?va@?ta) = getm ?reg ?x,
                          H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                          rewrite <- H in H'; inv H'
                      end).
              repeat
                (match goal with
                 | H : Some (?v@_) = _  |- context[setm reg _ ?v@_] =>
                     rewrite (setmI (esym H)); eauto
                 end). }
            rewrite RW in Heqa23. simplify_some; subst. rewrite (setmI RW).
            destruct (as_word (ssrint.Posz 1) == r) eqn:Heq.
            { move: Heq => /eqP ?; subst r.
              rewrite eqxx in Heqa24; inv Heqa24.
              assert (w = va9) by congruence; subst.
              rewrite (setmI (Logic.eq_sym Heqa9)).
              repeat (match goal with
                      | H: context [as_word ?x == as_word ?y] |- _ =>
                          rewrite G in H; [eauto | eauto | eauto | lia]
                      end
                     ).
              repeat (match goal with
                      | H: Some (?va@?ta) = getm ?reg ?x,
                          H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                          rewrite <- H in H'; inv H'
                      end).
              repeat
                (match goal with
                 | H : Some (?v@_) = _  |- context[setm reg _ ?v@_] =>
                     rewrite (setmI (esym H)); eauto
                 end). }
            rewrite Heq in Heqa24.
            repeat (match goal with
                    | H: Some (?va@?ta) = getm ?reg ?x,
                        H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                        rewrite <- H in H'; inv H'
                    end).
            rewrite (setmI (esym Heqa9)).
            clear Heq.
            destruct (as_word (ssrint.Posz 0) == r) eqn:Heq.
            { move: Heq => /eqP ?; subst r.
              rewrite eqxx in Heqa25; inv Heqa25.
              assert (w = va) by congruence; subst.
              rewrite (setmI (Logic.eq_sym Heqa6)).
              repeat (match goal with
                      | H: context [as_word ?x == as_word ?y] |- _ =>
                          rewrite G in H; [eauto | eauto | eauto | lia]
                      end
                     ).
              repeat (match goal with
                      | H: Some (?va@?ta) = getm ?reg ?x,
                          H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                          rewrite <- H in H'; inv H'
                      end).
              repeat
                (match goal with
                 | H : Some (?v@_) = _  |- context[setm reg _ ?v@_] =>
                     rewrite (setmI (esym H)); eauto
                 end). }
            rewrite Heq in Heqa25.
            repeat (match goal with
                    | H: Some (?va@?ta) = getm ?reg ?x,
                        H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                        rewrite <- H in H'; inv H'
                    end).
            rewrite (setmI (esym Heqa6)).
            clear Heq.
            destruct (as_word (ssrint.Posz 2) == r) eqn:Heq.
            { move: Heq => /eqP ?; subst r.
              rewrite eqxx in Heqa26; inv Heqa26.
              assert (w = va0) by congruence; subst.
              rewrite (setmI (Logic.eq_sym Heqa11)).
              repeat (match goal with
                      | H: context [as_word ?x == as_word ?y] |- _ =>
                          rewrite G in H; [eauto | eauto | eauto | lia]
                      end
                     ).
              repeat (match goal with
                      | H: Some (?va@?ta) = getm ?reg ?x,
                          H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                          rewrite <- H in H'; inv H'
                      end).
              repeat
                (match goal with
                 | H : Some (?v@_) = _  |- context[setm reg _ ?v@_] =>
                     rewrite (setmI (esym H)); eauto
                 end). }
            rewrite Heq in Heqa26.
            repeat (match goal with
                    | H: Some (?va@?ta) = getm ?reg ?x,
                        H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                        rewrite <- H in H'; inv H'
                    end).
            rewrite (setmI (esym Heqa11)).
            clear Heq.
            destruct (as_word (ssrint.Posz 3) == r) eqn:Heq.
            { move: Heq => /eqP ?; subst r.
              rewrite eqxx in Heqa27; inv Heqa27.
              assert (w = va1) by congruence; subst.
              rewrite (setmI (Logic.eq_sym Heqa12)).
              repeat (match goal with
                      | H: context [as_word ?x == as_word ?y] |- _ =>
                          rewrite G in H; [eauto | eauto | eauto | lia]
                      end
                     ).
              repeat (match goal with
                      | H: Some (?va@?ta) = getm ?reg ?x,
                          H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                          rewrite <- H in H'; inv H'
                      end).
              repeat
                (match goal with
                 | H : Some (?v@_) = _  |- context[setm reg _ ?v@_] =>
                     rewrite (setmI (esym H)); eauto
                 end). }
            rewrite Heq in Heqa27.
            repeat (match goal with
                    | H: Some (?va@?ta) = getm ?reg ?x,
                        H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                        rewrite <- H in H'; inv H'
                    end).
            rewrite (setmI (esym Heqa12)).
            clear Heq.
            destruct (as_word (ssrint.Posz 5) == r) eqn:Heq.
            { move: Heq => /eqP ?; subst r.
              rewrite eqxx in Heqa28; inv Heqa28.
              assert (w = va2) by congruence; subst.
              rewrite (setmI (Logic.eq_sym Heqa13)).
              repeat (match goal with
                      | H: context [as_word ?x == as_word ?y] |- _ =>
                          rewrite G in H; [eauto | eauto | eauto | lia]
                      end
                     ).
              repeat (match goal with
                      | H: Some (?va@?ta) = getm ?reg ?x,
                          H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                          rewrite <- H in H'; inv H'
                      end).
              repeat
                (match goal with
                 | H : Some (?v@_) = _  |- context[setm reg _ ?v@_] =>
                     rewrite (setmI (esym H)); eauto
                 end). }
            rewrite Heq in Heqa28.
            repeat (match goal with
                    | H: Some (?va@?ta) = getm ?reg ?x,
                        H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                        rewrite <- H in H'; inv H'
                    end).
            rewrite (setmI (esym Heqa13)).
            clear Heq.
            destruct (as_word (ssrint.Posz 6) == r) eqn:Heq.
            { move: Heq => /eqP ?; subst r.
              rewrite eqxx in Heqa29; inv Heqa29.
              assert (w = va3) by congruence; subst.
              rewrite (setmI (Logic.eq_sym Heqa14)).
              repeat (match goal with
                      | H: context [as_word ?x == as_word ?y] |- _ =>
                          rewrite G in H; [eauto | eauto | eauto | lia]
                      end
                     ).
              repeat (match goal with
                      | H: Some (?va@?ta) = getm ?reg ?x,
                          H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                          rewrite <- H in H'; inv H'
                      end).
              repeat
                (match goal with
                 | H : Some (?v@_) = _  |- context[setm reg _ ?v@_] =>
                     rewrite (setmI (esym H)); eauto
                 end). }
            rewrite Heq in Heqa29.
            repeat (match goal with
                    | H: Some (?va@?ta) = getm ?reg ?x,
                        H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                        rewrite <- H in H'; inv H'
                    end).
            rewrite (setmI (esym Heqa14)).
            clear Heq.
            destruct (as_word (ssrint.Posz 7) == r) eqn:Heq.
            { move: Heq => /eqP ?; subst r.
              rewrite eqxx in Heqa30; inv Heqa30.
              assert (w = va4) by congruence; subst.
              rewrite (setmI (Logic.eq_sym Heqa15)).
              repeat (match goal with
                      | H: context [as_word ?x == as_word ?y] |- _ =>
                          rewrite G in H; [eauto | eauto | eauto | lia]
                      end
                     ).
              repeat (match goal with
                      | H: Some (?va@?ta) = getm ?reg ?x,
                          H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                          rewrite <- H in H'; inv H'
                      end).
              repeat
                (match goal with
                 | H : Some (?v@_) = _  |- context[setm reg _ ?v@_] =>
                     rewrite (setmI (esym H)); eauto
                 end). }
            rewrite Heq in Heqa30.
            repeat (match goal with
                    | H: Some (?va@?ta) = getm ?reg ?x,
                        H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                        rewrite <- H in H'; inv H'
                    end).
            rewrite (setmI (esym Heqa15)).
            clear Heq.
            destruct (as_word (ssrint.Posz 16) == r) eqn:Heq.
            { move: Heq => /eqP ?; subst r.
              rewrite eqxx in Heqa31; inv Heqa31.
              assert (w = va5) by congruence; subst.
              rewrite (setmI (Logic.eq_sym Heqa16)).
              repeat (match goal with
                      | H: context [as_word ?x == as_word ?y] |- _ =>
                          rewrite G in H; [eauto | eauto | eauto | lia]
                      end
                     ).
              repeat (match goal with
                      | H: Some (?va@?ta) = getm ?reg ?x,
                          H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                          rewrite <- H in H'; inv H'
                      end).
              repeat
                (match goal with
                 | H : Some (?v@_) = _  |- context[setm reg _ ?v@_] =>
                     rewrite (setmI (esym H)); eauto
                 end). }
            rewrite Heq in Heqa31.
            repeat (match goal with
                    | H: Some (?va@?ta) = getm ?reg ?x,
                        H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                        rewrite <- H in H'; inv H'
                    end).
            rewrite (setmI (esym Heqa16)).
            clear Heq.
            destruct (as_word (ssrint.Posz 17) == r) eqn:Heq.
            { move: Heq => /eqP ?; subst r.
              rewrite eqxx in Heqa32; inv Heqa32.
              assert (w = va6) by congruence; subst.
              rewrite (setmI (Logic.eq_sym Heqa17)).
              repeat (match goal with
                      | H: context [as_word ?x == as_word ?y] |- _ =>
                          rewrite G in H; [eauto | eauto | eauto | lia]
                      end
                     ).
              repeat (match goal with
                      | H: Some (?va@?ta) = getm ?reg ?x,
                          H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                          rewrite <- H in H'; inv H'
                      end).
              repeat
                (match goal with
                 | H : Some (?v@_) = _  |- context[setm reg _ ?v@_] =>
                     rewrite (setmI (esym H)); eauto
                 end). }
            rewrite Heq in Heqa32.
            repeat (match goal with
                    | H: Some (?va@?ta) = getm ?reg ?x,
                        H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                        rewrite <- H in H'; inv H'
                    end).
            rewrite (setmI (esym Heqa17)).
            clear Heq.
            destruct (as_word (ssrint.Posz 18) == r) eqn:Heq.
            { move: Heq => /eqP ?; subst r.
              rewrite eqxx in Heqa33; inv Heqa33.
              assert (w = va7) by congruence; subst.
              rewrite (setmI (Logic.eq_sym Heqa18)).
              repeat (match goal with
                      | H: context [as_word ?x == as_word ?y] |- _ =>
                          rewrite G in H; [eauto | eauto | eauto | lia]
                      end
                     ).
              repeat (match goal with
                      | H: Some (?va@?ta) = getm ?reg ?x,
                          H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                          rewrite <- H in H'; inv H'
                      end).
              repeat
                (match goal with
                 | H : Some (?v@_) = _  |- context[setm reg _ ?v@_] =>
                     rewrite (setmI (esym H)); eauto
                 end). }
            rewrite Heq in Heqa33.
            repeat (match goal with
                    | H: Some (?va@?ta) = getm ?reg ?x,
                        H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                        rewrite <- H in H'; inv H'
                    end).
            rewrite (setmI (esym Heqa18)).
            clear Heq.
            destruct (as_word (ssrint.Posz 19) == r) eqn:Heq.
            { move: Heq => /eqP ?; subst r.
              rewrite eqxx in Heqa20; inv Heqa20.
              assert (w = va8) by congruence; subst.
              rewrite (setmI (Logic.eq_sym Heqa19)).
              repeat (match goal with
                      | H: context [as_word ?x == as_word ?y] |- _ =>
                          rewrite G in H; [eauto | eauto | eauto | lia]
                      end
                     ). }
            rewrite Heq in Heqa20.
            repeat (match goal with
                    | H: Some (?va@?ta) = getm ?reg ?x,
                        H': Some (?va'@?ta') = getm ?reg ?x |- _ =>
                        rewrite <- H in H'; inv H'
                    end).
            rewrite (setmI (esym Heqa19)). reflexivity. }
          unfold color_of in tag_pc3, tag_pc1. simpl in tag_pc3, tag_pc1. inversion tag_pc1. subst n1.
          eapply preserves_equiv_right_pc_incr with (pc1' := (w)) (tpc1':=pc3_tag)
                                                   (pc3' := (addw w (as_word off))) (tpc3':=(pc3_tag)); subst pc3_tag.
          eauto. auto. auto.
          all: simpl; try trivial.
          all: unfold updm.
          all: try done.
          -- subst. simpl. eapply same_pc_normal.
             subst. simpl. eauto.
             unfold color_of. subst. simpl in *. eauto.
             subst. simpl. trivial.
      + unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        unfold_all; try unfold_match; unfold_all.
        all: try (clear -Heqa2; repeat unfold_match' Heqa2; done); simpl in *. (* eliminates many goals *)
        try (rewrite ST in PC_None; unfold color_of in PC_None; rewrite PC in PC_None; try (inversion PC_None; done || clear PC_None)).
        try (assert (tpc1 = tpc0) by (clear -Heqa2; unfold_match' Heqa2); subst tpc1).
        try (assert (ts0 = (ts (mvec None)) ) by
                 (unfold mvec in *; simpl; clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                  destruct Heqa2 as [_ _ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ts0).
        try (unfold mvec in *; assert (ti1 = ti0) by
                    (clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                     destruct Heqa2 as [_ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ti1).
        try (rewrite ST in end_s1 Heqa2; simpl in end_s1, Heqa2;
                  destruct (end_s1 pc0 _ PC) as [ instr_is_halt | [[i' ti'] [Heqi' code_i']]];
                  [destruct ti0; simpl in *; auto; try unfold_match' Heqa5; try done |
                    (match goal with
                     | op: _ = op_of_word _, inst: instr_of_args _ = _ |- _
                       => simpl in instr_is_halt;  rewrite <- op in instr_is_halt; simpl in instr_is_halt;
                         rewrite inst in instr_is_halt; done end) |
                    simpl in Heqi'; try (rewrite Heqi' in Heqa2; inversion Heqa2) ] ).
        unfold check_belong, belong, reg_clear_list in *.
        simpl in *; unfold_all.
        (match (type of Heqa2) with
           (_ = match ?m ?w with _ => _ end)
           => eapply (@modusponens (exists res, m w = Some res /\
                                            (LRC.color (taga res) \in domm ip ->
                                             is_code (taga res))));
             [|intros [res [res_eq res_code]]; rewrite res_eq in Heqa2]
         end).
        { (* 11: remember (mem0 pc') as next_pc_content; destruct next_pc_content. *)
        try (match goal with
                    |- exists _ _, _ => repeat (unfold_all || unfold_match || rewrite orb_false_r in Heqa4, Heqa16) end).
        convert_eq_op.
        unfold is_jump in *; try (unfold_match; subst t1).
        unfold hshead in *; simpl in *.
        try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3. (* trick to keep an equality on s1 and s3 *)
        try (pose proof (esym Heqa3) as PC; clear Heqa3).
        try (match goal with c: Component.id |- _ => rename c into color end).
        try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                  [exfalso; subst; simpl in *; rewrite (proj1 eq_none) in PC; done |]).
        try (assert (color_of s1 = c0) as eq by (unfold color_of; subst; simpl; clear -tag_pc1; destruct tpc0; simpl in *; congruence);
                  subst c0).
        try (destruct tpc0; unfold_all).
        try (unfold compatible in *; rewrite eq in m_compat).
        try rewrite m_compat in side_eq.
        remember pc' as w'. unfold pc' in Heqw'.
        match (type of Heqw') with
          _ = (_ _ (match ?c as _ with _ => _ end)) => remember c as cond
        end. destruct cond; subst w'; try (rewrite Heqi'; eauto).
        subst. unfold_match' Heqa5. unfold is_code in Heqa3. unfold_match' Heqa3. pose proof (bnz_s1 _ _ PC) as H.
        simpl in H. simpl in *. rewrite <- Heqa1 in H. simpl in *. rewrite H0 in H. destruct H as [? [? ?]]; auto. eauto. }
        (* 11: remember (mem0 pc') as next_pc_content; destruct next_pc_content. *)
        try (match goal with
                    |- exists _ _, _ => repeat (unfold_all || unfold_match || rewrite orb_false_r in Heqa4, Heqa16) end).
        convert_eq_op.
        unfold is_jump in *; try (unfold_match; subst t1).
        unfold hshead in *; simpl in *.
        try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3. (* trick to keep an equality on s1 and s3 *)
        try (pose proof (esym Heqa3) as PC; clear Heqa3).
        try (match goal with c: Component.id |- _ => rename c into color end).
        try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                  [exfalso; subst; simpl in *; rewrite (proj1 eq_none) in PC; done |]).
        try (assert (color_of s1 = c0) as eq by (unfold color_of; subst; simpl; clear -tag_pc1; destruct tpc0; simpl in *; congruence);
                  subst c0).
        try (destruct tpc0; unfold_all).
        try (unfold compatible in *; rewrite eq in m_compat).
        try rewrite m_compat in side_eq.
        inversion Heqa2.
        deduce_equality_r RW.
        destruct res as [resv rest]. simpl in H1.
        subst rest.
        destruct vt_match as [? match_t]. subst t1. destruct t; unfold is_other in *; try congruence. subst w.
        remember (@eq_op (mword_eqType _) v0 zerow) as cond.
        remember (pc3_val + (if cond then 1 else swcast n0))%w as pc3'.
        rewrite ST eq_s3 in pc_s1_s3, code_left. simpl in *.
        unfold side_of in *. unfold_match' side_eq. simpl in *.
        (*
        assert (pceq': pc3' = (pc' + (as_word off))%w).
        { subst pc3' pc3_val pc'. rewrite <- Heqcond. rewrite <- addwA. rewrite (addwC (as_word off) _).
          rewrite addwA. trivial. }
        *)
        deduce_equality_r PC. rewrite eq_s3 in bnz_s3.
        pose proof (bnz_s3 _ _ vt_eq0) as H. simpl in H. eapply modusponens; [apply H; auto|]. clear H.
        inversion vt_match; try subst i; revert H; decode_instr_eq; intro H. clear H.
        intros [v' [v'eq v'code]]. rewrite eq_s3 in end_s3.
        pose proof (end_s3 _ _ vt_eq0 t_code). revert H. decode_instr_eq. intro H. destruct H; try contradiction.
        destruct H as [v'' [v''eq v''code]].
        assert (next_pc_eq : mem3 pc3' = Some (if cond then v'' else v')).
        { subst pc3'. destruct cond; simpl; auto. }
        assert (pc'_eq: pc3' = (pc' + as_word off)%w).
        {subst. simpl in *. subst. unfold pc'. subst.
         rewrite <- addwA. rewrite (addwC (as_word _) (if _ then _ else _)).
         rewrite addwA. reflexivity. }
        assert (is_code0). { eapply res_code. subst s1. clear -Heqa3. simpl in *. unfold Component.id. rewrite <- Heqa3. trivial. }
        deduce_equality_r res_eq. rewrite next_pc_eq in vt_eq1. simplify_some.

        edestruct (code_left pc0) as [X _].
        { instantiate (1 := (color_of s1)).
          simpl in side_eq.  unfold side_of in side_eq. unfold is_relevant_comp.
          eauto. }
          (* move: side_eq; case: ((color_of s1) \in domm ip) => //=. } *)
        { instantiate (1 := off). eauto. }
        { instantiate (1 := {| vtag := vtag; color := color_of s1; entry := entry; is_code := true |}); eauto. }
        { eauto. }
        rewrite ST in X. simpl in X.
        specialize (X PC) as [vpc [match_dec mem_s3]].
        
        
        eexists. exists M. simpl.
        split.
        * eapply (plus_left _ [::]); try eapply step_bnz. eauto.
          -- eauto.
             (* rewrite eq_s3 in pc_s1_s3. *)
             (* simpl in pc_s1_s3. subst pc3_val. rewrite ST. simpl. rewrite eq_s3 in mem_s3. rewrite mem_s3. reflexivity. *)
          -- inversion match_dec.
             ++ subst vpc.
                decode_instr_eq.
             ++ assert (decode_instr v1 = Some (Bnz r n0)) by decode_instr_eq.
                congruence.
             ++ assert (decode_instr v1 = Some (Bnz r n0)) by decode_instr_eq.
                congruence.
          (* -- eapply (etrans _ (PC)). *)
          (* -- decode_instr_eq. *)
          -- rewrite eq_s3 in vt_eq. eauto.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_all.
             deduce_reg reg_match. rewrite <- Heqcond. rewrite <- Heqpc3'. rewrite eq_s3 next_pc_eq. simpl.
             rewrite eq_s3 in tag_pc3. simpl in tag_pc3. rewrite tag_pc3. rewrite t_color0. rewrite eq_refl. simpl.
             unfold check_belong, belong. rewrite H3. simpl. rewrite t_color0 eq_refl. simpl.
             unfold updm. subst. rewrite vt_eq. simpl.
             try rewrite eq_s3 in tag_pc3. simpl in *. reflexivity.
          -- destruct cond; eapply star_refl.
          -- done.
        * eapply preserves_equiv_right_reg_write with (r := r) (v := v0@Other) (v' := (v0@Other)).
          eapply preserves_equiv_right_pc_incr with (pc1' := pc') (tpc1' := taga (pc s1))
                                                   (pc3' := pc3') (tpc3' := taga (pc s3)); auto. eauto.
          all: simpl; try trivial.
          all: unfold updm.
          all: try done.
          -- subst. simpl. eapply same_pc_normal.
             simpl. eauto.
             unfold color_of. simpl. eauto.
             simpl. unfold pc'. trivial.
          -- subst. simpl in *. rewrite RW. simpl. trivial.
          -- rewrite vt_eq. simpl. trivial.
          -- subst. simpl in *. rewrite <- Heqa9 in RW. simplify_some. trivial.
          -- subst. simpl in *. trivial.
      + unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        unfold_all; try unfold_match; unfold_all.
        all: try (clear -Heqa2; repeat unfold_match' Heqa2; done); simpl in *. (* eliminates many goals *)
        try (rewrite ST in PC_None; unfold color_of in PC_None; rewrite PC in PC_None; try (inversion PC_None; done || clear PC_None)).
        try (assert (tpc1 = tpc0) by (clear -Heqa2; unfold_match' Heqa2); subst tpc1).
        try (assert (ts0 = (ts (mvec None)) ) by
                 (unfold mvec in *; simpl; clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                  destruct Heqa2 as [_ _ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ts0).
        try (unfold mvec in *; assert (ti1 = ti0) by
                    (clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                     destruct Heqa2 as [_ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ti1).
        try (rewrite ST in end_s1 Heqa2; simpl in end_s1, Heqa2;
                  destruct (end_s1 pc0 _ PC) as [ instr_is_halt | [[i' ti'] [Heqi' code_i']]];
                  [destruct ti0; simpl in *; auto; try unfold_match' Heqa5; try done |
                    (match goal with
                     | op: _ = op_of_word _, inst: instr_of_args _ = _ |- _
                       => simpl in instr_is_halt;  rewrite <- op in instr_is_halt; simpl in instr_is_halt;
                         rewrite inst in instr_is_halt; done end) |
                    simpl in Heqi'; try (rewrite Heqi' in Heqa2; inversion Heqa2) ] ).
        unfold check_belong, belong, reg_clear_list in *.
        simpl in *; unfold_all.
        (* 7-8: (match (type of Heqa2) with *)
        (*         (_ = match ?m ?w with _ => _ end) *)
        (*         => eapply (@modusponens (exists res, m w = Some res /\ *)
        (*                                          (LRC.color (taga res) \in domm ip -> *)
        (*                                           is_code (taga res)))); *)
        (*           [|intros [res [res_eq res_code]]; rewrite res_eq in Heqa2] *)
        (*       end). *)
        remember (mem0 pc') as next_pc_content; destruct next_pc_content.
        {
        try (match goal with
                    |- exists _ _, _ => repeat (unfold_all || unfold_match || rewrite orb_false_r in Heqa4, Heqa16) end).
        convert_eq_op.
        unfold is_jump in *; try (unfold_match; subst t1).
        unfold hshead in *; simpl in *.
        try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3. (* trick to keep an equality on s1 and s3 *)
        try (pose proof (esym Heqa3) as PC; clear Heqa3).
        try (match goal with c: Component.id |- _ => rename c into color end).
        try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                  [exfalso; subst; simpl in *; rewrite (proj1 eq_none) in PC; done |]).
        try (assert (color_of s1 = c0) as eq by (unfold color_of; subst; simpl; clear -tag_pc1; destruct tpc0; simpl in *; congruence);
                  subst c0).
        try (destruct tpc0; unfold_all).
        try (unfold compatible in *; rewrite eq in m_compat).
        try rewrite m_compat in side_eq.
        (* rewrite ST in tag_pc1. inversion tag_pc1. subst n1 i0. *)
        (*normal JAL*)
        (* we start by proving that pc' points to code *)
        unfold pc' in *. rewrite ST in bnz_s1, PC, alloc_mem_s1. pose proof (bnz_s1 _ _ PC) as JALcond.
        revert JALcond. decode_instr_eq. intro JALcond.
        destruct JALcond as [[x [next_pc_content' next_pc_code]] | imm_alloc_eq ]; auto.
        2: { exfalso. subst imm. inversion Heqa2. destruct a10 as [va ta]. simpl in *.
             assert ((@swcast _ (word_size mt) (@word_of_nat (imm_size mt) alloc_label)) = ((word_of_nat alloc_label))).
             { unfold swcast, word_of_nat. simpl.
               unfold alloc_label. rewrite div.modn_small. trivial. trivial. }
             rename Heqnext_pc_content into H'.
             rewrite H in H'. rewrite alloc_mem_s1 in H'. inversion H'. }
        rewrite <- Heqnext_pc_content in next_pc_content'. simplify_some. inversion Heqa2.
        (* unfolding of the modified registers and their value *)
        repeat
          (let va := fresh "va" in
           let ta := fresh "ta" in
           match goal with
             a: atom _ value_tag |- _ => destruct a as [va ta]
           end).
        simpl in *.
        repeat
          (match goal with
             H: Some _ = getm (setm _ _ _) _ |- _ =>
               repeat (rewrite setmE in H; unfold as_word in H; simpl in H)
           end).
        simpl in *.
        deduce_equality_r (esym Heqa9).
        deduce_equality_r (esym Heqa6).
        deduce_equality_r (esym Heqa11).
        deduce_equality_r (esym Heqa12).
        deduce_equality_r (esym Heqa13).
        deduce_equality_r (esym Heqa14).
        deduce_equality_r (esym Heqa15).
        deduce_equality_r (esym Heqa16).
        deduce_equality_r (esym Heqa17).
        deduce_equality_r (esym Heqa18).
        deduce_equality_r (esym Heqa19).
        deduce_equality_r OLD.
        subst. unfold side_of in *. unfold_match' side_eq. simpl in *.
        deduce_equality_r PC.
        rewrite Heqi' in RA. simplify_some. subst ti' vret. simpl in *.
        deduce_equality_r Heqi'.
        (* quick proof that v10 (s3) is a JAL offseted from i (s1) *)
        inversion vt_match11; try subst i; revert H; decode_instr_eq; intro H.
        { destruct (H imm). trivial. }
        { inv H. rewrite alloc_mem_s1 in Heqnext_pc_content. inversion Heqnext_pc_content. }
        inversion H. subst imm0. clear H. subst pc'.
        rewrite H3 in Heqnext_pc_content. simplify_some. simpl in *. rewrite <- H1 in H8. simpl in H8.
        assert (eq'_off: get_offset (side_of i0) i0 = Some off).
        { inv tag_pc1. unfold side_of. rewrite comp_in. simpl. trivial. }
        pose proof (H8 off (eq'_off)) as imm'_eq.
        assert (pc_eq_imm: (@swcast _ (word_size mt) imm') =
                             addw (swcast imm) (as_word off)).
        { eauto. }
        (* probably doable with slight lemma/hypothesis on off *)
        destruct d as [vx tx].
        destruct ((fst (code_left _ vx tx off _ comp_in eq_off next_pc_code (esym (congr1 LRC.color H1)))) (H3))
        as [d [dmatch deq]].
        simpl in *.
        repeat ((match goal with
             H : Some _ = getm reg (as_word (_ ?a)), H': Some _ = getm reg (_ (_ ((_ (_ ?a _) _ _)))) |- _ =>
               idtac a; unfold as_word in H; simpl in H; rewrite <- H in H'; simplify_some; subst
                 end)).

        (* edestruct (code_left pc0) as [X _]. *)
        (* { instantiate (1 := color). *)
        (*   simpl in side_eq.  unfold side_of in side_eq. unfold is_relevant_comp. *)
        (*   eauto. } *)
        (* { instantiate (1 := off). eauto. } *)
        (* { instantiate (1 := {| vtag := vtag; color := color; entry := entry; is_code := true |}); eauto. } *)
        (* { eauto. } *)
        (* simpl in X. *)
        (* (* rewrite ST in X. simpl in X. *) *)
        (* specialize (X PC) as [vpc [match_dec mem_s3]]. *)
        
        eexists. exists M.
        split.
        * eapply (plus_left _ [::]); try eapply step_jal. eauto.
          -- exact vt_eq11.
          -- exact vt_eq12.
          -- simpl. exact H2.
          -- exact vt_eq10.
          -- unfold reg_clear_list, reg_list. simpl. unfold as_word. subst. simpl.
             repeat
               (match goal with
                | H: _ ?w = _  |- context[_ ?w] => rewrite H; simpl
                end). trivial.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_all. rewrite vt_eq.
             simpl in *.
             rewrite pc_eq_imm deq. simpl. rewrite eq_refl. simpl.
             unfold check_belong, belong. rewrite eq_refl. simpl.
             unfold updm.
             simpl.
             repeat((repeat
                (match goal with
                 | H: ?regs3 ?w = _  |- context[?regs3 ?w] => rewrite H; simpl
                 end)); repeat rewrite setmE; simpl; try trivial).
          -- eapply star_refl.
          -- done.
        * simpl in *.
          repeat rewrite (setmC _ (_@InternalJump) _). all: try (simpl; done).
          repeat
            (match goal with
             | H: Some ?v = getm ?m ?r |- context[setm ?m ?r ?v] => rewrite (setmI (esym H))
             | H: getm ?m ?r = Some ?v |- context[setm ?m ?r ?v] => rewrite (setmI H)
             end).
          unfold color_of in tag_pc1. simpl in tag_pc1. inversion tag_pc1. subst n1.
          eapply preserves_equiv_right_reg_write with (r := ra) (v := (pc0 + 1)%w @InternalJump)
                                                     (v' := ((pc0 + as_word off + 1)%w @InternalJump)).
          eapply preserves_equiv_right_pc_incr with (pc1' := (swcast imm)) (tpc1':= Level n color)
                                                   (pc3' := (swcast imm + as_word off)%w) (tpc3':= Level n color).
          eauto. auto. auto.
          all: simpl; try trivial.
          all: unfold updm.
          -- subst. simpl. eapply same_pc_normal.
             simpl. eauto. simpl. eauto. simpl. trivial.
          -- pose proof (end_s3 _ _ vt_eq11). simpl in H. revert H. rewrite H2.
             intro H. destruct H; auto; try contradiction. subst.
             split; auto. simpl. rewrite eq_off. simpl.
             rewrite <- addwA. rewrite (addwC (as_word _) onew). rewrite addwA. trivial.
          -- rewrite Heqi'. eexists. split; eauto.
          -- pose proof (end_s3 _ _ vt_eq11). simpl in H. revert H. rewrite H2.
             intro H. destruct H; auto; try contradiction. subst.
             destruct H as [? [? ?]].
             eexists; split; [eauto|]. intro. trivial.
          (* -- pose proof (end_s3 _ _ vt_eq11). simpl in H. revert H. rewrite H2. *)
          (*    intro H. destruct H; auto; try contradiction. destruct H as [? [? ?]]. *)
          (*    eexists; split; [eauto|]. intro. trivial. *)
          -- rewrite OLD. simpl. trivial.
          -- rewrite vt_eq10. simpl. trivial.
          -- subst. rewrite setmI. auto. auto. rewrite <- Heqa22 in Heqi'. simplify_some.
             rewrite Heqa22. trivial. }
        try (match goal with
                    |- exists _ _, _ => repeat (unfold_all || unfold_match || rewrite orb_false_r in Heqa4, Heqa16) end).
        convert_eq_op.
        unfold is_jump in *; try (unfold_match; subst t1).
        unfold hshead in *; simpl in *.
        try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3. (* trick to keep an equality on s1 and s3 *)
        try (pose proof (esym Heqa3) as PC; clear Heqa3).
        try (match goal with c: Component.id |- _ => rename c into color end).
        try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                  [exfalso; subst; simpl in *; rewrite (proj1 eq_none) in PC; done |]).
        try (assert (color_of s1 = c0) as eq by (unfold color_of; subst; simpl; clear -tag_pc1; destruct tpc0; simpl in *; congruence);
                  subst c0).
        try (destruct tpc0; unfold_all).
        try (unfold compatible in *; rewrite eq in m_compat).
        try rewrite m_compat in side_eq.
        (* rewrite ST in tag_pc1. inversion tag_pc1. subst n1 i1. *)
        (*JAL to alloc*)
        unfold pc' in *. rewrite ST in bnz_s1. pose proof (bnz_s1 _ _ PC) as JALcond. simpl in JALcond.
        (match goal with
         | op: _ = op_of_word _, inst: instr_of_args _ = _ |- _
           => simpl; rewrite <- op in JALcond; simpl in JALcond; rewrite inst in JALcond
         end). destruct JALcond as [[? [tmp_eq next_pc_code]] | imm_alloc_eq ]; auto.
        { exfalso. rewrite <- Heqnext_pc_content in tmp_eq. inversion tmp_eq. }
        inversion Heqa2.
        (* unfolding of the modified registers and their value *)
        repeat
          (let va := fresh "va" in
           let ta := fresh "ta" in
           match goal with
             a: atom _ value_tag |- _ => destruct a as [va ta]
           end).
        simpl in *.
        repeat
          (match goal with
             H: Some _ = getm (setm _ _ _) _ |- _ =>
               repeat (rewrite setmE in H; unfold as_word in H; simpl in H)
           end).
        simpl in *.
        repeat ((match goal with
             H : Some _ = getm reg (as_word (_ ?a)), H': Some _ = getm reg (_ (_ ((_ (_ ?a _) _ _)))) |- _ =>
               idtac a; unfold as_word in H; simpl in H; rewrite <- H in H'; simplify_some; subst
          end)).
        deduce_equality_r (esym Heqa9).
        deduce_equality_r (esym Heqa6).
        deduce_equality_r (esym Heqa11).
        deduce_equality_r (esym Heqa12).
        deduce_equality_r (esym Heqa13).
        deduce_equality_r (esym Heqa14).
        deduce_equality_r (esym Heqa15).
        deduce_equality_r (esym Heqa16).
        deduce_equality_r (esym Heqa17).
        deduce_equality_r (esym Heqa18).
        deduce_equality_r (esym Heqa19).
        deduce_equality_r OLD.
        subst. unfold side_of in *. unfold_match' side_eq. simpl in *.
        deduce_equality_r PC.
        rewrite Heqi' in RA. simplify_some. subst ti' vret. simpl in *.
        deduce_equality_r Heqi'.
        (* quick proof that v10 (s3) is a JAL offseted from i (s1) *)
        inversion vt_match11; try subst i; revert H; decode_instr_eq; intro H.
        { destruct (H (word_of_nat alloc_label)). trivial. }
        2: { inv H. rewrite alloc_mem_s1 in H2. inversion H2. }
        clear H. subst pc'. inversion tag_pc1. subst n1 i1. simpl in *.
        repeat ((match goal with
             H : Some _ = getm reg (as_word (_ ?a)), H': Some _ = getm reg (_ (_ ((_ (_ ?a _) _ _)))) |- _ =>
               idtac a; unfold as_word in H; simpl in H; rewrite <- H in H'; simplify_some; subst
          end)).
        eexists. exists M.
        split.
        * eapply (plus_left _ [::]); try eapply step_jal. eauto.
          -- exact vt_eq11.
          -- exact vt_eq12.
          -- simpl. exact H1.
          -- exact vt_eq10.
          -- unfold reg_clear_list, reg_list. simpl. unfold as_word. subst. simpl.
             repeat
               (match goal with
                | H: ?r ?w = _  |- context[?r ?w] => rewrite H; simpl
                end). trivial.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_all. rewrite vt_eq.
             simpl in *. rewrite alloc_mem_s3. simpl. rewrite eq_refl. simpl.
             unfold check_belong, belong. rewrite eq_refl. simpl. rewrite vt_eq12. simpl.
             unfold updm. simpl.
             (repeat
                (*automatically rewrite regs3 registers*)
                ((repeat
                   (match goal with
                    | H: ?r ?w = _  |- context[isSome(?r ?w)] =>rewrite H; simpl
                    end);
                 (*automatically transforms setm in if (_ == _) then _ else _*)
                 repeat rewrite setmE; simpl
                ); try trivial)).
          -- eapply star_refl.
          -- done.
        * simpl in *.
          repeat rewrite (setmC _ (_@InternalJump) _). all: simpl. all: try tauto.
          repeat
            (match goal with
             | H: Some ?v = getm ?m ?r |- context[setm ?m ?r ?v] => rewrite (setmI (esym H))
             | H: getm ?m ?r = Some ?v |- context[setm ?m ?r ?v] => rewrite (setmI H)
             end).
          unfold color_of in tag_pc1. simpl in tag_pc1.
          eapply preserves_equiv_right_reg_write with (r := ra) (v := (pc0 + 1)%w @InternalJump) (
                                                       v' := ((pc0 + as_word off + 1)%w @InternalJump)).
          eapply preserves_equiv_right_pc_incr with (pc1' := (word_of_nat alloc_label)) (tpc1':= Level n color)
                                                   (pc3' := (word_of_nat alloc_label)%w) (tpc3':= Level n color).
          eauto. auto. auto.
          all: simpl; try trivial.
          all: unfold updm.
          -- subst. simpl. eapply same_pc_alloc; simpl. trivial. exact alloc_mem_s1.
          -- split;auto. simpl. rewrite eq_off. simpl. rewrite <- addwA. rewrite (addwC _ onew).
             rewrite addwA. trivial.
          -- rewrite Heqi'. eexists. split; eauto.
          -- pose proof (end_s3 _ _ vt_eq11). simpl in H. revert H. rewrite H1.
             intro H. destruct H; auto; try contradiction. destruct H as [? [? ?]].
             eexists; split; [eauto|]. intro. trivial.
          (* -- pose proof (end_s3 _ _ vt_eq11). simpl in H. revert H. rewrite H1. *)
          (*    intro H. destruct H; auto; try contradiction. destruct H as [? [? ?]]. *)
          (*    eexists; split; [eauto|]. intro. trivial. *)
          -- rewrite OLD. simpl. trivial.
          -- rewrite vt_eq10. simpl. trivial.
          -- rewrite setmI. auto. rewrite <- Heqa22 in Heqi'. simplify_some. rewrite Heqa22. trivial.
      + unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        unfold_all; try unfold_match; unfold_all.
        all: try (clear -Heqa2; repeat unfold_match' Heqa2; done); simpl in *. (* eliminates many goals *)
        try (rewrite ST in PC_None; unfold color_of in PC_None; rewrite PC in PC_None; try (inversion PC_None; done || clear PC_None)).
        try (assert (tpc1 = tpc0) by (clear -Heqa2; unfold_match' Heqa2); subst tpc1).
        try (assert (ts0 = (ts (mvec None)) ) by
                 (unfold mvec in *; simpl; clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                  destruct Heqa2 as [_ _ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ts0).
        try (unfold mvec in *; assert (ti1 = ti0) by
                    (clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                     destruct Heqa2 as [_ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ti1).
        try (rewrite ST in end_s1 Heqa2; simpl in end_s1, Heqa2;
                  destruct (end_s1 pc0 _ PC) as [ instr_is_halt | [[i' ti'] [Heqi' code_i']]];
                  [destruct ti0; simpl in *; auto; try unfold_match' Heqa5; try done |
                    (match goal with
                     | op: _ = op_of_word _, inst: instr_of_args _ = _ |- _
                       => simpl in instr_is_halt;  rewrite <- op in instr_is_halt; simpl in instr_is_halt;
                         rewrite inst in instr_is_halt; done end) |
                    simpl in Heqi'; try (rewrite Heqi' in Heqa2; inversion Heqa2) ] ).
        unfold check_belong, belong, reg_clear_list in *.
        simpl in *; unfold_all.
        (* 7-8: (match (type of Heqa2) with *)
        (*         (_ = match ?m ?w with _ => _ end) *)
        (*         => eapply (@modusponens (exists res, m w = Some res /\ *)
        (*                                          (LRC.color (taga res) \in domm ip -> *)
        (*                                           is_code (taga res)))); *)
        (*           [|intros [res [res_eq res_code]]; rewrite res_eq in Heqa2] *)
        (*       end). *)
        (* 11: remember (mem0 pc') as next_pc_content; destruct next_pc_content. *)
        try (match goal with
                    |- exists _ _, _ => repeat (unfold_all || unfold_match || rewrite orb_false_r in Heqa4, Heqa16) end).
        convert_eq_op.
        unfold is_jump in *; try (unfold_match; subst t1).
        unfold hshead in *; simpl in *.
        try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3. (* trick to keep an equality on s1 and s3 *)
        try (pose proof (esym Heqa3) as PC; clear Heqa3).
        try (match goal with c: Component.id |- _ => rename c into color end).
        try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                  [exfalso; subst; simpl in *; rewrite (proj1 eq_none) in PC; done |]).
        try (assert (color_of s1 = c0) as eq by (unfold color_of; subst; simpl; clear -tag_pc1; destruct tpc0; simpl in *; congruence);
                  subst c0).
        try (destruct tpc0; unfold_all).
        try (unfold compatible in *; rewrite eq in m_compat).
        try rewrite m_compat in side_eq.
        destruct pc_s1_s3 as [s1 s3 pc_s1_s3 eq_none|s1 s3 ? ? eq_some eq_off pc_s1_s3].
        2: { exfalso. rewrite ST in eq_some. unfold color_of in eq_some. simpl in eq_some. rewrite PC in eq_some. inversion eq_some. }
        unfold run_syscall in *.
        unfold evi in *. repeat unfold_bind. inversion CALL. subst s1'. simpl.
        simpl in Heqa0. unfold Instance.table, table in *. simpl in GETCALL.
        rewrite setmE in GETCALL. unfold_match' GETCALL. repeat simplify_some.
        assert (exists s3', alloc_fun (NC := NC) s3 = Some s3') as [s3' s3'_eq].
        { unfold Symbolic.sem in *.
          unfold alloc_fun in *.
          do 2 unfold_all || unfold_match.
          unfold updm in Heqa1.
          repeat (unfold_all || unfold_match).
          unfold isSome in Heqa10.
          remember (regs s1 (as_word (ssrint.Posz 16))) as retval. simpl in *. try (rewrite <- Heqretval in Heqa9).
          destruct retval as [retval|]; try (inversion Heqa9; done).
          destruct a0 as [va ?]. unfold is_jump in *. destruct taga; inversion Heqa4.
          destruct ((snd (reg_match _ _)) (esym Heqa3)) as [b [bmatch beq]].
          destruct ((snd (reg_match _ _)) (esym Heqa5)) as [b' [b'match b'eq]].
          destruct ((snd (reg_match _ _)) (esym Heqretval)) as [b'' [b''match b''eq]].
          rewrite beq. simpl. destruct b as [bv bt]. destruct bmatch. subst bt. simpl.
          rewrite b'eq. simpl. unfold is_other in *. destruct a1, b'. destruct b'match. subst taga0.
          destruct taga; inversion Heqa6. simpl.
          assert (Hcside : side_of color = Right).
          { clear -tag_pc1 side_eq.
            destruct s1 as [?? [] ?]; simpl in *; subst. congruence. }
          assert (Hcval' : (color \in domm ip) || (color \in domm ic)).
          { have Ecol : color = c0
              by clear -tag_pc1 side_eq Hcside; destruct s1 as [?? [] ?]; simpl in *; subst; congruence.
            by rewrite Ecol. }
          assert (domm_eq: (List.filter
                              (fun mw : word (word_size mt) =>
                                 andw mw (@mask mt NC) ==
                                   @component_memory_prefix mt NC (ssrint.Posz (1 + color))) (domm (mem s1)))
                           = (List.filter
                                (fun mw : word (word_size mt) =>
                                   andw mw (@mask mt NC) ==
                                     @component_memory_prefix mt NC (ssrint.Posz (1 + color))) (domm (mem s3)))).
          { eapply match_mem_pref_condition_filter_eq;
              [ exact: (is_relevant_comp_of_side Hcval' Hcside) | eauto | eauto | eauto ]. }
          subst s1 s3. simpl in *. destruct pc3_tag. simpl.
          inversion tag_pc1. inversion tag_pc3. subst n1 n0 i i0.
          simpl in *. rewrite <- domm_eq. subst vala0.
          rewrite <- Heqa10 => //=.
          rewrite <- Heqa8. simpl.

          rewrite <- Heqa1. simpl. unfold updm. rewrite b''eq. simpl. eauto. }

        exists s3'; exists M. simpl.
        split.
        * eapply (plus_left _ [::]); try eapply step_syscall; eauto.
          -- subst s1 s3; simpl in *.
             rewrite -pc_s1_s3. symmetry in Heqa2.
             move: Heqa2 => /idP /eqP ->. eapply alloc_mem_s3.
          -- subst. simpl in *. rewrite <- pc_s1_s3. unfold Instance.table, table. convert_eq_op. subst. simpl.
             rewrite setmE. rewrite eq_refl. done.
          -- unfold run_syscall, evi. deduce_reg reg_match. rewrite s3'_eq. simpl. done.
          -- eapply star_refl.
          -- done.
        * idtac "last line".
          eapply preserves_equiv_right_alloc_fun; eauto; done.
===== END ADMITTED OPCODE BODIES ===== *)
      (* ===== Load opcode (ported from the reference body above) ===== *)
      + unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        unfold_all; try unfold_match; unfold_all.
        all: try (clear -Heqa2; repeat unfold_match' Heqa2; done); simpl in *.
        try (rewrite ST in PC_None; unfold color_of in PC_None; rewrite PC in PC_None; try (inversion PC_None; done || clear PC_None)).
        try (assert (tpc1 = tpc0) by (clear -Heqa2; unfold_match' Heqa2); subst tpc1).
        try (assert (ts0 = (ts (mvec None)) ) by
                 (unfold mvec in *; simpl; clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                  destruct Heqa2 as [_ _ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ts0).
        try (unfold mvec in *; assert (ti1 = ti0) by
                    (clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                     destruct Heqa2 as [_ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ti1).
        try (rewrite ST in end_s1 Heqa2; simpl in end_s1, Heqa2;
                  destruct (end_s1 pc0 _ PC) as [ instr_is_halt | [[i' ti'] [Heqi' code_i']]];
                  [destruct ti0; simpl in *; auto; try unfold_match' Heqa5; try done |
                    (match goal with
                     | op: _ = op_of_word _, inst: instr_of_args _ = _ |- _
                       => simpl in instr_is_halt;  rewrite <- op in instr_is_halt; simpl in instr_is_halt;
                         rewrite inst in instr_is_halt; done end) |
                    simpl in Heqi'; try (rewrite Heqi' in Heqa2; inversion Heqa2) ] ).
        unfold check_belong, belong, reg_clear_list in *.
        simpl in *; unfold_all.
        try (match goal with
                    |- exists _ _, _ => repeat (unfold_all || unfold_match || rewrite orb_false_r in Heqa4, Heqa16) end).
        convert_eq_op.
        unfold is_jump in *; try (unfold_match; subst t1).
        unfold hshead in *; simpl in *.
        try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3.
        try (pose proof (esym Heqa3) as PC; clear Heqa3).
        try (match goal with c: Component.id |- _ => rename c into color end).
        try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                  [exfalso; subst; simpl in *; rewrite (proj1 eq_none) in PC; done |]).
        try (assert (color_of s1 = c0) as eq by (unfold color_of; subst; simpl; clear -tag_pc1; destruct tpc0; simpl in *; congruence);
                  subst c0).
        try (destruct tpc0; unfold_all).
        try (unfold compatible in *; rewrite eq in m_compat).
        try rewrite m_compat in side_eq.
        rewrite ST in tag_pc1. inversion tag_pc1. subst n1 i1.
        edestruct (code_left pc0) as [X _].
        { instantiate (1 := color). unfold is_relevant_comp.
          (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ]). }
        { instantiate (1 := off). rewrite ST in eq_off; eauto. }
        { instantiate (1 := {| vtag := vtag; color := color; entry := entry; is_code := true |}); eauto. }
        { eauto. }
        rewrite ST in X. simpl in X.
        specialize (X PC) as [vpc [match_dec mem_s3]].
        edestruct (code_left (pc0 + 1)%w) as [X' _].
        { instantiate (1 := color). unfold is_relevant_comp.
          (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ]). }
        { instantiate (1 := off). rewrite ST in eq_off; eauto. }
        { instantiate (1 := {| vtag := vtag0; color := color; entry := entry0; is_code := is_code0 |}); eauto. }
        { eauto. }
        rewrite ST in X'. simpl in X'.
        specialize (X' Heqi') as [vpc' [match_dec' mem_s3']].
        deduce_equality_r R1W.
        deduce_equality_r MEM1.
        deduce_equality_r OLD.
        destruct vt_match as [? match_t]. subst t. destruct t1; unfold is_other in *; try congruence. subst v0.
        exists (@State mt lrc_tags _
                  (setm mem3 w1 (v1 @ {| vtag := (if is_address vtag1 then Invalidated else Other);
                                         color := color; entry := entry1; is_code := false |}))
                  (setm (setm regs3 r1 (w1 @ Other)) r2 (v1 @ vtag1))
                  (((pc0 + as_word off + 1)%w) @ (Level n color))
                  tt); exists M. simpl.
        split.
        * eapply plus_one; try eapply step_load; eauto.
          -- rewrite eq_s3 in pc_s1_s3.
             simpl in pc_s1_s3. subst pc3_val. rewrite ST. simpl. rewrite eq_s3 in mem_s3. rewrite mem_s3. reflexivity.
          -- inversion match_dec.
             ++ subst vpc. decode_instr_eq.
             ++ assert (decode_instr i = Some (Load r1 r2)) by decode_instr_eq. congruence.
             ++ assert (decode_instr i = Some (Load r1 r2)) by decode_instr_eq. congruence.
          -- rewrite eq_s3 in vt_eq. eauto.
          -- rewrite eq_s3 in vt_eq0. eauto.
          -- rewrite eq_s3 in vt_eq1. eauto.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_bind. deduce_reg reg_match.
             rewrite eq_s3. simpl.
             rewrite eq_s3 in pc_s1_s3. simpl in pc_s1_s3. subst pc3_val. rewrite ST. simpl. rewrite eq_s3 in mem_s3'. simpl in mem_s3'.
             rewrite -addwA in mem_s3'. rewrite (addwC 1%w _) in mem_s3'. rewrite addwA in mem_s3'.
             rewrite !mem_s3'. simpl.
             rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3.
             destruct vt_match0. subst t0. simpl. rewrite eq_refl. simpl.
             unfold check_belong, belong. rewrite eq_refl. simpl.
             try rewrite eq_s3 in tag_pc3. simpl in *.
             try rewrite ST. simpl.
             subst s3.
             rewrite vt_eq. simpl. unfold updm. rewrite vt_eq. simpl. rewrite vt_eq0. simpl.
             repeat rewrite setmE. unfold stack_value in *. simpl in *.
             match goal with |- context [@eq_op ?T r2 r1] => destruct (@eq_op T r2 r1) eqn:Hcond end; simpl.
             all: first [ reflexivity
                        | (rewrite vt_eq1; simpl; reflexivity)
                        | (move/eqP: Hcond => r_eq; subst r2; simpl; reflexivity) ].
        * (* Load STEP + EQUIV both GENUINE (no admit).  The EQUIV is a 4-level
             reg_write(r2,_@vtag1) ∘ mem_write(w1,_@t2') ∘ reg_write(r1,w1@Other) ∘ pc_incr chain.
             The post-chain residuals are discharged by the `all: lazymatch` dispatcher below using
             TARGETED reductions (cbn [specific symbols] / rewrite /name), NOT `simpl`/`destruct;simpl`
             (which time out >110s on the big load state).  The outermost reg_write(r2)'s
             address_correctness premises for the loaded value (w2@vtag1 / v1@vtag1) are SHELVED by
             eapply, so they are surfaced by `Unshelve` after the dispatcher and closed by two explicit
             bullets (memory_address_correctness via s_mem_cor/s'_mem_cor — see below). *)
          (* --- Load helpers (analogs of Store's; cell tag ct={vtag1;color;entry1;false}) --- *)
          have Hco : color_of s1 = color by (rewrite ST /color_of /=; reflexivity).
          have Ht0 : t0 = {| vtag := vtag1; color := color; entry := entry1; is_code := false |}
            by (move: vt_match0; rewrite /data_match' => -[H _]; exact (esym H)).
          rewrite Ht0 in vt_eq0 vt_match0.
          have Hnpc : mem s1 (vala (pc s1) + 1)%w =
            Some (i' @ {| vtag := vtag0; color := color; entry := entry0; is_code := is_code0 |})
            by (rewrite ST /=; exact Heqi').
          have Hdm : data_match Right color M (w2@vtag1) (v1@vtag1)
            by (move: vt_match0; rewrite /data_match' => -[_ H]; exact H).
          have Hw2v1 : is_address vtag1 = false -> w2 = v1.
          { move=> Ha; move: Hdm Ha; clear; rewrite /data_match => -[_]; by case: vtag1 => //= ->. }
          have Hent1 : entry1 = None.
          { destruct entry1; [exfalso | reflexivity].
            rewrite ST in entry_code1.
            pose proof (entry_code1 _ _ _ MEM1 Logic.eq_refl) as Hcd. simpl in Hcd. inversion Hcd. }
          have MEM1s1 : mem s1 w1 = Some (w2 @ {| vtag := vtag1; color := color; entry := entry1; is_code := false |})
            by (rewrite ST /=; exact MEM1).
          have R1Ws1 : regs s1 r1 = Some (w1 @ Other) by (rewrite ST /=; exact R1W).
          have OLDs1 : regs s1 r2 = Some (old @ told) by (rewrite ST /=; exact OLD).
          have Hms3 : mem s3 = mem3 by (rewrite eq_s3; reflexivity).
          have Hrs3 : regs s3 = regs3 by (rewrite eq_s3; reflexivity).
          have Htpc1 : taga (pc s1) = Level n color by (rewrite ST /=; reflexivity).
          rewrite Hrs3 in vt_eq1.
          (* Resolve the step's reads a/a0 (Heqa13 : Some a = mem s1 w1, Heqa12 : Some a0 = regs s1 r1)
             into the loaded value w2 / address w1 — like region-A's line 840 — so the step's s1'
             carries w2/w1 directly (not `vala a`/`vala a0`) and state-eq #30 becomes reflexive. *)
          rewrite MEM1s1 in Heqa13. rewrite R1Ws1 in Heqa12. do 2 simplify_some.
          remember (if is_address vtag1 then Invalidated else Other) as new_t2.
          remember ({| vtag := new_t2; color := color; entry := entry1; is_code := false |}) as t2'.
          case: (internal s1); case: (internal s3).
          eapply preserves_equiv_right_reg_write with (r := r2) (v := w2@vtag1) (v' := v1@vtag1).
          eapply preserves_equiv_right_mem_write with (w := w1) (v := w2@t2') (v' := v1@t2').
          eapply preserves_equiv_right_reg_write with (r := r1) (v := w1@Other) (v' := w1@Other).
          eapply preserves_equiv_right_pc_incr with (pc1' := (vala (pc s1) + 1)%w) (tpc1' := taga (pc s1))
                                                    (pc3' := (pc0 + as_word off + 1)%w) (tpc3' := Level n color).
          1:{ split; [exact strong | split; [exact weak | exact common]]. }
          all: try (simpl; reflexivity).
          all: try exact I.
          all: subst t2'.
          all: subst new_t2.
          all: try (simpl; reflexivity).
          all: try exact I.
          (* resolve updm goals FIRST (they instantiate the ?r1'0/?r3'/?m1' evars; rewrite refuses
             on evar-containing goals, so the other cases need them resolved). *)
          all: try (cbn [mem regs]; unfold updm; rewrite ?MEM1s1 ?vt_eq0 ?R1Ws1 ?vt_eq /=; rewrite ?Hms3 ?Hrs3; reflexivity).
          all: try (cbn [regs]; unfold updm;
                    rewrite ?(setmE (regs s1) r1 (w1@Other) r2) ?(setmE regs3 r1 (w1@Other) r2) ?OLDs1 ?vt_eq1;
                    case: (r2 == r1) => /=; reflexivity).
          (* data_match #23 (loaded value w2@vtag1): a separate pass — Hdm matches only this goal
             (the w1@Other reg-write data_match fails the exact and is skipped). *)
          all: try (lazymatch goal with
                    | |- data_match Right ?cc ?m ?a ?b =>
                        have Hcst : cc = color by (rewrite ST /color_of /=; reflexivity);
                        exact (eq_ind_r (fun c => data_match Right c m a b) Hdm Hcst)
                    end).
          all: try (match goal with |- pc_code_color _ => pcc_close2 (PCCM.step_me_mp step_1) ST end).
          all: lazymatch goal with
               | |- data_match' _ _ _ _ =>
                   rewrite /data_match'; split; first reflexivity;
                   rewrite /data_match; split; first reflexivity;
                   cbn [LRC.vtag]; destruct (is_address vtag1) eqn:Ha; [ exact I | by apply Hw2v1 ]
               | |- LRC.entry _ = None => cbn [taga LRC.entry]; exact Hent1
               | |- is_relevant_comp _ _ =>
                   cbn [taga LRC.color]; unfold is_relevant_comp; (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ])
               | |- not _ => cbn [taga is_code]; done
               | |- is_true (is_code (taga _)) =>
                   first [ (cbn [taga is_code]; assumption)
                         | (cbn [taga is_code]; done) ]
               | |- _ = taga (pc _) => first [by rewrite ST | by rewrite tag_pc3]
               | |- same_pc _ _ _ =>
                   eapply same_pc_normal;
                   [ (cbn [mem pc vala]; split; [exact Hnpc | exact code_i'])
                   | (rewrite ST /color_of /= in eq_off; rewrite ST /get_offset /color_of /=; exact eq_off)
                   | (cbn [pc vala]; rewrite ST /=; word_ac) ]
               | |- LRC.color _ = color_of _ =>
                   cbn [taga LRC.color]; rewrite ST /color_of /=; reflexivity
               | |- forall _, _ \/ _ -> _ =>
                   cbn [mem]; move=> vv [Hd|Hd];
                   [ move: Hd; rewrite MEM1s1 | move: Hd; rewrite vt_eq0 ];
                   move=> [= <-]; cbn [taga LRC.color]; reflexivity
               | |- (exists _, _ /\ _) =>
                   cbn [mem];
                   first [ (exists (w2 @ {| vtag := vtag1; color := color; entry := entry1; is_code := false |});
                            split; [exact MEM1s1 | cbn [taga is_code]; done])
                         | (exists (v1 @ {| vtag := vtag1; color := color; entry := entry1; is_code := false |});
                            split; [exact vt_eq0 | cbn [taga is_code]; done]) ]
               | |- address_correctness _ _ _ _ =>
                   first
                     [ (cbn [mem taga LRC.vtag]; destruct (is_address vtag1); exact I)
                     | (cbn [mem taga LRC.vtag];
                        have Hrel : is_relevant_comp Right color by (rewrite /is_relevant_comp; (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ]));
                        first
                          [ (* WS_S1: value w2, cell MEM1s1, mem s1 *)
                            (move: (s_mem_cor (w2 @ {| vtag := vtag1; color := color; entry := entry1; is_code := false |}) w1 Hrel MEM1s1);
                             move: MEM1s1 Hrel; clear; case: vtag1 => [ n0 | | | ] MEM1s1 Hrel; rewrite /address_correctness /=;
                             [ (move=> [v' [Hmw' Hcode]]; rewrite (setmE (mem s1) w1 _ w2); case: ifP => [/eqP Heq | _];
                                 [ (exfalso; move: Hmw'; rewrite Heq MEM1s1 => -[<-]; move: (Hcode Hrel); rewrite /= => //)
                                 | (exists v'; split; [exact Hmw' | exact Hcode]) ])
                             | exact I
                             | (move=> [v' [Hmw' Hcode]]; rewrite (setmE (mem s1) w1 _ w2); case: ifP => [/eqP Heq | _];
                                 [ (exfalso; move: Hmw'; rewrite Heq MEM1s1 => -[<-]; move: (Hcode Hrel); rewrite /= => //)
                                 | (exists v'; split; [exact Hmw' | exact Hcode]) ])
                             | exact I ])
                          | (* WS_S3: value v1, cell vt_eq0, mem3 (bridge Hms3) *)
                            (move: (s'_mem_cor (v1 @ {| vtag := vtag1; color := color; entry := entry1; is_code := false |}) w1 Hrel vt_eq0);
                             rewrite Hms3;
                             move: vt_eq0 Hrel Hms3; clear; case: vtag1 => [ n0 | | | ] vt_eq0 Hrel Hms3; rewrite /address_correctness /=;
                             [ (move=> [v' [Hmw' Hcode]]; rewrite (setmE mem3 w1 _ v1); case: ifP => [/eqP Heq | _];
                                 [ (exfalso; move: Hmw'; rewrite Heq -Hms3 vt_eq0 => -[<-]; move: (Hcode Hrel); rewrite /= => //)
                                 | (exists v'; split; [exact Hmw' | exact Hcode]) ])
                             | exact I
                             | (move=> [v' [Hmw' Hcode]]; rewrite (setmE mem3 w1 _ v1); case: ifP => [/eqP Heq | _];
                                 [ (exfalso; move: Hmw'; rewrite Heq -Hms3 vt_eq0 => -[<-]; move: (Hcode Hrel); rewrite /= => //)
                                 | (exists v'; split; [exact Hmw' | exact Hcode]) ])
                             | exact I ]) ]) ]
               | |- capability_correctness' ?ws _ _ _ _ =>
                   first
                     [ (cbn [taga LRC.vtag]; destruct (is_address vtag1); exact I)
                     | (cbn [taga LRC.vtag];
                        move: capa_cor1 capa_cor3 MEM1s1 vt_eq0 Hms3 Hrs3; clear;
                        case: vtag1 => [ n0 | | | ]; move=> capa_cor1 capa_cor3 MEM1s1 vt_eq0 Hms3 Hrs3;
                        [ rewrite /capability_correctness' /=;
                          lazymatch ws with
                          | WS_S2 =>
                            (move: (capa_cor1 w2 n0 (inr w1) (ex_intro _ {| vtag := Ret n0; color := color; entry := entry1; is_code := false |} (conj MEM1s1 Logic.eq_refl))) => [iss uu];
                             split;
                             [ (move=> vv ww tt' tteq meq; move: meq; rewrite (setmE (mem s1) w1 _ ww);
                               case: ifP => [_ | Hne];
                                 [ (move=> H; move: (congr1 (fun o => if o is Some a then vtag (taga a) else Other) H);
                                    rewrite tteq /= => //)
                                 | (move=> meq; move: (capa_cor1 vv n0 (inr ww) (ex_intro _ tt' (conj meq tteq))) => [_ uu2];
                                    move: (uu2 (inr w1) w2 (ex_intro _ {| vtag := Ret n0; color := color; entry := entry1; is_code := false |} (conj MEM1s1 Logic.eq_refl))) => Hww;
                                    move: Hne; rewrite Hww eqxx // ) ])
                             | (split; last exact iss;
                               move=> vv rr rq; move: rq; rewrite (setmE (regs s1) r1 (w1@Other) rr);
                               case: ifP => [_ | _];
                                 [ (by move=> H; discriminate (congr1 (fun o => if o is Some a then taga a else Ret 0) H))
                                 | (move=> rq; exact (uu (inl rr) vv rq)) ]) ])
                          | WS_S3 =>
                            (rewrite -Hms3 -Hrs3;
                             move: (capa_cor3 v1 n0 (inr w1) (ex_intro _ {| vtag := Ret n0; color := color; entry := entry1; is_code := false |} (conj vt_eq0 Logic.eq_refl))) => [iss uu];
                             split;
                             [ move=> vv ww tt' tteq meq; move: meq; rewrite (setmE (mem s3) w1 _ ww);
                               case: ifP => [_ | Hne];
                                 [ (move=> H; move: (congr1 (fun o => if o is Some a then vtag (taga a) else Other) H);
                                    rewrite tteq /= => //)
                                 | (move=> meq; move: (capa_cor3 vv n0 (inr ww) (ex_intro _ tt' (conj meq tteq))) => [_ uu2];
                                    move: (uu2 (inr w1) v1 (ex_intro _ {| vtag := Ret n0; color := color; entry := entry1; is_code := false |} (conj vt_eq0 Logic.eq_refl))) => Hww;
                                    move: Hne; rewrite Hww eqxx // ) ]
                             | split; last exact iss;
                               move=> vv rr rq; move: rq; rewrite (setmE (regs s3) r1 (w1@Other) rr);
                               case: ifP => [_ | _];
                                 [ (by move=> H; discriminate (congr1 (fun o => if o is Some a then taga a else Ret 0) H))
                                 | (move=> rq; exact (uu (inl rr) vv rq)) ] ])
                          | _ => idtac
                          end
                        | exact I | exact I | exact I ]) ]
               | |- data_match Right ?cc _ ?a ?b =>
                   first [ (rewrite /data_match; split; reflexivity)
                         | (let Hc := fresh "Hcc" in
                            assert (Hc : cc = color) by (rewrite ST /color_of /=; reflexivity);
                            rewrite Hc; exact Hdm) ]
               | |- ?g => first [ (cbn [mem vala pc]; exact Hnpc)
                                | (cbn [mem regs pc internal vala]; rewrite Htpc1; reflexivity) ]
               end.
          (* Second pass: the outermost reg_write(r2) spawns its address_correctness for the loaded
             value (w2@vtag1 / v1@vtag1) AFTER the dispatcher enumerated goals, so re-run the same
             memory-address closer (WS_S1: value w2, cell MEM1s1; WS_S3: value v1, cell vt_eq0). *)
          (* The outermost reg_write(r2) address_correctness premise for the loaded value
             (w2@vtag1 / v1@vtag1) is SHELVED by the eapply chain, so the `all:` dispatcher never
             enumerates it.  `Unshelve` surfaces it; the memory-address closer then discharges each
             (WS_S1: value w2 via s_mem_cor+MEM1s1, mem s1; WS_S3: value v1 via s'_mem_cor+vt_eq0,
             mem3): for Other/Invalidated the obligation is trivially True; for Ret/InternalJump it is
             `exists v, (setm … w1 …) w2 = Some v ∧ (is_relevant→is_code)`, closed at the loaded
             address w2≠w1 by the cell's own address-correctness (s_mem_cor at w2), and at w2=w1 by
             the re-tagged cell being non-code (is_relevant⇒is_code is then contradictory). *)
          Unshelve.
          1:{ move: (s_mem_cor (w2 @ {| vtag := vtag1; color := color; entry := entry1; is_code := false |}) w1 Hrel MEM1s1);
              move: MEM1s1 Hrel; clear; case: vtag1 => [ n0 | | | ] MEM1s1 Hrel; rewrite /address_correctness /=;
              [ (move=> [v' [Hmw' Hcode]]; rewrite (setmE (mem s1) w1 _ w2); case: ifP => [/eqP Heq | _];
                  [ (exfalso; move: Hmw'; rewrite Heq MEM1s1 => -[= Ev]; subst v'; move: (Hcode Hrel); by rewrite /=)
                  | (exists v'; split; [exact Hmw' | exact Hcode]) ])
              | by move=> _
              | (move=> [v' [Hmw' Hcode]]; rewrite (setmE (mem s1) w1 _ w2); case: ifP => [/eqP Heq | _];
                  [ (exfalso; move: Hmw'; rewrite Heq MEM1s1 => -[= Ev]; subst v'; move: (Hcode Hrel); by rewrite /=)
                  | (exists v'; split; [exact Hmw' | exact Hcode]) ])
              | by move=> _ ]. }
          1:{ move: (s'_mem_cor (v1 @ {| vtag := vtag1; color := color; entry := entry1; is_code := false |}) w1 Hrel vt_eq0); rewrite Hms3;
              move: vt_eq0 Hrel Hms3; clear; case: vtag1 => [ n0 | | | ] vt_eq0 Hrel Hms3; rewrite /address_correctness /=;
              [ (move=> [v' [Hmw' Hcode]]; rewrite (setmE mem3 w1 _ v1); case: ifP => [/eqP Heq | _];
                  [ (exfalso; move: Hmw'; rewrite Heq -Hms3 vt_eq0 => -[= Ev]; subst v'; move: (Hcode Hrel); by rewrite /=)
                  | (exists v'; split; [exact Hmw' | exact Hcode]) ])
              | by move=> _
              | (move=> [v' [Hmw' Hcode]]; rewrite (setmE mem3 w1 _ v1); case: ifP => [/eqP Heq | _];
                  [ (exfalso; move: Hmw'; rewrite Heq -Hms3 vt_eq0 => -[= Ev]; subst v'; move: (Hcode Hrel); by rewrite /=)
                  | (exists v'; split; [exact Hmw' | exact Hcode]) ])
              | by move=> _ ]. }
          (* Load EQUIV fully closed (no admit).  The loaded value came from MEMORY (MEM1s1: mem s1 w1=
             Some w2@_, vt_eq0: mem s3 w1=Some v1@_), so capability_correctness' for vtag1=Ret uses the
             capa_cor1/capa_cor3 *inr-w* (memory-location w1) uniqueness branch (NOT the inl-r2 register
             branch), and address_correctness for the loaded value uses memory_address_correctness
             (s_mem_cor/s'_mem_cor) — discharged in the two `Unshelve` bullets above. *)
      (* ===== remaining opcodes: Store, Jump, Bnz, Jal, Jal2 (bodies in the reference comment above) ===== *)
      + (* Store *)
        unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        repeat (apply obind_inv in NEXT as [? [?HR NEXT]]).
        destruct (mem s1 (vala (pc s1) + 1)%w) as [ni|] eqn:NPC;
          [| (* Store-as-last-instruction (no next cell). belong c None = true (LRC.v:103, "accepting
                ni=None ⇒ monitor service/stopping") makes this a VALID step, NOT killed by NEXT=Some;
                instead the recomposition invariant end_condition (Definitions.v:543: a non-Halt code
                cell has a following code cell) contradicts mem(pc0+1)=None. We DON'T resolve s1' (the
                None-branch peel diverges — x0 is a state not the (ov,ev) pair); we only need HE5 (peel
                the transfer HR0) + ST, then exfalso. *)
             exfalso;
             clear NEXT;
             cbn in HR0;
             repeat (match goal with
                     | H : obind _ _ = Some _ |- _ => apply obind_inv in H as [? [? H]]
                     | H : (let (_, _) := ?x in _) = Some _ |- _ => let E := fresh "HE" in destruct x eqn:E
                     | H : (if ?b then _ else _) = Some _ |- _ => let E := fresh "HE" in destruct b eqn:E
                     end);
             try discriminate;
             assert (Hic0 : is_code ti0) by (match goal with H : is_code ti0 = true |- _ => exact H end);
             rewrite ST /= in end_s1 NPC;
             case: (end_s1 pc0 (i@ti0) PC Hic0) => [Hh | [v' [Hv' _]]];
             first [ (rewrite INST in Hh; exact Hh) | (rewrite NPC in Hv'; discriminate Hv') ] ].
        simpl in NEXT.
        repeat (apply obind_inv in NEXT as [? [?HR2 NEXT]]).
        destruct x0 as [ov ev]. simpl in NEXT.
        repeat (apply obind_inv in NEXT as [? [?HR3 NEXT]]).
        move: NEXT => [= Hs1' Hev]. subst ev. subst s1'.
        try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3.
        try (match goal with c: Component.id |- _ => rename c into color end).
        try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                  [exfalso; subst; simpl in *; rewrite (proj1 eq_none) in PC; done |]).
        cbn in HR0.
        repeat (match goal with
                | H : obind _ _ = Some _ |- _ => apply obind_inv in H as [? [? H]]
                | H : (let (_, _) := ?x in _) = Some _ |- _ => let E := fresh "HE" in destruct x eqn:E
                | H : (if ?b then _ else _) = Some _ |- _ => let E := fresh "HE" in destruct b eqn:E
                end).
        all: try discriminate.
        (* resolve x0 (do_updates result) → s1' concrete *)
        injection HR3 as HR3; subst x0.
        injection H1 as H1; subst x3.
        injection H0 as H0; subst x2.
        injection H as H; subst x1.
        move: (updm_set H6) => Hx8; subst x8.
        move: (updm_set H4) => Hx6; subst x6.
        move: (updm_set H2) => Hx4; subst x4.
        cbn [mem regs pc internal] in *.
        (* STORE prologue PEELED + s1' RESOLVED & GREEN (2026-05-31).
           s1' = {| mem := setm (mem s1) w1 (w2@s);
                    regs := setm (setm (regs s1) r1 (w1@t1)) r2 (w2@(is_address t2 ? Invalidated : Other));
                    pc := (vala (pc s1) + 1)%w@tpc0; internal := internal s1 |}
           with s = (switch_val told t2).1 (the new stored-cell tag), vala x7=w1, vala x5=w2,
           hshead (tr ov)=t1, trpc ov=tpc0, tr ov = [t1; (is_address t2?Inv:Other); s]
           (ov resolvable via subst through HR0/HE/H7/HE0/H10 if needed). Transfer facts in ctx:
           HE2 (is_code told=false), H13/H14 (check_belong ni at pc0+1 / told both pass),
           H12 (is_other t1), HE4 (color ti0 = i0), HE5 (is_code ti0).
           REMAINING (mechanical, mirrors Bnz): step_store on s3 (Symbolic.v:351; code_left fetch
           + match_dec + R1W/R2W via reg_match + OLD via mem_match + NEXT forward-compute);
           equiv = preserves_equiv_right_mem_write(w1,w2@s) (PreservationLemmas.v:127, ~20 stored-cell
           premises = the new work) ∘ reg_write(r2) ∘ reg_write(r1) ∘ pc_incr, dispatched like Bnz. *)
        assert (Htpc0 : tpc0 = Level n color) by (move: tag_pc1; rewrite ST /=; done).
        assert (Hi0 : i0 = color) by (move: HE1; rewrite Htpc0 /= => [= _ <-]; reflexivity).
        assert (Hcti0 : LRC.color ti0 = color).
        { have E : is_true (eqn (LRC.color ti0) i0) by (move: HE4; case: (eqn (LRC.color ti0) i0) => //).
          move/eqnP: E => E. by rewrite E Hi0. }
        assert (belong_eq : forall (cc:Component.id) m, belong cc (Some m) = (cc == LRC.color m))
          by (move=> cc [vt ct et ict]; reflexivity).
        assert (Hcoltold : LRC.color told = color).
        { have Hb : LRC.color ti0 == LRC.color told.
          { rewrite -belong_eq. move: H14; rewrite /check_belong; by case: ifP. }
          move/eqP: Hb => Hb. rewrite -Hb; exact Hcti0. }
        assert (Hco : color_of s1 = color) by (rewrite ST /color_of /= Htpc0; reflexivity).
        assert (R1Ws1 : regs s1 r1 = Some (w1@t1)) by (rewrite ST; exact R1W).
        pose proof (proj2 (reg_match r1 _) R1Ws1) as [d1' [VTM1 VT31]].
        assert (R2Ws1 : regs s1 r2 = Some (w2@t2)) by (rewrite ST; exact R2W).
        pose proof (proj2 (reg_match r2 _) R2Ws1) as [d2' [VTM2 VT32]].
        assert (OLDs1 : mem s1 w1 = Some (old@told)) by (rewrite ST; exact OLD).
        assert (Hnc : ~ is_code told) by (rewrite HE2; done).
        assert (Hrel : is_relevant_comp Right (LRC.color told)).
        { rewrite Hcoltold /is_relevant_comp.
          (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ]). }
        pose proof (proj2 (mem_match w1 (old@told) Hnc Hrel) OLDs1) as [dm' [DMM OLD3]].
        destruct d1' as [vd1 td1]; destruct d2' as [vd2 td2]; destruct dm' as [vdm tdm].
        destruct t1; try (move: H12 => /=; discriminate).
        move: VTM1; rewrite /data_match => -[Htd1 Hvd1]; subst td1; subst vd1.
        rewrite Hco in eq_off side_eq.
        edestruct (code_left pc0) as [X _].
        { instantiate (1 := color). unfold is_relevant_comp.
          (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ]). }
        { instantiate (1 := off). exact eq_off. }
        { instantiate (1 := ti0). move: HE5; case: (is_code ti0) => //. }
        { exact Hcti0. }
        rewrite ST in X. simpl in X. specialize (X PC) as [vpc [match_dec mem_s3]].
        assert (Hpc3v : pc3_val = (pc0 + as_word off)%w) by (move: pc_s1_s3; rewrite eq_s3 ST /=; done).
        eexists. exists M. simpl. split.
        * eapply plus_one. eapply step_store.
          -- rewrite eq_s3; reflexivity.
          -- rewrite Hpc3v; rewrite eq_s3 in mem_s3; simpl in mem_s3; exact mem_s3.
          -- assert (Hvv : vpc = i) by (inversion match_dec; congruence). rewrite Hvv; exact INST.
          -- rewrite eq_s3 in VT31; simpl in VT31; exact VT31.
          -- rewrite eq_s3 in VT32; simpl in VT32; exact VT32.
          -- rewrite eq_s3 in OLD3; simpl in OLD3; exact OLD3.
          -- (* NEXT: next_state_updates s3 (IVec STORE pc3_tag ti0 [hseq Other; td2; tdm])
                [RegRead r1; RegRead r2; MemWrite w1 vd2] = Some (?s3', None). Forward-compute like
                Bnz's NEXT: read mem3 (pc3_val+1) for the next-instr tni (code_left at pc'+1), evi s3
                via reg_match, then the STORE transfer (is_code ti0 via HE5; color check via Hcti0 +
                tag_pc3; is_other Other; check_belong next-instr; check_belong (Some tdm); is_code tdm
                = false [from DMM : data_match' (old@told)(vdm@tdm) + HE2 is_code told=false]; switch_val
                tdm td2), then do_updates over the 3 updates. Result s3' = State (setm mem3 w1 (vd2@s3))
                (setm (setm regs3 r1 (w1@Other)) r2 (vd2@(is_address td2?Inv:Other))) ((pc3_val+1)@pc3_tag)
                internal3, s3 = (switch_val tdm td2).1. *)
             move: DMM; rewrite /data_match' => -[Htoldtdm _]; subst tdm.
             destruct ni as [vni0 tni0].
             assert (Hic : is_code tni0).
             { have PCs1 : mem s1 pc0 = Some (i@ti0) by (rewrite ST; exact PC).
               move: (end_s1 pc0 (i@ti0) PCs1 HE5).
               have Hvi : vala (i@ti0) = i by []. rewrite Hvi INST.
               move => [Hh|[v' [Hv' Hcv']]]; first (exfalso; exact Hh).
               rewrite ST /= in NPC Hv'.
               rewrite NPC in Hv'. case: Hv' => Heq. rewrite -Heq in Hcv'; exact Hcv'. }
             assert (Hcolni : LRC.color tni0 = color).
             { have Hb : LRC.color ti0 == LRC.color tni0.
               { rewrite -belong_eq. move: H13; rewrite /check_belong; by case: ifP. }
               move/eqP: Hb => Hb. by rewrite -Hb Hcti0. }
             edestruct (code_left (vala (pc s1) + 1)%w) as [Y _].
             { instantiate (1 := color). unfold is_relevant_comp.
          (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ]). }
             { instantiate (1 := off). exact eq_off. }
             { instantiate (1 := tni0). exact Hic. }
             { exact Hcolni. }
             specialize (Y NPC) as [vni [match_ni mem_tgt]].
             assert (Hnextpc : (vala (pc s3) + 1)%w = ((vala (pc s1) + 1)%w + as_word off)%w) by (rewrite pc_s1_s3; word_ac).
             unfold next_state_updates, next_state_updates_and_pc. rewrite Hnextpc mem_tgt.
             unfold next_state, evi.
             assert (Hrc1 : exists a, regs s1 rcom = Some a) by (move: HR; rewrite /evi; case: (regs s1 rcom) => [a _|//]; by exists a).
             destruct Hrc1 as [arcom1 Hrc1].
             move: (proj2 (reg_match rcom arcom1) Hrc1) => [arcom3 [_ Hrc3]].
             rewrite Hrc3 /=.
             assert (Htpc3 : pc3_tag = Level n color) by (move: tag_pc3; rewrite eq_s3 /=; done).
             destruct ti0 as [vti0 cti0 eti0 icti0]; simpl in Hcti0, HE5.
             destruct icti0; [| discriminate HE5].
             unfold transfer, instr_rules, LRC.instr_rules.
             rewrite Htpc3 /= Hcti0 eqxx /=.
             unfold check_belong. rewrite !(belong_eq color) Hcolni Hcoltold !eqxx /=.
             rewrite HE2 (surjective_pairing (switch_val told td2)) /=.
             (* do_updates: if_Some lets obind reduce past the r1/r2 setm-aliasing while keeping
                the `if r2==r1` as a value the eexists absorbs. *)
             have if_Some : forall (T:Type) (cc:bool) (xx yy:T), (if cc then Some xx else Some yy) = Some (if cc then xx else yy)
               by (move=> T cc xx yy; case: cc).
             rewrite VT31 /=. rewrite /updm VT31 /=.
             rewrite (setmE (regs s3) r1 (w1@Other) r2) VT32 if_Some /=.
             rewrite OLD3 /=.
             reflexivity.
        * (* equiv: 4-level preserves_equiv_right_mem_write(w1, vd2@s3) (PreservationLemmas.v:127)
             ∘ reg_write(r2, vd2@..) ∘ reg_write(r1, w1@Other) ∘ pc_incr, dispatched like Bnz. All
             s3 reads resolved (VT31: regs3 r1=w1@Other, VT32: regs3 r2=vd2@td2, OLD3: mem3 w1=vdm@tdm);
             color facts Hcti0/Hcoltold; DMM = data_match' for the stored cell (mem_write premises).
             s1' = {mem:=setm(mem s1)w1 (w2@(switch_val told t2).1); regs:=setm(setm(regs s1)r1 (vala x7@Other))r2 (vala x5@(is_addr t2?Inv:Other)); pc:=(vala(pc s1)+1)@(trpc ov); internal s1};
             s3' = {mem:=setm(mem s3)w1 (vd2@(switch_val tdm td2).1); regs:=setm(setm(regs s3)r1 w1@Other)r2 ((vala(if r2==r1 then w1@Other else vd2@td2))@(is_addr td2?Inv:Other)); pc:=(vala(pc s1)+1+as_word off)@pc3_tag; internal s3}.
             Compose: mem_write(w1) ∘ reg_write(r2) ∘ reg_write(r1) ∘ pc_incr; the r2-value carries
             `if r2==r1` (both sides — data_match relates them); mem_write's ~20 premises = data_match'
             (VTM2-derived), no_code_w (HE2/DMM), color (Hcoltold), capability/address (Other/cap). *)
          (* eapply preserves_equiv_right_mem_write with (w := w1) gives 21 premises (verified):
             base equiv (→ reg_write(r2) ∘ reg_write(r1) ∘ pc_incr → strong/weak/common) + the
             stored-value conditions: data_match' v v' (v=w2@(switch_val told t2).1,
             v'=vd2@(switch_val tdm td2).1 — the HARD one, relate via VTM2+DMM and switch_val's
             vtag:=value-tag/color:=cell-color form), color/entry/is_relevant of v, mem s1 pc = code,
             ~is_code v/v' (HE2: is_code told=false ⇒ is_code (switch_val..)=is_code told=false),
             capability/address (Other⇒I), updm×2 (via OLD-domm), state-eqs. *)
          assert (Hov : ov = OVec STORE tpc0 [hseq Other; (if is_address t2 then Invalidated else Other); s])
            by (destruct x12 as [x12a x12b]; destruct o as [ot otr]; simpl in *; congruence).
          rewrite !Hov /=.
          have Htoldtdm : told = tdm by (move: DMM; rewrite /data_match' => -[H _]; exact H).
          have Ht2td2 : t2 = td2 by (move: VTM2; rewrite /data_match => -[H _]; exact H).
          subst tdm; subst td2.
          have Hsv : s = (switch_val told t2).1 by rewrite HE3.
          have Hsw_ic : forall (m : tag_type lrc_tags Symbolic.M) (vv : tag_type lrc_tags R), is_code (switch_val m vv).1 = is_code m by (move=> m vv; case: m).
          have Hsw_col : forall (m : tag_type lrc_tags Symbolic.M) (vv : tag_type lrc_tags R), LRC.color (switch_val m vv).1 = LRC.color m by (move=> m vv; case: m).
          have Hsw_vt : forall (m : tag_type lrc_tags Symbolic.M) (vv : tag_type lrc_tags R), vtag (switch_val m vv).1 = vv by (move=> m vv; case: m).
          have Hsw_ent : forall (m : tag_type lrc_tags Symbolic.M) (vv : tag_type lrc_tags R), entry (switch_val m vv).1 = entry m by (move=> m vv; case: m).
          have Hics : is_code s = false by (rewrite Hsv Hsw_ic; exact HE2).
          have Hscol : LRC.color s = color by (rewrite Hsv Hsw_col; exact Hcoltold).
          have Hvts : vtag s = t2 by (rewrite Hsv Hsw_vt).
          have Hent : entry told = None.
          { case He : (entry told) => [e|//]. exfalso; move: (entry_code1 w1 (old@told) e OLDs1 He); rewrite HE2 //. }
          have Hents : entry s = None by (rewrite Hsv Hsw_ent; exact Hent).
          have Hic_ni : is_code (taga ni).
          { have PCs1 : mem s1 pc0 = Some (i@ti0) by (rewrite ST; exact PC).
            move: (end_s1 pc0 (i@ti0) PCs1 HE5).
            have Hvi : vala (i@ti0) = i by []. rewrite Hvi INST.
            move => [Hh|[v' [Hv' Hcv']]]; first (exfalso; exact Hh).
            rewrite ST /= in NPC Hv'.
            rewrite NPC in Hv'. case: Hv' => Heq. rewrite -Heq in Hcv'; exact Hcv'. }
          rewrite -!Hsv.
          have Hx7 : x7 = w1@Other by (move: R1Ws1; rewrite H5 => -[<-]).
          have if_Some : forall (T:Type) (cc:bool) (xx yy:T), (if cc then Some xx else Some yy) = Some (if cc then xx else yy)
            by (move=> T cc xx yy; case: cc).
          have Hx5 : x5 = (if r2 == r1 then w1@Other else w2@t2).
          { move: H3; rewrite Hov /= Hx7 /= (setmE (regs s1) r1 (w1@Other) r2) R2Ws1 if_Some => -[<-] //. }
          have Hw2vd2 : is_address t2 = false -> w2 = vd2.
          { move: VTM2 => Hvm; rewrite /data_match in Hvm; move: Hvm; clear; case: t2 => //=; by move=> -[_ ->]. }
          rewrite Hx7 Hx5 ?(fun_if vala) /=.
          case: (internal s1); case: (internal s3).
          eapply preserves_equiv_right_mem_write with (w := w1) (v := w2@s) (v' := vd2@s).
          eapply preserves_equiv_right_reg_write with (r := r2) (v := (if r2 == r1 then w1 else w2)@(if is_address t2 then Invalidated else Other)) (v' := (if r2 == r1 then w1 else vd2)@(if is_address t2 then Invalidated else Other)).
          eapply preserves_equiv_right_reg_write with (r := r1) (v := w1@Other) (v' := w1@Other).
          eapply preserves_equiv_right_pc_incr with (pc1' := (vala (pc s1) + 1)%w) (tpc1' := tpc0)
                                                    (pc3' := (vala (pc s1) + 1 + as_word off)%w) (tpc3' := pc3_tag).
          1:{ split; [exact strong | split; [exact weak | exact common]]. }
          all: try (simpl; reflexivity).
          all: try exact I.
          all: lazymatch goal with
               | |- data_match' _ _ _ _ => rewrite /data_match'; split; [reflexivity | simpl; rewrite Hscol Hvts -Hco; exact VTM2]
               | |- entry _ = None => simpl; exact Hents
               | |- is_relevant_comp _ _ => simpl; rewrite Hscol; unfold is_relevant_comp;
                   (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ])
               | |- not _ => simpl; rewrite Hics; done
               | |- updm _ _ _ = Some _ =>
                   unfold updm; simpl;
                   rewrite ?R1Ws1 ?VT31 ?OLDs1 ?OLD3 ?(setmE (regs s1) r1 (w1@Other) r2) ?(setmE (regs s3) r1 (w1@Other) r2) ?R2Ws1 ?VT32 ?if_Some /=;
                   reflexivity
               | |- mem _ _ = Some _ => simpl; exact NPC
               | |- is_true (is_code (taga _)) => exact Hic_ni
               | |- _ = taga (pc _) => first [by rewrite ST | by rewrite eq_s3]
               | |- same_pc _ _ _ =>
                   eapply same_pc_normal;
                   [ simpl; split; [exact NPC | exact Hic_ni]
                   | simpl; unfold color_of; simpl; rewrite Htpc0; exact eq_off
                   | simpl; reflexivity ]
               | |- data_match _ _ _ _ _ =>
                   rewrite ?Hx7 ?Hx5; unfold color_of; simpl; rewrite ?Htpc0; simpl;
                   split; first reflexivity;
                   first [ reflexivity
                         | (destruct (is_address t2) eqn:Ha; simpl;
                            [ exact I
                            | (destruct (r2 == r1) eqn:Hrr; simpl;
                               [ reflexivity
                               | by apply Hw2vd2 ]) ]) ]
               | |- LRC.color _ = color_of _ =>
                   cbn [taga]; rewrite Hscol; rewrite /color_of /=; rewrite Htpc0; reflexivity
               | |- forall _, _ \/ _ -> _ =>
                   cbn [mem taga]; move=> vv [Hd|Hd];
                   [ move: Hd; rewrite OLDs1 | move: Hd; rewrite OLD3 ];
                   move=> [= <-] /=; rewrite Hscol Hcoltold; reflexivity
               | |- (exists _, _ /\ _) =>
                   cbn [mem];
                   first [ (exists (old@told); split; [exact OLDs1 | exact Hnc])
                         | (exists (vdm@told); split; [exact OLD3 | exact Hnc]) ]
               | |- address_correctness _ _ _ _ =>
                   first [ (cbn [taga vtag]; destruct (is_address t2); exact I)
                         | (cbn [taga vtag vala mem]; rewrite Hvts;
                            first [ exact (s_reg_cor _ _ R2Ws1) | exact (s'_reg_cor _ _ VT32) ]) ]
               | |- capability_correctness' ?ws _ _ _ _ =>
                   first
                     [ exact I
                     | (cbn [taga vtag]; destruct (is_address t2); exact I)
                     | (cbn [taga vtag]; rewrite Hvts;
                        move: capa_cor1 capa_cor3 R2Ws1 VT32; clear;
                        case: t2 => [ n0 | | | ]; move=> capa_cor1 capa_cor3 R2Ws1 VT32;
                        [ rewrite /capability_correctness' /=;
                          lazymatch ws with
                          | WS_S2 =>
                            (split;
                             [ move=> vv ww tt' tteq meq;
                               move: (capa_cor1 vv n0 (inr ww) (ex_intro _ tt' (conj meq tteq))) => [_ uu];
                               exact (uu (inl r2) w2 R2Ws1)
                             | move: (capa_cor1 w2 n0 (inl r2) R2Ws1) => [iss uu]; split; last exact iss;
                               move=> vv rr rq; move: rq;
                               rewrite (setmE (setm (regs s1) r1 w1@Other) r2 _ rr) (setmE (regs s1) r1 _ rr);
                               case: ifP => [_ | Hr2]; first (by move=> H; discriminate (congr1 (fun o => if o is Some a then taga a else Ret 0) H));
                               case: ifP => [_ | Hr1]; first (by move=> H; discriminate (congr1 (fun o => if o is Some a then taga a else Ret 0) H));
                               move=> rq; move: (uu (inl rr) vv rq) => Erq; move: Hr2; rewrite Erq eqxx // ])
                          | WS_S3 =>
                            (split;
                             [ move=> vv ww tt' tteq meq;
                               move: (capa_cor3 vv n0 (inr ww) (ex_intro _ tt' (conj meq tteq))) => [_ uu];
                               exact (uu (inl r2) vd2 VT32)
                             | move: (capa_cor3 vd2 n0 (inl r2) VT32) => [iss uu]; split; last exact iss;
                               move=> vv rr rq; move: rq;
                               rewrite (setmE (setm (regs s3) r1 w1@Other) r2 _ rr) (setmE (regs s3) r1 _ rr);
                               case: ifP => [_ | Hr2]; first (by move=> H; discriminate (congr1 (fun o => if o is Some a then taga a else Ret 0) H));
                               case: ifP => [_ | Hr1]; first (by move=> H; discriminate (congr1 (fun o => if o is Some a then taga a else Ret 0) H));
                               move=> rq; move: (uu (inl rr) vv rq) => Erq; move: Hr2; rewrite Erq eqxx // ])
                          | _ => idtac
                          end
                        | exact I | exact I | exact I ]) ]
               | |- pc_code_color _ => pcc_close2 (PCCM.step_me_mp step_1) ST
               | |- _ => cbn [mem vala pc]; exact NPC
               end.
      + (* JUMP (register-indirect): silent ⇒ intra (belong=true); registers UNCHANGED *)
        Local Opaque next_state_do_update next_state_do_updates.
        unfold next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        repeat (apply obind_inv in NEXT as [? [?HR NEXT]]).
        destruct (mem s1 w) as [ni|] eqn:NPC.
        2: { (* None target: contradiction — reg r holds an InternalJump value, whose target must exist *)
             Local Transparent belong next_state_do_update next_state_do_updates.
             destruct x0 as [ov ev].
             have Htpc : tpc0 = Level n c0 by (move: tag_pc1; rewrite ST /=).
             cbn in HR0.
             apply obind_inv in HR0 as [[] [Hic HR0]]; destruct (is_code ti0) eqn:Eic; [| discriminate Hic].
             subst tpc0. cbn in HR0.
             repeat (apply obind_inv in HR0 as [? [?HC HR0]]).
             move: HR0 => [= Hov Ho0]. subst o0.
             apply obind_inv in Hic as [[] [_ Hic]].
             apply obind_inv in Hic as [out [Hout Hic]].
             apply obind_inv in Hout as [[] [Hcol Hout]].
             rewrite (hseq_eta l) (hseq_eta (hsbehead l)) in Hout.
             cbn in Hout.
             apply obind_inv in Hout as [[] [Hjmp Hout]].
             have Hhl : hshead l = t1 := reg_clear_list_head CLEAR.
             move: Hjmp; rewrite Hhl => Hjmp'.
             destruct t1; try discriminate Hjmp'.
             exfalso.
             move: (s_reg_cor (w @ InternalJump) r) => Hac.
             have RW' : regs s1 r = Some (w @ InternalJump) by (rewrite ST /=; exact RW).
             move: (Hac RW'); rewrite /address_correctness /=.
             move=> [v' [Hmv _]]. rewrite NPC in Hmv. discriminate Hmv. }
        cbn -[next_state_do_updates next_state_do_update] in NEXT.
        repeat (apply obind_inv in NEXT as [? [?HR2 NEXT]]).
        destruct x0 as [ov ev]. cbn -[next_state_do_updates next_state_do_update] in NEXT.
        repeat (apply obind_inv in NEXT as [? [?HR3 NEXT]]).
        move: NEXT => [= Hs1' Hev]. subst ev. subst s1'.
        have Htpc : tpc0 = Level n c0 by (move: tag_pc1; rewrite ST /=).
        Local Opaque belong.
        cbn in HR0.
        apply obind_inv in HR0 as [[] [Hic HR0]]; destruct (is_code ti0) eqn:Eic; [| discriminate Hic].
        subst tpc0. cbn in HR0.
        repeat (apply obind_inv in HR0 as [? [?HC HR0]]).
        move: HR0 => [= Hov Ho0]. subst o0.
        apply obind_inv in Hic as [[] [_ Hic]].
        apply obind_inv in Hic as [out [Hout Hic]].
        apply obind_inv in Hout as [[] [Hcol Hout]].
        rewrite (hseq_eta l) (hseq_eta (hsbehead l)) in Hout.
        cbn in Hout.
        destruct (belong (match ti0 with | {| color := c |} => c end) (Some (taga ni))) eqn:Hbel.
        * (* intra: belong = true ⇒ identity re-tag, regs unchanged (x0 = s1) *)
          rewrite Hbel in Hout; cbn in Hout.
          apply obind_inv in Hout as [[] [Hjmp Hout]].
          move: Hout => [= Hout]; subst out.
          cbn in Hic; move: Hic => [= Ho]; subst o.
          rewrite -Hov in HR3 *; cbn [trpc tr] in HR3 |- *.
          rewrite -(hseq_eta (hsbehead l)) -(hseq_eta l) in HR3.
          have Hra' : regs s1 ra = Some (rav @ rat) by rewrite ST /=; exact: RA.
          have Hrw' : regs s1 r = Some (w @ t1) by rewrite ST /=; exact: RW.
          have Hcl' : reg_clear_list (regs s1) t1 = Some l by rewrite ST /=; exact: CLEAR.
          rewrite (jump_do_updates_result Hra' Hrw' Hcl') in HR3.
          move: HR3 => [= Hx0].
          Local Transparent belong next_state_do_update next_state_do_updates.
          rewrite -Hx0.
          inversion pc_s1_s3 as [sA sA' Hva Hnone | sA sA' vv0 off Hsome Hoff Hpcrel].
          { subst sA. case: Hnone => Hnone _. rewrite ST /= in Hnone; rewrite PC in Hnone; discriminate. }
          subst sA sA'.
          have Hcolor : color_of s1 = c0 by rewrite ST.
          rewrite Hcolor in Hoff.
          have Hhl : hshead l = t1 := reg_clear_list_head CLEAR.
          move: Hjmp; rewrite Hhl => Hjmp'.
          destruct t1; try discriminate Hjmp'.
          destruct ni as [vni tni].
          assert (belong_eq : forall (cc : Component.id) m, belong cc (Some m) = (cc == LRC.color m))
            by (move=> cc [vt cm em icm]; reflexivity).
          have Hc0 : color ti0 = c0 by (apply/eqnP; move: Hcol; by case: (eqn (color ti0) c0)).
          have Hrel : c0 \in domm ic by (eapply side_right_in_ic; [ exact col_mem1 | rewrite ST; exact PC | exact Hc0 | rewrite Hcolor in side_eq; exact side_eq ]).
          have Hcolni : color tni = c0.
          { move: Hbel; rewrite belong_eq => /eqP <-. by []. }
          have Hrws1 : regs s1 r = Some (w @ InternalJump) by rewrite ST /=; exact RW.
          destruct (reg_match r (w @ InternalJump)) as [_ Yr].
          specialize (Yr Hrws1) as [d3 [Hdm Hr3]].
          destruct d3 as [w3 t3]. move: Hdm => [Ht3 Hrel2]. subst t3.
          move: Hrel2; rewrite Hcolor Hoff /= => Hreloc.
          have HPCs1 : mem s1 pc0 = Some (i @ ti0) by rewrite ST.
          edestruct (code_left pc0 i ti0 off c0) as [Xf _].
          { rewrite /is_relevant_comp; exact Hrel. }
          { exact Hoff. }
          { exact Eic. }
          { exact Hc0. }
          specialize (Xf HPCs1) as [v' [match_dec mem_s3]].
          have Hvi : v' = i.
          { inversion match_dec as [Hn1 Hn2 Hvv | Hd1 Hd2 | jimm dd dd' Hdi Hdi' Hmd1 Hmd3 Hcd Htagdd Hr].
            - congruence.
            - congruence.
            - congruence. }
          subst v'.
          have Hcodeni : is_code tni.
          { move: (s_reg_cor (w @ InternalJump) r); rewrite ST /= => Hac.
            move: (Hac RW); rewrite /address_correctness /=.
            move=> [vv [Hmv Himpl]]. move: NPC; rewrite ST /= => NPC0. rewrite NPC0 in Hmv.
            case: Hmv => Hmv'; subst vv.
            apply Himpl. rewrite /is_relevant_comp Hcolni. exact Hrel. }
          edestruct (code_left w vni tni off c0) as [Xt _].
          { rewrite /is_relevant_comp; exact Hrel. }
          { exact Hoff. }
          { exact Hcodeni. }
          { exact Hcolni. }
          specialize (Xt NPC) as [vt3 [match_t mem_t3]].
          have Hras1 : regs s1 ra = Some (rav @ rat) by rewrite ST /=; exact RA.
          destruct (reg_match ra (rav @ rat)) as [_ Yra].
          specialize (Yra Hras1) as [da3 [_ Hra3]]. destruct da3 as [rav3 rat3].
          have Hpc3v : pc3_val = (pc0 + as_word off)%w by (move: Hpcrel; rewrite ST eq_s3 /=).
          have Hpc3t : pc3_tag = Level n c0 by (move: tag_pc3; rewrite eq_s3 /=).
          rewrite eq_s3 /= in mem_s3 mem_t3 Hr3 Hra3.
          have Hdomm3 : domm regs3 = fset (ra :: [seq word_of_nat i | i <- reg_list])
            by (move: reg_domm3; rewrite /register_domm eq_s3 /=).
          have [l3 Hl3] := @reg_clear_list_total regs3 InternalJump Hdomm3.
          exists (@State mt lrc_tags _ mem3 regs3 (w3 @ (Level n c0)) internal3).
          exists M.
          split.
          { eapply plus_one. eapply step_jump.
            - rewrite eq_s3 Hpc3t; reflexivity.
            - rewrite Hpc3v; exact mem_s3.
            - exact INST.
            - exact Hr3.
            - exact Hra3.
            - exact Hl3.
            - (* NEXT3: forward JUMP transfer for s3 — belong+is_jump ⇒ identity, regs unchanged *)
              have [arcom1 Hrc1] : exists a, regs s1 rcom = Some a
                by (move: HR; rewrite /evi; case: (regs s1 rcom) => [a _|//]; by exists a).
              have [arcom3 [_ Hrc3]] := proj2 (reg_match rcom arcom1) Hrc1.
              have Hmt3 : mem s3 w3 = Some (vt3 @ tni) by (rewrite eq_s3 /= Hreloc; exact mem_t3).
              have Hra3' : regs s3 ra = Some (rav3 @ rat3) by (rewrite eq_s3; exact Hra3).
              have Hrw3' : regs s3 r = Some (w3 @ InternalJump) by (rewrite eq_s3; exact Hr3).
              have Hl3' : reg_clear_list (regs s3) InternalJump = Some l3 by (rewrite eq_s3; exact Hl3).
              have Hhl3 : hshead l3 = InternalJump := reg_clear_list_head Hl3.
              have Hbel3 : belong (match ti0 with {| color := c |} => c end) (Some tni) = true
                by (rewrite belong_eq Hcolni; apply/eqP; exact Hc0).
              have Hisj : is_jump (hshead l3) = Some tt by (rewrite Hhl3).
              Local Opaque belong next_state_do_updates next_state_do_update.
              unfold next_state_updates_and_pc.
              rewrite Hmt3 /=.
              unfold next_state.
              rewrite /evi Hrc3 /=.
              unfold transfer, instr_rules, LRC.instr_rules.
              rewrite Eic /= Hpc3t /= Hcol /=.
              rewrite (hseq_eta l3) (hseq_eta (hsbehead l3)) /=.
              rewrite Hbel3 /= Hisj /=.
              rewrite -(hseq_eta (hsbehead l3)) -(hseq_eta l3).
              rewrite (jump_do_updates_result Hra3' Hrw3' Hl3').
              Local Transparent belong next_state_do_updates next_state_do_update.
              rewrite eq_s3 /=. reflexivity. }
          { eapply preserves_equiv_right_pc_incr with
              (s1 := s1) (s3 := s3)
              (pc1' := w) (tpc1' := Level n c0) (pc3' := w3) (tpc3' := Level n c0).
            - exact: (conj strong (conj weak common)).
            - by case: (internal s1).
            - have Eu : forall u : unit, u = tt by case.
              have Em : mem3 = mem s3 by rewrite eq_s3.
              have Er : regs3 = regs s3 by rewrite eq_s3.
              by rewrite (Eu internal3) Em Er.
            - eapply same_pc_normal; [split; [exact NPC | exact Hcodeni] | exact Hoff | exact Hreloc].
            - exact: (esym tag_pc1).
            - exact: (esym tag_pc3).
            - pcc_close2 (PCCM.step_me_mp step_1) ST. }
        * (* cross: belong = false ⇒ RETURN, which emits an ERet event, contradicting the silent step *)
          rewrite Hbel in Hout; cbn in Hout.
          apply obind_inv in Hout as [[] [_ Hout]].
          apply obind_inv in Hout as [cc [_ Hout]].
          apply obind_inv in Hout as [[] [_ Hout]].
          move: Hout => [= Hout]; subst out.
          cbn in Hic; move: Hic => [= _ Hev].
          Local Transparent belong next_state_do_update next_state_do_updates.
          discriminate Hev.
      + unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        repeat (apply obind_inv in NEXT as [? [?HR NEXT]]).
        destruct (mem s1 pc') as [ni|] eqn:NPC;
          [| (* None: the new pc always has a code cell (w=0 ⇒ fall-through/end_s1;
                w≠0 ⇒ branch target/bnz_s1) ⇒ contradiction *)
             exfalso;
             cbn in HR0;
             apply obind_inv in HR0 as [[] [Hic _]];
             destruct (is_code ti0) eqn:Eic; [| discriminate Hic];
             rewrite ST /= in end_s1 bnz_s1 NPC;
             change pc' with (pc0 + (if w == 0%w then 1 else swcast n0))%w in NPC;
             destruct (w == 0%w) eqn:E0; move: NPC; rewrite ?E0 /=; move=> NPC;
             [ (case: (end_s1 pc0 (i@ti0) PC Eic) => [Hh | [v' [Hv' _]]];
                 [ rewrite INST in Hh; exact Hh | rewrite NPC in Hv'; discriminate Hv' ])
             | (move: (bnz_s1 pc0 (i@ti0) PC Eic); rewrite INST => -[v' [Hv' _]];
                rewrite NPC in Hv'; discriminate Hv') ] ].
        simpl in NEXT.
        repeat (apply obind_inv in NEXT as [? [?HR2 NEXT]]).
        destruct x0 as [ov ev]. simpl in NEXT.
        repeat (apply obind_inv in NEXT as [? [?HR3 NEXT]]).
        move: NEXT => [= Hs1' Hev]. subst ev. subst s1'.
        (* s3-side setup (try-wrapped lines are safe; the Heqa* refs no-op under obind_inv) *)
        try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3.
        try (match goal with c: Component.id |- _ => rename c into color end).
        try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                  [exfalso; subst; simpl in *; rewrite (proj1 eq_none) in PC; done |]).
        (* derive the s3 condition read from the s1 read RW via reg_match *)
        assert (RWs1 : regs s1 r = Some (w@t1)) by (rewrite ST; exact RW).
        pose proof (proj2 (reg_match r _) RWs1) as [d' [VTM VT3]].
        (* VTM : data_match Right (color_of s1) M (w@t1) d' ; VT3 : regs s3 r = Some d' (the s3 condition read) *)
        (* HR0 = the transfer equation (= Some(ov,None)); reduce its concrete-mvec match + peel is_other t1 *)
        cbn in HR0.
        repeat (match goal with
                | H : obind _ _ = Some _ |- _ => apply obind_inv in H as [? [? H]]
                | H : (let (_, _) := ?x in _) = Some _ |- _ => let E := fresh "HE" in destruct x eqn:E
                end).
        match goal with H : is_other t1 = Some _ |- _ => rename H into HISO end.
        destruct t1; unfold is_other in HISO; simpl in HISO; try discriminate HISO.  (* t1 = Other *)
        (* === BNZ: obind_inv prologue FAST + t1=Other extracted (validated 2026-05-31, green ~17s). The full
             post-peel state (from rocq-mcp get_proof_state) gives every value to finish — NEXT (mechanical,
             no hangs; iterate the exact injection/subst forms with MCP):
             - resolve the witness chain so s1' is concrete:
                 H4 : Some({trpc:=tpc0; tr:=[hseq Other]},None) = Some x6  ⇒ x6
                 H2 : Some({trpc:=trpc0; tr:=tr0}, x6.2) = Some(o,o0)       ⇒ o, o0=None
                 HR0: Some({trpc o; tr o}, o0) = Some(ov,None)             ⇒ trpc ov=tpc0, tr ov=[hseq Other]
                 H  : Some{mem s1; regs:=x3; pc s1; internal s1} = Some x1, HR3: Some x1=Some x0 ⇒ x0
                 H1 : updm (regs s1) r (vala x2)@(hshead (tr ov)) = Some x3 ⇒ x3 = setm (regs s1) r (w@Other)
                       (updm_set; hshead [hseq Other] = Other; H0+RWs1 ⇒ vala x2 = w)
               ⇒ s1' = {| mem:=mem s1; regs:=setm (regs s1) r (w@Other); pc:=pc'@tpc0; internal:=internal s1 |},
                 pc' = (pc0 + (if w==0 then 1 else swcast n0))%w, tpc0 = taga(pc s1) = Level n color.
             - then: eexists concrete s3' {mem3; setm regs3 r (w@Other); pc3'@(Level n color); tt} (pc3' = pc3_val
               + (if w==0 then 1 else swcast n0)); eapply plus_one; eapply step_bnz + premises (s3 fetch via
               code_left, s3 cond read VT3); then the simple equiv: reg_write r (w@Other) + pc_incr (orig ref 1908-1921),
               pc'_eq via word_ac. Same obind_inv recipe ⇒ Jal/Store/Jump. === *)
        move: (updm_set H1) => H1'. clear H1.
        rewrite RWs1 in H0.
        repeat (match goal with
                | H : context[fst (_, _)] |- _ => cbn [fst] in H
                | H : context[snd (_, _)] |- _ => cbn [snd] in H
                | H : Some _ = Some _ |- _ => injection H as H
                | H : (_, _) = (_, _) |- _ => injection H as ? ?
                | H : {| trpc := _; tr := _ |} = {| trpc := _; tr := _ |} |- _ => injection H as ? ?
                end); subst.
        cbn [mem regs pc internal hshead Types.taga Types.vala fst snd trpc tr] in *.
        (* s1' resolved to {| mem:=mem0; regs:=setm reg r w@(hshead tr0); pc:=pc'@trpc0; internal:=extra |}.
           LAST MILE: trpc0/tr0 (the BNZ ovec fields) are still abstract — the peel's `destruct` of the
           ovec `let '{trpc:=trpc0; tr:=tr0} := out.1` ran BEFORE x6 was resolved, losing the connection
           trpc0=tpc0 / tr0=[hseq Other]. FIX (next): in the t1=Other robust peel, only `destruct` the PAIR
           lets (the (ov,ev) state pairs), NOT the ovec record let — let cbn reduce the latter after the
           Some-eqs resolve x6; OR after this point assert (Htr: tr0 = [hseq Other]) (⇒ hshead tr0 = Other)
           and (Htrpc: trpc0 = tpc0 = Level n color) [both hold by the BNZ rule output] and rewrite.
           THEN: eexists concrete s3' {mem3; setm regs3 r (w@Other); pc3'@(Level n color); internal3}
           (pc3' = pc3_val + (if w==0 then 1 else swcast n0)); eapply plus_one; eapply step_bnz + premises
           (s3 fetch via code_left, s3 cond read = VT3); then equiv: reg_write r (w@Other) + pc_incr,
           pc'_eq via word_ac (orig ref 1908-1921). Whole thing is FAST (obind_inv); no hangs. *)
        assert (Htr0 : tr0 = [hseq Other]) by congruence.
        assert (Htrpc0 : trpc0 = tpc0) by congruence.
        rewrite Htr0 Htrpc0. cbn [hshead] in *.
        (* s1' = {| mem:=mem0; regs:=setm reg r w@Other; pc:=pc'@tpc0; internal:=extra |} (CONCRETE). *)
        (* resolve d' = w@Other (data_match Other) *)
        destruct d' as [dv dt]. unfold data_match in VTM. destruct VTM as [Hdt Hdv]. subst dt. simpl in Hdv.
        rewrite <- Hdv in VT3. clear Hdv dv.
        (* === PROLOGUE COMPLETE + s1' FULLY CONCRETE (validated 2026-05-31, green ~17s, obind_inv, NO hangs):
             s1' = {| mem:=mem0; regs:=setm reg r w@Other; pc:=pc'@tpc0; internal:=extra |};
             pc' (a let-var) = (pc0 + (if w==0 then 1 else swcast n0))%w; tpc0 = taga(pc s1) = Level n color;
             VT3 : regs3 r = Some w@Other (s3 condition read); s3 = {mem3;regs3;pc3_val@pc3_tag;internal3};
             pc_s1_s3 : pc3_val = pc0 + as_word off. ALL hyps available (PC/INST/RW/code_left/reg_match/...).
           REMAINING = step + equiv (mechanical, no hangs; the SIMPLE all-Other equiv):
             - grab the branch cond: `pc'` is a zeta let-var, so `match goal` can't see the `if`; use
               `cbv zeta in *` (or reference pc'+as_word off); s3' = {mem3; setm regs3 r (w@Other);
               (pc3_val + (if w==0 then 1 else swcast n0))%w @ pc3_tag; internal3}.
             - s3 fetch: `edestruct (code_left pc0) as [X _]` (instantiate color/off/ti0; the 3rd code_left
               premise wants the instr tag) then `specialize (X PC)` ⇒ match_dec + mem_s3.
             - eexists s3' + `eapply plus_one; eapply step_bnz` + premises (fetch via mem_s3; decode via
               match_dec+decode_instr_eq; cond read = VT3; NEXT = forward-compute, peel with obind_inv if slow).
             - equiv: `eapply preserves_equiv_right_reg_write with (r:=r)(v:=w@Other)(v':=w@Other);
               eapply preserves_equiv_right_pc_incr with (pc1':=pc')(tpc1':=tpc0)(pc3':=<s3 target>)(tpc3':=pc3_tag)`
               then the all-Other dispatcher (exact I / split;reflexivity / same_pc via word_ac); pc'_eq:
               <s3 target> = (pc' + as_word off)%w by word_ac. (orig ref 1908-1921.) NO huge Heqa2; all fast. === *)
        assert (Hcc : color_of {| mem := mem0; regs := reg; pc := pc0@tpc0; internal := extra |} = color)
          by (by rewrite /color_of/= tag_pc1).
        assert (Hi0 : i0 = color).
          { move: HE1; rewrite tag_pc1 /= => [= Hn Hi]; by rewrite Hi. }
        assert (Htic : LRC.color ti0 = color).
          { have E5 : is_true (eqn (LRC.color ti0) i0) by (move: H5; case: (eqn (LRC.color ti0) i0) => //).
            move/eqnP: E5 => E5. by rewrite E5 Hi0. }
        rewrite Hcc in side_eq eq_off.
        edestruct (code_left pc0) as [X _].
        { instantiate (1 := color). unfold is_relevant_comp.
          (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ]). }
        { instantiate (1 := off). exact eq_off. }
        { instantiate (1 := ti0). move: H3; case: (is_code ti0) => //. }
        { exact Htic. }
        specialize (X PC) as [vpc [match_dec mem_s3]].
        eexists. exists M. simpl.
        split.
        * eapply plus_one. eapply step_bnz.
          -- reflexivity.
          -- rewrite pc_s1_s3; exact mem_s3.
          -- assert (Hvv : vpc = i) by (inversion match_dec; congruence).
             rewrite Hvv; exact INST.
          -- exact VT3.
          -- (* NEXT (premise 5): next_state_updates_and_pc s3 (IVec BNZ pc3_tag ti0 [hseq Other])
                  [RegRead r] (pc3_val + (if w==0 then 1 else swcast n0)) = Some (?s3', None).
                ?s3' is the evar; the forward computation determines it to
                  State mem3 (setm regs3 r w@Other) ((pc3_val+brnch)@pc3_tag) internal3.
                RECIPE (mechanical, no hang — transfer is structurally identical to the s1 side,
                 same ti0 / same color (Hti) / tx = Other (VT3) / same target tag (taga ni)):
                 1. is_code (taga ni): from BNZ_correctness mem0 (with INST + H3) for the w<>0
                    taken branch (target = pc0 + swcast n0); the w==0 fall-through (pc0+1)
                    is is_code by code_prefix_condition (plumbing).
                 2. second code_left at the s1 branch target pc' (NPC : mem0 pc' = Some ni):
                    edestruct (code_left pc') with premises [color | off | taga ni (=Hic) |
                    color (taga ni) = color (from H7 check_belong success + Hti)] => gives
                    mem_tgt : mem3 (pc' + as_word off) = Some vni@(taga ni).
                 3. Hpc3' : (pc3_val + brnch) = (pc' + as_word off) by (rewrite pc_s1_s3 /pc'; word_ac);
                    rewrite Hpc3' so the mem read hits mem_tgt.
                 4. unfold next_state_updates_and_pc; rewrite mem_tgt; unfold next_state;
                    rewrite (evi s3 = Some _); compute transfer (BNZ instr_rules): the color check
                    color ti0 == color (Hti + tag_pc3), is_other Other, check_belong color (taga ni)
                    (= H7 via Hti) all succeed => ov = OVec BNZ pc3_tag [hseq Other]; then
                    next_state_do_updates applies RegRead r (reads VT3) => setm regs3 r w@Other. *)
             destruct ni as [vni0 tni0].
             assert (Hcode : is_code ti0) by (move: H3; case: (is_code ti0) => //).
             (* Hic: branch target is code. w==0 fall-through (pc0+onew) via end_condition,
                w<>0 taken branch (pc0+swcast n0) via BNZ_correctness. `case: ifP` reduces
                the branch `if` WITHOUT simpl (avoids the swcast `=> /=` hang; 1%w = onew). *)
             assert (Hic : is_code tni0).
             { have Hvi : vala (i@ti0) = i by [].
               move: NPC; rewrite /pc'; case: ifP => Hw NPC.
               - move: (end_s1 pc0 (i@ti0) PC Hcode); rewrite Hvi INST.
                 move => [Hh|[v' [Hv' Hcv']]]; first (exfalso; exact Hh).
                 rewrite NPC in Hv'. case: Hv' => Heq. rewrite -Heq in Hcv'. exact Hcv'.
               - move: (bnz_s1 pc0 (i@ti0) PC Hcode); rewrite Hvi INST.
                 move => [v' [Hv' Hcv']].
                 rewrite NPC in Hv'. case: Hv' => Heq. rewrite -Heq in Hcv'. exact Hcv'. }
             assert (Hcolni : LRC.color tni0 = color).
             { clear NPC Hic. move: H7 => /=. rewrite /check_belong /belong.
               case: tni0 => vt ct et ict /=. case: ifP => [/eqP H _|//]. rewrite -H; exact Htic. }
             edestruct (code_left pc') as [Y _].
             { instantiate (1 := color). unfold is_relevant_comp.
          (eapply side_right_in_ic;
             [ exact col_mem1
             | first [ (rewrite ST; exact PC) | exact PC ]
             | first [ reflexivity | assumption ]
             | first [ exact side_eq
                     | (rewrite ST in side_eq; simpl in side_eq; exact side_eq)
                     | (rewrite Hco in side_eq; exact side_eq) ] ]). }
             { instantiate (1 := off). exact eq_off. }
             { instantiate (1 := tni0). exact Hic. }
             { exact Hcolni. }
             specialize (Y NPC) as [vni [match_ni mem_tgt]].
             assert (Hpc3' : (pc3_val + (if w == 0 then 1 else swcast n0))%w = (pc' + as_word off)%w).
             { rewrite pc_s1_s3 /pc'. word_ac. }
             rewrite Hpc3'.
             unfold next_state_updates_and_pc. rewrite mem_tgt.
             unfold next_state, evi.
             assert (Hrc1 : exists a, reg rcom = Some a).
             { move: HR. rewrite /evi. case: (reg rcom) => [a _|//]; by exists a. }
             destruct Hrc1 as [arcom1 Hrc1].
             move: (proj2 (reg_match rcom arcom1) Hrc1) => [arcom3 [_ Hrc3]].
             rewrite Hrc3 /=.
             destruct ti0 as [vti0 cti0 eti0 icti0]; simpl in Htic, Hcode.
             destruct icti0; [| discriminate Hcode].
             destruct tni0 as [vtni0 ctni0 etni0 ictni0]; simpl in Hcolni.
             unfold transfer, instr_rules, LRC.instr_rules.
             rewrite tag_pc3 /= Htic eqxx /=.
             unfold check_belong, belong. simpl. rewrite Hcolni eqxx /=.
             rewrite VT3 /=. rewrite /updm VT3 /=.
             reflexivity.
        * (* equiv: s3' = State mem3 (setm regs3 r w@Other) ((pc3_val+brnch)@pc3_tag) internal3.
             strong_equiv Right M s1' s3' /\ weak_equiv Left M s2 s3' /\ common_equiv M s2 s1' s3'
             where s1' = State mem0 (setm reg r w@Other) (pc'@tpc0) extra (all-Other, both sides).
             Via preserves_equiv_right_reg_write (r, w@Other) + preserves_equiv_right_pc_incr
             (pc1':=pc', tpc1':=tpc0, pc3':=pc3_val+brnch, tpc3':=pc3_tag); pc'_eq by word_ac
             (pc3_val+brnch = pc'+as_word off). orig ref 1922-1960. *)
          destruct extra; destruct internal3.
          have Hcode2 : is_code ti0 by (move: H3; case: (is_code ti0) => //).
          have Hic : is_code (taga ni).
          { have Hvi : vala (i@ti0) = i by [].
            move: NPC; rewrite /pc'; case: ifP => Hw NPC.
            - move: (end_s1 pc0 (i@ti0) PC Hcode2); rewrite Hvi INST.
              move => [Hh|[v' [Hv' Hcv']]]; first (exfalso; exact Hh).
              rewrite NPC in Hv'. case: Hv' => Heq. rewrite -Heq in Hcv'. exact Hcv'.
            - move: (bnz_s1 pc0 (i@ti0) PC Hcode2); rewrite Hvi INST.
              move => [v' [Hv' Hcv']].
              rewrite NPC in Hv'. case: Hv' => Heq. rewrite -Heq in Hcv'. exact Hcv'. }
          eapply preserves_equiv_right_reg_write with (r := r) (v := w@Other) (v' := w@Other).
          eapply (preserves_equiv_right_pc_incr) with (pc1' := pc') (tpc1' := tpc0)
                                                     (pc3' := (pc' + as_word off)%w) (tpc3' := pc3_tag).
          1:{ split; [exact strong | split; [exact weak | exact common]]. }
          all: try (simpl; reflexivity).
          all: lazymatch goal with
               | |- capability_correctness' _ _ _ _ _ => exact I
               | |- address_correctness _ _ _ _ => exact I
               | |- data_match _ _ _ _ _ => simpl; split; reflexivity
               | |- same_pc _ _ _ =>
                   eapply same_pc_normal;
                   [ simpl; split; [exact NPC | exact Hic]
                   | simpl; unfold color_of; simpl; rewrite tag_pc1; exact eq_off
                   | reflexivity ]
               | |- updm _ _ _ = Some _ => unfold updm; simpl; first [rewrite RW | rewrite VT3]; reflexivity
               | |- pc_code_color _ => pcc_close2 (PCCM.step_me_mp step_1) ST
               | |- _ => simpl; reflexivity
               end.
      (* ===== PORTED-BNZ-ATTEMPT =====
        unfold_all; try unfold_match; unfold_all.
        all: try (clear -Heqa2; repeat unfold_match' Heqa2; done); simpl in *.
        try (rewrite ST in PC_None; unfold color_of in PC_None; rewrite PC in PC_None; try (inversion PC_None; done || clear PC_None)).
        try (assert (tpc1 = tpc0) by (clear -Heqa2; unfold_match' Heqa2); subst tpc1).
        try (assert (ts0 = (ts (mvec None)) ) by
                 (unfold mvec in *; simpl; clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                  destruct Heqa2 as [_ _ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ts0).
        try (unfold mvec in *; assert (ti1 = ti0) by
                    (clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                     destruct Heqa2 as [_ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ti1).
        try (rewrite ST in end_s1 Heqa2; simpl in end_s1, Heqa2;
                  destruct (end_s1 pc0 _ PC) as [ instr_is_halt | [[i' ti'] [Heqi' code_i']]];
                  [destruct ti0; simpl in *; auto; try unfold_match' Heqa5; try done |
                    (match goal with
                     | op: _ = op_of_word _, inst: instr_of_args _ = _ |- _
                       => simpl in instr_is_halt;  rewrite <- op in instr_is_halt; simpl in instr_is_halt;
                         rewrite inst in instr_is_halt; done end) |
                    simpl in Heqi'; try (rewrite Heqi' in Heqa2; inversion Heqa2) ] ).
        unfold check_belong, belong, reg_clear_list in *.
        simpl in *; unfold_all.
        (match (type of Heqa2) with
           (_ = match ?m ?w with _ => _ end)
           => eapply (@modusponens (exists res, m w = Some res /\
                                            (LRC.color (taga res) \in domm ip ->
                                             is_code (taga res))));
             [|intros [res [res_eq res_code]]; rewrite res_eq in Heqa2]
         end).
        { try (match goal with
                    |- exists _ _, _ => repeat (unfold_all || unfold_match || rewrite orb_false_r in Heqa4, Heqa16) end).
        convert_eq_op.
        unfold is_jump in *; try (unfold_match; subst t1).
        unfold hshead in *; simpl in *.
        try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3.
        try (pose proof (esym Heqa3) as PC; clear Heqa3).
        try (match goal with c: Component.id |- _ => rename c into color end).
        try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                  [exfalso; subst; simpl in *; rewrite (proj1 eq_none) in PC; done |]).
        try (assert (color_of s1 = c0) as eq by (unfold color_of; subst; simpl; clear -tag_pc1; destruct tpc0; simpl in *; congruence);
                  subst c0).
        try (destruct tpc0; unfold_all).
        try (unfold compatible in *; rewrite eq in m_compat).
        try rewrite m_compat in side_eq.
        remember pc' as w'. unfold pc' in Heqw'.
        match (type of Heqw') with
          _ = (_ _ (match ?c as _ with _ => _ end)) => remember c as cond
        end. destruct cond; subst w'; try (rewrite Heqi'; eauto).
        subst. unfold_match' Heqa5. unfold is_code in Heqa3. unfold_match' Heqa3. pose proof (bnz_s1 _ _ PC) as H.
        simpl in H. simpl in *. rewrite <- Heqa1 in H. simpl in *. rewrite H0 in H. destruct H as [? [? ?]]; auto. eauto. }
        try (match goal with
                    |- exists _ _, _ => repeat (unfold_all || unfold_match || rewrite orb_false_r in Heqa4, Heqa16) end).
        convert_eq_op.
        unfold is_jump in *; try (unfold_match; subst t1).
        unfold hshead in *; simpl in *.
        try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3.
        try (pose proof (esym Heqa3) as PC; clear Heqa3).
        try (match goal with c: Component.id |- _ => rename c into color end).
        try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                  [exfalso; subst; simpl in *; rewrite (proj1 eq_none) in PC; done |]).
        try (assert (color_of s1 = c0) as eq by (unfold color_of; subst; simpl; clear -tag_pc1; destruct tpc0; simpl in *; congruence);
                  subst c0).
        try (destruct tpc0; unfold_all).
        try (unfold compatible in *; rewrite eq in m_compat).
        try rewrite m_compat in side_eq.
        inversion Heqa2.
        deduce_equality_r RW.
        destruct res as [resv rest]. simpl in H1.
        subst rest.
        destruct vt_match as [? match_t]. subst t1. destruct t; unfold is_other in *; try congruence. subst w.
        remember (@eq_op (mword_eqType _) v0 zerow) as cond.
        remember (pc3_val + (if cond then 1 else swcast n0))%w as pc3'.
        rewrite ST eq_s3 in pc_s1_s3, code_left. simpl in *.
        unfold side_of in *. unfold_match' side_eq. simpl in *.
        deduce_equality_r PC. rewrite eq_s3 in bnz_s3.
        pose proof (bnz_s3 _ _ vt_eq0) as H. simpl in H. eapply modusponens; [apply H; auto|]. clear H.
        inversion vt_match; try subst i; revert H; decode_instr_eq; intro H. clear H.
        intros [v' [v'eq v'code]]. rewrite eq_s3 in end_s3.
        pose proof (end_s3 _ _ vt_eq0 t_code). revert H. decode_instr_eq. intro H. destruct H; try contradiction.
        destruct H as [v'' [v''eq v''code]].
        assert (next_pc_eq : mem3 pc3' = Some (if cond then v'' else v')).
        { subst pc3'. destruct cond; simpl; auto. }
        assert (pc'_eq: pc3' = (pc' + as_word off)%w).
        { subst pc3' pc3_val. unfold pc'. word_ac. }
        assert (is_code0). { eapply res_code. subst s1. clear -Heqa3. simpl in *. unfold Component.id. rewrite <- Heqa3. trivial. }
        deduce_equality_r res_eq. rewrite next_pc_eq in vt_eq1. simplify_some.
        edestruct (code_left pc0) as [X _].
        { instantiate (1 := (color_of s1)).
          simpl in side_eq.  unfold side_of in side_eq. unfold is_relevant_comp.
          eauto. }
        { instantiate (1 := off). eauto. }
        { instantiate (1 := {| vtag := vtag; color := color_of s1; entry := entry; is_code := true |}); eauto. }
        { eauto. }
        rewrite ST in X. simpl in X.
        specialize (X PC) as [vpc [match_dec mem_s3]].
        admit.
      ===== END PORTED-BNZ-ATTEMPT ===== *)
      + Local Opaque next_state_do_updates.
        unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        repeat (apply obind_inv in NEXT as [? [?HR NEXT]]).
        destruct (mem s1 pc') as [ni|] eqn:NPC.
        2: { (* None target: JAL to the empty alloc cell (imm = alloc_label); pcs coincide *)
             simpl in NEXT.
             repeat (apply obind_inv in NEXT as [? [?HR2 NEXT]]).
             destruct x0 as [ov ev]. simpl in NEXT.
             repeat (apply obind_inv in NEXT as [? [?HR3 NEXT]]).
             move: NEXT => [= Hs1' Hev]. subst ev. subst s1'.
             have Htpc : tpc0 = Level n c0 by (move: tag_pc1; rewrite ST /=).
             Local Opaque belong.
             cbn in HR0.
             apply obind_inv in HR0 as [[] [Hic HR0]]; destruct (is_code ti0) eqn:Eic; [| discriminate Hic].
             subst tpc0. cbn in HR0.
             repeat (apply obind_inv in HR0 as [? [?HC HR0]]).
             move: HR0 => [= Hov Ho0]. subst o0.
             Local Transparent belong.
             apply obind_inv in Hic as [[] [_ Hic]].
             apply obind_inv in Hic as [out [Hout Hic]].
             apply obind_inv in Hout as [[] [Hcol Hout]].
             Local Opaque check_belong is_other.
             rewrite (hseq_eta l) (hseq_eta (hsbehead l)) in Hout.
             cbn in Hout.
             apply obind_inv in Hout as [[] [Hcb Hout]].
             cbn in Hout.
             move: Hout => [= Hout]; subst out.
             cbn in Hic; move: Hic => [= Ho]; subst o.
             rewrite -Hov in HR3 *; cbn [trpc tr] in HR3 |- *.
             rewrite -(hseq_eta (hsbehead l)) in HR3.
             have Hmem' : mem s1 (pc0 + 1)%w = Some (vret @ tret) by rewrite ST /=; exact: RA.
             have Ha4' : regs s1 (as_word (ssrint.Posz 4)) = Some (old @ told) by rewrite ST /=; exact: OLD.
             have Hcl' : reg_clear_list (regs s1) told = Some l by rewrite ST /=; exact: CLEAR.
             rewrite (jal_do_updates_result Hmem' Ha4' Hcl') in HR3.
             move: HR3; rewrite /next_state_do_update /= /updm Ha4' /= => [= Hx0].
             have Hmx0 : mem x0 = mem s1 by rewrite -Hx0.
             have Hrx0 : regs x0 = setm (regs s1) (as_word (ssrint.Posz 4)) ((pc0 + 1)%w @ InternalJump) by rewrite -Hx0.
             have Hix0 : internal x0 = internal s1 by rewrite -Hx0.
             rewrite Hmx0 Hrx0 Hix0.
             inversion pc_s1_s3 as [sA sA' Hva Hnone | sA sA' vv0 off Hsome Hoff Hpcrel].
             { subst sA. case: Hnone => Hnone _. rewrite ST /= in Hnone; rewrite PC in Hnone; discriminate. }
             subst sA sA'.
             have Hcolor : color_of s1 = c0 by rewrite ST.
             rewrite Hcolor in Hoff.
             have HPCs1 : mem s1 pc0 = Some (i @ ti0) by rewrite ST.
             edestruct (code_left pc0 i ti0 off c0) as [Xf _].
             { rewrite /is_relevant_comp; eapply side_right_in_ic;
                 [ exact col_mem1
                 | exact HPCs1
                 | (apply/eqnP; move: Hcol; by case: (eqn (color ti0) c0))
                 | rewrite Hcolor in side_eq; exact side_eq ]. }
             { exact Hoff. }
             { exact Eic. }
             { apply/eqnP; move: Hcol; by case: (eqn (color ti0) c0). }
             specialize (Xf HPCs1) as [v' [match_dec mem_s3]].
             inversion match_dec as [Hn1 Hn2 Hvv | Hd1 Hd2 | jimm dd dd' Hdi Hdi' Hmd1 Hmd3 Hcd Htagdd Hreloc].
             { exfalso; exact: (Hn1 imm INST). }
             2: { exfalso; rewrite /pc' in NPC; congruence. }
             have Hia : imm = @word_of_nat (imm_size mt) alloc_label by congruence.
             subst imm.
             have Hc0 : color ti0 = c0 by (apply/eqnP; move: Hcol; by case: (eqn (color ti0) c0)).
             have HsideL : side_of c0 = Right by (rewrite -Hcolor; exact side_eq).
             have Hcodetret : is_code tret.
             { have Hend := end_s1 pc0 (i @ ti0) HPCs1 Eic.
               case: Hend => [Hh | [v'' [Hv'' Hcv'']]].
               - have Hd : decode_instr (vala (i @ ti0)) = Some (Jal (@word_of_nat (imm_size mt) alloc_label)) by exact INST.
                 rewrite Hd in Hh. by case: Hh.
               - rewrite Hmem' in Hv''. move: Hv'' Hcv'' => [= <-]; exact id. }
             have Hrel : c0 \in domm ic
               by (eapply side_right_in_ic; [ exact col_mem1 | rewrite ST; exact PC | exact Hc0 | rewrite Hcolor in side_eq; exact side_eq ]).
             Local Transparent belong check_belong.
             assert (belong_eq : forall (cc : Component.id) m, belong cc (Some m) = (cc == LRC.color m))
               by (move=> cc [vt cm em icm]; reflexivity).
             have Hbtret : belong (color ti0) (Some tret) = true
               by (move: Hcb; rewrite /check_belong; by case: ifP).
             have Hcoltret : color tret = c0
               by (move: Hbtret; rewrite belong_eq => /eqP <-; exact: Hc0).
             Local Opaque belong check_belong.
             edestruct (code_left (pc0 + 1)%w vret tret off c0) as [Xra _].
             { rewrite /is_relevant_comp; exact Hrel. }
             { exact Hoff. }
             { exact Hcodetret. }
             { exact Hcoltret. }
             specialize (Xra Hmem') as [vra3 [match_ra mem_s3ra]].
             destruct (reg_match (as_word (ssrint.Posz 4)) (old @ told)) as [_ Yr].
             specialize (Yr Ha4') as [d3 [Hdm Hr3]].
             destruct d3 as [vd3 td3]. destruct Hdm as [Htd3 _]. subst td3.
             have Hpc3v : pc3_val = (pc0 + as_word off)%w by (move: Hpcrel; rewrite ST eq_s3 /=).
             have Hpc3t : pc3_tag = Level n c0 by (move: tag_pc3; rewrite eq_s3 /=).
             rewrite eq_s3 /= in mem_s3 mem_s3ra Hr3.
             have Hdomm3 : domm regs3 = fset (ra :: [seq word_of_nat i | i <- reg_list])
               by (move: reg_domm3; rewrite /register_domm eq_s3 /=).
             have [l3cl Hl3cl] := @reg_clear_list_total regs3 told Hdomm3.
             have Htgt3 : mem3 (swcast (@word_of_nat (imm_size mt) alloc_label)) = None.
             { rewrite swcast_word_of_nat_alloc_label.
               by move: alloc_mem_s3; rewrite /alloc_empty eq_s3 /=. }
             have HNPC' : mem s1 (swcast (@word_of_nat (imm_size mt) alloc_label)) = None
               by exact NPC.
             have HNPC3' : mem s3 (swcast (@word_of_nat (imm_size mt) alloc_label)) = None.
             { rewrite swcast_word_of_nat_alloc_label.
               by move: alloc_mem_s3; rewrite /alloc_empty. }
             have Haddr1 : address_correctness Right ((pc0 + 1)%w) InternalJump (mem s1).
             { rewrite /address_correctness. exists (vret @ tret). split; first exact Hmem'. by move=> _. }
             have Haddr3 : address_correctness Right ((pc3_val + 1)%w) InternalJump (mem s3).
             { rewrite /address_correctness. exists (vra3 @ tret). split.
               - rewrite eq_s3 Hpc3v. have -> : ((pc0 + as_word off) + 1)%w = ((pc0 + 1) + as_word off)%w by word_ac. exact mem_s3ra.
               - by move=> _. }
             have Hr3s : regs s3 (as_word (ssrint.Posz 4)) = Some (vd3 @ told) by (rewrite eq_s3; exact Hr3).
             exists (@State mt lrc_tags _ mem3 (setm regs3 (as_word (ssrint.Posz 4)) ((pc3_val + 1)%w @ InternalJump)) ((swcast (@word_of_nat (imm_size mt) alloc_label)) @ (Level n c0)) internal3).
             exists M.
             split.
             { eapply plus_one. eapply step_jal.
               - rewrite eq_s3 Hpc3t; reflexivity.
               - rewrite Hpc3v; exact mem_s3.
               - rewrite Hpc3v. have -> : ((pc0 + as_word off) + 1)%w = ((pc0 + 1) + as_word off)%w by word_ac. exact mem_s3ra.
               - exact Hd2.
               - exact Hr3.
               - exact Hl3cl.
               - (* NEXT3: forward JAL transfer for s3 with the empty (None) alloc target *)
                 have [arcom1 Hrc1] : exists a, regs s1 rcom = Some a
                   by (move: HR; rewrite /evi; case: (regs s1 rcom) => [a _|//]; by exists a).
                 have [arcom3 [_ Hrc3]] := proj2 (reg_match rcom arcom1) Hrc1.
                 have Hra3 : mem s3 (pc3_val + 1)%w = Some (vra3 @ tret).
                 { rewrite eq_s3 /= Hpc3v.
                   have -> : ((pc0 + as_word off) + 1)%w = (pc0 + 1 + as_word off)%w by word_ac.
                   exact mem_s3ra. }
                 have Hl3cl' : reg_clear_list (regs s3) told = Some l3cl by rewrite eq_s3.
                 have Htgt3' : mem s3 (swcast (@word_of_nat (imm_size mt) alloc_label)) = None
                   by (rewrite eq_s3 /=; exact Htgt3).
                 unfold next_state_updates_and_pc.
                 rewrite Htgt3'.
                 unfold next_state.
                 rewrite /evi Hrc3 /=.
                 unfold transfer, instr_rules, LRC.instr_rules.
                 rewrite Eic /= Hpc3t /= Hcol /=.
                 rewrite (hseq_eta l3cl) (hseq_eta (hsbehead l3cl)) /=.
                 Local Transparent belong.
                 rewrite Hcb /=.
                 Local Opaque belong.
                 rewrite -(hseq_eta (hsbehead l3cl)).
                 rewrite (jal_do_updates_result Hra3 Hr3s Hl3cl').
                 rewrite /next_state_do_update /= /updm Hr3s /=.
                 rewrite eq_s3 /=. reflexivity. }
             { (* equiv preserved: RA reg-write on top of the pc-increment; same_pc via the alloc rule *)
               eapply preserves_equiv_right_reg_write with
                 (s1 := @State mt lrc_tags _ (mem s1) (regs s1) ((swcast (@word_of_nat (imm_size mt) alloc_label)) @ (Level n c0)) tt)
                 (s3 := @State mt lrc_tags _ (mem s3) (regs s3) ((swcast (@word_of_nat (imm_size mt) alloc_label)) @ (Level n c0)) tt)
                 (r := as_word (ssrint.Posz 4))
                 (v := (pc0 + 1)%w @ InternalJump) (v' := (pc3_val + 1)%w @ InternalJump)
                 (r1' := setm (regs s1) (as_word (ssrint.Posz 4)) ((pc0 + 1)%w @ InternalJump))
                 (r3' := setm (regs s3) (as_word (ssrint.Posz 4)) ((pc3_val + 1)%w @ InternalJump)).
               - eapply preserves_equiv_right_pc_incr with
                   (s1 := s1) (s3 := s3)
                   (pc1' := swcast (@word_of_nat (imm_size mt) alloc_label)) (tpc1' := Level n c0)
                   (pc3' := swcast (@word_of_nat (imm_size mt) alloc_label)) (tpc3' := Level n c0).
                 + exact: (conj strong (conj weak common)).
                 + reflexivity.
                 + reflexivity.
                 + (* same_pc_alloc: both pcs are the empty alloc cell *)
                   eapply same_pc_alloc; first reflexivity.
                   split; [exact HNPC' | exact HNPC3'].
                 + exact: (esym tag_pc1).
                 + exact: (esym tag_pc3).
                 + pcc_close2 (PCCM.step_me_mp step_1) ST.
               - rewrite /data_match.
                 have Hco' : color_of (@State mt lrc_tags _ (mem s1) (regs s1) ((swcast (@word_of_nat (imm_size mt) alloc_label)) @ (Level n c0)) tt) = c0 by reflexivity.
                 rewrite Hco' Hoff /=.
                 split; first reflexivity.
                 rewrite Hpc3v. by word_ac.
               - exact I.
               - exact I.
               - exact Haddr1.
               - exact Haddr3.
               - by rewrite /updm Ha4' /=.
               - by rewrite /updm Hr3s /=.
               - by case: (internal s1).
               - have Eu : forall u : unit, u = tt by case.
                 have Em : mem3 = mem s3 by rewrite eq_s3.
                 have Er : regs3 = regs s3 by rewrite eq_s3.
                 by rewrite (Eu internal3) Em Er. } }
        simpl in NEXT.
        repeat (apply obind_inv in NEXT as [? [?HR2 NEXT]]).
        destruct x0 as [ov ev]. simpl in NEXT.
        repeat (apply obind_inv in NEXT as [? [?HR3 NEXT]]).
        move: NEXT => [= Hs1' Hev]. subst ev. subst s1'.
        have Htpc : tpc0 = Level n c0 by (move: tag_pc1; rewrite ST /=).
        Local Opaque belong.
        cbn in HR0.
        apply obind_inv in HR0 as [[] [Hic HR0]]; destruct (is_code ti0) eqn:Eic; [| discriminate Hic].
        subst tpc0. cbn in HR0.
        repeat (apply obind_inv in HR0 as [? [?HC HR0]]).
        move: HR0 => [= Hov Ho0]. subst o0.
        Local Transparent belong.
        apply obind_inv in Hic as [[] [_ Hic]].
        apply obind_inv in Hic as [out [Hout Hic]].
        apply obind_inv in Hout as [[] [Hcol Hout]].
        Local Opaque belong check_belong is_other.
        rewrite (hseq_eta l) (hseq_eta (hsbehead l)) in Hout.
        cbn in Hout.
        apply obind_inv in Hout as [[] [Hcb Hout]].
        destruct (belong (match ti0 with | {| color := c |} => c end) (Some (taga ni))) eqn:Hbel.
        * rewrite Hbel in Hout; cbn in Hout.
          move: Hout => [= Hout]; subst out.
          cbn in Hic; move: Hic => [= Ho]; subst o.
          rewrite -Hov in HR3 *; cbn [trpc tr] in HR3 |- *.
          rewrite -(hseq_eta (hsbehead l)) in HR3.
          have Hmem' : mem s1 (pc0 + 1)%w = Some (vret @ tret) by rewrite ST /=; exact: RA.
          have Ha4' : regs s1 (as_word (ssrint.Posz 4)) = Some (old @ told) by rewrite ST /=; exact: OLD.
          have Hcl' : reg_clear_list (regs s1) told = Some l by rewrite ST /=; exact: CLEAR.
          rewrite (jal_do_updates_result Hmem' Ha4' Hcl') in HR3.
          move: HR3; rewrite /next_state_do_update /= /updm Ha4' /= => [= Hx0].
          have Hmx0 : mem x0 = mem s1 by rewrite -Hx0.
          have Hrx0 : regs x0 = setm (regs s1) (as_word (ssrint.Posz 4)) ((pc0 + 1)%w @ InternalJump) by rewrite -Hx0.
          have Hix0 : internal x0 = internal s1 by rewrite -Hx0.
          rewrite Hmx0 Hrx0 Hix0.
          inversion pc_s1_s3 as [sA sA' Hva Hnone | sA sA' vv0 off Hsome Hoff Hpcrel].
          { subst sA. case: Hnone => Hnone _. rewrite ST /= in Hnone; rewrite PC in Hnone; discriminate. }
          subst sA sA'.
          have Hcolor : color_of s1 = c0 by rewrite ST.
          rewrite Hcolor in Hoff.
          have HPCs1 : mem s1 pc0 = Some (i @ ti0) by rewrite ST.
          edestruct (code_left pc0 i ti0 off c0) as [Xf _].
          { rewrite /is_relevant_comp; eapply side_right_in_ic;
              [ exact col_mem1
              | exact HPCs1
              | (apply/eqnP; move: Hcol; by case: (eqn (color ti0) c0))
              | rewrite Hcolor in side_eq; exact side_eq ]. }
          { exact Hoff. }
          { exact Eic. }
          { apply/eqnP; move: Hcol; by case: (eqn (color ti0) c0). }
          specialize (Xf HPCs1) as [v' [match_dec mem_s3]].
          inversion match_dec as [Hn1 Hn2 Hvv | Hd1 Hd2 | jimm dd dd' Hdi Hdi' Hmd1 Hmd3 Hcd Htagdd Hreloc].
          { exfalso; exact: (Hn1 imm INST). }
          { (* alloc JAL: contradiction — the jump target would be the (empty) alloc cell *)
            exfalso.
            have Hia : imm = @word_of_nat (imm_size mt) alloc_label by congruence.
            rewrite /pc' Hia swcast_word_of_nat_alloc_label in NPC.
            have Hae : mem s1 (word_of_nat alloc_label) = None by exact: alloc_mem_s1.
            rewrite Hae in NPC. discriminate NPC. }
          (* main JAL case: dd = s3's immediate; relocation H *)
          have Hji : jimm = imm by congruence.
          subst jimm.
          have Hc0 : color ti0 = c0 by (apply/eqnP; move: Hcol; by case: (eqn (color ti0) c0)).
          have HsideL : side_of c0 = Right by (rewrite -Hcolor; exact side_eq).
          have Hdef : dd' = ni by (move: NPC; rewrite /pc' => NPC'; congruence).
          Local Transparent belong.
          have Hcolni : color (taga dd') = c0.
          { rewrite Hdef. move: Hbel; rewrite /belong /=.
            case: (taga ni) => [vt cc ee ic] /=. move/eqP => Heq. by rewrite -Heq; exact: Hc0. }
          Local Opaque belong.
          have Hgo : get_offset (side_of (color (taga dd'))) (color (taga dd')) = Some off
            by (rewrite Hcolni HsideL; exact Hoff).
          have Hsg : side_of (color (taga dd')) = Right by rewrite Hcolni; exact HsideL.
          have Hreloc2 := H Hsg off Hgo.
          have Hcodetret : is_code tret.
          { have Hend := end_s1 pc0 (i @ ti0) HPCs1 Eic.
            case: Hend => [Hh | [v'' [Hv'' Hcv'']]].
            - have Hd : decode_instr (vala (i @ ti0)) = Some (Jal imm) by exact INST.
              rewrite Hd in Hh. by case: Hh.
            - rewrite Hmem' in Hv''. move: Hv'' Hcv'' => [= <-]; exact id. }
          have Hrel : c0 \in domm ic
            by (eapply side_right_in_ic; [ exact col_mem1 | exact HPCs1 | exact Hc0 | exact HsideL ]).
          Local Transparent belong check_belong.
          assert (belong_eq : forall (cc : Component.id) m, belong cc (Some m) = (cc == LRC.color m))
            by (move=> cc [vt cm em icm]; reflexivity).
          have Hbtret : belong (color ti0) (Some tret) = true
            by (move: Hcb; rewrite /check_belong; by case: ifP).
          have Hcoltret : color tret = c0
            by (move: Hbtret; rewrite belong_eq => /eqP <-; exact: Hc0).
          Local Opaque belong check_belong.
          edestruct (code_left (pc0 + 1)%w vret tret off c0) as [Xra _].
          { rewrite /is_relevant_comp; exact Hrel. }
          { exact Hoff. }
          { exact Hcodetret. }
          { exact Hcoltret. }
          specialize (Xra Hmem') as [vra3 [match_ra mem_s3ra]].
          destruct (reg_match (as_word (ssrint.Posz 4)) (old @ told)) as [_ Yr].
          specialize (Yr Ha4') as [d3 [Hdm Hr3]].
          destruct d3 as [vd3 td3]. destruct Hdm as [Htd3 _]. subst td3.
          have Hpc3v : pc3_val = (pc0 + as_word off)%w by (move: Hpcrel; rewrite ST eq_s3 /=).
          have Hpc3t : pc3_tag = Level n c0 by (move: tag_pc3; rewrite eq_s3 /=).
          rewrite eq_s3 /= in mem_s3 mem_s3ra Hr3.
          have Hdomm3 : domm regs3 = fset (ra :: [seq word_of_nat i | i <- reg_list])
            by (move: reg_domm3; rewrite /register_domm eq_s3 /=).
          have [l3cl Hl3cl] := @reg_clear_list_total regs3 told Hdomm3.
          have Haddr1 : address_correctness Right ((pc0 + 1)%w) InternalJump (mem s1).
          { rewrite /address_correctness. exists (vret @ tret). split; first exact Hmem'. by move=> _. }
          have Haddr3 : address_correctness Right ((pc3_val + 1)%w) InternalJump (mem s3).
          { rewrite /address_correctness. exists (vra3 @ tret). split.
            - rewrite eq_s3 Hpc3v. have -> : ((pc0 + as_word off) + 1)%w = ((pc0 + 1) + as_word off)%w by word_ac. exact mem_s3ra.
            - by move=> _. }
          have Hr3s : regs s3 (as_word (ssrint.Posz 4)) = Some (vd3 @ told) by (rewrite eq_s3; exact Hr3).
          exists (@State mt lrc_tags _ mem3 (setm regs3 (as_word (ssrint.Posz 4)) ((pc3_val + 1)%w @ InternalJump)) ((swcast dd) @ (Level n c0)) internal3).
          exists M.
          split.
          { eapply plus_one. eapply step_jal.
            - rewrite eq_s3 Hpc3t; reflexivity.
            - rewrite Hpc3v; exact mem_s3.
            - rewrite Hpc3v.
              have -> : ((pc0 + as_word off) + 1)%w = ((pc0 + 1) + as_word off)%w by word_ac.
              exact mem_s3ra.
            - exact Hmd1.
            - exact Hr3.
            - exact Hl3cl.
            - (* NEXT3: forward JAL transfer for the s3 run *)
              have [arcom1 Hrc1] : exists a, regs s1 rcom = Some a
                by (move: HR; rewrite /evi; case: (regs s1 rcom) => [a _|//]; by exists a).
              have [arcom3 [_ Hrc3]] := proj2 (reg_match rcom arcom1) Hrc1.
              have Hra3 : mem s3 (pc3_val + 1)%w = Some (vra3 @ tret).
              { rewrite eq_s3 /= Hpc3v.
                have -> : ((pc0 + as_word off) + 1)%w = (pc0 + 1 + as_word off)%w by word_ac.
                exact mem_s3ra. }
              have Hl3cl' : reg_clear_list (regs s3) told = Some l3cl by rewrite eq_s3.
              have Hcolhdi : color (taga Hdi) = c0 by rewrite -Hreloc Hcolni.
              unfold next_state_updates_and_pc.
              rewrite Hcd.
              unfold next_state.
              rewrite /evi Hrc3 /=.
              unfold transfer, instr_rules, LRC.instr_rules.
              have Htdi : taga Hdi = taga ni by rewrite -Hreloc Hdef.
              rewrite Eic /= Hpc3t /= Hcol /=.
              rewrite (hseq_eta l3cl) (hseq_eta (hsbehead l3cl)) /=.
              rewrite Hcb /= Htdi Hbel /=.
              rewrite -(hseq_eta (hsbehead l3cl)).
              rewrite (jal_do_updates_result Hra3 Hr3s Hl3cl').
              rewrite /next_state_do_update /= /updm Hr3s /=.
              rewrite eq_s3 /=. reflexivity. }
          { (* equiv preserved: RA reg-write on top of the pc-increment *)
            eapply preserves_equiv_right_reg_write with
              (s1 := @State mt lrc_tags _ (mem s1) (regs s1) ((swcast imm) @ (Level n c0)) tt)
              (s3 := @State mt lrc_tags _ (mem s3) (regs s3) ((swcast dd) @ (Level n c0)) tt)
              (r := as_word (ssrint.Posz 4))
              (v := (pc0 + 1)%w @ InternalJump) (v' := (pc3_val + 1)%w @ InternalJump)
              (r1' := setm (regs s1) (as_word (ssrint.Posz 4)) ((pc0 + 1)%w @ InternalJump))
              (r3' := setm (regs s3) (as_word (ssrint.Posz 4)) ((pc3_val + 1)%w @ InternalJump)).
            - (* equiv triple, via the pc-increment lemma *)
              eapply preserves_equiv_right_pc_incr with
                (s1 := s1) (s3 := s3)
                (pc1' := swcast imm) (tpc1' := Level n c0) (pc3' := swcast dd) (tpc3' := Level n c0).
              + exact: (conj strong (conj weak common)).
              + reflexivity.
              + reflexivity.
              + (* same_pc Right between the two jumped-to pcs *)
                eapply same_pc_normal.
                * split; [exact NPC | rewrite -Hdef; exact Htagdd].
                * exact Hoff.
                * exact Hreloc2.
              + exact: (esym tag_pc1).
              + exact: (esym tag_pc3).
              + pcc_close2 (PCCM.step_me_mp step_1) ST.
            - (* data_match for the RA cell (an InternalJump value) *)
              rewrite /data_match.
              have Hco' : color_of (@State mt lrc_tags _ (mem s1) (regs s1) ((swcast imm) @ (Level n c0)) tt) = c0 by reflexivity.
              rewrite Hco' Hoff /=.
              split; first reflexivity.
              rewrite Hpc3v. by word_ac.
            - (* capability_correctness' WS_S1 (InternalJump tag) *) exact I.
            - (* capability_correctness' WS_S3 (InternalJump tag) *) exact I.
            - (* address_correctness Right, s1 side *) exact Haddr1.
            - (* address_correctness Right, s3 side *) exact Haddr3.
            - (* updm s1 *) by rewrite /updm Ha4' /=.
            - (* updm s3 *) by rewrite /updm Hr3s /=.
            - (* eq_s1' *) by case: (internal s1).
            - (* eq_s3' *)
              have Eu : forall u : unit, u = tt by case.
              have Em : mem3 = mem s3 by rewrite eq_s3.
              have Er : regs3 = regs s3 by rewrite eq_s3.
              by rewrite (Eu internal3) Em Er.
          }
        * rewrite Hbel in Hout; cbn in Hout.
          apply obind_inv in Hout as [[] [_ Hout]].
          apply obind_inv in Hout as [cc [_ Hout]].
          apply obind_inv in Hout as [[] [Hce Hout]].
          move: Hout => [= Hout]; subst out.
          cbn in Hic; move: Hic => [= _ Hev].
          move: Hce Hev; case: (taga ni) => [vt col ent ic] /=.
          case: ent => [[pr ll0]|].
          { by move=> _ [=]. }
          { by move=> [=]. }
        Local Transparent belong check_belong is_other next_state_do_updates.
      (* ===== syscall opcode (ported from reference body) — equiv is the genuine alloc_fun lemma ===== *)
      + (* syscall (alloc_fun): clean reconstruction — no unfold_all/simpl in * *)
        Local Opaque alloc_fun evi.
        have Hsem : Symbolic.sem sc = alloc_fun (NC := NC).
        { move: GETCALL. rewrite /Instance.table /Merged.table mkfmapE /=.
          case: ifP => [_ [= <-] // | _ ]. by move=> [=]. }
        have Halloc1 : alloc_fun (NC := NC) s1 = Some s1'.
        { move: CALL. rewrite /run_syscall Hsem /= => H.
          case: (obind_inv H) => i [_ {}H].
          case: (obind_inv H) => s [Hs] [= <-]. exact Hs. }
        Local Transparent alloc_fun evi.
        have [s3' s3'_eq] : exists s3', alloc_fun (NC := NC) s3 = Some s3'.
        { move: Halloc1. rewrite {1}/alloc_fun => H1.
          case: (obind_inv H1) => ra_val [Hra1 {}H1].
          case: (obind_inv H1) => u1 [Hjmp1 {}H1].
          case: (obind_inv H1) => reta1 [Hreta1 {}H1].
          case: (obind_inv H1) => ureta1 [Hretchka1 {}H1].
          move: Hretchka1; case: ifP => Hretcola1 Hretchka1; last by []; clear ureta1 Hretchka1.
          case: (obind_inv H1) => sz [Hsz1 {}H1].
          case: (obind_inv H1) => u2 [Hoth1 {}H1].
          case: (obind_inv H1) => len [Hlen1 {}H1].
          case: (obind_inv H1) => uchk1 [Hszchk1 {}H1].
          have Hszbnd : leq (len + 1) (expn 2 (word_size mt - NC)) = true.
          { case E: (leq (len + 1) (expn 2 (word_size mt - NC))) => //.
            rewrite E /= in Hszchk1; discriminate Hszchk1. }
          move: H1; case: ifP => // Hchk1 H1.
          case: (obind_inv H1) => addr1 [Haddr1 {}H1].
          move: H1; rewrite /updm.
          case Hret1 : (regs s1 syscall_ret) => [retv|] //= _.
          case: (proj2 (reg_match ra ra_val) Hra1) => d_ra [Hdm_ra Hra3].
          case: (proj2 (reg_match syscall_arg1 sz) Hsz1) => d_sz [Hdm_sz Hsz3].
          case: (proj2 (reg_match syscall_ret retv) Hret1) => d_ret [Hdm_ret Hret3].
          (* tag/value facts that transfer the reads onto s3 *)
          have E_rat : taga ra_val = InternalJump
            by move: Hjmp1; rewrite /is_jump; case: (taga ra_val).
          have E_sat : taga sz = Other
            by move: Hoth1; rewrite /is_other; case: (taga sz).
          have E_drat : taga d_ra = InternalJump
            by rewrite -(data_match_taga Hdm_ra) E_rat.
          have E_dsat : taga d_sz = Other
            by rewrite -(data_match_taga Hdm_sz) E_sat.
          have E_dsv := data_match_other_val E_sat Hdm_sz.
          have Hcolor : color_of s1 = c0.
          { by move: tag_pc1; rewrite ST /color_of /= => ->. }
          have Hdomm :
            List.filter
              (fun mw : word (word_size mt) => andw mw (@mask mt NC) ==
                 @component_memory_prefix mt NC (ssrint.Posz (1 + c0))) (domm (mem s1))
          = List.filter
              (fun mw : word (word_size mt) => andw mw (@mask mt NC) ==
                 @component_memory_prefix mt NC (ssrint.Posz (1 + c0))) (domm (mem s3)).
          { eapply (match_mem_pref_condition_filter_eq (i := Right) (c := c0));
              [ apply: (is_relevant_comp_of_side Hcval); by rewrite -Hcolor
              | eauto | eauto | eauto ]. }
          have Hcc1 : (match taga (pc s1) with Level _ c => c end) = c0 by rewrite tag_pc1.
          have Hcc3 : (match taga (pc s3) with Level _ c => c end) = c0 by rewrite tag_pc3.
          (* s3 return-addr check: the [&&] alloc-check forces s1's return cell to be running CODE,
             so [code_left] (= combined_codes Right s1 s3) maps it to s3's return cell with the SAME
             tag, discharging s3's check. *)
          move: (Hretcola1); rewrite Hcc1 => /andP [Hic1 /eqP Hcol1].
          have Hext : forall (a b : atom (mword mt) (tag_type lrc_tags R)),
              taga a = InternalJump -> data_match Right c0 M a b ->
              exists off, get_offset Right c0 = Some off /\ vala b = addw (vala a) (as_word off).
          { move=> [av at0] [bv bt0] /= Hat Hdm; subst at0.
            move: Hdm; rewrite /data_match /= => -[_ Hop].
            move: Hop; case Ho: (offset2 c0) => [off|] //= Hb.
            exists off; split; [ by rewrite /get_offset | rewrite /=; exact Hb ]. }
          have Hdm_ra2 := Hdm_ra. rewrite Hcolor in Hdm_ra2.
          have [off [Hoff Haddrv]] := Hext ra_val d_ra E_rat Hdm_ra2.
          have Hrelc0 : is_relevant_comp Right c0.
          { rewrite /is_relevant_comp.
            case/orP: Hcval => [Hip | Hic]; last exact Hic.
            exfalso.
            have side_c0 : side_of (color_of s1) = Right by (destruct strong).
            by move: side_c0; rewrite (color_of_pc_tag s1) tag_pc1 /side_of Hip. }
          have Hreta1' : mem s1 (vala ra_val) = Some ((vala reta1) @ (taga reta1))
            by rewrite Hreta1; case: (reta1) => ? ? /=.
          have [vr3 [_ Hret3a]] :=
            proj1 (code_left (vala ra_val) (vala reta1) (taga reta1) off c0 Hrelc0 Hoff Hic1 Hcol1) Hreta1'.
          have Hretmem3 : mem s3 (vala d_ra) = Some (vr3 @ (taga reta1)) by rewrite Haddrv.
          have Hretchk3 : (is_code (taga reta1) && (color (taga reta1) == c0)) = true
            by rewrite Hcol1 eqxx andbT; exact Hic1.
          have Hck3 : (if is_code (taga (vr3 @ (taga reta1))) && (color (taga (vr3 @ (taga reta1))) == c0)
                       then Some tt else None) = Some tt by rewrite /= Hretchk3.
          rewrite Hcc1 Hdomm in Hchk1 Haddr1.
          rewrite /alloc_fun Hcc3.
          rewrite Hra3 obindE; cbn beta.
          rewrite E_drat is_jumpE obindE; cbn beta.
          rewrite Hretmem3 obindE; cbn beta.
          rewrite Hck3 obindE; cbn beta.
          rewrite Hsz3 obindE; cbn beta.
          rewrite E_dsat is_otherE obindE; cbn beta.
          rewrite -E_dsv Hlen1 obindE; cbn beta.
          have Htt : (if leq (len + 1) (expn 2 (word_size mt - NC)) then Some tt else None) = Some tt
            by rewrite Hszbnd.
          rewrite Htt obindE; cbn beta.
          rewrite Hchk1.
          rewrite Haddr1 obindE; cbn beta.
          have Hupd3 : updm (regs s3) syscall_ret (addr1 @ Other)
                     = Some (setm (regs s3) syscall_ret (addr1 @ Other))
            by rewrite /updm Hret3.
          rewrite Hupd3 obindE; cbn beta.
          by eexists. }
        Local Opaque alloc_fun.
        (* s3 fires the same alloc syscall (shared entry pc), reaching s3' *)
        have Hpc0 : pc0 = word_of_nat alloc_label.
        { move: GETCALL; rewrite /Instance.table /Merged.table mkfmapE /=.
          by case: ifP => [/eqP|]. }
        have Hpcs1 : vala (pc s1) = pc0 by rewrite ST.
        have Hmem1 : mem s1 (vala (pc s1)) = None by rewrite ST /=.
        have Hpc3v : vala (pc s3) = pc3_val by rewrite eq_s3.
        have Hpc3 : vala (pc s3) = vala (pc s1).
        { symmetry. move: pc_s1_s3 Hmem1 => H Hn.
          inversion H as [? ? Hva Hno | ? ? ? ? Hcj Hoo Hpp]; [ assumption | case: Hcj => Hcj _; congruence ]. }
        have Hpc3val : pc3_val = word_of_nat alloc_label
          by rewrite -Hpc3v Hpc3 Hpcs1 Hpc0.
        exists s3', M. split.
        { apply: plus_one. eapply step_syscall.
          { exact eq_s3. }
          { rewrite Hpc3val. by move: alloc_mem_s3; rewrite /alloc_empty eq_s3 /=. }
          { rewrite Hpc3val -Hpc0. exact GETCALL. }
          rewrite /run_syscall Hsem.
          have [a1 Ha1] : exists a1, regs s1 rcom = Some a1.
          { move: CALL; rewrite /run_syscall /evi.
            by case Hr: (regs s1 rcom) => [a1|] // _; exists a1. }
          case: (proj2 (reg_match rcom a1) Ha1) => a3 [_ Ha3].
          by rewrite /evi Ha3 /= s3'_eq. }
        eapply preserves_equiv_right_alloc_fun; eauto.
  Time Qed.

End StepStrong2.
