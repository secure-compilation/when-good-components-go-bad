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

Module StepStrong (S: RecompositionContext).

  Module Defs := RecompositionDefinitions S.
  Module Pres := Preservation S.
  Include Pres.



  Lemma step_silent_strong1:
    forall s1 s1', Step sem s1 E0 s1' ->
    forall s2 s3 M, strong_equiv Left M s1 s3 ->
               weak_equiv Right M s2 s3 ->
               common_equiv M s1 s2 s3 ->
    exists s3' M', Plus sem'' s3 E0 s3' /\ (* Using Plus to ensure the strongly related states take a step *)
              strong_equiv Left M' s1' s3' /\
              weak_equiv Right M' s2 s3' /\
              common_equiv M' s1' s2 s3'.
  Proof.
    import_context.
    intros s1 s1' step_s1 s2 s3 M strong weak common. simpl in step_s1.
    remember E0 as t.
    destruct step_s1 as [s1 ? s1' step_2 allowed | s1 ? s1' step_1 step_2]; subst t.
    - unfold allowed_UB in *.
      inversion strong as [m ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor _ s_reg_cor s'_reg_cor mem_match reg_match].
      subst m s s'.
      exfalso. eapply Machine.Intermediate.fdisjoint_partition_notinboth.
      * inversion Hmergeable_ifaces as [[_ fdisj] _]. exact fdisj.
      * exact allowed.
      * unfold side_of in *. unfold_match' side_eq.
    - remember (id s3) as s3'; simpl in Heqs3'; destruct s3' as [mem3 regs3 [pc3_val pc3_tag] internal3 cn3].
      rewrite Heqs3' in strong weak common; rewrite Heqs3'. pose proof (esym Heqs3') as eq_s3.
      inversion strong as [? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor _ s_reg_cor s'_reg_cor mem_match reg_match].
      inversion common as [? ? ? ? n ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          [mem_pref_cond_s1 [mem_pref_cond_s1' [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 entry_code1]]]]]]]
                          [mem_pref_cond_s2 [mem_pref_cond_s2' [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 entry_code2]]]]]]]
                          [mem_pref_cond_s3 [mem_pref_cond_s3' [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 entry_code3]]]]]]]
                          capa_cor1 capa_cor2 capa_cor3 code_left code_right].
      subst s s' s0 s4 s5 m m0.
      inversion step_1; unfold step1;
        unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
      all: unfold_all; try unfold_match; unfold_all.
      all: try (clear -Heqa2; repeat unfold_match' Heqa2; done); simpl in *. (* eliminates many goals *)
      all: try (rewrite ST in PC_None; unfold color_of in PC_None; rewrite PC in PC_None; try (inversion PC_None; done || clear PC_None)).
      all: try (assert (tpc1 = tpc0) by (clear -Heqa2; unfold_match' Heqa2); subst tpc1).
      all: try (assert (ts0 = (ts (mvec None)) ) by
               (unfold mvec in *; simpl; clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                destruct Heqa2 as [_ _ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ts0).
      all: try (unfold mvec in *; assert (ti1 = ti0) by
                  (clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                   destruct Heqa2 as [_ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ti1).
      all: try (rewrite ST in end_s1 Heqa2; simpl in end_s1, Heqa2;
                destruct (end_s1 pc0 _ PC) as [ instr_is_halt | [[i' ti'] [Heqi' code_i']]];
                [destruct ti0; simpl in *; auto; try unfold_match' Heqa5; try done |
                  (match goal with
                   | op: _ = op_of_word _, inst: instr_of_args _ = _ |- _
                     => simpl in instr_is_halt;  rewrite <- op in instr_is_halt; simpl in instr_is_halt;
                       rewrite inst in instr_is_halt; done end) |
                  simpl in Heqi'; try (rewrite Heqi' in Heqa2; inversion Heqa2) ] ).
      all: unfold check_belong, belong, reg_clear_list in *.
      all: simpl in *; unfold_all.
      7-8: (match (type of Heqa2) with
                  (_ = match ?m ?w with _ => _ end)
                  => eapply (@modusponens (exists res, m w = Some res /\
                                                   (LRC.color (taga res) \in domm ip ->
                                                                   is_code (taga res))));
                    [|intros [res [res_eq res_code]]; rewrite res_eq in Heqa2]
                end).
      11: remember (mem0 pc') as next_pc_content; destruct next_pc_content.
      all: try (match goal with
                  |- exists _ _, _ => repeat (unfold_all || unfold_match || rewrite orb_false_r in Heqa4, Heqa16) end).
      all: convert_eq_op.
      all: unfold is_jump in *; try (unfold_match; subst t1).
      all: unfold hshead in *; simpl in *.
      all: try (inversion Heqa0); clear Heqs3'; revert ST eq_s3; subst; intros ST eq_s3. (* trick to keep an equality on s1 and s3 *)
      all: try (pose proof (esym Heqa3) as PC; clear Heqa3).
      all: try (match goal with c: Component.id |- _ => rename c into color end).
      all: try (destruct pc_s1_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s1_s3];
                [exfalso; subst; simpl in *; rewrite eq_none in PC; done |]).
      all: try (assert (color_of s1 = c0) as eq by (unfold color_of; subst; simpl; clear -tag_pc1; destruct tpc0; simpl in *; congruence);
                subst c0).
      all: try (destruct tpc0; unfold_all).
      all: try (unfold compatible in *; rewrite eq in m_compat).
      all: try rewrite m_compat in side_eq.
      + eexists; exists M. simpl.
        split.
        * eapply (plus_left _ [::]). try eapply step_nop; eauto.
          -- eapply (etrans _ PC).
          -- decode_instr_eq.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. simpl. unfold_bind.
             deduce_reg reg_match.
             assert (mem3 (addw pc3_val onew) = mem0 (addw pc0 onew)). eapply (etrans _ (esym Heqi')).
             rewrite eq_s3. simpl. rewrite H1 Heqi'. simpl. rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3.
             clear tag_pc1. rewrite ST. unfold color_of. simpl. rewrite eq_refl. simpl.
             unfold check_belong, belong. rewrite eq_refl. simpl. trivial.
          -- eapply star_refl.
          -- done.
        * eapply (preserves_equiv_left_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)) (tpc1' := (taga (pc s1)))
                                                     (pc3' := (addw (vala (pc s3)) onew)) (tpc3' := (taga (pc s3))); eauto.
          -- rewrite ST. simpl. done.
          -- rewrite eq_s3. simpl. done.
          -- rewrite ST. eapply same_pc_normal; simpl; eauto.
             ++ subst. unfold color_of in * . simpl in *. exact eq_off.
             ++ subst. simpl in *. rewrite pc_s1_s3. simpl. rewrite <- (addwA pc0 _).
                rewrite (addwC (as_word _) onew). rewrite addwA. done.
      + eexists; exists M. simpl.
        split.
        * eapply (plus_left _ [::]); try eapply step_const; eauto.
          -- eapply (etrans _ (PC)).
          -- decode_instr_eq.
          -- eapply (etrans _ (OLD)).
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_all.
             deduce_reg reg_match.
             assert (mem3 (addw pc3_val onew) = mem0 (addw pc0 onew)). eapply (etrans _ (esym Heqi')).
             rewrite eq_s3. rewrite H1 Heqi'. simpl. unfold check_belong, belong. rewrite eq_refl. simpl.
             rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3. rewrite ST. unfold color_of. simpl. rewrite eq_refl. simpl.
             (let H := fresh "H" in
               let v := fresh "v" in
               match goal with
               | |- context [updm ?r ?w _] =>
                   assert (exists v, (r w = Some v)) as [v H]; [| unfold updm; rewrite H; clear H] end).
             { subst. deduce_reg reg_match. eauto. }
             simpl. done.
          -- eapply star_refl.
          -- done.
        * eapply preserves_equiv_left_reg_write with (r := r) (v := (swcast n0)@Other) (v' := (swcast n0)@Other); auto.
          eapply (preserves_equiv_left_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)) (tpc1' := (taga (pc s1)))
                                                     (pc3' := (addw (vala (pc s3)) onew)) (tpc3' := (taga (pc s3))); eauto.
          all: try (split; done).
          -- subst. simpl. eapply same_pc_normal.
             simpl. eauto.
             subst. unfold color_of in *. simpl in *. eauto.
             simpl in *. rewrite pc_s1_s3. simpl. rewrite <- (addwA pc0 _). rewrite (addwC (as_word _) onew). rewrite addwA. done.
          -- unfold updm. simpl.
             rewrite ST OLD. simpl. done.
          -- unfold updm. simpl. subst. deduce_reg reg_match. done.
          -- simpl. rewrite ST. simpl. done.
          -- subst. simpl. done.
      + deduce_equality OLD.
        deduce_equality R1W.
        eexists. exists M. simpl.
        remember (@eq_op (Ord.eqType _) r2 r1) as cond.
        split.
        * eapply (plus_left _ [::]); try eapply step_mov. eauto.
          -- eapply (etrans _ (PC)).
          -- decode_instr_eq.
          -- rewrite eq_s3 in vt_eq0. eauto.
          -- rewrite eq_s3 in vt_eq. eauto.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_all.
             deduce_reg reg_match.
             subst s3 s1. simpl in *. simpl in *.
             unfold side_of in side_eq. unfold_match' side_eq.
             deduce_equality Heqi'.
             rewrite vt_eq1. simpl.
             unfold check_belong, belong. rewrite eq_refl. simpl.
             unfold updm. rewrite vt_eq0. simpl.
             try rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3. try rewrite ST. unfold color_of. simpl. rewrite eq_refl. simpl.
             repeat rewrite setmE. simpl in Heqcond.
             rewrite <- Heqcond. destruct cond.
             ++ assert (r_eq: r2 = r1) by (eq_op_to_eq). simpl in *. simpl. trivial.
             ++ deduce_reg reg_match. done.
          -- destruct cond; eapply star_refl.
          -- done.
        * inversion vt_match0 as [? _]. subst t0. unfold_all.
          rewrite ST in Heqa11. simpl in Heqa11. rewrite R1W in Heqa11. simplify_some.
          rewrite ST. simpl. remember (if is_address t1 then Invalidated else Other) as new_t1.
          eapply preserves_equiv_left_reg_write with (r := r2) (v := w1@t1) (v' := v1@t1).
          eapply preserves_equiv_left_reg_write with (r := r1) (v := w1@new_t1) (v' := (v1@new_t1)).
          eapply (preserves_equiv_left_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)) (tpc1' := (taga (pc s1)))
                                                     (pc3' := (addw (vala (pc s3)) onew)) (tpc3' := (taga (pc s3))); auto. eauto.
          all: simpl; try trivial.
          all: unfold updm.
          all: try done.
          -- subst. simpl. eapply same_pc_normal.
             simpl. eauto.
             simpl. eauto. simpl in *.
             rewrite pc_s1_s3. simpl. rewrite <- (addwA pc0 _). rewrite (addwC (as_word _) onew). rewrite addwA. done.
          -- split; auto. subst. destruct t1; simpl; auto. destruct vt_match0. auto.
          -- subst. destruct t1; simpl; auto.
          -- subst. destruct t1; simpl; auto.
          -- subst new_t1. destruct t1; simpl; trivial.
          -- subst new_t1. destruct t1; simpl; trivial.
          -- subst new_t1. destruct t1; simpl; trivial.
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
          -- inversion weak as [? ? ? _ _ _ _ _ s'_reg_cor' _].
             subst. simpl. eapply (s'_reg_cor' _ _ vt_eq0).
          -- repeat rewrite setmE. rewrite <- Heqcond. destruct cond; subst; simpl; try done.
             rewrite OLD. simpl. done.
          -- repeat rewrite setmE. rewrite <- Heqcond. destruct cond; subst; simpl; try done.
             deduce_reg reg_match. done.
          -- simpl. subst. trivial.
          -- subst. simpl. trivial.
      + deduce_equality OLD.
        deduce_equality R1W.
        deduce_equality R2W.
        remember (@eq_op (Ord.eqType _) r2 r1) as cond.
        remember (@eq_op (Ord.eqType _) r3 r1) as cond1.
        remember (@eq_op (Ord.eqType _) r3 r2) as cond2.
        destruct vt_match0 as [? match_t1]. subst t0. destruct t1; unfold is_other in *; try congruence. subst v1.
        destruct vt_match1 as [? match_t3]. subst t2. destruct t3; unfold is_other in *; try congruence. subst v2.
        eexists. exists M. simpl.
        split.
        * eapply (plus_left _ [::]); try eapply step_binop. eauto.
          -- eapply (etrans _ (PC)).
          -- decode_instr_eq.
          -- rewrite eq_s3 in vt_eq0. eauto.
          -- rewrite eq_s3 in vt_eq1. eauto.
          -- rewrite eq_s3 in vt_eq. eauto.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_all.
             deduce_reg reg_match.
             unfold side_of in side_eq. unfold_match' side_eq. subst s1 s3. simpl in *. deduce_equality Heqi'.
             rewrite vt_eq2. simpl.
             unfold check_belong, belong. rewrite eq_refl. simpl.
             unfold updm. rewrite vt_eq0. simpl.
             try rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3. try rewrite ST. unfold color_of. simpl. rewrite eq_refl. simpl.
             repeat rewrite setmE. simpl in Heqcond, Heqcond1, Heqcond2. unfold stack_value in *. simpl in *. rewrite <- vt_eq0.
             rewrite <- Heqcond. destruct cond; simpl.
             ++ assert (r_eq: r2 = r1) by (eq_op_to_eq). rewrite r_eq in vt_eq1. rewrite vt_eq1. simpl.
                repeat rewrite setmE.
                rewrite <- Heqcond2. destruct cond2; simpl; try done.
                rewrite <- Heqcond1. destruct cond1; simpl; try done.
                rewrite vt_eq. simpl. done.
             ++ rewrite vt_eq1. simpl. repeat rewrite setmE.
                rewrite <- Heqcond2. destruct cond2; simpl; try done.
                rewrite <- Heqcond1. destruct cond1; simpl; try done.
                deduce_reg reg_match. done.
          -- eapply star_refl.
          -- done.
        * rewrite ST in Heqa11. simpl in Heqa11. rewrite R1W in Heqa11. simplify_some.
          assert (eq_a: a = (if cond then w1 else w2)@Other).
          { repeat rewrite setmE in Heqa12. simpl in *. rewrite <- Heqcond in Heqa12.
            subst s1. rewrite R2W in Heqa12. destruct cond; simplify_some; done. }
          destruct a as [w' t']. inversion eq_a. clear eq_a. subst t'. rewrite <- H1. simpl.
          remember (binop_denote op0 w1 w2) as new_w.
          eapply preserves_equiv_left_reg_write with (r := r3) (v := new_w@Other) (v' := new_w@Other).
          eapply preserves_equiv_left_reg_write with (r := r2) (v := w'@Other) (v' := w2@Other).
          eapply preserves_equiv_left_reg_write with (r := r1) (v := w1@Other) (v' := w1@Other).
          eapply (preserves_equiv_left_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)) (tpc1' := (taga (pc s1)))
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
          all: try trivial.
          -- rewrite ST. eapply same_pc_normal; simpl; eauto.
             ++ subst. unfold color_of in *. simpl in *. eauto.
             ++ rewrite pc_s1_s3 ST. simpl. rewrite <- (addwA pc0 _). rewrite (addwC (as_word _) onew). rewrite addwA. done.
          -- split; auto.
          -- split; auto. subst w'. destruct cond; auto. convert_eq_op. rewrite R1W in R2W. simplify_some. done.
          -- unfold updm. repeat rewrite setmE. simpl in *. rewrite <- Heqcond.
             destruct cond; simpl; try done. rewrite R2W. simpl. done.
          -- unfold updm. repeat rewrite setmE. simpl in *. rewrite <- Heqcond.
             destruct cond; simpl; try done. rewrite vt_eq1. simpl. done.
          -- split; auto.
          -- unfold updm. repeat rewrite setmE.
             simpl in *. rewrite <- Heqcond2.
             destruct cond2; simpl; try done.
             simpl in *. rewrite <- Heqcond1.
             destruct cond1; simpl; try done. rewrite OLD. simpl. done.
          -- unfold updm. repeat rewrite setmE.
             simpl in *. rewrite <- Heqcond2.
             destruct cond2; simpl; try done.
             simpl in *. rewrite <- Heqcond1.
             destruct cond1; simpl; try done. rewrite vt_eq. simpl. done.
          -- subst. done.
          -- subst. done.
      + rewrite ST in tag_pc1. inversion tag_pc1. subst n1 i1.
        deduce_equality R1W.
        deduce_equality MEM1.
        deduce_equality OLD.
        destruct vt_match as [? match_t]. subst t. destruct t1; unfold is_other in *; try congruence. subst v0.
        eexists; exists M. simpl.
        split.
        * eapply (plus_left _ [::]); try eapply step_load; eauto.
          -- eapply (etrans _ (PC)).
          -- decode_instr_eq.
          -- rewrite eq_s3 in vt_eq. eauto.
          -- rewrite eq_s3 in vt_eq0. eauto.
          -- rewrite eq_s3 in vt_eq1. eauto.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_bind. deduce_reg reg_match.
             assert (mem3 (addw pc3_val onew) = mem0 (addw pc0 onew)). eapply (etrans _ (esym Heqi')).
             rewrite eq_s3. rewrite H1 Heqi'. simpl. unfold check_belong, belong. rewrite eq_refl. simpl.
             destruct vt_match0. subst t0. simpl. rewrite eq_refl. simpl.
             try rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3. try rewrite ST. rewrite eq_refl. simpl.
             subst s3.
             rewrite vt_eq. simpl. unfold updm. rewrite vt_eq. simpl. rewrite vt_eq0. simpl.
             repeat rewrite setmE. unfold stack_value in *. simpl in *.
             remember (@eq_op (Ord.eqType _) r2 r1) as cond. simpl in Heqcond.
             rewrite <- Heqcond. destruct cond.
             ++ assert (r_eq: r2 = r1) by (eq_op_to_eq). simpl. reflexivity.
             ++ rewrite vt_eq1. simpl. done.
          -- eapply star_refl.
          -- done.
        * simpl in *.
          remember (if is_address vtag1 then Invalidated else Other) as new_t2.
          rewrite ST in Heqa12, Heqa13. rewrite R1W in Heqa12. rewrite MEM1 in Heqa13.
          do 2 simplify_some. simpl.
          remember ({| vtag := new_t2; color := color; entry := entry1; is_code := false |}) as t2'.
          eapply preserves_equiv_left_reg_write with (r := r2) (v := w2@vtag1) (v' := v1@vtag1).
          eapply preserves_equiv_left_mem_write with (v := w2@t2') (v' := v1@t2') (w := w1).
          eapply preserves_equiv_left_reg_write with (r := r1) (v := w1@Other) (v' := w1@Other).
          eapply (preserves_equiv_left_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)) (tpc1' := (taga (pc s1)))
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
          -- inversion weak as [? ? ? _ _ s_mem_cor' s'_mem_cor' _ _ _].
             subst. unfold memory_address_correctness in *. simpl in *. remember (@eq_op (Ord.eqType _) v1 w1) as cond.
             destruct vtag1; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond; destruct cond; simpl; convert_eq_op.
             all:try (destruct vt_match0; subst t0; eapply (s'_mem_cor _ _ _ vt_eq0)).
             all:try (destruct vt_match0; subst t0; eapply modusponens;
                      [eapply (s'_mem_cor _ _ _ vt_eq0)| simpl; intros [? [eq1 no_code]]]; rewrite vt_eq0 in eq1;
                    simplify_some; simpl in *; eexists; split; [eauto|]; intro in_ip; eapply no_code; eauto).
          -- inversion weak as [? ? ? _ _ s_mem_cor' s'_mem_cor' _ _ _].
             subst. unfold memory_address_correctness in *. simpl in *. remember (@eq_op (Ord.eqType _) v1 w1) as cond.
             destruct vtag1; simpl; auto; rewrite setmE; simpl in *; rewrite <- Heqcond; destruct cond; simpl; convert_eq_op.
             all:try (destruct vt_match0; subst t0; eapply (s'_mem_cor' _ _ _ vt_eq0)).
             all:try (destruct vt_match0; subst t0; eapply modusponens;
                      [eapply (s'_mem_cor' _ _ _ vt_eq0)| simpl; intros [? [eq1 no_code]]]; rewrite vt_eq0 in eq1;
                    simplify_some; simpl in *; eexists; split; [eauto|]; intro in_ip; eapply no_code; eauto).
          -- unfold updm. rewrite setmE. remember (@eq_op (Ord.eqType _) r2 r1) as cond. simpl in *.
             rewrite <- Heqcond. destruct cond; try done. rewrite OLD. simpl. done.
          -- unfold updm. rewrite setmE. remember (@eq_op (Ord.eqType _) r2 r1) as cond. simpl in *.
             rewrite <- Heqcond. destruct cond; try done. subst. simpl. trivial. rewrite vt_eq1. simpl. subst. done.
      + rewrite ST in tag_pc1. inversion tag_pc1. subst n1 i1.
        deduce_equality R2W.
        deduce_equality R1W.
        deduce_equality OLD.
        destruct vt_match0 as [? match_t1]. subst t0. destruct t1; unfold is_other in *; try congruence. subst v1.
        eexists; exists M. simpl.
        split.
        * eapply (plus_left _ [::]); try eapply step_store; eauto.
          -- eapply (etrans _ (PC)).
          -- decode_instr_eq.
          -- rewrite eq_s3 in vt_eq0. eauto.
          -- rewrite eq_s3 in vt_eq. eauto.
          -- rewrite eq_s3 in vt_eq1. eauto.
          -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
             unfold evi in *. unfold_bind. deduce_reg reg_match.
             assert (mem3 (addw pc3_val onew) = mem0 (addw pc0 onew)). eapply (etrans _ (esym Heqi')).
             rewrite eq_s3. rewrite H1 Heqi'. simpl. unfold check_belong, belong. rewrite eq_refl. simpl.
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
             try rewrite eq_s3 in tag_pc3. simpl in *. rewrite tag_pc3. try rewrite ST. rewrite eq_refl. simpl.
             repeat rewrite setmE. unfold stack_value in *. simpl in *. rewrite <- vt_eq0.
             remember (@eq_op (Ord.eqType _) r2 r1) as cond. simpl in Heqcond.
             rewrite <- Heqcond. destruct cond.
             ++ assert (r_eq: r2 = r1) by (eq_op_to_eq). rewrite r_eq in vt_eq. rewrite vt_eq. simpl. rewrite vt_eq1.
                simpl. done.
             ++ rewrite vt_eq. simpl. rewrite vt_eq1. simpl in *. done.
          -- eapply star_refl.
          -- done.
        * simpl in *. remember ({| vtag := t2; color := color ; entry := entry0; is_code := false |}) as t2'.
          remember (if is_address t2 then Invalidated else Other) as new_t2.
          eapply preserves_equiv_left_mem_write with (v := w2@t2') (v' := v0@t2') (w := w1). (* moved to erase the capacity first *)
          eapply preserves_equiv_left_reg_write with (r := r2) (v := w2@new_t2) (v' := v0@new_t2).
          eapply preserves_equiv_left_reg_write with (r := r1) (v := w1@Other) (v' := w1@Other).
          eapply (preserves_equiv_left_pc_incr) with (pc1' := (addw (vala (pc s1)) onew)) (tpc1' := (taga (pc s1)))
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
          -- subst. destruct t2; simpl; trivial.
          -- unfold updm. rewrite setmE. remember (@eq_op (Ord.eqType _) r2 r1) as cond. simpl in *.
             rewrite <- Heqcond. destruct cond; try done. rewrite R2W. done.
          -- unfold updm. rewrite setmE. remember (@eq_op (Ord.eqType _) r2 r1) as cond. simpl in *.
             rewrite <- Heqcond. destruct cond; try done. rewrite vt_eq. simpl. done.
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
          -- inversion weak as [? ? ? _ _ _ _ _ s'_reg_cor' _].
             subst. simpl. destruct vt_match. subst. eapply (s'_reg_cor' _ _ vt_eq).
          -- subst. simpl. trivial. rewrite R1W in Heqa12. simplify_some. simpl.
             rewrite setmE in Heqa13. unfold_match' Heqa13; convert_eq_op; try rewrite R2W in Heqa13; simplify_some; simpl; trivial.
             rewrite R1W in R2W. simplify_some. trivial.
          -- destruct vt_match. subst. trivial.
      + subst. pose proof (s_reg_cor _ _ RW) as cor_RW. simpl in cor_RW.
        assert (Hyp: t1 = InternalJump \/ exists n, t1 = Ret n).
        { clear - Heqa7; repeat (unfold check_ret in *; (unfold_all || unfold_match)); eauto. }
        remember t1 as t1'.
        destruct t1; subst t1'; try (destruct Hyp as [?|Hyp]; try destruct Hyp; done);
          simpl in cor_RW; destruct cor_RW as [? [? ?]]; eauto.
      + repeat
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
        deduce_equality RW.
        deduce_equality RA.
        deduce_equality (esym Heqa9).
        deduce_equality (esym Heqa6).
        deduce_equality (esym Heqa11).
        deduce_equality (esym Heqa12).
        deduce_equality (esym Heqa13).
        deduce_equality (esym Heqa14).
        deduce_equality (esym Heqa15).
        deduce_equality (esym Heqa16).
        deduce_equality (esym Heqa17).
        deduce_equality (esym Heqa18).
        deduce_equality (esym Heqa19).
        eexists. exists M.
        split.
        * eapply (plus_left _ [::]); try eapply step_jump. eauto.
          -- eapply (etrans _ (PC)).
          -- decode_instr_eq.
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
             assert (rel: is_relevant_comp Left i0). { clear - Heqa4. simpl in *. unfold Component.id. rewrite <- Heqa4. trivial. }
             assert (eq_off': get_offset Left i0 = Some off).
             { simpl; auto. rewrite -HeqH eq_off. auto. }
             pose proof ((fst (code_left w resv _ off _ rel eq_off' res_code' res_col))) as impl.
             simpl in impl. pose proof (impl (res_eq)) as [? [? pc3'eq]]. simpl.
             simpl in HeqH. rewrite eq_off in HeqH. simplify_some. rewrite pc3'eq. simpl.
             subst pc3_tag. simpl. rewrite eq_refl. simpl.
             unfold updm. simpl in pc3'eq. unfold as_word.
             try rewrite eq_s3 in tag_pc3. simpl in *. try rewrite ST. simpl.
             (*automatically rewrite regs3 registers*)
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

          { simpl. rewrite (setmI RA). unfold as_word. simpl. rewrite eq_sym in Heqa23.
            unfold_match' Heqa23; convert_eq_op; repeat simplify_some; subst; simpl.
            simpl in *. repeat simplify_some. subst. unfold as_word in *. simpl in *.
            rewrite RW in RA. simplify_some. subst. rewrite (setmI RW).
            repeat
              (match goal with
               | H : Some (?v@_) = _  |- context[setm reg _ ?v@_] =>
                   rewrite (setmI (esym H))
               end). now trivial.
            rewrite RW in Heqa23. simplify_some; subst. rewrite (setmI RW).
            repeat
            ((* this instruction branches on the value of r *)
              (match goal with
               | H : Some (?v@_) = _  |- context[setm reg _ ?v@_] =>
                   unfold_match' H; simplify_some; subst; convert_eq_op; simpl in *
               end);
              (* if r is a value that is being rewriten, this deduces new equalities *)
              try (match (type of vt_eq) with
                   | ?ls = ?rs =>
                       (match goal with
                          Heq: ls = Some (?a), Hmatch: (data_match _ _ _ _ ?a)  |- _ =>
                            rewrite vt_eq in Heq; simplify_some; inversion Hmatch; subst; rewrite (setmI RW)
                        end)
                   end);
              repeat (simplify_some; subst);
              (* shows that the setm are not changing the values *)
              repeat
                (match goal with
                   H: Some ?v = getm reg ?r |- context[setm reg ?r ?v] => rewrite (setmI (esym H))
                 end);
              try trivial).
            admit. admit. admit. admit. admit. admit. admit. admit. admit.
            admit. admit.
          }
          unfold color_of in tag_pc3, tag_pc1. simpl in tag_pc3, tag_pc1. inversion tag_pc1. subst n1.
          eapply preserves_equiv_left_pc_incr with (pc1' := (w)) (tpc1':=pc3_tag)
                                                   (pc3' := (addw w (as_word off))) (tpc3':=(pc3_tag)); subst pc3_tag.
          eauto. auto. auto.
          all: simpl; try trivial.
          all: unfold updm.
          all: try done.
          -- subst. simpl. eapply same_pc_normal.
             subst. simpl. eauto.
             unfold color_of. subst. simpl in *. eauto.
             subst. simpl. trivial.
      + remember pc' as w'. unfold pc' in Heqw'.
        match (type of Heqw') with
          _ = (_ _ (match ?c as _ with _ => _ end)) => remember c as cond
        end. destruct cond; subst w'; try (rewrite Heqi'; eauto).
        subst. unfold_match' Heqa5. unfold is_code in Heqa3. unfold_match' Heqa3. pose proof (bnz_s1 _ _ PC) as H.
        simpl in H. simpl in *. rewrite <- Heqa1 in H. simpl in *. rewrite H0 in H. destruct H as [? [? ?]]; auto. eauto.
      + inversion Heqa2.
        deduce_equality RW.
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
        deduce_equality PC. rewrite eq_s3 in bnz_s3.
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
        deduce_equality res_eq. rewrite next_pc_eq in vt_eq1. simplify_some.
        eexists. exists M. simpl.
        split.
        * eapply (plus_left _ [::]); try eapply step_bnz. eauto.
          -- eapply (etrans _ (PC)).
          -- decode_instr_eq.
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
        * eapply preserves_equiv_left_reg_write with (r := r) (v := v0@Other) (v' := (v0@Other)).
          eapply preserves_equiv_left_pc_incr with (pc1' := pc') (tpc1' := taga (pc s1))
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
      + (*normal JAL*)
        (* we start by proving that pc' points to code *)
        unfold pc' in *. rewrite ST in bnz_s1, PC, alloc_mem_s1. pose proof (bnz_s1 _ _ PC) as JALcond.
        revert JALcond. decode_instr_eq. intro JALcond.
        destruct JALcond as [[x [next_pc_content' next_pc_code]] | imm_alloc_eq ]; auto.
        2: { exfalso. subst imm. inversion Heqa2. destruct a10 as [va ta]. simpl in *. subst ta.
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
        deduce_equality (esym Heqa9).
        deduce_equality (esym Heqa6).
        deduce_equality (esym Heqa11).
        deduce_equality (esym Heqa12).
        deduce_equality (esym Heqa13).
        deduce_equality (esym Heqa14).
        deduce_equality (esym Heqa15).
        deduce_equality (esym Heqa16).
        deduce_equality (esym Heqa17).
        deduce_equality (esym Heqa18).
        deduce_equality (esym Heqa19).
        deduce_equality OLD.
        subst. unfold side_of in *. unfold_match' side_eq. simpl in *.
        deduce_equality PC.
        rewrite Heqi' in RA. simplify_some. subst ti' vret. simpl in *.
        deduce_equality Heqi'.
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
             repeat((repeat
                (match goal with
                 | H: getm _ ?w = _  |- context[getm _ ?w] => rewrite H; simpl
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
          eapply preserves_equiv_left_reg_write with (r := ra) (v := (pc0 + 1)%w @InternalJump)
                                                     (v' := ((pc0 + as_word off + 1)%w @InternalJump)).
          eapply preserves_equiv_left_pc_incr with (pc1' := (swcast imm)) (tpc1':= Level n color)
                                                   (pc3' := (swcast imm + as_word off)%w) (tpc3':= Level n color).
          eauto. auto. auto.
          all: simpl; try trivial.
          all: unfold updm.
          -- subst. simpl. eapply same_pc_normal.
             simpl. eauto. simpl. eauto. simpl. trivial.
          -- pose proof (end_s3 _ _ vt_eq11). simpl in H. revert H. rewrite H2.
             intro H. destruct H; auto; try contradiction.
             split; auto. simpl. rewrite eq_off. simpl.
             rewrite <- addwA. rewrite (addwC (as_word _) onew). rewrite addwA. trivial.
          -- rewrite Heqi'. eexists. split; eauto.
          -- pose proof (end_s3 _ _ vt_eq11). simpl in H. revert H. rewrite H2.
             intro H. destruct H; auto; try contradiction. destruct H as [? [? ?]].
             eexists; split; [eauto|]. intro. trivial.
          -- pose proof (end_s3 _ _ vt_eq11). simpl in H. revert H. rewrite H2.
             intro H. destruct H; auto; try contradiction. destruct H as [? [? ?]].
             eexists; split; [eauto|]. intro. trivial.
          -- rewrite OLD. simpl. trivial.
          -- rewrite vt_eq10. simpl. trivial.
          -- rewrite setmI. auto. auto. rewrite <- Heqa22 in Heqi'. simplify_some. rewrite Heqa22. trivial.
      + (*JAL to alloc*)
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
        deduce_equality (esym Heqa9).
        deduce_equality (esym Heqa6).
        deduce_equality (esym Heqa11).
        deduce_equality (esym Heqa12).
        deduce_equality (esym Heqa13).
        deduce_equality (esym Heqa14).
        deduce_equality (esym Heqa15).
        deduce_equality (esym Heqa16).
        deduce_equality (esym Heqa17).
        deduce_equality (esym Heqa18).
        deduce_equality (esym Heqa19).
        deduce_equality OLD.
        subst. unfold side_of in *. unfold_match' side_eq. simpl in *.
        deduce_equality PC.
        rewrite Heqi' in RA. simplify_some. subst ti' vret. simpl in *.
        deduce_equality Heqi'.
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
          eapply preserves_equiv_left_reg_write with (r := ra) (v := (pc0 + 1)%w @InternalJump) (
                                                       v' := ((pc0 + as_word off + 1)%w @InternalJump)).
          eapply preserves_equiv_left_pc_incr with (pc1' := (word_of_nat alloc_label)) (tpc1':= Level n color)
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
          -- pose proof (end_s3 _ _ vt_eq11). simpl in H. revert H. rewrite H1.
             intro H. destruct H; auto; try contradiction. destruct H as [? [? ?]].
             eexists; split; [eauto|]. intro. trivial.
          -- rewrite OLD. simpl. trivial.
          -- rewrite vt_eq10. simpl. trivial.
          -- rewrite setmI. auto. rewrite <- Heqa22 in Heqi'. simplify_some. rewrite Heqa22. trivial.
      + destruct pc_s1_s3 as [s1 s3 pc_s1_s3 eq_none|s1 s3 ? ? eq_some eq_off pc_s1_s3].
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
          remember (regs s1 (as_word (ssrint.Posz 16))) as retval. simpl in *. rewrite <- Heqretval in Heqa9.
          destruct retval as [retval|]; try (inversion Heqa9; done).
          destruct a0 as [va ?]. unfold is_jump in *. destruct taga; inversion Heqa4.
          destruct ((snd (reg_match _ _)) (esym Heqa3)) as [b [bmatch beq]].
          destruct ((snd (reg_match _ _)) (esym Heqa5)) as [b' [b'match b'eq]].
          destruct ((snd (reg_match _ _)) (esym Heqretval)) as [b'' [b''match b''eq]].
          rewrite beq. simpl. destruct b as [bv bt]. destruct bmatch. subst bt. simpl.
          rewrite b'eq. simpl. unfold is_other in *. destruct a1, b'. destruct b'match. subst taga0.
          destruct taga; inversion Heqa6. simpl.
          assert (side_of color = Left).
          { clear -tag_pc1 side_eq.
            destruct s1 as [?? [] ?]; simpl in *; subst. congruence. }
          assert (domm_eq: (List.filter
                              (fun mw : word 32 =>
                                 andw mw (@mask mt NC) ==
                                   @component_memory_prefix mt NC (ssrint.Posz (1 + color))) (domm (mem s1)))
                           = (List.filter
                                (fun mw : word 32 =>
                                   andw mw (@mask mt NC) ==
                                     @component_memory_prefix mt NC (ssrint.Posz (1 + color))) (domm (mem s3)))).
          { eapply match_mem_pref_condition_filter_eq; eauto. }
          subst s1 s3. simpl in *. destruct pc3_tag. simpl.
          inversion tag_pc1. inversion tag_pc3. subst n1 n0 i i0.
          simpl in *. rewrite <- domm_eq. subst vala0.
          rewrite <- Heqa10 => //=.
          rewrite <- Heqa8. simpl.

          rewrite <- Heqa1. simpl. unfold updm. rewrite b''eq. simpl. eauto. }
        exists s3'; exists M. simpl.
        split.
        * eapply (plus_left _ [::]); try eapply step_syscall; eauto.
          -- eapply (etrans _ (PC)).
          -- subst. simpl in *. rewrite <- pc_s1_s3. unfold Instance.table, table. convert_eq_op. subst. simpl.
             rewrite setmE. rewrite eq_refl. done.
          -- unfold run_syscall, evi. deduce_reg reg_match. rewrite s3'_eq. simpl. done.
          -- eapply star_refl.
          -- done.
        * eapply preserves_equiv_left_alloc_fun; eauto; done.
  Admitted.

End StepStrong.
