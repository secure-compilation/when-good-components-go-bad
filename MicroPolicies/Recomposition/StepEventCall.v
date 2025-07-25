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

Module StepEventCall (S: RecompositionContext).

  Module Defs := RecompositionDefinitions S.
  Module Pres := Preservation S.
  Include Pres.

  Lemma step_event_call:
  forall s1 comp proc z comp' s1', Step sem s1 ((ECall comp proc z comp') :: nil) s1' ->
  forall s2 s2',   Step sem' s2 ((ECall comp proc z comp') :: nil) s2' ->
  forall s3 M, match_states M s1 s2 s3    ->
  exists s3' M', Plus sem'' s3 ((ECall comp proc z comp') :: nil) s3' /\ (* using Plus here because we know if an event is emitted then we've done at least one step *)
              match_states M' s1' s2' s3'.
  Proof.
    import_context.
    intros s1 comp proc z comp' s1' step_s1 s2 s2' step_s2 s3 M match_st.
    remember (id s3) as s3'; simpl in Heqs3'; destruct s3' as [mem3 regs3 [pc3_val pc3_tag] internal3 cn3].
    rewrite Heqs3' in match_st; rewrite Heqs3'. pose proof (esym Heqs3') as eq_s3. clear Heqs3'.
    inversion step_s2;
      unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
    all: unfold_all; try unfold_match; unfold_all.
    all: try (clear -Heqa2; repeat unfold_match' Heqa2; done); simpl in *. (* eliminates many goals *)
    (* gets rid of cases with no events *)
    1-6, 8: (exfalso; clear -NEXT Heqa0 Heqa4 Heqa7; repeat (unfold_all || unfold_match); done).
    3: (exfalso; clear -CALL; unfold run_syscall in *; repeat (unfold_all || unfold_match); done).
    all: (assert (tpc1 = tpc0) by (clear -Heqa2; unfold_match' Heqa2); subst tpc1).
    all: (assert (ts0 = (ts (mvec None)) ) by
             (unfold mvec in *; simpl; clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
              destruct Heqa2 as [_ _ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ts0).
    all: (unfold mvec in *; assert (ti1 = ti0) by
                (clear -Heqa2; unfold_match' Heqa2; try (inversion Heqa2; subst b); eapply ivec_eq_inv in Heqa2;
                 destruct Heqa2 as [_ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ti1).
    all: unfold check_belong, belong, reg_clear_list in *.
    all: repeat (unfold_all || unfold_match).
    all: destruct tpc0; repeat (unfold_all || unfold_match); simpl in *.
    all: convert_eq_op.
    all: unfold is_jump, check_ret in *; try (repeat unfold_match; subst t1).
    all: unfold hshead in *; simpl in *.
    all: (inversion Heqa0); revert ST eq_s3; subst; intros ST eq_s3. (* trick to keep an equality on s1 and s3 *)
    all: simpl in *.
    1: rename i2 into comp; rename color1 into comp'.
    (* tidying up the hypothesis *)
    all: simpl in *.
    all: repeat
           (match goal with
              H: Some _ = getm (setm _ _ _) _ |- _ =>
                repeat (rewrite setmE in H; unfold as_word in H; simpl in H)
            end).
    all: repeat
           (match goal with
              H: Some _ = match (eq_op (_ (_ ((_ (_ ?a _)) _ _))) _) with _ => _ end,
                H' : Some _ = getm _ (as_word (_ ?a))
              |- _ => idtac a; unfold as_word in H'; rewrite ST in H; simpl in H', H; rewrite <- H' in H
            end).
    all: simpl in *.
    all: repeat (match goal with H: ?a = ?a |- _ => clear H end).
    (* we branch on which side is strongly related to s3 *)
    all: destruct match_st as [M ? ? ? common strong weak |M ? ? ? common weak strong];
      (* in each case, we keep only one step from s1 (the most useful for the case being treated) *)
      [match (type of step_s1) with
         (_ _ _ _ _ _ ?ev _) =>
           remember ev as t;
           destruct step_s1 as [s1 ? s1' step_s1 allowed | s1 ? s1' step_s1 _];
           [exfalso;
            destruct strong as [? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor s_reg_cor s'_reg_cor mem_match reg_match];
            eapply Machine.Intermediate.fdisjoint_partition_notinboth;
            [inversion Hmergeable_ifaces as [[_ fdisj] _]; exact fdisj | exact allowed | unfold side_of in *; unfold_match' side_eq]
           | ]; subst t
       end
      |match (type of step_s1) with
         (_ _ _ _ _ _ ?ev _) =>
           assert (step_2: step2 tt s1 ev s1');
           [remember ev as t; destruct step_s1 as [s1 ? s1' step_s1 allowed | s1 ? s1' _ step_s1]; subst t; exact step_s1
           | clear step_s1; rename step_2 into step_s1]
       end].
    repeat
      match goal with
        H: Some ?a = match ?cond with true => Some ?b | false => Some ?c end |- _ =>
          assert (a = if cond then b else c); [destruct cond; inversion H; try congruence| clear H]
      end.
    all: inversion step_s1;
      unfold next_state_updates, next_state_do_updates, next_state_updates_and_pc,
      next_state, transfer, instr_rules, LRC.transfer, LRC.instr_rules in *.
    all: unfold_all; try unfold_match; unfold_all.
    all: try (exfalso; clear -CALL; unfold run_syscall in *; repeat (unfold_all || unfold_match)). (* eliminate alloc cases *)
    all: match goal with
         | H: @eq (ivec lrc_tags) _ _ |- _ => rename H into ivec_eq
         end.
    all: try (exfalso; unfold mvec0 in ivec_eq; clear- ivec_eq; repeat unfold_match' ivec_eq; done). (* eliminate many uncoherent cases *)
    all: (assert (tpc1 = tpc0) by (clear -ivec_eq; unfold_match' ivec_eq); subst tpc1).
    all: destruct tpc0.
    all: assert (eqo1: OP o1 = op (mvec0 None)) by (try subst o1; unfold mvec0 in *; clear -ivec_eq; unfold_match' ivec_eq).
    all: unfold mvec0 in eqo1; simpl in eqo1; inversion eqo1; subst o1.
    all: (assert (ts0eq: ts0 = (ts (mvec0 None)) ) by
           (unfold mvec0 in *; simpl; clear -ivec_eq; unfold_match' ivec_eq; try (inversion ivec_eq; subst b);
            eapply ivec_eq_inv in ivec_eq; destruct ivec_eq as [_ _ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto);
          unfold mvec0 in ts0eq; simpl in ts0eq; subst ts0).
    all: (unfold mvec0 in *; assert (ti1 = ti0) by
                (clear -ivec_eq; unfold_match' ivec_eq; try (inversion ivec_eq; subst b); eapply ivec_eq_inv in ivec_eq;
                 destruct ivec_eq as [_ _ H]; eapply Classical_Prop.EqdepTheory.inj_pair2 in H; auto); subst ti1).
    all: unfold check_belong, belong, reg_clear_list in *.
    all: repeat
           let pl := fresh "pl" in
           let pr := fresh "pr" in
           match goal with
           | p : _ * option event |- _ =>
               match goal with
               | H : Some p = _ |- _ =>
                   assert (tmp: p.2 = None) by (clear -H; repeat (unfold_all || unfold_match));
                   destruct p as [pl pr]; inversion tmp; clear tmp; simpl in *; try subst pl; try subst pr
               end
           end.
    all: try simplify_some.
    all: try (exfalso; clear -NEXT; repeat (unfold_all || unfold_match); done). (* eliminate all remaining cases with no events *)
    all: unfold reg_clear_list_aux in CLEAR; unfold_all.
    1, 3: exfalso;
    repeat ( match goal with | p : _ * option event |- _ => destruct p end); simpl in *;
    repeat (unfold_all || unfold_match). (* eliminate cases with the wrong events *)
    all: repeat
           match goal with
             H: Some ?a = match ?cond with true => Some ?b | false => Some ?c end |- _ =>
               assert (a = if cond then b else c); [destruct cond; inversion H; try congruence| clear H]
           end.
    all: revert Heqa23; repeat (unfold_all || unfold_match).
    all: intro a21_eq.
    all: subst color; try subst color0; try subst color1; try subst i3; destruct e0, e; simpl in *; subst rcom_value0.
    all: unfold is_jump, check_ret, build_tpc in *; try (revert a21_eq; repeat unfold_match; subst t1; intro a21_eq).
    all: convert_eq_op.
    all: unfold_match' ivec_eq; inversion ivec_eq as [tag_mem_w0].
    all: try (match goal with
                H : @eq (ovec lrc_tags _) _ _ |- _ => inversion H; clear H
              end).
    all: revert ST ST0 eq_s3; subst; intros ST ST0 eq_s3; simpl in *. (* trick to keep an equality on s1 and s3 *)
    1-2: rename i2 into comp.
    all: inversion strong as [? ? ? pc_s'_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match].
    all: inversion common as [? ? ? ? ? ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          [mem_pref_cond_s1 [mem_pref_cond_s1' [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 entry_code1]]]]]]]
                          [mem_pref_cond_s2 [mem_pref_cond_s2' [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 entry_code2]]]]]]]
                          [mem_pref_cond_s3 [mem_pref_cond_s3' [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 entry_code3]]]]]]]
                          capa_cor1 capa_cor2 capa_cor3 code_left code_right].
    all: subst s s' s0 s4 s5 m m0.
    (* We now need to branch on which state is strongly related to s3 next (i.e. on what is comp', the color of the next compartment) *)
    all: ((match goal with
           H: Some ?a = getm (mem ?s) ?w, col_mem: color_in_memory (mem ?s) |- _ =>
             destruct (col_mem _ _ (esym  H)) as [ip_comp' | ic_comp']; destruct a; simpl in *;
             [setoid_rewrite <- Extra.In_in in ip_comp'; rewrite <- tag_mem_w0 in ip_comp'; simpl in ip_comp'
             |setoid_rewrite <- Extra.In_in in ic_comp'; rewrite <- tag_mem_w0 in ic_comp'; simpl in ic_comp']
         end) || exfalso).
    all: rewrite ST in tag_pc2; inversion tag_pc2; subst n0 c0; clear tag_pc2.
    all: repeat match goal with
             |- context[vala (match ?cond with true => ?a | false => ?b end)] =>
               assert (tmp: vala (match cond with true => a | false => b end) = (match cond with true => vala a | false => vala b end));
               [ clear; destruct cond; simpl; done | rewrite tmp; clear tmp]
           end; simpl.
    all: ((destruct pc_s'_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s'_s3]
          || destruct pc_s'_s3 as [? ? ? eq_none|s2 s3 ? ? _ eq_off pc_s'_s3]);
          [exfalso; subst; simpl in *; (rewrite eq_none in PC) || (rewrite eq_none in PC0); done |]).
    (* Steps needed in each cases: *)
    (* 1/ deduce beforehand the equalities on s3 needed to proceed, *)
    (* 2/ unfold to show that a step can be done from s3, *)
    (* 3/ show that match_state hold for the new states. *)
    + (* call from comp in P to comp' in P *)
      repeat
      (match goal with
         H : Some ?a = getm reg0 _ |- _ => deduce_equality (esym H); pose proof (esym H); clear H
       end).
      deduce_equality OLD0.
      subst s1. unfold side_of in *. unfold_match' side_eq. simpl in *.
      deduce_equality PC0.
      pose proof (end_s1 _ _ PC0) as end_cond. simpl in end_cond.
      revert end_cond. decode_instr_eq. intro end_cond. destruct end_cond as [ | [? [eq1 code_RA0]]]; auto; try tauto.
      rewrite RA0 in eq1. simplify_some. simpl in code_RA0. destruct tret. unfold_match' a21_eq. convert_eq_op.
      rewrite eq_s3 in H13, tag_pc1, tag_pc3. destruct pc3_tag. simpl in H13, tag_pc1, tag_pc3.
      inversion tag_pc1. inversion tag_pc3. clear tag_pc1 tag_pc3. subst n0 n1 i2. rename color into comp.
      deduce_equality RA0.
      (* quick proof that v12 (s3) is a JAL offseted from i0 *)
      unfold_match' Heqa2.
      inversion vt_match11; try subst i0; revert H13; decode_instr_eq; intro H13.
      { destruct (H13 imm0); auto. }
      { inversion H13. subst imm0 pc'0. unfold alloc_empty in *. subst. simpl in alloc_mem_s1.
        assert (sw_eq: @swcast _ (word_size mt) (@word_of_nat (imm_size mt) alloc_label) = word_of_nat alloc_label).
        { admit. } simpl in sw_eq.
        rewrite <- sw_eq in alloc_mem_s1. rewrite <- Heqa63 in alloc_mem_s1. inversion alloc_mem_s1. }
      inversion H13. subst imm1. clear H13. subst pc'0. rewrite H15 in Heqa63. simplify_some. simpl in *.
      rename taga into td. rename vala into vd. rename H16 into eq_next_pc.
      assert (exists off', offset1 comp' = Some off') as [off' eq_off'].
      { eapply (rwP dommP). rewrite offset1_domm. trivial. }
      rewrite <- tag_mem_w0 in H19. simpl in H19.
      assert (eq_off'_alt: get_offset (side_of comp') comp' = Some off').
      { rewrite <- eq_off'. unfold side_of. rewrite ip_comp'. simpl. trivial. }
      pose proof (H19 off' (eq_off'_alt)) as imm'_eq.
      assert (imm'eq: @swcast _ (word_size mt) imm' = (swcast imm0 + as_word off')%w).
      { subst imm'. admit. } (* need more hypothesis *)
      rewrite imm'eq in eq_next_pc.
      remember (((pc1 + 1)%w@(Ret n), (pc0 + 1)%w@(Ret n), (pc1 + 1 + as_word off)%w@(Ret n), comp) :: M) as M'.
      eexists. exists M'.
      split.
      * eapply (plus_left _ [:: ECall _ _ _ _] ). eapply step_jal; eauto.
        -- rewrite eq_s3 in vt_eq11. exact vt_eq11.
        -- rewrite eq_s3 in vt_eq12. exact vt_eq12.
        -- simpl. exact H14.
        -- rewrite eq_s3 in vt_eq10. exact vt_eq10.
        -- unfold reg_clear_list, reg_list. simpl. unfold as_word. subst. simpl.
           repeat
             (match goal with
              | H: _ ?w = _  |- context[_ ?w] => rewrite H; simpl
              end). trivial.
        -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
           unfold evi in *. simpl. unfold_bind.
           deduce_reg reg_match. rewrite imm'eq. rewrite eq_next_pc. simpl. rewrite eq_refl. simpl.
           simpl in *. rewrite <- tag_mem_w0. rewrite <- H18, <- tag_mem_w0.
           unfold check_belong, belong. rewrite eq_refl. simpl. rewrite eq_s3 in Heqa10. simpl in Heqa10. rewrite <- Heqa10.
           destruct a22 as [va22 ta22]. unfold is_other in *. destruct ta22; simpl in Heqa51; inversion Heqa51.
           inversion vt_match9 as [? _]; subst t9. simpl. rewrite eq_s3 in Heqa34. simpl in Heqa34. rewrite <- Heqa34.
           simpl. subst s3. rewrite vt_eq12.
           unfold updm. unfold as_word. simpl in *.
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
           destruct x as [vx tx]. inversion H13. subst tx vx.
           reflexivity.
        -- eapply star_refl.
        -- unfold evi in Heqa, Heqa0. repeat unfold_bind. inv Heqa. inv Heqa0. simpl.
           simpl in *. rewrite H16. rewrite H12 in Heqa46. simplify_some. reflexivity.
      * subst. simpl in *.
        pose proof (end_s2 _ _ PC) as end_cond. simpl in end_cond.
        revert end_cond. decode_instr_eq. intro end_cond. destruct end_cond as [ | [? [eq1 code_RA]]]; auto; try tauto.
        rewrite RA in eq1. simplify_some. simpl in code_RA.
        rewrite (@setmI _ _ mem1). 2:{ rewrite <- Heqa50 in RA0. simplify_some. simpl. done. }
        rewrite (@setmI _ _ mem0). 2:{ rewrite <- Heqa22 in RA. simplify_some. simpl. done. }
        rewrite (@setmI _ _ mem3). 2:{ trivial. }
        eapply match_states_left; econstructor; simpl; unfold build_tpc; try reflexivity.
        -- rewrite <- (addn1 n).
           eapply wf_stack_cons_left; simpl; eauto.
           ++ unfold points_to_comp_code'. rewrite RA0. simpl. split; [ | right]; trivial.
           ++ unfold points_to_comp_code. rewrite RA. simpl. split; trivial.
           ++ unfold points_to_comp_code. subst pc3_val.
              rewrite <- addwA, (addwC _ onew), addwA in vt_eq12. rewrite vt_eq12. simpl. split; auto.
        -- unfold register_domm. repeat rewrite domm_set. simpl.
           unfold register_domm, reg_field_size, mword, FSet.fsval in reg_domm1. simpl in reg_domm1.
           unfold mword, word_size. simpl.
           clear - reg_domm1. admit. (* exstructure *)
        -- unfold register_domm. repeat rewrite domm_set. simpl.
           unfold register_domm, reg_field_size, mword, FSet.fsval in reg_domm2. simpl in reg_domm2.
           unfold mword, word_size. simpl.
           clear - reg_domm2. admit. (* exstructure *)
        -- unfold register_domm. repeat rewrite domm_set. simpl.
           unfold register_domm, reg_field_size, mword, FSet.fsval in reg_domm3. simpl in reg_domm3.
           unfold mword, word_size. simpl.
           clear - reg_domm3. admit. (* exstructure *)
        -- split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]; trivial.
        -- split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]; trivial.
        -- split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]; trivial.
        -- intros d q rw rweq.
           destruct rw as [r | w]; simpl; simpl in rweq.
           ++ repeat rewrite setmE in rweq. repeat (unfold_match' rweq).
              ** convert_eq_op. simplify_some. subst d q.
                 split; [unfold in_stack; do 3 eexists; econstructor; eauto |].
                 intros rw d. destruct rw as [r | w].
                 { intro rweq. repeat rewrite setmE in rweq. repeat unfold_match' rweq. convert_eq_op; trivial.
                   exfalso.
                   assert (r_in : In r (domm reg0)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm1 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   unfold fset, FSet.fsval, locked_with in r_in.
                   destruct fset_key. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
                 { intro tex. pose proof (capa_cor1 d n (inr w) tex) as [is_in unicity].
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
              ** exfalso.
                 assert (r_in : In r (domm reg0)).
                 { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                 exfalso. rewrite reg_domm1 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                 repeat (destruct r_in as [|r_in];
                         [subst;
                          (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                 unfold fset, FSet.fsval, locked_with in r_in.
                 destruct fset_key. simpl in r_in.
                 repeat (destruct r_in as [|r_in];
                         [subst;
                          (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                 inversion r_in.
           ++ pose proof (capa_cor1 d q (inr w) rweq) as [is_in unicity].
              split. { clear -is_in. unfold in_stack in *. destruct is_in as [sv1 [sv2 [col is_in]]]. do 3 eexists. right. eauto. }
              intros [r' | w'] d''.
              ** intro rweq'. repeat rewrite setmE in rweq'. repeat unfold_match' rweq'.
                 { convert_eq_op. simplify_some. subst d'' q.
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
                 { assert (r_in : In r' (domm reg0)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm1 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   unfold fset, FSet.fsval, locked_with in r_in.
                   destruct fset_key. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
              ** eapply (unicity (inr w')).
        -- intros d q rw rweq.
           destruct rw as [r | w]; simpl; simpl in rweq.
           ++ repeat rewrite setmE in rweq. repeat (unfold_match' rweq).
              ** convert_eq_op. simplify_some. subst d q.
                 split; [unfold in_stack; do 3 eexists; econstructor; eauto |].
                 intros rw d. destruct rw as [r | w].
                 { intro rweq. repeat rewrite setmE in rweq. repeat unfold_match' rweq. convert_eq_op; trivial.
                   exfalso.
                   assert (r_in : In r (domm reg)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm2 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   unfold fset, FSet.fsval, locked_with in r_in.
                   destruct fset_key. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
                 { intro tex. pose proof (capa_cor2 d n (inr w) tex) as [is_in unicity].
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
              ** exfalso.
                 assert (r_in : In r (domm reg)).
                 { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                 exfalso. rewrite reg_domm2 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                 repeat (destruct r_in as [|r_in];
                         [subst;
                          (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                 unfold fset, FSet.fsval, locked_with in r_in.
                 destruct fset_key. simpl in r_in.
                 repeat (destruct r_in as [|r_in];
                         [subst;
                          (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                 inversion r_in.
           ++ pose proof (capa_cor2 d q (inr w) rweq) as [is_in unicity].
              split. { clear -is_in. unfold in_stack in *. destruct is_in as [sv1 [sv2 [col is_in]]]. do 3 eexists. right. eauto. }
              intros [r' | w'] d''.
              ** intro rweq'. repeat rewrite setmE in rweq'. repeat unfold_match' rweq'.
                 { convert_eq_op. simplify_some. subst d'' q.
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
                 { assert (r_in : In r' (domm reg)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm2 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   unfold fset, FSet.fsval, locked_with in r_in.
                   destruct fset_key. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
              ** eapply (unicity (inr w')).
        -- intros d q rw rweq.
           destruct rw as [r | w]; simpl; simpl in rweq.
           ++ repeat rewrite setmE in rweq. repeat (unfold_match' rweq).
              ** convert_eq_op. simplify_some. inversion Heqa51.
              ** convert_eq_op. simplify_some. subst d q pc3_val.
                 split; [unfold in_stack; do 3 eexists; econstructor; rewrite <- addwA, (addwC onew), addwA; eauto|].
                 intros rw d. destruct rw as [r | w].
                 { intro rweq. destruct a22 as [va ta]. destruct ta; inversion Heqa51.
                   repeat rewrite setmE in rweq. repeat unfold_match' rweq.
                   all: repeat simplify_some; convert_eq_op; trivial.
                   exfalso.
                   assert (r_in : In r (domm regs3)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm3 in r_in. simpl in r_in. unfold word_of_nat, as_word in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (Word ?a == Word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   unfold fset, FSet.fsval, locked_with in r_in.
                   destruct fset_key. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
                 { intro tex. pose proof (capa_cor3 d n (inr w) tex) as [is_in unicity].
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
              ** assert (r_in : In r (domm regs3)).
                 { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                 exfalso. rewrite reg_domm3 in r_in. simpl in r_in. unfold word_of_nat, as_word in r_in. simpl in r_in.
                 repeat (destruct r_in as [|r_in];
                         [subst;
                          (match goal with H : false = (Word ?a == Word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                 inversion r_in.
           ++ pose proof (capa_cor3 d q (inr w) rweq) as [is_in unicity].
              split. { clear -is_in. unfold in_stack in *. destruct is_in as [sv1 [sv2 [col is_in]]]. do 3 eexists. right. eauto. }
              intros [r' | w'] d''.
              ** intro rweq'. repeat rewrite setmE in rweq'. repeat unfold_match' rweq'.
                 { convert_eq_op. simplify_some. inversion Heqa51. }
                 { convert_eq_op. simplify_some. subst d'' q.
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
                 { assert (r_in : In r' (domm regs3)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm3 in r_in. simpl in r_in. unfold word_of_nat, as_word in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (Word ?a == Word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
              ** eapply (unicity (inr w')).
        -- unfold combined_codes. simpl. exact code_left.
        -- unfold combined_codes. simpl. exact code_right.
        -- eapply same_pc_normal; simpl; eauto.
        -- unfold side_of. rewrite ip_comp'. trivial.
        -- unfold memory_address_correctness. simpl. exact s_mem_cor.
        -- unfold memory_address_correctness. simpl. exact s'_mem_cor.
        -- trivial.
        -- unfold register_address_correctness. simpl.
           intros d r r_d_eq.
           unfold register_domm in *.
           assert (r_in : In r (domm reg0)).
           { clear - reg_domm1 r_d_eq. rewrite reg_domm1.
             repeat (rewrite setmE in r_d_eq; unfold_match' r_d_eq; [ convert_eq_op |]; simpl in r_d_eq).
             all: try (simpl; tauto).
             rewrite <- reg_domm1. setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). exists d. trivial. }
           rewrite reg_domm1 in r_in.
           repeat (destruct r_in as [? | r_in]; try subst r; repeat (rewrite setmE in r_d_eq; simpl in r_d_eq)).
           all: simpl in r_d_eq; try simplify_some; simpl; trivial.
           rewrite RA0. eexists; split; done.
           inversion r_in.
        -- unfold register_address_correctness. simpl.
           intros d r r_d_eq.
           unfold register_domm in *.
           assert (r_in : In r (domm regs3)).
           { clear - reg_domm3 r_d_eq. rewrite reg_domm3.
             repeat (rewrite setmE in r_d_eq; unfold_match' r_d_eq; [ convert_eq_op |]; simpl in r_d_eq).
             all: try (simpl; tauto).
             rewrite <- reg_domm3. setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). exists d. trivial. }
           rewrite reg_domm3 in r_in.
           repeat (destruct r_in as [? | r_in]; try subst r; repeat (rewrite setmE in r_d_eq; simpl in r_d_eq)).
           all: simpl in r_d_eq; try simplify_some; simpl; trivial.
           rewrite vt_eq12. eexists; split; done.
           { destruct d; unfold is_other in *; unfold_match Heqa52. }
           inversion r_in.
        -- unfold memory_match. simpl.
           intros w d d_code d_ip. split; intro w_eq.
           { destruct (fst (mem_match w d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
             simpl in *. exists d''. split; [|exact d''eq].
             destruct d; destruct d'' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
               split; [trivial|]; split; [trivial|]; simpl in *.
             destruct H16; subst. destruct d''t; try exact H16. destruct H16 as [sv' [comp'' inM]].
             exists sv', comp''. right. trivial. }
           { destruct (snd (mem_match w d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
             simpl in *. exists d''. split; [|exact d''eq].
             destruct d; destruct d'' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
               split; [trivial|]; split; [trivial|]; simpl in *.
             destruct H16; subst. destruct d''t; try exact H16. destruct H16 as [sv' [comp'' inM]].
             exists sv', comp''. right. trivial. }
        -- unfold registers_match. simpl. intros w d.
           split; intro w_eq.
           { repeat (rewrite setmE in w_eq; unfold_match' w_eq; [ convert_eq_op |]; simpl in w_eq).
             all: try simplify_some.
             all: repeat (rewrite setmE; simpl).
             1-12: eexists; split; [| reflexivity].
             1-12: try (split; trivial).
             { destruct d as [v_d t_d]. unfold is_other in *. destruct t_d; inversion Heqa51.
               split; trivial. rewrite setmE in Heqa52. simpl in Heqa52. rewrite <- Heqa52 in H12. simplify_some. trivial. }
             { subst pc3_val. eexists. eexists. left. rewrite <- addwA, (addwC onew), addwA. reflexivity. }
             simpl. unfold as_word. unfold ssrint.absz. simpl.
             repeat (match goal with | H: false = ?c |- context[?c] => rewrite <- H end).
             exfalso.
             assert (r_in : In w (domm regs3)).
             { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). exists d. trivial. }
             rewrite reg_domm3 in r_in.
             repeat (destruct r_in as [| r_in] ; [subst w ; simpl in *|] ).
             all: repeat
               (match goal with
                  H : false = eq_op _ _ |- _ => (rewrite eq_refl in H; inv H; done) || clear H
                end).
             inversion r_in. }

           { repeat (rewrite setmE in w_eq; unfold_match' w_eq; [ convert_eq_op |]; simpl in w_eq).
             all: try simplify_some.
             all: repeat (rewrite setmE; simpl).
             1-12: eexists; split; [| reflexivity].
             1-12: try (split; trivial).
             { destruct a22 as [v_d t_d]. unfold is_other in *. destruct t_d; inversion Heqa51.
               split; trivial. rewrite setmE in Heqa52. simpl in Heqa52. rewrite <- Heqa52 in H12. simplify_some. trivial. }
             { subst pc3_val. eexists. eexists. left. rewrite <- addwA, (addwC onew), addwA. reflexivity. }
             simpl. unfold as_word. unfold ssrint.absz. simpl.
             repeat (match goal with | H: false = ?c |- context[?c] => rewrite <- H end).
             exfalso.
             assert (r_in : In w (domm reg0)).
             { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). exists d. trivial. }
             rewrite reg_domm1 in r_in.
             repeat (destruct r_in as [| r_in] ; [subst w ; simpl in *|] ).
             all: repeat
               (match goal with
                  H : false = eq_op _ _ |- _ => (rewrite eq_refl in H; inv H; done) || clear H
                end).
             inversion r_in. }
        -- inversion weak; trivial.
        -- unfold side_of. rewrite ip_comp'. trivial.
        -- inversion weak; trivial.
        -- inversion weak; trivial.
        -- inversion weak; trivial.
        -- unfold register_address_correctness. simpl.
           intros d r r_d_eq.
           unfold register_domm in *.
           assert (r_in : In r (domm regs3)).
           { clear - reg_domm3 r_d_eq. rewrite reg_domm3.
             repeat (rewrite setmE in r_d_eq; unfold_match' r_d_eq; [ convert_eq_op |]; simpl in r_d_eq).
             all: try (simpl; tauto).
             rewrite <- reg_domm3. setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). exists d. trivial. }
           rewrite reg_domm3 in r_in.
           repeat (destruct r_in as [? | r_in]; try subst r; repeat (rewrite setmE in r_d_eq; simpl in r_d_eq)).
           all: simpl in r_d_eq; try simplify_some; simpl; trivial.
           rewrite vt_eq12. eexists; split; done.
           { destruct d; unfold is_other in *; unfold_match Heqa52. }
           inversion r_in.
        -- unfold memory_match. simpl. inversion weak as [? ? ? _ _ _ _ _ _ _ mem_match']. subst.
           intros w d d_code d_ip. split; intro w_eq.
           { destruct (fst (mem_match' w d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
             simpl in *. exists d''. split; [|exact d''eq].
             destruct d; destruct d'' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
               split; [trivial|]; split; [trivial|]; simpl in *.
             destruct H16; subst. destruct d''t; try exact H16. destruct H16 as [sv' [comp'' inM]].
             exists sv', comp''. right. trivial. }
           { destruct (snd (mem_match' w d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
             simpl in *. exists d''. split; [|exact d''eq].
             destruct d; destruct d'' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
               split; [trivial|]; split; [trivial|]; simpl in *.
             destruct H16; subst. destruct d''t; try exact H16. destruct H16 as [sv' [comp'' inM]].
             exists sv', comp''. right. trivial. }
    + (* call from comp in P to comp' in C *)
      repeat
      (match goal with
         H : Some ?a = getm reg0 _ |- _ => deduce_equality (esym H); pose proof (esym H); clear H
       end).
      deduce_equality OLD0.
      subst s1. unfold side_of in *. unfold_match' side_eq. simpl in *.
      deduce_equality PC0.
      pose proof (end_s1 _ _ PC0) as end_cond. simpl in end_cond.
      revert end_cond. decode_instr_eq. intro end_cond. destruct end_cond as [ | [? [eq1 code_RA0]]]; auto; try tauto.
      rewrite RA0 in eq1. simplify_some. simpl in code_RA0. destruct tret. unfold_match' a21_eq. convert_eq_op.
      rewrite eq_s3 in H13, tag_pc1, tag_pc3. destruct pc3_tag. simpl in H13, tag_pc1, tag_pc3.
      inversion tag_pc1. inversion tag_pc3. clear tag_pc1 tag_pc3. subst n0 n1 i2. rename color into comp.
      deduce_equality RA0.
      (* quick proof that v12 (s3) is a JAL offseted from i0 *)
      unfold_match' Heqa2.
      inversion vt_match11; try subst i0; revert H13; decode_instr_eq; intro H13.
      { destruct (H13 imm0); auto. }
      { inversion H13. subst imm0 pc'0. unfold alloc_empty in *. subst. simpl in alloc_mem_s1.
        assert (sw_eq: @swcast _ (word_size mt) (@word_of_nat (imm_size mt) alloc_label) = word_of_nat alloc_label).
        { admit. } simpl in sw_eq.
        rewrite <- sw_eq in alloc_mem_s1. rewrite <- Heqa63 in alloc_mem_s1. inversion alloc_mem_s1. }
      inversion H13. subst imm1. clear H13. subst pc'0. rewrite H15 in Heqa63. simplify_some. simpl in *.
      rename taga into td. rename vala into vd. rename H16 into eq_next_pc.
      assert (exists off', offset2 comp' = Some off') as [off' eq_off'].
      { eapply (rwP dommP). rewrite offset2_domm. trivial. }
      rewrite <- tag_mem_w0 in H19. simpl in H19.
      assert (eq_off'_alt: get_offset (side_of comp') comp' = Some off').
      { rewrite <- eq_off'. unfold side_of.
        destruct (comp' \in domm ip) eqn: comp'_ip.
        { exfalso. eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
          inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. }
        rewrite comp'_ip. simpl. trivial. }
      pose proof (H19 off' (eq_off'_alt)) as imm'_eq.
      assert (imm'eq: @swcast _ (word_size mt) imm' = (swcast imm0 + as_word off')%w).
      { subst imm'. admit. } (* need more hypothesis *)
      rewrite imm'eq in eq_next_pc.
      remember (((pc1 + 1)%w@(Ret n), (pc0 + 1)%w@(Ret n), (pc1 + 1 + as_word off)%w@(Ret n), comp) :: M) as M'.
      eexists. exists M'.
      split.
      * eapply (plus_left _ [:: ECall _ _ _ _] ). eapply step_jal; eauto.
        -- rewrite eq_s3 in vt_eq11. exact vt_eq11.
        -- rewrite eq_s3 in vt_eq12. exact vt_eq12.
        -- simpl. exact H14.
        -- rewrite eq_s3 in vt_eq10. exact vt_eq10.
        -- unfold reg_clear_list, reg_list. simpl. unfold as_word. subst. simpl.
           repeat
             (match goal with
              | H: _ ?w = _  |- context[_ ?w] => rewrite H; simpl
              end). trivial.
        -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
           unfold evi in *. simpl. unfold_bind.
           deduce_reg reg_match. rewrite imm'eq. rewrite eq_next_pc. simpl. rewrite eq_refl. simpl.
           simpl in *. rewrite <- tag_mem_w0. rewrite <- H18, <- tag_mem_w0.
           unfold check_belong, belong. rewrite eq_refl. simpl.
           rewrite eq_s3 in Heqa35. simpl in Heqa35. rewrite <- Heqa35. simpl.
           destruct a22 as [va22 ta22]. unfold is_other in *. destruct ta22; simpl in Heqa51; inversion Heqa51.
           inversion vt_match9 as [? _]; subst t9. simpl. subst s3. rewrite vt_eq12.
           simpl in Heqa34. rewrite <- Heqa34. simpl.
           unfold updm. unfold as_word. simpl in *.
           (*automatically rewrite regs3 registers*)
           repeat
             (repeat
                (simpl; match goal with
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
           destruct x as [vx tx]. inversion H13. subst tx vx.
           reflexivity.
        -- eapply star_refl.
        -- unfold evi in Heqa, Heqa0. repeat unfold_bind. inv Heqa. inv Heqa0. simpl.
           simpl in *. rewrite H16. rewrite H12 in Heqa46. simplify_some. reflexivity.
      * subst. simpl in *.
        pose proof (end_s2 _ _ PC) as end_cond. simpl in end_cond.
        revert end_cond. decode_instr_eq. intro end_cond. destruct end_cond as [ | [? [eq1 code_RA]]]; auto; try tauto.
        rewrite RA in eq1. simplify_some. simpl in code_RA.
        rewrite (@setmI _ _ mem1). 2:{ rewrite <- Heqa50 in RA0. simplify_some. simpl. done. }
        rewrite (@setmI _ _ mem0). 2:{ rewrite <- Heqa22 in RA. simplify_some. simpl. done. }
        rewrite (@setmI _ _ mem3). 2:{ trivial. }
        eapply match_states_right; econstructor; simpl; unfold build_tpc; try trivial.
        -- rewrite <- (addn1 n).
           eapply wf_stack_cons_left; simpl; eauto.
           ++ unfold points_to_comp_code'. rewrite RA0. simpl. split; [ | right]; trivial.
           ++ unfold points_to_comp_code. rewrite RA. simpl. split; trivial.
           ++ unfold points_to_comp_code. subst pc3_val.
              rewrite <- addwA, (addwC _ onew), addwA in vt_eq12. rewrite vt_eq12. simpl. split; auto.
        -- unfold register_domm. repeat rewrite domm_set. simpl.
           unfold register_domm, reg_field_size, mword, FSet.fsval in reg_domm1. simpl in reg_domm1.
           unfold mword, word_size. simpl.
           clear - reg_domm1. unfold_match' reg_domm1. admit. (* exstructure *)
        -- unfold register_domm. repeat rewrite domm_set. simpl.
           unfold register_domm, reg_field_size, mword, FSet.fsval in reg_domm2. simpl in reg_domm2.
           unfold mword, word_size. simpl.
           clear - reg_domm2. unfold_match' reg_domm2. admit. (* exstructure *)
        -- unfold register_domm. repeat rewrite domm_set. simpl.
           unfold register_domm, reg_field_size, mword, FSet.fsval in reg_domm3. simpl in reg_domm3.
           unfold mword, word_size. simpl.
           clear - reg_domm3. unfold_match' reg_domm3. admit. (* exstructure *)
        -- split; [|split; [|split; [|split; [|split; [|split]]]]]; trivial.
        -- split; [|split; [|split; [|split; [|split; [|split]]]]]; trivial.
        -- split; [|split; [|split; [|split; [|split; [|split]]]]]; trivial.
        -- intros d q rw rweq.
           destruct rw as [r | w]; simpl; simpl in rweq.
           ++ repeat rewrite setmE in rweq. repeat (unfold_match' rweq).
              ** convert_eq_op. simplify_some. subst d q.
                 split; [unfold in_stack; do 3 eexists; econstructor; eauto |].
                 intros rw d. destruct rw as [r | w].
                 { intro rweq. repeat rewrite setmE in rweq. repeat unfold_match' rweq. convert_eq_op; trivial.
                   exfalso.
                   assert (r_in : In r (domm reg0)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm1 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
                 { intro tex. pose proof (capa_cor1 d n (inr w) tex) as [is_in unicity].
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
              ** exfalso.
                 assert (r_in : In r (domm reg0)).
                 { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                 exfalso. rewrite reg_domm1 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                 repeat (destruct r_in as [|r_in];
                         [subst;
                          (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                 inversion r_in.
           ++ pose proof (capa_cor1 d q (inr w) rweq) as [is_in unicity].
              split. { clear -is_in. unfold in_stack in *. destruct is_in as [sv1 [sv2 [col is_in]]]. do 3 eexists. right. eauto. }
              intros [r' | w'] d''.
              ** intro rweq'. repeat rewrite setmE in rweq'. repeat unfold_match' rweq'.
                 { convert_eq_op. simplify_some. subst d'' q.
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
                 { assert (r_in : In r' (domm reg0)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm1 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
              ** eapply (unicity (inr w')).
        -- intros d q rw rweq.
           destruct rw as [r | w]; simpl; simpl in rweq.
           ++ repeat rewrite setmE in rweq. repeat (unfold_match' rweq).
              ** convert_eq_op. simplify_some. subst d q.
                 split; [unfold in_stack; do 3 eexists; econstructor; eauto |].
                 intros rw d. destruct rw as [r | w].
                 { intro rweq. repeat rewrite setmE in rweq. repeat unfold_match' rweq. convert_eq_op; trivial.
                   exfalso.
                   assert (r_in : In r (domm reg)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm2 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
                 { intro tex. pose proof (capa_cor2 d n (inr w) tex) as [is_in unicity].
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
              ** exfalso.
                 assert (r_in : In r (domm reg)).
                 { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                 exfalso. rewrite reg_domm2 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                 repeat (destruct r_in as [|r_in];
                         [subst;
                          (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                 inversion r_in.
           ++ pose proof (capa_cor2 d q (inr w) rweq) as [is_in unicity].
              split. { clear -is_in. unfold in_stack in *. destruct is_in as [sv1 [sv2 [col is_in]]]. do 3 eexists. right. eauto. }
              intros [r' | w'] d''.
              ** intro rweq'. repeat rewrite setmE in rweq'. repeat unfold_match' rweq'.
                 { convert_eq_op. simplify_some. subst d'' q.
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
                 { assert (r_in : In r' (domm reg)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm2 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
              ** eapply (unicity (inr w')).
        -- intros d q rw rweq.
           destruct rw as [r | w]; simpl; simpl in rweq.
           ++ repeat rewrite setmE in rweq. repeat (unfold_match' rweq).
              ** convert_eq_op. simplify_some. inversion Heqa51.
              ** convert_eq_op. simplify_some. subst d q pc3_val.
                 split; [unfold in_stack; do 3 eexists; econstructor; rewrite <- addwA, (addwC onew), addwA; eauto|].
                 intros rw d. destruct rw as [r | w].
                 { intro rweq. destruct a22 as [va ta]. destruct ta; inversion Heqa51.
                   repeat rewrite setmE in rweq. repeat unfold_match' rweq.
                   all: repeat simplify_some; convert_eq_op; trivial.
                   exfalso.
                   assert (r_in : In r (domm regs3)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm3 in r_in. simpl in r_in. unfold word_of_nat, as_word in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (Word ?a == Word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
                 { intro tex. pose proof (capa_cor3 d n (inr w) tex) as [is_in unicity].
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
              ** assert (r_in : In r (domm regs3)).
                 { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                 exfalso. rewrite reg_domm3 in r_in. simpl in r_in. unfold word_of_nat, as_word in r_in. simpl in r_in.
                 repeat (destruct r_in as [|r_in];
                         [subst;
                          (match goal with H : false = (Word ?a == Word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                 inversion r_in.
           ++ pose proof (capa_cor3 d q (inr w) rweq) as [is_in unicity].
              split. { clear -is_in. unfold in_stack in *. destruct is_in as [sv1 [sv2 [col is_in]]]. do 3 eexists. right. eauto. }
              intros [r' | w'] d''.
              ** intro rweq'. repeat rewrite setmE in rweq'. repeat unfold_match' rweq'.
                 { convert_eq_op. simplify_some. inversion Heqa51. }
                 { convert_eq_op. simplify_some. subst d'' q.
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
                 { assert (r_in : In r' (domm regs3)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm3 in r_in. simpl in r_in. unfold word_of_nat, as_word in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (Word ?a == Word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
              ** eapply (unicity (inr w')).
        -- unfold side_of.
           goal_match_bind_step; try trivial.
           { exfalso. eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
             inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. }
        -- unfold register_address_correctness. simpl.
           intros d r r_d_eq.
           unfold register_domm in *.
           assert (r_in : In r (domm regs3)).
           { clear - reg_domm3 r_d_eq. rewrite reg_domm3.
             repeat (rewrite setmE in r_d_eq; unfold_match' r_d_eq; [ convert_eq_op |]; simpl in r_d_eq).
             all: try (simpl; tauto).
             rewrite <- reg_domm3. setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). exists d. trivial. }
           rewrite reg_domm3 in r_in.
           repeat (destruct r_in as [? | r_in]; try subst r; repeat (rewrite setmE in r_d_eq; simpl in r_d_eq)).
           all: simpl in r_d_eq; try simplify_some; simpl; trivial.
           rewrite vt_eq12. eexists; split; done.
           { destruct d; unfold is_other in *; unfold_match Heqa52. }
           inversion r_in.
        -- unfold memory_match. simpl.
           intros w d d_code d_ip. split; intro w_eq.
           { destruct (fst (mem_match w d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
             simpl in *. exists d''. split; [|exact d''eq].
             destruct d; destruct d'' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
               split; [trivial|]; split; [trivial|]; simpl in *.
             destruct H16; subst. destruct d''t; try exact H16. destruct H16 as [sv' [comp'' inM]].
             exists sv', comp''. right. trivial. }
           { destruct (snd (mem_match w d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
             simpl in *. exists d''. split; [|exact d''eq].
             destruct d; destruct d'' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
               split; [trivial|]; split; [trivial|]; simpl in *.
             destruct H16; subst. destruct d''t; try exact H16. destruct H16 as [sv' [comp'' inM]].
             exists sv', comp''. right. trivial. }
        -- inversion weak; trivial.
        -- inversion weak as [? ? ? _ _ _ _ _ entry_off' _ _].
           inversion Heqa2.
           pose proof (entry_off' _ _ _ _ _ i1 l l0 ic_comp' (esym Heqa3) eq_next_pc) as same_entry.
           destruct same_entry as [off'' [off''eq pc'eq]]; simpl; try rewrite <- H22; try rewrite <- H18; simpl; try trivial.
           ++ pose proof (entry_code2 _ a45 (i1, l) (esym Heqa3) (congr1 LRC.entry (esym H22))); eauto.
              simpl in *. rewrite <- H22 in H21. trivial.
           ++ simpl in *. eapply same_pc_normal; simpl; eauto.
        -- unfold side_of.
           goal_match_bind_step; try trivial.
           { exfalso. eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
             inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. }
        -- inversion weak. trivial.
        -- inversion weak. trivial.
        -- inversion weak. trivial.
        -- unfold register_address_correctness. simpl.
           intros d r r_d_eq.
           unfold register_domm in *.
           assert (r_in : In r (domm reg)).
           { clear - reg_domm2 r_d_eq. rewrite reg_domm2.
             repeat (rewrite setmE in r_d_eq; unfold_match' r_d_eq; [ convert_eq_op |]; simpl in r_d_eq).
             all: try (simpl; tauto).
             rewrite <- reg_domm2. setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). exists d. trivial. }
           rewrite reg_domm2 in r_in.
           repeat (destruct r_in as [? | r_in]; try subst r; repeat (rewrite setmE in r_d_eq; simpl in r_d_eq)).
           all: simpl in r_d_eq; try simplify_some; simpl; trivial.
           rewrite RA. eexists; split; done.
           inversion r_in.
        -- unfold register_address_correctness. simpl.
           intros d r r_d_eq.
           unfold register_domm in *.
           assert (r_in : In r (domm regs3)).
           { clear - reg_domm3 r_d_eq. rewrite reg_domm3.
             repeat (rewrite setmE in r_d_eq; unfold_match' r_d_eq; [ convert_eq_op |]; simpl in r_d_eq).
             all: try (simpl; tauto).
             rewrite <- reg_domm3. setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). exists d. trivial. }
           rewrite reg_domm3 in r_in.
           repeat (destruct r_in as [? | r_in]; try subst r; repeat (rewrite setmE in r_d_eq; simpl in r_d_eq)).
           all: simpl in r_d_eq; try simplify_some; simpl; trivial.
           rewrite vt_eq12. eexists; split; done.
           { destruct d; unfold is_other in *; unfold_match Heqa52. }
           inversion r_in.
        -- unfold memory_match. simpl. inversion weak as [? ? ? _ _ _ _ _ _ _ mem_match']. subst.
           intros w d d_code d_ip. split; intro w_eq.
           { destruct (fst (mem_match' w d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
             simpl in *. exists d''. split; [|exact d''eq].
             destruct d; destruct d'' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
               split; [trivial|]; split; [trivial|]; simpl in *.
             destruct H16; subst. destruct d''t; try exact H16. destruct H16 as [sv' [comp'' inM]].
             exists sv', comp''. right. trivial. }
           { destruct (snd (mem_match' w d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
             simpl in *. exists d''. split; [|exact d''eq].
             destruct d; destruct d'' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
               split; [trivial|]; split; [trivial|]; simpl in *.
             destruct H16; subst. destruct d''t; try exact H16. destruct H16 as [sv' [comp'' inM]].
             exists sv', comp''. right. trivial. }
        -- unfold registers_match. simpl. intros w d.
           split; intro w_eq.
           { repeat (rewrite setmE in w_eq; unfold_match' w_eq; [ convert_eq_op |]; simpl in w_eq).
             all: try simplify_some.
             all: repeat (rewrite setmE; simpl).
             1-12: eexists; split; [| reflexivity].
             1-12: try (split; trivial).
             { destruct d as [v_d t_d]. unfold is_other in *. destruct t_d; inversion Heqa51.
               split; trivial.
               unfold evi in Heqa, Heqa0. simpl in Heqa, Heqa0. do 2 unfold_bind. inversion Heqa. repeat simplify_some.
               unfold as_word in Heqa44. simpl in Heqa44. rewrite <- Heqa24 in Heqa44. repeat simplify_some.
               rewrite H16 in H13. clear -H13. simpl in H13. remember (vala a20) as v.
               unfold mword, mt, concrete_int_32_mt in Heqv. simpl in Heqv. rewrite <- Heqv in H13. clear Heqv a20.
               admit. } (* TODO : convert & int_of_word injectivity *)
             { subst pc3_val. eexists. eexists. left. rewrite <- addwA, (addwC onew), addwA. reflexivity. }
             simpl. unfold as_word. unfold ssrint.absz. simpl.
             repeat (match goal with | H: false = ?c |- context[?c] => rewrite <- H end).
             exfalso.
             assert (r_in : In w (domm regs3)).
             { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). exists d. trivial. }
             rewrite reg_domm3 in r_in.
             repeat (destruct r_in as [| r_in] ; [subst w ; simpl in *|] ).
             all: repeat
               (match goal with
                  H : false = eq_op _ _ |- _ => (rewrite eq_refl in H; inv H; done) || clear H
                end).
             inversion r_in. }

           { repeat (rewrite setmE in w_eq; unfold_match' w_eq; [ convert_eq_op |]; simpl in w_eq).
             all: try simplify_some.
             all: repeat (rewrite setmE; simpl).
             1-12: eexists; split; [| reflexivity].
             1-12: try (split; trivial).
             { destruct a22 as [v_d t_d]. unfold is_other in *. destruct t_d; inversion Heqa51.
               split; trivial.
               unfold evi in Heqa, Heqa0. simpl in Heqa, Heqa0. do 2 unfold_bind. inversion Heqa. repeat simplify_some.
               unfold as_word in Heqa44. simpl in Heqa44. rewrite <- Heqa24 in Heqa44. repeat simplify_some.
               rewrite H16 in H13. clear -H13. simpl in H13. remember (vala a20) as v.
               unfold mword, mt, concrete_int_32_mt in Heqv. simpl in Heqv. rewrite <- Heqv in H13. clear Heqv a20.
               admit. } (* TODO : convert & int_of_word injectivity *)
             { subst pc3_val. eexists. eexists. left. rewrite <- addwA, (addwC onew), addwA. reflexivity. }
             simpl. unfold as_word. unfold ssrint.absz. simpl.
             repeat (match goal with | H: false = ?c |- context[?c] => rewrite <- H end).
             exfalso.
             assert (r_in : In w (domm reg)).
             { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). exists d. trivial. }
             rewrite reg_domm2 in r_in.
             repeat (destruct r_in as [| r_in] ; [subst w ; simpl in *|] ).
             all: repeat
               (match goal with
                  H : false = eq_op _ _ |- _ => (rewrite eq_refl in H; inv H; done) || clear H
                end).
             inversion r_in. }
    + (* call from comp in C to comp' in P *)
      repeat
      (match goal with
         H : Some ?a = getm reg _ |- _ => deduce_equality (esym H); pose proof (esym H); clear H
       end).
      deduce_equality OLD.
      subst s2. unfold side_of in *. unfold_match' side_eq. simpl in *.
      assert (side_eq': true = (comp \in domm ic)).
      { assert (comp_incl: comp \in (domm ic) \/ comp \in (domm ip)) by
          (rewrite ST0 in col_mem1; pose proof (col_mem1 _ _ PC0) as in_disj; simpl in in_disj;
           setoid_rewrite <- Extra.In_in in in_disj; exact ((fst (or_comm _ _)) in_disj)).
        destruct comp_incl as [Hl | Hr]. rewrite Hl. trivial. rewrite Hr in Heqa5. inversion Heqa5. }
      deduce_equality PC.
      pose proof (end_s2 _ _ PC) as end_cond. simpl in end_cond.
      revert end_cond. decode_instr_eq. intro end_cond. destruct end_cond as [ | [? [eq1 code_RA]]]; auto; try tauto.
      rewrite RA in eq1. simplify_some. simpl in code_RA.
      deduce_equality RA.
      (* quick proof that v12 (s3) is a JAL offseted from i0 *)
      unfold_match' Heqa2. inversion Heqa2 as [tag_mem_w].
      inversion vt_match11; try subst i0; revert H12; decode_instr_eq; intro H12.
      { destruct (H12 imm); auto. }
      { inversion H12. subst imm pc'. unfold alloc_empty in *. subst. simpl in alloc_mem_s2.
        assert (sw_eq: @swcast _ (word_size mt) (@word_of_nat (imm_size mt) alloc_label) = word_of_nat alloc_label).
        { admit. } simpl in sw_eq.
        rewrite <- sw_eq in alloc_mem_s2. rewrite <- Heqa6 in alloc_mem_s2. inversion alloc_mem_s2. }
      inversion H12. subst imm1. clear H12. subst pc'. rewrite H14 in Heqa6. simplify_some. simpl in *.
      rename taga into td. rename vala into vd. rename H15 into eq_next_pc.
      assert (exists off', offset1 comp' = Some off') as [off' eq_off'].
      { eapply (rwP dommP). rewrite offset1_domm. trivial. }
      rewrite <- tag_mem_w in H18. simpl in H18.
      assert (eq_off'_alt: get_offset (side_of comp') comp' = Some off').
      { rewrite <- eq_off'. unfold side_of. rewrite ip_comp'. trivial. }
      pose proof (H18 off' (eq_off'_alt)) as imm'_eq.
      assert (imm'eq: @swcast _ (word_size mt) imm' = (swcast imm + as_word off')%w).
      { subst imm'. admit. } (* need more hypothesis *)
      rewrite imm'eq in eq_next_pc.
      remember (((pc1 + 1)%w@(Ret n), (pc0 + 1)%w@(Ret n1), (pc0 + 1 + as_word off)%w@(Ret n1), comp) :: M) as M'.
      eexists. exists M'.
      split.
      * eapply (plus_left _ [:: ECall _ _ _ _] ). eapply step_jal; eauto.
        -- rewrite eq_s3 in vt_eq11. exact vt_eq11.
        -- rewrite eq_s3 in vt_eq12. exact vt_eq12.
        -- simpl. exact H13.
        -- rewrite eq_s3 in vt_eq10. exact vt_eq10.
        -- unfold reg_clear_list, reg_list. simpl. unfold as_word. subst. simpl.
           repeat
             (match goal with
              | H: _ ?w = _  |- context[_ ?w] => rewrite H; simpl
              end). trivial.
        -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
           unfold evi in *. simpl. unfold_bind.
           deduce_reg reg_match. rewrite imm'eq. rewrite eq_next_pc. simpl.
           rewrite eq_s3 in tag_pc3. simpl in tag_pc3. rewrite tag_pc3. simpl. rewrite eq_refl. simpl.
           simpl in *. rewrite <- H17, <- tag_mem_w. rewrite <- Heqa35. simpl.
           unfold check_belong, belong. rewrite eq_refl. simpl.
           destruct a as [va ta]. unfold is_other in *. destruct ta; simpl in Heqa36; inversion Heqa36.
           inversion vt_match9 as [? _]; subst t9. simpl. rewrite <- Heqa7. simpl. subst s3. rewrite vt_eq12.
           unfold updm. unfold as_word. simpl in *.
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
           destruct x as [vx tx]. inversion H12. subst tx vx.
           reflexivity.
        -- eapply star_refl.
        -- unfold evi in Heqa, Heqa0. repeat unfold_bind. inv Heqa. inv Heqa0. simpl.
           simpl in *. rewrite H11 in Heqa8. simplify_some. reflexivity.
      * subst. simpl in *.
        rewrite (@setmI _ _ mem1). 2:{ rewrite <- Heqa47 in RA0. simplify_some. simpl. done. }
        rewrite (@setmI _ _ mem0). 2:{ rewrite <- Heqa22 in RA. simplify_some. simpl. done. }
        rewrite (@setmI _ _ mem3). 2:{ trivial. }
        inversion tag_pc1. subst n1. clear tag_pc1. destruct pc3_tag as [n0 comp].
        inversion tag_pc3. subst n0. clear tag_pc3.
        eapply match_states_left; econstructor; simpl; unfold build_tpc; try trivial.
        -- rewrite <- (addn1 n).
           eapply wf_stack_cons_right; simpl; eauto.
           ++ unfold points_to_comp_code'. rewrite RA0. simpl. split; [ | left]; trivial.
              destruct tret; unfold_match' a21_eq. convert_eq_op. trivial.
              split; auto. unfold side_of. simpl. rewrite <- Heqa5. trivial.
           ++ unfold points_to_comp_code. rewrite RA. simpl. split; trivial.
           ++ unfold points_to_comp_code. subst pc3_val.
              rewrite <- addwA, (addwC _ onew), addwA in vt_eq12. rewrite vt_eq12. simpl. split; auto.
        -- unfold register_domm. repeat rewrite domm_set. simpl.
           unfold register_domm, reg_field_size, mword, FSet.fsval in reg_domm1. simpl in reg_domm1.
           unfold mword, word_size. simpl.
           clear - reg_domm1. unfold_match' reg_domm1. admit. (* exstructure *)
        -- unfold register_domm. repeat rewrite domm_set. simpl.
           unfold register_domm, reg_field_size, mword, FSet.fsval in reg_domm2. simpl in reg_domm2.
           unfold mword, word_size. simpl.
           clear - reg_domm2. unfold_match' reg_domm2. admit. (* exstructure *)
        -- unfold register_domm. repeat rewrite domm_set. simpl.
           unfold register_domm, reg_field_size, mword, FSet.fsval in reg_domm3. simpl in reg_domm3.
           unfold mword, word_size. simpl.
           clear - reg_domm3. unfold_match' reg_domm3. admit. (* exstructure *)
        -- split; [|split; [|split; [|split; [|split; [|split]]]]]; trivial.
        -- split; [|split; [|split; [|split; [|split; [|split]]]]]; trivial.
        -- split; [|split; [|split; [|split; [|split; [|split]]]]]; trivial.
        -- intros d'' q rw rweq.
           destruct rw as [r | w]; simpl; simpl in rweq.
           ++ repeat rewrite setmE in rweq. repeat (unfold_match' rweq).
              ** convert_eq_op. simplify_some. subst d'' q.
                 split; [unfold in_stack; do 3 eexists; econstructor; eauto |].
                 intros rw d''. destruct rw as [r | w].
                 { intro rweq. repeat rewrite setmE in rweq. repeat unfold_match' rweq. convert_eq_op; trivial.
                   exfalso.
                   assert (r_in : In r (domm reg0)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm1 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
                 { intro tex. pose proof (capa_cor1 d'' n (inr w) tex) as [is_in unicity].
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
              ** exfalso.
                 assert (r_in : In r (domm reg0)).
                 { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                 exfalso. rewrite reg_domm1 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                 repeat (destruct r_in as [|r_in];
                         [subst;
                          (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                 inversion r_in.
           ++ pose proof (capa_cor1 d'' q (inr w) rweq) as [is_in unicity].
              split. { clear -is_in. unfold in_stack in *. destruct is_in as [sv1 [sv2 [col is_in]]]. do 3 eexists. right. eauto. }
              intros [r' | w'] d'''.
              ** intro rweq'. repeat rewrite setmE in rweq'. repeat unfold_match' rweq'.
                 { convert_eq_op. simplify_some. subst d''' q.
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
                 { assert (r_in : In r' (domm reg0)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm1 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
              ** eapply (unicity (inr w')).
        -- intros d'' q rw rweq.
           destruct rw as [r | w]; simpl; simpl in rweq.
           ++ repeat rewrite setmE in rweq. repeat (unfold_match' rweq).
              ** convert_eq_op. simplify_some. subst d'' q.
                 split; [unfold in_stack; do 3 eexists; econstructor; eauto |].
                 intros rw d''. destruct rw as [r | w].
                 { intro rweq. repeat rewrite setmE in rweq. repeat unfold_match' rweq. convert_eq_op; trivial.
                   exfalso.
                   assert (r_in : In r (domm reg)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm2 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
                 { intro tex. pose proof (capa_cor2 d'' n (inr w) tex) as [is_in unicity].
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
              ** exfalso.
                 assert (r_in : In r (domm reg)).
                 { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                 exfalso. rewrite reg_domm2 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                 repeat (destruct r_in as [|r_in];
                         [subst;
                          (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                 inversion r_in.
           ++ pose proof (capa_cor2 d'' q (inr w) rweq) as [is_in unicity].
              split. { clear -is_in. unfold in_stack in *. destruct is_in as [sv1 [sv2 [col is_in]]]. do 3 eexists. right. eauto. }
              intros [r' | w'] d'''.
              ** intro rweq'. repeat rewrite setmE in rweq'. repeat unfold_match' rweq'.
                 { convert_eq_op. simplify_some. subst d''' q.
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
                 { assert (r_in : In r' (domm reg)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm2 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
              ** eapply (unicity (inr w')).
        -- intros d'' q rw rweq.
           destruct rw as [r | w]; simpl; simpl in rweq.
           ++ repeat rewrite setmE in rweq. repeat (unfold_match' rweq).
              ** convert_eq_op. simplify_some. inversion Heqa36.
              ** convert_eq_op. simplify_some. subst d'' q pc3_val.
                 split; [unfold in_stack; do 3 eexists; econstructor; rewrite <- addwA, (addwC onew), addwA; eauto|].
                 intros rw d''. destruct rw as [r | w].
                 { intro rweq. destruct a as [va ta]. destruct ta; inversion Heqa36.
                   repeat rewrite setmE in rweq. repeat unfold_match' rweq.
                   all: repeat simplify_some; convert_eq_op; trivial.
                   { assert (r_in : In r (domm regs3)).
                     { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                     exfalso. rewrite reg_domm3 in r_in. simpl in r_in. unfold word_of_nat, as_word in r_in. simpl in r_in.
                     repeat (destruct r_in as [|r_in];
                             [subst;
                              (match goal with H : false = (Word ?a == Word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                     inversion r_in. } }
                 { intro tex. pose proof (capa_cor3 d'' n (inr w) tex) as [is_in unicity].
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
              ** assert (r_in : In r (domm regs3)).
                 { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                 exfalso. rewrite reg_domm3 in r_in. simpl in r_in. unfold word_of_nat, as_word in r_in. simpl in r_in.
                 repeat (destruct r_in as [|r_in];
                         [subst;
                          (match goal with H : false = (Word ?a == Word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                 inversion r_in.
           ++ pose proof (capa_cor3 d'' q (inr w) rweq) as [is_in unicity].
              split. { clear -is_in. unfold in_stack in *. destruct is_in as [sv1 [sv2 [col is_in]]]. do 3 eexists. right. eauto. }
              intros [r' | w'] d'''.
              ** intro rweq'. repeat rewrite setmE in rweq'. repeat unfold_match' rweq'.
                 { convert_eq_op. simplify_some. inversion Heqa36. }
                 { convert_eq_op. simplify_some. subst d''' q.
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
                 { assert (r_in : In r' (domm regs3)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm3 in r_in. simpl in r_in. unfold word_of_nat, as_word in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (Word ?a == Word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
              ** eapply (unicity (inr w')).
        -- inversion weak. trivial.
        -- inversion weak as [? ? ? _ _ _ _ _ entry_off' _ _].
           inversion Heqa2.
           pose proof (entry_off' _ _ _ _ _ i1 l0 l ip_comp' (esym Heqa60) eq_next_pc) as same_entry.
           destruct same_entry as [off'' [off''eq pc'eq]]; simpl; try rewrite <- H17; try rewrite <- H21; trivial.
           ++ pose proof (entry_code1 _ _ (i1, l0) (esym Heqa60)); eauto.
           ++ pose proof (entry_code2 _ _ (i1, l) (H14)) as ent_cond; eauto. simpl in ent_cond. rewrite <- H21 in ent_cond.
              eapply ent_cond; eauto.
           ++ simpl in *. eapply same_pc_normal; simpl; eauto.
        -- unfold side_of. rewrite ip_comp'. trivial.
        -- inversion weak. trivial.
        -- inversion weak. trivial.
        -- inversion weak. trivial.
        -- unfold register_address_correctness. simpl.
           intros d'' r r_d_eq.
           unfold register_domm in *.
           repeat rewrite setmE in r_d_eq. repeat unfold_match' r_d_eq.
           { convert_eq_op. simplify_some. simpl. eexists. split. exact RA0. simpl.
             intro tret_ip. exfalso. destruct tret; unfold_match' a21_eq. convert_eq_op.
             simpl in tret_ip. eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
             inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. }
           assert (r_in : In r (domm reg0)).
           {  setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eauto. }
           exfalso. rewrite reg_domm1 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
           repeat (destruct r_in as [|r_in];
                   [subst;
                    (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
           inversion r_in.
        -- unfold register_address_correctness. simpl.
           intros d'' r r_d_eq.
           unfold register_domm in *.
           assert (r_in : In r (domm regs3)).
           { clear - reg_domm3 r_d_eq. rewrite reg_domm3.
             repeat (rewrite setmE in r_d_eq; unfold_match' r_d_eq; [ convert_eq_op |]; simpl in r_d_eq).
             all: try (simpl; tauto).
             rewrite <- reg_domm3. setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists. eauto. }
           rewrite reg_domm3 in r_in.
           repeat rewrite setmE in r_d_eq. repeat unfold_match' r_d_eq.
           { convert_eq_op. simplify_some. destruct d'' as [? d''t]. destruct d''t; inversion Heqa36.
             simpl. trivial. }
           { convert_eq_op. simplify_some. simpl. eexists. split. exact vt_eq12. trivial. }
           exfalso. simpl in r_in. unfold word_of_nat, as_word in r_in. simpl in r_in.
           repeat (destruct r_in as [|r_in];
                   [subst;
                    (match goal with H : false = (Word ?a == Word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
           inversion r_in.
        -- unfold memory_match. simpl. inversion weak as [? ? ? _ _ _ _ _ _ _ mem_match'].
           intros w d'' d_code d_ip. split; intro w_eq.
           { destruct (fst (mem_match' w d'' d_code d_ip) w_eq) as [d''' [d''match d''eq]].
             simpl in *. exists d'''. split; [|exact d''eq].
             destruct d'''; destruct d'' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
               split; [trivial|]; split; [trivial|]; simpl in *.
             destruct H21; subst. destruct d''t; try exact H15. destruct H15 as [sv' [comp'' inM]].
             exists sv', comp''. right. trivial. }
           { destruct (snd (mem_match' w d'' d_code d_ip) w_eq) as [d''' [d''match d''eq]].
             simpl in *. exists d'''. split; [|exact d''eq].
             destruct d'''; destruct d'' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
               split; [trivial|]; split; [trivial|]; simpl in *.
             destruct H21; subst. destruct d''t; try exact H15. destruct H15 as [sv' [comp'' inM]].
             exists sv', comp''. right. trivial. }
        -- unfold registers_match. simpl. intros w d''.
           split; intro w_eq.
           { repeat (rewrite setmE in w_eq; unfold_match' w_eq; [ convert_eq_op |]; simpl in w_eq).
             all: try simplify_some.
             all: repeat (rewrite setmE; simpl).
             1-12: eexists; split; [| reflexivity].
             1-12: try (split; trivial).
             { destruct d'' as [v_d t_d]. unfold is_other in *. destruct t_d; inversion Heqa36.
               split; trivial.
               unfold evi in Heqa, Heqa0. simpl in Heqa, Heqa0. do 2 unfold_bind. inversion Heqa. repeat simplify_some.
               rewrite setmE in Heqa49. simpl in Heqa49. rewrite <- Heqa17 in Heqa49. repeat simplify_some.
               remember (vala a) as v_a. unfold mword, mt, concrete_int_32_mt in Heqv_a.
               simpl in Heqv_a. rewrite <- Heqv_a in H12. rewrite H12 in H19. clear - H19.
               admit. } (* TODO : convert & int_of_word injectivity *)
             { subst pc3_val. eexists. eexists. left. rewrite <- addwA, (addwC onew), addwA. reflexivity. }
             simpl. unfold as_word. unfold ssrint.absz. simpl.
             repeat (match goal with | H: false = ?c |- context[?c] => rewrite <- H end).
             exfalso.
             assert (r_in : In w (domm regs3)).
             { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eauto. }
             rewrite reg_domm3 in r_in.
             repeat (destruct r_in as [| r_in] ; [subst w ; simpl in *|] ).
             all: repeat
               (match goal with
                  H : false = eq_op _ _ |- _ => (rewrite eq_refl in H; inv H; done) || clear H
                end).
             inversion r_in. }

           { repeat (rewrite setmE in w_eq; unfold_match' w_eq; [ convert_eq_op |]; simpl in w_eq).
             all: try simplify_some.
             all: repeat (rewrite setmE; simpl).
             1-12: eexists; split; [| reflexivity].
             1-12: try (split; trivial).
             { destruct a as [v_d t_d]. unfold is_other in *. destruct t_d; inversion Heqa36.
               split; trivial.
               unfold evi in Heqa, Heqa0. simpl in Heqa, Heqa0. do 2 unfold_bind. inversion Heqa. repeat simplify_some.
               rewrite setmE in Heqa49. simpl in Heqa49. rewrite <- Heqa17 in Heqa49. repeat simplify_some.
               remember (vala a) as v_a. unfold mword, mt, concrete_int_32_mt in Heqv_a.
               simpl in Heqv_a. rewrite <- Heqv_a in H12. rewrite H12 in H19. clear - H19.
               admit. } (* TODO : convert & int_of_word injectivity *)
             { subst pc3_val. eexists. eexists. left. rewrite <- addwA, (addwC onew), addwA. reflexivity. }
             simpl. unfold as_word. unfold ssrint.absz. simpl.
             repeat (match goal with | H: false = ?c |- context[?c] => rewrite <- H end).
             exfalso.
             assert (r_in : In w (domm reg0)).
             { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eauto. }
             rewrite reg_domm1 in r_in.
             repeat (destruct r_in as [| r_in] ; [subst w ; simpl in *|] ).
             all: repeat
               (match goal with
                  H : false = eq_op _ _ |- _ => (rewrite eq_refl in H; inv H; done) || clear H
                end).
             inversion r_in. }
        -- unfold side_of. rewrite ip_comp'. trivial.
        -- unfold register_address_correctness. simpl.
           intros d'' r r_d_eq.
           unfold register_domm in *.
           assert (r_in : In r (domm regs3)).
           { clear - reg_domm3 r_d_eq. rewrite reg_domm3.
             repeat (rewrite setmE in r_d_eq; unfold_match' r_d_eq; [ convert_eq_op |]; simpl in r_d_eq).
             all: try (simpl; tauto).
             rewrite <- reg_domm3. setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists. eauto. }
           rewrite reg_domm3 in r_in.
           repeat rewrite setmE in r_d_eq. repeat unfold_match' r_d_eq.
           { convert_eq_op. simplify_some. destruct d'' as [? d''t]. destruct d''t; inversion Heqa36.
             simpl. trivial. }
           { convert_eq_op. simplify_some. simpl. eexists. split. exact vt_eq12. trivial. }
           exfalso. simpl in r_in. unfold word_of_nat, as_word in r_in. simpl in r_in.
           repeat (destruct r_in as [|r_in];
                   [subst;
                    (match goal with H : false = (Word ?a == Word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
           inversion r_in.
        -- unfold memory_match. simpl. subst.
           intros w d'' d_code d_ip. split; intro w_eq.
           { destruct (fst (mem_match w d'' d_code d_ip) w_eq) as [d''' [d''match d''eq]].
             simpl in *. exists d'''. split; [|exact d''eq].
             destruct d''; destruct d''' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
               split; [trivial|]; split; [trivial|]; simpl in *.
             destruct H15; subst. destruct d''t; try exact H15. destruct H15 as [sv' [comp'' inM]].
             exists sv', comp''. right. trivial. }
           { destruct (snd (mem_match w d'' d_code d_ip) w_eq) as [d''' [d''match d''eq]].
             simpl in *. exists d'''. split; [|exact d''eq].
             destruct d''; destruct d''' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
               split; [trivial|]; split; [trivial|]; simpl in *.
             destruct H15; subst. destruct d''t; try exact H15. destruct H15 as [sv' [comp'' inM]].
             exists sv', comp''. right. trivial. }
    + (* call from comp in C to comp' in C *)
      repeat
      (match goal with
         H : Some ?a = getm reg _ |- _ => deduce_equality (esym H); pose proof (esym H); clear H
       end).
      deduce_equality OLD.
      subst s2. unfold side_of in *. unfold_match' side_eq. simpl in *.
      assert (side_eq': true = (comp \in domm ic)).
      { assert (comp_incl: comp \in (domm ic) \/ comp \in (domm ip)) by
          (rewrite ST0 in col_mem1; pose proof (col_mem1 _ _ PC0) as in_disj; simpl in in_disj;
           setoid_rewrite <- Extra.In_in in in_disj; exact ((fst (or_comm _ _)) in_disj)).
        destruct comp_incl as [Hl | Hr]. rewrite Hl. trivial. rewrite Hr in Heqa5. inversion Heqa5. }
      deduce_equality PC.
      pose proof (end_s2 _ _ PC) as end_cond. simpl in end_cond.
      revert end_cond. decode_instr_eq. intro end_cond. destruct end_cond as [ | [? [eq1 code_RA]]]; auto; try tauto.
      rewrite RA in eq1. simplify_some. simpl in code_RA.
      deduce_equality RA.
      (* quick proof that v12 (s3) is a JAL offseted from i0 *)
      unfold_match' Heqa2. inversion Heqa2 as [tag_mem_pc'].
      inversion vt_match11; try subst i; revert H12; decode_instr_eq; intro H12.
      { destruct (H12 imm); auto. }
      { inversion H12. subst imm pc'. unfold alloc_empty in *. subst. simpl in alloc_mem_s2.
        assert (sw_eq: @swcast _ (word_size mt) (@word_of_nat (imm_size mt) alloc_label) = word_of_nat alloc_label).
        { admit. } simpl in sw_eq.
        rewrite <- sw_eq in alloc_mem_s2. rewrite <- Heqa6 in alloc_mem_s2. inversion alloc_mem_s2. }
      inversion H12. subst imm1. clear H12. subst pc'. rewrite H14 in Heqa6. simplify_some. simpl in *.
      destruct d as [vd td]. rename H15 into eq_next_pc.
      assert (exists off', offset2 comp' = Some off') as [off' eq_off'].
      { eapply (rwP dommP). rewrite offset2_domm. trivial. }
      rewrite <- tag_mem_pc' in H18.
      assert (eq_off'_alt: get_offset (side_of comp') comp' = Some off').
      { rewrite <- eq_off'. unfold side_of.
        destruct (comp' \in domm ip) eqn: comp'_ip.
        { exfalso. eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)).
          inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. exact ic_comp'. trivial. }
        rewrite comp'_ip. simpl. trivial. }
      pose proof (H18 off' (eq_off'_alt)) as imm'_eq.
      assert (imm'eq: @swcast _ (word_size mt) imm' = (swcast imm + as_word off')%w).
      { subst imm'. admit. } (* need more hypothesis *)
      rewrite imm'eq in eq_next_pc.
      remember (((pc1 + 1)%w@(Ret n), (pc0 + 1)%w@(Ret n1), (pc0 + 1 + as_word off)%w@(Ret n1), comp) :: M) as M'.
      eexists. exists M'.
      split.
      * eapply (plus_left _ [:: ECall _ _ _ _] ). eapply step_jal; eauto.
        -- rewrite eq_s3 in vt_eq11. exact vt_eq11.
        -- rewrite eq_s3 in vt_eq12. exact vt_eq12.
        -- simpl. exact H13.
        -- rewrite eq_s3 in vt_eq10. exact vt_eq10.
        -- unfold reg_clear_list, reg_list. simpl. unfold as_word. subst. simpl.
           repeat
             (match goal with
              | H: _ ?w = _  |- context[_ ?w] => rewrite H; simpl
              end). trivial.
        -- unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
           unfold evi in *. simpl. unfold_bind.
           deduce_reg reg_match. rewrite imm'eq. rewrite eq_next_pc. simpl.
           rewrite eq_s3 in tag_pc3. simpl in tag_pc3. rewrite tag_pc3. simpl. rewrite eq_refl. simpl.
           simpl in *. rewrite <- H17, <- tag_mem_pc'. rewrite <- Heqa35. simpl.
           unfold check_belong, belong. rewrite eq_refl. simpl.
           destruct a as [va ta]. unfold is_other in *. destruct ta; simpl in Heqa36; inversion Heqa36.
           inversion vt_match9 as [? _]; subst t9. simpl. rewrite <- Heqa7. simpl. subst s3. rewrite vt_eq12.
           unfold updm. unfold as_word. simpl in *.
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
           destruct x as [vx tx]. inversion H12. subst tx vx.
           reflexivity.
        -- eapply star_refl.
        -- unfold evi in Heqa, Heqa0. repeat unfold_bind. inv Heqa. inv Heqa0. simpl.
           simpl in *. rewrite H11 in Heqa8. simplify_some. reflexivity.
      * rewrite ST0 in tag_pc1. simpl in tag_pc1. inversion tag_pc1. rewrite eq_s3 in tag_pc3. simpl in tag_pc3. subst pc3_tag.
        repeat rewrite (@setmI _ _ _ (addw _ _)).
        2: { rewrite eq_s3 in vt_eq12. simpl in vt_eq12. trivial. }
        2: { rewrite RA in Heqa22. simplify_some. rewrite RA. trivial. }
        2: { subst. rewrite RA0 in Heqa47. simplify_some. rewrite RA0. trivial. }
        clear tag_pc1. subst. simpl in *. rename n1 into n.
        eapply match_states_right; econstructor; simpl; unfold build_tpc; try reflexivity.
        -- rewrite <- (addn1 n). eapply wf_stack_cons_right; simpl; eauto.
           ++ unfold points_to_comp_code'. simpl. rewrite RA0. simpl.
              split. destruct tret; unfold_match' a21_eq; convert_eq_op; trivial.
              left. split; trivial. unfold side_of. trivial. simpl. rewrite <- Heqa5. trivial.
           ++ unfold points_to_comp_code. simpl. rewrite RA. simpl. split; trivial.
           ++ unfold points_to_comp_code. subst pc3_val. rewrite <- addwA, (addwC onew), addwA.
              rewrite vt_eq12. simpl. split; trivial. 
        -- unfold register_domm. repeat rewrite domm_set. simpl.
           unfold register_domm, reg_field_size, mword, FSet.fsval in reg_domm1. simpl in reg_domm1.
           unfold mword, word_size. simpl.
           clear - reg_domm1. unfold_match' reg_domm1. admit. (* exstructure *)
        -- unfold register_domm. repeat rewrite domm_set. simpl.
           unfold register_domm, reg_field_size, mword, FSet.fsval in reg_domm2. simpl in reg_domm2.
           unfold mword, word_size. simpl.
           clear - reg_domm2. unfold_match' reg_domm2. admit. (* exstructure *)
        -- unfold register_domm. repeat rewrite domm_set. simpl.
           unfold register_domm, reg_field_size, mword, FSet.fsval in reg_domm3. simpl in reg_domm3.
           unfold mword, word_size. simpl.
           clear - reg_domm3. unfold_match' reg_domm3. admit. (* exstructure *)
        -- split; [|split; [|split; [|split; [|split; [|split]]]]]; trivial.
        -- split; [|split; [|split; [|split; [|split; [|split]]]]]; trivial.
        -- split; [|split; [|split; [|split; [|split; [|split]]]]]; trivial.
        -- intros d'' q rw rweq.
           destruct rw as [r | w]; simpl; simpl in rweq.
           ++ repeat rewrite setmE in rweq. repeat (unfold_match' rweq).
              ** convert_eq_op. simplify_some. subst d'' q.
                 split; [unfold in_stack; do 3 eexists; econstructor; eauto |].
                 intros rw d''. destruct rw as [r | w].
                 { intro rweq. repeat rewrite setmE in rweq. repeat unfold_match' rweq. convert_eq_op; trivial.
                   exfalso.
                   assert (r_in : In r (domm reg0)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm1 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
                 { intro tex. pose proof (capa_cor1 d'' n (inr w) tex) as [is_in unicity].
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
              ** exfalso.
                 assert (r_in : In r (domm reg0)).
                 { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                 exfalso. rewrite reg_domm1 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                 repeat (destruct r_in as [|r_in];
                         [subst;
                          (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                 inversion r_in.
           ++ pose proof (capa_cor1 d'' q (inr w) rweq) as [is_in unicity].
              split. { clear -is_in. unfold in_stack in *. destruct is_in as [sv1 [sv2 [col is_in]]]. do 3 eexists. right. eauto. }
              intros [r' | w'] d'''.
              ** intro rweq'. repeat rewrite setmE in rweq'. repeat unfold_match' rweq'.
                 { convert_eq_op. simplify_some. subst d''' q.
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
                 { assert (r_in : In r' (domm reg0)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm1 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
              ** eapply (unicity (inr w')).
        -- intros d'' q rw rweq.
           destruct rw as [r | w]; simpl; simpl in rweq.
           ++ repeat rewrite setmE in rweq. repeat (unfold_match' rweq).
              ** convert_eq_op. simplify_some. subst d'' q.
                 split; [unfold in_stack; do 3 eexists; econstructor; eauto |].
                 intros rw d''. destruct rw as [r | w].
                 { intro rweq. repeat rewrite setmE in rweq. repeat unfold_match' rweq. convert_eq_op; trivial.
                   exfalso.
                   assert (r_in : In r (domm reg)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm2 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
                 { intro tex. pose proof (capa_cor2 d'' n (inr w) tex) as [is_in unicity].
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
              ** exfalso.
                 assert (r_in : In r (domm reg)).
                 { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                 exfalso. rewrite reg_domm2 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                 repeat (destruct r_in as [|r_in];
                         [subst;
                          (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                 inversion r_in.
           ++ pose proof (capa_cor2 d'' q (inr w) rweq) as [is_in unicity].
              split. { clear -is_in. unfold in_stack in *. destruct is_in as [sv1 [sv2 [col is_in]]]. do 3 eexists. right. eauto. }
              intros [r' | w'] d'''.
              ** intro rweq'. repeat rewrite setmE in rweq'. repeat unfold_match' rweq'.
                 { convert_eq_op. simplify_some. subst d''' q.
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
                 { assert (r_in : In r' (domm reg)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm2 in r_in. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
              ** eapply (unicity (inr w')).
        -- intros d'' q rw rweq.
           destruct rw as [r | w]; simpl; simpl in rweq.
           ++ repeat rewrite setmE in rweq. repeat (unfold_match' rweq).
              ** convert_eq_op. simplify_some. inversion Heqa36.
              ** convert_eq_op. simplify_some. subst d'' q pc3_val.
                 split; [unfold in_stack; do 3 eexists; econstructor; rewrite <- addwA, (addwC onew), addwA; eauto|].
                 intros rw d''. destruct rw as [r | w].
                 { intro rweq. destruct a as [va ta]. destruct ta; inversion Heqa36.
                   repeat rewrite setmE in rweq. repeat unfold_match' rweq.
                   all: repeat simplify_some; convert_eq_op; trivial.
                   { assert (r_in : In r (domm regs3)).
                     { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                     exfalso. rewrite reg_domm3 in r_in. simpl in r_in. unfold word_of_nat, as_word in r_in. simpl in r_in.
                     repeat (destruct r_in as [|r_in];
                             [subst;
                              (match goal with H : false = (Word ?a == Word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                     inversion r_in. } }
                 { intro tex. pose proof (capa_cor3 d'' n (inr w) tex) as [is_in unicity].
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
              ** assert (r_in : In r (domm regs3)).
                 { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                 exfalso. rewrite reg_domm3 in r_in. simpl in r_in. unfold word_of_nat, as_word in r_in. simpl in r_in.
                 repeat (destruct r_in as [|r_in];
                         [subst;
                          (match goal with H : false = (Word ?a == Word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                 inversion r_in.
           ++ pose proof (capa_cor3 d'' q (inr w) rweq) as [is_in unicity].
              split. { clear -is_in. unfold in_stack in *. destruct is_in as [sv1 [sv2 [col is_in]]]. do 3 eexists. right. eauto. }
              intros [r' | w'] d'''.
              ** intro rweq'. repeat rewrite setmE in rweq'. repeat unfold_match' rweq'.
                 { convert_eq_op. simplify_some. inversion Heqa36. }
                 { convert_eq_op. simplify_some. subst d''' q.
                   unfold in_stack in is_in. clear -is_in wfst.
                   revert is_in wfst. revert M.
                   induction n; intros M [sv1 [sv2 [col is_in]]] wfst.
                   - inv wfst; inversion is_in; try (rewrite addn1 in H0; inversion H0).
                   - inversion wfst; try inversion is_in; try( rewrite addn1 in H0; inversion H0);
                       subst; eapply (IHn _ _ WF_ST). }
                 { assert (r_in : In r' (domm regs3)).
                   { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists; eauto. }
                   exfalso. rewrite reg_domm3 in r_in. simpl in r_in. unfold word_of_nat, as_word in r_in. simpl in r_in.
                   repeat (destruct r_in as [|r_in];
                           [subst;
                            (match goal with H : false = (Word ?a == Word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
                   inversion r_in. }
              ** eapply (unicity (inr w')).
        -- inversion weak. trivial.
        -- inversion weak as [? ? ? _ _ _ _ _ entry_off' _ _].
           inversion Heqa2.
           pose proof (entry_off _ _ _ _ _ i1 l l ic_comp' (H14) eq_next_pc) as same_entry.
           destruct same_entry as [off'' [off''eq pc'eq]]; simpl; try rewrite <- H17; try rewrite <- H21; trivial.
           ++ pose proof (entry_code2 _ _ (i1, l) (H14)) as ent_cond; eauto. simpl in ent_cond. rewrite <- H21 in ent_cond.
              eapply ent_cond; eauto.
           ++ pose proof (entry_code2 _ _ (i1, l) (H14)) as ent_cond; eauto. simpl in ent_cond. rewrite <- H21 in ent_cond.
              eapply ent_cond; eauto.
        -- inversion weak. trivial.
        -- unfold side_of. goal_match_bind_step; trivial. exfalso.
           eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)).
           inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. exact ic_comp'.
           rewrite <- Heqa6. trivial.
        -- inversion weak. trivial.
        -- inversion weak. trivial.
        -- inversion weak. trivial.
        -- unfold register_address_correctness. simpl.
           intros d'' r r_d_eq.
           unfold register_domm in *.
           repeat rewrite setmE in r_d_eq. repeat unfold_match' r_d_eq.
           { convert_eq_op. simplify_some.
             destruct (taga d''); inversion Heqa36. simpl. trivial. }
           { convert_eq_op. simplify_some. simpl.
             eexists; split; [eauto |]. intro. trivial. }
           assert (r_in : In r (domm regs3)).
           {  setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eauto. }
           exfalso. rewrite reg_domm3 in r_in. simpl in r_in. unfold word_of_nat, as_word in r_in. simpl in r_in.
           repeat (destruct r_in as [|r_in];
                   [subst;
                    (match goal with H : false = (Word ?a == Word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
           inversion r_in.
        -- unfold memory_match. simpl. inversion weak as [? ? ? _ _ _ _ _ _ _ mem_match'].
           intros w d'' d_code d_ip. split; intro w_eq.
           { destruct (fst (mem_match' w d'' d_code d_ip) w_eq) as [d''' [d''match d''eq]].
             simpl in *. exists d'''. split; [|exact d''eq].
             destruct d'''; destruct d'' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
               split; [trivial|]; split; [trivial|]; simpl in *.
             destruct H21; subst. destruct d''t; try exact H15. destruct H15 as [sv' [comp'' inM]].
             exists sv', comp''. right. trivial. }
           { destruct (snd (mem_match' w d'' d_code d_ip) w_eq) as [d''' [d''match d''eq]].
             simpl in *. exists d'''. split; [|exact d''eq].
             destruct d'''; destruct d'' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
               split; [trivial|]; split; [trivial|]; simpl in *.
             destruct H21; subst. destruct d''t; try exact H15. destruct H15 as [sv' [comp'' inM]].
             exists sv', comp''. right. trivial. }
        -- eapply same_pc_normal; simpl; eauto.
        -- unfold side_of. goal_match_bind_step; trivial. exfalso.
           eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)).
           inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. exact ic_comp'.
           rewrite <- Heqa6. trivial.
        -- inversion weak. trivial.
        -- inversion weak. trivial.
        -- inversion weak. trivial.
        -- unfold register_address_correctness. simpl.
           intros d'' r r_d_eq.
           unfold register_domm in *.
           assert (r_in : In r (domm reg)).
           { clear - reg_domm2 r_d_eq. rewrite reg_domm2.
             repeat (rewrite setmE in r_d_eq; unfold_match' r_d_eq; [ convert_eq_op |]; simpl in r_d_eq).
             all: try (simpl; tauto).
             rewrite <- reg_domm2. setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists. eauto. }
           rewrite reg_domm2 in r_in.
           repeat rewrite setmE in r_d_eq. repeat unfold_match' r_d_eq.
           { convert_eq_op. simplify_some. simpl. eexists. split. exact RA. trivial. }
           exfalso. simpl in r_in. unfold word_of_nat in r_in. simpl in r_in.
           repeat (destruct r_in as [|r_in];
                   [subst;
                    (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
           inversion r_in.
        -- unfold register_address_correctness. simpl.
           intros d'' r r_d_eq.
           unfold register_domm in *.
           assert (r_in : In r (domm regs3)).
           { clear - reg_domm3 r_d_eq. rewrite reg_domm3.
             repeat (rewrite setmE in r_d_eq; unfold_match' r_d_eq; [ convert_eq_op |]; simpl in r_d_eq).
             all: try (simpl; tauto).
             rewrite <- reg_domm3. setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eexists. eauto. }
           rewrite reg_domm3 in r_in.
           repeat rewrite setmE in r_d_eq. repeat unfold_match' r_d_eq.
           { convert_eq_op. simplify_some. destruct d'' as [? d''t]. destruct d''t; inversion Heqa36.
             simpl. trivial. }
           { convert_eq_op. simplify_some. simpl. eexists. split. exact vt_eq12. trivial. }
           exfalso. simpl in r_in. unfold word_of_nat, as_word in r_in. simpl in r_in.
           repeat (destruct r_in as [|r_in];
                   [subst;
                    (match goal with H : false = (Word ?a == Word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]).
           inversion r_in.
        -- unfold memory_match. simpl. subst.
           intros w d'' d_code d_ip. split; intro w_eq.
           { destruct (fst (mem_match w d'' d_code d_ip) w_eq) as [d''' [d''match d''eq]].
             simpl in *. exists d'''. split; [|exact d''eq].
             destruct d''; destruct d''' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
               split; [trivial|]; split; [trivial|]; simpl in *.
             destruct H15; subst. destruct d''t; try exact H15. destruct H15 as [sv' [comp'' inM]].
             exists sv', comp''. right. trivial. }
           { destruct (snd (mem_match w d'' d_code d_ip) w_eq) as [d''' [d''match d''eq]].
             simpl in *. exists d'''. split; [|exact d''eq].
             destruct d''; destruct d''' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
               split; [trivial|]; split; [trivial|]; simpl in *.
             destruct H15; subst. destruct d''t; try exact H15. destruct H15 as [sv' [comp'' inM]].
             exists sv', comp''. right. trivial. }
        -- unfold registers_match. simpl. intros w d''.
           split; intro w_eq.
           { repeat (rewrite setmE in w_eq; unfold_match' w_eq; [ convert_eq_op |]; simpl in w_eq).
             all: try simplify_some.
             all: repeat (rewrite setmE; simpl).
             1-12: eexists; split; [| reflexivity].
             1-12: try (split; trivial).
             { destruct d'' as [v_d t_d]. unfold is_other in *. destruct t_d; inversion Heqa36.
               split; trivial. unfold as_word in H11. simpl in H11. rewrite H11 in Heqa24. simplify_some. trivial. }
             { subst pc3_val. eexists. eexists. left. rewrite <- addwA, (addwC onew), addwA. reflexivity. }
             simpl. unfold as_word. unfold ssrint.absz. simpl.
             repeat (match goal with | H: false = ?c |- context[?c] => rewrite <- H end).
             exfalso.
             assert (r_in : In w (domm regs3)).
             { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eauto. }
             rewrite reg_domm3 in r_in.
             repeat (destruct r_in as [| r_in] ; [subst w ; simpl in *|] ).
             all: repeat
               (match goal with
                  H : false = eq_op _ _ |- _ => (rewrite eq_refl in H; inv H; done) || clear H
                end).
             inversion r_in. }

           { repeat (rewrite setmE in w_eq; unfold_match' w_eq; [ convert_eq_op |]; simpl in w_eq).
             all: try simplify_some.
             all: repeat (rewrite setmE; simpl).
             1-12: eexists; split; [| reflexivity].
             1-12: try (split; trivial).
             { destruct a as [v_d t_d]. unfold is_other in *. destruct t_d; inversion Heqa36.
               split; trivial. unfold as_word in H11. simpl in H11. rewrite H11 in Heqa24. simplify_some. trivial. }
             { subst pc3_val. eexists. eexists. left. rewrite <- addwA, (addwC onew), addwA. reflexivity. }
             simpl. unfold as_word. unfold ssrint.absz. simpl.
             repeat (match goal with | H: false = ?c |- context[?c] => rewrite <- H end).
             exfalso.
             assert (r_in : In w (domm reg)).
             { setoid_rewrite <- Extra.In_in. setoid_rewrite <- (rwP dommP). eauto. }
             rewrite reg_domm2 in r_in.
             repeat (destruct r_in as [| r_in] ; [subst w ; simpl in *|] ).
             all: repeat
               (match goal with
                  H : false = eq_op _ _ |- _ => (rewrite eq_refl in H; inv H; done) || clear H
                end).
             inversion r_in. }
  Admitted.
  
End StepEventCall.
