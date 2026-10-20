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
From mathcomp Require Import zify.
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
Require MicroPolicies.Recomposition.TraceWF MicroPolicies.Recomposition.TraceBracket.
Import TraceWF(table_sem_alloc).
Import TraceBracket(reg_index_neq).
Require Import MicroPolicies.Recomposition.PreservationLemmas.
Require Import MicroPolicies.Recomposition.StepEventCall.



Module StepEventReturn (S: RecompositionContext).

  Include StepEventCall S.

  Local Opaque pc_code_color.

  Lemma pc_code_color_pts' : forall (s : state) i jj C n,
      points_to_comp_code' i jj (mem s) (vala (pc s)) C ->
      taga (pc s) = build_tpc n C -> pc_code_color s.
  Proof.
    move=> s i jj C n Hpts Htag d Hd _.
    have Hcol : color_of s = C by rewrite (color_of_pc_tag s) Htag /build_tpc.
    rewrite Hcol. move: Hpts; rewrite /points_to_comp_code' Hd /= => -[Hc _]; exact Hc.
  Qed.

  Lemma pc_code_color_pts : forall (s : state) C n,
      points_to_comp_code (mem s) (vala (pc s)) C ->
      taga (pc s) = build_tpc n C -> pc_code_color s.
  Proof.
    move=> s C n Hpts Htag d Hd _.
    have Hcol : color_of s = C by rewrite (color_of_pc_tag s) Htag /build_tpc.
    rewrite Hcol. move: Hpts; rewrite /points_to_comp_code Hd /= => -[Hc _]; exact Hc.
  Qed.

  Lemma wf_stack_levels_lt' :
    forall (m1 m2 m3 : memory) (cn : nat) (M : stack),
      wf_stack m1 m2 m3 cn M ->
      forall a b c col, In (a, b, c, col) M ->
        exists k, taga a = Ret k /\ taga b = Ret k /\ taga c = Ret k /\ (k < cn)%N.
  Proof.
    move=> m1 m2 m3 cn M H.
    induction H as [
      | n st v1 v2 v3 C off SIDE OFF P1 P2 P3 VO WF IH
      | n st v1 v2 v3 C off SIDE OFF P1 P2 P3 VO WF IH ].
    - by move=> a b c col [].
    - move=> a b c col [Heq | Hin].
      + move: Heq => [= H1 H2 H3 H4]; subst.
        exists n; split; [by [] | split; [by [] | split; [by [] |]]].
        by rewrite addn1 ltnSn.
      + have [k [Ha [Hb [Hc Hk]]]] := IH a b c col Hin.
        exists k; split; [exact: Ha | split; [exact: Hb | split; [exact: Hc |]]].
        by rewrite addn1; apply: (ltn_trans Hk); exact: ltnSn.
    - move=> a b c col [Heq | Hin].
      + move: Heq => [= H1 H2 H3 H4]; subst.
        exists n; split; [by [] | split; [by [] | split; [by [] |]]].
        by rewrite addn1 ltnSn.
      + have [k [Ha [Hb [Hc Hk]]]] := IH a b c col Hin.
        exists k; split; [exact: Ha | split; [exact: Hb | split; [exact: Hc |]]].
        by rewrite addn1; apply: (ltn_trans Hk); exact: ltnSn.
  Qed.

  Lemma dmc : forall (i : side) (c : Component.id) (m : metadata) (da db : atom (mword mt) value_tag),
      Types.taga da = Types.taga db ->
      (Types.taga da = Other -> Types.vala da = Types.vala db) ->
      (Types.taga da = Invalidated \/ Types.taga da = Other) ->
      data_match i c m da db.
  Proof.
    move=> i c m [va ta] [vb tb] /= Et Ev Ht.
    rewrite /data_match /=. subst tb. split=> //.
    case: Ht => Ht; rewrite Ht /=; [done | exact: (Ev Ht)].
  Qed.

  Lemma registers_match_clear :
    forall (i : side) (m : metadata) (s s' : state) (v : mword mt),
      domm (regs s) = domm (regs s') ->
      (forall w d, regs s  w = Some d ->
         (w = as_word (ssrint.Posz 1) /\ Types.taga d = Other) \/
         (w <> as_word (ssrint.Posz 1) /\ Types.taga d = Invalidated)) ->
      (forall w d, regs s' w = Some d ->
         (w = as_word (ssrint.Posz 1) /\ Types.taga d = Other) \/
         (w <> as_word (ssrint.Posz 1) /\ Types.taga d = Invalidated)) ->
      omap Types.vala (regs s  (as_word (ssrint.Posz 1))) = Some v ->
      omap Types.vala (regs s' (as_word (ssrint.Posz 1))) = Some v ->
      registers_match i m s s'.
  Proof.
    move=> i m s s' v Hdomm Hs Hs' V1 V3 w d; split=> Hw.
    - have wd : w \in domm (regs s) by rewrite Hdomm; apply/dommP; exists d.
      move/dommP: wd => [d' Hd']. exists d'; split=> //.
      apply: dmc.
      + case: (Hs _ _ Hd') => [[E1 ->] | [E1 ->]];
        case: (Hs' _ _ Hw) => [[E2 ->] | [E2 ->]] //;
        first [ by case: (E2 E1) | by case: (E1 E2) ].
      + move=> To1.
        have Ew : w = as_word (ssrint.Posz 1).
        { case: (Hs _ _ Hd') => [[E1 _] | [_ Ti1]] //. by rewrite Ti1 in To1. }
        subst w. move: V1 V3. by rewrite Hd' Hw /= => [= ->] [= ->].
      + case: (Hs _ _ Hd') => [[_ H] | [_ H]]; [by right | by left].
    - have wd : w \in domm (regs s') by rewrite -Hdomm; apply/dommP; exists d.
      move/dommP: wd => [d' Hd']. exists d'; split=> //.
      apply: dmc.
      + case: (Hs _ _ Hw) => [[E1 ->] | [E1 ->]];
        case: (Hs' _ _ Hd') => [[E2 ->] | [E2 ->]] //;
        first [ by case: (E2 E1) | by case: (E1 E2) ].
      + move=> To1.
        have Ew : w = as_word (ssrint.Posz 1).
        { case: (Hs _ _ Hw) => [[E1 _] | [_ Ti1]] //. by rewrite Ti1 in To1. }
        subst w. move: V1 V3. by rewrite Hw Hd' /= => [= ->] [= ->].
      + case: (Hs _ _ Hw) => [[_ H] | [_ H]]; [by right | by left].
  Qed.

  Local Ltac killcond_r :=
    repeat (match goal with |- context[as_word (ssrint.Posz ?a) == as_word (ssrint.Posz ?b)] =>
      rewrite (introF eqP (@reg_index_neq a b ltac:(move=> ?; discriminate)
                            ltac:(by []) ltac:(by []))) end).
  Local Ltac rrstep_r Hr := rewrite ?setmE; killcond_r; rewrite Hr /=.

  Lemma reg_clear_read_props :
    forall (st : state) (top : tag_type lrc_tags R),
      (forall n, n \in reg_list -> regs st (as_word (ssrint.Posz n)) <> None) ->
      exists rs,
        next_state_do_updates st
          (HSeqCons top reg_invalidate_hseq : hseq (tag_type lrc_tags) (R :: nseq 10 R))
          reg_clear_read
        = Some {| mem := mem st; regs := rs; pc := pc st; internal := internal st |}
        /\ rs (as_word (ssrint.Posz 1)) =
             omap (fun a => (Types.vala a) @ top) (regs st (as_word (ssrint.Posz 1)))
        /\ (forall n, n \in [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19] ->
              exists v, rs (as_word (ssrint.Posz n)) = Some (v @ Invalidated))
        /\ rs (as_word (ssrint.Posz 4)) = regs st (as_word (ssrint.Posz 4))
        /\ (forall w, w \notin [seq as_word (ssrint.Posz n) | n <- reg_list] -> rs w = regs st w).
  Proof.
    move=> st top Hex.
    Local Transparent next_state_do_update.
    have RD : forall n, n \in reg_list -> exists a, regs st (as_word (ssrint.Posz n)) = Some a.
    { move=> n Hn; case E: (regs st (as_word (ssrint.Posz n))) => [a|];
        [by exists a | by exfalso; apply: (Hex n Hn)]. }
    have [a1 Ha1]   := RD 1  isT. have [a0 Ha0]   := RD 0  isT. have [a2 Ha2]   := RD 2  isT.
    have [a3 Ha3]   := RD 3  isT. have [a5 Ha5]   := RD 5  isT. have [a6 Ha6]   := RD 6  isT.
    have [a7 Ha7]   := RD 7  isT. have [a16 Ha16] := RD 16 isT. have [a17 Ha17] := RD 17 isT.
    have [a18 Ha18] := RD 18 isT. have [a19 Ha19] := RD 19 isT.
    eexists. split.
    { cbn [next_state_do_updates ohead behead hshead hsbehead nseq make_hseq map
           reg_clear_read reg_list reg_invalidate_hseq].
      rewrite !obindE.
      rewrite {1}/next_state_do_update /= Ha1 /= /updm Ha1 /=.
      rrstep_r Ha0. rrstep_r Ha2. rrstep_r Ha3. rrstep_r Ha5.
      rrstep_r Ha6. rrstep_r Ha7. rrstep_r Ha16. rrstep_r Ha17. rrstep_r Ha18.
      rrstep_r Ha19. reflexivity. }
    split; [ | split; [ | split ] ].
    - by rewrite !setmE; killcond_r; rewrite eqxx /= Ha1 /=.
    - move=> n; rewrite !inE =>
        /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|
        /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]]]]]]];
        eexists; rewrite !setmE; killcond_r; rewrite eqxx /=; reflexivity.
    - by rewrite !setmE; killcond_r.
    - move=> w Hw.
      have F : forall n, n \in reg_list -> w != as_word (ssrint.Posz n).
      { move=> n Hn. apply: contraNneq Hw => ->. apply/mapP. by exists n. }
      rewrite !setmE (negbTE (F 1 isT)) (negbTE (F 0 isT)) (negbTE (F 2 isT))
        (negbTE (F 3 isT)) (negbTE (F 5 isT)) (negbTE (F 6 isT)) (negbTE (F 7 isT))
        (negbTE (F 16 isT)) (negbTE (F 17 isT)) (negbTE (F 18 isT)) (negbTE (F 19 isT)) /=.
      reflexivity.
  Qed.

  Lemma return_do_updates_props :
    forall (st : state) (r0 : reg mt) cell4 cellr0,
      r0 <> as_word (ssrint.Posz 1) ->
      register_domm (regs st) ->
      regs st (as_word (ssrint.Posz 4)) = Some cell4 ->
      regs st r0 = Some cellr0 ->
      exists rs,
        next_state_do_updates st
          ((Invalidated :: Invalidated :: Other :: reg_invalidate_hseq)%hseq
           : hseq (tag_type lrc_tags) (R :: R :: R :: nseq 10 R))
          (RegRead (as_word (ssrint.Posz 4)) :: RegRead r0 :: reg_clear_read)
        = Some {| mem := mem st; regs := rs; pc := pc st; internal := internal st |}
        /\ omap Types.vala (rs (as_word (ssrint.Posz 1)))
             = omap Types.vala (regs st (as_word (ssrint.Posz 1)))
        /\ (forall w d, rs w = Some d ->
              (w = as_word (ssrint.Posz 1) /\ Types.taga d = Other) \/
              (w <> as_word (ssrint.Posz 1) /\ Types.taga d = Invalidated)).
  Proof.
    move=> st r0 cell4 cellr0 Hr0 Hdomm Hcell4 Hcellr0.
    have keyin : forall n, n \in reg_list -> as_word (ssrint.Posz n) \in domm (regs st).
    { move=> n Hn. rewrite Hdomm in_fset inE; apply/orP; right; apply/mapP; by exists n. }
    have Hexst : forall n, n \in reg_list -> regs st (as_word (ssrint.Posz n)) <> None.
    { move=> n Hn; move: (keyin n Hn); rewrite mem_domm; by case: (regs st _). }
    Local Transparent next_state_do_update.
    have [st3 [Hpre1 [Hpre2 [Hm3 [Hp3 [Hi3 [H43 [H13 [Hex3 Hpres3]]]]]]]]] :
      exists st3,
        next_state_do_update st (Invalidated : tag_type lrc_tags R)
          (RegRead (as_word (ssrint.Posz 4)))
          = Some {| mem := mem st;
                    regs := setm (regs st) (as_word (ssrint.Posz 4)) (Types.vala cell4)@Invalidated;
                    pc := pc st; internal := internal st |}
        /\ next_state_do_update
             {| mem := mem st;
                regs := setm (regs st) (as_word (ssrint.Posz 4)) (Types.vala cell4)@Invalidated;
                pc := pc st; internal := internal st |}
             (Invalidated : tag_type lrc_tags R) (RegRead r0) = Some st3
        /\ mem st3 = mem st /\ pc st3 = pc st /\ internal st3 = internal st
        /\ omap Types.taga (regs st3 (as_word (ssrint.Posz 4))) = Some Invalidated
        /\ regs st3 (as_word (ssrint.Posz 1)) = regs st (as_word (ssrint.Posz 1))
        /\ (forall n, n \in reg_list -> regs st3 (as_word (ssrint.Posz n)) <> None)
        /\ (forall w, w <> as_word (ssrint.Posz 4) -> w <> r0 -> regs st3 w = regs st w).
    { rewrite /next_state_do_update /= Hcell4 /= /updm Hcell4 /=.
      have N14 : (as_word (ssrint.Posz 1) : reg mt) != as_word (ssrint.Posz 4)
        by apply/eqP; apply: (@reg_index_neq 1 4); by [].
      have N1r0 : (as_word (ssrint.Posz 1) : reg mt) != r0
        by apply/eqP => E; apply: Hr0; rewrite E.
      have [rv Hrv] : exists rv,
        setm (regs st) (as_word (ssrint.Posz 4)) (Types.vala cell4)@Invalidated r0 = Some rv.
      { rewrite setmE; case: ifP => [_|_]; [ by eexists | by rewrite Hcellr0; eexists ]. }
      rewrite !Hrv /=.
      eexists; do 2 (split; first reflexivity). do 3 (split; first reflexivity).
      split.
      { rewrite setmE; case: ifP => [_|_]; first by []. by rewrite setmE eqxx. }
      split.
      { by rewrite setmE (negbTE N1r0) setmE (negbTE N14). }
      split.
      { move=> n Hn. rewrite setmE; case: ifP => [_|_]; first by [].
        rewrite setmE; case: ifP => [_|_]; first by []. exact: (Hexst n Hn). }
      move=> w Hw4 Hwr0. rewrite setmE; case: ifP => [/eqP Ew | _]; first by case: (Hwr0 Ew).
      rewrite setmE; case: ifP => [/eqP Ew | _]; first by case: (Hw4 Ew). reflexivity. }
    have Hex3' : forall n, n \in reg_list -> regs st3 (as_word (ssrint.Posz n)) <> None
      by exact: Hex3.
    have [rs [Hrs [Hrs1 [Hrsinv [Hrs4 Hpres]]]]] := reg_clear_read_props Other Hex3'.
    exists rs.
    rewrite ndsu_cons Hpre1 obindE ndsu_cons Hpre2 obindE Hrs Hm3 Hp3 Hi3.
    split; first reflexivity.
    split.
    { rewrite Hrs1 H13. by case: (regs st (as_word (ssrint.Posz 1))). }
    move=> w d Hw.
    case: (eqVneq w (as_word (ssrint.Posz 1))) => [Ew | Ew].
    - subst w. left; split=> //. move: Hw; rewrite Hrs1 H13.
      by case: (regs st (as_word (ssrint.Posz 1))) => [a|] //= [<-].
    - right; split; first exact/eqP.
      case Ew4: (w == as_word (ssrint.Posz 4)).
      + move/eqP: Ew4 => Ew4; subst w.
        move: H43; rewrite -Hrs4 Hw /=. by move=> [= ->].
      + case Ewl: (w \in [seq as_word (ssrint.Posz n) | n <- [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]]).
        * move/mapP: Ewl => [n Hn Ewn]; subst w.
          have [v Hv] := Hrsinv n Hn. move: Hw; rewrite Hv. by move=> [= <-].
        *
          exfalso.
          have Hw4 : w <> as_word (ssrint.Posz 4) by move/eqP: (negbT Ew4).
          have Hwd : w \notin domm (regs st).
          { rewrite Hdomm in_fset inE negb_or; apply/andP; split.
            - exact: (negbT Ew4).
            - apply/mapP => -[n Hn Ewn]. move: Hn; rewrite inE => /orP[/eqP E1 | Hn'].
              + by move: Ew; rewrite Ewn /word_of_nat E1 eqxx.
              + by move: Ewl => /negP; apply; rewrite Ewn /word_of_nat; apply/mapP; exists n. }
          have Hwr0 : w <> r0 by move=> E; move: Hwd; rewrite E mem_domm Hcellr0.
          move: Hw; rewrite Hpres; first last.
          { move: Hwd; rewrite Hdomm in_fset inE negb_or => /andP[_].
            by rewrite /word_of_nat. }
          rewrite Hpres3 //. by move=> Hwst; move/dommPn: Hwd; rewrite Hwst.
  Qed.



  Lemma combined_codes_mem_cong :
    forall (i : side) (s s' t t' : state),
      mem s = mem s' -> mem t = mem t' ->
      combined_codes i s t -> combined_codes i s' t'.
  Proof.
    move=> i s s' t t' Hs Ht H. rewrite /combined_codes -Hs -Ht. exact: H.
  Qed.

  Lemma nsuap_domm_gen (tf : _) (st : state) (kiv : k_ivec lrc_tags) (updts : seq update)
        (pc' : mword mt) (s' : state) (ev : option event) :
    @next_state_updates_and_pc mt ops lrc_tags tf unit st kiv updts pc' = Some (s', ev) ->
    domm (regs s') = domm (regs st).
  Proof.
    rewrite /next_state_updates_and_pc /next_state.
    case: (evi st) => [evinp|] //=.
    case: (tf _ evinp) => [ov_ev|] //=.
    case: (op _) ov_ev => [op0|] ov_ev //=.
    case: ov_ev => ov0 ev0.
    case Edsu: (next_state_do_updates st (tr ov0) updts) => [st0|] //=.
    by move=> [= Hs Hev]; subst s'; cbn; exact: (next_state_do_updates_regs_domm Edsu).
  Qed.

  Lemma alloc_fun_regs_domm (N : nat) (st st' : state) :
    LRC.alloc_fun (NC := N) st = Some st' -> domm (regs st') = domm (regs st).
  Proof.
    rewrite /LRC.alloc_fun; cbv zeta => H.
    apply obind_inv in H as [ra_val [_ H]].
    apply obind_inv in H as [[] [_ H]].
    apply obind_inv in H as [ret_addr [_ H]].
    apply obind_inv in H as [[] [_ H]].
    apply obind_inv in H as [sz [_ H]].
    apply obind_inv in H as [[] [_ H]].
    apply obind_inv in H as [len [_ H]].
    apply obind_inv in H as [[] [_ H]].
    move: H; case: ifP => _ //= H.
    apply obind_inv in H as [addr [_ H]].
    apply obind_inv in H as [regs' [Hupd H]].
    move: H => [= <-] /=.
    exact: (updm_domm_eq Hupd).
  Qed.

  Lemma stepf_regs_domm (tf : _) (N : nat) (st st' : state) (ev : option event) :
    @Exec.stepf mt ops lrc_tags tf unit (table (NC:=N)) st = Some (st', ev) ->
    domm (regs st') = domm (regs st).
  Proof.
    destruct st as [smem sreg [spc stpc] sextra]; rewrite /Exec.stepf.
    case Ef: (smem spc) => [[i ti]|]; last first.
    -
      move=> H; apply obind_inv in H as [sc [Et H]].
      have Hsem := table_sem_alloc Et.
      have Hsemst := PCCM.run_syscall_sem_gen H.
      rewrite Hsem in Hsemst.
      exact: (alloc_fun_regs_domm Hsemst).
    - case: (decode_instr i) => [instr|]; last by [].
      move=> H; apply obind_inv in H as [x [_ H]]; clear instr; destruct x;
        cbn beta iota in H;
        repeat first
          [ match goal with Hh : obind _ _ = Some _ |- _ =>
              apply obind_inv in Hh as [? [_ Hh]] end
          | match goal with a : atom _ _ |- _ => destruct a end ];
        match goal with
        | Hh : next_state_updates _ _ _ = Some _ |- _ => exact: (nsuap_domm_gen Hh)
        | Hh : next_state_updates_and_pc _ _ _ _ = Some _ |- _ => exact: (nsuap_domm_gen Hh)
        | Hh : None = Some _ |- _ => by []
        end.
  Qed.

  Lemma reg_domm_step :
    forall (NC : nat) (st st' : state) (evt : option event),
      @step_me NC st st' evt -> register_domm (regs st) -> register_domm (regs st').
  Proof.
    move=> NC st st' evt H Hd.
    move: H; rewrite /step_me => /Exec.stepP H.
    by rewrite /register_domm (stepf_regs_domm H); move: Hd; rewrite /register_domm.
  Qed.

  Lemma reg_domm_step_mp :
    forall (NC : nat) (st st' : state) (evt : option event),
      @step_mp NC st st' evt -> register_domm (regs st) -> register_domm (regs st').
  Proof.
    move=> NC st st' evt H Hd.
    move: H; rewrite /step_mp => /Exec.stepP H.
    by rewrite /register_domm (stepf_regs_domm H); move: Hd; rewrite /register_domm.
  Qed.

  Lemma return_step_inv : forall (s s' : Symbolic.state lrc_tags unit) comp z comp',
    step_me (NC := NC) s s' (Some (ERet comp z comp')) ->
    exists ip r w n rac a1 cell st',
      Symbolic.mem s (vala (Symbolic.pc s)) = Some ip /\
      decode_instr (vala ip) = Some (Jump r) /\
      Symbolic.regs s r = Some (w @ (Ret n)) /\
      Symbolic.regs s (as_word (ssrint.Posz 4)) = Some rac /\
      Symbolic.regs s (as_word (ssrint.Posz 1)) = Some a1 /\
      Symbolic.mem s w = Some cell /\
      is_code (taga ip) = true /\
      color (taga ip) = comp /\
      taga (Symbolic.pc s) = Level n.+1 comp /\
      color (taga cell) = comp' /\
      belong comp (Some (taga cell)) = false /\
      taga a1 = Other /\
      z = convert (int_of_word (vala a1)) /\
      next_state_do_updates s
        ((Invalidated :: Invalidated :: Other :: reg_invalidate_hseq)%hseq
         : hseq (tag_type lrc_tags) (R :: R :: R :: nseq 10 R))
        (RegRead (as_word (ssrint.Posz 4)) :: RegRead r :: reg_clear_read) = Some st' /\
      s' = {| mem := mem st'; regs := regs st'; pc := w @ (Level n comp'); internal := internal st' |}.
  Proof.
    intros s s' comp z comp' H.
    apply Exec.stepP in H.
    match goal with |- ?Goal => set (G := Goal) end.
    destruct s as [smem sreg [spc stpc] sextra].
    destruct stpc as [slvl scol].
    cbn -[next_state_updates_and_pc next_state_updates as_word word_of_nat obind oapp
          andw setm unionm mkfmap getm decode_instr] in H.
    destruct (smem spc) as [[i ti]|] eqn:Hf; rewrite Hf in H;
      cbn -[next_state_updates_and_pc next_state_updates as_word word_of_nat obind oapp
            andw setm unionm mkfmap getm decode_instr] in H;
      try discriminate H.
    apply obind_inv in H as [instr [DEC H]].
    destruct instr.
    all: unfold next_state_updates, next_state_updates_and_pc, next_state in H.
    all: cbv zeta in H; mcbn H.
    all: try unfold run_syscall in H.
    all: repeat (lazymatch type of H with
           | obind _ (transfer _ _) = _ => fail
           | _ => first
               [ apply obind_inv in H as [? [? H]]
               | match goal with w : (_ * _)%type |- _ => destruct w end
               | match goal with a : atom _ _ |- _ =>
                   match type of H with context[a] => destruct a end end
               ]; mcbn H
           end).
    all: try (exfalso; congruence).
    all: try (match type of H with context[if ?c then _ else _] =>
                let e := fresh in destruct c eqn:e end; mcbn H).
    all: try (match goal with _ : decode_instr _ = Some _ |- _ =>
                move: H; case Ejt: (smem _) => [[niv nit]|]; move=> H; mcbn H end).
    all: unfold transfer, instr_rules, LRC.instr_rules, check_belong, check_entry in H.
    all: cbv zeta in H; mcbn H.
    all: repeat (first
           [ match goal with HH : (do! _ <- _; _) = Some _ |- _ =>
               apply obind_inv in HH as [? [? HH]]; mcbn HH end
           | match goal with HH : context[let '{| trpc := _; tr := _ |} := _ in _] |- _ =>
               progress mcbn HH end
           | match goal with HH : Some _ = Some (?a, ?b) |- _ =>
               is_var a; is_var b; injection HH as ? ?; subst end
           | match goal with HH : Some _ = Some ?w |- _ => is_var w; injection HH as ?; subst end
           | match goal with w : (_ * _)%type |- _ => destruct w end
           | match goal with HH : context[match ?c with true => _ | false => _ end] |- _ =>
               let e := fresh "Eif" in revert HH; destruct c eqn:e; intro HH; mcbn HH end
           | match goal with HH : context[let (_, _) := ?x in _] |- _ => destruct x; mcbn HH end ]).
    all: mcbn H.
    all: try (exfalso; congruence).
    all: try (injection H as ? Hev; apply obind_inv in Hev as [? [_ Hev]]; discriminate Hev).
    all: try (match goal with E : belong _ None = false |- _ => discriminate E end).
    all: repeat match goal with u : unit |- _ => destruct u end.
    match goal with Hr : check_ret _ _ = Some _ |- _ => move: Hr end.
    match goal with Hw : _ r = Some _ |- _ => move: Hw end.
    case: taga => // n' Hw; rewrite /check_ret; case: eqP => // Hlvl _.
    subst slvl.
    injection H as Hs' Hc Hz Hc'. subst comp comp' z s'.
    subst G.
    exists (i$ {| vtag := vtag; color := color; entry := entry; is_code := is_code |}).
    exists r. eexists. exists n'.
    do 4 eexists.
    split; [cbn [Symbolic.mem Symbolic.pc Types.vala]; exact Hf|].
    split; [exact DEC|].
    split; [cbn [Symbolic.regs]; exact Hw|].
    split; [cbn [Symbolic.regs]; match goal with H' : _ (as_word (ssrint.Posz 4)) = Some _ |- _ => exact H' end|].
    split; [cbn [Symbolic.regs]; match goal with H' : _ (as_word (ssrint.Posz 1)) = Some _ |- _ => exact H' end|].
    split; [cbn [Symbolic.mem]; exact Ejt|].
    split; [exact Eif1|].
    split; [reflexivity|].
    split; [cbn [Types.taga Symbolic.pc]; move/eqnP: Eif0 => ->; reflexivity|].
    split; [move: H7; case: nit {Ejt Eif} => ? ? ? ? /= [<-]; reflexivity|].
    split; [cbn [Types.taga]; exact Eif|].
    split; [match goal with Hio : is_other ?t = Some _ |- _ => move: Hio; case: t => // end|].
    split; [match goal with He : evi _ = Some _, Hr : _ (as_word (ssrint.Posz 1)) = Some _ |- _ =>
              move: He; rewrite /evi => He; mcbn He; rewrite Hr in He; mcbn He;
              case: He => <-; reflexivity end|].
    split; [match goal with H' : next_state_do_updates _ _ _ = Some _ |- _ => exact H' end|].
    reflexivity.
  Qed.

  Lemma return_step_inv_mp : forall (s s' : Symbolic.state lrc_tags unit) comp z comp',
    step_mp (NC := NC) s s' (Some (ERet comp z comp')) ->
    exists ip r w n rac a1 cell st',
      Symbolic.mem s (vala (Symbolic.pc s)) = Some ip /\
      decode_instr (vala ip) = Some (Jump r) /\
      Symbolic.regs s r = Some (w @ (Ret n)) /\
      Symbolic.regs s (as_word (ssrint.Posz 4)) = Some rac /\
      Symbolic.regs s (as_word (ssrint.Posz 1)) = Some a1 /\
      Symbolic.mem s w = Some cell /\
      color (taga ip) = comp /\
      taga (Symbolic.pc s) = Level n.+1 comp /\
      color (taga cell) = comp' /\
      belong comp (Some (taga cell)) = false /\
      is_data (taga a1) = Some tt /\
      z = convert (int_of_word (vala a1)) /\
      next_state_do_updates s
        ((Invalidated :: Invalidated :: Other :: reg_invalidate_hseq)%hseq
         : hseq (tag_type lrc_tags) (R :: R :: R :: nseq 10 R))
        (RegRead (as_word (ssrint.Posz 4)) :: RegRead r :: reg_clear_read) = Some st' /\
      s' = {| mem := mem st'; regs := regs st'; pc := w @ (Level n comp'); internal := internal st' |}.
  Proof.
    intros s s' comp z comp' H.
    apply Exec.stepP in H.
    match goal with |- ?Goal => set (G := Goal) end.
    destruct s as [smem sreg [spc stpc] sextra].
    destruct stpc as [slvl scol].
    cbn -[next_state_updates_and_pc next_state_updates as_word word_of_nat obind oapp
          andw setm unionm mkfmap getm decode_instr] in H.
    destruct (smem spc) as [[i ti]|] eqn:Hf; rewrite Hf in H;
      cbn -[next_state_updates_and_pc next_state_updates as_word word_of_nat obind oapp
            andw setm unionm mkfmap getm decode_instr] in H;
      try discriminate H.
    apply obind_inv in H as [instr [DEC H]].
    destruct instr.
    all: unfold next_state_updates, next_state_updates_and_pc, next_state in H.
    all: cbv zeta in H; mcbn H.
    all: try unfold run_syscall in H.
    all: repeat (lazymatch type of H with
           | obind _ (transfer _ _) = _ => fail
           | obind _ (LRC.transfer _ _) = _ => fail
           | _ => first
               [ apply obind_inv in H as [? [? H]]
               | match goal with w : (_ * _)%type |- _ => destruct w end
               | match goal with a : atom _ _ |- _ =>
                   match type of H with context[a] => destruct a end end
               ]; mcbn H
           end).
    all: try (exfalso; congruence).
    all: try (match type of H with context[if ?c then _ else _] =>
                let e := fresh in destruct c eqn:e end; mcbn H).
    all: try (match goal with _ : decode_instr _ = Some _ |- _ =>
                move: H; case Ejt: (smem _) => [[niv nit]|]; move=> H; mcbn H end).
    all: unfold transfer, LRC.transfer, instr_rules, LRC.instr_rules, LRC.instr_rules_mp in H.
    all: cbv zeta in H; mcbn H.
    all: repeat (first
           [ match goal with HH : (do! _ <- _; _) = Some _ |- _ =>
               apply obind_inv in HH as [? [? HH]]; mcbn HH end
           | match goal with HH : context[let '{| trpc := _; tr := _ |} := _ in _] |- _ =>
               progress mcbn HH end
           | match goal with HH : Some _ = Some (?a, ?b) |- _ =>
               is_var a; is_var b; injection HH as ? ?; subst end
           | match goal with HH : Some _ = Some ?w |- _ => is_var w; injection HH as ?; subst end
           | match goal with w : (_ * _)%type |- _ => destruct w end
           | match goal with HH : context[match ?c with true => _ | false => _ end] |- _ =>
               let e := fresh "Eif" in revert HH; destruct c eqn:e; intro HH; mcbn HH end
           | match goal with HH : context[let (_, _) := ?x in _] |- _ => destruct x; mcbn HH end ]).
    all: mcbn H.
    all: try (exfalso; congruence).
    all: try (injection H as ? Hev; apply obind_inv in Hev as [? [_ Hev]]; discriminate Hev).
    all: try (match goal with E : belong _ None = false |- _ => discriminate E end).
    all: repeat match goal with u : unit |- _ => destruct u end.
    match goal with Hr : check_ret _ _ = Some _ |- _ => move: Hr end.
    match goal with Hw : _ r = Some _ |- _ => move: Hw end.
    case: taga => // n' Hw; rewrite /check_ret; case: eqP => // Hlvl _.
    subst slvl.
    injection H as Hs' Hc Hz Hc'. subst comp comp' z s'.
    subst G.
    exists (i$ {| vtag := vtag; color := color; entry := entry; is_code := is_code |}).
    exists r. eexists. exists n'.
    do 4 eexists.
    split; [cbn [Symbolic.mem Symbolic.pc Types.vala]; exact Hf|].
    split; [exact DEC|].
    split; [cbn [Symbolic.regs]; exact Hw|].
    split; [cbn [Symbolic.regs]; match goal with H' : _ (as_word (ssrint.Posz 4)) = Some _ |- _ => exact H' end|].
    split; [cbn [Symbolic.regs]; match goal with H' : _ (as_word (ssrint.Posz 1)) = Some _ |- _ => exact H' end|].
    split; [cbn [Symbolic.mem]; exact Ejt|].
    split; [reflexivity|].
    split; [cbn [Types.taga Symbolic.pc]; move/eqnP: Eif0 => ->; reflexivity|].
    split; [move: H7; case: nit {Ejt Eif} => ? ? ? ? /= [<-]; reflexivity|].
    split; [cbn [Types.taga]; exact Eif|].
    split; [match goal with Hio : is_data _ = Some _ |- _ => exact Hio end|].
    split; [match goal with He : evi _ = Some _, Hr : _ (as_word (ssrint.Posz 1)) = Some _ |- _ =>
              move: He; rewrite /evi => He; mcbn He; rewrite Hr in He; mcbn He;
              case: He => <-; reflexivity end|].
    split; [match goal with H' : next_state_do_updates _ _ _ = Some _ |- _ => exact H' end|].
    reflexivity.
  Qed.

  Lemma common_col_mem2 M s1 s2 s3 : common_equiv M s1 s2 s3 -> color_in_memory (mem s2).
  Proof.
    case=> m x1 x2 x3 nn cc t1 t2 t3 wf r1 r2 r3 g1 g2 g3 c1 c2 c3 cl cr hv p1 p2.
    by case: g2 => _ [_ [_ [_ [_ [_ [H _]]]]]].
  Qed.

  Lemma jump_ret_step3 :
    forall (mem3 : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags M)})
           (regs3 : {fmap reg mt -> atom (mword mt) (tag_type lrc_tags R)})
           pc3v int3 n comp i3 ti3 r w rac a1 cell z comp',
      mem3 pc3v = Some (i3 @ ti3) ->
      decode_instr i3 = Some (Jump r) ->
      regs3 r = Some (w @ (Ret n)) ->
      regs3 (as_word (ssrint.Posz 4)) = Some rac ->
      regs3 (as_word (ssrint.Posz 1)) = Some a1 ->
      register_domm regs3 ->
      r <> as_word (ssrint.Posz 1) ->
      is_code ti3 = true ->
      color ti3 = comp ->
      mem3 w = Some cell ->
      color (taga cell) = comp' ->
      belong comp (Some (taga cell)) = false ->
      taga a1 = Other ->
      z = convert (int_of_word (vala a1)) ->
      exists rs,
        next_state_do_updates
          {| mem := mem3; regs := regs3; pc := pc3v @ (Level n.+1 comp); internal := int3 |}
          ((Invalidated :: Invalidated :: Other :: reg_invalidate_hseq)%hseq
           : hseq (tag_type lrc_tags) (R :: R :: R :: nseq 10 R))
          (RegRead (as_word (ssrint.Posz 4)) :: RegRead r :: reg_clear_read)
        = Some {| mem := mem3; regs := rs; pc := pc3v @ (Level n.+1 comp); internal := int3 |} /\
        (forall w' d, rs w' = Some d ->
              (w' = as_word (ssrint.Posz 1) /\ Types.taga d = Other) \/
              (w' <> as_word (ssrint.Posz 1) /\ Types.taga d = Invalidated)) /\
        step_me (NC := NC) {| mem := mem3; regs := regs3; pc := pc3v @ (Level n.+1 comp); internal := int3 |}
          {| mem := mem3; regs := rs; pc := w @ (Level n comp'); internal := int3 |}
          (Some (ERet comp z comp')).
  Proof.
    move=> mem3 regs3 pc3v int3 n comp i3 ti3 r w rac a1 cell z comp'
           Hpc Hdec Hr Hra Hr1 Hdomm Hrne1 Hcode Hcol Hcell Hccol Hbel Hoth Hz.
    have [rs [Hdu [_ Htc]]] := return_do_updates_props
      (st := {| mem := mem3; regs := regs3; pc := pc3v @ (Level n.+1 comp); internal := int3 |})
      Hrne1 Hdomm Hra Hr.
    exists rs. split; first exact: Hdu. split; first exact: Htc.
    have [l Hl] := reg_clear_list_total (Ret n) Hdomm.
    move: Hra; case: rac => rav rat Hra.
    eapply step_jump.
    - reflexivity.
    - exact Hpc.
    - exact Hdec.
    - exact Hr.
    - exact Hra.
    - exact Hl.
    - have [a0 Ha0] : exists a0, regs3 (as_word (ssrint.Posz 0)) = Some a0.
      { case E: (regs3 (as_word (ssrint.Posz 0))) => [a0|]; first by exists a0.
        exfalso. exact: (rd_ex Hdomm (n := 0%N) isT E). }
      have [rest El] : exists rest, l = HSeqCons (Ret n) (HSeqCons (taga a1) rest).
      { move: Hl; rewrite /reg_clear_list /reg_list reg_clear_list_aux_cons Hr1 obindE
          reg_clear_list_aux_cons Ha0 obindE.
        case: (reg_clear_list_aux [:: 2; 3; 5; 6; 7; 16; 17; 18; 19] regs3 (taga a0))
          => [rest|] //= [= <-]; by eexists. }
      subst l.
      unfold next_state_updates_and_pc.
      rewrite Hcell.
      unfold next_state. cbn [op].
      unfold evi, transfer, instr_rules, LRC.instr_rules.
      cbn -[obind belong is_other get_tni_color get_proc_name check_belong check_entry check_ret
            reg_invalidate_hseq next_state_do_updates getm setm build_tpc rcom_value
            reg_clear_read hsbehead hshead].
      rewrite Hr1 !obindE; cbn beta.
      rewrite Hcode !obindE; cbn beta.
      have Hcolor' : (match ti3 with {| color := cx |} => cx end) = comp by exact Hcol.
      rewrite Hcolor' (_ : eqn comp comp = true); last by apply/eqnP.
      cbn beta iota. rewrite obindE.
      rewrite Hbel; cbn beta iota.
      rewrite (_ : is_other (taga a1) = Some tt); last by rewrite /is_other Hoth.
      cbn beta iota. rewrite obindE.
      rewrite (_ : get_tni_color (Some (taga cell)) = Some comp');
        last by move: Hccol; rewrite /get_tni_color; case: (taga cell) => ? ? ? ? /= ->.
      cbn beta iota. rewrite obindE.
      rewrite (_ : check_ret n.+1 (Ret n) = Some tt); last by rewrite /check_ret eqxx.
      cbn beta iota. rewrite !obindE. cbn beta iota. cbn [tr trpc snd fst].
      rewrite Hdu obindE. cbn [mem regs internal rcom_value]. rewrite Hz. reflexivity.
  Qed.

  Lemma pop_frame : forall (m1 m2 m3 : memory) n M a b c col,
    wf_stack m1 m2 m3 n.+1 M ->
    In (a, b, c, col) M -> (taga a = Ret n \/ taga b = Ret n) ->
    exists M' v1 v2 v3 off,
      M = (a, b, c, col) :: M' /\ wf_stack m1 m2 m3 n M' /\
      a = v1 @ (Ret n) /\ b = v2 @ (Ret n) /\ c = v3 @ (Ret n) /\
      ((is_relevant_comp Left col /\ get_offset Left col = Some off /\ v3 = addw v1 (as_word off)) \/
       (is_relevant_comp Right col /\ get_offset Right col = Some off /\ v3 = addw v2 (as_word off))) /\
      points_to_comp_code' Right (side_of col) m1 v1 col /\
      points_to_comp_code m2 v2 col /\ points_to_comp_code m3 v3 col.
  Proof.
    move=> m1 m2 m3 n M a b c col Hwf Hin Ha.
    inversion Hwf; subst.
    all: move: H0; rewrite addn1 => -[?]; subst n0.
    all: case: Hin => [Eh | Htl].
    1: case: Eh => <- <- <- <-; exists st, v1, v2, (v1 + as_word off)%w, off;
       split; [reflexivity|]; split; [exact WF_ST|];
       do 3 (split; [reflexivity|]);
       split; [left; split; [exact SIDE | split; [exact OFF_C | reflexivity]]
              | split; [exact PTS_CODE1 | split; [exact PTS_CODE2 | exact PTS_CODE3]]].
    2: case: Eh => <- <- <- <-; exists st, v1, v2, (v2 + as_word off)%w, off;
       split; [reflexivity|]; split; [exact WF_ST|];
       do 3 (split; [reflexivity|]);
       split; [right; split; [exact SIDE | split; [exact OFF_C | reflexivity]]
              | split; [exact PTS_CODE1 | split; [exact PTS_CODE2 | exact PTS_CODE3]]].
    all: exfalso; have [k [Hk [Hk2 [_ Hlt]]]] := wf_stack_levels_lt' WF_ST Htl;
         case: Ha => Ha; [move: Hk | move: Hk2]; rewrite Ha => -[Ek]; subst k; by rewrite ltnn in Hlt.
  Qed.

  Lemma return_pop_post_ws : forall ws (st : state) (r0 : reg mt) cell4 v' n hd M',
      r0 <> as_word (ssrint.Posz 1) ->
      register_domm (regs st) ->
      regs st (as_word (ssrint.Posz 4)) = Some cell4 ->
      regs st r0 = Some (Types.Atom v' (Ret n)) ->
      capability_correctness (hd :: M') ws st ->
      (forall v k, in_stack [:: hd] ws v k -> k = n) ->
      exists rs,
        next_state_do_updates st
          ((Invalidated :: Invalidated :: Other :: reg_invalidate_hseq)%hseq
           : hseq (tag_type lrc_tags) (R :: R :: R :: nseq 10 R))
          (RegRead (as_word (ssrint.Posz 4)) :: RegRead r0 :: reg_clear_read)
        = Some {| mem := mem st; regs := rs; pc := pc st; internal := internal st |}
        /\ (forall i pcn, register_address_correctness i
                          {| mem := mem st; regs := rs; pc := pcn; internal := internal st |})
        /\ (forall pcn, capability_correctness M' ws
                          {| mem := mem st; regs := rs; pc := pcn; internal := internal st |})
        /\ (forall w d, rs w = Some d ->
              (w = as_word (ssrint.Posz 1) /\ Types.taga d = Other) \/
              (w <> as_word (ssrint.Posz 1) /\ Types.taga d = Invalidated)).
  Proof.
    move=> ws st r0 cell4 v' n hd M' Hr0ne1 Hdomm Hr4 Hr0 Hcap Hlev.
    have [rs [Hdu [_ Htagclass]]] := return_do_updates_props Hr0ne1 Hdomm Hr4 Hr0.
    exists rs. split; first exact: Hdu.
    split.
    { move=> i pcn rv rr Hrr; rewrite /address_correctness.
      case: (Htagclass rr rv Hrr) => [[_ ->] | [_ ->]]; exact: I. }
    split; last exact: Htagclass.
    move=> pcn kv kn kp kprem; destruct kp as [kr | kw].
    - case: (Htagclass kr _ kprem) => [[_ Ht] | [_ Ht]]; discriminate Ht.
    - have [kis_in kunicity] := Hcap kv kn (inr kw) kprem.
      split.
      + destruct ws; move: kis_in Hlev; rewrite /in_stack => -[ksv1 [ksv2 [kcol [kHhead | kis_in2]]]] Hlev.
        all: try (by exists ksv1, ksv2, kcol).
        all: exfalso; have Ekn : kn = n by apply: (Hlev kv kn); exists ksv1, ksv2, kcol; left.
        all: subst kn; eapply (kunicity (inl _)); exact Hr0.
      + move=> kp' kv'; destruct kp' as [kr' | kw'].
        * move=> Hr'.
          case: (Htagclass kr' _ Hr') => [[_ Ht] | [_ Ht]]; discriminate Ht.
        * move=> Hmem'; exact: (kunicity (inr kw') kv' Hmem').
  Qed.

  Lemma memory_match_pop : forall i (hd : stack_value * stack_value * stack_value * Component.id)
      M' (s t s' t' : state),
    memory_match i (hd :: M') s t ->
    mem s' = mem s -> mem t' = mem t ->
    (forall w d, mem s w = Some d ->
       Types.Atom (vala d) (vtag (taga d)) <> (if i is Left then hd.1.1.1 else hd.1.1.2)) ->
    memory_match i M' s' t'.
  Proof.
    move=> i hd M' s t s' t' Hmm Es Et Hex w d dnc drel.
    rewrite Es Et. have [H1 H2] := Hmm w d dnc drel.
    have pop : forall d1 d2, mem s w = Some d1 -> data_match' i (hd :: M') d1 d2 -> data_match' i M' d1 d2.
    { move=> [v1 t1] [v2 t2] Hd1 /= [Et12 [Ev Hc]]. split; first exact Et12. split; first exact Ev.
      move: Hc. case Evt: (vtag t1) => [k| | |] //=.
      destruct i => /= -[sv [c' [Hhead | Htl]]]; try (by exists sv, c').
      all: exfalso; apply: (Hex w (v1 @ t1) Hd1); by rewrite Hhead /= Evt. }
    split => Hw.
    - have [d'' [Hdm Hd'']] := H1 Hw. exists d''. split; last exact Hd''. exact: pop Hd'' Hdm.
    - have [d'' [Hdm Hd'']] := H2 Hw. exists d''. split; last exact Hd''. exact: pop Hw Hdm.
  Qed.

  Lemma ser_case_PP : forall M s1 s2 s3 comp z comp' s1' s2',
    step_me (NC := NC) s1 s1' (Some (ERet comp z comp')) ->
    step_me (NC := NC) s2 s2' (Some (ERet comp z comp')) ->
    common_equiv M s1 s2 s3 -> strong_equiv Left M s1 s3 -> weak_equiv Right M s2 s3 ->
    comp' \in domm ip ->
    exists s3' M', Plus sem'' s3 [:: ERet comp z comp'] s3' /\ match_states M' s1' s2' s3'.
  Proof.
    import_context.
    move=> M s1 s2 s3 comp z comp' s1' s2' Hs1 Hs2 common strong weak ip_comp'.
    have [ip1 [r1 [w1 [n1 [rac1 [a11 [cell1 [st1 H1]]]]]]]] := return_step_inv Hs1.
    have [Hpc1 [Hdec1 [Hr1 [Hra1 [Hrcom1 [Hcell1 [Hcode1 [Hcol1 [Htpc1 [Hccol1 [Hbel1 [Hoth1 [Hz1 [Hdu1 Hs1']]]]]]]]]]]]]] := H1.
    have [ip2 [r2 [w2 [n2 [rac2 [a12 [cell2 [st2 H2]]]]]]]] := return_step_inv Hs2.
    have [Hpc2 [Hdec2 [Hr2 [Hra2 [Hrcom2 [Hcell2 [Hcode2 [Hcol2 [Htpc2 [Hccol2 [Hbel2 [Hoth2 [Hz2 [Hdu2 Hs2']]]]]]]]]]]]]] := H2.
    inversion strong as [? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off
                         s_reg_cor s'_reg_cor mem_match reg_match].
    inversion common as [? ? ? ? n c tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          gmc1 gmc2 gmc3 capa_cor1 capa_cor2 capa_cor3 code_left code_right Hcval wpcc1 wpcc2].
    inversion weak as [? ? ? color_eq2 side_eq2 w_mem_cor2 w_mem_cor3 entry_off2 mem_match2].
    clear H1 H2.
    have [En Ec] : n = n1.+1 /\ c = comp by move: tag_pc1; rewrite Htpc1 => -[-> ->].
    subst n c.
    have Hcol_s1 : color_of s1 = comp by rewrite (color_of_pc_tag s1) Htpc1.
    inversion pc_s1_s3 as [? ? _ [Hnone _] | ? ? v0 off [Hv0 _] Hoff Hpc3v].
    { exfalso. by rewrite Hpc1 in Hnone. }
    rewrite Hcol_s1 in Hoff.
    have Hrel1 : is_relevant_comp Left comp.
    { move: side_eq; rewrite Hcol_s1 /side_of /is_relevant_comp; by case: (comp \in domm ip). }
    move: Hpc1 Hdec1 Hcode1 Hcol1; case: ip1 => i1 ti1 /= Hpc1 Hdec1 Hcode1 Hcol1.
    have [Xpc _] := code_left (vala (pc s1)) i1 ti1 off comp Hrel1 Hoff Hcode1 Hcol1.
    have [i3 [Hdm Hpc3cell]] := Xpc Hpc1.
    have Hdec3 : decode_instr i3 = Some (Jump r1).
    { inversion Hdm as [Hnj Hnj' Heq | Ha Ha2 | imm imm' dd dd' Hj Hj2 Hmd Hmd' Hicd Htagd Hreld].
      - rewrite -Heq. exact Hdec1.
      - exfalso. have E := etrans (esym Hdec1) Ha. discriminate E.
      - exfalso. have E := etrans (esym Hdec1) Hj. discriminate E. }
    have [d3 [Hdm3 Hr3]] := proj2 (reg_match r1 (w1 @ (Ret n1))) Hr1.
    move: d3 Hdm3 Hr3 => [v3 t3] [Et3 [sv' [cf Hin]]] Hr3. subst t3.
    move: a11 Hrcom1 Hoth1 Hz1 => [va11 ta11] Hrcom1 /= Hoth1 Hz1. subst ta11.
    have [d13 [Hdm13 Hr13]] := proj2 (reg_match (as_word (ssrint.Posz 1)) (va11 @ Other)) Hrcom1.
    move: d13 Hdm13 Hr13 => [v13 t13] [Et13 Ev13] Hr13. subst t13 v13.
    have [M' [x1 [x2 [x3 [offc [EM [WF' [Ex1 [Ex2 [Ex3 [Hoffrel [PTS1 [PTS2 PTS3]]]]]]]]]]]]] :=
      pop_frame wfst Hin (or_introl erefl).
    move: Ex1 Ex3 => [Ex1] [Ex3]. subst x1 x3.
    have Ecf : cf = comp'.
    { move: PTS1; rewrite /points_to_comp_code' Hcell1 /= => -[<- _]. exact Hccol1. }
    subst cf.
    have [_ [Hoffc Ev3]] : is_relevant_comp Left comp' /\ get_offset Left comp' = Some offc /\ v3 = (w1 + as_word offc)%w.
    { case: Hoffrel => [Hleft|[Hrr _]]; first exact Hleft.
      exfalso. apply: (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)).
      - by inversion Hmergeable_ifaces as [[_ fdisj] _].
      - exact: Hrr.
      - exact: ip_comp'. }
    have [cell3 [Hcell3 [Hccol3 Hcode3c]]] :
        exists cell3, mem s3 v3 = Some cell3 /\ color (taga cell3) = comp' /\ is_code (taga cell3).
    { move: PTS3; rewrite /points_to_comp_code; case: (mem s3 v3) => [c3|] //= [? ?]; by exists c3. }
    have Hbel3 : belong comp (Some (taga cell3)) = false.
    { move: Hbel1 Hccol1 Hccol3; rewrite /belong.
      case: (taga cell1) => ? c1 ? ?; case: (taga cell3) => ? c3 ? ? /= Hb E1 E3. by rewrite E3 -E1. }
    have Hrne1 : r1 <> as_word (ssrint.Posz 1).
    { move=> E. rewrite E Hrcom1 in Hr1. discriminate Hr1. }
    have [rac3 Hra3] : exists rac3, regs s3 (as_word (ssrint.Posz 4)) = Some rac3.
    { case E: (regs s3 (as_word (ssrint.Posz 4))) => [x|]; first by exists x.
      exfalso. exact: (rd_r4 reg_domm3 E). }
    destruct s3 as [mem3 regs3 [pc3v pc3t] int3].
    have Epc3t : pc3t = Level n1.+1 comp by exact: tag_pc3.
    subst pc3t.
    rewrite /= in Hpc3v Hpc3cell Hr3 Hr13 Hra3 Hcell3.
    rewrite -Hpc3v in Hpc3cell.
    have [rs3 [Hdu3 [Htc3 Hstep3]]] :=
      jump_ret_step3 int3 Hpc3cell Hdec3 Hr3 Hra3 Hr13 reg_domm3 Hrne1 Hcode1 Hcol1
                     Hcell3 Hccol3 Hbel3 erefl Hz1.
    exists {| mem := mem3; regs := rs3; pc := v3 @ (Level n1 comp'); internal := int3 |}, M'.
    split.
    { apply: plus_one. exact: Hstep3. }
    rewrite EM in capa_cor1 capa_cor2 capa_cor3.
    have Hlev : forall ws v k,
        in_stack ([:: ((w1 @ (Ret n1) : stack_value), sv', (v3 @ (Ret n1) : stack_value), comp')] : stack) ws v k -> k = n1.
    { move=> ws v k; rewrite Ex2 /in_stack; case: ws => -[? [? [? [Hh|[]]]]]; by case: Hh. }
    have [rs1 [Hdu1' [Hrac1 [Hcap1 Htc1]]]] :=
      return_pop_post_ws Hrne1 reg_domm1 Hra1 Hr1 capa_cor1 (Hlev WS_S1).
    have Est1 : st1 = {| mem := mem s1; regs := rs1; pc := pc s1; internal := internal s1 |}
      by have E := etrans (esym Hdu1) Hdu1'; case: E.
    have En2 : n2 = n1 by move: tag_pc2; rewrite Htpc2 => -[].
    subst n2.
    have Hr2ne1 : r2 <> as_word (ssrint.Posz 1).
    { move=> E. rewrite E Hrcom2 in Hr2. case: Hr2 => Ea. rewrite Ea in Hoth2. discriminate Hoth2. }
    have [rs2 [Hdu2' [Hrac2 [Hcap2 Htc2]]]] :=
      return_pop_post_ws Hr2ne1 reg_domm2 Hra2 Hr2 capa_cor2 (Hlev WS_S2).
    have Est2 : st2 = {| mem := mem s2; regs := rs2; pc := pc s2; internal := internal s2 |}
      by have E := etrans (esym Hdu2) Hdu2'; case: E.
    subst st1 st2. rewrite /= in Hs1' Hs2'. subst s1' s2'.
    have [rs3' [Hdu3' [Hrac3 [Hcap3 Htc3']]]] :=
      return_pop_post_ws Hrne1 reg_domm3 Hra3 Hr3 capa_cor3 (Hlev WS_S3).
    have Ers3 : rs3' = rs3 by have E := etrans (esym Hdu3') Hdu3; case: E.
    subst rs3'.
    have Ex2w : x2 = w2.
    { have [Hin2 _] := capa_cor2 w2 n1 (inl r2) Hr2.
      move: Hin2; rewrite /in_stack => -[sv1 [sv2 [col [Hhd | Htl]]]].
      - move: Hhd; rewrite Ex2 => -[_ Ew _ _]. by case: Ew.
      - exfalso. have [k [_ [Hb [_ Hk]]]] := wf_stack_levels_lt' WF' Htl.
        move: Hb => /= [Ek]. subst k. by rewrite ltnn in Hk. }
    subst x2.
    apply: match_states_left.
    - apply: (@common_equiv_def M' _ _ _ n1 comp').
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + exact: WF'.
      + exact: (reg_domm_step Hs1 reg_domm1).
      + exact: (reg_domm_step Hs2 reg_domm2).
      + exact: (reg_domm_step Hstep3 reg_domm3).
      + exact: gmc1.
      + exact: gmc2.
      + exact: gmc3.
      + exact: Hcap1.
      + exact: Hcap2.
      + exact: Hcap3.
      + eapply combined_codes_mem_cong; last exact: code_left. all: reflexivity.
      + eapply combined_codes_mem_cong; last exact: code_right. all: reflexivity.
      + by rewrite ip_comp'.
      + apply: (pc_code_color_pts' (s := {| mem := mem s1; regs := rs1; pc := w1 @ (Level n1 comp'); internal := internal s1 |}));
          [ exact: PTS1 | reflexivity ].
      + apply: (pc_code_color_pts (C := comp')); last reflexivity. exact: PTS2.
    - rewrite EM in mem_match.
      have [rs1b [Hdu1b [Hval1 _]]] := return_do_updates_props Hrne1 reg_domm1 Hra1 Hr1.
      have Ers1 : rs1b = rs1 by have E := etrans (esym Hdu1b) Hdu1'; case: E.
      subst rs1b.
      have [rs3b [Hdu3b [Hval3 _]]] := return_do_updates_props Hrne1 reg_domm3 Hra3 Hr3.
      have Ers3 : rs3b = rs3 by have E := etrans (esym Hdu3b) Hdu3; case: E.
      subst rs3b.
      apply: strong_equiv_def.
      + apply: (same_pc_normal (v := cell1) (off := offc)).
        * split; first exact Hcell1.
          move: PTS1; rewrite /points_to_comp_code' Hcell1 /= => -[_ [[_ Hrr]|Hic]];
            [ by move: Hrr; rewrite /side_of ip_comp' | exact Hic ].
        * exact Hoffc.
        * exact Ev3.
      + reflexivity.
      + by rewrite /side_of /= ip_comp'.
      + exact: s_mem_cor.
      + exact: s'_mem_cor.
      + exact: entry_off.
      + exact: Hrac1.
      + exact: Hrac3.
      + apply: (memory_match_pop mem_match); [reflexivity | reflexivity |].
        move=> w d Hd /= E. case: E => Ev Et.
        have prem : exists t, mem s1 w = Some ((vala d) @ t) /\ vtag t = Ret n1.
        { exists (taga d). split; last exact Et. by rewrite Hd; case: d {Hd Ev Et}. }
        have [_ uni] := capa_cor1 (vala d) n1 (inr w) prem.
        exact: (uni (inl r1) w1 Hr1).
      + apply: (@registers_match_clear Left M' _ _ va11).
        * have D1 := reg_domm_step Hs1 reg_domm1. have D3 := reg_domm_step Hstep3 reg_domm3.
          rewrite /register_domm in D1 D3. by rewrite D1 D3.
        * exact: Htc1.
        * exact: Htc3.
        * by rewrite /= Hval1 Hrcom1.
        * by rewrite /= Hval3 Hr13.
    - inversion weak as [? ? ? color_eq2' side_eq2' w_mem_cor2' w_mem_cor3' entry_off2' mem_match2'].
      rewrite EM in mem_match2'.
      apply: weak_equiv_def.
      + reflexivity.
      + by rewrite /side_of /= ip_comp'.
      + exact: w_mem_cor2'.
      + exact: w_mem_cor3'.
      + exact: entry_off2'.
      + apply: (memory_match_pop mem_match2'); [reflexivity | reflexivity |].
        move=> w d Hd /= E. rewrite Ex2 in E. case: E => Ev Et.
        have prem : exists t, mem s2 w = Some ((vala d) @ t) /\ vtag t = Ret n1.
        { exists (taga d). split; last exact Et. by rewrite Hd; case: d {Hd Ev Et}. }
        have [_ uni] := capa_cor2 (vala d) n1 (inr w) prem.
        exact: (uni (inl r2) w2 Hr2).
  Qed.

  Lemma ser_case_PC : forall M s1 s2 s3 comp z comp' s1' s2',
    step_me (NC := NC) s1 s1' (Some (ERet comp z comp')) ->
    step_me (NC := NC) s2 s2' (Some (ERet comp z comp')) ->
    common_equiv M s1 s2 s3 -> strong_equiv Left M s1 s3 -> weak_equiv Right M s2 s3 ->
    comp' \in domm ic ->
    exists s3' M', Plus sem'' s3 [:: ERet comp z comp'] s3' /\ match_states M' s1' s2' s3'.
  Proof.
    import_context.
    move=> M s1 s2 s3 comp z comp' s1' s2' Hs1 Hs2 common strong weak ic_comp'.
    have [ip1 [r1 [w1 [n1 [rac1 [a11 [cell1 [st1 H1]]]]]]]] := return_step_inv Hs1.
    have [Hpc1 [Hdec1 [Hr1 [Hra1 [Hrcom1 [Hcell1 [Hcode1 [Hcol1 [Htpc1 [Hccol1 [Hbel1 [Hoth1 [Hz1 [Hdu1 Hs1']]]]]]]]]]]]]] := H1.
    have [ip2 [r2 [w2 [n2 [rac2 [a12 [cell2 [st2 H2]]]]]]]] := return_step_inv Hs2.
    have [Hpc2 [Hdec2 [Hr2 [Hra2 [Hrcom2 [Hcell2 [Hcode2 [Hcol2 [Htpc2 [Hccol2 [Hbel2 [Hoth2 [Hz2 [Hdu2 Hs2']]]]]]]]]]]]]] := H2.
    inversion strong as [? ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off
                         s_reg_cor s'_reg_cor mem_match reg_match].
    inversion common as [? ? ? ? n c tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          gmc1 gmc2 gmc3 capa_cor1 capa_cor2 capa_cor3 code_left code_right Hcval wpcc1 wpcc2].
    inversion weak as [? ? ? color_eq2 side_eq2 w_mem_cor2 w_mem_cor3 entry_off2 mem_match2].
    clear H1 H2.
    have [En Ec] : n = n1.+1 /\ c = comp by move: tag_pc1; rewrite Htpc1 => -[-> ->].
    subst n c.
    have Hcol_s1 : color_of s1 = comp by rewrite (color_of_pc_tag s1) Htpc1.
    inversion pc_s1_s3 as [? ? _ [Hnone _] | ? ? v0 off [Hv0 _] Hoff Hpc3v].
    { exfalso. by rewrite Hpc1 in Hnone. }
    rewrite Hcol_s1 in Hoff.
    have Hrel1 : is_relevant_comp Left comp.
    { move: side_eq; rewrite Hcol_s1 /side_of /is_relevant_comp; by case: (comp \in domm ip). }
    move: Hpc1 Hdec1 Hcode1 Hcol1; case: ip1 => i1 ti1 /= Hpc1 Hdec1 Hcode1 Hcol1.
    have [Xpc _] := code_left (vala (pc s1)) i1 ti1 off comp Hrel1 Hoff Hcode1 Hcol1.
    have [i3 [Hdm Hpc3cell]] := Xpc Hpc1.
    have Hdec3 : decode_instr i3 = Some (Jump r1).
    { inversion Hdm as [Hnj Hnj' Heq | Ha Ha2 | imm imm' dd dd' Hj Hj2 Hmd Hmd' Hicd Htagd Hreld].
      - rewrite -Heq. exact Hdec1.
      - exfalso. have E := etrans (esym Hdec1) Ha. discriminate E.
      - exfalso. have E := etrans (esym Hdec1) Hj. discriminate E. }
    have [d3 [Hdm3 Hr3]] := proj2 (reg_match r1 (w1 @ (Ret n1))) Hr1.
    move: d3 Hdm3 Hr3 => [v3 t3] [Et3 [sv' [cf Hin]]] Hr3. subst t3.
    move: a11 Hrcom1 Hoth1 Hz1 => [va11 ta11] Hrcom1 /= Hoth1 Hz1. subst ta11.
    have [d13 [Hdm13 Hr13]] := proj2 (reg_match (as_word (ssrint.Posz 1)) (va11 @ Other)) Hrcom1.
    move: d13 Hdm13 Hr13 => [v13 t13] [Et13 Ev13] Hr13. subst t13 v13.
    have [M' [x1 [x2 [x3 [offc [EM [WF' [Ex1 [Ex2 [Ex3 [Hoffrel [PTS1 [PTS2 PTS3]]]]]]]]]]]]] :=
      pop_frame wfst Hin (or_introl erefl).
    move: Ex1 Ex3 => [Ex1] [Ex3]. subst x1 x3.
    have Ecf : cf = comp'.
    { move: PTS1; rewrite /points_to_comp_code' Hcell1 /= => -[<- _]. exact Hccol1. }
    subst cf.
    have Hnip : comp' \in domm ip = false.
    { case Eip: (comp' \in domm ip) => //. exfalso.
      apply: (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)).
      - by inversion Hmergeable_ifaces as [[_ fdisj] _].
      - exact: ic_comp'.
      - exact: Eip. }
    have [_ [Hoffc Ev3]] : is_relevant_comp Right comp' /\ get_offset Right comp' = Some offc /\ v3 = (x2 + as_word offc)%w.
    { case: Hoffrel => [[Hrl _]|Hright]; last exact Hright.
      exfalso. move: Hrl; rewrite /is_relevant_comp Hnip. by []. }
    have [cell3 [Hcell3 [Hccol3 Hcode3c]]] :
        exists cell3, mem s3 v3 = Some cell3 /\ color (taga cell3) = comp' /\ is_code (taga cell3).
    { move: PTS3; rewrite /points_to_comp_code; case: (mem s3 v3) => [c3|] //= [? ?]; by exists c3. }
    have Hbel3 : belong comp (Some (taga cell3)) = false.
    { move: Hbel1 Hccol1 Hccol3; rewrite /belong.
      case: (taga cell1) => ? c1 ? ?; case: (taga cell3) => ? c3 ? ? /= Hb E1 E3. by rewrite E3 -E1. }
    have Hrne1 : r1 <> as_word (ssrint.Posz 1).
    { move=> E. rewrite E Hrcom1 in Hr1. discriminate Hr1. }
    have [rac3 Hra3] : exists rac3, regs s3 (as_word (ssrint.Posz 4)) = Some rac3.
    { case E: (regs s3 (as_word (ssrint.Posz 4))) => [x|]; first by exists x.
      exfalso. exact: (rd_r4 reg_domm3 E). }
    destruct s3 as [mem3 regs3 [pc3v pc3t] int3].
    have Epc3t : pc3t = Level n1.+1 comp by exact: tag_pc3.
    subst pc3t.
    rewrite /= in Hpc3v Hpc3cell Hr3 Hr13 Hra3 Hcell3.
    rewrite -Hpc3v in Hpc3cell.
    have [rs3 [Hdu3 [Htc3 Hstep3]]] :=
      jump_ret_step3 int3 Hpc3cell Hdec3 Hr3 Hra3 Hr13 reg_domm3 Hrne1 Hcode1 Hcol1
                     Hcell3 Hccol3 Hbel3 erefl Hz1.
    exists {| mem := mem3; regs := rs3; pc := v3 @ (Level n1 comp'); internal := int3 |}, M'.
    split.
    { apply: plus_one. exact: Hstep3. }
    rewrite EM in capa_cor1 capa_cor2 capa_cor3.
    have Hlev : forall ws v k,
        in_stack ([:: ((w1 @ (Ret n1) : stack_value), sv', (v3 @ (Ret n1) : stack_value), comp')] : stack) ws v k -> k = n1.
    { move=> ws v k; rewrite Ex2 /in_stack; case: ws => -[? [? [? [Hh|[]]]]]; by case: Hh. }
    have [rs1 [Hdu1' [Hrac1 [Hcap1 Htc1]]]] :=
      return_pop_post_ws Hrne1 reg_domm1 Hra1 Hr1 capa_cor1 (Hlev WS_S1).
    have Est1 : st1 = {| mem := mem s1; regs := rs1; pc := pc s1; internal := internal s1 |}
      by have E := etrans (esym Hdu1) Hdu1'; case: E.
    have En2 : n2 = n1 by move: tag_pc2; rewrite Htpc2 => -[].
    subst n2.
    have Hr2ne1 : r2 <> as_word (ssrint.Posz 1).
    { move=> E. rewrite E Hrcom2 in Hr2. case: Hr2 => Ea. rewrite Ea in Hoth2. discriminate Hoth2. }
    have [rs2 [Hdu2' [Hrac2 [Hcap2 Htc2]]]] :=
      return_pop_post_ws Hr2ne1 reg_domm2 Hra2 Hr2 capa_cor2 (Hlev WS_S2).
    have Est2 : st2 = {| mem := mem s2; regs := rs2; pc := pc s2; internal := internal s2 |}
      by have E := etrans (esym Hdu2) Hdu2'; case: E.
    subst st1 st2. rewrite /= in Hs1' Hs2'. subst s1' s2'.
    have [rs3' [Hdu3' [Hrac3 [Hcap3 Htc3']]]] :=
      return_pop_post_ws Hrne1 reg_domm3 Hra3 Hr3 capa_cor3 (Hlev WS_S3).
    have Ers3 : rs3' = rs3 by have E := etrans (esym Hdu3') Hdu3; case: E.
    subst rs3'.
    have Ex2w : x2 = w2.
    { have [Hin2 _] := capa_cor2 w2 n1 (inl r2) Hr2.
      move: Hin2; rewrite /in_stack => -[sv1 [sv2 [col [Hhd | Htl]]]].
      - move: Hhd; rewrite Ex2 => -[_ Ew _ _]. by case: Ew.
      - exfalso. have [k [_ [Hb [_ Hk]]]] := wf_stack_levels_lt' WF' Htl.
        move: Hb => /= [Ek]. subst k. by rewrite ltnn in Hk. }
    subst x2.
    apply: match_states_right.
    - apply: (@common_equiv_def M' _ _ _ n1 comp').
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + exact: WF'.
      + exact: (reg_domm_step Hs1 reg_domm1).
      + exact: (reg_domm_step Hs2 reg_domm2).
      + exact: (reg_domm_step Hstep3 reg_domm3).
      + exact: gmc1.
      + exact: gmc2.
      + exact: gmc3.
      + exact: Hcap1.
      + exact: Hcap2.
      + exact: Hcap3.
      + eapply combined_codes_mem_cong; last exact: code_left. all: reflexivity.
      + eapply combined_codes_mem_cong; last exact: code_right. all: reflexivity.
      + by rewrite ic_comp' orbT.
      + apply: (pc_code_color_pts' (s := {| mem := mem s1; regs := rs1; pc := w1 @ (Level n1 comp'); internal := internal s1 |}));
          [ exact: PTS1 | reflexivity ].
      + apply: (pc_code_color_pts (C := comp')); last reflexivity. exact: PTS2.
    -
      rewrite EM in mem_match.
      apply: weak_equiv_def.
      + reflexivity.
      + by rewrite /side_of /= Hnip.
      + exact: s_mem_cor.
      + exact: s'_mem_cor.
      + exact: entry_off.
      + apply: (memory_match_pop mem_match); [reflexivity | reflexivity |].
        move=> w d Hd /= E. case: E => Ev Et.
        have prem : exists t, mem s1 w = Some ((vala d) @ t) /\ vtag t = Ret n1.
        { exists (taga d). split; last exact Et. by rewrite Hd; case: d {Hd Ev Et}. }
        have [_ uni] := capa_cor1 (vala d) n1 (inr w) prem.
        exact: (uni (inl r1) w1 Hr1).
    -
      inversion weak as [? ? ? color_eq2' side_eq2' w_mem_cor2' w_mem_cor3' entry_off2' mem_match2'].
      rewrite EM in mem_match2'.
      have [rs2b [Hdu2b [Hval2 _]]] := return_do_updates_props Hr2ne1 reg_domm2 Hra2 Hr2.
      have Ers2 : rs2b = rs2 by have E := etrans (esym Hdu2b) Hdu2'; case: E.
      subst rs2b.
      have [rs3b [Hdu3b [Hval3 _]]] := return_do_updates_props Hrne1 reg_domm3 Hra3 Hr3.
      have Ers3 : rs3b = rs3 by have E := etrans (esym Hdu3b) Hdu3; case: E.
      subst rs3b.
      have Hva : vala a12 = va11.
      { apply: convert_int_of_word_inj. by rewrite -Hz2 Hz1. }
      apply: strong_equiv_def.
      + apply: (same_pc_normal (v := cell2) (off := offc)).
        * split; first exact Hcell2.
          move: PTS2; rewrite /points_to_comp_code Hcell2 /= => -[_ Hic]. exact Hic.
        * exact Hoffc.
        * exact Ev3.
      + reflexivity.
      + by rewrite /side_of /= Hnip.
      + exact: w_mem_cor2'.
      + exact: w_mem_cor3'.
      + exact: entry_off2'.
      + exact: Hrac2.
      + exact: Hrac3.
      + apply: (memory_match_pop mem_match2'); [reflexivity | reflexivity |].
        move=> w d Hd /= E. rewrite Ex2 in E. case: E => Ev Et.
        have prem : exists t, mem s2 w = Some ((vala d) @ t) /\ vtag t = Ret n1.
        { exists (taga d). split; last exact Et. by rewrite Hd; case: d {Hd Ev Et}. }
        have [_ uni] := capa_cor2 (vala d) n1 (inr w) prem.
        exact: (uni (inl r2) w2 Hr2).
      + apply: (@registers_match_clear Right M' _ _ va11).
        * have D2 := reg_domm_step Hs2 reg_domm2. have D3 := reg_domm_step Hstep3 reg_domm3.
          rewrite /register_domm in D2 D3. by rewrite D2 D3.
        * exact: Htc2.
        * exact: Htc3.
        * by rewrite /= Hval2 Hrcom2 /= Hva.
        * by rewrite /= Hval3 Hr13.
  Qed.

  Lemma ser_case_CP : forall M s1 s2 s3 comp z comp' s1' s2',
    step_mp (NC := NC) s1 s1' (Some (ERet comp z comp')) ->
    step_me (NC := NC) s2 s2' (Some (ERet comp z comp')) ->
    common_equiv M s1 s2 s3 -> weak_equiv Left M s1 s3 -> strong_equiv Right M s2 s3 ->
    comp' \in domm ip ->
    exists s3' M', Plus sem'' s3 [:: ERet comp z comp'] s3' /\ match_states M' s1' s2' s3'.
  Proof.
    import_context.
    move=> M s1 s2 s3 comp z comp' s1' s2' Hs1 Hs2 common weak strong ip_comp'.
    have [ip1 [r1 [w1 [n1 [rac1 [a11 [cell1 [st1 H1]]]]]]]] := return_step_inv_mp Hs1.
    have [Hpc1 [Hdec1 [Hr1 [Hra1 [Hrcom1 [Hcell1 [Hcol1 [Htpc1 [Hccol1 [Hbel1 [Hdat1 [Hz1 [Hdu1 Hs1']]]]]]]]]]]]] := H1.
    have [ip2 [r2 [w2 [n2 [rac2 [a12 [cell2 [st2 H2]]]]]]]] := return_step_inv Hs2.
    have [Hpc2 [Hdec2 [Hr2 [Hra2 [Hrcom2 [Hcell2 [Hcode2 [Hcol2 [Htpc2 [Hccol2 [Hbel2 [Hoth2 [Hz2 [Hdu2 Hs2']]]]]]]]]]]]]] := H2.
    inversion strong as [? ? ? pc_s2_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off
                         s_reg_cor s'_reg_cor mem_match reg_match].
    inversion common as [? ? ? ? n c tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          gmc1 gmc2 gmc3 capa_cor1 capa_cor2 capa_cor3 code_left code_right Hcval wpcc1 wpcc2].
    inversion weak as [? ? ? color_eq1 side_eq1 w_mem_cor1 w_mem_cor3 entry_off1 mem_match1].
    clear H1 H2.
    have [En Ec] : n = n2.+1 /\ c = comp by move: tag_pc2; rewrite Htpc2 => -[-> ->].
    subst n c.
    have En1 : n1 = n2 by move: tag_pc1; rewrite Htpc1 => -[].
    subst n1.
    have Hcol_s2 : color_of s2 = comp by rewrite (color_of_pc_tag s2) Htpc2.
    inversion pc_s2_s3 as [? ? _ [Hnone _] | ? ? v0 off [Hv0 _] Hoff Hpc3v].
    { exfalso. by rewrite Hpc2 in Hnone. }
    rewrite Hcol_s2 in Hoff.
    have Hrel2 : is_relevant_comp Right comp.
    { move: side_eq; rewrite Hcol_s2 /side_of /is_relevant_comp.
      case Eip: (comp \in domm ip) => // _.
      move: Hcval; rewrite Eip /=. by []. }
    move: Hpc2 Hdec2 Hcode2 Hcol2; case: ip2 => i2 ti2 /= Hpc2 Hdec2 Hcode2 Hcol2.
    have [Xpc _] := code_right (vala (pc s2)) i2 ti2 off comp Hrel2 Hoff Hcode2 Hcol2.
    have [i3 [Hdm Hpc3cell]] := Xpc Hpc2.
    have Hdec3 : decode_instr i3 = Some (Jump r2).
    { inversion Hdm as [Hnj Hnj' Heq | Ha Ha2 | imm imm' dd dd' Hj Hj2 Hmd Hmd' Hicd Htagd Hreld].
      - rewrite -Heq. exact Hdec2.
      - exfalso. have E := etrans (esym Hdec2) Ha. discriminate E.
      - exfalso. have E := etrans (esym Hdec2) Hj. discriminate E. }
    have [d3 [Hdm3 Hr3]] := proj2 (reg_match r2 (w2 @ (Ret n2))) Hr2.
    move: d3 Hdm3 Hr3 => [v3 t3] [Et3 [sv' [cf Hin]]] Hr3. subst t3.
    move: a12 Hrcom2 Hoth2 Hz2 => [va12 ta12] Hrcom2 /= Hoth2 Hz2. subst ta12.
    have [d13 [Hdm13 Hr13]] := proj2 (reg_match (as_word (ssrint.Posz 1)) (va12 @ Other)) Hrcom2.
    move: d13 Hdm13 Hr13 => [v13 t13] [Et13 Ev13] Hr13. subst t13 v13.
    have [M' [x1 [x2 [x3 [offc [EM [WF' [Ex1 [Ex2 [Ex3 [Hoffrel [PTS1 [PTS2 PTS3]]]]]]]]]]]]] :=
      pop_frame wfst Hin (or_intror erefl).
    move: Ex2 Ex3 => [Ex2] [Ex3]. subst x2 x3.
    have Ecf : cf = comp'.
    { move: PTS2; rewrite /points_to_comp_code Hcell2 /= => -[<- _]. exact Hccol2. }
    subst cf.
    have [_ [Hoffc Ev3]] : is_relevant_comp Left comp' /\ get_offset Left comp' = Some offc /\ v3 = (x1 + as_word offc)%w.
    { case: Hoffrel => [Hleft|[Hrr _]]; first exact Hleft.
      exfalso. apply: (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)).
      - by inversion Hmergeable_ifaces as [[_ fdisj] _].
      - exact: Hrr.
      - exact: ip_comp'. }
    have [cell3 [Hcell3 [Hccol3 Hcode3c]]] :
        exists cell3, mem s3 v3 = Some cell3 /\ color (taga cell3) = comp' /\ is_code (taga cell3).
    { move: PTS3; rewrite /points_to_comp_code; case: (mem s3 v3) => [c3|] //= [? ?]; by exists c3. }
    have Hbel3 : belong comp (Some (taga cell3)) = false.
    { move: Hbel2 Hccol2 Hccol3; rewrite /belong.
      case: (taga cell2) => ? c2 ? ?; case: (taga cell3) => ? c3 ? ? /= Hb E2 E3. by rewrite E3 -E2. }
    have Hr2ne1 : r2 <> as_word (ssrint.Posz 1).
    { move=> E. rewrite E Hrcom2 in Hr2. discriminate Hr2. }
    have [rac3 Hra3] : exists rac3, regs s3 (as_word (ssrint.Posz 4)) = Some rac3.
    { case E: (regs s3 (as_word (ssrint.Posz 4))) => [x|]; first by exists x.
      exfalso. exact: (rd_r4 reg_domm3 E). }
    destruct s3 as [mem3 regs3 [pc3v pc3t] int3].
    have Epc3t : pc3t = Level n2.+1 comp by exact: tag_pc3.
    subst pc3t.
    rewrite /= in Hpc3v Hpc3cell Hr3 Hr13 Hra3 Hcell3.
    rewrite -Hpc3v in Hpc3cell.
    have [rs3 [Hdu3 [Htc3 Hstep3]]] :=
      jump_ret_step3 int3 Hpc3cell Hdec3 Hr3 Hra3 Hr13 reg_domm3 Hr2ne1 Hcode2 Hcol2
                     Hcell3 Hccol3 Hbel3 erefl Hz2.
    exists {| mem := mem3; regs := rs3; pc := v3 @ (Level n2 comp'); internal := int3 |}, M'.
    split.
    { apply: plus_one. exact: Hstep3. }
    rewrite EM in capa_cor1 capa_cor2 capa_cor3.
    have Hlev : forall ws v k,
        in_stack ([:: (sv', (w2 @ (Ret n2) : stack_value), (v3 @ (Ret n2) : stack_value), comp')] : stack) ws v k -> k = n2.
    { move=> ws v k; rewrite Ex1 /in_stack; case: ws => -[? [? [? [Hh|[]]]]]; by case: Hh. }
    have Hr1ne1 : r1 <> as_word (ssrint.Posz 1).
    { move=> E. rewrite E Hrcom1 in Hr1. case: Hr1 => Ea. rewrite Ea in Hdat1. discriminate Hdat1. }
    have [rs1 [Hdu1' [Hrac1 [Hcap1 Htc1]]]] :=
      return_pop_post_ws Hr1ne1 reg_domm1 Hra1 Hr1 capa_cor1 (Hlev WS_S1).
    have Est1 : st1 = {| mem := mem s1; regs := rs1; pc := pc s1; internal := internal s1 |}
      by have E := etrans (esym Hdu1) Hdu1'; case: E.
    have [rs2 [Hdu2' [Hrac2 [Hcap2 Htc2]]]] :=
      return_pop_post_ws Hr2ne1 reg_domm2 Hra2 Hr2 capa_cor2 (Hlev WS_S2).
    have Est2 : st2 = {| mem := mem s2; regs := rs2; pc := pc s2; internal := internal s2 |}
      by have E := etrans (esym Hdu2) Hdu2'; case: E.
    subst st1 st2. rewrite /= in Hs1' Hs2'. subst s1' s2'.
    have [rs3' [Hdu3' [Hrac3 [Hcap3 Htc3']]]] :=
      return_pop_post_ws Hr2ne1 reg_domm3 Hra3 Hr3 capa_cor3 (Hlev WS_S3).
    have Ers3 : rs3' = rs3 by have E := etrans (esym Hdu3') Hdu3; case: E.
    subst rs3'.
    have Ex1w : x1 = w1.
    { have [Hin1 _] := capa_cor1 w1 n2 (inl r1) Hr1.
      move: Hin1; rewrite /in_stack => -[sv1 [sv2 [col [Hhd | Htl]]]].
      - move: Hhd; rewrite Ex1 => -[Ew _ _ _]. by case: Ew.
      - exfalso. have [k [Hb [_ [_ Hk]]]] := wf_stack_levels_lt' WF' Htl.
        move: Hb => /= [Ek]. subst k. by rewrite ltnn in Hk. }
    subst x1.
    have Hva : vala a11 = va12.
    { apply: convert_int_of_word_inj. by rewrite -Hz1 Hz2. }
    apply: match_states_left.
    - apply: (@common_equiv_def M' _ _ _ n2 comp').
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + exact: WF'.
      + exact: (reg_domm_step_mp Hs1 reg_domm1).
      + exact: (reg_domm_step Hs2 reg_domm2).
      + exact: (reg_domm_step Hstep3 reg_domm3).
      + exact: gmc1.
      + exact: gmc2.
      + exact: gmc3.
      + exact: Hcap1.
      + exact: Hcap2.
      + exact: Hcap3.
      + eapply combined_codes_mem_cong; last exact: code_left. all: reflexivity.
      + eapply combined_codes_mem_cong; last exact: code_right. all: reflexivity.
      + by rewrite ip_comp'.
      + apply: (pc_code_color_pts' (s := {| mem := mem s1; regs := rs1; pc := w1 @ (Level n2 comp'); internal := internal s1 |}));
          [ exact: PTS1 | reflexivity ].
      + apply: (pc_code_color_pts (C := comp')); last reflexivity. exact: PTS2.
    -
      rewrite EM in mem_match1.
      have [rs1b [Hdu1b [Hval1 _]]] := return_do_updates_props Hr1ne1 reg_domm1 Hra1 Hr1.
      have Ers1 : rs1b = rs1 by have E := etrans (esym Hdu1b) Hdu1'; case: E.
      subst rs1b.
      have [rs3b [Hdu3b [Hval3 _]]] := return_do_updates_props Hr2ne1 reg_domm3 Hra3 Hr3.
      have Ers3 : rs3b = rs3 by have E := etrans (esym Hdu3b) Hdu3; case: E.
      subst rs3b.
      apply: strong_equiv_def.
      + apply: (same_pc_normal (v := cell1) (off := offc)).
        * split; first exact Hcell1.
          move: PTS1; rewrite /points_to_comp_code' Hcell1 /= => -[_ [[_ Hrr]|Hic]];
            [ by move: Hrr; rewrite /side_of ip_comp' | exact Hic ].
        * exact Hoffc.
        * exact Ev3.
      + reflexivity.
      + by rewrite /side_of /= ip_comp'.
      + exact: w_mem_cor1.
      + exact: w_mem_cor3.
      + exact: entry_off1.
      + exact: Hrac1.
      + exact: Hrac3.
      + apply: (memory_match_pop mem_match1); [reflexivity | reflexivity |].
        move=> w d Hd /= E. rewrite Ex1 in E. case: E => Ev Et.
        have prem : exists t, mem s1 w = Some ((vala d) @ t) /\ vtag t = Ret n2.
        { exists (taga d). split; last exact Et. by rewrite Hd; case: d {Hd Ev Et}. }
        have [_ uni] := capa_cor1 (vala d) n2 (inr w) prem.
        exact: (uni (inl r1) w1 Hr1).
      + apply: (@registers_match_clear Left M' _ _ va12).
        * have D1 := reg_domm_step_mp Hs1 reg_domm1. have D3 := reg_domm_step Hstep3 reg_domm3.
          rewrite /register_domm in D1 D3. by rewrite D1 D3.
        * exact: Htc1.
        * exact: Htc3.
        * by rewrite /= Hval1 Hrcom1 /= Hva.
        * by rewrite /= Hval3 Hr13.
    -
      rewrite EM in mem_match.
      apply: weak_equiv_def.
      + reflexivity.
      + by rewrite /side_of /= ip_comp'.
      + exact: s_mem_cor.
      + exact: s'_mem_cor.
      + exact: entry_off.
      + apply: (memory_match_pop mem_match); [reflexivity | reflexivity |].
        move=> w d Hd /= E. case: E => Ev Et.
        have prem : exists t, mem s2 w = Some ((vala d) @ t) /\ vtag t = Ret n2.
        { exists (taga d). split; last exact Et. by rewrite Hd; case: d {Hd Ev Et}. }
        have [_ uni] := capa_cor2 (vala d) n2 (inr w) prem.
        exact: (uni (inl r2) w2 Hr2).
  Qed.

  Lemma ser_case_CC : forall M s1 s2 s3 comp z comp' s1' s2',
    step_mp (NC := NC) s1 s1' (Some (ERet comp z comp')) ->
    step_me (NC := NC) s2 s2' (Some (ERet comp z comp')) ->
    common_equiv M s1 s2 s3 -> weak_equiv Left M s1 s3 -> strong_equiv Right M s2 s3 ->
    comp' \in domm ic ->
    exists s3' M', Plus sem'' s3 [:: ERet comp z comp'] s3' /\ match_states M' s1' s2' s3'.
  Proof.
    import_context.
    move=> M s1 s2 s3 comp z comp' s1' s2' Hs1 Hs2 common weak strong ic_comp'.
    have [ip1 [r1 [w1 [n1 [rac1 [a11 [cell1 [st1 H1]]]]]]]] := return_step_inv_mp Hs1.
    have [Hpc1 [Hdec1 [Hr1 [Hra1 [Hrcom1 [Hcell1 [Hcol1 [Htpc1 [Hccol1 [Hbel1 [Hdat1 [Hz1 [Hdu1 Hs1']]]]]]]]]]]]] := H1.
    have [ip2 [r2 [w2 [n2 [rac2 [a12 [cell2 [st2 H2]]]]]]]] := return_step_inv Hs2.
    have [Hpc2 [Hdec2 [Hr2 [Hra2 [Hrcom2 [Hcell2 [Hcode2 [Hcol2 [Htpc2 [Hccol2 [Hbel2 [Hoth2 [Hz2 [Hdu2 Hs2']]]]]]]]]]]]]] := H2.
    inversion strong as [? ? ? pc_s2_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off
                         s_reg_cor s'_reg_cor mem_match reg_match].
    inversion common as [? ? ? ? n c tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          gmc1 gmc2 gmc3 capa_cor1 capa_cor2 capa_cor3 code_left code_right Hcval wpcc1 wpcc2].
    inversion weak as [? ? ? color_eq1 side_eq1 w_mem_cor1 w_mem_cor3 entry_off1 mem_match1].
    clear H1 H2.
    have [En Ec] : n = n2.+1 /\ c = comp by move: tag_pc2; rewrite Htpc2 => -[-> ->].
    subst n c.
    have En1 : n1 = n2 by move: tag_pc1; rewrite Htpc1 => -[].
    subst n1.
    have Hcol_s2 : color_of s2 = comp by rewrite (color_of_pc_tag s2) Htpc2.
    inversion pc_s2_s3 as [? ? _ [Hnone _] | ? ? v0 off [Hv0 _] Hoff Hpc3v].
    { exfalso. by rewrite Hpc2 in Hnone. }
    rewrite Hcol_s2 in Hoff.
    have Hrel2 : is_relevant_comp Right comp.
    { move: side_eq; rewrite Hcol_s2 /side_of /is_relevant_comp.
      case Eip: (comp \in domm ip) => // _.
      move: Hcval; rewrite Eip /=. by []. }
    move: Hpc2 Hdec2 Hcode2 Hcol2; case: ip2 => i2 ti2 /= Hpc2 Hdec2 Hcode2 Hcol2.
    have [Xpc _] := code_right (vala (pc s2)) i2 ti2 off comp Hrel2 Hoff Hcode2 Hcol2.
    have [i3 [Hdm Hpc3cell]] := Xpc Hpc2.
    have Hdec3 : decode_instr i3 = Some (Jump r2).
    { inversion Hdm as [Hnj Hnj' Heq | Ha Ha2 | imm imm' dd dd' Hj Hj2 Hmd Hmd' Hicd Htagd Hreld].
      - rewrite -Heq. exact Hdec2.
      - exfalso. have E := etrans (esym Hdec2) Ha. discriminate E.
      - exfalso. have E := etrans (esym Hdec2) Hj. discriminate E. }
    have [d3 [Hdm3 Hr3]] := proj2 (reg_match r2 (w2 @ (Ret n2))) Hr2.
    move: d3 Hdm3 Hr3 => [v3 t3] [Et3 [sv' [cf Hin]]] Hr3. subst t3.
    move: a12 Hrcom2 Hoth2 Hz2 => [va12 ta12] Hrcom2 /= Hoth2 Hz2. subst ta12.
    have [d13 [Hdm13 Hr13]] := proj2 (reg_match (as_word (ssrint.Posz 1)) (va12 @ Other)) Hrcom2.
    move: d13 Hdm13 Hr13 => [v13 t13] [Et13 Ev13] Hr13. subst t13 v13.
    have [M' [x1 [x2 [x3 [offc [EM [WF' [Ex1 [Ex2 [Ex3 [Hoffrel [PTS1 [PTS2 PTS3]]]]]]]]]]]]] :=
      pop_frame wfst Hin (or_intror erefl).
    move: Ex2 Ex3 => [Ex2] [Ex3]. subst x2 x3.
    have Ecf : cf = comp'.
    { move: PTS2; rewrite /points_to_comp_code Hcell2 /= => -[<- _]. exact Hccol2. }
    subst cf.
    have Hnip : comp' \in domm ip = false.
    { case Eip: (comp' \in domm ip) => //. exfalso.
      apply: (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)).
      - by inversion Hmergeable_ifaces as [[_ fdisj] _].
      - exact: ic_comp'.
      - exact: Eip. }
    have [_ [Hoffc Ev3]] : is_relevant_comp Right comp' /\ get_offset Right comp' = Some offc /\ v3 = (w2 + as_word offc)%w.
    { case: Hoffrel => [[Hrl _]|Hright]; last exact Hright.
      exfalso. move: Hrl; rewrite /is_relevant_comp Hnip. by []. }
    have [cell3 [Hcell3 [Hccol3 Hcode3c]]] :
        exists cell3, mem s3 v3 = Some cell3 /\ color (taga cell3) = comp' /\ is_code (taga cell3).
    { move: PTS3; rewrite /points_to_comp_code; case: (mem s3 v3) => [c3|] //= [? ?]; by exists c3. }
    have Hbel3 : belong comp (Some (taga cell3)) = false.
    { move: Hbel2 Hccol2 Hccol3; rewrite /belong.
      case: (taga cell2) => ? c2 ? ?; case: (taga cell3) => ? c3 ? ? /= Hb E2 E3. by rewrite E3 -E2. }
    have Hr2ne1 : r2 <> as_word (ssrint.Posz 1).
    { move=> E. rewrite E Hrcom2 in Hr2. discriminate Hr2. }
    have [rac3 Hra3] : exists rac3, regs s3 (as_word (ssrint.Posz 4)) = Some rac3.
    { case E: (regs s3 (as_word (ssrint.Posz 4))) => [x|]; first by exists x.
      exfalso. exact: (rd_r4 reg_domm3 E). }
    destruct s3 as [mem3 regs3 [pc3v pc3t] int3].
    have Epc3t : pc3t = Level n2.+1 comp by exact: tag_pc3.
    subst pc3t.
    rewrite /= in Hpc3v Hpc3cell Hr3 Hr13 Hra3 Hcell3.
    rewrite -Hpc3v in Hpc3cell.
    have [rs3 [Hdu3 [Htc3 Hstep3]]] :=
      jump_ret_step3 int3 Hpc3cell Hdec3 Hr3 Hra3 Hr13 reg_domm3 Hr2ne1 Hcode2 Hcol2
                     Hcell3 Hccol3 Hbel3 erefl Hz2.
    exists {| mem := mem3; regs := rs3; pc := v3 @ (Level n2 comp'); internal := int3 |}, M'.
    split.
    { apply: plus_one. exact: Hstep3. }
    rewrite EM in capa_cor1 capa_cor2 capa_cor3.
    have Hlev : forall ws v k,
        in_stack ([:: (sv', (w2 @ (Ret n2) : stack_value), (v3 @ (Ret n2) : stack_value), comp')] : stack) ws v k -> k = n2.
    { move=> ws v k; rewrite Ex1 /in_stack; case: ws => -[? [? [? [Hh|[]]]]]; by case: Hh. }
    have Hr1ne1 : r1 <> as_word (ssrint.Posz 1).
    { move=> E. rewrite E Hrcom1 in Hr1. case: Hr1 => Ea. rewrite Ea in Hdat1. discriminate Hdat1. }
    have [rs1 [Hdu1' [Hrac1 [Hcap1 Htc1]]]] :=
      return_pop_post_ws Hr1ne1 reg_domm1 Hra1 Hr1 capa_cor1 (Hlev WS_S1).
    have Est1 : st1 = {| mem := mem s1; regs := rs1; pc := pc s1; internal := internal s1 |}
      by have E := etrans (esym Hdu1) Hdu1'; case: E.
    have [rs2 [Hdu2' [Hrac2 [Hcap2 Htc2]]]] :=
      return_pop_post_ws Hr2ne1 reg_domm2 Hra2 Hr2 capa_cor2 (Hlev WS_S2).
    have Est2 : st2 = {| mem := mem s2; regs := rs2; pc := pc s2; internal := internal s2 |}
      by have E := etrans (esym Hdu2) Hdu2'; case: E.
    subst st1 st2. rewrite /= in Hs1' Hs2'. subst s1' s2'.
    have [rs3' [Hdu3' [Hrac3 [Hcap3 Htc3']]]] :=
      return_pop_post_ws Hr2ne1 reg_domm3 Hra3 Hr3 capa_cor3 (Hlev WS_S3).
    have Ers3 : rs3' = rs3 by have E := etrans (esym Hdu3') Hdu3; case: E.
    subst rs3'.
    have Ex1w : x1 = w1.
    { have [Hin1 _] := capa_cor1 w1 n2 (inl r1) Hr1.
      move: Hin1; rewrite /in_stack => -[sv1 [sv2 [col [Hhd | Htl]]]].
      - move: Hhd; rewrite Ex1 => -[Ew _ _ _]. by case: Ew.
      - exfalso. have [k [Hb [_ [_ Hk]]]] := wf_stack_levels_lt' WF' Htl.
        move: Hb => /= [Ek]. subst k. by rewrite ltnn in Hk. }
    subst x1.
    have Hva : vala a11 = va12.
    { apply: convert_int_of_word_inj. by rewrite -Hz1 Hz2. }
    apply: match_states_right.
    - apply: (@common_equiv_def M' _ _ _ n2 comp').
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + exact: WF'.
      + exact: (reg_domm_step_mp Hs1 reg_domm1).
      + exact: (reg_domm_step Hs2 reg_domm2).
      + exact: (reg_domm_step Hstep3 reg_domm3).
      + exact: gmc1.
      + exact: gmc2.
      + exact: gmc3.
      + exact: Hcap1.
      + exact: Hcap2.
      + exact: Hcap3.
      + eapply combined_codes_mem_cong; last exact: code_left. all: reflexivity.
      + eapply combined_codes_mem_cong; last exact: code_right. all: reflexivity.
      + by rewrite ic_comp' orbT.
      + apply: (pc_code_color_pts' (s := {| mem := mem s1; regs := rs1; pc := w1 @ (Level n2 comp'); internal := internal s1 |}));
          [ exact: PTS1 | reflexivity ].
      + apply: (pc_code_color_pts (C := comp')); last reflexivity. exact: PTS2.
    -
      rewrite EM in mem_match1.
      apply: weak_equiv_def.
      + reflexivity.
      + by rewrite /side_of /= Hnip.
      + exact: w_mem_cor1.
      + exact: w_mem_cor3.
      + exact: entry_off1.
      + apply: (memory_match_pop mem_match1); [reflexivity | reflexivity |].
        move=> w d Hd /= E. rewrite Ex1 in E. case: E => Ev Et.
        have prem : exists t, mem s1 w = Some ((vala d) @ t) /\ vtag t = Ret n2.
        { exists (taga d). split; last exact Et. by rewrite Hd; case: d {Hd Ev Et}. }
        have [_ uni] := capa_cor1 (vala d) n2 (inr w) prem.
        exact: (uni (inl r1) w1 Hr1).
    -
      rewrite EM in mem_match.
      have [rs2b [Hdu2b [Hval2 _]]] := return_do_updates_props Hr2ne1 reg_domm2 Hra2 Hr2.
      have Ers2 : rs2b = rs2 by have E := etrans (esym Hdu2b) Hdu2'; case: E.
      subst rs2b.
      have [rs3b [Hdu3b [Hval3 _]]] := return_do_updates_props Hr2ne1 reg_domm3 Hra3 Hr3.
      have Ers3 : rs3b = rs3 by have E := etrans (esym Hdu3b) Hdu3; case: E.
      subst rs3b.
      apply: strong_equiv_def.
      + apply: (same_pc_normal (v := cell2) (off := offc)).
        * split; first exact Hcell2.
          move: PTS2; rewrite /points_to_comp_code Hcell2 /= => -[_ Hic]. exact Hic.
        * exact Hoffc.
        * exact Ev3.
      + reflexivity.
      + by rewrite /side_of /= Hnip.
      + exact: s_mem_cor.
      + exact: s'_mem_cor.
      + exact: entry_off.
      + exact: Hrac2.
      + exact: Hrac3.
      + apply: (memory_match_pop mem_match); [reflexivity | reflexivity |].
        move=> w d Hd /= E. case: E => Ev Et.
        have prem : exists t, mem s2 w = Some ((vala d) @ t) /\ vtag t = Ret n2.
        { exists (taga d). split; last exact Et. by rewrite Hd; case: d {Hd Ev Et}. }
        have [_ uni] := capa_cor2 (vala d) n2 (inr w) prem.
        exact: (uni (inl r2) w2 Hr2).
      + apply: (@registers_match_clear Right M' _ _ va12).
        * have D2 := reg_domm_step Hs2 reg_domm2. have D3 := reg_domm_step Hstep3 reg_domm3.
          rewrite /register_domm in D2 D3. by rewrite D2 D3.
        * exact: Htc2.
        * exact: Htc3.
        * by rewrite /= Hval2 Hrcom2.
        * by rewrite /= Hval3 Hr13.
  Qed.

  Lemma step_event_return:
  forall s1 comp z comp' s1', Step sem s1 ((ERet comp z comp') :: nil) s1' ->
  forall s2 s2',   Step sem' s2 ((ERet comp z comp') :: nil) s2' ->
  forall s3 M, match_states M s1 s2 s3    ->
  exists s3' M', Plus sem'' s3 ((ERet comp z comp') :: nil) s3' /\
              match_states M' s1' s2' s3'.
  Proof.
    import_context.
    intros s1 comp z comp' s1' step_s1 s2 s2' step_s2 s3 M match_st.
    have Hs2 : step_me (NC := NC) s2 s2' (Some (ERet comp z comp')) := step_s2.
    have [ip2 [r2 [w2 [n2 [rac2 [a12 [cell [st2 Hinv]]]]]]]] := return_step_inv Hs2.
    have [_ [_ [_ [_ [_ [Hcell [_ [_ [_ [Hccol _]]]]]]]]]] := Hinv.
    have Hside : (comp' \in domm ip) \/ (comp' \in domm ic).
    { have Hcm : color_in_memory (mem s2)
        by case: match_st => ? ? ? ? common ? ?; exact: common_col_mem2 common.
      case: (Hcm _ _ Hcell); rewrite Hccol => /Extra.In_in H; [left | right]; exact H. }
    destruct match_st as [M ? ? ? common strong weak | M ? ? ? common weak strong].
    - simpl in step_s1. remember [:: ERet comp z comp'] as t.
      destruct step_s1 as [s1 ? s1' step_2 allowed | s1 ? s1' step_1 step_2]; subst t.
      + exfalso.
        inversion strong as [m ? ? pc_s1_s3 color_eq side_eq s_mem_cor s'_mem_cor _ s_reg_cor s'_reg_cor mem_match reg_match].
        subst m s s'.
        eapply Machine.Intermediate.fdisjoint_partition_notinboth.
        * inversion Hmergeable_ifaces as [[_ fdisj] _]. exact fdisj.
        * exact allowed.
        * unfold side_of in *. unfold_match' side_eq.
      + case: Hside => Hside.
        * exact: (ser_case_PP step_1 Hs2 common strong weak Hside).
        * exact: (ser_case_PC step_1 Hs2 common strong weak Hside).
    - simpl in step_s1. remember [:: ERet comp z comp'] as t.
      have step_m : step2 tt s1 t s1'.
      { destruct step_s1 as [s1 ? s1' step_2 allowed | s1 ? s1' _ step_2]; exact step_2. }
      subst t.
      case: Hside => Hside.
      * exact: (ser_case_CP step_m Hs2 common weak strong Hside).
      * exact: (ser_case_CC step_m Hs2 common weak strong Hside).
  Qed.

End StepEventReturn.
