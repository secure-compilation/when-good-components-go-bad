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

(* SPEED: stop [simpl]/[simpl in *] (inside the old [deduce_equality]/[unfold_all]
   automation) from unfolding the recursive fmap assoc-search and word casts on the
   big memory/register maps — the catastrophic blow-up in this file. Local to this
   compilation unit (added after StepEventCall is built), so it cannot affect the
   already-Qed'd files; explicit fmap/word rewrite lemmas are unaffected. *)
(* [Local] so these [simpl never] settings stay inside this file: when RecInit/RecTop chain-Include
   StepEventReturn, a non-Local [Arguments getm_def : simpl never] would propagate and break their
   [simpl]-through-getm proofs (e.g. In_fmap_getm). *)
Local Arguments getm_def : simpl never.
Local Arguments getm : simpl never.
Local Arguments setm : simpl never.
Local Arguments as_word : simpl never.
Local Arguments swcast : simpl never.
Local Arguments addw : simpl never.

Module StepEventReturn (S: RecompositionContext).

  (* Chain off StepEventCall so the whole recomposition shares ONE Defs instance. *)
  Include StepEventCall S.

  (* PERF: keep [pc_code_color] folded so the giant-state pcc goals don't normalise in Qed. *)
  Local Opaque pc_code_color.

  (* The post-RETURN pc lands on the popped frame's saved return address, whose cell the wf_stack
     head's [points_to_comp_code(')] guarantees is running ([C = comp']) coloured.  So pc_code_color
     holds of the post-return state.  [pts'] handles the [points_to_comp_code'] (m1) slot, [pts] the
     plain [points_to_comp_code] (m2/m3) slots; both expose [color (taga cell) = C] as 1st conjunct. *)
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

  (* SPEED: fast replacement for the combined_codes branch of [deduce_equality] when
     applied to a code/instruction lookup. The shared [deduce_equality] does [simpl in
     impl] on [impl], whose type embeds the *whole* post-return state (mem s2, mem s3,
     decode_match) — catastrophic here. We derive s3's instruction via [code_left]
     directly and align the conclusion with [rewrite <- pc_s1_s3], no [simpl]. Produces
     the same [v]/[vt_match]/[vt_eq] hypotheses as [deduce_equality] (same fresh names). *)
  Ltac deduce_code_fast s_eq :=
    let v := fresh "v" in
    let vt_match := fresh "vt_match" in
    let vt_eq := fresh "vt_eq" in
    let comp_in := fresh "comp_in" in
    let t_color := fresh "t_color" in
    let t_code  := fresh "t_code" in
    let impl  := fresh "impl" in
    match (type of s_eq) with
    | (?m ?w) = Some ?ov@?ot =>
        match goal with
        | eq_off: (_ _ = Some ?off), pc_s1_s3: _ = (addw _ (as_word ?off)),
                code_left: combined_codes _ _ _, code: is_true ?isc |- _  =>
            match goal with
            | H : true = (@in_mem ?T ?comp ?s) |- _ =>
                assert (comp_in: @in_mem T comp s) by (rewrite <- H; done);
                assert (t_color: LRC.color ot = comp) by (subst; auto);
                assert (t_code : LRC.is_code ot) by (subst; done);
                destruct (code_left w ov ot off comp comp_in eq_off t_code t_color) as [impl _];
                rewrite <- pc_s1_s3 in impl;
                pose proof (impl s_eq) as [v [vt_match vt_eq]]; clear impl
            end
        end
    end.

  (* SPEED: stack-level fact, proved once in a CLEAN context (vs the old per-bullet
     [induction WF_ST] inside the huge return context, which was the >16min blow-up).
     Every entry of a [wf_stack ... cn] has [Ret]-level < cn. Copied from StepEventCall. *)
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

  (* The return's [next_state] updates are all [RegRead] (the [ra]/[r0] reads + [reg_clear_read],
     which is [[seq RegRead (as_word n) | n <- reg_list]]).  [RegRead]/[RegWrite] only touch
     [regs] (re-tag), leaving [mem]/[pc]/[internal] untouched.  So the abstract merged post-state
     [s3'] obtained from [destruct G'] still satisfies [mem s3' = mem3], [pc s3' = pc s3],
     [internal s3' = tt] — exactly what the mem-only obligations (combined_codes, gmc) need. *)
  Lemma ndsu_regread_proj :
    forall (tks : seq tag_kind) (st st' : state)
           (tags : hseq (tag_type lrc_tags) tks) (updts : seq update),
      (forall u, List.In u updts -> exists r, u = RegRead r) ->
      next_state_do_updates st tags updts = Some st' ->
      mem st' = mem st.
  Proof.
    have step1 : forall (k : tag_kind) (tg : tag_type lrc_tags k) (r : reg mt)
                        (s s' : state),
        next_state_do_update s tg (RegRead r) = Some s' ->
        mem s' = mem s.
    { move=> k tg r s s'. rewrite /next_state_do_update.
      case: k tg => [tg|tg|tg] /=; [|by []|by []].
      case E: (regs s r) => [a|] //=.
      case E2: (updm (regs s) r (vala a)@tg) => [rr|] //=.
      by move=> [= <-]. }
    elim => [|tk tks' IH] st st' tags updts Hall Hsome.
    - by move: Hsome => /= [= <-].
    - move: Hsome => /=. case: updts Hall => [|u updts'] Hall //=.
      case Es: (next_state_do_update st (hshead tags) u) => [st''|] //= Hrec.
      have [r Hu] : exists r, u = RegRead r by apply: Hall; left.
      subst u.
      have Hm := step1 _ _ _ _ _ Es.
      have Hall' : forall u, List.In u updts' -> exists r, u = RegRead r
        by move=> u' Hu'; apply: Hall; right.
      have Hm2 := IH _ _ (hsbehead tags) updts' Hall' Hrec.
      by rewrite Hm2 Hm.
  Qed.

  (* Companion of [ndsu_regread_proj] for the REGISTER values: a RegRead-only [do_updates] re-tags
     each register but PRESERVES its [vala] (RegRead reads [regs st r] then writes [(vala a)@tg]).
     This is the value half that registers_match needs (vala coincides on both cleared chains). *)
  Lemma ndsu_regread_vala :
    forall (tks : seq tag_kind) (st st' : state)
           (tags : hseq (tag_type lrc_tags) tks) (updts : seq update),
      (forall u, List.In u updts -> exists r, u = RegRead r) ->
      next_state_do_updates st tags updts = Some st' ->
      forall w, omap Types.vala (regs st' w) = omap Types.vala (regs st w).
  Proof.
    have step1 : forall (k : tag_kind) (tg : tag_type lrc_tags k) (r : reg mt)
                        (s s' : state),
        next_state_do_update s tg (RegRead r) = Some s' ->
        forall w, omap Types.vala (regs s' w) = omap Types.vala (regs s w).
    { move=> k tg r s s'. rewrite /next_state_do_update.
      case: k tg => [tg|tg|tg] /=; [|by []|by []].
      case E: (regs s r) => [a|] //=.
      case E2: (updm (regs s) r (vala a)@tg) => [rr|] //=.
      move=> [= <-] w /=. rewrite (updm_set E2) setmE.
      case: eqP => [-> | _]; [by rewrite E | by []]. }
    elim => [|tk tks' IH] st st' tags updts Hall Hsome w.
    - by move: Hsome => /= [= <-].
    - move: Hsome => /=. case: updts Hall => [|u updts'] Hall //=.
      case Es: (next_state_do_update st (hshead tags) u) => [st''|] //= Hrec.
      have [r Hu] : exists r, u = RegRead r by apply: Hall; left.
      subst u.
      have Hm := step1 _ _ _ _ _ Es w.
      have Hall' : forall u, List.In u updts' -> exists r, u = RegRead r
        by move=> u' Hu'; apply: Hall; right.
      have Hm2 := IH _ _ (hsbehead tags) updts' Hall' Hrec w.
      by rewrite Hm2 Hm.
  Qed.

  (* Policy-AGNOSTIC mem projection of the full [next_state_updates_and_pc] (the wrapper that the
     return's [G'] uses): [next_state st iv k = do! i<-evi st; do! ov<-transfer iv i; k ov], and the
     [k] here sets [mem := mem (next_state_do_updates …)].  Case-analysing the binds (no transfer
     reduction) + [ndsu_regread_proj] gives [mem s' = mem st].  Makes the abstract merged [s3']
     usable for the mem-only obligations (combined_codes, gmc). *)
  Lemma nsuap_mem_proj :
    forall (st : state) (kiv : k_ivec lrc_tags) (updts : seq update) (pc' : mword mt)
           (s' : state) (ev : option event),
      (forall u, List.In u updts -> exists r, u = RegRead r) ->
      @next_state_updates_and_pc mt ops lrc_tags transfer unit st kiv updts pc' = Some (s', ev) ->
      mem s' = mem st.
  Proof.
    move=> st kiv updts pc' s' ev Hall.
    rewrite /next_state_updates_and_pc /next_state.
    case: (evi st) => [i|] //=.
    case: (transfer _ i) => [ovev|] //=.
    case: (op _) ovev => [op0|] ovev //=.
    case: ovev => ov ev0.
    case Edu: (next_state_do_updates st (tr ov) updts) => [st'|] //=.
    move=> [= <- _] /=.
    exact: (ndsu_regread_proj Hall Edu).
  Qed.

  (* The merged post-state's pc VALUE is exactly the [pc'] passed to [next_state_updates_and_pc]
     (the wrapper sets [pc := pc'@(trpc ov)]).  Policy-agnostic — needed for the strong same_pc. *)
  Lemma nsuap_pc_proj :
    forall (st : state) (kiv : k_ivec lrc_tags) (updts : seq update) (pc' : mword mt)
           (s' : state) (ev : option event),
      @next_state_updates_and_pc mt ops lrc_tags transfer unit st kiv updts pc' = Some (s', ev) ->
      Types.vala (pc s') = pc'.
  Proof.
    move=> st kiv updts pc' s' ev.
    rewrite /next_state_updates_and_pc /next_state.
    case: (evi st) => [i|] //=.
    case: (transfer _ i) => [ovev|] //=.
    case: (op _) ovev => [op0|] ovev //=.
    case: ovev => ov ev0.
    case: (next_state_do_updates st (tr ov) updts) => [st'|] //=.
    by move=> [= <- _].
  Qed.

  (* The return's update list (the [ra]/[r0] reads + [reg_clear_read]) is all [RegRead] — the
     side condition needed to apply [nsuap_mem_proj]/[ndsu_regread_proj] to the merged step [G']. *)
  Lemma return_updts_regread :
    forall (ra' r0' : reg mt) u,
      List.In u ([:: @RegRead mt ra', @RegRead mt r0' & @reg_clear_read mt]) ->
      exists r, u = RegRead r.
  Proof.
    move=> ra' r0' u /= H.
    repeat (case: H => [<- | H]; first by eexists).
    by case: H.
  Qed.

  (* Register VALUE projection of the full [next_state_updates_and_pc] (verbatim mirror of
     [nsuap_mem_proj], using [ndsu_regread_vala]): a RegRead-only merged step re-tags every
     register but PRESERVES its [vala].  This is the value half [registers_match] needs at reg 1
     (the com register's value coincides on the s1' and s3' cleared chains). *)
  Lemma nsuap_regread_vala :
    forall (st : state) (kiv : k_ivec lrc_tags) (updts : seq update) (pc' : mword mt)
           (s' : state) (ev : option event),
      (forall u, List.In u updts -> exists r, u = RegRead r) ->
      @next_state_updates_and_pc mt ops lrc_tags transfer unit st kiv updts pc' = Some (s', ev) ->
      forall w, omap Types.vala (regs s' w) = omap Types.vala (regs st w).
  Proof.
    move=> st kiv updts pc' s' ev Hall.
    rewrite /next_state_updates_and_pc /next_state.
    case: (evi st) => [i|] //=.
    case: (transfer _ i) => [ovev|] //=.
    case: (op _) ovev => [op0|] ovev //=.
    case: ovev => ov ev0.
    case Edu: (next_state_do_updates st (tr ov) updts) => [st'|] //=.
    move=> [= <- _] /=.
    exact: (ndsu_regread_vala Hall Edu).
  Qed.

  (* [data_match] closer for the cleared-register chains: two atoms with equal tags agree under
     [data_match i] whenever the (only non-trivial) [Other] case has equal values — which is all
     a return needs, since every register is re-tagged [Invalidated] except reg 1 ([Other]). *)
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

  (* [registers_match] for a return's two cleared register chains, stated abstractly: given equal
     domains, a per-register tag classification of each side (reg 1 -> Other, else Invalidated) and
     the coinciding reg-1 value, the chains are register-matched.  Discharges the substantive
     [registers_match] obligation from the [s3'] exports + the concrete [s1'] chain, without
     re-deriving the (expensive) merged post-state. *)
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

  (* SPEED INFRASTRUCTURE (mirrors StepEventCall's killcond/rrstep): resolve [as_word i == as_word j]
     by the precomputed [reg_index_neq] (no per-rewrite side-condition discharge), and peel one
     register read of [next_state_do_updates] in a clean context. *)
  Local Ltac killcond_r :=
    repeat (match goal with |- context[as_word (ssrint.Posz ?a) == as_word (ssrint.Posz ?b)] =>
      rewrite (introF eqP (@reg_index_neq a b ltac:(move=> ?; discriminate)
                            ltac:(by []) ltac:(by []))) end).
  Local Ltac rrstep_r Hr := rewrite ?setmE; killcond_r; rewrite Hr /=.

  (* The reg-clear suffix [reg_clear_read] characterised ONCE in a CLEAN context (opaque [st]): it
     reads only the concrete [as_word]-keys of [reg_list] off [st], so there is NO [r0] aliasing
     (the whole reason the inline [assert G'] cascade was ~200s).  Re-tags reg 1 -> [top], the
     [reg_list] tail -> [Invalidated], preserves everything else (in particular reg 4 ∉ reg_list). *)
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

  (* The FULL return register clear ([RegRead 4 :: RegRead r0 :: reg_clear_read] with tags
     [Inv :: Inv :: Other :: reg_invalidate]) characterised in a CLEAN context: a single [r0]-case
     for the [RegRead r0] prefix (the only abstract read), then the [r0]-free [reg_clear_read_props].
     This REPLACES the ~200s in-place [assert G'] cascade (which branched on [r0]'s position ~13×,
     running the closers in the huge match_states context).  Gives: the do_updates succeeds with
     [mem]/[pc]/[internal] preserved; reg 1 keeps its value (com register); EVERY register is
     [Invalidated] except reg 1 ([Other]). *)
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
    (* reduce the [RegRead 4 :: RegRead r0] prefix to a state [st2]; one [r0]-case. *)
    Local Transparent next_state_do_update.
    (* The prefix [RegRead 4 :: RegRead r0] reduced to a state [st3]; the only [r0]-aliasing is
       isolated to this small [have] (a single [case Er4]), and reg 1 is untouched ([Hr0], 1<>4). *)
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
      (* [regs st3] = [setm (setm (regs st) (as_word 4) cell4@Inv) r0 rv@Inv] *)
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
    (* reg 1 value preserved *)
    split.
    { rewrite Hrs1 H13. by case: (regs st (as_word (ssrint.Posz 1))). }
    (* tag class: reg 1 -> Other, every other key -> Invalidated; fall-through by [register_domm]. *)
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
        * (* w not a key: rs w = regs st3 w = regs st w = None by register_domm — contradiction. *)
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

  Lemma return_pop_post :
    forall (st : state) (r0 : reg mt) cell4 v3 v3' n a1 a2 C M',
      r0 <> as_word (ssrint.Posz 1) ->
      register_domm (regs st) ->
      regs st (as_word (ssrint.Posz 4)) = Some cell4 ->
      regs st r0 = Some (Types.Atom v3' (Ret n)) ->
      capability_correctness ((a1, a2, Types.Atom v3 (Ret n), C) :: M') WS_S3 st ->
      exists rs,
        next_state_do_updates st
          ((Invalidated :: Invalidated :: Other :: reg_invalidate_hseq)%hseq
           : hseq (tag_type lrc_tags) (R :: R :: R :: nseq 10 R))
          (RegRead (as_word (ssrint.Posz 4)) :: RegRead r0 :: reg_clear_read)
        = Some {| mem := mem st; regs := rs; pc := pc st; internal := internal st |}
        /\ (forall pcn, register_address_correctness Left
                          {| mem := mem st; regs := rs; pc := pcn; internal := internal st |})
        /\ (forall pcn, capability_correctness M' WS_S3
                          {| mem := mem st; regs := rs; pc := pcn; internal := internal st |})
        /\ (forall w d, rs w = Some d ->
              (w = as_word (ssrint.Posz 1) /\ Types.taga d = Other) \/
              (w <> as_word (ssrint.Posz 1) /\ Types.taga d = Invalidated)).
  Proof.
    move=> st r0 cell4 v3 v3' n a1 a2 C M' Hr0ne1 Hdomm Hr4 Hr0 Hcap.
    have [rs [Hdu [_ Htagclass]]] := return_do_updates_props Hr0ne1 Hdomm Hr4 Hr0.
    exists rs. split; first exact: Hdu.
    split.
    { move=> pcn rv rr Hrr; rewrite /address_correctness.
      case: (Htagclass rr rv Hrr) => [[_ ->] | [_ ->]]; exact: I. }
    split; last exact: Htagclass.
    move=> pcn kv kn kp kprem; destruct kp as [kr | kw].
    - case: (Htagclass kr _ kprem) => [[_ Ht] | [_ Ht]]; discriminate Ht.
    - have [kis_in kunicity] := Hcap kv kn (inr kw) kprem.
      split.
      + move: kis_in; rewrite /in_stack => -[ksv1 [ksv2 [kcol [kHhead | kis_in2]]]].
        * exfalso; inversion kHhead; subst; eapply (kunicity (inl _)); exact Hr0.
        * by exists ksv1, ksv2, kcol.
      + move=> kp' kv'; destruct kp' as [kr' | kw'].
        * move=> Hr'.
          case: (Htagclass kr' _ Hr') => [[_ Ht] | [_ Ht]]; discriminate Ht.
        * move=> Hmem'; exact: (kunicity (inr kw') kv' Hmem').
  Qed.
  (* Keep [next_state_do_update] transparent for the downstream case-1 setup, which relies on
     [simpl] reducing the do_update chain (e.g. [subst s0] at the per-case branch).  In the
     [assert (G': ...)] below the do_updates chain is left unfolded by the setup, then folded
     back to [next_state_do_updates ...] by [transitivity] (conversion) so that
     [return_do_updates_props] rewrites it in one shot. *)
  Local Transparent next_state_do_update.

  (* [combined_codes] reads only the two memories, so it transports across any states with equal
     memories.  Combined with [nsuap_mem_proj] ([mem s3' = mem3]) this discharges the codeL/codeR
     match_states obligations from the input [code_left]/[code_right]. *)
  Lemma combined_codes_mem_cong :
    forall (i : side) (s s' t t' : state),
      mem s = mem s' -> mem t = mem t' ->
      combined_codes i s t -> combined_codes i s' t'.
  Proof.
    move=> i s s' t t' Hs Ht H. rewrite /combined_codes -Hs -Ht. exact: H.
  Qed.

  (* [color_of] pattern-matches on the state's pc tag, so it bridges to [taga(pc s)] — lets the
     augmented-assert fact [taga(pc s3') = Level n2 comp'] discharge the color_of obligations. *)
  Lemma color_of_from_taga :
    forall (s : state) (n : nat) (c : Component.id),
      Types.taga (pc s) = Level n c -> color_of s = c.
  Proof. by move=> [m r [v tpc] i] n c /= ->. Qed.

  (* [memory_address_correctness]/[memory_match] read only the memories ⇒ transport across equal
     mems.  With [nsuap_mem_proj] + the unchanged input mems, these land the mem-based obligations. *)
  Lemma mem_addr_mem_cong :
    forall (i : side) (s s' : state),
      mem s = mem s' -> memory_address_correctness i s -> memory_address_correctness i s'.
  Proof. move=> i s s' H Hma. rewrite /memory_address_correctness -H. exact: Hma. Qed.

  (* Plumbing (fset/register_domm arithmetic, per the admit policy — cf. StepEventCall.reg_domm_cross):
     a single step / the merged next_state only re-tags registers it reads, so it preserves the
     register domain.  Admitted so the substantive obligations stay on track. *)
  (* GENERIC (any transfer [tf]): [next_state_updates_and_pc] only [updm]s register/memory keys
     (via [next_state_do_updates]), so it preserves the register domain. *)
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

  Lemma reg_domm_nsuap :
    forall (st : state) (kiv : k_ivec lrc_tags) (updts : seq update)
           (pc' : mword mt) (s' : state) (ev : option event),
      @next_state_updates_and_pc mt ops lrc_tags transfer unit st kiv updts pc' = Some (s', ev) ->
      register_domm (regs st) -> register_domm (regs s').
  Proof.
    move=> st kiv updts pc' s' ev H Hd.
    by rewrite /register_domm (nsuap_domm_gen H); move: Hd; rewrite /register_domm.
  Qed.

  (* The allocator syscall only [updm]s [syscall_ret], so it preserves the register domain. *)
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
    - (* syscall: [sem sc = alloc_fun] (table_sem_alloc), [run_syscall] gives [sem sc st = Some st'] *)
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

  (* Discharge [register_address_correctness Left s3'] where s3' is the CONCRETE next_state
     chain over [regs s3] (only available inside the [assert G'] branches).  The return clears
     every register to Invalidated/Other (both trivially address-correct), and the fall-through
     [regs s3 r] is discharged by the input register-correctness [s'rc] = [s'_reg_cor]
     ([register_address_correctness Left s3]) — same [regs s3]/[mem s3], so no domm/ERS plumbing. *)
  Ltac regaddr3_closer s'rc :=
    rewrite /register_address_correctness /= => ? ?; rewrite ?setmE;
    do ? (case: ifP => _; [ move=> [= <-]; by rewrite /address_correctness | ]);
    exact: (s'rc _ _).

  (* Discharge [capability_correctness M' WS_S3 s3'] inside the [assert G'] branches (s3' concrete).
     Faithful mirror of the proven s1' capability block, parameterized: [cc]=capa_cor3,
     [rd]=reg_domm3, [rw]=the s3-side Ret-register witness (vt_eq10: regs s3 r0 = _@(Ret n2)).
     Register cases are vacuous (cleared regs are Invalidated/Other, never Ret); memory case via
     [cc] + the popped-frame [unicity] exfalso.  Fresh [k]-prefixed names avoid leaf clashes. *)
  Ltac capa3_closer cc rd rw :=
    intros kv kn krw krweq; simpl in *; destruct krw as [kr | kw];
    [ exfalso; repeat rewrite setmE in krweq; repeat unfold_match' krweq;
      assert (kr_in : kr \in ra :: (map (word_of_nat) reg_list)) by
        (now rewrite -in_fset -rd mem_domm krweq);
      simpl in kr_in; setoid_rewrite (Extra.In_in) in kr_in; unfold word_of_nat in kr_in;
      repeat (destruct kr_in as [|kr_in];
              [subst; (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]);
      inversion kr_in
    | pose proof (cc kv kn (inr kw) krweq) as [kis_in kunicity]; simpl in kunicity; split;
      [ unfold in_stack in *; destruct kis_in as [ksv1 [ksv2 [kcol [kHhead|kis_in]]]]; [|eauto];
        exfalso; inversion kHhead; subst kn kv ksv1 ksv2 kcol; eapply (kunicity (inl _)); exact rw
      | intros krw2 kv2; destruct krw2 as [kr2 | kw2]; simpl;
        [ let h := fresh "krweq2" in
          intro h; exfalso; repeat rewrite setmE in h; repeat unfold_match' h;
          assert (kr_in : kr2 \in ra :: (map (word_of_nat) reg_list)) by
            (now rewrite -in_fset -rd mem_domm h);
          simpl in kr_in; setoid_rewrite (Extra.In_in) in kr_in; unfold word_of_nat in kr_in;
          repeat (destruct kr_in as [|kr_in];
                  [subst; (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]);
          inversion kr_in
        | intros [kt [kv2eq kt2eq]]; eapply (kunicity (inr _)); eauto ] ] ].

  (* s3'-only TAG classification: each cleared register is [as_word 1 -> Other] / [else -> Invalidated]
     (the SPECIFIC form [registers_match] needs to match against the concrete s1' chain — the weak
     [Inv \/ Other] form admits mixed tags).  Per matched key: peel ([move=> [= <-]]), substitute
     [tgw := key] ([convert_eq_op] on the [true = (tgw==key)] eqn left by [unfold_match']), then route
     [left] (reg 1, both [reflexivity]) / [right] (else; disequality via [reg_index_neq] for [as_word k],
     or the in-context [false = (tgw==as_word 1)] eqn for the [r0] key).  Fall-through vacuous by
     [register_domm] via the proven [capa3_closer] enumeration pattern. *)
  Ltac regtag_closer rd :=
    intros tgw tgd tgHw;
    repeat rewrite setmE in tgHw; repeat unfold_match' tgHw;
    first
      [ (move: tgHw => [= <-]; convert_eq_op;
         first
           [ (left; split; reflexivity)
           | (right; split;
              [ first
                  [ (apply: reg_index_neq; by [])
                  | (match goal with
                     | He : false = (_ == as_word (ssrint.Posz 1)) |- _ =>
                         let h := fresh "Hxe" in
                         move=> h; rewrite h eqxx in He; discriminate He
                     end) ]
              | reflexivity ]) ])
      | (assert (tgw_in : tgw \in ra :: (map (word_of_nat) reg_list)) by (now rewrite -in_fset -rd mem_domm tgHw);
         simpl in tgw_in; setoid_rewrite (Extra.In_in) in tgw_in; unfold word_of_nat in tgw_in;
         repeat (destruct tgw_in as [|tgw_in];
                 [subst; (match goal with H : false = (as_word ?a == as_word ?a) |- _ => rewrite eq_refl in H; inversion H; done end) |]);
         inversion tgw_in) ].

  Ltac regs_noret H rd :=
    exfalso; repeat rewrite setmE in H; repeat unfold_match' H;
    match type of H with _ ?r = _ =>
      (have: r \in ra :: (map (word_of_nat) reg_list) by now rewrite -in_fset -rd mem_domm H);
      simpl; move/Extra.In_in; unfold word_of_nat;
      repeat (case=> [?|];
              [subst;
               (match goal with H' : false = (as_word ?a == as_word ?a) |- _ =>
                  rewrite eq_refl in H'; inversion H'; done end) |]);
      case
    end.

  Lemma step_event_return:
  forall s1 comp z comp' s1', Step sem s1 ((ERet comp z comp') :: nil) s1' ->
  forall s2 s2',   Step sem' s2 ((ERet comp z comp') :: nil) s2' ->
  forall s3 M, match_states M s1 s2 s3    ->
  exists s3' M', Plus sem'' s3 ((ERet comp z comp') :: nil) s3' /\ (* using Plus here because we know if an event is emitted then we've done at least one step *)
              match_states M' s1' s2' s3'.
  Proof.
    import_context.
    intros s1 comp z comp' s1' step_s1 s2 s2' step_s2 s3 M match_st.

    remember (id s3) as s3'; simpl in Heqs3'; destruct s3' as [mem3 regs3 [pc3_val pc3_tag] internal3].
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
    1: rename i1 into comp; rename color0 into comp'.
    (* tidying up the hypothesis *)
    all: simpl in *.
    all: repeat
           (match goal with
              H: Some _ = getm (setm _ _ _) _ |- _ =>
                repeat (rewrite setmE in H; simpl in H)
            end).
    Ltac simpl_as_word_equal_t :=
      match goal with
      | H: context [as_word (ssrint.Posz ?x) == as_word (ssrint.Posz ?x)] |- _ =>
          rewrite eqxx in H
      | H: context [as_word (ssrint.Posz _) == as_word (ssrint.Posz _)] |- _ =>
          rewrite simpl_as_word_equal in H; [| now auto | now auto | lia]
      end.
    repeat simpl_as_word_equal_t.
    simpl in *.
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
      next_state, transfer, instr_rules, LRC.transfer, LRC.instr_rules, LRC.instr_rules_mp in *.
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
    2, 4: exfalso;
    repeat ( match goal with | p : _ * option event |- _ => destruct p end); simpl in *;
    repeat (unfold_all || unfold_match). (* eliminate cases with the wrong events *)
    all: repeat
           match goal with
             H: Some ?a = match ?cond with true => Some ?b | false => Some ?c end |- _ =>
               assert (a = if cond then b else c); [destruct cond; inversion H; try congruence| clear H]
           end.
    all: revert Heqa23.
    1: repeat (match goal with
                 | H: context [as_word (ssrint.Posz _) == r] |- _ => revert H
           end).
    2: repeat (match goal with
                 | H: context [as_word (ssrint.Posz _) == r] |- _ => revert H
               end).
    all: repeat (unfold_all || unfold_match).
    all: intros.
    all: rename Heqa23 into a21_eq.
    (* all: revert Heqa23; repeat (unfold_all || unfold_match). *)
    (* all: intro a21_eq. *)
    all: subst color; try subst color0; try subst color1; try subst i3; destruct e0, e; simpl in *; subst rcom_value0.
    all: unfold is_jump, check_ret, build_tpc in *.
    
    1: repeat (match goal with
                 | H: context [as_word (ssrint.Posz _) == r] |- _ => revert H
                 | H: context [r == as_word (ssrint.Posz _)] |- _ => revert H
           end).
    2: repeat (match goal with
                 | H: context [as_word (ssrint.Posz _) == r] |- _ => revert H
                 | H: context [r == as_word (ssrint.Posz _)] |- _ => revert H
               end).
    all: repeat unfold_match; subst t1; intros.
    (* try (revert a21_eq; repeat unfold_match; subst t1; intro a21_eq). *)
    all: convert_eq_op.
    (* all: repeat simpl_as_word_equal_t. *)
    all: unfold_match' ivec_eq; inversion ivec_eq as [tag_mem_w0].
    all: try (match goal with
                H : @eq (ovec lrc_tags _) _ _ |- _ => inversion H; clear H
              end).
    all: revert ST ST0 eq_s3; subst; intros ST ST0 eq_s3; simpl in *. (* trick to keep an equality on s1 and s3 *)
    1-2: rename i1 into comp.
    all: inversion strong as [? ? ? pc_s'_s3 color_eq side_eq s_mem_cor s'_mem_cor entry_off s_reg_cor s'_reg_cor mem_match reg_match].
    all: inversion common as [? ? ? ? ? ? tag_pc1 tag_pc2 tag_pc3 wfst reg_domm1 reg_domm2 reg_domm3
                          [mem_pref_cond_s1 [mem_pref_cond_s1' [code_pref_cond_s1 [alloc_mem_s1 [bnz_s1 [end_s1 [col_mem1 [entry_code1 cvo1]]]]]]]]
                          [mem_pref_cond_s2 [mem_pref_cond_s2' [code_pref_cond_s2 [alloc_mem_s2 [bnz_s2 [end_s2 [col_mem2 [entry_code2 cvo2]]]]]]]]
                          [mem_pref_cond_s3 [mem_pref_cond_s3' [code_pref_cond_s3 [alloc_mem_s3 [bnz_s3 [end_s3 [col_mem3 [entry_code3 cvo3]]]]]]]]
                          capa_cor1 capa_cor2 capa_cor3 code_left code_right Hcval wpcc1 wpcc2].
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
             |- context[Types.vala (match ?cond with true => ?a | false => ?b end)] =>
               assert (tmp: Types.vala (match cond with true => a | false => b end) = (match cond with true => vala a | false => vala b end));
               [ clear; destruct cond; simpl; done | rewrite tmp; clear tmp]
           end; simpl.
    
    all: ((destruct pc_s'_s3 as [? ? ? eq_none|s1 s3 ? ? _ eq_off pc_s'_s3]
          || destruct pc_s'_s3 as [? ? ? eq_none|s2 s3 ? ? _ eq_off pc_s'_s3]);
          [exfalso; subst; simpl in *; (rewrite (proj1 eq_none) in PC) || (rewrite (proj1 eq_none) in PC0); done |]).
    (* Steps needed in each cases: *)
    (* 1/ deduce beforehand the equalities on s3 needed to proceed, *)
    (* 2/ unfold to show that a step can be done from s3, *)
    (* 3/ show that match_state hold for the new states. *)
    + (* case 1 (P->P): return from comp in P to comp' in P; output match_states_left. *)
      repeat
        (match goal with
           H : Some ?a = getm reg0 _ |- _ => deduce_equality (esym H);
                                           pose proof (esym H); clear H
         end).
      deduce_equality RW0.
      deduce_equality RA0.
      subst s1. unfold side_of in *. unfold_match' side_eq. simpl in *.
      deduce_code_fast PC0.
      assert (Meq: exists top M', M = top :: M').
      { destruct vt_match10 as [ret_eq stack_prop]. unfold color_of in stack_prop.
        subst t10. simpl in stack_prop. destruct stack_prop as [top [col top_in]].
        destruct M; eauto. inversion top_in. }
      destruct Meq as [top [M' M_eq]]. destruct a41 as [xt xv].
      destruct vt_match10 as [ret_eq stack_prop]. unfold color_of in stack_prop.
      subst t10. simpl in stack_prop. destruct stack_prop as [s2val [comp'' triple_in]].
      match (type of triple_in) with (_ ?t _) => assert (top = t); [|subst top] end.
      { inv tag_pc1. simpl in *. subst.
        clear- wfst triple_in. destruct triple_in as [?| is_in]; auto. exfalso.
        inversion wfst as [ | ? ? ? ? ? ? ? ? ? ? ? ? ? WF | ? ? ? ? ? ? ? ? ? ? ? ? ? WF ]; subst;
          ( try (match goal with E : _ + 1 = _ |- _ => move: E; rewrite addn1 => [= ?]; subst end);
            have [k [Hk1 [_ [_ Hklt]]]] := wf_stack_levels_lt' WF is_in;
            move: Hk1 => /= [= ?]; subst; by rewrite ltnn in Hklt ). }
      assert (comp'' = comp'); [|subst comp''].
      { clear - wfst M_eq Heqa7 tag_mem_w0.
        inv wfst; inv H1; rewrite addn1 in H0; inv H0.
        - unfold points_to_comp_code' in PTS_CODE1; oapp_False; simpl in *.
          rewrite <- Heqa7 in HeqH; simplify_some; simpl in *; destruct PTS_CODE1; auto.
        - unfold points_to_comp_code' in PTS_CODE1; oapp_False; simpl in *.
          rewrite <- Heqa7 in HeqH; simplify_some; simpl in *; destruct PTS_CODE1; auto.
      }
      inversion wfst; subst M; try (inv H0; done); simpl in *.
      2: { exfalso. inv H13. clear - SIDE ip_comp' Hmergeable_ifaces.
           eapply (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic)); eauto.
           inversion Hmergeable_ifaces as [[_ fdisj] _]; eauto. }
      inversion H13. rewrite addn1 in H14; inversion H14.
      simpl in *.
      subst n n0 s2val v16 C st. clear H20 H14.
      unfold points_to_comp_code in PTS_CODE3. oapp_False.

      (* No r=r0 assert: the s2-side operand r (from H0) was an artifact of the half-finished
         optimization (the manual [assert G'] with [RegRead r], now removed as dead code). The s3
         JUMP operand unifies to r0 (the s1/s3 side) via [eapply step_jump; eauto] below, driven by
         vt_eq10/the decode obligation — matching the pre-optimization structure. *)
      
 (*           assert (exists s3', *)
 (*                 next_state_updates_and_pc s3 *)
 (*   (IVec JUMP pc3_tag *)
 (*      {| vtag := vtag1; color := comp; entry := entry1; is_code := true |} *)
 (*      [hseq t11; Ret n2; t9; t8; t7; t6; t5; t4; t3; t2; t1; t0; t]) *)
 (*   [:: RegRead ra, RegRead r & reg_clear_read] v11 = *)
      (* Some (s3', Some (ERet comp rcom_value1 comp')) ). *)

      assert (G: Some {| rcom_value := rcom_value1 |} = evi s3).
      { unfold evi in Heqa0.
        unfold evi in *. simpl. rewrite vt_eq9.
        simpl.
        move: Heqa0. simpl. rewrite H12. simpl.
        move: vt_match9.
        rewrite /data_match. destruct a23.
        simpl in Heqa51. destruct taga0; simpl in Heqa51; try congruence.
        intros [? ?]; subst. simpl. eauto. }


      assert (G': exists s3',
  @next_state_updates_and_pc mt ops lrc_tags transfer unit s3
    (@IVec lrc_tags JUMP pc3_tag
       {| vtag := vtag1; color := comp; entry := entry1; is_code := true |}
       [hseq t11; Ret n2; t9; t8; t7; t6; t5; t4; t3; t2; t1; t0; t])
    [:: @RegRead mt (@ra mt ops), @RegRead mt r0 & @reg_clear_read mt] v11 =
  @Some (@Symbolic.state mt lrc_tags unit * option event)
    (s3', @Some event (ERet comp rcom_value1 comp')) /\ Types.taga (pc s3') = Level n2 comp'
    /\ register_address_correctness Left s3' /\ capability_correctness M' WS_S3 s3'
    /\ (forall w d, regs s3' w = Some d ->
          (w = as_word (ssrint.Posz 1) /\ Types.taga d = Other) \/
          (w <> as_word (ssrint.Posz 1) /\ Types.taga d = Invalidated))).
      { unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        setoid_rewrite <- G. simpl.
        subst v11. simpl in *. subst v14.
        rewrite <- HeqH. simpl. rewrite eq_s3 in tag_pc3. simpl in tag_pc3.
        rewrite tag_pc3. rewrite eq_refl. simpl.
        destruct PTS_CODE3 as [col_a41 code_a41].
        destruct a41 as [va10 ta10].
        destruct ta10.
        simpl in col_a41. rewrite col_a41. simpl.
        rewrite <- Heqa10. simpl.
        destruct a23 as [? ta]. unfold is_other in *.
        unfold_match' Heqa51. simpl in *.
        subst ta.
        inversion vt_match9 as [? ?]. subst t9 v10. simpl.
        rewrite eqxx. simpl.
        unfold updm. simpl in *.


        (* --- FAST replacement of the ~13x [r0]-aliasing cascade (which ran [capa3_closer]/
           [regtag_closer] ~13x in the huge match_states context, ~200s).  The post-setup goal's
           do_updates chain is definitionally
             [next_state_do_updates s3 (Inv :: Inv :: Other :: reg_invalidate_hseq)
                                       (RegRead 4 :: RegRead r0 :: reg_clear_read)],
           i.e. exactly the LHS of [return_do_updates_props].  Apply it once, then read off the
           four exports: the tag-class third conjunct discharges register_address_correctness and
           the register part of capability_correctness by plain [discriminate]. *)
        have Hr0ne1 : r0 <> as_word (ssrint.Posz 1).
        { move=> E; move: vt_eq10; rewrite E vt_eq9; discriminate. }
        have [rs [Hdu [Hrac [Hcap Htagclass]]]] :=
          return_pop_post Hr0ne1 reg_domm3 vt_eq11 vt_eq10 capa_cor3.
        exists {| mem := mem s3; regs := rs;
                  pc := (w0 + as_word off0)%w@(build_tpc n2 comp');
                  internal := internal s3 |}.
        split.
        { transitivity (do! st' <- next_state_do_updates s3
                          ((Invalidated :: Invalidated :: Other :: reg_invalidate_hseq)%hseq
                           : hseq (tag_type lrc_tags) (R :: R :: R :: nseq 10 R))
                          (RegRead (as_word (ssrint.Posz 4)) :: RegRead r0 :: reg_clear_read);
                        Some ({| mem := mem st'; regs := regs st';
                                 pc := (w0 + as_word off0)%w@(build_tpc n2 comp');
                                 internal := internal st' |},
                              Some (ERet comp rcom_value1 comp'))).
          - reflexivity.
          - by rewrite Hdu /=. }
        split; first by reflexivity.
        split.
        { exact: Hrac. }
        split.
        { exact: Hcap. }
        exact Htagclass. }

      destruct G' as [s3' [G' [Htag3 [Hregaddr3 [Hcapa3 Htagexport]]]]].
      have Hmem3 : mem s3' = mem3.
      { by rewrite (nsuap_mem_proj (@return_updts_regread _ _) G') eq_s3. }
      eexists. exists M'. simpl.
      split.
      * eapply (plus_left _ [:: ERet comp rcom_value1 comp'] ). try eapply step_jump; eauto.
        -- rewrite eq_s3 in vt_eq12. exact vt_eq12.
        -- subst v14 v11.
           inversion vt_match12; subst; revert H13; try decode_instr_eq.
           unfold decode_instr in H14. unfold ops in H14. simpl in H14.
           rewrite <- Heqa4 in H14. simpl in H14. rewrite H1 in H14. congruence.
           unfold decode_instr in H14. unfold ops in H14. simpl in H14.
           rewrite <- Heqa4 in H14. simpl in H14. rewrite H1 in H14. congruence.
        -- rewrite eq_s3 in vt_eq10. exact vt_eq10.
        -- rewrite eq_s3 in vt_eq11. exact vt_eq11.
        -- unfold reg_clear_list, reg_list. simpl. subst. simpl.
           repeat
             (match goal with
              | H: _ ?w = _  |- context[_ ?w] => rewrite H; simpl
              end). trivial.
        -- eapply star_refl.
        -- reflexivity.
      * inversion tag_pc1. rewrite eq_s3 in tag_pc3. simpl in tag_pc3.
        
        subst pc3_tag.
        clear tag_pc1. subst. simpl in *.
        (* repeat rewrite <- H14. *)
        eapply match_states_left.
        - eapply common_equiv_def.
          -- by rewrite /build_tpc. (* taga s1 *)
          -- by rewrite /build_tpc. (* taga s2 *)
          -- exact: Htag3. (* taga s3 -- from augmented assert *)
          -- exact: WF_ST. (* wf_stack -- mem s1'=mem1, mem s2'=mem0, mem s3' already in WF_ST *)
          -- exact: (reg_domm_step step_s1 reg_domm1).
          -- exact: (reg_domm_step step_s2 reg_domm2).
          -- exact: (reg_domm_nsuap G' reg_domm3).
          -- split; [|split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]]; trivial. (* gmc s1 *)
          -- split; [|split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]]; trivial. (* gmc s2 *)
          -- split; [|split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]]; trivial. (* gmc s3 *)
          -- intros v' n rw rweq. simpl in *. destruct rw as [r' | w'].
           { regs_noret rweq reg_domm1. }
           pose proof (capa_cor1 v' n (inr w') rweq) as [is_in unicity]. simpl in unicity. split.
           { unfold in_stack in *. destruct is_in as [sv1 [sv2 [col [Hhead|is_in]]]]; [|eauto].
             exfalso. inversion Hhead; subst n v' sv1 sv2 col. eapply (unicity (inl _)). exact RW0. }
           intros rw v''. destruct rw as [r' | w'']; simpl.
           { intro rweq'. regs_noret rweq' reg_domm1. }
           intros [t' [v''eq t'eq]]. eapply (unicity (inr _)); eauto.
        -- intros v' n rw rweq. simpl in *. destruct rw as [r' | w'].
           { regs_noret rweq reg_domm2. }
           pose proof (capa_cor2 v' n (inr w') rweq) as [is_in unicity]. simpl in unicity. split.
           { unfold in_stack in *. destruct is_in as [sv1 [sv2 [col [Hhead|is_in]]]]; [|eauto].
             exfalso. inversion Hhead; subst n v' sv1 sv2 col. eapply (unicity (inl _)). exact RW. }
           intros rw v''. destruct rw as [r' | w'']; simpl.
           { intro rweq'. regs_noret rweq' reg_domm2. }
           intros [t' [v''eq t'eq]]. eapply (unicity (inr _)); eauto.
          -- exact: Hcapa3. (* capability s3' -- proven in augmented assert *)
          -- (* combined_codes Left -- proven toolkit *)
            eapply combined_codes_mem_cong; last exact: code_left. all: by rewrite ?Hmem3.
          -- (* combined_codes Right *)
            eapply combined_codes_mem_cong; last exact: code_right. all: by rewrite ?Hmem3.
          -- (* running comp (the restored caller comp') valid: the return branch already
                established its side-membership (comp' ∈ ip on the Left / ∈ ic on the Right). *)
             by apply/orP; first [ left; assumption | right; assumption ].
          -- match goal with |- pc_code_color ?st =>
               apply: (pc_code_color_pts' (s := st)); [ exact: PTS_CODE1 | by [] ] end.
          -- (* WEAK-side pcc s2': post-pc [w] is the popped frame's saved RA; capability uniqueness
                ([capa_cor2] on [RW], head frame unique by [wf_stack_levels_lt']) links [w = v15]
                ([PTS_CODE2]'s value), so [pc_code_color_pts PTS_CODE2] closes it. *)
             have Hv15w : v15 = w.
             { have [Hin _] := capa_cor2 w n2 (inl r) RW.
               move: Hin => [sv1 [sv2 [col [Hhd|Htl]]]].
               - by move: Hhd => [= _ -> _ _].
               - exfalso. have [k [_ [Hb [_ Hk]]]] := wf_stack_levels_lt' WF_ST Htl.
                 move: Hb => /= [= ?]; subst k. by rewrite ltnn in Hk. }
             apply: (pc_code_color_pts (C := comp')); last by rewrite /build_tpc.
             rewrite -Hv15w. exact: PTS_CODE2.
        - eapply strong_equiv_def.
          -- (* same_pc via nsuap_pc_proj; congr addw avoids the slow addw-conversion *)
             have Hv3 := nsuap_pc_proj G';
             eapply (same_pc_normal (off := off0));
               [ split;
                 [ rewrite /=; exact: (esym Heqa7)
                 | (* the popped frame's PTS_CODE1: code-ness, Left side refutes the (Right,Right) escape *)
                   move: PTS_CODE1; rewrite /points_to_comp_code' -Heqa7 /= => -[_ [[_ Hrr]|Hic]];
                   [ by move: Hrr; rewrite /side_of ip_comp' | exact: Hic ] ]
               | by rewrite /get_offset /color_of /=; apply: OFF_C
               | rewrite Hv3; congr addw; by rewrite /= ].
          -- by rewrite (color_of_from_taga Htag3). (* color_of via bridge *)
          -- unfold side_of; rewrite ip_comp'; trivial. (* side_of = Left *)
          -- exact: s_mem_cor. (* mem_addr s1' *)
          -- exact: s'_mem_cor. (* mem_addr s3' *)
          -- exact: entry_off. (* entry_points_offset *)
        -- unfold register_address_correctness. simpl.
           intros d r1 r_d_eq.
           unfold register_domm in *.
           assert (r_in : In r1 (domm reg0)).
           { clear - reg_domm1 r_d_eq RW0. rewrite reg_domm1.
             rewrite -Extra.In_in in_fset. simpl.
             repeat (rewrite setmE in r_d_eq; unfold_match' r_d_eq; [ convert_eq_op |]; simpl in r_d_eq).
             all: try (red; simpl; tauto).
             rewrite -in_fset -reg_domm1. setoid_rewrite <- (rwP dommP). eauto.
             rewrite -in_fset -reg_domm1. setoid_rewrite <- (rwP dommP). eauto. }
           rewrite reg_domm1 in r_in.
           move: r_in; rewrite -Extra.In_in in_fset Extra.In_in => r_in.
           repeat (destruct r_in as [? | r_in]; try subst r1;
                   repeat (rewrite setmE in r_d_eq; simpl in r_d_eq)).
           all: unfold_match' r_d_eq; simpl.
           all: move: r_d_eq; rewrite ?eqxx;
                repeat (rewrite simpl_as_word_equal; [| by [] | by [] | by [] ]);
                rewrite /=; case: ifP => _; move=> [= <-]; by rewrite /address_correctness.
          -- exact: Hregaddr3. (* register_address_correctness s3' -- proven in augmented assert *)
          -- (* memory_match strong: metadata POPPED (M' vs full input). mem s1'=mem1, mem s3'
                unchanged; non-Ret cells m-independent; Ret cells discharged by capa_cor1/capa_cor3
                unicity (the popped frame head can't be the cell). Port of the proven block. *)
            unfold memory_match. simpl.
            intros w' d d_code d_ip. split; intro w_eq.
            { destruct (fst (mem_match w' d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
              simpl in *. exists d''. split; [|exact d''eq].
              destruct d; destruct d'' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
                split; [trivial|]; split; [trivial|]; simpl in *.
              destruct H15; subst. destruct d''t; try exact H15. destruct H15 as [sv' [comp'' inM]].
              destruct inM ; [|exists sv', comp''; trivial].
              exfalso. inversion H15. subst n vala1 vala0.
              have prem : exists t, mem1 w' = Some (w0 @ t) /\ LRC.vtag t = Ret n2
                by eexists; split; [exact: d''eq | reflexivity].
              destruct (capa_cor1 w0 n2 (inr w') prem) as [is_in unicity].
              exact: (unicity (inl r0) w0 RW0). }
            { destruct (snd (mem_match w' d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
              simpl in *. exists d''. split; [|exact d''eq].
              destruct d; destruct d'' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
                split; [trivial|]; split; [trivial|]; simpl in *.
              destruct H15; subst. destruct d''t; try exact H15. destruct H15 as [sv' [comp'' inM]].
              destruct inM ; [|exists sv', comp''; trivial].
              exfalso. inversion H15. subst n vala1 vala0.
              have prem : exists t, mem s3' w' = Some ((w0 + as_word off0)%w @ t) /\ LRC.vtag t = Ret n2
                by eexists; split; [exact: d''eq | reflexivity].
              destruct (capa_cor3 (w0 + as_word off0)%w n2 (inr w') prem) as [is_in unicity].
              exact: (unicity (inl r0) (w0 + as_word off0)%w vt_eq10). }
          -- (* registers_match: re-tagged regs.  Via [registers_match_clear] from the
                s3' classification export ([Htagexport]) + the concrete s1' chain classification
                ([regtag_closer]) + the reg-1 (com register) value coincidence: its value is
                preserved by the return on both chains ([Ha44] on s1', [nsuap_regread_vala] on s3'),
                and the two pre-values agree ([Hv23] from [reg_match]'s data_match at reg 1). *)
            have Hta23 : Types.taga a23 = Other.
            { case E: (Types.taga a23) => [n|||]; rewrite E /= in Heqa51;
                first [ discriminate Heqa51 | reflexivity ]. }
            have Hr0 : r0 <> as_word (ssrint.Posz 1).
            { move=> Er0. move: RW0; rewrite Er0 H12 => [= Eqa].
              rewrite Eqa /= in Hta23. discriminate Hta23. }
            have Hv23 : Types.vala a23 = v10
              by apply: (data_match_other_val Hta23 vt_match9).
            have Ha44 : Types.vala a44 = v10.
            { have E1 : (as_word (ssrint.Posz 1) == r0) = false.
              { case: eqP => [E|] //. by case: (Hr0 (esym E)). }
              move: Heqa27. rewrite !setmE E1.
              rewrite simpl_as_word_equal; [| by [] | by [] | by [] ].
              rewrite H12 /= => [= ->]. exact: Hv23. }
            apply: (@registers_match_clear Left M' _ s3' v10);
              [ have D1 := reg_domm_step step_s1 reg_domm1;
                have D3 := reg_domm_nsuap G' reg_domm3;
                rewrite /register_domm in D1 D3; by rewrite D1 D3
              | regtag_closer reg_domm1
              | exact: Htagexport
              | rewrite !setmE;
                do 10 (rewrite simpl_as_word_equal; [| by [] | by [] | by [] ]);
                rewrite eqxx /=; by rewrite Ha44
              | by rewrite (nsuap_regread_vala (@return_updts_regread _ _) G'
                              (as_word (ssrint.Posz 1))) vt_eq9 ].
        - inversion weak as [mw sw sw' Hcw Hsw Hma2 Hma3 Heow Hmmw];
          eapply weak_equiv_def.
          -- by rewrite (color_of_from_taga Htag3). (* color_of via bridge *)
          -- unfold side_of, other_side; rewrite ip_comp'; trivial. (* side_of = other Right = Left *)
          -- exact: Hma2.
          -- exact: Hma3.
          -- exact: Heow.
          -- (* memory_match Right: popped metadata; Ret cells via capa_cor2/capa_cor3 unicity.
                Uses the already-inverted weak fields Hmmw (mem_match) / Hma2 (mem_addr s2). *)
            unfold memory_match. simpl.
            intros w' d d_code d_ip. split; intro w_eq.
            { destruct (fst (Hmmw w' d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
              simpl in *. exists d''. split; [|exact d''eq].
              destruct d; destruct d'' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
                split; [trivial|]; split; [trivial|]; simpl in *.
              destruct H18 as [_ Hm]; destruct d''t as [n| | |]; try exact Hm.
              destruct Hm as [sv' [comp'' inM]].
              destruct inM as [Hhead|]; [|exists sv', comp''; trivial].
              exfalso. inversion Hhead. subst n vala1 vala0.
              have prem : exists t, mem0 w' = Some (v15 @ t) /\ LRC.vtag t = Ret n2
                by eexists; split; [exact: d''eq | reflexivity].
              destruct (capa_cor2 v15 n2 (inr w') prem) as [is_in unicity].
              exact: (unicity (inl r) w RW). }
            { destruct (snd (Hmmw w' d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
              simpl in *. exists d''. split; [|exact d''eq].
              destruct d; destruct d'' as [? d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
                split; [trivial|]; split; [trivial|]; simpl in *.
              destruct H18 as [_ Hm]; destruct d''t as [n| | |]; try exact Hm.
              destruct Hm as [sv' [comp'' inM]].
              destruct inM as [Hhead|]; [|exists sv', comp''; trivial].
              exfalso. inversion Hhead. subst n vala1 vala0.
              have prem : exists t, mem s3' w' = Some ((w0 + as_word off0)%w @ t) /\ LRC.vtag t = Ret n2
                by eexists; split; [exact: d''eq | reflexivity].
              destruct (capa_cor3 (w0 + as_word off0)%w n2 (inr w') prem) as [is_in unicity].
              exact: (unicity (inl r0) (w0 + as_word off0)%w vt_eq10). }
    + (* case 2 (P->C): return from comp in P to comp' in C; output match_states_right. *)
      repeat
        (match goal with
           H : Some ?a = getm reg0 _ |- _ => deduce_equality (esym H);
                                           pose proof (esym H); clear H
         end).
      deduce_equality RW0.
      deduce_equality RA0.
      subst s1. unfold side_of in *. unfold_match' side_eq. simpl in *.
      deduce_code_fast PC0.
      assert (Meq: exists top M', M = top :: M').
      { destruct vt_match10 as [ret_eq stack_prop]. unfold color_of in stack_prop.
        subst t10. simpl in stack_prop. destruct stack_prop as [top [col top_in]].
        destruct M; eauto. inversion top_in. }
      destruct Meq as [top [M' M_eq]]. destruct a41 as [xt xv].
      destruct vt_match10 as [ret_eq stack_prop]. unfold color_of in stack_prop.
      subst t10. simpl in stack_prop. destruct stack_prop as [s2val [comp'' triple_in]].
      match (type of triple_in) with (_ ?t _) => assert (top = t); [|subst top] end.
      { inv tag_pc1. simpl in *. subst.
        clear- wfst triple_in. destruct triple_in as [?| is_in]; auto. exfalso.
        inversion wfst as [ | ? ? ? ? ? ? ? ? ? ? ? ? ? WF | ? ? ? ? ? ? ? ? ? ? ? ? ? WF ]; subst;
          ( try (match goal with E : _ + 1 = _ |- _ => move: E; rewrite addn1 => [= ?]; subst end);
            have [k [Hk1 [_ [_ Hklt]]]] := wf_stack_levels_lt' WF is_in;
            move: Hk1 => /= [= ?]; subst; by rewrite ltnn in Hklt ). }
      assert (comp'' = comp'); [|subst comp''].
      { clear - wfst M_eq Heqa7 tag_mem_w0.
        inv wfst; inv H1; rewrite addn1 in H0; inv H0.
        - unfold points_to_comp_code' in PTS_CODE1; oapp_False; simpl in *.
          rewrite <- Heqa7 in HeqH; simplify_some; simpl in *; destruct PTS_CODE1; auto.
        - unfold points_to_comp_code' in PTS_CODE1; oapp_False; simpl in *.
          rewrite <- Heqa7 in HeqH; simplify_some; simpl in *; destruct PTS_CODE1; auto.
      }
      (* wfst handling for ic-target return (comp' in ic): the cons_right frame survives, the
         spurious cons_left frame (whose SIDE: C in domm ip contradicts comp' in domm ic) is
         discharged via the ip/ic disjointness. *)
      inversion wfst; subst M.
      1:{ exfalso.
          have Hcc : C = comp'.
            { match goal with H : (_ :: _) = (_ :: _) |- _ => move: H => [= [= _ _ _ Hc] _] end; congruence. }
          have Hic : C \in domm ic. { rewrite Hcc. exact: ic_comp'. }
          have Hip : C \in domm ip. { exact: SIDE. }
          have HD : fdisjoint (domm ip) (domm ic).
            { inversion Hmergeable_ifaces as [[_ fdisj] _]. exact fdisj. }
          exact: (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic) HD C Hic Hip). }
      (* cons_right head equality: read off the frame components (v15 the s2-val, v16 the s3-val) *)
      match goal with H : (_ :: _) = (_ :: _) |- _ => inversion H end.
      rewrite addn1 in H14; inversion H14.
      simpl in *.
      (* keep [s3]/[s2] as variables (protect their defining equations from [subst]) *)
      revert eq_s3 ST; subst; intros eq_s3 ST.
      unfold points_to_comp_code in PTS_CODE3. oapp_False.

      (* No r=r0 assert: the s2-side operand r (from H0) was an artifact of the half-finished
         optimization (the manual [assert G'] with [RegRead r], now removed as dead code). The s3
         JUMP operand unifies to r0 (the s1/s3 side) via [eapply step_jump; eauto] below, driven by
         vt_eq10/the decode obligation — matching the pre-optimization structure. *)
      
 (*           assert (exists s3', *)
 (*                 next_state_updates_and_pc s3 *)
 (*   (IVec JUMP pc3_tag *)
 (*      {| vtag := vtag1; color := comp; entry := entry1; is_code := true |} *)
 (*      [hseq t11; Ret n; t9; t8; t7; t6; t5; t4; t3; t2; t1; t0; t]) *)
 (*   [:: RegRead ra, RegRead r & reg_clear_read] v11 = *)
      (* Some (s3', Some (ERet comp rcom_value1 comp')) ). *)

      assert (G: Some {| rcom_value := rcom_value1 |} = evi s3).
      { unfold evi in Heqa0.
        unfold evi in *. simpl. rewrite vt_eq9.
        simpl.
        move: Heqa0. simpl. rewrite H12. simpl.
        move: vt_match9.
        rewrite /data_match. destruct a23 as [va23 ta23].
        simpl in Heqa51. destruct ta23; simpl in Heqa51; try congruence.
        intros [? ?]; subst. simpl. eauto. }


      assert (G': exists s3',
  @next_state_updates_and_pc mt ops lrc_tags transfer unit s3
    (@IVec lrc_tags JUMP pc3_tag
       {| vtag := vtag1; color := (color_of s3); entry := entry1; is_code := true |}
       [hseq t11; Ret n; t9; t8; t7; t6; t5; t4; t3; t2; t1; t0; t])
    [:: @RegRead mt (@ra mt ops), @RegRead mt r0 & @reg_clear_read mt] ((v15 + as_word off0)%w) =
  @Some (@Symbolic.state mt lrc_tags unit * option event)
    (s3', @Some event (ERet (color_of s3) rcom_value1 comp')) /\ Types.taga (pc s3') = Level n comp'
    /\ register_address_correctness Left s3' /\ capability_correctness M' WS_S3 s3'
    /\ (forall w d, regs s3' w = Some d ->
          (w = as_word (ssrint.Posz 1) /\ Types.taga d = Other) \/
          (w <> as_word (ssrint.Posz 1) /\ Types.taga d = Invalidated))).
      { unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        setoid_rewrite <- G. simpl.
        simpl in *.
        rewrite <- HeqH. simpl. rewrite eq_s3 in tag_pc3. simpl in tag_pc3.
        rewrite tag_pc3. rewrite eq_refl. simpl.
        destruct PTS_CODE3 as [col_a41 code_a41].
        destruct a41 as [va10 ta10].
        destruct ta10.
        simpl in col_a41. rewrite col_a41. simpl.
        rewrite -Heqa10.
        cbn beta iota.
        have Hatg : Types.taga a23 = Other
          by move: Heqa51; rewrite /is_other; case: (Types.taga a23).
        have Ht9 : t9 = Other.
        { have Hv := proj2 (data_match_eq _ _ _ _ _) vt_match9.
          inversion Hv;
            (match goal with
             | E : a23 = _ |- _ => move: Hatg; rewrite E /=
             | E : _ = a23 |- _ => move: Hatg; rewrite -E /=
             end); move=> Hatg'; congruence. }
        (* the tpc-color check [color_of s3 == (match pc3_tag with Level _ c => c)] is true:
           the [match] is definitionally [color_of s3] (via [eq_s3]). *)
        have Hcc : (color_of s3 == match pc3_tag with | Level _ c0 => c0 end) = true.
        { by rewrite {1}/color_of eq_s3 /= eqxx. }
        rewrite Hcc /= Ht9 /=. unfold updm. simpl in *.


        (* --- FAST replacement of the ~13x [r0]-aliasing cascade (which ran [capa3_closer]/
           [regtag_closer] ~13x in the huge match_states context, ~200s).  The post-setup goal's
           do_updates chain is definitionally
             [next_state_do_updates s3 (Inv :: Inv :: Other :: reg_invalidate_hseq)
                                       (RegRead 4 :: RegRead r0 :: reg_clear_read)],
           i.e. exactly the LHS of [return_do_updates_props].  Apply it once, then read off the
           four exports: the tag-class third conjunct discharges register_address_correctness and
           the register part of capability_correctness by plain [discriminate]. *)
        have Hr0ne1 : r0 <> as_word (ssrint.Posz 1).
        { move=> E; move: vt_eq10; rewrite E vt_eq9 Ht9; discriminate. }
        have [rs [Hdu [Hrac [Hcap Htagclass]]]] :=
          return_pop_post Hr0ne1 reg_domm3 vt_eq11 vt_eq10 capa_cor3.
        exists {| mem := mem s3; regs := rs;
                  pc := (v15 + as_word off0)%w@(build_tpc n comp');
                  internal := internal s3 |}.
        split.
        { transitivity (do! st' <- next_state_do_updates s3
                          ((Invalidated :: Invalidated :: Other :: reg_invalidate_hseq)%hseq
                           : hseq (tag_type lrc_tags) (R :: R :: R :: nseq 10 R))
                          (RegRead (as_word (ssrint.Posz 4)) :: RegRead r0 :: reg_clear_read);
                        Some ({| mem := mem st'; regs := regs st';
                                 pc := (v15 + as_word off0)%w@(build_tpc n comp');
                                 internal := internal st' |},
                              Some (ERet (color_of s3) rcom_value1 comp'))).
          - reflexivity.
          - by rewrite Hdu /=. }
        split; first by reflexivity.
        split.
        { exact: Hrac. }
        split.
        { exact: Hcap. }
        exact Htagclass. }

      destruct G' as [s3' [G' [Htag3 [Hregaddr3 [Hcapa3 Htagexport]]]]].
      have Hmem3 : mem s3' = mem3.
      { by rewrite (nsuap_mem_proj (@return_updts_regread _ _) G') eq_s3. }
      eexists. exists M'. simpl.
      split.
      * eapply (plus_left _ [:: ERet (color_of s3) rcom_value1 comp'] ). try eapply step_jump; eauto.
        -- move: vt_eq12; rewrite {1 2}eq_s3 /= => Hlk; exact: Hlk.
        --
           (* the s3 instruction decodes to [Jump r0] (the s1/s3 side, via [H1]); the JAL cases
              of [decode_match] are contradictory. *)
           inversion vt_match12; subst; try decode_instr_eq;
             match goal with
             | HJ : decode_instr i0 = Some (Jal _) |- _ =>
                 move: HJ; unfold decode_instr, ops; simpl;
                 rewrite <- Heqa4; simpl; rewrite H1; congruence
             end.
        -- rewrite eq_s3 in vt_eq10. exact vt_eq10.
        -- rewrite eq_s3 in vt_eq11. exact vt_eq11.
        -- unfold reg_clear_list, reg_list. simpl. subst. simpl.
           repeat
             (match goal with
              | H: _ ?w = _  |- context[_ ?w] => rewrite H; simpl
              end). trivial.
        -- eapply star_refl.
        -- reflexivity.
      * (* n2 was already unified to n by the wfst inversion+subst; [Htag3] gives [taga (pc s3')]. *)
        (* The s2-frame return value [v15] coincides with the s2 return register value [w]:
           by [capa_cor2] applied to [RW] (reg r = w@(Ret n)), [w] is recorded as the s2-component
           of some metadata frame at level [n]; the unique such frame is the head (levels in the
           tail [M'] are strictly < n by [wf_stack_levels_lt']), whose s2-component is [v15@(Ret n)]. *)
        have RWs2 : regs s2 r = Some w@(Ret n) by rewrite ST /=; exact RW.
        have Hv15w : v15 = w.
        { have [Hin _] := capa_cor2 w n (inl r) RWs2.
          move: Hin => [sv1 [sv2 [col [Hhd | Htl]]]].
          - by move: Hhd => [= _ -> _ _].
          - exfalso. have [k [_ [Hb [_ Hk]]]] := wf_stack_levels_lt' WF_ST Htl.
            move: Hb => /= [= ?]; subst k. by rewrite ltnn in Hk. }
        eapply match_states_right.
        - eapply common_equiv_def.
          -- by rewrite /build_tpc. (* taga s1 *)
          -- by rewrite /build_tpc. (* taga s2 *)
          -- exact: Htag3. (* taga s3 -- from augmented assert *)
          -- rewrite Hmem3; rewrite eq_s3 in WF_ST; exact: WF_ST. (* wf_stack *)
          -- exact: (reg_domm_step step_s1 reg_domm1).
          -- exact: (reg_domm_step step_s2 reg_domm2).
          -- exact: (reg_domm_nsuap G' reg_domm3).
          -- split; [|split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]]; trivial. (* gmc s1 *)
          -- split; [|split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]]; trivial. (* gmc s2 *)
          -- have ->: mem s3' = mem s3 by rewrite Hmem3 eq_s3 /=. split; [|split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]]; trivial. (* gmc s3 *)
          -- intros v' nA rw rweq. simpl in *. destruct rw as [r' | w'].
           { regs_noret rweq reg_domm1. }
           pose proof (capa_cor1 v' nA (inr w') rweq) as [is_in unicity]. simpl in unicity. split.
           { unfold in_stack in *. destruct is_in as [sv1 [sv2 [col [Hhead|is_in]]]]; [|eauto].
             exfalso. inversion Hhead. subst nA v'.
             eapply (unicity (inl r0)). exact RW0. }
           intros rw v''. destruct rw as [r' | w'']; simpl.
           { intro rweq'. regs_noret rweq' reg_domm1. }
           intros [t' [v''eq t'eq]]. eapply (unicity (inr _)); eauto.
          -- intros v' nA rw rweq. simpl in *. destruct rw as [r' | w'].
           { regs_noret rweq reg_domm2. }
           pose proof (capa_cor2 v' nA (inr w') rweq) as [is_in unicity]. simpl in unicity. split.
           { unfold in_stack in *. destruct is_in as [sv1 [sv2 [col [Hhead|is_in]]]]; [|eauto].
             exfalso. inversion Hhead. subst nA.
             eapply (unicity (inl r)). rewrite ST /=. exact RW. }
           intros rw v''. destruct rw as [r' | w'']; simpl.
           { intro rweq'. regs_noret rweq' reg_domm2. }
           intros [t' [v''eq t'eq]]. eapply (unicity (inr _)); eauto.
          -- exact: Hcapa3. (* capability s3' -- proven in augmented assert *)
          -- eapply combined_codes_mem_cong; last exact: code_left. all: by rewrite ?Hmem3 ?eq_s3. (* combined_codes Left *)
          -- eapply combined_codes_mem_cong; last exact: code_right. all: by rewrite ?Hmem3 ?eq_s3. (* combined_codes Right *)
          -- (* running comp valid (restored caller, side-membership established above) *)
             by apply/orP; first [ left; assumption | right; assumption ].
          -- (* pcc s1' (weak Left): post-pc [w0] = [PTS_CODE1]'s value, so [pc_code_color_pts'] *)
             match goal with |- pc_code_color ?st =>
               apply: (pc_code_color_pts' (s := st)); [ exact: PTS_CODE1 | by [] ] end.
          -- (* pcc s2' (running Right): [Hv15w : v15 = w] (already derived) + [pc_code_color_pts PTS_CODE2] *)
             apply: (pc_code_color_pts (C := comp')); last by rewrite /build_tpc.
             rewrite -Hv15w. exact: PTS_CODE2.
        - (* weak_equiv Left s1' s3' : WEAKENING of the input [strong : strong_equiv Left s1 s3]. *)
          have Hnip : (comp' \in domm ip) = false.
            { case Hin: (comp' \in domm ip) => //. exfalso.
              inversion Hmergeable_ifaces as [[_ fdisj] _].
              exact: (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic) fdisj comp' ic_comp' Hin). }
          eapply weak_equiv_def.
          -- by rewrite (color_of_from_taga Htag3). (* color_of via bridge *)
          -- unfold side_of, other_side; rewrite Hnip; trivial. (* side_of = other Left = Right *)
          -- exact: s_mem_cor. (* mem_addr s1' (Left) -- from strong *)
          -- eapply mem_addr_mem_cong; last exact: s'_mem_cor. by rewrite Hmem3 eq_s3. (* mem_addr s3' *)
          -- have ->: mem s3' = mem s3 by rewrite Hmem3 eq_s3 /=. exact: entry_off. (* entry_off (Left) *)
          -- (* memory_match Left s1' s3': popped metadata; Ret cells via capa_cor1/capa_cor3 unicity. *)
            unfold memory_match. simpl.
            intros w' d d_code d_ip.
            have Hms3 : mem s3' = mem s3 by first [ reflexivity | rewrite Hmem3 eq_s3 // ].
            rewrite ?Hms3.
            split; intro w_eq.
            { destruct (fst (mem_match w' d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
              simpl in *. exists d''. split; [|exact d''eq].
              destruct d; destruct d'' as [dv'' d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
                split; [trivial|]; split; [trivial|]; simpl in *.
              match goal with K : _ /\ _ |- _ => destruct K as [_ Hm] end.
              destruct d''t as [nn| | |]; try exact Hm.
              destruct Hm as [sv' [comp'' inM]].
              destruct inM as [Hhead|Htail]; [|exists sv', comp''; exact Htail].
              exfalso. inversion Hhead.
              subst nn.
              move: (capa_cor1 dv'' n (inr w')
                       (ex_intro _ _ (conj d''eq (Logic.eq_refl (Ret n))))) => [is_in unicity].
              exact: (unicity (inl r0) _ RW0). }
            { destruct (snd (mem_match w' d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
              simpl in *. exists d''. split; [|exact d''eq].
              destruct d; destruct d'' as [dv'' d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
                split; [trivial|]; split; [trivial|]; simpl in *.
              match goal with K : _ /\ _ |- _ => destruct K as [_ Hm] end.
              destruct d''t as [nn| | |]; try exact Hm.
              destruct Hm as [sv' [comp'' inM]].
              destruct inM as [Hhead|Htail]; [|exists sv', comp''; exact Htail].
              exfalso. inversion Hhead.
              subst nn.
              move: (capa_cor3 dv'' n (inr w')
                       (ex_intro _ _ (conj d''eq (Logic.eq_refl (Ret n))))) => [is_in unicity].
              exact: (unicity (inl r0) _ vt_eq10). }
        - (* strong_equiv Right s2' s3' : STRENGTHENING of [weak : weak_equiv Right s2 s3]. *)
          inversion weak as [mw sw sw' Hcw Hsw Hma2 Hma3 Heow Hmmw].
          have Hnip : (comp' \in domm ip) = false.
            { case Hin: (comp' \in domm ip) => //. exfalso.
              inversion Hmergeable_ifaces as [[_ fdisj] _].
              exact: (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic) fdisj comp' ic_comp' Hin). }
          eapply strong_equiv_def.
          -- (* same_pc Right s2' s3': s2' pc = w; s3' pc = (v15 + off0) (vt_eq10/G'); v15 = w (Hv15w);
                off0 = get_offset Right comp' (OFF_C). *)
             have Hmw : exists niv, mem s2 w = Some niv.
             { case E: (mem s2 w) => [niv|]; [by exists niv | exfalso; rewrite E in Heqa2; by inversion Heqa2]. }
             destruct Hmw as [niv Hmw].
             have Hicode : is_code (taga niv)
               by move: PTS_CODE2; rewrite /points_to_comp_code Hv15w Hmw /= => -[_ Hic].
             have Hv3 := nsuap_pc_proj G'.
             eapply (same_pc_normal (off := off0));
               [ split; [rewrite /=; exact: Hmw | exact: Hicode]
               | by rewrite /color_of /get_offset /=; apply: OFF_C
               | rewrite Hv3 Hv15w; congr addw; by rewrite /= ].
          -- by rewrite (color_of_from_taga Htag3). (* color_of via bridge *)
          -- unfold side_of; rewrite Hnip; trivial. (* side_of = Right *)
          -- exact: Hma2. (* mem_addr s2' (Right) -- from weak *)
          -- eapply mem_addr_mem_cong; last exact: Hma3. by rewrite Hmem3 eq_s3. (* mem_addr s3' *)
          -- have ->: mem s3' = mem s3 by rewrite Hmem3 eq_s3 /=. exact: Heow. (* entry_off (Right) *)
          -- (* register_address_correctness Right s2': every s2' register is Other/Invalidated
                (the return clear), so address_correctness is trivially [I].  The classification
                of each register is produced by the same per-register peel as [regtag_closer]. *)
             unfold register_address_correctness. simpl.
             intros d r1 r_d_eq.
             move: d r1 r_d_eq.
             match goal with
             | |- forall d r1, @?P r1 d -> _ =>
                 have Hcl : forall r1 d, P r1 d ->
                   (r1 = as_word (ssrint.Posz 1) /\ Types.taga d = Other) \/
                   (r1 <> as_word (ssrint.Posz 1) /\ Types.taga d = Invalidated)
                   by regtag_closer reg_domm2
             end.
             move=> d r1 r_d_eq; rewrite /address_correctness.
             case: (Hcl r1 d r_d_eq) => [[_ ->]|[_ ->]]; exact: I.
          -- (* register_address_correctness Right s3': all regs Other/Invalidated (Htagexport). *)
             move=> vv rr Hr; rewrite /address_correctness.
             case: (Htagexport rr vv Hr) => [[_ ->]|[_ ->]]; exact: I.
          -- (* memory_match Right s2' s3': popped metadata; Ret cells via capa_cor2/capa_cor3 unicity. *)
            unfold memory_match. simpl.
            intros w' d d_code d_ip.
            have Hms3 : mem s3' = mem s3 by first [ reflexivity | rewrite Hmem3 eq_s3 // ].
            rewrite ?Hms3.
            split; intro w_eq.
            { destruct (fst (Hmmw w' d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
              simpl in *. exists d''. split; [|exact d''eq].
              destruct d; destruct d'' as [dv'' d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
                split; [trivial|]; split; [trivial|]; simpl in *.
              match goal with K : _ /\ _ |- _ => destruct K as [_ Hm] end.
              destruct d''t as [nn| | |]; try exact Hm.
              destruct Hm as [sv' [comp'' inM]].
              destruct inM as [Hhead|Htail]; [|exists sv', comp''; exact Htail].
              exfalso. inversion Hhead.
              subst nn.
              move: (capa_cor2 dv'' n (inr w')
                       (ex_intro _ _ (conj d''eq (Logic.eq_refl (Ret n))))) => [is_in unicity].
              exact: (unicity (inl r) _ RW). }
            { destruct (snd (Hmmw w' d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
              simpl in *. exists d''. split; [|exact d''eq].
              destruct d; destruct d'' as [dv'' d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
                split; [trivial|]; split; [trivial|]; simpl in *.
              match goal with K : _ /\ _ |- _ => destruct K as [_ Hm] end.
              destruct d''t as [nn| | |]; try exact Hm.
              destruct Hm as [sv' [comp'' inM]].
              destruct inM as [Hhead|Htail]; [|exists sv', comp''; exact Htail].
              exfalso. inversion Hhead.
              subst nn.
              move: (capa_cor3 dv'' n (inr w')
                       (ex_intro _ _ (conj d''eq (Logic.eq_refl (Ret n))))) => [is_in unicity].
              exact: (unicity (inl r0) _ vt_eq10). }
          -- (* registers_match Right s2' s3': via registers_match_clear + Htagexport
                + regtag_closer reg_domm2 + reg-1 value coincidence (vala a = v10). *)
            have Hta_a : Types.taga a = Other.
            { case E: (Types.taga a) => [m|||]; rewrite E /= in Heqa36;
                first [ discriminate Heqa36 | reflexivity ]. }
            have Hr : r <> as_word (ssrint.Posz 1).
            { move=> Er. move: RW; rewrite Er -Heqa9 => [= Eqa].
              rewrite Eqa /= in Hta_a. discriminate Hta_a. }
            (* reg-1 (com register) value coincidence [vala a = v10] (a = s2 reg-1).  The s2-side
               has no [registers_match] (weak relation), so the link goes through the SHARED event:
               [vt_match9] is the s1<->s3 [data_match] at reg 1 (Other, [Heqa51]) giving [vala a23 = v10]
               (a23 = s1 reg-1); and [evi s2 = evi s1 = {rcom_value1}] ([Heqa]/[Heqa0]) gives
               [convert (int_of_word (vala a)) = convert (int_of_word (vala a23))], whence
               [vala a = vala a23] by [convert_int_of_word_inj]. *)
            have Ha23o : Types.taga a23 = Other.
            { case E: (Types.taga a23) => [m|||]; rewrite E /= in Heqa51;
                first [ discriminate Heqa51 | reflexivity ]. }
            have Hv23 : Types.vala a23 = v10 by apply: (data_match_other_val Ha23o vt_match9).
            have Hva : Types.vala a = v10.
            { rewrite -Hv23. apply: convert_int_of_word_inj.
              move: Heqa; rewrite /evi /rcom ST /= -Heqa9 /= => [= E2].
              move: Heqa0; rewrite /evi /rcom /= H12 /= => [= E1].
              by rewrite -E2 -E1. }
            have Ha20 : Types.vala a20 = v10.
            { have E1 : (as_word (ssrint.Posz 1) == r) = false.
              { case: eqP => [E|] //. by case: (Hr (esym E)). }
              move: Heqa65. rewrite E1 ST /= -Heqa9 /= => [= ->]. exact: Hva. }
            apply: (@registers_match_clear Right M' _ s3' v10);
              [ have D2 := reg_domm_step step_s2 reg_domm2;
                have D3 := reg_domm_nsuap G' reg_domm3;
                rewrite /register_domm in D2 D3; by rewrite D2 D3
              | regtag_closer reg_domm2
              | exact: Htagexport
              | rewrite !setmE;
                do 10 (rewrite simpl_as_word_equal; [| by [] | by [] | by [] ]);
                rewrite eqxx /=; by rewrite Ha20
              | by rewrite (nsuap_regread_vala (@return_updts_regread _ _) G'
                              (as_word (ssrint.Posz 1))) vt_eq9 ].

    + (* case 3 (C->P): return from comp in C to comp' in P; output match_states_left. Mirror of case 2: RIGHT input (s2 strong, s1 weak), ip_comp' branch. *)
      repeat
      (match goal with
         H : Some ?a = getm reg _ |- _ => deduce_equality (esym H); pose proof (esym H); clear H
       end).
      deduce_equality RW.
      deduce_equality RA.
      subst s2. unfold side_of in *. unfold_match' side_eq. simpl in *.
      assert (side_eq': true = (comp \in domm ic)).
      { assert (comp_incl: comp \in (domm ic) \/ comp \in (domm ip)) by
          (rewrite ST0 in col_mem1; pose proof (col_mem1 _ _ PC0) as in_disj; simpl in in_disj;
           setoid_rewrite <- Extra.In_in in in_disj; exact ((fst (or_comm _ _)) in_disj)).
        destruct comp_incl as [Hl | Hr]. rewrite Hl. trivial. rewrite Hr in Heqa5. inversion Heqa5. }
      deduce_code_fast PC.
      assert (Meq: exists top M', M = top :: M').
      { destruct vt_match10 as [ret_eq stack_prop]. unfold color_of in stack_prop.
        subst t10. simpl in stack_prop. destruct stack_prop as [top [col top_in]].
        destruct M; eauto. inversion top_in. }
      destruct Meq as [top [M' M_eq]].
      destruct vt_match10 as [ret_eq stack_prop].
      subst t10. simpl in stack_prop. destruct stack_prop as [s2val [comp'' triple_in]].
      match (type of triple_in) with (_ ?t _) => assert (top = t); [|subst top] end.
      { inv tag_pc1. simpl in *. subst.
        clear- wfst triple_in. destruct triple_in as [?| is_in]; auto. exfalso.
        inversion wfst as [ | ? ? ? ? ? ? ? ? ? ? ? ? ? WF | ? ? ? ? ? ? ? ? ? ? ? ? ? WF ]; subst;
          ( try (match goal with E : _ + 1 = _ |- _ => move: E; rewrite addn1 => [= ?]; subst end);
            have [k [_ [Hk1 [_ Hklt]]]] := wf_stack_levels_lt' WF is_in;
            move: Hk1 => /= [= ?]; subst; by rewrite ltnn in Hklt ). }
      assert (comp'' = comp'); [|subst comp''].
      { unfold_match' Heqa2. inversion Heqa2 as [tag_mem_w].
        clear - wfst M_eq Heqa6 tag_mem_w. destruct a47. simpl in *. subst taga.
        inversion wfst; subst M; inv H0; try rename PTS_COD22 into PTS_CODE2;
        unfold points_to_comp_code in PTS_CODE2; oapp_False; simpl in *.
        all: inv H1; rewrite <- HeqH in Heqa6; simplify_some; simpl in *;
             destruct PTS_CODE2; auto. }
      (* [inversion wfst] yields the [cons_left] (C∈ip) and [cons_right] (C∈ic) frames.  For this
         C→C return (comp'∈ic, C=comp') the [cons_left] frame is spurious — discharge it via the
         ip/ic disjointness; the real [cons_right] frame (VALA_OFF: v3 = v2 + off, the s2/Right
         offset) survives.  (The old [inv H0; done] wrongly killed [cons_right].) *)
      inversion wfst; subst M.
      (* [inversion wfst] gives goal 1 = [cons_left] (C∈ip, spurious for this C→C return since
         C=comp'∈ip) and goal 2 = [cons_right] (C∈ic) is spurious for this C→P return.
         Discharge the spurious [cons_right] via ip/ic disjointness; keep [cons_left]. *)
      2:{ exfalso.
          have Hcc : C = comp'. { move: H12 => [= Hhd _]. move: Hhd => [= _ _ _ Hc]. congruence. }
          have Hip : C \in domm ip. { rewrite Hcc. exact: ip_comp'. }
          have Hic : C \in domm ic. { exact: SIDE. }
          have HD : fdisjoint (domm ip) (domm ic).
            { inversion Hmergeable_ifaces as [[_ fdisj] _]. exact fdisj. }
          exact: (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic) HD C Hic Hip). }
      simpl in *.
      inversion H12; subst v11; try subst n0; try subst st.
      unfold points_to_comp_code in PTS_CODE3. oapp_False.
      assert (G: Some {| rcom_value := rcom_value1 |} = evi s3).
      { unfold evi in Heqa.
        unfold evi in *. simpl. rewrite vt_eq9.
        simpl.
        move: Heqa. simpl. rewrite H11. simpl.
        move: vt_match9.
        rewrite /data_match. destruct a as [av atg].
        simpl in Heqa36. destruct atg; simpl in Heqa36; try congruence.
        intros [? ?]; subst. simpl. eauto. }


      assert (G': exists s3',
  @next_state_updates_and_pc mt ops lrc_tags transfer unit s3
    (@IVec lrc_tags JUMP pc3_tag
       {| vtag := vtag; color := comp; entry := entry; is_code := true |}
       [hseq t11; Ret n; t9; t8; t7; t6; t5; t4; t3; t2; t1; t0; t])
    [:: @RegRead mt (@ra mt ops), @RegRead mt r & @reg_clear_read mt] v16 =
  @Some (@Symbolic.state mt lrc_tags unit * option event)
    (s3', @Some event (ERet comp rcom_value1 comp')) /\ Types.taga (pc s3') = Level n comp'
    /\ register_address_correctness Left s3' /\ capability_correctness M' WS_S3 s3'
    /\ (forall w d, regs s3' w = Some d ->
          (w = as_word (ssrint.Posz 1) /\ Types.taga d = Other) \/
          (w <> as_word (ssrint.Posz 1) /\ Types.taga d = Invalidated))).
      { unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        setoid_rewrite <- G. simpl.
        simpl in *.
        rewrite <- HeqH. simpl. rewrite eq_s3 in tag_pc3. simpl in tag_pc3.
        rewrite tag_pc3. rewrite eq_refl. simpl.
        destruct PTS_CODE3 as [col_a41 code_a41].
        destruct a47 as [va10 ta10].
        destruct ta10.
        simpl in col_a41. rewrite col_a41. simpl.
        rewrite H20 -Heqa35.
        cbn beta iota.
        have Hatg : Types.taga a = Other
          by move: Heqa36; rewrite /is_other; case: (Types.taga a).
        have Ht9 : t9 = Other.
        { have Hv := proj2 (data_match_eq _ _ _ _ _) vt_match9.
          inversion Hv;
            (match goal with
             | E : a = _ |- _ => move: Hatg; rewrite E /=
             | E : _ = a |- _ => move: Hatg; rewrite -E /=
             end); move=> Hatg'; congruence. }
        rewrite Ht9 /= eqxx /=. unfold updm. simpl in *.


        (* --- FAST replacement of the ~13x [r0]-aliasing cascade (which ran [capa3_closer]/
           [regtag_closer] ~13x in the huge match_states context, ~200s).  The post-setup goal's
           do_updates chain is definitionally
             [next_state_do_updates s3 (Inv :: Inv :: Other :: reg_invalidate_hseq)
                                       (RegRead 4 :: RegRead r :: reg_clear_read)],
           i.e. exactly the LHS of [return_do_updates_props].  Apply it once, then read off the
           four exports: the tag-class third conjunct discharges register_address_correctness and
           the register part of capability_correctness by plain [discriminate]. *)
        have Hrne1 : r <> as_word (ssrint.Posz 1).
        { move=> E; move: vt_eq10; rewrite E vt_eq9 Ht9; discriminate. }
        have [rs [Hdu [Hrac [Hcap Htagclass]]]] :=
          return_pop_post Hrne1 reg_domm3 vt_eq11 vt_eq10 capa_cor3.
        exists {| mem := mem s3; regs := rs;
                  pc := v16@(build_tpc n comp');
                  internal := internal s3 |}.
        split.
        { transitivity (do! st' <- next_state_do_updates s3
                          ((Invalidated :: Invalidated :: Other :: reg_invalidate_hseq)%hseq
                           : hseq (tag_type lrc_tags) (R :: R :: R :: nseq 10 R))
                          (RegRead (as_word (ssrint.Posz 4)) :: RegRead r :: reg_clear_read);
                        Some ({| mem := mem st'; regs := regs st';
                                 pc := v16@(build_tpc n comp');
                                 internal := internal st' |},
                              Some (ERet comp rcom_value1 comp'))).
          - reflexivity.
          - by rewrite Hdu /=. }
        split; first by reflexivity.
        split.
        { exact: Hrac. }
        split.
        { exact: Hcap. }
        exact Htagclass. }

      destruct G' as [s3' [G' [Htag3 [Hregaddr3 [Hcapa3 Htagexport]]]]].
      have Hmem3 : mem s3' = mem3.
      { by rewrite (nsuap_mem_proj (@return_updts_regread _ _) G') eq_s3. }
      eexists. exists M'. simpl.
      split.
      * eapply (plus_left _ [:: ERet comp rcom_value1 comp'] ). try eapply step_jump; eauto.
        -- rewrite eq_s3 in vt_eq12. exact vt_eq12.
        -- inversion vt_match12; subst; revert H13; try decode_instr_eq.
           unfold decode_instr in H14. unfold ops in H14. simpl in H14.
           rewrite <- Heqa1 in H14. simpl in H14. rewrite H0 in H14. congruence.
           unfold decode_instr in H14. unfold ops in H14. simpl in H14.
           rewrite <- Heqa1 in H14. simpl in H14. rewrite H0 in H14. congruence.
        -- rewrite eq_s3 in vt_eq10. exact vt_eq10.
        -- rewrite eq_s3 in vt_eq11. exact vt_eq11.
        -- unfold reg_clear_list, reg_list. simpl. subst. simpl.
           repeat
             (match goal with
              | H: _ ?w = _  |- context[_ ?w] => rewrite H; simpl
              end). trivial.
        -- eapply star_refl.
        -- reflexivity.
      * have Hn2n : n2 = n by move: tag_pc1; rewrite ST0 /=; congruence.
        subst n2.
        rewrite eq_s3 in tag_pc3. simpl in tag_pc3. subst pc3_tag. simpl in *.
        eapply match_states_left.
        - eapply common_equiv_def.
          -- by rewrite /build_tpc. (* taga s1 *)
          -- by rewrite /build_tpc. (* taga s2 *)
          -- exact: Htag3. (* taga s3 -- from augmented assert *)
          -- rewrite Hmem3; rewrite eq_s3 in WF_ST; exact: WF_ST. (* wf_stack *)
          -- exact: (reg_domm_step_mp step_s1 reg_domm1).
          -- exact: (reg_domm_step step_s2 reg_domm2).
          -- exact: (reg_domm_nsuap G' reg_domm3).
          -- split; [|split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]]; trivial. (* gmc s1 *)
          -- split; [|split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]]; trivial. (* gmc s2 *)
          -- have ->: mem s3' = mem s3 by rewrite Hmem3 eq_s3 /=. split; [|split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]]; trivial. (* gmc s3 *)
          -- intros v' nA rw rweq. simpl in *. destruct rw as [r' | w'].
           { regs_noret rweq reg_domm1. }
           pose proof (capa_cor1 v' nA (inr w') rweq) as [is_in unicity]. simpl in unicity. split.
           { unfold in_stack in *. destruct is_in as [sv1 [sv2 [col [Hhead|is_in]]]]; [|eauto].
             exfalso. inversion Hhead.
             have Hx : v14@(Ret n) = v'@(Ret nA) by rewrite H15; exact: H17.
             move: Hx => [= _ Hnn]. subst nA.
             eapply (unicity (inl r0)). rewrite ST0 /=. exact RW0. }
           intros rw v''. destruct rw as [r' | w'']; simpl.
           { intro rweq'. regs_noret rweq' reg_domm1. }
           intros [t' [v''eq t'eq]]. eapply (unicity (inr _)); eauto.
          -- intros v' nA rw rweq. simpl in *. destruct rw as [r' | w'].
           { regs_noret rweq reg_domm2. }
           pose proof (capa_cor2 v' nA (inr w') rweq) as [is_in unicity]. simpl in unicity. split.
           { unfold in_stack in *. destruct is_in as [sv1 [sv2 [col [Hhead|is_in]]]]; [|eauto].
             exfalso. inversion Hhead. subst nA.
             eapply (unicity (inl r)). exact RW. }
           intros rw v''. destruct rw as [r' | w'']; simpl.
           { intro rweq'. regs_noret rweq' reg_domm2. }
           intros [t' [v''eq t'eq]]. eapply (unicity (inr _)); eauto.
          -- exact: Hcapa3. (* capability s3' -- proven in augmented assert *)
          -- eapply combined_codes_mem_cong; last exact: code_left. all: by rewrite ?Hmem3 ?eq_s3. (* combined_codes Left *)
          -- eapply combined_codes_mem_cong; last exact: code_right. all: by rewrite ?Hmem3 ?eq_s3. (* combined_codes Right *)
          -- (* running comp valid (restored caller, side-membership established above) *)
             by apply/orP; first [ left; assumption | right; assumption ].
          -- (* pcc s1' (running Left): post-pc [w0]; [capa_cor1] on [RW0] links [w0 = v14]
                ([PTS_CODE1]'s value), so [pc_code_color_pts' PTS_CODE1]. *)
             have RWs1 : regs s1 r0 = Some w0@(Ret n) by rewrite ST0 /=; exact RW0.
             have Hv14w0 : w0 = v14.
             { have [Hin _] := capa_cor1 w0 n (inl r0) RWs1.
               move: Hin => [sv1 [sv2 [col [Hhd|Htl]]]].
               - move: Hhd => [= Hs2v _ _ _]. congruence.
               - exfalso. have [k [Hka [_ [_ Hklt]]]] := wf_stack_levels_lt' WF_ST Htl.
                 move: Hka => /= [= ?]; subst k. by rewrite ltnn in Hklt. }
             apply: (pc_code_color_pts' (C := comp')); last by rewrite /build_tpc.
             rewrite Hv14w0 -H20. exact: PTS_CODE1.
          -- (* pcc s2' (weak Right): [H16 : v15 = w], [H20 : C = comp'] + [pc_code_color_pts PTS_CODE2] *)
             apply: (pc_code_color_pts (C := comp')); last by rewrite /build_tpc.
             rewrite -H16 -H20. exact: PTS_CODE2.
        - (* strong_equiv Left s1' s3' : STRENGTHENING of [weak : weak_equiv Left s1 s3] (the switch). *)
          inversion weak as [mw sw sw' Hcw Hsw Hma1 Hma3 Heow Hmmw].
          eapply strong_equiv_def.
          -- (* same_pc Left s1' s3': s1' pc = w0; s3' pc = v16 = v14 + off0 (VALA_OFF); v14 = w0
                (capa_cor1 on RW0); off0 = get_offset Left comp' (OFF_C). *)
             have RWs1 : regs s1 r0 = Some w0@(Ret n) by rewrite ST0 /=; exact RW0.
             have Hv14w0 : w0 = v14.
             { have [Hin _] := capa_cor1 w0 n (inl r0) RWs1.
               move: Hin => [sv1 [sv2 [col [Hhd|Htl]]]].
               - move: Hhd => [= Hs2v _ _ _]. congruence.
               - exfalso. have [k [Hka [_ [_ Hklt]]]] := wf_stack_levels_lt' WF_ST Htl.
                 move: Hka => /= [= ?]; subst k. by rewrite ltnn in Hklt. }
             have Hv3 := nsuap_pc_proj G'.
             eapply (same_pc_normal (off := off0));
               [ split;
                 [ rewrite /=; exact: (esym Heqa3)
                 | move: PTS_CODE1; rewrite /points_to_comp_code' -Hv14w0 -Heqa3 /= => -[_ [[_ Hrr]|Hic]];
                   [ by move: Hrr; rewrite H20 /side_of ip_comp' | exact: Hic ] ]
               | rewrite /get_offset /color_of /= -H20; exact: OFF_C
               | rewrite Hv3 VALA_OFF -Hv14w0; congr addw; by rewrite /= ].
          -- by rewrite (color_of_from_taga Htag3). (* color_of via bridge *)
          -- unfold side_of; rewrite ip_comp'; trivial. (* side_of = Left *)
          -- exact: Hma1. (* mem_addr s1' (Left) -- from weak *)
          -- eapply mem_addr_mem_cong; last exact: Hma3. by rewrite Hmem3 eq_s3. (* mem_addr s3' *)
          -- have ->: mem s3' = mem s3 by rewrite Hmem3 eq_s3 /=. exact: Heow. (* entry_off (Left) *)
          -- (* register_address_correctness Left s1': every s1' register is Other/Invalidated. *)
             unfold register_address_correctness. simpl.
             intros d r1 r_d_eq. move: d r1 r_d_eq.
             match goal with
             | |- forall d r1, @?P r1 d -> _ =>
                 have Hcl : forall r1 d, P r1 d ->
                   (r1 = as_word (ssrint.Posz 1) /\ Types.taga d = Other) \/
                   (r1 <> as_word (ssrint.Posz 1) /\ Types.taga d = Invalidated)
                   by regtag_closer reg_domm1
             end.
             move=> d r1 r_d_eq; rewrite /address_correctness.
             case: (Hcl r1 d r_d_eq) => [[_ ->]|[_ ->]]; exact: I.
          -- (* register_address_correctness Left s3': all regs Other/Invalidated (Htagexport). *)
             move=> vv rr Hr; rewrite /address_correctness.
             case: (Htagexport rr vv Hr) => [[_ ->]|[_ ->]]; exact: I.
          -- (* memory_match Left s1' s3': popped metadata; Ret cells via capa_cor1/capa_cor3 unicity. *)
            unfold memory_match. simpl.
            intros w' d d_code d_ip.
            have RWs1 : regs s1 r0 = Some w0@(Ret n) by rewrite ST0 /=; exact RW0.
            have Hms3 : mem s3' = mem s3 by first [ reflexivity | rewrite Hmem3 eq_s3 // ].
            rewrite ?Hms3.
            split; intro w_eq.
            { destruct (fst (Hmmw w' d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
              simpl in *. exists d''. split; [|exact d''eq].
              destruct d; destruct d'' as [dv'' d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
                split; [trivial|]; split; [trivial|]; simpl in *.
              match goal with K : _ /\ _ |- _ => destruct K as [_ Hm] end.
              destruct d''t as [nn| | |]; try exact Hm.
              destruct Hm as [sv' [comp'' inM]].
              destruct inM as [Hhead|Htail]; [|exists sv', comp''; exact Htail].
              exfalso. inversion Hhead. subst nn.
              move: (capa_cor1 dv'' n (inr w')
                       (ex_intro _ _ (conj d''eq (Logic.eq_refl (Ret n))))) => [is_in unicity].
              exact: (unicity (inl r0) _ RWs1). }
            { destruct (snd (Hmmw w' d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
              simpl in *. exists d''. split; [|exact d''eq].
              destruct d; destruct d'' as [dv'' d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
                split; [trivial|]; split; [trivial|]; simpl in *.
              match goal with K : _ /\ _ |- _ => destruct K as [_ Hm] end.
              destruct d''t as [nn| | |]; try exact Hm.
              destruct Hm as [sv' [comp'' inM]].
              destruct inM as [Hhead|Htail]; [|exists sv', comp''; exact Htail].
              exfalso. inversion Hhead. subst nn.
              move: (capa_cor3 dv'' n (inr w')
                       (ex_intro _ _ (conj d''eq (Logic.eq_refl (Ret n))))) => [is_in unicity].
              exact: (unicity (inl r) _ vt_eq10). }
          -- (* registers_match Left s1' s3': registers_match_clear + Htagexport + reg-1 value
                coincidence [vala a23 = v10] (a23 = s1 reg-1).  s1-side has no registers_match (weak),
                so via the shared event: [vt_match9] (s2<->s3, Right) gives [vala a = v10] (a = s2 reg-1),
                and [evi s1 = evi s2 = {rcom_value1}] gives [vala a23 = vala a] by convert_int_of_word_inj. *)
            have Hta_a : Types.taga a = Other.
            { case E: (Types.taga a) => [m|||]; rewrite E /= in Heqa36;
                first [ discriminate Heqa36 | reflexivity ]. }
            have Hva_s2 : Types.vala a = v10 by apply: (data_match_other_val Hta_a vt_match9).
            have Ha23r : forall m, Types.taga a23 <> Ret m.
            { move=> m E. rewrite E /= in Heqa48. discriminate Heqa48. }
            have Hva23 : Types.vala a23 = v10.
            { rewrite -Hva_s2. apply: convert_int_of_word_inj.
              move: Heqa0; rewrite /evi /rcom ST0 /= -Heqa21 /= => [= E1].
              move: Heqa; rewrite /evi /rcom /= H11 /= => [= E2].
              by rewrite -E1 -E2. }
            have Hr0 : r0 <> as_word (ssrint.Posz 1).
            { move=> Er. move: RW0; rewrite Er -Heqa21 => [= Eqa].
              rewrite Eqa /= in Ha23r. exact: (Ha23r _ erefl). }
            have Ha44 : Types.vala a44 = v10.
            { have E1 : (as_word (ssrint.Posz 1) == r0) = false.
              { case: eqP => [E|] //. by case: (Hr0 (esym E)). }
              have H14a : (as_word (ssrint.Posz 1) : Types.reg mt) <> (as_word (ssrint.Posz 4) : Types.reg mt)
                by apply: (reg_index_neq (x:=1) (y:=4)).
              move: Heqa26; rewrite setmE E1 setmE (introF eqP H14a) ST0 /= -Heqa21 /=;
                move=> [= ->]. exact: Hva23. }
            apply: (@registers_match_clear Left M' _ s3' v10);
              [ have D1 := reg_domm_step_mp step_s1 reg_domm1;
                have D3 := reg_domm_nsuap G' reg_domm3;
                rewrite /register_domm in D1 D3; by rewrite D1 D3
              | regtag_closer reg_domm1
              | exact: Htagexport
              | rewrite !setmE;
                do 10 (rewrite simpl_as_word_equal; [| by [] | by [] | by [] ]);
                rewrite eqxx /=; by rewrite Ha44
              | by rewrite (nsuap_regread_vala (@return_updts_regread _ _) G'
                              (as_word (ssrint.Posz 1))) vt_eq9 ].
        - (* weak_equiv Right s2' s3' : WEAKENING of the input [strong : strong_equiv Right s2 s3]. *)
          eapply weak_equiv_def.
          -- by rewrite (color_of_from_taga Htag3). (* color_of via bridge *)
          -- unfold side_of, other_side; rewrite ip_comp'; trivial. (* side_of = other Right = Left *)
          -- exact: s_mem_cor. (* mem_addr s2' (Right) -- from strong *)
          -- eapply mem_addr_mem_cong; last exact: s'_mem_cor. by rewrite Hmem3 eq_s3. (* mem_addr s3' *)
          -- have ->: mem s3' = mem s3 by rewrite Hmem3 eq_s3 /=. exact: entry_off. (* entry_off (Right) *)
          -- (* memory_match Right s2' s3': popped metadata; Ret cells via capa_cor2/capa_cor3 unicity. *)
            unfold memory_match. simpl.
            intros w' d d_code d_ip.
            have Hms3 : mem s3' = mem s3 by first [ reflexivity | rewrite Hmem3 eq_s3 // ].
            rewrite ?Hms3.
            split; intro w_eq.
            { destruct (fst (mem_match w' d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
              simpl in *. exists d''. split; [|exact d''eq].
              destruct d; destruct d'' as [dv'' d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
                split; [trivial|]; split; [trivial|]; simpl in *.
              match goal with K : _ /\ _ |- _ => destruct K as [_ Hm] end.
              destruct d''t as [nn| | |]; try exact Hm.
              destruct Hm as [sv' [comp'' inM]].
              destruct inM as [Hhead|Htail]; [|exists sv', comp''; exact Htail].
              exfalso. inversion Hhead. subst nn.
              move: (capa_cor2 dv'' n (inr w')
                       (ex_intro _ _ (conj d''eq (Logic.eq_refl (Ret n))))) => [is_in unicity].
              exact: (unicity (inl r) _ RW). }
            { destruct (snd (mem_match w' d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
              simpl in *. exists d''. split; [|exact d''eq].
              destruct d; destruct d'' as [dv'' d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
                split; [trivial|]; split; [trivial|]; simpl in *.
              match goal with K : _ /\ _ |- _ => destruct K as [_ Hm] end.
              destruct d''t as [nn| | |]; try exact Hm.
              destruct Hm as [sv' [comp'' inM]].
              destruct inM as [Hhead|Htail]; [|exists sv', comp''; exact Htail].
              exfalso. inversion Hhead. subst nn.
              move: (capa_cor3 dv'' n (inr w')
                       (ex_intro _ _ (conj d''eq (Logic.eq_refl (Ret n))))) => [is_in unicity].
              exact: (unicity (inl r) _ vt_eq10). }
    + (* case 4 (C->C): return from comp in C to comp' in C; output match_states_right. *)
      repeat
      (match goal with
         H : Some ?a = getm reg _ |- _ => deduce_equality (esym H); pose proof (esym H); clear H
       end).
      deduce_equality RW.
      deduce_equality RA.
      subst s2. unfold side_of in *. unfold_match' side_eq. simpl in *.
      assert (side_eq': true = (comp \in domm ic)).
      { assert (comp_incl: comp \in (domm ic) \/ comp \in (domm ip)) by
          (rewrite ST0 in col_mem1; pose proof (col_mem1 _ _ PC0) as in_disj; simpl in in_disj;
           setoid_rewrite <- Extra.In_in in in_disj; exact ((fst (or_comm _ _)) in_disj)).
        destruct comp_incl as [Hl | Hr]. rewrite Hl. trivial. rewrite Hr in Heqa5. inversion Heqa5. }
      deduce_code_fast PC.
      assert (Meq: exists top M', M = top :: M').
      { destruct vt_match10 as [ret_eq stack_prop]. unfold color_of in stack_prop.
        subst t10. simpl in stack_prop. destruct stack_prop as [top [col top_in]].
        destruct M; eauto. inversion top_in. }
      destruct Meq as [top [M' M_eq]].
      destruct vt_match10 as [ret_eq stack_prop].
      subst t10. simpl in stack_prop. destruct stack_prop as [s2val [comp'' triple_in]].
      match (type of triple_in) with (_ ?t _) => assert (top = t); [|subst top] end.
      { inv tag_pc1. simpl in *. subst.
        clear- wfst triple_in. destruct triple_in as [?| is_in]; auto. exfalso.
        inversion wfst as [ | ? ? ? ? ? ? ? ? ? ? ? ? ? WF | ? ? ? ? ? ? ? ? ? ? ? ? ? WF ]; subst;
          ( try (match goal with E : _ + 1 = _ |- _ => move: E; rewrite addn1 => [= ?]; subst end);
            have [k [_ [Hk1 [_ Hklt]]]] := wf_stack_levels_lt' WF is_in;
            move: Hk1 => /= [= ?]; subst; by rewrite ltnn in Hklt ). }
      assert (comp'' = comp'); [|subst comp''].
      { unfold_match' Heqa2. inversion Heqa2 as [tag_mem_w].
        clear - wfst M_eq Heqa6 tag_mem_w. destruct a47. simpl in *. subst taga.
        inversion wfst; subst M; inv H0; try rename PTS_COD22 into PTS_CODE2;
        unfold points_to_comp_code in PTS_CODE2; oapp_False; simpl in *.
        all: inv H1; rewrite <- HeqH in Heqa6; simplify_some; simpl in *;
             destruct PTS_CODE2; auto. }
      (* [inversion wfst] yields the [cons_left] (C∈ip) and [cons_right] (C∈ic) frames.  For this
         C→C return (comp'∈ic, C=comp') the [cons_left] frame is spurious — discharge it via the
         ip/ic disjointness; the real [cons_right] frame (VALA_OFF: v3 = v2 + off, the s2/Right
         offset) survives.  (The old [inv H0; done] wrongly killed [cons_right].) *)
      inversion wfst; subst M.
      (* [inversion wfst] gives goal 1 = [cons_left] (C∈ip, spurious for this C→C return since
         C=comp'∈ic) and goal 2 = [cons_right] (the real frame, VALA_OFF: v16 = v15 + off).
         Discharge the spurious [cons_left] via ip/ic disjointness; keep [cons_right]. *)
      1:{ exfalso.
          have Hcc : C = comp'. { move: H12 => [= Hhd _]. move: Hhd => [= _ _ _ Hc]. congruence. }
          have Hic : C \in domm ic. { rewrite Hcc. exact: ic_comp'. }
          have Hip : C \in domm ip. { exact: SIDE. }
          have HD : fdisjoint (domm ip) (domm ic).
            { inversion Hmergeable_ifaces as [[_ fdisj] _]. exact fdisj. }
          exact: (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic) HD C Hic Hip). }
      simpl in *.
      inversion H12; subst v11; try subst n0; try subst st.
      unfold points_to_comp_code in PTS_CODE3. oapp_False.
      assert (G: Some {| rcom_value := rcom_value1 |} = evi s3).
      { unfold evi in Heqa.
        unfold evi in *. simpl. rewrite vt_eq9.
        simpl.
        move: Heqa. simpl. rewrite H11. simpl.
        move: vt_match9.
        rewrite /data_match. destruct a as [av atg].
        simpl in Heqa36. destruct atg; simpl in Heqa36; try congruence.
        intros [? ?]; subst. simpl. eauto. }


      assert (G': exists s3',
  @next_state_updates_and_pc mt ops lrc_tags transfer unit s3
    (@IVec lrc_tags JUMP pc3_tag
       {| vtag := vtag; color := comp; entry := entry; is_code := true |}
       [hseq t11; Ret n; t9; t8; t7; t6; t5; t4; t3; t2; t1; t0; t])
    [:: @RegRead mt (@ra mt ops), @RegRead mt r & @reg_clear_read mt] v16 =
  @Some (@Symbolic.state mt lrc_tags unit * option event)
    (s3', @Some event (ERet comp rcom_value1 comp')) /\ Types.taga (pc s3') = Level n comp'
    /\ register_address_correctness Left s3' /\ capability_correctness M' WS_S3 s3'
    /\ (forall w d, regs s3' w = Some d ->
          (w = as_word (ssrint.Posz 1) /\ Types.taga d = Other) \/
          (w <> as_word (ssrint.Posz 1) /\ Types.taga d = Invalidated))).
      { unfold next_state_updates, next_state_updates_and_pc, next_state, transfer, instr_rules, LRC.instr_rules in *.
        setoid_rewrite <- G. simpl.
        simpl in *.
        rewrite <- HeqH. simpl. rewrite eq_s3 in tag_pc3. simpl in tag_pc3.
        rewrite tag_pc3. rewrite eq_refl. simpl.
        destruct PTS_CODE3 as [col_a41 code_a41].
        destruct a47 as [va10 ta10].
        destruct ta10.
        simpl in col_a41. rewrite col_a41. simpl.
        rewrite H20 -Heqa35.
        cbn beta iota.
        have Hatg : Types.taga a = Other
          by move: Heqa36; rewrite /is_other; case: (Types.taga a).
        have Ht9 : t9 = Other.
        { have Hv := proj2 (data_match_eq _ _ _ _ _) vt_match9.
          inversion Hv;
            (match goal with
             | E : a = _ |- _ => move: Hatg; rewrite E /=
             | E : _ = a |- _ => move: Hatg; rewrite -E /=
             end); move=> Hatg'; congruence. }
        rewrite Ht9 /= eqxx /=. unfold updm. simpl in *.


        (* --- FAST replacement of the ~13x [r0]-aliasing cascade (which ran [capa3_closer]/
           [regtag_closer] ~13x in the huge match_states context, ~200s).  The post-setup goal's
           do_updates chain is definitionally
             [next_state_do_updates s3 (Inv :: Inv :: Other :: reg_invalidate_hseq)
                                       (RegRead 4 :: RegRead r :: reg_clear_read)],
           i.e. exactly the LHS of [return_do_updates_props].  Apply it once, then read off the
           four exports: the tag-class third conjunct discharges register_address_correctness and
           the register part of capability_correctness by plain [discriminate]. *)
        have Hrne1 : r <> as_word (ssrint.Posz 1).
        { move=> E; move: vt_eq10; rewrite E vt_eq9 Ht9; discriminate. }
        have [rs [Hdu [Hrac [Hcap Htagclass]]]] :=
          return_pop_post Hrne1 reg_domm3 vt_eq11 vt_eq10 capa_cor3.
        exists {| mem := mem s3; regs := rs;
                  pc := v16@(build_tpc n comp');
                  internal := internal s3 |}.
        split.
        { transitivity (do! st' <- next_state_do_updates s3
                          ((Invalidated :: Invalidated :: Other :: reg_invalidate_hseq)%hseq
                           : hseq (tag_type lrc_tags) (R :: R :: R :: nseq 10 R))
                          (RegRead (as_word (ssrint.Posz 4)) :: RegRead r :: reg_clear_read);
                        Some ({| mem := mem st'; regs := regs st';
                                 pc := v16@(build_tpc n comp');
                                 internal := internal st' |},
                              Some (ERet comp rcom_value1 comp'))).
          - reflexivity.
          - by rewrite Hdu /=. }
        split; first by reflexivity.
        split.
        { exact: Hrac. }
        split.
        { exact: Hcap. }
        exact Htagclass. }

      destruct G' as [s3' [G' [Htag3 [Hregaddr3 [Hcapa3 Htagexport]]]]].
      have Hmem3 : mem s3' = mem3.
      { by rewrite (nsuap_mem_proj (@return_updts_regread _ _) G') eq_s3. }
      eexists. exists M'. simpl.
      split.
      * eapply (plus_left _ [:: ERet comp rcom_value1 comp'] ). try eapply step_jump; eauto.
        -- rewrite eq_s3 in vt_eq12. exact vt_eq12.
        -- inversion vt_match12; subst; revert H13; try decode_instr_eq.
           unfold decode_instr in H14. unfold ops in H14. simpl in H14.
           rewrite <- Heqa1 in H14. simpl in H14. rewrite H0 in H14. congruence.
           unfold decode_instr in H14. unfold ops in H14. simpl in H14.
           rewrite <- Heqa1 in H14. simpl in H14. rewrite H0 in H14. congruence.
        -- rewrite eq_s3 in vt_eq10. exact vt_eq10.
        -- rewrite eq_s3 in vt_eq11. exact vt_eq11.
        -- unfold reg_clear_list, reg_list. simpl. subst. simpl.
           repeat
             (match goal with
              | H: _ ?w = _  |- context[_ ?w] => rewrite H; simpl
              end). trivial.
        -- eapply star_refl.
        -- reflexivity.
      * have Hn2n : n2 = n by move: tag_pc1; rewrite ST0 /=; congruence.
        subst n2.
        rewrite eq_s3 in tag_pc3. simpl in tag_pc3. subst pc3_tag. simpl in *.
        eapply match_states_right.
        - eapply common_equiv_def.
          -- by rewrite /build_tpc. (* taga s1 *)
          -- by rewrite /build_tpc. (* taga s2 *)
          -- exact: Htag3. (* taga s3 -- from augmented assert *)
          -- rewrite Hmem3; rewrite eq_s3 in WF_ST; exact: WF_ST. (* wf_stack *)
          -- exact: (reg_domm_step_mp step_s1 reg_domm1).
          -- exact: (reg_domm_step step_s2 reg_domm2).
          -- exact: (reg_domm_nsuap G' reg_domm3).
          -- split; [|split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]]; trivial. (* gmc s1 *)
          -- split; [|split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]]; trivial. (* gmc s2 *)
          -- have ->: mem s3' = mem s3 by rewrite Hmem3 eq_s3 /=. split; [|split; [|split; [|split; [|split; [|split; [|split; [| split]]]]]]]; trivial. (* gmc s3 *)
          -- intros v' nA rw rweq. simpl in *. destruct rw as [r' | w'].
           { regs_noret rweq reg_domm1. }
           pose proof (capa_cor1 v' nA (inr w') rweq) as [is_in unicity]. simpl in unicity. split.
           { unfold in_stack in *. destruct is_in as [sv1 [sv2 [col [Hhead|is_in]]]]; [|eauto].
             exfalso. inversion Hhead.
             have Hx : v14@(Ret n) = v'@(Ret nA) by rewrite H15; exact: H17.
             move: Hx => [= _ Hnn]. subst nA.
             eapply (unicity (inl r0)). rewrite ST0 /=. exact RW0. }
           intros rw v''. destruct rw as [r' | w'']; simpl.
           { intro rweq'. regs_noret rweq' reg_domm1. }
           intros [t' [v''eq t'eq]]. eapply (unicity (inr _)); eauto.
          -- intros v' nA rw rweq. simpl in *. destruct rw as [r' | w'].
           { regs_noret rweq reg_domm2. }
           pose proof (capa_cor2 v' nA (inr w') rweq) as [is_in unicity]. simpl in unicity. split.
           { unfold in_stack in *. destruct is_in as [sv1 [sv2 [col [Hhead|is_in]]]]; [|eauto].
             exfalso. inversion Hhead. subst nA.
             eapply (unicity (inl r)). exact RW. }
           intros rw v''. destruct rw as [r' | w'']; simpl.
           { intro rweq'. regs_noret rweq' reg_domm2. }
           intros [t' [v''eq t'eq]]. eapply (unicity (inr _)); eauto.
          -- exact: Hcapa3. (* capability s3' -- proven in augmented assert *)
          -- eapply combined_codes_mem_cong; last exact: code_left. all: by rewrite ?Hmem3 ?eq_s3. (* combined_codes Left *)
          -- eapply combined_codes_mem_cong; last exact: code_right. all: by rewrite ?Hmem3 ?eq_s3. (* combined_codes Right *)
          -- (* running comp valid (restored caller, side-membership established above) *)
             by apply/orP; first [ left; assumption | right; assumption ].
          -- (* pcc s1' (weak Left): post-pc [w0]; [capa_cor1] on [RW0] links [w0 = v14]
                ([PTS_CODE1]'s value), so [pc_code_color_pts' PTS_CODE1]. *)
             have RWs1 : regs s1 r0 = Some w0@(Ret n) by rewrite ST0 /=; exact RW0.
             have Hv14w0 : w0 = v14.
             { have [Hin _] := capa_cor1 w0 n (inl r0) RWs1.
               move: Hin => [sv1 [sv2 [col [Hhd|Htl]]]].
               - move: Hhd => [= Hs2v _ _ _]. congruence.
               - exfalso. have [k [Hka [_ [_ Hklt]]]] := wf_stack_levels_lt' WF_ST Htl.
                 move: Hka => /= [= ?]; subst k. by rewrite ltnn in Hklt. }
             apply: (pc_code_color_pts' (C := comp')); last by rewrite /build_tpc.
             rewrite Hv14w0 -H20. exact: PTS_CODE1.
          -- (* pcc s2' (running Right): [H16 : v15 = w], [H20 : C = comp'] + [pc_code_color_pts PTS_CODE2] *)
             apply: (pc_code_color_pts (C := comp')); last by rewrite /build_tpc.
             rewrite -H16 -H20. exact: PTS_CODE2.
        - inversion weak as [mw sw sw' Hcw Hsw Hma1 Hma3 Heow Hmmw].
          eapply weak_equiv_def.
          -- by rewrite (color_of_from_taga Htag3). (* color_of via bridge *)
          -- have Hnip : (comp' \in domm ip) = false.
             { case Hin: (comp' \in domm ip) => //. exfalso.
               inversion Hmergeable_ifaces as [[_ fdisj] _].
               exact: (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic) fdisj comp' ic_comp' Hin). }
             unfold side_of, other_side; rewrite Hnip; trivial. (* side_of = other Left = Right *)
          -- exact: Hma1.
          -- eapply mem_addr_mem_cong; last exact: Hma3. by rewrite Hmem3 eq_s3.
          -- have ->: mem s3' = mem s3 by rewrite Hmem3 eq_s3 /=. exact: Heow.
          -- (* memory_match Left: popped metadata; Ret cells via capa_cor1/capa_cor3 unicity.
                The s1'-side mem is [mem s1] (matching [Hmmw] / [capa_cor1]); the s3'-side mem is
                unchanged (mem s3' = mem s3, matching [Hmmw] / [capa_cor3]).  The popped frame head
                lives in register [r0] on s1 ([RW0] : regs s1 r0 = w0@(Ret n)) and in register [r] on
                s3 ([vt_eq10] : regs s3 r = v16@(Ret n)).  For a [Ret] cell the level [n] is forced by
                [Hhead], and the frame can't be both in register and in memory. *)
            unfold memory_match. simpl.
            intros w' d d_code d_ip.
            have Hms3 : mem s3' = mem s3 by first [ reflexivity | rewrite Hmem3 eq_s3 // ].
            rewrite ?Hms3.
            split; intro w_eq.
            { destruct (fst (Hmmw w' d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
              simpl in *. exists d''. split; [|exact d''eq].
              destruct d; destruct d'' as [dv'' d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
                split; [trivial|]; split; [trivial|]; simpl in *.
              match goal with K : _ /\ _ |- _ => destruct K as [_ Hm] end.
              destruct d''t as [nn| | |]; try exact Hm.
              destruct Hm as [sv' [comp'' inM]].
              destruct inM as [Hhead|Htail]; [|exists sv', comp''; exact Htail].
              exfalso. inversion Hhead.
              subst nn.
              move: (capa_cor1 dv'' n (inr w')
                       (ex_intro _ _ (conj d''eq (Logic.eq_refl (Ret n))))) => [is_in unicity].
              exact: (unicity (inl r0) _ RW0). }
            { destruct (snd (Hmmw w' d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
              simpl in *. exists d''. split; [|exact d''eq].
              destruct d; destruct d'' as [dv'' d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
                split; [trivial|]; split; [trivial|]; simpl in *.
              match goal with K : _ /\ _ |- _ => destruct K as [_ Hm] end.
              destruct d''t as [nn| | |]; try exact Hm.
              destruct Hm as [sv' [comp'' inM]].
              destruct inM as [Hhead|Htail]; [|exists sv', comp''; exact Htail].
              exfalso. inversion Hhead.
              subst nn.
              move: (capa_cor3 dv'' n (inr w')
                       (ex_intro _ _ (conj d''eq (Logic.eq_refl (Ret n))))) => [is_in unicity].
              exact: (unicity (inl r) _ vt_eq10). }
        - eapply strong_equiv_def.
          -- (* same_pc Right s2' s3': s2' pc = w, s3' pc = v16 = w + off0 (VALA_OFF/H16); off0 = get_offset Right comp' (OFF_C) *)
             have Hmw : exists niv, mem0 w = Some niv.
             { case E: (mem0 w) => [niv|]; [by exists niv | exfalso; rewrite E in Heqa2; by inversion Heqa2]. }
             destruct Hmw as [niv Hmw].
             have Hicode : LRC.is_code (Types.taga niv)
               by move: PTS_CODE2; rewrite /points_to_comp_code H16 Hmw /= => -[_ Hic].
             have Hv3 := nsuap_pc_proj G'.
             eapply (same_pc_normal (off := off0));
               [ split; [exact: Hmw | exact: Hicode]
               | rewrite /color_of /= -H20; exact: OFF_C
               | rewrite Hv3 VALA_OFF H16; congr addw; by rewrite /= ].
          -- by rewrite (color_of_from_taga Htag3). (* color_of via bridge *)
          -- have Hnip : (comp' \in domm ip) = false.
             { case Hin: (comp' \in domm ip) => //. exfalso.
               inversion Hmergeable_ifaces as [[_ fdisj] _].
               exact: (@Machine.Intermediate.fdisjoint_partition_notinboth _ (domm ip) (domm ic) fdisj comp' ic_comp' Hin). }
             unfold side_of; rewrite Hnip; trivial. (* side_of = Right *)
          -- exact: s_mem_cor. (* mem_addr s2' *)
          -- eapply mem_addr_mem_cong; last exact: s'_mem_cor. by rewrite Hmem3 eq_s3. (* mem_addr s3' *)
          -- have ->: mem s3' = mem s3 by rewrite Hmem3 eq_s3 /=. exact: entry_off. (* entry_points_offset *)
          -- unfold register_address_correctness. simpl.
             intros d r1 r_d_eq.
             unfold register_domm in *.
             assert (r_in : In r1 (domm reg)).
             { clear - reg_domm2 r_d_eq RW. rewrite reg_domm2.
               rewrite -Extra.In_in in_fset. simpl.
               repeat (rewrite setmE in r_d_eq; unfold_match' r_d_eq; [ convert_eq_op |]; simpl in r_d_eq).
               all: try (red; simpl; tauto).
               rewrite -in_fset -reg_domm2. setoid_rewrite <- (rwP dommP). eauto.
               rewrite -in_fset -reg_domm2. setoid_rewrite <- (rwP dommP). eauto. }
             rewrite reg_domm2 in r_in.
             move: r_in; rewrite -Extra.In_in in_fset Extra.In_in => r_in.
             repeat (destruct r_in as [? | r_in]; try subst r1;
                     repeat (rewrite setmE in r_d_eq; simpl in r_d_eq)).
             all: unfold_match' r_d_eq; simpl.
             all: move: r_d_eq; rewrite ?eqxx;
                  repeat (rewrite simpl_as_word_equal; [| by [] | by [] | by [] ]);
                  rewrite /=; case: ifP => _; move=> [= <-]; by rewrite /address_correctness.
          -- (* register_address_correctness s3': all regs Other/Invalidated (Htagexport) ⇒ True, any side *)
             move=> vv rr Hr; rewrite /address_correctness.
             case: (Htagexport rr vv Hr) => [[_ ->]|[_ ->]]; exact: I.
          -- (* memory_match Right: popped metadata; Ret cells via capa_cor2/capa_cor3 unicity.
                The s2'-side mem is [mem0] (matching [mem_match] / [capa_cor2]); the s3'-side mem is
                unchanged (mem s3' here, matching [mem_match] / [capa_cor3]).  The popped frame head
                lives in register [r] on both runs ([RW] : reg r = w@(Ret n);
                [vt_eq10] : regs3 r = (w + as_word off0)%w@(Ret n)).  For a [Ret] cell the level [n] is
                forced by [Hhead], and the frame can't be both in register [r] and in memory. *)
            unfold memory_match. simpl.
            intros w' d d_code d_ip.
            have Hms3 : mem s3' = mem s3 by first [ reflexivity | rewrite Hmem3 eq_s3 // ].
            rewrite ?Hms3.
            split; intro w_eq.
            { destruct (fst (mem_match w' d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
              simpl in *. exists d''. split; [|exact d''eq].
              destruct d; destruct d'' as [dv'' d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
                split; [trivial|]; split; [trivial|]; simpl in *.
              match goal with K : _ /\ _ |- _ => destruct K as [_ Hm] end.
              destruct d''t as [nn| | |]; try exact Hm.
              destruct Hm as [sv' [comp'' inM]].
              destruct inM as [Hhead|Htail]; [|exists sv', comp''; exact Htail].
              exfalso. inversion Hhead.
              subst nn.
              move: (capa_cor2 dv'' n (inr w')
                       (ex_intro _ _ (conj d''eq (Logic.eq_refl (Ret n))))) => [is_in unicity].
              exact: (unicity (inl r) _ RW). }
            { destruct (snd (mem_match w' d d_code d_ip) w_eq) as [d'' [d''match d''eq]].
              simpl in *. exists d''. split; [|exact d''eq].
              destruct d; destruct d'' as [dv'' d''t]; destruct d''t as [d''t ? ? ?]. destruct d''match; subst;
                split; [trivial|]; split; [trivial|]; simpl in *.
              match goal with K : _ /\ _ |- _ => destruct K as [_ Hm] end.
              destruct d''t as [nn| | |]; try exact Hm.
              destruct Hm as [sv' [comp'' inM]].
              destruct inM as [Hhead|Htail]; [|exists sv', comp''; exact Htail].
              exfalso. inversion Hhead.
              subst nn.
              move: (capa_cor3 dv'' n (inr w')
                       (ex_intro _ _ (conj d''eq (Logic.eq_refl (Ret n))))) => [is_in unicity].
              exact: (unicity (inl r) _ vt_eq10). }
          -- (* registers_match Right: re-tagged regs.  Via [registers_match_clear] from the
                s3' classification export ([Htagexport]) + the concrete s2' chain classification
                ([regtag_closer reg_domm2]) + the reg-1 (com register) value coincidence: its value is
                preserved by the return on both chains, and the two pre-values agree ([Hv_a] from
                [reg_match]'s data_match at reg 1). *)
            have Hta_a : Types.taga a = Other.
            { case E: (Types.taga a) => [m|||]; rewrite E /= in Heqa36;
                first [ discriminate Heqa36 | reflexivity ]. }
            have Hr : r <> as_word (ssrint.Posz 1).
            { move=> Er. move: RW; rewrite Er H11 => [= Eqa].
              rewrite Eqa /= in Hta_a. discriminate Hta_a. }
            have Hv_a : Types.vala a = v10
              by apply: (data_match_other_val Hta_a vt_match9).
            have Ha20 : Types.vala a20 = v10.
            { have E1 : (as_word (ssrint.Posz 1) == r) = false.
              { case: eqP => [E|] //. by case: (Hr (esym E)). }
              move: Heqa62. rewrite E1 H11 /= => [= ->]. exact: Hv_a. }
            apply: (@registers_match_clear Right M' _ s3' v10);
              [ have D2 := reg_domm_step step_s2 reg_domm2;
                have D3 := reg_domm_nsuap G' reg_domm3;
                rewrite /register_domm in D2 D3; by rewrite D2 D3
              | regtag_closer reg_domm2
              | exact: Htagexport
              | rewrite !setmE;
                do 10 (rewrite simpl_as_word_equal; [| by [] | by [] | by [] ]);
                rewrite eqxx /=; by rewrite Ha20
              | by rewrite (nsuap_regread_vala (@return_updts_regread _ _) G'
                              (as_word (ssrint.Posz 1))) vt_eq9 ].

  (* All four return cases discharge both [pc_code_color] obligations.  The running side's post-pc
     equals the popped frame's saved RA definitionally ([pc_code_color_pts'/pts] on [PTS_CODE1/2]);
     the weak side's post-pc is linked to that saved RA by the per-case capability [in_stack]
     uniqueness ([capa_cor1/2] on the return register read, head frame unique by
     [wf_stack_levels_lt']). *)
  Qed.
End StepEventReturn.
