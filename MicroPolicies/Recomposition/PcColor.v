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
Require Import MicroPolicies.Recomposition.RecompositionInit.

(* ============================================================================
   PcColor.v — the UNCONDITIONAL pc-colour reachability invariant.

   [pc_code_color] (Definitions.v) records only the CONDITIONAL fact "if the
   pc-cell is code then its colour is the running colour".  That is too weak for
   the final-state correspondence: a spurious [final_state] can sit on a
   same-colour DATA cell whose value decodes to Halt.  The LRC [check_belong]
   guard checks COLOUR ONLY (belong c (Some t) = (c == color t), LRC.v:103), so
   the *unconditional* invariant

       pc_color_inv s := forall d, mem s (vala (pc s)) = Some d -> color (taga d) = color_of s

   is a genuine per-step invariant.  We prove it is preserved by silent/event
   steps and holds at the initial state, hence at every reachable state.
   ============================================================================ *)

Module RecPcColor (S: RecompositionContext) (A: AlignmentFacts S).

  Module Init := RecInit S A.
  Include Init.
  Import PCCM.

  (* The unconditional pc-colour invariant: the cell the pc currently addresses
     (code OR data) has the running colour. *)
  Definition pc_color_inv (s: state) : Prop :=
    forall d, mem s (vala (pc s)) = Some d -> color (taga d) = color_of s.

  (* Unconditional analogue of [pc_code_color_combine]: from the post-pc =
     [pc']@[tpc] and a colour-correspondence between [mem s' (pc s')] and an
     auxiliary [mpre pc'] on which [belong] holds, conclude [pc_color_inv s']. *)
  Lemma pc_color_inv_combine : forall (s' : state)
      (mpre : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags Symbolic.M)}) pc' tpc,
    pc s' = pc'@tpc ->
    (forall d, mem s' (vala (pc s')) = Some d ->
       exists d0, mpre pc' = Some d0 /\ color (taga d0) = color (taga d)) ->
    belong (match tpc with Level _ c => c end)
           (match mpre pc' with Some ni => Some (taga ni) | None => None end) ->
    pc_color_inv s'.
  Proof.
    move=> s' mpre pc' tpc Hpc Hrel Hbel d Hd.
    have Hcol : color_of s' = match tpc with Level _ c => c end by rewrite color_of_pc_tag Hpc.
    case: (Hrel d Hd) => [d0 [Hd0 Hcol0]].
    move: Hbel Hcol0; rewrite Hd0 /belong.
    case Et: (taga d0) => [vt ct et bt] /= /eqP Hbel Hcol0.
    by rewrite Hcol Hbel Hcol0.
  Qed.

  (* Unconditional analogue of [pc_code_color_alloc]: the allocator lands the pc on
     the return-address cell [ret], whose colour the syscall has checked equals the
     current component (we only use the colour conjunct of the check). *)
  Lemma pc_color_alloc : forall (s s' : state) blk (a : mword mt) ret,
    mem s' = unionm (mem s) blk -> mem s a = Some ret ->
    vala (pc s') = a -> taga (pc s') = taga (pc s) ->
    (is_code (taga ret) && (color (taga ret) == match taga (pc s) with Level _ c => c end)) ->
    pc_color_inv s'.
  Proof.
    move=> s s' blk a ret Hmem Hret Hpc Htag Hchk d.
    have Hcol := color_of_taga_eq Htag.
    rewrite Hmem Hpc unionmE Hret /= => -[= Hd]. subst d.
    move: Hchk => /andP [_ /eqP Hc].
    by rewrite Hcol (color_ofE s).
  Qed.

  Lemma pc_color_alloc_fun : forall (s s' : state),
    alloc_fun (NC:=NC) s = Some s' -> pc_color_inv s'.
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
    apply: (pc_color_alloc (s := s) (a := vala ra_val) (ret := ret_addr));
      [ reflexivity | exact Hret | reflexivity | reflexivity | exact Hretcol ].
  Qed.

  (* An event-producing transfer is necessarily a (cross-component) JUMP or JAL.
     Mirrors [op_silent_trpc]'s case split; the 12 non-event opcodes produce [None]
     ([by move: H => [=]] discriminates [None = Some e]). *)
  Lemma transfer_event_jumpjal :
    forall (op : opcode) (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
           (ts : hseq (tag_type lrc_tags) (inputs op)) (tni : option (tag_type lrc_tags Symbolic.M))
           (evinp : ev_inputs) (ov : ovec lrc_tags op) (e : event),
      LRC.transfer (IVec (OP op) tpc ti ts tni) evinp = Some (ov, Some e) ->
      op = JUMP \/ op = JAL.
  Proof.
    move=> op tpc ti ts tni evinp ov e.
    rewrite /LRC.transfer /LRC.instr_rules.
    case: tpc => level current'.
    move: ts ov; case: op => [|||b||||||||||] ts ov; cbv zeta; move=> H.
    - rewrite (hseq0 ts) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H]. by move: H => [=].
    - rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H]. by move: H => [=].
    - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq0 (hsbehead (hsbehead ts))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H]. by move: H => [=].
    - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts)))
              (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => u3 [_ {}H]. by move: H => [=].
    - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts)))
              (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => u2 [_ {}H]. move: H. case: ifP => // _ H.
      move: H. case E: (switch_val _ _) => [a c] /=. by move=> [=].
    - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts)))
              (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => u3 [_ {}H].
      move: H. case: ifP => // _ H. move: H. case E: (switch_val _ _) => [a c] /=. by move=> [=].
    - (* JUMP *) by left.
    - rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => u2 [_ {}H]. by move: H => [=].
    - (* JAL *) by right.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
  Qed.

  (* The new pc-tag colour of an EVENT transfer equals the colour of the next-instruction cell
     [tnitag]: both the JUMP (return) and JAL (call) event branches set [trpc = build_tpc _
     (get_tni_color tni)], and [get_tni_color (Some tnitag) = Some (color tnitag)]. *)
  Lemma event_trpc_tni :
    forall (op : opcode) (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
           (ts : hseq (tag_type lrc_tags) (inputs op)) (tnitag : tag_type lrc_tags Symbolic.M)
           (evinp : ev_inputs) (ov : ovec lrc_tags op) (e : event),
      LRC.transfer (IVec (OP op) tpc ti ts (Some tnitag)) evinp = Some (ov, Some e) ->
      match trpc ov with Level _ c => c end = color tnitag.
  Proof.
    move=> op tpc ti ts tnitag evinp ov e.
    rewrite /LRC.transfer /LRC.instr_rules.
    case: tpc => level current'.
    move: ts ov; case: op => [|||b||||||||||] ts ov; cbv zeta; move=> H.
    - rewrite (hseq0 ts) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H]. by move: H => [=].
    - rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H]. by move: H => [=].
    - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq0 (hsbehead (hsbehead ts))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H]. by move: H => [=].
    - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts)))
              (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => u3 [_ {}H]. by move: H => [=].
    - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts)))
              (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => u2 [_ {}H]. move: H. case: ifP => // _ H.
      move: H. case E: (switch_val _ _) => [a c] /=. by move=> [=].
    - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts)))
              (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => u3 [_ {}H].
      move: H. case: ifP => // _ H. move: H. case E: (switch_val _ _) => [a c] /=. by move=> [=].
    - (* JUMP — event (return) branch *)
      rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts))) in H.
      case: (obind_inv H) => u0 [_ {}H]. move: H. case: ifP => _ H.
      + case: (obind_inv H) => u1 [_ {}H]. by move: H => [=].
      + case: (obind_inv H) => u1 [_ {}H]. case: (obind_inv H) => c' [Hc' {}H].
        case: (obind_inv H) => u3 [_ {}H]. move: H => [= Hov _]. rewrite -Hov /=. clear Hov.
        move: Hc'; case: tnitag => ? c0 ? ? /=; congruence.
    - rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => u2 [_ {}H]. by move: H => [=].
    - (* JAL — event (call) branch *)
      rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      move: H. case: ifP => _ H.
      + by move: H => [=].
      + case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => c' [Hc' {}H].
        case: (obind_inv H) => u3 [_ {}H]. move: H => [= Hov _]. rewrite -Hov /=. clear Hov.
        move: Hc'; case: tnitag => ? c0 ? ? /=; congruence.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
  Qed.

  (* Event analogue of [nsu_silent_extract]: peel a [next_state_updates_and_pc] producing an
     event, KEEPING the transfer equation (to feed [event_trpc_tni]/[transfer_event_jumpjal])
     and the [next_state_do_updates] (to read off [mem s']). *)
  Lemma nsuap_event_inv : forall (st s' : state) (op : opcode) tpc ti
      (ts : hseq (tag_type lrc_tags) (inputs op)) updts pc' e,
    @next_state_updates_and_pc mt ops lrc_tags LRC.transfer unit st
      (IVec (OP op) tpc ti ts) updts pc' = Some (s', Some e) ->
    exists evinp ov0 st0,
      LRC.transfer (IVec (OP op) tpc ti ts
        (match mem st pc' with Some ni => Some (taga ni) | None => None end)) evinp
        = Some (ov0, Some e) /\
      next_state_do_updates st (tr ov0) updts = Some st0 /\
      mem s' = mem st0 /\ pc s' = pc'@(trpc ov0).
  Proof.
    move=> st s' op tpc ti ts updts pc' e.
    rewrite /next_state_updates_and_pc /next_state.
    case Hevi: (evi st) => [evinp|] //=.
    case Hm: (mem st pc') => [ni|] /=.
    - case Htr: (LRC.instr_rules evinp op tpc ti ts (Some (taga ni))) => [ov_ev|] //=.
      case: ov_ev Htr => ov0 ev Htr /=.
      case Edsu: (next_state_do_updates st (tr ov0) updts) => [st0|] //=.
      move=> [= Hs Hev]. subst s'. rewrite Hev in Htr.
      exists evinp, ov0, st0. cbn.
      split; [exact Htr | split; [exact: Edsu | by []]].
    - case Htr: (LRC.instr_rules evinp op tpc ti ts None) => [ov_ev|] //=.
      case: ov_ev Htr => ov0 ev Htr /=.
      case Edsu: (next_state_do_updates st (tr ov0) updts) => [st0|] //=.
      move=> [= Hs Hev]. subst s'. rewrite Hev in Htr.
      exists evinp, ov0, st0. cbn.
      split; [exact Htr | split; [exact: Edsu | by []]].
  Qed.

  (* A silent LRC step lands the pc on a cell of the running colour.  Mirrors the
     case split of [silent_step_pc_code_color] but UNCONDITIONALLY: the OP opcodes
     leave memory unchanged (so the post-pc cell is a [mem s] cell guarded by
     [belong]); LOAD re-tags keeping colour ([switch_val_color]); STORE writes a
     cell whose colour is the running colour ([weak_store_facts]); the allocator
     lands on the running-coloured return address. *)
  Lemma silent_step_pc_color :
    forall (s s' : state), step_mp (NC := NC) s s' None -> pc_color_inv s'.
  Proof.
    move=> s s' Hstep. inversion Hstep.
    - (* 1  nop *)
      rewrite /next_state_updates in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmm : mem s' = mem s.
      { move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]].
        rewrite Hmem (ndsu_mem_noM (st := s) _ _ Edsu); [ by rewrite ST | nomw | nomr ]. }
      apply: (pc_color_inv_combine Hpc _ Hbel) => d Hd.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    - (* 2  const *)
      rewrite /next_state_updates in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmm : mem s' = mem s.
      { move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]].
        rewrite Hmem (ndsu_mem_noM (st := s) _ _ Edsu); [ by rewrite ST | nomw | nomr ]. }
      apply: (pc_color_inv_combine Hpc _ Hbel) => d Hd.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    - (* 3  mov *)
      rewrite /next_state_updates in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmm : mem s' = mem s.
      { move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]].
        rewrite Hmem (ndsu_mem_noM (st := s) _ _ Edsu); [ by rewrite ST | nomw | nomr ]. }
      apply: (pc_color_inv_combine Hpc _ Hbel) => d Hd.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    - (* 4  binop *)
      rewrite /next_state_updates in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmm : mem s' = mem s.
      { move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]].
        rewrite Hmem (ndsu_mem_noM (st := s) _ _ Edsu); [ by rewrite ST | nomw | nomr ]. }
      apply: (pc_color_inv_combine Hpc _ Hbel) => d Hd.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    - (* 5  load — re-tag of the loaded cell keeps colour *)
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have [Hw0 [Hmem' [Htag Hguard]]] := weak_load_facts ST MEM1 NEXT.
      apply: (pc_color_inv_combine Hpc _ Hbel) => d Hd.
      move: Hd; rewrite Hpc /= Hmem' setmE => Hd.
      move: Hd; case: eqP => [Heq | Hne].
      + move=> [= Hdeq]. exists (w2 @ t2). rewrite Heq Hw0.
        split; [ reflexivity | ]. by rewrite -Hdeq /= switch_val_color.
      + move=> Hd. by exists d.
    - (* 6  store — the written cell carries the running colour *)
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have [vnew [oldd [Hw0 [Hmem' [Htag [Hcolv [Hcolold _]]]]]]] := weak_store_facts ST OLD NEXT.
      apply: (pc_color_inv_combine Hpc _ Hbel) => d Hd.
      move: Hd; rewrite Hpc /= Hmem' setmE => Hd.
      move: Hd; case: eqP => [Heq | Hne].
      + move=> [= Hdeq]. exists oldd. rewrite Heq. split; [ exact Hw0 | ].
        by rewrite -Hdeq Hcolold Hcolv.
      + move=> Hd. by exists d.
    - (* 7  jump — memory unchanged *)
      unfold mvec in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmm : mem s' = mem s.
      { move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]].
        rewrite Hmem (ndsu_mem_noM (st := s) _ _ Edsu); [ by rewrite ST | nomw | nomr ]. }
      apply: (pc_color_inv_combine Hpc _ Hbel) => d Hd.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    - (* 8  bnz — memory unchanged *)
      unfold mvec, pc' in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmm : mem s' = mem s.
      { move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]].
        rewrite Hmem (ndsu_mem_noM (st := s) _ _ Edsu); [ by rewrite ST | nomw | nomr ]. }
      apply: (pc_color_inv_combine Hpc _ Hbel) => d Hd.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    - (* 9  jal — memory unchanged (identity MemRead + reg writes) *)
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
      apply: (pc_color_inv_combine Hpc _ Hbel) => d Hd.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    - (* 10  syscall (alloc) — pc lands on the running-coloured return address *)
      have Halloc := run_syscall_alloc GETCALL CALL.
      exact: (pc_color_alloc_fun Halloc).
  Qed.

  (* An EVENT (cross-component Call/Return) step also lands the pc on a running-coloured cell.
     The 7 non-event opcodes (nop..store, bnz) cannot emit an event ([transfer_event_jumpjal]);
     JUMP (return) and JAL (call) set the new pc-tag colour to the next-cell colour
     ([event_trpc_tni]), and memory is unchanged so that next-cell is the [mem s] cell read by
     [Hd]; SYSCALL(alloc) reuses [pc_color_alloc_fun] ([run_syscall_alloc] ignores the event). *)
  Lemma event_step_pc_color :
    forall (s s' : state) e, step_mp (NC := NC) s s' (Some e) -> pc_color_inv s'.
  Proof.
    move=> s s' e Hstep. inversion Hstep.
    - (* nop *) rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    - (* const *) rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    - (* mov *) rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    - (* binop *) rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    - (* load *) rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    - (* store *) rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    - (* jump — cross-component return *)
      unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem Hpcs]]]]]] := nsuap_event_inv NEXT.
      have Hmm : mem s' = mem s.
      { rewrite Hmem (ndsu_mem_noM (st := s) _ _ Hdsu); [ by rewrite ST | nomw | nomr ]. }
      move=> d Hd. move: Hd; rewrite Hpcs /= Hmm => Hd.
      move: Htr; rewrite Hd => Htr.
      have Hc := event_trpc_tni Htr.
      rewrite (color_of_pc_tag s') Hpcs /=. by rewrite Hc.
    - (* bnz *) unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    - (* jal — cross-component call *)
      unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem Hpcs]]]]]] := nsuap_event_inv NEXT.
      have Hmemcell : mem s (pc0 + 1)%w = Some (vret @ tret) by rewrite ST.
      have Hhead := jal_head_tret Htr.
      have Hmm : mem s' = mem s.
      { rewrite Hmem.
        apply: (@mem_unchanged_jal s st0 (pc0+1)%w vret tret (nseq 12 R) (tr ov0)
                  (RegWrite ra (pc0+1)%w :: reg_clear_read) Hmemcell Hhead _ _ Hdsu);
          [ nomw | nomr ]. }
      move=> d Hd. move: Hd; rewrite Hpcs /= Hmm => Hd.
      move: Htr; rewrite Hd => Htr.
      have Hc := event_trpc_tni Htr.
      rewrite (color_of_pc_tag s') Hpcs /=. by rewrite Hc.
    - (* syscall (alloc) — same as the silent case *)
      have Halloc := run_syscall_alloc GETCALL CALL.
      exact: (pc_color_alloc_fun Halloc).
  Qed.

  (* Any LRC step (silent or event) lands the pc on a running-coloured cell. *)
  Lemma step_mp_pc_color : forall (s s' : state) ev,
    step_mp (NC := NC) s s' ev -> pc_color_inv s'.
  Proof.
    move=> s s' [e|] H; [ exact: (event_step_pc_color H) | exact: (silent_step_pc_color H) ].
  Qed.

  (* A [sem] step yields a [step_mp] (BOTH [step_restricted_UB] constructors carry the [stepT]=[step2]
     relation, SmallstepUB.v:22-31), hence [pc_color_inv] of the target. *)
  Lemma sem_step_pc_color : forall s t s', Step sem s t s' -> pc_color_inv s'.
  Proof.
    move=> s t s' Hstep. simpl in Hstep. destruct t as [|e [|? ?]].
    - inversion Hstep as [? ? ? H ? | ? ? ? ? H]; subst; exact: (step_mp_pc_color H).
    - inversion Hstep as [? ? ? H ? | ? ? ? ? H]; subst; exact: (step_mp_pc_color H).
    - inversion Hstep as [? ? ? H ? | ? ? ? ? H]; subst; exact: (False_rect _ H).
  Qed.

  (* A [Star] either stays at the initial state or its last step targets [s']. *)
  Lemma star_last_or_refl : forall (L : Smallstep.semantics) s t s',
    Star L s t s' -> s' = s \/ exists s'' e, Step L s'' e s'.
  Proof.
    move=> L s t s' H. elim: H => [s0 | s1 t1 s2 t2 s3 t0 Hstep _ IH _].
    - by left.
    - right. case: IH => [Heq | [s'' [e0 H'']]].
      + subst s2. by exists s1, t1.
      + by exists s'', e0.
  Qed.

  (* [find_rank] succeeding means the predicate holds somewhere ([has]). *)
  Lemma find_rank'_has {T} (f : pred T) : forall l k n, find_rank' f l k = Some n -> has f l.
  Proof.
    elim => [|x l IH] k n //=. case E: (f x) => H; first by [].
    apply/orP; right. exact: (IH _ _ H).
  Qed.
  Lemma find_rank_has {T} (f : pred T) l n : find_rank f l = Some n -> has f l.
  Proof. exact: find_rank'_has. Qed.

  (* A [sem''] step (plain [step1] = [step_me], Definitions.v:242) yields a [step_mp] (via [step_me_mp]). *)
  Lemma sem''_step_pc_color : forall s t s', Step sem'' s t s' -> pc_color_inv s'.
  Proof.
    move=> s t s' Hstep. simpl in Hstep. destruct t as [|e [|? ?]].
    - exact: (step_mp_pc_color (step_me_mp Hstep)).
    - exact: (step_mp_pc_color (step_me_mp Hstep)).
    - by case: Hstep.
  Qed.

  (* Base case: the INITIAL state's pc-cell (the main entry) is running-coloured.  Unconditional
     analogue of [initial_state_pc_cell]: the pc lands inside [encode_code] (a code cell coloured
     [Component.main]); [encode_code_nth] makes the lookup succeed so no [is_code] side-condition
     is needed. *)
  Lemma initial_pc_color_inv : forall cde pb pi,
    has (fun '(_, tag) => color tag == Component.main) cde ->
    size (initial_memory (mt := mt) pb) + size cde < 2 ^ word_size mt ->
    pc_color_inv (initial_state cde pb pi).
  Proof.
    move=> cde pb pi Hhas Hsz d.
    set pc0 := size (initial_memory (mt := mt) pb).
    set mp := find (fun '(_, tag) => color tag == Component.main) cde.
    have Hmp : mp < size cde by rewrite /mp -has_find.
    have Hcol : color_of (initial_state cde pb pi) = Component.main by [].
    have Hpcv : vala (pc (initial_state cde pb pi)) = word_of_nat (pc0 + mp) by [].
    have Hmem : mem (initial_state cde pb pi)
              = unionm (encode_code cde pc0) (initial_memory (mt := mt) pb) by [].
    have [vmp Hvmp] : exists v, encode_code cde pc0 (word_of_nat (pc0 + mp)) = Some v.
    { have Hlt2 : mp < size (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
        (encode_instr_atom x
          (fun l default => match findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) cde
           with Some m => pc0 + m | None => if l == alloc_label then l else default end)
          (pc0 + size cde - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) cde).1
        by rewrite encode_code_foldr_size.
      destruct (nth_error_Some_ex Hlt2) as [v' Hv'].
      exists v'. rewrite addnC. exact: (encode_code_nth Hsz Hv'). }
    rewrite Hcol Hmem Hpcv unionmE Hvmp /=.
    move=> [= <-].
    destruct (encode_code_nth_inv Hvmp) as [n [Hwn [Hltn Hnthn]]].
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
  Qed.

  (* The reachability invariant for the LEFT run [sem]: every reachable state's pc-cell is
     running-coloured.  (Non-empty: the last step, [sem_step_pc_color]; empty: [initial_pc_color_inv].) *)
  Lemma reachable_pc_color : forall s t s',
    Smallstep.initial_state sem s -> Star sem s t s' -> pc_color_inv s'.
  Proof.
    move=> s t s' Hinit Hstar.
    case: (star_last_or_refl Hstar) => [Heq | [s'' [e0 Hstep]]]; last exact: (sem_step_pc_color Hstep).
    subst s'.
    move: Hinit; unfold Smallstep.initial_state, sem; simpl; unfold initial_state1 => Hinit; subst s.
    apply: initial_pc_color_inv.
    - have Hmain := cprog_main_existence Hprog_is_closed.
      move: Hmain; rewrite /prog /program_link /= => /orP[Hmp | Hmc].
      + have Hin := proj2 (wfprog_main_existence Hwfp) Hmp.
        rewrite /prog /program_link /= has_cat; apply/orP; left.
        exact: (@wf_color_has p Component.main Hwfp Hin).
      + have Hin := proj2 (wfprog_main_existence Hwfc) Hmc.
        rewrite /prog /program_link /= has_cat; apply/orP; right.
        exact: (@wf_color_has c Component.main Hwfc Hin).
    - rewrite /prog /program_link /=. exact: (ltn_trans memory_size alloc_label_lt_w).
  Qed.

  (* Reachability invariant for the MERGED run [sem''] (mirrors [reachable_pc_color]). *)
  Lemma reachable_pc_color'' : forall s t s',
    Smallstep.initial_state sem'' s -> Star sem'' s t s' -> pc_color_inv s'.
  Proof.
    move=> s t s' Hinit Hstar.
    case: (star_last_or_refl Hstar) => [Heq | [s'' [e0 Hstep]]]; last exact: (sem''_step_pc_color Hstep).
    subst s'.
    move: Hinit; unfold Smallstep.initial_state, sem''; simpl; unfold initial_state3 => Hinit; subst s.
    apply: initial_pc_color_inv.
    - have [start Hfr] := find_rank_main_prog''. exact: (find_rank_has Hfr).
    - rewrite /prog'' /program_link /=. exact: (ltn_trans memory_size'' alloc_label_lt_w).
  Qed.

  (* A [sem'] step (plain [step1] = [step_me]) yields a [step_mp] — dedicated copy of
     [sem''_step_pc_color] so the goal [simpl]s the step directly (avoids unifying the [sem']/[sem'']
     semantics records, which is very slow). *)
  Lemma sem'_step_pc_color : forall s t s', Step sem' s t s' -> pc_color_inv s'.
  Proof.
    move=> s t s' Hstep. simpl in Hstep. destruct t as [|e [|? ?]].
    - exact: (step_mp_pc_color (step_me_mp Hstep)).
    - exact: (step_mp_pc_color (step_me_mp Hstep)).
    - by case: Hstep.
  Qed.

  (* Reachability invariant for the RIGHT run [sem'] (mirrors [reachable_pc_color'']). *)
  Lemma reachable_pc_color' : forall s t s',
    Smallstep.initial_state sem' s -> Star sem' s t s' -> pc_color_inv s'.
  Proof.
    move=> s t s' Hinit Hstar.
    case: (star_last_or_refl Hstar) => [Heq | [s'' [e0 Hstep]]]; last exact: (sem'_step_pc_color Hstep).
    subst s'.
    move: Hinit; unfold Smallstep.initial_state, sem'; simpl; unfold initial_state2 => Hinit; subst s.
    apply: initial_pc_color_inv.
    - have [start Hfr] := find_rank_main_prog'. exact: (find_rank_has Hfr).
    - rewrite /prog' /program_link /=. exact: (ltn_trans memory_size' alloc_label_lt_w).
  Qed.

  (* ===== Running-colour tracking along a trace (for undef_running_left) ===== *)

  Lemma get_tni_color_eq : forall t : tag_type lrc_tags Symbolic.M,
    get_tni_color (Some t) = Some (color t).
  Proof. by case. Qed.

  (* An EVENT transfer's [tni] is present and the event's target [next_comp_of_event] is its colour.
     Mirror of [event_trpc_tni]/[transfer_event_jumpjal], generic in [tni]. *)
  Lemma event_nextcomp_and_some :
    forall (op : opcode) (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
           (ts : hseq (tag_type lrc_tags) (inputs op)) (tni : option (tag_type lrc_tags Symbolic.M))
           (evinp : ev_inputs) (ov : ovec lrc_tags op) (e : event),
      LRC.transfer (IVec (OP op) tpc ti ts tni) evinp = Some (ov, Some e) ->
      exists t, tni = Some t /\ next_comp_of_event e = color t.
  Proof.
    move=> op tpc ti ts tni evinp ov e.
    rewrite /LRC.transfer /LRC.instr_rules.
    case: tpc => level current'.
    move: ts ov; case: op => [|||b||||||||||] ts ov; cbv zeta; move=> H.
    - rewrite (hseq0 ts) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H]. by move: H => [=].
    - rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H]. by move: H => [=].
    - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq0 (hsbehead (hsbehead ts))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H]. by move: H => [=].
    - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts)))
              (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => u3 [_ {}H]. by move: H => [=].
    - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts)))
              (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => u2 [_ {}H]. move: H. case: ifP => // _ H.
      move: H. case E: (switch_val _ _) => [a c] /=. by move=> [=].
    - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts)))
              (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => u3 [_ {}H].
      move: H. case: ifP => // _ H. move: H. case E: (switch_val _ _) => [a c] /=. by move=> [=].
    - (* JUMP — return branch *)
      rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts))) in H.
      case: (obind_inv H) => u0 [_ {}H]. move: H. case: ifP => _ H.
      + case: (obind_inv H) => u1 [_ {}H]. by move: H => [=].
      + case: (obind_inv H) => u1 [_ {}H]. case: (obind_inv H) => c' [Hc' {}H].
        case: (obind_inv H) => u3 [_ {}H]. move: H => [= _ He]. move: He => [= He].
        case: tni Hc' => [t|] // Hc'. rewrite get_tni_color_eq in Hc'. case: Hc' => Hc'.
        exists t; split; first by []. by rewrite -He /= Hc'.
    - rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => u2 [_ {}H]. by move: H => [=].
    - (* JAL — call branch *)
      rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts))) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H]. move: H. case: ifP => _ H.
      + by move: H => [=].
      + case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => c' [Hc' {}H].
        case: (obind_inv H) => u3 [_ {}H]. move: H => [= _ He].
        case: tni Hc' He => [t|] // Hc' He. rewrite get_tni_color_eq in Hc'. case: Hc' => Hc'.
        exists t; split; first by [].
        move: He; case Hpn: (get_proc_name (Some t)) => [p|] //=.
        move=> [= He]. by rewrite -He /= Hc'.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
  Qed.

  (* A system call never emits an event (the only syscall, alloc, returns [Some (_, None)]). *)
  Lemma run_syscall_event_none : forall sc (s s' : state) ev,
    @run_syscall mt ops lrc_tags LRC.transfer unit sc s = Some (s', ev) -> ev = None.
  Proof.
    move=> sc s s' ev. rewrite /run_syscall.
    case: (evi s) => [i|] //=.
    case: (Symbolic.sem sc s) => [ss|] //=. by move=> [= _ <-].
  Qed.

  (* The running colour after an EVENT step is the event's target component. *)
  Lemma event_step_color :
    forall (s s' : state) e, step_mp (NC := NC) s s' (Some e) -> color_of s' = next_comp_of_event e.
  Proof.
    move=> s s' e Hstep. inversion Hstep.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    - (* jump *)
      unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [_ [_ Hpcs]]]]]] := nsuap_event_inv NEXT.
      have [t [Htni Hnc]] := event_nextcomp_and_some Htr.
      rewrite Htni in Htr.
      rewrite (color_of_pc_tag s') Hpcs /= (event_trpc_tni Htr). by rewrite Hnc.
    - (* bnz *) unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    - (* jal *)
      unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr [_ [_ Hpcs]]]]]] := nsuap_event_inv NEXT.
      have [t [Htni Hnc]] := event_nextcomp_and_some Htr.
      rewrite Htni in Htr.
      rewrite (color_of_pc_tag s') Hpcs /= (event_trpc_tni Htr). by rewrite Hnc.
    - (* syscall: run_syscall never emits an event *)
      have Hev := run_syscall_event_none CALL. discriminate Hev.
  Qed.

  (* A single [sem] step advances the running colour to the [last] of the step's trace. *)
  Lemma sem_step_color : forall s t s', Step sem s t s' ->
    color_of s' = last (color_of s) [seq next_comp_of_event e | e <- t].
  Proof.
    move=> s t s' Hstep. simpl in Hstep. destruct t as [|e [|? ?]].
    - inversion Hstep as [? ? ? H ? | ? ? ? ? H]; subst; by rewrite (silent_step_color_preserved H).
    - inversion Hstep as [? ? ? H ? | ? ? ? ? H]; subst; by rewrite /= (event_step_color H).
    - inversion Hstep as [? ? ? H ? | ? ? ? ? H]; subst; exact: (False_rect _ H).
  Qed.

  (* The running colour at the end of a [sem] run is [last_comp] of its trace. *)
  Lemma star_color_last : forall s m s', Star sem s m s' ->
    color_of s' = last (color_of s) [seq next_comp_of_event e | e <- m].
  Proof.
    move=> s m s' H. elim: H => [s0 | s1 t1 s2 t2 s3 t0 Hstep Hstar IH Heqt].
    - by [].
    - rewrite Heqt map_cat last_cat -(sem_step_color Hstep). exact IH.
  Qed.

  (* The blame-colour interface: if the LEFT run goes undefined in [ip], the running colour at the
     end is an [ip]-component.  ([color_of (initial) = main = last_comp E0]; events advance it.) *)
  Lemma undef_running_left : forall s1 s1' m,
    Smallstep.initial_state sem s1 -> Star sem s1 m s1' ->
    Common.Blame.undef_in m ip -> color_of s1' \in domm ip.
  Proof.
    move=> s1 s1' m Hinit Hstar Hundef.
    have Hcol := star_color_last Hstar.
    have Hmain : color_of s1 = Component.main.
    { move: Hinit; rewrite /Smallstep.initial_state /sem /= /initial_state1 => ->. by []. }
    move: Hundef; rewrite /Common.Blame.undef_in /Common.Blame.last_comp => Hundef.
    by rewrite Hcol Hmain.
  Qed.

End RecPcColor.
