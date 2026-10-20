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
Require MicroPolicies.Recomposition.TraceWF MicroPolicies.Recomposition.TraceBracket.
Import TraceWF(ndsu_mem_noM, jal_head_tret, mem_unchanged_jal, nsuap_event_inv, get_tni_color_eq, run_syscall_event_none).
Import TraceBracket(nsu_silent_extract, switch_val_color).
Require Import MicroPolicies.Recomposition.PreservationLemmas.
Require Import MicroPolicies.Recomposition.RecompositionInit.

Module RecPcColor (S: RecompositionContext) (A: AlignmentFacts S).

  Module Init := RecInit S A.
  Include Init.
  Import PCCM.

  Definition pc_color_inv (s: state) : Prop :=
    forall d, mem s (vala (pc s)) = Some d -> color (taga d) = color_of s.

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

  Lemma transfer_event_jumpjal :
    forall (op : opcode) (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
           (ts : hseq (tag_type lrc_tags) (inputs op)) (tni : option (tag_type lrc_tags Symbolic.M))
           (evinp : ev_inputs) (ov : ovec lrc_tags op) (e : event),
      LRC.transfer (IVec (OP op) tpc ti ts tni) evinp = Some (ov, Some e) ->
      op = JUMP \/ op = JAL.
  Proof.
    move=> op tpc ti ts tni evinp ov e.
    rewrite /LRC.transfer /LRC.instr_rules_mp.
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
      by move: H => [=].
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
    -  by left.
    - rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      by move: H => [=].
    -  by right.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
    - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
  Qed.

  Lemma event_trpc_tni :
    forall (op : opcode) (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
           (ts : hseq (tag_type lrc_tags) (inputs op)) (tnitag : tag_type lrc_tags Symbolic.M)
           (evinp : ev_inputs) (ov : ovec lrc_tags op) (e : event),
      LRC.transfer (IVec (OP op) tpc ti ts (Some tnitag)) evinp = Some (ov, Some e) ->
      match trpc ov with Level _ c => c end = color tnitag.
  Proof.
    move=> op tpc ti ts tnitag evinp ov e.
    rewrite /LRC.transfer /LRC.instr_rules_mp.
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
      by move: H => [=].
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
    -
      rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts))) in H.
      case: (obind_inv H) => u0 [_ {}H]. move: H. case: ifP => _ H.
      + case: (obind_inv H) => u1 [_ {}H]. by move: H => [=].
      + case: (obind_inv H) => u1 [_ {}H]. case: (obind_inv H) => c' [Hc' {}H].
        case: (obind_inv H) => u3 [_ {}H]. move: H => [= Hov _]. rewrite -Hov /=. clear Hov.
        move: Hc'; case: tnitag => ? c0 ? ? /=; congruence.
    - rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      by move: H => [=].
    -
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

  Lemma silent_step_pc_color :
    forall (s s' : state), step_mp (NC := NC) s s' None -> pc_color_inv s'.
  Proof.
    move=> s s' Hstep. inversion Hstep.
    -
      rewrite /next_state_updates in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmm : mem s' = mem s.
      { move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]].
        rewrite Hmem (ndsu_mem_noM (st := s) _ _ Edsu); [ by rewrite ST | nomw | nomr ]. }
      apply: (pc_color_inv_combine Hpc _ Hbel) => d Hd.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    -
      rewrite /next_state_updates in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmm : mem s' = mem s.
      { move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]].
        rewrite Hmem (ndsu_mem_noM (st := s) _ _ Edsu); [ by rewrite ST | nomw | nomr ]. }
      apply: (pc_color_inv_combine Hpc _ Hbel) => d Hd.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    -
      rewrite /next_state_updates in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmm : mem s' = mem s.
      { move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]].
        rewrite Hmem (ndsu_mem_noM (st := s) _ _ Edsu); [ by rewrite ST | nomw | nomr ]. }
      apply: (pc_color_inv_combine Hpc _ Hbel) => d Hd.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    -
      rewrite /next_state_updates in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmm : mem s' = mem s.
      { move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]].
        rewrite Hmem (ndsu_mem_noM (st := s) _ _ Edsu); [ by rewrite ST | nomw | nomr ]. }
      apply: (pc_color_inv_combine Hpc _ Hbel) => d Hd.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    -
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have [Hw0 [Hmem' [Htag Hguard]]] := weak_load_facts ST MEM1 NEXT.
      apply: (pc_color_inv_combine Hpc _ Hbel) => d Hd.
      move: Hd; rewrite Hpc /= Hmem' setmE => Hd.
      move: Hd; case: eqP => [Heq | Hne].
      + move=> [= Hdeq]. exists (w2 @ t2). rewrite Heq Hw0.
        split; [ reflexivity | ]. by rewrite -Hdeq /= switch_val_color.
      + move=> Hd. by exists d.
    -
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have [vnew [oldd [Hw0 [Hmem' [Htag [Hcolv [Hcolold _]]]]]]] := weak_store_facts ST OLD NEXT.
      apply: (pc_color_inv_combine Hpc _ Hbel) => d Hd.
      move: Hd; rewrite Hpc /= Hmem' setmE => Hd.
      move: Hd; case: eqP => [Heq | Hne].
      + move=> [= Hdeq]. exists oldd. rewrite Heq. split; [ exact Hw0 | ].
        by rewrite -Hdeq Hcolold Hcolv.
      + move=> Hd. by exists d.
    -
      unfold mvec in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmm : mem s' = mem s.
      { move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]].
        rewrite Hmem (ndsu_mem_noM (st := s) _ _ Edsu); [ by rewrite ST | nomw | nomr ]. }
      apply: (pc_color_inv_combine Hpc _ Hbel) => d Hd.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    -
      unfold mvec, pc' in NEXT.
      have [Hpc Hbel] := silent_next_pc_belong NEXT.
      have Hmm : mem s' = mem s.
      { move: NEXT => /nsu_silent_extract [? [? [st0 [Edsu [Hmem _]]]]].
        rewrite Hmem (ndsu_mem_noM (st := s) _ _ Edsu); [ by rewrite ST | nomw | nomr ]. }
      apply: (pc_color_inv_combine Hpc _ Hbel) => d Hd.
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
      apply: (pc_color_inv_combine Hpc _ Hbel) => d Hd.
      exists d; split; [ rewrite -Hmm; by move: Hd; rewrite Hpc /= | by [] ].
    -
      have Halloc := run_syscall_alloc GETCALL CALL.
      exact: (pc_color_alloc_fun Halloc).
  Qed.

  Lemma event_step_pc_color :
    forall (s s' : state) e, step_mp (NC := NC) s s' (Some e) -> pc_color_inv s'.
  Proof.
    move=> s s' e Hstep. inversion Hstep.
    -  rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    -  rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    -  rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    -  rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    -  rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    -  rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    -
      unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem Hpcs]]]]]] := nsuap_event_inv NEXT.
      have Hmm : mem s' = mem s.
      { rewrite Hmem (ndsu_mem_noM (st := s) _ _ Hdsu); [ by rewrite ST | nomw | nomr ]. }
      move=> d Hd. move: Hd; rewrite Hpcs /= Hmm => Hd.
      move: Htr; rewrite Hd => Htr.
      have Hc := event_trpc_tni Htr.
      rewrite (color_of_pc_tag s') Hpcs /=. by rewrite Hc.
    -  unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    -
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
    -
      have Halloc := run_syscall_alloc GETCALL CALL.
      exact: (pc_color_alloc_fun Halloc).
  Qed.

  Lemma step_mp_pc_color : forall (s s' : state) ev,
    step_mp (NC := NC) s s' ev -> pc_color_inv s'.
  Proof.
    move=> s s' [e|] H; [ exact: (event_step_pc_color H) | exact: (silent_step_pc_color H) ].
  Qed.

  Lemma sem_step_pc_color : forall s t s', Step sem s t s' -> pc_color_inv s'.
  Proof.
    move=> s t s' Hstep. simpl in Hstep. destruct t as [|e [|? ?]].
    - inversion Hstep as [? ? ? H ? | ? ? ? ? H]; subst; exact: (step_mp_pc_color H).
    - inversion Hstep as [? ? ? H ? | ? ? ? ? H]; subst; exact: (step_mp_pc_color H).
    - inversion Hstep as [? ? ? H ? | ? ? ? ? H]; subst; exact: (False_rect _ H).
  Qed.

  Lemma star_last_or_refl : forall (L : Smallstep.semantics) s t s',
    Star L s t s' -> s' = s \/ exists s'' e, Step L s'' e s'.
  Proof.
    move=> L s t s' H. elim: H => [s0 | s1 t1 s2 t2 s3 t0 Hstep _ IH _].
    - by left.
    - right. case: IH => [Heq | [s'' [e0 H'']]].
      + subst s2. by exists s1, t1.
      + by exists s'', e0.
  Qed.

  Lemma find_rank'_has {T} (f : pred T) : forall l k n, find_rank' f l k = Some n -> has f l.
  Proof.
    elim => [|x l IH] k n //=. case E: (f x) => H; first by [].
    apply/orP; right. exact: (IH _ _ H).
  Qed.
  Lemma find_rank_has {T} (f : pred T) l n : find_rank f l = Some n -> has f l.
  Proof. exact: find_rank'_has. Qed.

  Lemma sem''_step_pc_color : forall s t s', Step sem'' s t s' -> pc_color_inv s'.
  Proof.
    move=> s t s' Hstep. simpl in Hstep. destruct t as [|e [|? ?]].
    - exact: (step_mp_pc_color (step_me_mp Hstep)).
    - exact: (step_mp_pc_color (step_me_mp Hstep)).
    - by case: Hstep.
  Qed.

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

  Lemma sem'_step_pc_color : forall s t s', Step sem' s t s' -> pc_color_inv s'.
  Proof.
    move=> s t s' Hstep. simpl in Hstep. destruct t as [|e [|? ?]].
    - exact: (step_mp_pc_color (step_me_mp Hstep)).
    - exact: (step_mp_pc_color (step_me_mp Hstep)).
    - by case: Hstep.
  Qed.

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

  Lemma event_nextcomp_and_some :
    forall (op : opcode) (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
           (ts : hseq (tag_type lrc_tags) (inputs op)) (tni : option (tag_type lrc_tags Symbolic.M))
           (evinp : ev_inputs) (ov : ovec lrc_tags op) (e : event),
      LRC.transfer (IVec (OP op) tpc ti ts tni) evinp = Some (ov, Some e) ->
      exists t, tni = Some t /\ next_comp_of_event e = color t.
  Proof.
    move=> op tpc ti ts tni evinp ov e.
    rewrite /LRC.transfer /LRC.instr_rules_mp.
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
      by move: H => [=].
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
    -
      rewrite (hseq_eta ts) (hseq_eta (hsbehead ts)) (hseq_eta (hsbehead (hsbehead ts))) in H.
      case: (obind_inv H) => u0 [_ {}H]. move: H. case: ifP => _ H.
      + case: (obind_inv H) => u1 [_ {}H]. by move: H => [=].
      + case: (obind_inv H) => u1 [_ {}H]. case: (obind_inv H) => c' [Hc' {}H].
        case: (obind_inv H) => u3 [_ {}H]. move: H => [= _ He]. move: He => [= He].
        case: tni Hc' => [t|] // Hc'. rewrite get_tni_color_eq in Hc'. case: Hc' => Hc'.
        exists t; split; first by []. by rewrite -He /= Hc'.
    - rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
      case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
      by move: H => [=].
    -
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
    -
      unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [_ [_ Hpcs]]]]]] := nsuap_event_inv NEXT.
      have [t [Htni Hnc]] := event_nextcomp_and_some Htr.
      rewrite Htni in Htr.
      rewrite (color_of_pc_tag s') Hpcs /= (event_trpc_tni Htr). by rewrite Hnc.
    -  unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
      case: (transfer_event_jumpjal Htr) => E; discriminate.
    -
      unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr [_ [_ Hpcs]]]]]] := nsuap_event_inv NEXT.
      have [t [Htni Hnc]] := event_nextcomp_and_some Htr.
      rewrite Htni in Htr.
      rewrite (color_of_pc_tag s') Hpcs /= (event_trpc_tni Htr). by rewrite Hnc.
    -
      have Hev := run_syscall_event_none CALL. discriminate Hev.
  Qed.

  Lemma sem_step_color : forall s t s', Step sem s t s' ->
    color_of s' = last (color_of s) [seq next_comp_of_event e | e <- t].
  Proof.
    move=> s t s' Hstep. simpl in Hstep. destruct t as [|e [|? ?]].
    - inversion Hstep as [? ? ? H ? | ? ? ? ? H]; subst; by rewrite (silent_step_color_preserved H).
    - inversion Hstep as [? ? ? H ? | ? ? ? ? H]; subst; by rewrite /= (event_step_color H).
    - inversion Hstep as [? ? ? H ? | ? ? ? ? H]; subst; exact: (False_rect _ H).
  Qed.

  Lemma star_color_last : forall s m s', Star sem s m s' ->
    color_of s' = last (color_of s) [seq next_comp_of_event e | e <- m].
  Proof.
    move=> s m s' H. elim: H => [s0 | s1 t1 s2 t2 s3 t0 Hstep Hstar IH Heqt].
    - by [].
    - rewrite Heqt map_cat last_cat -(sem_step_color Hstep). exact IH.
  Qed.

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
