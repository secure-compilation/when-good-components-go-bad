(* Phase 5, tier 3a (part 1): event-level facts for MP trace
   well-formedness.

   Every event emitted by the micro-policy machine ([step_mp], and hence by
   the overlay/UB-restricted runs) satisfies, at the point of emission:
     - its source component is the running colour,
     - it is CROSS-component (the [belong]-false branches of the LRC
       JUMP/JAL rules are the only event emitters),
     - a call's procedure and allowed-caller list come from the target
       cell's ENTRY tag, with the caller listed.

   These are the per-event ingredients of [well_formed_event]; combined
   with the entry-tag soundness invariant (part 2, forthcoming) they give
   the import condition, and with the shadow-stack invariant (part 3) the
   bracketing condition of [well_formed_trace].

   This file is deliberately S-FREE (no [RecompositionContext]): the
   handful of functor-internal helpers it needs from PcColor.v
   ([nsuap_event_inv], [get_tni_color_eq], [run_syscall_event_none]) are
   reproduced verbatim. *)

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
Require Import MicroPolicies.Utils.
Require Import Common.Traces.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import Coq.micromega.Lia.

Import DoNotation.
Import Types.
Import Symbolic.

Local Notation state := (@Symbolic.state mt LRC.lrc_tags unit).

(* ==================== functor-free helper copies ==================== *)

Lemma get_tni_color_eq : forall t : tag_type lrc_tags Symbolic.M,
  get_tni_color (Some t) = Some (color t).
Proof. by case. Qed.

Lemma run_syscall_event_none : forall sc (s s' : state) ev,
  @run_syscall mt ops lrc_tags LRC.transfer unit sc s = Some (s', ev) ->
  ev = None.
Proof.
  move=> sc s s' ev. rewrite /run_syscall.
  case: (evi s) => [i|] //=.
  case: (Symbolic.sem sc s) => [ss|] //=. by move=> [= _ <-].
Qed.

Lemma nsuap_event_inv : forall (st s' : state) (op : opcode) tpc ti
    (ts : hseq (tag_type lrc_tags) (inputs op)) updts pc' e,
  @next_state_updates_and_pc mt ops lrc_tags LRC.transfer unit st
    (IVec (OP op) tpc ti ts) updts pc' = Some (s', Some e) ->
  exists evinp ov0 st0,
    LRC.transfer (IVec (OP op) tpc ti ts
      (match mem st pc' with Some ni => Some (taga ni) | None => None end))
      evinp
      = Some (ov0, Some e) /\
    next_state_do_updates st (tr ov0) updts = Some st0 /\
    mem s' = mem st0 /\ pc s' = pc'@(trpc ov0).
Proof.
  move=> st s' op tpc ti ts updts pc' e.
  rewrite /next_state_updates_and_pc /next_state.
  case Hevi: (evi st) => [evinp|] //=.
  case Hm: (mem st pc') => [ni|] /=.
  - case Htr: (LRC.instr_rules_mp evinp op tpc ti ts (Some (taga ni))) => [ov_ev|] //=.
    case: ov_ev Htr => ov0 ev Htr /=.
    case Edsu: (next_state_do_updates st (tr ov0) updts) => [st0|] //=.
    move=> [= Hs Hev]. subst s'. rewrite Hev in Htr.
    exists evinp, ov0, st0. cbn.
    split; [exact Htr | split; [exact: Edsu | by []]].
  - case Htr: (LRC.instr_rules_mp evinp op tpc ti ts None) => [ov_ev|] //=.
    case: ov_ev Htr => ov0 ev Htr /=.
    case Edsu: (next_state_do_updates st (tr ov0) updts) => [st0|] //=.
    move=> [= Hs Hev]. subst s'. rewrite Hev in Htr.
    exists evinp, ov0, st0. cbn.
    split; [exact Htr | split; [exact: Edsu | by []]].
Qed.

(* ==================== small monitor-level helpers ==================== *)

(* the component of a pc tag *)
Definition pct_comp (t : tag_type lrc_tags Symbolic.P) : Component.id :=
  match t with Level _ c => c end.

Lemma belong_false_neq : forall c (t : tag_type lrc_tags Symbolic.M),
  belong c (Some t) = false -> c <> color t.
Proof.
  move=> c [vt col ent icd]; rewrite /belong /= => Hb E.
  by rewrite E eqxx in Hb.
Qed.

Lemma check_entry_some_facts : forall c (t : tag_type lrc_tags Symbolic.M) u p,
  check_entry c (Some t) = Some u ->
  get_proc_name (Some t) = Some p ->
  exists lc, entry t = Some (p, lc) /\ c \in lc.
Proof.
  move=> c [vt col [[pe lc]|] icd] u p //= Hce Hpn.
  case: Hpn => Epe; subst pe.
  move: Hce; case: ifP => // Hmem _.
  exists lc. split; first by [].
  exact: Hmem.
Qed.

(* the [tni] fed to the transfer function is the tag of an existing
   next-instruction memory cell *)
Lemma tni_cell : forall (s : state) (w : mword mt) tn,
  (match mem s w with
   | Some ni => Some (taga ni)
   | None => None
   end) = Some tn ->
  exists iv, mem s w = Some (iv@tn).
Proof.
  move=> s w tn. case: (mem s w) => [[iv it]|] //= [->]. by exists iv.
Qed.

(* ==================== memory-effect helpers (functor-free copies) ==================== *)

(* generic (any-event) version of [nsuap_event_inv] *)
Lemma nsuap_inv : forall (st s' : state) (op : opcode) tpc ti
    (ts : hseq (tag_type lrc_tags) (inputs op)) updts pc' ev,
  @next_state_updates_and_pc mt ops lrc_tags LRC.transfer unit st
    (IVec (OP op) tpc ti ts) updts pc' = Some (s', ev) ->
  exists evinp ov0 st0,
    LRC.transfer (IVec (OP op) tpc ti ts
      (match mem st pc' with Some ni => Some (taga ni) | None => None end))
      evinp
      = Some (ov0, ev) /\
    next_state_do_updates st (tr ov0) updts = Some st0 /\
    mem s' = mem st0 /\ pc s' = pc'@(trpc ov0).
Proof.
  move=> st s' op tpc ti ts updts pc' ev.
  rewrite /next_state_updates_and_pc /next_state.
  case Hevi: (evi st) => [evinp|] //=.
  case Hm: (mem st pc') => [ni|] /=.
  - case Htr: (LRC.instr_rules_mp evinp op tpc ti ts (Some (taga ni))) => [ov_ev|] //=.
    case: ov_ev Htr => ov0 ev0 Htr /=.
    case Edsu: (next_state_do_updates st (tr ov0) updts) => [st0|] //=.
    move=> [= Hs Hev]. subst s'. rewrite Hev in Htr.
    exists evinp, ov0, st0. cbn.
    split; [exact Htr | split; [exact: Edsu | by []]].
  - case Htr: (LRC.instr_rules_mp evinp op tpc ti ts None) => [ov_ev|] //=.
    case: ov_ev Htr => ov0 ev0 Htr /=.
    case Edsu: (next_state_do_updates st (tr ov0) updts) => [st0|] //=.
    move=> [= Hs Hev]. subst s'. rewrite Hev in Htr.
    exists evinp, ov0, st0. cbn.
    split; [exact Htr | split; [exact: Edsu | by []]].
Qed.

Lemma updm_set {T : ordType} {S : Type} (m m' : {fmap T -> S}) k v :
  updm m k v = Some m' -> m' = setm m k v.
Proof. rewrite /updm; case: (m k) => [a|] //. by move=> [<-]. Qed.

Lemma ndsu_cons :
  forall (st : state) (tk : tag_kind) (tks : seq tag_kind)
         (t : tag_type lrc_tags tk) (tags : hseq (tag_type lrc_tags) tks)
         (u : update) (us : seq update),
    next_state_do_updates st (HSeqCons t tags : hseq (tag_type lrc_tags) (tk :: tks)) (u :: us)
    = obind (fun st' => next_state_do_updates st' tags us)
            (next_state_do_update st t u).
Proof. by []. Qed.

Lemma mem_read_update_id :
  forall (st : state) (w : mword mt) (a : atom (mword mt) (tag_type lrc_tags Symbolic.M)),
    mem st w = Some a ->
    next_state_do_update st (taga a) (MemRead w) = Some st.
Proof.
  move=> st w [va ta] Hw. rewrite /next_state_do_update /= Hw /= /updm Hw /=.
  have Es : setm (mem st) w (va@ta) = mem st.
  { apply/eq_fmap => w'; rewrite setmE; case: eqP => [-> | _]; by rewrite ?Hw. }
  rewrite Es; clear Hw Es; by case: st.
Qed.

Lemma ndsu1_mem_noM : forall (st st1 : state) (tk : tag_kind) (tag : tag_type lrc_tags tk) u,
  (forall w v, u <> MemWrite w v) -> (forall w, u <> MemRead w) ->
  next_state_do_update st tag u = Some st1 -> mem st1 = mem st.
Proof.
  move=> st st1 tk tag u Hmw Hmr. case: tk tag => /= tag.
  - case: u Hmw Hmr => //= [r x|r] _ _.
    + by case: (updm (regs st) r x@tag) => [rs|] //= [<-].
    + case: (regs st r) => [a|] //=. by case: (updm _ _ _) => [rs|] //= [<-].
  - case: u Hmw Hmr => //= [w v|w] Hmw Hmr.
    + by move: (Hmw w v).
    + by move: (Hmr w).
  - by [].
Qed.

Lemma ndsu_mem_noM : forall (tks : seq tag_kind) (tags : hseq (tag_type lrc_tags) tks)
    (updts : seq update) (st st0 : state),
  (forall w v, ~ List.In (MemWrite w v) updts) -> (forall w, ~ List.In (MemRead w) updts) ->
  next_state_do_updates st tags updts = Some st0 -> mem st0 = mem st.
Proof.
  elim => [|tk tks IH] tags updts st st0 Hmw Hmr /=.
  - by move=> [<-].
  - case: updts Hmw Hmr => [|u us] Hmw Hmr //=.
    case E1: (next_state_do_update st (hshead tags) u) => [st1|] //= H.
    rewrite (IH _ _ _ _ _ _ H).
    + apply: (ndsu1_mem_noM _ _ E1).
      * by move=> w v Heq; apply: (Hmw w v); rewrite Heq; apply: List.in_eq.
      * by move=> w Heq; apply: (Hmr w); rewrite Heq; apply: List.in_eq.
    + by move=> w v Hin; apply: (Hmw w v); rewrite /=; right; exact: Hin.
    + by move=> w Hin; apply: (Hmr w); rewrite /=; right; exact: Hin.
Qed.

Lemma no_mw_reg_clear_read : forall (w v : mword mt), ~ List.In (MemWrite w v) reg_clear_read.
Proof.
  rewrite /reg_clear_read => w v.
  elim: reg_list => [|n l IH] /=; first by move=> [].
  by move=> [E|H]; [discriminate | exact: IH H].
Qed.

Lemma no_mr_reg_clear_read : forall (w : mword mt), ~ List.In (MemRead w) reg_clear_read.
Proof.
  rewrite /reg_clear_read => w.
  elim: reg_list => [|n l IH] /=; first by move=> [].
  by move=> [E|H]; [discriminate | exact: IH H].
Qed.

Lemma jal_head_tret : forall (tpc : tag_type lrc_tags P) (ti tret : tag_type lrc_tags Symbolic.M)
    (l : hseq (tag_type lrc_tags) (nseq (size reg_list).+1 R))
    (tni : option (tag_type lrc_tags Symbolic.M))
    (evinp : ev_inputs) (ov : ovec lrc_tags JAL) (ev : option event),
  LRC.transfer (IVec JAL tpc ti (HSeqCons tret l) tni) evinp = Some (ov, ev) ->
  hshead (tr ov) = tret.
Proof.
  move=> tpc ti tret l tni evinp ov ev.
  rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. case: ti => [vti cti eti bti]. cbv zeta.
  rewrite (hseq_eta l) (hseq_eta (hsbehead l)) /=.
  move=> H. case: (obind_inv H) => u0 [_ {}H].
  case: (obind_inv H) => ucb [_ {}H].
  move: H. case Hb: (belong cti tni).
  - by move=> [= <- _].
  - move=> H. case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => c' [_ {}H].
    case: (obind_inv H) => u2 [_ {}H].
    by move: H => [= <- _].
Qed.
Arguments jal_head_tret {tpc ti tret l tni evinp ov ev} _.

Lemma mem_unchanged_jal : forall (s s' : state) (w vw : mword mt)
    (tw : tag_type lrc_tags Symbolic.M) (tks : seq tag_kind)
    (tags : hseq (tag_type lrc_tags) (Symbolic.M :: tks)) (rest : seq update),
  mem s w = Some (vw @ tw) -> hshead tags = tw ->
  (forall w' v', ~ List.In (MemWrite w' v') rest) ->
  (forall w', ~ List.In (MemRead w') rest) ->
  next_state_do_updates s tags (MemRead w :: rest) = Some s' ->
  mem s' = mem s.
Proof.
  move=> s s' w vw tw tks tags rest Hmem Hhead Hnmw Hnmr Hndsu.
  have Hid := mem_read_update_id Hmem. cbn [taga] in Hid.
  move: Hndsu. rewrite (hseq_eta tags) Hhead ndsu_cons Hid /=. move=> Hndsu.
  by rewrite (ndsu_mem_noM Hnmw Hnmr Hndsu).
Qed.

Lemma mkfmap_pred_val (T : ordType) (S : eqType) (P : S -> Prop) :
  forall (kvs : seq (T * S)) w d,
    (forall p, p \in kvs -> P p.2) -> getm (mkfmap kvs) w = Some d -> P d.
Proof.
  elim => [|p kvs IH] w d Hall //=.
  rewrite setmE. case: eqP => [_ [<-]|_ H].
  - apply: Hall. by rewrite in_cons eqxx.
  - apply: (IH w d _ H) => q Hq. apply: Hall. by rewrite in_cons Hq orbT.
Qed.

Lemma table_sem_alloc : forall (N : nat) pc0 sc,
  Instance.table (NC:=N) pc0 = Some sc -> Symbolic.sem sc = alloc_fun (NC := N).
Proof.
  move=> N pc0 sc Htbl; move: Htbl.
  rewrite /Instance.table /Merged.table mkfmapE /=.
  case: ifP => [_ [= <-] // | _]. by [].
Qed.

Lemma run_syscall_alloc : forall (N : nat) pc0 sc (s s' : state) ev,
  Instance.table (NC:=N) pc0 = Some sc ->
  @run_syscall _ _ lrc_tags LRC.transfer unit sc s = Some (s', ev) ->
  alloc_fun (NC:=N) s = Some s'.
Proof.
  move=> N pc0 sc s s' ev Htbl Hrun.
  have Hsem : Symbolic.sem sc = alloc_fun (NC := N) := table_sem_alloc Htbl.
  move: Hrun. rewrite /run_syscall Hsem /= => H.
  case: (obind_inv H) => i [_ {}H].
  by case: (obind_inv H) => s0 [Hs0] [= <-].
Qed.

(* ==================== cell-shape preservation ==================== *)

(* the step-invariant part of a memory tag: its colour, entry data, and
   code flag (only the value tag [vtag] ever changes, via [switch_val]) *)
Definition tag_shape (t : tag_type lrc_tags Symbolic.M)
    : Component.id * option (Procedure.id * seq Component.id) * bool :=
  (color t, entry t, is_code t).

Lemma switch_val_shape : forall (t : tag_type lrc_tags Symbolic.M) v a c,
  switch_val t v = (a, c) -> tag_shape a = tag_shape t.
Proof. by move=> [vt col ent icd] v a c /= [<- _]. Qed.

(* every new memory cell of the allocator carries [def_mem_tag _ false] *)
Lemma alloc_cell_shape : forall (N : nat) (s s' : state),
  alloc_fun (NC:=N) s = Some s' ->
  forall w d, mem s' w = Some d ->
    mem s w = Some d \/ (entry (taga d) = None /\ is_code (taga d) = false).
Proof.
  move=> N s s' H. move: H. rewrite /alloc_fun. cbv zeta. move=> H.
  case: (obind_inv H) => ra_val [Hra {}H].
  case: (obind_inv H) => u1 [_ {}H].
  case: (obind_inv H) => reta [_ {}H].
  case: (obind_inv H) => uretchk [_ {}H].
  case: (obind_inv H) => sz [Hsz {}H].
  case: (obind_inv H) => u2 [_ {}H].
  case: (obind_inv H) => len [Hlen {}H].
  case: (obind_inv H) => u3 [_ {}H].
  move: H. case: ifP => // _ H.
  case: (obind_inv H) => addr [Haddr {}H].
  case: (obind_inv H) => regs' [Hregs' {}H].
  move: H => [= HSt]. subst s'.
  move=> w d /=. rewrite unionmE. case Ew: (mem s w) => [d0|].
  - by move=> [= ->]; left.
  - move=> Hb. right.
    move: Hb.
    apply: (@mkfmap_pred_val _ _
              (fun a : atom (mword mt) (tag_type lrc_tags Symbolic.M) =>
                 entry (taga a) = None /\ is_code (taga a) = false)).
    move=> p /mapP [n _ ->] /=. by [].
Qed.

(* the LOAD transfer re-tags the loaded cell through [switch_val]: the
   output M tag has the shape of the input cell tag *)
Lemma transfer_load_shape :
  forall (tpc : tag_type lrc_tags Symbolic.P) (ti : tag_type lrc_tags Symbolic.M)
         (t1 : tag_type lrc_tags Symbolic.R) (t2 : tag_type lrc_tags Symbolic.M)
         (told : tag_type lrc_tags Symbolic.R)
         (tni : option (tag_type lrc_tags Symbolic.M))
         (evinp : ev_inputs) (ov : ovec lrc_tags LOAD) (ev : option event),
    LRC.transfer (IVec (OP LOAD) tpc ti [hseq t1; t2; told] tni) evinp
      = Some (ov, ev) ->
    exists ta tm tb,
      tr ov = [hseq ta; tm; tb] /\ tag_shape tm = tag_shape t2.
Proof.
  move=> tpc ti t1 t2 told tni evinp ov ev.
  rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. cbv zeta. move=> H.
  case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
  case: (obind_inv H) => u2 [_ {}H].
  move: H. case: ifP => // _ H.
  move: H. case E: (switch_val _ _) => [a c] /=. move=> [= Hov _].
  do 3 eexists. split.
  - by rewrite -Hov.
  - exact: (switch_val_shape E).
Qed.

(* the STORE transfer writes the target cell with a [switch_val]-derived
   tag: the written M tag has the shape of the old cell tag *)
Lemma transfer_store_shape :
  forall (tpc : tag_type lrc_tags Symbolic.P) (ti : tag_type lrc_tags Symbolic.M)
         (t1 t2 : tag_type lrc_tags Symbolic.R) (told : tag_type lrc_tags Symbolic.M)
         (tni : option (tag_type lrc_tags Symbolic.M))
         (evinp : ev_inputs) (ov : ovec lrc_tags STORE) (ev : option event),
    LRC.transfer (IVec (OP STORE) tpc ti [hseq t1; t2; told] tni) evinp
      = Some (ov, ev) ->
    exists ta tb tm,
      tr ov = [hseq ta; tb; tm] /\ tag_shape tm = tag_shape told.
Proof.
  move=> tpc ti t1 t2 told tni evinp ov ev.
  rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. cbv zeta. move=> H.
  case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
  case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => u3 [_ {}H].
  move: H. case: ifP => // _ H.
  move: H. case E: (switch_val _ _) => [a c] /=. move=> [= Hov _].
  do 3 eexists. split.
  - by rewrite -Hov.
  - exact: (switch_val_shape E).
Qed.

(* concrete memory effect of the LOAD update list *)
Lemma ndsu_load_mem : forall (st st0 : state)
    (ta : tag_type lrc_tags Symbolic.R) (tm : tag_type lrc_tags Symbolic.M)
    (tb : tag_type lrc_tags Symbolic.R) (r1 r2 : reg mt) (w1 wv v1 : mword mt)
    (told : tag_type lrc_tags Symbolic.M),
  mem st w1 = Some (v1 @ told) ->
  next_state_do_updates st
      ([hseq ta; tm; tb] : hseq (tag_type lrc_tags) [:: Symbolic.R; Symbolic.M; Symbolic.R])
      [:: RegRead r1; MemRead w1; RegWrite r2 wv] = Some st0 ->
  mem st0 = setm (mem st) w1 (v1 @ tm).
Proof.
  move=> st st0 ta tm tb r1 r2 w1 wv v1 told Hw1 H.
  rewrite ndsu_cons in H. case: (obind_inv H) => st1 [H1 {}H].
  rewrite ndsu_cons in H. case: (obind_inv H) => st2 [H2 {}H].
  rewrite ndsu_cons in H. case: (obind_inv H) => st3 [H3 {}H].
  move: H => /= [= Est3].
  rewrite /next_state_do_update in H1 H2 H3.
  case: (obind_inv H1) => a1 [_ {}H1]. case: (obind_inv H1) => rs1 [_ {}H1].
  move: H1 => [= E1].
  case: (obind_inv H2) => a2 [Ha2 {}H2]. case: (obind_inv H2) => mm [Hmm {}H2].
  move: H2 => [= E2].
  case: (obind_inv H3) => rs3 [_ {}H3].
  move: H3 => [= E3].
  have Hm1 : mem st1 = mem st by rewrite -E1.
  have Ea2 : a2 = v1 @ told.
  { move: Ha2. rewrite Hm1 Hw1. by move=> [= ->]. }
  by rewrite -Est3 -E3 /= -E2 /= (updm_set Hmm) Hm1 Ea2 /=.
Qed.

(* concrete memory effect of the STORE update list *)
Lemma ndsu_store_mem : forall (st st0 : state)
    (ta tb : tag_type lrc_tags Symbolic.R) (tm : tag_type lrc_tags Symbolic.M)
    (r1 r2 : reg mt) (w1 w2 : mword mt),
  next_state_do_updates st
      ([hseq ta; tb; tm] : hseq (tag_type lrc_tags) [:: Symbolic.R; Symbolic.R; Symbolic.M])
      [:: RegRead r1; RegRead r2; MemWrite w1 w2] = Some st0 ->
  mem st0 = setm (mem st) w1 (w2 @ tm).
Proof.
  move=> st st0 ta tb tm r1 r2 w1 w2 H.
  rewrite ndsu_cons in H. case: (obind_inv H) => st1 [H1 {}H].
  rewrite ndsu_cons in H. case: (obind_inv H) => st2 [H2 {}H].
  rewrite ndsu_cons in H. case: (obind_inv H) => st3 [H3 {}H].
  move: H => /= [= Est3].
  rewrite /next_state_do_update in H1 H2 H3.
  case: (obind_inv H1) => a1 [_ {}H1]. case: (obind_inv H1) => rs1 [_ {}H1].
  move: H1 => [= E1].
  case: (obind_inv H2) => a2 [_ {}H2]. case: (obind_inv H2) => rs2 [_ {}H2].
  move: H2 => [= E2].
  case: (obind_inv H3) => mm [Hmm {}H3].
  move: H3 => [= E3].
  have Hm1 : mem st1 = mem st by rewrite -E1.
  have Hm2 : mem st2 = mem st1 by rewrite -E2.
  by rewrite -Est3 -E3 /= (updm_set Hmm) Hm2 Hm1.
Qed.

(* the reflexive-transitive cell-shape relation carried along runs *)
Definition mem_shape_extends
    (m0 m1 : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags Symbolic.M)}) : Prop :=
  forall w d, m1 w = Some d ->
    (exists d0, m0 w = Some d0 /\ tag_shape (taga d) = tag_shape (taga d0))
    \/ (entry (taga d) = None /\ is_code (taga d) = false).

(* ==================== entry-tag interface soundness ==================== *)

(* every allowed-caller list recorded in an entry tag is sanctioned by the
   interface: this is the invariant that turns [step_event_facts]'s call
   conclusion into [well_formed_event]'s import condition *)
Definition entry_sound (intf : Program.interface)
    (m : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags Symbolic.M)}) : Prop :=
  forall w iv tn p lc c,
    m w = Some (iv @ tn) -> entry tn = Some (p, lc) -> c \in lc ->
    imported_procedure_b intf c (color tn) p.

Lemma entry_sound_extends : forall intf m0 m1,
  mem_shape_extends m0 m1 -> entry_sound intf m0 -> entry_sound intf m1.
Proof.
  move=> intf m0 m1 Hext Hsnd w iv tn p lc c Hw Hent Hc.
  case: (Hext _ _ Hw) => [[[iv0 tn0] [Hd0 Esh]] | [Hnone _]]; last first.
  - by rewrite /= Hent in Hnone.
  - move: Esh. rewrite /tag_shape /=. move=> [= E1 E2 E3].
    rewrite E1. apply: (Hsnd _ _ _ _ _ _ Hd0 _ Hc). by rewrite -E2.
Qed.

(* ==================== transfer-level event facts ==================== *)

(* An event-producing LRC transfer emits a CROSS-component event whose
   source is the running (pc) component and whose target is the colour of
   the (present) next-instruction cell; a call's procedure and
   allowed-caller list come from that cell's entry tag, with the caller
   listed. *)
Lemma transfer_event_facts :
  forall (op : opcode) (tpc : tag_type lrc_tags Symbolic.P)
         (ti : tag_type lrc_tags Symbolic.M)
         (ts : hseq (tag_type lrc_tags) (inputs op))
         (tni : option (tag_type lrc_tags Symbolic.M))
         (evinp : ev_inputs) (ov : ovec lrc_tags op) (e : event),
    LRC.transfer (IVec (OP op) tpc ti ts tni) evinp = Some (ov, Some e) ->
    exists tn,
      [/\ tni = Some tn,
          cur_comp_of_event e = pct_comp tpc,
          next_comp_of_event e = color tn,
          pct_comp tpc <> color tn
        & forall c p v c', e = ECall c p v c' ->
            exists lc, entry tn = Some (p, lc) /\ c \in lc].
Proof.
  move=> op tpc ti ts tni evinp ov e.
  rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'.
  move: ts ov; case: op => [|||b||||||||||] ts ov; cbv zeta; move=> H.
  - rewrite (hseq0 ts) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    by move: H => [=].
  - rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    by move: H => [=].
  - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts))
            (hseq0 (hsbehead (hsbehead ts))) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    by move: H => [=].
  - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts))
            (hseq_eta (hsbehead (hsbehead ts)))
            (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    by move: H => [=].
  - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts))
            (hseq_eta (hsbehead (hsbehead ts)))
            (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => u2 [_ {}H]. move: H. case: ifP => // _ H.
    move: H. case E: (switch_val _ _) => [a c] /=. by move=> [=].
  - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts))
            (hseq_eta (hsbehead (hsbehead ts)))
            (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => u3 [_ {}H].
    move: H. case: ifP => // _ H.
    move: H. case E: (switch_val _ _) => [a c] /=. by move=> [=].
  - (* JUMP — the cross-component return branch emits *)
    rewrite (hseq_eta ts) (hseq_eta (hsbehead ts))
            (hseq_eta (hsbehead (hsbehead ts))) in H.
    case: (obind_inv H) => u0 [Hcc {}H].
    move: Hcc; case: eqP => [Ecur _|//].
    move: H. case Hbel: (belong _ _) => H.
    + case: (obind_inv H) => u1 [_ {}H]. by move: H => [=].
    + case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => c' [Hc' {}H].
      case: (obind_inv H) => u3 [_ {}H]. move: H => [= _ He].
      case: tni Hc' Hbel => [t|] // Hc' Hbel.
      rewrite get_tni_color_eq in Hc'. case: Hc' => Hc'.
      exists t. split.
      * by [].
      * by rewrite -He /= Ecur.
      * by rewrite -He /= Hc'.
      * move=> /= Ecol. exact: (belong_false_neq Hbel (etrans Ecur Ecol)).
      * by move=> c p v c'0; rewrite -He.
  - rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    by move: H => [=].
  - (* JAL — the cross-component call branch emits *)
    rewrite (hseq_eta ts) (hseq_eta (hsbehead ts))
            (hseq_eta (hsbehead (hsbehead ts))) in H.
    case: (obind_inv H) => u0 [Hcc {}H].
    move: Hcc; case: eqP => [Ecur _|//].
    case: (obind_inv H) => u1 [_ {}H].
    move: H. case Hbel: (belong _ _) => H.
    + by move: H => [=].
    + case: (obind_inv H) => u2 [_ {}H].
      case: (obind_inv H) => c' [Hc' {}H].
      case: (obind_inv H) => u3 [Hce {}H].
      move: H => [= _ He].
      case: tni Hc' Hce Hbel He => [t|] // Hc' Hce Hbel He.
      rewrite get_tni_color_eq in Hc'. case: Hc' => Hc'.
      move: He; case Hpn: (get_proc_name (Some t)) => [p|] //=.
      move=> [= He].
      exists t. split.
      * by [].
      * by rewrite -He /= Ecur.
      * by rewrite -He /= Hc'.
      * move=> /= Ecol. exact: (belong_false_neq Hbel (etrans Ecur Ecol)).
      * move=> c p0 v c'0. rewrite -He. move=> [= Ec Ep _ _].
        have [lc [He1 He2]] := check_entry_some_facts Hce Hpn.
        exists lc. split.
        { by rewrite He1 Ep. }
        by rewrite -Ec.
  - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
  - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
  - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
  - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
  - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
Qed.

(* ==================== step-level event facts ==================== *)

(* the common body of the instruction cases of [step_event_facts], on a
   destructured pre-state *)
Lemma step_event_facts_aux :
  forall (m : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags Symbolic.M)})
         (r : {fmap reg mt -> atom (mword mt) (tag_type lrc_tags Symbolic.R)})
         (pcv : mword mt) (tpc : tag_type lrc_tags Symbolic.P) (ex : unit)
         (s' : state) (op : opcode)
         (ti : tag_type lrc_tags Symbolic.M)
         (ts : hseq (tag_type lrc_tags) (inputs op)) updts pcn e,
    @next_state_updates_and_pc mt ops lrc_tags LRC.transfer unit
      {| Symbolic.mem := m; Symbolic.regs := r;
         Symbolic.pc := pcv@tpc; Symbolic.internal := ex |}
      (IVec (OP op) tpc ti ts) updts pcn = Some (s', Some e) ->
    [/\ cur_comp_of_event e = pct_comp tpc,
        next_comp_of_event e <> cur_comp_of_event e
      & forall c p v c', e = ECall c p v c' ->
          exists w iv (tn : tag_type lrc_tags Symbolic.M),
            [/\ m w = Some (iv@tn), color tn = c'
              & exists lc, entry tn = Some (p, lc) /\ c \in lc]].
Proof.
  move=> m r pcv tpc ex s' op ti ts updts pcn e NEXT.
  have [evinp [ov0 [st0 [Htr _]]]] := nsuap_event_inv NEXT.
  have [tn [Htni Hcur Hnext Hneq Hcall]] := transfer_event_facts Htr.
  split.
  - exact: Hcur.
  - rewrite Hnext Hcur => E. by apply: Hneq; rewrite E.
  - move=> c p v c'0 Ee.
    have [iv Hmw] := tni_cell Htni.
    eexists; exists iv, tn. split.
    + exact: Hmw.
    + by rewrite -Hnext Ee.
    + by have [lc [He1 He2]] := Hcall _ _ _ _ Ee; exists lc.
Qed.

Section StepEventFacts.

  Variable NC : nat.

  (* Every event of the micro-policy machine is a cross-component event out
     of the running component; a call's procedure and allowed-caller list
     come from the entry tag of an existing memory cell of the target's
     colour. *)
  Lemma step_event_facts : forall (s s' : state) e,
    step_mp s s' (Some e) (NC := NC) ->
    [/\ cur_comp_of_event e = rsc_color_of s,
        next_comp_of_event e <> cur_comp_of_event e
      & forall c p v c', e = ECall c p v c' ->
          exists w iv (tn : tag_type lrc_tags Symbolic.M),
            [/\ mem s w = Some (iv@tn), color tn = c'
              & exists lc, entry tn = Some (p, lc) /\ c \in lc]].
  Proof.
    move=> s s' e Hstep. inversion Hstep.
    - (* nop *)
      rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      rewrite ST in NEXT *. exact: (step_event_facts_aux NEXT).
    - (* const *)
      rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      rewrite ST in NEXT *. exact: (step_event_facts_aux NEXT).
    - (* mov *)
      rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      rewrite ST in NEXT *. exact: (step_event_facts_aux NEXT).
    - (* binop *)
      rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      rewrite ST in NEXT *. exact: (step_event_facts_aux NEXT).
    - (* load *)
      rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      rewrite ST in NEXT *. exact: (step_event_facts_aux NEXT).
    - (* store *)
      rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      rewrite ST in NEXT *. exact: (step_event_facts_aux NEXT).
    - (* jump *)
      unfold mvec in NEXT.
      rewrite ST in NEXT *. exact: (step_event_facts_aux NEXT).
    - (* bnz *)
      unfold mvec, pc' in NEXT.
      rewrite ST in NEXT *. exact: (step_event_facts_aux NEXT).
    - (* jal *)
      unfold mvec, pc' in NEXT.
      rewrite ST in NEXT *. exact: (step_event_facts_aux NEXT).
    - (* syscall: run_syscall never emits an event *)
      have Hev := run_syscall_event_none CALL. discriminate Hev.
  Qed.

  (* -------- cell-shape preservation along ANY machine step -------- *)

  (* A machine step never changes the colour, entry data, or code flag of
     an existing memory cell, and only the allocator creates cells — all of
     them entry-free non-code.  (Only LOAD/STORE re-tag a cell, both via
     [switch_val]; JAL rewrites the return cell with its own tag.) *)
  Lemma step_cell_shape : forall (s s' : state) ev,
    step_mp s s' ev (NC := NC) ->
    mem_shape_extends (mem s) (mem s').
  Proof.
    move=> s s' ev Hstep. inversion Hstep.
    - (* nop *)
      rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem _]]]]]] := nsuap_inv NEXT.
      have Hms : mem s' = mem s.
      { rewrite Hmem. apply: ndsu_mem_noM Hdsu.
        + by (move=> w' v' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (no_mw_reg_clear_read Hin))).
        + by (move=> w' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (no_mr_reg_clear_read Hin))). }
      move=> w d Hd. left. exists d. split; last by [].
      by rewrite -Hms.
    - (* const *)
      rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem _]]]]]] := nsuap_inv NEXT.
      have Hms : mem s' = mem s.
      { rewrite Hmem. apply: ndsu_mem_noM Hdsu.
        + by (move=> w' v' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (no_mw_reg_clear_read Hin))).
        + by (move=> w' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (no_mr_reg_clear_read Hin))). }
      move=> w d Hd. left. exists d. split; last by [].
      by rewrite -Hms.
    - (* mov *)
      rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem _]]]]]] := nsuap_inv NEXT.
      have Hms : mem s' = mem s.
      { rewrite Hmem. apply: ndsu_mem_noM Hdsu.
        + by (move=> w' v' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (no_mw_reg_clear_read Hin))).
        + by (move=> w' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (no_mr_reg_clear_read Hin))). }
      move=> w d Hd. left. exists d. split; last by [].
      by rewrite -Hms.
    - (* binop *)
      rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem _]]]]]] := nsuap_inv NEXT.
      have Hms : mem s' = mem s.
      { rewrite Hmem. apply: ndsu_mem_noM Hdsu.
        + by (move=> w' v' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (no_mw_reg_clear_read Hin))).
        + by (move=> w' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (no_mr_reg_clear_read Hin))). }
      move=> w d Hd. left. exists d. split; last by [].
      by rewrite -Hms.
    - (* load *)
      rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem _]]]]]] := nsuap_inv NEXT.
      have [ta [tm [tb [Etr Esh]]]] := transfer_load_shape Htr.
      rewrite Etr in Hdsu.
      have Hcell : mem s w1 = Some (w2 @ t2) by rewrite ST.
      have Hset := ndsu_load_mem Hcell Hdsu.
      move=> w d. rewrite Hmem Hset setmE.
      case: eqP => [-> [= <-]|_ Hd].
      + left. exists (w2 @ t2). split; first exact: Hcell.
        by rewrite /= Esh.
      + left. by exists d.
    - (* store *)
      rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem _]]]]]] := nsuap_inv NEXT.
      have [ta [tb [tm [Etr Esh]]]] := transfer_store_shape Htr.
      rewrite Etr in Hdsu.
      have Hcell : mem s w1 = Some (old @ told) by rewrite ST.
      have Hset := ndsu_store_mem Hdsu.
      move=> w d. rewrite Hmem Hset setmE.
      case: eqP => [-> [= <-]|_ Hd].
      + left. exists (old @ told). split; first exact: Hcell.
        by rewrite /= Esh.
      + left. by exists d.
    - (* jump *)
      unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem _]]]]]] := nsuap_inv NEXT.
      have Hms : mem s' = mem s.
      { rewrite Hmem. apply: ndsu_mem_noM Hdsu.
        + by (move=> w' v' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (no_mw_reg_clear_read Hin))).
        + by (move=> w' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (no_mr_reg_clear_read Hin))). }
      move=> w0 d Hd. left. exists d. split; last by [].
      by rewrite -Hms.
    - (* bnz *)
      unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem _]]]]]] := nsuap_inv NEXT.
      have Hms : mem s' = mem s.
      { rewrite Hmem. apply: ndsu_mem_noM Hdsu.
        + by (move=> w' v' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (no_mw_reg_clear_read Hin))).
        + by (move=> w' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (no_mr_reg_clear_read Hin))). }
      move=> w0 d Hd. left. exists d. split; last by [].
      by rewrite -Hms.
    - (* jal *)
      unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem _]]]]]] := nsuap_inv NEXT.
      have Hcell : mem s (pc0 + 1)%w = Some (vret @ tret) by rewrite ST.
      have Hhead := jal_head_tret Htr.
      have Hms : mem s' = mem s.
      { rewrite Hmem.
        apply: (@mem_unchanged_jal s st0 (pc0+1)%w vret tret (nseq 12 R)
                  (tr ov0) (RegWrite ra (pc0+1)%w :: reg_clear_read)
                  Hcell Hhead _ _ Hdsu).
        + by (move=> w' v' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (no_mw_reg_clear_read Hin))).
        + by (move=> w' Hin; cbn in Hin;
            repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
            (case: Hin || exact: (no_mr_reg_clear_read Hin))). }
      move=> w0 d Hd. left. exists d. split; last by [].
      by rewrite -Hms.
    - (* syscall: alloc *)
      have Halloc := run_syscall_alloc GETCALL CALL.
      move=> w d Hd.
      case: (alloc_cell_shape Halloc Hd) => [Hold | Hfresh].
      + left. exists d. by [].
      + by right.
  Qed.

  (* -------- star-level corollaries -------- *)

  (* Every event of a machine run is well-formed for any interface whose
     import relation sanctions the entry tags of the initial memory. *)
  Lemma star_events_wf : forall (W : program) (intf : Program.interface)
      (s : state) tw (s' : state),
    Star (mp_sem NC W) s tw s' ->
    entry_sound intf (mem s) ->
    all (well_formed_event intf) tw.
  Proof.
    move=> W intf s tw s' Hstar.
    elim: Hstar => [//| s1 t1 s2 t2 s3 tw0 Hstep Hstar IH Etw Hsnd].
    rewrite Etw {Etw}. move: Hstep. rewrite /= /prog_step_mp.
    case: t1 => [|e [|??]] // Hstep.
    - (* silent step *)
      apply: IH. exact: (entry_sound_extends (step_cell_shape Hstep) Hsnd).
    - (* event step *)
      rewrite /=. apply/andP. split; last first.
      + apply: IH. exact: (entry_sound_extends (step_cell_shape Hstep) Hsnd).
      + have [Hcur Hneq Hcall] := step_event_facts Hstep.
        clear Hstep.
        case: e Hcur Hneq Hcall => [C P v C'|C v C'] Hcur Hneq Hcall /=.
        * apply/andP. split.
          -- apply/eqP => EC. apply: Hneq. by rewrite /= EC.
          -- have [w [iv [tn [Hw Hcol [lc [Hent Hlc]]]]]] :=
               Hcall _ _ _ _ (erefl _).
             have Him := Hsnd _ _ _ _ _ _ Hw Hent Hlc.
             by rewrite -Hcol.
        * apply/eqP => EC. apply: Hneq. by rewrite /= EC.
  Qed.

End StepEventFacts.
