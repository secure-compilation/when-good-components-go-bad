(* Phase 5, tier 3a (part 3): the bracketing half of MP trace
   well-formedness.

   Single-run shadow-stack invariant tying a machine state to a
   [Traces.stack_state]: the pc tag's level is the call depth, and every
   linear Ret capability is registered in a shadow stack whose recorded
   values point (in memory) at caller-coloured cells.  The LRC monitor's
   linear-capability discipline (MOV/LOAD/STORE move capabilities,
   invalidating the source; cross-events invalidate registers; JAL events
   mint exactly one colour-checked capability) makes the invariant
   inductive, and at a JUMP event it forces the ERet target to be the
   top-of-stack caller — [well_bracketed_trace].

   Functor-free, building on TraceWF.v.  The capability machinery
   ([cap_at]/[cap_bijection]/[cap_reloc]/[lrc_silent_cap]) and the
   per-opcode silent transfer lemmas are reproduced from StepSilentWeak.v
   / PreservationLemmas.v (functor-internal there), with
   [capability_correctness M ws] generalized to an arbitrary level
   predicate [Q]. *)

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

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssrint seq.
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
Require Import MicroPolicies.Recomposition.TraceWF.
Require Import Coq.micromega.Lia.

Import DoNotation.
Import Types.
Import Symbolic.

Local Notation state := (@Symbolic.state mt LRC.lrc_tags unit).

(* ==================== the linear-capability predicate ==================== *)

(* "Ret capability at location [p]" ([inl r] register, [inr w] memory cell) *)
Definition cap_at (s : state) (p : Types.reg mt + mword mt) (v : mword mt) (n : nat) : Prop :=
  match p with
  | inr w => exists t, mem s w = Some (v @ t) /\ vtag t = Ret n
  | inl r => regs s r = Some (v @ (Ret n))
  end.

(* [capability_correctness] with the metadata lookup abstracted into an
   arbitrary level predicate [Q v n]: every Ret-[n] capability's value
   satisfies [Q _ n], and there is at most one Ret-[n] capability. *)
Definition cap_correct_gen (Q : mword mt -> nat -> Prop) (s : state) : Prop :=
  forall v n p,
    match p with
    | inr w => exists t, (mem s) w = Some (v @ t) /\ vtag t = Ret n
    | inl r => (regs s) r = Some (v @ (Ret n))
    end ->
    Q v n
    /\ forall p' v',
        (match p, p' with
         | inr w, inr w' => (exists t', (mem s) w' = Some (v' @ t') /\ vtag t' = Ret n) -> w = w'
         | inl r, inl r' => (regs s) r' = Some (v' @ (Ret n)) -> r = r'
         | inl _, inr w' => (exists t', (mem s) w' = Some (v' @ t') /\ vtag t' = Ret n) -> False
         | inr _, inl r' => (regs s) r' = Some (v' @ (Ret n)) -> False
         end).

Lemma cap_correct_to_cap_at : forall Q s,
  cap_correct_gen Q s ->
  forall v n p, cap_at s p v n ->
    Q v n /\ (forall p' v', cap_at s p' v' n -> p = p').
Proof.
  move=> Q s Hcap v n p Hp.
  move: (Hcap v n p Hp) => [Hin Huniq]. split; first exact: Hin.
  move=> p' v'. case: p Hp Huniq => [r|w] Hp Huniq; case: p' => [r'|w'] /=.
  - by move=> Hr'; move: (Huniq (inl r') v' Hr') => ->.
  - by move=> [t' [Hw' Ht']]; move: (Huniq (inr w') v' (ex_intro _ t' (conj Hw' Ht'))).
  - by move=> Hr'; move: (Huniq (inl r') v' Hr').
  - by move=> [t' [Hw' Ht']]; move: (Huniq (inr w') v' (ex_intro _ t' (conj Hw' Ht'))) => ->.
Qed.

Lemma cap_correct_via_cap_at : forall Q s,
  (forall v n p, cap_at s p v n ->
     Q v n /\ (forall p' v', cap_at s p' v' n -> p = p')) ->
  cap_correct_gen Q s.
Proof.
  move=> Q s H v n p Hp.
  move: (H v n p Hp) => [Hin Huniq]. split; first exact: Hin.
  move=> p' v'. case: p Hp Huniq => [r|w] Hp Huniq; case: p' => [r'|w'] /=.
  - by move=> Hr'; move: (Huniq (inl r') v' Hr') => [= ->].
  - by move=> [t' [Hw' Ht']]; move: (Huniq (inr w') v' (ex_intro _ t' (conj Hw' Ht'))).
  - by move=> Hr'; move: (Huniq (inl r') v' Hr').
  - by move=> [t' [Hw' Ht']]; move: (Huniq (inr w') v' (ex_intro _ t' (conj Hw' Ht'))) => [= ->].
Qed.

(* Master relocation lemma: a value/index-preserving map from [s']-cap
   locations to [s]-cap locations, injective on same-index cap locations,
   transfers [cap_correct_gen] from [s] to [s']. *)
Lemma cap_bijection : forall (s s' : state) (Q : mword mt -> nat -> Prop)
    (f : Types.reg mt + mword mt -> Types.reg mt + mword mt),
  (forall p v n, cap_at s' p v n -> cap_at s (f p) v n) ->
  (forall p1 p2 v1 v2 n, cap_at s' p1 v1 n -> cap_at s' p2 v2 n -> f p1 = f p2 -> p1 = p2) ->
  cap_correct_gen Q s -> cap_correct_gen Q s'.
Proof.
  move=> s s' Q f H1 H2 /cap_correct_to_cap_at Hcap.
  apply: cap_correct_via_cap_at => v n p Hp.
  move: (Hcap v n (f p) (H1 p v n Hp)) => [Hin Huniq]. split; first exact: Hin.
  move=> p' v' Hp'. exact: (H2 p p' v v' n Hp Hp' (Huniq (f p') v' (H1 p' v' n Hp'))).
Qed.

(* Single-relocation corollary: the one Ret cap moves from [src] to [dst],
   [src] is invalidated, every other location is unchanged. *)
Lemma cap_reloc : forall (s s' : state) (Q : mword mt -> nat -> Prop)
    (src dst : Types.reg mt + mword mt),
  (forall v n, cap_at s' dst v n -> cap_at s src v n) ->
  (forall v n, ~ cap_at s' src v n) ->
  (forall p v n, p <> src -> p <> dst -> cap_at s' p v n -> cap_at s p v n) ->
  cap_correct_gen Q s -> cap_correct_gen Q s'.
Proof.
  move=> s s' Q src dst Hdst Hsrc Hoth Hcap.
  pose f := fun p : Types.reg mt + mword mt => if p == dst then src else p.
  apply: (cap_bijection (f := f) _ _ Hcap).
  - move=> p v n Hp. rewrite /f. case: (p =P dst) => [E|E].
    + subst p. exact: (Hdst v n Hp).
    + case: (p =P src) => [Es|Es].
      * subst p. exfalso. exact: (Hsrc v n Hp).
      * exact: (Hoth p v n Es E Hp).
  - move=> p1 p2 v1 v2 n Hp1 Hp2. rewrite /f.
    case: (p1 =P dst) => [E1|E1]; case: (p2 =P dst) => [E2|E2].
    + by rewrite E1 E2.
    + move=> Hf. exfalso. apply: (Hsrc v2 n). by rewrite Hf.
    + move=> Hf. exfalso. apply: (Hsrc v1 n). by rewrite -Hf.
    + by [].
Qed.

(* Subset corollary: every cap of [s'] was already at the SAME location in [s]. *)
Lemma cap_subset : forall (s s' : state) (Q : mword mt -> nat -> Prop),
  (forall w v t n, mem s' w = Some (v @ t) -> vtag t = Ret n -> mem s w = Some (v @ t)) ->
  (forall r v n, regs s' r = Some (v @ (Ret n)) -> regs s r = Some (v @ (Ret n))) ->
  cap_correct_gen Q s -> cap_correct_gen Q s'.
Proof.
  move=> s s' Q Hmem Hreg Hcap v n p Hp.
  case: p Hp => [r|w] Hp.
  - have Hr : regs s r = Some (v @ (Ret n)) by exact: (Hreg r v n Hp).
    move: (Hcap v n (inl r) Hr) => [Hin Huniq]; split; first exact: Hin.
    move=> p' v'; case: p' => [r'|w'].
    + move=> Hr'; apply: (Huniq (inl r') v'); exact: (Hreg r' v' n Hr').
    + move=> [t' [Hw' Ht']]; apply: (Huniq (inr w') v'); exists t';
        split; [exact: (Hmem w' v' t' n Hw' Ht') | exact: Ht'].
  - case: Hp => t [Hw Ht].
    have Hwc : exists t0, mem s w = Some (v @ t0) /\ vtag t0 = Ret n
      by (exists t; split; [exact: (Hmem w v t n Hw Ht) | exact: Ht]).
    move: (Hcap v n (inr w) Hwc) => [Hin Huniq]; split; first exact: Hin.
    move=> p' v'; case: p' => [r'|w'].
    + move=> Hr'; apply: (Huniq (inl r') v'); exact: (Hreg r' v' n Hr').
    + move=> [t' [Hw'' Ht']]; apply: (Huniq (inr w') v'); exists t';
        split; [exact: (Hmem w' v' t' n Hw'' Ht') | exact: Ht'].
Qed.

(* ==================== small update-effect helpers ==================== *)

Lemma setm_reg_nonret :
  forall (rg : {fmap Types.reg mt -> atom (mword mt) (tag_type lrc_tags R)}) r x t,
  (forall n, t <> Ret n) ->
  forall r' v n, setm rg r (x @ t) r' = Some (v @ (Ret n)) -> rg r' = Some (v @ (Ret n)).
Proof.
  move=> rg r x t Hnr r' v n. rewrite setmE. case: eqP => [Heq|Hne].
  - move=> [= Hx Ht]. exfalso. exact: (Hnr n Ht).
  - by [].
Qed.

Lemma setm_mem_nonret :
  forall (mm : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags Symbolic.M)}) w x t,
  (forall n, vtag t <> Ret n) ->
  forall w' v t' n, setm mm w (x @ t) w' = Some (v @ t') -> vtag t' = Ret n -> mm w' = Some (v @ t').
Proof.
  move=> mm w x t Hnr w' v t' n. rewrite setmE. case: eqP => [Heq|Hne].
  - move=> [= Hx Ht]. subst t'. move=> Hvt. exfalso. exact: (Hnr n Hvt).
  - by [].
Qed.

Lemma ndsu_nil_updts : forall (tks : seq tag_kind) (tags : hseq (tag_type lrc_tags) tks) (st st0 : state),
  next_state_do_updates st tags [::] = Some st0 -> st0 = st.
Proof. move=> [|tk tks] tags st st0 /=; [by move=> [<-] | by []]. Qed.

Lemma setm_self : forall (T : ordType) (S : eqType) (m : {fmap T -> S}) k v,
  m k = Some v -> setm m k v = m.
Proof.
  move=> T S m k v Hk. apply/eq_fmap => k'. rewrite setmE. case: eqP => [->|//]. by rewrite Hk.
Qed.

Lemma switch_val_color : forall (m : tag_type lrc_tags Symbolic.M) v, color (switch_val m v).1 = color m.
Proof. by move=> [vt ct et bt] v. Qed.
Lemma switch_val_iscode : forall (m : tag_type lrc_tags Symbolic.M) v, is_code (switch_val m v).1 = is_code m.
Proof. by move=> [vt ct et bt] v. Qed.
Lemma switch_val_entry : forall (m : tag_type lrc_tags Symbolic.M) v, entry (switch_val m v).1 = entry m.
Proof. by move=> [vt ct et bt] v. Qed.
Lemma switch_val_vtag : forall (m : tag_type lrc_tags Symbolic.M) v, vtag (switch_val m v).1 = v.
Proof. by move=> [vt ct et bt] v. Qed.
Lemma switch_val_snd : forall (m : tag_type lrc_tags Symbolic.M) v, (switch_val m v).2 = vtag m.
Proof. by move=> [vt ct et bt] v. Qed.

Lemma check_belong_color : forall c (td : tag_type lrc_tags Symbolic.M) u,
  check_belong c (Some td) = Some u -> c = color td.
Proof.
  move=> c td u. rewrite /check_belong /belong.
  by case: td => vt ct et bt /=; case: ifP => // /eqP.
Qed.

(* silent-step extraction through [next_state_updates_and_pc] *)
Lemma nsu_silent_extract :
  forall (st : state) (kiv : option (tag_type lrc_tags Symbolic.M) -> ivec lrc_tags)
         (updts : seq update) (pc' : mword mt) (s' : state),
    @next_state_updates_and_pc mt ops lrc_tags LRC.transfer unit st kiv updts pc' = Some (s', None) ->
    exists (op0 : opcode) (ov0 : ovec lrc_tags op0) (st0 : state),
      next_state_do_updates st (tr ov0) updts = Some st0 /\
      mem s' = mem st0 /\ regs s' = regs st0 /\
      pc s' = pc'@(trpc ov0) /\ internal s' = internal st0.
Proof.
  move=> st kiv updts pc' s'.
  rewrite /next_state_updates_and_pc /next_state.
  case: (evi st) => [evinp|] //=.
  case: (LRC.transfer _ evinp) => [ov_ev|] //=.
  case: (op _) ov_ev => [op0|] ov_ev //=.
  case: ov_ev => ov0 ev.
  case Edsu: (next_state_do_updates st (tr ov0) updts) => [st0|] //=.
  move=> [= Hs Hev]. subst s'.
  exists op0, ov0, st0. cbn. split; [exact: Edsu | by []].
Qed.

(* ==================== silent output-tag shapes ==================== *)

Lemma const_transfer : forall (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
    (told : tag_type lrc_tags R) tni evinp (ov : ovec lrc_tags CONST) ev,
  LRC.transfer (IVec CONST tpc ti [hseq told] tni) evinp = Some (ov, ev) -> tr ov = [hseq Other].
Proof.
  move=> tpc ti told tni evinp ov ev. rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. cbv zeta => H.
  case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
  by move: H => [= <-].
Qed.

Lemma bnz_transfer : forall (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
    (t1 : tag_type lrc_tags R) tni evinp (ov : ovec lrc_tags BNZ) ev,
  LRC.transfer (IVec BNZ tpc ti [hseq t1] tni) evinp = Some (ov, ev) -> tr ov = [hseq t1].
Proof.
  move=> tpc ti t1 tni evinp ov ev. rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. cbv zeta => H.
  case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
  case: (obind_inv H) => u2 [_ {}H].
  by move: H => [= <-].
Qed.

Lemma mov_transfer : forall (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
    (t1 told : tag_type lrc_tags R) tni evinp (ov : ovec lrc_tags MOV) ev,
  LRC.transfer (IVec MOV tpc ti [hseq t1; told] tni) evinp = Some (ov, ev) ->
  tr ov = [hseq (moved_tag t1); t1].
Proof.
  move=> tpc ti t1 told tni evinp ov ev. rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. cbv zeta => H.
  case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
  by move: H => [= <-].
Qed.

Lemma binop_transfer : forall b (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
    (t1 t2 told : tag_type lrc_tags R) tni evinp (ov : ovec lrc_tags (BINOP b)) ev,
  LRC.transfer (IVec (BINOP b) tpc ti [hseq t1; t2; told] tni) evinp = Some (ov, ev) ->
  tr ov = [hseq t1; t2; Other].
Proof.
  move=> b tpc ti t1 t2 told tni evinp ov ev. rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. cbv zeta => H.
  case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
  case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => u3 [_ {}H].
  by move: H => [= <-].
Qed.

Lemma store_transfer : forall (tpc : tag_type lrc_tags P) (ti told : tag_type lrc_tags Symbolic.M)
    (t1 t2 : tag_type lrc_tags R) (tni : option (tag_type lrc_tags Symbolic.M))
    (evinp : ev_inputs) (ov : ovec lrc_tags STORE) (ev : option event),
  LRC.transfer (IVec STORE tpc ti [hseq t1; t2; told] tni) evinp = Some (ov, ev) ->
  ev = None /\ trpc ov = tpc /\
  tr ov = [hseq t1; (moved_tag t2); (switch_val told t2).1] /\
  color told = (match tpc with Level _ c => c end) /\ ~~ is_code told.
Proof.
  move=> tpc ti told t1 t2 tni evinp ov ev.
  rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. cbv zeta => H.
  case: (obind_inv H) => u0 [Hg0 {}H].
  case: (obind_inv H) => u1 [_ {}H].
  case: (obind_inv H) => u2 [_ {}H].
  case: (obind_inv H) => u3 [Hg3 {}H].
  have Hc0 : color ti = current'.
  { case E0: (color ti == current'); first by apply/eqP. by rewrite E0 in Hg0. }
  have Hcol : color told = current'.
  { have Hc1 := check_belong_color Hg3. by rewrite -Hc1. }
  case Hic: (is_code told).
  - move: H; rewrite Hic /=; move=> Heq; discriminate Heq.
  - move: H; rewrite Hic /= => Heq.
    move: Heq; case E: (switch_val told t2) => [tdd vt] /=.
    move=> [= <- <-] /=.
    split; first by []. split; first by []. split; first by [].
    split; last by []. exact: Hcol.
Qed.

Lemma load_transfer : forall (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
    (tp td : tag_type lrc_tags R) (ts : tag_type lrc_tags Symbolic.M)
    (tni : option (tag_type lrc_tags Symbolic.M))
    (evinp : ev_inputs) (ov : ovec lrc_tags LOAD) (ev : option event),
  LRC.transfer (IVec LOAD tpc ti [hseq tp; ts; td] tni) evinp = Some (ov, ev) ->
  ev = None /\ trpc ov = tpc /\
  tr ov = [hseq tp;
           (switch_val ts (moved_tag (vtag ts))).1;
           (switch_val ts (moved_tag (vtag ts))).2].
Proof.
  move=> tpc ti tp td ts tni evinp ov ev.
  rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. cbv zeta => H.
  case: (obind_inv H) => u0 [_ {}H].
  case: (obind_inv H) => u1 [_ {}H].
  case: (obind_inv H) => u2 [_ {}H].
  move: H. case: ifP => // _ H.
  move: H. case E: (switch_val ts (moved_tag (vtag ts))) => [ts' td'] /=.
  move=> [= <- <-] /=.
  split; first by []. split; first by []. by [].
Qed.

Lemma load_guard : forall (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
    (tp td : tag_type lrc_tags R) (ts : tag_type lrc_tags Symbolic.M)
    (tni : option (tag_type lrc_tags Symbolic.M))
    (evinp : ev_inputs) (ov : ovec lrc_tags LOAD) (ev : option event),
  LRC.transfer (IVec LOAD tpc ti [hseq tp; ts; td] tni) evinp = Some (ov, ev) ->
  is_code ts \/ color ts = (match tpc with Level _ c => c end).
Proof.
  move=> tpc ti tp td ts tni evinp ov ev.
  rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. cbv zeta => H.
  case: (obind_inv H) => u0 [Hcc {}H].
  case: (obind_inv H) => u1 [_ {}H].
  case: (obind_inv H) => u2 [_ {}H].
  have Hcc' : (match ti with {| color := c |} => c end) = current'.
  { case E: (match ti with {| color := c |} => c end == current'); first by apply/eqP.
    by rewrite E in Hcc. }
  move: H. case: ifP => // Hg _.
  move: Hg => /orP [Hbel | Hic].
  - case: ts Hbel => vts cts ets bts /= Hbel.
    right. move/eqP: Hbel => <-. exact: Hcc'.
  - by left.
Qed.

Lemma jump_transfer : forall (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
    (rat : tag_type lrc_tags R) (l : hseq (tag_type lrc_tags) (nseq (size reg_list).+1 R))
    (tni : option (tag_type lrc_tags Symbolic.M)) (evinp : ev_inputs) (ov : ovec lrc_tags JUMP) (ev : option event),
  LRC.transfer (IVec JUMP tpc ti (HSeqCons rat l) tni) evinp = Some (ov, ev) ->
  ev = None ->
  tr ov = HSeqCons rat l.
Proof.
  move=> tpc ti rat l tni evinp ov ev.
  rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. case: ti => [vti cti eti bti]. cbv zeta.
  rewrite (hseq_eta l) (hseq_eta (hsbehead l)) /=.
  move=> H Hev. case: (obind_inv H) => u0 [_ {}H].
  move: H. case Hb: (belong cti tni).
  - move=> H. case: (obind_inv H) => u1 [_ {}H]. by move: H => [= <- _].
  - move=> H. case: (obind_inv H) => u1 [_ {}H]. case: (obind_inv H) => c' [_ {}H].
    case: (obind_inv H) => u2 [_ {}H]. move: H => [= _ Hc]. move: Hev. by rewrite -Hc.
Qed.

Lemma jal_transfer : forall (tpc : tag_type lrc_tags P) (ti : tag_type lrc_tags Symbolic.M)
    (tret : tag_type lrc_tags Symbolic.M) (l : hseq (tag_type lrc_tags) (nseq (size reg_list).+1 R))
    (tni : option (tag_type lrc_tags Symbolic.M)) (evinp : ev_inputs) (ov : ovec lrc_tags JAL) (ev : option event),
  LRC.transfer (IVec JAL tpc ti (HSeqCons tret l) tni) evinp = Some (ov, ev) ->
  ev = None ->
  tr ov = HSeqCons tret (HSeqCons InternalJump (hsbehead l)).
Proof.
  move=> tpc ti tret l tni evinp ov ev.
  rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. case: ti => [vti cti eti bti]. cbv zeta.
  rewrite (hseq_eta l) (hseq_eta (hsbehead l)) /=.
  move=> H Hev. case: (obind_inv H) => u0 [_ {}H].
  case: (obind_inv H) => ucb [_ {}H].
  move: H. case Hb: (belong cti tni).
  - move=> H. by move: H => [= <- _].
  - move=> H. case: (obind_inv H) => u1 [_ {}H]. case: (obind_inv H) => c' [Hgtc {}H].
    case: (obind_inv H) => u2 [Hce {}H]. move: H => [= _ Hc].
    exfalso. move: Hgtc Hce Hc Hev {Hb}. case: tni => [cell|] //=.
    case: cell => [vc cc [[p ll]|] bc] //=.
    move=> _ _ Hc Hev. rewrite -Hc in Hev. discriminate Hev.
Qed.

(* ==================== jump/jal do-updates identities ==================== *)

Lemma reg_read_update_id :
  forall (st : state) (k : reg mt) (a : atom (mword mt) (tag_type lrc_tags R)),
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
         (a0 : atom (mword mt) (tag_type lrc_tags R))
         (tags : hseq (tag_type lrc_tags) (nseq (S (size l)) R)),
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

Lemma register_index_bound' : (20 < 2 ^ reg_field_size mt)%nat.
Proof. by rewrite reg_field_size_mt. Qed.

Lemma reg_index_neq : forall (x y : nat),
    x <> y -> (x < 20)%nat -> (y < 20)%nat ->
    (as_word (ssrint.Posz x) : reg mt) <> (as_word (ssrint.Posz y) : reg mt).
Proof.
  move=> x y Hxy Hx Hy Heq. apply: Hxy.
  have Hx' : (x < 2 ^ reg_field_size mt)%nat by apply: (ltn_trans Hx register_index_bound').
  have Hy' : (y < 2 ^ reg_field_size mt)%nat by apply: (ltn_trans Hy register_index_bound').
  by rewrite -(as_wordK Hx') -(as_wordK Hy') Heq.
Qed.

Lemma reg_clear_list_aux_setm_irrel :
  forall (l : seq nat) (rs : {fmap reg mt -> atom (mword mt) (tag_type lrc_tags R)})
         (k : reg mt) (v : atom (mword mt) (tag_type lrc_tags R)) (top : tag_type lrc_tags R),
    (forall n, n \in l -> as_word (ssrint.Posz n) <> k) ->
    reg_clear_list_aux l (setm rs k v) top = reg_clear_list_aux l rs top.
Proof.
  elim => [|e l' IH] rs k v top Hne //=.
  have Hek : as_word (ssrint.Posz e) <> k by (apply: (Hne e); rewrite in_cons eqxx).
  rewrite setmE (introF eqP Hek) /=.
  case: (rs (as_word (ssrint.Posz e))) => [a|] //=.
  by rewrite IH // => n Hn; apply: Hne; rewrite in_cons Hn orbT.
Qed.

Lemma reg_clear_list_aux_cons :
  forall (e : nat) (l' : seq nat)
         (rs : {fmap reg mt -> atom (mword mt) (tag_type lrc_tags R)})
         (top : tag_type lrc_tags R),
    reg_clear_list_aux (e :: l') rs top
    = obind (fun v => obind (fun l'' => Some (HSeqCons top l''))
                            (reg_clear_list_aux l' rs (taga v)))
            (rs (as_word (ssrint.Posz e))).
Proof. move=> e l' rs top /=. by case: (rs (as_word (ssrint.Posz e))). Qed.

Lemma jump_do_updates_result :
  forall (st : state) (r : reg mt) (rav w : mword mt) rat t1 l,
    regs st ra = Some (rav @ rat) ->
    regs st r = Some (w @ t1) ->
    reg_clear_list (regs st) t1 = Some l ->
    next_state_do_updates st
      (HSeqCons rat l : hseq (tag_type lrc_tags) [:: R & nseq (size reg_list).+1 R])
      (RegRead ra :: RegRead r :: reg_clear_read) = Some st.
Proof.
  move=> st r rav w rat t1 l Hra Hr Hcl.
  have HraU : next_state_do_update st (rat : tag_type lrc_tags R) (RegRead ra) = Some st
    by exact: (reg_read_update_id Hra).
  rewrite ndsu_cons HraU /=.
  exact: (reg_clear_do_updates_id Hr Hcl).
Qed.

Lemma jal_do_updates_result :
  forall (st : state) (pcw vv : mword mt) tret told a4 l,
    mem st (pcw + 1)%w = Some (vv @ tret) ->
    regs st (as_word (ssrint.Posz 4)) = Some a4 ->
    reg_clear_list (regs st) told = Some l ->
    next_state_do_updates st
      (HSeqCons tret (HSeqCons InternalJump (hsbehead l))
         : hseq (tag_type lrc_tags) [:: M, R & nseq (size reg_list) R])
      (MemRead (pcw + 1)%w
       :: RegWrite (as_word (ssrint.Posz 4)) (pcw + 1)%w
       :: reg_clear_read)
    = next_state_do_update st (InternalJump : tag_type lrc_tags R) (RegWrite (as_word (ssrint.Posz 4)) (pcw + 1)%w).
Proof.
  move=> st pcw vv tret told a4 l Hmem Ha4.
  Local Opaque next_state_do_updates reg_clear_list_aux next_state_do_update.
  rewrite /reg_clear_list /reg_list reg_clear_list_aux_cons.
  case Hv1 : (regs st (as_word (ssrint.Posz 1))) => [v1|] //=.
  case Hll : (reg_clear_list_aux [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19] (regs st) (taga v1)) => [ll|] //=.
  move=> [= Hl]. rewrite -Hl.
  rewrite ndsu_cons.
  Local Transparent next_state_do_update.
  rewrite (mem_read_update_id Hmem).
  Local Opaque next_state_do_update.
  rewrite [obind _ (Some st)]/= ndsu_cons.
  case HRW : (next_state_do_update st (InternalJump : tag_type lrc_tags R) (RegWrite (as_word (ssrint.Posz 4)) (pcw + 1)%w))
    => [s1a|] //.
  rewrite [obind _ (Some s1a)]/=.
  Local Transparent next_state_do_update.
  move: HRW; rewrite /next_state_do_update /= /updm Ha4 /= => [= Hs1a].
  Local Opaque next_state_do_update.
  have Hr : regs s1a = setm (regs st) (as_word (ssrint.Posz 4)) ((pcw + 1)%w @ InternalJump)
    by rewrite -Hs1a.
  have Hv1a : regs s1a (as_word (ssrint.Posz 1)) = Some v1.
  { rewrite Hr setmE.
    have H14 : (as_word (ssrint.Posz 1) : reg mt) <> (as_word (ssrint.Posz 4) : reg mt)
      by apply: (reg_index_neq (x:=1) (y:=4)).
    by rewrite (introF eqP H14). }
  have Hlla : reg_clear_list_aux [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19] (regs s1a) (taga v1) = Some ll.
  { rewrite Hr reg_clear_list_aux_setm_irrel; first exact Hll.
    have Hall : all (fun n => (n < 20)%nat && (n != 4)) [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19] = true by [].
    move=> nn Hnn. move: (allP Hall _ Hnn) => /andP[Hlt /eqP Hne].
    by apply: (reg_index_neq (x:=nn) (y:=4)). }
  exact: (reg_clear_do_updates_id Hv1a Hlla).
Qed.
Local Transparent next_state_do_updates reg_clear_list_aux next_state_do_update.

(* ==================== the allocator introduces no capability ==================== *)

Lemma mkfmap_const_val (T : ordType) (S : eqType) (v : S) :
  forall (kvs : seq (T * S)) w d,
    (forall p, p \in kvs -> p.2 = v) -> getm (mkfmap kvs) w = Some d -> d = v.
Proof.
  elim => [|p kvs IH] w d Hall //=.
  rewrite setmE. case: eqP => [_ [<-]|_ H].
  - by rewrite -(Hall p) // in_cons eqxx.
  - apply: (IH w) => // q Hq. apply: Hall. by rewrite in_cons Hq orbT.
Qed.

Lemma alloc_fun_cap : forall (N : nat) (s s' : state),
  alloc_fun (NC:=N) s = Some s' ->
  (forall w v t n, mem s' w = Some (v @ t) -> vtag t = Ret n -> mem s w = Some (v @ t)) /\
  (forall r v n, regs s' r = Some (v @ (Ret n)) -> regs s r = Some (v @ (Ret n))).
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
  move: H => [= HSt]. subst s'. split.
  - move=> w v t n /=. rewrite unionmE. case Ew: (mem s w) => [d0|] /=.
    + by move=> H _.
    + move=> Hb Hvt. exfalso. move: Hvt.
      have [= _ Ht] : (v @ t) = (word.as_word (ssrint.Posz 0)) @
          (def_mem_tag (match taga (pc s) with Level _ c => c end) false).
      { move: Hb. apply: mkfmap_const_val. by move=> p /mapP [m _ ->]. }
      rewrite Ht /=. by [].
  - move=> r v n /=. rewrite (updm_set Hregs') setmE.
    case: eqP => [_ H|_ H]; last exact: H.
    by move: H => [= _ Hc]; discriminate Hc.
Qed.

(* ==================== silent steps preserve capability correctness ==================== *)

Section SilentCap.

  Variable NC : nat.

  (* Verbatim adaptation of StepSilentWeak's [lrc_silent_cap], with the
     metadata lookup generalized to an arbitrary level predicate [Q]. *)
  Lemma lrc_silent_capQ : forall (s s' : state) (Q : mword mt -> nat -> Prop),
      step_mp (NC:=NC) s s' None ->
      cap_correct_gen Q s -> cap_correct_gen Q s'.
  Proof.
    move=> s s' Q Hstep Hcap. inversion Hstep.
    - (* nop *)
      move: NEXT; rewrite /next_state_updates => /nsu_silent_extract [op0 [ov0 [st0 [Edsu [Hm [Hr _]]]]]].
      have Hs0 := ndsu_nil_updts Edsu. rewrite Hs0 in Hm Hr.
      apply: (cap_subset _ _ Hcap); [by move=> w v t n0; rewrite Hm | by move=> r0 v n0; rewrite Hr].
    - (* const *)
      move: NEXT. rewrite /next_state_updates /next_state_updates_and_pc /next_state.
      case Hevi: (evi s) => [evinp|] //=.
      case Hpc': (mem s (vala (pc s) + 1)%w) => [ni|]; rewrite /=; move=> Hgoal;
        ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
          case: ov_ev Htr Hk => ov ev Htr Hk;
          have Htrov := const_transfer Htr; rewrite Htrov in Hk;
          case: (obind_inv Hk) => st0 [Hndsu Hfin];
          move: Hfin => [= Hst _]; subst s';
          move: Hndsu; rewrite /= => Hndsu;
          case: (obind_inv Hndsu) => st1 [Hndsu1 Hrest]; move: Hrest => [= Hr1];
          case: (obind_inv Hndsu1) => rg' [Hupd Hr2]; move: Hr2 => [= Hr2];
          apply: (cap_subset _ _ Hcap);
            [ by move=> w v t n0; rewrite /= -Hr1 -Hr2 /=
            | move=> r0 v n0; rewrite /= -Hr1 -Hr2 /= (updm_set Hupd); move=> Hset;
              exact: (setm_reg_nonret (t := Other) ltac:(move=> ?; discriminate) Hset) ] ).
    - (* mov *)
      move: NEXT. rewrite /next_state_updates /next_state_updates_and_pc /next_state.
      case Hevi: (evi s) => [evinp|] //=.
      case Hpc': (mem s (vala (pc s) + 1)%w) => [ni|]; rewrite /=; move=> Hgoal.
      { case: (obind_inv Hgoal) => ov_ev [Htr Hk].
        case: ov_ev Htr Hk => ov ev Htr Hk.
        move: (mov_transfer Htr) => Htrov. rewrite Htrov in Hk.
        case: (obind_inv Hk) => st0 [Hndsu Hfin].
        move: Hfin => [= Hst _]. subst s'.
        move: Hndsu. rewrite /= => Hndsu.
        case: (obind_inv Hndsu) => sta [Hnda HndsuB].
        case: (obind_inv Hnda) => a1 [Ha1 Hnda2].
        case: (obind_inv Hnda2) => rga [Hupda HstaE]. move: HstaE => [= HstaE].
        case: (obind_inv HndsuB) => stb [Hndb HndsuC].
        move: Hndb. rewrite -HstaE /= => Hndb.
        case: (obind_inv Hndb) => rgb [Hupdb HstbE]. move: HstbE => [= HstbE].
        move: HndsuC => [= Hfin2].
        have Ha1w : a1 = w1 @ t1 by move: Ha1; rewrite ST /= R1W; move=> [= <-].
        case: (r2 =P r1) => [Er2|Er2].
        - (* r1 = r2: self-move, identity *)
          subst r2. apply: (cap_subset _ _ Hcap).
          + by move=> w v t n0; rewrite -Hfin2 -HstbE /=.
          + move=> r v n0. rewrite -Hfin2 -HstbE /= (updm_set Hupdb) setmE (updm_set Hupda) setmE.
            case: (r =P r1) => [Er1|_].
            * subst r. rewrite ST /= R1W. by [].
            * by [].
        - (* r1 <> r2: cap moves r1 -> r2 *)
          apply: (cap_reloc (s := s) (src := inl r1) (dst := inl r2)).
          + move=> v n. rewrite /cap_at -Hfin2 -HstbE /= (updm_set Hupdb) setmE eqxx.
            move=> [= Hw1 Hvt]. rewrite /cap_at ST /= R1W Hvt -Hw1. by [].
          + move=> v n. rewrite /cap_at -Hfin2 -HstbE /= (updm_set Hupdb) setmE.
            have Hr1r2 : r1 != r2 by apply/eqP => Hc; apply: Er2; rewrite Hc.
            rewrite (negbTE Hr1r2) (updm_set Hupda) setmE eqxx.
            move=> [= _ Ht]. move: Ht. by case: (t1).
          + move=> p v n Hpr Hpw. case: p Hpr Hpw => [r|w] Hpr Hpw.
            * have Hrr1 : r != r1 by apply/eqP => Hc; apply: Hpr; rewrite Hc.
              have Hrr2 : r != r2 by apply/eqP => Hc; apply: Hpw; rewrite Hc.
              rewrite /cap_at -Hfin2 -HstbE /= (updm_set Hupdb) setmE (negbTE Hrr2) (updm_set Hupda) setmE (negbTE Hrr1). by [].
            * rewrite /cap_at -Hfin2 -HstbE /=. by [].
          + exact: Hcap. }
      { case: (obind_inv Hgoal) => ov_ev [Htr Hk].
        case: ov_ev Htr Hk => ov ev Htr Hk.
        move: (mov_transfer Htr) => Htrov. rewrite Htrov in Hk.
        case: (obind_inv Hk) => st0 [Hndsu Hfin].
        move: Hfin => [= Hst _]. subst s'.
        move: Hndsu. rewrite /= => Hndsu.
        case: (obind_inv Hndsu) => sta [Hnda HndsuB].
        case: (obind_inv Hnda) => a1 [Ha1 Hnda2].
        case: (obind_inv Hnda2) => rga [Hupda HstaE]. move: HstaE => [= HstaE].
        case: (obind_inv HndsuB) => stb [Hndb HndsuC].
        move: Hndb. rewrite -HstaE /= => Hndb.
        case: (obind_inv Hndb) => rgb [Hupdb HstbE]. move: HstbE => [= HstbE].
        move: HndsuC => [= Hfin2].
        have Ha1w : a1 = w1 @ t1 by move: Ha1; rewrite ST /= R1W; move=> [= <-].
        case: (r2 =P r1) => [Er2|Er2].
        - subst r2. apply: (cap_subset _ _ Hcap).
          + by move=> w v t n0; rewrite -Hfin2 -HstbE /=.
          + move=> r v n0. rewrite -Hfin2 -HstbE /= (updm_set Hupdb) setmE (updm_set Hupda) setmE.
            case: (r =P r1) => [Er1|_].
            * subst r. rewrite ST /= R1W. by [].
            * by [].
        - apply: (cap_reloc (s := s) (src := inl r1) (dst := inl r2)).
          + move=> v n. rewrite /cap_at -Hfin2 -HstbE /= (updm_set Hupdb) setmE eqxx.
            move=> [= Hw1 Hvt]. rewrite /cap_at ST /= R1W Hvt -Hw1. by [].
          + move=> v n. rewrite /cap_at -Hfin2 -HstbE /= (updm_set Hupdb) setmE.
            have Hr1r2 : r1 != r2 by apply/eqP => Hc; apply: Er2; rewrite Hc.
            rewrite (negbTE Hr1r2) (updm_set Hupda) setmE eqxx.
            move=> [= _ Ht]. move: Ht. by case: (t1).
          + move=> p v n Hpr Hpw. case: p Hpr Hpw => [r|w] Hpr Hpw.
            * have Hrr1 : r != r1 by apply/eqP => Hc; apply: Hpr; rewrite Hc.
              have Hrr2 : r != r2 by apply/eqP => Hc; apply: Hpw; rewrite Hc.
              rewrite /cap_at -Hfin2 -HstbE /= (updm_set Hupdb) setmE (negbTE Hrr2) (updm_set Hupda) setmE (negbTE Hrr1). by [].
            * rewrite /cap_at -Hfin2 -HstbE /=. by [].
          + exact: Hcap. }
    - (* binop *)
      move: NEXT. rewrite /next_state_updates /next_state_updates_and_pc /next_state.
      case Hevi: (evi s) => [evinp|] //=.
      case Hpc': (mem s (vala (pc s) + 1)%w) => [ni|]; rewrite /=; move=> Hgoal;
        ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
          case: ov_ev Htr Hk => ov ev Htr Hk;
          have Htrov := binop_transfer Htr; rewrite Htrov in Hk;
          case: (obind_inv Hk) => st0 [Hndsu Hfin];
          move: Hfin => [= Hst _]; subst s';
          move: Hndsu; rewrite /= => Hndsu;
          case: (obind_inv Hndsu) => sta [Hnda HndsuB];
          case: (obind_inv Hnda) => a1 [Ha1 Hnda2];
          case: (obind_inv Hnda2) => rga [Hupda HstaE]; move: HstaE => [= HstaE];
          case: (obind_inv HndsuB) => stb [Hndb HndsuC];
          move: Hndb; rewrite -HstaE /= => Hndb;
          case: (obind_inv Hndb) => a2 [Ha2 Hndb2];
          case: (obind_inv Hndb2) => rgb [Hupdb HstbE]; move: HstbE => [= HstbE];
          case: (obind_inv HndsuC) => stc [Hndc Hfin2]; move: Hfin2 => [= Hfin2];
          move: Hndc; rewrite -HstbE /= => Hndc;
          case: (obind_inv Hndc) => rgc [Hupdc HstcE]; move: HstcE => [= HstcE];
          (have Ha1w : a1 = w1 @ t1 by (move: (Ha1); rewrite ST /= R1W; move=> [= <-]));
          (have Ha2w : a2 = w2 @ t2 by
            (move: Ha2; rewrite (updm_set Hupda) setmE Ha1w /=;
             case: eqP => [Hr21|Hr21];
               [ move: R2W; rewrite Hr21 R1W; move=> [= <- <-]; move=> [= <-]
               | rewrite ST /= R2W; move=> [= <-] ]));
          apply: (cap_subset _ _ Hcap);
            [ by move=> w v t n0; rewrite /= -Hfin2 -HstcE /=
            | move=> r0 v n0; rewrite /= -Hfin2 -HstcE /= (updm_set Hupdc) setmE;
              case: eqP => [Heq3|Hne3];
                [ by move=> [= _ Hcon]
                | rewrite (updm_set Hupdb) setmE;
                  case: eqP => [Heq2|Hne2];
                    [ subst r0; rewrite Ha2w /=; move=> Hpre; rewrite ST /= R2W; exact: Hpre
                    | rewrite (updm_set Hupda) setmE;
                      case: eqP => [Heq1|Hne1];
                        [ subst r0; rewrite Ha1w /=; move=> Hpre; rewrite ST /= R1W; exact: Hpre
                        | move=> Hpre; exact: Hpre ] ] ] ] ).
    - (* load *)
      move: NEXT. rewrite /next_state_updates /next_state_updates_and_pc /next_state.
      case Hevi: (evi s) => [evinp|] //=.
      case Hpc': (mem s (vala (pc s) + 1)%w) => [ni|]; rewrite /=; move=> Hgoal.
      { case: (obind_inv Hgoal) => ov_ev [Htr Hk].
        case: ov_ev Htr Hk => ov ev Htr Hk.
        move: (load_transfer Htr) => [_ [_ Htrov]]. rewrite Htrov in Hk.
        case: (obind_inv Hk) => st0 [Hndsu Hfin].
        move: Hfin => [= Hst _]. subst s'.
        move: Hndsu. rewrite /= => Hndsu.
        case: (obind_inv Hndsu) => sta [Hnda HndsuB].
        case: (obind_inv Hnda) => a1 [Ha1 Hnda2].
        case: (obind_inv Hnda2) => rga [Hupda HstaE]. move: HstaE => [= HstaE].
        case: (obind_inv HndsuB) => stb [Hndb HndsuC].
        move: Hndb. rewrite -HstaE /= => Hndb.
        case: (obind_inv Hndb) => b1 [Hb1 Hndb2].
        case: (obind_inv Hndb2) => mmb [Hupdb HstbE]. move: HstbE => [= HstbE].
        case: (obind_inv HndsuC) => stc [Hndc Hfin2]. move: Hfin2 => [= Hfin2].
        move: Hndc. rewrite -HstbE /= => Hndc.
        case: (obind_inv Hndc) => rgc [Hupdc HstcE]. move: HstcE => [= HstcE].
        have Ha1w : a1 = w1 @ t1 by move: Ha1; rewrite ST /= R1W; move=> [= <-].
        have Hb1w : b1 = w2 @ t2 by move: Hb1; rewrite ST /= MEM1; move=> [= <-].
        apply: (cap_reloc (s := s) (src := inr w1) (dst := inl r2)).
        - (* Hdst: the loaded cap was at cell w1 *)
          move=> v n. rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdc) setmE eqxx switch_val_snd.
          move=> [= Hw2 Hvt]. exists t2. rewrite ST /= MEM1 -Hw2. by split.
        - (* Hsrc: cell w1 is invalidated -> no cap *)
          move=> v n [t [Hmem Hvt]]. move: Hmem Hvt.
          rewrite -Hfin2 -HstcE /= (updm_set Hupdb) setmE eqxx.
          move=> [= _ <-]. rewrite switch_val_vtag. by case: (vtag t2).
        - (* Hoth: every other location unchanged *)
          move=> p v n Hpw Hpr. case: p Hpw Hpr => [r|w] Hpw Hpr.
          + have Hrr2 : r != r2 by apply/eqP => Hc; apply: Hpr; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdc) setmE (negbTE Hrr2) (updm_set Hupda) setmE.
            case: (r =P r1) => [Er1|_].
            * subst r. rewrite Ha1w /= ST /= R1W. by [].
            * by [].
          + have Hww1 : w != w1 by apply/eqP => Hc; apply: Hpw; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdb) setmE (negbTE Hww1). by [].
        - exact: Hcap. }
      { case: (obind_inv Hgoal) => ov_ev [Htr Hk].
        case: ov_ev Htr Hk => ov ev Htr Hk.
        move: (load_transfer Htr) => [_ [_ Htrov]]. rewrite Htrov in Hk.
        case: (obind_inv Hk) => st0 [Hndsu Hfin].
        move: Hfin => [= Hst _]. subst s'.
        move: Hndsu. rewrite /= => Hndsu.
        case: (obind_inv Hndsu) => sta [Hnda HndsuB].
        case: (obind_inv Hnda) => a1 [Ha1 Hnda2].
        case: (obind_inv Hnda2) => rga [Hupda HstaE]. move: HstaE => [= HstaE].
        case: (obind_inv HndsuB) => stb [Hndb HndsuC].
        move: Hndb. rewrite -HstaE /= => Hndb.
        case: (obind_inv Hndb) => b1 [Hb1 Hndb2].
        case: (obind_inv Hndb2) => mmb [Hupdb HstbE]. move: HstbE => [= HstbE].
        case: (obind_inv HndsuC) => stc [Hndc Hfin2]. move: Hfin2 => [= Hfin2].
        move: Hndc. rewrite -HstbE /= => Hndc.
        case: (obind_inv Hndc) => rgc [Hupdc HstcE]. move: HstcE => [= HstcE].
        have Ha1w : a1 = w1 @ t1 by move: Ha1; rewrite ST /= R1W; move=> [= <-].
        apply: (cap_reloc (s := s) (src := inr w1) (dst := inl r2)).
        - move=> v n. rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdc) setmE eqxx switch_val_snd.
          move=> [= Hw2 Hvt]. exists t2. rewrite ST /= MEM1 -Hw2. by split.
        - move=> v n [t [Hmem Hvt]]. move: Hmem Hvt.
          rewrite -Hfin2 -HstcE /= (updm_set Hupdb) setmE eqxx.
          move=> [= _ <-]. rewrite switch_val_vtag. by case: (vtag t2).
        - move=> p v n Hpw Hpr. case: p Hpw Hpr => [r|w] Hpw Hpr.
          + have Hrr2 : r != r2 by apply/eqP => Hc; apply: Hpr; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdc) setmE (negbTE Hrr2) (updm_set Hupda) setmE.
            case: (r =P r1) => [Er1|_].
            * subst r. rewrite Ha1w /= ST /= R1W. by [].
            * by [].
          + have Hww1 : w != w1 by apply/eqP => Hc; apply: Hpw; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdb) setmE (negbTE Hww1). by [].
        - exact: Hcap. }
    - (* store *)
      move: NEXT. rewrite /next_state_updates /next_state_updates_and_pc /next_state.
      case Hevi: (evi s) => [evinp|] //=.
      case Hpc': (mem s (vala (pc s) + 1)%w) => [ni|]; rewrite /=; move=> Hgoal.
      { case: (obind_inv Hgoal) => ov_ev [Htr Hk].
        case: ov_ev Htr Hk => ov ev Htr Hk.
        move: (store_transfer Htr) => [_ [_ [Htrov _]]]. rewrite Htrov in Hk.
        case: (obind_inv Hk) => st0 [Hndsu Hfin].
        move: Hfin => [= Hst _]. subst s'.
        move: Hndsu. rewrite /= => Hndsu.
        case: (obind_inv Hndsu) => sta [Hnda HndsuB].
        case: (obind_inv Hnda) => a1 [Ha1 Hnda2].
        case: (obind_inv Hnda2) => rga [Hupda HstaE]. move: HstaE => [= HstaE].
        case: (obind_inv HndsuB) => stb [Hndb HndsuC].
        move: Hndb. rewrite -HstaE /= => Hndb.
        case: (obind_inv Hndb) => a2 [Ha2 Hndb2].
        case: (obind_inv Hndb2) => rgb [Hupdb HstbE]. move: HstbE => [= HstbE].
        case: (obind_inv HndsuC) => stc [Hndc Hfin2]. move: Hfin2 => [= Hfin2].
        move: Hndc. rewrite -HstbE /= => Hndc.
        case: (obind_inv Hndc) => mmc [Hupdc HstcE]. move: HstcE => [= HstcE].
        have Ha1w : a1 = w1 @ t1 by move: Ha1; rewrite ST /= R1W; move=> [= <-].
        apply: (cap_reloc (s := s) (src := inl r2) (dst := inr w1)).
        - (* Hdst: the stored cap was in reg r2 *)
          move=> v n [t [Hmem Hvt]]. move: Hmem.
          rewrite -Hfin2 -HstcE /= (updm_set Hupdc) setmE eqxx.
          move=> [= Hw2 Ht]. move: Hvt. rewrite -Ht switch_val_vtag => Hvt.
          rewrite /cap_at ST /= R2W Hvt -Hw2. by [].
        - (* Hsrc: source reg r2 is invalidated -> no cap *)
          move=> v n. rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdb) setmE eqxx.
          move=> [= _ Ht]. move: Ht. by case: (t2).
        - (* Hoth: every other location unchanged *)
          move=> p v n Hpr Hpw. case: p Hpr Hpw => [r|w] Hpr Hpw.
          + have Hrr2 : r != r2 by apply/eqP => Hc; apply: Hpr; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdb) setmE (negbTE Hrr2) (updm_set Hupda) setmE.
            case: (r =P r1) => [Er1|_].
            * subst r. rewrite Ha1w /= ST /= R1W. by [].
            * by [].
          + have Hww1 : w != w1 by apply/eqP => Hc; apply: Hpw; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdc) setmE (negbTE Hww1). by [].
        - exact: Hcap. }
      { case: (obind_inv Hgoal) => ov_ev [Htr Hk].
        case: ov_ev Htr Hk => ov ev Htr Hk.
        move: (store_transfer Htr) => [_ [_ [Htrov _]]]. rewrite Htrov in Hk.
        case: (obind_inv Hk) => st0 [Hndsu Hfin].
        move: Hfin => [= Hst _]. subst s'.
        move: Hndsu. rewrite /= => Hndsu.
        case: (obind_inv Hndsu) => sta [Hnda HndsuB].
        case: (obind_inv Hnda) => a1 [Ha1 Hnda2].
        case: (obind_inv Hnda2) => rga [Hupda HstaE]. move: HstaE => [= HstaE].
        case: (obind_inv HndsuB) => stb [Hndb HndsuC].
        move: Hndb. rewrite -HstaE /= => Hndb.
        case: (obind_inv Hndb) => a2 [Ha2 Hndb2].
        case: (obind_inv Hndb2) => rgb [Hupdb HstbE]. move: HstbE => [= HstbE].
        case: (obind_inv HndsuC) => stc [Hndc Hfin2]. move: Hfin2 => [= Hfin2].
        move: Hndc. rewrite -HstbE /= => Hndc.
        case: (obind_inv Hndc) => mmc [Hupdc HstcE]. move: HstcE => [= HstcE].
        have Ha1w : a1 = w1 @ t1 by move: Ha1; rewrite ST /= R1W; move=> [= <-].
        apply: (cap_reloc (s := s) (src := inl r2) (dst := inr w1)).
        - move=> v n [t [Hmem Hvt]]. move: Hmem.
          rewrite -Hfin2 -HstcE /= (updm_set Hupdc) setmE eqxx.
          move=> [= Hw2 Ht]. move: Hvt. rewrite -Ht switch_val_vtag => Hvt.
          rewrite /cap_at ST /= R2W Hvt -Hw2. by [].
        - move=> v n. rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdb) setmE eqxx.
          move=> [= _ Ht]. move: Ht. by case: (t2).
        - move=> p v n Hpr Hpw. case: p Hpr Hpw => [r|w] Hpr Hpw.
          + have Hrr2 : r != r2 by apply/eqP => Hc; apply: Hpr; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdb) setmE (negbTE Hrr2) (updm_set Hupda) setmE.
            case: (r =P r1) => [Er1|_].
            * subst r. rewrite Ha1w /= ST /= R1W. by [].
            * by [].
          + have Hww1 : w != w1 by apply/eqP => Hc; apply: Hpw; rewrite Hc.
            rewrite /cap_at -Hfin2 -HstcE /= (updm_set Hupdc) setmE (negbTE Hww1). by [].
        - exact: Hcap. }
    - (* jump *)
      move: NEXT. rewrite /next_state_updates_and_pc /next_state.
      case Hevi: (evi s) => [evinp|] //=.
      case Hpc': (mem s w) => [ni|]; rewrite /=; move=> Hgoal;
        ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
          case: ov_ev Htr Hk => ov ev Htr Hk;
          case: (obind_inv Hk) => st0 [Hndsu Hfin];
          move: Hfin => [= Hst Hev]; subst s';
          (have Htrov := jump_transfer Htr Hev); rewrite Htrov in Hndsu;
          (have HRA : regs s ra = Some (rav @ rat) by (rewrite ST; exact: RA));
          (have HRWj : regs s r = Some (w @ t1) by (rewrite ST; exact: RW));
          (have HCL : reg_clear_list (regs s) t1 = Some l by (rewrite ST; exact: CLEAR));
          (have Hjd := jump_do_updates_result HRA HRWj HCL);
          (have Hss : Some st0 = Some s by (rewrite -Hndsu; exact: Hjd));
          move: Hss => [= ->];
          apply: (cap_subset _ _ Hcap);
            [ by move=> w0 v t n0; rewrite /= | by move=> r0 v n0; rewrite /= ] ).
    - (* bnz *)
      move: NEXT. rewrite /next_state_updates_and_pc /next_state.
      case Hevi: (evi s) => [evinp|] //=.
      case Hpc'2: (mem s pc') => [ni|]; rewrite /=; move=> Hgoal;
        ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
          case: ov_ev Htr Hk => ov ev Htr Hk;
          have Htrov := bnz_transfer Htr; rewrite Htrov in Hk;
          case: (obind_inv Hk) => st0 [Hndsu Hfin];
          move: Hfin => [= Hst _]; subst s';
          move: Hndsu; rewrite /= => Hndsu;
          case: (obind_inv Hndsu) => st1 [Hndsu1 Hrest]; move: Hrest => [= Hr1];
          case: (obind_inv Hndsu1) => a [Ha Hndsu2];
          case: (obind_inv Hndsu2) => rg' [Hupd Hr2]; move: Hr2 => [= Hr2];
          (have Haw : a = w @ t1 by (move: (Ha); rewrite ST /= RW; move=> [= <-]));
          apply: (cap_subset _ _ Hcap);
            [ by move=> w0 v t n0; rewrite /= -Hr1 -Hr2 /=
            | move=> r0 v n0; rewrite /= -Hr1 -Hr2 /= (updm_set Hupd) setmE;
              case: eqP => [Heq|Hne];
                [ subst r0; rewrite Ha Haw /=; move=> Hpre; exact: Hpre
                | move=> Hpre; exact: Hpre ] ] ).
    - (* jal *)
      move: NEXT. rewrite /next_state_updates_and_pc /next_state.
      case Hevi: (evi s) => [evinp|] //=.
      case Hpc': (mem s (swcast imm)) => [ni|]; rewrite /=; move=> Hgoal;
        ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
          case: ov_ev Htr Hk => ov ev Htr Hk;
          case: (obind_inv Hk) => st0 [Hndsu Hfin];
          move: Hfin => [= Hst Hev]; subst s';
          (have Htrov := jal_transfer Htr Hev); rewrite Htrov in Hndsu;
          (have HmemRA : mem s (pc0 + 1)%w = Some (vret @ tret) by (rewrite ST; exact: RA));
          (have Ha4 : regs s (as_word (ssrint.Posz 4)) = Some (old @ told) by (rewrite ST; exact: OLD));
          (have HCL : reg_clear_list (regs s) told = Some l by (rewrite ST; exact: CLEAR));
          (have Hjd := jal_do_updates_result HmemRA Ha4 HCL);
          (have Hstep1 : next_state_do_update s (InternalJump : tag_type lrc_tags R)
             (RegWrite (as_word (ssrint.Posz 4)) (pc0 + 1)%w) = Some st0
             by (rewrite -Hjd; exact: Hndsu));
          move: Hstep1; rewrite /= => Hstep1;
          case: (obind_inv Hstep1) => regs' [Hupd Hst0];
          move: Hst0 => [= Hst0]; subst st0;
          apply: (cap_subset _ _ Hcap);
            [ by move=> w0 v t n0; rewrite /=
            | move=> r0 v n0; rewrite /= (updm_set Hupd) setmE;
              case: eqP => [_|_]; [ by move=> [= _ Hc]; discriminate Hc | by [] ] ] ).
    - (* syscall *)
      have Halloc := run_syscall_alloc GETCALL CALL.
      have [Hmem Hreg] := alloc_fun_cap Halloc.
      apply: (cap_subset _ _ Hcap); [ exact: Hmem | exact: Hreg ].
  Qed.

End SilentCap.

(* ==================== silent pc-tag preservation ==================== *)

(* A silent transfer keeps the pc tag (both event branches produce Some). *)
Lemma transfer_silent_trpc :
  forall (op : opcode) (tpc : tag_type lrc_tags Symbolic.P)
         (ti : tag_type lrc_tags Symbolic.M)
         (ts : hseq (tag_type lrc_tags) (inputs op))
         (tni : option (tag_type lrc_tags Symbolic.M))
         (evinp : ev_inputs) (ov : ovec lrc_tags op) (ev : option event),
    LRC.transfer (IVec (OP op) tpc ti ts tni) evinp = Some (ov, ev) ->
    ev = None ->
    trpc ov = tpc.
Proof.
  move=> op tpc ti ts tni evinp ov ev.
  rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'.
  move: ts ov; case: op => [|||b||||||||||] ts ov; cbv zeta; move=> H Hev.
  - rewrite (hseq0 ts) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    by move: H => [= <- _].
  - rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    by move: H => [= <- _].
  - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts))
            (hseq0 (hsbehead (hsbehead ts))) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    by move: H => [= <- _].
  - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts))
            (hseq_eta (hsbehead (hsbehead ts)))
            (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => u3 [_ {}H].
    by move: H => [= <- _].
  - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts))
            (hseq_eta (hsbehead (hsbehead ts)))
            (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => u2 [_ {}H]. move: H. case: ifP => // _ H.
    move: H. case E: (switch_val _ _) => [a c] /=. by move=> [= <- _].
  - rewrite (hseq_eta ts) (hseq_eta (hsbehead ts))
            (hseq_eta (hsbehead (hsbehead ts)))
            (hseq0 (hsbehead (hsbehead (hsbehead ts)))) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => u3 [_ {}H].
    move: H. case: ifP => // _ H.
    move: H. case E: (switch_val _ _) => [a c] /=. by move=> [= <- _].
  - (* jump *)
    rewrite (hseq_eta ts) (hseq_eta (hsbehead ts))
            (hseq_eta (hsbehead (hsbehead ts))) in H.
    case: (obind_inv H) => u0 [_ {}H].
    move: H. case Hbel: (belong _ _) => H.
    + case: (obind_inv H) => u1 [_ {}H]. by move: H => [= <- _].
    + case: (obind_inv H) => u1 [_ {}H].
      case: (obind_inv H) => c' [_ {}H].
      case: (obind_inv H) => u3 [_ {}H]. move: H => [= _ Hc].
      move: Hev. by rewrite -Hc.
  - rewrite (hseq_eta ts) (hseq0 (hsbehead ts)) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => u2 [_ {}H]. by move: H => [= <- _].
  - (* jal *)
    rewrite (hseq_eta ts) (hseq_eta (hsbehead ts))
            (hseq_eta (hsbehead (hsbehead ts))) in H.
    case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
    move: H. case Hbel: (belong _ _) => H.
    + by move: H => [= <- _].
    + case: (obind_inv H) => u2 [_ {}H].
      case: (obind_inv H) => c' [Hgtc {}H].
      case: (obind_inv H) => u3 [Hce {}H]. move: H => [= _ Hc].
      exfalso. move: Hgtc Hce Hc Hev {Hbel}. case: tni => [cell|] //=.
      case: cell => [vc cc [[p ll]|] bc] //=.
      move=> _ _ Hc Hev. rewrite -Hc in Hev. discriminate Hev.
  - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
  - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
  - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
  - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
  - by case: (obind_inv H) => u0 [_ H1]; discriminate H1.
Qed.

(* the allocator keeps the pc tag and every existing memory cell *)
Lemma alloc_taga_pc : forall (N : nat) (s s' : state),
  alloc_fun (NC:=N) s = Some s' -> taga (pc s') = taga (pc s).
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
  move: H => [= HSt]. subst s'. by [].
Qed.

Lemma alloc_mem_incl : forall (N : nat) (s s' : state),
  alloc_fun (NC:=N) s = Some s' ->
  forall w d, mem s w = Some d -> mem s' w = Some d.
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
  move=> w d Hw /=. by rewrite unionmE Hw.
Qed.

(* ==================== the bracketing invariant ==================== *)

(* address [v] holds a [C]-coloured cell *)
Definition points_to_col
    (m : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags Symbolic.M)})
    (v : mword mt) (C : Component.id) : Prop :=
  exists iv tn, m v = Some (iv @ tn) /\ color tn = C.

(* the single-run shadow stack: one entry (cap value, caller colour) per
   level, most-recent-first (mirroring [Traces.callers]) *)
Definition sstack : Type := seq (mword mt * Component.id).

Definition sstack_pts
    (m : {fmap mword mt -> atom (mword mt) (tag_type lrc_tags Symbolic.M)})
    (st : sstack) : Prop :=
  forall e, e \in st -> points_to_col m e.1 e.2.

(* the level-[n] entry sits at position [size st - n.+1] *)
Definition s_in_stack (st : sstack) (v : mword mt) (n : nat) : Prop :=
  n < size st /\ (nth (as_word 0, 0%nat) st (size st - n.+1)).1 = v.

(* the machine's register keys: [ra] plus the clear list *)
Definition regdomm_ok (s : state) : Prop :=
  forall r0, r0 \in domm (regs s) ->
    (r0 == ra) || (r0 \in [seq (as_word (ssrint.Posz n) : reg mt) | n <- reg_list]).

(* the machine state realizes the trace-side [stack_state]: the pc level
   is the call depth, the recorded caller colours are [callers], every
   recorded value points at a cell of the recorded colour, and the Ret
   capabilities are exactly (at most one each) the recorded values *)
Definition bracket_inv (ss : stack_state) (s : state) : Prop :=
  exists st : sstack,
    [/\ taga (pc s) = Level (size st) (cur_comp ss),
        map snd st = callers ss,
        sstack_pts (mem s) st,
        cap_correct_gen (s_in_stack st) s
      & regdomm_ok s ].

Section BracketSilent.

  Variable NC : nat.

  Lemma silent_step_tpc : forall (s s' : state),
    step_mp (NC:=NC) s s' None -> taga (pc s') = taga (pc s).
  Proof.
    move=> s s' Hstep. inversion Hstep.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [_ [_ Hpcs]]]]]] := nsuap_inv NEXT.
      rewrite Hpcs ST /=. exact: (transfer_silent_trpc Htr (erefl _)).
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [_ [_ Hpcs]]]]]] := nsuap_inv NEXT.
      rewrite Hpcs ST /=. exact: (transfer_silent_trpc Htr (erefl _)).
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [_ [_ Hpcs]]]]]] := nsuap_inv NEXT.
      rewrite Hpcs ST /=. exact: (transfer_silent_trpc Htr (erefl _)).
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [_ [_ Hpcs]]]]]] := nsuap_inv NEXT.
      rewrite Hpcs ST /=. exact: (transfer_silent_trpc Htr (erefl _)).
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [_ [_ Hpcs]]]]]] := nsuap_inv NEXT.
      rewrite Hpcs ST /=. exact: (transfer_silent_trpc Htr (erefl _)).
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [_ [_ Hpcs]]]]]] := nsuap_inv NEXT.
      rewrite Hpcs ST /=. exact: (transfer_silent_trpc Htr (erefl _)).
    - unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [_ [_ Hpcs]]]]]] := nsuap_inv NEXT.
      rewrite Hpcs ST /=. exact: (transfer_silent_trpc Htr (erefl _)).
    - unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr [_ [_ Hpcs]]]]]] := nsuap_inv NEXT.
      rewrite Hpcs ST /=. exact: (transfer_silent_trpc Htr (erefl _)).
    - unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr [_ [_ Hpcs]]]]]] := nsuap_inv NEXT.
      rewrite Hpcs ST /=. exact: (transfer_silent_trpc Htr (erefl _)).
    - have Halloc := run_syscall_alloc GETCALL CALL.
      exact: (alloc_taga_pc Halloc).
  Qed.

  (* forward cell persistence: every cell survives any step with its
     colour/entry/is_code intact *)
  Lemma step_cell_persist : forall (s s' : state) ev,
    step_mp (NC:=NC) s s' ev ->
    forall w d, mem s w = Some d ->
      exists d', mem s' w = Some d' /\ tag_shape (taga d') = tag_shape (taga d).
  Proof.
    move=> s s' ev Hstep. inversion Hstep.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem _]]]]]] := nsuap_inv NEXT.
      have Hms : mem s' = mem s.
      { rewrite Hmem. apply: ndsu_mem_noM Hdsu.
        + by (move=> w' v' Hin; cbn in Hin;
              repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
              (case: Hin || exact: (no_mw_reg_clear_read Hin))).
        + by (move=> w' Hin; cbn in Hin;
              repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
              (case: Hin || exact: (no_mr_reg_clear_read Hin))). }
      move=> w d Hd. exists d. by rewrite Hms.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem _]]]]]] := nsuap_inv NEXT.
      have Hms : mem s' = mem s.
      { rewrite Hmem. apply: ndsu_mem_noM Hdsu.
        + by (move=> w' v' Hin; cbn in Hin;
              repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
              (case: Hin || exact: (no_mw_reg_clear_read Hin))).
        + by (move=> w' Hin; cbn in Hin;
              repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
              (case: Hin || exact: (no_mr_reg_clear_read Hin))). }
      move=> w d Hd. exists d. by rewrite Hms.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem _]]]]]] := nsuap_inv NEXT.
      have Hms : mem s' = mem s.
      { rewrite Hmem. apply: ndsu_mem_noM Hdsu.
        + by (move=> w' v' Hin; cbn in Hin;
              repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
              (case: Hin || exact: (no_mw_reg_clear_read Hin))).
        + by (move=> w' Hin; cbn in Hin;
              repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
              (case: Hin || exact: (no_mr_reg_clear_read Hin))). }
      move=> w d Hd. exists d. by rewrite Hms.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem _]]]]]] := nsuap_inv NEXT.
      have Hms : mem s' = mem s.
      { rewrite Hmem. apply: ndsu_mem_noM Hdsu.
        + by (move=> w' v' Hin; cbn in Hin;
              repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
              (case: Hin || exact: (no_mw_reg_clear_read Hin))).
        + by (move=> w' Hin; cbn in Hin;
              repeat (move: Hin => [Hin|Hin]; [by discriminate|]);
              (case: Hin || exact: (no_mr_reg_clear_read Hin))). }
      move=> w d Hd. exists d. by rewrite Hms.
    - (* load *)
      rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem _]]]]]] := nsuap_inv NEXT.
      have [ta [tm [tb [Etr Esh]]]] := transfer_load_shape Htr.
      rewrite Etr in Hdsu.
      have Hcell : mem s w1 = Some (w2 @ t2) by rewrite ST.
      have Hset := ndsu_load_mem Hcell Hdsu.
      move=> w d Hd. rewrite Hmem Hset setmE.
      case: eqP => [Ew|_]; last by exists d.
      exists (w2 @ tm). split; first by [].
      move: Hd. rewrite Ew Hcell. move=> [= <-] /=.
      by rewrite Esh.
    - (* store *)
      rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr [Hdsu [Hmem _]]]]]] := nsuap_inv NEXT.
      have [ta [tb [tm [Etr Esh]]]] := transfer_store_shape Htr.
      rewrite Etr in Hdsu.
      have Hcell : mem s w1 = Some (old @ told) by rewrite ST.
      have Hset := ndsu_store_mem Hdsu.
      move=> w d Hd. rewrite Hmem Hset setmE.
      case: eqP => [Ew|_]; last by exists d.
      exists (w2 @ tm). split; first by [].
      move: Hd. rewrite Ew Hcell. move=> [= <-] /=.
      by rewrite Esh.
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
      move=> w0 d Hd. exists d. by rewrite Hms.
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
      move=> w0 d Hd. exists d. by rewrite Hms.
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
      move=> w0 d Hd. exists d. by rewrite Hms.
    - (* syscall *)
      have Halloc := run_syscall_alloc GETCALL CALL.
      move=> w d Hd. exists d. split; last by [].
      exact: (alloc_mem_incl Halloc Hd).
  Qed.

  Lemma points_to_col_persist : forall (s s' : state) ev,
    step_mp (NC:=NC) s s' ev ->
    forall v C, points_to_col (mem s) v C -> points_to_col (mem s') v C.
  Proof.
    move=> s s' ev Hstep v C [iv [tn [Hv Hcol]]].
    have [d' [Hd' Esh]] := step_cell_persist Hstep Hv.
    case: d' Hd' Esh => iv' tn' Hd' Esh.
    exists iv', tn'. split; first by [].
    move: Esh. rewrite /tag_shape /=. move=> [= E1 _ _]. by rewrite E1.
  Qed.

End BracketSilent.

(* ==================== event-step transfer extras ==================== *)

Definition pct_level (t : tag_type lrc_tags Symbolic.P) : nat :=
  match t with Level n _ => n end.

Lemma reg_clear_list_head :
  forall (rs : {fmap reg mt -> atom (mword mt) (tag_type lrc_tags Symbolic.R)})
         (top : tag_type lrc_tags Symbolic.R) l,
  reg_clear_list rs top = Some l -> hshead l = top.
Proof.
  move=> rs top l. rewrite /reg_clear_list reg_clear_list_aux_cons.
  case: (rs _) => [v|] //= H.
  case: (obind_inv H) => l'' [_ {}H].
  by move: H => [= <-].
Qed.

(* An event JUMP consumes a top-level Ret capability from the jumped-through
   register, decrements the level to the target cell's colour, and
   invalidates the register file. *)
Lemma jump_event_extra :
  forall (tpc : tag_type lrc_tags Symbolic.P) (ti : tag_type lrc_tags Symbolic.M)
         (rat : tag_type lrc_tags Symbolic.R)
         (l : hseq (tag_type lrc_tags) (nseq (size reg_list).+1 Symbolic.R))
         (tni : option (tag_type lrc_tags Symbolic.M))
         (evinp : ev_inputs) (ov : ovec lrc_tags JUMP) (e : event),
    LRC.transfer (IVec JUMP tpc ti (HSeqCons rat l) tni) evinp = Some (ov, Some e) ->
    exists n c',
      [/\ hshead l = Ret n, pct_level tpc = n.+1, get_tni_color tni = Some c',
          trpc ov = build_tpc n c'
        & tr ov = (Invalidated :: Invalidated :: Other :: reg_invalidate_hseq)%hseq ].
Proof.
  move=> tpc ti rat l tni evinp ov e.
  rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. cbv zeta.
  rewrite (hseq_eta l) (hseq_eta (hsbehead l)) /=. move=> H.
  case: (obind_inv H) => u0 [_ {}H].
  move: H. case Hbel: (belong _ _) => H.
  - case: (obind_inv H) => u1 [_ {}H]. by move: H => [=].
  - case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => c' [Hc' {}H].
    case: (obind_inv H) => u3 [Hcr {}H]. move: H => [= Hov He].
    move: Hcr. rewrite /check_ret. case Ehd: (hshead l) => [n'|||] //.
    case: ifP => // /eqP Elev _.
    exists n', c'. split.
    + by [].
    + exact: Elev.
    + exact: Hc'.
    + by rewrite -Hov Elev /=.
    + by rewrite -Hov.
Qed.

(* An event JAL mints exactly one Ret capability (index = the current
   level) in the [ra] slot, increments the level to the target cell's
   colour, checks the return cell's colour against the running component,
   and invalidates the rest of the register file. *)
Lemma jal_event_extra :
  forall (tpc : tag_type lrc_tags Symbolic.P) (ti : tag_type lrc_tags Symbolic.M)
         (tret : tag_type lrc_tags Symbolic.M)
         (l : hseq (tag_type lrc_tags) (nseq (size reg_list).+1 Symbolic.R))
         (tni : option (tag_type lrc_tags Symbolic.M))
         (evinp : ev_inputs) (ov : ovec lrc_tags JAL) (e : event),
    LRC.transfer (IVec JAL tpc ti (HSeqCons tret l) tni) evinp = Some (ov, Some e) ->
    exists c',
      [/\ get_tni_color tni = Some c',
          color tret = pct_comp tpc,
          trpc ov = build_tpc (pct_level tpc).+1 c'
        & tr ov = (tret :: Ret (pct_level tpc) :: Other :: reg_invalidate_hseq)%hseq ].
Proof.
  move=> tpc ti tret l tni evinp ov e.
  rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. cbv zeta.
  rewrite (hseq_eta l) (hseq_eta (hsbehead l)) /=. move=> H.
  case: (obind_inv H) => u0 [Hcc {}H].
  move: Hcc; case: eqP => [Ecur _|//].
  case: (obind_inv H) => u1 [Hcb {}H].
  move: H. case Hbel: (belong _ _) => H.
  - by move: H => [=].
  - case: (obind_inv H) => u2 [_ {}H].
    case: (obind_inv H) => c' [Hc' {}H].
    case: (obind_inv H) => u3 [Hce {}H].
    move: H => [= Hov He].
    exists c'. split.
    + exact: Hc'.
    + rewrite -(check_belong_color Hcb). by rewrite Ecur.
    + by rewrite -Hov /=.
    + by rewrite -Hov.
Qed.

(* ==================== register invalidation at events ==================== *)

(* "no tag in this all-R hseq is a Ret capability" *)
Fixpoint all_nonret (tks : seq tag_kind) : hseq (tag_type lrc_tags) tks -> Prop :=
  match tks with
  | [::] => fun _ => True
  | tk :: tks' => fun h =>
      (match tk return tag_type lrc_tags tk -> Prop with
       | Symbolic.R => fun t => forall n, t <> Ret n
       | _ => fun _ => True
       end) (hshead h) /\ all_nonret (hsbehead h)
  end.

Lemma nsdu_regread_nonret_step : forall (st st1 : state) (t : tag_type lrc_tags Symbolic.R) k,
  (forall n, t <> Ret n) ->
  next_state_do_update st t (RegRead k) = Some st1 ->
  mem st1 = mem st /\
  (forall r0 v n, regs st1 r0 = Some (v @ (Ret n)) ->
     regs st r0 = Some (v @ (Ret n)) /\ r0 <> k).
Proof.
  move=> st st1 t k Hnr H. move: H. rewrite /next_state_do_update /=.
  case Ha: (regs st k) => [a|] //=.
  case Hupd: (updm (regs st) k _) => [rg'|] //=.
  move=> [= Hst1].
  have Hr : regs st1 = setm (regs st) k ((vala a) @ t)
    by rewrite -Hst1 /= (updm_set Hupd).
  split; first by rewrite -Hst1.
  move=> r0 v n. rewrite Hr setmE. case: eqP => [Heq|Hne].
  - move=> [= _ Hc]. exfalso. exact: (Hnr n Hc).
  - move=> Hg. by split.
Qed.

(* a fold of RegReads with non-Ret tags: memory untouched, and every
   surviving Ret capability was already there, outside the written keys *)
Lemma ndsu_regreads_nonret : forall (ks : seq (reg mt))
    (tags : hseq (tag_type lrc_tags) (nseq (size ks) Symbolic.R)) (st st0 : state),
  all_nonret tags ->
  next_state_do_updates st tags [seq RegRead k | k <- ks] = Some st0 ->
  mem st0 = mem st /\
  (forall r0 v n, regs st0 r0 = Some (v @ (Ret n)) ->
     regs st r0 = Some (v @ (Ret n)) /\ r0 \notin ks).
Proof.
  elim => [|k ks IH] tags st st0 Hnr /=.
  - move=> [<-]. split; first by []. move=> r0 v n Hg. by split.
  - move=> H.
    case: (obind_inv H) => st1 [H1 {}H].
    case: Hnr => Hnr1 Hnrs.
    have [Hm1 Hc1] := nsdu_regread_nonret_step Hnr1 H1.
    have [Hm2 Hc2] := IH (hsbehead tags) st1 st0 Hnrs H.
    split; first by rewrite Hm2 Hm1.
    move=> r0 v n Hg.
    have [Hg1 Hnk] := Hc2 r0 v n Hg.
    have [Hg0 Hne] := Hc1 r0 v n Hg1.
    split; first exact: Hg0.
    rewrite in_cons negb_or Hnk andbT. by apply/eqP.
Qed.

Lemma reg_clear_read_map :
  reg_clear_read
  = [seq RegRead k | k <- [seq (as_word (ssrint.Posz n) : reg mt) | n <- reg_list]].
Proof. by rewrite /reg_clear_read -map_comp. Qed.

Lemma reg_invalidate_nonret :
  all_nonret (((Other : tag_type lrc_tags Symbolic.R) :: reg_invalidate_hseq)%hseq
              : hseq (tag_type lrc_tags) (nseq 11 Symbolic.R)).
Proof. by do !split. Qed.

(* ==================== full nsuap inversion (with registers) ==================== *)

Lemma nsuap_inv_full : forall (st s' : state) (op : opcode) tpc ti
    (ts : hseq (tag_type lrc_tags) (inputs op)) updts pc' ev,
  @next_state_updates_and_pc mt ops lrc_tags LRC.transfer unit st
    (IVec (OP op) tpc ti ts) updts pc' = Some (s', ev) ->
  exists evinp ov0 st0,
    [/\ LRC.transfer (IVec (OP op) tpc ti ts
          (match mem st pc' with Some ni => Some (taga ni) | None => None end))
          evinp
          = Some (ov0, ev),
        next_state_do_updates st (tr ov0) updts = Some st0,
        mem s' = mem st0, regs s' = regs st0 & pc s' = pc'@(trpc ov0)].
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
    split; [exact: Htr | exact: Edsu | by [] | by [] | by []].
  - case Htr: (LRC.instr_rules_mp evinp op tpc ti ts None) => [ov_ev|] //=.
    case: ov_ev Htr => ov0 ev0 Htr /=.
    case Edsu: (next_state_do_updates st (tr ov0) updts) => [st0|] //=.
    move=> [= Hs Hev]. subst s'. rewrite Hev in Htr.
    exists evinp, ov0, st0. cbn.
    split; [exact: Htr | exact: Edsu | by [] | by [] | by []].
Qed.

(* ==================== register-domain machinery ==================== *)

Lemma alloc_regs_domm : forall (N : nat) (s s' : state),
  alloc_fun (NC:=N) s = Some s' -> domm (regs s') = domm (regs s).
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
  move: H => [= HSt]. subst s'. exact: (updm_domm_eq Hregs').
Qed.

Section RegDomm.

  Variable NC : nat.

  Lemma step_regs_domm_any : forall (s s' : state) ev,
    step_mp (NC:=NC) s s' ev -> domm (regs s') = domm (regs s).
  Proof.
    move=> s s' ev Hstep. inversion Hstep.
    all: try (rewrite /next_state_updates in NEXT).
    all: try (unfold mvec in NEXT).
    all: try (have [evinp [ov0 [st0 [_ Hdsu _ Hr _]]]] := nsuap_inv_full NEXT;
              rewrite Hr; exact: (next_state_do_updates_regs_domm Hdsu)).
    have Halloc := run_syscall_alloc GETCALL CALL.
    exact: (alloc_regs_domm Halloc).
  Qed.

  Lemma step_regdomm_ok : forall (s s' : state) ev,
    step_mp (NC:=NC) s s' ev -> regdomm_ok s -> regdomm_ok s'.
  Proof.
    move=> s s' ev Hstep Hdom r0.
    rewrite (step_regs_domm_any Hstep). exact: Hdom.
  Qed.

End RegDomm.

(* ==================== emitted-event shapes per opcode ==================== *)

Lemma nop_emit : forall tpc (ti : tag_type lrc_tags Symbolic.M) tni evinp
    (ov : ovec lrc_tags NOP) ev,
  LRC.transfer (IVec NOP tpc ti [hseq] tni) evinp = Some (ov, ev) -> ev = None.
Proof.
  move=> tpc ti tni evinp ov ev. rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. cbv zeta => H.
  case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
  by move: H => [= _ <-].
Qed.

Lemma const_emit : forall tpc (ti : tag_type lrc_tags Symbolic.M)
    (told : tag_type lrc_tags Symbolic.R) tni evinp (ov : ovec lrc_tags CONST) ev,
  LRC.transfer (IVec CONST tpc ti [hseq told] tni) evinp = Some (ov, ev) -> ev = None.
Proof.
  move=> tpc ti told tni evinp ov ev. rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. cbv zeta => H.
  case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
  by move: H => [= _ <-].
Qed.

Lemma mov_emit : forall tpc (ti : tag_type lrc_tags Symbolic.M)
    (t1 told : tag_type lrc_tags Symbolic.R) tni evinp (ov : ovec lrc_tags MOV) ev,
  LRC.transfer (IVec MOV tpc ti [hseq t1; told] tni) evinp = Some (ov, ev) -> ev = None.
Proof.
  move=> tpc ti t1 told tni evinp ov ev. rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. cbv zeta => H.
  case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
  by move: H => [= _ <-].
Qed.

Lemma binop_emit : forall b tpc (ti : tag_type lrc_tags Symbolic.M)
    (t1 t2 told : tag_type lrc_tags Symbolic.R) tni evinp
    (ov : ovec lrc_tags (BINOP b)) ev,
  LRC.transfer (IVec (BINOP b) tpc ti [hseq t1; t2; told] tni) evinp = Some (ov, ev) -> ev = None.
Proof.
  move=> b tpc ti t1 t2 told tni evinp ov ev. rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. cbv zeta => H.
  case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
  case: (obind_inv H) => u2 [_ {}H]. case: (obind_inv H) => u3 [_ {}H].
  by move: H => [= _ <-].
Qed.

Lemma bnz_emit : forall tpc (ti : tag_type lrc_tags Symbolic.M)
    (t1 : tag_type lrc_tags Symbolic.R) tni evinp (ov : ovec lrc_tags BNZ) ev,
  LRC.transfer (IVec BNZ tpc ti [hseq t1] tni) evinp = Some (ov, ev) -> ev = None.
Proof.
  move=> tpc ti t1 tni evinp ov ev. rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. cbv zeta => H.
  case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
  case: (obind_inv H) => u2 [_ {}H].
  by move: H => [= _ <-].
Qed.

Lemma jump_event_eret :
  forall tpc (ti : tag_type lrc_tags Symbolic.M) (rat : tag_type lrc_tags Symbolic.R)
         (l : hseq (tag_type lrc_tags) (nseq (size reg_list).+1 Symbolic.R))
         tni evinp (ov : ovec lrc_tags JUMP) (e : event),
  LRC.transfer (IVec JUMP tpc ti (HSeqCons rat l) tni) evinp = Some (ov, Some e) ->
  exists c v c', e = ERet c v c'.
Proof.
  move=> tpc ti rat l tni evinp ov e.
  rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. cbv zeta.
  rewrite (hseq_eta l) (hseq_eta (hsbehead l)) /=. move=> H.
  case: (obind_inv H) => u0 [_ {}H].
  move: H. case Hbel: (belong _ _) => H.
  - case: (obind_inv H) => u1 [_ {}H]. by move: H => [=].
  - case: (obind_inv H) => u1 [_ {}H].
    case: (obind_inv H) => c' [_ {}H].
    case: (obind_inv H) => u3 [_ {}H]. move: H => [= _ He].
    do 3 eexists. by rewrite -He.
Qed.

Lemma jal_event_ecall :
  forall tpc (ti : tag_type lrc_tags Symbolic.M) (tret : tag_type lrc_tags Symbolic.M)
         (l : hseq (tag_type lrc_tags) (nseq (size reg_list).+1 Symbolic.R))
         tni evinp (ov : ovec lrc_tags JAL) (e : event),
  LRC.transfer (IVec JAL tpc ti (HSeqCons tret l) tni) evinp = Some (ov, Some e) ->
  exists c p v c', e = ECall c p v c'.
Proof.
  move=> tpc ti tret l tni evinp ov e.
  rewrite /LRC.transfer /LRC.instr_rules_mp.
  case: tpc => level current'. cbv zeta.
  rewrite (hseq_eta l) (hseq_eta (hsbehead l)) /=. move=> H.
  case: (obind_inv H) => u0 [_ {}H]. case: (obind_inv H) => u1 [_ {}H].
  move: H. case Hbel: (belong _ _) => H.
  - by move: H => [=].
  - case: (obind_inv H) => u2 [_ {}H].
    case: (obind_inv H) => c' [_ {}H].
    case: (obind_inv H) => u3 [_ {}H]. move: H => [= _ He].
    move: He. case Hpn: (get_proc_name tni) => [p|] //=.
    move=> [= He].
    do 4 eexists. by rewrite -He.
Qed.

(* ==================== invariant preservation: silent steps ==================== *)

Section BracketSilentFull.

  Variable NC : nat.

  Lemma bracket_inv_silent : forall (ss : stack_state) (s s' : state),
    step_mp (NC:=NC) s s' None ->
    bracket_inv ss s -> bracket_inv ss s'.
  Proof.
    move=> ss s s' Hstep [st [Hpc Hmap Hpts Hcap Hdom]].
    exists st. split.
    - by rewrite (silent_step_tpc Hstep).
    - exact: Hmap.
    - move=> e He. exact: (points_to_col_persist Hstep (Hpts e He)).
    - exact: (lrc_silent_capQ Hstep Hcap).
    - exact: (step_regdomm_ok Hstep Hdom).
  Qed.

End BracketSilentFull.

(* ==================== invariant transformation: event steps ==================== *)

Lemma jump_inval_nonret :
  all_nonret (((Invalidated : tag_type lrc_tags Symbolic.R)
                 :: Invalidated :: Other :: reg_invalidate_hseq)%hseq
              : hseq (tag_type lrc_tags) (nseq 13 Symbolic.R)).
Proof. by do !split. Qed.

Section BracketEvents.

  Variable NC : nat.

  (* the register keys rewritten by the event update lists *)
  Local Notation clear_ks :=
    ([seq (as_word (ssrint.Posz n1) : reg mt) | n1 <- reg_list]).
  Local Notation jump_ks r := ([:: ra, r & clear_ks]).

  (* An ERet event pops the shadow stack: the machine's target component is
     forced (by the consumed linear capability) to be the top caller. *)
  Lemma bracket_inv_ret : forall (ss : stack_state) (s s' : state) C v C',
    step_mp (NC:=NC) s s' (Some (ERet C v C')) ->
    bracket_inv ss s ->
    cur_comp ss = C /\
    exists tail, callers ss = C' :: tail /\ bracket_inv (StackState C' tail) s'.
  Proof.
    move=> ss s s' C v C' Hstep [st [Hpc Hmap Hpts Hcap Hdom]].
    inversion Hstep.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _ _ _ _]]]] := nsuap_inv_full NEXT.
      have Hev := nop_emit Htr. discriminate Hev.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _ _ _ _]]]] := nsuap_inv_full NEXT.
      have Hev := const_emit Htr. discriminate Hev.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _ _ _ _]]]] := nsuap_inv_full NEXT.
      have Hev := mov_emit Htr. discriminate Hev.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _ _ _ _]]]] := nsuap_inv_full NEXT.
      have Hev := binop_emit Htr. discriminate Hev.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _ _ _ _]]]] := nsuap_inv_full NEXT.
      have [Hev _] := load_transfer Htr. discriminate Hev.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _ _ _ _]]]] := nsuap_inv_full NEXT.
      have [Hev _] := store_transfer Htr. discriminate Hev.
    - (* jump: the ERet case *)
      unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr Hdsu Hm Hr Hpcs]]]] := nsuap_inv_full NEXT.
      have [tn [Htni Hcur Hnext Hneq _]] := transfer_event_facts Htr.
      have [n [c' [Ehd Elev Hgtc Htrpc Htrov]]] := jump_event_extra Htr.
      have Etpc : tpc0 = Level (size st) (cur_comp ss).
      { move: Hpc. by rewrite ST /=. }
      have HC : cur_comp ss = C.
      { move: Hcur. rewrite Etpc /=. by move=> ->. }
      have Et1 : t1 = Ret n.
      { by rewrite -(reg_clear_list_head CLEAR) Ehd. }
      have Hcapr : cap_at s (inl r) w n.
      { by rewrite /cap_at ST /= RW Et1. }
      have [Hin Huniq] := cap_correct_to_cap_at Hcap Hcapr.
      case: Hin => Hnlt Hnth.
      have Esz : size st = n.+1.
      { move: Elev. rewrite Etpc /=. by []. }
      (* the stack is nonempty; its head is the consumed capability *)
      case: st Hpc Hmap Hpts Hcap Hnlt Hnth Esz Etpc
        => [|[wtop Ctop] st'] //= Hpc Hmap Hpts Hcap Hnlt Hnth Esz Etpc.
      have Esz' : size st' = n by move: Esz => [=].
      have E0 : ((size st').+1 - n.+1)%N = 0%N by lia.
      rewrite E0 /= in Hnth. subst wtop.
      have Hpt := Hpts (w, Ctop) (mem_head _ _).
      case: Hpt => iv0 [tn0 [Hcell Hcol0]].
      have Ecol : color tn = Ctop.
      { move: Htni. rewrite Hcell /=. move=> [= <-]. exact: Hcol0. }
      have EC' : C' = Ctop.
      { rewrite -Ecol. exact: Hnext. }
      have Egtc : c' = Ctop.
      { move: Hgtc. rewrite Hcell. cbn [taga]. rewrite get_tni_color_eq.
        move=> [= <-]. exact: Hcol0. }
      (* memory and registers after the step *)
      rewrite Htrov in Hdsu.
      have [Hmem0 Hnoret] := ndsu_regreads_nonret
        (ks := jump_ks r) jump_inval_nonret Hdsu.
      have Hms : mem s' = mem s by rewrite Hm Hmem0.
      have Hnoreg : forall r0 v0 n0, ~ cap_at s' (inl r0) v0 n0.
      { move=> r0 v0 n0 Hp. rewrite /cap_at Hr in Hp.
        have [Hg0 Hnk] := Hnoret r0 v0 n0 Hp.
        have Hdm : r0 \in domm (regs s) by rewrite mem_domm Hg0.
        move: (Hdom r0 Hdm) => /orP [/eqP Era | Hinl].
        - move: Hnk. by rewrite Era !in_cons eqxx.
        - move: Hnk => /negP Hnk. apply: Hnk.
          rewrite !in_cons. apply/orP. right. apply/orP. right. exact: Hinl. }
      split; first exact: HC.
      exists (map snd st'). split.
      { by rewrite -Hmap EC' /=. }
      exists st'. split.
      + by rewrite Hpcs /= Htrpc /build_tpc Egtc EC' Esz'.
      + by [].
      + move=> e He. rewrite Hms. apply: Hpts. by rewrite in_cons He orbT.
      + apply: cap_correct_via_cap_at => v0 n0 p Hp.
        case: p Hp => [r0|w0] Hp; first by case: (Hnoreg _ _ _ Hp).
        have Hps : cap_at s (inr w0) v0 n0.
        { move: Hp. by rewrite /cap_at Hms. }
        have [Hin0 Huniq0] := cap_correct_to_cap_at Hcap Hps.
        have Hn0n : n0 <> n.
        { move=> En. subst n0. by have := Huniq (inr w0) v0 Hps. }
        case: Hin0 => Hlt0 Hnth0.
        have Hlt0' : (n0 < n)%N by move: Hlt0 Hn0n => /=; lia.
        split.
        * split; first by rewrite Esz'.
          have Eidx : (((size st').+1) - n0.+1)%N = ((size st' - n0.+1).+1)%N
            by move: Hlt0'; rewrite -Esz'; lia.
          move: Hnth0 => /=. by rewrite Eidx /=.
        * move=> p' v' Hp'.
          case: p' Hp' => [r'|w'] Hp'; first by case: (Hnoreg _ _ _ Hp').
          have Hps' : cap_at s (inr w') v' n0.
          { move: Hp'. by rewrite /cap_at Hms. }
          exact: (Huniq0 (inr w') v' Hps').
      + move=> r0. rewrite (step_regs_domm_any Hstep). exact: Hdom.
    - rewrite /next_state_updates in NEXT; unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr _ _ _ _]]]] := nsuap_inv_full NEXT.
      have Hev := bnz_emit Htr. discriminate Hev.
    - (* jal emits an ECall, not an ERet *)
      unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr _ _ _ _]]]] := nsuap_inv_full NEXT.
      have [c [p [v0 [c'0 He]]]] := jal_event_ecall Htr. discriminate He.
    - have Hev := run_syscall_event_none CALL. discriminate Hev.
  Qed.

  (* An ECall event pushes the caller onto the shadow stack: the freshly
     minted capability points back at the (colour-checked) return cell. *)
  Lemma bracket_inv_call : forall (ss : stack_state) (s s' : state) C P0 v C',
    step_mp (NC:=NC) s s' (Some (ECall C P0 v C')) ->
    bracket_inv ss s ->
    cur_comp ss = C /\
    bracket_inv (StackState C' (C :: callers ss)) s'.
  Proof.
    move=> ss s s' C P0 v C' Hstep [st [Hpc Hmap Hpts Hcap Hdom]].
    inversion Hstep.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _ _ _ _]]]] := nsuap_inv_full NEXT.
      have Hev := nop_emit Htr. discriminate Hev.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _ _ _ _]]]] := nsuap_inv_full NEXT.
      have Hev := const_emit Htr. discriminate Hev.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _ _ _ _]]]] := nsuap_inv_full NEXT.
      have Hev := mov_emit Htr. discriminate Hev.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _ _ _ _]]]] := nsuap_inv_full NEXT.
      have Hev := binop_emit Htr. discriminate Hev.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _ _ _ _]]]] := nsuap_inv_full NEXT.
      have [Hev _] := load_transfer Htr. discriminate Hev.
    - rewrite /next_state_updates in NEXT; unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _ _ _ _]]]] := nsuap_inv_full NEXT.
      have [Hev _] := store_transfer Htr. discriminate Hev.
    - (* jump emits an ERet, not an ECall *)
      unfold mvec in NEXT.
      have [evinp [ov0 [st0 [Htr _ _ _ _]]]] := nsuap_inv_full NEXT.
      have [c [v0 [c'0 He]]] := jump_event_eret Htr. discriminate He.
    - rewrite /next_state_updates in NEXT; unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr _ _ _ _]]]] := nsuap_inv_full NEXT.
      have Hev := bnz_emit Htr. discriminate Hev.
    - (* jal: the ECall case *)
      unfold mvec, pc' in NEXT.
      have [evinp [ov0 [st0 [Htr Hdsu Hm Hr Hpcs]]]] := nsuap_inv_full NEXT.
      have [tn [Htni Hcur Hnext Hneq _]] := transfer_event_facts Htr.
      have [c' [Hgtc Hcoltret Htrpc Htrov]] := jal_event_extra Htr.
      have Etpc : tpc0 = Level (size st) (cur_comp ss).
      { move: Hpc. by rewrite ST /=. }
      have HC : cur_comp ss = C.
      { move: Hcur. rewrite Etpc /=. by move=> ->. }
      case: (tni_cell Htni) => ivn Hcelln.
      have Egtc : c' = color tn.
      { move: Hgtc. rewrite Hcelln. cbn [taga]. rewrite get_tni_color_eq.
        by move=> [= <-]. }
      have EC' : C' = color tn by exact: Hnext.
      have Hretcell : mem s (pc0 + 1)%w = Some (vret @ tret) by rewrite ST.
      have Hcolret : color tret = cur_comp ss.
      { move: Hcoltret. rewrite Etpc /=. by move=> ->. }
      rewrite Etpc /= in Htrov Htrpc.
      (* peel the update chain: MemRead identity, RegWrite ra, clear *)
      rewrite Htrov in Hdsu.
      rewrite ndsu_cons in Hdsu.
      case: (obind_inv Hdsu) => st1 [H1 {}Hdsu].
      have Est1 : st1 = s.
      { have Hid := mem_read_update_id Hretcell. cbn [taga] in Hid.
        have : Some st1 = Some s by rewrite -H1; exact: Hid.
        by move=> [= ->]. }
      subst st1.
      rewrite ndsu_cons in Hdsu.
      case: (obind_inv Hdsu) => st2 [H2 {}Hdsu].
      move: H2. rewrite {1}/next_state_do_update /=. move=> H2.
      case: (obind_inv H2) => rg2 [Hupd {}H2].
      move: H2 => [= Est2].
      have Hr2 : regs st2
        = setm (regs s) ra ((pc0 + 1)%w @ (Ret (size st) : tag_type lrc_tags Symbolic.R)).
      { by rewrite -Est2 /= (updm_set Hupd). }
      have Hm2 : mem st2 = mem s by rewrite -Est2.
      have [Hmem0 Hnoret] := ndsu_regreads_nonret
        (ks := clear_ks) reg_invalidate_nonret Hdsu.
      have Hms : mem s' = mem s by rewrite Hm Hmem0 Hm2.
      (* every register capability of s' is the freshly minted one *)
      have Hcap' : forall r0 v0 n0, cap_at s' (inl r0) v0 n0 ->
        r0 = ra /\ v0 = (pc0 + 1)%w /\ n0 = size st.
      { move=> r0 v0 n0 Hp. rewrite /cap_at Hr in Hp.
        have [Hg2 Hnk] := Hnoret r0 v0 n0 Hp.
        move: Hg2. rewrite Hr2 setmE. case: eqP => [Era [= Ev En]|Hne Hg0].
        - by rewrite Era -Ev -En.
        - exfalso.
          have Hdm : r0 \in domm (regs s) by rewrite mem_domm Hg0.
          move: (Hdom r0 Hdm) => /orP [/eqP Era | Hinl].
          + by apply: Hne.
          + move: Hnk => /negP Hnk. apply: Hnk. exact: Hinl. }
      split; first exact: HC.
      exists (((pc0 + 1)%w, C) :: st). split.
      + by rewrite Hpcs /= Htrpc /build_tpc Egtc EC'.
      + by rewrite /= Hmap.
      + move=> e. rewrite in_cons => /orP [/eqP -> | He].
        * rewrite Hms /=. exists vret, tret. split; first exact: Hretcell.
          by rewrite Hcolret HC.
        * rewrite Hms. exact: (Hpts e He).
      + apply: cap_correct_via_cap_at => v0 n0 p Hp.
        case: p Hp => [r0|w0] Hp.
        * have [Era [Ev En]] := Hcap' _ _ _ Hp.
          split.
          -- split.
             ++ rewrite En /=. by rewrite ltnSn.
             ++ rewrite En Ev /=.
                have E0 : (((size st).+1) - (size st).+1)%N = 0%N by lia.
                by rewrite E0 /=.
          -- move=> p' v' Hp'.
             case: p' Hp' => [r'|w'] Hp'.
             ++ have [Era' _] := Hcap' _ _ _ Hp'. by rewrite Era Era'.
             ++ exfalso.
                have Hps' : cap_at s (inr w') v' n0.
                { move: Hp'. by rewrite /cap_at Hms. }
                have [Hin' _] := cap_correct_to_cap_at Hcap Hps'.
                case: Hin' => Hlt' _. move: Hlt'. rewrite En. by rewrite ltnn.
        * have Hps : cap_at s (inr w0) v0 n0.
          { move: Hp. by rewrite /cap_at Hms. }
          have [Hin0 Huniq0] := cap_correct_to_cap_at Hcap Hps.
          case: Hin0 => Hlt0 Hnth0.
          split.
          -- split; first by rewrite /=; lia.
             have Eidx : (((size st).+1) - n0.+1)%N = ((size st - n0.+1).+1)%N
               by lia.
             rewrite /= Eidx /=. exact: Hnth0.
          -- move=> p' v' Hp'.
             case: p' Hp' => [r'|w'] Hp'.
             ++ exfalso.
                have [_ [_ En']] := Hcap' _ _ _ Hp'.
                move: Hlt0. rewrite En'. by rewrite ltnn.
             ++ have Hps' : cap_at s (inr w') v' n0.
                { move: Hp'. by rewrite /cap_at Hms. }
                exact: (Huniq0 (inr w') v' Hps').
      + move=> r0. rewrite (step_regs_domm_any Hstep). exact: Hdom.
    - have Hev := run_syscall_event_none CALL. discriminate Hev.
  Qed.

End BracketEvents.

(* ==================== the bracketing theorem for machine runs ==================== *)

Section BracketStar.

  Variable NC : nat.

  Lemma star_bracket : forall (W : program) (s : state) tw (s' : state) (ss : stack_state),
    Star (mp_sem NC W) s tw s' ->
    bracket_inv ss s ->
    well_bracketed_trace ss tw /\ bracket_inv (run_trace ss tw) s'.
  Proof.
    move=> W s tw s' ss Hstar.
    elim: Hstar ss => [s0 ss Hinv | s1 t1 s2 t2 s3 tw0 Hstep Hstar IH Etw ss Hinv].
    - by split.
    - rewrite Etw {Etw}. move: Hstep. rewrite /= /prog_step_mp.
      case: t1 => [|e [|??]] // Hstep.
      + (* silent *)
        exact: (IH ss (bracket_inv_silent Hstep Hinv)).
      + (* event *)
        case: e Hstep => [C P0 v C'|C v C'] Hstep.
        * (* ECall *)
          have [HC Hinv'] := bracket_inv_call Hstep Hinv.
          have [Hwbt Hinv''] := IH (StackState C' (C :: callers ss)) Hinv'.
          split.
          -- rewrite /= HC eqxx /=. exact: Hwbt.
          -- exact: Hinv''.
        * (* ERet *)
          have [HC [tail0 [Hcs Hinv']]] := bracket_inv_ret Hstep Hinv.
          have [Hwbt Hinv''] := IH (StackState C' tail0) Hinv'.
          split.
          -- rewrite /= HC eqxx /= Hcs eqxx /=. exact: Hwbt.
          -- rewrite /= /run_event Hcs /=. exact: Hinv''.
  Qed.

End BracketStar.

(* ==================== full trace well-formedness ==================== *)

Section TraceWFMain.

  Variable NC : nat.

  (* Every trace of a micro-policy machine run started in a state whose
     entry tags are interface-sound and which realizes [stack_state0] is a
     well-formed trace.  (The initial-state premises are static facts about
     the loaded program, discharged for [compiler] output separately.) *)
  Lemma star_well_formed_trace :
    forall (W : program) (intf : Program.interface) (s : state) tw (s' : state),
    Star (mp_sem NC W) s tw s' ->
    entry_sound intf (mem s) ->
    bracket_inv stack_state0 s ->
    well_formed_trace intf tw.
  Proof.
    move=> W intf s tw s' Hstar Hsnd Hinv.
    rewrite /well_formed_trace.
    apply/andP. split.
    - by have [Hwbt _] := star_bracket Hstar Hinv.
    - exact: (star_events_wf Hstar Hsnd).
  Qed.

End TraceWFMain.
