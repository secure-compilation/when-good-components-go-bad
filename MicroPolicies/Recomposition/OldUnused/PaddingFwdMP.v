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

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq fintype.
From mathcomp Require Import zify.
From CoqUtils Require Import hseq word.
From extructures Require Import fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Coq.micromega.Lia.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.WordExtra.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Exec.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Utils.
Import DoNotation.
Import Types.

Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.Padding.
Require Import MicroPolicies.Recomposition.EncodeCode.
Require Import MicroPolicies.Recomposition.PaddingCorrect.
Require Import MicroPolicies.Recomposition.PaddingSim.
Import PaddingSim.
Require Import MicroPolicies.Recomposition.PaddingFwd.
Require Import MicroPolicies.Recomposition.PaddingValid.

Section CodeShiftFwdMP.

Variables q q' : program.
Local Notation pc0 := (size (@Merged.initial_memory mt (prog_buffers q))).
Local Notation padc := ((pad_code (code q) (code q')).1).
Local Notation sizes := (pad_block_sizes (code q) (code q')).

Hypothesis word_of_nat_inj : forall a b,
    a < 2 ^ (word_size mt) -> b < 2 ^ (word_size mt) ->
    @word_of_nat (word_size mt) a = word_of_nat b -> a = b.
Hypothesis Hcount  : size (proc_split (code q)) = size (proc_split (code q')).
Hypothesis Hbound  : pc0 + size (code q) < alloc_label.
Hypothesis Hbound' : pc0 + size padc < alloc_label.
Hypothesis code_tags_wf_q    : forall w a, encode_code (code q) pc0 w = Some a -> is_code (taga a).
Hypothesis code_tags_wf_padc : forall w a, encode_code padc pc0 w = Some a -> is_code (taga a).
Hypothesis fallthrough_aligned : forall n i t,
  n.+1 < size (code q) -> nth_error (code q) n = Some (i, t) -> is_term i = false ->
  shift_pos sizes (n.+1) = (shift_pos sizes n).+1.
Hypothesis code_last_term : forall n i t,
  n.+1 = size (code q) -> nth_error (code q) n = Some (i, t) -> is_term i = true.
Hypothesis bnz_labels_resolved : forall n r l t,
  nth_error (code q) n = Some (MrBnz r l, t) ->
  exists m, findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code q) = Some m.

Variable NC : nat.
Hypothesis alloc_label_lt_NC : alloc_label < 2 ^ (word_size mt - NC).
Hypothesis code_colors_bounded : forall w a,
  encode_code (code q) pc0 w = Some a -> 1 + color (taga a) < 2 ^ NC.
Hypothesis NC_lt_word : NC < word_size mt.

Local Notation st := (@Symbolic.state mt lrc_tags unit).
Local Notation match_pad  := (@PaddingSim.match_pad q q').
Local Notation pad_valid  := (@PaddingSim.pad_valid q q').

Local Notation pad_step_fwd := (@PaddingFwd.pad_step_fwd q q' word_of_nat_inj Hcount Hbound Hbound'
  code_tags_wf_q code_tags_wf_padc fallthrough_aligned code_last_term bnz_labels_resolved
  NC alloc_label_lt_NC code_colors_bounded).

Local Notation pad_valid_step := (@PaddingValid.pad_valid_step q q' NC).

Local Notation cptr_code := (@PaddingValid.cptr_code q).

Local Notation cptr_code_step := (PaddingValid.cptr_code_step Hcount Hbound Hbound' code_last_term).

Lemma merged_transfer_lrc_rev (iv : Symbolic.ivec lrc_tags) (i : Symbolic.ev_inputs)
      (r : Symbolic.vovec lrc_tags (Symbolic.op iv) * option event) :
  (let 'Symbolic.IVec vop tpc ti ts tni := iv in
     match vop as v
       return (@Symbolic.instr_tag lrc_tags v -> hseq (@Symbolic.tag_type lrc_tags) (Symbolic.vinputs v) -> Prop)
     with
     | OP STORE => fun ti ts => is_code ti = true /\ match ts with [hseq _ ; _ ; t] => is_code t = false end
     | OP LOAD  => fun ti ts => is_code ti = true /\ match ts with [hseq _ ; t ; _] => is_code t = false end
     | OP _     => fun ti _  => is_code ti = true
     | SERVICE  => fun _  _  => True
     end ti ts) ->
  LRC.transfer iv i = Some r -> Merged.transfer iv i = Some r.
Proof.
  destruct iv as [vop tpc ti ts tni]. destruct i as [rc].
  simpl in r.
  destruct vop as [op0|]; last by (move=> _; rewrite /Merged.transfer /LRC.transfer).
  rewrite /Merged.transfer /Merged.instr_rules.
  move: ts ti r; case: op0 => [|||bop||||||||||] ts ti r Hg HL;
    rewrite /LRC.transfer in HL; rewrite HL /=; clear HL.
  all: try (case: r => [a e]; case: a => [t' r']; rewrite Hg /=; by []).
  -
    move: Hg => [Hic Ht]; rewrite Hic /=.
    case: ts Ht => t0 [t1 [t2 ts]] Ht; rewrite (hseq0 ts) /= in Ht *.
    by rewrite Ht /=; case: r => [a e]; case: a => [t' r'].
  -
    move: Hg => [Hic Ht]; rewrite Hic /=.
    case: ts Ht => t0 [t1 [t2 ts]] Ht; rewrite (hseq0 ts) /= in Ht *.
    by rewrite Ht /=; case: r => [a e]; case: a => [t' r'].
Qed.

Definition merged_iv_ok (iv : Symbolic.ivec lrc_tags) : Prop :=
  let 'Symbolic.IVec vop tpc ti ts tni := iv in
     match vop as v
       return (@Symbolic.instr_tag lrc_tags v -> hseq (@Symbolic.tag_type lrc_tags) (Symbolic.vinputs v) -> Prop)
     with
     | OP STORE => fun ti ts => is_code ti = true /\ match ts with [hseq _ ; _ ; t] => is_code t = false end
     | OP LOAD  => fun ti ts => is_code ti = true /\ match ts with [hseq _ ; t ; _] => is_code t = false end
     | OP _     => fun ti _  => is_code ti = true
     | SERVICE  => fun _  _  => True
     end ti ts.

Lemma merged_transfer_lrc_loc (iv : Symbolic.ivec lrc_tags) (i : Symbolic.ev_inputs)
      (r : Symbolic.vovec lrc_tags (Symbolic.op iv) * option event) :
  Merged.transfer iv i = Some r -> LRC.transfer iv i = Some r.
Proof.
  destruct iv as [vop tpc ti ts tni]. destruct i as [rc].
  simpl in r. revert ts ti r. destruct vop as [op0|]; intros ts ti r.
  - cbn [Merged.transfer Merged.instr_rules].
    move=> H. apply obind_inv in H. destruct H as [out [Hir Hr]].
    apply obind_inv in Hir. destruct Hir as [u1 [_ Hir]].
    apply obind_inv in Hir. destruct Hir as [u2 [_ Hir]].
    apply obind_inv in Hir. destruct Hir as [o [Hlrc Ho]].
    case: o Hlrc Ho => ov0 ev0 Hlrc Ho.
    case: ov0 Hlrc Ho => t' r' Hlrc Ho.
    move: Ho => /= [= Hout]; subst out.
    move: Hr => /= [= Hr]; subst r.
    exact: Hlrc.
  - by rewrite /Merged.transfer /LRC.transfer.
Qed.

Lemma merged_transfer_lrc_eq {iv : Symbolic.ivec lrc_tags} (i : Symbolic.ev_inputs) :
  merged_iv_ok iv -> Merged.transfer iv i = LRC.transfer iv i.
Proof.
  move=> Hg. case E: (LRC.transfer iv i) => [r|].
  - by rewrite (merged_transfer_lrc_rev Hg E).
  - case Em: (Merged.transfer iv i) => [r|] //.
    by rewrite (merged_transfer_lrc_loc Em) in E.
Qed.

Lemma nsu_and_pc_bridge_rev (s : st) (kiv : Symbolic.k_ivec lrc_tags)
      (updts : seq Symbolic.update) (pc' : mword mt) (res : (st * option event)%type) :
  (forall to, merged_iv_ok (kiv to)) ->
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags LRC.transfer unit s kiv updts pc' = Some res ->
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s kiv updts pc' = Some res.
Proof.
  move=> Hok Hlrc.
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state in Hlrc *.
  case: (Symbolic.mem s pc') Hlrc => [ni|] Hlrc;
  ( apply obind_inv in Hlrc; case: Hlrc => [i [Hevi Hlrc]];
    rewrite Hevi /=; apply obind_inv in Hlrc; case: Hlrc => [ov [Htr Hk]];
    rewrite (merged_transfer_lrc_eq i (Hok _)) Htr /=; exact: Hk ).
Qed.

Lemma nsu_bridge_rev (s : st) (kiv : Symbolic.k_ivec lrc_tags)
      (updts : seq Symbolic.update) (res : (st * option event)%type) :
  (forall to, merged_iv_ok (kiv to)) ->
  @Symbolic.next_state_updates mt ops lrc_tags LRC.transfer unit s kiv updts = Some res ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit s kiv updts = Some res.
Proof. move=> Hok. exact: (nsu_and_pc_bridge_rev Hok). Qed.

Lemma run_syscall_bridge_rev (sc : Symbolic.syscall lrc_tags unit) (s : st)
      (res : (st * option event)%type) :
  @Symbolic.run_syscall mt ops lrc_tags LRC.transfer unit sc s = Some res ->
  @Symbolic.run_syscall mt ops lrc_tags Merged.transfer unit sc s = Some res.
Proof. rewrite /Symbolic.run_syscall. by case: (Symbolic.evi s) => [i|] //=. Qed.

Definition no_compromise (s : st) : Prop :=
  forall i ti, Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) ->
    is_code ti = true /\
    (forall r1 r2, decode_instr i = Some (Load r1 r2) ->
       forall w1 t1 w2 t2, Symbolic.regs s r1 = Some (w1 @ t1) ->
         Symbolic.mem s w1 = Some (w2 @ t2) -> is_code t2 = false) /\
    (forall r1 r2, decode_instr i = Some (Store r1 r2) ->
       forall w1 t1 old told, Symbolic.regs s r1 = Some (w1 @ t1) ->
         Symbolic.mem s w1 = Some (old @ told) -> is_code told = false).

Lemma step_mp_me (s s' : st) (ev : option event) :
  no_compromise s -> step_mp (NC := NC) s s' ev -> step_me (NC := NC) s s' ev.
Proof.
  move=> Hnc H. case: H.
  -  move=> mem reg pc tpc i ti extra ST PC INST mvec NEXT.
    eapply step_nop; try eassumption.
    apply: (nsu_bridge_rev _ NEXT) => to; rewrite /merged_iv_ok /=.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) by rewrite ST.
    exact: (proj1 (Hnc _ _ HPC)).
  -  move=> mem reg pc tpc i ti n r old told extra ST PC INST OLD mvec NEXT.
    eapply step_const; try eassumption.
    apply: (nsu_bridge_rev _ NEXT) => to; rewrite /merged_iv_ok /=.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) by rewrite ST.
    exact: (proj1 (Hnc _ _ HPC)).
  -  move=> mem reg pc tpc i ti r1 w1 t1 r2 old told extra ST PC INST R1W OLD mvec NEXT.
    eapply step_mov; try eassumption.
    apply: (nsu_bridge_rev _ NEXT) => to; rewrite /merged_iv_ok /=.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) by rewrite ST.
    exact: (proj1 (Hnc _ _ HPC)).
  -  move=> mem reg pc tpc i ti op r1 r2 r3 w1 w2 t1 t2 old told extra ST PC INST R1W R2W OLD mvec NEXT.
    eapply step_binop; try eassumption.
    apply: (nsu_bridge_rev _ NEXT) => to; rewrite /merged_iv_ok /=.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) by rewrite ST.
    exact: (proj1 (Hnc _ _ HPC)).
  -  move=> mem reg pc tpc i ti r1 r2 w1 w2 t1 t2 old told extra ST PC INST R1W MEM1 OLD mvec NEXT.
    eapply step_load; try eassumption.
    apply: (nsu_bridge_rev _ NEXT) => to; rewrite /merged_iv_ok /=.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) by rewrite ST.
    have HR1 : Symbolic.regs s r1 = Some (w1 @ t1) by rewrite ST.
    have HM1 : Symbolic.mem s w1 = Some (w2 @ t2) by rewrite ST.
    split; first exact: (proj1 (Hnc _ _ HPC)).
    exact: (proj1 (proj2 (Hnc _ _ HPC)) _ _ INST _ _ _ _ HR1 HM1).
  -  move=> mem reg pc i r1 r2 w1 w2 tpc ti t1 t2 old told extra ST PC INST R1W R2W OLD mvec NEXT.
    eapply step_store; try eassumption.
    apply: (nsu_bridge_rev _ NEXT) => to; rewrite /merged_iv_ok /=.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) by rewrite ST.
    have HR1 : Symbolic.regs s r1 = Some (w1 @ t1) by rewrite ST.
    have HM1 : Symbolic.mem s w1 = Some (old @ told) by rewrite ST.
    split; first exact: (proj1 (Hnc _ _ HPC)).
    exact: (proj2 (proj2 (Hnc _ _ HPC)) _ _ INST _ _ _ _ HR1 HM1).
  -  move=> mem reg pc i r w tpc ti t1 extra l rav rat ST PC INST RW RA CLEAR mvec NEXT.
    eapply step_jump; try eassumption.
    apply: (nsu_and_pc_bridge_rev _ NEXT) => to; rewrite /merged_iv_ok /=.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) by rewrite ST.
    exact: (proj1 (Hnc _ _ HPC)).
  -  move=> mem reg pc i r n w tpc ti t1 extra ST PC INST RW mvec pc' NEXT.
    eapply step_bnz; try eassumption.
    apply: (nsu_and_pc_bridge_rev _ NEXT) => to; rewrite /merged_iv_ok /=.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) by rewrite ST.
    exact: (proj1 (Hnc _ _ HPC)).
  -  move=> mem reg pc i imm tpc ti old told extra l vret tret ST PC RA INST OLD CLEAR mvec pc' NEXT.
    eapply step_jal; try eassumption.
    apply: (nsu_and_pc_bridge_rev _ NEXT) => to; rewrite /merged_iv_ok /=.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) by rewrite ST.
    exact: (proj1 (Hnc _ _ HPC)).
  -  move=> mem reg pc sc tpc extra ST PC GETCALL CALL.
    eapply step_syscall; try exact: ST; try exact: PC; try exact: GETCALL.
    exact: (run_syscall_bridge_rev CALL).
Qed.

Lemma nsu_and_pc_bridge_fwd (s : st) (kiv : Symbolic.k_ivec lrc_tags)
      (updts : seq Symbolic.update) (pc' : mword mt) (res : (st * option event)%type) :
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s kiv updts pc' = Some res ->
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags LRC.transfer unit s kiv updts pc' = Some res.
Proof.
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state.
  case: (Symbolic.mem s pc') => [ni|];
  ( move=> H; apply obind_inv in H; case: H => [i [Hevi H]];
    rewrite Hevi /=; apply obind_inv in H; case: H => [ov [Htr Hk]];
    rewrite (merged_transfer_lrc_loc Htr) /=; exact: Hk ).
Qed.

Lemma nsu_bridge_fwd (s : st) (kiv : Symbolic.k_ivec lrc_tags)
      (updts : seq Symbolic.update) (res : (st * option event)%type) :
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit s kiv updts = Some res ->
  @Symbolic.next_state_updates mt ops lrc_tags LRC.transfer unit s kiv updts = Some res.
Proof. exact: nsu_and_pc_bridge_fwd. Qed.

Lemma run_syscall_bridge_fwd (sc : Symbolic.syscall lrc_tags unit) (s : st)
      (res : (st * option event)%type) :
  @Symbolic.run_syscall mt ops lrc_tags Merged.transfer unit sc s = Some res ->
  @Symbolic.run_syscall mt ops lrc_tags LRC.transfer unit sc s = Some res.
Proof. rewrite /Symbolic.run_syscall. by case: (Symbolic.evi s) => [i|] //=. Qed.

Lemma step_me_mp_loc (s s' : st) (ev : option event) :
  step_me (NC := NC) s s' ev -> step_mp (NC := NC) s s' ev.
Proof.
  move=> H. inversion H;
    [ eapply step_nop | eapply step_const | eapply step_mov | eapply step_binop
    | eapply step_load | eapply step_store | eapply step_jump | eapply step_bnz
    | eapply step_jal | eapply step_syscall ];
    eauto using nsu_bridge_fwd, nsu_and_pc_bridge_fwd, run_syscall_bridge_fwd.
Qed.

Lemma pad_step_fwd_mp_code (s1 s2 s1' : st) (ev : option event) :
  no_compromise s1 -> match_pad s1 s2 -> pad_valid s1 -> step_mp (NC := NC) s1 s1' ev ->
  exists s2', step_mp (NC := NC) s2 s2' ev /\ match_pad s1' s2' /\ pad_valid s1'.
Proof.
  move=> Hnc Hm Hv Hstep.
  have Hme : step_me (NC := NC) s1 s1' ev := step_mp_me Hnc Hstep.
  have [s2' [Hme2 Hm']] := pad_step_fwd Hm Hv Hme.
  exists s2'; split; [exact: (step_me_mp_loc Hme2)
                     | split; [exact: Hm' | exact: (pad_valid_step Hv Hme)]].
Qed.

Lemma some_atom_inj {T : Type} {x y : mword mt} {tx ty : T} :
  Some (x @ tx) = Some (y @ ty) -> x = y /\ tx = ty.
Proof.
  move=> H; split.
  - exact: (f_equal (fun o => oapp vala x o) H).
  - exact: (f_equal (fun o => oapp taga tx o) H).
Qed.

Lemma store_transfer_not_code (tpc : Symbolic.tag_type lrc_tags Symbolic.P)
   (ti told : Symbolic.tag_type lrc_tags Symbolic.M) (t1 t2 : Symbolic.tag_type lrc_tags Symbolic.R)
   (tni : option (Symbolic.tag_type lrc_tags Symbolic.M)) (evinp : Symbolic.ev_inputs)
   (ov : Symbolic.ovec lrc_tags STORE) (ev : option event) :
  LRC.transfer (Symbolic.IVec STORE tpc ti [hseq t1; t2; told] tni) evinp = Some (ov, ev) ->
  is_code told = false.
Proof.
  rewrite /LRC.transfer /LRC.instr_rules. case: tpc => level current'. cbv zeta => H.
  case: (obind_inv H) => u0 [_ {}H].
  case: (obind_inv H) => u1 [_ {}H].
  case: (obind_inv H) => u2 [_ {}H].
  case: (obind_inv H) => u3 [_ {}H].
  case Hic: (is_code told) => //.
  by move: H; rewrite Hic /=; move=> Heq.
Qed.

Lemma load_transfer_loc (tpc : Symbolic.tag_type lrc_tags Symbolic.P) (ti : Symbolic.tag_type lrc_tags Symbolic.M)
   (tp td : Symbolic.tag_type lrc_tags Symbolic.R) (ts : Symbolic.tag_type lrc_tags Symbolic.M)
   (tni : option (Symbolic.tag_type lrc_tags Symbolic.M)) (evinp : Symbolic.ev_inputs)
   (ov : Symbolic.ovec lrc_tags LOAD) (ev : option event) :
  LRC.transfer (Symbolic.IVec LOAD tpc ti [hseq tp; ts; td] tni) evinp = Some (ov, ev) ->
  ev = None /\ Symbolic.trpc ov = tpc /\
  Symbolic.tr ov = [hseq tp;
           (switch_val ts (if is_address (vtag ts) then Invalidated else Other)).1;
           (switch_val ts (if is_address (vtag ts) then Invalidated else Other)).2].
Proof.
  rewrite /LRC.transfer /LRC.instr_rules. case: tpc => level current'. cbv zeta => H.
  case: (obind_inv H) => u0 [_ {}H].
  case: (obind_inv H) => u1 [_ {}H].
  case: (obind_inv H) => u2 [_ {}H].
  move: H. case: ifP => // _ H.
  move: H. case E: (switch_val ts (if is_address (vtag ts) then Invalidated else Other)) => [ts' td'] /=.
  move=> [= <- <-] /=. by split; [|split].
Qed.

Lemma switch_val_vtag1 (m : Symbolic.tag_type lrc_tags Symbolic.M) (v : Symbolic.tag_type lrc_tags Symbolic.R) :
  vtag (switch_val m v).1 = v.
Proof. by case: m => vt ct et bt. Qed.
Lemma switch_val_snd (m : Symbolic.tag_type lrc_tags Symbolic.M) (v : Symbolic.tag_type lrc_tags Symbolic.R) :
  (switch_val m v).2 = vtag m.
Proof. by case: m => vt ct et bt. Qed.

Lemma ndu_mem_domm (s s' : st) (tk : Symbolic.tag_kind)
      (tag : Symbolic.tag_type lrc_tags tk) (updt : Symbolic.update) :
  Symbolic.next_state_do_update s tag updt = Some s' -> domm (Symbolic.mem s') = domm (Symbolic.mem s).
Proof.
  case: tk tag => tag; rewrite /Symbolic.next_state_do_update.
  - case: updt => [r x | r | w1 w2 | w] //=.
    + by case E: (updm (Symbolic.regs s) r _) => [rs'|] //= [<-].
    + case Ea: (Symbolic.regs s r) => [a|] //=.
      by case E: (updm (Symbolic.regs s) r _) => [rs'|] //= [<-].
  - case: updt => [r x | r | w1 w2 | w] //=.
    + case E: (updm (Symbolic.mem s) w1 _) => [m'|] //= [<-] /=. exact: (Symbolic.updm_domm_eq E).
    + case Ea: (Symbolic.mem s w) => [a|] //=.
      case E: (updm (Symbolic.mem s) w _) => [m'|] //= [<-] /=. exact: (Symbolic.updm_domm_eq E).
  - by [].
Qed.

Lemma ndsu_mem_domm :
  forall (tks : seq Symbolic.tag_kind) (tags : hseq (Symbolic.tag_type lrc_tags) tks)
         (updts : seq Symbolic.update) (s0 s0' : st),
    Symbolic.next_state_do_updates s0 tags updts = Some s0' ->
    domm (Symbolic.mem s0') = domm (Symbolic.mem s0).
Proof.
  elim => [|tk tks' IH] tags updts s0 s0' /=.
  - by move=> [<-].
  - case: (ohead updts) => [updt|] //=.
    case E: (Symbolic.next_state_do_update s0 (hshead tags) updt) => [st1|] //= H.
    by rewrite (IH _ _ _ _ H) (ndu_mem_domm E).
Qed.

Local Arguments Symbolic.next_state_do_updates : simpl never.
Lemma load_nsu_lrc (s s' : st) (tpc : Symbolic.tag_type lrc_tags Symbolic.P) (ti : mem_tag)
   (r1 r2 : reg mt) (w1 w2 : mword mt) (t1 : value_tag) (t2 : mem_tag) (old : mword mt) (told : value_tag)
   (e : option event) :
  Symbolic.regs s r1 = Some (w1 @ t1) -> Symbolic.mem s w1 = Some (w2 @ t2) -> Symbolic.regs s r2 = Some (old @ told) ->
  @Symbolic.next_state_updates mt ops lrc_tags LRC.transfer unit s
    (Symbolic.IVec LOAD tpc ti [hseq t1; t2; told]) [:: Symbolic.RegRead r1; Symbolic.MemRead w1; Symbolic.RegWrite r2 w2] = Some (s', e) ->
  Symbolic.regs s' = setm (setm (Symbolic.regs s) r1 (w1 @ t1)) r2 (w2 @ (vtag t2)) /\
  exists tc, Symbolic.mem s' = setm (Symbolic.mem s) w1 (w2 @ tc) /\ is_codeptr (vtag tc) = false.
Proof.
  move=> Hr1 Hw1 Hr2.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state.
  case Hni: (Symbolic.mem s ((Symbolic.pcv s) + 1)%w) => [v1n|];
    move=> H; case: (obind_inv H) => evinp [_ {}H];
    case: (obind_inv H) => [[ov0 ev']] [Htr {}H];
    have [Hev [_ Htr3]] := load_transfer_loc Htr; subst ev';
    move: H => /= H; rewrite Htr3 in H; case: (obind_inv H) => st3 [Edu [= <- _]];
    have [Hre Hme] := load_du Edu Hr1 Hw1 Hr2;
    (split; [ by rewrite /= Hre switch_val_snd
            | exists (switch_val t2 (if is_address (vtag t2) then Invalidated else Other)).1;
              by split; [ rewrite /= Hme | rewrite switch_val_vtag1; case: (is_address (vtag t2)) ] ]).
Qed.

Definition pc_incode (s : st) : Prop :=
  forall d, Symbolic.mem s (Symbolic.pcv s) = Some d -> is_code (taga d) = true.

Lemma pc_incode_of_pos (s s2 : st) :
  match_pad s s2 -> @PaddingValid.pc_pos q s -> pc_incode s.
Proof.
  move=> Hm Hpp d Hd.
  move: Hpp; rewrite /PaddingValid.pc_pos => -[Hcr | Hnone];
    last by move: Hd; rewrite /Symbolic.pcv Hnone.
  have Hrev : forall w a, encode_code (code q) pc0 w = Some a -> Symbolic.mem s w = Some a
    by move: Hm => [_ [_ [_ [_ [_ [H _]]]]]].
  move: Hcr; rewrite /PaddingValid.in_crange => -[Hlo Hhi].
  have Hk : val (vala (Symbolic.pc s)) - pc0 < size (code q) by move: Hlo Hhi; lia.
  have Hb : pc0 + size (code q) < 2 ^ (word_size mt)
    by have := alloc_label_lt_word; move: Hbound; lia.
  have [v Hv] := PaddingSim.encode_code_dom word_of_nat_inj Hb Hk.
  have Hidx : @word_of_nat (word_size mt) ((val (vala (Symbolic.pc s)) - pc0) + pc0)
            = vala (Symbolic.pc s).
  { have -> : (val (vala (Symbolic.pc s)) - pc0) + pc0 = val (vala (Symbolic.pc s))
      by move: Hlo; lia.
    exact: valwK. }
  rewrite Hidx in Hv.
  have Hmem := Hrev _ _ Hv.
  move: Hd; rewrite /Symbolic.pcv Hmem => -[= <-].
  exact: (code_tags_wf_q Hv).
Qed.

Lemma pad_step_fwd_mp (s1 s2 s1' : st) (ev : option event) :
  match_pad s1 s2 -> pad_valid s1 -> pc_incode s1 -> step_mp (NC := NC) s1 s1' ev ->
  exists s2', step_mp (NC := NC) s2 s2' ev /\ match_pad s1' s2' /\ pad_valid s1'.
Proof.
  move=> Hm Hv Hpci Hstep. have Hcopy := Hstep. case: Hstep.
  -  move=> mem reg pc tpc i ti extra ST PC INST mvec NEXT.
    case Hic: (is_code ti); last first.
    { have Hm0 : Symbolic.mem s1 (Symbolic.pcv s1) = Some (i @ ti) by rewrite ST /= PC.
      have Hcc := Hpci _ Hm0; rewrite Hic in Hcc; discriminate Hcc. }
    have HPC : Symbolic.mem s1 (Symbolic.pcv s1) = Some (i @ ti) by rewrite ST /= PC.
    apply: (pad_step_fwd_mp_code _ Hm Hv Hcopy) => i0 ti0; rewrite HPC.
    move/some_atom_inj => [Ei Eti]; subst i0 ti0; split; first exact: Hic.
    by split=> ra rb Hd; rewrite INST in Hd; discriminate Hd.
  -  move=> mem reg pc tpc i ti n r old told extra ST PC INST OLD mvec NEXT.
    case Hic: (is_code ti); last first.
    { have Hm0 : Symbolic.mem s1 (Symbolic.pcv s1) = Some (i @ ti) by rewrite ST /= PC.
      have Hcc := Hpci _ Hm0; rewrite Hic in Hcc; discriminate Hcc. }
    have HPC : Symbolic.mem s1 (Symbolic.pcv s1) = Some (i @ ti) by rewrite ST /= PC.
    apply: (pad_step_fwd_mp_code _ Hm Hv Hcopy) => i0 ti0; rewrite HPC.
    move/some_atom_inj => [Ei Eti]; subst i0 ti0; split; first exact: Hic.
    by split=> ra rb Hd; rewrite INST in Hd; discriminate Hd.
  -  move=> mem reg pc tpc i ti r1 w1 t1 r2 old told extra ST PC INST R1W OLD mvec NEXT.
    case Hic: (is_code ti); last first.
    { have Hm0 : Symbolic.mem s1 (Symbolic.pcv s1) = Some (i @ ti) by rewrite ST /= PC.
      have Hcc := Hpci _ Hm0; rewrite Hic in Hcc; discriminate Hcc. }
    have HPC : Symbolic.mem s1 (Symbolic.pcv s1) = Some (i @ ti) by rewrite ST /= PC.
    apply: (pad_step_fwd_mp_code _ Hm Hv Hcopy) => i0 ti0; rewrite HPC.
    move/some_atom_inj => [Ei Eti]; subst i0 ti0; split; first exact: Hic.
    by split=> ra rb Hd; rewrite INST in Hd; discriminate Hd.
  -  move=> mem reg pc tpc i ti op r1 r2 r3 w1 w2 t1 t2 old told extra ST PC INST R1W R2W OLD mvec NEXT.
    case Hic: (is_code ti); last first.
    { have Hm0 : Symbolic.mem s1 (Symbolic.pcv s1) = Some (i @ ti) by rewrite ST /= PC.
      have Hcc := Hpci _ Hm0; rewrite Hic in Hcc; discriminate Hcc. }
    have HPC : Symbolic.mem s1 (Symbolic.pcv s1) = Some (i @ ti) by rewrite ST /= PC.
    apply: (pad_step_fwd_mp_code _ Hm Hv Hcopy) => i0 ti0; rewrite HPC.
    move/some_atom_inj => [Ei Eti]; subst i0 ti0; split; first exact: Hic.
    by split=> ra rb Hd; rewrite INST in Hd; discriminate Hd.
  -  move=> mem reg pc tpc i ti r1 r2 w1 w2 t1 t2 old told extra ST PC INST R1W MEM1 OLD mvec NEXT.
    case Hic: (is_code ti); last first.
    { have Hm0 : Symbolic.mem s1 (Symbolic.pcv s1) = Some (i @ ti) by rewrite ST /= PC.
      have Hcc := Hpci _ Hm0; rewrite Hic in Hcc; discriminate Hcc. }
    case Hic2: (is_code t2); first by admit.
    have HPC : Symbolic.mem s1 (Symbolic.pcv s1) = Some (i @ ti) by rewrite ST /= PC.
    have HR1 : Symbolic.regs s1 r1 = Some (w1 @ t1) by rewrite ST /= R1W.
    have HM1 : Symbolic.mem s1 w1 = Some (w2 @ t2) by rewrite ST /= MEM1.
    apply: (pad_step_fwd_mp_code _ Hm Hv Hcopy) => i0 ti0; rewrite HPC.
    move/some_atom_inj => [Ei Eti]; subst i0 ti0; split; first exact: Hic.
    split.
    + move=> ra rb Hd; move: Hd; rewrite INST => [= Era Erb]; subst ra rb.
      move=> w1' t1' w2' t2'; rewrite HR1; move/some_atom_inj => [Ew Et]; subst w1' t1'.
      rewrite HM1; move/some_atom_inj => [Ew2 Et2]; subst w2' t2'; exact: Hic2.
    + by move=> ra rb Hd; rewrite INST in Hd; discriminate Hd.
  -  move=> mem reg pc i r1 r2 w1 w2 tpc ti t1 t2 old told extra ST PC INST R1W R2W OLD mvec NEXT.
    case Hic: (is_code ti); last first.
    { have Hm0 : Symbolic.mem s1 (Symbolic.pcv s1) = Some (i @ ti) by rewrite ST /= PC.
      have Hcc := Hpci _ Hm0; rewrite Hic in Hcc; discriminate Hcc. }
    case Hic2: (is_code told).
    {
      exfalso; move: NEXT.
      rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state.
      case: (Symbolic.mem s1 _) => [ni|]; move=> H;
        ( case: (obind_inv H) => i0 [_ {}H]; case: (obind_inv H) => [[ov0 ev0]] [Htr _];
          move: (store_transfer_not_code Htr) => Hcf; rewrite Hcf in Hic2; discriminate Hic2 ). }
    have HPC : Symbolic.mem s1 (Symbolic.pcv s1) = Some (i @ ti) by rewrite ST /= PC.
    have HR1 : Symbolic.regs s1 r1 = Some (w1 @ t1) by rewrite ST /= R1W.
    have HM1 : Symbolic.mem s1 w1 = Some (old @ told) by rewrite ST /= OLD.
    apply: (pad_step_fwd_mp_code _ Hm Hv Hcopy) => i0 ti0; rewrite HPC.
    move/some_atom_inj => [Ei Eti]; subst i0 ti0; split; first exact: Hic.
    split.
    + by move=> ra rb Hd; rewrite INST in Hd; discriminate Hd.
    + move=> ra rb Hd; move: Hd; rewrite INST => [= Era Erb]; subst ra rb.
      move=> w1' t1' old' told'; rewrite HR1; move/some_atom_inj => [Ew Et]; subst w1' t1'.
      rewrite HM1; move/some_atom_inj => [Eo Eto]; subst old' told'; exact: Hic2.
  -  move=> mem reg pc i r w tpc ti t1 extra l rav rat ST PC INST RW RA CLEAR mvec NEXT.
    case Hic: (is_code ti); last first.
    { have Hm0 : Symbolic.mem s1 (Symbolic.pcv s1) = Some (i @ ti) by rewrite ST /= PC.
      have Hcc := Hpci _ Hm0; rewrite Hic in Hcc; discriminate Hcc. }
    have HPC : Symbolic.mem s1 (Symbolic.pcv s1) = Some (i @ ti) by rewrite ST /= PC.
    apply: (pad_step_fwd_mp_code _ Hm Hv Hcopy) => i0 ti0; rewrite HPC.
    move/some_atom_inj => [Ei Eti]; subst i0 ti0; split; first exact: Hic.
    by split=> ra rb Hd; rewrite INST in Hd; discriminate Hd.
  -  move=> mem reg pc i r n w tpc ti t1 extra ST PC INST RW mvec pc' NEXT.
    case Hic: (is_code ti); last first.
    { have Hm0 : Symbolic.mem s1 (Symbolic.pcv s1) = Some (i @ ti) by rewrite ST /= PC.
      have Hcc := Hpci _ Hm0; rewrite Hic in Hcc; discriminate Hcc. }
    have HPC : Symbolic.mem s1 (Symbolic.pcv s1) = Some (i @ ti) by rewrite ST /= PC.
    apply: (pad_step_fwd_mp_code _ Hm Hv Hcopy) => i0 ti0; rewrite HPC.
    move/some_atom_inj => [Ei Eti]; subst i0 ti0; split; first exact: Hic.
    by split=> ra rb Hd; rewrite INST in Hd; discriminate Hd.
  -  move=> mem reg pc i imm tpc ti old told extra l vret tret ST PC RA INST OLD CLEAR mvec pc' NEXT.
    case Hic: (is_code ti); last first.
    { have Hm0 : Symbolic.mem s1 (Symbolic.pcv s1) = Some (i @ ti) by rewrite ST /= PC.
      have Hcc := Hpci _ Hm0; rewrite Hic in Hcc; discriminate Hcc. }
    have HPC : Symbolic.mem s1 (Symbolic.pcv s1) = Some (i @ ti) by rewrite ST /= PC.
    apply: (pad_step_fwd_mp_code _ Hm Hv Hcopy) => i0 ti0; rewrite HPC.
    move/some_atom_inj => [Ei Eti]; subst i0 ti0; split; first exact: Hic.
    by split=> ra rb Hd; rewrite INST in Hd; discriminate Hd.
  -
    move=> mem reg pc sc tpc extra ST PC GETCALL CALL.
    have HPC : Symbolic.mem s1 (Symbolic.pcv s1) = None by rewrite ST /= PC.
    apply: (pad_step_fwd_mp_code _ Hm Hv Hcopy) => i0 ti0; rewrite HPC => Hd; discriminate Hd.
Admitted.

Local Notation step1L := (fun (_ : unit) s (t : trace) s' =>
  match t with [::] => step_me (NC:=NC) s s' None
             | [:: e] => step_me (NC:=NC) s s' (Some e) | _ => False end).
Local Notation step2L := (fun (_ : unit) s (t : trace) s' =>
  match t with [::] => step_mp (NC:=NC) s s' None
             | [:: e] => step_mp (NC:=NC) s s' (Some e) | _ => False end).

Lemma srUB_inv {stp stpt : unit -> st -> trace -> st -> Prop} {al : st -> Prop} {a a' : st} {t0 : trace} :
  step_restricted_UB stp stpt al tt a t0 a' ->
  (stpt tt a t0 a' /\ al a) \/ (stp tt a t0 a' /\ stpt tt a t0 a').
Proof. case=> [s0 u0 s0' H1 H2 | s0 u0 s0' H1 H2]; [left|right]; split; assumption. Qed.

Definition alloc_empty (s : st) : Prop :=
  Symbolic.mem s (@word_of_nat (word_size mt) alloc_label) = None.

Definition RL (s1 s2 : st) : Prop :=
  match_pad s1 s2 /\ pad_valid s1 /\ cptr_code s1 /\ @PaddingValid.pc_pos q s1 /\ alloc_empty s1.

Lemma no_compromise_or_load (s s' : st) (ev : option event) :
  pc_incode s -> step_mp (NC := NC) s s' ev ->
  no_compromise s \/
  (exists (tpc : Symbolic.tag_type lrc_tags Symbolic.P) (i : mword mt)
          (ti : Symbolic.tag_type lrc_tags Symbolic.M) (r1 r2 : reg mt) (w1 w2 : mword mt)
          (t1 : Symbolic.tag_type lrc_tags Symbolic.R) (t2 : Symbolic.tag_type lrc_tags Symbolic.M)
          (old : mword mt) (told : Symbolic.tag_type lrc_tags Symbolic.R),
     Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) /\
     decode_instr i = Some (Load r1 r2) /\ Symbolic.regs s r1 = Some (w1 @ t1) /\
     Symbolic.mem s w1 = Some (w2 @ t2) /\ Symbolic.regs s r2 = Some (old @ told) /\
     is_code t2 = true /\
     @Symbolic.next_state_updates mt ops lrc_tags LRC.transfer unit s
       (Symbolic.IVec LOAD tpc ti [hseq t1; t2; told])
       [:: Symbolic.RegRead r1 ; Symbolic.MemRead w1 ; Symbolic.RegWrite r2 w2 ] = Some (s', ev)).
Proof.
  move=> Hpci Hstep; case: Hstep.
  -  move=> mem reg pc tpc i ti extra ST PC INST mvec NEXT. left.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) by rewrite ST /= PC.
    move=> i0 ti0; rewrite HPC; move/some_atom_inj => [Ei Eti]; subst i0 ti0.
    split; first exact: (Hpci _ HPC).
    by split=> ra rb Hd; rewrite INST in Hd; discriminate Hd.
  -  move=> mem reg pc tpc i ti n r old told extra ST PC INST OLD mvec NEXT. left.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) by rewrite ST /= PC.
    move=> i0 ti0; rewrite HPC; move/some_atom_inj => [Ei Eti]; subst i0 ti0.
    split; first exact: (Hpci _ HPC).
    by split=> ra rb Hd; rewrite INST in Hd; discriminate Hd.
  -  move=> mem reg pc tpc i ti r1 w1 t1 r2 old told extra ST PC INST R1W OLD mvec NEXT. left.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) by rewrite ST /= PC.
    move=> i0 ti0; rewrite HPC; move/some_atom_inj => [Ei Eti]; subst i0 ti0.
    split; first exact: (Hpci _ HPC).
    by split=> ra rb Hd; rewrite INST in Hd; discriminate Hd.
  -  move=> mem reg pc tpc i ti op r1 r2 r3 w1 w2 t1 t2 old told extra ST PC INST R1W R2W OLD mvec NEXT. left.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) by rewrite ST /= PC.
    move=> i0 ti0; rewrite HPC; move/some_atom_inj => [Ei Eti]; subst i0 ti0.
    split; first exact: (Hpci _ HPC).
    by split=> ra rb Hd; rewrite INST in Hd; discriminate Hd.
  -  move=> mem reg pc tpc i ti r1 r2 w1 w2 t1 t2 old told extra ST PC INST R1W MEM1 OLD mvec NEXT.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) by rewrite ST /= PC.
    have HR1 : Symbolic.regs s r1 = Some (w1 @ t1) by rewrite ST /= R1W.
    have HM1 : Symbolic.mem s w1 = Some (w2 @ t2) by rewrite ST /= MEM1.
    have HR2 : Symbolic.regs s r2 = Some (old @ told) by rewrite ST /= OLD.
    case Hic2: (is_code t2).
    +
      right; exists tpc, i, ti, r1, r2, w1, w2, t1, t2, old, told.
      split; first exact: HPC. split; first exact: INST. split; first exact: HR1.
      split; first exact: HM1. split; first exact: HR2.
      split; first exact: Hic2. exact: NEXT.
    +
      left. move=> i0 ti0; rewrite HPC; move/some_atom_inj => [Ei Eti]; subst i0 ti0.
      split; first exact: (Hpci _ HPC). split.
      * move=> ra rb Hd; move: Hd; rewrite INST => [= Era Erb]; subst ra rb.
        move=> w1' t1' w2' t2'; rewrite HR1; move/some_atom_inj => [Ew Et]; subst w1' t1'.
        rewrite HM1; move/some_atom_inj => [Ew2 Et2]; subst w2' t2'; exact: Hic2.
      * by move=> ra rb Hd; rewrite INST in Hd; discriminate Hd.
  -  move=> mem reg pc i r1 r2 w1 w2 tpc ti t1 t2 old told extra ST PC INST R1W R2W OLD mvec NEXT. left.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) by rewrite ST /= PC.
    have HR1 : Symbolic.regs s r1 = Some (w1 @ t1) by rewrite ST /= R1W.
    have HM1 : Symbolic.mem s w1 = Some (old @ told) by rewrite ST /= OLD.
    have Htold : is_code told = false.
    { move: NEXT; rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state.
      case: (Symbolic.mem s _) => [ni|]; move=> H;
        by (case: (obind_inv H) => i0 [_ {}H]; case: (obind_inv H) => [[ov0 ev0]] [Htr _];
            exact: (store_transfer_not_code Htr)). }
    move=> i0 ti0; rewrite HPC; move/some_atom_inj => [Ei Eti]; subst i0 ti0.
    split; first exact: (Hpci _ HPC). split.
    * by move=> ra rb Hd; rewrite INST in Hd; discriminate Hd.
    * move=> ra rb Hd; move: Hd; rewrite INST => [= Era Erb]; subst ra rb.
      move=> w1' t1' old' told'; rewrite HR1; move/some_atom_inj => [Ew Et]; subst w1' t1'.
      rewrite HM1; move/some_atom_inj => [Eo Eto]; subst old' told'; exact: Htold.
  -  move=> mem reg pc i r w tpc ti t1 extra l rav rat ST PC INST RW RA CLEAR mvec NEXT. left.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) by rewrite ST /= PC.
    move=> i0 ti0; rewrite HPC; move/some_atom_inj => [Ei Eti]; subst i0 ti0.
    split; first exact: (Hpci _ HPC).
    by split=> ra rb Hd; rewrite INST in Hd; discriminate Hd.
  -  move=> mem reg pc i r n w tpc ti t1 extra ST PC INST RW mvec pc' NEXT. left.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) by rewrite ST /= PC.
    move=> i0 ti0; rewrite HPC; move/some_atom_inj => [Ei Eti]; subst i0 ti0.
    split; first exact: (Hpci _ HPC).
    by split=> ra rb Hd; rewrite INST in Hd; discriminate Hd.
  -  move=> mem reg pc i imm tpc ti old told extra l vret tret ST PC RA INST OLD CLEAR mvec pc' NEXT. left.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = Some (i @ ti) by rewrite ST /= PC.
    move=> i0 ti0; rewrite HPC; move/some_atom_inj => [Ei Eti]; subst i0 ti0.
    split; first exact: (Hpci _ HPC).
    by split=> ra rb Hd; rewrite INST in Hd; discriminate Hd.
  -  move=> mem reg pc sc tpc extra ST PC GETCALL CALL. left.
    have HPC : Symbolic.mem s (Symbolic.pcv s) = None by rewrite ST /= PC.
    by move=> i0 ti0; rewrite HPC.
Qed.

Lemma cptr_code_step_mp (s1 s2 s1' : st) (ev : option event) :
  match_pad s1 s2 -> pc_incode s1 -> cptr_code s1 -> step_mp (NC := NC) s1 s1' ev -> cptr_code s1'.
Proof.
  move=> Hm Hpci Hcc Hstep.
  have Hciso : forall w a, Symbolic.mem s1 w = Some a -> is_code (taga a) ->
                 encode_code (code q) pc0 w = Some a by move: Hm => [_ [_ [_ [_ [H _]]]]].
  case: (no_compromise_or_load Hpci Hstep) => [Hnc | Hload].
  -
    exact: (cptr_code_step Hciso Hcc (step_mp_me Hnc Hstep)).
  -
    move: Hload => [tpc' [i' [ti' [r1 [r2 [w1 [w2 [t1 [t2 [old [told
      [Hpc [Hdec [HR1 [HM1 [HR2 [Hic2 HNEXT]]]]]]]]]]]]]]]]].
    have [Hre [tc [Hme Hcptc]]] := load_nsu_lrc HR1 HM1 HR2 HNEXT.
    move: Hcc => [CC1 CC2]; split.
    + move=> r w t; rewrite Hre 2!setmE.
      case: (r =P r2) => [_|_]; first by move=> [= <- <-] Hcp; exact: (CC2 _ _ _ HM1 Hcp).
      case: (r =P r1) => [_|_]; first by move=> [= <- <-] Hcp; exact: (CC1 _ _ _ HR1 Hcp).
      by move=> Hr Hcp; exact: (CC1 _ _ _ Hr Hcp).
    + move=> w v t; rewrite Hme setmE.
      case: (w =P w1) => [_|_]; first by move=> [= <- <-] Hcp; rewrite Hcptc in Hcp.
      by move=> Hw Hcp; exact: (CC2 _ _ _ Hw Hcp).
Qed.

Lemma nsuap_extract_lrc (s s' : st) (kiv : Symbolic.k_ivec lrc_tags)
   (updts : seq Symbolic.update) (pc' : mword mt) (e : option event) :
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags LRC.transfer unit s kiv updts pc' = Some (s', e) ->
  exists (op0 : opcode) (ov0 : Symbolic.ovec lrc_tags op0) (st0 : st),
    Symbolic.next_state_do_updates s (Symbolic.tr ov0) updts = Some st0 /\
    Symbolic.mem s' = Symbolic.mem st0 /\ Symbolic.regs s' = Symbolic.regs st0.
Proof.
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state.
  case: (Symbolic.evi s) => [evinp|] //=.
  case: (LRC.transfer _ evinp) => [ov_ev|] //=.
  case: (Symbolic.op _) ov_ev => [op0|] ov_ev //=.
  case: ov_ev => ov0 ev0.
  case Edsu: (Symbolic.next_state_do_updates s (Symbolic.tr ov0) updts) => [st0|] //=.
  by move=> [= <- _] /=; exists op0, ov0, st0.
Qed.

Lemma nsuap_pc_lrc (s s' : st) (kiv : Symbolic.k_ivec lrc_tags)
   (updts : seq Symbolic.update) (pc' : mword mt) (e : option event) :
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags LRC.transfer unit s kiv updts pc' = Some (s', e) ->
  vala (Symbolic.pc s') = pc'.
Proof.
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state.
  case: (Symbolic.evi s) => [evinp|] //=.
  case: (LRC.transfer _ evinp) => [ov_ev|] //=.
  case: (Symbolic.op _) ov_ev => [op0|] ov_ev //=.
  case: ov_ev => ov0 ev0.
  case Edsu: (Symbolic.next_state_do_updates s (Symbolic.tr ov0) updts) => [st0|] //=.
  by move=> [= <- _].
Qed.

Lemma alloc_empty_nonalloc (s s' : st) (kiv : Symbolic.k_ivec lrc_tags)
   (updts : seq Symbolic.update) (pc' : mword mt) (e : option event) :
  alloc_empty s ->
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags LRC.transfer unit s kiv updts pc' = Some (s', e) ->
  alloc_empty s'.
Proof.
  rewrite /alloc_empty => Halloc /nsuap_extract_lrc [op0 [ov0 [st0 [Hds [Hmem _]]]]].
  apply/dommPn; rewrite Hmem (ndsu_mem_domm Hds); apply/dommPn; exact: Halloc.
Qed.

Lemma bloc_no_alloc_label (c : Component.id) (len : nat) (max_addr : mword mt) :
   1 + c < 2 ^ NC ->
   andw max_addr (@mask mt NC) = @component_memory_prefix mt NC (ssrint.Posz (1 + c)) ->
   andw (addw max_addr (@as_word (word_size mt) (ssrint.Posz (len + 1)))) (@mask mt NC)
     = @component_memory_prefix mt NC (ssrint.Posz (1 + c)) ->
   len + 1 <= 2 ^ (word_size mt - NC) ->
   mkfmap (mkseq (fun n => (addw max_addr (@as_word (word_size mt) (ssrint.Posz (n + 1))),
                            (@as_word (word_size mt) (ssrint.Posz 0)) @ (def_mem_tag c false))) len)
     (@word_of_nat (word_size mt) alloc_label) = None.
Proof.
  move=> Hc Hstart Hend Hlen.
  case E: (mkfmap _ _) => [a|] //. exfalso.
  have HE := mkfmap_Some E.
  move: HE; rewrite /mkseq => /mapP [k Hk] [= Hkey _].
  have Hmask : andw (@word_of_nat (word_size mt) alloc_label) (@mask mt NC)
             = @component_memory_prefix mt NC (ssrint.Posz (1 + c)).
  { rewrite Hkey. exact: (mask_range Hlen Hstart Hend Hk). }
  apply: (component_memory_prefix_succ_not_zero (NC := NC) c (ltnW NC_lt_word) Hc).
  by rewrite -Hmask (mask_alloc_label alloc_label_lt_NC) component_memory_prefix_zero.
Qed.

Lemma alloc_empty_step (s s2 s' : st) (ev : option event) :
  match_pad s s2 -> alloc_empty s -> step_mp (NC := NC) s s' ev -> alloc_empty s'.
Proof.
  move=> Hm Halloc Hstep; case: Hstep.
  -  move=> mem reg pc tpc i ti extra ST PC INST mvec NEXT.
    by move: NEXT; rewrite /Symbolic.next_state_updates => NEXT; exact: (alloc_empty_nonalloc Halloc NEXT).
  -  move=> mem reg pc tpc i ti n r old told extra ST PC INST OLD mvec NEXT.
    by move: NEXT; rewrite /Symbolic.next_state_updates => NEXT; exact: (alloc_empty_nonalloc Halloc NEXT).
  -  move=> mem reg pc tpc i ti r1 w1 t1 r2 old told extra ST PC INST R1W OLD mvec NEXT.
    by move: NEXT; rewrite /Symbolic.next_state_updates => NEXT; exact: (alloc_empty_nonalloc Halloc NEXT).
  -  move=> mem reg pc tpc i ti op r1 r2 r3 w1 w2 t1 t2 old told extra ST PC INST R1W R2W OLD mvec NEXT.
    by move: NEXT; rewrite /Symbolic.next_state_updates => NEXT; exact: (alloc_empty_nonalloc Halloc NEXT).
  -  move=> mem reg pc tpc i ti r1 r2 w1 w2 t1 t2 old told extra ST PC INST R1W MEM1 OLD mvec NEXT.
    by move: NEXT; rewrite /Symbolic.next_state_updates => NEXT; exact: (alloc_empty_nonalloc Halloc NEXT).
  -  move=> mem reg pc i r1 r2 w1 w2 tpc ti t1 t2 old told extra ST PC INST R1W R2W OLD mvec NEXT.
    by move: NEXT; rewrite /Symbolic.next_state_updates => NEXT; exact: (alloc_empty_nonalloc Halloc NEXT).
  -  move=> mem reg pc i r w tpc ti t1 extra l rav rat ST PC INST RW RA CLEAR mvec NEXT.
    exact: (alloc_empty_nonalloc Halloc NEXT).
  -  move=> mem reg pc i r n w tpc ti t1 extra ST PC INST RW mvec pc' NEXT.
    exact: (alloc_empty_nonalloc Halloc NEXT).
  -  move=> mem reg pc i imm tpc ti old told extra l vret tret ST PC RA INST OLD CLEAR mvec pc' NEXT.
    exact: (alloc_empty_nonalloc Halloc NEXT).
  -
    move=> mem0 reg pcw sc tpc0 extra ST PC GETCALL CALL.
    admit.
Admitted.

Lemma pc_pos_step_mp (s1 s2 s1' : st) (ev : option event) :
  match_pad s1 s2 -> cptr_code s1 -> @PaddingValid.pc_pos q s1 -> alloc_empty s1 ->
  step_mp (NC := NC) s1 s1' ev -> @PaddingValid.pc_pos q s1'.
Proof.
  move=> Hm Hcc Hpp Hae Hstep.
  have Hpci := pc_incode_of_pos Hm Hpp.
  have Hae' := alloc_empty_step Hm Hae Hstep.
  have Hciso : forall w a, Symbolic.mem s1 w = Some a -> is_code (taga a) ->
                 encode_code (code q) pc0 w = Some a by move: Hm => [_ [_ [_ [_ [H _]]]]].
  case: (no_compromise_or_load Hpci Hstep) => [Hnc | Hload].
  -
    exact: (PaddingValid.pc_pos_step Hcount Hbound Hbound' code_last_term bnz_labels_resolved
              Hciso Hcc Hae' (step_mp_me Hnc Hstep)).
  -
    move: Hload => [tpc' [i' [ti' [r1 [r2 [w1 [w2 [t1 [t2 [old [told
      [Hpcm [Hdeci [HR1 [HM1 [HR2 [Hic2 HNEXT]]]]]]]]]]]]]]]]].
    rewrite /PaddingValid.pc_pos; left.
    have Hicc : is_code ti' = true := Hpci (i' @ ti') Hpcm.
    have Hcell := Hciso _ _ Hpcm Hicc.
    case: (PaddingSim.code_cell_q Hcount Hbound Hbound' Hcell)
      => ncc [imc [tmc [Hn [Hweq [Hnth [Htag Hdec]]]]]].
    have H1 := Hdec; rewrite vala_at Hdeci in H1; move: H1 => [= H1].
    move: HNEXT; rewrite /Symbolic.next_state_updates => HNEXT.
    have Hpcv := nsuap_pc_lrc HNEXT.
    move: Hpcv; rewrite /Symbolic.pcv Hweq => ->.
    exact: (PaddingValid.pc1_in_range Hbound
              (PaddingSim.nonterm_succ_lt code_last_term Hn Hnth (imt_load_nonterm H1))).
Qed.

Lemma left_step_sim (allowed : st -> Prop)
  (Hallowed : forall a b, match_pad a b -> allowed a -> allowed b)
  (s1 s2 : st) (t : trace) (s1' : st) :
  RL s1 s2 ->
  step_restricted_UB step1L step2L allowed tt s1 t s1' ->
  exists s2', step_restricted_UB step1L step2L allowed tt s2 t s2' /\ RL s1' s2'.
Proof.
  move=> [Hm [Hv [Hcc [Hpp Hae]]]] Hstep; have Hpci := pc_incode_of_pos Hm Hpp.
  move: Hstep => /srUB_inv [[Hmp Hub] | [Hme Hmp]].
  -
    have [ev [Het Hmp2]] : exists ev, t = oapp (fun e => [:: e]) [::] ev /\ step_mp (NC:=NC) s1 s1' ev.
    { move: Hmp; case: t => [|e [|? ?]].
      - by move=> H; exists None.
      - by move=> H; exists (Some e).
      - by move=> H; case: H. }
    clear Hmp.
    have [s2' [Hs2 [Hm' Hpv']]] := pad_step_fwd_mp Hm Hv Hpci Hmp2.
    exists s2'; subst t; split.
    + apply: step_UB_allowed; last exact: (Hallowed _ _ Hm Hub).
      by case: ev Hs2 {Hmp2} => [e|] /= Hs2.
    + rewrite /RL.
      split; first exact: Hm'.
      split; first exact: Hpv'.
      split; first exact: (cptr_code_step_mp Hm Hpci Hcc Hmp2).
      split.
      * exact: (pc_pos_step_mp Hm Hcc Hpp Hae Hmp2).
      * exact: (alloc_empty_step Hm Hae Hmp2).
  -
    clear Hmp.
    have [ev [Het Hme2]] : exists ev, t = oapp (fun e => [:: e]) [::] ev /\ step_me (NC:=NC) s1 s1' ev.
    { move: Hme; case: t => [|e [|? ?]].
      - by move=> H; exists None.
      - by move=> H; exists (Some e).
      - by move=> H; case: H. }
    clear Hme.
    have [s2' [Hs2 Hm']] := pad_step_fwd Hm Hv Hme2.
    have Hmpfull := step_me_mp_loc Hme2.
    exists s2'; subst t; split.
    + apply: step_UB_disallowed.
      * by case: ev Hs2 {Hme2 Hmpfull} => [e|] /= Hs2.
      * by case: ev Hs2 {Hme2 Hmpfull} => [e|] /= Hs2; apply: step_me_mp_loc.
    + rewrite /RL.
      split; first exact: Hm'.
      split; first exact: (pad_valid_step Hv Hme2).
      split; first exact: (cptr_code_step_mp Hm Hpci Hcc Hmpfull).
      split.
      * exact: (pc_pos_step_mp Hm Hcc Hpp Hae Hmpfull).
      * exact: (alloc_empty_step Hm Hae Hmpfull).
Qed.

End CodeShiftFwdMP.
