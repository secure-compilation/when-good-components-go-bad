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

Section CodeShiftValid.

Variables q q' : program.
Local Notation pc0 := (size (@Merged.initial_memory mt (prog_buffers q))).
Local Notation padc := ((pad_code (code q) (code q')).1).
Local Notation sizes := (pad_block_sizes (code q) (code q')).
Local Notation lpf c :=
  (fun (l d : nat) =>
     match findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) c with
     | Some m => pc0 + m | None => if l == alloc_label then l else d end).

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

Local Notation st := (@Symbolic.state mt lrc_tags unit).

Local Notation match_pad  := (@PaddingSim.match_pad q q').
Local Notation pad_valid  := (@PaddingSim.pad_valid q q').
Local Notation phia       := (@PaddingSim.phia q q').
Local Notation rel_v      := (@PaddingSim.rel_v q q').
Local Notation addr_ok    := (@PaddingSim.addr_ok q q').
Local Notation memwk      := (@PaddingSim.memwk q q').
Local Notation memwk_bwd  := (@PaddingSim.memwk_bwd q q').
Local Notation wregs      := (@PaddingSim.wregs q q').

Local Notation code_cell_q      := (PaddingSim.code_cell_q Hcount Hbound Hbound').
Local Notation phia_addr_code   := (PaddingSim.phia_addr_code Hcount Hbound Hbound').
Local Notation pc_succ_corr     := (PaddingSim.pc_succ_corr Hcount Hbound Hbound' fallthrough_aligned).
Local Notation jal_corr         := (PaddingSim.jal_corr Hcount Hbound Hbound').
Local Notation bnz_corr         := (PaddingSim.bnz_corr Hcount Hbound Hbound').
Local Notation size_code_le_padc := (PaddingSim.size_code_le_padc Hcount).
Local Notation code_cell_padc   := (PaddingSim.code_cell_padc word_of_nat_inj Hcount Hbound Hbound').
Local Notation jump_target_corr := (PaddingSim.jump_target_corr word_of_nat_inj Hcount Hbound Hbound' code_tags_wf_q).
Local Notation jump_belong_corr := (PaddingSim.jump_belong_corr word_of_nat_inj Hcount Hbound Hbound' code_tags_wf_q).
Local Notation encode_code_dom  := (PaddingSim.encode_code_dom word_of_nat_inj).
Local Notation nonterm_succ_lt  := (PaddingSim.nonterm_succ_lt code_last_term).

Local Opaque PaddingSim.rel_v.

Lemma addr_ok_mono (m m' : {fmap mword mt -> atom (mword mt) mem_tag}) (w : mword mt) :
  (forall w' c, m w' = Some c -> exists c', m' w' = Some c') ->
  PaddingSim.addr_ok q q' m w -> PaddingSim.addr_ok q q' m' w.
Proof. move=> Hext; rewrite /PaddingSim.addr_ok => -[[c Hc]|Hr]; [ left; exact: (Hext _ _ Hc) | by right ]. Qed.

Lemma setm_ext (m : {fmap mword mt -> atom (mword mt) mem_tag}) (k : mword mt) (v : matom) :
  forall w' c, m w' = Some c -> exists c', (setm m k v) w' = Some c'.
Proof. move=> w' c Hc; rewrite setmE; case: (w' =P k) => [_|_]; [by exists v | by exists c]. Qed.

Lemma unionm_ext (m bm : {fmap mword mt -> atom (mword mt) mem_tag}) :
  forall w' c, m w' = Some c -> exists c', (unionm m bm) w' = Some c'.
Proof. move=> w' c Hc; exists c; rewrite unionmE Hc //. Qed.

Lemma ndsu1_mem_ext (s s' : st) (tk : Symbolic.tag_kind)
   (tag : Symbolic.tag_type lrc_tags tk) (u : Symbolic.update) :
  Symbolic.next_state_do_update s tag u = Some s' ->
  forall w c, Symbolic.mem s w = Some c -> exists c', Symbolic.mem s' w = Some c'.
Proof.
  move=> H w c Hw; move: H; rewrite /Symbolic.next_state_do_update.
  case: tk tag => tag; case: u => [r x|r|w1 w2|w0] //=.
  - rewrite /updm; case: (Symbolic.regs s r) => [a|] //= [<-] /=; by exists c.
  - case Ea: (Symbolic.regs s r) => [a|] /=; last by move=> Hd; discriminate Hd.
    rewrite /updm Ea /= => [= <-] /=; by exists c.
  - rewrite /updm; case: (Symbolic.mem s w1) => [a|] //= [<-] /=.
    rewrite setmE; case: (w =P w1) => [_|_]; [by eexists | by exists c].
  - case Ea: (Symbolic.mem s w0) => [a|] /=; last by move=> Hd; discriminate Hd.
    rewrite /updm Ea /= => [= <-] /=.
    rewrite setmE; case: (w =P w0) => [_|_]; [by eexists | by exists c].
Qed.

Lemma ndsu_mem_ext (tks : seq Symbolic.tag_kind) (tags : hseq (Symbolic.tag_type lrc_tags) tks)
   (updts : seq Symbolic.update) (s s' : st) :
  Symbolic.next_state_do_updates s tags updts = Some s' ->
  forall w c, Symbolic.mem s w = Some c -> exists c', Symbolic.mem s' w = Some c'.
Proof.
  elim: tks tags updts s s' => [|tk tks' IH] tags updts s s' /=.
  - by move=> [<-] w c Hw; exists c.
  - case: (ohead updts) => [u|] /=; last by move=> Hd; discriminate Hd.
    case E: (Symbolic.next_state_do_update s (hshead tags) u) => [s1|] /=; last by move=> Hd; discriminate Hd.
    move=> H w c Hw.
    have [c1 Hc1] := ndsu1_mem_ext E Hw. exact: (IH _ _ _ _ H _ _ Hc1).
Qed.

Lemma nsuap_mem_ext (s s' : st) (kiv : Symbolic.k_ivec lrc_tags)
   (updts : seq Symbolic.update) (pc' : mword mt) (e : option event) :
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s kiv updts pc' = Some (s', e) ->
  forall w c, Symbolic.mem s w = Some c -> exists c', Symbolic.mem s' w = Some c'.
Proof.
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state.
  case: (Symbolic.evi s) => [i|] //=.
  case: (Merged.transfer _ i) => [ov_ev|] //=.
  move: ov_ev; case: (Symbolic.op _) => [op|] ov_ev //=.
  case: ov_ev => ov ev0.
  case Hds: (Symbolic.next_state_do_updates s (Symbolic.tr ov) updts) => [st'|] //= [<- _] /=.
  exact: (ndsu_mem_ext Hds).
Qed.

Lemma nsuap_extract (s s' : st) (kiv : Symbolic.k_ivec lrc_tags)
   (updts : seq Symbolic.update) (pc' : mword mt) (e : option event) :
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s kiv updts pc' = Some (s', e) ->
  exists (op0 : opcode) (ov0 : Symbolic.ovec lrc_tags op0) (st0 : st),
    Symbolic.next_state_do_updates s (Symbolic.tr ov0) updts = Some st0 /\
    Symbolic.mem s' = Symbolic.mem st0 /\ Symbolic.regs s' = Symbolic.regs st0.
Proof.
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state.
  case: (Symbolic.evi s) => [evinp|] //=.
  case: (Merged.transfer _ evinp) => [ov_ev|] //=.
  case: (Symbolic.op _) ov_ev => [op0|] ov_ev //=.
  case: ov_ev => ov0 ev0.
  case Edsu: (Symbolic.next_state_do_updates s (Symbolic.tr ov0) updts) => [st0|] //=.
  by move=> [= <- _] /=; exists op0, ov0, st0.
Qed.

Lemma nsuap_pc (s s' : st) (kiv : Symbolic.k_ivec lrc_tags)
   (updts : seq Symbolic.update) (pc' : mword mt) (e : option event) :
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s kiv updts pc' = Some (s', e) ->
  vala (Symbolic.pc s') = pc'.
Proof.
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state.
  case: (Symbolic.evi s) => [evinp|] //=.
  case: (Merged.transfer _ evinp) => [ov_ev|] //=.
  case: (Symbolic.op _) ov_ev => [op0|] ov_ev //=.
  case: ov_ev => ov0 ev0.
  case Edsu: (Symbolic.next_state_do_updates s (Symbolic.tr ov0) updts) => [st0|] //=.
  by move=> [= <- _].
Qed.

Lemma ndsu_nil (tks : seq tag_kind) (tags : hseq (tag_type lrc_tags) tks) (s0 st0 : st) :
  Symbolic.next_state_do_updates s0 tags [::] = Some st0 -> st0 = s0.
Proof. by case: tks tags => [|tk tks'] tags //= [->]. Qed.

Definition codeptr_unchanged (r0 rs : {fmap reg mt -> atom (mword mt) value_tag}) : Prop :=
  forall k w t, rs k = Some (w @ t) -> is_codeptr t -> r0 k = Some (w @ t).

Lemma cpu_refl (r0 : {fmap reg mt -> atom (mword mt) value_tag}) : codeptr_unchanged r0 r0.
Proof. by move=> k w t H _. Qed.

Lemma cpu_setm_other (r0 rs : {fmap reg mt -> atom (mword mt) value_tag}) (k : reg mt) (v : mword mt) :
  codeptr_unchanged r0 rs -> codeptr_unchanged r0 (setm rs k (v @ Other)).
Proof.
  move=> H k0 w t; rewrite setmE; case: (k0 =P k) => [_|_].
  - by move=> [= _ <-] Hcp; discriminate Hcp.
  - exact: H.
Qed.

Lemma cpu_setm_nc (r0 rs : {fmap reg mt -> atom (mword mt) value_tag}) (k : reg mt) (v : mword mt) (t : value_tag) :
  is_codeptr t = false -> codeptr_unchanged r0 rs -> codeptr_unchanged r0 (setm rs k (v @ t)).
Proof.
  move=> Ht H k0 w t0; rewrite setmE; case: (k0 =P k) => [_|_].
  - by move=> [= _ <-] Hcp; rewrite Ht in Hcp.
  - exact: H.
Qed.

Lemma ndu_R_cpu (r0 : {fmap reg mt -> atom (mword mt) value_tag}) (s0 s0' : st)
   (t : tag_type lrc_tags R) (u : Symbolic.update) :
  is_codeptr t = false ->
  Symbolic.next_state_do_update s0 t u = Some s0' ->
  codeptr_unchanged r0 (Symbolic.regs s0) ->
  codeptr_unchanged r0 (Symbolic.regs s0') /\ Symbolic.mem s0' = Symbolic.mem s0.
Proof.
  move=> Ht Hdu Hcpu; move: Hdu; rewrite /Symbolic.next_state_do_update.
  case: u => [k v|k|w1 w2|w] //=.
  - case E: (updm (Symbolic.regs s0) k (v @ t)) => [rs'|] //= [= <-] /=.
    split; last by []. move: E; rewrite /updm; case: (Symbolic.regs s0 k) => [a|] // [= <-].
    exact: (cpu_setm_nc Ht Hcpu).
  - case Ek: (Symbolic.regs s0 k) => [a|] //=; rewrite /updm Ek /= => [= <-] /=.
    split; last by []. exact: (cpu_setm_nc Ht Hcpu).
Qed.

Lemma ndu_M_regs (s0 s0' : st) (t : tag_type lrc_tags M) (u : Symbolic.update) :
  Symbolic.next_state_do_update s0 t u = Some s0' -> Symbolic.regs s0' = Symbolic.regs s0.
Proof.
  rewrite /Symbolic.next_state_do_update; case: u => [k v|k|w1 w2|w] //=.
  - by case E: (updm (Symbolic.mem s0) w1 (w2 @ t)) => [m'|] //= [= <-].
  - by case Ew: (Symbolic.mem s0 w) => [a|] //=; case E: (updm _ _ _) => [m'|] //= [= <-].
Qed.

Lemma updm_R (r : {fmap reg mt -> atom (mword mt) value_tag}) (k : reg mt)
   (vold v : atom (mword mt) value_tag) :
  r k = Some vold -> updm r k v = Some (setm r k v).
Proof. by move=> H; rewrite /updm H. Qed.

Lemma updm_setm_R (r : {fmap reg mt -> atom (mword mt) value_tag}) (k1 k2 : reg mt)
   (v1 vold v2 : atom (mword mt) value_tag) :
  r k2 = Some vold -> updm (setm r k1 v1) k2 v2 = Some (setm (setm r k1 v1) k2 v2).
Proof. move=> H; rewrite /updm setmE; by case: (k2 =P k1) => [_|_]; rewrite ?H. Qed.

Arguments updm_R {r k vold v} _.
Arguments updm_setm_R {r k1 k2 v1 vold v2} _.

Lemma const_nsu_valid (m : {fmap mword mt -> matom}) (r : {fmap reg mt -> ratom})
   (pcw : mword mt) (tpc : tag_type lrc_tags Symbolic.P) (ext : unit) (ti : mem_tag)
   (nn : imm mt) (rg : reg mt) (vold : mword mt) (told : value_tag) (s' : st) (e : option event) :
  r rg = Some (vold @ told) ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
    (@Symbolic.State mt lrc_tags unit m r (pcw @ tpc) ext)
    (IVec (OP CONST) tpc ti [hseq told]) [:: RegWrite rg (swcast nn)] = Some (s', e) ->
  Symbolic.mem s' = m /\ Symbolic.regs s' = setm r rg ((swcast nn) @ Other).
Proof.
  move=> Hrg. case: tpc => ltpc ctpc.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  case Hni: (m (pcw + 1)%w) => [v1n|];
    (case Hevi: (Symbolic.evi _) => [evinp|]; last by move=> [=]);
    rewrite /Merged.transfer /= /Merged.instr_rules /=;
    (case Hic: (is_code ti) => /=; last by move=> [=]);
    rewrite /LRC.instr_rules /=; rewrite ?PaddingSim.color_matchE;
    (case Hcur: (color ti == ctpc) => /=; last by move=> [=]).
  - rewrite /LRC.check_belong PaddingSim.belong_someE.
    case Hbel: (color ti == color (taga v1n)) => /=; last by move=> [=].
    by rewrite /updm Hrg /= => [= <- _].
  - rewrite /LRC.check_belong /=.
    by rewrite /updm Hrg /= => [= <- _].
Qed.

Lemma mov_nsu_valid (m : {fmap mword mt -> matom}) (r : {fmap reg mt -> ratom})
   (pcw : mword mt) (tpc : tag_type lrc_tags Symbolic.P) (ext : unit) (ti : mem_tag)
   (r1 r2 : reg mt) (w1 : mword mt) (t1 : value_tag) (vold : mword mt) (told : value_tag) (s' : st) (e : option event) :
  r r1 = Some (w1 @ t1) -> r r2 = Some (vold @ told) ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
    (@Symbolic.State mt lrc_tags unit m r (pcw @ tpc) ext)
    (IVec (OP MOV) tpc ti [hseq t1; told]) [:: RegRead r1; RegWrite r2 w1] = Some (s', e) ->
  Symbolic.mem s' = m /\
  Symbolic.regs s' = setm (setm r r1 (w1 @ (if is_address t1 then Invalidated else Other))) r2 (w1 @ t1).
Proof.
  move=> Hr1 Hr2. case: tpc => ltpc ctpc.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  case Hni: (m (pcw + 1)%w) => [v1n|];
    (case Hevi: (Symbolic.evi _) => [evinp|]; last by move=> [=]);
    rewrite /Merged.transfer /= /Merged.instr_rules /=;
    (case Hic: (is_code ti) => /=; last by move=> [=]);
    rewrite /LRC.instr_rules /=; rewrite ?PaddingSim.color_matchE;
    (case Hcur: (color ti == ctpc) => /=; last by move=> [=]).
  - rewrite /LRC.check_belong PaddingSim.belong_someE.
    case Hbel: (color ti == color (taga v1n)) => /=; last by move=> [=].
    by rewrite /= Hr1 /= (updm_R Hr1) /= (updm_setm_R Hr2) /= => [= <- _].
  - rewrite /LRC.check_belong /=.
    by rewrite /= Hr1 /= (updm_R Hr1) /= (updm_setm_R Hr2) /= => [= <- _].
Qed.

Lemma bnz_nsu_valid (m : {fmap mword mt -> matom}) (r : {fmap reg mt -> ratom})
   (pcw : mword mt) (tpc : tag_type lrc_tags Symbolic.P) (ext : unit) (ti : mem_tag)
   (rg : reg mt) (w : mword mt) (t1 : value_tag) (pc' : mword mt) (s' : st) (e : option event) :
  r rg = Some (w @ t1) ->
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
    (@Symbolic.State mt lrc_tags unit m r (pcw @ tpc) ext)
    (IVec (OP BNZ) tpc ti [hseq t1]) [:: RegRead rg] pc' = Some (s', e) ->
  Symbolic.mem s' = m /\ Symbolic.regs s' = setm r rg (w @ Other).
Proof.
  move=> Hrg. case: tpc => ltpc ctpc.
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  case Hni: (m pc') => [v1n|];
    (case Hevi: (Symbolic.evi _) => [evinp|]; last by move=> [=]);
    rewrite /Merged.transfer /= /Merged.instr_rules /=;
    (case Hic: (is_code ti) => /=; last by move=> [=]);
    rewrite /LRC.instr_rules /=; rewrite ?PaddingSim.color_matchE;
    (case Hcur: (color ti == ctpc) => /=; last by move=> [=]);
    case: t1 Hrg => [?||| ] /= Hrg; first [ by move=> [=] | idtac ].
  - rewrite /LRC.check_belong PaddingSim.belong_someE.
    case Hbel: (color ti == color (taga v1n)) => /=; last by move=> [=].
    by rewrite /= Hrg /= (updm_R Hrg) /= => [= <- _].
  - by rewrite /= /LRC.check_belong /= Hrg /= (updm_R Hrg) /= => [= <- _].
Qed.

Definition tk_R_nc (tk : tag_kind) : tag_type lrc_tags tk -> bool :=
  match tk return tag_type lrc_tags tk -> bool with
  | R => fun t => ~~ is_codeptr t | _ => fun _ => false end.

Fixpoint hseq_allR_nc (tks : seq tag_kind) : hseq (tag_type lrc_tags) tks -> bool :=
  match tks return hseq (tag_type lrc_tags) tks -> bool with
  | [::] => fun _ => true
  | tk :: tks' => fun tags => tk_R_nc (hshead tags) && hseq_allR_nc (hsbehead tags)
  end.

Lemma tk_R_nc_eq (tk : tag_kind) (t : tag_type lrc_tags tk) : tk_R_nc t -> tk = R.
Proof. by case: tk t. Qed.

Lemma ndsu_allR (r0 : {fmap reg mt -> atom (mword mt) value_tag})
   (tks : seq tag_kind) (tags : hseq (tag_type lrc_tags) tks) (updts : seq Symbolic.update) (s0 s0' : st) :
  Symbolic.next_state_do_updates s0 tags updts = Some s0' -> hseq_allR_nc tags ->
  codeptr_unchanged r0 (Symbolic.regs s0) ->
  codeptr_unchanged r0 (Symbolic.regs s0') /\ Symbolic.mem s0' = Symbolic.mem s0.
Proof.
  move: tks tags updts s0 s0'; elim => [|tk tks' IH] tags updts s0 s0' /=.
  - by move=> [<-] _ Hcpu; split.
  - case: updts => [|u us]; first by move=> [=].
    rewrite /=. case Hd: (Symbolic.next_state_do_update s0 (hshead tags) u) => [st1|]; last by move=> [=].
    move=> Hrec /andP [Htk Hrest] Hcpu.
    have [Hc1 Hm1] : codeptr_unchanged r0 (Symbolic.regs st1) /\ Symbolic.mem st1 = Symbolic.mem s0.
    { have Etk := tk_R_nc_eq Htk; subst tk.
      exact: (ndu_R_cpu (negbTE Htk) Hd Hcpu). }
    have [Hc2 Hm2] := IH _ _ _ _ Hrec Hrest Hc1.
    by split; [ exact: Hc2 | rewrite Hm2 Hm1 ].
Qed.

Definition tk_nc (tk : tag_kind) : tag_type lrc_tags tk -> bool :=
  match tk return tag_type lrc_tags tk -> bool with
  | R => fun t => ~~ is_codeptr t | _ => fun _ => true end.

Fixpoint hseq_R_nc (tks : seq tag_kind) : hseq (tag_type lrc_tags) tks -> bool :=
  match tks return hseq (tag_type lrc_tags) tks -> bool with
  | [::] => fun _ => true
  | tk :: tks' => fun tags => tk_nc (hshead tags) && hseq_R_nc (hsbehead tags)
  end.

Lemma ndu_cpu (r0 : {fmap reg mt -> atom (mword mt) value_tag}) (s0 s0' : st)
   (tk : tag_kind) (t : tag_type lrc_tags tk) (u : Symbolic.update) :
  tk_nc t -> Symbolic.next_state_do_update s0 t u = Some s0' ->
  codeptr_unchanged r0 (Symbolic.regs s0) -> codeptr_unchanged r0 (Symbolic.regs s0').
Proof.
  case: tk t => [t|t|t] /=.
  - by move=> Ht Hd Hcpu; case: (ndu_R_cpu (negbTE Ht) Hd Hcpu).
  - by move=> _ Hd Hcpu; rewrite (ndu_M_regs Hd).
  - by move=> _ Hd; rewrite /Symbolic.next_state_do_update /= in Hd; discriminate Hd.
Qed.

Lemma ndsu_cpu (r0 : {fmap reg mt -> atom (mword mt) value_tag})
   (tks : seq tag_kind) (tags : hseq (tag_type lrc_tags) tks) (updts : seq Symbolic.update) (s0 s0' : st) :
  Symbolic.next_state_do_updates s0 tags updts = Some s0' -> hseq_R_nc tags ->
  codeptr_unchanged r0 (Symbolic.regs s0) -> codeptr_unchanged r0 (Symbolic.regs s0').
Proof.
  move: tks tags updts s0 s0'; elim => [|tk tks' IH] tags updts s0 s0' /=.
  - by move=> [<-].
  - case: updts => [|u us]; first by move=> [=].
    rewrite /=. case Hd: (Symbolic.next_state_do_update s0 (hshead tags) u) => [st1|]; last by move=> [=].
    move=> Hrec /andP [Htk Hrest] Hcpu.
    apply: (IH _ _ _ _ Hrec Hrest). exact: (ndu_cpu Htk Hd Hcpu).
Qed.

Lemma my_ndsu_cons (s0 : st) (tk : tag_kind) (tks' : seq tag_kind) (t : tag_type lrc_tags tk)
   (tags' : hseq (tag_type lrc_tags) tks') (u : Symbolic.update) (us : seq Symbolic.update) :
  Symbolic.next_state_do_updates s0 (HSeqCons t tags' : hseq (tag_type lrc_tags) (tk :: tks')) (u :: us)
  = obind (fun st' => Symbolic.next_state_do_updates st' tags' us) (Symbolic.next_state_do_update s0 t u).
Proof. by []. Qed.

Lemma ndu_R_mem (s0 s0' : st) (t : tag_type lrc_tags R) (u : Symbolic.update) :
  Symbolic.next_state_do_update s0 t u = Some s0' -> Symbolic.mem s0' = Symbolic.mem s0.
Proof.
  rewrite /Symbolic.next_state_do_update; case: u => [k v|k|w1 w2|w] //=.
  - by case E: (updm (Symbolic.regs s0) k (v @ t)) => [rs'|] //= [= <-].
  - by case Ek: (Symbolic.regs s0 k) => [a|] //=; case E: (updm _ _ _) => [rs'|] //= [= <-].
Qed.

Lemma ndu_MW_mem (s0 s0' : st) (t : tag_type lrc_tags M) (w1 w2 : mword mt) :
  Symbolic.next_state_do_update s0 t (Symbolic.MemWrite w1 w2) = Some s0' ->
  Symbolic.mem s0' = setm (Symbolic.mem s0) w1 (w2 @ t).
Proof.
  rewrite /Symbolic.next_state_do_update /=.
  case E: (updm (Symbolic.mem s0) w1 (w2 @ t)) => [m'|] //= [= <-] /=.
  by move: E; rewrite /updm; case: (Symbolic.mem s0 w1) => [a|] // [= <-].
Qed.

Lemma ndu_RegRead_eq (s0 s0' : st) (t : tag_type lrc_tags R) (k : reg mt) (a : atom (mword mt) value_tag) :
  Symbolic.regs s0 k = Some a -> Symbolic.next_state_do_update s0 t (RegRead k) = Some s0' ->
  Symbolic.regs s0' = setm (Symbolic.regs s0) k ((vala a) @ t) /\ Symbolic.mem s0' = Symbolic.mem s0.
Proof. move=> Hk; rewrite /Symbolic.next_state_do_update Hk /= /updm Hk /= => [= <-] /=; split=> //. Qed.

Lemma ndu_MemRead_eq (s0 s0' : st) (t : tag_type lrc_tags M) (w : mword mt) (a : matom) :
  Symbolic.mem s0 w = Some a -> Symbolic.next_state_do_update s0 t (MemRead w) = Some s0' ->
  Symbolic.mem s0' = setm (Symbolic.mem s0) w ((vala a) @ t) /\ Symbolic.regs s0' = Symbolic.regs s0.
Proof. move=> Hw; rewrite /Symbolic.next_state_do_update Hw /= /updm Hw /= => [= <-] /=; split=> //. Qed.

Lemma ndu_RegWrite_eq (s0 s0' : st) (t : tag_type lrc_tags R) (k : reg mt) (x : mword mt) (vold : atom (mword mt) value_tag) :
  Symbolic.regs s0 k = Some vold -> Symbolic.next_state_do_update s0 t (RegWrite k x) = Some s0' ->
  Symbolic.regs s0' = setm (Symbolic.regs s0) k (x @ t) /\ Symbolic.mem s0' = Symbolic.mem s0.
Proof. move=> Hk; rewrite /Symbolic.next_state_do_update /= /updm Hk /= => [= <-] /=; split=> //. Qed.

Lemma reg_read_update_id : forall (s0 : st) (k : reg mt) (a : atom (mword mt) (tag_type lrc_tags R)),
  Symbolic.regs s0 k = Some a -> Symbolic.next_state_do_update s0 (taga a) (RegRead k) = Some s0.
Proof.
  move=> s0 k [va ta] Hk; rewrite /Symbolic.next_state_do_update /= Hk /= /updm Hk /=.
  have Es : setm (Symbolic.regs s0) k (va @ ta) = Symbolic.regs s0.
  { apply/eq_fmap => k'; rewrite setmE; case: eqP => [-> | _]; by rewrite ?Hk. }
  rewrite Es; clear Hk Es; by case: s0.
Qed.

Lemma reg_write_set (s0 : st) (k : reg mt) (x : mword mt) (t : tag_type lrc_tags R)
   (vold : atom (mword mt) value_tag) :
  Symbolic.regs s0 k = Some vold ->
  Symbolic.next_state_do_update s0 t (RegWrite k x)
  = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem s0)
            (setm (Symbolic.regs s0) k (x @ t)) (Symbolic.pc s0) (Symbolic.internal s0)).
Proof. by move=> Hk; rewrite /Symbolic.next_state_do_update /= /updm Hk /=. Qed.

Local Opaque Symbolic.next_state_do_update.

Lemma reg_clear_do_updates_id :
  forall (l : seq nat) (s0 : st) (k0 : reg mt) (a0 : atom (mword mt) (tag_type lrc_tags R))
         (tags : hseq (tag_type lrc_tags) (nseq (S (size l)) R)),
    Symbolic.regs s0 k0 = Some a0 ->
    reg_clear_list_aux l (Symbolic.regs s0) (taga a0) = Some tags ->
    Symbolic.next_state_do_updates s0 tags
      (RegRead k0 :: map (fun n => RegRead (as_word (ssrint.Posz n))) l) = Some s0.
Proof.
  elim => [|e l' IH] s0 k0 a0 tags Hk0.
  - by move=> /= [= <-] /=; rewrite (reg_read_update_id Hk0).
  - rewrite /=.
    case Hve : (Symbolic.regs s0 (as_word (ssrint.Posz e))) => [ve|] //=.
    case Hl'' : (reg_clear_list_aux l' (Symbolic.regs s0) (taga ve)) => [l''|] //=.
    move=> [= <-] /=; rewrite (reg_read_update_id Hk0) /=.
    exact: (IH s0 (as_word (ssrint.Posz e)) ve l'' Hve Hl'').
Qed.

Lemma ndsu_nil0 (s0 : st) (tags : hseq (tag_type lrc_tags) [::]) :
  Symbolic.next_state_do_updates s0 tags [::] = Some s0.
Proof. by []. Qed.

Local Opaque Symbolic.next_state_do_updates.

Lemma nsuap_inval_list_1 : forall (ks : seq nat) (s0 : st),
  (forall k, k \in ks -> exists a, Symbolic.regs s0 (as_word (ssrint.Posz k)) = Some a) ->
  exists sd, Symbolic.next_state_do_updates s0
       (make_hseq (size ks) Invalidated) (map (fun n => RegRead (as_word (ssrint.Posz n))) ks) = Some sd
     /\ Symbolic.mem sd = Symbolic.mem s0.
Proof.
  elim => [|k ks' IH] s0 Hdom.
  - by exists s0; split; [ exact: (ndsu_nil0 s0 (make_hseq 0 Invalidated)) | ].
  - have [a Ha] := Hdom k (mem_head k ks').
    set s0a := @Symbolic.State mt lrc_tags unit (Symbolic.mem s0)
                 (setm (Symbolic.regs s0) (as_word (ssrint.Posz k)) ((vala a) @ Invalidated))
                 (Symbolic.pc s0) (Symbolic.internal s0).
    have Hd1 : Symbolic.next_state_do_update s0 (Invalidated : Symbolic.tag_type lrc_tags Symbolic.R)
                 (RegRead (as_word (ssrint.Posz k))) = Some s0a := reg_read_retag _ Ha.
    have Hdom' : forall k', k' \in ks' -> exists a, Symbolic.regs s0a (as_word (ssrint.Posz k')) = Some a.
    { move=> k' Hk'; rewrite /s0a /= setmE; case: eqP => [_|_];
        [ by eexists | apply: (Hdom k'); by rewrite in_cons Hk' orbT ]. }
    have [sd [Hsd Hmsd]] := IH s0a Hdom'.
    exists sd; split; last by rewrite Hmsd.
    rewrite [make_hseq (size (k :: ks')) Invalidated]/=
            [map (fun n => RegRead (as_word (ssrint.Posz n))) (k :: ks')]/=.
    rewrite ndsu_cons Hd1 [obind _ (Some s0a)]/=; exact: Hsd.
Qed.

Lemma load_du (s0 s0' : st) (ta : tag_type lrc_tags R) (tb : tag_type lrc_tags M) (td : tag_type lrc_tags R)
   (r1 r2 : reg mt) (w1 w2 : mword mt) (a1 : atom (mword mt) value_tag) (am : matom) (vold : atom (mword mt) value_tag) :
  Symbolic.next_state_do_updates s0
     (HSeqCons ta (HSeqCons tb (HSeqCons td HSeqNil)) : hseq (tag_type lrc_tags) [:: R; M; R])
     [:: RegRead r1; MemRead w1; RegWrite r2 w2] = Some s0' ->
  Symbolic.regs s0 r1 = Some a1 -> Symbolic.mem s0 w1 = Some am -> Symbolic.regs s0 r2 = Some vold ->
  Symbolic.regs s0' = setm (setm (Symbolic.regs s0) r1 ((vala a1) @ ta)) r2 (w2 @ td) /\
  Symbolic.mem s0' = setm (Symbolic.mem s0) w1 ((vala am) @ tb).
Proof.
  move=> Hd Hr1 Hw1 Hr2; move: Hd.
  rewrite my_ndsu_cons; case Hd1: (Symbolic.next_state_do_update s0 ta (RegRead r1)) => [st1|] //=.
  rewrite my_ndsu_cons; case Hd2: (Symbolic.next_state_do_update st1 tb (MemRead w1)) => [st2|] //=.
  rewrite my_ndsu_cons; case Hd3: (Symbolic.next_state_do_update st2 td (RegWrite r2 w2)) => [st3|] //= [= <-].
  have [Hr1e Hm1e] := ndu_RegRead_eq Hr1 Hd1.
  have Hw1' : Symbolic.mem st1 w1 = Some am by rewrite Hm1e.
  have [Hm2e Hr2e] := ndu_MemRead_eq Hw1' Hd2.
  have Hr2v : exists v, Symbolic.regs st2 r2 = Some v.
  { rewrite Hr2e Hr1e setmE; case: (r2 =P r1) => _; [ by eexists | by exists vold ]. }
  case: Hr2v => v Hr2v.
  have [Hr3e Hm3e] := ndu_RegWrite_eq Hr2v Hd3.
  by split; [ rewrite Hr3e Hr2e Hr1e | rewrite Hm3e Hm2e Hm1e ].
Qed.

Lemma store_du_mem (s0 s0' : st) (ta tb : tag_type lrc_tags R) (tc : tag_type lrc_tags M)
   (r1 r2 : reg mt) (w1 w2 : mword mt) :
  Symbolic.next_state_do_updates s0
     (HSeqCons ta (HSeqCons tb (HSeqCons tc HSeqNil)) : hseq (tag_type lrc_tags) [:: R; R; M])
     [:: RegRead r1; RegRead r2; MemWrite w1 w2] = Some s0' ->
  Symbolic.mem s0' = setm (Symbolic.mem s0) w1 (w2 @ tc).
Proof.
  rewrite my_ndsu_cons; case Hd1: (Symbolic.next_state_do_update s0 ta (RegRead r1)) => [st1|] //=.
  rewrite my_ndsu_cons; case Hd2: (Symbolic.next_state_do_update st1 tb (RegRead r2)) => [st2|] //=.
  rewrite my_ndsu_cons; case Hd3: (Symbolic.next_state_do_update st2 tc (MemWrite w1 w2)) => [st3|] //= [= <-].
  by rewrite (ndu_MW_mem Hd3) (ndu_R_mem Hd2) (ndu_R_mem Hd1).
Qed.

Lemma binop_nsu_cpu (m : {fmap mword mt -> matom}) (r : {fmap reg mt -> ratom})
   (pcw : mword mt) (tpc : tag_type lrc_tags Symbolic.P) (ext : unit) (ti : mem_tag) (op : binop)
   (r1 r2 r3 : reg mt) (x : mword mt) (t1 t2 told : value_tag) (s' : st) (e : option event) :
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
    (@Symbolic.State mt lrc_tags unit m r (pcw @ tpc) ext)
    (IVec (OP (BINOP op)) tpc ti [hseq t1; t2; told]) [:: RegRead r1; RegRead r2; RegWrite r3 x] = Some (s', e) ->
  Symbolic.mem s' = m /\ codeptr_unchanged r (Symbolic.regs s').
Proof.
  case: tpc => ltpc ctpc.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  case Hni: (m (pcw + 1)%w) => [v1n|];
    (case Hevi: (Symbolic.evi _) => [evinp|]; last by move=> [=]);
    rewrite /Merged.transfer /= /Merged.instr_rules /=;
    (case Hic: (is_code ti) => /=; last by move=> [=]);
    rewrite /LRC.instr_rules /=; rewrite ?PaddingSim.color_matchE;
    (case Hcur: (color ti == ctpc) => /=; last by move=> [=]);
    case: t1 => [?||| ] /=; first [ by move=> [=] | idtac ];
    case: t2 => [?||| ] /=; first [ by move=> [=] | idtac ];
    [ rewrite /LRC.check_belong PaddingSim.belong_someE;
      (case Hbel: (color ti == color (taga v1n)) => /=; last by move=> [=])
    | rewrite /= /LRC.check_belong /= ];
    move=> H; case: (obind_inv H) => st3 [Edu [= <- _]] /=;
    by have [Hc Hmm] := ndsu_allR Edu isT (@cpu_refl r); split; [ rewrite Hmm | exact: Hc ].
Qed.

Lemma switch_val_vtag (td : mem_tag) (v : value_tag) : vtag ((switch_val td v).1) = v.
Proof. by case: td. Qed.

Lemma return_clear_1 (s0 : st) (r : reg mt) (rav w rcv : mword mt) (rat t1 : value_tag)
   (l : hseq (tag_type lrc_tags) (nseq (size Symbolic.reg_list).+1 Symbolic.R)) :
  Symbolic.regs s0 ra = Some (rav @ rat) -> Symbolic.regs s0 r = Some (w @ t1) ->
  Symbolic.regs s0 rcom = Some (rcv @ Other) -> r != rcom -> ra != rcom ->
  Symbolic.reg_clear_list (Symbolic.regs s0) t1 = Some l ->
  exists sd, @Symbolic.next_state_do_updates mt lrc_tags unit s0
       [:: Symbolic.R, Symbolic.R, Symbolic.R & nseq 10 Symbolic.R]
       (Invalidated :: Invalidated :: Other :: reg_invalidate_hseq)%hseq
       (RegRead ra :: RegRead r :: reg_clear_read) = Some sd /\ Symbolic.mem sd = Symbolic.mem s0.
Proof.
  move=> Hra Hr Hrcom Hrne Harne Hcl.
  set s0a := @Symbolic.State mt lrc_tags unit (Symbolic.mem s0)
               (setm (Symbolic.regs s0) ra ((vala (rav @ rat)) @ Invalidated)) (Symbolic.pc s0) (Symbolic.internal s0).
  have E1a : Symbolic.next_state_do_update s0 (Invalidated : tag_type lrc_tags R) (RegRead ra) = Some s0a
    := reg_read_retag _ Hra.
  have [ar Har] : exists a, Symbolic.regs s0a r = Some a.
  { rewrite /s0a /= setmE; case: eqP => [_|_]; [by eexists | by rewrite Hr; eexists]. }
  set s0b := @Symbolic.State mt lrc_tags unit (Symbolic.mem s0a)
               (setm (Symbolic.regs s0a) r ((vala ar) @ Invalidated)) (Symbolic.pc s0a) (Symbolic.internal s0a).
  have E1b : Symbolic.next_state_do_update s0a (Invalidated : tag_type lrc_tags R) (RegRead r) = Some s0b
    := reg_read_retag _ Har.
  have Hrne' : r != as_word (ssrint.Posz 1) := Hrne.
  have Harne' : as_word (ssrint.Posz 4) != as_word (ssrint.Posz 1) := Harne.
  have Hrcomb : Symbolic.regs s0b rcom = Some (rcv @ Other).
  { rewrite /s0b /s0a /= !setmE.
    case: (as_word (ssrint.Posz 1) =P r) => [E|_]; first by move: Hrne'; rewrite E eqxx.
    case: (as_word (ssrint.Posz 1) =P as_word (ssrint.Posz 4)) => [E|_]; first by move: Harne'; rewrite -E eqxx.
    exact: Hrcom. }
  set s0c := @Symbolic.State mt lrc_tags unit (Symbolic.mem s0b)
               (setm (Symbolic.regs s0b) rcom (rcv @ Other)) (Symbolic.pc s0b) (Symbolic.internal s0b).
  have E1c : Symbolic.next_state_do_update s0b (Other : tag_type lrc_tags R) (RegRead rcom) = Some s0c
    by rewrite (reg_read_retag _ Hrcomb) vala_at.
  have Hdomc : forall k, k \in [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19] ->
                 exists a, Symbolic.regs s0c (as_word (ssrint.Posz k)) = Some a.
  { move=> k Hk.
    have Hkrl : k \in Symbolic.reg_list by rewrite /Symbolic.reg_list in_cons; apply/orP; right.
    have [a Ha] := reg_clear_list_aux_dom Hcl Hkrl.
    rewrite /s0c /s0b /s0a /= !setmE.
    case: eqP => [_|_]; first by eexists.
    case: eqP => [_|_]; first by eexists.
    case: eqP => [_|_]; first by eexists.
    by rewrite Ha; eexists. }
  have [sd [Hd1 Hmd]] := @nsuap_inval_list_1 [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19] s0c Hdomc.
  have Hrcr : Symbolic.reg_clear_read
            = RegRead (as_word (ssrint.Posz 1))
              :: [seq RegRead (as_word (ssrint.Posz n)) | n <- [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]]
    by rewrite /Symbolic.reg_clear_read /Symbolic.reg_list.
  exists sd; split; last by rewrite Hmd.
  rewrite ndsu_cons E1a; cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read].
  rewrite ndsu_cons E1b; cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read].
  rewrite Hrcr ndsu_cons E1c; cbn -[Symbolic.next_state_do_updates].
  exact: Hd1.
Qed.

Local Lemma rcla_cons_some (e : nat) (l' : seq nat)
   (rs : {fmap reg mt -> atom (mword mt) (Symbolic.tag_type lrc_tags Symbolic.R)})
   (t : Symbolic.tag_type lrc_tags Symbolic.R)
   (a : atom (mword mt) (Symbolic.tag_type lrc_tags Symbolic.R))
   (ll : hseq (Symbolic.tag_type lrc_tags) (nseq (S (size l')) Symbolic.R)) :
   rs (as_word (ssrint.Posz e)) = Some a ->
   Symbolic.reg_clear_list_aux l' rs (taga a) = Some ll ->
   Symbolic.reg_clear_list_aux (e :: l') rs t = Some (HSeqCons t ll).
Proof.
  move=> Hr Hll.
  by rewrite reg_clear_list_aux_cons Hr [obind _ (Some a)]/= Hll [obind _ (Some ll)]/=.
Qed.

Lemma jal_call_clear_1 (s0 : st) (vret old rcv : mword mt) (tret : mem_tag) (told : value_tag) (level : nat) :
  Symbolic.mem s0 (vala (Symbolic.pc s0) + 1)%w = Some (vret @ tret) ->
  Symbolic.regs s0 ra = Some (old @ told) ->
  Symbolic.regs s0 rcom = Some (rcv @ Other) ->
  (forall k, k \in [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N ->
       exists a, Symbolic.regs s0 (as_word (ssrint.Posz k)) = Some a) ->
  exists sd, @Symbolic.next_state_do_updates mt lrc_tags unit s0
       [:: Symbolic.M, Symbolic.R, Symbolic.R & nseq 10 Symbolic.R]
       (tret :: Ret level :: Other :: reg_invalidate_hseq)%hseq
       (MemRead (vala (Symbolic.pc s0) + 1)%w :: RegWrite ra (vala (Symbolic.pc s0) + 1)%w :: reg_clear_read)
       = Some sd
    /\ Symbolic.mem sd = Symbolic.mem s0
    /\ codeptr_unchanged (setm (Symbolic.regs s0) ra ((vala (Symbolic.pc s0) + 1)%w @ (Ret level)))
                          (Symbolic.regs sd).
Proof.
  move=> Hmem Hra Hrcom Hdom.
  set s0b := @Symbolic.State mt lrc_tags unit (Symbolic.mem s0)
               (setm (Symbolic.regs s0) ra ((vala (Symbolic.pc s0) + 1)%w @ (Ret level)))
               (Symbolic.pc s0) (Symbolic.internal s0).
  have E1a : Symbolic.next_state_do_update s0 (tret : tag_type lrc_tags M)
               (MemRead (vala (Symbolic.pc s0) + 1)%w) = Some s0 := mem_read_update_id Hmem.
  have E1b : Symbolic.next_state_do_update s0 (Ret level : tag_type lrc_tags R)
               (RegWrite ra (vala (Symbolic.pc s0) + 1)%w) = Some s0b
    := reg_write_set (vala (Symbolic.pc s0) + 1)%w (Ret level) Hra.
  have Hrab : ra != rcom by [].
  have Hrcomb : Symbolic.regs s0b rcom = Some (rcv @ Other).
  { rewrite /s0b /= setmE. by case: (rcom =P ra) => [E|_]; [ move: Hrab; rewrite E eqxx | exact: Hrcom ]. }
  set s0c := @Symbolic.State mt lrc_tags unit (Symbolic.mem s0b)
               (setm (Symbolic.regs s0b) rcom (rcv @ Other)) (Symbolic.pc s0b) (Symbolic.internal s0b).
  have E1c : Symbolic.next_state_do_update s0b (Other : tag_type lrc_tags R) (RegRead rcom) = Some s0c
    by rewrite (reg_read_retag _ Hrcomb) vala_at.
  have Hdomc : forall k, k \in [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19] ->
                 exists a, Symbolic.regs s0c (as_word (ssrint.Posz k)) = Some a.
  { move=> k Hk. have [a Ha] := Hdom k Hk.
    rewrite /s0c /s0b /= !setmE.
    case: eqP => [_|_]; first by eexists.
    case: eqP => [_|_]; first by eexists.
    by rewrite Ha; eexists. }
  have [sd [Hd1 Hmd]] := @nsuap_inval_list_1 [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19] s0c Hdomc.
  have Hrcr : Symbolic.reg_clear_read
            = RegRead (as_word (ssrint.Posz 1))
              :: [seq RegRead (as_word (ssrint.Posz n)) | n <- [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]]
    by rewrite /Symbolic.reg_clear_read /Symbolic.reg_list.
  have Htail : @Symbolic.next_state_do_updates mt lrc_tags unit s0b
       [:: Symbolic.R & nseq 10 Symbolic.R] (Other :: reg_invalidate_hseq)%hseq
       Symbolic.reg_clear_read = Some sd.
  { rewrite Hrcr ndsu_cons E1c; cbn -[Symbolic.next_state_do_updates]. exact: Hd1. }
  have [Hcpu _] := ndsu_allR Htail isT (@cpu_refl (Symbolic.regs s0b)).
  exists sd; split; last split.
  - rewrite ndsu_cons E1a; cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read].
    rewrite ndsu_cons E1b; cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read].
    exact: Htail.
  - by rewrite Hmd /s0c /s0b.
  - exact: Hcpu.
Qed.

Lemma store_nsu (m : {fmap mword mt -> matom}) (r : {fmap reg mt -> ratom})
   (pcw : mword mt) (tpc : tag_type lrc_tags Symbolic.P) (ext : unit) (ti : mem_tag)
   (r1 r2 : reg mt) (w1 w2 : mword mt) (t1 t2 : value_tag) (told : mem_tag) (s' : st) (e : option event) :
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
    (@Symbolic.State mt lrc_tags unit m r (pcw @ tpc) ext)
    (IVec (OP STORE) tpc ti [hseq t1; t2; told]) [:: RegRead r1; RegRead r2; MemWrite w1 w2] = Some (s', e) ->
  codeptr_unchanged r (Symbolic.regs s') /\
  (exists tc : mem_tag, Symbolic.mem s' = setm m w1 (w2 @ tc) /\ vtag tc = t2).
Proof.
  case: tpc => ltpc ctpc. case: told => [vt cl en cd].
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  case Hni: (m (pcw + 1)%w) => [v1n|];
    (case Hevi: (Symbolic.evi _) => [evinp|]; last by move=> [=]);
    rewrite /Merged.transfer /= /Merged.instr_rules /=;
    (case Hic: (is_code ti) => /=; last by move=> [=]);
    (case Hcd: cd => /=; first by move=> [=]);
    rewrite /LRC.instr_rules /=; rewrite ?PaddingSim.color_matchE;
    (case Hcur: (color ti == ctpc) => /=; last by move=> [=]);
    case: t1 => [?||| ] /=; first [ by move=> [=] | idtac ];
    [ rewrite /LRC.check_belong !PaddingSim.belong_someE;
      (case Hbel: (color ti == color (taga v1n)) => /=; last by move=> [=]);
      (case Hbel2: (color ti == cl) => /=; last by move=> [=])
    | rewrite /LRC.check_belong PaddingSim.belong_someE /=;
      (case Hbel2: (color ti == cl) => /=; last by move=> [=]) ];
    (case Has: (is_address t2) => /=);
    move=> H; case: (obind_inv H) => st3 [Edu [= <- _]] /=;
    have Hc := ndsu_cpu Edu isT (@cpu_refl r);
    have Hm := store_du_mem Edu;
    by split; [ exact: Hc | eexists; split; [ exact: Hm | by [] ] ].
Qed.

Lemma load_nsu (m : {fmap mword mt -> matom}) (r : {fmap reg mt -> ratom})
   (pcw : mword mt) (tpc : tag_type lrc_tags Symbolic.P) (ext : unit) (ti : mem_tag)
   (r1 r2 : reg mt) (w1 w2 : mword mt) (t1 : value_tag) (t2 : mem_tag) (old : mword mt) (told : value_tag)
   (s' : st) (e : option event) :
  r r1 = Some (w1 @ t1) -> m w1 = Some (w2 @ t2) -> r r2 = Some (old @ told) ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
    (@Symbolic.State mt lrc_tags unit m r (pcw @ tpc) ext)
    (IVec (OP LOAD) tpc ti [hseq t1; t2; told]) [:: RegRead r1; MemRead w1; RegWrite r2 w2] = Some (s', e) ->
  Symbolic.regs s' = setm (setm r r1 (w1 @ Other)) r2 (w2 @ (vtag t2)) /\
  (exists tc : mem_tag, Symbolic.mem s' = setm m w1 (w2 @ tc) /\ is_codeptr (vtag tc) = false).
Proof.
  move=> Hr1 Hw1 Hr2.
  case: tpc => ltpc ctpc. case: t2 Hw1 => [vt2 cl2 en2 cd2] Hw1.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  case Hni: (m (pcw + 1)%w) => [v1n|];
    (case Hevi: (Symbolic.evi _) => [evinp|]; last by move=> [=]);
    rewrite /Merged.transfer /= /Merged.instr_rules /=;
    (case Hic: (is_code ti) => /=; last by move=> [=]);
    (case Hcd2: cd2 => /=; first by move=> [=]);
    rewrite /LRC.instr_rules /=; rewrite ?PaddingSim.color_matchE;
    (case Hcur: (color ti == ctpc) => /=; last by move=> [=]);
    case: t1 Hr1 => [?||| ] Hr1 /=; first [ by move=> [=] | idtac ];
    [ rewrite /LRC.check_belong PaddingSim.belong_someE;
      (case Hbel: (color ti == color (taga v1n)) => /=; last by move=> [=])
    | rewrite /LRC.check_belong /= ];
    rewrite orbF;
    (case Hbelm: (color ti == cl2) => /=; last by move=> [=]);
    (case Has: (is_address vt2) => /=);
    move=> H; case: (obind_inv H) => st3 [Edu [= <- _]] /=;
    have [Hre Hme] := load_du Edu Hr1 Hw1 Hr2;
    by split; [ exact: Hre | eexists; split; [ exact: Hme | by [] ] ].
Qed.

Lemma nsuap_is_code (s s' : st) (op0 : opcode) (tpc : tag_type lrc_tags Symbolic.P) (ti : mem_tag)
   (ts : hseq (tag_type lrc_tags) (inputs op0)) (updts : seq Symbolic.update) (pc' : mword mt) (e : option event) :
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s
    (IVec (OP op0) tpc ti ts) updts pc' = Some (s', e) -> is_code ti.
Proof.
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state.
  case: (Symbolic.mem s pc') => [ni|];
    (case: (Symbolic.evi s) => [evinp|]; last by move=> [=]);
    rewrite /Merged.transfer /= /Merged.instr_rules /=;
    by case: (is_code ti) => /=; [ move=> _ | move=> [=] ].
Qed.

Lemma pc_tag_eta (t : tag_type lrc_tags Symbolic.P) : exists l c, t = build_tpc l c.
Proof. by case: t => l c; exists l, c. Qed.

Lemma nsuap_evi (s s' : st) (kiv : Symbolic.k_ivec lrc_tags) (updts : seq Symbolic.update)
   (pc' : mword mt) (e : option event) :
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s kiv updts pc' = Some (s', e) ->
  exists ei, Symbolic.evi s = Some ei.
Proof.
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state.
  by case Hevi: (Symbolic.evi s) => [ei|]; [ exists ei | move=> [=] ].
Qed.

Lemma alloc_block_const_value {T : ordType} {S : eqType}
      (f : nat -> T) (a : S) (k : nat) (w : T) (d : S) :
  mkfmap (mkseq (fun n => (f n, a)) k) w = Some d -> d = a.
Proof. move=> H; move/mkfmap_Some: H; rewrite /mkseq => /mapP[x _ [= _ ->]] //. Qed.

Local Opaque unionm mkfmap mkseq.

Lemma pad_valid_step (s s' : st) (ev : option event) :
  pad_valid s -> step_me (NC := NC) s s' ev -> pad_valid s'.
Proof.
  move=> [PV1 PV2] Hstep; rewrite /step_me in Hstep; inversion Hstep; subst.
  -
    move: NEXT => /nsuap_extract [op0 [ov0 [st0 [Hds [Hmem Hreg]]]]].
    have ? := ndsu_nil Hds; subst st0.
    split.
    + by move=> r0 w t; rewrite Hreg Hmem => Hr Hc; exact: (PV1 _ _ _ Hr Hc).
    + by move=> w v t; rewrite Hmem => Hw Hc; exact: (PV2 _ _ _ Hw Hc).
  -
    have [Hmem Hreg] := const_nsu_valid OLD NEXT.
    split.
    + move=> r0 w t; rewrite Hreg setmE; case: (r0 =P r) => [_|_].
      * by move=> [= _ <-] Hcp; discriminate Hcp.
      * by move=> Hr Hc; rewrite Hmem; exact: (PV1 _ _ _ Hr Hc).
    + by move=> w v t; rewrite Hmem => Hw Hc; exact: (PV2 _ _ _ Hw Hc).
  -
    have [Hmem Hreg] := mov_nsu_valid R1W OLD NEXT.
    split.
    + move=> r0 w t; rewrite Hreg !setmE.
      case: (r0 =P r2) => [_|_].
      * by move=> [= <- <-] Hc; rewrite Hmem; exact: (PV1 _ _ _ R1W Hc).
      * case: (r0 =P r1) => [_|_].
        -- by move=> [= _ <-]; case: (is_address t1) => /= Hcp; discriminate Hcp.
        -- by move=> Hr Hc; rewrite Hmem; exact: (PV1 _ _ _ Hr Hc).
    + by move=> w v t; rewrite Hmem => Hw Hc; exact: (PV2 _ _ _ Hw Hc).
  -
    have [Hmem Hcpu] := binop_nsu_cpu NEXT.
    split.
    + by move=> r0 w t Hr0 Hc; rewrite Hmem; exact: (PV1 _ _ _ (Hcpu _ _ _ Hr0 Hc) Hc).
    + by move=> w v t; rewrite Hmem => Hw Hc; exact: (PV2 _ _ _ Hw Hc).
  -
    have [Hreg [tc [Hmem Hnc]]] := load_nsu R1W MEM1 OLD NEXT.
    split.
    + move=> r0 w t; rewrite Hreg !setmE.
      case: (r0 =P r2) => [_|_].
      * move=> [= <- <-] Hc.
        apply: (addr_ok_mono _ (PV2 _ _ _ MEM1 Hc)).
        move=> w' c Hw'; rewrite Hmem setmE; case: (w' =P w1) => [_|_]; [ by eexists | by exists c ].
      * case: (r0 =P r1) => [_|_].
        -- by move=> [= _ <-] Hcp; discriminate Hcp.
        -- move=> Hr Hc.
           apply: (addr_ok_mono _ (PV1 _ _ _ Hr Hc)).
           move=> w' c Hw'; rewrite Hmem setmE; case: (w' =P w1) => [_|_]; [ by eexists | by exists c ].
    + move=> w v t; rewrite Hmem setmE; case: (w =P w1) => [_|_].
      * by move=> [= <- <-] Hc; rewrite Hnc in Hc; discriminate Hc.
      * move=> Hw Hc.
        apply: (addr_ok_mono _ (PV2 _ _ _ Hw Hc)).
        move=> w' c Hw'; rewrite setmE; case: (w' =P w1) => [_|_]; [ by eexists | by exists c ].
  -
    have [Hcpu [tc [Hmem Hvt]]] := store_nsu NEXT.
    split.
    + move=> r0 w t Hr0 Hc.
      apply: (addr_ok_mono _ (PV1 _ _ _ (Hcpu _ _ _ Hr0 Hc) Hc)).
      move=> w' c Hw'; rewrite Hmem setmE; case: (w' =P w1) => [_|_]; [ by eexists | by exists c ].
    + move=> w v t; rewrite Hmem setmE; case: (w =P w1) => [_|_].
      * move=> [= <- <-] Hc; move: Hc; rewrite Hvt => Hcc.
        apply: (addr_ok_mono _ (PV1 _ _ _ R2W Hcc)).
        move=> w' c Hw'; rewrite setmE; case: (w' =P w1) => [_|_]; [ by eexists | by exists c ].
      * move=> Hw Hc.
        apply: (addr_ok_mono _ (PV2 _ _ _ Hw Hc)).
        move=> w' c Hw'; rewrite setmE; case: (w' =P w1) => [_|_]; [ by eexists | by exists c ].
  -
    have [level [ctpc Etpc]] := pc_tag_eta tpc0.
    rewrite /mvec Etpc in NEXT.
    pose st0 := @Symbolic.State mt lrc_tags unit mem0 reg (pc0 @ (build_tpc level ctpc)) extra.
    have Hic := nsuap_is_code NEXT.
    have [evinp Hevi] := nsuap_evi NEXT.
    have [Hcolor Hdisj] := jump_step_inv Hic RW RA CLEAR NEXT.
    case: Hdisj => [[Hbel Ht1]|[n [celltgt [rcv [Hmw [Hnbel [Ht1 [Hlvl Hrcom]]]]]]]].
    + subst t1.
      move: NEXT.
      rewrite (jump_internal_nsuap (s := st0) Hic RW RA CLEAR Hbel Hcolor Hevi) => [= <- _].
      by split; [ move=> r0 w0 t Hr0 Hc; exact: (PV1 _ _ _ Hr0 Hc)
                | move=> w0 v t Hw0 Hc; exact: (PV2 _ _ _ Hw0 Hc) ].
    + have Ht1' : t1 = Ret level.-1 by rewrite Ht1 Hlvl.
      have Hlv : 0 < level by rewrite Hlvl.
      rewrite Ht1' in RW CLEAR.
      have Hrne : r != rcom by apply/eqP => E; move: RW; rewrite E Hrcom; case.
      have Harne : ra != rcom by [].
      have Hbelne : color ti0 != color (taga celltgt)
        by move: Hnbel; rewrite PaddingSim.belong_someE.
      have [sd [Hsd Hmsd]] := return_clear_1 (s0 := st0) RA RW Hrcom Hrne Harne CLEAR.
      move: NEXT.
      rewrite (jump_return_nsuap (s := st0) rav rat
                 Hic erefl Hcolor Hmw Hbelne RW Hrcom Hlv CLEAR Hevi Hsd)
        => [= <- _].
      have [Hcpu _] := ndsu_allR Hsd isT (@cpu_refl reg).
      split.
      * move=> r0 w0 t Hr0 Hc; rewrite /= Hmsd; exact: (PV1 _ _ _ (Hcpu _ _ _ Hr0 Hc) Hc).
      * move=> w0 v t; rewrite /= Hmsd => Hw0 Hc; exact: (PV2 _ _ _ Hw0 Hc).
  -
    have [Hmem Hreg] := bnz_nsu_valid RW NEXT.
    split.
    + move=> r0 w0 t; rewrite Hreg setmE; case: (r0 =P r) => [_|_].
      * by move=> [= _ <-] Hcp; discriminate Hcp.
      * by move=> Hr Hc; rewrite Hmem; exact: (PV1 _ _ _ Hr Hc).
    + by move=> w0 v t; rewrite Hmem => Hw Hc; exact: (PV2 _ _ _ Hw Hc).
  -
    have [level [ctpc Etpc]] := pc_tag_eta tpc0.
    rewrite /mvec Etpc in NEXT.
    pose st0 := @Symbolic.State mt lrc_tags unit mem0 reg (pc0 @ (build_tpc level ctpc)) extra.
    have Hic := nsuap_is_code NEXT.
    have [evinp Hevi] := nsuap_evi NEXT.
    have [a1 Ha1] : exists a1, reg rcom = Some a1.
    { case E: (reg rcom) => [a1|]; first by exists a1.
      exfalso; move: NEXT.
      by rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state /Symbolic.evi E /=. }
    have Hdomk : forall k, k \in [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N ->
                   exists a, reg (as_word (ssrint.Posz k)) = Some a.
    { move=> k Hk; apply: (reg_clear_list_aux_dom CLEAR); by rewrite in_cons Hk orbT. }
    have [lh1 Hlh1] : exists lh1,
        Symbolic.reg_clear_list_aux [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N reg (taga a1) = Some lh1.
    { apply: reg_clear_list_aux_total => e He; exact: Hdomk. }
    have Ha1' : reg (as_word (ssrint.Posz 1)) = Some a1 by exact: Ha1.
    have Hcl1 : Symbolic.reg_clear_list reg told = Some (HSeqCons told lh1).
    { rewrite /Symbolic.reg_clear_list /Symbolic.reg_list.
      exact: (@rcla_cons_some 1 [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N reg told a1 lh1 Ha1' Hlh1). }
    have Hleq : l = HSeqCons told lh1 by move: CLEAR; rewrite Hcl1 => -[= <-].
    have [Hcolor [Hcret Hdisj]] := jal_step_inv Hic RA OLD CLEAR NEXT.
    rewrite Hleq in NEXT.
    case: Hdisj => [Hbel1 | [celltgt [rcv [Hmw0 [Hbel1 [Hrcom [u Hentry]]]]]]].
    +
      move: NEXT.
      rewrite (jal_internal_nsuap (s := st0) Hic RA OLD Ha1 Hlh1 Hbel1 Hcolor Hcret Hevi) => [= <- _].
      split.
      * move=> r0 w0 t; rewrite /= setmE; case: eqP => [_|_].
        -- by move=> [= Ew Et] _; subst; rewrite /addr_ok; left; exists (vret @ tret).
        -- move=> Hr0 Hc; exact: (PV1 _ _ _ Hr0 Hc).
      * move=> w0 v t Hw0 Hc; exact: (PV2 _ _ _ Hw0 Hc).
    +
      have Hbelne : color ti0 != color (taga celltgt) by move: Hbel1; rewrite PaddingSim.belong_someE.
      have Hentry' : check_entry (color ti0) (Some (taga celltgt)) = Some tt by move: Hentry; case: u.
      have [p Hpname] : exists p, get_proc_name (Some (taga celltgt)) = Some p.
      { move: Hentry; rewrite /check_entry /get_proc_name.
        case: (taga celltgt) => [vt cc0 ee ic]; case: ee => [[pp el]|] /= H; last by [].
        by exists pp. }
      have Ea1 : a1 = rcv @ Other by move: Ha1; rewrite Hrcom => -[= <-].
      have Hta1 : taga a1 = Other by rewrite Ea1 taga_at.
      have [a0 Ha0] : exists a, reg (as_word (ssrint.Posz 0)) = Some a by apply: Hdomk.
      have [cc Hcc] : exists cc,
          Symbolic.reg_clear_list_aux [:: 2; 3; 5; 6; 7; 16; 17; 18; 19]%N reg (taga a0) = Some cc.
      { apply: reg_clear_list_aux_total => kk Hkk; apply: Hdomk; by rewrite in_cons Hkk orbT. }
      have Hlh1' : lh1 = HSeqCons (taga a1) cc.
      { have H := @rcla_cons_some 0 [:: 2; 3; 5; 6; 7; 16; 17; 18; 19]%N reg (taga a1) a0 cc Ha0 Hcc.
        by move: Hlh1; rewrite H => -[= <-]. }
      rewrite Hlh1' Hta1 in NEXT.
      have Hmemst : Symbolic.mem st0 (vala (Symbolic.pc st0) + 1)%w = Some (vret @ tret) by exact: RA.
      have [sd [Hsd [Hmsd Hcpu]]] := jal_call_clear_1 (s0 := st0) level Hmemst OLD Hrcom Hdomk.
      move: NEXT.
      rewrite (@jal_call_nsuap st0 sd ti0 (swcast imm) tret told level ctpc p cc celltgt evinp
                 Hic erefl Hcolor Hcret Hmw0 Hbelne Hpname Hentry' Hevi Hsd) => [= <- _].
      split.
      * move=> r0 w0 t Hr0 Hc; rewrite /= Hmsd.
        move: (Hcpu _ _ _ Hr0 Hc); rewrite setmE; case: eqP => [_|_].
        -- by move=> [= Ew Et]; subst; rewrite /addr_ok; left; exists (vret @ tret).
        -- move=> Hr0'; exact: (PV1 _ _ _ Hr0' Hc).
      * move=> w0 v t; rewrite /= Hmsd => Hw0 Hc; exact: (PV2 _ _ _ Hw0 Hc).
  -
    have Hsem : Symbolic.sem sc = LRC.alloc_fun (NC := NC).
    { move: GETCALL; rewrite /Instance.table /Merged.table mkfmapE /=.
      case: ifP => [_ [= <-] //|_]. by move=> [=]. }
    have Hent : Symbolic.entry_tag sc = tt by case: (Symbolic.entry_tag sc).
    have Halloc1 : LRC.alloc_fun (NC := NC)
                     (@Symbolic.State mt lrc_tags unit mem0 reg (pc0 @ tpc0) extra) = Some s'.
    { move: CALL; rewrite /Symbolic.run_syscall Hsem Hent /=.
      case Hevi: (Symbolic.evi _) => [i|] //=.
      rewrite /Merged.transfer /=.
      by case Halloc: (LRC.alloc_fun (NC := NC) _) => [s|] //= [= <- _]. }
    move: Halloc1; rewrite {1}/LRC.alloc_fun /= => H1.
    case: (obind_inv H1) => ra_val [Hra1 {}H1].
    case: (obind_inv H1) => u1 [Hjmp1 {}H1].
    case: (obind_inv H1) => reta1 [Hreta1 {}H1].
    case: (obind_inv H1) => uret [Hretchk1 {}H1].
    move: Hretchk1; case: ifP => Hretc1 Hretc1'; last by [].
    case: (obind_inv H1) => sz1 [Hsz1 {}H1].
    case: (obind_inv H1) => uoth [Hoth1 {}H1].
    case: (obind_inv H1) => len1 [Hlen1 {}H1].
    case: (obind_inv H1) => ulen [Hlenchk1 {}H1].
    move: H1; case: ifP => // Hpf1 H1.
    case: (obind_inv H1) => addr1 [Haddr1 {}H1].
    case: (obind_inv H1) => regs1' [Hregs1' {}H1].
    move: H1 => [= Hs1'].
    have [vold Hvold] : exists vold, reg syscall_ret = Some vold.
    { case E: (reg syscall_ret) => [vold|]; first by exists vold.
      by move: Hregs1'; rewrite /updm E. }
    have Hregs1eq : regs1' = setm reg syscall_ret (addr1 @ Other)
      by move: Hregs1'; rewrite (updm_R Hvold) => -[= <-].
    have Hext : forall w' c, mem0 w' = Some c -> exists c', Symbolic.mem s' w' = Some c'.
    { move=> w' c Hc; rewrite -Hs1' /= unionmE Hc /=; by exists c. }
    have Hregeq : Symbolic.regs s' = setm reg syscall_ret (addr1 @ Other)
      by rewrite -Hs1' /= Hregs1eq.
    split.
    + move=> r0 w0 t; rewrite Hregeq setmE; case: eqP => [_|_].
      * by move=> [= _ <-].
      * move=> Hr0 Hc; apply: (addr_ok_mono Hext); exact: (PV1 _ _ _ Hr0 Hc).
    + move=> w0 v t Hw0 Hc; rewrite -Hs1' /= unionmE in Hw0; move: Hw0; case Hm0: (mem0 w0) => [c|].
      * move=> [= E]; rewrite E in Hm0; apply: (addr_ok_mono Hext); exact: (PV2 _ _ _ Hm0 Hc).
      * move=> Hbloc; exfalso.
        move: (congr1 taga (alloc_block_const_value Hbloc)); rewrite !taga_at => Ht.
        by move: Hc; rewrite Ht.
Qed.

Lemma imt_jal_nonterm (i : Merged.instr) (lp : nat -> nat -> nat) (pos : nat) (w : imm mt) :
  Jal w = instr_merged_to_mp i lp pos -> PaddingSim.is_term i = false.
Proof. by case: i. Qed.

Lemma imt_nop_nonterm i lp pos :
  Nop mt = instr_merged_to_mp i lp pos -> PaddingSim.is_term i = false.
Proof. by case: i. Qed.
Lemma imt_const_nonterm i lp pos w r :
  Const w r = instr_merged_to_mp i lp pos -> PaddingSim.is_term i = false.
Proof. by case: i. Qed.
Lemma imt_mov_nonterm i lp pos r1 r2 :
  Mov r1 r2 = instr_merged_to_mp i lp pos -> PaddingSim.is_term i = false.
Proof. by case: i. Qed.
Lemma imt_binop_nonterm i lp pos b r1 r2 r3 :
  Binop b r1 r2 r3 = instr_merged_to_mp i lp pos -> PaddingSim.is_term i = false.
Proof. by case: i. Qed.
Lemma imt_load_nonterm i lp pos r1 r2 :
  Load r1 r2 = instr_merged_to_mp i lp pos -> PaddingSim.is_term i = false.
Proof. by case: i. Qed.
Lemma imt_store_nonterm i lp pos r1 r2 :
  Store r1 r2 = instr_merged_to_mp i lp pos -> PaddingSim.is_term i = false.
Proof. by case: i. Qed.
Lemma imt_bnz_nonterm i lp pos r w :
  Bnz r w = instr_merged_to_mp i lp pos -> PaddingSim.is_term i = false.
Proof. by case: i. Qed.

Lemma imt_jal_target (i : Merged.instr) (lp : nat -> nat -> nat) (pos : nat) (w : imm mt) :
  Jal w = instr_merged_to_mp i lp pos -> exists l, w = @word_of_nat (imm_size mt) (lp l pos).
Proof. by case: i => //= l [= ->]; exists l. Qed.

Lemma imt_bnz_target (i : Merged.instr) (lp : nat -> nat -> nat) (pos : nat) (r : Types.reg mt) (w : imm mt) :
  Bnz r w = instr_merged_to_mp i lp pos -> exists l, w = @word_of_nat (imm_size mt) (lp l pos - pos).
Proof. by case: i => //= rc l [= _ ->]; exists l. Qed.

Lemma imt_bnz_inv (i : Merged.instr) (lp : nat -> nat -> nat) (pos : nat) (r : Types.reg mt) (w : imm mt) :
  Bnz r w = instr_merged_to_mp i lp pos ->
  exists rc l, i = MrBnz rc l /\ w = @word_of_nat (imm_size mt) (lp l pos - pos).
Proof. by case: i => //= rc l [= _ ->]; exists rc, l. Qed.

Definition in_crange (w : mword mt) : Prop :=
  size (@Merged.initial_memory mt (prog_buffers q)) <= (val w : nat) /\
  (val w : nat) < size (@Merged.initial_memory mt (prog_buffers q)) + size (code q).

Definition cptr_code (s : st) : Prop :=
  (forall r w t, Symbolic.regs s r = Some (w @ t) -> is_codeptr t -> in_crange w) /\
  (forall w v t, Symbolic.mem s w = Some (v @ t) -> is_codeptr (vtag t) -> in_crange v).

Lemma cptr_code_step (s s' : st) (ev : option event) :
  (forall w a, Symbolic.mem s w = Some a -> is_code (taga a) -> encode_code (code q) pc0 w = Some a) ->
  cptr_code s -> step_me (NC := NC) s s' ev -> cptr_code s'.
Proof.
  move=> Hciso [CC1 CC2] Hstep; rewrite /step_me in Hstep; inversion Hstep; subst.
  -
    move: NEXT => /nsuap_extract [op0 [ov0 [st0 [Hds [Hmem Hreg]]]]].
    have ? := ndsu_nil Hds; subst st0.
    by split; [ move=> r0 w t; rewrite Hreg => Hr Hc; exact: (CC1 _ _ _ Hr Hc)
              | move=> w v t; rewrite Hmem => Hw Hc; exact: (CC2 _ _ _ Hw Hc) ].
  -
    have [Hmem Hreg] := const_nsu_valid OLD NEXT.
    split.
    + move=> r0 w t; rewrite Hreg setmE; case: (r0 =P r) => [_|_].
      * by move=> [= _ <-] Hcp; discriminate Hcp.
      * by move=> Hr Hc; exact: (CC1 _ _ _ Hr Hc).
    + by move=> w v t; rewrite Hmem => Hw Hc; exact: (CC2 _ _ _ Hw Hc).
  -
    have [Hmem Hreg] := mov_nsu_valid R1W OLD NEXT.
    split.
    + move=> r0 w t; rewrite Hreg !setmE; case: (r0 =P r2) => [_|_].
      * by move=> [= <- <-] Hc; exact: (CC1 _ _ _ R1W Hc).
      * case: (r0 =P r1) => [_|_].
        -- by move=> [= _ <-]; case: (is_address t1) => /= Hcp; discriminate Hcp.
        -- by move=> Hr Hc; exact: (CC1 _ _ _ Hr Hc).
    + by move=> w v t; rewrite Hmem => Hw Hc; exact: (CC2 _ _ _ Hw Hc).
  -
    have [Hmem Hcpu] := binop_nsu_cpu NEXT.
    split.
    + by move=> r0 w t Hr0 Hc; exact: (CC1 _ _ _ (Hcpu _ _ _ Hr0 Hc) Hc).
    + by move=> w v t; rewrite Hmem => Hw Hc; exact: (CC2 _ _ _ Hw Hc).
  -
    have [Hreg [tc [Hmem Hnc]]] := load_nsu R1W MEM1 OLD NEXT.
    split.
    + move=> r0 w t; rewrite Hreg !setmE; case: (r0 =P r2) => [_|_].
      * by move=> [= <- <-] Hc; exact: (CC2 _ _ _ MEM1 Hc).
      * case: (r0 =P r1) => [_|_].
        -- by move=> [= _ <-] Hcp; discriminate Hcp.
        -- by move=> Hr Hc; exact: (CC1 _ _ _ Hr Hc).
    + move=> w v t; rewrite Hmem setmE; case: (w =P w1) => [_|_].
      * by move=> [= <- <-] Hc; rewrite Hnc in Hc; discriminate Hc.
      * by move=> Hw Hc; exact: (CC2 _ _ _ Hw Hc).
  -
    have [Hcpu [tc [Hmem Hvt]]] := store_nsu NEXT.
    split.
    + by move=> r0 w t Hr0 Hc; exact: (CC1 _ _ _ (Hcpu _ _ _ Hr0 Hc) Hc).
    + move=> w v t; rewrite Hmem setmE; case: (w =P w1) => [_|_].
      * by move=> [= <- <-] Hc; move: Hc; rewrite Hvt => Hcc; exact: (CC1 _ _ _ R2W Hcc).
      * by move=> Hw Hc; exact: (CC2 _ _ _ Hw Hc).
  -
    have [level [ctpc Etpc]] := pc_tag_eta tpc0.
    rewrite /mvec Etpc in NEXT.
    pose st0 := @Symbolic.State mt lrc_tags unit mem0 reg (pc0 @ (build_tpc level ctpc)) extra.
    have Hic := nsuap_is_code NEXT.
    have [evinp Hevi] := nsuap_evi NEXT.
    have [Hcolor Hdisj] := jump_step_inv Hic RW RA CLEAR NEXT.
    case: Hdisj => [[Hbel Ht1]|[n [celltgt [rcv [Hmw [Hnbel [Ht1 [Hlvl Hrcom]]]]]]]].
    + subst t1.
      move: NEXT.
      rewrite (jump_internal_nsuap (s := st0) Hic RW RA CLEAR Hbel Hcolor Hevi) => [= <- _].
      by split; [ move=> r0 w0 t Hr0 Hc; exact: (CC1 _ _ _ Hr0 Hc)
                | move=> w0 v t Hw0 Hc; exact: (CC2 _ _ _ Hw0 Hc) ].
    + have Ht1' : t1 = Ret level.-1 by rewrite Ht1 Hlvl.
      have Hlv : 0 < level by rewrite Hlvl.
      rewrite Ht1' in RW CLEAR.
      have Hrne : r != rcom by apply/eqP => E; move: RW; rewrite E Hrcom; case.
      have Harne : ra != rcom by [].
      have Hbelne : color ti0 != color (taga celltgt)
        by move: Hnbel; rewrite PaddingSim.belong_someE.
      have [sd [Hsd Hmsd]] := return_clear_1 (s0 := st0) RA RW Hrcom Hrne Harne CLEAR.
      move: NEXT.
      rewrite (jump_return_nsuap (s := st0) rav rat
                 Hic erefl Hcolor Hmw Hbelne RW Hrcom Hlv CLEAR Hevi Hsd) => [= <- _].
      have [Hcpu _] := ndsu_allR Hsd isT (@cpu_refl reg).
      split.
      * by move=> r0 w0 t Hr0 Hc; exact: (CC1 _ _ _ (Hcpu _ _ _ Hr0 Hc) Hc).
      * by move=> w0 v t; rewrite /= Hmsd => Hw0 Hc; exact: (CC2 _ _ _ Hw0 Hc).
  -
    have [Hmem Hreg] := bnz_nsu_valid RW NEXT.
    split.
    + move=> r0 w0 t; rewrite Hreg setmE; case: (r0 =P r) => [_|_].
      * by move=> [= _ <-] Hcp; discriminate Hcp.
      * by move=> Hr Hc; exact: (CC1 _ _ _ Hr Hc).
    + by move=> w0 v t; rewrite Hmem => Hw Hc; exact: (CC2 _ _ _ Hw Hc).
  -
    have Hic := nsuap_is_code NEXT.
    have Hpc1 : in_crange (pc0 + 1)%w.
    { have Hcell := Hciso _ _ PC Hic.
      have [n [im [tm [Hn [Hweq [Hnth [Htag Hdec]]]]]]] := code_cell_q Hcell.
      have Hterm : is_term im = false.
      { have H1 := Hdec; rewrite vala_at INST in H1.
        move: H1 => [= H1]; exact: (imt_jal_nonterm H1). }
      have Hn1 := nonterm_succ_lt Hn Hnth Hterm.
      rewrite /in_crange Hweq word_of_nat_succ val_word_of_nat.
      * move: Hn1; lia.
      * have := alloc_label_lt_word; move: Hn1 Hbound; lia. }
    have [level [ctpc Etpc]] := pc_tag_eta tpc0.
    rewrite /mvec Etpc in NEXT.
    pose st0 := @Symbolic.State mt lrc_tags unit mem0 reg (pc0 @ (build_tpc level ctpc)) extra.
    have Hic' := nsuap_is_code NEXT.
    have [evinp Hevi] := nsuap_evi NEXT.
    have [a1 Ha1] : exists a1, reg rcom = Some a1.
    { case E: (reg rcom) => [a1|]; first by exists a1.
      exfalso; move: NEXT.
      by rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state /Symbolic.evi E /=. }
    have Hdomk : forall k, k \in [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N ->
                   exists a, reg (as_word (ssrint.Posz k)) = Some a.
    { move=> k Hk; apply: (reg_clear_list_aux_dom CLEAR); by rewrite in_cons Hk orbT. }
    have [lh1 Hlh1] : exists lh1,
        Symbolic.reg_clear_list_aux [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N reg (taga a1) = Some lh1.
    { apply: reg_clear_list_aux_total => e He; exact: Hdomk. }
    have Ha1' : reg (as_word (ssrint.Posz 1)) = Some a1 by exact: Ha1.
    have Hcl1 : Symbolic.reg_clear_list reg told = Some (HSeqCons told lh1).
    { rewrite /Symbolic.reg_clear_list /Symbolic.reg_list.
      exact: (@rcla_cons_some 1 [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N reg told a1 lh1 Ha1' Hlh1). }
    have Hleq : l = HSeqCons told lh1 by move: CLEAR; rewrite Hcl1 => -[= <-].
    have [Hcolor [Hcret Hdisj]] := jal_step_inv Hic' RA OLD CLEAR NEXT.
    rewrite Hleq in NEXT.
    case: Hdisj => [Hbel1 | [celltgt [rcv [Hmw0 [Hbel1 [Hrcom [u Hentry]]]]]]].
    + move: NEXT.
      rewrite (jal_internal_nsuap (s := st0) Hic' RA OLD Ha1 Hlh1 Hbel1 Hcolor Hcret Hevi) => [= <- _].
      split.
      * move=> r0 w0 t; rewrite /= setmE; case: eqP => [_|_].
        -- by move=> [= Ew Et] _; subst; exact: Hpc1.
        -- by move=> Hr0 Hc; exact: (CC1 _ _ _ Hr0 Hc).
      * by move=> w0 v t Hw0 Hc; exact: (CC2 _ _ _ Hw0 Hc).
    + have Hbelne : color ti0 != color (taga celltgt) by move: Hbel1; rewrite PaddingSim.belong_someE.
      have Hentry' : check_entry (color ti0) (Some (taga celltgt)) = Some tt by move: Hentry; case: u.
      have [p Hpname] : exists p, get_proc_name (Some (taga celltgt)) = Some p.
      { move: Hentry; rewrite /check_entry /get_proc_name.
        case: (taga celltgt) => [vt cc0 ee ic]; case: ee => [[pp el]|] /= H; last by []. by exists pp. }
      have Ea1 : a1 = rcv @ Other by move: Ha1; rewrite Hrcom => -[= <-].
      have Hta1 : taga a1 = Other by rewrite Ea1 taga_at.
      have [a0 Ha0] : exists a, reg (as_word (ssrint.Posz 0)) = Some a by apply: Hdomk.
      have [cc Hcc] : exists cc,
          Symbolic.reg_clear_list_aux [:: 2; 3; 5; 6; 7; 16; 17; 18; 19]%N reg (taga a0) = Some cc.
      { apply: reg_clear_list_aux_total => kk Hkk; apply: Hdomk; by rewrite in_cons Hkk orbT. }
      have Hlh1' : lh1 = HSeqCons (taga a1) cc.
      { have H := @rcla_cons_some 0 [:: 2; 3; 5; 6; 7; 16; 17; 18; 19]%N reg (taga a1) a0 cc Ha0 Hcc.
        by move: Hlh1; rewrite H => -[= <-]. }
      rewrite Hlh1' Hta1 in NEXT.
      have Hmemst : Symbolic.mem st0 (vala (Symbolic.pc st0) + 1)%w = Some (vret @ tret) by exact: RA.
      have [sd [Hsd [Hmsd Hcpu]]] := jal_call_clear_1 (s0 := st0) level Hmemst OLD Hrcom Hdomk.
      move: NEXT.
      rewrite (@jal_call_nsuap st0 sd ti0 (swcast imm) tret told level ctpc p cc celltgt evinp
                 Hic' erefl Hcolor Hcret Hmw0 Hbelne Hpname Hentry' Hevi Hsd) => [= <- _].
      split.
      * move=> r0 w0 t Hr0 Hc.
        move: (Hcpu _ _ _ Hr0 Hc); rewrite setmE; case: eqP => [_|_].
        -- by move=> [= Ew Et]; subst; exact: Hpc1.
        -- by move=> Hr0'; exact: (CC1 _ _ _ Hr0' Hc).
      * by move=> w0 v t; rewrite /= Hmsd => Hw0 Hc; exact: (CC2 _ _ _ Hw0 Hc).
  -
    have Hsem : Symbolic.sem sc = LRC.alloc_fun (NC := NC).
    { move: GETCALL; rewrite /Instance.table /Merged.table mkfmapE /=.
      case: ifP => [_ [= <-] //|_]. by move=> [=]. }
    have Hent : Symbolic.entry_tag sc = tt by case: (Symbolic.entry_tag sc).
    have Halloc1 : LRC.alloc_fun (NC := NC)
                     (@Symbolic.State mt lrc_tags unit mem0 reg (pc0 @ tpc0) extra) = Some s'.
    { move: CALL; rewrite /Symbolic.run_syscall Hsem Hent /=.
      case Hevi: (Symbolic.evi _) => [i|] //=.
      rewrite /Merged.transfer /=.
      by case Halloc: (LRC.alloc_fun (NC := NC) _) => [s|] //= [= <- _]. }
    move: Halloc1; rewrite {1}/LRC.alloc_fun /= => H1.
    case: (obind_inv H1) => ra_val [Hra1 {}H1].
    case: (obind_inv H1) => u1 [Hjmp1 {}H1].
    case: (obind_inv H1) => reta1 [Hreta1 {}H1].
    case: (obind_inv H1) => uret [Hretchk1 {}H1].
    move: Hretchk1; case: ifP => Hretc1 Hretc1'; last by [].
    case: (obind_inv H1) => sz1 [Hsz1 {}H1].
    case: (obind_inv H1) => uoth [Hoth1 {}H1].
    case: (obind_inv H1) => len1 [Hlen1 {}H1].
    case: (obind_inv H1) => ulen [Hlenchk1 {}H1].
    move: H1; case: ifP => // Hpf1 H1.
    case: (obind_inv H1) => addr1 [Haddr1 {}H1].
    case: (obind_inv H1) => regs1' [Hregs1' {}H1].
    move: H1 => [= Hs1'].
    have [vold Hvold] : exists vold, reg syscall_ret = Some vold.
    { case E: (reg syscall_ret) => [vold|]; first by exists vold.
      by move: Hregs1'; rewrite /updm E. }
    have Hregeq : Symbolic.regs s' = setm reg syscall_ret (addr1 @ Other)
      by rewrite -Hs1' /= (updm_R Hvold) in Hregs1' *; move: Hregs1' => [= <-].
    split.
    + move=> r0 w t; rewrite Hregeq setmE; case: eqP => [_|_].
      * by move=> [= _ <-] Hcp; discriminate Hcp.
      * by move=> Hr Hc; exact: (CC1 _ _ _ Hr Hc).
    + move=> w v t Hw; rewrite -Hs1' /= unionmE in Hw; move: Hw; case Hm0: (mem0 w) => [c|].
      * by move=> [= E] Hc; rewrite E in Hm0; exact: (CC2 _ _ _ Hm0 Hc).
      * move=> Hbloc Hc; exfalso.
        move: (congr1 taga (alloc_block_const_value Hbloc)); rewrite !taga_at => Ht.
        by move: Hc; rewrite Ht.
Qed.

Lemma addr_in_code (x : nat) :
  x < size (code q) -> (val (@word_of_nat (word_size mt) (pc0 + x)) : nat) < pc0 + size (code q).
Proof.
  move=> Hx; rewrite val_word_of_nat.
  - move: Hx; lia.
  - have := alloc_label_lt_word; move: Hx Hbound; lia.
Qed.

Lemma pc1_in_code (n : nat) :
  n.+1 < size (code q) ->
  (val ((@word_of_nat (word_size mt) (n + pc0) + 1)%w) : nat) < pc0 + size (code q).
Proof.
  move=> Hn1; rewrite word_of_nat_succ val_word_of_nat.
  - move: Hn1; lia.
  - have := alloc_label_lt_word; move: Hn1 Hbound; lia.
Qed.

Definition pc_safe (s : st) : Prop :=
  ((val (vala (Symbolic.pc s)) : nat) < size (@Merged.initial_memory mt (prog_buffers q)) + size (code q))
  \/ (size (@Merged.initial_memory mt (prog_buffers q)) + size padc <= (val (vala (Symbolic.pc s)) : nat)).

Lemma pc_safe_step (s s' : st) (ev : option event) :
  (forall w a, Symbolic.mem s w = Some a -> is_code (taga a) -> encode_code (code q) pc0 w = Some a) ->
  cptr_code s -> step_me (NC := NC) s s' ev -> pc_safe s'.
Proof.
  move=> Hciso [CC1 _] Hstep; rewrite /step_me in Hstep; inversion Hstep; subst; rewrite /pc_safe.
  1-6: have Hpc := nsuap_pc NEXT; have Hic := nsuap_is_code NEXT; have Hcell := Hciso _ _ PC Hic.
  1-6: case: (code_cell_q Hcell) => ncc [imc [tmc [Hn [Hweq [Hnth [Htag Hdec]]]]]].
  1-6: have H1 := Hdec; rewrite vala_at INST in H1; move: H1 => [= H1].
  1-6: left; move: Hpc; rewrite /Symbolic.pcv /= Hweq => ->.
  - exact: (pc1_in_code (nonterm_succ_lt Hn Hnth (imt_nop_nonterm   H1))).
  - exact: (pc1_in_code (nonterm_succ_lt Hn Hnth (imt_const_nonterm H1))).
  - exact: (pc1_in_code (nonterm_succ_lt Hn Hnth (imt_mov_nonterm   H1))).
  - exact: (pc1_in_code (nonterm_succ_lt Hn Hnth (imt_binop_nonterm H1))).
  - exact: (pc1_in_code (nonterm_succ_lt Hn Hnth (imt_load_nonterm  H1))).
  - exact: (pc1_in_code (nonterm_succ_lt Hn Hnth (imt_store_nonterm H1))).
  -
    have Hpc := nsuap_pc NEXT.
    have Hic := nsuap_is_code NEXT.
    have [level [ctpc Etpc]] := pc_tag_eta tpc0.
    rewrite /mvec Etpc in NEXT.
    have [Hcolor Hdisj] := jump_step_inv Hic RW RA CLEAR NEXT.
    have Ht1c : is_codeptr t1 by case: Hdisj => [[_ ->]|[? [? [? [_ [_ [-> _]]]]]]].
    by left; move: Hpc => ->; exact: (proj2 (CC1 _ _ _ RW Ht1c)).
  -
    have Hpc := nsuap_pc NEXT.
    have Hic := nsuap_is_code NEXT.
    have Hcell := Hciso _ _ PC Hic.
    case: (code_cell_q Hcell) => ncc [imc [tmc [Hn [Hweq [Hnth [Htag Hdec]]]]]].
    have H1 := Hdec; rewrite vala_at INST in H1; move: H1 => [= H1].
    move: Hpc; rewrite /pc'; case: ifP => [Hw0|Hwn].
    +
      rewrite Hweq => ->.
      left; exact: (pc1_in_code (nonterm_succ_lt Hn Hnth (imt_bnz_nonterm H1))).
    +
      have [rc [l0 [Himc Hn_eq]]] := imt_bnz_inv H1.
      rewrite Hweq Hn_eq.
      case Hfo: (findopt (fun p => match p.1 with MrLabel l1 => l0 == l1 | _ => false end) (code q)) => [m|].
      * have Hmlt := findopt_lt Hfo.
        rewrite addw_word_of_nat_swcast'; last by move: Hmlt Hbound; lia.
        move=> ->; left; rewrite val_word_of_nat;
          [ move: Hmlt Hn; lia | have := alloc_label_lt_word; move: Hmlt Hn Hbound; lia ].
      * rewrite Himc in Hnth.
        have [m Hm] := bnz_labels_resolved Hnth.
        by congruence.
  -
    have Hpc := nsuap_pc NEXT.
    have Hic := nsuap_is_code NEXT.
    have Hcell := Hciso _ _ PC Hic.
    case: (code_cell_q Hcell) => ncc [imc [tmc [Hn [Hweq [Hnth [Htag Hdec]]]]]].
    have H1 := Hdec; rewrite vala_at INST in H1; move: H1 => [= H1].
    case: (imt_jal_target H1) => l0 Himm.
    move: Hpc; rewrite /pc' Himm.
    case Hfo: (findopt (fun p => match p.1 with MrLabel l1 => l0 == l1 | _ => false end) (code q)) => [m|].
    + have Hm := findopt_lt Hfo.
      have Hb : size (@Merged.initial_memory mt (prog_buffers q)) + m < alloc_label
        by move: Hm Hbound; lia.
      by rewrite (swcast_word_of_nat_id Hb) => ->; left; exact: (addr_in_code Hm).
    + case: ifP => [Hal|Hal].
      * move/eqP: Hal => Hal; rewrite Hal swcast_alloc => ->.
        right; rewrite (val_word_of_nat alloc_label_lt_word); move: Hbound'; lia.
      * have Hb : size (@Merged.initial_memory mt (prog_buffers q)) + ncc < alloc_label
          by move: Hn Hbound; lia.
        by rewrite (swcast_word_of_nat_id Hb) => ->; left; exact: (addr_in_code Hn).
  -
    have Hsem : Symbolic.sem sc = LRC.alloc_fun (NC := NC).
    { move: GETCALL; rewrite /Instance.table /Merged.table mkfmapE /=.
      case: ifP => [_ [= <-] //|_]. by move=> [=]. }
    have Hent : Symbolic.entry_tag sc = tt by case: (Symbolic.entry_tag sc).
    have Halloc1 : LRC.alloc_fun (NC := NC)
                     (@Symbolic.State mt lrc_tags unit mem0 reg (pc0 @ tpc0) extra) = Some s'.
    { move: CALL; rewrite /Symbolic.run_syscall Hsem Hent /=.
      case Hevi: (Symbolic.evi _) => [i|] //=.
      rewrite /Merged.transfer /=.
      by case Halloc: (LRC.alloc_fun (NC := NC) _) => [s|] //= [= <- _]. }
    move: Halloc1; rewrite {1}/LRC.alloc_fun /= => H1.
    case: (obind_inv H1) => ra_val [Hra1 {}H1].
    case: (obind_inv H1) => u1 [Hjmp1 {}H1].
    case: (obind_inv H1) => reta1 [Hreta1 {}H1].
    case: (obind_inv H1) => uret [Hretchk1 {}H1].
    move: Hretchk1; case: ifP => Hretc1 Hretc1'; last by [].
    case: (obind_inv H1) => sz1 [Hsz1 {}H1].
    case: (obind_inv H1) => uoth [Hoth1 {}H1].
    case: (obind_inv H1) => len1 [Hlen1 {}H1].
    case: (obind_inv H1) => ulen [Hlenchk1 {}H1].
    move: H1; case: ifP => // Hpf1 H1.
    case: (obind_inv H1) => addr1 [Haddr1 {}H1].
    case: (obind_inv H1) => regs1' [Hregs1' {}H1].
    move: H1 => [= Hs1'].
    have Hjc : taga ra_val = InternalJump := is_jump_invE Hjmp1.
    have Hra1' : Symbolic.regs (@Symbolic.State mt lrc_tags unit mem0 reg (pc0 @ tpc0) extra) ra
               = Some ((vala ra_val) @ (taga ra_val)) by rewrite /= atom_etaE.
    left; rewrite -Hs1' /=.
    apply: (proj2 (CC1 _ _ _ Hra1' _)); by rewrite Hjc.
Qed.

Lemma in_crange_val (w : mword mt) :
  size (@Merged.initial_memory mt (prog_buffers q)) <= (val w : nat) ->
  (val w : nat) < size (@Merged.initial_memory mt (prog_buffers q)) + size (code q) ->
  in_crange w.
Proof. by move=> H1 H2; rewrite /in_crange; split. Qed.

Lemma pc1_in_range (n : nat) :
  n.+1 < size (code q) -> in_crange ((@word_of_nat (word_size mt) (n + pc0) + 1)%w).
Proof.
  move=> Hn1; apply: in_crange_val.
  - rewrite word_of_nat_succ val_word_of_nat;
      [ move: Hn1; lia | have := alloc_label_lt_word; move: Hn1 Hbound; lia ].
  - rewrite word_of_nat_succ val_word_of_nat;
      [ move: Hn1; lia | have := alloc_label_lt_word; move: Hn1 Hbound; lia ].
Qed.

Lemma addr_in_range (x : nat) :
  x < size (code q) -> in_crange (@word_of_nat (word_size mt) (pc0 + x)).
Proof.
  move=> Hx; apply: in_crange_val.
  - rewrite val_word_of_nat; [ move: Hx; lia | have := alloc_label_lt_word; move: Hx Hbound; lia ].
  - rewrite val_word_of_nat; [ move: Hx; lia | have := alloc_label_lt_word; move: Hx Hbound; lia ].
Qed.

Definition pc_pos (s : st) : Prop :=
  in_crange (vala (Symbolic.pc s)) \/ Symbolic.mem s (vala (Symbolic.pc s)) = None.

Lemma pc_pos_step (s s' : st) (ev : option event) :
  (forall w a, Symbolic.mem s w = Some a -> is_code (taga a) -> encode_code (code q) pc0 w = Some a) ->
  cptr_code s ->
  Symbolic.mem s' (@word_of_nat (word_size mt) alloc_label) = None ->
  step_me (NC := NC) s s' ev -> pc_pos s'.
Proof.
  move=> Hciso [CC1 _] Hanm' Hstep; rewrite /step_me in Hstep; inversion Hstep; subst; rewrite /pc_pos.
  1-6: have Hpc := nsuap_pc NEXT; have Hic := nsuap_is_code NEXT; have Hcell := Hciso _ _ PC Hic.
  1-6: case: (code_cell_q Hcell) => ncc [imc [tmc [Hn [Hweq [Hnth [Htag Hdec]]]]]].
  1-6: have H1 := Hdec; rewrite vala_at INST in H1; move: H1 => [= H1].
  1-6: left; move: Hpc; rewrite /Symbolic.pcv /= Hweq => ->.
  - exact: (pc1_in_range (nonterm_succ_lt Hn Hnth (imt_nop_nonterm   H1))).
  - exact: (pc1_in_range (nonterm_succ_lt Hn Hnth (imt_const_nonterm H1))).
  - exact: (pc1_in_range (nonterm_succ_lt Hn Hnth (imt_mov_nonterm   H1))).
  - exact: (pc1_in_range (nonterm_succ_lt Hn Hnth (imt_binop_nonterm H1))).
  - exact: (pc1_in_range (nonterm_succ_lt Hn Hnth (imt_load_nonterm  H1))).
  - exact: (pc1_in_range (nonterm_succ_lt Hn Hnth (imt_store_nonterm H1))).
  -
    have Hpc := nsuap_pc NEXT.
    have Hic := nsuap_is_code NEXT.
    have [level [ctpc Etpc]] := pc_tag_eta tpc0.
    rewrite /mvec Etpc in NEXT.
    have [Hcolor Hdisj] := jump_step_inv Hic RW RA CLEAR NEXT.
    have Ht1c : is_codeptr t1 by case: Hdisj => [[_ ->]|[? [? [? [_ [_ [-> _]]]]]]].
    by left; move: Hpc => ->; exact: (CC1 _ _ _ RW Ht1c).
  -
    have Hpc := nsuap_pc NEXT.
    have Hic := nsuap_is_code NEXT.
    have Hcell := Hciso _ _ PC Hic.
    case: (code_cell_q Hcell) => ncc [imc [tmc [Hn [Hweq [Hnth [Htag Hdec]]]]]].
    have H1 := Hdec; rewrite vala_at INST in H1; move: H1 => [= H1].
    move: Hpc; rewrite /pc'; case: ifP => [Hw0|Hwn].
    + rewrite Hweq => ->.
      left; exact: (pc1_in_range (nonterm_succ_lt Hn Hnth (imt_bnz_nonterm H1))).
    + have [rc [l0 [Himc Hn_eq]]] := imt_bnz_inv H1.
      rewrite Hweq Hn_eq.
      case Hfo: (findopt (fun p => match p.1 with MrLabel l1 => l0 == l1 | _ => false end) (code q)) => [m|].
      * have Hmlt := findopt_lt Hfo.
        rewrite addw_word_of_nat_swcast'; last by move: Hmlt Hbound; lia.
        move=> ->; left; apply: in_crange_val.
        { rewrite val_word_of_nat;
            [ move: Hmlt Hn; lia | have := alloc_label_lt_word; move: Hmlt Hn Hbound; lia ]. }
        rewrite val_word_of_nat;
          [ move: Hmlt Hn; lia | have := alloc_label_lt_word; move: Hmlt Hn Hbound; lia ].
      * rewrite Himc in Hnth.
        have [m Hm] := bnz_labels_resolved Hnth.
        by congruence.
  -
    have Hpc := nsuap_pc NEXT.
    have Hic := nsuap_is_code NEXT.
    have Hcell := Hciso _ _ PC Hic.
    case: (code_cell_q Hcell) => ncc [imc [tmc [Hn [Hweq [Hnth [Htag Hdec]]]]]].
    have H1 := Hdec; rewrite vala_at INST in H1; move: H1 => [= H1].
    case: (imt_jal_target H1) => l0 Himm.
    move: Hpc; rewrite /pc' Himm.
    case Hfo: (findopt (fun p => match p.1 with MrLabel l1 => l0 == l1 | _ => false end) (code q)) => [m|].
    + have Hm := findopt_lt Hfo.
      have Hb : size (@Merged.initial_memory mt (prog_buffers q)) + m < alloc_label
        by move: Hm Hbound; lia.
      by rewrite (swcast_word_of_nat_id Hb) => ->; left; exact: (addr_in_range Hm).
    + case: ifP => [Hal|Hal].
      * move/eqP: Hal => Hal; rewrite Hal swcast_alloc => ->.
        right; exact: Hanm'.
      * have Hb : size (@Merged.initial_memory mt (prog_buffers q)) + ncc < alloc_label
          by move: Hn Hbound; lia.
        by rewrite (swcast_word_of_nat_id Hb) => ->; left; exact: (addr_in_range Hn).
  -
    have Hsem : Symbolic.sem sc = LRC.alloc_fun (NC := NC).
    { move: GETCALL; rewrite /Instance.table /Merged.table mkfmapE /=.
      case: ifP => [_ [= <-] //|_]. by move=> [=]. }
    have Hent : Symbolic.entry_tag sc = tt by case: (Symbolic.entry_tag sc).
    have Halloc1 : LRC.alloc_fun (NC := NC)
                     (@Symbolic.State mt lrc_tags unit mem0 reg (pc0 @ tpc0) extra) = Some s'.
    { move: CALL; rewrite /Symbolic.run_syscall Hsem Hent /=.
      case Hevi: (Symbolic.evi _) => [i|] //=.
      rewrite /Merged.transfer /=.
      by case Halloc: (LRC.alloc_fun (NC := NC) _) => [s|] //= [= <- _]. }
    move: Halloc1; rewrite {1}/LRC.alloc_fun /= => H1.
    case: (obind_inv H1) => ra_val [Hra1 {}H1].
    case: (obind_inv H1) => u1 [Hjmp1 {}H1].
    case: (obind_inv H1) => reta1 [Hreta1 {}H1].
    case: (obind_inv H1) => uret [Hretchk1 {}H1].
    move: Hretchk1; case: ifP => Hretc1 Hretc1'; last by [].
    case: (obind_inv H1) => sz1 [Hsz1 {}H1].
    case: (obind_inv H1) => uoth [Hoth1 {}H1].
    case: (obind_inv H1) => len1 [Hlen1 {}H1].
    case: (obind_inv H1) => ulen [Hlenchk1 {}H1].
    move: H1; case: ifP => // Hpf1 H1.
    case: (obind_inv H1) => addr1 [Haddr1 {}H1].
    case: (obind_inv H1) => regs1' [Hregs1' {}H1].
    move: H1 => [= Hs1'].
    have Hjc : taga ra_val = InternalJump := is_jump_invE Hjmp1.
    have Hra1' : Symbolic.regs (@Symbolic.State mt lrc_tags unit mem0 reg (pc0 @ tpc0) extra) ra
               = Some ((vala ra_val) @ (taga ra_val)) by rewrite /= atom_etaE.
    left; rewrite -Hs1' /=.
    apply: (CC1 _ _ _ Hra1' _); by rewrite Hjc.
Qed.

End CodeShiftValid.
