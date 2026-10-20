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

Section PaddingCorrect.

Variable NC : nat.

Local Notation state := (@Symbolic.state mt LRC.lrc_tags unit).

Definition pstep (ge : unit) (s : state) (t : trace) (s' : state) : Prop :=
  match t with
  | [::]      => step_me s s' None     (NC := NC)
  | [:: e]    => step_me s s' (Some e) (NC := NC)
  | _         => False
  end.

Definition pfinal : state -> Prop :=
  fun '(Symbolic.State m r (Types.Atom pc _) _) =>
    match m pc with
    | None => False
    | Some (Types.Atom i tag) =>
        Types.decode_instr i = Some (Types.Halt _) /\ is_code tag = true
    end.

Definition mergedsem (prg : program) : semantics :=
  {| Smallstep.state := state;
     Smallstep.genvtype := unit;
     Smallstep.step := pstep;
     Smallstep.initial_state :=
       fun s => s = Merged.initial_state (code prg) (prog_buffers prg) (prog_interface prg);
     Smallstep.final_state := pfinal;
     Smallstep.globalenv := tt |}.

Lemma det_mergedsem prg : determinate (mergedsem prg).
Proof.
  econstructor; intros; unfold mergedsem in *.
  - simpl in *. unfold pstep, step_me in *.
    destruct t1, t2; try destruct t1; try destruct t2; try contradiction;
      setoid_rewrite <- Exec.stepP in H; setoid_rewrite <- Exec.stepP in H0;
      rewrite H in H0; inv H0; (split; [try destruct e0; try econstructor | done]).
  - unfold single_events. intros.
    destruct t; try destruct t; try contradiction; simpl; lia.
  - simpl in *. subst. done.
  - simpl in *. intros t s' step. unfold pstep, step_me in step.
    destruct t; try destruct t; try contradiction;
      setoid_rewrite <- Exec.stepP in step; unfold Exec.stepf in step;
      destruct s, pc0; unfold pfinal in H; destruct (mem0 vala); try auto; destruct a;
      destruct H as [eq ?]; rewrite eq in step; simpl in step; inversion step.
Qed.

Fixpoint shift_pos (sizes : seq (nat * nat)) (p : nat) : nat :=
  match sizes with
  | [::] => p
  | (s, n) :: rest => if p < s then p else n + shift_pos rest (p - s)
  end.

Lemma shift_pos_ge sizes p :
  all (fun x => x.1 <= x.2) sizes -> p <= shift_pos sizes p.
Proof.
  elim: sizes p => [|[s n] rest IH] p //= /andP[Hsn Hall].
  case: (ltnP p s) => Hps; first by [].
  have Hrec := IH (p - s) Hall. move: Hps Hsn Hrec; lia.
Qed.

Lemma shift_pos_mono sizes p q :
  all (fun x => x.1 <= x.2) sizes -> p <= q -> shift_pos sizes p <= shift_pos sizes q.
Proof.
  elim: sizes p q => [|[s n] rest IH] p q //= /andP[Hsn Hall] Hpq.
  case: (ltnP p s) => Hps; case: (ltnP q s) => Hqs.
  - exact: Hpq.
  - move: Hps Hsn; lia.
  - move: Hps Hqs Hpq; lia.
  - have Hle : p - s <= q - s by move: Hps Hpq; lia.
    have Hrec := IH (p - s) (q - s) Hall Hle. move: Hrec; lia.
Qed.

Definition block_sizes (bs bs' : seq (@Merged.code mt)) : seq (nat * nat) :=
  [seq (size p.1, maxn (size p.1) (size p.2)) | p <- zip bs bs'].

Definition pad_block_sizes (cde cde' : @Merged.code mt) : seq (nat * nat) :=
  block_sizes (proc_split cde) (proc_split cde').

Lemma block_sizes_le bs bs' : all (fun x => x.1 <= x.2) (block_sizes bs bs').
Proof. rewrite /block_sizes all_map. by elim: (zip bs bs') => //= p s IH; rewrite leq_maxl. Qed.
Lemma pad_block_sizes_le cde cde' : all (fun x => x.1 <= x.2) (pad_block_sizes cde cde').
Proof. exact: block_sizes_le. Qed.

Lemma size_block_pad_max n b : size b <= n -> size (block_pad n b) = n.
Proof. move=> H; rewrite block_pad_size; lia. Qed.

Lemma block_sizes_cons b b' bs bs' :
  block_sizes (b :: bs) (b' :: bs')
  = (size b, maxn (size b) (size b')) :: block_sizes bs bs'.
Proof. by []. Qed.

Lemma shift_pos_cons s n rest p :
  shift_pos ((s, n) :: rest) p = if p < s then p else n + shift_pos rest (p - s).
Proof. by []. Qed.

Lemma align_blocks_cons b b' bs bs' :
  (align_blocks (b :: bs) (b' :: bs')).1
  = block_pad (maxn (size b) (size b')) b ++ (align_blocks bs bs').1.
Proof. rewrite /=. by case: (align_blocks bs bs'). Qed.

Lemma size_align_blocks_l b b' bs bs' :
  size (align_blocks (b :: bs) (b' :: bs')).1
  = maxn (size b) (size b') + size (align_blocks bs bs').1.
Proof.
  rewrite align_blocks_cons size_cat size_block_pad_max //; exact: leq_maxl.
Qed.

Lemma shift_pos_lt_size bs bs' n :
  size bs = size bs' -> n < size (flatten bs) ->
  shift_pos (block_sizes bs bs') n < size (align_blocks bs bs').1.
Proof.
  elim: bs bs' n => [|b bs IH] [|b' bs'] n.
  - by rewrite ltn0.
  - by [].
  - by [].
  - move=> Hsz0 Hi0; have Hsz : size bs = size bs' by move: Hsz0 => /= [].
    move: Hi0; rewrite [flatten (b :: bs)]/= size_cat => Hi.
    rewrite block_sizes_cons size_align_blocks_l shift_pos_cons.
    set sz := block_sizes bs bs'.
    case: (ltnP n (size b)) => Hnb.
    + have := leq_maxl (size b) (size b'); lia.
    + have := IH bs' (n - size b) Hsz; rewrite -/sz => H.
      have Hlt : n - size b < size (flatten bs) by lia.
      move: (H Hlt); lia.
Qed.

Lemma align_blocks_nth (bs bs' : seq (@Merged.code mt)) i
      (dflt : @Merged.instr mt * mem_tag) :
  size bs = size bs' -> i < size (flatten bs) ->
  nth dflt (align_blocks bs bs').1 (shift_pos (block_sizes bs bs') i)
  = nth dflt (flatten bs) i.
Proof.
  elim: bs bs' i => [|b bs IH] [|b' bs'] i; try by move=> _ _.
  move=> Hsz Hi.
  have Hsz' : size bs = size bs' by move: Hsz => /= [].
  move: Hi; rewrite [flatten (b :: bs)]/= size_cat => Hi.
  rewrite align_blocks_cons block_sizes_cons.
  set sz := block_sizes bs bs'.
  set n := maxn (size b) (size b').
  have Hbn : size b <= n by rewrite /n leq_maxl.
  have Hbp : size (block_pad n b) = n by exact: size_block_pad_max.
  case: (ltnP i (size b)) => Hib.
  - have Hsh : shift_pos ((size b, n) :: sz) i = i by rewrite shift_pos_cons ifT.
    rewrite Hsh nth_cat Hbp ifT; last by lia.
    rewrite /block_pad nth_cat ifT; last by [].
    by rewrite nth_cat ifT.
  - have Hsh : shift_pos ((size b, n) :: sz) i = n + shift_pos sz (i - size b)
      by rewrite shift_pos_cons ifF //; lia.
    rewrite Hsh nth_cat Hbp ifF; last by lia.
    rewrite addKn IH //; last by lia.
    by rewrite nth_cat ifF //; lia.
Qed.

Lemma pad_code_nth cde cde' i dflt :
  size (proc_split cde) = size (proc_split cde') -> i < size cde ->
  nth dflt (pad_code cde cde').1 (shift_pos (pad_block_sizes cde cde') i) = nth dflt cde i.
Proof.
  move=> Hcount Hi.
  have HR : nth dflt cde i = nth dflt (flatten (proc_split cde)) i
    by rewrite proc_split_flatten.
  rewrite /pad_code /pad_block_sizes HR.
  apply: align_blocks_nth; [exact: Hcount | by rewrite proc_split_flatten].
Qed.

Lemma findopt_cons T (pred : T -> bool) x s :
  findopt pred (x :: s)
  = if findopt pred s is Some n then Some (n + 1) else if pred x then Some 0 else None.
Proof. rewrite /findopt /=. by case: (foldr _ _ s). Qed.

Lemma findopt_cat T (pred : T -> bool) s1 s2 :
  findopt pred (s1 ++ s2)
  = if findopt pred s2 is Some n then Some (size s1 + n) else findopt pred s1.
Proof.
  elim: s1 => [|x s1 IH].
  - by rewrite cat0s; case: (findopt pred s2) => [n|].
  - rewrite cat_cons findopt_cons IH findopt_cons.
    case: (findopt pred s2) => [n|] //.
    by congr Some; rewrite [size (x :: s1)]/=; lia.
Qed.

Lemma findopt_nop (pred : (@Merged.instr mt * mem_tag) -> bool) k c :
  pred (nop_cell c) = false -> findopt pred (nseq k (nop_cell c)) = None.
Proof. move=> Hp; elim: k => [//|k IH]; by rewrite findopt_cons IH Hp. Qed.

Lemma findopt_lt T (pred : T -> bool) s k : findopt pred s = Some k -> k < size s.
Proof.
  elim: s k => [|x s IH] k.
  - by [].
  - rewrite findopt_cons [size (x :: s)]/=.
    case E: (findopt pred s) => [m|]; last case: (pred x).
    + by move=> [] <-; move: (IH m E); lia.
    + by move=> [] <-.
    + by [].
Qed.

Lemma findopt_align_blocks (pred : (@Merged.instr mt * mem_tag) -> bool) bs bs' :
  (forall c, pred (nop_cell c) = false) -> size bs = size bs' ->
  findopt pred (align_blocks bs bs').1
  = omap (shift_pos (block_sizes bs bs')) (findopt pred (flatten bs)).
Proof.
  Local Opaque shift_pos.
  move=> Hnop; elim: bs bs' => [|b bs IH] [|b' bs'].
  - by move=> _.
  - by move=> [].
  - by move=> [].
  - move=> Hsz0; have Hsz : size bs = size bs' by move: Hsz0 => /= [].
    rewrite align_blocks_cons block_sizes_cons [flatten (b :: bs)]/=.
    set sz := block_sizes bs bs'. set n := maxn (size b) (size b').
    have Hbp : size (block_pad n b) = n by rewrite size_block_pad_max // leq_maxl.
    rewrite findopt_cat -/sz Hbp (IH bs' Hsz).
    rewrite {1}/block_pad findopt_cat findopt_nop // findopt_cat.
    case Ef: (findopt pred (flatten bs)) => [m0|] /=.
    + by rewrite shift_pos_cons ifF; [rewrite addKn | lia].
    + case Eb: (findopt pred b) => [k|] //=.
      by rewrite shift_pos_cons ifT //; apply: (findopt_lt Eb).
  Local Transparent shift_pos.
Qed.

Lemma findopt_pad (pred : (@Merged.instr mt * mem_tag) -> bool) cde cde' :
  (forall c, pred (nop_cell c) = false) ->
  size (proc_split cde) = size (proc_split cde') ->
  findopt pred (pad_code cde cde').1
  = omap (shift_pos (pad_block_sizes cde cde')) (findopt pred cde).
Proof.
  move=> Hnop Hcount; rewrite /pad_code /pad_block_sizes findopt_align_blocks //.
  by rewrite proc_split_flatten.
Qed.

End PaddingCorrect.

Section PadRelabel.

Variables q q' : program.
Local Notation pc0 := (size (@Merged.initial_memory mt (prog_buffers q))).
Local Notation sizes := (pad_block_sizes (code q) (code q')).

Definition phi_nat (a : nat) : nat :=
  if a < pc0 then a else pc0 + shift_pos sizes (a - pc0).

Definition phi_addr (w : mword mt) : mword mt := word_of_nat (phi_nat (val w : nat)).

Lemma phi_nat_data a : a < pc0 -> phi_nat a = a.
Proof. by rewrite /phi_nat => ->. Qed.

Lemma phi_nat_ge a : a <= phi_nat a.
Proof.
  rewrite /phi_nat; case: ifP => // /negbT; rewrite -leqNgt => H.
  have := shift_pos_ge (a - pc0) (pad_block_sizes_le (code q) (code q')); lia.
Qed.

Lemma phi_nat_mono a b : a <= b -> phi_nat a <= phi_nat b.
Proof.
  rewrite /phi_nat => Hab; case: ifP => Ha; case: ifP => Hb.
  - exact: Hab.
  - move: Ha Hb; lia.
  - move: Ha Hb Hab; lia.
  - have H4 : a - pc0 <= b - pc0 by move: Ha Hb Hab; lia.
    have := shift_pos_mono (pad_block_sizes_le (code q) (code q')) H4; lia.
Qed.

End PadRelabel.

Section EncodeShift.

Variables q q' : program.
Local Notation pc0 := (size (@Merged.initial_memory mt (prog_buffers q))).
Local Notation padc := ((pad_code (code q) (code q')).1).

Hypothesis word_of_nat_inj : forall a b,
    a < 2^(word_size mt) -> b < 2^(word_size mt) ->
    word_of_nat (k := word_size mt) a = word_of_nat b -> a = b.
Hypothesis Hcount : size (proc_split (code q)) = size (proc_split (code q')).
Hypothesis Hbound  : pc0 + size (code q) < 2 ^ word_size mt.
Hypothesis Hbound' : pc0 + size padc < 2 ^ word_size mt.

Lemma phi_addr_code (n : nat) :
  n < size (code q) ->
  phi_addr q q' (word_of_nat (n + pc0)) = word_of_nat (shift_pos (pad_block_sizes (code q) (code q')) n + pc0).
Proof.
  move=> Hn.
  have Hlt : n + pc0 < 2 ^ word_size mt by lia.
  have Hv : (val (word_of_nat (n + pc0) : mword mt) : nat) = n + pc0
    by rewrite /word_of_nat valw_as_word modn_small.
  rewrite /phi_addr Hv /phi_nat ifF; last by lia.
  by rewrite addnK addnC.
Qed.

End EncodeShift.

Lemma does_prefix_dir (L1 L2 : semantics)
  (det1 : determinate L1) (det2 : determinate L2)
  (R : Smallstep.state L1 -> Smallstep.state L2 -> Prop)
  (Hinit : forall s1, Smallstep.initial_state L1 s1 ->
                 exists s2, Smallstep.initial_state L2 s2 /\ R s1 s2)
  (Hnoinit : (forall s1, ~ Smallstep.initial_state L1 s1) ->
              forall s2, ~ Smallstep.initial_state L2 s2)
  (Hstar : forall s1 s2 t s1', R s1 s2 -> Star L1 s1 t s1' ->
                          exists s2', Star L2 s2 t s2' /\ R s1' s2')
  (Hfinal : forall s1 s2, R s1 s2 ->
              (Smallstep.final_state L1 s1 <-> Smallstep.final_state L2 s2))
  (Hnostep : forall s1 s2, R s1 s2 -> Nostep L1 s1 -> Nostep L2 s2) :
  forall m, does_prefix L1 m -> does_prefix L2 m.
Proof.
  move=> m H. apply (does_prefix_equiv det1) in H. apply (does_prefix_equiv det2).
  case: H => [s s' t Hi Hstr | s s' t Hi Hstr Hns Hnf | s s' t Hi Hstr Hf | Hni | Hni].
  - have [s2 [Hi2 HR]] := Hinit _ Hi.
    have [s2' [Hstr2 _]] := Hstar _ _ _ _ HR Hstr.
    by econstructor; eauto.
  - have [s2 [Hi2 HR]] := Hinit _ Hi.
    have [s2' [Hstr2 HR']] := Hstar _ _ _ _ HR Hstr.
    apply: (does_FGoes_wrong Hi2 Hstr2); first exact: (Hnostep _ _ HR' Hns).
    by move=> Hf2; apply: Hnf; apply/(Hfinal _ _ HR').
  - have [s2 [Hi2 HR]] := Hinit _ Hi.
    have [s2' [Hstr2 HR']] := Hstar _ _ _ _ HR Hstr.
    apply: (does_FTerminates Hi2 Hstr2). by apply/(Hfinal _ _ HR').
  - by apply: does_no_initial_FGoes_wrong; apply: Hnoinit.
  - by apply: does_no_initial_FTbc; apply: Hnoinit.
Qed.

Lemma sim_star (L1 L2 : semantics)
  (R : Smallstep.state L1 -> Smallstep.state L2 -> Prop)
  (Hstep : forall s1 s2 t s1', R s1 s2 -> Step L1 s1 t s1' ->
                          exists s2', Star L2 s2 t s2' /\ R s1' s2') :
  forall s1 t s1', Star L1 s1 t s1' -> forall s2, R s1 s2 ->
              exists s2', Star L2 s2 t s2' /\ R s1' s2'.
Proof.
  move=> s1 t s1' H.
  elim: H => [s | s t1 s' t2 s'' t12 Hst Hstar IH Heq] s2 HR.
  - exists s2; split=> //. exact: star_refl.
  - have [u [Hu HRu]] := Hstep _ _ _ _ HR Hst.
    have [w [Hw HRw]] := IH _ HRu.
    exists w; split=> //. subst t12. exact: (star_trans Hu Hw erefl).
Qed.

Section PaddingTheorems.

Variable NC : nat.
Variables q q' : program.
Local Notation padl := ((pad_align q q').1).
Local Notation S := (@Symbolic.state mt LRC.lrc_tags unit).

Variable Rf : S -> S -> Prop.
Hypothesis Rf_init :
  Rf (Merged.initial_state (code q) (prog_buffers q) (prog_interface q))
     (Merged.initial_state (code padl) (prog_buffers padl) (prog_interface padl)).
Hypothesis Rf_step :
  forall s1 s2 t s1', Rf s1 s2 -> pstep NC tt s1 t s1' ->
                 exists s2', Star (mergedsem NC padl) s2 t s2' /\ Rf s1' s2'.
Hypothesis Rf_final :
  forall s1 s2, Rf s1 s2 -> (pfinal s1 <-> pfinal s2).
Hypothesis Rf_nostep :
  forall s1 s2, Rf s1 s2 -> Nostep (mergedsem NC q) s1 -> Nostep (mergedsem NC padl) s2.

Theorem padding_forward m :
  does_prefix (mergedsem NC q) m -> does_prefix (mergedsem NC padl) m.
Proof.
  apply: (does_prefix_dir (det_mergedsem NC q) (det_mergedsem NC padl) (R := Rf)).
  - move=> s1 ->. eexists; split; [reflexivity | exact: Rf_init].
  - by move=> Hno; case: (Hno _ erefl).
  - move=> s1 s2 t s1' HR HStar.
    exact: (@sim_star (mergedsem NC q) (mergedsem NC padl) Rf Rf_step _ _ _ HStar _ HR).
  - exact: Rf_final.
  - exact: Rf_nostep.
Qed.

Variable Rb : S -> S -> Prop.
Hypothesis Rb_init :
  Rb (Merged.initial_state (code padl) (prog_buffers padl) (prog_interface padl))
     (Merged.initial_state (code q) (prog_buffers q) (prog_interface q)).
Hypothesis Rb_step :
  forall s1 s2 t s1', Rb s1 s2 -> pstep NC tt s1 t s1' ->
                 exists s2', Star (mergedsem NC q) s2 t s2' /\ Rb s1' s2'.
Hypothesis Rb_final :
  forall s1 s2, Rb s1 s2 -> (pfinal s1 <-> pfinal s2).
Hypothesis Rb_nostep :
  forall s1 s2, Rb s1 s2 -> Nostep (mergedsem NC padl) s1 -> Nostep (mergedsem NC q) s2.

Theorem padding_backward m :
  does_prefix (mergedsem NC padl) m -> does_prefix (mergedsem NC q) m.
Proof.
  apply: (does_prefix_dir (det_mergedsem NC padl) (det_mergedsem NC q) (R := Rb)).
  - move=> s1 ->. eexists; split; [reflexivity | exact: Rb_init].
  - by move=> Hno; case: (Hno _ erefl).
  - move=> s1 s2 t s1' HR HStar.
    exact: (@sim_star (mergedsem NC padl) (mergedsem NC q) Rb Rb_step _ _ _ HStar _ HR).
  - exact: Rb_final.
  - exact: Rb_nostep.
Qed.

End PaddingTheorems.

Lemma match_traces_eq (t1 t2 : trace) : match_traces t1 t2 -> t1 = t2.
Proof. by case. Qed.

Section PaddingFromForward.

Variable NC : nat.
Variables q q' : program.
Local Notation padl := ((pad_align q q').1).
Local Notation S := (@Symbolic.state mt LRC.lrc_tags unit).

Variable Rf : S -> S -> Prop.
Hypothesis Rf_init :
  Rf (Merged.initial_state (code q) (prog_buffers q) (prog_interface q))
     (Merged.initial_state (code padl) (prog_buffers padl) (prog_interface padl)).
Hypothesis Rf_step1 :
  forall s1 s2 t s1', Rf s1 s2 -> pstep NC tt s1 t s1' ->
                 exists s2', pstep NC tt s2 t s2' /\ Rf s1' s2'.
Hypothesis Rf_final :
  forall s1 s2, Rf s1 s2 -> (pfinal s1 <-> pfinal s2).
Hypothesis Rf_nostep :
  forall s1 s2, Rf s1 s2 -> Nostep (mergedsem NC q) s1 -> Nostep (mergedsem NC padl) s2.

Theorem padding_forward_sf m :
  does_prefix (mergedsem NC q) m -> does_prefix (mergedsem NC padl) m.
Proof.
  apply: (does_prefix_dir (det_mergedsem NC q) (det_mergedsem NC padl) (R := Rf)).
  - move=> s1 ->. eexists; split; [reflexivity | exact: Rf_init].
  - by move=> Hno; case: (Hno _ erefl).
  - have Hstar1 : forall a b u a', Rf a b -> Step (mergedsem NC q) a u a' ->
                    exists b', Star (mergedsem NC padl) b u b' /\ Rf a' b'.
    { move=> a b u a' Hab Hst. have [b' [Hb Hab']] := Rf_step1 Hab Hst.
      exists b'; split=> //. apply: star_one; exact: Hb. }
    move=> s1 s2 t s1' HR HStar.
    exact: (@sim_star (mergedsem NC q) (mergedsem NC padl) Rf Hstar1 _ _ _ HStar _ HR).
  - exact: Rf_final.
  - exact: Rf_nostep.
Qed.

Theorem padding_backward_sf m :
  does_prefix (mergedsem NC padl) m -> does_prefix (mergedsem NC q) m.
Proof.
  have Rb_step : forall sp su t sp', Rf su sp -> Step (mergedsem NC padl) sp t sp' ->
                   exists su', Star (mergedsem NC q) su t su' /\ Rf su' sp'.
  { move=> sp su t sp' Hrf Hstep.
    case Hsf: (step_eval_me (NC := NC) su) => [[su0 ev0]|].
    - have Hsu : step_me (NC := NC) su su0 ev0 by apply/Exec.stepP; exact: Hsf.
      have Hpsu : pstep NC tt su (if ev0 is Some e then [:: e] else [::]) su0.
      { move: Hsu; clear Hsf; case: ev0 => [e|] Hsu; exact: Hsu. }
      have [sp0 [Hsp0 Hrf']] := Rf_step1 Hrf Hpsu.
      have [Hmt Heq] := sd_determ (det_mergedsem NC padl) _ _ _ _ _ Hstep Hsp0.
      have Htt := match_traces_eq Hmt.
      exists su0; split.
      + rewrite Htt. apply: star_one; exact: Hpsu.
      + rewrite /= (Heq Htt). exact: Hrf'.
    - exfalso.
      have Hns : Nostep (mergedsem NC q) su.
      { move=> tt0 s' Hps.
        have [ev Hsm] : exists ev, step_me (NC := NC) su s' ev.
        { move: Hps; rewrite /= /pstep; case: tt0 => [|e [|??]];
            [ move=> H; by exists None | move=> H; by exists (Some e) | by move=> [] ]. }
        have Hc : step_eval_me (NC := NC) su = Some (s', ev) by apply/Exec.stepP; exact: Hsm.
        rewrite Hsf in Hc. discriminate Hc. }
      have Hnsp := Rf_nostep Hrf Hns. exact: (Hnsp _ _ Hstep). }
  apply: (does_prefix_dir (det_mergedsem NC padl) (det_mergedsem NC q) (R := fun sp su => Rf su sp)).
  - move=> s1 ->. eexists; split; [reflexivity | exact: Rf_init].
  - by move=> Hno; case: (Hno _ erefl).
  - move=> sp su t sp' HR HStar.
    exact: (@sim_star (mergedsem NC padl) (mergedsem NC q) (fun sp su => Rf su sp) Rb_step _ _ _ HStar _ HR).
  - move=> sp su HR. apply: iff_sym; exact: (Rf_final HR).
  - move=> sp su HR Hnsp t su' Hsu. have [sp' [Hsp' _]] := Rf_step1 HR Hsu. exact: (Hnsp _ _ Hsp').
Qed.

End PaddingFromForward.
