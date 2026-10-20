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

Section ShiftInjective.

Lemma shift_pos_strict sizes p r :
  all (fun x => x.1 <= x.2) sizes -> p < r -> shift_pos sizes p < shift_pos sizes r.
Proof.
  elim: sizes p r => [|[s n] rest IH] p r.
  - by move=> _ Hpr; exact: Hpr.
  - move=> /andP[Hsn Hall] Hpr.
    simpl in Hsn.
    rewrite !shift_pos_cons.
    case: (ltnP p s) => Hps; case: (ltnP r s) => Hrs.
    + exact: Hpr.
    + have Hrec := shift_pos_ge (r - s) Hall. lia.
    + lia.
    + have Hlt : p - s < r - s by lia.
      have Hrec := IH (p - s) (r - s) Hall Hlt. lia.
Qed.

Lemma shift_pos_inj sizes p r :
  all (fun x => x.1 <= x.2) sizes -> shift_pos sizes p = shift_pos sizes r -> p = r.
Proof.
  move=> Hall Heq.
  case: (ltngtP p r) => // Hlt.
  - have := shift_pos_strict Hall Hlt; lia.
  - have := shift_pos_strict Hall Hlt; lia.
Qed.

End ShiftInjective.

Section WordArith.

Lemma valw_won (k n : nat) : val (@word_of_nat k n) = n %% 2 ^ k :> nat.
Proof. by rewrite /word_of_nat valw_as_word. Qed.

Lemma word_of_natDall (k a b : nat) :
  (@word_of_nat k a + @word_of_nat k b)%w = @word_of_nat k (a + b).
Proof.
  apply: word_nat_inj. rewrite /addw.
  move: (valw_won k a) (valw_won k b) => Ea Eb. rewrite Ea Eb.
  rewrite (valw_won k (a + b)) valw_as_word. by rewrite modnDm.
Qed.

Lemma onew_word_of_nat : @onew (word_size mt) = @word_of_nat (word_size mt) 1.
Proof. rewrite /onew /word_of_nat. congr as_word. Qed.

Lemma swcast_word_of_nat_id : forall x,
    x < alloc_label ->
    @swcast _ (word_size mt) (@word_of_nat (imm_size mt) x) = @word_of_nat (word_size mt) x.
Proof.
  move=> x Hx. have H15 : x < 2 ^ imm_size mt.
  { rewrite imm_size_mt. apply: (leq_trans Hx). rewrite /alloc_label leq_exp2l //. }
  by rewrite /swcast /word_of_nat (as_wordK H15).
Qed.

Lemma addw_word_of_nat_swcast : forall a b,
    a + b < alloc_label ->
    (@word_of_nat (word_size mt) a + @swcast _ (word_size mt) (@word_of_nat (imm_size mt) b))%w
      = @word_of_nat (word_size mt) (a + b).
Proof.
  move=> a b Hab. have Hb : b < alloc_label by apply: (leq_ltn_trans (leq_addl a b) Hab).
  rewrite (swcast_word_of_nat_id Hb) word_of_natDall. by [].
Qed.

Lemma addw_word_of_nat_swcast' : forall a b,
    b < alloc_label ->
    (@word_of_nat (word_size mt) a + @swcast _ (word_size mt) (@word_of_nat (imm_size mt) b))%w
      = @word_of_nat (word_size mt) (a + b).
Proof. move=> a b Hb. by rewrite (swcast_word_of_nat_id Hb) word_of_natDall. Qed.

Lemma swcast_word_of_nat_zero :
    @swcast _ (word_size mt) (@word_of_nat (imm_size mt) 0) = zerow.
Proof.
  have H : 0 < 2 ^ imm_size mt by rewrite imm_size_mt expn_gt0.
  rewrite /swcast /word_of_nat (as_wordK H) /zerow. exact: erefl.
Qed.

Lemma word_of_nat_succ : forall a,
    (@word_of_nat (word_size mt) a + 1)%w = @word_of_nat (word_size mt) (a + 1).
Proof. move=> a. rewrite onew_word_of_nat word_of_natDall. by []. Qed.

End WordArith.

Lemma nth_error_nth_lt {A : Type} (l : list A) n (d : A) :
  n < size l -> List.nth_error l n = Some (nth d l n).
Proof.
  elim: l n => [|x xs IH] [|n] //=. by move=> Hn; rewrite IH.
Qed.

Lemma nth_error_size_ex {A : Type} (l : list A) n :
  n < size l -> exists v, List.nth_error l n = Some v.
Proof.
  elim: l n => [|x xs IH] [|n] //=.
  - by move=> _; exists x.
  - exact: IH.
Qed.

Section CodeShift.

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

Lemma alloc_label_lt_word : alloc_label < 2 ^ (word_size mt).
Proof. rewrite /alloc_label word_size_mt ltn_exp2l //. Qed.

Local Notation lpf c :=
  (fun (l d : nat) =>
     match findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) c with
     | Some m => pc0 + m | None => if l == alloc_label then l else d end).

Lemma code_cell_q (w : mword mt) (v1 : matom) :
  encode_code (code q) pc0 w = Some v1 ->
  exists n i t,
    n < size (code q) /\ w = word_of_nat (n + pc0) /\
    List.nth_error (code q) n = Some (i, t) /\ taga v1 = t /\
    decode_instr (vala v1) = Some (instr_merged_to_mp i (lpf (code q)) (pc0 + n)).
Proof.
  move=> Henc.
  have [n [Hw [Hn Hfr1]]] := encode_code_nth_inv Henc.
  have [i [t [Hnth [Htag Hval]]]] := encode_code_foldr_nth Hfr1.
  exists n, i, t.
  have Hpos1 : pc0 + size (code q) - 1 - (size (code q) - 1 - n) = pc0 + n by lia.
  split; first exact: Hn.
  split; first exact: Hw.
  split; first exact: Hnth.
  split; first exact: Htag.
  by rewrite Hval /Merged.encode_instr_mp encodeK Hpos1.
Qed.

Lemma code_cell_padc (n : nat) (i : Merged.instr) (t : mem_tag) :
  n < size (code q) -> List.nth_error (code q) n = Some (i, t) ->
  exists v2, encode_code padc pc0 (word_of_nat (shift_pos sizes n + pc0)) = Some v2 /\
    taga v2 = t /\
    decode_instr (vala v2) = Some (instr_merged_to_mp i (lpf padc) (pc0 + shift_pos sizes n)).
Proof.
  move=> Hn Hnth.
  have Hflat : size (flatten (proc_split (code q))) = size (code q)
    by rewrite proc_split_flatten.
  have Hphi_lt : shift_pos sizes n < size padc.
  { rewrite /padc /pad_code. apply: shift_pos_lt_size; first exact: Hcount. by rewrite Hflat. }
  have Hpadnth : List.nth_error padc (shift_pos sizes n) = Some (i, t).
  { rewrite (nth_error_nth_lt (i, t)) // pad_code_nth // -(nth_error_nth_lt (i, t) Hn).
    by rewrite Hnth. }
  have [v2 Hfr2] : exists v, List.nth_error (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
      (encode_instr_atom x (lpf padc) (pc0 + size padc - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) padc).1
      (shift_pos sizes n) = Some v.
  { apply: nth_error_size_ex. by rewrite encode_code_foldr_size. }
  have [i2 [t2 [Hnth2 [Htag2 Hval2]]]] := encode_code_foldr_nth Hfr2.
  have Ei : i2 = i by congruence. have Et : t2 = t by congruence.
  exists v2.
  have Henc2 : encode_code padc pc0 (word_of_nat (shift_pos sizes n + pc0)) = Some v2
    by apply: (encode_code_nth word_of_nat_inj (ltn_trans Hbound' alloc_label_lt_word) Hfr2).
  have Hpos2 : pc0 + size padc - 1 - (size padc - 1 - shift_pos sizes n) = pc0 + shift_pos sizes n by lia.
  split; first exact: Henc2.
  split; first by rewrite Htag2 Et.
  rewrite Hval2 Ei /Merged.encode_instr_mp encodeK. by rewrite Hpos2.
Qed.

Lemma encode_code_dom (cde : @Merged.code mt) (k : nat) :
  pc0 + size cde < 2 ^ (word_size mt) -> k < size cde ->
  exists v, encode_code cde pc0 (word_of_nat (k + pc0)) = Some v.
Proof.
  move=> Hb Hk.
  have [v Hv] : exists v, List.nth_error (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
      (encode_instr_atom x
         (fun l default => match findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) cde
            with Some m => pc0 + m | None => if l == alloc_label then l else default end)
         (pc0 + size cde - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) cde).1 k = Some v.
  { apply: nth_error_size_ex. by rewrite encode_code_foldr_size. }
  exists v. exact: (encode_code_nth word_of_nat_inj Hb Hv).
Qed.

Lemma val_word_of_nat (x : nat) :
  x < 2 ^ (word_size mt) -> (val (@word_of_nat (word_size mt) x) : nat) = x.
Proof. move=> Hx. by rewrite valw_won modn_small. Qed.

Definition phia_nat (a : nat) : nat :=
  if a < pc0 then a
  else if a < pc0 + size (code q) then pc0 + shift_pos sizes (a - pc0)
  else a.

Definition phia (w : mword mt) : mword mt := word_of_nat (phia_nat (val w : nat)).

Lemma phia_nat_id_lo a : a < pc0 -> phia_nat a = a.
Proof. by rewrite /phia_nat => ->. Qed.

Lemma phia_nat_id_hi a : pc0 + size (code q) <= a -> phia_nat a = a.
Proof.
  move=> Ha. rewrite /phia_nat.
  case: (ltnP a pc0) => H1; first by move: Ha H1; lia.
  by case: (ltnP a (pc0 + size (code q))) => H2 //; move: Ha H2; lia.
Qed.

Lemma phia_addr_code (k : nat) :
  k < size (code q) ->
  phia (word_of_nat (k + pc0)) = word_of_nat (shift_pos sizes k + pc0).
Proof.
  move=> Hk.
  have Hk2 : k + pc0 < alloc_label by move: Hk Hbound; lia.
  rewrite /phia val_word_of_nat; last exact: (ltn_trans Hk2 alloc_label_lt_word).
  rewrite /phia_nat.
  case: (ltnP (k + pc0) pc0) => H1; first by exfalso; lia.
  case: (ltnP (k + pc0) (pc0 + size (code q))) => H2; last by exfalso; move: Hk H2; lia.
  by rewrite addnK addnC.
Qed.

Lemma swcast_alloc :
  @swcast _ (word_size mt) (@word_of_nat (imm_size mt) alloc_label) = @word_of_nat (word_size mt) alloc_label.
Proof.
  have H : alloc_label < 2 ^ imm_size mt by rewrite imm_size_mt /alloc_label ltn_exp2l //.
  by rewrite /swcast /word_of_nat (as_wordK H).
Qed.

Lemma phia_alloc_fixed :
  phia (@swcast _ (word_size mt) (@word_of_nat (imm_size mt) alloc_label))
  = @swcast _ (word_size mt) (@word_of_nat (imm_size mt) alloc_label).
Proof.
  rewrite swcast_alloc /phia val_word_of_nat; last exact: alloc_label_lt_word.
  rewrite phia_nat_id_hi; last by move: Hbound; lia.
  by [].
Qed.

Lemma phi_lt_padc k : k < size (code q) -> shift_pos sizes k < size padc.
Proof.
  move=> Hk. rewrite /padc /pad_code /sizes /pad_block_sizes.
  apply: shift_pos_lt_size; first exact: Hcount. by rewrite proc_split_flatten.
Qed.

Lemma jal_corr (l n : nat) :
  n < size (code q) ->
  @swcast _ (word_size mt) (@word_of_nat (imm_size mt) (lpf padc l (pc0 + shift_pos sizes n)))
  = phia (@swcast _ (word_size mt) (@word_of_nat (imm_size mt) (lpf (code q) l (pc0 + n)))).
Proof.
  move=> Hn. cbv beta.
  have Hfp : findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) padc
           = omap (shift_pos sizes)
               (findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code q))
    by apply: findopt_pad; [by move=> c | exact: Hcount].
  case E: (findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code q)) => [m|].
  - have Hm : m < size (code q) by apply: (findopt_lt E).
    have Hpm := phi_lt_padc Hm.
    have B1 : pc0 + shift_pos sizes m < alloc_label by move: Hm Hbound Hbound' Hpm; lia.
    have B2 : pc0 + m < alloc_label by move: Hm Hbound; lia.
    have EP : findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) padc
            = Some (shift_pos sizes m) by rewrite Hfp E.
    rewrite EP.
    change (@swcast _ (word_size mt) (@word_of_nat (imm_size mt) (pc0 + shift_pos sizes m))
          = phia (@swcast _ (word_size mt) (@word_of_nat (imm_size mt) (pc0 + m)))).
    rewrite (swcast_word_of_nat_id B1) (swcast_word_of_nat_id B2) (addnC pc0 m) (phia_addr_code Hm).
    by rewrite addnC.
  - have EP : findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) padc = None
      by rewrite Hfp E.
    rewrite EP.
    change (@swcast _ (word_size mt) (@word_of_nat (imm_size mt)
              (if l == alloc_label then l else pc0 + shift_pos sizes n))
          = phia (@swcast _ (word_size mt) (@word_of_nat (imm_size mt)
              (if l == alloc_label then l else pc0 + n)))).
    case: (altP (l =P alloc_label)) => [Hal|Hal].
    + by rewrite Hal phia_alloc_fixed.
    + have Hpn := phi_lt_padc Hn.
      have B1 : pc0 + shift_pos sizes n < alloc_label by move: Hn Hbound Hbound' Hpn; lia.
      have B2 : pc0 + n < alloc_label by move: Hn Hbound; lia.
      rewrite (swcast_word_of_nat_id B1) (swcast_word_of_nat_id B2) (addnC pc0 n) (phia_addr_code Hn).
      by rewrite addnC.
Qed.

Lemma bnz_corr (l n m : nat) :
  n < size (code q) ->
  findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code q) = Some m ->
  addw (@word_of_nat (word_size mt) (pc0 + shift_pos sizes n))
       (@swcast _ (word_size mt) (@word_of_nat (imm_size mt)
           (lpf padc l (pc0 + shift_pos sizes n) - (pc0 + shift_pos sizes n))))
  = phia (addw (@word_of_nat (word_size mt) (pc0 + n))
               (@swcast _ (word_size mt) (@word_of_nat (imm_size mt)
                   (lpf (code q) l (pc0 + n) - (pc0 + n))))).
Proof.
  move=> Hn E. cbv beta.
  have Hm : m < size (code q) by apply: (findopt_lt E).
  have Hpm := phi_lt_padc Hm. have Hpn := phi_lt_padc Hn.
  have Hfp : findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) padc
           = omap (shift_pos sizes)
               (findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code q))
    by apply: findopt_pad; [by move=> c | exact: Hcount].
  have EP : findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) padc
          = Some (shift_pos sizes m) by rewrite Hfp E.
  rewrite EP E.
  change (addw (@word_of_nat (word_size mt) (pc0 + shift_pos sizes n))
               (@swcast _ (word_size mt) (@word_of_nat (imm_size mt)
                   ((pc0 + shift_pos sizes m) - (pc0 + shift_pos sizes n))))
        = phia (addw (@word_of_nat (word_size mt) (pc0 + n))
                     (@swcast _ (word_size mt) (@word_of_nat (imm_size mt)
                         ((pc0 + m) - (pc0 + n)))))).
  rewrite !subnDl.
  have Bp : shift_pos sizes m - shift_pos sizes n < alloc_label by move: Hpm Hbound'; lia.
  have Bu : m - n < alloc_label by move: Hm Hbound; lia.
  rewrite [X in X = _] (addw_word_of_nat_swcast' (pc0 + shift_pos sizes n) Bp).
  rewrite [X in _ = phia X] (addw_word_of_nat_swcast' (pc0 + n) Bu).
  case: (leqP n m) => Hnm.
  - have Hsp : shift_pos sizes n <= shift_pos sizes m
      by apply: shift_pos_mono; [exact: pad_block_sizes_le | exact: Hnm].
    have -> : pc0 + shift_pos sizes n + (shift_pos sizes m - shift_pos sizes n) = pc0 + shift_pos sizes m
      by move: Hsp; lia.
    have -> : pc0 + n + (m - n) = pc0 + m by move: Hnm; lia.
    rewrite (addnC pc0 m) (phia_addr_code Hm). by rewrite addnC.
  - have Hsp : shift_pos sizes m < shift_pos sizes n
      by apply: shift_pos_strict; [exact: pad_block_sizes_le | exact: Hnm].
    have -> : pc0 + shift_pos sizes n + (shift_pos sizes m - shift_pos sizes n) = pc0 + shift_pos sizes n
      by move: Hsp; lia.
    have -> : pc0 + n + (m - n) = pc0 + n by move: Hnm; lia.
    rewrite (addnC pc0 n) (phia_addr_code Hn). by rewrite addnC.
Qed.

Local Notation st := (@Symbolic.state mt lrc_tags unit).

Definition rel_v (vt : value_tag) (v : mword mt) : mword mt :=
  if is_address vt then phia v else v.

Definition addr_ok (m : {fmap mword mt -> atom (mword mt) mem_tag}) (w : mword mt) : Prop :=
  (exists c, m w = Some c) \/ pc0 + size padc <= (val w) \/ (val w) < pc0.

Definition is_codeptr (t : value_tag) : bool :=
  match t with Ret _ | InternalJump => true | _ => false end.

Variant instr_corr_at (w : mword mt) : @Types.instr mt -> @Types.instr mt -> Prop :=
  | ica_other : forall i, (forall a, i <> Jal a) -> (forall r o, i <> Bnz r o) ->
                  instr_corr_at w i i
  | ica_jal : forall a1 a2, swcast a2 = phia (swcast a1) -> instr_corr_at w (Jal a1) (Jal a2)
  | ica_bnz : forall r o1 o2, addw (phia w) (swcast o2) = phia (addw w (swcast o1)) ->
                instr_corr_at w (Bnz r o1) (Bnz r o2).

Definition memwk (m1 m2 : {fmap mword mt -> atom (mword mt) mem_tag}) : Prop :=
  forall w a, m1 w = Some a -> is_code (taga a) = false ->
     exists v2, m2 w = Some (v2 @ (taga a)) /\ (vtag (taga a) <> Invalidated -> v2 = rel_v (vtag (taga a)) (vala a)).
Definition memwk_bwd (m1 m2 : {fmap mword mt -> atom (mword mt) mem_tag}) : Prop :=
  forall w a, m2 w = Some a -> is_code (taga a) = false ->
     exists a0, m1 w = Some a0 /\ taga a = taga a0
       /\ (vtag (taga a0) <> Invalidated -> vala a = rel_v (vtag (taga a0)) (vala a0)).

Definition match_pad (s1 s2 : st) : Prop :=
  vala (Symbolic.pc s2) = phia (vala (Symbolic.pc s1)) /\
  taga (Symbolic.pc s2) = taga (Symbolic.pc s1) /\
  Symbolic.internal s2 = Symbolic.internal s1 /\
  (forall r, oapp (fun a : ratom => exists v2, Symbolic.regs s2 r = Some (v2 @ (taga a))
                       /\ (taga a <> Invalidated -> v2 = rel_v (taga a) (vala a)))
                  (Symbolic.regs s2 r = None)
                  (Symbolic.regs s1 r)) /\
  (forall w a, Symbolic.mem s1 w = Some a -> is_code (taga a) -> encode_code (code q) pc0 w = Some a) /\
  (forall w a, encode_code (code q) pc0 w = Some a -> Symbolic.mem s1 w = Some a) /\
  (forall w a, Symbolic.mem s2 w = Some a -> is_code (taga a) -> encode_code padc pc0 w = Some a) /\
  (forall w a, encode_code padc pc0 w = Some a -> Symbolic.mem s2 w = Some a) /\
  memwk (Symbolic.mem s1) (Symbolic.mem s2) /\
  memwk_bwd (Symbolic.mem s1) (Symbolic.mem s2).

Definition pad_valid (s : st) : Prop :=
  (forall r w t, Symbolic.regs s r = Some (w @ t) -> is_codeptr t -> addr_ok (Symbolic.mem s) w) /\
  (forall w v t, Symbolic.mem s w = Some (v @ t) -> is_codeptr (vtag t) ->
     addr_ok (Symbolic.mem s) v).

Definition is_term (i : @Merged.instr mt) : bool :=
  match i with MrJump _ | MrHalt => true | _ => false end.

Hypothesis fallthrough_aligned : forall n i t,
  n.+1 < size (code q) -> nth_error (code q) n = Some (i, t) -> is_term i = false ->
  shift_pos sizes (n.+1) = (shift_pos sizes n).+1.

Hypothesis code_last_term : forall n i t,
  n.+1 = size (code q) -> nth_error (code q) n = Some (i, t) -> is_term i = true.

Hypothesis bnz_labels_resolved : forall n r l t,
  nth_error (code q) n = Some (MrBnz r l, t) ->
  exists m, findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code q) = Some m.

Lemma nonterm_succ_lt n i t :
  n < size (code q) -> nth_error (code q) n = Some (i, t) -> is_term i = false ->
  n.+1 < size (code q).
Proof.
  move=> Hn Hnth Hterm. rewrite ltn_neqAle Hn andbT.
  apply/eqP => Heq. by rewrite (code_last_term Heq Hnth) in Hterm.
Qed.

Lemma pc_succ_corr (n : nat) (i : Merged.instr) (t : mem_tag) :
  n.+1 < size (code q) -> nth_error (code q) n = Some (i, t) -> is_term i = false ->
  (phia (word_of_nat (n + pc0)) + 1)%w = phia (word_of_nat (n.+1 + pc0)).
Proof.
  move=> Hn Hnth Hterm.
  have Hn0 : n < size (code q) by move: Hn; lia.
  have Hsh : shift_pos sizes (n.+1) = (shift_pos sizes n).+1 by apply: (fallthrough_aligned Hn Hnth Hterm).
  rewrite [X in (X + 1)%w = _] (phia_addr_code Hn0).
  rewrite [X in _ = X] (phia_addr_code Hn).
  rewrite [X in X = _] word_of_nat_succ.
  congr word_of_nat. rewrite Hsh. by lia.
Qed.

Variable NC : nat.

Lemma transfer_nop_evi (tpc : tag_type lrc_tags P) (ti : mem_tag)
      (tni : option mem_tag) (ei ei' : Symbolic.ev_inputs) :
  Merged.transfer (IVec (OP NOP) tpc ti [hseq] tni) ei
  = Merged.transfer (IVec (OP NOP) tpc ti [hseq] tni) ei'.
Proof. by []. Qed.

Lemma instr_nop_indep (i0 : @Merged.instr mt) (lp1 lp2 : nat -> nat -> nat) (p1 p2 : nat) :
  instr_merged_to_mp i0 lp1 p1 = Nop mt -> instr_merged_to_mp i0 lp2 p2 = Nop mt.
Proof. by case: i0 => //=; move=> *; match goal with H : _ = _ |- _ => discriminate H end. Qed.

Lemma instr_const_indep (i0 : @Merged.instr mt) (lp1 lp2 : nat -> nat -> nat) (p1 p2 : nat)
      (a : imm mt) (b : reg mt) :
  instr_merged_to_mp i0 lp1 p1 = Const a b -> instr_merged_to_mp i0 lp2 p2 = Const a b.
Proof. by case: i0 => //=; move=> *; match goal with H : _ = _ |- _ => discriminate H end. Qed.

Lemma instr_mov_indep (i0 : @Merged.instr mt) (lp1 lp2 : nat -> nat -> nat) (p1 p2 : nat)
      (a b : reg mt) :
  instr_merged_to_mp i0 lp1 p1 = Mov a b -> instr_merged_to_mp i0 lp2 p2 = Mov a b.
Proof. by case: i0 => //=; move=> *; match goal with H : _ = _ |- _ => discriminate H end. Qed.

Lemma instr_load_indep (i0 : @Merged.instr mt) (lp1 lp2 : nat -> nat -> nat) (p1 p2 : nat)
      (a b : reg mt) :
  instr_merged_to_mp i0 lp1 p1 = Load a b -> instr_merged_to_mp i0 lp2 p2 = Load a b.
Proof. by case: i0 => //=; move=> *; match goal with H : _ = _ |- _ => discriminate H end. Qed.

Lemma instr_store_indep (i0 : @Merged.instr mt) (lp1 lp2 : nat -> nat -> nat) (p1 p2 : nat)
      (a b : reg mt) :
  instr_merged_to_mp i0 lp1 p1 = Store a b -> instr_merged_to_mp i0 lp2 p2 = Store a b.
Proof. by case: i0 => //=; move=> *; match goal with H : _ = _ |- _ => discriminate H end. Qed.

Lemma instr_jump_indep (i0 : @Merged.instr mt) (lp1 lp2 : nat -> nat -> nat) (p1 p2 : nat)
      (a : reg mt) :
  instr_merged_to_mp i0 lp1 p1 = Jump a -> instr_merged_to_mp i0 lp2 p2 = Jump a.
Proof. by case: i0 => //=; move=> *; match goal with H : _ = _ |- _ => discriminate H end. Qed.

Lemma atom_etaE (V T : Type) (a : atom V T) : (vala a) @ (taga a) = a.
Proof. by case: a. Qed.

Lemma taga_at (V T : Type) (v : V) (t : T) : taga (v @ t) = t.
Proof. by []. Qed.
Lemma vala_at (V T : Type) (v : V) (t : T) : vala (v @ t) = v.
Proof. by []. Qed.

Lemma setm_id (T : ordType) (S : Type) (m : {fmap T -> S}) k v :
  m k = Some v -> setm m k v = m.
Proof. move=> H; apply/eq_fmap => k'; rewrite setmE; by case: eqP => [->|_]; rewrite ?H. Qed.

Lemma nsdu_binop (s : @Symbolic.state mt lrc_tags unit) (r1 r2 r3 : reg mt)
   (w1 w2 : mword mt) (t1 t2 : value_tag) (v : mword mt) (a3 : ratom) :
  Symbolic.regs s r1 = Some (w1 @ t1) -> Symbolic.regs s r2 = Some (w2 @ t2) ->
  Symbolic.regs s r3 = Some a3 ->
  @Symbolic.next_state_do_updates mt lrc_tags unit s
     [:: Symbolic.R; Symbolic.R; Symbolic.R] [hseq t1; t2; Other]
     [:: RegRead r1; RegRead r2; RegWrite r3 v]
   = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem s)
            (setm (Symbolic.regs s) r3 (v @ Other)) (Symbolic.pc s) (Symbolic.internal s)).
Proof.
  move=> Hr1 Hr2 Hr3.
  rewrite /= /Symbolic.next_state_do_update /= Hr1 /= /updm Hr1 /= (setm_id Hr1) /=.
  rewrite !Hr2 /= (setm_id Hr2) /=.
  by rewrite Hr3 /=.
Qed.

Lemma nsdu_mov (s : @Symbolic.state mt lrc_tags unit) (r1 r2 : reg mt)
   (v : mword mt) (ts' ts : value_tag) (a1 a2 : ratom) :
  Symbolic.regs s r1 = Some a1 -> Symbolic.regs s r2 = Some a2 ->
  @Symbolic.next_state_do_updates mt lrc_tags unit s
     [:: Symbolic.R; Symbolic.R] [hseq ts'; ts] [:: RegRead r1; RegWrite r2 v]
   = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem s)
            (setm (setm (Symbolic.regs s) r1 ((vala a1) @ ts')) r2 (v @ ts))
            (Symbolic.pc s) (Symbolic.internal s)).
Proof.
  move=> Hr1 Hr2.
  rewrite /= /Symbolic.next_state_do_update /= Hr1 /= /updm Hr1 /=.
  rewrite /Symbolic.next_state_do_update /= /updm setmE.
  by case: (r2 == r1) => /=; rewrite ?Hr2.
Qed.

Lemma nsdu_load (s : @Symbolic.state mt lrc_tags unit) (r1 r2 : reg mt)
   (w1 w2 : mword mt) (t1 td' : value_tag) (ts' : mem_tag) (a2 : ratom) (am : matom) :
  Symbolic.regs s r1 = Some (w1 @ t1) -> Symbolic.mem s w1 = Some am ->
  Symbolic.regs s r2 = Some a2 ->
  @Symbolic.next_state_do_updates mt lrc_tags unit s
     [:: Symbolic.R; Symbolic.M; Symbolic.R] [hseq t1; ts'; td']
     [:: RegRead r1; MemRead w1; RegWrite r2 w2]
   = Some (@Symbolic.State mt lrc_tags unit
            (setm (Symbolic.mem s) w1 ((vala am) @ ts'))
            (setm (Symbolic.regs s) r2 (w2 @ td'))
            (Symbolic.pc s) (Symbolic.internal s)).
Proof.
  move=> Hr1 Hmem Hr2.
  rewrite /= /Symbolic.next_state_do_update /= Hr1 /= /updm Hr1 /= (setm_id Hr1) /=.
  rewrite !Hmem /=.
  by rewrite Hr2 /=.
Qed.

Lemma nsdu_store (s : @Symbolic.state mt lrc_tags unit) (r1 r2 : reg mt)
   (w1 v w2 : mword mt) (t1 t2 ts' : value_tag) (td' : mem_tag) (am : matom) :
  Symbolic.regs s r1 = Some (w1 @ t1) -> Symbolic.regs s r2 = Some (w2 @ t2) ->
  Symbolic.mem s w1 = Some am ->
  @Symbolic.next_state_do_updates mt lrc_tags unit s
     [:: Symbolic.R; Symbolic.R; Symbolic.M] [hseq t1; ts'; td']
     [:: RegRead r1; RegRead r2; MemWrite w1 v]
   = Some (@Symbolic.State mt lrc_tags unit
            (setm (Symbolic.mem s) w1 (v @ td'))
            (setm (Symbolic.regs s) r2 (w2 @ ts'))
            (Symbolic.pc s) (Symbolic.internal s)).
Proof.
  move=> Hr1 Hr2 Hmem.
  rewrite /= /Symbolic.next_state_do_update /= Hr1 /= /updm Hr1 /= (setm_id Hr1) /=.
  rewrite !Hr2 /=.
  by rewrite !Hmem /=.
Qed.

Lemma color_matchE (t : mem_tag) : match t with {| color := c |} => c end = color t.
Proof. by case: t. Qed.

Lemma belong_someE (c : Component.id) (t : mem_tag) : belong c (Some t) = (c == color t).
Proof. by case: t. Qed.

Lemma belong_matchE (c : Component.id) (t : mem_tag) :
  (match t with {| color := c' |} => c == c' end) = (c == color t).
Proof. by case: t. Qed.

Lemma gtc_someE (t : mem_tag) : (match t with {| color := c' |} => Some c' end) = Some (color t).
Proof. by case: t. Qed.

Lemma reg_read_update_id (s : @Symbolic.state mt lrc_tags unit) (k : reg mt)
   (a : atom (mword mt) (Symbolic.tag_type lrc_tags Symbolic.R)) :
  Symbolic.regs s k = Some a ->
  Symbolic.next_state_do_update s (taga a) (RegRead k) = Some s.
Proof.
  case: a => va ta Hk. rewrite /Symbolic.next_state_do_update /= Hk /= /updm Hk /= (setm_id Hk).
  clear Hk; by case: s.
Qed.

Lemma reg_read_retag (s : @Symbolic.state mt lrc_tags unit) (k : reg mt)
   (a : atom (mword mt) (Symbolic.tag_type lrc_tags Symbolic.R)) (t : Symbolic.tag_type lrc_tags Symbolic.R) :
  Symbolic.regs s k = Some a ->
  Symbolic.next_state_do_update s t (RegRead k)
  = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem s)
            (setm (Symbolic.regs s) k ((vala a) @ t)) (Symbolic.pc s) (Symbolic.internal s)).
Proof.
  case: a => va ta Hk. by rewrite /Symbolic.next_state_do_update /= Hk /= /updm Hk /=.
Qed.

Definition wregs (rg1 rg2 : {fmap reg mt -> ratom}) : Prop :=
  forall r, oapp (fun a : ratom => exists v2, rg2 r = Some (v2 @ (taga a))
                       /\ (taga a <> Invalidated -> v2 = rel_v (taga a) (vala a)))
                 (rg2 r = None) (rg1 r).

Lemma wregs_setm_inval {rg1 rg2 : {fmap reg mt -> ratom}} {k : reg mt} {v1 v2 : mword mt} :
  wregs rg1 rg2 -> wregs (setm rg1 k (v1 @ Invalidated)) (setm rg2 k (v2 @ Invalidated)).
Proof.
  move=> H r0; rewrite !setmE; case: (r0 =P k) => [_|_]; last exact: (H r0).
  exists v2; rewrite taga_at; split; first by []. by move=> Hni; case: (Hni erefl).
Qed.

Lemma wregs_setm_other {rg1 rg2 : {fmap reg mt -> ratom}} {k : reg mt} {v : mword mt} :
  wregs rg1 rg2 -> wregs (setm rg1 k (v @ Other)) (setm rg2 k (v @ Other)).
Proof.
  move=> H r0; rewrite !setmE; case: (r0 =P k) => [_|_]; last exact: (H r0).
  exists v; rewrite taga_at vala_at; split; first by []. by move=> _.
Qed.

Lemma wregs_setm_ret {rg1 rg2 : {fmap reg mt -> ratom}} {k : reg mt} {v1 v2 : mword mt} {n : nat} :
  wregs rg1 rg2 -> v2 = phia v1 ->
  wregs (setm rg1 k (v1 @ (Ret n))) (setm rg2 k (v2 @ (Ret n))).
Proof.
  move=> H Hv r0; rewrite !setmE; case: (r0 =P k) => [_|_]; last exact: (H r0).
  exists v2; rewrite taga_at; split; first by [].
  move=> _; by rewrite vala_at Hv /rel_v /=.
Qed.

Lemma wregs_setm_ij {rg1 rg2 : {fmap reg mt -> ratom}} {k : reg mt} {v1 v2 : mword mt} :
  wregs rg1 rg2 -> v2 = phia v1 ->
  wregs (setm rg1 k (v1 @ InternalJump)) (setm rg2 k (v2 @ InternalJump)).
Proof.
  move=> H Hv r0; rewrite !setmE; case: (r0 =P k) => [_|_]; last exact: (H r0).
  exists v2; rewrite taga_at; split; first by [].
  move=> _; by rewrite vala_at Hv /rel_v /=.
Qed.

Lemma ndsu_cons (s : @Symbolic.state mt lrc_tags unit) (tk : Symbolic.tag_kind)
   (tks : seq Symbolic.tag_kind) (t : Symbolic.tag_type lrc_tags tk)
   (tags : hseq (Symbolic.tag_type lrc_tags) tks) (u : update) (us : seq update) :
   @Symbolic.next_state_do_updates mt lrc_tags unit s (tk :: tks)
      (HSeqCons t tags : hseq (Symbolic.tag_type lrc_tags) (tk :: tks)) (u :: us)
   = obind (fun s' => @Symbolic.next_state_do_updates mt lrc_tags unit s' tks tags us)
           (Symbolic.next_state_do_update s t u).
Proof. by []. Qed.

Lemma reg_clear_list_aux_cons (e : nat) (l' : seq nat)
   (rs : {fmap reg mt -> atom (mword mt) (Symbolic.tag_type lrc_tags Symbolic.R)})
   (top : Symbolic.tag_type lrc_tags Symbolic.R) :
   Symbolic.reg_clear_list_aux (e :: l') rs top
   = obind (fun v => obind (fun l'' => Some (HSeqCons top l''))
                           (Symbolic.reg_clear_list_aux l' rs (taga v)))
           (rs (as_word (ssrint.Posz e))).
Proof. rewrite [LHS]/=. by case: (rs (as_word (ssrint.Posz e))). Qed.

Lemma reg_clear_do_updates_id :
  forall (l : seq nat) (s : @Symbolic.state mt lrc_tags unit) (k0 : reg mt)
         (a0 : atom (mword mt) (Symbolic.tag_type lrc_tags Symbolic.R))
         (tags : hseq (Symbolic.tag_type lrc_tags) (nseq (S (size l)) Symbolic.R)),
    Symbolic.regs s k0 = Some a0 ->
    Symbolic.reg_clear_list_aux l (Symbolic.regs s) (taga a0) = Some tags ->
    @Symbolic.next_state_do_updates mt lrc_tags unit s (nseq (S (size l)) Symbolic.R) tags
      (RegRead k0 :: map (fun n => RegRead (as_word (ssrint.Posz n))) l) = Some s.
Proof.
  elim => [|e l' IH] s k0 a0 tags Hk0.
  - rewrite [Symbolic.reg_clear_list_aux _ _ _]/= => -[= <-].
    rewrite ndsu_cons (reg_read_update_id Hk0). by rewrite [obind _ (Some s)]/=.
  - rewrite reg_clear_list_aux_cons.
    case Hve : (Symbolic.regs s (as_word (ssrint.Posz e))) => [ve|]; last by [].
    rewrite [obind _ (Some ve)]/=.
    case Hl'' : (Symbolic.reg_clear_list_aux l' (Symbolic.regs s) (taga ve)) => [l''|]; last by [].
    rewrite [obind _ (Some l'')]/= => -[= <-].
    rewrite ndsu_cons (reg_read_update_id Hk0) [obind _ (Some s)]/=.
    exact: (IH s (as_word (ssrint.Posz e)) ve l'' Hve Hl'').
Qed.

Lemma reg_clear_list_aux_dom :
  forall (l : seq nat) (rs : {fmap reg mt -> atom (mword mt) (Symbolic.tag_type lrc_tags Symbolic.R)})
         (t : Symbolic.tag_type lrc_tags Symbolic.R)
         (l0 : hseq (Symbolic.tag_type lrc_tags) (nseq (S (size l)) Symbolic.R)),
    Symbolic.reg_clear_list_aux l rs t = Some l0 ->
    forall e, e \in l -> exists a, rs (as_word (ssrint.Posz e)) = Some a.
Proof.
  elim => [|e l' IH] rs t l0.
  - by move=> _ e; rewrite in_nil.
  - rewrite reg_clear_list_aux_cons.
    case Hre : (rs (as_word (ssrint.Posz e))) => [a|]; last by [].
    rewrite [obind _ (Some a)]/=.
    case Hrec : (Symbolic.reg_clear_list_aux l' rs (taga a)) => [l1|]; last by [].
    rewrite [obind _ (Some l1)]/= => _ e0.
    rewrite in_cons => /orP[/eqP ->|He0]; first by exists a.
    exact: (IH rs (taga a) l1 Hrec e0).
Qed.

Lemma reg_clear_list_aux_total :
  forall (l : seq nat) (rs : {fmap reg mt -> atom (mword mt) (Symbolic.tag_type lrc_tags Symbolic.R)})
         (t : Symbolic.tag_type lrc_tags Symbolic.R),
    (forall e, e \in l -> exists a, rs (as_word (ssrint.Posz e)) = Some a) ->
    exists ll, Symbolic.reg_clear_list_aux l rs t = Some ll.
Proof.
  elim => [|e l' IH] rs t Hmem.
  - by exists (HSeqCons t HSeqNil).
  - rewrite reg_clear_list_aux_cons.
    have [a Ha] : exists a, rs (as_word (ssrint.Posz e)) = Some a
      by (apply: Hmem; rewrite in_cons eqxx).
    rewrite Ha [obind _ (Some a)]/=.
    have Hmem' : forall e', e' \in l' -> exists a0, rs (as_word (ssrint.Posz e')) = Some a0
      by (move=> e' He'; apply: Hmem; rewrite in_cons He' orbT).
    have [ll Hll] := IH rs (taga a) Hmem'.
    rewrite Hll [obind _ (Some ll)]/=. by exists (HSeqCons t ll).
Qed.

Lemma reg_clear_list_aux_eq :
  forall (l : seq nat) (rs1 rs2 : {fmap reg mt -> atom (mword mt) (Symbolic.tag_type lrc_tags Symbolic.R)})
         (t : Symbolic.tag_type lrc_tags Symbolic.R),
    (forall e, e \in l -> rs1 (as_word (ssrint.Posz e)) = rs2 (as_word (ssrint.Posz e))) ->
    Symbolic.reg_clear_list_aux l rs1 t = Symbolic.reg_clear_list_aux l rs2 t.
Proof.
  elim => [|e l' IH] rs1 rs2 t Heq; first by [].
  rewrite !reg_clear_list_aux_cons.
  rewrite (Heq e); last by rewrite in_cons eqxx.
  case: (rs2 (as_word (ssrint.Posz e))) => [a|] //=.
  rewrite (IH rs1 rs2 (taga a)) //.
  move=> e' He'; apply: Heq; by rewrite in_cons He' orbT.
Qed.

Lemma jump_do_updates_result :
  forall (s : @Symbolic.state mt lrc_tags unit) (r : reg mt) (rav w : mword mt) rat t1 l,
    Symbolic.regs s ra = Some (rav @ rat) ->
    Symbolic.regs s r = Some (w @ t1) ->
    Symbolic.reg_clear_list (Symbolic.regs s) t1 = Some l ->
    @Symbolic.next_state_do_updates mt lrc_tags unit s
      [:: Symbolic.R & nseq (size Symbolic.reg_list).+1 Symbolic.R]
      (HSeqCons rat l
        : hseq (Symbolic.tag_type lrc_tags) [:: Symbolic.R & nseq (size Symbolic.reg_list).+1 Symbolic.R])
      (RegRead ra :: RegRead r :: Symbolic.reg_clear_read) = Some s.
Proof.
  move=> s r rav w rat t1 l Hra Hr Hcl.
  have HraU : Symbolic.next_state_do_update s (rat : Symbolic.tag_type lrc_tags Symbolic.R) (RegRead ra) = Some s
    by exact: (reg_read_update_id Hra).
  rewrite ndsu_cons HraU [obind _ (Some s)]/=.
  exact: (reg_clear_do_updates_id Hr Hcl).
Qed.

Local Opaque Symbolic.reg_clear_list_aux.

Lemma reg_clear_list_head :
  forall (rs : {fmap reg mt -> atom (mword mt) (Symbolic.tag_type lrc_tags Symbolic.R)})
         (t : Symbolic.tag_type lrc_tags Symbolic.R) l,
    Symbolic.reg_clear_list rs t = Some l -> hshead l = t.
Proof.
  move=> rs t l. rewrite /Symbolic.reg_clear_list /Symbolic.reg_list reg_clear_list_aux_cons.
  case Ev1: (rs (as_word (ssrint.Posz 1))) => [v1|]; last by rewrite [obind _ None]/=.
  rewrite [obind _ (Some v1)]/=.
  case Ell: (Symbolic.reg_clear_list_aux [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19] rs (taga v1)) => [ll|];
    last by rewrite [obind _ None]/=.
  rewrite [obind _ (Some ll)]/=. by move=> [= <-].
Qed.

Lemma reg_clear_list_2nd :
  forall (rs : {fmap reg mt -> atom (mword mt) (Symbolic.tag_type lrc_tags Symbolic.R)})
         (t : Symbolic.tag_type lrc_tags Symbolic.R) l a,
    Symbolic.reg_clear_list rs t = Some l -> rs (as_word (ssrint.Posz 1)) = Some a ->
    hshead (hsbehead l) = taga a.
Proof.
  move=> rs t l a Hcl Ha. move: Hcl.
  rewrite /Symbolic.reg_clear_list /Symbolic.reg_list reg_clear_list_aux_cons Ha [obind _ (Some a)]/=.
  rewrite reg_clear_list_aux_cons.
  case Ev0: (rs (as_word (ssrint.Posz 0))) => [v0|]; last by rewrite [obind _ None]/=.
  rewrite [obind _ (Some v0)]/=.
  case: (Symbolic.reg_clear_list_aux [:: 2; 3; 5; 6; 7; 16; 17; 18; 19] rs (taga v0)) => [ll|];
    last by rewrite [obind _ None]/=.
  rewrite [obind _ (Some ll)]/=. by move=> [= <-].
Qed.

Lemma nsuap_inval_list :
  forall (ks : seq nat) (s1 s2 : @Symbolic.state mt lrc_tags unit),
    wregs (Symbolic.regs s1) (Symbolic.regs s2) ->
    (forall k, k \in ks -> exists a, Symbolic.regs s1 (as_word (ssrint.Posz k)) = Some a) ->
    exists sd1 sd2,
      @Symbolic.next_state_do_updates mt lrc_tags unit s1 (nseq (size ks) Symbolic.R)
         (make_hseq (size ks) Invalidated) (map (fun n => RegRead (as_word (ssrint.Posz n))) ks) = Some sd1 /\
      @Symbolic.next_state_do_updates mt lrc_tags unit s2 (nseq (size ks) Symbolic.R)
         (make_hseq (size ks) Invalidated) (map (fun n => RegRead (as_word (ssrint.Posz n))) ks) = Some sd2 /\
      wregs (Symbolic.regs sd1) (Symbolic.regs sd2) /\
      Symbolic.mem sd1 = Symbolic.mem s1 /\ Symbolic.mem sd2 = Symbolic.mem s2 /\
      Symbolic.pc sd1 = Symbolic.pc s1 /\ Symbolic.pc sd2 = Symbolic.pc s2 /\
      Symbolic.internal sd1 = Symbolic.internal s1 /\ Symbolic.internal sd2 = Symbolic.internal s2.
Proof.
  elim => [|k ks' IH] s1 s2 Hw Hdom.
  - by exists s1, s2.
  - have [a1 Ha1] : exists a, Symbolic.regs s1 (as_word (ssrint.Posz k)) = Some a
      by apply: Hdom; rewrite in_cons eqxx.
    have [a2 Ha2] : exists a, Symbolic.regs s2 (as_word (ssrint.Posz k)) = Some a.
    { move: (Hw (as_word (ssrint.Posz k))); rewrite Ha1 /= => [[v2 [Hr2 _]]]. by exists (v2 @ (taga a1)). }
    pose s1a := @Symbolic.State mt lrc_tags unit (Symbolic.mem s1)
                  (setm (Symbolic.regs s1) (as_word (ssrint.Posz k)) ((vala a1) @ Invalidated))
                  (Symbolic.pc s1) (Symbolic.internal s1).
    pose s2a := @Symbolic.State mt lrc_tags unit (Symbolic.mem s2)
                  (setm (Symbolic.regs s2) (as_word (ssrint.Posz k)) ((vala a2) @ Invalidated))
                  (Symbolic.pc s2) (Symbolic.internal s2).
    have Hw' : wregs (Symbolic.regs s1a) (Symbolic.regs s2a) by exact: (wregs_setm_inval Hw).
    have Hdom' : forall k0, k0 \in ks' -> exists a, Symbolic.regs s1a (as_word (ssrint.Posz k0)) = Some a.
    { move=> k0 Hk0. rewrite /s1a /= setmE; case: (_ =P _) => [_|_];
        [ by exists ((vala a1) @ Invalidated) | by apply: Hdom; rewrite in_cons Hk0 orbT ]. }
    have [sd1 [sd2 [Hd1 [Hd2 [Hwd [Hm1 [Hm2 [Hp1 [Hp2 [Hi1 Hi2]]]]]]]]]] := IH s1a s2a Hw' Hdom'.
    exists sd1, sd2.
    split; first by rewrite ndsu_cons (reg_read_retag _ Ha1) [obind _ (Some _)]/=; exact: Hd1.
    split; first by rewrite ndsu_cons (reg_read_retag _ Ha2) [obind _ (Some _)]/=; exact: Hd2.
    by rewrite Hm1 Hm2 Hp1 Hp2 Hi1 Hi2.
Qed.

Lemma jump_internal_nsuap (s : @Symbolic.state mt lrc_tags unit) (tcell : mem_tag) (r : reg mt)
   (wtgt rav : mword mt) (rat : value_tag)
   (l : hseq (Symbolic.tag_type lrc_tags) (nseq (size Symbolic.reg_list).+1 Symbolic.R))
   (evinp : Symbolic.ev_inputs) :
   is_code tcell ->
   Symbolic.regs s r = Some (wtgt @ InternalJump) ->
   Symbolic.regs s ra = Some (rav @ rat) ->
   Symbolic.reg_clear_list (Symbolic.regs s) InternalJump = Some l ->
   belong (color tcell)
     (match Symbolic.mem s wtgt with Some ni => Some (taga ni) | None => None end) ->
   (color tcell == match taga (Symbolic.pc s) with Level _ c => c end) ->
   Symbolic.evi s = Some evinp ->
   @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
      s (IVec (OP JUMP) (taga (Symbolic.pc s)) tcell (HSeqCons rat l))
      [:: RegRead ra, RegRead r & reg_clear_read] wtgt
   = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem s) (Symbolic.regs s)
             (wtgt @ (taga (Symbolic.pc s))) (Symbolic.internal s), None).
Proof.
  move=> Hic Hr Hra Hcl Hbel Hcur Hevi.
  have Ha : hshead l = InternalJump := reg_clear_list_head Hcl.
  move: Hcl Hbel Ha; case: l => a l'; case: l' => b c => Hcl Hbel Ha.
  have Ea : a = InternalJump := Ha. rewrite {a Ha}Ea in Hcl *.
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state Hevi [obind _ (Some evinp)]/=.
  have Htr : forall tni, belong (color tcell) tni ->
      Merged.transfer (IVec (OP JUMP) (taga (Symbolic.pc s)) tcell
        (HSeqCons rat (HSeqCons InternalJump (HSeqCons b c))) tni) evinp
      = Some (Symbolic.OVec JUMP (taga (Symbolic.pc s))
                (HSeqCons rat (HSeqCons InternalJump (HSeqCons b c))), None).
  { move=> tni Hb. rewrite /Merged.transfer /Merged.instr_rules Hic /LRC.instr_rules /=.
    move: Hcur; case: (taga (Symbolic.pc s)) => ltpc ctpc /=.
    rewrite color_matchE => Hcur. by rewrite Hcur /= Hb /=. }
  move: Hbel; case Hmw: (Symbolic.mem s wtgt) => [celltgt|] Hbel;
    rewrite (Htr _ Hbel); cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read addw];
    rewrite (jump_do_updates_result Hra Hr Hcl); by [].
Qed.

Lemma jump_return_nsuap (s sd : @Symbolic.state mt lrc_tags unit) (tcell : mem_tag) (r : reg mt)
   (wtgt rav rcv : mword mt) (level : nat) (ctpc : Component.id) (rat : value_tag)
   (l : hseq (Symbolic.tag_type lrc_tags) (nseq (size Symbolic.reg_list).+1 Symbolic.R))
   (celltgt : atom (mword mt) (tag_type lrc_tags Symbolic.M)) (evinp : Symbolic.ev_inputs) :
   is_code tcell ->
   taga (Symbolic.pc s) = Level level ctpc ->
   color tcell == ctpc ->
   Symbolic.mem s wtgt = Some celltgt ->
   color tcell != color (taga celltgt) ->
   Symbolic.regs s r = Some (wtgt @ (Ret level.-1)) ->
   Symbolic.regs s rcom = Some (rcv @ Other) ->
   0 < level ->
   Symbolic.reg_clear_list (Symbolic.regs s) (Ret level.-1) = Some l ->
   Symbolic.evi s = Some evinp ->
   @Symbolic.next_state_do_updates mt lrc_tags unit s (nseq 13 Symbolic.R)
      (Invalidated :: Invalidated :: Other :: reg_invalidate_hseq)%hseq
      (RegRead ra :: RegRead r :: reg_clear_read) = Some sd ->
   @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
      s (IVec (OP JUMP) (taga (Symbolic.pc s)) tcell (HSeqCons rat l))
      [:: RegRead ra, RegRead r & reg_clear_read] wtgt
   = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem sd) (Symbolic.regs sd)
             (wtgt @ (build_tpc level.-1 (color (taga celltgt)))) (Symbolic.internal sd),
           Some (ERet (color tcell) (rcom_value evinp) (color (taga celltgt)))).
Proof.
  move=> Hic Hpct Hcur Hmw Hbel HRr HRrcom Hlv Hcl Hevi Hsd.
  have Ha : hshead l = Ret level.-1 := reg_clear_list_head Hcl.
  have Hb : hshead (hsbehead l) = Other.
  { rewrite (reg_clear_list_2nd Hcl HRrcom). by rewrite taga_at. }
  move: Hcl Ha Hb; case: l => a l'; case: l' => b c => Hcl Ha Hb.
  have Ea : a = Ret level.-1 := Ha. have Eb : b = Other := Hb.
  rewrite Ea Eb.
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state Hevi [obind _ (Some evinp)]/= Hmw.
  have Htr : Merged.transfer (IVec (OP JUMP) (taga (Symbolic.pc s)) tcell
               (HSeqCons rat (HSeqCons (Ret level.-1) (HSeqCons Other c))) (Some (taga celltgt))) evinp
           = Some (Symbolic.OVec JUMP (build_tpc level.-1 (color (taga celltgt)))
                     (Invalidated :: Invalidated :: Other :: reg_invalidate_hseq)%hseq,
                   Some (ERet (color tcell) (rcom_value evinp) (color (taga celltgt)))).
  { rewrite /Merged.transfer /Merged.instr_rules Hic /LRC.instr_rules /= Hpct /=.
    rewrite !color_matchE Hcur /=.
    rewrite belong_matchE (negbTE Hbel) /= gtc_someE /=.
    have Hlvl := prednK Hlv. by rewrite Hlvl eqxx. }
  rewrite Htr; cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read addw].
  by rewrite Hsd.
Qed.

Lemma mem_read_update_id (s : @Symbolic.state mt lrc_tags unit) (w1 v : mword mt)
   (t : Symbolic.tag_type lrc_tags Symbolic.M) :
  Symbolic.mem s w1 = Some (v @ t) ->
  Symbolic.next_state_do_update s t (MemRead w1) = Some s.
Proof.
  move=> Hw. rewrite /Symbolic.next_state_do_update /= Hw /= /updm Hw /= (setm_id Hw).
  clear Hw; by case: s.
Qed.

Lemma reg_clear_ra_neq (e : nat) :
  e \in [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N ->
  (@as_word (reg_field_size mt) (ssrint.Posz e) == as_word (ssrint.Posz 4)) = false.
Proof.
  rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|
     /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]]]]]]].
Qed.

Lemma jal_reg_clear_id (s : @Symbolic.state mt lrc_tags unit)
   (a1 : atom (mword mt) (Symbolic.tag_type lrc_tags Symbolic.R))
   (lh : hseq (Symbolic.tag_type lrc_tags) (nseq (size Symbolic.reg_list) Symbolic.R)) :
   Symbolic.regs s rcom = Some a1 ->
   Symbolic.reg_clear_list_aux [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N (Symbolic.regs s) (taga a1) = Some lh ->
   @Symbolic.next_state_do_updates mt lrc_tags unit s (nseq (size Symbolic.reg_list) Symbolic.R)
     lh Symbolic.reg_clear_read = Some s.
Proof.
  move=> Hrc Hc.
  have Hrcr : Symbolic.reg_clear_read
            = RegRead (as_word (ssrint.Posz 1)) :: map (fun n => RegRead (as_word (ssrint.Posz n)))
                                                       [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N
    by rewrite /Symbolic.reg_clear_read /Symbolic.reg_list.
  rewrite Hrcr.
  exact: (reg_clear_do_updates_id Hrc Hc).
Qed.

Lemma jal_internal_nsuap (s : @Symbolic.state mt lrc_tags unit) (tcell : mem_tag)
   (vret old tgt : mword mt) (tret : mem_tag) (told : value_tag)
   (a1 : atom (mword mt) (Symbolic.tag_type lrc_tags Symbolic.R))
   (lh : hseq (Symbolic.tag_type lrc_tags) (nseq (size Symbolic.reg_list) Symbolic.R))
   (evinp : Symbolic.ev_inputs) :
   is_code tcell ->
   Symbolic.mem s (vala (Symbolic.pc s) + 1)%w = Some (vret @ tret) ->
   Symbolic.regs s ra = Some (old @ told) ->
   Symbolic.regs s rcom = Some a1 ->
   Symbolic.reg_clear_list_aux [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N (Symbolic.regs s) (taga a1) = Some lh ->
   belong (color tcell)
     (match Symbolic.mem s tgt with Some ni => Some (taga ni) | None => None end) ->
   (color tcell == match taga (Symbolic.pc s) with Level _ c0 => c0 end) ->
   color tcell == color tret ->
   Symbolic.evi s = Some evinp ->
   @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
      s (IVec (OP JAL) (taga (Symbolic.pc s)) tcell (HSeqCons tret (HSeqCons told lh)))
      [:: MemRead (vala (Symbolic.pc s) + 1)%w, RegWrite ra (vala (Symbolic.pc s) + 1)%w & reg_clear_read] tgt
   = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem s)
             (setm (Symbolic.regs s) ra ((vala (Symbolic.pc s) + 1)%w @ InternalJump))
             (tgt @ (taga (Symbolic.pc s))) (Symbolic.internal s), None).
Proof.
  move=> Hic Hret Hra Hrc Hc Hbel Hcur Hcret Hevi.
  move: Hc; case: lh => trcom next Hc.
  set sw := @Symbolic.State mt lrc_tags unit (Symbolic.mem s)
              (setm (Symbolic.regs s) ra ((vala (Symbolic.pc s) + 1)%w @ InternalJump))
              (Symbolic.pc s) (Symbolic.internal s).
  have Hswrc : Symbolic.regs sw rcom = Some a1.
  { rewrite /sw /= setmE. by case: (rcom =P ra) => [E|_]; [ by [] | exact: Hrc ]. }
  have Hswc : Symbolic.reg_clear_list_aux [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N (Symbolic.regs sw) (taga a1) = Some (HSeqCons trcom next).
  { rewrite -Hc; apply: reg_clear_list_aux_eq => e He.
    by rewrite /sw /= setmE (reg_clear_ra_neq He). }
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state Hevi [obind _ (Some evinp)]/=.
  have Htr : forall tni, belong (color tcell) tni -> color tcell == color tret ->
      Merged.transfer (IVec (OP JAL) (taga (Symbolic.pc s)) tcell
        (HSeqCons tret (HSeqCons told (HSeqCons trcom next))) tni) evinp
      = Some (Symbolic.OVec JAL (taga (Symbolic.pc s))
                (HSeqCons tret (HSeqCons InternalJump (HSeqCons trcom next))), None).
  { move=> tni Hb Hcr.
    rewrite /Merged.transfer /Merged.instr_rules Hic /LRC.instr_rules /=.
    move: Hcur; case: (taga (Symbolic.pc s)) => ltpc ctpc /=.
    rewrite color_matchE => Hcur'.
    by rewrite /check_belong !belong_someE Hcur' Hcr Hb /=. }
  have HrwU : Symbolic.next_state_do_update s (InternalJump : Symbolic.tag_type lrc_tags Symbolic.R)
                (RegWrite ra (vala (Symbolic.pc s) + 1)%w) = Some sw
    by rewrite /Symbolic.next_state_do_update /= /updm Hra /=.
  move: Hbel; case Hmw: (Symbolic.mem s tgt) => [celltgt|] Hbel;
    rewrite (Htr _ Hbel Hcret);
    cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read addw];
    rewrite ndsu_cons (mem_read_update_id Hret);
    cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read addw];
    rewrite ndsu_cons HrwU;
    cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read addw];
    by rewrite (jal_reg_clear_id Hswrc Hswc).
Qed.


Lemma switch_val_snd (t : mem_tag) (v : value_tag) : (switch_val t v).2 = vtag t.
Proof. by case: t. Qed.
Lemma switch_val_iscode (t : mem_tag) (v : value_tag) : is_code (switch_val t v).1 = is_code t.
Proof. by case: t. Qed.
Lemma switch_val_color (t : mem_tag) (v : value_tag) : color (switch_val t v).1 = color t.
Proof. by case: t. Qed.
Lemma switch_val_vtag (t : mem_tag) (v : value_tag) : vtag (switch_val t v).1 = v.
Proof. by case: t. Qed.

Lemma merged_nop_inv
   (m : {fmap mword mt -> matom}) (r : {fmap reg mt -> ratom})
   (pcw : mword mt) (tpc : tag_type lrc_tags Symbolic.P) (ext : unit)
   (ti : mem_tag) (v1n : matom) (s' : st) (e : option event) :
  is_code ti -> m (pcw + 1)%w = Some v1n ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
     (@Symbolic.State mt lrc_tags unit m r (pcw @ tpc) ext) (IVec (OP NOP) tpc ti [hseq]) [::]
   = Some (s', e) ->
  s' = @Symbolic.State mt lrc_tags unit m r ((pcw + 1)%w @ tpc) ext /\ e = None /\
  (color ti == match tpc with Level _ c => c end) /\
  (color ti == color (taga v1n)) /\
  (exists ei, Symbolic.evi (@Symbolic.State mt lrc_tags unit m r (pcw @ tpc) ext) = Some ei).
Proof.
  move=> Hic Hsucc.
  case: tpc => ltpc ctpc.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  rewrite Hsucc /=.
  case Hevi: (Symbolic.evi _) => [evinp|]; last by move=> [=].
  rewrite /Merged.transfer /= /Merged.instr_rules Hic /= /LRC.instr_rules /=.
  rewrite !color_matchE.
  case Hcur: (color ti == ctpc); last by move=> [=].
  rewrite /check_belong belong_someE.
  case Hbel: (color ti == color (taga v1n)); last by move=> [=].
  move=> [= <- <-].
  split; first by []. split; first by []. split; first by [].
  split; first by [].
  by exists evinp.
Qed.

Lemma merged_nop_intro (s : st) (tcell : mem_tag) (v2n : matom) (evinp : Symbolic.ev_inputs) :
  is_code tcell ->
  Symbolic.mem s (vala (Symbolic.pc s) + 1)%w = Some v2n ->
  (color tcell == match taga (Symbolic.pc s) with Level _ c => c end) ->
  (color tcell == color (taga v2n)) ->
  Symbolic.evi s = Some evinp ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
     s (IVec (OP NOP) (taga (Symbolic.pc s)) tcell [hseq]) [::]
   = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem s) (Symbolic.regs s)
             ((vala (Symbolic.pc s) + 1)%w @ (taga (Symbolic.pc s))) (Symbolic.internal s), None).
Proof.
  move=> Hic Hsucc Hcur Hbel.
  move: Hcur; case: (taga (Symbolic.pc s)) => ltpc ctpc /= Hcur Hevi.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  rewrite Hsucc /= Hevi /=.
  rewrite /Merged.transfer /= /Merged.instr_rules Hic /= /LRC.instr_rules /=.
  rewrite !color_matchE.
  have Hb2 : belong (color tcell) (Some (taga v2n)) = true by rewrite belong_someE.
  rewrite Hcur /= /check_belong Hb2 /=.
  by [].
Qed.

Lemma merged_const_inv
   (m : {fmap mword mt -> matom}) (r : {fmap reg mt -> ratom})
   (pcw : mword mt) (tpc : tag_type lrc_tags Symbolic.P) (ext : unit)
   (ti : mem_tag) (v1n : matom) (nn : imm mt) (rg : reg mt)
   (vold : mword mt) (told : value_tag) (s' : st) (e : option event) :
  is_code ti -> m (pcw + 1)%w = Some v1n -> r rg = Some (vold @ told) ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
     (@Symbolic.State mt lrc_tags unit m r (pcw @ tpc) ext)
     (IVec (OP CONST) tpc ti [hseq told]) [:: RegWrite rg (swcast nn)]
   = Some (s', e) ->
  s' = @Symbolic.State mt lrc_tags unit m (setm r rg ((swcast nn) @ Other)) ((pcw + 1)%w @ tpc) ext
  /\ e = None /\ (color ti == match tpc with Level _ c => c end)
  /\ (color ti == color (taga v1n))
  /\ (exists ei, Symbolic.evi (@Symbolic.State mt lrc_tags unit m r (pcw @ tpc) ext) = Some ei).
Proof.
  move=> Hic Hsucc Hrg.
  case: tpc => ltpc ctpc.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  rewrite Hsucc /=.
  case Hevi: (Symbolic.evi _) => [evinp|]; last by move=> [=].
  rewrite /Merged.transfer /= /Merged.instr_rules Hic /= /LRC.instr_rules /=.
  rewrite !color_matchE.
  case Hcur: (color ti == ctpc); last by move=> [=].
  rewrite /check_belong belong_someE.
  case Hbel: (color ti == color (taga v1n)); last by move=> [=].
  rewrite /= /updm Hrg /=.
  move=> [= <- <-].
  split; first by []. split; first by []. split; first by []. split; first by [].
  by exists evinp.
Qed.

Lemma merged_const_intro (s : st) (tcell : mem_tag) (v2n : matom)
   (nn : imm mt) (rg : reg mt) (vold : mword mt) (told : value_tag) (evinp : Symbolic.ev_inputs) :
  is_code tcell ->
  Symbolic.mem s (vala (Symbolic.pc s) + 1)%w = Some v2n ->
  Symbolic.regs s rg = Some (vold @ told) ->
  (color tcell == match taga (Symbolic.pc s) with Level _ c => c end) ->
  (color tcell == color (taga v2n)) ->
  Symbolic.evi s = Some evinp ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
     s (IVec (OP CONST) (taga (Symbolic.pc s)) tcell [hseq told]) [:: RegWrite rg (swcast nn)]
   = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem s)
             (setm (Symbolic.regs s) rg ((swcast nn) @ Other))
             ((vala (Symbolic.pc s) + 1)%w @ (taga (Symbolic.pc s))) (Symbolic.internal s), None).
Proof.
  move=> Hic Hsucc Hrg Hcur Hbel.
  move: Hcur; case: (taga (Symbolic.pc s)) => ltpc ctpc /= Hcur Hevi.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  rewrite Hsucc /= Hevi /=.
  rewrite /Merged.transfer /= /Merged.instr_rules Hic /= /LRC.instr_rules /=.
  rewrite !color_matchE.
  have Hb2 : belong (color tcell) (Some (taga v2n)) = true by rewrite belong_someE.
  rewrite Hcur /= /check_belong Hb2 /= /updm Hrg /=.
  by [].
Qed.

Lemma instr_binop_indep (i0 : @Merged.instr mt) (lp1 lp2 : nat -> nat -> nat) (p1 p2 : nat)
      (bop : binop) (a b c : reg mt) :
  instr_merged_to_mp i0 lp1 p1 = Binop bop a b c -> instr_merged_to_mp i0 lp2 p2 = Binop bop a b c.
Proof. by case: i0 => //=; move=> *; match goal with H : _ = _ |- _ => discriminate H end. Qed.

Lemma merged_binop_inv
   (m : {fmap mword mt -> matom}) (rr : {fmap reg mt -> ratom})
   (pcw : mword mt) (tpc : tag_type lrc_tags Symbolic.P) (ext : unit)
   (ti : mem_tag) (v1n : matom) (bop : binop) (r1 r2 r3 : reg mt)
   (w1 w2 : mword mt) (t1 t2 : value_tag) (a3 : ratom) (s' : st) (e : option event) :
  is_code ti -> m (pcw + 1)%w = Some v1n ->
  rr r1 = Some (w1 @ t1) -> rr r2 = Some (w2 @ t2) -> rr r3 = Some a3 ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
     (@Symbolic.State mt lrc_tags unit m rr (pcw @ tpc) ext)
     (IVec (OP (BINOP bop)) tpc ti [hseq t1; t2; taga a3])
     [:: RegRead r1; RegRead r2; RegWrite r3 (binop_denote bop w1 w2)]
   = Some (s', e) ->
  s' = @Symbolic.State mt lrc_tags unit m
         (setm rr r3 ((binop_denote bop w1 w2) @ Other)) ((pcw + 1)%w @ tpc) ext
  /\ e = None /\ t1 = Other /\ t2 = Other
  /\ (color ti == match tpc with Level _ c => c end) /\ (color ti == color (taga v1n))
  /\ (exists ei, Symbolic.evi (@Symbolic.State mt lrc_tags unit m rr (pcw @ tpc) ext) = Some ei).
Proof.
  move=> Hic Hsucc Hr1 Hr2 Hr3.
  case: tpc => ltpc ctpc.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  rewrite Hsucc /=.
  case Hevi: (Symbolic.evi _) => [evinp|]; last by move=> [=].
  rewrite /Merged.transfer /= /Merged.instr_rules Hic /= /LRC.instr_rules /=.
  rewrite !color_matchE.
  case Hcur: (color ti == ctpc); last by move=> [=].
  move: Hr1 Hr2; case: t1 => [nr1|||]; case: t2 => [nr2|||] Hr1 Hr2;
    rewrite /is_other /=; try by move=> [=].
  rewrite /check_belong belong_someE.
  case Hbel: (color ti == color (taga v1n)); last by move=> [=].
  rewrite /= /Symbolic.next_state_do_update /= Hr1 /= /updm Hr1 /= (setm_id Hr1) /=.
  rewrite !Hr2 /= (setm_id Hr2) /= Hr3 /=.
  move=> [= <- <-].
  split; first by []. split; first by []. split; first by []. split; first by [].
  split; first by []. split; first by [].
  by exists evinp.
Qed.

Lemma merged_binop_intro (s : st) (tcell : mem_tag) (v2n : matom) (bop : binop)
   (r1 r2 r3 : reg mt) (w1 w2 : mword mt) (a3 : ratom) (evinp : Symbolic.ev_inputs) :
  is_code tcell ->
  Symbolic.mem s (vala (Symbolic.pc s) + 1)%w = Some v2n ->
  Symbolic.regs s r1 = Some (w1 @ Other) -> Symbolic.regs s r2 = Some (w2 @ Other) ->
  Symbolic.regs s r3 = Some a3 ->
  (color tcell == match taga (Symbolic.pc s) with Level _ c => c end) ->
  (color tcell == color (taga v2n)) ->
  Symbolic.evi s = Some evinp ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
     s (IVec (OP (BINOP bop)) (taga (Symbolic.pc s)) tcell [hseq Other; Other; taga a3])
     [:: RegRead r1; RegRead r2; RegWrite r3 (binop_denote bop w1 w2)]
   = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem s)
            (setm (Symbolic.regs s) r3 ((binop_denote bop w1 w2) @ Other))
            ((vala (Symbolic.pc s) + 1)%w @ (taga (Symbolic.pc s))) (Symbolic.internal s), None).
Proof.
  move=> Hic Hsucc Hr1 Hr2 Hr3 Hcur Hbel.
  move: Hcur; case: (taga (Symbolic.pc s)) => ltpc ctpc /= Hcur Hevi.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  rewrite Hsucc /= Hevi /=.
  rewrite /Merged.transfer /= /Merged.instr_rules Hic /= /LRC.instr_rules /=.
  rewrite !color_matchE.
  have Hb2 : belong (color tcell) (Some (taga v2n)) = true by rewrite belong_someE.
  rewrite Hcur /= /is_other /= /check_belong Hb2 /=.
  rewrite /Symbolic.next_state_do_update /= Hr1 /= /updm Hr1 /= (setm_id Hr1) /=.
  rewrite !Hr2 /= (setm_id Hr2) /= Hr3 /=.
  by [].
Qed.

Lemma rel_v_invalidate (t : value_tag) (v : mword mt) :
  rel_v (if is_address t then Invalidated else Other) v = rel_v t v.
Proof. by rewrite /rel_v; case: (is_address t). Qed.

Lemma merged_mov_inv
   (m : {fmap mword mt -> matom}) (rr : {fmap reg mt -> ratom})
   (pcw : mword mt) (tpc : tag_type lrc_tags Symbolic.P) (ext : unit)
   (ti : mem_tag) (v1n : matom) (r1 r2 : reg mt) (w1 : mword mt) (t1 : value_tag)
   (a2 : ratom) (s' : st) (e : option event) :
  is_code ti -> m (pcw + 1)%w = Some v1n ->
  rr r1 = Some (w1 @ t1) -> rr r2 = Some a2 ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
     (@Symbolic.State mt lrc_tags unit m rr (pcw @ tpc) ext)
     (IVec (OP MOV) tpc ti [hseq t1; taga a2]) [:: RegRead r1; RegWrite r2 w1]
   = Some (s', e) ->
  s' = @Symbolic.State mt lrc_tags unit m
         (setm (setm rr r1 (w1 @ (if is_address t1 then Invalidated else Other))) r2 (w1 @ t1))
         ((pcw + 1)%w @ tpc) ext
  /\ e = None /\ (color ti == match tpc with Level _ c => c end) /\ (color ti == color (taga v1n))
  /\ (exists ei, Symbolic.evi (@Symbolic.State mt lrc_tags unit m rr (pcw @ tpc) ext) = Some ei).
Proof.
  move=> Hic Hsucc Hr1 Hr2.
  case: tpc => ltpc ctpc.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  rewrite Hsucc /=.
  case Hevi: (Symbolic.evi _) => [evinp|]; last by move=> [=].
  rewrite /Merged.transfer /= /Merged.instr_rules Hic /= /LRC.instr_rules /=.
  rewrite !color_matchE.
  case Hcur: (color ti == ctpc); last by move=> [=].
  rewrite /check_belong belong_someE.
  case Hbel: (color ti == color (taga v1n)); last by move=> [=].
  rewrite /= /Symbolic.next_state_do_update /= Hr1 /= /updm Hr1 /=.
  rewrite /Symbolic.next_state_do_update /= /updm setmE.
  case: (r2 == r1) => /=; rewrite ?Hr2 /=; move=> [= <- <-];
    (split; first by []); (split; first by []); (split; first by []); (split; first by []);
    by exists evinp.
Qed.

Lemma merged_mov_intro (s : st) (tcell : mem_tag) (v2n : matom)
   (r1 r2 : reg mt) (vw : mword mt) (t1 : value_tag) (a2 : ratom) (evinp : Symbolic.ev_inputs) :
  is_code tcell ->
  Symbolic.mem s (vala (Symbolic.pc s) + 1)%w = Some v2n ->
  Symbolic.regs s r1 = Some (vw @ t1) -> Symbolic.regs s r2 = Some a2 ->
  (color tcell == match taga (Symbolic.pc s) with Level _ c => c end) ->
  (color tcell == color (taga v2n)) ->
  Symbolic.evi s = Some evinp ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
     s (IVec (OP MOV) (taga (Symbolic.pc s)) tcell [hseq t1; taga a2])
     [:: RegRead r1; RegWrite r2 vw]
   = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem s)
            (setm (setm (Symbolic.regs s) r1 (vw @ (if is_address t1 then Invalidated else Other)))
                  r2 (vw @ t1))
            ((vala (Symbolic.pc s) + 1)%w @ (taga (Symbolic.pc s))) (Symbolic.internal s), None).
Proof.
  move=> Hic Hsucc Hr1 Hr2 Hcur Hbel.
  move: Hcur; case: (taga (Symbolic.pc s)) => ltpc ctpc /= Hcur Hevi.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  rewrite Hsucc /= Hevi /=.
  rewrite /Merged.transfer /= /Merged.instr_rules Hic /= /LRC.instr_rules /=.
  rewrite !color_matchE.
  have Hb2 : belong (color tcell) (Some (taga v2n)) = true by rewrite belong_someE.
  rewrite Hcur /= /check_belong Hb2 /=.
  rewrite /Symbolic.next_state_do_update /= Hr1 /= /updm Hr1 /=.
  rewrite /Symbolic.next_state_do_update /= /updm setmE.
  by case: (r2 == r1) => /=; rewrite ?Hr2.
Qed.

Lemma merged_load_inv
   (m : {fmap mword mt -> matom}) (rr : {fmap reg mt -> ratom})
   (pcw : mword mt) (tpc : tag_type lrc_tags Symbolic.P) (ext : unit)
   (ti : mem_tag) (v1n : matom) (r1 r2 : reg mt) (w1 w2 : mword mt)
   (t1 : value_tag) (t2 : mem_tag) (a2 : ratom) (s' : st) (e : option event) :
  is_code ti -> m (pcw + 1)%w = Some v1n ->
  rr r1 = Some (w1 @ t1) -> m w1 = Some (w2 @ t2) -> rr r2 = Some a2 ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
     (@Symbolic.State mt lrc_tags unit m rr (pcw @ tpc) ext)
     (IVec (OP LOAD) tpc ti [hseq t1; t2; taga a2]) [:: RegRead r1; MemRead w1; RegWrite r2 w2]
   = Some (s', e) ->
  s' = @Symbolic.State mt lrc_tags unit
         (setm m w1 (w2 @ (switch_val t2 (if is_address (vtag t2) then Invalidated else Other)).1))
         (setm rr r2 (w2 @ (vtag t2)))
         ((pcw + 1)%w @ tpc) ext
  /\ e = None /\ t1 = Other /\ is_code t2 = false /\ (color ti == color t2)
  /\ (color ti == match tpc with Level _ c => c end) /\ (color ti == color (taga v1n))
  /\ (exists ei, Symbolic.evi (@Symbolic.State mt lrc_tags unit m rr (pcw @ tpc) ext) = Some ei).
Proof.
  move=> Hic Hsucc Hr1 Hmem Hr2.
  case: tpc => ltpc ctpc.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  rewrite Hsucc /=.
  case Hevi: (Symbolic.evi _) => [evinp|]; last by move=> [=].
  rewrite /Merged.transfer /= /Merged.instr_rules Hic /=.
  case Hct2: (is_code t2); first by move=> [=].
  rewrite /LRC.instr_rules /=.
  rewrite !color_matchE.
  case Hcur: (color ti == ctpc); last by move=> [=].
  move: Hr1; case: t1 => [nr|||] Hr1; rewrite /is_other /=; try by move=> [=].
  rewrite /check_belong belong_someE.
  case Hbel: (color ti == color (taga v1n)); last by move=> [=].
  rewrite Hct2 orbF belong_matchE.
  case Hbelt2: (color ti == color t2); last by move=> [=].
  rewrite (surjective_pairing (switch_val t2 (if is_address (vtag t2) then Invalidated else Other))) /=.
  rewrite /= /Symbolic.next_state_do_update /= Hr1 /= /updm Hr1 /= (setm_id Hr1) /=.
  rewrite !Hmem /=.
  rewrite Hr2 /=.
  rewrite switch_val_snd.
  move=> [= <- <-].
  do ! (split; first by []). by exists evinp.
Qed.

Lemma merged_load_intro (s : st) (tcell : mem_tag) (v2n : matom)
   (r1 r2 : reg mt) (w1 vw2 : mword mt) (t2 : mem_tag) (a2 : ratom) (evinp : Symbolic.ev_inputs) :
  is_code tcell -> is_code t2 = false ->
  Symbolic.mem s (vala (Symbolic.pc s) + 1)%w = Some v2n ->
  Symbolic.regs s r1 = Some (w1 @ Other) -> Symbolic.mem s w1 = Some (vw2 @ t2) ->
  Symbolic.regs s r2 = Some a2 ->
  (color tcell == match taga (Symbolic.pc s) with Level _ c => c end) ->
  (color tcell == color (taga v2n)) -> (color tcell == color t2) ->
  Symbolic.evi s = Some evinp ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
     s (IVec (OP LOAD) (taga (Symbolic.pc s)) tcell [hseq Other; t2; taga a2])
     [:: RegRead r1; MemRead w1; RegWrite r2 vw2]
   = Some (@Symbolic.State mt lrc_tags unit
            (setm (Symbolic.mem s) w1
               (vw2 @ (switch_val t2 (if is_address (vtag t2) then Invalidated else Other)).1))
            (setm (Symbolic.regs s) r2 (vw2 @ (vtag t2)))
            ((vala (Symbolic.pc s) + 1)%w @ (taga (Symbolic.pc s))) (Symbolic.internal s), None).
Proof.
  move=> Hic Hct2 Hsucc Hr1 Hmem Hr2 Hcur Hbel Hbelt2.
  move: Hcur; case: (taga (Symbolic.pc s)) => ltpc ctpc /= Hcur Hevi.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  rewrite Hsucc /= Hevi /=.
  rewrite /Merged.transfer /= /Merged.instr_rules Hic /= Hct2 /= /LRC.instr_rules /=.
  rewrite !color_matchE.
  have Hb2 : belong (color tcell) (Some (taga v2n)) = true by rewrite belong_someE.
  rewrite Hcur /= /check_belong Hb2 /= Hct2 orbF belong_matchE.
  have Hbt : (color tcell == color t2) = true by exact: Hbelt2.
  rewrite Hbt /=.
  rewrite (surjective_pairing (switch_val t2 (if is_address (vtag t2) then Invalidated else Other))) /=.
  rewrite /Symbolic.next_state_do_update /= Hr1 /= /updm Hr1 /= (setm_id Hr1) /=.
  rewrite !Hmem /=.
  rewrite Hr2 /=.
  by rewrite switch_val_snd.
Qed.

Lemma merged_store_inv
   (m : {fmap mword mt -> matom}) (rr : {fmap reg mt -> ratom})
   (pcw : mword mt) (tpc : tag_type lrc_tags Symbolic.P) (ext : unit)
   (ti : mem_tag) (v1n : matom) (r1 r2 : reg mt) (w1 w2 old : mword mt)
   (t1 t2 : value_tag) (told : mem_tag) (s' : st) (e : option event) :
  is_code ti -> m (pcw + 1)%w = Some v1n ->
  rr r1 = Some (w1 @ t1) -> rr r2 = Some (w2 @ t2) -> m w1 = Some (old @ told) ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
     (@Symbolic.State mt lrc_tags unit m rr (pcw @ tpc) ext)
     (IVec (OP STORE) tpc ti [hseq t1; t2; told]) [:: RegRead r1; RegRead r2; MemWrite w1 w2]
   = Some (s', e) ->
  s' = @Symbolic.State mt lrc_tags unit
         (setm m w1 (w2 @ (switch_val told t2).1))
         (setm rr r2 (w2 @ (if is_address t2 then Invalidated else Other)))
         ((pcw + 1)%w @ tpc) ext
  /\ e = None /\ t1 = Other /\ is_code told = false /\ (color ti == color told)
  /\ (color ti == match tpc with Level _ c => c end) /\ (color ti == color (taga v1n))
  /\ (exists ei, Symbolic.evi (@Symbolic.State mt lrc_tags unit m rr (pcw @ tpc) ext) = Some ei).
Proof.
  move=> Hic Hsucc Hr1 Hr2 Hmem.
  case: tpc => ltpc ctpc.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  rewrite Hsucc /=.
  case Hevi: (Symbolic.evi _) => [evinp|]; last by move=> [=].
  rewrite /Merged.transfer /= /Merged.instr_rules Hic /=.
  case Hctold: (is_code told); first by move=> [=].
  rewrite /LRC.instr_rules /=.
  rewrite !color_matchE.
  case Hcur: (color ti == ctpc); last by move=> [=].
  move: Hr1; case: t1 => [nr|||] Hr1; rewrite /is_other /=; try by move=> [=].
  rewrite /check_belong !belong_someE.
  case Hbel: (color ti == color (taga v1n)); last by move=> [=].
  case Hbelt: (color ti == color told); last by move=> [=].
  rewrite Hctold /=.
  rewrite (surjective_pairing (switch_val told t2)) /=.
  rewrite /= /Symbolic.next_state_do_update /= Hr1 /= /updm Hr1 /= (setm_id Hr1) /=.
  rewrite !Hr2 /=.
  rewrite !Hmem /=.
  move=> [= <- <-].
  do ! (split; first by []). by exists evinp.
Qed.

Lemma merged_store_intro (s : st) (tcell : mem_tag) (v2n : matom)
   (r1 r2 : reg mt) (w1 vw2 old : mword mt) (t2 : value_tag) (told : mem_tag)
   (evinp : Symbolic.ev_inputs) :
  is_code tcell -> is_code told = false ->
  Symbolic.mem s (vala (Symbolic.pc s) + 1)%w = Some v2n ->
  Symbolic.regs s r1 = Some (w1 @ Other) -> Symbolic.regs s r2 = Some (vw2 @ t2) ->
  Symbolic.mem s w1 = Some (old @ told) ->
  (color tcell == match taga (Symbolic.pc s) with Level _ c => c end) ->
  (color tcell == color (taga v2n)) -> (color tcell == color told) ->
  Symbolic.evi s = Some evinp ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
     s (IVec (OP STORE) (taga (Symbolic.pc s)) tcell [hseq Other; t2; told])
     [:: RegRead r1; RegRead r2; MemWrite w1 vw2]
   = Some (@Symbolic.State mt lrc_tags unit
            (setm (Symbolic.mem s) w1 (vw2 @ (switch_val told t2).1))
            (setm (Symbolic.regs s) r2 (vw2 @ (if is_address t2 then Invalidated else Other)))
            ((vala (Symbolic.pc s) + 1)%w @ (taga (Symbolic.pc s))) (Symbolic.internal s), None).
Proof.
  move=> Hic Hctold Hsucc Hr1 Hr2 Hmem Hcur Hbel Hbelt.
  move: Hcur; case: (taga (Symbolic.pc s)) => ltpc ctpc /= Hcur Hevi.
  rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  rewrite Hsucc /= Hevi /=.
  rewrite /Merged.transfer /= /Merged.instr_rules Hic /= Hctold /= /LRC.instr_rules /=.
  rewrite !color_matchE.
  rewrite Hcur /= /check_belong !belong_someE Hbel Hbelt /= Hctold /=.
  rewrite (surjective_pairing (switch_val told t2)) /=.
  rewrite /Symbolic.next_state_do_update /= Hr1 /= /updm Hr1 /= (setm_id Hr1) /=.
  rewrite !Hr2 /=.
  by rewrite !Hmem /=.
Qed.

Lemma merged_bnz_inv
   (m : {fmap mword mt -> matom}) (rr : {fmap reg mt -> ratom})
   (pcw : mword mt) (tpc : tag_type lrc_tags Symbolic.P) (ext : unit)
   (ti : mem_tag) (r : reg mt) (w : mword mt) (t1 : value_tag)
   (pc' : mword mt) (celln : matom) (s' : st) (e : option event) :
  is_code ti -> rr r = Some (w @ t1) -> m pc' = Some celln ->
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
     (@Symbolic.State mt lrc_tags unit m rr (pcw @ tpc) ext)
     (IVec (OP BNZ) tpc ti [hseq t1]) [:: RegRead r] pc'
   = Some (s', e) ->
  s' = @Symbolic.State mt lrc_tags unit m rr (pc' @ tpc) ext
  /\ e = None /\ t1 = Other /\ (color ti == match tpc with Level _ c => c end)
  /\ (color ti == color (taga celln))
  /\ (exists ei, Symbolic.evi (@Symbolic.State mt lrc_tags unit m rr (pcw @ tpc) ext) = Some ei).
Proof.
  move=> Hic Hr Hmem'.
  case: tpc => ltpc ctpc.
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  rewrite Hmem' /=.
  case Hevi: (Symbolic.evi _) => [evinp|]; last by move=> [=].
  rewrite /Merged.transfer /= /Merged.instr_rules Hic /= /LRC.instr_rules /=.
  rewrite !color_matchE.
  case Hcur: (color ti == ctpc); last by move=> [=].
  move: Hr; case: t1 => [nr|||] Hr; rewrite /is_other /=; try by move=> [=].
  rewrite /check_belong belong_someE.
  case Hbel: (color ti == color (taga celln)); last by move=> [=].
  rewrite /= /Symbolic.next_state_do_update /= Hr /= /updm Hr /= (setm_id Hr) /=.
  move=> [= <- <-].
  do ! (split; first by []). by exists evinp.
Qed.

Lemma merged_bnz_intro (s : st) (tcell : mem_tag)
   (r : reg mt) (w : mword mt) (pc' : mword mt) (celln : matom) (evinp : Symbolic.ev_inputs) :
  is_code tcell -> Symbolic.regs s r = Some (w @ Other) -> Symbolic.mem s pc' = Some celln ->
  (color tcell == match taga (Symbolic.pc s) with Level _ c => c end) ->
  (color tcell == color (taga celln)) ->
  Symbolic.evi s = Some evinp ->
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
     s (IVec (OP BNZ) (taga (Symbolic.pc s)) tcell [hseq Other]) [:: RegRead r] pc'
   = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem s) (Symbolic.regs s)
            (pc' @ (taga (Symbolic.pc s))) (Symbolic.internal s), None).
Proof.
  move=> Hic Hr Hmem' Hcur Hbel.
  move: Hcur; case: (taga (Symbolic.pc s)) => ltpc ctpc /= Hcur Hevi.
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state /=.
  rewrite Hmem' /= Hevi /=.
  rewrite /Merged.transfer /= /Merged.instr_rules Hic /= /LRC.instr_rules /=.
  rewrite !color_matchE.
  have Hb : belong (color tcell) (Some (taga celln)) = true by rewrite belong_someE.
  rewrite Hcur /= /check_belong Hb /=.
  rewrite /Symbolic.next_state_do_update /= Hr /= /updm Hr /= (setm_id Hr) /=.
  by [].
Qed.

Lemma addr_ok_setm_mono (m : {fmap mword mt -> atom (mword mt) mem_tag})
    (k : mword mt) (a : atom (mword mt) mem_tag) (w : mword mt) :
  addr_ok m w -> addr_ok (setm m k a) w.
Proof.
  rewrite /addr_ok; case=> [[c Hc]|H]; last by right.
  left; rewrite setmE; case: (w =P k) => [_|_]; [by exists a | by exists c].
Qed.

Lemma vreg_setm (m : {fmap mword mt -> atom (mword mt) mem_tag}) (rg : {fmap reg mt -> ratom})
    (r0 : reg mt) (a : ratom) :
  (is_address (taga a) -> addr_ok m (vala a)) ->
  (forall r w t, rg r = Some (w @ t) -> is_address t -> addr_ok m w) ->
  forall r w t, setm rg r0 a r = Some (w @ t) -> is_address t -> addr_ok m w.
Proof.
  move=> Ha IH r w t; rewrite setmE; case: (r =P r0) => [_|_]; last exact: IH.
  move=> [= Heq] Haddr. rewrite Heq in Ha. apply: Ha. exact: Haddr.
Qed.

Lemma vreg_setm_other (m : {fmap mword mt -> atom (mword mt) mem_tag}) (rg : {fmap reg mt -> ratom})
    (r0 : reg mt) (v : mword mt) :
  (forall r w t, rg r = Some (w @ t) -> is_address t -> addr_ok m w) ->
  forall r w t, setm rg r0 (v @ Other) r = Some (w @ t) -> is_address t -> addr_ok m w.
Proof.
  move=> IH r w t; rewrite setmE; case: (r =P r0) => [_|_]; last exact: IH.
  move=> [= _ <-] H; discriminate H.
Qed.

Lemma reg_strong (rg1 rg2 : {fmap reg mt -> ratom})
  (H : forall r, oapp (fun a : ratom => exists v2, rg2 r = Some (v2 @ (taga a))
                       /\ (taga a <> Invalidated -> v2 = rel_v (taga a) (vala a)))
                  (rg2 r = None) (rg1 r))
  (r : reg mt) (w : mword mt) (t : value_tag) :
  rg1 r = Some (w @ t) -> t <> Invalidated -> rg2 r = Some ((rel_v t w) @ t).
Proof. move=> Hr Hni; move: (H r); rewrite Hr /= => [[v2 [Hr2 Hv2]]]; by rewrite Hr2 (Hv2 Hni). Qed.

Lemma reg_some (rg1 rg2 : {fmap reg mt -> ratom})
  (H : forall r, oapp (fun a : ratom => exists v2, rg2 r = Some (v2 @ (taga a))
                       /\ (taga a <> Invalidated -> v2 = rel_v (taga a) (vala a)))
                  (rg2 r = None) (rg1 r))
  (r : reg mt) (a : ratom) :
  rg1 r = Some a -> exists v2, rg2 r = Some (v2 @ (taga a)).
Proof. move=> Hr; move: (H r); rewrite Hr /= => [[v2 [Hr2 _]]]; by exists v2. Qed.

Lemma regrel_setm (rg1 rg2 : {fmap reg mt -> ratom}) (r0 : reg mt) (a1 a2 : ratom)
  (H : forall r, oapp (fun a : ratom => exists v2, rg2 r = Some (v2 @ (taga a))
                       /\ (taga a <> Invalidated -> v2 = rel_v (taga a) (vala a)))
                  (rg2 r = None) (rg1 r))
  (Ht : taga a2 = taga a1)
  (Hv : taga a1 <> Invalidated -> vala a2 = rel_v (taga a1) (vala a1)) :
  forall r, oapp (fun a : ratom => exists v2, (setm rg2 r0 a2) r = Some (v2 @ (taga a))
                       /\ (taga a <> Invalidated -> v2 = rel_v (taga a) (vala a)))
                 ((setm rg2 r0 a2) r = None) (setm rg1 r0 a1 r).
Proof.
  move=> r; rewrite !setmE; case: (r =P r0) => [_|_]; last exact: (H r).
  exists (vala a2). split; first by rewrite -Ht atom_etaE. exact: Hv.
Qed.

Lemma reg_get (rg1 rg2 : {fmap reg mt -> ratom})
  (H : forall r, oapp (fun a : ratom => exists v2, rg2 r = Some (v2 @ (taga a))
                       /\ (taga a <> Invalidated -> v2 = rel_v (taga a) (vala a)))
                  (rg2 r = None) (rg1 r))
  (r : reg mt) (w : mword mt) (t : value_tag) :
  rg1 r = Some (w @ t) -> exists v2, rg2 r = Some (v2 @ t) /\ (t <> Invalidated -> v2 = rel_v t w).
Proof. move=> Hr; move: (H r); rewrite Hr /=; by []. Qed.

Lemma reg_otherE (rg1 rg2 : {fmap reg mt -> ratom})
  (H : forall r, oapp (fun a : ratom => exists v2, rg2 r = Some (v2 @ (taga a))
                       /\ (taga a <> Invalidated -> v2 = rel_v (taga a) (vala a)))
                  (rg2 r = None) (rg1 r))
  (r : reg mt) (w : mword mt) (t : value_tag) :
  rg1 r = Some (w @ t) -> t = Other -> rg2 r = Some (w @ Other).
Proof.
  move=> Hr Ht; have [v2 [Hr2 Hv2]] := reg_get H Hr.
  have Ev : v2 = w. { rewrite (Hv2 _); [by rewrite /rel_v Ht | by rewrite Ht]. }
  by rewrite Hr2 Ht Ev.
Qed.

Lemma mem_get (m1 m2 : {fmap mword mt -> atom (mword mt) mem_tag}) (H : memwk m1 m2)
  (w : mword mt) (v : mword mt) (t : mem_tag) :
  m1 w = Some (v @ t) -> is_code t = false ->
  exists v2, m2 w = Some (v2 @ t) /\ (vtag t <> Invalidated -> v2 = rel_v (vtag t) v).
Proof. move=> Hw Hc; exact: (H w (v @ t) Hw Hc). Qed.

Lemma jump_target_corr (m1 m2 : {fmap mword mt -> matom}) (w : mword mt) (celltgt : matom)
   (Hc1 : forall w0 a, m1 w0 = Some a -> is_code (taga a) -> encode_code (code q) pc0 w0 = Some a)
   (Hc1' : forall w0 a, encode_code (code q) pc0 w0 = Some a -> m1 w0 = Some a)
   (Hc2' : forall w0 a, encode_code padc pc0 w0 = Some a -> m2 w0 = Some a)
   (Hnc1 : memwk m1 m2)
   (Htgt : m1 w = Some celltgt) :
   exists celltgt2, m2 (phia w) = Some celltgt2 /\ taga celltgt2 = taga celltgt.
Proof.
  have Hbw : pc0 + size (code q) < 2 ^ word_size mt by exact: (ltn_trans Hbound alloc_label_lt_word).
  case Hcc : (is_code (taga celltgt)).
  - have Henc := Hc1 _ _ Htgt Hcc.
    have [n [i [t [Hnlt [Hw [Hnth [Htag _]]]]]]] := code_cell_q Henc.
    have [v2 [Henc2 [Htag2 _]]] := code_cell_padc Hnlt Hnth.
    have Hphi : phia w = word_of_nat (shift_pos sizes n + pc0)
      by rewrite Hw; exact: (phia_addr_code Hnlt).
    exists v2. rewrite Hphi.
    split; first exact: (Hc2' _ _ Henc2). by rewrite Htag2 -Htag.
  - have Hpid : phia w = w.
    { rewrite /phia.
      case: (ltnP (val w) pc0) => Hlo; first by rewrite (phia_nat_id_lo Hlo); exact: valwK.
      case: (ltnP (val w) (pc0 + size (code q))) => Hhi; last by rewrite (phia_nat_id_hi Hhi); exact: valwK.
      exfalso.
      have Hk : (val w - pc0) < size (code q) by lia.
      have [v Hv] := encode_code_dom Hbw Hk.
      have Hwn : word_of_nat ((val w - pc0) + pc0) = w.
      { have -> : (val w - pc0) + pc0 = val w by lia. exact: valwK. }
      rewrite Hwn in Hv.
      have Hm1 := Hc1' _ _ Hv. rewrite Htgt in Hm1. case: Hm1 => Hcell.
      have := code_tags_wf_q Hv. by rewrite -Hcell Hcc. }
    rewrite Hpid.
    have [v2 [Hm2 _]] := Hnc1 _ _ Htgt Hcc.
    exists (v2 @ (taga celltgt)). split; first exact: Hm2. by rewrite taga_at.
Qed.

Lemma size_flatten_le_align_l (bs bs' : seq (@Merged.code mt)) :
  size (flatten bs) <= size (align_blocks bs bs').1.
Proof.
  elim: bs bs' => [|b bs IH] bs' /=; first by [].
  case: bs' => [|b' bs'] /=; first exact: leqnn.
  case E: (align_blocks bs bs') => [r r'] /=.
  rewrite /block_pad !size_cat size_nseq.
  have := IH bs'; rewrite E /= => Hr.
  have := leq_maxl (size b) (size b'); lia.
Qed.

Lemma size_code_le_padc : size (code q) <= size padc.
Proof.
  rewrite /padc /pad_code -{1}(proc_split_flatten (code q)).
  exact: size_flatten_le_align_l.
Qed.

Lemma jump_belong_corr (s1 s2 : st) (w : mword mt) (c : Component.id) :
  match_pad s1 s2 -> addr_ok (Symbolic.mem s1) w ->
  belong c (match Symbolic.mem s1 w with Some ni => Some (taga ni) | None => None end) ->
  belong c (match Symbolic.mem s2 (phia w) with Some ni => Some (taga ni) | None => None end).
Proof.
  move=> [_ [_ [_ [_ [Hc1 [Hc1' [Hc2 [Hc2' [Hnc1 Hnc2]]]]]]]]] Hok Hb.
  have Hbw' : pc0 + size padc < 2 ^ word_size mt by exact: (ltn_trans Hbound' alloc_label_lt_word).
  case Hmw: (Symbolic.mem s1 w) => [celltgt|].
  - have [celltgt2 [Hm2 Ht2]] := jump_target_corr Hc1 Hc1' Hc2' Hnc1 Hmw.
    move: Hb; rewrite Hmw Hm2 !belong_someE Ht2. by [].
  - have Hout : pc0 + size padc <= val w \/ val w < pc0.
    { case: Hok => [[c0 Hc0]|H]; [by rewrite Hmw in Hc0 | exact: H]. }
    have Hpid : phia w = w.
    { rewrite /phia; case: (ltnP (val w) pc0) => Hlo;
        first by rewrite (phia_nat_id_lo Hlo); exact: valwK.
      have Hle : pc0 + size (code q) <= val w.
      { case: Hout => H; [ have := size_code_le_padc; lia | move: Hlo H; lia ]. }
      rewrite (phia_nat_id_hi Hle); exact: valwK. }
    rewrite Hpid; case Hm2: (Symbolic.mem s2 w) => [a|]; last by [].
    exfalso; case Hcc: (is_code (taga a)).
    + have Henc := Hc2 _ _ Hm2 Hcc.
      have [n [Hwn [Hnlt _]]] := encode_code_nth_inv Henc.
      have Hb2 : n + pc0 < 2 ^ word_size mt by move: Hnlt Hbw'; lia.
      have Hval : (val w : nat) = n + pc0 by rewrite Hwn (val_word_of_nat Hb2).
      move: Hout; rewrite Hval; lia.
    + have [a0 [Ha0 _]] := Hnc2 _ _ Hm2 Hcc.
      by rewrite Ha0 in Hmw.
Qed.

Lemma memrel_fwd (m1 m2 : {fmap mword mt -> atom (mword mt) mem_tag})
  (w0 : mword mt) (b1 b2 : atom (mword mt) mem_tag) (H : memwk m1 m2)
  (Ht : taga b2 = taga b1)
  (Hv : vtag (taga b1) <> Invalidated -> vala b2 = rel_v (vtag (taga b1)) (vala b1)) :
  memwk (setm m1 w0 b1) (setm m2 w0 b2).
Proof.
  move=> w a; rewrite !setmE; case: (w =P w0) => [_|_]; last exact: (H w a).
  move=> [= Hb] _; rewrite -Hb. exists (vala b2). split; first by rewrite -Ht atom_etaE. exact: Hv.
Qed.

Lemma memrel_bwd (m1 m2 : {fmap mword mt -> atom (mword mt) mem_tag})
  (w0 : mword mt) (b1 b2 : atom (mword mt) mem_tag) (H : memwk_bwd m1 m2)
  (Ht : taga b2 = taga b1)
  (Hv : vtag (taga b1) <> Invalidated -> vala b2 = rel_v (vtag (taga b1)) (vala b1)) :
  memwk_bwd (setm m1 w0 b1) (setm m2 w0 b2).
Proof.
  move=> w a; rewrite !setmE; case: (w =P w0) => [_|_]; last exact: (H w a).
  move=> [= Hb] _; rewrite -Hb. exists b1. split; first by []. split; first exact: Ht. exact: Hv.
Qed.

Lemma return_clear (s1 s2 : @Symbolic.state mt lrc_tags unit) (r : reg mt)
   (rav w rcv : mword mt) (rat t1 : value_tag) (l : hseq _ _) :
  wregs (Symbolic.regs s1) (Symbolic.regs s2) ->
  Symbolic.regs s1 ra = Some (rav @ rat) ->
  Symbolic.regs s1 r = Some (w @ t1) ->
  Symbolic.regs s1 rcom = Some (rcv @ Other) ->
  r != rcom -> ra != rcom ->
  Symbolic.reg_clear_list (Symbolic.regs s1) t1 = Some l ->
  exists sd1 sd2,
    @Symbolic.next_state_do_updates mt lrc_tags unit s1
       [:: Symbolic.R, Symbolic.R, Symbolic.R & nseq 10 Symbolic.R]
       (Invalidated :: Invalidated :: Other :: reg_invalidate_hseq)%hseq
       (RegRead ra :: RegRead r :: reg_clear_read) = Some sd1 /\
    @Symbolic.next_state_do_updates mt lrc_tags unit s2
       [:: Symbolic.R, Symbolic.R, Symbolic.R & nseq 10 Symbolic.R]
       (Invalidated :: Invalidated :: Other :: reg_invalidate_hseq)%hseq
       (RegRead ra :: RegRead r :: reg_clear_read) = Some sd2 /\
    wregs (Symbolic.regs sd1) (Symbolic.regs sd2) /\
    Symbolic.mem sd1 = Symbolic.mem s1 /\ Symbolic.mem sd2 = Symbolic.mem s2 /\
    Symbolic.pc sd1 = Symbolic.pc s1 /\ Symbolic.pc sd2 = Symbolic.pc s2 /\
    Symbolic.internal sd1 = Symbolic.internal s1 /\ Symbolic.internal sd2 = Symbolic.internal s2.
Proof.
  move=> Hw Hra Hr Hrcom Hrne Harne Hcl.
  have [a2ra H2ra] : exists a, Symbolic.regs s2 ra = Some a.
  { have [v Hv] := reg_some Hw Hra. by exists (v @ (taga (rav @ rat))). }
  have Hrcom2 := reg_otherE Hw Hrcom erefl.
  set s1a := @Symbolic.State mt lrc_tags unit (Symbolic.mem s1)
               (setm (Symbolic.regs s1) ra ((vala (rav @ rat)) @ Invalidated)) (Symbolic.pc s1) (Symbolic.internal s1).
  set s2a := @Symbolic.State mt lrc_tags unit (Symbolic.mem s2)
               (setm (Symbolic.regs s2) ra ((vala a2ra) @ Invalidated)) (Symbolic.pc s2) (Symbolic.internal s2).
  have E1a : Symbolic.next_state_do_update s1 (Invalidated : Symbolic.tag_type lrc_tags Symbolic.R) (RegRead ra) = Some s1a
    by rewrite (reg_read_retag _ Hra).
  have E2a : Symbolic.next_state_do_update s2 (Invalidated : Symbolic.tag_type lrc_tags Symbolic.R) (RegRead ra) = Some s2a
    by rewrite (reg_read_retag _ H2ra).
  have Hwa : wregs (Symbolic.regs s1a) (Symbolic.regs s2a) by exact: (wregs_setm_inval Hw).
  have [ar Har] : exists a, Symbolic.regs s1a r = Some a.
  { rewrite /s1a /= setmE; case: eqP => [_|_]; [by eexists | by rewrite Hr; eexists]. }
  have [ar2 Har2] : exists a, Symbolic.regs s2a r = Some a.
  { have [v Hv] := reg_some Hwa Har. by exists (v @ (taga ar)). }
  set s1b := @Symbolic.State mt lrc_tags unit (Symbolic.mem s1a)
               (setm (Symbolic.regs s1a) r ((vala ar) @ Invalidated)) (Symbolic.pc s1a) (Symbolic.internal s1a).
  set s2b := @Symbolic.State mt lrc_tags unit (Symbolic.mem s2a)
               (setm (Symbolic.regs s2a) r ((vala ar2) @ Invalidated)) (Symbolic.pc s2a) (Symbolic.internal s2a).
  have E1b : Symbolic.next_state_do_update s1a (Invalidated : Symbolic.tag_type lrc_tags Symbolic.R) (RegRead r) = Some s1b
    by rewrite (reg_read_retag _ Har).
  have E2b : Symbolic.next_state_do_update s2a (Invalidated : Symbolic.tag_type lrc_tags Symbolic.R) (RegRead r) = Some s2b
    by rewrite (reg_read_retag _ Har2).
  have Hwb : wregs (Symbolic.regs s1b) (Symbolic.regs s2b) by exact: (wregs_setm_inval Hwa).
  have Hrne' : r != as_word (ssrint.Posz 1) := Hrne.
  have Harne' : as_word (ssrint.Posz 4) != as_word (ssrint.Posz 1) := Harne.
  have Hrcom1b : Symbolic.regs s1b rcom = Some (rcv @ Other).
  { rewrite /s1b /s1a /= !setmE.
    case: (as_word (ssrint.Posz 1) =P r) => [E|_]; first by move: Hrne'; rewrite E eqxx.
    case: (as_word (ssrint.Posz 1) =P as_word (ssrint.Posz 4)) => [E|_]; first by move: Harne'; rewrite -E eqxx.
    exact: Hrcom. }
  have Hrcom2b : Symbolic.regs s2b rcom = Some (rcv @ Other).
  { rewrite /s2b /s2a /= !setmE.
    case: (as_word (ssrint.Posz 1) =P r) => [E|_]; first by move: Hrne'; rewrite E eqxx.
    case: (as_word (ssrint.Posz 1) =P as_word (ssrint.Posz 4)) => [E|_]; first by move: Harne'; rewrite -E eqxx.
    exact: Hrcom2. }
  set s1c := @Symbolic.State mt lrc_tags unit (Symbolic.mem s1b)
               (setm (Symbolic.regs s1b) rcom (rcv @ Other)) (Symbolic.pc s1b) (Symbolic.internal s1b).
  set s2c := @Symbolic.State mt lrc_tags unit (Symbolic.mem s2b)
               (setm (Symbolic.regs s2b) rcom (rcv @ Other)) (Symbolic.pc s2b) (Symbolic.internal s2b).
  have E1c : Symbolic.next_state_do_update s1b (Other : Symbolic.tag_type lrc_tags Symbolic.R) (RegRead rcom) = Some s1c
    by rewrite (reg_read_retag _ Hrcom1b) vala_at.
  have E2c : Symbolic.next_state_do_update s2b (Other : Symbolic.tag_type lrc_tags Symbolic.R) (RegRead rcom) = Some s2c
    by rewrite (reg_read_retag _ Hrcom2b) vala_at.
  have Hwc : wregs (Symbolic.regs s1c) (Symbolic.regs s2c) by exact: (wregs_setm_other Hwb).
  have Hdomc : forall k, k \in [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19] ->
                 exists a, Symbolic.regs s1c (as_word (ssrint.Posz k)) = Some a.
  { move=> k Hk.
    have Hkrl : k \in Symbolic.reg_list by rewrite /Symbolic.reg_list in_cons; apply/orP; right.
    have [a Ha] := reg_clear_list_aux_dom Hcl Hkrl.
    rewrite /s1c /s1b /s1a /= !setmE.
    case: eqP => [_|_]; first by eexists.
    case: eqP => [_|_]; first by eexists.
    case: eqP => [_|_]; first by eexists.
    by rewrite Ha; eexists. }
  have [sd1 [sd2 [Hd1 [Hd2 [Hwd [Hm1 [Hm2 [Hp1 [Hp2 [Hi1 Hi2]]]]]]]]]]
    := nsuap_inval_list Hwc Hdomc.
  exists sd1, sd2.
  have Hrcr : Symbolic.reg_clear_read
            = RegRead (as_word (ssrint.Posz 1))
              :: [seq RegRead (as_word (ssrint.Posz n)) | n <- [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]]
    by rewrite /Symbolic.reg_clear_read /Symbolic.reg_list.
  split.
  { rewrite ndsu_cons E1a; cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read addw].
    rewrite ndsu_cons E1b; cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read addw].
    rewrite Hrcr ndsu_cons E1c; cbn -[Symbolic.next_state_do_updates addw].
    exact: Hd1. }
  split.
  { rewrite ndsu_cons E2a; cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read addw].
    rewrite ndsu_cons E2b; cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read addw].
    rewrite Hrcr ndsu_cons E2c; cbn -[Symbolic.next_state_do_updates addw].
    exact: Hd2. }
  split; first exact: Hwd.
  by rewrite Hm1 Hm2 Hp1 Hp2 Hi1 Hi2.
Qed.

Lemma jal_call_clear (s1 s2 : @Symbolic.state mt lrc_tags unit)
   (old1 old2 : mword mt) (told1 told2 : value_tag) (rcv : mword mt) (level : nat)
   (vret1 vret2 : mword mt) (tret : mem_tag) :
  wregs (Symbolic.regs s1) (Symbolic.regs s2) ->
  Symbolic.regs s1 ra = Some (old1 @ told1) ->
  Symbolic.regs s2 ra = Some (old2 @ told2) ->
  Symbolic.regs s1 rcom = Some (rcv @ Other) ->
  Symbolic.mem s1 (vala (Symbolic.pc s1) + 1)%w = Some (vret1 @ tret) ->
  Symbolic.mem s2 (vala (Symbolic.pc s2) + 1)%w = Some (vret2 @ tret) ->
  (vala (Symbolic.pc s2) + 1)%w = phia (vala (Symbolic.pc s1) + 1)%w ->
  (forall k, k \in [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N ->
       exists a, Symbolic.regs s1 (as_word (ssrint.Posz k)) = Some a) ->
  exists sd1 sd2,
    @Symbolic.next_state_do_updates mt lrc_tags unit s1
       [:: Symbolic.M, Symbolic.R, Symbolic.R & nseq 10 Symbolic.R]
       (tret :: (Ret level) :: Other :: reg_invalidate_hseq)%hseq
       (MemRead (vala (Symbolic.pc s1) + 1)%w :: RegWrite ra (vala (Symbolic.pc s1) + 1)%w :: reg_clear_read) = Some sd1 /\
    @Symbolic.next_state_do_updates mt lrc_tags unit s2
       [:: Symbolic.M, Symbolic.R, Symbolic.R & nseq 10 Symbolic.R]
       (tret :: (Ret level) :: Other :: reg_invalidate_hseq)%hseq
       (MemRead (vala (Symbolic.pc s2) + 1)%w :: RegWrite ra (vala (Symbolic.pc s2) + 1)%w :: reg_clear_read) = Some sd2 /\
    wregs (Symbolic.regs sd1) (Symbolic.regs sd2) /\
    Symbolic.mem sd1 = Symbolic.mem s1 /\ Symbolic.mem sd2 = Symbolic.mem s2 /\
    Symbolic.pc sd1 = Symbolic.pc s1 /\ Symbolic.pc sd2 = Symbolic.pc s2 /\
    Symbolic.internal sd1 = Symbolic.internal s1 /\ Symbolic.internal sd2 = Symbolic.internal s2.
Proof.
  move=> Hw Hra1 Hra2 Hrcom Hmem1 Hmem2 Hphi Hdom.
  have Hrcom2 := reg_otherE Hw Hrcom erefl.
  have E1a : Symbolic.next_state_do_update s1 (tret : Symbolic.tag_type lrc_tags Symbolic.M)
               (MemRead (vala (Symbolic.pc s1) + 1)%w) = Some s1 := mem_read_update_id Hmem1.
  have E2a : Symbolic.next_state_do_update s2 (tret : Symbolic.tag_type lrc_tags Symbolic.M)
               (MemRead (vala (Symbolic.pc s2) + 1)%w) = Some s2 := mem_read_update_id Hmem2.
  set s1b := @Symbolic.State mt lrc_tags unit (Symbolic.mem s1)
               (setm (Symbolic.regs s1) ra ((vala (Symbolic.pc s1) + 1)%w @ (Ret level))) (Symbolic.pc s1) (Symbolic.internal s1).
  set s2b := @Symbolic.State mt lrc_tags unit (Symbolic.mem s2)
               (setm (Symbolic.regs s2) ra ((vala (Symbolic.pc s2) + 1)%w @ (Ret level))) (Symbolic.pc s2) (Symbolic.internal s2).
  have E1b : Symbolic.next_state_do_update s1 (Ret level : Symbolic.tag_type lrc_tags Symbolic.R)
               (RegWrite ra (vala (Symbolic.pc s1) + 1)%w) = Some s1b
    by rewrite /Symbolic.next_state_do_update /= /updm Hra1 /=.
  have E2b : Symbolic.next_state_do_update s2 (Ret level : Symbolic.tag_type lrc_tags Symbolic.R)
               (RegWrite ra (vala (Symbolic.pc s2) + 1)%w) = Some s2b
    by rewrite /Symbolic.next_state_do_update /= /updm Hra2 /=.
  have Hwb : wregs (Symbolic.regs s1b) (Symbolic.regs s2b) by exact: (wregs_setm_ret Hw Hphi).
  have Hrcom1b : Symbolic.regs s1b rcom = Some (rcv @ Other).
  { rewrite /s1b /= setmE. by case: (rcom =P ra) => [_|_]; [ by [] | exact: Hrcom ]. }
  have Hrcom2b : Symbolic.regs s2b rcom = Some (rcv @ Other).
  { rewrite /s2b /= setmE. by case: (rcom =P ra) => [_|_]; [ by [] | exact: Hrcom2 ]. }
  set s1c := @Symbolic.State mt lrc_tags unit (Symbolic.mem s1b)
               (setm (Symbolic.regs s1b) rcom (rcv @ Other)) (Symbolic.pc s1b) (Symbolic.internal s1b).
  set s2c := @Symbolic.State mt lrc_tags unit (Symbolic.mem s2b)
               (setm (Symbolic.regs s2b) rcom (rcv @ Other)) (Symbolic.pc s2b) (Symbolic.internal s2b).
  have E1c : Symbolic.next_state_do_update s1b (Other : Symbolic.tag_type lrc_tags Symbolic.R) (RegRead rcom) = Some s1c
    by rewrite (reg_read_retag _ Hrcom1b) vala_at.
  have E2c : Symbolic.next_state_do_update s2b (Other : Symbolic.tag_type lrc_tags Symbolic.R) (RegRead rcom) = Some s2c
    by rewrite (reg_read_retag _ Hrcom2b) vala_at.
  have Hwc : wregs (Symbolic.regs s1c) (Symbolic.regs s2c) by exact: (wregs_setm_other Hwb).
  have Hdomc : forall k, k \in [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19] ->
                 exists a, Symbolic.regs s1c (as_word (ssrint.Posz k)) = Some a.
  { move=> k Hk. have [a Ha] := Hdom k Hk.
    rewrite /s1c /s1b /= !setmE.
    case: eqP => [_|_]; first by eexists.
    case: eqP => [_|_]; first by eexists.
    by rewrite Ha; eexists. }
  have [sd1 [sd2 [Hd1 [Hd2 [Hwd [Hm1 [Hm2 [Hp1 [Hp2 [Hi1 Hi2]]]]]]]]]]
    := nsuap_inval_list Hwc Hdomc.
  exists sd1, sd2.
  have Hrcr : Symbolic.reg_clear_read
            = RegRead (as_word (ssrint.Posz 1))
              :: [seq RegRead (as_word (ssrint.Posz n)) | n <- [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]]
    by rewrite /Symbolic.reg_clear_read /Symbolic.reg_list.
  split.
  { rewrite ndsu_cons E1a; cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read addw].
    rewrite ndsu_cons E1b; cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read addw].
    rewrite Hrcr ndsu_cons E1c; cbn -[Symbolic.next_state_do_updates addw].
    exact: Hd1. }
  split.
  { rewrite ndsu_cons E2a; cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read addw].
    rewrite ndsu_cons E2b; cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read addw].
    rewrite Hrcr ndsu_cons E2c; cbn -[Symbolic.next_state_do_updates addw].
    exact: Hd2. }
  split; first exact: Hwd.
  rewrite Hm1 Hm2 Hp1 Hp2 Hi1 Hi2 /s1c /s1b /s2c /s2b.
  by repeat split.
Qed.

Lemma jal_call_nsuap (s sd : @Symbolic.state mt lrc_tags unit) (tcell : mem_tag)
   (tgt : mword mt) (tret : mem_tag) (told : value_tag)
   (level : nat) (ctpc : Component.id) (p : Procedure.id)
   (c : hseq (Symbolic.tag_type lrc_tags) (nseq 10 Symbolic.R))
   (celltgt : matom) (evinp : Symbolic.ev_inputs) :
   is_code tcell ->
   taga (Symbolic.pc s) = Level level ctpc ->
   color tcell == ctpc ->
   color tcell == color tret ->
   Symbolic.mem s tgt = Some celltgt ->
   color tcell != color (taga celltgt) ->
   get_proc_name (Some (taga celltgt)) = Some p ->
   check_entry (color tcell) (Some (taga celltgt)) = Some tt ->
   Symbolic.evi s = Some evinp ->
   @Symbolic.next_state_do_updates mt lrc_tags unit s
      [:: Symbolic.M, Symbolic.R, Symbolic.R & nseq 10 Symbolic.R]
      (tret :: (Ret level) :: Other :: reg_invalidate_hseq)%hseq
      (MemRead (vala (Symbolic.pc s) + 1)%w :: RegWrite ra (vala (Symbolic.pc s) + 1)%w :: reg_clear_read) = Some sd ->
   @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
      s (IVec (OP JAL) (taga (Symbolic.pc s)) tcell (HSeqCons tret (HSeqCons told (HSeqCons Other c))))
      [:: MemRead (vala (Symbolic.pc s) + 1)%w, RegWrite ra (vala (Symbolic.pc s) + 1)%w & reg_clear_read]
      tgt
   = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem sd) (Symbolic.regs sd)
             (tgt @ (build_tpc (level.+1) (color (taga celltgt)))) (Symbolic.internal sd),
           Some (ECall (color tcell) p (rcom_value evinp) (color (taga celltgt)))).
Proof.
  move=> Hic Hpct Hcur Hcret Hmw Hbel Hpname Hentry Hevi Hsd.
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state Hevi [obind _ (Some evinp)]/= Hmw.
  have Htr : Merged.transfer (IVec (OP JAL) (taga (Symbolic.pc s)) tcell
               (HSeqCons tret (HSeqCons told (HSeqCons Other c))) (Some (taga celltgt))) evinp
           = Some (Symbolic.OVec JAL (build_tpc (level.+1) (color (taga celltgt)))
                     (tret :: (Ret level) :: Other :: reg_invalidate_hseq)%hseq,
                   Some (ECall (color tcell) p (rcom_value evinp) (color (taga celltgt)))).
  { rewrite /Merged.transfer /Merged.instr_rules Hic /LRC.instr_rules /= Hpct /=.
    rewrite !color_matchE Hcur /=.
    rewrite /check_belong belong_someE Hcret /=.
    rewrite belong_matchE (negbTE Hbel) /=.
    move: Hpname Hentry. rewrite /get_proc_name /check_entry.
    case: (taga celltgt) => [vt cc ee ic] /=.
    case: ee => [[pp el]|] //=.
    case Hms: (mem_seq el (color tcell)) => //=.
    by move=> [->] _. }
  rewrite Htr; cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read addw].
  by rewrite Hsd.
Qed.

Lemma is_jump_invE (t : value_tag) u : is_jump t = Some u -> t = InternalJump.
Proof. by case: t. Qed.
Lemma check_ret_invE (lev : nat) (t : value_tag) u :
  check_ret lev t = Some u -> exists n, t = Ret n /\ lev = n.+1.
Proof. case: t => [n|||] //=. case: ifP => [/eqP E _|//]. by exists n. Qed.
Lemma is_other_invE (t : value_tag) u : is_other t = Some u -> t = Other.
Proof. by case: t. Qed.

Lemma jump_step_inv (m : {fmap mword mt -> matom})
   (rr : {fmap reg mt -> atom (mword mt) (Symbolic.tag_type lrc_tags Symbolic.R)})
   (pcw0 : mword mt) (level : nat) (ctpc : Component.id) (ext : unit)
   (ti : mem_tag) (r : reg mt) (w rav : mword mt) (t1 rat : value_tag)
   (l : hseq (Symbolic.tag_type lrc_tags) (nseq (size Symbolic.reg_list).+1 Symbolic.R))
   (s' : st) (e : option event) :
   is_code ti -> rr r = Some (w @ t1) -> rr ra = Some (rav @ rat) ->
   Symbolic.reg_clear_list rr t1 = Some l ->
   @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
      (@Symbolic.State mt lrc_tags unit m rr
         (pcw0 @ ((Level level ctpc) : Symbolic.tag_type lrc_tags Symbolic.P)) ext)
      (IVec (OP JUMP) ((Level level ctpc) : Symbolic.tag_type lrc_tags Symbolic.P) ti (HSeqCons rat l))
      [:: RegRead ra, RegRead r & reg_clear_read] w = Some (s', e) ->
   (color ti == ctpc) /\
   ( (belong (color ti) (match m w with Some ni => Some (taga ni) | None => None end)
      /\ t1 = InternalJump)
     \/ (exists n celltgt rcv, m w = Some celltgt
          /\ ~~ belong (color ti) (Some (taga celltgt))
          /\ t1 = Ret n /\ level = n.+1 /\ rr rcom = Some (rcv @ Other)) ).
Proof.
  move=> Hic Hr Hra Hcl HN.
  have [a1 Ha1] : exists a, rr rcom = Some a.
  { case E: (rr rcom) => [a|]; first by exists a.
    exfalso; move: HN.
    by rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state /Symbolic.evi /= E /=. }
  have Hhd : hshead l = t1 := reg_clear_list_head Hcl.
  have H2nd : hshead (hsbehead l) = taga a1 := reg_clear_list_2nd Hcl Ha1.
  move: HN; rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state /Symbolic.evi Ha1.
  cbn -[Merged.transfer Symbolic.next_state_do_updates Symbolic.reg_clear_read].
  clear Hcl; move: Hhd H2nd; case: l => a lh; case: lh => b c => Hhd H2nd.
  have Ea : a = t1 := Hhd. have Eb : b = taga a1 := H2nd.
  case Hmw: (m w) => [celltgt|].
  - rewrite /Merged.transfer /Merged.instr_rules Hic /LRC.instr_rules.
    cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read belong].
    rewrite Ea Eb !color_matchE.
    case Hcur: (eqn (color ti) ctpc); last by [].
    case Hbel: (belong (color ti) (Some (taga celltgt))).
    + case Hjmp: (is_jump t1) => [u|]; last by [].
      move=> _; split; first by []; left; split; first by [].
      exact: (is_jump_invE Hjmp).
    + case Hoth: (is_other (taga a1)) => [u|]; last by [].
      rewrite gtc_someE.
      cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read check_ret].
      case Hck: (check_ret level t1) => [u2|]; last by [].
      move=> _; split; first by []; right.
      have [n [Hn Hlv]] := check_ret_invE Hck.
      have Hta1 : taga a1 = Other := is_other_invE Hoth.
      exists n, celltgt, (vala a1).
      split; first by [].
      split; first by (change (~~ belong (color ti) (Some (taga celltgt))); rewrite Hbel).
      split; first exact: Hn.
      split; first exact: Hlv.
      by rewrite -Hta1 (atom_etaE a1).
  - rewrite /Merged.transfer /Merged.instr_rules Hic /LRC.instr_rules.
    cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read belong].
    rewrite Ea !color_matchE.
    case Hcur: (eqn (color ti) ctpc); last by [].
    case Hjmp: (is_jump t1) => [u|]; last by [].
    move=> _; split; first by []; left; split; last exact: (is_jump_invE Hjmp).
    by [].
Qed.

Lemma jal_step_inv (m : {fmap mword mt -> matom})
   (rr : {fmap reg mt -> atom (mword mt) (Symbolic.tag_type lrc_tags Symbolic.R)})
   (pcw0 : mword mt) (imm : imm mt) (level : nat) (ctpc : Component.id) (ext : unit)
   (ti : mem_tag) (vret old : mword mt) (tret : mem_tag) (told : value_tag)
   (l : hseq (Symbolic.tag_type lrc_tags) (nseq (size Symbolic.reg_list).+1 Symbolic.R))
   (s' : st) (e : option event) :
   is_code ti -> m (pcw0 + 1)%w = Some (vret @ tret) -> rr ra = Some (old @ told) ->
   Symbolic.reg_clear_list rr told = Some l ->
   @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
      (@Symbolic.State mt lrc_tags unit m rr
         (pcw0 @ ((Level level ctpc) : Symbolic.tag_type lrc_tags Symbolic.P)) ext)
      (IVec (OP JAL) ((Level level ctpc) : Symbolic.tag_type lrc_tags Symbolic.P) ti (HSeqCons tret l))
      [:: MemRead (pcw0 + 1)%w, RegWrite ra (pcw0 + 1)%w & reg_clear_read] (swcast imm) = Some (s', e) ->
   (color ti == ctpc) /\ (color ti == color tret) /\
   ( belong (color ti) (match m (swcast imm) with Some ni => Some (taga ni) | None => None end)
     \/ (exists celltgt rcv, m (swcast imm) = Some celltgt
          /\ ~~ belong (color ti) (Some (taga celltgt))
          /\ rr rcom = Some (rcv @ Other)
          /\ (exists u, check_entry (color ti) (Some (taga celltgt)) = Some u)) ).
Proof.
  move=> Hic HRA HOLD Hcl HN.
  have [a1 Ha1] : exists a, rr rcom = Some a.
  { case E: (rr rcom) => [a|]; first by exists a.
    exfalso; move: HN.
    by rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state /Symbolic.evi E /=. }
  have Hhd : hshead l = told := reg_clear_list_head Hcl.
  have H2nd : hshead (hsbehead l) = taga a1 := reg_clear_list_2nd Hcl Ha1.
  move: HN; rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state /Symbolic.evi Ha1.
  cbn -[Merged.transfer Symbolic.next_state_do_updates Symbolic.reg_clear_read].
  clear Hcl; move: Hhd H2nd; case: l => a lh; case: lh => b c => Hhd H2nd.
  have Ea : a = told := Hhd. have Eb : b = taga a1 := H2nd.
  case Hmw: (m (swcast imm)) => [celltgt|].
  - rewrite /Merged.transfer /Merged.instr_rules Hic /LRC.instr_rules.
    cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read belong check_entry].
    rewrite Eb !color_matchE.
    case Hcur: (eqn (color ti) ctpc); last by [].
    rewrite /check_belong.
    case Hbret: (belong (color ti) (Some tret)); last by [].
    have Hcret : color ti == color tret by move: Hbret; rewrite belong_someE.
    case Hbel: (belong (color ti) (Some (taga celltgt))).
    + move=> _; split; first by []; split; first exact: Hcret.
      by left.
    + case Hoth: (is_other (taga a1)) => [u|]; last by [].
      rewrite gtc_someE.
      cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read belong check_entry].
      case Hce: (check_entry (color ti) (Some (taga celltgt))) => [u2|]; last by [].
      have Hta1 : taga a1 = Other := is_other_invE Hoth.
      have HnB : ~~ belong (color ti) (Some (taga celltgt)) by rewrite Hbel.
      move=> _; split; first by []; split; first exact: Hcret.
      right.
      exists celltgt, (vala a1).
      split; first by [].
      split; first exact: HnB.
      split; first by rewrite -Hta1 atom_etaE.
      by exists u2.
  - rewrite /Merged.transfer /Merged.instr_rules Hic /LRC.instr_rules.
    cbn -[Symbolic.next_state_do_updates Symbolic.reg_clear_read belong].
    rewrite !color_matchE.
    case Hcur: (eqn (color ti) ctpc); last by [].
    rewrite /check_belong.
    case Hbret: (belong (color ti) (Some tret)); last by [].
    move=> _; split; first by []. split; first by move: Hbret; rewrite belong_someE.
    by left.
Qed.
Lemma rel_v_Other (v : mword mt) : rel_v Other v = v.
Proof. by []. Qed.

Lemma rel_v_InternalJump (v : mword mt) : rel_v InternalJump v = phia v.
Proof. by []. Qed.
Lemma rel_v_Ret (n : nat) (v : mword mt) : rel_v (Ret n) v = phia v.
Proof. by []. Qed.

Lemma is_addrF_Other (t : value_tag) : is_address t = false -> t = Other.
Proof. by case: t. Qed.

Lemma code_fwd_setm {m enc : {fmap mword mt -> atom (mword mt) mem_tag}}
   {w0 : mword mt} {b : atom (mword mt) mem_tag}
   (Hc : forall w a, m w = Some a -> is_code (taga a) -> enc w = Some a)
   (Hb : is_code (taga b) = false) :
   forall w a, (setm m w0 b) w = Some a -> is_code (taga a) -> enc w = Some a.
Proof.
  move=> w a; rewrite setmE; case: (w =P w0) => [_|_]; last exact: Hc.
  move=> [= <-] Hic; move: Hic; by rewrite Hb.
Qed.

Lemma encode_none_noncode {m enc : {fmap mword mt -> atom (mword mt) mem_tag}}
   {w0 v : mword mt} {t : mem_tag}
   (Hwf : forall w a, enc w = Some a -> is_code (taga a))
   (Hc' : forall w a, enc w = Some a -> m w = Some a)
   (Hm : m w0 = Some (v @ t)) (Ht : is_code t = false) :
   enc w0 = None.
Proof.
  case E: (enc w0) => [a|]; last by [].
  have Hma := Hc' _ _ E. rewrite Hm in Hma. move: Hma => [= Eq]. subst a.
  move: (Hwf _ _ E). by rewrite taga_at Ht.
Qed.

Lemma code_bwd_setm {m enc : {fmap mword mt -> atom (mword mt) mem_tag}}
   {w0 : mword mt} {b : atom (mword mt) mem_tag}
   (Hc' : forall w a, enc w = Some a -> m w = Some a)
   (Hnone : enc w0 = None) :
   forall w a, enc w = Some a -> (setm m w0 b) w = Some a.
Proof.
  move=> w a He; rewrite setmE; case: (w =P w0) => [Hw|_]; last exact: (Hc' _ _ He).
  move: He; by rewrite Hw Hnone.
Qed.

End CodeShift.
