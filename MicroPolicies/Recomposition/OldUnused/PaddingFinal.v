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

Section CodeShiftFinal.

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
Hypothesis alloc_label_lt_NC : alloc_label < 2 ^ (word_size mt - NC).
Hypothesis code_colors_bounded : forall w a,
  encode_code (code q) pc0 w = Some a -> 1 + color (taga a) < 2 ^ NC.

Local Notation st := (@Symbolic.state mt lrc_tags unit).
Local Notation match_pad := (@PaddingSim.match_pad q q').
Local Notation pad_valid := (@PaddingSim.pad_valid q q').
Local Notation cptr_code := (@PaddingValid.cptr_code q).
Local Notation addr_ok := (@PaddingSim.addr_ok q q').
Local Notation pc_safe := (@PaddingValid.pc_safe q q').

Hypothesis jal_labels_resolved : forall n l t,
  nth_error (code q) n = Some (MrJal l, t) ->
  findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code q) = None ->
  l = alloc_label.

Definition Rf (s1 s2 : st) : Prop :=
  match_pad s1 s2 /\ pad_valid s1 /\ cptr_code s1 /\ pc_safe s1.

Lemma Rf_step1 : forall s1 s2 t s1',
  Rf s1 s2 -> pstep NC tt s1 t s1' -> exists s2', pstep NC tt s2 t s2' /\ Rf s1' s2'.
Proof.
  move=> s1 s2 t s1' [Hmp [Hpv [Hcc Hps]]]; rewrite /pstep; case: t => [|e [|??]] // Hstep;
    ( have [_ [_ [_ [_ [Hciso _]]]]] := Hmp;
      have [s2' [H2 Hmp']] := pad_step_fwd word_of_nat_inj Hcount Hbound Hbound'
          code_tags_wf_q code_tags_wf_padc fallthrough_aligned code_last_term bnz_labels_resolved
          alloc_label_lt_NC code_colors_bounded Hmp Hpv Hstep;
      by exists s2'; split;
        [ exact: H2
        | split; [ exact: Hmp'
          | split; [ exact: (pad_valid_step Hpv Hstep)
            | split; [ exact: (cptr_code_step Hcount Hbound Hbound' code_last_term Hciso Hcc Hstep)
                     | exact: (pc_safe_step Hcount Hbound Hbound' code_last_term bnz_labels_resolved
                                 Hciso Hcc Hstep) ] ] ] ] ).
Qed.

Hypothesis init_noncodeptr : forall w v t,
  unionm (encode_code (code q) pc0) (Merged.initial_memory (prog_buffers q)) w = Some (v @ t) ->
  is_codeptr (vtag t) = false.

Lemma pad_valid_init :
  pad_valid (Merged.initial_state (code q) (prog_buffers q) (prog_interface q)).
Proof.
  rewrite /PaddingSim.pad_valid /Merged.initial_state /=; split.
  - move=> r w t; rewrite /reg0 !setmE.
    repeat (case: ifP => _; first by move=> [= _ <-]).
    by rewrite emptymE.
  - by move=> w v t Hw; rewrite (init_noncodeptr Hw).
Qed.

Lemma cptr_code_init :
  cptr_code (Merged.initial_state (code q) (prog_buffers q) (prog_interface q)).
Proof.
  rewrite /PaddingValid.cptr_code /Merged.initial_state /=; split.
  - move=> r w t; rewrite /reg0 !setmE.
    repeat (case: ifP => _; first by move=> [= _ <-]).
    by rewrite emptymE.
  - by move=> w v t Hw; rewrite (init_noncodeptr Hw).
Qed.

Hypothesis main_in_code :
  find (fun '(_, tag) => color tag == Component.main) (code q) < size (code q).

Lemma pc_safe_init :
  pc_safe (Merged.initial_state (code q) (prog_buffers q) (prog_interface q)).
Proof.
  rewrite /PaddingValid.pc_safe.
  cbn [Merged.initial_state Symbolic.pc vala].
  left; rewrite val_word_of_nat.
  - move: main_in_code; lia.
  - have := alloc_label_lt_word; move: main_in_code Hbound; lia.
Qed.

Hypothesis initial_memory_domm : forall b,
  domm (@Merged.initial_memory mt b)
  = fset (map (@word_of_nat (word_size mt)) (List.seq 0 (size (@Merged.initial_memory mt b)))).

Hypothesis initial_memory_not_code : forall (w : mword mt) (v : matom),
  @Merged.initial_memory mt (prog_buffers q) w = Some v -> is_code (taga v) = false.

Lemma seqE : forall len start, List.seq start len = iota start len.
Proof. by elim => [|len IH] start //=; rewrite IH. Qed.

Lemma enc_data_disj (cde : @Merged.code mt) (w : mword mt) (v : matom) :
  pc0 + size cde < alloc_label ->
  @Merged.initial_memory mt (prog_buffers q) w = Some v ->
  encode_code cde pc0 w = None.
Proof.
  move=> Hsz Hmem.
  have Hsz2 : pc0 + size cde < 2 ^ word_size mt by have := alloc_label_lt_word; lia.
  have Hwd : w \in domm (@Merged.initial_memory mt (prog_buffers q)) by apply/dommP; exists v.
  move: Hwd; rewrite initial_memory_domm in_fset => /mapP[n Hn Hw].
  have Hnlt : n < size (@Merged.initial_memory mt (prog_buffers q))
    by move: Hn; rewrite seqE mem_iota add0n => /andP[_].
  case Henc: (encode_code cde pc0 w) => [v'|] //.
  exfalso.
  case: (encode_code_nth_inv Henc) => m [Hwm [Hltm _]].
  rewrite Hw in Hwm.
  have Hb1 : n < 2 ^ word_size mt by lia.
  have Hb2 : m + pc0 < 2 ^ word_size mt by lia.
  have He := word_of_nat_inj Hb1 Hb2 Hwm.
  move: Hnlt; rewrite He; lia.
Qed.

Hypothesis initial_memory_vtag_other : forall (w : mword mt) (v : matom),
  @Merged.initial_memory mt (prog_buffers q) w = Some v -> vtag (taga v) = Other.

Hypothesis main_entry_aligned :
  find (fun '(_, tag) => color tag == Component.main) padc
  = shift_pos sizes (find (fun '(_, tag) => color tag == Component.main) (code q)).

Lemma reg0_other (r : reg mt) (a : ratom) : reg0 r = Some a -> taga a = Other.
Proof. rewrite /reg0 !setmE; repeat (case: ifP => _; first by move=> [= <-]); by rewrite emptymE. Qed.

Lemma match_pad_init :
  match_pad (Merged.initial_state (code q) (prog_buffers q) (prog_interface q))
            (Merged.initial_state padc (prog_buffers q) (prog_interface q)).
Proof.
  rewrite /PaddingSim.match_pad.
  cbn [Merged.initial_state Symbolic.pc Symbolic.regs Symbolic.mem Symbolic.internal vala taga].
  split; last split; last split; last split; last split; last split; last split; last split; last split.
  -
    rewrite (addnC (size (@Merged.initial_memory mt (prog_buffers q)))
                   (find (fun '(_, tag) => color tag == Component.main) (code q))).
    by rewrite (phia_addr_code Hcount Hbound Hbound' main_in_code) main_entry_aligned addnC.
  -  by [].
  -  by [].
  -
    move=> r; case Hr: (reg0 r) => [a|] //=.
    have Hto := reg0_other Hr.
    exists (vala a); split; first by congr Some; rewrite atom_etaE.
    by move=> _; rewrite Hto; exact: (esym (rel_v_Other q q' (vala a))).
  -
    move=> w a; rewrite unionmE; case Henc: (encode_code (code q) _ w) => [a'|] /=.
    + by move=> [= <-].
    + by move=> Hdata Hcode; rewrite (initial_memory_not_code Hdata) in Hcode.
  -
    by move=> w a Henc; rewrite unionmE Henc.
  -
    move=> w a; rewrite unionmE; case Henc: (encode_code padc _ w) => [a'|] /=.
    + by move=> [= <-].
    + by move=> Hdata Hcode; rewrite (initial_memory_not_code Hdata) in Hcode.
  -
    by move=> w a Henc; rewrite unionmE Henc.
  -
    rewrite /PaddingSim.memwk.
    move=> w a; rewrite unionmE; case Henc: (encode_code (code q) _ w) => [a'|] /=.
    + by move=> [= <-] Hcode; rewrite (code_tags_wf_q Henc) in Hcode.
    + move=> Hdata _.
      rewrite unionmE (enc_data_disj Hbound' Hdata) /=.
      exists (vala a); split; first by rewrite Hdata; congr Some; rewrite atom_etaE.
      by move=> _; rewrite (initial_memory_vtag_other Hdata); exact: (esym (rel_v_Other q q' _)).
  -
    rewrite /PaddingSim.memwk_bwd.
    move=> w a; rewrite unionmE; case Henc: (encode_code padc _ w) => [a'|] /=.
    + by move=> [= <-] Hcode; rewrite (code_tags_wf_padc Henc) in Hcode.
    + move=> Hdata _.
      rewrite unionmE (enc_data_disj Hbound Hdata) /= Hdata.
      exists a; split; first by [].
      split; first by [].
      by move=> _; rewrite (initial_memory_vtag_other Hdata); exact: (esym (rel_v_Other q q' _)).
Qed.

Lemma imt_halt_indep (i : Merged.instr) (lp1 lp2 : nat -> nat -> nat) (pos1 pos2 : nat) :
  instr_merged_to_mp i lp1 pos1 = Halt mt -> instr_merged_to_mp i lp2 pos2 = Halt mt.
Proof. by case: i. Qed.

Lemma align_blocks_size_ge (bs bs' : seq (@Merged.code mt)) :
  size (flatten bs) <= size (align_blocks bs bs').1.
Proof.
  elim: bs bs' => [|b bs IH] [|b' bs'] //=.
  case E: (align_blocks bs bs') => [r r'] /=.
  have := IH bs'; rewrite E /= => Hle.
  rewrite size_cat size_cat block_pad_size.
  have Hm : size b <= maxn (size b) (maxn (size b) (size b')) by rewrite leq_maxl.
  move: Hle Hm; lia.
Qed.

Lemma size_code_le_padc : size (code q) <= size padc.
Proof.
  rewrite /padc /pad_code.
  have H := align_blocks_size_ge (proc_split (code q)) (proc_split (code q')).
  by rewrite proc_split_flatten in H.
Qed.

Local Opaque decode_instr.

Lemma Rf_final : forall s1 s2, Rf s1 s2 -> (pfinal s1 <-> pfinal s2).
Proof.
  move=> [m1 r1 [v1 t1] e1] [m2 r2 [v2 t2] e2] HR.
  have [Hmp [_ [_ Hps]]] := HR.
  have [Hpcv0 [_ [_ [_ [Hc1iso [Hc1rev [Hc2iso [Hc2rev _]]]]]]]] := Hmp.
  cbn [Symbolic.mem Symbolic.pc vala] in Hpcv0, Hc1iso, Hc1rev, Hc2iso, Hc2rev.
  rewrite /PaddingValid.pc_safe in Hps; cbn [Symbolic.pc vala] in Hps.
  rewrite /pfinal /=; split.
  -
    case Hm1: (m1 v1) => [[i1 tag1]|] // [Hdec1 Hcode1].
    have Henc1 : encode_code (code q) pc0 v1 = Some (i1 @ tag1) by apply: (Hc1iso _ _ Hm1 Hcode1).
    have [n [im [tm [Hn [Hvq [Hnth [Htagq Hdecq]]]]]]] := code_cell_q Hcount Hbound Hbound' Henc1.
    move: Hdecq Htagq; rewrite vala_at taga_at => Hdecq Htagq.
    have [[iv2 tv2] [Henc2 [Htag2 Hdec2]]] := code_cell_padc word_of_nat_inj Hcount Hbound Hbound' Hn Hnth.
    move: Hdec2 Htag2; rewrite vala_at taga_at => Hdec2 Htag2.
    have Hm2v2 : m2 v2 = Some (iv2 @ tv2).
    { rewrite Hpcv0 Hvq (phia_addr_code Hcount Hbound Hbound' Hn); exact: (Hc2rev _ _ Henc2). }
    rewrite Hm2v2; split.
    + rewrite Hdec2; congr Some; apply: imt_halt_indep.
      have Hh := Hdecq; rewrite Hdec1 in Hh; move: Hh => [= Hh]; exact: (esym Hh).
    + by rewrite Htag2 -Htagq.
  -
    case Hm2: (m2 v2) => [[i2 tag2]|] // [Hdec2 Hcode2].
    have Henc2 : encode_code padc pc0 v2 = Some (i2 @ tag2) by apply: (Hc2iso _ _ Hm2 Hcode2).
    have [k [Hv2k Hk]] := encode_code_nth_inv Henc2.
    have Hval2 : (val v2 : nat) = k + pc0.
    { rewrite Hv2k val_word_of_nat //. have := alloc_label_lt_word; move: Hk Hbound'; lia. }
    have [n [Hn Hvq]] : exists n, n < size (code q)
                            /\ v1 = word_of_nat (n + size (@Merged.initial_memory mt (prog_buffers q))).
    { case: Hps => Hpcsafe.
      - case: (ltnP (val v1) (size (@Merged.initial_memory mt (prog_buffers q)))) => Hlo.
        + exfalso.
          have Hv2v1 : (val v2 : nat) = val v1.
          { rewrite Hpcv0 /phia valw_won (phia_nat_id_lo q' Hlo) modn_small;
              [ by [] | have := alloc_label_lt_word; move: Hlo Hbound; lia ]. }
          move: Hval2 Hv2v1 Hlo; lia.
        + exists (val v1 - size (@Merged.initial_memory mt (prog_buffers q))); split;
            first by move: Hpcsafe Hlo; lia.
          by rewrite (subnK Hlo); symmetry; exact: valwK.
      - exfalso.
        have Hge : size (@Merged.initial_memory mt (prog_buffers q)) + size (code q) <= val v1
          by have := size_code_le_padc; move: Hpcsafe; lia.
        have Hv2v1 : (val v2 : nat) = val v1.
        { rewrite Hpcv0 /phia valw_won (phia_nat_id_hi Hcount Hbound Hbound' Hge) modn_small;
            [ by [] | exact: ltn_ord ]. }
        move: Hval2 Hv2v1 Hpcsafe Hk; lia. }
    have [[i1' tag1'] Henc1] := encode_code_dom word_of_nat_inj
                                  (ltn_trans Hbound alloc_label_lt_word) Hn.
    rewrite -Hvq in Henc1.
    have [n1 [im [tm [Hn1 [Hvq1 [Hnth [Htagq Hdecq]]]]]]] := code_cell_q Hcount Hbound Hbound' Henc1.
    move: Hdecq Htagq; rewrite vala_at taga_at => Hdecq Htagq.
    have En1 : n1 = n.
    { have Hb1 : n1 + pc0 < 2 ^ word_size mt by have := alloc_label_lt_word; move: Hn1 Hbound; lia.
      have Hb2 : n + pc0 < 2 ^ word_size mt by have := alloc_label_lt_word; move: Hn Hbound; lia.
      by have := word_of_nat_inj Hb1 Hb2 (etrans (esym Hvq1) Hvq); lia. }
    rewrite En1 in Hnth Hdecq.
    have [[iv2 tv2] [Henc2' [Htag2' Hdec2']]] :=
      code_cell_padc word_of_nat_inj Hcount Hbound Hbound' Hn Hnth.
    move: Hdec2' Htag2'; rewrite vala_at taga_at => Hdec2' Htag2'.
    have Hv2eq : v2 = word_of_nat (shift_pos sizes n + pc0).
    { rewrite Hpcv0 Hvq. exact: (phia_addr_code Hcount Hbound Hbound' Hn). }
    have [Hi2 Htag2eq] : i2 = iv2 /\ tag2 = tv2.
    { have H := Henc2; rewrite Hv2eq Henc2' in H; by move: H => [= -> ->]. }
    have Hm1v1 : m1 v1 = Some (i1' @ tag1') by apply: (Hc1rev _ _ Henc1).
    rewrite Hm1v1; split.
    + rewrite Hdecq; congr Some; apply: imt_halt_indep.
      have Hh := Hdec2'; rewrite -Hi2 Hdec2 in Hh; move: Hh => [= Hh]; exact: (esym Hh).
    + by rewrite Htagq -Htag2' -Htag2eq.
Qed.

Local Notation padl := ((pad_align q q').1).

Lemma Rf_init :
  Rf (Merged.initial_state (code q) (prog_buffers q) (prog_interface q))
     (Merged.initial_state (code padl) (prog_buffers padl) (prog_interface padl)).
Proof.
  rewrite /Rf; split; first exact: match_pad_init.
  split; first exact: pad_valid_init.
  by split; [exact: cptr_code_init | exact: pc_safe_init].
Qed.

Lemma pad_pc_cell_bwd_aux (s1 s2 : st) (i2 : mword mt) (ti2 : mem_tag) :
  match_pad s1 s2 -> pc_safe s1 ->
  Symbolic.mem s2 (vala (Symbolic.pc s2)) = Some (i2 @ ti2) -> is_code ti2 ->
  exists n im tm i1 ti1,
    n < size (code q) /\
    vala (Symbolic.pc s1) = word_of_nat (n + pc0) /\
    vala (Symbolic.pc s2) = word_of_nat (shift_pos sizes n + pc0) /\
    nth_error (code q) n = Some (im, tm) /\
    encode_code (code q) pc0 (vala (Symbolic.pc s1)) = Some (i1 @ ti1) /\
    encode_code padc pc0 (vala (Symbolic.pc s2)) = Some (i2 @ ti2) /\
    Symbolic.mem s1 (vala (Symbolic.pc s1)) = Some (i1 @ ti1) /\
    ti1 = tm /\ ti2 = tm.
Proof.
  move=> Hmp Hps Hm2 Hcode2.
  have [Hpcv0 [_ [_ [_ [_ [Hc1rev [Hc2iso _]]]]]]] := Hmp.
  have Henc2 : encode_code padc pc0 (vala (Symbolic.pc s2)) = Some (i2 @ ti2)
    by apply: (Hc2iso _ _ Hm2 Hcode2).
  have [k [Hv2k Hk]] := encode_code_nth_inv Henc2.
  have Hval2 : (val (vala (Symbolic.pc s2)) : nat) = k + pc0.
  { rewrite Hv2k val_word_of_nat //. have := alloc_label_lt_word; move: Hk Hbound'; lia. }
  have [n [Hn Hvq]] : exists n, n < size (code q) /\ vala (Symbolic.pc s1) = word_of_nat (n + pc0).
  { case: Hps => Hpcsafe.
    - case: (ltnP (val (vala (Symbolic.pc s1))) pc0) => Hlo.
      + exfalso.
        have Hv2v1 : (val (vala (Symbolic.pc s2)) : nat) = val (vala (Symbolic.pc s1)).
        { rewrite Hpcv0 /phia valw_won (phia_nat_id_lo q' Hlo) modn_small;
            [ by [] | have := alloc_label_lt_word; move: Hlo Hbound; lia ]. }
        move: Hval2 Hv2v1 Hlo; lia.
      + exists (val (vala (Symbolic.pc s1)) - pc0); split; first by move: Hpcsafe Hlo; lia.
        by rewrite (subnK Hlo); symmetry; exact: valwK.
    - exfalso.
      have Hge : pc0 + size (code q) <= val (vala (Symbolic.pc s1))
        by have := size_code_le_padc; move: Hpcsafe; lia.
      have Hv2v1 : (val (vala (Symbolic.pc s2)) : nat) = val (vala (Symbolic.pc s1)).
      { rewrite Hpcv0 /phia valw_won (phia_nat_id_hi Hcount Hbound Hbound' Hge) modn_small;
          [ by [] | exact: ltn_ord ]. }
      move: Hval2 Hv2v1 Hpcsafe Hk; lia. }
  have [[i1 ti1] Henc1] := encode_code_dom word_of_nat_inj
                            (ltn_trans Hbound alloc_label_lt_word) Hn.
  rewrite -Hvq in Henc1.
  have [n1 [im [tm [Hn1 [Hvq1 [Hnth [Htagq Hdecq]]]]]]] := code_cell_q Hcount Hbound Hbound' Henc1.
  move: Hdecq Htagq; rewrite vala_at taga_at => Hdecq Htagq.
  have En1 : n1 = n.
  { have Hb1 : n1 + pc0 < 2 ^ word_size mt by have := alloc_label_lt_word; move: Hn1 Hbound; lia.
    have Hb2 : n + pc0 < 2 ^ word_size mt by have := alloc_label_lt_word; move: Hn Hbound; lia.
    by have := word_of_nat_inj Hb1 Hb2 (etrans (esym Hvq1) Hvq); lia. }
  rewrite En1 in Hnth Hdecq.
  have [[iv2 tv2] [Henc2' [Htag2' Hdec2']]] :=
    code_cell_padc word_of_nat_inj Hcount Hbound Hbound' Hn Hnth.
  move: Hdec2' Htag2'; rewrite vala_at taga_at => Hdec2' Htag2'.
  have Hv2eq : vala (Symbolic.pc s2) = word_of_nat (shift_pos sizes n + pc0).
  { rewrite Hpcv0 Hvq. exact: (phia_addr_code Hcount Hbound Hbound' Hn). }
  have [Hi2 Htag2eq] : i2 = iv2 /\ ti2 = tv2.
  { have H := Henc2; rewrite Hv2eq Henc2' in H; by move: H => [= -> ->]. }
  have Hm1v1 : Symbolic.mem s1 (vala (Symbolic.pc s1)) = Some (i1 @ ti1)
    by apply: (Hc1rev _ _ Henc1).
  exists n, im, tm, i1, ti1.
  split; first exact: Hn.
  split; first exact: Hvq.
  split; first exact: Hv2eq.
  split; first exact: Hnth.
  split; first exact: Henc1.
  split; first exact: Henc2.
  split; first exact: Hm1v1.
  split; first exact: Htagq.
  by rewrite Htag2eq.
Qed.

Lemma pad_pc_cell_bwd (s1 s2 : st) (i2 : mword mt) (ti2 : mem_tag) :
  match_pad s1 s2 -> pc_safe s1 ->
  Symbolic.mem s2 (vala (Symbolic.pc s2)) = Some (i2 @ ti2) -> is_code ti2 ->
  exists n im tm i1 ti1,
    n < size (code q) /\
    vala (Symbolic.pc s1) = word_of_nat (n + pc0) /\
    nth_error (code q) n = Some (im, tm) /\
    Symbolic.mem s1 (vala (Symbolic.pc s1)) = Some (i1 @ ti1) /\
    ti1 = tm /\ ti2 = tm /\
    exists lp1 lp2 pos1 pos2,
      decode_instr i1 = Some (instr_merged_to_mp im lp1 pos1) /\
      decode_instr i2 = Some (instr_merged_to_mp im lp2 pos2).
Proof.
  move=> Hmp Hps Hm2 Hcode2.
  have [Hpcv0 [_ [_ [_ [_ [Hc1rev [Hc2iso _]]]]]]] := Hmp.
  have Henc2 : encode_code padc pc0 (vala (Symbolic.pc s2)) = Some (i2 @ ti2)
    by apply: (Hc2iso _ _ Hm2 Hcode2).
  have [k [Hv2k Hk]] := encode_code_nth_inv Henc2.
  have Hval2 : (val (vala (Symbolic.pc s2)) : nat) = k + pc0.
  { rewrite Hv2k val_word_of_nat //. have := alloc_label_lt_word; move: Hk Hbound'; lia. }
  have [n [Hn Hvq]] : exists n, n < size (code q) /\ vala (Symbolic.pc s1) = word_of_nat (n + pc0).
  { case: Hps => Hpcsafe.
    - case: (ltnP (val (vala (Symbolic.pc s1))) pc0) => Hlo.
      + exfalso.
        have Hv2v1 : (val (vala (Symbolic.pc s2)) : nat) = val (vala (Symbolic.pc s1)).
        { rewrite Hpcv0 /phia valw_won (phia_nat_id_lo q' Hlo) modn_small;
            [ by [] | have := alloc_label_lt_word; move: Hlo Hbound; lia ]. }
        move: Hval2 Hv2v1 Hlo; lia.
      + exists (val (vala (Symbolic.pc s1)) - pc0); split; first by move: Hpcsafe Hlo; lia.
        by rewrite (subnK Hlo); symmetry; exact: valwK.
    - exfalso.
      have Hge : pc0 + size (code q) <= val (vala (Symbolic.pc s1))
        by have := size_code_le_padc; move: Hpcsafe; lia.
      have Hv2v1 : (val (vala (Symbolic.pc s2)) : nat) = val (vala (Symbolic.pc s1)).
      { rewrite Hpcv0 /phia valw_won (phia_nat_id_hi Hcount Hbound Hbound' Hge) modn_small;
          [ by [] | exact: ltn_ord ]. }
      move: Hval2 Hv2v1 Hpcsafe Hk; lia. }
  have [[i1 ti1] Henc1] := encode_code_dom word_of_nat_inj
                            (ltn_trans Hbound alloc_label_lt_word) Hn.
  rewrite -Hvq in Henc1.
  have [n1 [im [tm [Hn1 [Hvq1 [Hnth [Htagq Hdecq]]]]]]] := code_cell_q Hcount Hbound Hbound' Henc1.
  move: Hdecq Htagq; rewrite vala_at taga_at => Hdecq Htagq.
  have En1 : n1 = n.
  { have Hb1 : n1 + pc0 < 2 ^ word_size mt by have := alloc_label_lt_word; move: Hn1 Hbound; lia.
    have Hb2 : n + pc0 < 2 ^ word_size mt by have := alloc_label_lt_word; move: Hn Hbound; lia.
    by have := word_of_nat_inj Hb1 Hb2 (etrans (esym Hvq1) Hvq); lia. }
  rewrite En1 in Hnth Hdecq.
  have [[iv2 tv2] [Henc2' [Htag2' Hdec2']]] :=
    code_cell_padc word_of_nat_inj Hcount Hbound Hbound' Hn Hnth.
  move: Hdec2' Htag2'; rewrite vala_at taga_at => Hdec2' Htag2'.
  have Hv2eq : vala (Symbolic.pc s2) = word_of_nat (shift_pos sizes n + pc0).
  { rewrite Hpcv0 Hvq. exact: (phia_addr_code Hcount Hbound Hbound' Hn). }
  have [Hi2 Htag2eq] : i2 = iv2 /\ ti2 = tv2.
  { have H := Henc2; rewrite Hv2eq Henc2' in H; by move: H => [= -> ->]. }
  have Hm1v1 : Symbolic.mem s1 (vala (Symbolic.pc s1)) = Some (i1 @ ti1)
    by apply: (Hc1rev _ _ Henc1).
  exists n, im, tm, i1, ti1.
  split; first exact: Hn.
  split; first exact: Hvq.
  split; first exact: Hnth.
  split; first exact: Hm1v1.
  split; first exact: Htagq.
  split; first by rewrite Htag2eq.
  do 4 eexists; split; [exact: Hdecq | rewrite Hi2; exact: Hdec2'].
Qed.

Lemma reg_reflect_bwd (s1 s2 : st) (r : reg mt) (w2 : mword mt) (t : tag_type lrc_tags R) :
  match_pad s1 s2 -> Symbolic.regs s2 r = Some (w2 @ t) ->
  exists w1, Symbolic.regs s1 r = Some (w1 @ t).
Proof.
  move=> Hmp Hr2.
  have [_ [_ [_ [Hreg _]]]] := Hmp.
  move: (Hreg r); case Hr1: (Symbolic.regs s1 r) => [a|] /=; last by rewrite Hr2.
  move=> [v2 [Hr2' _]].
  have Ht : taga a = t by move: Hr2'; rewrite Hr2 => [= _ ->].
  by exists (vala a); rewrite -Ht; congr Some; exact: (esym (atom_etaE a)).
Qed.

Lemma reg_reflect_bwd_other (s1 s2 : st) (r : reg mt) (w : mword mt) :
  match_pad s1 s2 -> Symbolic.regs s2 r = Some (w @ Other) ->
  Symbolic.regs s1 r = Some (w @ Other).
Proof.
  move=> Hmp Hr2.
  have [_ [_ [_ [Hreg _]]]] := Hmp.
  move: (Hreg r); case Hr1: (Symbolic.regs s1 r) => [a|] /=; last by rewrite Hr2.
  move=> [v2 [Hr2' Hrel]].
  have Hta : taga a = Other by move: Hr2'; rewrite Hr2 => [= _ ->].
  have Hv2 : v2 = w by move: Hr2'; rewrite Hr2 => [= -> _].
  have Hvw : vala a = w.
  { have Hni : taga a <> Invalidated by rewrite Hta.
    by rewrite -Hv2 (Hrel Hni) Hta rel_v_Other. }
  congr Some.
  by rewrite -(atom_etaE a) Hta Hvw.
Qed.

Lemma reg_reflect_bwd_cptr (s1 s2 : st) (r : reg mt) (w : mword mt) (t : value_tag) :
  match_pad s1 s2 -> Symbolic.regs s2 r = Some (w @ t) -> is_address t -> t <> Invalidated ->
  exists w', Symbolic.regs s1 r = Some (w' @ t) /\ w = phia q q' w'.
Proof.
  move=> Hmp Hr2 Haddr Hninv.
  have [_ [_ [_ [Hreg _]]]] := Hmp.
  move: (Hreg r); case Hr1: (Symbolic.regs s1 r) => [a|] /=; last by rewrite Hr2.
  move=> [v2 [Hr2' Hrel]].
  have Hta : taga a = t by move: Hr2'; rewrite Hr2 => [= _ ->].
  have Hv2 : v2 = w by move: Hr2'; rewrite Hr2 => [= -> _].
  have Hni : taga a <> Invalidated by rewrite Hta.
  have Hwv : w = phia q q' (vala a).
  { by rewrite -Hv2 (Hrel Hni) Hta /rel_v Haddr. }
  exists (vala a); split; last exact: Hwv.
  congr Some. by rewrite -(atom_etaE a) Hta.
Qed.

Lemma jump_belong_corr_bwd (s1 s2 : st) (w : mword mt) (c : Component.id) :
  match_pad s1 s2 ->
  belong c (match Symbolic.mem s2 (phia q q' w) with Some ni => Some (taga ni) | None => None end) ->
  belong c (match Symbolic.mem s1 w with Some ni => Some (taga ni) | None => None end).
Proof.
  move=> Hmp Hb.
  have [_ [_ [_ [_ [Hc1 [Hc1' [_ [Hc2' [Hnc1 _]]]]]]]]] := Hmp.
  case Hmw: (Symbolic.mem s1 w) => [celltgt|]; last by [].
  have [celltgt2 [Hm2 Ht2]] :=
    jump_target_corr word_of_nat_inj Hcount Hbound Hbound' code_tags_wf_q Hc1 Hc1' Hc2' Hnc1 Hmw.
  move: Hb; rewrite Hm2 !belong_someE Ht2. by [].
Qed.

Lemma jump_target_corr_bwd (s1 s2 : st) (w : mword mt) (celltgt2 : matom) :
  match_pad s1 s2 -> addr_ok (Symbolic.mem s1) w -> Symbolic.mem s2 (phia q q' w) = Some celltgt2 ->
  exists celltgt1, Symbolic.mem s1 w = Some celltgt1 /\ taga celltgt1 = taga celltgt2.
Proof.
  move=> Hmp Hok Hm2.
  have [_ [_ [_ [_ [Hc1 [Hc1' [Hc2 [Hc2' [Hnc1 Hnc2]]]]]]]]] := Hmp.
  case Hmw: (Symbolic.mem s1 w) => [celltgt1|].
  - have [celltgt2' [Hm2' Ht2]] :=
      jump_target_corr word_of_nat_inj Hcount Hbound Hbound' code_tags_wf_q Hc1 Hc1' Hc2' Hnc1 Hmw.
    exists celltgt1; split; first by []. move: Hm2; rewrite Hm2' => [= <-]; by rewrite Ht2.
  - exfalso.
    have Hout : pc0 + size padc <= val w \/ (val w : nat) < pc0.
    { case: Hok => [[c0 Hc0]|H]; [by rewrite Hmw in Hc0 | exact: H]. }
    have Hpid : phia q q' w = w.
    { rewrite /phia; case: (ltnP (val w) pc0) => Hlo.
      - by rewrite (phia_nat_id_lo q' Hlo); exact: valwK.
      - have Hge : pc0 + size (code q) <= val w
          by case: Hout => H; [ have := size_code_le_padc; lia | move: Hlo H; lia ].
        rewrite (phia_nat_id_hi Hcount Hbound Hbound' Hge); exact: valwK. }
    move: Hm2; rewrite Hpid => Hm2.
    case Hcc: (is_code (taga celltgt2)).
    + have Henc := Hc2 _ _ Hm2 Hcc.
      have Hbw' : pc0 + size padc < 2 ^ word_size mt by exact: (ltn_trans Hbound' alloc_label_lt_word).
      have [k [Hwk [Hklt _]]] := encode_code_nth_inv Henc.
      have Hb2 : k + pc0 < 2 ^ word_size mt by move: Hklt Hbw'; lia.
      have Hval : (val w : nat) = k + pc0 by rewrite Hwk (val_word_of_nat Hb2).
      move: Hout; rewrite Hval; lia.
    + have [a0 [Ha0 _]] := Hnc2 _ _ Hm2 Hcc. by rewrite Ha0 in Hmw.
Qed.

Lemma mem_reflect_bwd (s1 s2 : st) (w : mword mt) (v2 : mword mt) (t : mem_tag) :
  match_pad s1 s2 -> Symbolic.mem s2 w = Some (v2 @ t) -> is_code t = false ->
  exists v1, Symbolic.mem s1 w = Some (v1 @ t).
Proof.
  move=> Hmp Hm2 Hnc.
  have [_ [_ [_ [_ [_ [_ [_ [_ [_ Hmwkb]]]]]]]]] := Hmp.
  have [a0 [Ha0 [Hta _]]] := Hmwkb _ _ Hm2 Hnc.
  have Ht : t = taga a0 by move: Hta; rewrite taga_at.
  exists (vala a0); rewrite Ha0; congr Some.
  by rewrite Ht; exact: (esym (atom_etaE a0)).
Qed.

Lemma pad_evi_reflect (s1 s2 : st) :
  match_pad s1 s2 -> (exists a2, Symbolic.regs s2 rcom = Some a2) ->
  exists ei, Symbolic.evi s1 = Some ei.
Proof.
  move=> Hmp [a2 Hr2].
  have Hr2' : Symbolic.regs s2 rcom = Some ((vala a2) @ (taga a2)) by rewrite Hr2 atom_etaE.
  have [w1 Hr1] := reg_reflect_bwd Hmp Hr2'.
  by rewrite /Symbolic.evi Hr1 /=; eexists.
Qed.

Lemma merged_silent_transfer_belong :
  forall (op : opcode) tpc ti (ts : hseq (tag_type lrc_tags) (inputs op)) tni e
         (ov : ovec lrc_tags op),
    Merged.transfer (IVec (OP op) tpc ti ts tni) e = Some (ov, None) ->
    belong (match tpc with Level _ c => c end) tni.
Proof.
  move=> op; destruct op; move=> tpc ti ts tni e ov;
    rewrite /Merged.transfer /Merged.instr_rules => Htr;
    case: (obind_inv Htr) => out [Hir Hfin]; clear Htr;
    case: out Hir Hfin => ov0 ev0 Hir [= _ Hev]; subst ev0;
    case: (obind_inv Hir) => u0 [_ {}Hir];
    case: (obind_inv Hir) => u1 [_ {}Hir];
    case: (obind_inv Hir) => lout [Hlrc Hfin2]; clear Hir;
    case: lout Hlrc Hfin2 => [[ltrpc ltr] lev] Hlrc Hfin2; move: Hfin2 => [= _ Hlev]; subst lev;
    move: Hlrc; rewrite /LRC.instr_rules; case: tpc => [level current']; cbv zeta => Hlrc;
    case: (obind_inv Hlrc) => u [Hg Hrest]; clear Hlrc; move: Hg;
    case Heq: (_ == current') => // _; move/eqP: Heq => <-;
    set cur := (match ti with {| color := c |} => c end) in Hrest *;
    have cbE : (forall u', check_belong cur tni = Some u' -> belong cur tni)
      by (move=> u'; rewrite /check_belong; case: (belong cur tni));
    cbn -[check_belong belong is_other is_jump get_tni_color check_ret] in Hrest.
  all: try by [].
  - rewrite (hseq0 ts) /= in Hrest.
    by case: (obind_inv Hrest) => u' [Hcb _]; exact: (cbE _ Hcb).
  - case: ts Hrest => t0 ts Hrest; rewrite (hseq0 ts) /= in Hrest.
    by case: (obind_inv Hrest) => u' [Hcb _]; exact: (cbE _ Hcb).
  - case: ts Hrest => t0 [t1 ts] Hrest; rewrite (hseq0 ts) /= in Hrest.
    by case: (obind_inv Hrest) => u' [Hcb _]; exact: (cbE _ Hcb).
  - case: ts Hrest => t0 [t1 [t2 ts]] Hrest; rewrite (hseq0 ts) /= in Hrest.
    case: (obind_inv Hrest) => ? [_ {}Hrest]; case: (obind_inv Hrest) => ? [_ {}Hrest].
    by case: (obind_inv Hrest) => u' [Hcb _]; exact: (cbE _ Hcb).
  - case: ts Hrest => t0 [t1 [t2 ts]] Hrest; rewrite (hseq0 ts) /= in Hrest.
    case: (obind_inv Hrest) => ? [_ {}Hrest].
    by case: (obind_inv Hrest) => u' [Hcb _]; exact: (cbE _ Hcb).
  - case: ts Hrest => t0 [t1 [t2 ts]] Hrest; rewrite (hseq0 ts) /= in Hrest.
    case: (obind_inv Hrest) => ? [_ {}Hrest].
    by case: (obind_inv Hrest) => u' [Hcb _]; exact: (cbE _ Hcb).
  - case: ts Hrest => tra [tp [trcom next]] Hrest.
    move: Hrest; case Hb: (belong cur tni) => Hrest; first by [].
    exfalso; case: (obind_inv Hrest) => ? [_ {}Hrest]; case: (obind_inv Hrest) => ? [_ {}Hrest].
    case: (obind_inv Hrest) => ? [_ {}Hrest]; by move: Hrest => [= _].
  - case: ts Hrest => t0 ts Hrest; rewrite (hseq0 ts) /= in Hrest.
    case: (obind_inv Hrest) => ? [_ {}Hrest].
    by case: (obind_inv Hrest) => u' [Hcb _]; exact: (cbE _ Hcb).
  - case: ts Hrest => tnext [tra [trcom next]] Hrest.
    case: (obind_inv Hrest) => ? [_ {}Hrest].
    move: Hrest; case Hb: (belong cur tni) => Hrest; first by [].
    exfalso; case: (obind_inv Hrest) => ? [_ {}Hrest].
    case: (obind_inv Hrest) => c' [Htc {}Hrest]; case: (obind_inv Hrest) => ? [Hce {}Hrest].
    move: Hrest => [= _ Hev]; move: Htc Hce Hev; clear cbE Hb.
    rewrite /get_tni_color /check_entry /get_proc_name.
    case: tni => [t|] //; case: t => vt ct et bt; by case: et => [[p l]|].
Qed.

Lemma merged_silent_next_pc_belong :
  forall (s s' : st) op tpc ti (ts : hseq (tag_type lrc_tags) (inputs op)) updts pc',
    @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s
      (IVec (OP op) tpc ti ts) updts pc' = Some (s', None) ->
    belong (match tpc with Level _ c => c end)
           (match Symbolic.mem s pc' with Some ni => Some (taga ni) | None => None end).
Proof.
  move=> s s' op tpc ti ts updts pc'.
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state.
  case Hevi: (Symbolic.evi s) => [evinp|] //=.
  case Hm: (Symbolic.mem s pc') => [ni|] /= Hgoal;
    ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
      case: ov_ev Htr Hk => ov ev Htr Hk;
      case: (obind_inv Hk) => st0 [_ Hfin];
      move: Hfin => [= _ Hev]; subst ev;
      exact: (merged_silent_transfer_belong Htr) ).
Qed.

Lemma pad_succ_cell_eq_tag (s1 s2 : st) (n : nat) (i : Merged.instr) (t : mem_tag) :
  match_pad s1 s2 -> vala (Symbolic.pc s1) = word_of_nat (n + pc0) ->
  n.+1 < size (code q) -> nth_error (code q) n = Some (i, t) -> PaddingSim.is_term i = false ->
  exists v1 v2 tnext,
    Symbolic.mem s1 (vala (Symbolic.pc s1) + 1)%w = Some (v1 @ tnext) /\
    Symbolic.mem s2 (vala (Symbolic.pc s2) + 1)%w = Some (v2 @ tnext).
Proof.
  move=> Hmp Hpc1 Hn1 Hnth Hterm.
  have [Hpcv0 [_ [_ [_ [_ [Hc1rev [_ [Hc2rev _]]]]]]]] := Hmp.
  have Hn : n < size (code q) by apply: ltnW.
  have [[v1 t1] Henc1] := encode_code_dom word_of_nat_inj
                            (ltn_trans Hbound alloc_label_lt_word) Hn1.
  have [m [im' [tm' [Hm [Hmeq [Hnth' [Htag' _]]]]]]] := code_cell_q Hcount Hbound Hbound' Henc1.
  have Em : m = n.+1.
  { have Hb1 : n.+1 + pc0 < 2 ^ word_size mt by have := alloc_label_lt_word; move: Hn1 Hbound; lia.
    have Hb2 : m + pc0 < 2 ^ word_size mt by have := alloc_label_lt_word; move: Hm Hbound; lia.
    by have := word_of_nat_inj Hb1 Hb2 Hmeq; lia. }
  rewrite Em in Hnth' Htag'.
  move: Htag'; rewrite taga_at => Htag'.
  have [v2cell [Henc2 [Htag2 _]]] := code_cell_padc word_of_nat_inj Hcount Hbound Hbound' Hn1 Hnth'.
  have Hpc1' : (vala (Symbolic.pc s1) + 1)%w = word_of_nat (n.+1 + pc0)
    by rewrite Hpc1 word_of_nat_succ; congr word_of_nat; lia.
  have Hpc2' : (vala (Symbolic.pc s2) + 1)%w = word_of_nat (shift_pos sizes n.+1 + pc0).
  { rewrite Hpcv0 Hpc1 (phia_addr_code Hcount Hbound Hbound' Hn) word_of_nat_succ.
    congr word_of_nat. rewrite (fallthrough_aligned Hn1 Hnth Hterm). lia. }
  exists v1, (vala v2cell), t1; split.
  - rewrite Hpc1'; exact: (Hc1rev _ _ Henc1).
  - rewrite Hpc2' (Hc2rev _ _ Henc2); congr Some.
    have Ht1 : t1 = taga v2cell by rewrite Htag' Htag2.
    by rewrite Ht1; exact: (esym (atom_etaE v2cell)).
Qed.

Lemma merged_transfer_current_eq (op : opcode) tpc ti
      (ts : hseq (tag_type lrc_tags) (inputs op)) tni e (ov : ovec lrc_tags op) ev :
  Merged.transfer (IVec (OP op) tpc ti ts tni) e = Some (ov, ev) ->
  color ti = match tpc with Level _ c => c end.
Proof.
  rewrite /Merged.transfer /Merged.instr_rules => Htr;
    case: (obind_inv Htr) => out [Hir _]; clear Htr;
    case: (obind_inv Hir) => u0 [_ {}Hir];
    case: (obind_inv Hir) => u1 [_ {}Hir];
    case: (obind_inv Hir) => lout [Hlrc _]; clear Hir;
    move: Hlrc; rewrite /LRC.instr_rules; case: tpc => [level current']; cbv zeta => Hlrc;
    case: (obind_inv Hlrc) => u [Hg _]; move: Hg.
  by case Heq: (_ == current') => // _; apply/eqP; exact: Heq.
Qed.

Lemma imt_nop_indep (i : Merged.instr) (lp1 lp2 : nat -> nat -> nat) (pos1 pos2 : nat) :
  instr_merged_to_mp i lp1 pos1 = Nop mt -> instr_merged_to_mp i lp2 pos2 = Nop mt.
Proof. by case: i. Qed.

Lemma merged_nop_silent tpc ti tni e (ov : ovec lrc_tags NOP) ev :
  Merged.transfer (IVec NOP tpc ti [hseq] tni) e = Some (ov, ev) -> ev = None.
Proof.
  rewrite /Merged.transfer /Merged.instr_rules => Htr.
  case: (obind_inv Htr) => out [Hir Hfin]; clear Htr.
  case: out Hir Hfin => ov0 ev0 Hir [= _ Hev].
  case: (obind_inv Hir) => u0 [_ {}Hir].
  case: (obind_inv Hir) => u1 [_ {}Hir].
  case: (obind_inv Hir) => lout [Hlrc Hfin2]; clear Hir.
  case: lout Hlrc Hfin2 => [[ltrpc ltr] lev] Hlrc Hfin2.
  move: Hlrc; rewrite /LRC.instr_rules; case: tpc => [level current']; cbv zeta.
  case: (_ == current') => //=.
  case: (check_belong _ _) => //= u'.
  move=> [= _ Hlev].
  by move: Hfin2 => [= _ Hlev2]; congruence.
Qed.

Lemma imt_nop_nonterm (i : Merged.instr) (lp : nat -> nat -> nat) (pos : nat) :
  instr_merged_to_mp i lp pos = Nop mt -> PaddingSim.is_term i = false.
Proof. by case: i. Qed.

Lemma merged_nop_nsu_silent (s : st) tpc ti pc' s' ev :
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s
    (IVec NOP tpc ti [hseq]) [::] pc' = Some (s', ev) -> ev = None.
Proof.
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state.
  case: (Symbolic.evi s) => [evinp|] //=.
  case Hm: (Symbolic.mem s pc') => [ni|] /= Hgoal;
    ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
      case: ov_ev Htr Hk => ov ev' Htr Hk;
      have Hev' := merged_nop_silent Htr;
      by move: Hk => [= _ Hf]; congruence ).
Qed.

Lemma merged_nsu_current_eq (s s' : st) op tpc ti
      (ts : hseq (tag_type lrc_tags) (inputs op)) updts pc' ev :
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s
    (IVec (OP op) tpc ti ts) updts pc' = Some (s', ev) ->
  color ti = match tpc with Level _ c => c end.
Proof.
  rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state.
  case: (Symbolic.evi s) => [evinp|] //=.
  case Hm: (Symbolic.mem s pc') => [ni|] /= Hgoal;
    ( case: (obind_inv Hgoal) => ov_ev [Htr Hk];
      case: ov_ev Htr Hk => ov ev0 Htr Hk;
      case: (obind_inv Hk) => st0 [_ _];
      exact: (merged_transfer_current_eq Htr) ).
Qed.

Lemma pad_nostep_nop (s1 s2 : st)
  (mem2 : {fmap mword mt -> matom}) (reg2 : {fmap reg mt -> ratom})
  (pc2 : mword mt) (tpc2 : tag_type lrc_tags P) (i2 : mword mt) (ti2 : mem_tag)
  (extra2 : unit) (s2' : st) (ev : option event) :
  match_pad s1 s2 -> pc_safe s1 ->
  s2 = @Symbolic.State mt lrc_tags unit mem2 reg2 (pc2 @ tpc2) extra2 ->
  mem2 pc2 = Some (i2 @ ti2) -> decode_instr i2 = Some (Nop mt) ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit s2
    (IVec NOP tpc2 ti2 [hseq]) [::] = Some (s2', ev) ->
  exists s1' ev', step_me (NC := NC) s1 s1' ev'.
Proof.
  move=> Hmp Hps Hs2 Hpc2cell Hdec2 NEXT2.
  have Hm2 : Symbolic.mem s2 (vala (Symbolic.pc s2)) = Some (i2 @ ti2) by rewrite Hs2.
  have Hic2 : is_code ti2 by apply: (nsuap_is_code NEXT2).
  have [n [im [tm [i1 [ti1 [Hn [Hpc1 [Hnth [Hm1 [Hti1 [Hti2 [lp1 [lp2 [pos1 [pos2 [Hdq1 Hdq2]]]]]]]]]]]]]]]] :=
    pad_pc_cell_bwd Hmp Hps Hm2 Hic2.
  have Hnop2 : instr_merged_to_mp im lp2 pos2 = Nop mt.
  { have H := Hdec2; rewrite Hdq2 in H; by move: H => [= ->]. }
  have Hdec1 : decode_instr i1 = Some (Nop mt).
  { rewrite Hdq1; congr Some; apply: imt_nop_indep; exact: Hnop2. }
  have Hterm : PaddingSim.is_term im = false by apply: (imt_nop_nonterm Hnop2).
  have Hn1 : n.+1 < size (code q) by apply: (nonterm_succ_lt code_last_term Hn Hnth Hterm).
  have Hev0 : ev = None by apply: (merged_nop_nsu_silent NEXT2).
  rewrite Hev0 in NEXT2.
  have Hcur2 := merged_nsu_current_eq NEXT2.
  have Hbel2 := merged_silent_next_pc_belong NEXT2.
  have [v1n [v2n [tnext [Hm1n Hm2n]]]] := pad_succ_cell_eq_tag Hmp Hpc1 Hn1 Hnth Hterm.
  have [_ [Hpct _]] := Hmp.
  have Hic1 : is_code ti1 by rewrite Hti1 -Hti2.
  have Htpc2eq : tpc2 = taga (Symbolic.pc s1) by rewrite -Hpct Hs2.
  have Hcc1 : color ti1 = match taga (Symbolic.pc s1) with Level _ c => c end.
  { by rewrite Hti1 -Hti2 Hcur2 Htpc2eq. }
  have Hctn : color tnext = match taga (Symbolic.pc s1) with Level _ c => c end.
  { move: Hbel2; rewrite Hm2n.
    change (match Some (v2n @ tnext) with Some ni => Some (taga ni) | None => None end)
      with (Some tnext).
    rewrite PaddingSim.belong_someE => /eqP H. by rewrite -H Htpc2eq. }
  exists (@Symbolic.State mt lrc_tags unit (Symbolic.mem s1) (Symbolic.regs s1)
            ((vala (Symbolic.pc s1) + 1)%w @ (Symbolic.pct s1)) (Symbolic.internal s1)), None.
  have [a2 Hrcom2] : exists a2, Symbolic.regs s2 rcom = Some a2.
  { move: NEXT2; rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc
                        /Symbolic.next_state /Symbolic.evi.
    case: (Symbolic.regs s2 rcom) => [a2|] /=; [by move=> _; exists a2 | by []]. }
  have [ei Hevi] := pad_evi_reflect Hmp (ex_intro _ a2 Hrcom2).
  eapply step_nop.
  - exact: (Symbolic.state_eta s1).
  - exact: Hm1.
  - exact: Hdec1.
  - have Hcur1 : color ti1 == match taga (Symbolic.pc s1) with Level _ c => c end.
    { apply/eqP; exact: Hcc1. }
    have Hbel1 : color ti1 == color (taga (v1n @ tnext)).
    { apply/eqP. have -> : taga (v1n @ tnext) = tnext by []. by rewrite Hcc1 Hctn. }
    exact: (merged_nop_intro Hic1 Hm1n Hcur1 Hbel1 Hevi).
Qed.

Lemma imt_const_nonterm (i : Merged.instr) (lp : nat -> nat -> nat) (pos : nat) n r :
  instr_merged_to_mp i lp pos = Const n r -> PaddingSim.is_term i = false.
Proof. by case: i => //= *; congruence. Qed.

Lemma pad_nostep_const (s1 s2 : st)
  (mem2 : {fmap mword mt -> matom}) (reg2 : {fmap reg mt -> ratom})
  (pc2 : mword mt) (tpc2 : tag_type lrc_tags P) (i2 : mword mt) (ti2 : mem_tag)
  (extra2 : unit) (n2 : imm mt) (r2 : reg mt) (old2 : mword mt) (told2 : value_tag)
  (s2' : st) (ev : option event) :
  match_pad s1 s2 -> pc_safe s1 ->
  s2 = @Symbolic.State mt lrc_tags unit mem2 reg2 (pc2 @ tpc2) extra2 ->
  mem2 pc2 = Some (i2 @ ti2) -> decode_instr i2 = Some (Const n2 r2) ->
  reg2 r2 = Some (old2 @ told2) ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit s2
    (IVec CONST tpc2 ti2 [hseq told2]) [:: RegWrite r2 (swcast n2)] = Some (s2', ev) ->
  exists s1' ev', step_me (NC := NC) s1 s1' ev'.
Proof.
  move=> Hmp Hps Hs2 Hpc2cell Hdec2 Hold2 NEXT2.
  have Hm2 : Symbolic.mem s2 (vala (Symbolic.pc s2)) = Some (i2 @ ti2) by rewrite Hs2.
  have Hic2 : is_code ti2 by apply: (nsuap_is_code NEXT2).
  have [n [im [tm [i1 [ti1 [Hn [Hpc1 [Hnth [Hm1 [Hti1 [Hti2 [lp1 [lp2 [pos1 [pos2 [Hdq1 Hdq2]]]]]]]]]]]]]]]] :=
    pad_pc_cell_bwd Hmp Hps Hm2 Hic2.
  have Hconst2 : instr_merged_to_mp im lp2 pos2 = Const n2 r2.
  { have H := Hdec2; rewrite Hdq2 in H; by move: H => [= ->]. }
  have Hdec1 : decode_instr i1 = Some (Const n2 r2).
  { rewrite Hdq1; congr Some; apply: instr_const_indep; exact: Hconst2. }
  have Hterm : PaddingSim.is_term im = false by apply: (imt_const_nonterm Hconst2).
  have Hn1 : n.+1 < size (code q) by apply: (nonterm_succ_lt code_last_term Hn Hnth Hterm).
  have [v1n [v2n [tnext [Hm1n Hm2n]]]] := pad_succ_cell_eq_tag Hmp Hpc1 Hn1 Hnth Hterm.
  have Hm2n' : mem2 (pc2 + 1)%w = Some (v2n @ tnext) by move: Hm2n; rewrite Hs2.
  have NEXT2' : @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
                  (@Symbolic.State mt lrc_tags unit mem2 reg2 (pc2 @ tpc2) extra2)
                  (IVec (OP CONST) tpc2 ti2 [hseq told2]) [:: RegWrite r2 (swcast n2)] = Some (s2', ev)
    by move: NEXT2; rewrite Hs2.
  have [_ [_ [Hcur2 [Hbel2 [ei2 Hevi2]]]]] := merged_const_inv Hic2 Hm2n' Hold2 NEXT2'.
  have [_ [Hpct _]] := Hmp.
  have Hic1 : is_code ti1 by rewrite Hti1 -Hti2.
  have Htpc2eq : tpc2 = taga (Symbolic.pc s1) by rewrite -Hpct Hs2.
  have Hregs2 : Symbolic.regs s2 r2 = Some (old2 @ told2) by rewrite Hs2.
  have [w1 Hreg1] := reg_reflect_bwd Hmp Hregs2.
  have [a2 Hrcom2] : exists a2, Symbolic.regs s2 rcom = Some a2.
  { move: NEXT2; rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc
                        /Symbolic.next_state /Symbolic.evi.
    case: (Symbolic.regs s2 rcom) => [a2|] /=; [by move=> _; exists a2 | by []]. }
  have [ei Hevi] := pad_evi_reflect Hmp (ex_intro _ a2 Hrcom2).
  have Hcur1 : color ti1 == match taga (Symbolic.pc s1) with Level _ c => c end.
  { rewrite Hti1 -Hti2 -Htpc2eq; exact: Hcur2. }
  have Hbel1 : color ti1 == color (taga (v1n @ tnext)).
  { have E1 : taga (v1n @ tnext) = tnext by []. have E2 : taga (v2n @ tnext) = tnext by [].
    rewrite E1 Hti1 -Hti2. by move: Hbel2; rewrite E2. }
  do 2 eexists; eapply step_const.
  - exact: (Symbolic.state_eta s1).
  - exact: Hm1.
  - exact: Hdec1.
  - exact: Hreg1.
  - apply: merged_const_intro;
      [exact: Hic1 | exact: Hm1n | exact: Hreg1 | exact: Hcur1 | exact: Hbel1 | exact: Hevi].
Qed.

Lemma imt_mov_nonterm (i : Merged.instr) (lp : nat -> nat -> nat) (pos : nat) r1 r2 :
  instr_merged_to_mp i lp pos = Mov r1 r2 -> PaddingSim.is_term i = false.
Proof. by case: i => //= *; congruence. Qed.
Lemma imt_binop_nonterm (i : Merged.instr) (lp : nat -> nat -> nat) (pos : nat) op r1 r2 r3 :
  instr_merged_to_mp i lp pos = Binop op r1 r2 r3 -> PaddingSim.is_term i = false.
Proof. by case: i => //= *; congruence. Qed.

Lemma pad_nostep_mov (s1 s2 : st)
  (mem2 : {fmap mword mt -> matom}) (reg2 : {fmap reg mt -> ratom})
  (pc2 : mword mt) (tpc2 : tag_type lrc_tags P) (i2 : mword mt) (ti2 : mem_tag)
  (extra2 : unit) (r1 r2 : reg mt) (w1 : mword mt) (t1 : value_tag)
  (old : mword mt) (told : value_tag) (s2' : st) (ev : option event) :
  match_pad s1 s2 -> pc_safe s1 ->
  s2 = @Symbolic.State mt lrc_tags unit mem2 reg2 (pc2 @ tpc2) extra2 ->
  mem2 pc2 = Some (i2 @ ti2) -> decode_instr i2 = Some (Mov r1 r2) ->
  reg2 r1 = Some (w1 @ t1) -> reg2 r2 = Some (old @ told) ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit s2
    (IVec MOV tpc2 ti2 [hseq t1; told]) [:: RegRead r1; RegWrite r2 w1] = Some (s2', ev) ->
  exists s1' ev', step_me (NC := NC) s1 s1' ev'.
Proof.
  move=> Hmp Hps Hs2 Hpc2cell Hdec2 Hr1 Hr2 NEXT2.
  have Hm2 : Symbolic.mem s2 (vala (Symbolic.pc s2)) = Some (i2 @ ti2) by rewrite Hs2.
  have Hic2 : is_code ti2 by apply: (nsuap_is_code NEXT2).
  have [n [im [tm [i1 [ti1 [Hn [Hpc1 [Hnth [Hm1 [Hti1 [Hti2 [lp1 [lp2 [pos1 [pos2 [Hdq1 Hdq2]]]]]]]]]]]]]]]] :=
    pad_pc_cell_bwd Hmp Hps Hm2 Hic2.
  have Hmov2 : instr_merged_to_mp im lp2 pos2 = Mov r1 r2.
  { have H := Hdec2; rewrite Hdq2 in H; by move: H => [= ->]. }
  have Hdec1 : decode_instr i1 = Some (Mov r1 r2).
  { rewrite Hdq1; congr Some; apply: instr_mov_indep; exact: Hmov2. }
  have Hterm : PaddingSim.is_term im = false by apply: (imt_mov_nonterm Hmov2).
  have Hn1 : n.+1 < size (code q) by apply: (nonterm_succ_lt code_last_term Hn Hnth Hterm).
  have [v1n [v2n [tnext [Hm1n Hm2n]]]] := pad_succ_cell_eq_tag Hmp Hpc1 Hn1 Hnth Hterm.
  have Hm2n' : mem2 (pc2 + 1)%w = Some (v2n @ tnext) by move: Hm2n; rewrite Hs2.
  have NEXT2' : @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
                  (@Symbolic.State mt lrc_tags unit mem2 reg2 (pc2 @ tpc2) extra2)
                  (IVec (OP MOV) tpc2 ti2 [hseq t1; told]) [:: RegRead r1; RegWrite r2 w1] = Some (s2', ev)
    by move: NEXT2; rewrite Hs2.
  have [_ [_ [Hcur2 [Hbel2 [ei2 Hevi2]]]]] := merged_mov_inv Hic2 Hm2n' Hr1 Hr2 NEXT2'.
  have [_ [Hpct _]] := Hmp.
  have Hic1 : is_code ti1 by rewrite Hti1 -Hti2.
  have Htpc2eq : tpc2 = taga (Symbolic.pc s1) by rewrite -Hpct Hs2.
  have Hregs2r1 : Symbolic.regs s2 r1 = Some (w1 @ t1) by rewrite Hs2.
  have Hregs2r2 : Symbolic.regs s2 r2 = Some (old @ told) by rewrite Hs2.
  have [w1' Hreg1s1] := reg_reflect_bwd Hmp Hregs2r1.
  have [old' Hreg2s1] := reg_reflect_bwd Hmp Hregs2r2.
  have [a2 Hrcom2] : exists a2, Symbolic.regs s2 rcom = Some a2.
  { move: NEXT2; rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc
                        /Symbolic.next_state /Symbolic.evi.
    case: (Symbolic.regs s2 rcom) => [a2|] /=; [by move=> _; exists a2 | by []]. }
  have [ei Hevi] := pad_evi_reflect Hmp (ex_intro _ a2 Hrcom2).
  have Hcur1 : color ti1 == match taga (Symbolic.pc s1) with Level _ c => c end.
  { rewrite Hti1 -Hti2 -Htpc2eq; exact: Hcur2. }
  have Hbel1 : color ti1 == color (taga (v1n @ tnext)).
  { have E1 : taga (v1n @ tnext) = tnext by []. have E2 : taga (v2n @ tnext) = tnext by [].
    rewrite E1 Hti1 -Hti2. by move: Hbel2; rewrite E2. }
  do 2 eexists; eapply step_mov.
  - exact: (Symbolic.state_eta s1).
  - exact: Hm1.
  - exact: Hdec1.
  - exact: Hreg1s1.
  - exact: Hreg2s1.
  - exact: (merged_mov_intro Hic1 Hm1n Hreg1s1 Hreg2s1 Hcur1 Hbel1 Hevi).
Qed.

Lemma pad_nostep_binop (s1 s2 : st)
  (mem2 : {fmap mword mt -> matom}) (reg2 : {fmap reg mt -> ratom})
  (pc2 : mword mt) (tpc2 : tag_type lrc_tags P) (i2 : mword mt) (ti2 : mem_tag)
  (extra2 : unit) (bop : binop) (r1 r2 r3 : reg mt) (w1 w2 : mword mt) (t1 t2 : value_tag)
  (old : mword mt) (told : value_tag) (s2' : st) (ev : option event) :
  match_pad s1 s2 -> pc_safe s1 ->
  s2 = @Symbolic.State mt lrc_tags unit mem2 reg2 (pc2 @ tpc2) extra2 ->
  mem2 pc2 = Some (i2 @ ti2) -> decode_instr i2 = Some (Binop bop r1 r2 r3) ->
  reg2 r1 = Some (w1 @ t1) -> reg2 r2 = Some (w2 @ t2) -> reg2 r3 = Some (old @ told) ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit s2
    (IVec (BINOP bop) tpc2 ti2 [hseq t1; t2; told])
    [:: RegRead r1; RegRead r2; RegWrite r3 (binop_denote bop w1 w2)] = Some (s2', ev) ->
  exists s1' ev', step_me (NC := NC) s1 s1' ev'.
Proof.
  move=> Hmp Hps Hs2 Hpc2cell Hdec2 Hr1 Hr2 Hr3 NEXT2.
  have Hm2 : Symbolic.mem s2 (vala (Symbolic.pc s2)) = Some (i2 @ ti2) by rewrite Hs2.
  have Hic2 : is_code ti2 by apply: (nsuap_is_code NEXT2).
  have [n [im [tm [i1 [ti1 [Hn [Hpc1 [Hnth [Hm1 [Hti1 [Hti2 [lp1 [lp2 [pos1 [pos2 [Hdq1 Hdq2]]]]]]]]]]]]]]]] :=
    pad_pc_cell_bwd Hmp Hps Hm2 Hic2.
  have Hbinop2 : instr_merged_to_mp im lp2 pos2 = Binop bop r1 r2 r3.
  { have H := Hdec2; rewrite Hdq2 in H; by move: H => [= ->]. }
  have Hdec1 : decode_instr i1 = Some (Binop bop r1 r2 r3).
  { rewrite Hdq1; congr Some; apply: instr_binop_indep; exact: Hbinop2. }
  have Hterm : PaddingSim.is_term im = false by apply: (imt_binop_nonterm Hbinop2).
  have Hn1 : n.+1 < size (code q) by apply: (nonterm_succ_lt code_last_term Hn Hnth Hterm).
  have [v1n [v2n [tnext [Hm1n Hm2n]]]] := pad_succ_cell_eq_tag Hmp Hpc1 Hn1 Hnth Hterm.
  have Hm2n' : mem2 (pc2 + 1)%w = Some (v2n @ tnext) by move: Hm2n; rewrite Hs2.
  have NEXT2' : @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
                  (@Symbolic.State mt lrc_tags unit mem2 reg2 (pc2 @ tpc2) extra2)
                  (IVec (OP (BINOP bop)) tpc2 ti2 [hseq t1; t2; told])
                  [:: RegRead r1; RegRead r2; RegWrite r3 (binop_denote bop w1 w2)] = Some (s2', ev)
    by move: NEXT2; rewrite Hs2.
  have [_ [_ [Ht1 [Ht2 [Hcur2 [Hbel2 [ei2 Hevi2]]]]]]] := merged_binop_inv Hic2 Hm2n' Hr1 Hr2 Hr3 NEXT2'.
  have [_ [Hpct _]] := Hmp.
  have Hic1 : is_code ti1 by rewrite Hti1 -Hti2.
  have Htpc2eq : tpc2 = taga (Symbolic.pc s1) by rewrite -Hpct Hs2.
  have Hregs2r1 : Symbolic.regs s2 r1 = Some (w1 @ Other) by rewrite Hs2 -Ht1.
  have Hregs2r2 : Symbolic.regs s2 r2 = Some (w2 @ Other) by rewrite Hs2 -Ht2.
  have Hregs2r3 : Symbolic.regs s2 r3 = Some (old @ told) by rewrite Hs2.
  have [w1' Hreg1s1] := reg_reflect_bwd Hmp Hregs2r1.
  have [w2' Hreg2s1] := reg_reflect_bwd Hmp Hregs2r2.
  have [old' Hreg3s1] := reg_reflect_bwd Hmp Hregs2r3.
  have [a2 Hrcom2] : exists a2, Symbolic.regs s2 rcom = Some a2.
  { move: NEXT2; rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc
                        /Symbolic.next_state /Symbolic.evi.
    case: (Symbolic.regs s2 rcom) => [a2|] /=; [by move=> _; exists a2 | by []]. }
  have [ei Hevi] := pad_evi_reflect Hmp (ex_intro _ a2 Hrcom2).
  have Hcur1 : color ti1 == match taga (Symbolic.pc s1) with Level _ c => c end.
  { rewrite Hti1 -Hti2 -Htpc2eq; exact: Hcur2. }
  have Hbel1 : color ti1 == color (taga (v1n @ tnext)).
  { have E1 : taga (v1n @ tnext) = tnext by []. have E2 : taga (v2n @ tnext) = tnext by [].
    rewrite E1 Hti1 -Hti2. by move: Hbel2; rewrite E2. }
  do 2 eexists; eapply step_binop.
  - exact: (Symbolic.state_eta s1).
  - exact: Hm1.
  - exact: Hdec1.
  - exact: Hreg1s1.
  - exact: Hreg2s1.
  - exact: Hreg3s1.
  - exact: (merged_binop_intro bop Hic1 Hm1n Hreg1s1 Hreg2s1 Hreg3s1 Hcur1 Hbel1 Hevi).
Qed.

Lemma imt_load_nonterm (i : Merged.instr) (lp : nat -> nat -> nat) (pos : nat) r1 r2 :
  instr_merged_to_mp i lp pos = Load r1 r2 -> PaddingSim.is_term i = false.
Proof. by case: i => //= *; congruence. Qed.
Lemma imt_store_nonterm (i : Merged.instr) (lp : nat -> nat -> nat) (pos : nat) r1 r2 :
  instr_merged_to_mp i lp pos = Store r1 r2 -> PaddingSim.is_term i = false.
Proof. by case: i => //= *; congruence. Qed.

Lemma pad_nostep_load (s1 s2 : st)
  (mem2 : {fmap mword mt -> matom}) (reg2 : {fmap reg mt -> ratom})
  (pc2 : mword mt) (tpc2 : tag_type lrc_tags P) (i2 : mword mt) (ti2 : mem_tag)
  (extra2 : unit) (r1 r2 : reg mt) (w1 w2 : mword mt) (t1 : value_tag) (t2 : mem_tag)
  (old : mword mt) (told : value_tag) (s2' : st) (ev : option event) :
  match_pad s1 s2 -> pc_safe s1 ->
  s2 = @Symbolic.State mt lrc_tags unit mem2 reg2 (pc2 @ tpc2) extra2 ->
  mem2 pc2 = Some (i2 @ ti2) -> decode_instr i2 = Some (Load r1 r2) ->
  reg2 r1 = Some (w1 @ t1) -> mem2 w1 = Some (w2 @ t2) -> reg2 r2 = Some (old @ told) ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit s2
    (IVec LOAD tpc2 ti2 [hseq t1; t2; told]) [:: RegRead r1; MemRead w1; RegWrite r2 w2] = Some (s2', ev) ->
  exists s1' ev', step_me (NC := NC) s1 s1' ev'.
Proof.
  move=> Hmp Hps Hs2 Hpc2cell Hdec2 Hr1 Hmem Hr2 NEXT2.
  have Hm2 : Symbolic.mem s2 (vala (Symbolic.pc s2)) = Some (i2 @ ti2) by rewrite Hs2.
  have Hic2 : is_code ti2 by apply: (nsuap_is_code NEXT2).
  have [n [im [tm [i1 [ti1 [Hn [Hpc1 [Hnth [Hm1 [Hti1 [Hti2 [lp1 [lp2 [pos1 [pos2 [Hdq1 Hdq2]]]]]]]]]]]]]]]] :=
    pad_pc_cell_bwd Hmp Hps Hm2 Hic2.
  have Hload2 : instr_merged_to_mp im lp2 pos2 = Load r1 r2.
  { have H := Hdec2; rewrite Hdq2 in H; by move: H => [= ->]. }
  have Hdec1 : decode_instr i1 = Some (Load r1 r2).
  { rewrite Hdq1; congr Some; apply: instr_load_indep; exact: Hload2. }
  have Hterm : PaddingSim.is_term im = false by apply: (imt_load_nonterm Hload2).
  have Hn1 : n.+1 < size (code q) by apply: (nonterm_succ_lt code_last_term Hn Hnth Hterm).
  have [v1n [v2n [tnext [Hm1n Hm2n]]]] := pad_succ_cell_eq_tag Hmp Hpc1 Hn1 Hnth Hterm.
  have Hm2n' : mem2 (pc2 + 1)%w = Some (v2n @ tnext) by move: Hm2n; rewrite Hs2.
  have NEXT2' : @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
                  (@Symbolic.State mt lrc_tags unit mem2 reg2 (pc2 @ tpc2) extra2)
                  (IVec (OP LOAD) tpc2 ti2 [hseq t1; t2; told])
                  [:: RegRead r1; MemRead w1; RegWrite r2 w2] = Some (s2', ev)
    by move: NEXT2; rewrite Hs2.
  have [_ [_ [Ht1 [Hisct2 [Hct2col2 [Hcur2 [Hbel2 [ei2 Hevi2]]]]]]]] :=
    merged_load_inv Hic2 Hm2n' Hr1 Hmem Hr2 NEXT2'.
  have [_ [Hpct _]] := Hmp.
  have Hic1 : is_code ti1 by rewrite Hti1 -Hti2.
  have Htpc2eq : tpc2 = taga (Symbolic.pc s1) by rewrite -Hpct Hs2.
  have Hregs2r1 : Symbolic.regs s2 r1 = Some (w1 @ Other) by rewrite Hs2 -Ht1.
  have Hreg1s1 := reg_reflect_bwd_other Hmp Hregs2r1.
  have Hmems2w1 : Symbolic.mem s2 w1 = Some (w2 @ t2) by rewrite Hs2.
  have [vw2' Hmems1w1] := mem_reflect_bwd Hmp Hmems2w1 Hisct2.
  have Hregs2r2 : Symbolic.regs s2 r2 = Some (old @ told) by rewrite Hs2.
  have [old' Hreg2s1] := reg_reflect_bwd Hmp Hregs2r2.
  have [a2 Hrcom2] : exists a2, Symbolic.regs s2 rcom = Some a2.
  { move: NEXT2; rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc
                        /Symbolic.next_state /Symbolic.evi.
    case: (Symbolic.regs s2 rcom) => [a2|] /=; [by move=> _; exists a2 | by []]. }
  have [ei Hevi] := pad_evi_reflect Hmp (ex_intro _ a2 Hrcom2).
  have Hcur1 : color ti1 == match taga (Symbolic.pc s1) with Level _ c => c end.
  { rewrite Hti1 -Hti2 -Htpc2eq; exact: Hcur2. }
  have Hbel1 : color ti1 == color (taga (v1n @ tnext)).
  { have E1 : taga (v1n @ tnext) = tnext by []. have E2 : taga (v2n @ tnext) = tnext by [].
    rewrite E1 Hti1 -Hti2. by move: Hbel2; rewrite E2. }
  have Hct2col : color ti1 == color t2 by rewrite Hti1 -Hti2; exact: Hct2col2.
  do 2 eexists; eapply step_load.
  - exact: (Symbolic.state_eta s1).
  - exact: Hm1.
  - exact: Hdec1.
  - exact: Hreg1s1.
  - exact: Hmems1w1.
  - exact: Hreg2s1.
  - exact: (merged_load_intro Hic1 Hisct2 Hm1n Hreg1s1 Hmems1w1 Hreg2s1 Hcur1 Hbel1 Hct2col Hevi).
Qed.

Lemma pad_nostep_store (s1 s2 : st)
  (mem2 : {fmap mword mt -> matom}) (reg2 : {fmap reg mt -> ratom})
  (pc2 : mword mt) (tpc2 : tag_type lrc_tags P) (i2 : mword mt) (ti2 : mem_tag)
  (extra2 : unit) (r1 r2 : reg mt) (w1 w2 old : mword mt) (t1 t2 : value_tag) (told : mem_tag)
  (s2' : st) (ev : option event) :
  match_pad s1 s2 -> pc_safe s1 ->
  s2 = @Symbolic.State mt lrc_tags unit mem2 reg2 (pc2 @ tpc2) extra2 ->
  mem2 pc2 = Some (i2 @ ti2) -> decode_instr i2 = Some (Store r1 r2) ->
  reg2 r1 = Some (w1 @ t1) -> reg2 r2 = Some (w2 @ t2) -> mem2 w1 = Some (old @ told) ->
  @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit s2
    (IVec STORE tpc2 ti2 [hseq t1; t2; told]) [:: RegRead r1; RegRead r2; MemWrite w1 w2] = Some (s2', ev) ->
  exists s1' ev', step_me (NC := NC) s1 s1' ev'.
Proof.
  move=> Hmp Hps Hs2 Hpc2cell Hdec2 Hr1 Hr2 Hmem NEXT2.
  have Hm2 : Symbolic.mem s2 (vala (Symbolic.pc s2)) = Some (i2 @ ti2) by rewrite Hs2.
  have Hic2 : is_code ti2 by apply: (nsuap_is_code NEXT2).
  have [n [im [tm [i1 [ti1 [Hn [Hpc1 [Hnth [Hm1 [Hti1 [Hti2 [lp1 [lp2 [pos1 [pos2 [Hdq1 Hdq2]]]]]]]]]]]]]]]] :=
    pad_pc_cell_bwd Hmp Hps Hm2 Hic2.
  have Hstore2 : instr_merged_to_mp im lp2 pos2 = Store r1 r2.
  { have H := Hdec2; rewrite Hdq2 in H; by move: H => [= ->]. }
  have Hdec1 : decode_instr i1 = Some (Store r1 r2).
  { rewrite Hdq1; congr Some; apply: instr_store_indep; exact: Hstore2. }
  have Hterm : PaddingSim.is_term im = false by apply: (imt_store_nonterm Hstore2).
  have Hn1 : n.+1 < size (code q) by apply: (nonterm_succ_lt code_last_term Hn Hnth Hterm).
  have [v1n [v2n [tnext [Hm1n Hm2n]]]] := pad_succ_cell_eq_tag Hmp Hpc1 Hn1 Hnth Hterm.
  have Hm2n' : mem2 (pc2 + 1)%w = Some (v2n @ tnext) by move: Hm2n; rewrite Hs2.
  have NEXT2' : @Symbolic.next_state_updates mt ops lrc_tags Merged.transfer unit
                  (@Symbolic.State mt lrc_tags unit mem2 reg2 (pc2 @ tpc2) extra2)
                  (IVec (OP STORE) tpc2 ti2 [hseq t1; t2; told])
                  [:: RegRead r1; RegRead r2; MemWrite w1 w2] = Some (s2', ev)
    by move: NEXT2; rewrite Hs2.
  have [_ [_ [Ht1 [Hisctold [Htoldcol2 [Hcur2 [Hbel2 [ei2 Hevi2]]]]]]]] :=
    merged_store_inv Hic2 Hm2n' Hr1 Hr2 Hmem NEXT2'.
  have [_ [Hpct _]] := Hmp.
  have Hic1 : is_code ti1 by rewrite Hti1 -Hti2.
  have Htpc2eq : tpc2 = taga (Symbolic.pc s1) by rewrite -Hpct Hs2.
  have Hregs2r1 : Symbolic.regs s2 r1 = Some (w1 @ Other) by rewrite Hs2 -Ht1.
  have Hreg1s1 := reg_reflect_bwd_other Hmp Hregs2r1.
  have Hregs2r2 : Symbolic.regs s2 r2 = Some (w2 @ t2) by rewrite Hs2.
  have [w2' Hreg2s1] := reg_reflect_bwd Hmp Hregs2r2.
  have Hmems2w1 : Symbolic.mem s2 w1 = Some (old @ told) by rewrite Hs2.
  have [old' Hmems1w1] := mem_reflect_bwd Hmp Hmems2w1 Hisctold.
  have [a2 Hrcom2] : exists a2, Symbolic.regs s2 rcom = Some a2.
  { move: NEXT2; rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc
                        /Symbolic.next_state /Symbolic.evi.
    case: (Symbolic.regs s2 rcom) => [a2|] /=; [by move=> _; exists a2 | by []]. }
  have [ei Hevi] := pad_evi_reflect Hmp (ex_intro _ a2 Hrcom2).
  have Hcur1 : color ti1 == match taga (Symbolic.pc s1) with Level _ c => c end.
  { rewrite Hti1 -Hti2 -Htpc2eq; exact: Hcur2. }
  have Hbel1 : color ti1 == color (taga (v1n @ tnext)).
  { have E1 : taga (v1n @ tnext) = tnext by []. have E2 : taga (v2n @ tnext) = tnext by [].
    rewrite E1 Hti1 -Hti2. by move: Hbel2; rewrite E2. }
  have Htoldcol : color ti1 == color told by rewrite Hti1 -Hti2; exact: Htoldcol2.
  do 2 eexists; eapply step_store.
  - exact: (Symbolic.state_eta s1).
  - exact: Hm1.
  - exact: Hdec1.
  - exact: Hreg1s1.
  - exact: Hreg2s1.
  - exact: Hmems1w1.
  - exact: (merged_store_intro Hic1 Hisctold Hm1n Hreg1s1 Hreg2s1 Hmems1w1 Hcur1 Hbel1 Htoldcol Hevi).
Qed.

Lemma pad_nostep_bnz (s1 s2 : st)
  (mem2 : {fmap mword mt -> matom}) (reg2 : {fmap reg mt -> ratom})
  (pc2 : mword mt) (tpc2 : tag_type lrc_tags P) (i2 : mword mt) (ti2 : mem_tag)
  (extra2 : unit) (r : reg mt) (n2 : imm mt) (w : mword mt) (t1 : value_tag)
  (s2' : st) (ev : option event) :
  match_pad s1 s2 -> pc_safe s1 ->
  s2 = @Symbolic.State mt lrc_tags unit mem2 reg2 (pc2 @ tpc2) extra2 ->
  mem2 pc2 = Some (i2 @ ti2) -> decode_instr i2 = Some (Bnz r n2) -> reg2 r = Some (w @ t1) ->
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s2
    (IVec BNZ tpc2 ti2 [hseq t1]) [:: RegRead r]
    (pc2 + (if w == 0%w then 1%w else swcast n2))%w = Some (s2', ev) ->
  exists s1' ev', step_me (NC := NC) s1 s1' ev'.
Proof.
  move=> Hmp Hps Hs2 Hpc2cell Hdec2 Hr NEXT2.
  have Hm2 : Symbolic.mem s2 (vala (Symbolic.pc s2)) = Some (i2 @ ti2) by rewrite Hs2.
  have Hic2 : is_code ti2 by apply: (nsuap_is_code NEXT2).
  have [n [im [tm [i1 [ti1 [Hn [Hvq [Hv2eq [Hnth [Henc1 [Henc2 [Hm1 [Hti1 Hti2]]]]]]]]]]]]] :=
    pad_pc_cell_bwd_aux Hmp Hps Hm2 Hic2.
  have [_ [_ [_ [_ [_ [Hc1rev [_ [Hc2rev _]]]]]]]] := Hmp.
  have [_ [Hpct _]] := Hmp.
  have Hic1 : is_code ti1 by rewrite Hti1 -Hti2.
  have Htpc2eq : tpc2 = taga (Symbolic.pc s1) by rewrite -Hpct Hs2.
  have Hbw : pc0 + size (code q) < 2 ^ word_size mt by exact: (ltn_trans Hbound alloc_label_lt_word).
  have [na [ima [tma [Hna [Hvqa [Hntha [Htagqa Hdecq]]]]]]] := code_cell_q Hcount Hbound Hbound' Henc1.
  have Ena : na = n.
  { have Hb1 : na + pc0 < 2 ^ word_size mt by move: Hna Hbw; lia.
    have Hb2 : n + pc0 < 2 ^ word_size mt by move: Hn Hbw; lia.
    by have := word_of_nat_inj Hb1 Hb2 (etrans (esym Hvqa) Hvq); lia. }
  rewrite Ena in Hntha Hdecq.
  have [Eim Etm] : ima = im /\ tma = tm by move: Hntha; rewrite Hnth => [= -> ->].
  rewrite Eim in Hdecq.
  move: Hdecq; rewrite vala_at => Hdecq.
  have [v2 [Henc2c [Htag2c Hdec2c]]] := code_cell_padc word_of_nat_inj Hcount Hbound Hbound' Hn Hnth.
  have Hv2cell : v2 = i2 @ ti2 by have H := Henc2; rewrite Hv2eq Henc2c in H; move: H => [= ->].
  rewrite Hv2cell vala_at in Hdec2c.
  have HBeq : Bnz r n2 = instr_merged_to_mp im (lpf padc) (pc0 + shift_pos sizes n).
  { have H := Hdec2; rewrite Hdec2c in H; move: H => [= H']; by rewrite H'. }
  have [rc [l0 [Him Hn2eq]]] := imt_bnz_inv HBeq.
  rewrite Him in HBeq Hdecq Hnth; clear Him.
  pose n1 := @word_of_nat (imm_size mt) (lpf (code q) l0 (pc0 + n) - (pc0 + n)).
  have Hdec1 : decode_instr i1 = Some (Bnz r n1).
  { simpl in HBeq. injection HBeq as E1 E2. rewrite Hdecq. by rewrite ?E1 ?E2. }
  have [Hpcv _] := Hmp.
  have [celln1 [celln2 [Hmem1pc' [Hmem2pc' Hcol]]]] :
    exists celln1 celln2,
      Symbolic.mem s1 (vala (Symbolic.pc s1) + (if w == 0%w then 1%w else swcast n1))%w = Some celln1 /\
      Symbolic.mem s2 (vala (Symbolic.pc s2) + (if w == 0%w then 1%w else swcast n2))%w = Some celln2 /\
      color (taga celln2) = color (taga celln1).
  { case: (w == 0%w).
    -
      have Hterm : PaddingSim.is_term (MrBnz rc l0) = false by [].
      have Hn1 : n.+1 < size (code q) by apply: (nonterm_succ_lt code_last_term Hn Hnth Hterm).
      have [v1n [v2n [tnext [Hm1n Hm2n]]]] := pad_succ_cell_eq_tag Hmp Hvq Hn1 Hnth Hterm.
      by exists (v1n @ tnext), (v2n @ tnext); rewrite Hm1n Hm2n.
    - have [mtgt Hfind] := bnz_labels_resolved Hnth.
      have Hmlt : mtgt < size (code q) by exact: (findopt_lt Hfind).
      have Hlpfq : lpf (code q) l0 (pc0 + n) = pc0 + mtgt by rewrite Hfind.
      have Hbk : (n + pc0) + (mtgt - n) < alloc_label by move: Hmlt Hn Hbound; lia.
      have Hjtgt : n + (mtgt - n) < size (code q) by move: Hmlt Hn; lia.
      have Hpc1t : (vala (Symbolic.pc s1) + swcast n1)%w = word_of_nat ((n + (mtgt - n)) + pc0).
      { rewrite Hvq /n1 Hlpfq.
        have -> : (pc0 + mtgt) - (pc0 + n) = mtgt - n by lia.
        rewrite (addw_word_of_nat_swcast Hbk). congr word_of_nat. by lia. }
      have [v1tgt Henc1t] := encode_code_dom word_of_nat_inj Hbw Hjtgt.
      have Hmem1t : Symbolic.mem s1 (vala (Symbolic.pc s1) + swcast n1)%w = Some v1tgt
        by rewrite Hpc1t; exact: (Hc1rev _ _ Henc1t).
      have [jt [imt0 [tmt [Hjtlt [Hpwt [Hntht [Htmt Hdect]]]]]]] := code_cell_q Hcount Hbound Hbound' Henc1t.
      have Ejt : n + (mtgt - n) = jt.
      { have Hb1 : (n + (mtgt - n)) + pc0 < 2 ^ word_size mt by move: Hjtgt Hbw; lia.
        have Hb2 : jt + pc0 < 2 ^ word_size mt by move: Hjtlt Hbw; lia.
        have := word_of_nat_inj Hb1 Hb2 Hpwt. by lia. }
      have [v2tgt [Henc2t [Htag2t _]]] := code_cell_padc word_of_nat_inj Hcount Hbound Hbound' Hjtlt Hntht.
      have Hpccorr_t : (vala (Symbolic.pc s2) + swcast n2)%w = phia q q' (vala (Symbolic.pc s1) + swcast n1)%w.
      { have HB := bnz_corr Hcount Hbound Hbound' Hn Hfind.
        have Hvp : vala (Symbolic.pc s2) = word_of_nat (pc0 + shift_pos sizes n)
          by rewrite Hpcv Hvq (phia_addr_code Hcount Hbound Hbound' Hn); congr word_of_nat; lia.
        have Hpcwk : vala (Symbolic.pc s1) = word_of_nat (pc0 + n) by rewrite Hvq; congr word_of_nat; lia.
        rewrite Hvp Hpcwk Hn2eq /n1; exact: HB. }
      have Hmem2t : Symbolic.mem s2 (vala (Symbolic.pc s2) + swcast n2)%w = Some v2tgt.
      { rewrite Hpccorr_t Hpc1t (phia_addr_code Hcount Hbound Hbound' Hjtgt) Ejt.
        exact: (Hc2rev _ _ Henc2t). }
      exists v1tgt, v2tgt; split; first exact: Hmem1t.
      split; first exact: Hmem2t.
      by rewrite Htag2t -Htmt. }
  have Hm2pc' : mem2 (pc2 + (if w == 0%w then 1%w else swcast n2))%w = Some celln2
    by move: Hmem2pc'; rewrite Hs2.
  have NEXT2' : @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
                  (@Symbolic.State mt lrc_tags unit mem2 reg2 (pc2 @ tpc2) extra2)
                  (IVec (OP BNZ) tpc2 ti2 [hseq t1]) [:: RegRead r]
                  (pc2 + (if w == 0%w then 1%w else swcast n2))%w = Some (s2', ev)
    by move: NEXT2; rewrite Hs2.
  have [_ [_ [Ht1 [Hcur2 [Hbel2 [ei2 Hevi2]]]]]] := merged_bnz_inv Hic2 Hr Hm2pc' NEXT2'.
  have Hregs2r : Symbolic.regs s2 r = Some (w @ Other) by rewrite Hs2 -Ht1.
  have Hreg1s1 := reg_reflect_bwd_other Hmp Hregs2r.
  have [a2 Hrcom2] : exists a2, Symbolic.regs s2 rcom = Some a2.
  { move: NEXT2; rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state /Symbolic.evi.
    case: (Symbolic.regs s2 rcom) => [a2|] /=; [by move=> _; exists a2 | by []]. }
  have [ei Hevi] := pad_evi_reflect Hmp (ex_intro _ a2 Hrcom2).
  have Hcur1 : color ti1 == match taga (Symbolic.pc s1) with Level _ c => c end.
  { rewrite Hti1 -Hti2 -Htpc2eq; exact: Hcur2. }
  have Hbel1 : color ti1 == color (taga celln1).
  { rewrite Hti1 -Hti2 -Hcol; exact: Hbel2. }
  do 2 eexists; eapply step_bnz.
  - exact: (Symbolic.state_eta s1).
  - exact: Hm1.
  - exact: Hdec1.
  - exact: Hreg1s1.
  - exact: (merged_bnz_intro Hic1 Hreg1s1 Hmem1pc' Hcur1 Hbel1 Hevi).
Qed.

Lemma pad_nostep_jump (s1 s2 : st)
  (mem2 : {fmap mword mt -> matom}) (reg2 : {fmap reg mt -> ratom})
  (pc2 : mword mt) (tpc2 : tag_type lrc_tags P) (i2 : mword mt) (ti2 : mem_tag)
  (extra2 : unit) (r : reg mt) (w : mword mt) (t1 : value_tag) (rav : mword mt) (rat : value_tag)
  (l : hseq (Symbolic.tag_type lrc_tags) (nseq (size Symbolic.reg_list).+1 Symbolic.R))
  (s2' : st) (ev : option event) :
  match_pad s1 s2 -> pc_safe s1 -> pad_valid s1 ->
  s2 = @Symbolic.State mt lrc_tags unit mem2 reg2 (pc2 @ tpc2) extra2 ->
  mem2 pc2 = Some (i2 @ ti2) -> decode_instr i2 = Some (Jump r) ->
  reg2 r = Some (w @ t1) -> reg2 ra = Some (rav @ rat) ->
  @Symbolic.reg_clear_list mt lrc_tags reg2 t1 = Some l ->
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s2
    (IVec JUMP tpc2 ti2 (HSeqCons rat l)) [:: RegRead ra, RegRead r & reg_clear_read] w
    = Some (s2', ev) ->
  exists s1' ev', step_me (NC := NC) s1 s1' ev'.
Proof.
  move=> Hmp Hps Hpv Hs2 Hpc2cell Hdec2 Hr Hra Hclear NEXT2.
  have Hm2 : Symbolic.mem s2 (vala (Symbolic.pc s2)) = Some (i2 @ ti2) by rewrite Hs2.
  have Hic2 : is_code ti2 by apply: (nsuap_is_code NEXT2).
  have [n [im [tm [i1 [ti1 [Hn [Hpc1 [Hnth [Hm1 [Hti1 [Hti2 [lp1 [lp2 [pos1 [pos2 [Hdq1 Hdq2]]]]]]]]]]]]]]]] :=
    pad_pc_cell_bwd Hmp Hps Hm2 Hic2.
  have Hjump2 : instr_merged_to_mp im lp2 pos2 = Jump r.
  { have H := Hdec2; rewrite Hdq2 in H; by move: H => [= ->]. }
  have Hdec1 : decode_instr i1 = Some (Jump r).
  { rewrite Hdq1; congr Some; apply: instr_jump_indep; exact: Hjump2. }
  have Hic1 : is_code ti1 by rewrite Hti1 -Hti2.
  have [_ [Hpct _]] := Hmp.
  case: tpc2 Hs2 NEXT2 => [level ctpc] Hs2 NEXT2.
  have NEXT2' := NEXT2; rewrite Hs2 in NEXT2'.
  have [Hcolor Hdisj] := jump_step_inv Hic2 Hr Hra Hclear NEXT2'.
  have Htpcs1 : taga (Symbolic.pc s1) = Level level ctpc by rewrite -Hpct Hs2.
  have Hcur1 : color ti1 == match taga (Symbolic.pc s1) with Level _ c => c end.
  { rewrite Htpcs1 /= Hti1 -Hti2; exact: Hcolor. }
  have Hras2 : Symbolic.regs s2 ra = Some (rav @ rat) by rewrite Hs2.
  have [rav' Hra1s1] := reg_reflect_bwd Hmp Hras2.
  have [a2 Hrcom2] : exists a2, Symbolic.regs s2 rcom = Some a2.
  { move: NEXT2; rewrite /Symbolic.next_state_updates_and_pc /Symbolic.next_state /Symbolic.evi.
    case: (Symbolic.regs s2 rcom) => [a2|] /=; [by move=> _; exists a2 | by []]. }
  have [ei Hevi] := pad_evi_reflect Hmp (ex_intro _ a2 Hrcom2).
  case: Hdisj => [[Hbel Ht1] | [n0 [celltgt [rcv [Hmw [Hbelne [Ht1 [Hlvl Hrcom]]]]]]]].
  -
    have Hregs2r : Symbolic.regs s2 r = Some (w @ InternalJump) by rewrite Hs2 -Ht1.
    have [w' [Hr1s1 Hweq]] := reg_reflect_bwd_cptr Hmp Hregs2r isT (fun H => ltac:(discriminate H)).
    have Hbel1 : belong (color ti1)
                   (match Symbolic.mem s1 w' with Some ni => Some (taga ni) | None => None end).
    { rewrite Hti1 -Hti2; apply: (jump_belong_corr_bwd (s2 := s2)).
      - exact: Hmp.
      - rewrite Hs2 /= -Hweq; exact: Hbel. }
    have [l1 Hl1] : exists l1, @Symbolic.reg_clear_list mt lrc_tags (Symbolic.regs s1) InternalJump = Some l1.
    { apply: reg_clear_list_aux_total => e He.
      have [a Ha] := reg_clear_list_aux_dom Hclear He.
      have Hregs2e : Symbolic.regs s2 (as_word (ssrint.Posz e)) = Some a by rewrite Hs2.
      rewrite -(atom_etaE a) in Hregs2e.
      have [v' Hv'] := reg_reflect_bwd Hmp Hregs2e. by exists (v' @ (taga a)). }
    do 2 eexists; eapply step_jump.
    + exact: (Symbolic.state_eta s1).
    + exact: Hm1.
    + exact: Hdec1.
    + exact: Hr1s1.
    + exact: Hra1s1.
    + exact: Hl1.
    + apply: jump_internal_nsuap.
      * exact: Hic1.
      * exact: Hr1s1.
      * exact: Hra1s1.
      * exact: Hl1.
      * exact: Hbel1.
      * exact: Hcur1.
      * exact: Hevi.
  -
    have Hregs2r : Symbolic.regs s2 r = Some (w @ (Ret n0)) by rewrite Hs2 -Ht1.
    have [w' [Hr1s1 Hweq]] := reg_reflect_bwd_cptr Hmp Hregs2r isT (fun H => ltac:(discriminate H)).
    have Hok : addr_ok (Symbolic.mem s1) w'.
    { have [Hav _] := Hpv. apply: (Hav _ _ _ Hr1s1). by []. }
    have Hm2tgt : Symbolic.mem s2 (phia q q' w') = Some celltgt.
    { rewrite -Hweq. by move: Hmw; rewrite Hs2. }
    have [celltgt1 [Hm1tgt Htceq]] := jump_target_corr_bwd Hmp Hok Hm2tgt.
    have Hrcoms2 : Symbolic.regs s2 rcom = Some (rcv @ Other) by rewrite Hs2.
    have Hrcom1 := reg_reflect_bwd_other Hmp Hrcoms2.
    have [_ [_ [_ [Hwreg _]]]] := Hmp.
    have Hrne : r != rcom.
    { apply/eqP => E. move: Hr1s1; rewrite E Hrcom1. by move=> [=]. }
    have Harne : ra != rcom by [].
    have [l1 Hl1] : exists l1, @Symbolic.reg_clear_list mt lrc_tags (Symbolic.regs s1) (Ret n0) = Some l1.
    { apply: reg_clear_list_aux_total => e He.
      have [a Ha] := reg_clear_list_aux_dom Hclear He.
      have Hregs2e : Symbolic.regs s2 (as_word (ssrint.Posz e)) = Some a by rewrite Hs2.
      rewrite -(atom_etaE a) in Hregs2e.
      have [v' Hv'] := reg_reflect_bwd Hmp Hregs2e. by exists (v' @ (taga a)). }
    have [sd1 [sd2 [Hsd1 _]]] := return_clear Hwreg Hra1s1 Hr1s1 Hrcom1 Hrne Harne Hl1.
    have Hlv0 : 0 < level by rewrite Hlvl.
    have Hcur1' : color ti1 == ctpc by rewrite Hti1 -Hti2; exact: Hcolor.
    have Hbelne1 : color ti1 != color (taga celltgt1).
    { rewrite Hti1 -Hti2 Htceq; move: Hbelne; by rewrite belong_someE. }
    have Hr1s1' : Symbolic.regs s1 r = Some (w' @ (Ret level.-1)) by rewrite Hlvl /=; exact: Hr1s1.
    have Hl1' : @Symbolic.reg_clear_list mt lrc_tags (Symbolic.regs s1) (Ret level.-1) = Some l1
      by rewrite Hlvl /=; exact: Hl1.
    do 2 eexists; eapply step_jump.
    + exact: (Symbolic.state_eta s1).
    + exact: Hm1.
    + exact: Hdec1.
    + exact: Hr1s1.
    + exact: Hra1s1.
    + exact: Hl1.
    + apply: (jump_return_nsuap rav' rat).
      * exact: Hic1.
      * exact: Htpcs1.
      * exact: Hcur1'.
      * exact: Hm1tgt.
      * exact: Hbelne1.
      * exact: Hr1s1'.
      * exact: Hrcom1.
      * exact: Hlv0.
      * exact: Hl1'.
      * exact: Hevi.
      * exact: Hsd1.
Qed.

Lemma imt_jal_inv (i : Merged.instr) (lp : nat -> nat -> nat) (pos : nat) (w : imm mt) :
  Jal w = instr_merged_to_mp i lp pos ->
  exists l, i = MrJal l /\ w = @word_of_nat (imm_size mt) (lp l pos).
Proof. by case: i => //= l [= ->]; exists l. Qed.

Lemma rcla_cons_some (e : nat) (l' : seq nat)
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

Lemma pad_nostep_jal (s1 s2 : st)
  (mem2 : {fmap mword mt -> matom}) (reg2 : {fmap reg mt -> ratom})
  (pc2 : mword mt) (tpc2 : tag_type lrc_tags P) (i2 : mword mt) (ti2 : mem_tag)
  (extra2 : unit) (imm : imm mt) (old : mword mt) (told : value_tag)
  (l : hseq (Symbolic.tag_type lrc_tags) (nseq (size Symbolic.reg_list).+1 Symbolic.R))
  (vret : mword mt) (tret : mem_tag) (s2' : st) (ev : option event) :
  match_pad s1 s2 -> pc_safe s1 -> pad_valid s1 ->
  s2 = @Symbolic.State mt lrc_tags unit mem2 reg2 (pc2 @ tpc2) extra2 ->
  mem2 pc2 = Some (i2 @ ti2) -> mem2 (pc2 + 1)%w = Some (vret @ tret) ->
  decode_instr i2 = Some (Jal imm) ->
  reg2 ra = Some (old @ told) ->
  @Symbolic.reg_clear_list mt lrc_tags reg2 told = Some l ->
  @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit s2
    (IVec JAL tpc2 ti2 (HSeqCons tret l))
    [:: MemRead (pc2 + 1)%w, RegWrite ra (pc2 + 1)%w & reg_clear_read] (swcast imm)
    = Some (s2', ev) ->
  exists s1' ev', step_me (NC := NC) s1 s1' ev'.
Proof.
  move=> Hmp Hps Hpv Hs2 Hpc2cell Hretcell Hdec2 Hra Hclear NEXT2.
  have Hm2 : Symbolic.mem s2 (vala (Symbolic.pc s2)) = Some (i2 @ ti2) by rewrite Hs2.
  have Hic2 : is_code ti2 by apply: (nsuap_is_code NEXT2).
  have [n [im [tm [i1 [ti1 [Hn [Hpc1 [Hv2eq [Hnth [Henc1 [Henc2 [Hm1 [Hti1 Hti2]]]]]]]]]]]]] :=
    pad_pc_cell_bwd_aux Hmp Hps Hm2 Hic2.
  have [_ [_ [_ [_ [Hc1iso [Hc1rev [_ [Hc2rev _]]]]]]]] := Hmp.
  have [_ [Hpct _]] := Hmp.
  have Hic1 : is_code ti1 by rewrite Hti1 -Hti2.
  have [na [ima [tma [Hna [Hvqa [Hntha [Htagqa Hdecq]]]]]]] := code_cell_q Hcount Hbound Hbound' Henc1.
  have Ena : na = n.
  { have Hbw : pc0 + size (code q) < 2 ^ word_size mt by exact: (ltn_trans Hbound alloc_label_lt_word).
    have Hb1 : na + pc0 < 2 ^ word_size mt by move: Hna Hbw; lia.
    have Hb2 : n + pc0 < 2 ^ word_size mt by move: Hn Hbw; lia.
    by have := word_of_nat_inj Hb1 Hb2 (etrans (esym Hvqa) Hpc1); lia. }
  rewrite Ena in Hntha Hdecq.
  have [Eim Etm] : ima = im /\ tma = tm by move: Hntha; rewrite Hnth => [= -> ->].
  rewrite Eim in Hdecq; move: Hdecq; rewrite vala_at => Hdecq.
  have [v2c [Henc2c [Htag2c Hdec2c]]] := code_cell_padc word_of_nat_inj Hcount Hbound Hbound' Hn Hnth.
  have Hv2cell : v2c = i2 @ ti2 by have H := Henc2; rewrite Hv2eq Henc2c in H; move: H => [= ->].
  rewrite Hv2cell vala_at in Hdec2c.
  have HBeq := Hdec2c; rewrite Hdec2 in HBeq; move: HBeq => [= HBeq].
  have [l0 [Him Himm]] := imt_jal_inv HBeq.
  subst im.
  rewrite Him in Hdecq Hnth.
  pose imm1 := @word_of_nat (imm_size mt) (lpf (code q) l0 (pc0 + n)).
  have Hdec1 : decode_instr i1 = Some (Jal imm1). { rewrite /imm1 Hdecq. by []. }
  have Hterm : PaddingSim.is_term (MrJal l0) = false by [].
  have Hn1 : n.+1 < size (code q) by apply: (nonterm_succ_lt code_last_term Hn Hnth Hterm).
  have [v1n [v2n [tnext [Hm1n Hm2n]]]] := pad_succ_cell_eq_tag Hmp Hpc1 Hn1 Hnth Hterm.
  have Htgt : swcast imm = phia q q' (swcast imm1).
  { rewrite Himm /imm1. exact: (PaddingSim.jal_corr Hcount Hbound Hbound' l0 Hn). }
  have Hmem2 : Symbolic.mem s2 = mem2 by rewrite Hs2.
  have Hpcv2 : vala (Symbolic.pc s2) = pc2 by rewrite Hs2.
  have Etret : tret = tnext.
  { move: Hm2n; rewrite Hmem2 Hpcv2 Hretcell => -[= _ ->]; by []. }
  have Hras2 : Symbolic.regs s2 ra = Some (old @ told) by rewrite Hs2.
  have [old' Hra1s1] := reg_reflect_bwd Hmp Hras2.
  have [a2 Hrcom2] : exists a2, Symbolic.regs s2 rcom = Some a2.
  { move: NEXT2; rewrite Hs2 /Symbolic.next_state_updates_and_pc /Symbolic.next_state /Symbolic.evi.
    case E: (reg2 rcom) => [a2|] /=; [by move=> _; exists a2 | by []]. }
  have Hrcom2' : Symbolic.regs s2 rcom = Some ((vala a2) @ (taga a2)) by rewrite Hrcom2 atom_etaE.
  have [w1 Hrcom1] := reg_reflect_bwd Hmp Hrcom2'.
  have [ei Hevi] := pad_evi_reflect Hmp (ex_intro _ a2 Hrcom2).
  have Hdom : forall e, e \in [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N ->
                exists a, Symbolic.regs s1 (as_word (ssrint.Posz e)) = Some a.
  { move=> e He.
    have He' : e \in Symbolic.reg_list by rewrite /Symbolic.reg_list in_cons He orbT.
    have [a Ha] := reg_clear_list_aux_dom Hclear He'.
    have Hregs2e : Symbolic.regs s2 (as_word (ssrint.Posz e)) = Some a by rewrite Hs2.
    rewrite -(atom_etaE a) in Hregs2e.
    have [v' Hv'] := reg_reflect_bwd Hmp Hregs2e. by exists (v' @ (taga a)). }
  have [lh1 Hlh1] : exists lh1,
       Symbolic.reg_clear_list_aux [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N (Symbolic.regs s1) (taga a2) = Some lh1.
  { apply: reg_clear_list_aux_total; exact: Hdom. }
  have Hl1full : Symbolic.reg_clear_list (Symbolic.regs s1) told = Some (HSeqCons told lh1).
  { have Hr1 : Symbolic.regs s1 (as_word (ssrint.Posz 1)) = Some (w1 @ (taga a2)) by exact: Hrcom1.
    have Hlh1' : Symbolic.reg_clear_list_aux [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N
                   (Symbolic.regs s1) (taga (w1 @ (taga a2))) = Some lh1 by rewrite taga_at; exact: Hlh1.
    rewrite /Symbolic.reg_clear_list /Symbolic.reg_list.
    exact: (@rcla_cons_some 1 [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N (Symbolic.regs s1) told
              (w1 @ (taga a2)) lh1 Hr1 Hlh1'). }
  case: tpc2 Hs2 Hpct Hm2 NEXT2 Hmem2 Hpcv2 => [level ctpc] Hs2 Hpct Hm2 NEXT2 Hmem2 Hpcv2.
  have NEXT2' := NEXT2; rewrite Hs2 in NEXT2'.
  have [Hcolor [Hcret Hdisj]] := jal_step_inv Hic2 Hretcell Hra Hclear NEXT2'.
  have Htpcs1 : taga (Symbolic.pc s1) = Level level ctpc by rewrite -Hpct Hs2.
  have Hcur1 : color ti1 == match taga (Symbolic.pc s1) with Level _ c => c end.
  { rewrite Htpcs1 /= Hti1 -Hti2; exact: Hcolor. }
  have Hcret1 : color ti1 == color tnext by rewrite Hti1 -Hti2 -Etret; exact: Hcret.
  case: Hdisj => [Hbel | [celltgt [rcv [Hmw [Hbelne [Hrcoms2 [u Hentry]]]]]]].
  -
    have Hbel1 : belong (color ti1)
                   (match Symbolic.mem s1 (swcast imm1) with Some ni => Some (taga ni) | None => None end).
    { rewrite Hti1 -Hti2; apply: (jump_belong_corr_bwd (s2 := s2)).
      - exact: Hmp.
      - rewrite -Htgt Hmem2; exact: Hbel. }
    have HN1 : @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
                 s1 (IVec (OP JAL) (taga (Symbolic.pc s1)) ti1 (HSeqCons tnext (HSeqCons told lh1)))
                 [:: MemRead (vala (Symbolic.pc s1) + 1)%w, RegWrite ra (vala (Symbolic.pc s1) + 1)%w & reg_clear_read]
                 (swcast imm1)
               = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem s1)
                         (setm (Symbolic.regs s1) ra ((vala (Symbolic.pc s1) + 1)%w @ InternalJump))
                         ((swcast imm1) @ (taga (Symbolic.pc s1))) (Symbolic.internal s1), None).
    { apply: jal_internal_nsuap.
      - exact: Hic1.
      - exact: Hm1n.
      - exact: Hra1s1.
      - exact: Hrcom1.
      - exact: Hlh1.
      - exact: Hbel1.
      - exact: Hcur1.
      - exact: Hcret1.
      - exact: Hevi. }
    do 2 eexists; eapply step_jal.
    + exact: (Symbolic.state_eta s1).
    + exact: Hm1.
    + exact: Hm1n.
    + exact: Hdec1.
    + exact: Hra1s1.
    + exact: Hl1full.
    + exact: HN1.
  -
    have Hrcoms2' : Symbolic.regs s2 rcom = Some (rcv @ Other) by rewrite Hs2; exact: Hrcoms2.
    have Hrcom1' := reg_reflect_bwd_other Hmp Hrcoms2'.
    have Hta2 : taga a2 = Other by move: Hrcom2; rewrite Hrcoms2' => -[= <-].
    have [a0 Ha0] : exists a, Symbolic.regs s1 (as_word (ssrint.Posz 0)) = Some a
      by apply: Hdom; rewrite !inE.
    have [cc Hcc] : exists cc,
        Symbolic.reg_clear_list_aux [:: 2; 3; 5; 6; 7; 16; 17; 18; 19]%N (Symbolic.regs s1) (taga a0) = Some cc.
    { apply: reg_clear_list_aux_total => kk Hkk. apply: Hdom. by rewrite inE Hkk orbT. }
    have Hcons : Symbolic.reg_clear_list_aux [:: 0; 2; 3; 5; 6; 7; 16; 17; 18; 19]%N
                   (Symbolic.regs s1) (taga a2) = Some (HSeqCons Other cc).
    { rewrite Hta2.
      exact: (@rcla_cons_some 0 [:: 2; 3; 5; 6; 7; 16; 17; 18; 19]%N (Symbolic.regs s1) Other a0 cc Ha0 Hcc). }
    have Hlh1eq : lh1 = HSeqCons Other cc by move: Hlh1; rewrite Hcons => -[= <-].
    have Hm2tgt : Symbolic.mem s2 (phia q q' (swcast imm1)) = Some celltgt by rewrite -Htgt Hmem2.
    have Hok : addr_ok (Symbolic.mem s1) (swcast imm1).
    { rewrite /imm1.
      case Hfo: (findopt (fun p => match p.1 with MrLabel l1 => l0 == l1 | _ => false end) (code q))
        => [mlbl|].
      - have Hmlt : mlbl < size (code q) by exact: (findopt_lt Hfo).
        have Hb : pc0 + mlbl < alloc_label by move: Hmlt Hbound; lia.
        rewrite (swcast_word_of_nat_id Hb).
        have [v Hv] := encode_code_dom word_of_nat_inj (ltn_trans Hbound alloc_label_lt_word) Hmlt.
        left; exists v. apply: Hc1rev. by rewrite (addnC pc0 mlbl).
      - have Hl0 : l0 = alloc_label by exact: (jal_labels_resolved Hnth Hfo).
        rewrite Hl0 eqxx swcast_alloc.
        right; left. rewrite (val_word_of_nat alloc_label_lt_word). move: Hbound'; lia. }
    have [celltgt1 [Hm1tgt Htceq]] := jump_target_corr_bwd Hmp Hok Hm2tgt.
    have Hbelne' : color ti2 != color (taga celltgt) by move: Hbelne; rewrite belong_someE.
    have Hbelne1 : color ti1 != color (taga celltgt1) by rewrite Hti1 -Hti2 Htceq; exact: Hbelne'.
    have [p Hpname] : exists p, get_proc_name (Some (taga celltgt1)) = Some p.
    { rewrite Htceq. move: Hentry; rewrite /check_entry /get_proc_name.
      case: (taga celltgt) => [vt cc0 ee ic]. case: ee => [[pp el]|] /= H; last by [].
      by exists pp. }
    have Hentry1 : check_entry (color ti1) (Some (taga celltgt1)) = Some tt.
    { rewrite Hti1 -Hti2 Htceq. by move: Hentry; case: u => H; exact: H. }
    have Hcur1c : color ti1 == ctpc by rewrite Hti1 -Hti2; exact: Hcolor.
    have [sd [Hsd _]] := @jal_call_clear_1 s1 v1n old' rcv tnext told level Hm1n Hra1s1 Hrcom1' Hdom.
    have HN1 : @Symbolic.next_state_updates_and_pc mt ops lrc_tags Merged.transfer unit
                 s1 (IVec (OP JAL) (taga (Symbolic.pc s1)) ti1
                        (HSeqCons tnext (HSeqCons told (HSeqCons Other cc))))
                 [:: MemRead (vala (Symbolic.pc s1) + 1)%w, RegWrite ra (vala (Symbolic.pc s1) + 1)%w & reg_clear_read]
                 (swcast imm1)
               = Some (@Symbolic.State mt lrc_tags unit (Symbolic.mem sd) (Symbolic.regs sd)
                         ((swcast imm1) @ (build_tpc (level.+1) (color (taga celltgt1)))) (Symbolic.internal sd),
                       Some (ECall (color ti1) p (Symbolic.rcom_value ei) (color (taga celltgt1)))).
    { apply: (@jal_call_nsuap s1 sd ti1 (swcast imm1) tnext told level ctpc p cc celltgt1 ei).
      - exact: Hic1.
      - exact: Htpcs1.
      - exact: Hcur1c.
      - exact: Hcret1.
      - exact: Hm1tgt.
      - exact: Hbelne1.
      - exact: Hpname.
      - exact: Hentry1.
      - exact: Hevi.
      - exact: Hsd. }
    do 2 eexists; eapply step_jal.
    + exact: (Symbolic.state_eta s1).
    + exact: Hm1.
    + exact: Hm1n.
    + exact: Hdec1.
    + exact: Hra1s1.
    + exact: Hl1full.
    + rewrite Hlh1eq; exact: HN1.
Qed.

Lemma pad_step_bwd_exists (s1 s2 s2' : st) (ev : option event) :
  match_pad s1 s2 -> pc_safe s1 -> pad_valid s1 ->
  step_me (NC := NC) s2 s2' ev ->
  exists s1' ev', step_me (NC := NC) s1 s1' ev'.
Proof.
  move=> Hmp Hps Hpv Hstep. inversion Hstep.
  - exact: (pad_nostep_nop Hmp Hps ST PC INST NEXT).
  - exact: (pad_nostep_const Hmp Hps ST PC INST OLD NEXT).
  - exact: (pad_nostep_mov Hmp Hps ST PC INST R1W OLD NEXT).
  - exact: (pad_nostep_binop Hmp Hps ST PC INST R1W R2W OLD NEXT).
  - exact: (pad_nostep_load Hmp Hps ST PC INST R1W MEM1 OLD NEXT).
  - exact: (pad_nostep_store Hmp Hps ST PC INST R1W R2W OLD NEXT).
  - exact: (pad_nostep_jump Hmp Hps Hpv ST PC INST RW RA CLEAR NEXT).
  - exact: (pad_nostep_bnz Hmp Hps ST PC INST RW NEXT).
  - exact: (pad_nostep_jal Hmp Hps Hpv ST PC RA INST OLD CLEAR NEXT).
  - exact: (PaddingFwdSys.pad_nostep_syscall word_of_nat_inj Hcount Hbound Hbound'
             code_tags_wf_q alloc_label_lt_NC code_colors_bounded Hmp Hpv ST PC GETCALL CALL).
Qed.

Lemma Rf_nostep :
  forall s1 s2, Rf s1 s2 -> Nostep (mergedsem NC q) s1 -> Nostep (mergedsem NC padl) s2.
Proof.
  move=> s1 s2 [Hmp [Hpv [_ Hps]]] HNo t s2' Hstep.
  have [ev Hsm] : exists ev, step_me (NC := NC) s2 s2' ev.
  { move: Hstep; rewrite /= /pstep; case: t => [|e [|??]];
      [ move=> H; by exists None | move=> H; by exists (Some e) | by move=> [] ]. }
  have [s1' [ev' Hsm1]] := pad_step_bwd_exists Hmp Hps Hpv Hsm.
  apply: (HNo (if ev' is Some e then [:: e] else [::]) s1').
  rewrite /= /pstep. by case: ev' Hsm1 => [e|] Hsm1.
Qed.

Theorem padding_forward m :
  does_prefix (mergedsem NC q) m -> does_prefix (mergedsem NC padl) m.
Proof. exact: (padding_forward_sf Rf_init Rf_step1 Rf_final Rf_nostep). Qed.

Theorem padding_backward m :
  does_prefix (mergedsem NC padl) m -> does_prefix (mergedsem NC q) m.
Proof. exact: (padding_backward_sf Rf_init Rf_step1 Rf_final Rf_nostep). Qed.

End CodeShiftFinal.

Lemma shift_pos_succ (sizes : seq (nat * nat)) (n : nat) :
  all (fun x => x.1 <= x.2) sizes ->
  (forall k, sumn [seq p.1 | p <- take k sizes] <> n.+1) ->
  PaddingCorrect.shift_pos sizes n.+1 = (PaddingCorrect.shift_pos sizes n).+1.
Proof.
  elim: sizes n => [|[s m] rest IH] n //=.
  move=> /andP[Hsm Hall] Hbd.
  case: (ltnP n.+1 s) => Hn1s.
  - have T2 : (n < s) by lia. by rewrite T2.
  - have Htc : forall j : nat, take j.+1 ((s, m) :: rest) = (s, m) :: take j rest by [].
    have Hns : (n < s) = false.
    { case: (ltnP n s) => [Hlt|//]. exfalso.
      move: (Hbd 1); rewrite (Htc 0) take0 /= addn0 => Hne; apply: Hne; lia. }
    rewrite Hns.
    have Hsn : s <= n by rewrite leqNgt Hns.
    have Hrec : forall k, sumn [seq p.1 | p <- take k rest] <> (n - s).+1.
    { move=> k Heq. apply: (Hbd k.+1). rewrite (Htc k) /= Heq. lia. }
    have Hn1 : n.+1 - s = (n - s).+1 by lia.
    rewrite Hn1 (IH (n - s) Hall Hrec). by rewrite addnS.
Qed.

Lemma proc_split_fuel_all_entry (fuel : nat) (ys : @Merged.code mt) (dflt : Merged.instr * mem_tag) :
  (ys <> [::] -> is_entry (head dflt ys)) ->
  all (fun b => is_entry (head dflt b)) (proc_split_fuel fuel ys).
Proof.
  elim: fuel ys => [|fuel IH] ys Hhd.
  - case: ys Hhd => [|x xs] Hhd //=. rewrite andbT. by apply: Hhd.
  - case: ys Hhd => [|x xs] Hhd //=. apply/andP; split; first by apply: Hhd.
    apply: IH => Hne.
    have Hpos : 0 < size (drop (find is_entry xs) xs) by case: (drop _ _) Hne.
    have Hlt : find is_entry xs < size xs by move: Hpos; rewrite size_drop; lia.
    rewrite -nth0 nth_drop addn0. apply: nth_find. by rewrite has_find.
Qed.

Lemma proc_split_fuel_nonempty_b (fuel : nat) (ys : @Merged.code mt) :
  all (fun b => 0 < size b) (proc_split_fuel fuel ys).
Proof.
  elim: fuel ys => [|fuel IH] [|x xs] //=; exact: IH.
Qed.
Lemma proc_split_nonempty_b (cde : @Merged.code mt) :
  all (fun b => 0 < size b) (proc_split cde).
Proof. exact: proc_split_fuel_nonempty_b. Qed.

Lemma nth_flatten_block (bs : seq (@Merged.code mt)) (k : nat) (dflt : Merged.instr * mem_tag) :
  all (fun b => 0 < size b) bs -> k < size bs ->
  nth dflt (flatten bs) (sumn [seq size b | b <- take k bs]) = head dflt (nth [::] bs k).
Proof.
  elim: bs k => [|b bs IH] k.
  - by move=> _; rewrite ltn0.
  - move=> /andP[Hb Hall]. case: k => [|k] Hk.
    + by rewrite /= nth_cat Hb /= nth0.
    + rewrite /= nth_cat.
      have Hge : size b <= size b + sumn [seq size b0 | b0 <- take k bs] by lia.
      rewrite ltnNge Hge /= addKn. apply: (IH k Hall). by move: Hk; rewrite /= ltnS.
Qed.

Lemma proc_split_behead_entry (cde : @Merged.code mt) (dflt : Merged.instr * mem_tag) :
  all (fun b => is_entry (head dflt b)) (behead (proc_split cde)).
Proof.
  case: cde => [|x xs] //=. rewrite /proc_split /=.
  apply: proc_split_fuel_all_entry => Hne.
  have Hpos : 0 < size (drop (find is_entry xs) xs) by case: (drop _ _) Hne.
  have Hlt : find is_entry xs < size xs by move: Hpos; rewrite size_drop; lia.
  rewrite -nth0 nth_drop addn0. apply: nth_find. by rewrite has_find.
Qed.

Lemma boundary_entry (cde : @Merged.code mt) (k : nat) (dflt : Merged.instr * mem_tag) :
  0 < k -> k < size (proc_split cde) ->
  is_entry (nth dflt cde (sumn [seq size b | b <- take k (proc_split cde)])).
Proof.
  move=> Hk0 Hk.
  rewrite -{1}(proc_split_flatten cde) (nth_flatten_block dflt (proc_split_nonempty_b cde) Hk).
  move/(all_nthP [::]): (proc_split_behead_entry cde dflt) => Hbh.
  rewrite -(prednK Hk0) -nth_behead. apply: Hbh.
  rewrite size_behead -!subn1. apply: ltn_sub2r => //. exact: (leq_ltn_trans Hk0 Hk).
Qed.

Lemma sumn_sizes_flatten (bs : seq (@Merged.code mt)) :
  sumn [seq size b | b <- bs] = size (flatten bs).
Proof. by elim: bs => [|b bs IH] //=; rewrite size_cat IH. Qed.

Lemma sumn_take_block_sizes (bs bs' : seq (@Merged.code mt)) (k : nat) :
  size bs = size bs' ->
  sumn [seq p.1 | p <- take k (PaddingCorrect.block_sizes bs bs')]
  = sumn [seq size b | b <- take k bs].
Proof.
  elim: bs bs' k => [|b bs IH] [|b' bs'] [|k] //= [] Hsz //.
  by rewrite (IH bs' k Hsz).
Qed.

Lemma find_align_blocks (P : pred (Merged.instr * mem_tag)) (bs bs' : seq (@Merged.code mt)) :
  size bs = size bs' ->
  all (fun b => ~~ has P b ==> ~~ P (nop_cell (block_color b))) bs ->
  find P (align_blocks bs bs').1
  = PaddingCorrect.shift_pos (PaddingCorrect.block_sizes bs bs') (find P (flatten bs)).
Proof.
  elim: bs bs' => [|b bs IH] [|b' bs'] //= [Hsz] /andP[Hnop Hall].
  case E: (align_blocks bs bs') => [r r'] /=.
  have IHr : find P r = PaddingCorrect.shift_pos (PaddingCorrect.block_sizes bs bs') (find P (flatten bs))
    by have := IH bs' Hsz Hall; rewrite E.
  rewrite -/(PaddingCorrect.block_sizes bs bs').
  set m := maxn (size b) (size b').
  case Hhb: (has P b).
  - have Hfblt : find P b < size b by rewrite -has_find Hhb.
    rewrite find_cat /block_pad has_cat Hhb /= find_cat Hhb /=.
    by rewrite find_cat Hhb /= Hfblt.
  - have Hnopf : ~~ P (nop_cell (block_color b)) by move: Hnop; rewrite Hhb.
    have Hhnop : has P (nseq (m - size b) (nop_cell (block_color b))) = false
      by rewrite has_nseq (negbTE Hnopf) andbF.
    rewrite find_cat /block_pad has_cat Hhb /= Hhnop /= size_cat size_nseq.
    have Hmsz : size b + (m - size b) = m by rewrite addnC subnK // leq_maxl.
    rewrite Hmsz find_cat Hhb /=.
    have Hge : (size b + find P (flatten bs) < size b) = false
      by apply/negbTE; rewrite -leqNgt leq_addr.
    by rewrite Hge addKn IHr.
Qed.

Section AlignDischarge.

Variables q q' : program.
Local Notation pc0 := (size (@Merged.initial_memory mt (prog_buffers q))).
Local Notation padc := ((pad_code (code q) (code q')).1).

Hypothesis code_wf_q : forall i t, List.In (i, t) (code q) -> is_code t = true /\ vtag t = Other.

Lemma encode_code_cell_in (cde : @Merged.code mt) (w : mword mt) (a : matom) :
  encode_code cde pc0 w = Some a -> exists i, List.In (i, taga a) cde.
Proof.
  move=> Henc.
  have [n [_ [_ Hfr]]] := encode_code_nth_inv Henc.
  have [i [t [Hnth [Htag _]]]] := encode_code_foldr_nth Hfr.
  exists i; rewrite Htag; exact: (nth_error_In _ _ Hnth).
Qed.

Lemma code_tags_wf_padc_disch : forall w a, encode_code padc pc0 w = Some a -> is_code (taga a).
Proof.
  move=> w a Henc.
  have [i Hin] := encode_code_cell_in Henc.
  by have [Hc _] := pad_code_tags_wf code_wf_q Hin.
Qed.

Lemma code_tags_wf_q_disch : forall w a, encode_code (code q) pc0 w = Some a -> is_code (taga a).
Proof.
  move=> w a Henc.
  have [i Hin] := encode_code_cell_in Henc.
  by have [Hc _] := code_wf_q Hin.
Qed.

Hypothesis Hcount_d : size (proc_split (code q)) = size (proc_split (code q')).
Hypothesis code_noterm_noentry : forall (j : nat) (dflt : Merged.instr * mem_tag),
  j.+1 < size (code q) -> is_term (fst (nth dflt (code q) j)) = false ->
  is_entry (nth dflt (code q) j.+1) = false.

Lemma fallthrough_aligned_disch : forall n i t,
  n.+1 < size (code q) -> nth_error (code q) n = Some (i, t) -> is_term i = false ->
  PaddingCorrect.shift_pos (pad_block_sizes (code q) (code q')) n.+1
  = (PaddingCorrect.shift_pos (pad_block_sizes (code q) (code q')) n).+1.
Proof.
  move=> n i t Hn1 Hnth Hterm.
  apply: shift_pos_succ; first exact: pad_block_sizes_le.
  move=> k Heq.
  rewrite /pad_block_sizes (sumn_take_block_sizes k Hcount_d) in Heq.
  have Hn0 : n < size (code q) by apply: ltnW.
  have Hi : nth (i, t) (code q) n = (i, t).
  { by have := @nth_error_nth_lt _ (code q) n (i, t) Hn0; rewrite Hnth => -[<-]. }
  case: (ltnP k (size (proc_split (code q)))) => Hkc.
  - case: (posnP k) => Hk0.
    + by move: Heq; rewrite Hk0 take0 /= => -[].
    + have Hent := boundary_entry (i, t) Hk0 Hkc.
      rewrite Heq in Hent.
      have Hterm' : is_term (fst (nth (i, t) (code q) n)) = false by rewrite Hi.
      have Hne := code_noterm_noentry Hn1 Hterm'.
      by rewrite Hne in Hent.
  - have Hsat : take k (proc_split (code q)) = proc_split (code q) by apply: take_oversize.
    move: Heq; rewrite Hsat sumn_sizes_flatten proc_split_flatten => Heq.
    by move: Hn1; rewrite Heq ltnn.
Qed.

Lemma main_entry_aligned_disch :
  find (fun '(_, tag) => color tag == Component.main) padc
  = PaddingCorrect.shift_pos (pad_block_sizes (code q) (code q'))
      (find (fun '(_, tag) => color tag == Component.main) (code q)).
Proof.
  have Hall : all (fun b => ~~ has (fun '(_, tag) => color tag == Component.main) b
                       ==> ~~ (fun '(_, tag) => color tag == Component.main) (nop_cell (block_color b)))
                  (proc_split (code q)).
  { apply/(all_nthP [::]) => i Hi. apply/implyP => Hnh.
    have Hbne : 0 < size (nth [::] (proc_split (code q)) i)
      by move/(all_nthP [::]): (proc_split_nonempty_b (code q)) => /(_ i Hi).
    case Eb: (nth [::] (proc_split (code q)) i) => [|[xi xt] xs].
    - by move: Hbne; rewrite Eb.
    - move: Hnh; rewrite Eb /= negb_or => /andP[Hx _].
      by rewrite /nop_cell /block_color /=. }
  rewrite /padc /pad_code /pad_block_sizes.
  by rewrite (@find_align_blocks (fun '(_, tag) => color tag == Component.main)
                 (proc_split (code q)) (proc_split (code q')) Hcount_d Hall)
             proc_split_flatten.
Qed.

Lemma padc_vtag_other : forall w a, encode_code padc pc0 w = Some a -> vtag (taga a) = Other.
Proof.
  move=> w a Henc.
  have [i Hin] := encode_code_cell_in Henc.
  by have [_ Hv] := pad_code_tags_wf code_wf_q Hin.
Qed.

Lemma codeq_vtag_other : forall w a, encode_code (code q) pc0 w = Some a -> vtag (taga a) = Other.
Proof.
  move=> w a Henc.
  have [i Hin] := encode_code_cell_in Henc.
  by have [_ Hv] := code_wf_q Hin.
Qed.

Lemma align_blocks_size_le (bs bs' : seq (@Merged.code mt)) :
  size (align_blocks bs bs').1 <= size (flatten bs) + size (flatten bs').
Proof.
  elim: bs bs' => [|b bs IH] [|b' bs'] //=.
  - by rewrite addn0.
  - case E: (align_blocks bs bs') => [r r'] /=.
    have := IH bs'; rewrite E /= => Hle.
    rewrite size_cat block_pad_size !size_cat. move: Hle; lia.
Qed.

Lemma size_pad_code_le : size padc <= size (code q) + size (code q').
Proof.
  rewrite /padc /pad_code.
  have := align_blocks_size_le (proc_split (code q)) (proc_split (code q')).
  by rewrite !proc_split_flatten.
Qed.

Hypothesis Hbound_sum : pc0 + (size (code q) + size (code q')) < alloc_label.

Lemma Hbound'_disch : pc0 + size padc < alloc_label.
Proof. have := size_pad_code_le; move: Hbound_sum; lia. Qed.

Lemma Hbound_disch : pc0 + size (code q) < alloc_label.
Proof. move: Hbound_sum; lia. Qed.

Lemma word_of_nat_inj_disch : forall a b,
  a < 2 ^ (word_size mt) -> b < 2 ^ (word_size mt) ->
  @word_of_nat (word_size mt) a = word_of_nat b -> a = b.
Proof. move=> a b Ha Hb H. by rewrite -(val_word_of_nat Ha) -(val_word_of_nat Hb) H. Qed.

Variable NC : nat.
Hypothesis alloc_label_lt_NC : alloc_label < 2 ^ (word_size mt - NC).
Hypothesis code_colors_bounded : forall w a,
  encode_code (code q) pc0 w = Some a -> 1 + color (taga a) < 2 ^ NC.
Hypothesis code_last_term : forall n i t,
  n.+1 = size (code q) -> nth_error (code q) n = Some (i, t) -> is_term i = true.
Hypothesis bnz_labels_resolved : forall n r l t,
  nth_error (code q) n = Some (MrBnz r l, t) ->
  exists m, findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code q) = Some m.
Hypothesis jal_labels_resolved : forall n l t,
  nth_error (code q) n = Some (MrJal l, t) ->
  findopt (fun p => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code q) = None ->
  l = alloc_label.
Hypothesis init_noncodeptr : forall w v t,
  unionm (encode_code (code q) pc0) (Merged.initial_memory (prog_buffers q)) w = Some (v @ t) ->
  is_codeptr (vtag t) = false.
Hypothesis main_in_code :
  find (fun '(_, tag) => color tag == Component.main) (code q) < size (code q).
Hypothesis initial_memory_domm : forall b,
  domm (@Merged.initial_memory mt b)
  = fset (map (@word_of_nat (word_size mt)) (List.seq 0 (size (@Merged.initial_memory mt b)))).
Hypothesis initial_memory_not_code : forall (w : mword mt) (v : matom),
  @Merged.initial_memory mt (prog_buffers q) w = Some v -> is_code (taga v) = false.
Hypothesis initial_memory_vtag_other : forall (w : mword mt) (v : matom),
  @Merged.initial_memory mt (prog_buffers q) w = Some v -> vtag (taga v) = Other.

Theorem padding_forward_closed m :
  does_prefix (mergedsem NC q) m -> does_prefix (mergedsem NC (pad_align q q').1) m.
Proof.
  exact: (padding_forward word_of_nat_inj_disch Hcount_d Hbound_disch Hbound'_disch
    code_tags_wf_q_disch code_tags_wf_padc_disch fallthrough_aligned_disch
    code_last_term bnz_labels_resolved alloc_label_lt_NC code_colors_bounded
    jal_labels_resolved init_noncodeptr main_in_code initial_memory_domm
    initial_memory_not_code initial_memory_vtag_other main_entry_aligned_disch).
Qed.

Theorem padding_backward_closed m :
  does_prefix (mergedsem NC (pad_align q q').1) m -> does_prefix (mergedsem NC q) m.
Proof.
  exact: (padding_backward word_of_nat_inj_disch Hcount_d Hbound_disch Hbound'_disch
    code_tags_wf_q_disch code_tags_wf_padc_disch fallthrough_aligned_disch
    code_last_term bnz_labels_resolved alloc_label_lt_NC code_colors_bounded
    jal_labels_resolved init_noncodeptr main_in_code initial_memory_domm
    initial_memory_not_code initial_memory_vtag_other main_entry_aligned_disch).
Qed.

End AlignDischarge.
