(** * T2M step-simulation diagrams (part 1): per-opcode lemmas taking
    one T step to one me step with [match_states] re-established —
    shared statics, silent 1:1 opcodes, and control-flow diagrams. *)

Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Maps.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div fintype ssrint seq path.
From mathcomp Require Import ssralg intdiv zify.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.WordExtra.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.OffsetWord.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.EncodeCode.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import S2T.TSem.

Require Import Common.Linking.
Require Import CompCert.Events.
Require Import MicroPolicies.Recomposition.BufferShape.

Require Import T2M.MPos.
Require Import T2M.MPosT.
Require Import T2M.MMem.
Require Import T2M.MMemBase.
Require Import T2M.MInj.
Require Import T2M.MMatch.
Require T2M.MDefs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* Prove in an empty context: a `2 ^ literal` nat hypothesis can make a
   later `done`/`assumption` evaluate 2^32 in unary. *)
Lemma expn_ws_32 : (2 : nat) ^ word_size mt = 2 ^ 32.
Proof. by rewrite word_size_mt. Qed.

Lemma expn_ws_31 : (2 : nat) ^ (word_size mt).-1 = 2 ^ 31.
Proof. by have -> : (word_size mt).-1 = 31 by rewrite word_size_mt. Qed.

Lemma inc_offset (p : Pointer.t) :
  Pointer.offset (Pointer.inc p) = BinInt.Z.add (Pointer.offset p) 1.
Proof. by case: p => [[? ?] ?]. Qed.

(* a store at an EXISTING address preserves the syscall-entry gap *)
Lemma gap_setm (mmem : {fmap mword mt -> atom (mword mt) mem_tag})
    (w : mword mt) (mc0 x : atom (mword mt) mem_tag) :
  mmem (@word_of_nat (word_size mt) Merged.alloc_label) = None ->
  mmem w = Some mc0 ->
  setm mmem w x (@word_of_nat (word_size mt) Merged.alloc_label) = None.
Proof.
move=> Hgap Hw.
rewrite setmE.
case: (altP (@word_of_nat (word_size mt) Merged.alloc_label =P w))
  => [E|//].
by rewrite -E Hgap in Hw.
Qed.

(* [setm] on an EXISTING key preserves the domain *)
Lemma domm_setm_pres (mmem : {fmap mword mt -> atom (mword mt) mem_tag})
    (k : mword mt) (v0 v : atom (mword mt) mem_tag) :
  mmem k = Some v0 ->
  domm (setm mmem k v) = domm mmem.
Proof.
move=> Hk.
apply/eq_fset => x.
rewrite domm_set in_fsetU1.
case: (altP (x =P k)) => [->|_] //=.
by rewrite mem_domm Hk.
Qed.

(* an element of a strictly-sorted list is bounded by its last *)
Lemma sorted_in_leq_last (T : ordType) (x0 x : T) (s : seq T) :
  sorted (@Ord.lt T) s -> x \in s -> Ord.leq x (last x0 s).
Proof.
elim: s x0 => [|a s IH] x0 //= Hp.
rewrite inE => /orP[/eqP ->|Hx].
- case E: s Hp => [|b s'] /=.
  + move=> _. exact: Ord.leqxx.
  + move=> Hp.
    have Hp' : path Ord.lt a (b :: s') := Hp.
    have Hall := order_path_min (@Ord.lt_trans T) Hp'.
    have Hlt := allP Hall _ (mem_last b s').
    exact: Ord.ltW Hlt.
- exact: (IH a (path_sorted Hp) Hx).
Qed.

(* the allocator's bump pointer dominates every mapped in-region
   address: [last] of the sorted, filtered domain is its maximum *)
Lemma domm_filter_last_max
    (m : {fmap mword mt -> atom (mword mt) mem_tag})
    (p : pred (mword mt)) (dflt w : mword mt) :
  w \in domm m -> p w ->
  Ord.leq w (last dflt (filter p (domm m))).
Proof.
move=> Hw Hp.
have Hs : sorted (@Ord.lt _) (\val (domm m)) := valP (domm m).
have Hsf : sorted (@Ord.lt _) (filter p (\val (domm m))).
{ exact: (sorted_filter (@Ord.lt_trans _) _ Hs). }
apply: sorted_in_leq_last Hsf _.
by rewrite mem_filter Hp /=.
Qed.

(* the word successor the me machine computes at every fall-through *)
Lemma addw_onew (n : nat) :
  addw (@word_of_nat (word_size mt) n) onew
  = @word_of_nat (word_size mt) n.+1.
Proof.
have -> : (onew : mword mt) = @word_of_nat (word_size mt) 1 by [].
rewrite /word_of_nat as_word_addwD.
congr word.as_word. by lia.
Qed.

Section Diagrams.

Variable NC : nat.

Variables L P C : nat.
Variables pra prb : Intermediate.program.
Variable PB : NMap {fmap Block.id -> nat + seq value}.
Variable PI : Program.interface.

Local Notation cdeW :=
  (Transitional.intermediate_to_transitional_gen PI
     (Intermediate.program_link pra prb)).
Local Notation codeW :=
  (compiler_code L P C PB PI pra ++ compiler_code L P C PB PI prb).
Local Notation pc0 := (size (initial_memory (mt := mt) PB)).
Local Notation pc_relW := (pc_rel L P C pra prb PB PI).
Local Notation match_statesW := (match_states L P C pra prb PB PI).
Local Notation cmapWW := (cmapW L P C pra prb PB PI).
Local Notation mregs_relW := (mregs_rel L P C pra prb PB PI).
Local Notation reg_syncedW := (reg_synced L P C pra prb PB PI).

Hypothesis Hbound : pc0 + size codeW < 2 ^ word_size mt.

(* the canonical joint buffer map, and side well-formedness (used by the
   CONST diagram to transport the per-side [imm_fits] facts to PB) *)
Hypothesis HPB :
  PB = Intermediate.prog_buffers (Intermediate.program_link pra prb).
Hypothesis Hwfa : Intermediate.well_formed_program pra.
Hypothesis Hwfb : Intermediate.well_formed_program prb.
Hypothesis Hlinkable :
  linkable (Intermediate.prog_interface pra) (Intermediate.prog_interface prb).
(* the link fits the 15-bit / alloc_label window (from [link_fits]) *)
Hypothesis Hsmall :
  size (linearize_bufs PB) + size codeW < Merged.alloc_label.
(* the per-side immediate statics *)
Hypothesis Himm_a : MDefs.imm_fits pra.
Hypothesis Himm_b : MDefs.imm_fits prb.

(* ================================================================== *)
(* 1. Code cells are code-tagged in the owner's colour.               *)
(* ================================================================== *)

Lemma side_cell_props (pr : Intermediate.program) c cseg q
    (x : Transitional.instr * mem_tag) :
  Transitional.intermediate_to_transitional_gen PI pr c = Some cseg ->
  List.nth_error cseg q = Some x ->
  is_code x.2 = true /\ color x.2 = c.
Proof.
move=> Hc Hq.
have HIn := List.nth_error_In _ _ Hq.
move: Hc; rewrite i2t_getm.
case E: (Intermediate.prog_procedures pr c) => [Cp|] //= [Ecs]; subst cseg.
have [Cp' [Pid [_ [_ Hcell]]]] := proj1 (lin_comp_In _ _ _ _) HIn.
have := proj1 (lin_proc_In _ _ _ _ _) Hcell.
case=> [-> | [mi [_ ->]]] /=.
- by split.
- case: mi => * /=; try by split.
  by case: (Nat.eqb _ _) => /=; split.
Qed.

Lemma tcell_props c cseg q (x : Transitional.instr * mem_tag) :
  cdeW c = Some cseg ->
  List.nth_error cseg q = Some x ->
  is_code x.2 = true /\ color x.2 = c.
Proof.
case Hside: (c \in domm (Intermediate.prog_procedures pra)) => Hc Hq.
- move: Hc; rewrite (cdeW_left prb PI Hside) => Hc.
  exact: side_cell_props Hc Hq.
- move: Hc.
  rewrite (cdeW_right prb PI (negbT Hside)) => Hc.
  exact: side_cell_props Hc Hq.
Qed.

(* [check_pc]'s content, extracted through the boolean [has_next] *)
Lemma check_pc_next (cde0 : Transitional.code) pc1 tg1 :
  Transitional.check_pc cde0 pc1 tg1 ->
  exists i' tni,
    Transitional.executing cde0 (Pointer.inc pc1) i' tni
      (Pointer.component (Pointer.inc pc1)).
Proof.
move=> /TS.has_nextPn.
rewrite /TS.has_next.
case E: (cde0 (Pointer.component (Pointer.inc pc1))) => [C_code|] //.
case E0: (BinInt.Z.leb 0 (Pointer.offset (Pointer.inc pc1))) => //.
case E1: (nth_error C_code (BinInt.Z.to_nat (Pointer.offset (Pointer.inc pc1))))
  => [[i2 tni2]|] // _.
exists i2, tni2, C_code.
split=> //.
split=> //.
split.
- move: E0 => /Z.leb_le. by lia.
- exact: E1.
Qed.

(* the shape [executing] always provides *)
Lemma executing_props tpc i tg c :
  Transitional.executing cdeW tpc i tg c ->
  [/\ c = Pointer.component tpc, is_code tg = true & color tg = c].
Proof.
case=> C_code [Hcomp [Hcde [Hoff Hnth]]].
have [Hic Hcol] := tcell_props Hcde Hnth.
by rewrite Hcomp.
Qed.

(* ================================================================== *)
(* 2. The fall-through successor.                                     *)
(* ================================================================== *)

Lemma take_nth_error (A : Type) (l : seq A) q (x : A) :
  List.nth_error l q = Some x ->
  take q.+1 l = rcons (take q l) x.
Proof.
elim: l q => [|a l IH] [|q] /=.
- by move=> [].
- by move=> [].
- by move=> [->]; rewrite take0.
- by move=> /IH ->.
Qed.

Lemma tpos_next (pr : Intermediate.program) c cseg q
    (x : Transitional.instr * mem_tag) :
  List.nth_error cseg q = Some x ->
  tpos PI pr c cseg q.+1 = tpos PI pr c cseg q + texp_size x.1.
Proof.
move=> Hq.
rewrite /tpos -addnA; congr addn.
by rewrite (take_nth_error Hq) /tseg_size map_rcons -cats1 sumn_cat /= addn0.
Qed.

(** The fall-through lemma for every 1-cell opcode: the me pc is
    [pos + pc0], the successor address [addw _ onew] holds the successor
    cell (tag [tni] for [check_belong]), and [pc_rel] holds at [Pointer.inc]. *)
Lemma silent_next (mmem : {fmap mword mt -> matom})
    (tpc : Pointer.t) (w : mword mt)
    (i : Transitional.instr) (tg : mem_tag)
    (i' : Transitional.instr) (tg' : mem_tag) cell' :
  texp_size i = 1 ->
  (forall w' v, encode_code codeW pc0 w' = Some v -> mmem w' = Some v) ->
  Transitional.executing cdeW tpc i tg (Pointer.component tpc) ->
  Transitional.executing cdeW (Pointer.inc tpc) i' tg'
    (Pointer.component tpc) ->
  pc_relW tpc w ->
  List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB) (i', tg')) 0
  = Some cell' ->
  exists pos (v' : matom),
    [/\ w = word_of_nat (pos + pc0),
        addw w onew = word_of_nat ((pos + pc0).+1),
        mmem (addw w onew) = Some v',
        taga v' = cell'.2
      & pc_relW (Pointer.inc tpc) (addw w onew)].
Proof.
move=> Htexp Hcode Hex Hex' Hpc Hcell'.
have Hcomp' : Pointer.component (Pointer.inc tpc) = Pointer.component tpc.
{ exact: Pointer.inc_preserves_component. }
have Hnext : exists pos,
    [/\ w = word_of_nat (pos + pc0)
      & pc_relW (Pointer.inc tpc) (word_of_nat ((pos + 1) + pc0))].
{ case: Hpc => cseg Hside Hseg Hle Hw.
  -
    have Hnth : List.nth_error cseg
                  (BinInt.Z.to_nat (Pointer.offset tpc)) = Some (i, tg).
    { case: Hex => C_code [_ [Hcde [_ Hn]]].
      move: Hcde. rewrite (cdeW_left prb PI Hside) Hseg.
      by move=> [->]. }
    exists (tpos PI pra (Pointer.component tpc) cseg
              (BinInt.Z.to_nat (Pointer.offset tpc))).
    split; first exact: Hw.
    apply: (@PCLeft _ _ _ _ _ _ _ _ _ cseg).
    + by rewrite Hcomp'.
    + by rewrite Hcomp'.
    + rewrite inc_offset. by lia.
    + have Hoff' : BinInt.Z.to_nat (Pointer.offset (Pointer.inc tpc))
                   = (BinInt.Z.to_nat (Pointer.offset tpc)).+1.
      { rewrite inc_offset. by lia. }
      congr word_of_nat.
      rewrite Hcomp' Hoff' (tpos_next _ _ Hnth) Htexp. by lia.
  -
    have Hnth : List.nth_error cseg
                  (BinInt.Z.to_nat (Pointer.offset tpc)) = Some (i, tg).
    { case: Hex => C_code [_ [Hcde [_ Hn]]].
      move: Hcde. rewrite (cdeW_right prb PI Hside) Hseg.
      by move=> [->]. }
    exists (size (compiler_code L P C PB PI pra)
            + tpos PI prb (Pointer.component tpc) cseg
                (BinInt.Z.to_nat (Pointer.offset tpc))).
    split; first exact: Hw.
    apply: (@PCRight _ _ _ _ _ _ _ _ _ cseg).
    + by rewrite Hcomp'.
    + by rewrite Hcomp'.
    + rewrite inc_offset. by lia.
    + have Hoff' : BinInt.Z.to_nat (Pointer.offset (Pointer.inc tpc))
                   = (BinInt.Z.to_nat (Pointer.offset tpc)).+1.
      { rewrite inc_offset. by lia. }
      congr word_of_nat.
      rewrite Hcomp' Hoff' (tpos_next _ _ Hnth) Htexp. by lia. }
case: Hnext => pos [Hw Hpc'].
have Htexp' : 0 < texp_size i' by case: i' {Hex' Hcell'}.
have Hfetch := match_fetch Hbound Hcode
                 (tpc := Pointer.inc tpc) (w := word_of_nat ((pos + 1) + pc0))
                 _ Hpc' Hcell'.
move: Hfetch.
have Hex'' : Transitional.executing cdeW (Pointer.inc tpc) i' tg'
               (Pointer.component (Pointer.inc tpc)).
{ by rewrite Hcomp'. }
move=> /(_ Hex'') [pos' [v' [Hwpos' [Hv' [Htag _]]]]].
exists pos, v'.
have Haddr : addw w onew = word_of_nat ((pos + pc0).+1).
{ rewrite Hw. exact: addw_onew. }
have Epos1 : (pos + 1) + pc0 = (pos + pc0).+1 by lia.
split.
- exact: Hw.
- exact: Haddr.
- rewrite Haddr -Epos1. exact: Hv'.
- exact: Htag.
- rewrite Haddr -Epos1. exact: Hpc'.
Qed.

(* ================================================================== *)
(* 3. The first diagram: Nop.                                         *)
(* ================================================================== *)

Lemma cell_exp_snd cseg' (i' : Transitional.instr) (tg' : mem_tag) k cell :
  List.nth_error
    (cell_exp (can_make L P C) (can_upd L) cseg' (i', tg')) k = Some cell ->
  cell.2 = tg'.
Proof.
rewrite /cell_exp => H.
have [x [_ ->]] := nth_error_map_inv H.
by [].
Qed.

Lemma sim_nop (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (tpc : Pointer.t) (tpct : Transitional.pc_tag)
    (ms : @Symbolic.state mt lrc_tags unit)
    (tg : mem_tag) (c : Component.id) :
  match_statesW amap tmem tregs tpc tpct ms ->
  Transitional.executing cdeW tpc TrNop tg c ->
  Transitional.check_pc cdeW tpc tg ->
  exists ms',
    [/\ step_me (NC := NC) ms ms' None,
        match_statesW amap tmem tregs (Pointer.inc tpc) tpct ms',
        domm (Symbolic.mem ms') = domm (Symbolic.mem ms),
        Symbolic.regs ms' = Symbolic.regs ms
      & Symbolic.mem ms' = Symbolic.mem ms].
Proof.
move=> Hm Hex0 Hcp.
have [Ec Hic Hcol] := executing_props Hex0.
subst c.
have [i' [tni Hex1]] := check_pc_next Hcp.
rewrite Pointer.inc_preserves_component in Hex1.
have [_ Etni_ic Etni_col] := executing_props Hex1.
case: tg Hex0 Hic Hcol {Hcp} => vt0 col0 ent0 isc0 Hex0 /= Hic Hcol.
subst isc0 col0.
case: tni Hex1 Etni_ic Etni_col => vt1 col1 ent1 isc1 Hex1 /= Etni_ic Etni_col.
subst isc1 col1.
set tg := MTag vt0 (Pointer.component tpc) ent0 true.
set tni := MTag vt1 (Pointer.component tpc) ent1 true.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB) (TrNop, tg)) 0
  = Some (MrNop, tg) by [].
have [cell' Hcell'] : exists cell',
    List.nth_error
      (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB) (i', tni)) 0
    = Some cell'.
{ apply: nth_error_Some_ex.
  rewrite lin_size_length size_cell_exp. by case: i' {Hex1}. }
have Ecell2 : cell'.2 = tni := cell_exp_snd Hcell'.
case: Hm => Hpc Hpct Hregs Hmem Hcode Hsys Hgap.
have [pos [v [Hwv Hv Htagv Hdec _]]] :=
  match_fetch Hbound Hcode Hex0 Hpc Hcell.
have [pos2 [v' [Hw2 Haddr Hv' Htagv' Hpc']]] :=
  silent_next (i := TrNop) (erefl _) Hcode Hex0 Hex1 Hpc Hcell'.
have [rc Hrc] := mregs_rel_lookup R_COM Hregs.
rewrite /Symbolic.pct in Hpct.
exists (@Symbolic.State mt lrc_tags unit
          (Symbolic.mem ms) (Symbolic.regs ms)
          (addw (Symbolic.pcv ms) onew)@(taga (Symbolic.pc ms))
          (Symbolic.internal ms)).
split.
-
  rewrite /step_me.
  apply: (@Symbolic.step_nop _ _ _ _ _ _ _ _ _
            (Symbolic.mem ms) (Symbolic.regs ms)
            (Symbolic.pcv ms) (taga (Symbolic.pc ms))
            (vala v) (taga v) (Symbolic.internal ms)).
  + exact: Symbolic.state_eta.
  + by case: (v) Hv.
  + move: Hdec => /= Hdec. exact: Hdec.
  +
    rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc.
    rewrite /Symbolic.pcv in Hv'.
    rewrite Hv'.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt)
              = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
    rewrite Hrc /=.
    rewrite /Merged.transfer /Merged.instr_rules.
    rewrite Hpct Htagv /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite /check_belong /belong Htagv' Ecell2 /= eqxx /=.
    by [].
-
  constructor.
  + exact: Hpc'.
  +
    rewrite /Symbolic.pct /= Hpct.
    by rewrite Pointer.inc_preserves_component.
  + exact: Hregs.
  + exact: Hmem.
  + exact: Hcode.
  + exact: Hsys.
  + exact: Hgap.
- exact: erefl.
- exact: erefl.
- exact: erefl.
Qed.

(* [Label] is the same diagram: both [MrLabel] spellings decode to Nop. *)
Lemma sim_label (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (tpc : Pointer.t) (tpct : Transitional.pc_tag)
    (ms : @Symbolic.state mt lrc_tags unit)
    (tg : mem_tag) (c : Component.id) (l : Transitional.plabel) :
  match_statesW amap tmem tregs tpc tpct ms ->
  Transitional.executing cdeW tpc (TrLabel l) tg c ->
  Transitional.check_pc cdeW tpc tg ->
  exists ms',
    [/\ step_me (NC := NC) ms ms' None,
        match_statesW amap tmem tregs (Pointer.inc tpc) tpct ms',
        domm (Symbolic.mem ms') = domm (Symbolic.mem ms),
        Symbolic.regs ms' = Symbolic.regs ms
      & Symbolic.mem ms' = Symbolic.mem ms].
Proof.
move=> Hm Hex0 Hcp.
have [Ec Hic Hcol] := executing_props Hex0.
subst c.
have [i' [tni Hex1]] := check_pc_next Hcp.
rewrite Pointer.inc_preserves_component in Hex1.
have [_ Etni_ic Etni_col] := executing_props Hex1.
case: tg Hex0 Hic Hcol {Hcp} => vt0 col0 ent0 isc0 Hex0 /= Hic Hcol.
subst isc0 col0.
case: tni Hex1 Etni_ic Etni_col => vt1 col1 ent1 isc1 Hex1 /= Etni_ic Etni_col.
subst isc1 col1.
set tg := MTag vt0 (Pointer.component tpc) ent0 true.
set tni := MTag vt1 (Pointer.component tpc) ent1 true.
have [ml Hcell] : exists ml,
    List.nth_error
      (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
         (TrLabel l, tg)) 0
    = Some (MrLabel ml, tg).
{ by case: l {Hex0} => [lbl|pl]; eexists. }
have [cell' Hcell'] : exists cell',
    List.nth_error
      (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB) (i', tni)) 0
    = Some cell'.
{ apply: nth_error_Some_ex.
  rewrite lin_size_length size_cell_exp. by case: i' {Hex1}. }
have Ecell2 : cell'.2 = tni := cell_exp_snd Hcell'.
case: Hm => Hpc Hpct Hregs Hmem Hcode Hsys Hgap.
have [pos [v [Hwv Hv Htagv Hdec _]]] :=
  match_fetch Hbound Hcode Hex0 Hpc Hcell.
have [pos2 [v' [Hw2 Haddr Hv' Htagv' Hpc']]] :=
  silent_next (i := TrLabel l) (erefl _) Hcode Hex0 Hex1 Hpc Hcell'.
have [rc Hrc] := mregs_rel_lookup R_COM Hregs.
rewrite /Symbolic.pct in Hpct.
exists (@Symbolic.State mt lrc_tags unit
          (Symbolic.mem ms) (Symbolic.regs ms)
          (addw (Symbolic.pcv ms) onew)@(taga (Symbolic.pc ms))
          (Symbolic.internal ms)).
split.
- rewrite /step_me.
  apply: (@Symbolic.step_nop _ _ _ _ _ _ _ _ _
            (Symbolic.mem ms) (Symbolic.regs ms)
            (Symbolic.pcv ms) (taga (Symbolic.pc ms))
            (vala v) (taga v) (Symbolic.internal ms)).
  + exact: Symbolic.state_eta.
  + by case: (v) Hv.
  + move: Hdec => /= Hdec. exact: Hdec.
  + rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc.
    rewrite /Symbolic.pcv in Hv'.
    rewrite Hv'.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt)
              = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
    rewrite Hrc /=.
    rewrite /Merged.transfer /Merged.instr_rules.
    rewrite Hpct Htagv /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite /check_belong /belong Htagv' Ecell2 /= eqxx /=.
    by [].
- constructor.
  + exact: Hpc'.
  + rewrite /Symbolic.pct /= Hpct.
    by rewrite Pointer.inc_preserves_component.
  + exact: Hregs.
  + exact: Hmem.
  + exact: Hcode.
  + exact: Hsys.
  + exact: Hgap.
- exact: erefl.
- exact: erefl.
- exact: erefl.
Qed.

(* ================================================================== *)
(* 4. CONST: the immediate is faithful.                               *)
(* ================================================================== *)

(* a [TrConst] cell comes from an [IConst] of the side program *)
Lemma const_origin (pr : Intermediate.program) c cseg q
    (v : imvalue) (r : register) (tg : mem_tag) :
  Transitional.intermediate_to_transitional_gen PI pr c = Some cseg ->
  List.nth_error cseg q = Some (TrConst v r, tg) ->
  exists Cprocs Pid Pcode n,
    [/\ Intermediate.prog_procedures pr c = Some Cprocs,
        Cprocs Pid = Some Pcode
      & List.nth_error Pcode n = Some (IConst v r)].
Proof.
move=> Hc Hq.
have HIn := List.nth_error_In _ _ Hq.
move: Hc; rewrite i2t_getm.
case E: (Intermediate.prog_procedures pr c) => [Cp|] //= [Ecs]; subst cseg.
have [Cp' [Pid [Ecp [HPid Hcell]]]] := proj1 (lin_comp_In _ _ _ _) HIn.
move: Ecp; rewrite E => -[?]; subst Cp'.
have := proj1 (lin_proc_In _ _ _ _ _) Hcell.
case=> [Ehd | [mi [HmIn Emi]]].
- by congruence.
- have Emi' : mi = IConst v r.
  { move: Emi; rewrite /Transitional.instr_to_transitional.
    case: mi {HmIn}
      => [|l0|v0 r0|? ?|? ? ? ?|? ?|? ?|? ?|? ?| |l0|c' P'| |] /= Emi;
      try congruence.
    by case: (Nat.eqb c c') Emi => Emi; congruence. }
  subst mi.
  move: HmIn; rewrite /proc_code E /=.
  case ECp: (Cp Pid) => [Pcode|] /=; last by [].
  move=> HIn'.
  have [n Hn] := List.In_nth_error _ _ HIn'.
  by exists Cp, Pid, Pcode, n.
Qed.

(* the [imm_fits] fact at an executing [TrConst], with buffers already
   transported to the JOINT map PB *)
Lemma const_fact (tpc : Pointer.t) (v : imvalue) (r : register)
    (tg : mem_tag) :
  Transitional.executing cdeW tpc (TrConst v r) tg (Pointer.component tpc) ->
  match v with
  | IInt z => MDefs.imm_ok z
  | IPtr p =>
      [/\ Pointer.component p = Pointer.component tpc,
          BinInt.Z.le 0 (Pointer.offset p)
        & exists bufs bf,
            [/\ PB (Pointer.component p) = Some bufs,
                bufs (Pointer.block p) = Some bf
              & BinInt.Z.to_nat (Pointer.offset p) < bsize bf]]
  end.
Proof.
case=> C_code [Hcomp [Hcde [Hoff Hnth]]].
case Hside: (Pointer.component tpc
             \in domm (Intermediate.prog_procedures pra)).
-
  move: Hcde; rewrite (cdeW_left prb PI Hside) => Hcde.
  have [Cp [Pid [Pcode [n [Ep Epp Hn]]]]] := const_origin Hcde Hnth.
  have := Himm_a Ep Epp Hn.
  case: v {Hnth Hn} => [z|p] //.
  move=> [Hpc Hle [bufs [bf [Hbufs [Hbf Hsz]]]]].
  split=> //.
  exists bufs, bf.
  split=> //.
  rewrite HPB /= unionmE.
  by rewrite Hbufs.
-
  move: Hcde; rewrite (cdeW_right prb PI (negbT Hside)) => Hcde.
  have [Cp [Pid [Pcode [n [Ep Epp Hn]]]]] := const_origin Hcde Hnth.
  have := Himm_b Ep Epp Hn.
  case: v {Hnth Hn} => [z|p] //.
  move=> [Hpc Hle [bufs [bf [Hbufs [Hbf Hsz]]]]].
  split=> //.
  exists bufs, bf.
  split=> //.
  have Hnb : Intermediate.prog_buffers pra (Pointer.component p) = None.
  { apply/dommPn.
    rewrite -(Intermediate.wfprog_defined_buffers Hwfa)
            (Intermediate.wfprog_defined_procedures Hwfa).
    by rewrite Hpc Hside. }
  rewrite HPB /= unionmE Hnb.
  by rewrite Hbufs.
Qed.

(* the expanded CONST immediate lands, RELATED, in the register file *)
Lemma vrel_const (amap : amap_t) (tmem : Transitional.Memory.t)
    (tpc : Pointer.t) (v : imvalue) (r : register) (tg : mem_tag) :
  amap_ok PB amap tmem ->
  Transitional.executing cdeW tpc (TrConst v r) tg (Pointer.component tpc) ->
  vrel amap (imm_to_val v)
    (@swcast (imm_size mt) (word_size mt)
       (convert_value (memory_lengths PB) v)).
Proof.
move=> Haok Hex.
have Hfact := const_fact Hex.
have H1415 : Merged.alloc_label < 2 ^ imm_size mt.
{ rewrite /Merged.alloc_label imm_size_mt. by rewrite ltn_exp2l. }
case: v Hfact {Hex} => [z|p] Hfact.
-
  case: Hfact => Hlo Hhi.
  have Hb15 : Z.of_nat (2 ^ 15) = BinInt.Z.pow 2 15 by rewrite expn_Zpow.
  have Hz : z = Z.of_nat (BinInt.Z.to_nat z) by lia.
  have Hn15 : BinInt.Z.to_nat z < 2 ^ imm_size mt.
  { rewrite imm_size_mt. by lia. }
  have Himm : convert_value (memory_lengths PB) (IInt z)
              = @word_of_nat (imm_size mt) (BinInt.Z.to_nat z).
  { by rewrite /convert_value {1}Hz encode_int_of_nat. }
  apply: VRInt.
  rewrite /wrepr Himm (swcast_word_of_nat_small Hn15).
  have Hk : 0 < word_size mt by rewrite word_size_mt.
  have Hn31 : BinInt.Z.to_nat z < 2 ^ (word_size mt).-1.
  { rewrite word_size_mt.
    have H2 : (2:nat) ^ 15 < 2 ^ 31 by rewrite ltn_exp2l.
    move: Hn15; rewrite imm_size_mt => Hn15'.
    exact: (ltn_trans Hn15' H2). }
  rewrite (int_of_word_as_word_pos Hk Hn31) /=.
  by lia.
-
  case: Hfact => Hpcmp Hle [bufs [bf [Hbufs Hbf Hsz]]].
  have [m [Hm Hmb]] := memory_lengths_bl_base Hbufs Hbf.
  have Himm : convert_value (memory_lengths PB) (IPtr p)
              = @word_of_nat (imm_size mt)
                  (bl_base PB (Pointer.component p) (Pointer.block p)
                   + BinInt.Z.to_nat (Pointer.offset p)).
  { rewrite /convert_value Hm /= Hmb /=.
    congr word_of_nat. by lia. }
  have Hbnd : bl_base PB (Pointer.component p) (Pointer.block p)
              + BinInt.Z.to_nat (Pointer.offset p) < 2 ^ imm_size mt.
  { have Hlin := size_linearize_buf Hbufs Hbf.
    have Htot := base_len_leq_total Hbufs Hbf.
    move: Hsmall. rewrite /Merged.alloc_label imm_size_mt in H1415 *.
    by lia. }
  case: p Hpcmp Hle Hbufs Hbf Hsz Himm Hbnd {Hm Hmb}
    => [[cp bp] op] /= Hpcmp Hle Hbufs Hbf Hsz Himm Hbnd.
  apply: (@VRPtr _ _ _ _ _ (bl_base PB cp bp)).
  + exact: (aok_static Haok Hbufs Hbf).
  + exact: Hle.
  + by rewrite Himm (swcast_word_of_nat_small Hbnd).
Qed.

(* the two (identical) register tables, bridged pointwise *)
Lemma to_natE (r : register) :
  Transitional.Register.to_nat r = Intermediate.Register.to_nat r.
Proof. by case: r. Qed.

(* record-eta for [tvrel], needed at rewrites *)
Lemma tvrel_eta (amap : amap_t) (tval : Transitional.tvalue) (w : mword mt) :
  tvrel cmapWW amap tval w ->
  tvrel cmapWW amap
    (Transitional.MVal (Transitional.tvtag tval) (Transitional.val tval)) w.
Proof. by case: tval. Qed.

(* re-tagging with the invalidate-if-address discipline preserves the
   relation: Invalidated values are unconstrained, and non-address tags
   are [Other], where the data relation carries over *)
Lemma tvrel_retag (amap : amap_t) (tval : Transitional.tvalue)
    (w : mword mt) :
  tvrel cmapWW amap tval w ->
  tvrel cmapWW amap
    (Transitional.MVal
       (moved_tag (Transitional.tvtag tval))
       (Transitional.val tval)) w.
Proof.
case: tval => vt v.
rewrite /tvrel /=.
by case: vt.
Qed.

(* register updates: setm on both sides, keys aligned *)
Lemma mregs_rel_set (amap : amap_t) (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt}) (r : register)
    (tv : value) (vt : value_tag) (w : mword mt) :
  mregs_relW amap tregs mregs ->
  tvrel cmapWW amap (Transitional.MVal vt tv) w ->
  mregs_relW amap (Transitional.Register.set r tv vt tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r)) (Atom w vt)).
Proof.
move=> Hrel Hv r''.
have Hlt : forall r0 : register, Intermediate.Register.to_nat r0 < 32
  by case.
rewrite /reg_synced setmE
        (won_eqE (small_lt_reg (Hlt r'')) (small_lt_reg (Hlt r))).
rewrite /Transitional.Register.set /Transitional.Register.get setmE !to_natE.
case: (altP (Intermediate.Register.to_nat r''
             =P Intermediate.Register.to_nat r)) => [Etn|Hne] /=.
- left. exists (Atom w vt). by split.
- case: (Hrel r'') => [[ra'' [Hra'' Hv'' Ht'']]|[ra'' [Hra'' Hu'' Ht'']]].
  + left. exists ra''. by split.
  + right. exists ra''. by split.
Qed.

(* the clobbered-write mirror: T writes [tUndef] while me keeps a
   stale word under [Invalidated] — the register lands in the
   clobbered arm (loads of [clobcell] cells produce exactly this) *)
Lemma mregs_rel_set_clob (amap : amap_t)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt}) (r : register) (w : mword mt) :
  mregs_relW amap tregs mregs ->
  mregs_relW amap (Transitional.Register.set r Undef Other tregs)
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r))
       (Atom w Invalidated)).
Proof.
move=> Hrel r''.
have Hlt : forall r0 : register, Intermediate.Register.to_nat r0 < 32
  by case.
rewrite /reg_synced setmE
        (won_eqE (small_lt_reg (Hlt r'')) (small_lt_reg (Hlt r))).
rewrite /Transitional.Register.set /Transitional.Register.get setmE !to_natE.
case: (altP (Intermediate.Register.to_nat r''
             =P Intermediate.Register.to_nat r)) => [Etn|Hne] /=.
- right. exists (Atom w Invalidated). by split.
- case: (Hrel r'') => [[ra'' [Hra'' Hv'' Ht'']]|[ra'' [Hra'' Hu'' Ht'']]].
  + left. exists ra''. by split.
  + right. exists ra''. by split.
Qed.

Lemma sim_const (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (tpc : Pointer.t) (tpct : Transitional.pc_tag)
    (ms : @Symbolic.state mt lrc_tags unit)
    (tg : mem_tag) (c : Component.id) (v : imvalue) (r : register) :
  match_statesW amap tmem tregs tpc tpct ms ->
  Transitional.executing cdeW tpc (TrConst v r) tg c ->
  Transitional.check_pc cdeW tpc tg ->
  exists ms' w,
    [/\ step_me (NC := NC) ms ms' None,
        match_statesW amap tmem
          (Transitional.Register.set r (imm_to_val v) Other tregs)
          (Pointer.inc tpc) tpct ms',
        domm (Symbolic.mem ms') = domm (Symbolic.mem ms),
        tvrel cmapWW amap
          (Transitional.MVal Other (imm_to_val v)) w
      & Symbolic.regs ms'
        = setm (Symbolic.regs ms)
            (@word_of_nat (reg_field_size mt)
               (Intermediate.Register.to_nat r)) (Atom w Other) /\
        Symbolic.mem ms' = Symbolic.mem ms].
Proof.
move=> Hm Hex0 Hcp.
have [Ec Hic Hcol] := executing_props Hex0.
subst c.
have Hvrel := vrel_const (mj_amap (mm_mem Hm)) Hex0.
have [i' [tni Hex1]] := check_pc_next Hcp.
rewrite Pointer.inc_preserves_component in Hex1.
have [_ Etni_ic Etni_col] := executing_props Hex1.
case: tg Hex0 Hic Hcol {Hcp} => vt0 col0 ent0 isc0 Hex0 /= Hic Hcol.
subst isc0 col0.
case: tni Hex1 Etni_ic Etni_col => vt1 col1 ent1 isc1 Hex1 /= Etni_ic Etni_col.
subst isc1 col1.
set tg := MTag vt0 (Pointer.component tpc) ent0 true.
set tni := MTag vt1 (Pointer.component tpc) ent1 true.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrConst v r, tg)) 0
  = Some (MrConst (convert_value (memory_lengths PB) v) r, tg) by [].
have [cell' Hcell'] : exists cell',
    List.nth_error
      (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB) (i', tni)) 0
    = Some cell'.
{ apply: nth_error_Some_ex.
  rewrite lin_size_length size_cell_exp. by case: i' {Hex1}. }
have Ecell2 : cell'.2 = tni := cell_exp_snd Hcell'.
case: Hm => Hpc Hpct Hregs Hmem Hcode Hsys Hgap.
have [pos [w0 [Hwv Hv Htagv Hdec _]]] :=
  match_fetch Hbound Hcode Hex0 Hpc Hcell.
have [pos2 [v' [Hw2 Haddr Hv' Htagv' Hpc']]] :=
  silent_next (i := TrConst v r) (erefl _) Hcode Hex0 Hex1 Hpc Hcell'.
have [rc Hrc] := mregs_rel_lookup R_COM Hregs.
have [rold Hrold] := mregs_rel_lookup r Hregs.
rewrite /Symbolic.pct in Hpct.
set key := @word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r).
set wimm := @swcast (imm_size mt) (word_size mt)
              (convert_value (memory_lengths PB) v).
exists (@Symbolic.State mt lrc_tags unit
          (Symbolic.mem ms)
          (setm (Symbolic.regs ms) key (Atom wimm Other))
          (addw (Symbolic.pcv ms) onew)@(taga (Symbolic.pc ms))
          (Symbolic.internal ms)), wimm.
split.
- rewrite /step_me.
  apply: (@Symbolic.step_const _ _ _ _ _ _ _ _ _
            (Symbolic.mem ms) (Symbolic.regs ms)
            (Symbolic.pcv ms) (taga (Symbolic.pc ms))
            (vala w0) (taga w0)
            (convert_value (memory_lengths PB) v) key
            (vala rold) (taga rold)
            (Symbolic.internal ms)).
  + exact: Symbolic.state_eta.
  + by case: (w0) Hv.
  + move: Hdec => /= Hdec. exact: Hdec.
  + by case: (rold) Hrold.
  + rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc.
    rewrite /Symbolic.pcv in Hv'.
    rewrite Hv'.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt)
              = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
    rewrite Hrc /=.
    rewrite /Merged.transfer /Merged.instr_rules.
    rewrite Hpct Htagv /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite /check_belong /belong Htagv' Ecell2 /= eqxx /=.
    rewrite /Symbolic.next_state_do_update /updm Hrold /=.
    by [].
- constructor.
  + exact: Hpc'.
  + rewrite /Symbolic.pct /= Hpct.
    by rewrite Pointer.inc_preserves_component.
  +
    rewrite /=.
    apply: mregs_rel_set; first exact: Hregs.
    rewrite /tvrel /=. exact: Hvrel.
  + exact: Hmem.
  + exact: Hcode.
  + exact: sysregs_ok_setm Hsys.
  + exact: Hgap.
- exact: erefl.
- rewrite /tvrel /=. exact: Hvrel.
- split.
  + exact: erefl.
  + exact: erefl.
Qed.

(* ================================================================== *)
(* 5. MOV and BNZ-fall-through.                                       *)
(* ================================================================== *)

Lemma vrel_int_inv (amap : amap_t) (z : Z) (w : mword mt) :
  vrel amap (Int z) w -> wrepr z w.
Proof.
move=> H.
by inversion H; subst.
Qed.

Lemma vrel_ptr_inv (amap : amap_t) (p : Pointer.t) (w : mword mt) :
  vrel amap (Ptr p) w ->
  exists a,
    [/\ addr_of amap (Pointer.component p) (Pointer.block p) = Some a,
        BinInt.Z.le 0 (Pointer.offset p)
      & w = @word_of_nat (word_size mt)
              (a + BinInt.Z.to_nat (Pointer.offset p))].
Proof.
move=> H.
inversion H; subst.
exists a.
by split.
Qed.

(* only the zero word represents 0 *)
Lemma wrepr_zero (w : mword mt) : wrepr 0 w -> w = 0%w.
Proof.
rewrite /wrepr => H.
have Hi : int_of_word w = ssrint.Posz 0.
{ case E: (int_of_word w) H => [n|n] /= H.
  - congr ssrint.Posz. by lia.
  - exfalso. by lia. }
by rewrite -(int_of_wordK w) Hi.
Qed.

(* distinct registers, distinct me keys *)
Lemma to_nat_inj : injective Intermediate.Register.to_nat.
Proof. by case; case => // H; discriminate H. Qed.

Lemma regkey_neq (r1 r2 : register) :
  r1 <> r2 ->
  (@word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r1))
  != (@word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r2)).
Proof.
move=> Hne.
have Hlt : forall r0 : register, Intermediate.Register.to_nat r0 < 32
  by case.
rewrite (won_eqE (small_lt_reg (Hlt r1)) (small_lt_reg (Hlt r2))).
apply/negP => /eqP /to_nat_inj E.
exact: Hne.
Qed.

(* re-writing a register with its own content preserves the relation *)
Lemma mregs_rel_refresh (amap : amap_t) (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt}) (r : register) (ra : @ratom mt) :
  mregs (@word_of_nat (reg_field_size mt)
           (Intermediate.Register.to_nat r)) = Some ra ->
  mregs_relW amap tregs mregs ->
  mregs_relW amap tregs
    (setm mregs (@word_of_nat (reg_field_size mt)
                   (Intermediate.Register.to_nat r)) ra).
Proof.
move=> Hr Hrel r''.
have Hlt : forall r0 : register, Intermediate.Register.to_nat r0 < 32
  by case.
rewrite /reg_synced setmE
        (won_eqE (small_lt_reg (Hlt r'')) (small_lt_reg (Hlt r))).
case: (Hrel r'') => [[ra'' [Hra'' Hv'' Ht'']]|[ra'' [Hra'' Hu'' Ht'']]].
- left. exists ra''.
  case: (altP (Intermediate.Register.to_nat r''
               =P Intermediate.Register.to_nat r)) => [Etn|Hne];
    last by split.
  split=> //.
  move: Hra''. rewrite Etn Hr. by move=> [->].
- right. exists ra''.
  case: (altP (Intermediate.Register.to_nat r''
               =P Intermediate.Register.to_nat r)) => [Etn|Hne];
    last by split.
  split=> //.
  move: Hra''. rewrite Etn Hr. by move=> [->].
Qed.

Lemma sim_mov (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (tpc : Pointer.t) (tpct : Transitional.pc_tag)
    (ms : @Symbolic.state mt lrc_tags unit)
    (tg : mem_tag) (c : Component.id) (r1 r2 : register) :
  r1 <> r2 ->
  match_statesW amap tmem tregs tpc tpct ms ->
  Transitional.executing cdeW tpc (TrMov r1 r2) tg c ->
  Transitional.check_pc cdeW tpc tg ->
  exists ms' w1 ts1,
    [/\ step_me (NC := NC) ms ms' None,
        match_statesW amap tmem
          (Transitional.Register.set r1
             (Transitional.val (Transitional.Register.get r1 tregs))
             (moved_tag (Transitional.tvtag
                               (Transitional.Register.get r1 tregs)))
             (Transitional.Register.set r2
                (Transitional.val (Transitional.Register.get r1 tregs))
                (Transitional.tvtag (Transitional.Register.get r1 tregs))
                tregs))
          (Pointer.inc tpc) tpct ms',
        domm (Symbolic.mem ms') = domm (Symbolic.mem ms),
        getm (Symbolic.regs ms)
          (@word_of_nat (reg_field_size mt)
             (Intermediate.Register.to_nat r1)) = Some (Atom w1 ts1)
      & Symbolic.regs ms'
        = setm (setm (Symbolic.regs ms)
                 (@word_of_nat (reg_field_size mt)
                    (Intermediate.Register.to_nat r1))
                 (Atom w1 (moved_tag ts1)))
            (@word_of_nat (reg_field_size mt)
               (Intermediate.Register.to_nat r2)) (Atom w1 ts1) /\
        Symbolic.mem ms' = Symbolic.mem ms].
Proof.
move=> Hr12 Hm Hex0 Hcp.
have [Ec Hic Hcol] := executing_props Hex0.
subst c.
have [i' [tni Hex1]] := check_pc_next Hcp.
rewrite Pointer.inc_preserves_component in Hex1.
have [_ Etni_ic Etni_col] := executing_props Hex1.
case: tg Hex0 Hic Hcol {Hcp} => vt0 col0 ent0 isc0 Hex0 /= Hic Hcol.
subst isc0 col0.
case: tni Hex1 Etni_ic Etni_col => vt1 col1 ent1 isc1 Hex1 /= Etni_ic Etni_col.
subst isc1 col1.
set tg := MTag vt0 (Pointer.component tpc) ent0 true.
set tni := MTag vt1 (Pointer.component tpc) ent1 true.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrMov r1 r2, tg)) 0
  = Some (MrMov (inl r1) (inl r2), tg) by [].
have [cell' Hcell'] : exists cell',
    List.nth_error
      (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB) (i', tni)) 0
    = Some cell'.
{ apply: nth_error_Some_ex.
  rewrite lin_size_length size_cell_exp. by case: i' {Hex1}. }
have Ecell2 : cell'.2 = tni := cell_exp_snd Hcell'.
case: Hm => Hpc Hpct Hregs Hmem Hcode Hsys Hgap.
have [pos [w0 [Hwv Hv Htagv Hdec _]]] :=
  match_fetch Hbound Hcode Hex0 Hpc Hcell.
have [pos2 [v' [Hw2 Haddr Hv' Htagv' Hpc']]] :=
  silent_next (i := TrMov r1 r2) (erefl _) Hcode Hex0 Hex1 Hpc Hcell'.
have [rc Hrc] := mregs_rel_lookup R_COM Hregs.
have [ra1 Hr1] := mregs_rel_lookup r1 Hregs.
have Hcase1 :
    (tvrel cmapWW amap (Transitional.Register.get r1 tregs) (vala ra1)
     /\ taga ra1
        = Transitional.tvtag (Transitional.Register.get r1 tregs))
    \/ (Transitional.Register.get r1 tregs = Transitional.tUndef
        /\ taga ra1 = Invalidated).
{ case: (Hregs r1) => [[ra1' [Hr1' Hv1 Ht1]]|[ra1' [Hr1' Hu1 Ht1c]]].
  - move: Hr1'; rewrite Hr1 => -[Era]. subst ra1'.
    left. by split.
  - move: Hr1'; rewrite Hr1 => -[Era]. subst ra1'.
    right. by split. }
have [ra2 Hr2] := mregs_rel_lookup r2 Hregs.
rewrite /Symbolic.pct in Hpct.
set key1 := @word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r1).
set key2 := @word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r2).
set ts' := moved_tag (taga ra1).
exists (@Symbolic.State mt lrc_tags unit
          (Symbolic.mem ms)
          (setm (setm (Symbolic.regs ms) key1 (Atom (vala ra1) ts'))
                key2 (Atom (vala ra1) (taga ra1)))
          (addw (Symbolic.pcv ms) onew)@(taga (Symbolic.pc ms))
          (Symbolic.internal ms)), (vala ra1), (taga ra1).
split.
- rewrite /step_me.
  apply: (@Symbolic.step_mov _ _ _ _ _ _ _ _ _
            (Symbolic.mem ms) (Symbolic.regs ms)
            (Symbolic.pcv ms) (taga (Symbolic.pc ms))
            (vala w0) (taga w0)
            key1 (vala ra1) (taga ra1)
            key2 (vala ra2) (taga ra2)
            (Symbolic.internal ms)).
  + exact: Symbolic.state_eta.
  + by case: (w0) Hv.
  + move: Hdec => /= Hdec. exact: Hdec.
  + by case: (ra1) Hr1.
  + by case: (ra2) Hr2.
  + rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc.
    rewrite /Symbolic.pcv in Hv'.
    rewrite Hv'.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt)
              = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
    rewrite Hrc /=.
    rewrite /Merged.transfer /Merged.instr_rules.
    rewrite Hpct Htagv /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite /check_belong /belong Htagv' Ecell2 /= eqxx /=.
    rewrite /Symbolic.next_state_do_update /updm.
    rewrite Hr1 /=.
    have Hk21 : key2 != key1.
    { apply: regkey_neq => E. by apply: Hr12; rewrite E. }
    rewrite setmE (negbTE Hk21) Hr2 /=.
    by [].
- constructor.
  + exact: Hpc'.
  + rewrite /Symbolic.pct /= Hpct.
    by rewrite Pointer.inc_preserves_component.
  +
    rewrite /= setmC; last exact: (regkey_neq Hr12).
    case: Hcase1 => [[Hv1 Ht1]|[Hu1 Ht1c]].
    * rewrite /ts' Ht1.
      apply: mregs_rel_set; last exact: (tvrel_retag Hv1).
      apply: mregs_rel_set; last exact: (tvrel_eta Hv1).
      exact: Hregs.
    * rewrite /ts' Ht1c /= Hu1 /=.
      apply: mregs_rel_set_clob.
      apply: mregs_rel_set_clob.
      exact: Hregs.
  + exact: Hmem.
  + exact: Hcode.
  + apply: sysregs_ok_setm.
    apply: sysregs_ok_setm.
    exact: Hsys.
  + exact: Hgap.
- exact: erefl.
- by case: (ra1) Hr1.
- split.
  + exact: erefl.
  + exact: erefl.
Qed.

Lemma sim_bnzZ (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (tpc : Pointer.t) (tpct : Transitional.pc_tag)
    (ms : @Symbolic.state mt lrc_tags unit)
    (tg : mem_tag) (c : Component.id) (r : register) (l : label) :
  match_statesW amap tmem tregs tpc tpct ms ->
  reg_syncedW amap tregs (Symbolic.regs ms) r ->
  Transitional.executing cdeW tpc (TrBnz r l) tg c ->
  Transitional.check_pc cdeW tpc tg ->
  Transitional.tvtag (Transitional.Register.get r tregs) = Other ->
  Transitional.val (Transitional.Register.get r tregs) = Int 0 ->
  exists ms',
    [/\ step_me (NC := NC) ms ms' None,
        match_statesW amap tmem tregs (Pointer.inc tpc) tpct ms',
        domm (Symbolic.mem ms') = domm (Symbolic.mem ms),
        Symbolic.regs ms' = Symbolic.regs ms
      & Symbolic.mem ms' = Symbolic.mem ms].
Proof.
move=> Hm Hsyncr Hex0 Hcp Htag0 Hval0.
have [Ec Hic Hcol] := executing_props Hex0.
subst c.
have [i' [tni Hex1]] := check_pc_next Hcp.
rewrite Pointer.inc_preserves_component in Hex1.
have [_ Etni_ic Etni_col] := executing_props Hex1.
case: tg Hex0 Hic Hcol {Hcp} => vt0 col0 ent0 isc0 Hex0 /= Hic Hcol.
subst isc0 col0.
case: tni Hex1 Etni_ic Etni_col => vt1 col1 ent1 isc1 Hex1 /= Etni_ic Etni_col.
subst isc1 col1.
set tg := MTag vt0 (Pointer.component tpc) ent0 true.
set tni := MTag vt1 (Pointer.component tpc) ent1 true.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrBnz r l, tg)) 0
  = Some (MrBnz r (can_upd L (Pointer.component tpc) l), tg) by [].
have [cell' Hcell'] : exists cell',
    List.nth_error
      (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB) (i', tni)) 0
    = Some cell'.
{ apply: nth_error_Some_ex.
  rewrite lin_size_length size_cell_exp. by case: i' {Hex1}. }
have Ecell2 : cell'.2 = tni := cell_exp_snd Hcell'.
case: Hm => Hpc Hpct Hregs Hmem Hcode Hsys Hgap.
have [pos [w0 [Hwv Hv Htagv Hdec _]]] :=
  match_fetch Hbound Hcode Hex0 Hpc Hcell.
have [pos2 [v' [Hw2 Haddr Hv' Htagv' Hpc']]] :=
  silent_next (i := TrBnz r l) (erefl _) Hcode Hex0 Hex1 Hpc Hcell'.
have [rc Hrc] := mregs_rel_lookup R_COM Hregs.
have [rar [Hrr Hvr Htr]] := Hsyncr.
case: rar Hrr Hvr Htr => wr tr Hrr Hvr Htr.
have Hw0 : wr = 0%w.
{ apply: wrepr_zero.
  move: Hvr; rewrite /tvrel Htag0 Hval0 /= => Hvr.
  exact: vrel_int_inv Hvr. }
have Etr : tr = Other by rewrite /= in Htr; rewrite Htr Htag0.
subst wr tr.
rewrite /Symbolic.pct in Hpct.
set key := @word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r).
exists (@Symbolic.State mt lrc_tags unit
          (Symbolic.mem ms)
          (setm (Symbolic.regs ms) key (Atom 0%w Other))
          (addw (Symbolic.pcv ms) onew)@(taga (Symbolic.pc ms))
          (Symbolic.internal ms)).
split.
- rewrite /step_me.
  apply: (@Symbolic.step_bnz _ _ _ _ _ _ _ _ _
            (Symbolic.mem ms) (Symbolic.regs ms)
            (Symbolic.pcv ms)
            (vala w0) key _ 0%w
            (taga (Symbolic.pc ms)) (taga w0) Other
            (Symbolic.internal ms)).
  + exact: Symbolic.state_eta.
  + by case: (w0) Hv.
  + move: Hdec => /= Hdec. exact: Hdec.
  + exact: Hrr.
  + rewrite eqxx.
    rewrite /Symbolic.next_state_updates_and_pc.
    rewrite /Symbolic.pcv in Hv'.
    rewrite Hv'.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt)
              = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
    rewrite Hrc /=.
    rewrite /Merged.transfer /Merged.instr_rules.
    rewrite Hpct Htagv /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite /check_belong /belong Htagv' Ecell2 /= eqxx /=.
    rewrite /Symbolic.next_state_do_update /updm Hrr /=.
    by [].
- constructor.
  + exact: Hpc'.
  + rewrite /Symbolic.pct /= Hpct.
    by rewrite Pointer.inc_preserves_component.
  + exact: mregs_rel_refresh Hrr Hregs.
  + exact: Hmem.
  + exact: Hcode.
  + exact: sysregs_ok_setm Hsys.
  + exact: Hgap.
- exact: erefl.
- exact: (setmI Hrr).
- exact: erefl.
Qed.

(* ================================================================== *)
(* 6. BINOP.  The arithmetic core is congruence modulo 2^32:          *)
(*    [wrepr_val]/[wrepr_congr] pin the value up to one wrap.  Bounds  *)
(*    go through Z LITERALS (lia treats Z.pow/expn as opaque, and      *)
(*    k·2^32 with symbolic 2^32 is nonlinear).                         *)
(* ================================================================== *)

Lemma convert_subz (a b : nat) :
  Symbolic.convert ((a%:Z) - (b%:Z))%R
  = BinInt.Z.sub (Z.of_nat a) (Z.of_nat b).
Proof.
case: (leqP b a) => H.
- rewrite (subzn H) /=. by lia.
- have -> : ((a%:Z) - (b%:Z))%R = ssrint.Negz (b - a).-1 by lia.
  rewrite /=. by lia.
Qed.

Lemma wrepr_val (z : Z) (w : mword mt) :
  wrepr z w ->
  exists k : Z,
    Z.of_nat (nat_of_ord (word.ord_of_word w))
    = BinInt.Z.add z (BinInt.Z.mul k (4294967296 : Z)).
Proof.
rewrite /wrepr /int_of_word.
have Hb32 : Z.of_nat (2 ^ 32) = (4294967296 : Z) by rewrite expn_Zpow.
have E32 := expn_ws_32.
have Hw : nat_of_ord (word.ord_of_word w) < 2 ^ word_size mt := ltn_ord _.
case: ifP => Hlt <-.
- exists BinNums.Z0. rewrite /=. by lia.
- exists (Z.of_nat 1).
  rewrite convert_subz. by lia.
Qed.

Lemma wrepr_congr (z : Z) (w : mword mt) (k : Z) :
  MDefs.int_fits z ->
  Z.of_nat (nat_of_ord (word.ord_of_word w))
  = BinInt.Z.add z (BinInt.Z.mul k (4294967296 : Z)) ->
  wrepr z w.
Proof.
case=> Hlo Hhi Hk.
have Hb31 : Z.of_nat (2 ^ 31) = (2147483648 : Z) by rewrite expn_Zpow.
have Hb32 : Z.of_nat (2 ^ 32) = (4294967296 : Z) by rewrite expn_Zpow.
have HpE := expn_Zpow31.
have E32 := expn_ws_32.
have E31 := expn_ws_31.
have Hw : nat_of_ord (word.ord_of_word w) < 2 ^ word_size mt := ltn_ord _.
rewrite /wrepr /int_of_word.
case: ifP => Hlt.
- rewrite /=. by lia.
- rewrite convert_subz. by lia.
Qed.

Lemma wrepr_uniq (z : Z) (w1 w2 : mword mt) :
  wrepr z w1 -> wrepr z w2 -> w1 = w2.
Proof.
rewrite /wrepr => H1 H2.
apply: (can_inj (@int_of_wordK (word_size mt))).
apply: Symbolic.convert_inj.
by rewrite H1 H2.
Qed.

(* val-level characterizations of the remaining word operations *)
Lemma valw_mulw' (w1 w2 : mword mt) :
  nat_of_ord (word.ord_of_word (mulw w1 w2))
  = (nat_of_ord (word.ord_of_word w1) * nat_of_ord (word.ord_of_word w2))
    %% 2 ^ word_size mt.
Proof. by rewrite /mulw valw_as_word. Qed.

Lemma valw_subw' (w1 w2 : mword mt) :
  nat_of_ord (word.ord_of_word (subw w1 w2))
  = (nat_of_ord (word.ord_of_word w1)
     + (2 ^ word_size mt - nat_of_ord (word.ord_of_word w2)))
    %% 2 ^ word_size mt.
Proof.
by rewrite /subw /oppw valw_addw valw_as_word modnDmr.
Qed.

(* mod by M, for arguments below 2·M: at most one wrap *)
Lemma modn_two (a M : nat) :
  0 < M -> a < M.*2 ->
  (a < M /\ a %% M = a) \/ (M <= a /\ a %% M = a - M).
Proof.
move=> HM Ha.
case: (ltnP a M) => H.
- left. split=> //. by rewrite modn_small.
- right. split=> //.
  rewrite -{1}(subnKC H) modnDl modn_small //.
  rewrite ltn_subLR //. by rewrite addnn.
Qed.

(* ---- the three arithmetic operators, related under result-fit ---- *)

Lemma wrepr_addw (z1 z2 : Z) (w1 w2 : mword mt) :
  MDefs.int_fits (BinInt.Z.add z1 z2) ->
  wrepr z1 w1 -> wrepr z2 w2 ->
  wrepr (BinInt.Z.add z1 z2) (addw w1 w2).
Proof.
move=> Hf H1 H2.
have [k1 E1] := wrepr_val H1.
have [k2 E2] := wrepr_val H2.
have Hb32 : Z.of_nat (2 ^ 32) = (4294967296 : Z) by rewrite expn_Zpow.
have E32 := expn_ws_32.
set n1 := nat_of_ord (word.ord_of_word w1) in E1 *.
set n2 := nat_of_ord (word.ord_of_word w2) in E2 *.
have Hval := valw_addw w1 w2.
rewrite -/n1 -/n2 in Hval.
have Hw1 : n1 < 2 ^ word_size mt by rewrite /n1; exact: ltn_ord.
have Hw2 : n2 < 2 ^ word_size mt by rewrite /n2; exact: ltn_ord.
have HM : (0 : nat) < 2 ^ word_size mt by rewrite expn_gt0.
have Hlt2 : n1 + n2 < (2 ^ word_size mt).*2 by rewrite -addnn; lia.
case: (modn_two HM Hlt2) => [[Hb Hr]|[Hb Hr]].
- apply: (wrepr_congr (k := BinInt.Z.add k1 k2) Hf).
  rewrite Hval Hr. by lia.
- apply: (wrepr_congr
            (k := BinInt.Z.sub (BinInt.Z.add k1 k2) 1) Hf).
  rewrite Hval Hr. by lia.
Qed.

Lemma wrepr_subw (z1 z2 : Z) (w1 w2 : mword mt) :
  MDefs.int_fits (BinInt.Z.sub z1 z2) ->
  wrepr z1 w1 -> wrepr z2 w2 ->
  wrepr (BinInt.Z.sub z1 z2) (subw w1 w2).
Proof.
move=> Hf H1 H2.
have [k1 E1] := wrepr_val H1.
have [k2 E2] := wrepr_val H2.
have Hb32 : Z.of_nat (2 ^ 32) = (4294967296 : Z) by rewrite expn_Zpow.
have E32 := expn_ws_32.
set n1 := nat_of_ord (word.ord_of_word w1) in E1 *.
set n2 := nat_of_ord (word.ord_of_word w2) in E2 *.
have Hval := valw_subw' w1 w2.
rewrite -/n1 -/n2 in Hval.
have Hw1 : n1 < 2 ^ word_size mt by rewrite /n1; exact: ltn_ord.
have Hw2 : n2 < 2 ^ word_size mt by rewrite /n2; exact: ltn_ord.
have HM : (0 : nat) < 2 ^ word_size mt by rewrite expn_gt0.
have Hlt2 : n1 + (2 ^ word_size mt - n2) < (2 ^ word_size mt).*2
  by rewrite -addnn; lia.
case: (modn_two HM Hlt2) => [[Hb Hr]|[Hb Hr]].
- apply: (wrepr_congr
            (k := BinInt.Z.add (BinInt.Z.sub k1 k2) 1) Hf).
  rewrite Hval Hr. by lia.
- apply: (wrepr_congr (k := BinInt.Z.sub k1 k2) Hf).
  rewrite Hval Hr. by lia.
Qed.

Lemma wrepr_mulw (z1 z2 : Z) (w1 w2 : mword mt) :
  MDefs.int_fits (BinInt.Z.mul z1 z2) ->
  wrepr z1 w1 -> wrepr z2 w2 ->
  wrepr (BinInt.Z.mul z1 z2) (mulw w1 w2).
Proof.
move=> Hf H1 H2.
have [k1 E1] := wrepr_val H1.
have [k2 E2] := wrepr_val H2.
have Hb32 : Z.of_nat (2 ^ 32) = (4294967296 : Z) by rewrite expn_Zpow.
have E32 := expn_ws_32.
set n1 := nat_of_ord (word.ord_of_word w1) in E1 *.
set n2 := nat_of_ord (word.ord_of_word w2) in E2 *.
have Hval := valw_mulw' w1 w2.
rewrite -/n1 -/n2 in Hval.
have Hmod := divn_eq (n1 * n2) (2 ^ word_size mt).
set q := (_ %/ _)%N in Hmod.
set r := ((n1 * n2) %% 2 ^ word_size mt)%N in Hmod Hval.
have HmodZ := congr1 Z.of_nat Hmod.
have HbW : Z.of_nat (2 ^ word_size mt) = (4294967296 : Z).
{ rewrite E32. exact: Hb32. }
rewrite Nat2Z.inj_add (Nat2Z.inj_mul q (2 ^ word_size mt))
        (Nat2Z.inj_mul n1 n2) HbW in HmodZ.
apply: (wrepr_congr
          (k := BinInt.Z.sub
                  (BinInt.Z.add
                     (BinInt.Z.add (BinInt.Z.mul k1 z2)
                                   (BinInt.Z.mul k2 z1))
                     (BinInt.Z.mul (BinInt.Z.mul k1 k2) (4294967296 : Z)))
                  (Z.of_nat q)) Hf).
rewrite Hval.
by nia.
Qed.

(* equality: canonical words decide it *)
Lemma wrepr_eqw (z1 z2 : Z) (w1 w2 : mword mt) :
  MDefs.int_fits z1 -> MDefs.int_fits z2 ->
  wrepr z1 w1 -> wrepr z2 w2 ->
  wrepr (Util.Z.of_bool (BinInt.Z.eqb z1 z2))
        (word.as_word ((w1 == w2) : nat)).
Proof.
move=> Hf1 Hf2 H1 H2.
have HpE := expn_Zpow31.
have Hb31 : Z.of_nat (2 ^ 31) = (2147483648 : Z).
{ rewrite expn_Zpow31. exact: erefl. }
case: (altP (w1 =P w2)) => [Ew|Hne].
- subst w2.
  have Ez : z1 = z2.
  { by rewrite -H1 -H2. }
  rewrite Ez Z.eqb_refl /=.
  have Hfit1 : MDefs.int_fits 1 by split; lia.
  have := wrepr_encode_int Hfit1.
  by [].
- have Ez : BinInt.Z.eqb z1 z2 = false.
  { apply/Z.eqb_neq => Ez.
    move/eqP: Hne => []; apply: (wrepr_uniq H1).
    by rewrite Ez. }
  rewrite Ez /=.
  have Hfit0 : MDefs.int_fits 0 by split; lia.
  have := wrepr_encode_int Hfit0.
  by [].
Qed.

Lemma sim_binop (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (tpc : Pointer.t) (tpct : Transitional.pc_tag)
    (ms : @Symbolic.state mt lrc_tags unit)
    (tg : mem_tag) (c : Component.id)
    (op : Values.binop) (r1 r2 r3 : register) :
  match_statesW amap tmem tregs tpc tpct ms ->
  reg_syncedW amap tregs (Symbolic.regs ms) r1 ->
  reg_syncedW amap tregs (Symbolic.regs ms) r2 ->
  Transitional.executing cdeW tpc (TrBinOp op r1 r2 r3) tg c ->
  Transitional.check_pc cdeW tpc tg ->
  Transitional.tvtag (Transitional.Register.get r1 tregs) = Other ->
  Transitional.tvtag (Transitional.Register.get r2 tregs) = Other ->
  (forall w1 w2,
      vrel amap (Transitional.val (Transitional.Register.get r1 tregs)) w1 ->
      vrel amap (Transitional.val (Transitional.Register.get r2 tregs)) w2 ->
      vrel amap
        (eval_binop op (Transitional.val (Transitional.Register.get r1 tregs))
                       (Transitional.val (Transitional.Register.get r2 tregs)))
        (binop_denote (binop_trans op) w1 w2)) ->
  exists ms' w,
    [/\ step_me (NC := NC) ms ms' None,
        match_statesW amap tmem
          (Transitional.Register.set r3
             (eval_binop op
                (Transitional.val (Transitional.Register.get r1 tregs))
                (Transitional.val (Transitional.Register.get r2 tregs)))
             Other tregs)
          (Pointer.inc tpc) tpct ms',
        domm (Symbolic.mem ms') = domm (Symbolic.mem ms),
        tvrel cmapWW amap
          (Transitional.MVal Other
             (eval_binop op
                (Transitional.val (Transitional.Register.get r1 tregs))
                (Transitional.val (Transitional.Register.get r2 tregs)))) w
      & Symbolic.regs ms'
        = setm (Symbolic.regs ms)
            (@word_of_nat (reg_field_size mt)
               (Intermediate.Register.to_nat r3)) (Atom w Other) /\
        Symbolic.mem ms' = Symbolic.mem ms].
Proof.
move=> Hm Hsync1 Hsync2 Hex0 Hcp Htag1 Htag2 Hres.
have [Ec Hic Hcol] := executing_props Hex0.
subst c.
have [i' [tni Hex1]] := check_pc_next Hcp.
rewrite Pointer.inc_preserves_component in Hex1.
have [_ Etni_ic Etni_col] := executing_props Hex1.
case: tg Hex0 Hic Hcol {Hcp} => vt0 col0 ent0 isc0 Hex0 /= Hic Hcol.
subst isc0 col0.
case: tni Hex1 Etni_ic Etni_col => vt1 col1 ent1 isc1 Hex1 /= Etni_ic Etni_col.
subst isc1 col1.
set tg := MTag vt0 (Pointer.component tpc) ent0 true.
set tni := MTag vt1 (Pointer.component tpc) ent1 true.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrBinOp op r1 r2 r3, tg)) 0
  = Some (MrBinop op r1 r2 r3, tg) by [].
have [cell' Hcell'] : exists cell',
    List.nth_error
      (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB) (i', tni)) 0
    = Some cell'.
{ apply: nth_error_Some_ex.
  rewrite lin_size_length size_cell_exp. by case: i' {Hex1}. }
have Ecell2 : cell'.2 = tni := cell_exp_snd Hcell'.
case: Hm => Hpc Hpct Hregs Hmem Hcode Hsys Hgap.
have [pos [w0 [Hwv Hv Htagv Hdec _]]] :=
  match_fetch Hbound Hcode Hex0 Hpc Hcell.
have [pos2 [v' [Hw2 Haddr Hv' Htagv' Hpc']]] :=
  silent_next (i := TrBinOp op r1 r2 r3) (erefl _) Hcode Hex0 Hex1 Hpc Hcell'.
have [rc Hrc] := mregs_rel_lookup R_COM Hregs.
have [ra1 [Hr1 Hv1 Ht1]] := Hsync1.
have [ra2 [Hr2 Hv2 Ht2]] := Hsync2.
have [ra3 Hr3] := mregs_rel_lookup r3 Hregs.
case: ra1 Hr1 Hv1 Ht1 => w1 t1 Hr1 Hv1 Ht1.
case: ra2 Hr2 Hv2 Ht2 => w2 t2 Hr2 Hv2 Ht2.
rewrite /= in Hv1 Ht1 Hv2 Ht2.
have Et1 : t1 = Other by rewrite Ht1 Htag1.
have Et2 : t2 = Other by rewrite Ht2 Htag2.
subst t1 t2.
rewrite Et1 in Hr1.
rewrite Et2 in Hr2.
have Hv1' : vrel amap (Transitional.val (Transitional.Register.get r1 tregs)) w1
  by move: Hv1; rewrite /tvrel Htag1.
have Hv2' : vrel amap (Transitional.val (Transitional.Register.get r2 tregs)) w2
  by move: Hv2; rewrite /tvrel Htag2.
rewrite /Symbolic.pct in Hpct.
set key3 := @word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r3).
set res := binop_denote (binop_trans op) w1 w2.
exists (@Symbolic.State mt lrc_tags unit
          (Symbolic.mem ms)
          (setm (Symbolic.regs ms) key3 (Atom res Other))
          (addw (Symbolic.pcv ms) onew)@(taga (Symbolic.pc ms))
          (Symbolic.internal ms)), res.
split.
- rewrite /step_me.
  apply: (@Symbolic.step_binop _ _ _ _ _ _ _ _ _
            (Symbolic.mem ms) (Symbolic.regs ms)
            (Symbolic.pcv ms) (taga (Symbolic.pc ms))
            (vala w0) (taga w0)
            (binop_trans op)
            (@word_of_nat (reg_field_size mt)
               (Intermediate.Register.to_nat r1))
            (@word_of_nat (reg_field_size mt)
               (Intermediate.Register.to_nat r2))
            key3
            w1 w2 Other Other (vala ra3) (taga ra3)
            (Symbolic.internal ms)).
  + exact: Symbolic.state_eta.
  + by case: (w0) Hv.
  + move: Hdec => /= Hdec. exact: Hdec.
  + exact Hr1.
  + exact Hr2.
  + by case: (ra3) Hr3.
  + rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc.
    rewrite /Symbolic.pcv in Hv'.
    rewrite Hv'.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt)
              = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
    rewrite Hrc /=.
    rewrite /Merged.transfer /Merged.instr_rules.
    rewrite Hpct Htagv /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite /check_belong /belong Htagv' Ecell2 /= eqxx /=.
    rewrite /Symbolic.next_state_do_update /updm.
    rewrite Hr1 /= (setmI Hr1) Hr2 /= (setmI Hr2) Hr3 /=.
    by [].
- constructor.
  + exact: Hpc'.
  + rewrite /Symbolic.pct /= Hpct.
    by rewrite Pointer.inc_preserves_component.
  + apply: mregs_rel_set; first exact: Hregs.
    rewrite /tvrel /=.
    exact: (Hres _ _ Hv1' Hv2').
  + exact: Hmem.
  + exact: Hcode.
  + exact: sysregs_ok_setm Hsys.
  + exact: Hgap.
- exact: erefl.
- rewrite /tvrel /=. exact: (Hres _ _ Hv1' Hv2').
- split.
  + exact: erefl.
  + exact: erefl.
Qed.

(* ================================================================== *)
(* 7. LOAD.  The memory halves come from [minj_load] (the fetch) and  *)
(*    [minj_store] (T's tag write-back = me's MemRead re-tag).        *)
(* ================================================================== *)

(* every encoded code atom carries some code cell's tag *)
Lemma encode_code_tag (cde0 : @Merged.code mt) (pc1 : nat)
    (w : mword mt) (v : matom) :
  encode_code cde0 pc1 w = Some v ->
  exists n i t, List.nth_error cde0 n = Some (i, t) /\ taga v = t.
Proof.
move=> H.
have [n [Hw [Hlt Hnth]]] := encode_code_nth_inv H.
have [i [t [Hn' [Htag _]]]] := encode_code_foldr_nth Hnth.
by exists n, i, t.
Qed.

Lemma In_cat (A : Type) (l1 l2 : seq A) (y : A) :
  List.In y (l1 ++ l2) -> List.In y l1 \/ List.In y l2.
Proof.
elim: l1 => [|a l1 IH] /= H; first by right.
case: H => [->|H]; first by left; left.
by case: (IH H) => [Hl|Hr]; [left; right | right].
Qed.

Lemma In_rcons (A : Type) (l : seq A) (x y : A) :
  List.In y (rcons l x) -> List.In y l \/ y = x.
Proof.
elim: l => [|a l IH] /=.
- by case=> [->|//]; right.
- case=> [->|H]; first by left; left.
  by case: (IH H) => [Hl|->]; [left; right | right].
Qed.

(* all cells of the linked code are code-tagged *)
Lemma codeW_is_code (n : nat) (cell : @Merged.instr mt * mem_tag) :
  List.nth_error codeW n = Some cell -> is_code cell.2 = true.
Proof.
move=> Hn.
have HIn := List.nth_error_In _ _ Hn.
have Hcc : forall pr : Intermediate.program,
    List.In cell (compiler_code L P C PB PI pr) -> is_code cell.2 = true.
{ move=> pr.
  rewrite /compiler_code.
  case E: (compiler_body L P C PB PI pr) => [|c0 rest];
    first by move=> [].
  move=> HIn'.
  case: (In_rcons HIn') => [HInb|Ehalt].
  - rewrite -E in HInb.
    case: cell HInb {HIn Hn HIn'} => i t HInb.
    by have [Hicode _] := compiler_body_tags HInb.
  - by rewrite Ehalt. }
case: (In_cat HIn) => H; exact: Hcc H.
Qed.

(* updating a DATA address never disturbs the code region *)
Lemma mm_code_setm (mmem : {fmap mword mt -> matom}) (addr : mword mt)
    (mcold mcnew : matom) :
  (forall w v, encode_code codeW pc0 w = Some v -> mmem w = Some v) ->
  mmem addr = Some mcold ->
  is_code (taga mcold) = false ->
  forall w v, encode_code codeW pc0 w = Some v ->
    setm mmem addr mcnew w = Some v.
Proof.
move=> Hcode Hold Hicf w v Hw.
rewrite setmE.
case: (altP (w =P addr)) => [Ew|_]; last exact: Hcode.
exfalso.
subst w.
have Hv := Hcode _ _ Hw.
have Emc : v = mcold by move: Hv; rewrite Hold => -[].
have [n [i [t [Hn Htag]]]] := encode_code_tag Hw.
have Hicc := codeW_is_code Hn.
rewrite -Emc Htag Hicc in Hicf.
by discriminate Hicf.
Qed.

Lemma sim_load (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (tpc : Pointer.t) (tpct : Transitional.pc_tag)
    (ms : @Symbolic.state mt lrc_tags unit)
    (tg : mem_tag) (c : Component.id) (r1 r2 : register)
    (ptr : Pointer.t) (v : Transitional.tvalue * mem_tag)
    (tmem' : Transitional.Memory.t) :
  match_statesW amap tmem tregs tpc tpct ms ->
  reg_syncedW amap tregs (Symbolic.regs ms) r1 ->
  Transitional.executing cdeW tpc (TrLoad r1 r2) tg c ->
  Transitional.check_pc cdeW tpc tg ->
  Transitional.tvtag (Transitional.Register.get r1 tregs) = Other ->
  Transitional.val (Transitional.Register.get r1 tregs) = Ptr ptr ->
  Pointer.component ptr = c ->
  Transitional.Memory.load tmem ptr = Some v ->
  Transitional.Memory.store tmem ptr
    ({| Transitional.val := Transitional.val v.1;
        Transitional.tvtag := moved_tag (Transitional.tvtag v.1) |},
     {| vtag := moved_tag (Transitional.tvtag v.1);
        color := c; entry := None; is_code := false |}) = Some tmem' ->
  exists ms' a wmc mtg,
    [/\ step_me (NC := NC) ms ms' None,
        match_statesW amap tmem'
          (Transitional.Register.set r2 (Transitional.val v.1)
             (Transitional.tvtag v.1) tregs)
          (Pointer.inc tpc) tpct ms',
        domm (Symbolic.mem ms') = domm (Symbolic.mem ms),
        addr_of amap (Pointer.component ptr) (Pointer.block ptr)
          = Some a /\
        getm (Symbolic.mem ms)
          (@word_of_nat (word_size mt)
             (a + BinInt.Z.to_nat (Pointer.offset ptr)))
          = Some (Atom wmc mtg)
      & (cellrel cmapWW amap v (Atom wmc mtg) /\
         Symbolic.regs ms'
           = setm (Symbolic.regs ms)
               (@word_of_nat (reg_field_size mt)
                  (Intermediate.Register.to_nat r2))
               (Atom wmc (Transitional.tvtag v.1)) /\
         Symbolic.mem ms'
           = setm (Symbolic.mem ms)
               (@word_of_nat (word_size mt)
                  (a + BinInt.Z.to_nat (Pointer.offset ptr)))
               (Atom wmc
                  (MTag (moved_tag (Transitional.tvtag v.1))
                     (Pointer.component tpc) None false)))
        \/
        (clobcell v (Atom wmc mtg) /\
         Symbolic.regs ms'
           = setm (Symbolic.regs ms)
               (@word_of_nat (reg_field_size mt)
                  (Intermediate.Register.to_nat r2))
               (Atom wmc Invalidated) /\
         Symbolic.mem ms'
           = setm (Symbolic.mem ms)
               (@word_of_nat (word_size mt)
                  (a + BinInt.Z.to_nat (Pointer.offset ptr)))
               (Atom wmc
                  (MTag Invalidated (Pointer.component tpc) None
                     false)))].
Proof using Hbound HPB Hsmall.
move=> Hm Hsync1 Hex0 Hcp Htag1 Hval1 Hcomp Hld Hst.
have [Ec Hic Hcol] := executing_props Hex0.
rewrite {}Ec in Hex0 Hcomp Hcol Hst.
have [i' [tni Hex1]] := check_pc_next Hcp.
rewrite Pointer.inc_preserves_component in Hex1.
have [_ Etni_ic Etni_col] := executing_props Hex1.
case: tg Hex0 Hic Hcol {Hcp} => vt0 col0 ent0 isc0 Hex0 /= Hic Hcol.
subst isc0 col0.
case: tni Hex1 Etni_ic Etni_col => vt1 col1 ent1 isc1 Hex1 /= Etni_ic Etni_col.
subst isc1 col1.
set tg := MTag vt0 (Pointer.component tpc) ent0 true.
set tni := MTag vt1 (Pointer.component tpc) ent1 true.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrLoad r1 r2, tg)) 0
  = Some (MrLoad r1 r2, tg) by [].
have [cell' Hcell'] : exists cell',
    List.nth_error
      (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB) (i', tni)) 0
    = Some cell'.
{ apply: nth_error_Some_ex.
  rewrite lin_size_length size_cell_exp. by case: i' {Hex1}. }
have Ecell2 : cell'.2 = tni := cell_exp_snd Hcell'.
case: Hm => Hpc Hpct Hregs Hmem Hcode Hsys Hgap.
have [pos [w0 [Hwv Hv Htagv Hdec _]]] :=
  match_fetch Hbound Hcode Hex0 Hpc Hcell.
have [pos2 [v' [Hw2 Haddr Hv' Htagv' Hpc']]] :=
  silent_next (i := TrLoad r1 r2) (erefl _) Hcode Hex0 Hex1 Hpc Hcell'.
have [rc Hrc] := mregs_rel_lookup R_COM Hregs.
have [ra1 [Hr1 Hv1 Ht1]] := Hsync1.
case: ra1 Hr1 Hv1 Ht1 => w1 t1 Hr1 Hv1 Ht1.
rewrite /= in Hv1 Ht1.
have Et1 : t1 = Other by rewrite Ht1 Htag1.
subst t1.
rewrite Et1 in Hr1.
have [ra2 Hr2] := mregs_rel_lookup r2 Hregs.
have [a [mc [Ha Hmc Hrelmc Hdata]]] := minj_load Hmem Hld.
have Hw1 : w1 = @word_of_nat (word_size mt)
                  (a + BinInt.Z.to_nat (Pointer.offset ptr)).
{ move: Hv1; rewrite /tvrel Htag1 Hval1 => /vrel_ptr_inv [a0 [Ha0 _ Ew]].
  move: Ha0; rewrite Ha => -[?]; subst a0. exact: Ew. }
case: mc Hmc Hrelmc Hdata => wmc [vtgm colm entm icdm] Hmc Hrelmc /=.
move=> [Hicdm Hcolm Hentm].
subst icdm entm colm.
rewrite Hcomp in Hmc.
case: Hrelmc => [Hrelmc|Hclob]; last first.
{  have HclobK := Hclob.
  rewrite Hcomp in HclobK.
  case: Hclob => -[/= Ev1 Evt2 Evtgm] _.
  subst vtgm.
  have Etv1 : Transitional.tvtag v.1 = Other by rewrite Ev1.
  have Evv1 : Transitional.val v.1 = Undef by rewrite Ev1.
  set ts' := moved_tag (Transitional.tvtag v.1).
  have Ets' : ts' = Other by rewrite /ts' Etv1.
  set tagT := MTag ts' (Pointer.component tpc) None false.
  have Hclob' : clobcell
      ({| Transitional.val := Transitional.val v.1;
          Transitional.tvtag := ts' |}, tagT)
      (Atom wmc (MTag Invalidated (Pointer.component tpc) None false)).
  { (* explicit closers only: [done] hangs against this context *)
    split.
    - split.
      + rewrite /= Ev1 Ets'. exact: erefl.
      + rewrite /tagT /= Ets'. exact: erefl.
      + exact: erefl.
    - split; exact: erefl. }
  have Hcolp : color tagT = Pointer.component ptr by rewrite /= Hcomp.
  have [a' [Ha' Hinj']] :=
    minj_store Hmem Hst (or_intror Hclob') (erefl _) Hcolp (erefl _).
  have Ea' : a' = a by move: Ha'; rewrite Ha => -[].
  subst a'.
  rewrite /Symbolic.pct in Hpct.
  set addr := @word_of_nat (word_size mt)
                (a + BinInt.Z.to_nat (Pointer.offset ptr)).
  set key2 := @word_of_nat (reg_field_size mt)
                (Intermediate.Register.to_nat r2).
  exists (@Symbolic.State mt lrc_tags unit
            (setm (Symbolic.mem ms) addr
               (Atom wmc (MTag Invalidated (Pointer.component tpc)
                            None false)))
            (setm (Symbolic.regs ms) key2 (Atom wmc Invalidated))
            (addw (Symbolic.pcv ms) onew)@(taga (Symbolic.pc ms))
            (Symbolic.internal ms)), a, wmc,
         (MTag Invalidated (Pointer.component tpc) None false).
  split.
  - rewrite /step_me.
    apply: (@Symbolic.step_load _ _ _ _ _ _ _ _ _
              (Symbolic.mem ms) (Symbolic.regs ms)
              (Symbolic.pcv ms) (taga (Symbolic.pc ms))
              (vala w0) (taga w0)
              (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat r1))
              key2
              addr wmc Other
              (MTag Invalidated (Pointer.component tpc) None false)
              (vala ra2) (taga ra2)
              (Symbolic.internal ms)).
    + exact: Symbolic.state_eta.
    + by case: (w0) Hv.
    + move: Hdec => /= Hdec. exact: Hdec.
    + rewrite Hw1 in Hr1. exact Hr1.
    + exact Hmc.
    + by case: (ra2) Hr2.
    + rewrite /Symbolic.next_state_updates
              /Symbolic.next_state_updates_and_pc.
      rewrite /Symbolic.pcv in Hv'.
      rewrite Hv'.
      rewrite /Symbolic.next_state /Symbolic.evi.
      have -> : (rcom : reg mt)
                = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
      rewrite Hrc /=.
      rewrite /Merged.transfer /Merged.instr_rules.
      rewrite Hpct Htagv /=.
      rewrite /LRC.instr_rules /= eqxx /=.
      rewrite /check_belong /belong Htagv' Ecell2 /= eqxx /=.
      rewrite /Symbolic.next_state_do_update /updm.
      rewrite Hw1 in Hr1.
      rewrite Hr1 /= (setmI Hr1) Hmc /= Hr2 /=.
      by [].
  - constructor.
    + exact: Hpc'.
    + rewrite /Symbolic.pct /= Hpct.
      by rewrite Pointer.inc_preserves_component.
    +
      rewrite /= Ev1 /=.
      exact: mregs_rel_set_clob Hregs.
    +
      exact: Hinj'.
    +
      move=> w vv Hvv /=.
      rewrite setmE.
      case: (altP (w =P addr)) => [Ew|_]; last exact: Hcode.
      exfalso.
      subst w.
      have Hv2 := Hcode _ _ Hvv.
      have Evv : vv = Atom wmc (MTag Invalidated (Pointer.component tpc)
                                  None false).
      { move: Hv2. rewrite /addr Hmc. by move=> [->]. }
      have [n2 [i2 [t2 [Hn2 Htag2]]]] := encode_code_tag Hvv.
      have Hicc2 := codeW_is_code Hn2.
      rewrite Evv /= in Htag2.
      rewrite -Htag2 /= in Hicc2.
      by discriminate Hicc2.
    + exact: sysregs_ok_setm Hsys.
    + exact: gap_setm Hgap Hmc.
  - exact: domm_setm_pres Hmc.
  - split.
    + exact: Ha.
    + exact: Hmc.
  - right. split.
    + exact: HclobK.
    + split.
      * exact: erefl.
      * exact: erefl. }
have HrelK := Hrelmc.
rewrite Hcomp in HrelK.
case: Hrelmc => /= Hvmc Htmc Hvtmc.
have Evt : vtgm = Transitional.tvtag v.1 by rewrite -Hvtmc -Htmc.
set ts' := moved_tag (Transitional.tvtag v.1).
set tagT := MTag ts' (Pointer.component tpc) None false.
have Hrel' : cellrel cmapWW amap
    ({| Transitional.val := Transitional.val v.1;
        Transitional.tvtag := ts' |}, tagT)
    (Atom wmc tagT).
{ split.
  - exact: (tvrel_retag Hvmc).
  - by [].
  - by []. }
have Hcolp : color tagT = Pointer.component ptr by rewrite /= Hcomp.
have [a' [Ha' Hinj']] :=
  minj_store Hmem Hst (or_introl Hrel') (erefl _) Hcolp (erefl _).
have Ea' : a' = a by move: Ha'; rewrite Ha => -[].
subst a'.
rewrite /Symbolic.pct in Hpct.
set addr := @word_of_nat (word_size mt)
              (a + BinInt.Z.to_nat (Pointer.offset ptr)).
set key2 := @word_of_nat (reg_field_size mt)
              (Intermediate.Register.to_nat r2).
exists (@Symbolic.State mt lrc_tags unit
          (setm (Symbolic.mem ms) addr (Atom wmc tagT))
          (setm (Symbolic.regs ms) key2 (Atom wmc vtgm))
          (addw (Symbolic.pcv ms) onew)@(taga (Symbolic.pc ms))
          (Symbolic.internal ms)), a, wmc,
       (MTag vtgm (Pointer.component tpc) None false).
split.
- rewrite /step_me.
  apply: (@Symbolic.step_load _ _ _ _ _ _ _ _ _
            (Symbolic.mem ms) (Symbolic.regs ms)
            (Symbolic.pcv ms) (taga (Symbolic.pc ms))
            (vala w0) (taga w0)
            (@word_of_nat (reg_field_size mt)
               (Intermediate.Register.to_nat r1))
            key2
            addr wmc Other (MTag vtgm (Pointer.component tpc) None false)
            (vala ra2) (taga ra2)
            (Symbolic.internal ms)).
  + exact: Symbolic.state_eta.
  + by case: (w0) Hv.
  + move: Hdec => /= Hdec. exact: Hdec.
  + rewrite Hw1 in Hr1. exact Hr1.
  + exact Hmc.
  + by case: (ra2) Hr2.
  + rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc.
    rewrite /Symbolic.pcv in Hv'.
    rewrite Hv'.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt)
              = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
    rewrite Hrc /=.
    rewrite /Merged.transfer /Merged.instr_rules.
    rewrite Hpct Htagv /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite /check_belong /belong Htagv' Ecell2 /= eqxx /=.
    rewrite Evt -/ts' /=.
    rewrite /Symbolic.next_state_do_update /updm.
    rewrite Hw1 in Hr1.
    rewrite Hr1 /= (setmI Hr1) Hmc /= Hr2 /=.
    by [].
- constructor.
  + exact: Hpc'.
  + rewrite /Symbolic.pct /= Hpct.
    by rewrite Pointer.inc_preserves_component.
  +
    rewrite /= Evt.
    apply: mregs_rel_set; first exact: Hregs.
    exact: (tvrel_eta Hvmc).
  +
    exact: Hinj'.
  +
    move=> w vv Hvv /=.
    rewrite setmE.
    case: (altP (w =P addr)) => [Ew|_]; last exact: Hcode.
    exfalso.
    subst w.
    have Hv2 := Hcode _ _ Hvv.
    have Evv : vv = Atom wmc (MTag vtgm (Pointer.component tpc) None false).
    { move: Hv2. rewrite /addr Hmc. by move=> [->]. }
    have [n2 [i2 [t2 [Hn2 Htag2]]]] := encode_code_tag Hvv.
    have Hicc2 := codeW_is_code Hn2.
    rewrite Evv /= in Htag2.
    rewrite -Htag2 /= in Hicc2.
    by discriminate Hicc2.
  + exact: sysregs_ok_setm Hsys.
  + exact: gap_setm Hgap Hmc.
- exact: domm_setm_pres Hmc.
- split.
  + exact: Ha.
  + exact: Hmc.
- left. split.
  + exact: HrelK.
  + split.
    * rewrite /= Evt. exact: erefl.
    * exact: erefl.
Qed.

(* ================================================================== *)
(* 8. STORE.                                                          *)
(* ================================================================== *)

(* a successful store's target cell exists, so it can be loaded *)
Lemma store_load (tmem : Transitional.Memory.t) (ptr : Pointer.t)
    (cell : Transitional.tvalue * mem_tag) (tmem' : Transitional.Memory.t) :
  Transitional.Memory.store tmem ptr cell = Some tmem' ->
  exists oldcell, Transitional.Memory.load tmem ptr = Some oldcell.
Proof.
case: ptr => [[c b] o].
rewrite /Transitional.Memory.store /Transitional.Memory.load /=.
case Hc: (tmem c) => [cm|] //=.
rewrite /Transitional.Memory.store_b /Transitional.Memory.load_b.
case Hb: (Transitional.Memory.content cm b) => [chunk|] //.
case Ho: (BinInt.Z.leb 0 o) => //.
case Hupd: (list_upd chunk (BinInt.Z.to_nat o) cell) => [chunk'|] // _.
have Hi := list_upd_lt Hupd.
apply: nth_error_Some_ex.
by rewrite lin_size_length.
Qed.

Lemma sim_store (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (tpc : Pointer.t) (tpct : Transitional.pc_tag)
    (ms : @Symbolic.state mt lrc_tags unit)
    (tg : mem_tag) (c : Component.id) (r1 r2 : register)
    (ptr : Pointer.t) (vt : value_tag)
    (tmem' : Transitional.Memory.t) :
  match_statesW amap tmem tregs tpc tpct ms ->
  reg_syncedW amap tregs (Symbolic.regs ms) r1 ->
  Transitional.executing cdeW tpc (TrStore r1 r2) tg c ->
  Transitional.check_pc cdeW tpc tg ->
  Transitional.tvtag (Transitional.Register.get r1 tregs) = Other ->
  Transitional.val (Transitional.Register.get r1 tregs) = Ptr ptr ->
  Pointer.component ptr = c ->
  Transitional.Register.get_tag r2 tregs = Some vt ->
  Transitional.Memory.store tmem ptr
    (Transitional.Register.get r2 tregs,
     {| vtag := vt; color := c; entry := None; is_code := false |})
    = Some tmem' ->
  exists ms' a w2 ts2,
    [/\ step_me (NC := NC) ms ms' None,
        match_statesW amap tmem'
          (Transitional.Register.set r2
             (Transitional.val (Transitional.Register.get r2 tregs))
             (moved_tag vt) tregs)
          (Pointer.inc tpc) tpct ms',
        domm (Symbolic.mem ms') = domm (Symbolic.mem ms),
        addr_of amap (Pointer.component ptr) (Pointer.block ptr)
          = Some a /\
        getm (Symbolic.regs ms)
          (@word_of_nat (reg_field_size mt)
             (Intermediate.Register.to_nat r2)) = Some (Atom w2 ts2)
      & (Symbolic.regs ms'
         = setm (Symbolic.regs ms)
             (@word_of_nat (reg_field_size mt)
                (Intermediate.Register.to_nat r2))
             (Atom w2 (moved_tag ts2)) /\
         Symbolic.mem ms'
           = setm (Symbolic.mem ms)
               (@word_of_nat (word_size mt)
                  (a + BinInt.Z.to_nat (Pointer.offset ptr)))
               (Atom w2 (MTag ts2 (Pointer.component tpc) None false)))
        /\ (ts2 = vt
            \/ [/\ ts2 = Invalidated, vt = Other
                 & Transitional.Register.get r2 tregs
                   = Transitional.tUndef])].
Proof.
move=> Hm Hsync1 Hex0 Hcp Htag1 Hval1 Hcomp Hvt Hst.
have [Ec Hic Hcol] := executing_props Hex0.
rewrite {}Ec in Hex0 Hcomp Hcol Hst.
have [i' [tni Hex1]] := check_pc_next Hcp.
rewrite Pointer.inc_preserves_component in Hex1.
have [_ Etni_ic Etni_col] := executing_props Hex1.
case: tg Hex0 Hic Hcol {Hcp} => vt0 col0 ent0 isc0 Hex0 /= Hic Hcol.
subst isc0 col0.
case: tni Hex1 Etni_ic Etni_col => vt1 col1 ent1 isc1 Hex1 /= Etni_ic Etni_col.
subst isc1 col1.
set tg := MTag vt0 (Pointer.component tpc) ent0 true.
set tni := MTag vt1 (Pointer.component tpc) ent1 true.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrStore r1 r2, tg)) 0
  = Some (MrStore r1 r2, tg) by [].
have [cell' Hcell'] : exists cell',
    List.nth_error
      (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB) (i', tni)) 0
    = Some cell'.
{ apply: nth_error_Some_ex.
  rewrite lin_size_length size_cell_exp. by case: i' {Hex1}. }
have Ecell2 : cell'.2 = tni := cell_exp_snd Hcell'.
case: Hm => Hpc Hpct Hregs Hmem Hcode Hsys Hgap.
have [pos [w0 [Hwv Hv Htagv Hdec _]]] :=
  match_fetch Hbound Hcode Hex0 Hpc Hcell.
have [pos2 [v' [Hw2 Haddr Hv' Htagv' Hpc']]] :=
  silent_next (i := TrStore r1 r2) (erefl _) Hcode Hex0 Hex1 Hpc Hcell'.
have [rc Hrc] := mregs_rel_lookup R_COM Hregs.
have [ra1 [Hr1 Hv1 Ht1]] := Hsync1.
case: ra1 Hr1 Hv1 Ht1 => w1 t1 Hr1 Hv1 Ht1.
rewrite /= in Hv1 Ht1.
have Et1 : t1 = Other by rewrite Ht1 Htag1.
subst t1.
rewrite Et1 in Hr1.
have Evt : vt = Transitional.tvtag (Transitional.Register.get r2 tregs).
{ move: Hvt.
  rewrite /Transitional.Register.get_tag /Transitional.Register.get.
  case: (tregs (Transitional.Register.to_nat r2)) => [tv|].
  - by move=> [<-].
  - move=> H. by discriminate H. }
have [ra2 Hr2] := mregs_rel_lookup r2 Hregs.
case: ra2 Hr2 => w2 t2 Hr2.
have Hcase2 :
    (t2 = vt
     /\ tvrel cmapWW amap (Transitional.Register.get r2 tregs) w2)
    \/ [/\ t2 = Invalidated, vt = Other
         & Transitional.Register.get r2 tregs = Transitional.tUndef].
{ case: (Hregs r2) => [[ra2' [Hr2' Hv2 Ht2]]|[ra2' [Hr2' Hu2 Ht2c]]].
  - move: Hr2'; rewrite Hr2 => -[Era]. subst ra2'.
    rewrite /= in Hv2 Ht2.
    left. split; last exact: Hv2.
    by rewrite Ht2 Evt.
  - move: Hr2'; rewrite Hr2 => -[Era]. subst ra2'.
    rewrite /= in Ht2c.
    right. split.
    + exact: Ht2c.
    + by rewrite Evt Hu2.
    + exact: Hu2. }
have [oldcell Hld] := store_load Hst.
have [a [mc [Ha Hmc Hrelmc Hdata]]] := minj_load Hmem Hld.
have Hw1 : w1 = @word_of_nat (word_size mt)
                  (a + BinInt.Z.to_nat (Pointer.offset ptr)).
{ move: Hv1; rewrite /tvrel Htag1 Hval1 => /vrel_ptr_inv [a0 [Ha0 _ Ew]].
  move: Ha0; rewrite Ha => -[?]; subst a0. exact: Ew. }
case: mc Hmc Hrelmc Hdata => wmc [vtgm colm entm icdm] Hmc Hrelmc /=.
move=> [Hicdm Hcolm Hentm].
subst icdm entm colm.
rewrite Hcomp in Hmc.
set tagW := MTag vt (Pointer.component tpc) None false.
set tagM := MTag t2 (Pointer.component tpc) None false.
have Hrelw' : cellrelw cmapWW amap
    (Transitional.Register.get r2 tregs, tagW) (Atom w2 tagM).
{ case: Hcase2 => [[Et2 Hv2]|[Et2c Evto Hu2]].
  - left. split.
    + exact: Hv2.
    + rewrite /tagM Et2. exact: erefl.
    + rewrite /tagW /= Evt. exact: erefl.
  - right. split.
    + split.
      * exact: Hu2.
      * rewrite /tagW /= Evto. exact: erefl.
      * rewrite /tagM /= Et2c. exact: erefl.
    + split; exact: erefl. }
have Hcolp : color tagW = Pointer.component ptr by rewrite /= Hcomp.
have [a' [Ha' Hinj']] :=
  minj_store Hmem Hst Hrelw' (erefl _) Hcolp (erefl _).
have Ea' : a' = a by move: Ha'; rewrite Ha => -[].
subst a'.
rewrite /Symbolic.pct in Hpct.
set addr := @word_of_nat (word_size mt)
              (a + BinInt.Z.to_nat (Pointer.offset ptr)).
set key2 := @word_of_nat (reg_field_size mt)
              (Intermediate.Register.to_nat r2).
set ts' := moved_tag t2.
exists (@Symbolic.State mt lrc_tags unit
          (setm (Symbolic.mem ms) addr (Atom w2 tagM))
          (setm (Symbolic.regs ms) key2 (Atom w2 ts'))
          (addw (Symbolic.pcv ms) onew)@(taga (Symbolic.pc ms))
          (Symbolic.internal ms)), a, w2, t2.
split.
- rewrite /step_me.
  apply: (@Symbolic.step_store _ _ _ _ _ _ _ _ _
            (Symbolic.mem ms) (Symbolic.regs ms)
            (Symbolic.pcv ms)
            (vala w0)
            (@word_of_nat (reg_field_size mt)
               (Intermediate.Register.to_nat r1))
            key2
            addr w2
            (taga (Symbolic.pc ms)) (taga w0) Other t2
            wmc (MTag vtgm (Pointer.component tpc) None false)
            (Symbolic.internal ms)).
  + exact: Symbolic.state_eta.
  + by case: (w0) Hv.
  + move: Hdec => /= Hdec. exact: Hdec.
  + rewrite Hw1 in Hr1. exact Hr1.
  + exact Hr2.
  + exact Hmc.
  + rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc.
    rewrite /Symbolic.pcv in Hv'.
    rewrite Hv'.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt)
              = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
    rewrite Hrc /=.
    rewrite /Merged.transfer /Merged.instr_rules.
    rewrite Hpct Htagv /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite /check_belong /belong Htagv' Ecell2 /= eqxx /=.
    rewrite -/ts' /=.
    rewrite /Symbolic.next_state_do_update /updm.
    rewrite Hw1 in Hr1.
    rewrite Hr1 /= (setmI Hr1) Hr2 /= Hmc /=.
    by [].
- constructor.
  + exact: Hpc'.
  + rewrite /Symbolic.pct /= Hpct.
    by rewrite Pointer.inc_preserves_component.
  +
    rewrite /= /ts'.
    case: Hcase2 => [[Et2 Hv2]|[Et2c Evto Hu2]].
    * rewrite Et2 Evt.
      apply: mregs_rel_set; first exact: Hregs.
      exact: (tvrel_retag Hv2).
    * rewrite Et2c /= Evto Hu2 /=.
      apply: mregs_rel_set_clob.
      exact: Hregs.
  +
    exact: Hinj'.
  +
    move=> w vv Hvv /=.
    rewrite setmE.
    case: (altP (w =P addr)) => [Ew|_]; last exact: Hcode.
    exfalso.
    subst w.
    have Hv2' := Hcode _ _ Hvv.
    have Evv : vv = Atom wmc (MTag vtgm (Pointer.component tpc) None false).
    { move: Hv2'. rewrite /addr Hmc. by move=> [->]. }
    have [n2 [i2 [t2x [Hn2 Htag2]]]] := encode_code_tag Hvv.
    have Hicc2 := codeW_is_code Hn2.
    rewrite Evv /= in Htag2.
    rewrite -Htag2 /= in Hicc2.
    by discriminate Hicc2.
  + exact: sysregs_ok_setm Hsys.
  + exact: gap_setm Hgap Hmc.
- exact: domm_setm_pres Hmc.
- split.
  + exact: Ha.
  + exact: Hr2.
- split.
  + split.
    * exact: erefl.
    * exact: erefl.
  + case: Hcase2 => [[Et2 _]|[Et2c Evto Hu2]].
    * left. exact: Et2.
    * right. split.
      -- exact: Et2c.
      -- exact: Evto.
      -- exact: Hu2.
Qed.

(* ================================================================== *)
(* 9. HALT: a T final state is an me final state.                     *)
(* ================================================================== *)

Lemma sim_halt (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (tpc : Pointer.t) (tpct : Transitional.pc_tag)
    (ms : @Symbolic.state mt lrc_tags unit)
    (tg : mem_tag) (c : Component.id) :
  match_statesW amap tmem tregs tpc tpct ms ->
  Transitional.executing cdeW tpc TrHalt tg c ->
  RSCDefs.final_halt_code ms.
Proof.
move=> Hm Hex0.
have [Ec Hic Hcol] := executing_props Hex0.
subst c.
case: tg Hex0 Hic Hcol => vt0 col0 ent0 isc0 Hex0 /= Hic Hcol.
subst isc0 col0.
set tg := MTag vt0 (Pointer.component tpc) ent0 true.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrHalt, tg)) 0
  = Some (MrHalt, tg) by [].
case: Hm => Hpc Hpct Hregs Hmem Hcode Hsys Hgap.
have [pos [w0 [Hwv Hv Htagv Hdec _]]] :=
  match_fetch Hbound Hcode Hex0 Hpc Hcell.
rewrite /RSCDefs.final_halt_code.
case: ms Hv Hdec Htagv {Hpc Hpct Hregs Hmem Hcode Hwv Hsys Hgap}
  => mmem mregs [pcw pct] intr.
rewrite /Symbolic.pcv /= => Hv Hdec Htagv.
rewrite Hv.
case: (w0) Hv Hdec Htagv => iv it Hv /= Hdec Htagv.
split.
- exact: Hdec.
- by rewrite Htagv.
Qed.

(* ================================================================== *)
(* 10. JUMP (internal): invert the register's [code_rel] through       *)
(*     [cmap_pc_rel]; the 12-register scan computes literally, every    *)
(*     update a self-read ([setmI]).                                    *)
(* ================================================================== *)

(* [check_pc_jump]'s content *)
Lemma check_pc_jump_ex (cde0 : Transitional.code) (tg1 : mem_tag)
    (pc1 : Pointer.t) (c1 : Component.id) :
  Transitional.check_pc_jump cde0 tg1 pc1 c1 ->
  exists i2 tni2,
    Transitional.executing cde0 pc1 i2 tni2 (Pointer.component pc1).
Proof.
move=> H.
inversion H as [cde2 tg2 pc2 i2 tni2 c2 c02 Hex2 Ecomp2]; subst.
exists i2, tni2.
case: Hex2 => C_code [Ecomp3 Hrest].
exists C_code.
split; first by [].
move: Hrest. rewrite -Ecomp3. by [].
Qed.

Lemma sim_jump (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (tpc : Pointer.t) (tpct : Transitional.pc_tag)
    (ms : @Symbolic.state mt lrc_tags unit)
    (tg : mem_tag) (c : Component.id) (r : register) (pc' : Pointer.t) :
  match_statesW amap tmem tregs tpc tpct ms ->
  reg_syncedW amap tregs (Symbolic.regs ms) r ->
  Transitional.executing cdeW tpc (TrJump r) tg c ->
  Transitional.Register.get r tregs
    = Transitional.MVal InternalJump (Ptr pc') ->
  Pointer.component pc' = Pointer.component tpc ->
  Transitional.check_pc_jump cdeW tg pc' c ->
  exists ms',
    [/\ step_me (NC := NC) ms ms' None,
        match_statesW amap tmem tregs pc' tpct ms',
        domm (Symbolic.mem ms') = domm (Symbolic.mem ms),
        Symbolic.regs ms' = Symbolic.regs ms
      & Symbolic.mem ms' = Symbolic.mem ms].
Proof.
move=> Hm Hsyncr Hex0 Hget Hcomp' Hcpj.
have [Ec Hic Hcol] := executing_props Hex0.
rewrite {}Ec in Hex0 Hcol Hcpj.
case: tg Hex0 Hic Hcol Hcpj => vt0 col0 ent0 isc0 Hex0 /= Hic Hcol Hcpj.
subst isc0 col0.
set tg := MTag vt0 (Pointer.component tpc) ent0 true.
have [i2 [tni2 Hex2]] := check_pc_jump_ex Hcpj.
have [_ E2ic E2col] := executing_props Hex2.
have [cell2 Hcell2] : exists cell2,
    List.nth_error
      (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB) (i2, tni2)) 0
    = Some cell2.
{ apply: nth_error_Some_ex.
  rewrite lin_size_length size_cell_exp. by case: i2 {Hex2}. }
have Ecell22 : cell2.2 = tni2 := cell_exp_snd Hcell2.
case: Hm => Hpc Hpct Hregs Hmem Hcode Hsys Hgap.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrJump r, tg)) 0
  = Some (MrJump r, tg) by [].
have [pos [w0 [Hwv Hv Htagv Hdec _]]] :=
  match_fetch Hbound Hcode Hex0 Hpc Hcell.
have [rar [Hrr Hvr Htr]] := Hsyncr.
case: rar Hrr Hvr Htr => wr tr Hrr Hvr Htr.
rewrite /= in Hvr Htr.
have Etr : tr = InternalJump by rewrite Htr Hget.
rewrite {}Etr in Hrr.
have Hcr : code_rel cmapWW (Ptr pc') wr.
{ by move: Hvr; rewrite /tvrel Hget /=. }
case: Hcr => cp [bp [op [posc [Eptr Hcm Hop Ew]]]].
have Epc : pc' = (cp, bp, op) by case: Eptr.
have Ecp : Pointer.component pc' = cp by rewrite Epc.
have Eop : Pointer.offset pc' = op by rewrite Epc.
have Hcm' : cmapWW (Pointer.component pc')
              (BinInt.Z.to_nat (Pointer.offset pc')) = Some posc.
{ by rewrite Ecp Eop. }
have Hop' : BinInt.Z.le 0 (Pointer.offset pc') by rewrite Eop.
have Hpc2 : pc_rel L P C pra prb PB PI pc' wr.
{ exact: (cmap_pc_rel Hcm' Hop' Ew). }
have [posf [v2 [Hwv2 Hv2m Htagv2 Hdec2 _]]] :=
  match_fetch Hbound Hcode Hex2 Hpc2 Hcell2.
case: tni2 Hex2 E2ic E2col Ecell22 {Hcell2} => vt2 col2 ent2 isc2
  Hex2 /= E2ic E2col Ecell22.
subst isc2.
rewrite Hcomp' in E2col.
subst col2.
have [Ara HraL] := mregs_rel_lookup R_RA Hregs.
case: Ara HraL => wra tra HraL.
have [A1 HA1] := mregs_rel_lookup R_COM Hregs.
case: A1 HA1 => w1' t1' HA1.
have [A0 HA0] := mregs_rel_lookup R_ONE Hregs.
case: A0 HA0 => w0' t0' HA0.
have [A2 HA2] := mregs_rel_lookup R_AUX1 Hregs.
case: A2 HA2 => w2' t2' HA2.
have [A3 HA3] := mregs_rel_lookup R_AUX2 Hregs.
case: A3 HA3 => w3' t3' HA3.
have [A5 HA5] := mregs_rel_lookup R_SP Hregs.
case: A5 HA5 => w5' t5' HA5.
have [A6 HA6] := mregs_rel_lookup R_ARG Hregs.
case: A6 HA6 => w6' t6' HA6.
have [A7 HA7] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 7) = Some a
  by apply: Hsys; rewrite !inE eqxx.
case: A7 HA7 => w7' t7' HA7.
have [A16 HA16] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 16) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
case: A16 HA16 => w16' t16' HA16.
have [A17 HA17] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 17) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
case: A17 HA17 => w17' t17' HA17.
have [A18 HA18] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 18) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
case: A18 HA18 => w18' t18' HA18.
have [A19 HA19] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 19) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
case: A19 HA19 => w19' t19' HA19.
have HA1c : Symbolic.regs ms (word.as_word (ssrint.Posz 1))
            = Some (Atom w1' t1') := HA1.
have HA0c : Symbolic.regs ms (word.as_word (ssrint.Posz 0))
            = Some (Atom w0' t0') := HA0.
have HA2c : Symbolic.regs ms (word.as_word (ssrint.Posz 2))
            = Some (Atom w2' t2') := HA2.
have HA3c : Symbolic.regs ms (word.as_word (ssrint.Posz 3))
            = Some (Atom w3' t3') := HA3.
have HA5c : Symbolic.regs ms (word.as_word (ssrint.Posz 5))
            = Some (Atom w5' t5') := HA5.
have HA6c : Symbolic.regs ms (word.as_word (ssrint.Posz 6))
            = Some (Atom w6' t6') := HA6.
have HA7c : Symbolic.regs ms (word.as_word (ssrint.Posz 7))
            = Some (Atom w7' t7') := HA7.
have HA16c : Symbolic.regs ms (word.as_word (ssrint.Posz 16))
            = Some (Atom w16' t16') := HA16.
have HA17c : Symbolic.regs ms (word.as_word (ssrint.Posz 17))
            = Some (Atom w17' t17') := HA17.
have HA18c : Symbolic.regs ms (word.as_word (ssrint.Posz 18))
            = Some (Atom w18' t18') := HA18.
have HA19c : Symbolic.regs ms (word.as_word (ssrint.Posz 19))
            = Some (Atom w19' t19') := HA19.
have Hclear : Symbolic.reg_clear_list (Symbolic.regs ms) InternalJump
  = Some [hseq InternalJump; t1'; t0'; t2'; t3'; t5'; t6'; t7';
          t16'; t17'; t18'; t19'].
{ rewrite /Symbolic.reg_clear_list /=.
  by rewrite HA1c /= HA0c /= HA2c /= HA3c /= HA5c /= HA6c /= HA7c /=
             HA16c /= HA17c /= HA18c /= HA19c /=. }
rewrite /Symbolic.pct in Hpct.
exists (@Symbolic.State mt lrc_tags unit
          (Symbolic.mem ms) (Symbolic.regs ms)
          wr@(taga (Symbolic.pc ms)) (Symbolic.internal ms)).
split.
- rewrite /step_me.
  apply: (@Symbolic.step_jump _ _ _ _ _ _ _ _ _
            (Symbolic.mem ms) (Symbolic.regs ms) (Symbolic.pcv ms)
            (vala w0)
            (@word_of_nat (reg_field_size mt)
               (Intermediate.Register.to_nat r))
            wr
            (taga (Symbolic.pc ms)) (taga w0) InternalJump
            (Symbolic.internal ms)
            [hseq InternalJump; t1'; t0'; t2'; t3'; t5'; t6'; t7';
             t16'; t17'; t18'; t19']
            wra tra).
  + exact: Symbolic.state_eta.
  + by case: (w0) Hv.
  + move: Hdec => /= Hdec. exact: Hdec.
  + exact: Hrr.
  + exact: HraL.
  + exact: Hclear.
  + rewrite /Symbolic.next_state_updates_and_pc.
    rewrite Hv2m.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt)
              = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
    rewrite HA1 /=.
    rewrite /Merged.transfer /Merged.instr_rules.
    rewrite Hpct Htagv /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite Htagv2 Ecell22 /= eqxx /=.
    rewrite /Symbolic.next_state_do_update /updm.
    rewrite HraL /= (setmI HraL).
    rewrite Hrr /= (setmI Hrr).
    rewrite HA1c /= (setmI HA1c).
    rewrite HA0c /= (setmI HA0c).
    rewrite HA2c /= (setmI HA2c).
    rewrite HA3c /= (setmI HA3c).
    rewrite HA5c /= (setmI HA5c).
    rewrite HA6c /= (setmI HA6c).
    rewrite HA7c /= (setmI HA7c).
    rewrite HA16c /= (setmI HA16c).
    rewrite HA17c /= (setmI HA17c).
    rewrite HA18c /= (setmI HA18c).
    rewrite HA19c /= (setmI HA19c).
    by [].
- constructor.
  +
    rewrite /Symbolic.pcv /=. exact: Hpc2.
  +
    rewrite /Symbolic.pct /= Hpct.
    by rewrite Hcomp'.
  + exact: Hregs.
  + exact: Hmem.
  + exact: Hcode.
  + exact: Hsys.
  + exact: Hgap.
- exact: erefl.
- exact: erefl.
- exact: erefl.
Qed.

(* ================================================================== *)
(* 11. The T-side label bridge: [find_label] inverted to the array    *)
(*     position of the defining [TrLabel] cell (feeds MPosT's         *)
(*     [tlink_label_pos_body_*] for the Jal/BnzNZ targets).           *)
(* ================================================================== *)

(* [find_label]'s counter is a local fix; top-level twin + bridge *)
Fixpoint laux (cd : seq (Transitional.instr * mem_tag))
    (l : label) (o : Z) : option Z :=
  match cd with
  | [::] => None
  | (TrLabel (inl l'), _) :: c' =>
      if Nat.eqb l l' then Some o else laux c' l (BinInt.Z.add 1 o)
  | _ :: c' => laux c' l (BinInt.Z.add 1 o)
  end.

Lemma find_label_laux cd l :
  Transitional.find_label cd l = laux cd l BinNums.Z0.
Proof.
rewrite /Transitional.find_label.
elim: cd (BinNums.Z0) => [|[i tg] cd IH] o //=.
by case: i => [|[l'|[c' p']]|v r|r1 r2|op r1 r2 r3|r1 r2|r1 r2|r1 r2
              |r l0|r|l0|lp|] /=; rewrite -?IH; case: cd {IH}.
Qed.

(* keep the accumulator arithmetic folded ([simpl] shreds [Z.add 1 o]
   into a raw match that lia cannot read) *)
Local Arguments BinInt.Z.add : simpl never.
Local Arguments BinInt.Z.sub : simpl never.

Lemma laux_nth cd l (o z : Z) :
  laux cd l o = Some z ->
  BinInt.Z.le o z /\
  exists xt,
    List.nth_error cd (BinInt.Z.to_nat (BinInt.Z.sub z o))
    = Some (TrLabel (inl l), xt).
Proof.
elim: cd o => [|[i tg] cd IH] o //=.
case: i => [|pl|v r|r1 r2|op r1 r2 r3|r1 r2|r1 r2|r1 r2|r l0|r|l0|lp|].
2: { case: pl => [l'|[c' p']].
     - case E: (Nat.eqb l l').
       + move=> [<-]. split; first by lia.
         exists tg.
         have -> : BinInt.Z.to_nat (BinInt.Z.sub o o) = 0 by lia.
         by move/PeanoNat.Nat.eqb_eq: E => <-.
       + move=> /IH [Hle [xt Hnth]].
         split; first by lia.
         exists xt.
         have -> : BinInt.Z.to_nat (BinInt.Z.sub z o)
                 = (BinInt.Z.to_nat
                      (BinInt.Z.sub z (BinInt.Z.add 1 o))).+1 by lia.
         exact: Hnth.
     - move=> /IH [Hle [xt Hnth]].
       split; first by lia.
       exists xt.
       have -> : BinInt.Z.to_nat (BinInt.Z.sub z o)
               = (BinInt.Z.to_nat
                    (BinInt.Z.sub z (BinInt.Z.add 1 o))).+1 by lia.
       exact: Hnth. }
all: move=> /IH [Hle [xt Hnth]];
  split; [by lia|];
  exists xt;
  (have -> : BinInt.Z.to_nat (BinInt.Z.sub z o)
           = (BinInt.Z.to_nat
                (BinInt.Z.sub z (BinInt.Z.add 1 o))).+1 by lia);
  exact: Hnth.
Qed.

(* the payoff: a successful [find_label_in_comp] pins the label cell *)
Lemma find_label_in_comp_nth (cde0 : Transitional.code)
    (c : Component.id) (l : label) (pc1 : Pointer.t) :
  Transitional.find_label_in_comp cde0 c l = Some pc1 ->
  exists cseg xt,
    [/\ cde0 c = Some cseg,
        pc1 = (c, 0, Pointer.offset pc1),
        BinInt.Z.le 0 (Pointer.offset pc1)
      & List.nth_error cseg (BinInt.Z.to_nat (Pointer.offset pc1))
        = Some (TrLabel (inl l), xt)].
Proof.
rewrite /Transitional.find_label_in_comp.
case Hc: (cde0 c) => [cseg|] //.
case Hf: (Transitional.find_label cseg l) => [z|] // [Epc].
move: Hf; rewrite find_label_laux => /laux_nth [Hle [xt Hnth]].
exists cseg, xt.
subst pc1.
split.
- by [].
- by [].
- exact: Hle.
- rewrite /=.
  rewrite BinInt.Z.sub_0_r in Hnth.
  exact: Hnth.
Qed.

(* ================================================================== *)
(* 12. Jal: the jump-and-link diagram.                                *)
(* ================================================================== *)

(* the label statics feeding the me-side label-position bridges
   (ILabel bound, component bound, per-label uniqueness) *)
Hypothesis Hlab_a : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures pra cid = Some Cprocs ->
  Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hlab_b : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures prb cid = Some Cprocs ->
  Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hcomp_a : forall cid,
  cid \in domm (Intermediate.prog_procedures pra) -> cid < C.
Hypothesis Hcomp_b : forall cid,
  cid \in domm (Intermediate.prog_procedures prb) -> cid < C.
Hypothesis Huniq_a : forall cid l0 Cprocs0,
  Intermediate.prog_procedures pra cid = Some Cprocs0 ->
  sumn [seq count (ilab l0) (odflt [::] (Cprocs0 p')) | p' <- domm Cprocs0]
  <= 1.
Hypothesis Huniq_b : forall cid l0 Cprocs0,
  Intermediate.prog_procedures prb cid = Some Cprocs0 ->
  sumn [seq count (ilab l0) (odflt [::] (Cprocs0 p')) | p' <- domm Cprocs0]
  <= 1.

(* procedure-map disjointness, from linkability + well-formedness *)
Let Hdisj : fdisjoint (domm (Intermediate.prog_procedures pra))
                      (domm (Intermediate.prog_procedures prb)).
Proof.
case: Hlinkable => _ Hd.
rewrite -(Intermediate.wfprog_defined_procedures Hwfa)
        -(Intermediate.wfprog_defined_procedures Hwfb).
exact: Hd.
Qed.

(* a pc relation IS a code capability *)
Lemma pc_rel_code_rel (p : Pointer.t) (w : mword mt) :
  pc_relW p w -> code_rel cmapWW (Ptr p) w.
Proof.
case: p => [[cp bp] op] Hp.
have [pos [Hcm Hle Hw]] := pc_rel_cmap Hp.
exists cp, bp, op, pos.
split.
- by [].
- exact: Hcm.
- exact: Hle.
- exact: Hw.
Qed.

(* a non-R_RA scan key survives the R_RA write *)
Lemma askey_ra_neq (k : nat) :
  k < 32 -> (k == 4) = false ->
  (word.as_word (ssrint.Posz k) == (ra : reg mt)) = false.
Proof.
move=> Hk Hne.
have H4 : (4 : nat) < 32 by [].
have H := won_eqE (small_lt_reg Hk) (small_lt_reg H4).
rewrite Hne in H.
exact: H.
Qed.

Lemma setm_ra_other (mregs : {fmap reg mt -> @ratom mt})
    (a b : @ratom mt) (k : nat) :
  k < 32 -> (k == 4) = false ->
  mregs (word.as_word (ssrint.Posz k)) = Some b ->
  setm mregs (ra : reg mt) a (word.as_word (ssrint.Posz k)) = Some b.
Proof.
move=> Hk Hne Hb.
rewrite setmE (askey_ra_neq Hk Hne).
exact: Hb.
Qed.

Lemma sim_jal (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (tpc : Pointer.t) (tpct : Transitional.pc_tag)
    (ms : @Symbolic.state mt lrc_tags unit)
    (tg : mem_tag) (c : Component.id) (l : label) (pc' : Pointer.t)
    (i3 : Transitional.instr) (tg3 : mem_tag) :
  match_statesW amap tmem tregs tpc tpct ms ->
  Transitional.executing cdeW tpc (TrJalNat l) tg c ->
  Transitional.find_label_in_comp cdeW c l = Some pc' ->
  Transitional.check_pc_jump cdeW tg pc' c ->
  Transitional.executing cdeW (Pointer.inc tpc) i3 tg3 c ->
  l < L ->
  exists ms' ra_me,
    [/\ step_me (NC := NC) ms ms' None,
        match_statesW amap tmem
          (Transitional.Register.set R_RA (Ptr (Pointer.inc tpc))
             InternalJump tregs)
          pc' tpct ms',
        domm (Symbolic.mem ms') = domm (Symbolic.mem ms),
        Symbolic.regs ms'
          = setm (Symbolic.regs ms)
              (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat R_RA)) ra_me
      & Symbolic.mem ms' = Symbolic.mem ms].
Proof.
move=> Hm Hex0 Hfind Hcpj Hex3 HlL.
have [Ec Hic Hcol] := executing_props Hex0.
rewrite {}Ec in Hex0 Hcol Hcpj Hfind Hex3.
case: tg Hex0 Hic Hcol Hcpj => vt0 col0 ent0 isc0 Hex0 /= Hic Hcol Hcpj.
subst isc0 col0.
set tg := MTag vt0 (Pointer.component tpc) ent0 true.
have [csegW [xt [Hcw Epc' Hz Hnthlab]]] := find_label_in_comp_nth Hfind.
have Ecomp' : Pointer.component pc' = Pointer.component tpc
  by rewrite {1}Epc'.
have [i2 [tni2 Hex2]] := check_pc_jump_ex Hcpj.
have [_ E2ic E2col] := executing_props Hex2.
have Hnth2 : List.nth_error csegW
    (BinInt.Z.to_nat (Pointer.offset pc')) = Some (i2, tni2).
{ case: Hex2 => C2 [_ [Hcde2 [_ Hn2]]].
  move: Hcde2 Hn2. rewrite Ecomp' Hcw. move=> [<-]. by []. }
move: Hnthlab; rewrite Hnth2 => - [Ei2 Ext].
subst i2 xt.
case: tni2 Hex2 E2ic E2col Hnth2 => vt2 col2 ent2 isc2
  Hex2 /= E2ic E2col Hnth2.
subst isc2.
rewrite Ecomp' in E2col.
subst col2.
have [_ H3ic H3col] := executing_props Hex3.
case: tg3 Hex3 H3ic H3col => vt3 col3 ent3 isc3 Hex3 /= H3ic H3col.
subst isc3 col3.
case: Hm => Hpc Hpct Hregs Hmem Hcode Hsys Hgap.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrJalNat l, tg)) 0
  = Some (MrJal (can_upd L (Pointer.component tpc) l), tg) by [].
have [pos [v [Hwv Hv Htagv Hdec _]]] :=
  match_fetch Hbound Hcode Hex0 Hpc Hcell.
have [cell3 Hcell3] : exists cell3,
    List.nth_error
      (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
         (i3, MTag vt3 (Pointer.component tpc) ent3 true)) 0
    = Some cell3.
{ apply: nth_error_Some_ex.
  rewrite lin_size_length size_cell_exp. by case: i3 {Hex3}. }
have Ecell3 : cell3.2 = MTag vt3 (Pointer.component tpc) ent3 true
  := cell_exp_snd Hcell3.
have [pos2 [vret [Hw2 Haddr Hvret Htagvret Hpcinc]]] :=
  silent_next (i := TrJalNat l) (erefl _) Hcode Hex0 Hex3 Hpc Hcell3.
case: vret Hvret Htagvret => vret_v tret_t Hvret /= Htagvret.
rewrite {}Ecell3 in Htagvret.
subst tret_t.
have Hcr : tvrel cmapWW amap
    (Transitional.MVal InternalJump (Ptr (Pointer.inc tpc)))
    (addw (Symbolic.pcv ms) onew).
{ rewrite /tvrel /=. exact: pc_rel_code_rel Hpcinc. }
have H1415 : Merged.alloc_label < 2 ^ imm_size mt.
{ rewrite /Merged.alloc_label imm_size_mt. by rewrite ltn_exp2l. }
have Hlin32 : size (linearize_bufs PB) < 2 ^ word_size mt.
{ have H1532 : (2 : nat) ^ imm_size mt < 2 ^ word_size mt
    by rewrite imm_size_mt word_size_mt ltn_exp2l.
  by lia. }
have Hpc0E : size (initial_memory (mt := mt) PB)
             = size (linearize_bufs PB)
  := initial_memory_size_eq Hlin32.
have [poslab [Hlp Hbnd Hpc2]] : exists poslab,
    [/\ forall default,
          code_label_pos codeW pc0
            (can_upd L (Pointer.component tpc) l) default
          = pc0 + poslab,
        pc0 + poslab < 2 ^ imm_size mt
      & pc_relW pc' (@word_of_nat (word_size mt) (pc0 + poslab))].
{ case E: (Pointer.component tpc \in domm (Intermediate.prog_procedures pra)).
  -
    have Hseg : Transitional.intermediate_to_transitional_gen PI pra
                  (Pointer.component tpc) = Some csegW.
    { rewrite -(cdeW_left prb PI E). exact: Hcw. }
    have Hcolx : color (MTag vt2 (Pointer.component tpc) ent2 true)
                 = Pointer.component tpc by [].
    have Hnthc := tlink_body_nth_l L P C prb PB Hseg Hnth2 Hcolx.
    have Hposlt := nth_error_lt Hnthc.
    exists (tpos PI pra (Pointer.component tpc) csegW
              (BinInt.Z.to_nat (Pointer.offset pc')) + 0).
    split.
    + move=> default.
      rewrite /can_upd.
      exact: (tlink_label_pos_body_l P PB Hlab_a Hcomp_a Hlab_b Hdisj
                Hseg Hnth2 Hcolx HlL
                (@Huniq_a (Pointer.component tpc) l) pc0 default).
    + by lia.
    + apply: (@PCLeft _ _ _ _ _ _ _ _ _ csegW).
      * by rewrite Ecomp' E.
      * by rewrite Ecomp' Hseg.
      * by lia.
      * congr word_of_nat. rewrite Ecomp'. by lia.
  -
    have Hseg : Transitional.intermediate_to_transitional_gen PI prb
                  (Pointer.component tpc) = Some csegW.
    { rewrite -(cdeW_right prb PI (negbT E)). exact: Hcw. }
    have Hcolx : color (MTag vt2 (Pointer.component tpc) ent2 true)
                 = Pointer.component tpc by [].
    have Hnthc := tlink_body_nth_r L P C pra PB Hseg Hnth2 Hcolx.
    have Hposlt := nth_error_lt Hnthc.
    exists (size (compiler_code L P C PB PI pra)
            + (tpos PI prb (Pointer.component tpc) csegW
                 (BinInt.Z.to_nat (Pointer.offset pc')) + 0)).
    split.
    + move=> default.
      rewrite /can_upd.
      exact: (tlink_label_pos_body_r P PB Hlab_a Hlab_b Hcomp_b Hdisj
                Hseg Hnth2 Hcolx HlL
                (@Huniq_b (Pointer.component tpc) l) pc0 default).
    + by lia.
    + apply: (@PCRight _ _ _ _ _ _ _ _ _ csegW).
      * by rewrite Ecomp' E.
      * by rewrite Ecomp' Hseg.
      * by lia.
      * congr word_of_nat. rewrite Ecomp'. by lia. }
have Hcell2 : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrLabel (inl l), MTag vt2 (Pointer.component tpc) ent2 true)) 0
  = Some (MrLabel (can_upd L (Pointer.component tpc) l),
          MTag vt2 (Pointer.component tpc) ent2 true) by [].
have [posf [v2 [Hwv2 Hv2m Htagv2 Hdec2 _]]] :=
  match_fetch Hbound Hcode Hex2 Hpc2 Hcell2.
have [Ara HraL] := mregs_rel_lookup R_RA Hregs.
case: Ara HraL => wra tra HraL.
have [A1 HA1] := mregs_rel_lookup R_COM Hregs.
case: A1 HA1 => w1' t1' HA1.
have [A0 HA0] := mregs_rel_lookup R_ONE Hregs.
case: A0 HA0 => w0' t0' HA0.
have [A2 HA2] := mregs_rel_lookup R_AUX1 Hregs.
case: A2 HA2 => w2' t2' HA2.
have [A3 HA3] := mregs_rel_lookup R_AUX2 Hregs.
case: A3 HA3 => w3' t3' HA3.
have [A5 HA5] := mregs_rel_lookup R_SP Hregs.
case: A5 HA5 => w5' t5' HA5.
have [A6 HA6] := mregs_rel_lookup R_ARG Hregs.
case: A6 HA6 => w6' t6' HA6.
have [A7 HA7] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 7) = Some a
  by apply: Hsys; rewrite !inE eqxx.
case: A7 HA7 => w7' t7' HA7.
have [A16 HA16] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 16) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
case: A16 HA16 => w16' t16' HA16.
have [A17 HA17] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 17) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
case: A17 HA17 => w17' t17' HA17.
have [A18 HA18] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 18) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
case: A18 HA18 => w18' t18' HA18.
have [A19 HA19] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 19) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
case: A19 HA19 => w19' t19' HA19.
have HA1c : Symbolic.regs ms (word.as_word (ssrint.Posz 1))
            = Some (Atom w1' t1') := HA1.
have HA0c : Symbolic.regs ms (word.as_word (ssrint.Posz 0))
            = Some (Atom w0' t0') := HA0.
have HA2c : Symbolic.regs ms (word.as_word (ssrint.Posz 2))
            = Some (Atom w2' t2') := HA2.
have HA3c : Symbolic.regs ms (word.as_word (ssrint.Posz 3))
            = Some (Atom w3' t3') := HA3.
have HA5c : Symbolic.regs ms (word.as_word (ssrint.Posz 5))
            = Some (Atom w5' t5') := HA5.
have HA6c : Symbolic.regs ms (word.as_word (ssrint.Posz 6))
            = Some (Atom w6' t6') := HA6.
have HA7c : Symbolic.regs ms (word.as_word (ssrint.Posz 7))
            = Some (Atom w7' t7') := HA7.
have HA16c : Symbolic.regs ms (word.as_word (ssrint.Posz 16))
            = Some (Atom w16' t16') := HA16.
have HA17c : Symbolic.regs ms (word.as_word (ssrint.Posz 17))
            = Some (Atom w17' t17') := HA17.
have HA18c : Symbolic.regs ms (word.as_word (ssrint.Posz 18))
            = Some (Atom w18' t18') := HA18.
have HA19c : Symbolic.regs ms (word.as_word (ssrint.Posz 19))
            = Some (Atom w19' t19') := HA19.
have Hclear : Symbolic.reg_clear_list (Symbolic.regs ms) tra
  = Some [hseq tra; t1'; t0'; t2'; t3'; t5'; t6'; t7';
          t16'; t17'; t18'; t19'].
{ rewrite /Symbolic.reg_clear_list /=.
  by rewrite HA1c /= HA0c /= HA2c /= HA3c /= HA5c /= HA6c /= HA7c /=
             HA16c /= HA17c /= HA18c /= HA19c /=. }
move: Hdec => /= Hdec.
rewrite Hlp in Hdec.
have Ecast : @swcast (imm_size mt) (word_size mt)
               (@word_of_nat (imm_size mt) (pc0 + poslab))
             = @word_of_nat (word_size mt) (pc0 + poslab)
  := swcast_word_of_nat_small Hbnd.
have HB1 : setm (Symbolic.regs ms) (ra : reg mt)
             (Atom (addw (Symbolic.pcv ms) onew) InternalJump)
             (word.as_word (ssrint.Posz 1)) = Some (Atom w1' t1')
  by apply: setm_ra_other.
have HB0 : setm (Symbolic.regs ms) (ra : reg mt)
             (Atom (addw (Symbolic.pcv ms) onew) InternalJump)
             (word.as_word (ssrint.Posz 0)) = Some (Atom w0' t0')
  by apply: setm_ra_other.
have HB2 : setm (Symbolic.regs ms) (ra : reg mt)
             (Atom (addw (Symbolic.pcv ms) onew) InternalJump)
             (word.as_word (ssrint.Posz 2)) = Some (Atom w2' t2')
  by apply: setm_ra_other.
have HB3 : setm (Symbolic.regs ms) (ra : reg mt)
             (Atom (addw (Symbolic.pcv ms) onew) InternalJump)
             (word.as_word (ssrint.Posz 3)) = Some (Atom w3' t3')
  by apply: setm_ra_other.
have HB5 : setm (Symbolic.regs ms) (ra : reg mt)
             (Atom (addw (Symbolic.pcv ms) onew) InternalJump)
             (word.as_word (ssrint.Posz 5)) = Some (Atom w5' t5')
  by apply: setm_ra_other.
have HB6 : setm (Symbolic.regs ms) (ra : reg mt)
             (Atom (addw (Symbolic.pcv ms) onew) InternalJump)
             (word.as_word (ssrint.Posz 6)) = Some (Atom w6' t6')
  by apply: setm_ra_other.
have HB7 : setm (Symbolic.regs ms) (ra : reg mt)
             (Atom (addw (Symbolic.pcv ms) onew) InternalJump)
             (word.as_word (ssrint.Posz 7)) = Some (Atom w7' t7')
  by apply: setm_ra_other.
have HB16 : setm (Symbolic.regs ms) (ra : reg mt)
              (Atom (addw (Symbolic.pcv ms) onew) InternalJump)
              (word.as_word (ssrint.Posz 16)) = Some (Atom w16' t16')
  by apply: setm_ra_other.
have HB17 : setm (Symbolic.regs ms) (ra : reg mt)
              (Atom (addw (Symbolic.pcv ms) onew) InternalJump)
              (word.as_word (ssrint.Posz 17)) = Some (Atom w17' t17')
  by apply: setm_ra_other.
have HB18 : setm (Symbolic.regs ms) (ra : reg mt)
              (Atom (addw (Symbolic.pcv ms) onew) InternalJump)
              (word.as_word (ssrint.Posz 18)) = Some (Atom w18' t18')
  by apply: setm_ra_other.
have HB19 : setm (Symbolic.regs ms) (ra : reg mt)
              (Atom (addw (Symbolic.pcv ms) onew) InternalJump)
              (word.as_word (ssrint.Posz 19)) = Some (Atom w19' t19')
  by apply: setm_ra_other.
rewrite /Symbolic.pct in Hpct.
exists (@Symbolic.State mt lrc_tags unit
          (Symbolic.mem ms)
          (setm (Symbolic.regs ms)
             (@word_of_nat (reg_field_size mt)
                (Intermediate.Register.to_nat R_RA))
             (Atom (addw (Symbolic.pcv ms) onew) InternalJump))
          (@word_of_nat (word_size mt) (pc0 + poslab))
            @(taga (Symbolic.pc ms))
          (Symbolic.internal ms)),
       (Atom (addw (Symbolic.pcv ms) onew) InternalJump).
split.
- rewrite /step_me.
  apply: (@Symbolic.step_jal _ _ _ _ _ _ _ _ _
            (Symbolic.mem ms) (Symbolic.regs ms) (Symbolic.pcv ms)
            (vala v)
            (@word_of_nat (imm_size mt) (pc0 + poslab))
            (taga (Symbolic.pc ms)) (taga v)
            wra tra
            (Symbolic.internal ms)
            [hseq tra; t1'; t0'; t2'; t3'; t5'; t6'; t7';
             t16'; t17'; t18'; t19']
            vret_v (MTag vt3 (Pointer.component tpc) ent3 true)).
  + exact: Symbolic.state_eta.
  + by case: (v) Hv.
  + exact: Hvret.
  + exact: Hdec.
  + exact: HraL.
  + exact: Hclear.
  +
    rewrite /Symbolic.next_state_updates_and_pc.
    rewrite Ecast Hv2m.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt)
              = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
    rewrite HA1 /=.
    rewrite /Merged.transfer /Merged.instr_rules.
    rewrite Hpct Htagv /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite Htagv2 /= eqxx /=.
    rewrite /check_belong /belong /= eqxx /=.
    rewrite /Symbolic.next_state_do_update /updm.
    rewrite Hvret /= (setmI Hvret).
    rewrite HraL /=.
    rewrite HB1 /= (setmI HB1).
    rewrite HB0 /= (setmI HB0).
    rewrite HB2 /= (setmI HB2).
    rewrite HB3 /= (setmI HB3).
    rewrite HB5 /= (setmI HB5).
    rewrite HB6 /= (setmI HB6).
    rewrite HB7 /= (setmI HB7).
    rewrite HB16 /= (setmI HB16).
    rewrite HB17 /= (setmI HB17).
    rewrite HB18 /= (setmI HB18).
    rewrite HB19 /= (setmI HB19).
    by [].
- constructor.
  +
    rewrite /Symbolic.pcv /=. exact: Hpc2.
  +
    rewrite /Symbolic.pct /= Hpct.
    by rewrite Ecomp'.
  +
    apply: mregs_rel_set; first exact: Hregs.
    exact: Hcr.
  + exact: Hmem.
  + exact: Hcode.
  + exact: sysregs_ok_setm Hsys.
  + exact: Hgap.
- exact: erefl.
- exact: erefl.
- exact: erefl.
Qed.

(* ================================================================== *)
(* 13. BnzNZ: the taken branch.                                       *)
(* ================================================================== *)

(* [addw] is addition of representatives *)
Lemma addw_word_of_nat (a b : nat) :
  addw (@word_of_nat (word_size mt) a) (@word_of_nat (word_size mt) b)
  = @word_of_nat (word_size mt) (a + b).
Proof.
by rewrite /word_of_nat as_word_addwD.
Qed.

(* [tpos] is monotone in the cell index *)
Lemma tseg_take_leq (cseg : seq (Transitional.instr * mem_tag)) q q' :
  q <= q' ->
  tseg_size (take q cseg) <= tseg_size (take q' cseg).
Proof.
move=> Hq.
rewrite -(cat_take_drop q (take q' cseg)).
rewrite /tseg_size map_cat sumn_cat.
have -> : take q (take q' cseg) = take q cseg.
{ by rewrite take_takel. }
exact: leq_addr.
Qed.

Lemma tpos_leq (PI' : Program.interface) (pr : Intermediate.program)
    (c1 : Component.id) (cseg : seq (Transitional.instr * mem_tag)) q q' :
  q <= q' ->
  tpos PI' pr c1 cseg q <= tpos PI' pr c1 cseg q'.
Proof.
move=> Hq.
rewrite /tpos leq_add2l.
exact: tseg_take_leq.
Qed.

(* a related nonzero integer is a nonzero word *)
Lemma vrel_nonzero (amap : amap_t) (z : Z) (w : mword mt) :
  vrel amap (Int z) w -> z <> BinNums.Z0 -> (w == 0%w) = false.
Proof.
move=> Hv Hnz.
case E: (w == 0%w) => //.
exfalso; apply: Hnz.
move/eqP: E => E; subst w.
have Hr := vrel_int_inv Hv.
move: Hr. rewrite /wrepr.
have -> : (0%w : mword mt) = @word_of_nat (word_size mt) 0 by [].
have Hk : 0 < word_size mt by rewrite word_size_mt.
have Hn0 : 0 < 2 ^ (word_size mt).-1 by rewrite expn_gt0.
rewrite (int_of_word_as_word_pos Hk Hn0) /=.
by move=> <-.
Qed.

Lemma sim_bnzNZ (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (tpc : Pointer.t) (tpct : Transitional.pc_tag)
    (ms : @Symbolic.state mt lrc_tags unit)
    (tg : mem_tag) (c : Component.id) (r : register) (l : label)
    (pc' : Pointer.t) (z : Z) :
  match_statesW amap tmem tregs tpc tpct ms ->
  reg_syncedW amap tregs (Symbolic.regs ms) r ->
  Transitional.executing cdeW tpc (TrBnz r l) tg c ->
  Transitional.tvtag (Transitional.Register.get r tregs) = Other ->
  Transitional.val (Transitional.Register.get r tregs) = Int z ->
  z <> BinNums.Z0 ->
  Transitional.find_label_in_comp cdeW c l = Some pc' ->
  Transitional.check_pc_jump cdeW tg pc' c ->
  BinInt.Z.le (Pointer.offset tpc) (Pointer.offset pc') ->
  l < L ->
  exists ms',
    [/\ step_me (NC := NC) ms ms' None,
        match_statesW amap tmem tregs pc' tpct ms',
        domm (Symbolic.mem ms') = domm (Symbolic.mem ms),
        Symbolic.regs ms' = Symbolic.regs ms
      & Symbolic.mem ms' = Symbolic.mem ms].
Proof.
move=> Hm Hsyncr Hex0 Htag0 Hval0 Hnz Hfind Hcpj Hfwd HlL.
have [Ec Hic Hcol] := executing_props Hex0.
rewrite {}Ec in Hex0 Hcol Hcpj Hfind.
case: tg Hex0 Hic Hcol Hcpj => vt0 col0 ent0 isc0 Hex0 /= Hic Hcol Hcpj.
subst isc0 col0.
set tg := MTag vt0 (Pointer.component tpc) ent0 true.
have [csegW [xt [Hcw Epc' Hz Hnthlab]]] := find_label_in_comp_nth Hfind.
have Ecomp' : Pointer.component pc' = Pointer.component tpc
  by rewrite {1}Epc'.
have [i2 [tni2 Hex2]] := check_pc_jump_ex Hcpj.
have [_ E2ic E2col] := executing_props Hex2.
have Hnth2 : List.nth_error csegW
    (BinInt.Z.to_nat (Pointer.offset pc')) = Some (i2, tni2).
{ case: Hex2 => C2 [_ [Hcde2 [_ Hn2]]].
  move: Hcde2 Hn2. rewrite Ecomp' Hcw. move=> [<-]. by []. }
move: Hnthlab; rewrite Hnth2 => - [Ei2 Ext].
subst i2 xt.
case: tni2 Hex2 E2ic E2col Hnth2 => vt2 col2 ent2 isc2
  Hex2 /= E2ic E2col Hnth2.
subst isc2.
rewrite Ecomp' in E2col.
subst col2.
case: Hm => Hpc Hpct Hregs Hmem Hcode Hsys Hgap.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrBnz r l, tg)) 0
  = Some (MrBnz r (can_upd L (Pointer.component tpc) l), tg) by [].
have [pos [v [Hwv Hv Htagv Hdec Hcm5]]] :=
  match_fetch Hbound Hcode Hex0 Hpc Hcell.
have [rc Hrc] := mregs_rel_lookup R_COM Hregs.
have [rar [Hrr Hvr Htr]] := Hsyncr.
case: rar Hrr Hvr Htr => wr tr Hrr Hvr Htr.
have Etr : tr = Other by rewrite /= in Htr; rewrite Htr Htag0.
subst tr.
have Hvrel : vrel amap (Int z) wr.
{ by move: Hvr; rewrite /tvrel Htag0 Hval0 /=. }
have Hwnz : (wr == 0%w) = false := vrel_nonzero Hvrel Hnz.
have H1415 : Merged.alloc_label < 2 ^ imm_size mt.
{ rewrite /Merged.alloc_label imm_size_mt. by rewrite ltn_exp2l. }
have Hlin32 : size (linearize_bufs PB) < 2 ^ word_size mt.
{ have H1532 : (2 : nat) ^ imm_size mt < 2 ^ word_size mt
    by rewrite imm_size_mt word_size_mt ltn_exp2l.
  by lia. }
have Hpc0E : size (initial_memory (mt := mt) PB)
             = size (linearize_bufs PB)
  := initial_memory_size_eq Hlin32.
have [poslab [possrc [Hlp Hbnd Hpc2 Hcmsrc Hple]]] :
    exists poslab possrc,
    [/\ forall default,
          code_label_pos codeW pc0
            (can_upd L (Pointer.component tpc) l) default
          = pc0 + poslab,
        pc0 + poslab < 2 ^ imm_size mt,
        pc_relW pc' (@word_of_nat (word_size mt) (pc0 + poslab)),
        cmapWW (Pointer.component tpc)
          (BinInt.Z.to_nat (Pointer.offset tpc)) = Some (possrc + pc0)
      & possrc <= poslab].
{ case E: (Pointer.component tpc \in domm (Intermediate.prog_procedures pra)).
  -
    have Hseg : Transitional.intermediate_to_transitional_gen PI pra
                  (Pointer.component tpc) = Some csegW.
    { rewrite -(cdeW_left prb PI E). exact: Hcw. }
    have Hcolx : color (MTag vt2 (Pointer.component tpc) ent2 true)
                 = Pointer.component tpc by [].
    have Hnthc := tlink_body_nth_l L P C prb PB Hseg Hnth2 Hcolx.
    have Hposlt := nth_error_lt Hnthc.
    exists (tpos PI pra (Pointer.component tpc) csegW
              (BinInt.Z.to_nat (Pointer.offset pc')) + 0),
           (tpos PI pra (Pointer.component tpc) csegW
              (BinInt.Z.to_nat (Pointer.offset tpc))).
    split.
    + move=> default.
      rewrite /can_upd.
      exact: (tlink_label_pos_body_l P PB Hlab_a Hcomp_a Hlab_b Hdisj
                Hseg Hnth2 Hcolx HlL
                (@Huniq_a (Pointer.component tpc) l) pc0 default).
    + by lia.
    + apply: (@PCLeft _ _ _ _ _ _ _ _ _ csegW).
      * by rewrite Ecomp' E.
      * by rewrite Ecomp' Hseg.
      * by lia.
      * congr word_of_nat. rewrite Ecomp'. by lia.
    + by rewrite /cmapW E Hseg.
    + rewrite addn0. apply: tpos_leq. by lia.
  -
    have Hseg : Transitional.intermediate_to_transitional_gen PI prb
                  (Pointer.component tpc) = Some csegW.
    { rewrite -(cdeW_right prb PI (negbT E)). exact: Hcw. }
    have Hcolx : color (MTag vt2 (Pointer.component tpc) ent2 true)
                 = Pointer.component tpc by [].
    have Hnthc := tlink_body_nth_r L P C pra PB Hseg Hnth2 Hcolx.
    have Hposlt := nth_error_lt Hnthc.
    exists (size (compiler_code L P C PB PI pra)
            + (tpos PI prb (Pointer.component tpc) csegW
                 (BinInt.Z.to_nat (Pointer.offset pc')) + 0)),
           (size (compiler_code L P C PB PI pra)
            + tpos PI prb (Pointer.component tpc) csegW
                (BinInt.Z.to_nat (Pointer.offset tpc))).
    split.
    + move=> default.
      rewrite /can_upd.
      exact: (tlink_label_pos_body_r P PB Hlab_a Hlab_b Hcomp_b Hdisj
                Hseg Hnth2 Hcolx HlL
                (@Huniq_b (Pointer.component tpc) l) pc0 default).
    + by lia.
    + apply: (@PCRight _ _ _ _ _ _ _ _ _ csegW).
      * by rewrite Ecomp' E.
      * by rewrite Ecomp' Hseg.
      * by lia.
      * congr word_of_nat. rewrite Ecomp'. by lia.
    + by rewrite /cmapW E Hseg.
    + rewrite addn0 leq_add2l. apply: tpos_leq. by lia. }
have Epos : pos = possrc.
{ move: Hcm5. rewrite Hcmsrc => - [E5]. by lia. }
subst pos.
have Hcell2 : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrLabel (inl l), MTag vt2 (Pointer.component tpc) ent2 true)) 0
  = Some (MrLabel (can_upd L (Pointer.component tpc) l),
          MTag vt2 (Pointer.component tpc) ent2 true) by [].
have [posf [v2 [Hwv2 Hv2m Htagv2 Hdec2 _]]] :=
  match_fetch Hbound Hcode Hex2 Hpc2 Hcell2.
move: Hdec => /= Hdec.
rewrite Hlp in Hdec.
have HbndD : (pc0 + poslab) - (pc0 + possrc) < 2 ^ imm_size mt.
{ by lia. }
have EcastD : @swcast (imm_size mt) (word_size mt)
                (@word_of_nat (imm_size mt)
                   ((pc0 + poslab) - (pc0 + possrc)))
              = @word_of_nat (word_size mt)
                  ((pc0 + poslab) - (pc0 + possrc))
  := swcast_word_of_nat_small HbndD.
have EA : addw (Symbolic.pcv ms)
            (@word_of_nat (word_size mt)
               ((pc0 + poslab) - (pc0 + possrc)))
          = @word_of_nat (word_size mt) (pc0 + poslab).
{ rewrite Hwv addw_word_of_nat. congr word_of_nat. by lia. }
rewrite /Symbolic.pct in Hpct.
set key := @word_of_nat (reg_field_size mt) (Intermediate.Register.to_nat r).
exists (@Symbolic.State mt lrc_tags unit
          (Symbolic.mem ms)
          (Symbolic.regs ms)
          (@word_of_nat (word_size mt) (pc0 + poslab))
            @(taga (Symbolic.pc ms))
          (Symbolic.internal ms)).
split.
- rewrite /step_me.
  apply: (@Symbolic.step_bnz _ _ _ _ _ _ _ _ _
            (Symbolic.mem ms) (Symbolic.regs ms)
            (Symbolic.pcv ms)
            (vala v) key
            (@word_of_nat (imm_size mt) ((pc0 + poslab) - (pc0 + possrc)))
            wr
            (taga (Symbolic.pc ms)) (taga v) Other
            (Symbolic.internal ms)).
  + exact: Symbolic.state_eta.
  + by case: (v) Hv.
  + exact: Hdec.
  + exact: Hrr.
  +
    rewrite Hwnz.
    rewrite /Symbolic.next_state_updates_and_pc.
    rewrite EcastD EA Hv2m.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt)
              = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
    rewrite Hrc /=.
    rewrite /Merged.transfer /Merged.instr_rules.
    rewrite Hpct Htagv /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite /check_belong /belong Htagv2 /= eqxx /=.
    rewrite /Symbolic.next_state_do_update /updm Hrr /=.
    rewrite (setmI Hrr).
    by [].
- constructor.
  +
    rewrite /Symbolic.pcv /=. exact: Hpc2.
  +
    rewrite /Symbolic.pct /= Hpct.
    by rewrite Ecomp'.
  + exact: Hregs.
  + exact: Hmem.
  + exact: Hcode.
  + exact: Hsys.
  + exact: Hgap.
- exact: erefl.
- exact: erefl.
- exact: erefl.
Qed.

(* ================================================================== *)
(* 14. Call: the cross-component event diagram.                       *)
(* ================================================================== *)

(* the procedure-bound statics (entry-label bridges) *)
Hypothesis Hproc_a : forall cid Cprocs Pid,
  Intermediate.prog_procedures pra cid = Some Cprocs ->
  Pid \in domm Cprocs -> Pid < P.
Hypothesis Hproc_b : forall cid Cprocs Pid,
  Intermediate.prog_procedures prb cid = Some Cprocs ->
  Pid \in domm Cprocs -> Pid < P.

(* the T-side ENTRY-label bridge: [find_plabel] inverted *)
Fixpoint plaux (cd : seq (Transitional.instr * mem_tag))
    (c : Component.id) (p : Procedure.id) (o : Z) : option Z :=
  match cd with
  | [::] => None
  | (TrLabel (inr (c1, p1)), _) :: cd' =>
      if Nat.eqb c c1 && Nat.eqb p p1 then Some o
      else plaux cd' c p (BinInt.Z.add 1 o)
  | _ :: cd' => plaux cd' c p (BinInt.Z.add 1 o)
  end.

Lemma find_plabel_plaux cd c p :
  Transitional.find_plabel cd c p = plaux cd c p BinNums.Z0.
Proof.
rewrite /Transitional.find_plabel.
elim: cd (BinNums.Z0) => [|[i tg] cd IH] o //=.
by case: i => [|[l'|[c1 p1]]|v r|r1 r2|op r1 r2 r3|r1 r2|r1 r2|r1 r2
              |r l0|r|l0|lp|] /=; rewrite -?IH; case: cd {IH}.
Qed.

Lemma plaux_nth cd c p (o z : Z) :
  plaux cd c p o = Some z ->
  BinInt.Z.le o z /\
  exists xt,
    List.nth_error cd (BinInt.Z.to_nat (BinInt.Z.sub z o))
    = Some (TrLabel (inr (c, p)), xt).
Proof.
elim: cd o => [|[i tg] cd IH] o //=.
case: i => [|pl|v r|r1 r2|op r1 r2 r3|r1 r2|r1 r2|r1 r2|r l0|r|l0|lp|].
2: { case: pl => [l'|[c1 p1]].
     - move=> /IH [Hle [xt Hnth]].
       split; first by lia.
       exists xt.
       have -> : BinInt.Z.to_nat (BinInt.Z.sub z o)
               = (BinInt.Z.to_nat
                    (BinInt.Z.sub z (BinInt.Z.add 1 o))).+1 by lia.
       exact: Hnth.
     - case E: (Nat.eqb c c1 && Nat.eqb p p1).
       + move=> [<-]. split; first by lia.
         move/andP: E => [/PeanoNat.Nat.eqb_eq Ec1 /PeanoNat.Nat.eqb_eq Ep1].
         subst c1 p1.
         exists tg.
         have -> : BinInt.Z.to_nat (BinInt.Z.sub o o) = 0 by lia.
         by [].
       + move=> /IH [Hle [xt Hnth]].
         split; first by lia.
         exists xt.
         have -> : BinInt.Z.to_nat (BinInt.Z.sub z o)
                 = (BinInt.Z.to_nat
                      (BinInt.Z.sub z (BinInt.Z.add 1 o))).+1 by lia.
         exact: Hnth. }
all: move=> /IH [Hle [xt Hnth]];
  split; [by lia|];
  exists xt;
  (have -> : BinInt.Z.to_nat (BinInt.Z.sub z o)
           = (BinInt.Z.to_nat
                (BinInt.Z.sub z (BinInt.Z.add 1 o))).+1 by lia);
  exact: Hnth.
Qed.

Lemma find_plabel_in_code_nth (cde0 : Transitional.code)
    (c : Component.id) (p : Procedure.id) (pc1 : Pointer.t) :
  Transitional.find_plabel_in_code cde0 c p = Some pc1 ->
  exists cseg xt,
    [/\ cde0 c = Some cseg,
        pc1 = (c, 0, Pointer.offset pc1),
        BinInt.Z.le 0 (Pointer.offset pc1)
      & List.nth_error cseg (BinInt.Z.to_nat (Pointer.offset pc1))
        = Some (TrLabel (inr (c, p)), xt)].
Proof.
rewrite /Transitional.find_plabel_in_code.
case Hc: (cde0 c) => [cseg|] //.
case Hf: (Transitional.find_plabel cseg c p) => [z|] // [Epc].
move: Hf; rewrite find_plabel_plaux => /plaux_nth [Hle [xt Hnth]].
exists cseg, xt.
subst pc1.
split.
- by [].
- by [].
- exact: Hle.
- rewrite /=.
  rewrite BinInt.Z.sub_0_r in Hnth.
  exact: Hnth.
Qed.

(* [check_comp_belongs] is boolean membership *)
Lemma check_comp_belongs_mem (c0 : Component.id) (l0 : seq Component.id) :
  Transitional.check_comp_belongs c0 l0 -> mem_seq l0 c0.
Proof.
elim: l0 => [|x l0 IH] //= [->|/IH H] /=.
- by rewrite eqxx.
- by rewrite H orbT.
Qed.

Lemma sim_call (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (tpc : Pointer.t) (tpct : Transitional.pc_tag)
    (ms : @Symbolic.state mt lrc_tags unit)
    (tg : mem_tag) (c c' : Component.id) (pid : Procedure.id)
    (pc' : Pointer.t) (i2 : Transitional.instr) (tni2 : mem_tag)
    (i3 : Transitional.instr) (tg3 : mem_tag) (call_arg : Z) (n : nat) :
  match_statesW amap tmem tregs tpc tpct ms ->
  reg_syncedW amap tregs (Symbolic.regs ms) R_COM ->
  Transitional.executing cdeW tpc (TrJalProc (c', pid)) tg c ->
  Transitional.find_plabel_in_code cdeW c' pid = Some pc' ->
  Transitional.executing cdeW pc' i2 tni2 c' ->
  c <> c' ->
  Transitional.check_pc_call c tni2 pid ->
  tpct = Transitional.Level n ->
  Transitional.tvtag (Transitional.Register.get R_COM tregs) = Other ->
  Transitional.val (Transitional.Register.get R_COM tregs) = Int call_arg ->
  Transitional.executing cdeW (Pointer.inc tpc) i3 tg3 c ->
  pid < P ->
  exists ms',
    [/\ step_me (NC := NC) ms ms' (Some (ECall c pid call_arg c')),
        match_statesW amap tmem
          (Transitional.Register.set R_RA (Ptr (Pointer.inc tpc))
             (Ret n) (Transitional.Register.invalidate tregs))
          pc' (Transitional.inc_pc_tag tpct) ms',
        domm (Symbolic.mem ms') = domm (Symbolic.mem ms)
      & Symbolic.mem ms' = Symbolic.mem ms].
Proof.
move=> Hm Hsynccom Hex0 Hfind Hex2 Hneq Hcall Htpct Htagcom Hvalcom Hex3 HpP.
have [Ec Hic Hcol] := executing_props Hex0.
subst c tpct.
case: tg Hex0 Hic Hcol => vt0 col0 ent0 isc0 Hex0 /= Hic Hcol.
subst isc0 col0.
set tg := MTag vt0 (Pointer.component tpc) ent0 true.
have [csegW [xt [Hcw Epc' Hz Hnthlab]]] := find_plabel_in_code_nth Hfind.
have Ecomp2 : Pointer.component pc' = c' by rewrite {1}Epc'.
have [_ E2ic E2col] := executing_props Hex2.
have Hnth2 : List.nth_error csegW
    (BinInt.Z.to_nat (Pointer.offset pc')) = Some (i2, tni2).
{ case: Hex2 => C2 [_ [Hcde2 [_ Hn2]]].
  move: Hcde2 Hn2. rewrite Hcw. move=> [<-]. by []. }
move: Hnthlab; rewrite Hnth2 => - [Ei2 Ext].
subst i2 xt.
have [lst [Hent Hbel]] := TS.check_pc_callE Hcall.
case: tni2 Hex2 E2ic E2col Hnth2 Hent {Hcall}
  => vt2 col2 ent2 isc2 Hex2 /= E2ic E2col Hnth2 Hent.
subst isc2 ent2 col2.
have [_ H3ic H3col] := executing_props Hex3.
case: tg3 Hex3 H3ic H3col => vt3 col3 ent3 isc3 Hex3 /= H3ic H3col.
subst isc3 col3.
case: Hm => Hpc Hpct Hregs Hmem Hcode Hsys Hgap.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrJalProc (c', pid), tg)) 0
  = Some (MrJal (can_make L P C (c', pid)), tg) by [].
have [pos [v [Hwv Hv Htagv Hdec _]]] :=
  match_fetch Hbound Hcode Hex0 Hpc Hcell.
have [cell3 Hcell3] : exists cell3,
    List.nth_error
      (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
         (i3, MTag vt3 (Pointer.component tpc) ent3 true)) 0
    = Some cell3.
{ apply: nth_error_Some_ex.
  rewrite lin_size_length size_cell_exp. by case: i3 {Hex3}. }
have Ecell3 : cell3.2 = MTag vt3 (Pointer.component tpc) ent3 true
  := cell_exp_snd Hcell3.
have [pos2 [vret [Hw2 Haddr Hvret Htagvret Hpcinc]]] :=
  silent_next (i := TrJalProc (c', pid)) (erefl _) Hcode Hex0 Hex3 Hpc Hcell3.
case: vret Hvret Htagvret => vret_v tret_t Hvret /= Htagvret.
rewrite {}Ecell3 in Htagvret.
subst tret_t.
have Hcr : tvrel cmapWW amap
    (Transitional.MVal (Ret n) (Ptr (Pointer.inc tpc)))
    (addw (Symbolic.pcv ms) onew).
{ rewrite /tvrel /=. exact: pc_rel_code_rel Hpcinc. }
have H1415 : Merged.alloc_label < 2 ^ imm_size mt.
{ rewrite /Merged.alloc_label imm_size_mt. by rewrite ltn_exp2l. }
have Hlin32 : size (linearize_bufs PB) < 2 ^ word_size mt.
{ have H1532 : (2 : nat) ^ imm_size mt < 2 ^ word_size mt
    by rewrite imm_size_mt word_size_mt ltn_exp2l.
  by lia. }
have Hpc0E : size (initial_memory (mt := mt) PB)
             = size (linearize_bufs PB)
  := initial_memory_size_eq Hlin32.
have [poslab [Hlp Hbnd Hpc2]] : exists poslab,
    [/\ forall default,
          code_label_pos codeW pc0 (can_make L P C (c', pid)) default
          = pc0 + poslab,
        pc0 + poslab < 2 ^ imm_size mt
      & pc_relW pc' (@word_of_nat (word_size mt) (pc0 + poslab))].
{ case E: (c' \in domm (Intermediate.prog_procedures pra)).
  -
    have Hseg : Transitional.intermediate_to_transitional_gen PI pra c'
                = Some csegW.
    { rewrite -(cdeW_left prb PI E). exact: Hcw. }
    have Hnthc := tlink_entry_nth_l L P C prb PB Hseg Hnth2.
    have Hposlt := nth_error_lt Hnthc.
    exists (tpos PI pra c' csegW
              (BinInt.Z.to_nat (Pointer.offset pc')) + 0).
    split.
    + move=> default.
      rewrite /can_make.
      exact: (tlink_label_pos_entry_l PB Hlab_a Hproc_a Hcomp_a
                Hlab_b Hproc_b Hcomp_b Hdisj Hseg Hnth2 HpP pc0 default).
    + by lia.
    + apply: (@PCLeft _ _ _ _ _ _ _ _ _ csegW).
      * by rewrite Ecomp2 E.
      * by rewrite Ecomp2 Hseg.
      * by lia.
      * congr word_of_nat. rewrite Ecomp2. by lia.
  -
    have Hseg : Transitional.intermediate_to_transitional_gen PI prb c'
                = Some csegW.
    { rewrite -(cdeW_right prb PI (negbT E)). exact: Hcw. }
    have Hnthc := tlink_entry_nth_r L P C pra PB Hseg Hnth2.
    have Hposlt := nth_error_lt Hnthc.
    exists (size (compiler_code L P C PB PI pra)
            + (tpos PI prb c' csegW
                 (BinInt.Z.to_nat (Pointer.offset pc')) + 0)).
    split.
    + move=> default.
      rewrite /can_make.
      exact: (tlink_label_pos_entry_r PB Hlab_a Hproc_a Hcomp_a
                Hlab_b Hproc_b Hcomp_b Hdisj Hseg Hnth2 HpP pc0 default).
    + by lia.
    + apply: (@PCRight _ _ _ _ _ _ _ _ _ csegW).
      * by rewrite Ecomp2 E.
      * by rewrite Ecomp2 Hseg.
      * by lia.
      * congr word_of_nat. rewrite Ecomp2. by lia. }
have Hcell2 : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrLabel (inr (c', pid)),
        MTag vt2 c' (Some (pid, lst)) true)) 0
  = Some (MrLabel (can_make L P C (c', pid)),
          MTag vt2 c' (Some (pid, lst)) true) by [].
have Hex2' : Transitional.executing cdeW pc' (TrLabel (inr (c', pid)))
    (MTag vt2 c' (Some (pid, lst)) true) (Pointer.component pc')
  by rewrite Ecomp2.
have [posf [v2 [Hwv2 Hv2m Htagv2 Hdec2 _]]] :=
  match_fetch Hbound Hcode Hex2' Hpc2 Hcell2.
have [A1p [HA1 Hvr1 Htr1]] := Hsynccom.
case: A1p HA1 Hvr1 Htr1 => w1' t1' HA1 Hvr1 Htr1.
have Et1 : t1' = Other by rewrite /= in Htr1; rewrite Htr1 Htagcom.
subst t1'.
move: Hvr1; rewrite /tvrel Htagcom Hvalcom /= => Hvr1.
have Hpay := vrel_int_inv Hvr1.
move: Hpay; rewrite /wrepr => Hpay.
have [Ara HraL] := mregs_rel_lookup R_RA Hregs.
case: Ara HraL => wra tra HraL.
have [A0 HA0] := mregs_rel_lookup R_ONE Hregs.
case: A0 HA0 => w0' t0' HA0.
have [A2 HA2] := mregs_rel_lookup R_AUX1 Hregs.
case: A2 HA2 => w2' t2' HA2.
have [A3 HA3] := mregs_rel_lookup R_AUX2 Hregs.
case: A3 HA3 => w3' t3' HA3.
have [A5 HA5] := mregs_rel_lookup R_SP Hregs.
case: A5 HA5 => w5' t5' HA5.
have [A6 HA6] := mregs_rel_lookup R_ARG Hregs.
case: A6 HA6 => w6' t6' HA6.
have [A7 HA7] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 7) = Some a
  by apply: Hsys; rewrite !inE eqxx.
case: A7 HA7 => w7' t7' HA7.
have [A16 HA16] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 16) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
case: A16 HA16 => w16' t16' HA16.
have [A17 HA17] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 17) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
case: A17 HA17 => w17' t17' HA17.
have [A18 HA18] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 18) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
case: A18 HA18 => w18' t18' HA18.
have [A19 HA19] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 19) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
case: A19 HA19 => w19' t19' HA19.
have HA1c : Symbolic.regs ms (word.as_word (ssrint.Posz 1))
            = Some (Atom w1' Other) := HA1.
have HA0c : Symbolic.regs ms (word.as_word (ssrint.Posz 0))
            = Some (Atom w0' t0') := HA0.
have HA2c : Symbolic.regs ms (word.as_word (ssrint.Posz 2))
            = Some (Atom w2' t2') := HA2.
have HA3c : Symbolic.regs ms (word.as_word (ssrint.Posz 3))
            = Some (Atom w3' t3') := HA3.
have HA5c : Symbolic.regs ms (word.as_word (ssrint.Posz 5))
            = Some (Atom w5' t5') := HA5.
have HA6c : Symbolic.regs ms (word.as_word (ssrint.Posz 6))
            = Some (Atom w6' t6') := HA6.
have HA7c : Symbolic.regs ms (word.as_word (ssrint.Posz 7))
            = Some (Atom w7' t7') := HA7.
have HA16c : Symbolic.regs ms (word.as_word (ssrint.Posz 16))
            = Some (Atom w16' t16') := HA16.
have HA17c : Symbolic.regs ms (word.as_word (ssrint.Posz 17))
            = Some (Atom w17' t17') := HA17.
have HA18c : Symbolic.regs ms (word.as_word (ssrint.Posz 18))
            = Some (Atom w18' t18') := HA18.
have HA19c : Symbolic.regs ms (word.as_word (ssrint.Posz 19))
            = Some (Atom w19' t19') := HA19.
have Hclear : Symbolic.reg_clear_list (Symbolic.regs ms) tra
  = Some [hseq tra; Other; t0'; t2'; t3'; t5'; t6'; t7';
          t16'; t17'; t18'; t19'].
{ rewrite /Symbolic.reg_clear_list /=.
  by rewrite HA1c /= HA0c /= HA2c /= HA3c /= HA5c /= HA6c /= HA7c /=
             HA16c /= HA17c /= HA18c /= HA19c /=. }
move: Hdec => /= Hdec.
rewrite Hlp in Hdec.
have Ecast : @swcast (imm_size mt) (word_size mt)
               (@word_of_nat (imm_size mt) (pc0 + poslab))
             = @word_of_nat (word_size mt) (pc0 + poslab)
  := swcast_word_of_nat_small Hbnd.
have Hbf : (Pointer.component tpc == c') = false.
{ apply/negbTE/eqP => E'. by apply: Hneq. }
have Hbelmem := check_comp_belongs_mem Hbel.
have HB1 : setm (Symbolic.regs ms) (ra : reg mt)
             (Atom (addw (Symbolic.pcv ms) onew)
                (Ret (Transitional.level (Transitional.Level n))))
             (word.as_word (ssrint.Posz 1)) = Some (Atom w1' Other)
  by apply: setm_ra_other.
rewrite /Symbolic.pct in Hpct.
exists (@Symbolic.State mt lrc_tags unit
          (Symbolic.mem ms)
          (setm (setm (setm (setm (setm (setm (setm (setm (setm (setm (setm
             (Symbolic.regs ms)
             (@word_of_nat (reg_field_size mt)
                (Intermediate.Register.to_nat R_RA))
             (Atom (addw (Symbolic.pcv ms) onew)
                (Ret (Transitional.level (Transitional.Level n)))))
             (word.as_word (ssrint.Posz 0)) (Atom w0' Invalidated))
             (word.as_word (ssrint.Posz 2)) (Atom w2' Invalidated))
             (word.as_word (ssrint.Posz 3)) (Atom w3' Invalidated))
             (word.as_word (ssrint.Posz 5)) (Atom w5' Invalidated))
             (word.as_word (ssrint.Posz 6)) (Atom w6' Invalidated))
             (word.as_word (ssrint.Posz 7)) (Atom w7' Invalidated))
             (word.as_word (ssrint.Posz 16)) (Atom w16' Invalidated))
             (word.as_word (ssrint.Posz 17)) (Atom w17' Invalidated))
             (word.as_word (ssrint.Posz 18)) (Atom w18' Invalidated))
             (word.as_word (ssrint.Posz 19)) (Atom w19' Invalidated))
          (@word_of_nat (word_size mt) (pc0 + poslab))
            @(LRC.Level (Transitional.level (Transitional.Level n)).+1 c')
          (Symbolic.internal ms)).
split.
- rewrite /step_me.
  apply: (@Symbolic.step_jal _ _ _ _ _ _ _ _ _
            (Symbolic.mem ms) (Symbolic.regs ms) (Symbolic.pcv ms)
            (vala v)
            (@word_of_nat (imm_size mt) (pc0 + poslab))
            (taga (Symbolic.pc ms)) (taga v)
            wra tra
            (Symbolic.internal ms)
            [hseq tra; Other; t0'; t2'; t3'; t5'; t6'; t7';
             t16'; t17'; t18'; t19']
            vret_v (MTag vt3 (Pointer.component tpc) ent3 true)).
  + exact: Symbolic.state_eta.
  + by case: (v) Hv.
  + exact: Hvret.
  + exact: Hdec.
  + exact: HraL.
  + exact: Hclear.
  +
    rewrite /Symbolic.next_state_updates_and_pc.
    rewrite Ecast Hv2m.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt)
              = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
    rewrite HA1 /=.
    rewrite /Merged.transfer /Merged.instr_rules.
    rewrite Hpct Htagv /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite Htagv2 /= Hbf /=.
    rewrite /check_belong /belong /= eqxx /= Hbelmem /=.
    rewrite Hpay /=.
    rewrite /Symbolic.next_state_do_update /updm.
    rewrite Hvret /= (setmI Hvret).
    rewrite HraL /=.
    rewrite HB1 /= (setmI HB1).
    rewrite (_ : _ (word.as_word (ssrint.Posz 0)) = Some (Atom w0' t0')) /=;
      last by rewrite /= !setmE HA0c.
    rewrite (_ : _ (word.as_word (ssrint.Posz 2)) = Some (Atom w2' t2')) /=;
      last by rewrite /= !setmE HA2c.
    rewrite (_ : _ (word.as_word (ssrint.Posz 3)) = Some (Atom w3' t3')) /=;
      last by rewrite /= !setmE HA3c.
    rewrite (_ : _ (word.as_word (ssrint.Posz 5)) = Some (Atom w5' t5')) /=;
      last by rewrite /= !setmE HA5c.
    rewrite (_ : _ (word.as_word (ssrint.Posz 6)) = Some (Atom w6' t6')) /=;
      last by rewrite /= !setmE HA6c.
    rewrite (_ : _ (word.as_word (ssrint.Posz 7)) = Some (Atom w7' t7')) /=;
      last by rewrite /= !setmE HA7c.
    rewrite (_ : _ (word.as_word (ssrint.Posz 16))
                 = Some (Atom w16' t16')) /=;
      last by rewrite /= !setmE HA16c.
    rewrite (_ : _ (word.as_word (ssrint.Posz 17))
                 = Some (Atom w17' t17')) /=;
      last by rewrite /= !setmE HA17c.
    rewrite (_ : _ (word.as_word (ssrint.Posz 18))
                 = Some (Atom w18' t18')) /=;
      last by rewrite /= !setmE HA18c.
    rewrite (_ : _ (word.as_word (ssrint.Posz 19))
                 = Some (Atom w19' t19')) /=;
      last by rewrite /= !setmE HA19c.
    by [].
- constructor.
  +
    rewrite /Symbolic.pcv /=. exact: Hpc2.
  +
    rewrite /Symbolic.pct /= Ecomp2.
    congr LRC.Level. by lia.
  +
    move=> r''.
    case: r''.
    *
      right.
      exists (Atom w0' Invalidated).
      split.
      { by rewrite !setmE HA0c. }
      { by []. }
      { by []. }
    *
      left.
      exists (Atom w1' Other).
      split.
      { by rewrite !setmE HA1c. }
      { rewrite /tvrel /= Htagcom Hvalcom /=. exact: Hvr1. }
      { by rewrite /= Htagcom. }
    *
      right.
      exists (Atom w2' Invalidated).
      split.
      { by rewrite !setmE HA2c. }
      { by []. }
      { by []. }
    *
      right.
      exists (Atom w3' Invalidated).
      split.
      { by rewrite !setmE HA3c. }
      { by []. }
      { by []. }
    *
      left.
      exists (Atom (addw (Symbolic.pcv ms) onew)
                (Ret (Transitional.level (Transitional.Level n)))).
      split.
      { by rewrite !setmE. }
      { exact: Hcr. }
      { by []. }
    *
      right.
      exists (Atom w5' Invalidated).
      split.
      { by rewrite !setmE HA5c. }
      { by []. }
      { by []. }
    *
      right.
      exists (Atom w6' Invalidated).
      split.
      { by rewrite !setmE HA6c. }
      { by []. }
      { by []. }
  + exact: Hmem.
  + exact: Hcode.
  +
    do 11!apply: sysregs_ok_setm.
    exact: Hsys.
  + exact: Hgap.
- exact: erefl.
- exact: erefl.
Qed.

(* ================================================================== *)
(* 14b. The syscall entry: no code label is [alloc_label] (labels are  *)
(*      ODD, the entry is a power of two), so [code_label_pos] falls   *)
(*      through [findopt] to the entry address itself.                 *)
(* ================================================================== *)

Lemma tlink_no_alloc :
  findopt (MicroPolicies.Recomposition.Definitions.is_label_def
             Merged.alloc_label) codeW = None.
Proof.
apply: findopt_notIn_None => x HIn.
have HN1 := findopt_None_notIn (lin_low_no_alloc L P C PB PI pra).
have HN2 := findopt_None_notIn (lin_low_no_alloc L P C PB PI prb).
case: (List.in_app_or _ _ _ HIn) => HIn'.
- exact: (HN1 _ HIn').
- exact: (HN2 _ HIn').
Qed.

Lemma code_label_pos_alloc (default : nat) :
  code_label_pos codeW pc0 Merged.alloc_label default = Merged.alloc_label.
Proof.
by rewrite /code_label_pos tlink_no_alloc eqxx.
Qed.

(* the whole register relation transports along the ALLOC extension *)
Lemma mregs_rel_upd (amap : amap_t) (c b base : nat)
    (tregs : Transitional.Register.t)
    (mregs : {fmap reg mt -> @ratom mt}) :
  addr_of amap c b = None ->
  mregs_relW amap tregs mregs ->
  mregs_relW (amap_upd amap c b base) tregs mregs.
Proof.
move=> Hfresh Hrel r.
case: (Hrel r) => [[ra [H1 H2 H3]]|Hclob].
- left. exists ra. split.
  + exact: H1.
  + exact: tvrel_upd Hfresh H2.
  + exact: H3.
- by right.
Qed.

(* ================================================================== *)
(* 15. Return: the cross-component ERet diagram (Jump on a spent      *)
(*     RET capability; the compiled convention returns through R_RA). *)
(* ================================================================== *)

Lemma sim_ret (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (tpc : Pointer.t) (tpct : Transitional.pc_tag)
    (ms : @Symbolic.state mt lrc_tags unit)
    (tg : mem_tag) (c : Component.id) (pc' : Pointer.t)
    (rcomval : Z) (n : nat) :
  match_statesW amap tmem tregs tpc tpct ms ->
  reg_syncedW amap tregs (Symbolic.regs ms) R_RA ->
  reg_syncedW amap tregs (Symbolic.regs ms) R_COM ->
  Transitional.executing cdeW tpc (TrJump R_RA) tg c ->
  Transitional.Register.get R_RA tregs
    = Transitional.MVal (Ret n) (Ptr pc') ->
  Pointer.component pc' <> Pointer.component tpc ->
  tpct = Transitional.Level n.+1 ->
  Transitional.tvtag (Transitional.Register.get R_COM tregs) = Other ->
  Transitional.val (Transitional.Register.get R_COM tregs) = Int rcomval ->
  Transitional.check_pc_jump cdeW tg pc' (Pointer.component pc') ->
  exists ms',
    [/\ step_me (NC := NC) ms ms'
          (Some (ERet c rcomval (Pointer.component pc'))),
        match_statesW amap tmem (TS.invalidate_ret tregs) pc'
          (Transitional.dec_pc_tag tpct) ms',
        domm (Symbolic.mem ms') = domm (Symbolic.mem ms)
      & Symbolic.mem ms' = Symbolic.mem ms].
Proof.
move=> Hm Hsyncra Hsynccom Hex0 Hget Hneq Htpct Htagcom Hvalcom Hcpj.
have [Ec Hic Hcol] := executing_props Hex0.
subst c tpct.
case: tg Hex0 Hic Hcol Hcpj => vt0 col0 ent0 isc0 Hex0 /= Hic Hcol Hcpj.
subst isc0 col0.
set tg := MTag vt0 (Pointer.component tpc) ent0 true.
have [i2 [tni2 Hex2]] := check_pc_jump_ex Hcpj.
have [_ E2ic E2col] := executing_props Hex2.
have [cell2 Hcell2] : exists cell2,
    List.nth_error
      (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB) (i2, tni2)) 0
    = Some cell2.
{ apply: nth_error_Some_ex.
  rewrite lin_size_length size_cell_exp. by case: i2 {Hex2}. }
have Ecell22 : cell2.2 = tni2 := cell_exp_snd Hcell2.
case: Hm => Hpc Hpct Hregs Hmem Hcode Hsys Hgap.
have Hcell : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrJump R_RA, tg)) 0
  = Some (MrJump R_RA, tg) by [].
have [pos [v [Hwv Hv Htagv Hdec _]]] :=
  match_fetch Hbound Hcode Hex0 Hpc Hcell.
have [Ara [HraL Hvra Htra]] := Hsyncra.
case: Ara HraL Hvra Htra => wra rat HraL Hvra Htra.
rewrite /= in Hvra Htra.
have Erat : rat = Ret n by rewrite Htra Hget.
rewrite {}Erat in HraL.
have Hcr : code_rel cmapWW (Ptr pc') wra.
{ by move: Hvra; rewrite /tvrel Hget /=. }
case: Hcr => cp [bp [op [posc [Eptr Hcm Hop Ew]]]].
have Epc : pc' = (cp, bp, op) by case: Eptr.
have Ecp : Pointer.component pc' = cp by rewrite Epc.
have Eop : Pointer.offset pc' = op by rewrite Epc.
have Hcm' : cmapWW (Pointer.component pc')
              (BinInt.Z.to_nat (Pointer.offset pc')) = Some posc.
{ by rewrite Ecp Eop. }
have Hop' : BinInt.Z.le 0 (Pointer.offset pc') by rewrite Eop.
have Hpc2 : pc_rel L P C pra prb PB PI pc' wra.
{ exact: (cmap_pc_rel Hcm' Hop' Ew). }
have [posf [v2 [Hwv2 Hv2m Htagv2 Hdec2 _]]] :=
  match_fetch Hbound Hcode Hex2 Hpc2 Hcell2.
case: tni2 Hex2 E2ic E2col Ecell22 {Hcell2} => vt2 col2 ent2 isc2
  Hex2 /= E2ic E2col Ecell22.
subst isc2 col2.
have [A1p [HA1 Hvr1 Htr1]] := Hsynccom.
case: A1p HA1 Hvr1 Htr1 => w1' t1' HA1 Hvr1 Htr1.
have Et1 : t1' = Other by rewrite /= in Htr1; rewrite Htr1 Htagcom.
subst t1'.
move: Hvr1; rewrite /tvrel Htagcom Hvalcom /= => Hvr1.
have Hpay := vrel_int_inv Hvr1.
move: Hpay; rewrite /wrepr => Hpay.
have [A0 HA0] := mregs_rel_lookup R_ONE Hregs.
case: A0 HA0 => w0' t0' HA0.
have [A2 HA2] := mregs_rel_lookup R_AUX1 Hregs.
case: A2 HA2 => w2' t2' HA2.
have [A3 HA3] := mregs_rel_lookup R_AUX2 Hregs.
case: A3 HA3 => w3' t3' HA3.
have [A5 HA5] := mregs_rel_lookup R_SP Hregs.
case: A5 HA5 => w5' t5' HA5.
have [A6 HA6] := mregs_rel_lookup R_ARG Hregs.
case: A6 HA6 => w6' t6' HA6.
have [A7 HA7] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 7) = Some a
  by apply: Hsys; rewrite !inE eqxx.
case: A7 HA7 => w7' t7' HA7.
have [A16 HA16] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 16) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
case: A16 HA16 => w16' t16' HA16.
have [A17 HA17] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 17) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
case: A17 HA17 => w17' t17' HA17.
have [A18 HA18] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 18) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
case: A18 HA18 => w18' t18' HA18.
have [A19 HA19] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 19) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
case: A19 HA19 => w19' t19' HA19.
have HA1c : Symbolic.regs ms (word.as_word (ssrint.Posz 1))
            = Some (Atom w1' Other) := HA1.
have HA0c : Symbolic.regs ms (word.as_word (ssrint.Posz 0))
            = Some (Atom w0' t0') := HA0.
have HA2c : Symbolic.regs ms (word.as_word (ssrint.Posz 2))
            = Some (Atom w2' t2') := HA2.
have HA3c : Symbolic.regs ms (word.as_word (ssrint.Posz 3))
            = Some (Atom w3' t3') := HA3.
have HA5c : Symbolic.regs ms (word.as_word (ssrint.Posz 5))
            = Some (Atom w5' t5') := HA5.
have HA6c : Symbolic.regs ms (word.as_word (ssrint.Posz 6))
            = Some (Atom w6' t6') := HA6.
have HA7c : Symbolic.regs ms (word.as_word (ssrint.Posz 7))
            = Some (Atom w7' t7') := HA7.
have HA16c : Symbolic.regs ms (word.as_word (ssrint.Posz 16))
            = Some (Atom w16' t16') := HA16.
have HA17c : Symbolic.regs ms (word.as_word (ssrint.Posz 17))
            = Some (Atom w17' t17') := HA17.
have HA18c : Symbolic.regs ms (word.as_word (ssrint.Posz 18))
            = Some (Atom w18' t18') := HA18.
have HA19c : Symbolic.regs ms (word.as_word (ssrint.Posz 19))
            = Some (Atom w19' t19') := HA19.
have Hclear : Symbolic.reg_clear_list (Symbolic.regs ms) (Ret n)
  = Some [hseq Ret n; Other; t0'; t2'; t3'; t5'; t6'; t7';
          t16'; t17'; t18'; t19'].
{ rewrite /Symbolic.reg_clear_list /=.
  by rewrite HA1c /= HA0c /= HA2c /= HA3c /= HA5c /= HA6c /= HA7c /=
             HA16c /= HA17c /= HA18c /= HA19c /=. }
have Hbf : (Pointer.component tpc == Pointer.component pc') = false.
{ apply/negbTE/eqP => E'. apply: Hneq. by rewrite E'. }
have HBra : setm (Symbolic.regs ms) (ra : reg mt)
              (Atom wra Invalidated)
              (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat R_RA))
            = Some (Atom wra Invalidated).
{ by rewrite setmE. }
have HB1 : setm (Symbolic.regs ms) (ra : reg mt)
             (Atom wra Invalidated)
             (word.as_word (ssrint.Posz 1)) = Some (Atom w1' Other)
  by apply: setm_ra_other.
rewrite /Symbolic.pct in Hpct.
exists (@Symbolic.State mt lrc_tags unit
          (Symbolic.mem ms)
          (setm (setm (setm (setm (setm (setm (setm (setm (setm (setm (setm
             (Symbolic.regs ms)
             (@word_of_nat (reg_field_size mt)
                (Intermediate.Register.to_nat R_RA))
             (Atom wra Invalidated))
             (word.as_word (ssrint.Posz 0)) (Atom w0' Invalidated))
             (word.as_word (ssrint.Posz 2)) (Atom w2' Invalidated))
             (word.as_word (ssrint.Posz 3)) (Atom w3' Invalidated))
             (word.as_word (ssrint.Posz 5)) (Atom w5' Invalidated))
             (word.as_word (ssrint.Posz 6)) (Atom w6' Invalidated))
             (word.as_word (ssrint.Posz 7)) (Atom w7' Invalidated))
             (word.as_word (ssrint.Posz 16)) (Atom w16' Invalidated))
             (word.as_word (ssrint.Posz 17)) (Atom w17' Invalidated))
             (word.as_word (ssrint.Posz 18)) (Atom w18' Invalidated))
             (word.as_word (ssrint.Posz 19)) (Atom w19' Invalidated))
          wra@(LRC.Level
                 (Transitional.level (Transitional.Level n.+1)).-1
                 (Pointer.component pc'))
          (Symbolic.internal ms)).
split.
- rewrite /step_me.
  apply: (@Symbolic.step_jump _ _ _ _ _ _ _ _ _
            (Symbolic.mem ms) (Symbolic.regs ms) (Symbolic.pcv ms)
            (vala v)
            (@word_of_nat (reg_field_size mt)
               (Intermediate.Register.to_nat R_RA))
            wra
            (taga (Symbolic.pc ms)) (taga v) (Ret n)
            (Symbolic.internal ms)
            [hseq Ret n; Other; t0'; t2'; t3'; t5'; t6'; t7';
             t16'; t17'; t18'; t19']
            wra (Ret n)).
  + exact: Symbolic.state_eta.
  + by case: (v) Hv.
  + exact: Hdec.
  + exact: HraL.
  + exact: HraL.
  + exact: Hclear.
  +
    rewrite /Symbolic.next_state_updates_and_pc.
    rewrite Hv2m.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt)
              = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
    rewrite HA1 /=.
    rewrite /Merged.transfer /Merged.instr_rules.
    rewrite Hpct Htagv /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite Htagv2 Ecell22 /= Hbf /=.
    rewrite Hpay /=.
    rewrite /check_ret /= eqxx /=.
    rewrite /Symbolic.next_state_do_update /updm.
    rewrite HraL /=.
    rewrite HBra /= (setmI HBra).
    rewrite HB1 /= (setmI HB1).
    rewrite (_ : _ (word.as_word (ssrint.Posz 0)) = Some (Atom w0' t0')) /=;
      last by rewrite /= !setmE HA0c.
    rewrite (_ : _ (word.as_word (ssrint.Posz 2)) = Some (Atom w2' t2')) /=;
      last by rewrite /= !setmE HA2c.
    rewrite (_ : _ (word.as_word (ssrint.Posz 3)) = Some (Atom w3' t3')) /=;
      last by rewrite /= !setmE HA3c.
    rewrite (_ : _ (word.as_word (ssrint.Posz 5)) = Some (Atom w5' t5')) /=;
      last by rewrite /= !setmE HA5c.
    rewrite (_ : _ (word.as_word (ssrint.Posz 6)) = Some (Atom w6' t6')) /=;
      last by rewrite /= !setmE HA6c.
    rewrite (_ : _ (word.as_word (ssrint.Posz 7)) = Some (Atom w7' t7')) /=;
      last by rewrite /= !setmE HA7c.
    rewrite (_ : _ (word.as_word (ssrint.Posz 16))
                 = Some (Atom w16' t16')) /=;
      last by rewrite /= !setmE HA16c.
    rewrite (_ : _ (word.as_word (ssrint.Posz 17))
                 = Some (Atom w17' t17')) /=;
      last by rewrite /= !setmE HA17c.
    rewrite (_ : _ (word.as_word (ssrint.Posz 18))
                 = Some (Atom w18' t18')) /=;
      last by rewrite /= !setmE HA18c.
    rewrite (_ : _ (word.as_word (ssrint.Posz 19))
                 = Some (Atom w19' t19')) /=;
      last by rewrite /= !setmE HA19c.
    by [].
- constructor.
  +
    rewrite /Symbolic.pcv /=. exact: Hpc2.
  +
    rewrite /Symbolic.pct /=.
    congr LRC.Level. by lia.
  +
    move=> r''.
    have Egcom : Transitional.Register.get R_COM (TS.invalidate_ret tregs)
                 = Transitional.Register.get R_COM tregs by [].
    case: r''.
    *
      right.
      exists (Atom w0' Invalidated).
      split.
      { by rewrite !setmE HA0c. }
      { by []. }
      { by []. }
    *
      left.
      exists (Atom w1' Other).
      split.
      { by rewrite !setmE HA1c. }
      { rewrite Egcom /tvrel /= Htagcom Hvalcom /=. exact: Hvr1. }
      { by rewrite Egcom /= Htagcom. }
    *
      right.
      exists (Atom w2' Invalidated).
      split.
      { by rewrite !setmE HA2c. }
      { by []. }
      { by []. }
    *
      right.
      exists (Atom w3' Invalidated).
      split.
      { by rewrite !setmE HA3c. }
      { by []. }
      { by []. }
    *
      left.
      have Egra : Transitional.Register.get R_RA (TS.invalidate_ret tregs)
                  = Transitional.MVal Invalidated (Ptr pc').
      { by rewrite /TS.invalidate_ret /= Hget. }
      exists (Atom wra Invalidated).
      split.
      { by rewrite !setmE. }
      { by rewrite Egra /tvrel /=. }
      { by rewrite Egra. }
    *
      right.
      exists (Atom w5' Invalidated).
      split.
      { by rewrite !setmE HA5c. }
      { by []. }
      { by []. }
    *
      right.
      exists (Atom w6' Invalidated).
      split.
      { by rewrite !setmE HA6c. }
      { by []. }
      { by []. }
  + exact: Hmem.
  + exact: Hcode.
  +
    do 11!apply: sysregs_ok_setm.
    exact: Hsys.
  + exact: Hgap.
- exact: erefl.
- exact: erefl.
Qed.

End Diagrams.
