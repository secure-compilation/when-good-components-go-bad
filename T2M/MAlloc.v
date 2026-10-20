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
Require Import T2M.MStep.
Require T2M.MDefs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section AllocDiagram.

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
Hypothesis HPB :
  PB = Intermediate.prog_buffers (Intermediate.program_link pra prb).
Hypothesis Hwfa : Intermediate.well_formed_program pra.
Hypothesis Hwfb : Intermediate.well_formed_program prb.
Hypothesis Hlinkable :
  linkable (Intermediate.prog_interface pra) (Intermediate.prog_interface prb).
Hypothesis Hsmall :
  size (linearize_bufs PB) + size codeW < Merged.alloc_label.
Hypothesis HNCws : NC <= word_size mt.
Hypothesis HNCal : Merged.alloc_label < 2 ^ (word_size mt - NC).


Lemma prefix_val (m : nat) :
  m < 2 ^ NC ->
  (\val (LRC.component_memory_prefix (NC := NC) (ssrint.Posz m)
        : word (word_size mt)) : nat)
  = m * 2 ^ (word_size mt - NC).
Proof.
move=> Hm.
have Hsub : word_size mt - NC < 2 ^ (word_size mt)
  by apply: (leq_ltn_trans (leq_subr NC (word_size mt))); apply: ltn_expl.
have Hmw : m < 2 ^ (word_size mt) by apply: (leq_trans Hm); rewrite leq_exp2l.
have Hprod : m * 2 ^ (word_size mt - NC) < 2 ^ (word_size mt).
{ rewrite -{2}(subnK HNCws) expnD [X in _ < X]mulnC ltn_mul2r expn_gt0 /=.
  exact: Hm. }
rewrite /LRC.component_memory_prefix.
set wm := word.as_word (ssrint.Posz m).
set sh := word.as_word (ssrint.Posz (word_size mt - NC)).
rewrite valw_shlw.
have Evm : (\val wm : nat) = m
  by rewrite /wm valw_as_word modn_small.
have Evsh : (\val sh : nat) = word_size mt - NC
  by rewrite /sh valw_as_word modn_small.
apply: (eq_trans
          (y := (m * 2 ^ (word_size mt - NC)) %% 2 ^ word_size mt)).
- congr (_ %% _).
  congr (_ * 2 ^ _).
  + exact: Evm.
  + exact: Evsh.
- exact: modn_small Hprod.
Qed.

Lemma andw_mask_val (w : word (word_size mt)) :
  (\val (word.andw w (LRC.mask (NC := NC))) : nat)
  = \val w %/ 2 ^ (word_size mt - NC) * 2 ^ (word_size mt - NC).
Proof.
have NatpowE : forall a b, Nat.pow a b = expn a b.
{ move=> a; elim => [|b IH]; first by rewrite expn0.
  by rewrite expnS /= IH. }
have Hmone : (word.as_word (Nat.sub (Nat.pow 2 (word_size mt)) 1)
              : word (word_size mt)) = monew.
{ rewrite NatpowE. apply: mone_as_word. }
rewrite /LRC.mask.
set sh := word.as_word (ssrint.Posz (word_size mt - NC)).
rewrite Hmone.
rewrite val_andw_shlw_mone.
have Hsub : word_size mt - NC < 2 ^ word_size mt
  by apply: (leq_ltn_trans (leq_subr NC (word_size mt))); apply: ltn_expl.
have Evsh : (\val sh : nat) = word_size mt - NC
  by rewrite /sh valw_as_word modn_small.
congr (_ %/ 2 ^ _ * 2 ^ _).
- exact: Evsh.
- exact: Evsh.
Qed.

Lemma pfilter_val (c0 : nat) (w : word (word_size mt)) :
  1 + c0 < 2 ^ NC ->
  (word.andw w (LRC.mask (NC := NC))
   == LRC.component_memory_prefix (NC := NC) (ssrint.Posz (1 + c0)))
  = ((1 + c0) * 2 ^ (word_size mt - NC) <= \val w)
    && (\val w < (2 + c0) * 2 ^ (word_size mt - NC)).
Proof.
move=> Hc.
have Hk : 0 < 2 ^ (word_size mt - NC) by rewrite expn_gt0.
apply/idP/idP.
- move=> /eqP E.
  have Ev : (\val (word.andw w (LRC.mask (NC := NC))) : nat)
            = \val (LRC.component_memory_prefix (NC := NC)
                      (ssrint.Posz (1 + c0)) : word (word_size mt))
    by rewrite E.
  have Ev2 := eq_trans (eq_trans (esym (andw_mask_val w)) Ev)
                (prefix_val Hc).
  have Hq : \val w %/ 2 ^ (word_size mt - NC) = 1 + c0.
  { move: Ev2 => /eqP Ev3.
    rewrite (eqn_pmul2r Hk) in Ev3.
    apply/eqP. exact: Ev3. }
  apply/andP; split; by lia.
- move=> /andP[H1 H2].
  have Hle1 : \val w %/ 2 ^ (word_size mt - NC) < 2 + c0
    by rewrite ltn_divLR //.
  have Hle2 : 1 + c0 <= \val w %/ 2 ^ (word_size mt - NC)
    by rewrite leq_divRL //.
  have Hq : \val w %/ 2 ^ (word_size mt - NC) = 1 + c0 by lia.
  apply/eqP.
  apply: word_nat_inj.
  have Emid : \val w %/ 2 ^ (word_size mt - NC) * 2 ^ (word_size mt - NC)
              = (1 + c0) * 2 ^ (word_size mt - NC).
  { by rewrite Hq. }
  exact: (eq_trans (eq_trans (andw_mask_val w) Emid)
            (esym (prefix_val Hc))).
Qed.

Lemma word_leq_val (k : nat) (w1 w2 : word k) :
  Ord.leq w1 w2 = ((\val w1 : nat) <= (\val w2 : nat)).
Proof. by []. Qed.

Lemma val_addw_small (w : word (word_size mt)) (n : nat) :
  \val w + n < 2 ^ word_size mt ->
  (\val (addw w (word.as_word (ssrint.Posz n))) : nat) = \val w + n.
Proof.
move=> H.
have HnW : n < 2 ^ word_size mt by lia.
by rewrite valw_addw valw_as_word modnDmr (modn_small H).
Qed.

Lemma addw_region_nowrap (c0 : nat) (w : word (word_size mt)) (n : nat) :
  1 + c0 < 2 ^ NC ->
  n <= 2 ^ (word_size mt - NC) ->
  (1 + c0) * 2 ^ (word_size mt - NC)
    <= \val (addw w (word.as_word (ssrint.Posz n))) ->
  \val w + n < 2 ^ word_size mt.
Proof.
move=> Hc Hn Hep.
case: (ltnP (\val w + n) (2 ^ word_size mt)) => // Hge.
exfalso.
have Hvw : (\val w : nat) < 2 ^ word_size mt := ltn_ord (\val w).
have Hkw : 2 ^ (word_size mt - NC) <= 2 ^ word_size mt
  by rewrite leq_exp2l // leq_subr.
have Ha2 : \val w + n - 2 ^ word_size mt < 2 ^ word_size mt by lia.
have Hval : (\val (addw w (word.as_word (ssrint.Posz n))) : nat)
            = \val w + n - 2 ^ word_size mt.
{ rewrite valw_addw valw_as_word modnDmr.
  by rewrite -{1}(subnK Hge) modnDr (modn_small Ha2). }
have Hmul : 2 ^ (word_size mt - NC)
            <= (1 + c0) * 2 ^ (word_size mt - NC)
  by rewrite leq_pmull.
rewrite Hval in Hep.
by lia.
Qed.

Definition pfilterC (c0 : nat) : pred (mword mt) :=
  fun mw => word.andw mw (LRC.mask (NC := NC))
            == LRC.component_memory_prefix (NC := NC)
                 (ssrint.Posz (1 + c0)).

Lemma List_filter_seq (T : Type) (p : pred T) (l : seq T) :
  List.filter p l = filter p l.
Proof. by elim: l => //= a l ->. Qed.

Lemma List_last_seq (T : Type) (d : T) (l : seq T) :
  List.last l d = last d l.
Proof.
elim: l d => [|a l IH] d //.
case: l IH => [|b l'] IH //.
have E1 : List.last [:: a, b & l'] d = List.last (b :: l') d by [].
by rewrite E1 (IH d).
Qed.

Definition maxaddr (m : {fmap mword mt -> atom (mword mt) mem_tag})
    (c0 : nat) : mword mt :=
  List.last
    (List.filter (pfilterC c0) (domm m))
    (LRC.component_memory_prefix (NC := NC) (ssrint.Posz (1 + c0))).

Lemma maxaddrE (m : {fmap mword mt -> atom (mword mt) mem_tag})
    (c0 : nat) :
  maxaddr m c0
  = last (LRC.component_memory_prefix (NC := NC) (ssrint.Posz (1 + c0)))
      (filter (pfilterC c0) (domm m)).
Proof.
by rewrite /maxaddr List_filter_seq List_last_seq.
Qed.

Lemma maxaddr_lo (m : {fmap mword mt -> atom (mword mt) mem_tag})
    (c0 : nat) :
  1 + c0 < 2 ^ NC ->
  (1 + c0) * 2 ^ (word_size mt - NC) <= \val (maxaddr m c0).
Proof.
move=> Hc.
case E: (filter (pfilterC c0) (domm m)) => [|x s].
- have E0 : maxaddr m c0
            = LRC.component_memory_prefix (NC := NC) (ssrint.Posz (1 + c0))
    by rewrite maxaddrE E.
  have Ev := prefix_val Hc.
  by rewrite E0 Ev.
- have E0 : maxaddr m c0
            = last (LRC.component_memory_prefix (NC := NC)
                      (ssrint.Posz (1 + c0))) (x :: s)
    by rewrite maxaddrE E.
  have Hp : pfilterC c0
              (last (LRC.component_memory_prefix (NC := NC)
                       (ssrint.Posz (1 + c0))) (x :: s)).
  { have Hin : last (LRC.component_memory_prefix (NC := NC)
                       (ssrint.Posz (1 + c0))) (x :: s)
               \in filter (pfilterC c0) (domm m).
    { rewrite E.
      have -> : last (LRC.component_memory_prefix (NC := NC)
                        (ssrint.Posz (1 + c0))) (x :: s) = last x s by [].
      exact: (mem_last x s). }
    by move: Hin; rewrite mem_filter => /andP[]. }
  move: Hp; rewrite /pfilterC pfilter_val // => /andP[H1 _].
  by rewrite E0.
Qed.

Lemma above_max_none (m : {fmap mword mt -> atom (mword mt) mem_tag})
    (c0 : nat) (w : mword mt) :
  1 + c0 < 2 ^ NC ->
  (1 + c0) * 2 ^ (word_size mt - NC) <= \val w ->
  \val w < (2 + c0) * 2 ^ (word_size mt - NC) ->
  (\val (maxaddr m c0) : nat) < \val w ->
  m w = None.
Proof.
move=> Hc Hlo Hhi Hmax.
case E: (m w) => [v|] //.
exfalso.
have Hdomm : w \in domm m by rewrite mem_domm E.
have Hp : pfilterC c0 w.
{ rewrite /pfilterC pfilter_val //.
  apply/andP; split.
  - exact: Hlo.
  - exact: Hhi. }
have Hle := domm_filter_last_max
              (p := pfilterC c0)
              (LRC.component_memory_prefix (NC := NC)
                 (ssrint.Posz (1 + c0)))
              Hdomm Hp.
rewrite word_leq_val in Hle.
rewrite -maxaddrE in Hle.
have Habs := leq_ltn_trans Hle Hmax.
by rewrite ltnn in Habs.
Qed.


Lemma pc_rel_nextK (K : nat) (tpc : Pointer.t) (w : mword mt)
    (i : Transitional.instr) (tg : mem_tag) :
  texp_size i = K ->
  Transitional.executing cdeW tpc i tg (Pointer.component tpc) ->
  pc_relW tpc w ->
  exists pos,
    [/\ w = word_of_nat (pos + pc0),
        cmapWW (Pointer.component tpc)
          (BinInt.Z.to_nat (Pointer.offset tpc)) = Some (pos + pc0)
      & pc_relW (Pointer.inc tpc) (word_of_nat ((pos + K) + pc0))].
Proof.
move=> Htexp Hex Hpc.
have Hcomp' : Pointer.component (Pointer.inc tpc) = Pointer.component tpc.
{ exact: Pointer.inc_preserves_component. }
case: Hpc => cseg Hside Hseg Hle Hw.
-
  have Hnth : List.nth_error cseg
                (BinInt.Z.to_nat (Pointer.offset tpc)) = Some (i, tg).
  { case: Hex => C_code [_ [Hcde [_ Hn]]].
    move: Hcde. rewrite (cdeW_left prb PI Hside) Hseg.
    by move=> [->]. }
  exists (tpos PI pra (Pointer.component tpc) cseg
            (BinInt.Z.to_nat (Pointer.offset tpc))).
  split; first exact: Hw.
  { by rewrite /cmapW Hside Hseg /=. }
  apply: (@PCLeft _ _ _ _ _ _ _ _ _ cseg).
  + by rewrite Hcomp'.
  + by rewrite Hcomp'.
  + rewrite inc_offset. by lia.
  + have Hoff' : BinInt.Z.to_nat (Pointer.offset (Pointer.inc tpc))
                 = (BinInt.Z.to_nat (Pointer.offset tpc)).+1.
    { rewrite inc_offset. by lia. }
    congr word_of_nat.
    rewrite Hcomp' Hoff'
            (tpos_next PI pra (Pointer.component tpc) Hnth) Htexp.
    by lia.
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
  { by rewrite /cmapW (negbTE Hside) Hseg /=. }
  apply: (@PCRight _ _ _ _ _ _ _ _ _ cseg).
  + by rewrite Hcomp'.
  + by rewrite Hcomp'.
  + rewrite inc_offset. by lia.
  + have Hoff' : BinInt.Z.to_nat (Pointer.offset (Pointer.inc tpc))
                 = (BinInt.Z.to_nat (Pointer.offset tpc)).+1.
    { rewrite inc_offset. by lia. }
    congr word_of_nat.
    rewrite Hcomp' Hoff'
            (tpos_next PI prb (Pointer.component tpc) Hnth) Htexp.
    by lia.
Qed.



Lemma bloc_key_val (m : {fmap mword mt -> atom (mword mt) mem_tag})
    (c0 len n : nat) :
  1 + c0 < 2 ^ NC ->
  len + 1 <= 2 ^ (word_size mt - NC) ->
  pfilterC c0 (word.addw (maxaddr m c0)
                 (word.as_word (ssrint.Posz (len + 1)))) ->
  n + 1 <= len + 1 ->
  (\val (word.addw (maxaddr m c0)
           (word.as_word (ssrint.Posz (n + 1)))) : nat)
  = \val (maxaddr m c0) + (n + 1).
Proof.
move=> Hc Hlen Hfit Hn.
have Hep : (1 + c0) * 2 ^ (word_size mt - NC)
           <= \val (word.addw (maxaddr m c0)
                      (word.as_word (ssrint.Posz (len + 1)))).
{ move: Hfit; rewrite /pfilterC pfilter_val // => /andP[H1 _].
  exact: H1. }
have Hnw := addw_region_nowrap Hc Hlen Hep.
apply: val_addw_small.
by lia.
Qed.


Lemma to_nat_le6 (r : register) : Intermediate.Register.to_nat r <= 6.
Proof. by case: r. Qed.

Lemma wkey_neq (i j : nat) :
  i < 32 -> j < 32 -> i <> j ->
  (@word_of_nat (reg_field_size mt) i
   != @word_of_nat (reg_field_size mt) j).
Proof.
move=> Hi Hj Hne.
rewrite (won_eqE (small_lt_reg Hi) (small_lt_reg Hj)).
apply/negP => /eqP E. by lia.
Qed.

Lemma alloc_fun_spec (st : @Symbolic.state mt lrc_tags unit)
    (c0 lvl : nat) (wret wsz : mword mt) (len : nat)
    (rc : atom (mword mt) mem_tag) (a16 : @ratom mt) :
  taga (Symbolic.pc st) = LRC.Level lvl c0 ->
  Symbolic.regs st (ra : reg mt) = Some (Atom wret InternalJump) ->
  Symbolic.mem st wret = Some rc ->
  is_code (taga rc) ->
  color (taga rc) = c0 ->
  Symbolic.regs st (syscall_arg1 : reg mt) = Some (Atom wsz Other) ->
  word.int_of_word wsz = ssrint.Posz len ->
  Symbolic.regs st (syscall_ret : reg mt) = Some a16 ->
  0 < len ->
  len + 1 <= 2 ^ (word_size mt - NC) ->
  1 + c0 < 2 ^ NC ->
  pfilterC c0 (word.addw (maxaddr (Symbolic.mem st) c0)
                 (word.as_word (ssrint.Posz (len + 1)))) ->
  LRC.alloc_fun (NC := NC) st
  = Some (@Symbolic.State mt lrc_tags unit
            (unionm (Symbolic.mem st)
               (mkfmap (mkseq (fun n =>
                  (word.addw (maxaddr (Symbolic.mem st) c0)
                     (word.as_word (ssrint.Posz (n + 1))),
                   Atom (word.as_word 0) (def_mem_tag c0 false))) len)))
            (setm (Symbolic.regs st) (syscall_ret : reg mt)
               (Atom (word.addw (maxaddr (Symbolic.mem st) c0)
                        (word.as_word (ssrint.Posz 1))) Other))
            (Atom wret (LRC.Level lvl c0))
            tt).
Proof.
move=> Hpct Hra Hrc Hic Hcol Hsz Hint Hret Hpos Hlen Hc Hfit.
case: len Hint Hpos Hlen Hfit => [|len0] // Hint _ Hlen Hfit.
have obE : forall (S T : Type) (f : S -> option T) (y : S),
    obind f (Some y) = f y by [].
have EIJ : LRC.is_jump InternalJump = Some tt by [].
have EIO : LRC.is_other Other = Some tt by [].
rewrite /LRC.alloc_fun.
rewrite Hpct.
cbv beta iota zeta.
rewrite Hra obE.
cbv beta.
rewrite EIJ obE.
cbv beta.
rewrite Hrc obE.
cbv beta.
rewrite Hic Hcol eqxx.
cbv beta iota.
rewrite obE.
cbv beta.
rewrite Hsz obE.
cbv beta.
rewrite EIO obE.
cbv beta.
rewrite Hint.
cbv beta iota.
rewrite obE.
cbv beta.
rewrite Hlen.
cbv beta iota.
rewrite obE.
cbv beta.
case: ifP => [Hneg|Hneg].
- exfalso.
  move: Hfit; rewrite /pfilterC /maxaddr => Hfit.
  by rewrite Hfit in Hneg.
- rewrite /updm Hret.
  cbv beta iota.
  by congr Some.
Qed.



Lemma region_end_le (c0 : nat) :
  1 + c0 < 2 ^ NC ->
  (2 + c0) * 2 ^ (word_size mt - NC) <= 2 ^ word_size mt.
Proof.
move=> Hc.
have H2 : 2 + c0 <= 2 ^ NC by lia.
rewrite -{2}(subnKC HNCws) expnD.
exact: leq_mul H2 (leqnn _).
Qed.

Lemma alloc_end_val
    (m : {fmap mword mt -> atom (mword mt) mem_tag}) (c0 len : nat) :
  1 + c0 < 2 ^ NC ->
  len + 1 <= 2 ^ (word_size mt - NC) ->
  pfilterC c0 (word.addw (maxaddr m c0)
                 (word.as_word (ssrint.Posz (len + 1)))) ->
  [/\ (\val (word.addw (maxaddr m c0)
              (word.as_word (ssrint.Posz (len + 1)))) : nat)
      = \val (maxaddr m c0) + (len + 1)
    & \val (maxaddr m c0) + (len + 1)
      < (2 + c0) * 2 ^ (word_size mt - NC)].
Proof.
move=> Hc Hlen Hfit.
have Ev := bloc_key_val Hc Hlen Hfit (leqnn (len + 1)).
split; first exact: Ev.
have Hhi : \val (word.addw (maxaddr m c0)
              (word.as_word (ssrint.Posz (len + 1))))
           < (2 + c0) * 2 ^ (word_size mt - NC).
{ move: Hfit; rewrite /pfilterC pfilter_val // => /andP[_ H2].
  exact: H2. }
by rewrite Ev in Hhi.
Qed.

Lemma mkfmap_notin_None (T : ordType) (S : Type)
    (kvs : seq (T * S)) (k : T) :
  k \notin [seq p.1 | p <- kvs] ->
  mkfmap kvs k = None.
Proof.
elim: kvs => [|[k0 v0] kvs IH] //=.
rewrite inE negb_or => /andP[Hne Hnin].
rewrite setmE (negbTE Hne).
exact: IH.
Qed.

Lemma alloc_block_rekey
    (m : {fmap mword mt -> atom (mword mt) mem_tag}) (c0 len : nat) :
  1 + c0 < 2 ^ NC ->
  len + 1 <= 2 ^ (word_size mt - NC) ->
  pfilterC c0 (word.addw (maxaddr m c0)
                 (word.as_word (ssrint.Posz (len + 1)))) ->
  mkseq (fun n =>
     (word.addw (maxaddr m c0) (word.as_word (ssrint.Posz (n + 1))),
      Atom (word.as_word 0) (def_mem_tag c0 false))) len
  = [seq (@word_of_nat (word_size mt)
            (((\val (maxaddr m c0) : nat) + 1) + o),
          Atom (word.as_word 0 : mword mt) (def_mem_tag c0 false))
    | o <- iota 0 len].
Proof.
move=> Hc Hlen Hfit.
have [Eend Hend] := alloc_end_val Hc Hlen Hfit.
rewrite /mkseq.
apply/eq_in_map => n.
rewrite mem_iota add0n => /andP[_ Hn].
have Hn1 : n + 1 <= len + 1 by lia.
have Ek := bloc_key_val Hc Hlen Hfit Hn1.
have Hb : ((\val (maxaddr m c0) : nat) + 1) + n < 2 ^ word_size mt.
{ have Hle := region_end_le Hc. by lia. }
have Ekey : word.addw (maxaddr m c0) (word.as_word (ssrint.Posz (n + 1)))
            = @word_of_nat (word_size mt)
                (((\val (maxaddr m c0) : nat) + 1) + n).
{ apply: word_nat_inj.
  have Er : (\val (@word_of_nat (word_size mt)
                     (((\val (maxaddr m c0) : nat) + 1) + n)) : nat)
            = ((\val (maxaddr m c0) : nat) + 1) + n
    by rewrite valw_as_word (modn_small Hb).
  have Emid : (\val (maxaddr m c0) : nat) + (n + 1)
              = ((\val (maxaddr m c0) : nat) + 1) + n by lia.
  exact: (eq_trans (eq_trans Ek Emid) (esym Er)). }
by rewrite Ekey.
Qed.



Lemma sim_alloc (amap : amap_t)
    (tmem : Transitional.Memory.t) (tregs : Transitional.Register.t)
    (tpc : Pointer.t) (tpct : Transitional.pc_tag)
    (ms : @Symbolic.state mt lrc_tags unit)
    (tg : mem_tag) (c : Component.id) (rptr rsize : register)
    (zsz : Z) (tmem' : Transitional.Memory.t) (ptr : Pointer.t) :
  match_statesW amap tmem tregs tpc tpct ms ->
  reg_syncedW amap tregs (Symbolic.regs ms) rsize ->
  Transitional.executing cdeW tpc (TrAlloc rptr rsize) tg c ->
  Transitional.check_pc cdeW tpc tg ->
  Transitional.tvtag (Transitional.Register.get rsize tregs) = Other ->
  Transitional.val (Transitional.Register.get rsize tregs) = Values.Int zsz ->
  BinInt.Z.lt BinNums.Z0 zsz ->
  Transitional.Memory.alloc tmem c (BinInt.Z.to_nat zsz)
    = Some (tmem', ptr) ->
  1 + Pointer.component tpc < 2 ^ NC ->
  BinInt.Z.to_nat zsz + 1 <= 2 ^ (word_size mt - NC) ->
  pfilterC (Pointer.component tpc)
    (word.addw (maxaddr (Symbolic.mem ms) (Pointer.component tpc))
       (word.as_word (ssrint.Posz (BinInt.Z.to_nat zsz + 1)))) ->
  exists amap' ms1 ms2 ms3 ms4 ms5 ms',
    step_me (NC := NC) ms ms1 None /\
    step_me (NC := NC) ms1 ms2 None /\
    step_me (NC := NC) ms2 ms3 None /\
    step_me (NC := NC) ms3 ms4 None /\
    step_me (NC := NC) ms4 ms5 None /\
    step_me (NC := NC) ms5 ms' None /\
    match_statesW amap' tmem'
      (Transitional.Register.set rptr (Ptr ptr) Other tregs)
      (Pointer.inc tpc) tpct ms' /\
    Symbolic.mem ms' = unionm (Symbolic.mem ms)
      (mkfmap (mkseq (fun n =>
         (word.addw (maxaddr (Symbolic.mem ms) (Pointer.component tpc))
            (word.as_word (ssrint.Posz (n + 1))),
          Atom (word.as_word 0 : mword mt)
            (def_mem_tag (Pointer.component tpc) false)))
         (BinInt.Z.to_nat zsz))) /\
    (forall r : register, r <> rptr ->
       getm (Symbolic.regs ms')
         (@word_of_nat (reg_field_size mt)
            (Intermediate.Register.to_nat r))
       = getm (Symbolic.regs ms)
           (@word_of_nat (reg_field_size mt)
              (Intermediate.Register.to_nat r))) /\
    (exists wret,
       getm (Symbolic.regs ms')
         (@word_of_nat (reg_field_size mt)
            (Intermediate.Register.to_nat rptr))
       = Some (Atom wret Other)
       /\ tvrel cmapWW amap' (Transitional.MVal Other (Ptr ptr)) wret) /\
    (exists base,
       [/\ amap' = amap_upd amap (Pointer.component ptr)
                     (Pointer.block ptr) base,
           addr_of amap (Pointer.component ptr) (Pointer.block ptr)
             = None
         & forall o, o < BinInt.Z.to_nat zsz ->
             getm (Symbolic.mem ms')
               (@word_of_nat (word_size mt) (base + o))
             = Some (Atom (word.as_word 0 : mword mt)
                       (def_mem_tag (Pointer.component tpc) false))]).
Proof.
move=> Hm Hsyncr Hex0 Hcp Htagsz Hvalsz Hposz Hal Hc1 Hfitlen Hfitcap.
have [Ec Hic Hcol] := executing_props Hex0.
subst c.
case: tg Hex0 Hic Hcol Hcp => vt0 col0 ent0 isc0 Hex0 /= Hic Hcol Hcp.
subst isc0 col0.
set tg := MTag vt0 (Pointer.component tpc) ent0 true.
move: Hal; rewrite /Transitional.Memory.alloc.
case Hcm: (tmem (Pointer.component tpc)) => [cm|] //=.
move=> [Etm Etp].
have [wsz [Hrsz Hvsz Htsz]] := Hsyncr.
case: wsz Hrsz Hvsz Htsz => wsz tsz Hrsz Hvsz Htsz.
have Etsz : tsz = Other by rewrite /= in Htsz; rewrite Htsz Htagsz.
rewrite {}Etsz in Hrsz.
move: Hvsz; rewrite /tvrel Htagsz Hvalsz /= => Hvsz.
have Hwrep := vrel_int_inv Hbound HPB Hsmall Hvsz.
move: Hwrep; rewrite /wrepr => Hwrep.
have Hint : word.int_of_word wsz = ssrint.Posz (BinInt.Z.to_nat zsz).
{ case E: (word.int_of_word wsz) Hwrep => [x|x] /= Hwrep.
  - congr ssrint.Posz. by lia.
  - exfalso. by lia. }
have Hlen0 : 0 < BinInt.Z.to_nat zsz by lia.
case: Hm => Hpc Hpct Hregs Hmem Hcode Hsys Hgap.
have Hcell0 : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrAlloc rptr rsize, tg)) 0
  = Some (MrMov (inl rsize) (inr R_SC_ARG1), tg) by [].
have Hcell1 : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrAlloc rptr rsize, tg)) 1
  = Some (MrMov (inl R_RA) (inr R_SC_ARG3), tg) by [].
have Hcell2 : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrAlloc rptr rsize, tg)) 2
  = Some (MrJal Merged.alloc_label, tg) by [].
have Hcell3 : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrAlloc rptr rsize, tg)) 3
  = Some (MrMov (inr R_SC_ARG3) (inl R_RA), tg) by [].
have Hcell4 : List.nth_error
    (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB)
       (TrAlloc rptr rsize, tg)) 4
  = Some (MrMov (inr R_SC_RET) (inl rptr), tg) by [].
have Hb0 : 0 < texp_size (TrAlloc rptr rsize : Transitional.instr) by [].
have Hb1 : 1 < texp_size (TrAlloc rptr rsize : Transitional.instr) by [].
have Hb2 : 2 < texp_size (TrAlloc rptr rsize : Transitional.instr) by [].
have Hb3 : 3 < texp_size (TrAlloc rptr rsize : Transitional.instr) by [].
have Hb4 : 4 < texp_size (TrAlloc rptr rsize : Transitional.instr) by [].
have [p0 [v0 [Hw0 Hv0 Ht0 Hd0 Hpin0]]] :=
  match_fetch_k Hbound Hcode Hex0 Hpc Hb0 Hcell0.
have [p1 [v1 [Hw1 Hv1 Ht1 Hd1 Hpin1]]] :=
  match_fetch_k Hbound Hcode Hex0 Hpc Hb1 Hcell1.
have [p2 [v2 [Hw2 Hv2 Ht2 Hd2 Hpin2]]] :=
  match_fetch_k Hbound Hcode Hex0 Hpc Hb2 Hcell2.
have [p3 [v3 [Hw3 Hv3 Ht3 Hd3 Hpin3]]] :=
  match_fetch_k Hbound Hcode Hex0 Hpc Hb3 Hcell3.
have [p4 [v4 [Hw4 Hv4 Ht4 Hd4 Hpin4]]] :=
  match_fetch_k Hbound Hcode Hex0 Hpc Hb4 Hcell4.
have Ep1 : p1 = p0.
{ move: Hpin1; rewrite Hpin0 => - [E]. by lia. }
have Ep2 : p2 = p0.
{ move: Hpin2; rewrite Hpin0 => - [E]. by lia. }
have Ep3 : p3 = p0.
{ move: Hpin3; rewrite Hpin0 => - [E]. by lia. }
have Ep4 : p4 = p0.
{ move: Hpin4; rewrite Hpin0 => - [E]. by lia. }
rewrite {}Ep1 in Hw1 Hv1 Hd1; rewrite {}Ep2 in Hw2 Hv2 Hd2.
rewrite {}Ep3 in Hw3 Hv3 Hd3; rewrite {}Ep4 in Hw4 Hv4 Hd4.
have [i5 [tg5 Hex5]] := check_pc_next Hbound Hsmall Hcp.
rewrite Pointer.inc_preserves_component in Hex5.
have Htx5 : texp_size (TrAlloc rptr rsize : Transitional.instr) = 5 by [].
have [pN [HwN HpinN HpcN]] := pc_rel_nextK Htx5 Hex0 Hpc.
have EpN : pN = p0.
{ move: HpinN; rewrite Hpin0 => - [E]. by lia. }
rewrite {}EpN in HwN HpcN.
have [_ Hic5 Hcol5] := executing_props Hex5.
case: tg5 Hex5 Hic5 Hcol5 => vt5 col5 ent5 isc5 Hex5 /= Hic5 Hcol5.
subst isc5 col5.
set tni := MTag vt5 (Pointer.component tpc) ent5 true.
have [cell5 Hcell5] : exists cell5,
    List.nth_error
      (cell_exp (can_make L P C) (can_upd L) (memory_lengths PB) (i5, tni)) 0
    = Some cell5.
{ apply: nth_error_Some_ex.
  rewrite lin_size_length size_cell_exp. by case: i5 {Hex5}. }
have Ecell5 : cell5.2 = tni := cell_exp_snd Hcell5.
have Hex5'' : Transitional.executing cdeW (Pointer.inc tpc) i5 tni
                (Pointer.component (Pointer.inc tpc)).
{ rewrite Pointer.inc_preserves_component. exact: Hex5. }
have [p5 [v5 [Hwv5 Hv5 Ht5 _ Hpin5]]] :=
  match_fetch Hbound Hcode Hex5'' HpcN Hcell5.
rewrite Ecell5 in Ht5.
have [rc Hrc] := mregs_rel_lookup R_COM Hregs.
have [raRA HraL] := mregs_rel_lookup R_RA Hregs.
case: raRA HraL => wra tra HraL.
have [rap Hrp] := mregs_rel_lookup rptr Hregs.
have [a16 Ha16] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 16) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
have [a17 Ha17] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 17) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
have [a19 Ha19] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 19) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
have [a7 Ha7] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 7) = Some a
  by apply: Hsys; rewrite !inE eqxx.
case: a7 Ha7 => w7' t7' Ha7.
have [a18 Ha18] : exists a,
    Symbolic.regs ms (@word_of_nat (reg_field_size mt) 18) = Some a
  by apply: Hsys; rewrite !inE eqxx !orbT.
case: a18 Ha18 => w18' t18' Ha18.
case: a16 Ha16 => w16' t16' Ha16.
have [aON HA0] := mregs_rel_lookup R_ONE Hregs.
case: aON HA0 => w0' t0' HA0.
have [aA1 HA2r] := mregs_rel_lookup R_AUX1 Hregs.
case: aA1 HA2r => w2' t2' HA2r.
have [aA2 HA3r] := mregs_rel_lookup R_AUX2 Hregs.
case: aA2 HA3r => w3' t3' HA3r.
have [aSP HA5] := mregs_rel_lookup R_SP Hregs.
case: aSP HA5 => w5' t5' HA5.
have [aAR HA6] := mregs_rel_lookup R_ARG Hregs.
case: aAR HA6 => w6' t6' HA6.
case: rc Hrc => wrc trc Hrc.
case: a17 Ha17 => w17o t17o Ha17.
case: a19 Ha19 => w19o t19o Ha19.
rewrite /Symbolic.pct in Hpct.
set K4 := @word_of_nat (reg_field_size mt) 4.
set K16 := @word_of_nat (reg_field_size mt) 16.
set K17 := @word_of_nat (reg_field_size mt) 17.
set K19 := @word_of_nat (reg_field_size mt) 19.
set Krs := @word_of_nat (reg_field_size mt)
             (Intermediate.Register.to_nat rsize).
set Krp := @word_of_nat (reg_field_size mt)
             (Intermediate.Register.to_nat rptr).
set tra2 := moved_tag tra.
set MAXA := maxaddr (Symbolic.mem ms) (Pointer.component tpc).
set LEN := BinInt.Z.to_nat zsz.
pose ADDR := word.addw MAXA (word.as_word (ssrint.Posz 1)).
set NEWBASE := ((\val MAXA : nat) + 1).
set regs1 := setm (setm (Symbolic.regs ms) Krs (Atom wsz Other))
               K17 (Atom wsz Other).
set regs2 := setm (setm regs1 K4 (Atom wra tra2)) K19 (Atom wra tra).
set regs3 := setm regs2 K4
               (Atom (@word_of_nat (word_size mt) ((p0 + 3) + pc0))
                  InternalJump).
set BLOC := mkfmap (mkseq (fun n =>
               (word.addw MAXA (word.as_word (ssrint.Posz (n + 1))),
                Atom (word.as_word 0 : mword mt)
                  (def_mem_tag (Pointer.component tpc) false))) LEN).
set MEM4 := unionm (Symbolic.mem ms) BLOC.
set regs4 := setm regs3 K16 (Atom ADDR Other).
set regs5 := setm (setm regs4 K19 (Atom wra tra2)) K4 (Atom wra tra).
set regs6 := setm (setm regs5 K16 (Atom ADDR Other)) Krp (Atom ADDR Other).
set PCT := LRC.Level (Transitional.level tpct) (Pointer.component tpc).
exists (amap_upd amap (Pointer.component tpc)
          (Transitional.Memory.nextblock cm) NEWBASE).
exists (@Symbolic.State mt lrc_tags unit (Symbolic.mem ms) regs1
          (@word_of_nat (word_size mt) ((p0 + 1) + pc0))@PCT
          (Symbolic.internal ms)).
exists (@Symbolic.State mt lrc_tags unit (Symbolic.mem ms) regs2
          (@word_of_nat (word_size mt) ((p0 + 2) + pc0))@PCT
          (Symbolic.internal ms)).
exists (@Symbolic.State mt lrc_tags unit (Symbolic.mem ms) regs3
          (@word_of_nat (word_size mt) Merged.alloc_label)@PCT
          (Symbolic.internal ms)).
exists (@Symbolic.State mt lrc_tags unit MEM4 regs4
          (@word_of_nat (word_size mt) ((p0 + 3) + pc0))@PCT tt).
exists (@Symbolic.State mt lrc_tags unit MEM4 regs5
          (@word_of_nat (word_size mt) ((p0 + 4) + pc0))@PCT tt).
exists (@Symbolic.State mt lrc_tags unit MEM4 regs6
          (@word_of_nat (word_size mt) ((p0 + 5) + pc0))@PCT tt).
split; last split; last split; last split; last split; last split;
  last split; last split; last split; last split.
-
  rewrite /step_me.
  have Ea1 : word.addw (Symbolic.pcv ms) onew
             = @word_of_nat (word_size mt) ((p0 + 1) + pc0).
  { rewrite Hw0 addw_onew. congr word_of_nat. by lia. }
  have Hk17 : K17 != Krs.
  { rewrite /K17 /Krs.
    have H6 := to_nat_le6 rsize.
    have HA : (17 : nat) < 32 by [].
    have HB : Intermediate.Register.to_nat rsize < 32 by lia.
    rewrite (won_eqE (small_lt_reg HA) (small_lt_reg HB)).
    apply/negP => /eqP E. by lia. }
  move: Hd0 => /= Hd0.
  have E00 : (p0 + 0) + pc0 = p0 + pc0 by lia.
  have Hv0' : Symbolic.mem ms (Symbolic.pcv ms) = Some v0.
  { rewrite Hw0 -E00. exact: Hv0. }
  apply: (@Symbolic.step_mov _ _ _ _ _ _ _ _ _
            (Symbolic.mem ms) (Symbolic.regs ms)
            (Symbolic.pcv ms) (taga (Symbolic.pc ms))
            (vala v0) (taga v0)
            Krs wsz Other
            K17 w17o t17o
            (Symbolic.internal ms)).
  + exact: Symbolic.state_eta.
  + by case: (v0) Hv0'.
  + exact: Hd0.
  + exact: Hrsz.
  + exact: Ha17.
  + rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc.
    rewrite Ea1 Hv1.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt)
              = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
    rewrite Hrc /=.
    rewrite /Merged.transfer /Merged.instr_rules.
    rewrite Hpct Ht0 /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite /check_belong /belong Ht1 /= eqxx /=.
    rewrite /Symbolic.next_state_do_update /updm.
    rewrite Hrsz /=.
    rewrite setmE (negbTE Hk17) Ha17 /=.
    by congr Some.
-
  rewrite /step_me.
  have H6 := to_nat_le6 rsize.
  have Eregs1 : regs1 = setm (Symbolic.regs ms) K17 (Atom wsz Other).
  { by rewrite /regs1 (setmI Hrsz). }
  have Hne_4_17 : K4 != K17.
  { rewrite /K4 /K17. by apply: wkey_neq; lia. }
  have Hne_19_17 : K19 != K17.
  { rewrite /K19 /K17. by apply: wkey_neq; lia. }
  have Hne_1_17 : (@word_of_nat (reg_field_size mt)
                     (Intermediate.Register.to_nat R_COM)) != K17.
  { rewrite /K17.
    have Hc6 := to_nat_le6 R_COM.
    by apply: wkey_neq; lia. }
  have Hr4 : regs1 K4 = Some (Atom wra tra).
  { rewrite Eregs1 setmE (negbTE Hne_4_17). exact: HraL. }
  have Hr19 : regs1 K19 = Some (Atom w19o t19o).
  { rewrite Eregs1 setmE (negbTE Hne_19_17). exact: Ha19. }
  have Hrc1 : regs1 (@word_of_nat (reg_field_size mt)
                       (Intermediate.Register.to_nat R_COM))
              = Some (Atom wrc trc).
  { rewrite Eregs1 setmE (negbTE Hne_1_17). exact: Hrc. }
  have Ea2 : word.addw (@word_of_nat (word_size mt) ((p0 + 1) + pc0)) onew
             = @word_of_nat (word_size mt) ((p0 + 2) + pc0).
  { rewrite addw_onew. congr word_of_nat. by lia. }
  move: Hd1 => /= Hd1.
  apply: (@Symbolic.step_mov _ _ _ _ _ _ _ _ _
            (Symbolic.mem ms) regs1
            (@word_of_nat (word_size mt) ((p0 + 1) + pc0)) PCT
            (vala v1) (taga v1)
            K4 wra tra
            K19 w19o t19o
            (Symbolic.internal ms)).
  + by [].
  + by case: (v1) Hv1.
  + exact: Hd1.
  + exact: Hr4.
  + exact: Hr19.
  + rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc.
    rewrite Ea2 Hv2.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt)
              = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
    rewrite Hrc1 /=.
    rewrite /Merged.transfer /Merged.instr_rules.
    rewrite /PCT Ht1 /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite /check_belong /belong Ht2 /= eqxx /=.
    rewrite /Symbolic.next_state_do_update /updm.
    rewrite Hr4 /=.
    have Hne_19_4 : K19 != K4.
    { rewrite /K19 /K4. by apply: wkey_neq; lia. }
    rewrite setmE (negbTE Hne_19_4) Hr19 /=.
    by congr Some.
-
  rewrite /step_me.
  have H6 := to_nat_le6 rsize.
  have Eregs1 : regs1 = setm (Symbolic.regs ms) K17 (Atom wsz Other).
  { by rewrite /regs1 (setmI Hrsz). }
  have H1415 : Merged.alloc_label < 2 ^ imm_size mt.
  { rewrite /Merged.alloc_label imm_size_mt. by rewrite ltn_exp2l. }
  have Hne_4_19 : K4 != K19.
  { rewrite /K4 /K19. by apply: wkey_neq; lia. }
  have Hr4' : regs2 K4 = Some (Atom wra tra2).
  { by rewrite /regs2 setmE (negbTE Hne_4_19) setmE eqxx. }
  have HrcC : Symbolic.regs ms (word.as_word (ssrint.Posz 1))
              = Some (Atom wrc trc) := Hrc.
  have HA0C : Symbolic.regs ms (word.as_word (ssrint.Posz 0))
              = Some (Atom w0' t0') := HA0.
  have HA2C : Symbolic.regs ms (word.as_word (ssrint.Posz 2))
              = Some (Atom w2' t2') := HA2r.
  have HA3C : Symbolic.regs ms (word.as_word (ssrint.Posz 3))
              = Some (Atom w3' t3') := HA3r.
  have HA5C : Symbolic.regs ms (word.as_word (ssrint.Posz 5))
              = Some (Atom w5' t5') := HA5.
  have HA6C : Symbolic.regs ms (word.as_word (ssrint.Posz 6))
              = Some (Atom w6' t6') := HA6.
  have HA7C : Symbolic.regs ms (word.as_word (ssrint.Posz 7))
              = Some (Atom w7' t7') := Ha7.
  have HA16C : Symbolic.regs ms (word.as_word (ssrint.Posz 16))
              = Some (Atom w16' t16') := Ha16.
  have HA18C : Symbolic.regs ms (word.as_word (ssrint.Posz 18))
              = Some (Atom w18' t18') := Ha18.
  have Hs1 : regs2 (word.as_word (ssrint.Posz 1)) = Some (Atom wrc trc).
  { by rewrite /regs2 Eregs1 !setmE HrcC. }
  have Hs0 : regs2 (word.as_word (ssrint.Posz 0)) = Some (Atom w0' t0').
  { by rewrite /regs2 Eregs1 !setmE HA0C. }
  have Hs2 : regs2 (word.as_word (ssrint.Posz 2)) = Some (Atom w2' t2').
  { by rewrite /regs2 Eregs1 !setmE HA2C. }
  have Hs3 : regs2 (word.as_word (ssrint.Posz 3)) = Some (Atom w3' t3').
  { by rewrite /regs2 Eregs1 !setmE HA3C. }
  have Hs5 : regs2 (word.as_word (ssrint.Posz 5)) = Some (Atom w5' t5').
  { by rewrite /regs2 Eregs1 !setmE HA5C. }
  have Hs6 : regs2 (word.as_word (ssrint.Posz 6)) = Some (Atom w6' t6').
  { by rewrite /regs2 Eregs1 !setmE HA6C. }
  have Hs7 : regs2 (word.as_word (ssrint.Posz 7)) = Some (Atom w7' t7').
  { by rewrite /regs2 Eregs1 !setmE HA7C. }
  have Hs16 : regs2 (word.as_word (ssrint.Posz 16)) = Some (Atom w16' t16').
  { by rewrite /regs2 Eregs1 !setmE HA16C. }
  have Hs17 : regs2 (word.as_word (ssrint.Posz 17)) = Some (Atom wsz Other).
  { by rewrite /regs2 Eregs1 !setmE. }
  have Hs18 : regs2 (word.as_word (ssrint.Posz 18)) = Some (Atom w18' t18').
  { by rewrite /regs2 Eregs1 !setmE HA18C. }
  have Hs19 : regs2 (word.as_word (ssrint.Posz 19)) = Some (Atom wra tra).
  { by rewrite /regs2 !setmE. }
  have Hrc2 : regs2 (@word_of_nat (reg_field_size mt)
                       (Intermediate.Register.to_nat R_COM))
              = Some (Atom wrc trc) := Hs1.
  have Hclear : Symbolic.reg_clear_list regs2 tra2
    = Some [hseq tra2; trc; t0'; t2'; t3'; t5'; t6'; t7';
            t16'; Other; t18'; tra].
  { rewrite /Symbolic.reg_clear_list.
    cbv beta iota zeta delta [Symbolic.reg_clear_list_aux Symbolic.reg_list].
    rewrite Hs1 Hs0 Hs2 Hs3 Hs5 Hs6 Hs7 Hs16 Hs17 Hs18 Hs19.
    by []. }
  move: Hd2 => /= Hd2.
  rewrite code_label_pos_alloc in Hd2.
  have Ecast : @swcast (imm_size mt) (word_size mt)
                 (@word_of_nat (imm_size mt) Merged.alloc_label)
               = @word_of_nat (word_size mt) Merged.alloc_label
    := swcast_word_of_nat_small H1415.
  have Ea3 : word.addw (@word_of_nat (word_size mt) ((p0 + 2) + pc0)) onew
             = @word_of_nat (word_size mt) ((p0 + 3) + pc0).
  { rewrite addw_onew. congr word_of_nat. by lia. }
  case: v3 Hv3 Ht3 Hd3 => v3v v3t Hv3 /= Ht3 Hd3.
  apply: (@Symbolic.step_jal _ _ _ _ _ _ _ _ _
            (Symbolic.mem ms) regs2
            (@word_of_nat (word_size mt) ((p0 + 2) + pc0))
            (vala v2)
            (@word_of_nat (imm_size mt) Merged.alloc_label)
            PCT (taga v2)
            wra tra2
            (Symbolic.internal ms)
            [hseq tra2; trc; t0'; t2'; t3'; t5'; t6'; t7';
             t16'; Other; t18'; tra]
            v3v v3t).
  + by [].
  + by case: (v2) Hv2.
  + rewrite Ea3. exact: Hv3.
  + exact: Hd2.
  + exact: Hr4'.
  + exact: Hclear.
  + rewrite /Symbolic.next_state_updates_and_pc.
    rewrite Ecast Hgap.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt)
              = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
    rewrite Hrc2 /=.
    rewrite /Merged.transfer /Merged.instr_rules.
    rewrite /PCT Ht2 /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite Ht3 /=.
    rewrite /check_belong /belong /tg /= eqxx /=.
    rewrite /Symbolic.next_state_do_update /updm.
    rewrite Ea3.
    have Hv3g : Symbolic.mem ms
                  (@word_of_nat (word_size mt) ((p0 + 3) + pc0))
                = Some (Atom v3v tg).
    { by rewrite Hv3 Ht3. }
    rewrite Hv3g /= (setmI Hv3g).
    rewrite Hr4' /=.
    have Hj1 : (setm regs2 (ra : reg mt)
                  (Atom (@word_of_nat (word_size mt) ((p0 + 3) + pc0))
                     InternalJump))
                 (word.as_word (ssrint.Posz 1)) = Some (Atom wrc trc).
    { by rewrite setmE Hs1. }
    have Hj0 : (setm regs2 (ra : reg mt)
                  (Atom (@word_of_nat (word_size mt) ((p0 + 3) + pc0))
                     InternalJump))
                 (word.as_word (ssrint.Posz 0)) = Some (Atom w0' t0').
    { by rewrite setmE Hs0. }
    have Hj2 : (setm regs2 (ra : reg mt)
                  (Atom (@word_of_nat (word_size mt) ((p0 + 3) + pc0))
                     InternalJump))
                 (word.as_word (ssrint.Posz 2)) = Some (Atom w2' t2').
    { by rewrite setmE Hs2. }
    have Hj3 : (setm regs2 (ra : reg mt)
                  (Atom (@word_of_nat (word_size mt) ((p0 + 3) + pc0))
                     InternalJump))
                 (word.as_word (ssrint.Posz 3)) = Some (Atom w3' t3').
    { by rewrite setmE Hs3. }
    have Hj5 : (setm regs2 (ra : reg mt)
                  (Atom (@word_of_nat (word_size mt) ((p0 + 3) + pc0))
                     InternalJump))
                 (word.as_word (ssrint.Posz 5)) = Some (Atom w5' t5').
    { by rewrite setmE Hs5. }
    have Hj6 : (setm regs2 (ra : reg mt)
                  (Atom (@word_of_nat (word_size mt) ((p0 + 3) + pc0))
                     InternalJump))
                 (word.as_word (ssrint.Posz 6)) = Some (Atom w6' t6').
    { by rewrite setmE Hs6. }
    have Hj7 : (setm regs2 (ra : reg mt)
                  (Atom (@word_of_nat (word_size mt) ((p0 + 3) + pc0))
                     InternalJump))
                 (word.as_word (ssrint.Posz 7)) = Some (Atom w7' t7').
    { by rewrite setmE Hs7. }
    have Hj16 : (setm regs2 (ra : reg mt)
                  (Atom (@word_of_nat (word_size mt) ((p0 + 3) + pc0))
                     InternalJump))
                 (word.as_word (ssrint.Posz 16)) = Some (Atom w16' t16').
    { by rewrite setmE Hs16. }
    have Hj17 : (setm regs2 (ra : reg mt)
                  (Atom (@word_of_nat (word_size mt) ((p0 + 3) + pc0))
                     InternalJump))
                 (word.as_word (ssrint.Posz 17)) = Some (Atom wsz Other).
    { by rewrite setmE Hs17. }
    have Hj18 : (setm regs2 (ra : reg mt)
                  (Atom (@word_of_nat (word_size mt) ((p0 + 3) + pc0))
                     InternalJump))
                 (word.as_word (ssrint.Posz 18)) = Some (Atom w18' t18').
    { by rewrite setmE Hs18. }
    have Hj19 : (setm regs2 (ra : reg mt)
                  (Atom (@word_of_nat (word_size mt) ((p0 + 3) + pc0))
                     InternalJump))
                 (word.as_word (ssrint.Posz 19)) = Some (Atom wra tra).
    { by rewrite setmE Hs19. }
    rewrite Hj1 /= (setmI Hj1).
    rewrite Hj0 /= (setmI Hj0).
    rewrite Hj2 /= (setmI Hj2).
    rewrite Hj3 /= (setmI Hj3).
    rewrite Hj5 /= (setmI Hj5).
    rewrite Hj6 /= (setmI Hj6).
    rewrite Hj7 /= (setmI Hj7).
    rewrite Hj16 /= (setmI Hj16).
    rewrite Hj17 /= (setmI Hj17).
    rewrite Hj18 /= (setmI Hj18).
    rewrite Hj19 /= (setmI Hj19).
    by congr Some.
-
  rewrite /step_me.
  have H6 := to_nat_le6 rsize.
  have Eregs1 : regs1 = setm (Symbolic.regs ms) K17 (Atom wsz Other).
  { by rewrite /regs1 (setmI Hrsz). }
  have HrcC : Symbolic.regs ms (word.as_word (ssrint.Posz 1))
              = Some (Atom wrc trc) := Hrc.
  have HA16C : Symbolic.regs ms (word.as_word (ssrint.Posz 16))
              = Some (Atom w16' t16') := Ha16.
  have Hs1 : regs2 (word.as_word (ssrint.Posz 1)) = Some (Atom wrc trc).
  { by rewrite /regs2 Eregs1 !setmE HrcC. }
  have Hs16 : regs2 (word.as_word (ssrint.Posz 16)) = Some (Atom w16' t16').
  { by rewrite /regs2 Eregs1 !setmE HA16C. }
  have Hs17 : regs2 (word.as_word (ssrint.Posz 17)) = Some (Atom wsz Other).
  { by rewrite /regs2 Eregs1 !setmE. }
  have Hr1 : regs3 (word.as_word (ssrint.Posz 1)) = Some (Atom wrc trc).
  { by rewrite /regs3 setmE Hs1. }
  have Hr16 : regs3 (word.as_word (ssrint.Posz 16)) = Some (Atom w16' t16').
  { by rewrite /regs3 setmE Hs16. }
  have Hr17 : regs3 (word.as_word (ssrint.Posz 17)) = Some (Atom wsz Other).
  { by rewrite /regs3 setmE Hs17. }
  have Hr4 : regs3 (word.as_word (ssrint.Posz 4))
             = Some (Atom (@word_of_nat (word_size mt) ((p0 + 3) + pc0))
                       InternalJump).
  { by rewrite /regs3 setmE. }
  apply: (@Symbolic.step_syscall _ _ _ _ _ _ _ _ _
            (Symbolic.mem ms) regs3
            (@word_of_nat (word_size mt) Merged.alloc_label)
            (@Symbolic.Syscall mt lrc_tags unit tt (LRC.alloc_fun (NC := NC)))
            PCT (Symbolic.internal ms)).
  + by [].
  + exact: Hgap.
  + by rewrite /Merged.table /= setmE eqxx.
  + rewrite /Symbolic.run_syscall /Symbolic.evi.
    have obE : forall (S T : Type) (f : S -> option T) (y : S),
        obind f (Some y) = f y by [].
    have -> : (rcom : reg mt) = word.as_word (ssrint.Posz 1) by [].
    have -> : Symbolic.regs
                (@Symbolic.State mt lrc_tags unit (Symbolic.mem ms) regs3
                   (@word_of_nat (word_size mt) Merged.alloc_label)@PCT
                   (Symbolic.internal ms))
              = regs3 by [].
    rewrite Hr1 obE.
    cbv beta.
    rewrite /Merged.transfer.
    cbv beta iota.
    have Hspec := (@alloc_fun_spec
        (@Symbolic.State mt lrc_tags unit (Symbolic.mem ms) regs3
           (@word_of_nat (word_size mt) Merged.alloc_label)@PCT
           (Symbolic.internal ms))
        (Pointer.component tpc) (Transitional.level tpct)
        (@word_of_nat (word_size mt) ((p0 + 3) + pc0)) wsz
        (BinInt.Z.to_nat zsz) v3 (Atom w16' t16')).
    have -> : Symbolic.sem
                (@Symbolic.Syscall mt lrc_tags unit tt
                   (LRC.alloc_fun (NC := NC)))
              = LRC.alloc_fun (NC := NC) by [].
    have Hpct4 : taga (Symbolic.pc
                   (@Symbolic.State mt lrc_tags unit (Symbolic.mem ms) regs3
                      (@word_of_nat (word_size mt) Merged.alloc_label)@PCT
                      (Symbolic.internal ms)))
                 = LRC.Level (Transitional.level tpct)
                     (Pointer.component tpc) by [].
    have Hic3 : is_code (taga v3). { by rewrite Ht3. }
    have Hcol3 : color (taga v3) = Pointer.component tpc. { by rewrite Ht3. }
    have Hspec2 := Hspec Hpct4 Hr4 Hv3 Hic3 Hcol3 Hr17 Hint Hr16
                     Hlen0 Hfitlen Hc1 Hfitcap.
    rewrite Hspec2.
    cbv beta.
    by congr Some.
-
  rewrite /step_me.
  have H6 := to_nat_le6 rsize.
  have Eregs1 : regs1 = setm (Symbolic.regs ms) K17 (Atom wsz Other).
  { by rewrite /regs1 (setmI Hrsz). }
  have Hq19 : regs4 K19 = Some (Atom wra tra).
  { by rewrite /regs4 /regs3 /regs2 !setmE. }
  have Hq4 : regs4 K4
             = Some (Atom (@word_of_nat (word_size mt) ((p0 + 3) + pc0))
                       InternalJump).
  { by rewrite /regs4 /regs3 !setmE. }
  have Hqc : regs4 (@word_of_nat (reg_field_size mt)
                      (Intermediate.Register.to_nat R_COM))
             = Some (Atom wrc trc).
  { by rewrite /regs4 /regs3 /regs2 Eregs1 !setmE Hrc. }
  have Hu3 : MEM4 (@word_of_nat (word_size mt) ((p0 + 3) + pc0)) = Some v3.
  { by rewrite /MEM4 unionmE Hv3. }
  have Hu4 : MEM4 (@word_of_nat (word_size mt) ((p0 + 4) + pc0)) = Some v4.
  { by rewrite /MEM4 unionmE Hv4. }
  have Ea5 : word.addw (@word_of_nat (word_size mt) ((p0 + 3) + pc0)) onew
             = @word_of_nat (word_size mt) ((p0 + 4) + pc0).
  { rewrite addw_onew. congr word_of_nat. by lia. }
  have Hne_4_19 : K4 != K19.
  { rewrite /K4 /K19. by apply: wkey_neq; lia. }
  move: Hd3 => /= Hd3.
  apply: (@Symbolic.step_mov _ _ _ _ _ _ _ _ _
            MEM4 regs4
            (@word_of_nat (word_size mt) ((p0 + 3) + pc0)) PCT
            (vala v3) (taga v3)
            K19 wra tra
            K4 (@word_of_nat (word_size mt) ((p0 + 3) + pc0)) InternalJump
            tt).
  + by [].
  + by case: (v3) Hu3.
  + exact: Hd3.
  + exact: Hq19.
  + exact: Hq4.
  + rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc.
    rewrite Ea5 Hu4.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt)
              = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
    rewrite Hqc /=.
    rewrite /Merged.transfer /Merged.instr_rules.
    rewrite /PCT Ht3 /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite /check_belong /belong Ht4 /= eqxx /=.
    rewrite /Symbolic.next_state_do_update /updm.
    rewrite Hq19 /=.
    rewrite setmE (negbTE Hne_4_19) Hq4 /=.
    by congr Some.
-
  rewrite /step_me.
  have H6 := to_nat_le6 rsize.
  have H6p := to_nat_le6 rptr.
  have Eregs1 : regs1 = setm (Symbolic.regs ms) K17 (Atom wsz Other).
  { by rewrite /regs1 (setmI Hrsz). }
  have Hq16 : regs5 K16 = Some (Atom ADDR Other).
  { by rewrite /regs5 /regs4 !setmE. }
  have [aP HqP] : exists a, regs5 Krp = Some a.
  { rewrite /regs5 /regs4 /regs3 /regs2 Eregs1 !setmE.
    do ![case: ifP => _; first by eexists].
    by exists rap; exact: Hrp. }
  case: aP HqP => wp tp HqP.
  have Hqc5 : regs5 (@word_of_nat (reg_field_size mt)
                       (Intermediate.Register.to_nat R_COM))
              = Some (Atom wrc trc).
  { by rewrite /regs5 /regs4 /regs3 /regs2 Eregs1 !setmE Hrc. }
  have Hu4 : MEM4 (@word_of_nat (word_size mt) ((p0 + 4) + pc0)) = Some v4.
  { by rewrite /MEM4 unionmE Hv4. }
  have Hu5 : MEM4 (@word_of_nat (word_size mt) ((p0 + 5) + pc0)) = Some v5.
  { by rewrite /MEM4 unionmE Hv5. }
  have Ea6 : word.addw (@word_of_nat (word_size mt) ((p0 + 4) + pc0)) onew
             = @word_of_nat (word_size mt) ((p0 + 5) + pc0).
  { rewrite addw_onew. congr word_of_nat. by lia. }
  have Hne_rp_16 : Krp != K16.
  { rewrite /Krp /K16. by apply: wkey_neq; lia. }
  move: Hd4 => /= Hd4.
  apply: (@Symbolic.step_mov _ _ _ _ _ _ _ _ _
            MEM4 regs5
            (@word_of_nat (word_size mt) ((p0 + 4) + pc0)) PCT
            (vala v4) (taga v4)
            K16 ADDR Other
            Krp wp tp
            tt).
  + by [].
  + by case: (v4) Hu4.
  + exact: Hd4.
  + exact: Hq16.
  + exact: HqP.
  + rewrite /Symbolic.next_state_updates /Symbolic.next_state_updates_and_pc.
    rewrite Ea6 Hu5.
    rewrite /Symbolic.next_state /Symbolic.evi.
    have -> : (rcom : reg mt)
              = word_of_nat (Intermediate.Register.to_nat R_COM) by [].
    rewrite Hqc5 /=.
    rewrite /Merged.transfer /Merged.instr_rules.
    rewrite /PCT Ht4 /=.
    rewrite /LRC.instr_rules /= eqxx /=.
    rewrite /check_belong /belong Ht5 /= eqxx /=.
    rewrite /Symbolic.next_state_do_update /updm.
    rewrite Hq16 /=.
    rewrite setmE (negbTE Hne_rp_16) HqP /=.
    by congr Some.
-
  have H6 := to_nat_le6 rsize.
  have H6p := to_nat_le6 rptr.
  have Eregs1 : regs1 = setm (Symbolic.regs ms) K17 (Atom wsz Other).
  { by rewrite /regs1 (setmI Hrsz). }
  have Hlt32 : forall r0 : register, Intermediate.Register.to_nat r0 < 32
    by case.
  have Hfresh : addr_of amap (Pointer.component tpc)
                  (Transitional.Memory.nextblock cm) = None.
  { case E: (addr_of amap (Pointer.component tpc)
               (Transitional.Memory.nextblock cm)) => [a|]; last by [].
    have [cm0 [blk0 [Hcx0 Hbx0]]] := aok_dom (mj_amap Hmem) E.
    move: Hcx0; rewrite Hcm => -[Ecm0]; subst cm0.
    have Hlt := aok_next (mj_amap Hmem) Hcm Hbx0.
    by rewrite ltnn in Hlt. }
  have [Eend Hend] := alloc_end_val Hc1 Hfitlen Hfitcap.
  have Hre := region_end_le Hc1.
  have Hlo := @maxaddr_lo (Symbolic.mem ms) (Pointer.component tpc) Hc1.
  have EA : ADDR = @word_of_nat (word_size mt) NEWBASE.
  { have Hnb : NEWBASE < 2 ^ word_size mt.
    { rewrite /NEWBASE /MAXA. by lia. }
    have Hnw : (\val MAXA : nat) + 1 < 2 ^ word_size mt.
    { rewrite /MAXA. by lia. }
    have El : (\val ADDR : nat) = (\val MAXA : nat) + 1
      := val_addw_small Hnw.
    have Er : (\val (@word_of_nat (word_size mt) NEWBASE) : nat) = NEWBASE
      by rewrite /word_of_nat valw_as_word (modn_small Hnb).
    apply: word_nat_inj.
    have Emid : (\val MAXA : nat) + 1 = NEWBASE by [].
    exact: (eq_trans (eq_trans El Emid) (esym Er)). }
  constructor.
  +
    rewrite /Symbolic.pcv /=. exact: HpcN.
  +
    rewrite /Symbolic.pct /= /PCT.
    by rewrite Pointer.inc_preserves_component.
  +
    have Hregs' := @mregs_rel_upd L P C pra prb PB PI amap
                     (Pointer.component tpc)
                     (Transitional.Memory.nextblock cm) NEWBASE
                     tregs (Symbolic.regs ms) Hfresh Hregs.
    move=> r.
    case: (altP (Intermediate.Register.to_nat r
                 =P Intermediate.Register.to_nat rptr)) => [Etn|Hnetn].
    *
      have Er : r = rptr := to_nat_inj Etn.
      subst r. left.
      have Egss : Transitional.Register.get rptr
                    (Transitional.Register.set rptr
                       (Ptr ptr) Other tregs)
                  = Transitional.MVal Other (Ptr ptr).
      { by rewrite /Transitional.Register.get /Transitional.Register.set
                   setmE !to_natE eqxx. }
      exists (Atom ADDR Other). split.
      { by rewrite /regs6 /Krp setmE eqxx. }
      { rewrite Egss /tvrel /=.
        rewrite -Etp.
        apply: (@VRPtr _ _ _ _ _ NEWBASE).
        - exact: addr_of_upd_same.
        - by [].
        - rewrite EA. congr word_of_nat.
          by rewrite /= addn0. }
      by rewrite Egss.
    *
      have Hrne : r <> rptr.
      { move=> E. by rewrite E eqxx in Hnetn. }
      have Hkne : (@word_of_nat (reg_field_size mt)
                     (Intermediate.Register.to_nat r))
                  != (@word_of_nat (reg_field_size mt)
                        (Intermediate.Register.to_nat rptr))
        := regkey_neq Hrne.
      have Hnat : (Intermediate.Register.to_nat r
                   == Intermediate.Register.to_nat rptr) = false
        := negbTE Hnetn.
      have Egso : Transitional.Register.get r
                    (Transitional.Register.set rptr
                       (Ptr ptr) Other tregs)
                  = Transitional.Register.get r tregs.
      { by rewrite /Transitional.Register.get /Transitional.Register.set
                   setmE !to_natE Hnat. }
      have Hr6 := to_nat_le6 r.
      have Hne16 : (@word_of_nat (reg_field_size mt)
                      (Intermediate.Register.to_nat r))
                   != @word_of_nat (reg_field_size mt) 16.
      { by apply: wkey_neq; lia. }
      have Hne19 : (@word_of_nat (reg_field_size mt)
                      (Intermediate.Register.to_nat r))
                   != @word_of_nat (reg_field_size mt) 19.
      { by apply: wkey_neq; lia. }
      have Hne17 : (@word_of_nat (reg_field_size mt)
                      (Intermediate.Register.to_nat r))
                   != @word_of_nat (reg_field_size mt) 17.
      { by apply: wkey_neq; lia. }
      have Hkey : regs6 (@word_of_nat (reg_field_size mt)
                           (Intermediate.Register.to_nat r))
                  = Symbolic.regs ms
                      (@word_of_nat (reg_field_size mt)
                         (Intermediate.Register.to_nat r)).
      { rewrite /regs6 /regs5 /regs4 /regs3 /regs2 Eregs1
                /Krp /K16 /K19 /K17 /K4 !setmE.
        rewrite (negbTE Hkne) (negbTE Hne16) (negbTE Hne19) (negbTE Hne17).
        case E4: (@word_of_nat (reg_field_size mt)
                    (Intermediate.Register.to_nat r)
                  == @word_of_nat (reg_field_size mt) 4).
        - by rewrite (eqP E4) HraL.
        - by []. }
      case: (Hregs' r) => [[ra' [Hra' Hv' Ht']]|[ra' [Hra' Hu' Ht']]].
      { left. exists ra'. split.
        - by rewrite Hkey.
        - rewrite Egso. exact: Hv'.
        - rewrite Egso. exact: Ht'. }
      right. exists ra'. split.
      { by rewrite Hkey. }
      { rewrite Egso. exact: Hu'. }
      exact: Ht'.
  +
    have EB : BLOC = mkfmap
        [seq (@word_of_nat (word_size mt) (NEWBASE + o),
              Atom (word.as_word 0 : mword mt)
                (def_mem_tag (Pointer.component tpc) false))
        | o <- iota 0 LEN].
    { by rewrite /BLOC (alloc_block_rekey Hc1 Hfitlen Hfitcap). }
    have Hal' : Transitional.Memory.alloc tmem (Pointer.component tpc) LEN
                = Some (tmem', ptr).
    { by rewrite /Transitional.Memory.alloc Hcm /= Etm Etp. }
    have Hbnd' : NEWBASE + LEN <= 2 ^ word_size mt.
    { rewrite /NEWBASE /MAXA /LEN. by lia. }
    have Hnone : forall o, o < LEN ->
        Symbolic.mem ms (@word_of_nat (word_size mt) (NEWBASE + o)) = None.
    { move=> o Ho.
      have Hsmall2 : NEWBASE + o < 2 ^ word_size mt.
      { rewrite /NEWBASE /MAXA. rewrite /LEN in Ho. by lia. }
      have Hval : (\val (@word_of_nat (word_size mt) (NEWBASE + o)) : nat)
                  = NEWBASE + o.
      { by rewrite valw_as_word modn_small. }
      apply: (above_max_none Hc1).
      - rewrite Hval /NEWBASE /MAXA. by lia.
      - rewrite Hval /NEWBASE /MAXA. rewrite /LEN in Ho. by lia.
      - rewrite Hval /NEWBASE /MAXA. by lia. }
    have Hm' := minj_alloc (newbase := NEWBASE) Hmem Hal' Hlen0 Hbnd' Hnone.
    rewrite -Etp /= in Hm'.
    rewrite /MEM4 EB.
    exact: Hm'.
  +
    move=> w' v' Hv'.
    by rewrite /MEM4 unionmE (Hcode _ _ Hv').
  +
    rewrite /regs6 /regs5 /regs4 /regs3 /regs2 /regs1.
    do !apply: sysregs_ok_setm.
    exact: Hsys.
  +
    have EB : BLOC = mkfmap
        [seq (@word_of_nat (word_size mt) (NEWBASE + o),
              Atom (word.as_word 0 : mword mt)
                (def_mem_tag (Pointer.component tpc) false))
        | o <- iota 0 LEN].
    { by rewrite /BLOC (alloc_block_rekey Hc1 Hfitlen Hfitcap). }
    rewrite /MEM4 unionmE Hgap EB.
    apply: mkfmap_notin_None.
    apply/negP => /mapP [[k a] Hin /= Ek].
    move/mapP: Hin => [o Ho [Ekey _]].
    have Hsmall2 : NEWBASE + o < 2 ^ word_size mt.
    { move: Ho; rewrite mem_iota /NEWBASE /MAXA /LEN => /andP[_ Ho].
      by lia. }
    have Hal32 : Merged.alloc_label < 2 ^ word_size mt.
    { have := HNCal.
      have H2 : 2 ^ (word_size mt - NC) <= 2 ^ word_size mt
        := leq_pexp2l (isT : (0 < 2)%N) (leq_subr NC (word_size mt)).
      by lia. }
    have Ew : (@word_of_nat (word_size mt) Merged.alloc_label)
              = @word_of_nat (word_size mt) (NEWBASE + o)
      := eq_trans Ek Ekey.
    have Heq := won_inj Hal32 Hsmall2 Ew.
    have Hge : 2 ^ (word_size mt - NC)
               <= (1 + Pointer.component tpc) * 2 ^ (word_size mt - NC).
    { by rewrite leq_pmull. }
    move: Heq. rewrite /NEWBASE /MAXA => Heq.
    have := HNCal.
    by lia.
-
  by [].
-
  move=> r Hrne.
  have Eregs1 : regs1 = setm (Symbolic.regs ms) K17 (Atom wsz Other).
  { by rewrite /regs1 (setmI Hrsz). }
  have Hkne : (@word_of_nat (reg_field_size mt)
                 (Intermediate.Register.to_nat r))
              != (@word_of_nat (reg_field_size mt)
                    (Intermediate.Register.to_nat rptr))
    := regkey_neq Hrne.
  have Hr6 := to_nat_le6 r.
  have Hne16 : (@word_of_nat (reg_field_size mt)
                  (Intermediate.Register.to_nat r))
               != @word_of_nat (reg_field_size mt) 16.
  { by apply: wkey_neq; lia. }
  have Hne19 : (@word_of_nat (reg_field_size mt)
                  (Intermediate.Register.to_nat r))
               != @word_of_nat (reg_field_size mt) 19.
  { by apply: wkey_neq; lia. }
  have Hne17 : (@word_of_nat (reg_field_size mt)
                  (Intermediate.Register.to_nat r))
               != @word_of_nat (reg_field_size mt) 17.
  { by apply: wkey_neq; lia. }
  rewrite /Symbolic.regs /regs6 /regs5 /regs4 /regs3 /regs2 Eregs1
          /Krp /K16 /K19 /K17 /K4 !setmE.
  rewrite (negbTE Hkne) (negbTE Hne16) (negbTE Hne19) (negbTE Hne17).
  case E4: (@word_of_nat (reg_field_size mt)
              (Intermediate.Register.to_nat r)
            == @word_of_nat (reg_field_size mt) 4).
  + by rewrite (eqP E4) HraL.
  + by [].
-
  have [Eend Hend] := alloc_end_val Hc1 Hfitlen Hfitcap.
  have Hre := region_end_le Hc1.
  have Hlo := @maxaddr_lo (Symbolic.mem ms) (Pointer.component tpc) Hc1.
  have EA : ADDR = @word_of_nat (word_size mt) NEWBASE.
  { have Hnb : NEWBASE < 2 ^ word_size mt.
    { rewrite /NEWBASE /MAXA. by lia. }
    have Hnw : (\val MAXA : nat) + 1 < 2 ^ word_size mt.
    { rewrite /MAXA. by lia. }
    have El : (\val ADDR : nat) = (\val MAXA : nat) + 1
      := val_addw_small Hnw.
    have Er : (\val (@word_of_nat (word_size mt) NEWBASE) : nat) = NEWBASE
      by rewrite /word_of_nat valw_as_word (modn_small Hnb).
    apply: word_nat_inj.
    have Emid : (\val MAXA : nat) + 1 = NEWBASE by [].
    exact: (eq_trans (eq_trans El Emid) (esym Er)). }
  exists ADDR. split.
  + by rewrite /Symbolic.regs /regs6 /Krp setmE eqxx.
  + rewrite /tvrel /= -Etp.
    apply: (@VRPtr _ _ _ _ _ NEWBASE).
    * exact: addr_of_upd_same.
    * by [].
    * rewrite EA. congr word_of_nat.
      by rewrite /= addn0.
-
  have Hfresh : addr_of amap (Pointer.component tpc)
                  (Transitional.Memory.nextblock cm) = None.
  { case E: (addr_of amap (Pointer.component tpc)
               (Transitional.Memory.nextblock cm)) => [a|]; last by [].
    have [cm0 [blk0 [Hcx0 Hbx0]]] := aok_dom (mj_amap Hmem) E.
    move: Hcx0; rewrite Hcm => -[Ecm0]; subst cm0.
    have Hlt := aok_next (mj_amap Hmem) Hcm Hbx0.
    by rewrite ltnn in Hlt. }
  have [Eend Hend] := alloc_end_val Hc1 Hfitlen Hfitcap.
  have Hre := region_end_le Hc1.
  have Hlo := @maxaddr_lo (Symbolic.mem ms) (Pointer.component tpc) Hc1.
  have Hnone : forall o, o < LEN ->
      Symbolic.mem ms (@word_of_nat (word_size mt) (NEWBASE + o)) = None.
  { move=> o Ho.
    have Hsmall2 : NEWBASE + o < 2 ^ word_size mt.
    { rewrite /NEWBASE /MAXA. rewrite /LEN in Ho. by lia. }
    have Hval : (\val (@word_of_nat (word_size mt) (NEWBASE + o)) : nat)
                = NEWBASE + o.
    { by rewrite valw_as_word modn_small. }
    apply: (above_max_none Hc1).
    - rewrite Hval /NEWBASE /MAXA. by lia.
    - rewrite Hval /NEWBASE /MAXA. rewrite /LEN in Ho. by lia.
    - rewrite Hval /NEWBASE /MAXA. by lia. }
  have EB : BLOC = mkfmap
      [seq (@word_of_nat (word_size mt) (NEWBASE + o),
            Atom (word.as_word 0 : mword mt)
              (def_mem_tag (Pointer.component tpc) false))
      | o <- iota 0 LEN].
  { by rewrite /BLOC (alloc_block_rekey Hc1 Hfitlen Hfitcap). }
  have Hwbnd : NEWBASE + LEN <= 2 ^ word_size mt.
  { rewrite /NEWBASE /MAXA /LEN. by lia. }
  have Hmk : forall (len s k : nat),
      s <= k -> k < s + len -> NEWBASE + (s + len) <= 2 ^ word_size mt ->
      getm (mkfmap [seq (@word_of_nat (word_size mt) (NEWBASE + o0),
                         Atom (word.as_word 0 : mword mt)
                           (def_mem_tag (Pointer.component tpc) false))
                   | o0 <- iota s len])
        (@word_of_nat (word_size mt) (NEWBASE + k))
      = Some (Atom (word.as_word 0)
                (def_mem_tag (Pointer.component tpc) false)).
  { elim=> [|len IH] s k Hsk Hklt Hbnd.
    - exfalso. by lia.
    - rewrite /= setmE won_eqE; [|by lia|by lia].
      case Eks: (NEWBASE + k == NEWBASE + s).
      + by [].
      + apply: IH; by lia. }
  exists NEWBASE. split.
  + by rewrite -Etp.
  + rewrite -Etp /=. exact: Hfresh.
  + move=> o Ho.
    have HLo : o < LEN by exact: Ho.
    rewrite /Symbolic.mem /MEM4 unionmE (Hnone _ HLo) /= EB.
    have := Hmk LEN 0 o (leq0n o) _ _.
    rewrite add0n => HH.
    apply: HH.
    * exact: HLo.
    * exact: Hwbnd.
Qed.

End AllocDiagram.
