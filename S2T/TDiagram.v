(** * Stage 4, part 11 — the diagrams.

    See plan-i2t-redo.md §4 (Stage 4).

    Ports of `S2I/Simulation.v:2041-...`. Each diagram takes an invariant at a
    source state, runs the target to the next matching point, and re-establishes
    the invariant there.

    The first one is `diagram_seq2` (`Simulation.v:2045`): the source drops the
    value of `e1` and moves into `e2`, taking NO target step of its own. All the
    target motion is the junk drain, so this diagram is exactly the composition

        drain (TDrain) → cont_match inversion (reused) → field transport

    and it is the template for the other value-consuming ones. Note the three
    reuse levels visible in it:

    - `cont_match_seq_inv` is used **verbatim** from `Simulation.v` — the
      inversion lemmas mention no memory and no code predicate;
    - the drain is the T version, and it is where the T-specific tax sits;
    - the field transport is per-diagram work, but it is transport, not proof:
      every field is either untouched or comes from the drain. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Intermediate.Machine.
Require Import S2I.CompMonad.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import S2I.SimInject.
Require Import S2I.Simulation.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.
Require Import S2T.TMem.
Require Import S2T.TInv.
Require Import S2T.TStack.
Require Import S2T.TInject.
Require Import S2T.TLabel.
Require Import S2T.TMacros.
Require Import S2T.TStackMatch.
Require Import S2T.TMatch.
Require Import S2T.TDrain.
Require Import S2T.TReplumb.
Require Import S2T.TProlog.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Require Import Coq.ZArith.ZArith.
From mathcomp Require Import zify.
Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.

Module TDiagram.

Notation icode := Intermediate.Machine.code.

Section WithProgram.

Variable cde : Transitional.code.
Variable iface : Program.interface.
Variable labelsP : NMap (NMap label).

Local Notation expr_inv := (TMatch.expr_inv cde iface labelsP).
Local Notation val_inv := (TMatch.val_inv cde iface labelsP).

(** Drain from a [val_inv]: the four premises the drain needs are four of its
    fields. Packaged once, because every value-consuming diagram starts here. *)
Lemma vi_drain a scrs C stk mem k v arg ret rtag Sl tmem tregs pct pc fb prot
      temps plm rest cap :
  val_inv a scrs C stk mem k v arg ret rtag Sl tmem tregs pct pc fb prot temps
          plm rest cap ->
  exists pc' rest',
    [/\ star TS.step cde (tmem, tregs, pc, pct) E0 (tmem, tregs, pc', pct),
        pc' = pc \/ plus TS.step cde (tmem, tregs, pc, pct) E0
                         (tmem, tregs, pc', pct),
        TMacros.code_at_I cde C pc' rest',
        Pointer.component pc' = C
      & cont_match a C plm k rest' temps].
Proof.
  move=> HI.
  (* [labels_uniq] is transparent, so [vi_uniq]'s component argument is
     absorbed as an implicit of the unfolded [forall]; ascribe to pin it *)
  have Hu : TDrain.labels_uniq cde C.
  { move=> l C_code Hg. exact: (TMatch.vi_uniq HI l Hg). }
  exact: (TDrain.cont_matchJ_drain (TMatch.vi_cont HI) (TMatch.vi_code HI)
            (TMatch.vi_pc HI) Hu tmem pct (TMatch.vi_one HI)).
Qed.

(* ================================================================== *)
(* KS_Seq2 — drain, then a stutter                                    *)
(* ================================================================== *)

Lemma diagram_seq2 a scrs C stk mem k v arg ret rtag Sl tmem tregs pct pc fb
      prot temps plm rest cap e2 :
  val_inv a scrs C stk mem (Kseq e2 k) v arg ret rtag Sl tmem tregs pct pc fb
          prot temps plm rest cap ->
  exists pc' c2 rest' sA sB,
    [/\ star TS.step cde (tmem, tregs, pc, pct) E0 (tmem, tregs, pc', pct),
        pc' = pc \/ plus TS.step cde (tmem, tregs, pc, pct) E0
                         (tmem, tregs, pc', pct)
      & expr_inv a scrs C stk mem k e2 arg ret rtag Sl tmem tregs pct pc' fb
                 prot temps plm c2 rest' sA sB cap].
Proof.
  move=> HI.
  case: (vi_drain HI) => [pc' [rest1 [Sd Hor Hc' Ec Hcm']]].
  case: (cont_match_seq_inv Hcm') => [c2 [rest0 [s1 [s2 [E2 Erest Hk]]]]].
  exists pc', c2, rest0, s1, s2.
  split=> //.
  apply: TMatch.ExprInv;
    last by eauto using TMatch.ei_anchor, TMatch.vi_anchor.
  - exact: TMatch.vi_plm HI.
  - exact: TMatch.vi_dom HI.
  - exact: TMatch.vi_mem HI.
  - exact: TMatch.vi_scrs HI.
  - exact: TMatch.vi_one HI.
  - exact: TMatch.vi_sp HI.
  - exact: TMatch.vi_arg HI.
  - exact: TMatch.vi_ra HI.
  - exact: TMatch.vi_rtag HI.
  - exact: Ec.
  - exact: E2.
  - by rewrite -Erest.
  - exact: Hk.
  - exact: TMatch.vi_uniq HI.
  - exact: TMatch.vi_priv HI.
  - exact: TMatch.vi_scrp HI.
  - exact: TMatch.vi_temps HI.
  - exact: TMatch.vi_cap HI.
  - (* [kneed (Kseq e2 k) t] IS [maxn (t + stack_need e2) (kneed k t)] *)
    exact: TMatch.vi_budget HI.
  - exact: TMatch.vi_prot HI.
  - exact: TMatch.vi_stack HI.
  - exact: TMatch.vi_tag HI.
Qed.


Lemma vi_nosite a scrs C stk mem k v arg ret rtag Sl tmem tregs pct pc fb prot
      temps plm rest cap :
  val_inv a scrs C stk mem k v arg ret rtag Sl tmem tregs pct pc fb prot temps
          plm rest cap ->
  forall o : Z,
    ~ List.In (TInv.CMem (C, fb, o))
              (TInv.sites (TMatch.ledger_at rtag Sl)).
Proof.
  move=> HI o Hin.
  have [t Ht] := TInv.in_sites_pair Hin.
  move: Ht; rewrite /TMatch.ledger_at => -[E|Hin']; first by congruence.
  exact: (TSM.stack_match_nosite (TMatch.vi_stack HI) (TMatch.vi_prot HI)
            (TInv.in_sites Hin')).
Qed.

(* ================================================================== *)
(* KS_Binop2 — drain, push the operand, descend into [e2]             *)
(* ================================================================== *)

(** The first diagram that MOVES MEMORY. Everything memory-side comes from
    `TProlog.push_data_run`, which is why that lemma was stated with abstract
    outputs: the diagram never sees a `Register.set` nest or a store rule.

    The three obligations that are genuinely T-specific are all discharged by
    machinery already built:

    - the target cell is not a live capability site — `ei_nosite`, i.e. `prot`;
    - the frame is outside the injection's range — `ei_priv`'s second half;
    - `tag_inv` survives the store — inside `push_data_run`. *)
Lemma diagram_binop2 a scrs C stk mem k v1 arg ret rtag Sl tmem tregs pct pc fb
      prot temps plm rest cap op e2 :
  val_inv a scrs C stk mem (Kbinop1 op e2 k) v1 arg ret rtag Sl tmem tregs pct
          pc fb prot temps plm rest cap ->
  exists pcF tmem' tregs' cd rest' sA sB,
    plus TS.step cde (tmem, tregs, pc, pct) E0 (tmem', tregs', pcF, pct)
    /\ expr_inv a scrs C stk mem (Kbinop2 op v1 k) e2 arg ret rtag Sl tmem'
         tregs' pct pcF fb prot
         (Transitional.val (Transitional.Register.get R_COM tregs) :: temps)
         plm cd rest' sA sB cap.
Proof.
  move=> HI.
  case: (vi_drain HI) => [pcD [rest1 [Sd _ HcD Ec Hcm']]].
  case: (cont_match_binop1_inv Hcm') => [cd [rest0 [sA [sB [E2 Erest Hk]]]]].
  have HcP : TMacros.code_at_I cde C pcD
      (push R_COM ++ cd ++ pop R_AUX1
       ++ IBinOp op R_AUX1 R_COM R_COM :: rest0)
    by rewrite -Erest.
  have Htl : cd ++ pop R_AUX1 ++ IBinOp op R_AUX1 R_COM R_COM :: rest0 <> [::]
    by apply: TDrain.cat_nonempty.
  (* the frame has room for the operand: that is what the budget says *)
  have Hsp : (0 <= Z.of_nat (2 + size temps) < Z.of_nat cap)%Z.
  { split; first by lia.
    have Hb := TMatch.vi_budget HI. move: Hb => /=. lia. }
  have Hns : ~ List.In (TInv.CMem (C, fb, Z.of_nat (2 + size temps)))
               (TInv.sites (TMatch.ledger_at rtag Sl)) by exact: (vi_nosite HI).
  case: (TProlog.push_data_run HcP Htl Ec
           (ltac:(by []) : R_COM <> R_RA)
           (ltac:(by []) : R_SP <> R_COM)
           (ltac:(by []) : R_ONE <> R_COM)
           (TMatch.vi_sp HI) (TMatch.vi_one HI) Hsp (TMatch.vi_cap HI)
           Hns (proj2 (TMatch.vi_priv HI)) (TMatch.vi_mem HI)
           (TMatch.vi_tag HI))
    => [tmem' [tregs' [Pp [Hsl Hpres Hst Hcap' Hmj']]
                      [HSP' HCOM' Hoth'] Htag']].
  exists (Pointer.inc (Pointer.inc pcD)), tmem', tregs', cd,
         (pop R_AUX1 ++ IBinOp op R_AUX1 R_COM R_COM :: rest0), sA, sB.
  (* the pushed cell is above the linkage slots and outside block 1 *)
  have Hb1 : Pointer.block (C, fb, Z.of_nat (2 + size temps)) <> 1
    by rewrite /=; exact: (proj1 (TMatch.vi_priv HI)).
  have Hoff2 : (Pointer.component (C, fb, Z.of_nat (2 + size temps)),
                Pointer.block (C, fb, Z.of_nat (2 + size temps))) = (C, fb) ->
               (2 <= Pointer.offset (C, fb, Z.of_nat (2 + size temps)))%Z
    by move=> _ /=; lia.
  have Hslots : TStack.slots_ok tmem' Sl.
  { apply: (TStack.slots_ok_store _ Hst (TSM.stack_match_slots
              (TMatch.vi_stack HI))).
    move=> s Hin E.
    have Hns2 : ~ List.In (TInv.CMem (C, fb, Z.of_nat (2 + size temps)))
                  (TInv.sites (TStack.ledger_of Sl))
      by exact: (TSM.stack_match_nosite (TMatch.vi_stack HI)
                   (TMatch.vi_prot HI)).
    apply: Hns2. rewrite TStack.sites_ledger_of -E.
    exact: (List.in_map _ _ _ (TStack.in_addrs_of_slot Hin)). }
  split.
  - eapply star_plus_trans; [exact: Sd | exact: Pp | by []].
  - apply: TMatch.ExprInv;
    last by eauto using TMatch.ei_anchor, TMatch.vi_anchor.
    + exact: TMatch.vi_plm HI.
    + exact: TMatch.vi_dom HI.
    + exact: Hmj'.
    + exact: (TSM.scrs_ok_store (TMatch.vi_scrs HI) Hst Hb1).
    + by rewrite Hoth' //; exact: TMatch.vi_one HI.
    + rewrite HSP'. congr MVal. congr Ptr. congr (_, _). rewrite /=. lia.
    + by rewrite Hoth' //; exact: TMatch.vi_arg HI.
    + by rewrite Hoth' //; exact: TMatch.vi_ra HI.
    + exact: TMatch.vi_rtag HI.
    + by rewrite !Pointer.inc_preserves_component.
    + exact: E2.
    + exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail HcP)).
    + apply: CMJ_base. exact: CM_binop2 (TMatch.vi_com HI) Hk.
    + exact: TMatch.vi_uniq HI.
    + exact: TMatch.vi_priv HI.
    + exact: TMatch.vi_scrp HI.
    + (* the new temp is the cell just written; the old ones shift by one *)
      move=> i. case: i => [_|i Hi].
      * have -> : Z.of_nat (1 + size (Transitional.val
                     (Transitional.Register.get R_COM tregs) :: temps) - 0)
                = Z.of_nat (2 + size temps)
          by rewrite [size (_ :: _)]/=; lia.
        (* the tag clause: the pushed cell carries [R_COM]'s tag, which
           [ti_regs] pins to [Other] *)
        have HCt : tvtag (Transitional.Register.get R_COM tregs) = Other.
        { apply: (TInv.ti_regs (TMatch.vi_tag HI)). by []. }
        by rewrite /TMem.vload /TMem.tload Hsl /= HCt.
      * have -> : Z.of_nat (1 + size (Transitional.val
                     (Transitional.Register.get R_COM tregs) :: temps) - i.+1)
                = Z.of_nat (1 + size temps - i)
          by rewrite [size (_ :: _)]/=; lia.
        have Hne : (C, fb, Z.of_nat (1 + size temps - i))
                 <> (C, fb, Z.of_nat (2 + size temps)).
        { move=> E. move: (f_equal Pointer.offset E) => /=. lia. }
        have Hlt : i < size temps by move: Hi; rewrite /=; lia.
        case: (TMatch.vi_temps HI Hlt) => [Hv Ht].
        have [w Hl] := TMem.vload_load Hv.
        rewrite /TMem.vload /TMem.tload (Hpres _ _ Hl Hne). split.
        - by move: Hv; rewrite /TMem.vload Hl.
        - by move: Ht; rewrite /TMem.tload Hl.
    + exact: Hcap'.
    + have Hb := TMatch.vi_budget HI. move: Hb => /=. lia.
    + exact: TMatch.vi_prot HI.
    + exact: (TSM.stack_match_store (TMatch.vi_stack HI) Hst
                (TMatch.vi_prot HI) Hoff2 Hslots).
    + exact: Htag'.
Qed.

(* ================================================================== *)
(* KS_Assign2 — drain, push the value, descend into the ADDRESS       *)
(* ================================================================== *)

(** Structurally `diagram_binop2`: the value being assigned is spilled and the
    ADDRESS expression is evaluated next. Only the glue code and the target
    continuation differ, which is the point — the memory reasoning is entirely
    inside `push_data_run` and does not vary per diagram. *)
Lemma diagram_assign2 a scrs C stk mem k v arg ret rtag Sl tmem tregs pct pc fb
      prot temps plm rest cap e1 :
  val_inv a scrs C stk mem (Kassign1 e1 k) v arg ret rtag Sl tmem tregs pct
          pc fb prot temps plm rest cap ->
  exists pcF tmem' tregs' cd rest' sA sB,
    plus TS.step cde (tmem, tregs, pc, pct) E0 (tmem', tregs', pcF, pct)
    /\ expr_inv a scrs C stk mem (Kassign2 v k) e1 arg ret rtag Sl tmem'
         tregs' pct pcF fb prot
         (Transitional.val (Transitional.Register.get R_COM tregs) :: temps)
         plm cd rest' sA sB cap.
Proof.
  move=> HI.
  case: (vi_drain HI) => [pcD [rest1 [Sd _ HcD Ec Hcm']]].
  case: (cont_match_assign1_inv Hcm') => [cd [rest0 [sA [sB [E2 Erest Hk]]]]].
  have HcP : TMacros.code_at_I cde C pcD
      (push R_COM ++ cd ++ pop R_AUX1
       ++ [:: IStore R_COM R_AUX1; IMov R_AUX1 R_COM] ++ rest0)
    by rewrite -Erest.
  have Htl : cd ++ pop R_AUX1
             ++ [:: IStore R_COM R_AUX1; IMov R_AUX1 R_COM] ++ rest0 <> [::]
    by apply: TDrain.cat_nonempty.
  (* the frame has room for the operand: that is what the budget says *)
  have Hsp : (0 <= Z.of_nat (2 + size temps) < Z.of_nat cap)%Z.
  { split; first by lia.
    have Hb := TMatch.vi_budget HI. move: Hb => /=. lia. }
  have Hns : ~ List.In (TInv.CMem (C, fb, Z.of_nat (2 + size temps)))
               (TInv.sites (TMatch.ledger_at rtag Sl)) by exact: (vi_nosite HI).
  case: (TProlog.push_data_run HcP Htl Ec
           (ltac:(by []) : R_COM <> R_RA)
           (ltac:(by []) : R_SP <> R_COM)
           (ltac:(by []) : R_ONE <> R_COM)
           (TMatch.vi_sp HI) (TMatch.vi_one HI) Hsp (TMatch.vi_cap HI)
           Hns (proj2 (TMatch.vi_priv HI)) (TMatch.vi_mem HI)
           (TMatch.vi_tag HI))
    => [tmem' [tregs' [Pp [Hsl Hpres Hst Hcap' Hmj']]
                      [HSP' HCOM' Hoth'] Htag']].
  exists (Pointer.inc (Pointer.inc pcD)), tmem', tregs', cd,
         (pop R_AUX1 ++ [:: IStore R_COM R_AUX1; IMov R_AUX1 R_COM] ++ rest0),
         sA, sB.
  (* the pushed cell is above the linkage slots and outside block 1 *)
  have Hb1 : Pointer.block (C, fb, Z.of_nat (2 + size temps)) <> 1
    by rewrite /=; exact: (proj1 (TMatch.vi_priv HI)).
  have Hoff2 : (Pointer.component (C, fb, Z.of_nat (2 + size temps)),
                Pointer.block (C, fb, Z.of_nat (2 + size temps))) = (C, fb) ->
               (2 <= Pointer.offset (C, fb, Z.of_nat (2 + size temps)))%Z
    by move=> _ /=; lia.
  have Hslots : TStack.slots_ok tmem' Sl.
  { apply: (TStack.slots_ok_store _ Hst (TSM.stack_match_slots
              (TMatch.vi_stack HI))).
    move=> s Hin E.
    have Hns2 : ~ List.In (TInv.CMem (C, fb, Z.of_nat (2 + size temps)))
                  (TInv.sites (TStack.ledger_of Sl))
      by exact: (TSM.stack_match_nosite (TMatch.vi_stack HI)
                   (TMatch.vi_prot HI)).
    apply: Hns2. rewrite TStack.sites_ledger_of -E.
    exact: (List.in_map _ _ _ (TStack.in_addrs_of_slot Hin)). }
  split.
  - eapply star_plus_trans; [exact: Sd | exact: Pp | by []].
  - apply: TMatch.ExprInv;
    last by eauto using TMatch.ei_anchor, TMatch.vi_anchor.
    + exact: TMatch.vi_plm HI.
    + exact: TMatch.vi_dom HI.
    + exact: Hmj'.
    + exact: (TSM.scrs_ok_store (TMatch.vi_scrs HI) Hst Hb1).
    + by rewrite Hoth' //; exact: TMatch.vi_one HI.
    + rewrite HSP'. congr MVal. congr Ptr. congr (_, _). rewrite /=. lia.
    + by rewrite Hoth' //; exact: TMatch.vi_arg HI.
    + by rewrite Hoth' //; exact: TMatch.vi_ra HI.
    + exact: TMatch.vi_rtag HI.
    + by rewrite !Pointer.inc_preserves_component.
    + exact: E2.
    + exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail HcP)).
    + apply: CMJ_base. exact: CM_assign2 (TMatch.vi_com HI) Hk.
    + exact: TMatch.vi_uniq HI.
    + exact: TMatch.vi_priv HI.
    + exact: TMatch.vi_scrp HI.
    + (* the new temp is the cell just written; the old ones shift by one *)
      move=> i. case: i => [_|i Hi].
      * have -> : Z.of_nat (1 + size (Transitional.val
                     (Transitional.Register.get R_COM tregs) :: temps) - 0)
                = Z.of_nat (2 + size temps)
          by rewrite [size (_ :: _)]/=; lia.
        (* the tag clause: the pushed cell carries [R_COM]'s tag, which
           [ti_regs] pins to [Other] *)
        have HCt : tvtag (Transitional.Register.get R_COM tregs) = Other.
        { apply: (TInv.ti_regs (TMatch.vi_tag HI)). by []. }
        by rewrite /TMem.vload /TMem.tload Hsl /= HCt.
      * have -> : Z.of_nat (1 + size (Transitional.val
                     (Transitional.Register.get R_COM tregs) :: temps) - i.+1)
                = Z.of_nat (1 + size temps - i)
          by rewrite [size (_ :: _)]/=; lia.
        have Hne : (C, fb, Z.of_nat (1 + size temps - i))
                 <> (C, fb, Z.of_nat (2 + size temps)).
        { move=> E. move: (f_equal Pointer.offset E) => /=. lia. }
        have Hlt : i < size temps by move: Hi; rewrite /=; lia.
        case: (TMatch.vi_temps HI Hlt) => [Hv Ht].
        have [w Hl] := TMem.vload_load Hv.
        rewrite /TMem.vload /TMem.tload (Hpres _ _ Hl Hne). split.
        - by move: Hv; rewrite /TMem.vload Hl.
        - by move: Ht; rewrite /TMem.tload Hl.
    + exact: Hcap'.
    + have Hb := TMatch.vi_budget HI. move: Hb => /=. lia.
    + exact: TMatch.vi_prot HI.
    + exact: (TSM.stack_match_store (TMatch.vi_stack HI) Hst
                (TMatch.vi_prot HI) Hoff2 Hslots).
    + exact: Htag'.
Qed.


(* ================================================================== *)
(* KS_BinopEval — drain, pop the operand, apply the operator          *)
(* ================================================================== *)

(** The first diagram that POPS. Everything memory-side is
    `TProlog.pop_data_run`, and the pop's write-back costs nothing here because
    it preserves the cell's tvalue outright (see that lemma).

    What this diagram is really checking is the tag discipline of the operator
    step: `TS.BinOp` demands BOTH operand registers be `Other`-tagged. `R_AUX1`
    is `Other` because it was just loaded from a temp cell, whose tag
    `frame_temps` now pins; `R_COM` is `Other` by `ti_regs`. Remove the
    `frame_temps` tag clause and this step is stuck — that is the concrete
    reason it had to be added. *)
Lemma diagram_binop_eval a scrs C stk mem k v1 v2 arg ret rtag Sl tmem tregs
      pct pc fb prot temps plm rest cap op :
  val_inv a scrs C stk mem (Kbinop2 op v1 k) v2 arg ret rtag Sl tmem tregs pct
          pc fb prot temps plm rest cap ->
  exists tmem' tregs' pcF rest' temps',
    plus TS.step cde (tmem, tregs, pc, pct) E0 (tmem', tregs', pcF, pct)
    /\ val_inv a scrs C stk mem k (eval_binop op v1 v2) arg ret rtag Sl tmem'
         tregs' pct pcF fb prot temps' plm rest' cap.
Proof.
  move=> HI.
  case: (vi_drain HI) => [pcD [rest1 [Sd _ HcD Ec Hcm']]].
  case: (cont_match_binop2_inv Hcm')
    => [tv [temps' [rest0 [Hvtv Etemps Erest Hk]]]].
  (* the cell under R_SP is the top temp: value [tv], tag [Other] *)
  have Eoff : (Z.of_nat (2 + size temps) - 1)%Z
            = Z.of_nat (1 + size temps - 0)
    by rewrite Etemps [size (_ :: _)]/=; lia.
  case: (TMatch.vi_temps HI (ltac:(by rewrite Etemps) : 0 < size temps))
    => [Hv0 Ht0].
  have [w Hw] : exists w,
      Transitional.Memory.load tmem (C, fb, (Z.of_nat (2 + size temps) - 1)%Z)
      = Some w
    by rewrite Eoff; exact: (TMem.vload_load Hv0).
  have Evw : Transitional.val w.1 = tv.
  { move: Hv0; rewrite /TMem.vload -Eoff Hw /= Etemps => -[<-]. by []. }
  have Etw : tvtag w.1 = Other.
  { by move: Ht0; rewrite /TMem.tload -Eoff Hw /= => -[<-]. }
  have HcP : TMacros.code_at_I cde C pcD
      (pop R_AUX1 ++ IBinOp op R_AUX1 R_COM R_COM :: rest0)
    by rewrite -Erest.
  have Hns : ~ List.In
      (TInv.CMem (C, fb, (Z.of_nat (2 + size temps) - 1)%Z))
      (TInv.sites (TMatch.ledger_at rtag Sl)) by exact: (vi_nosite HI).
  have HtlB : IBinOp op R_AUX1 R_COM R_COM :: rest0 <> [::] by [].
  case: (TProlog.pop_data_run HcP HtlB Ec
           (ltac:(by []) : R_AUX1 <> R_RA)
           (ltac:(by []) : R_SP <> R_AUX1)
           (ltac:(by []) : R_ONE <> R_AUX1)
           (TMatch.vi_sp HI) (TMatch.vi_one HI) Hw Etw Hns
           (TMatch.vi_cap HI) (TMatch.vi_mem HI) (TMatch.vi_tag HI))
    => [tmem' [regsA [Pp [Hst Hvl Htl Hcap' Hmj'] [HSPA HA1A HothA] HtagA]]].
  (* the operator step *)
  have HcA : TMacros.code_at_I cde C (Pointer.inc (Pointer.inc pcD))
      (IBinOp op R_AUX1 R_COM R_COM :: rest0)
    by exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail HcP)).
  have [i0 [r0 Er0]] := TDrain.cont_matchJ_cons Hk.
  have HcA2 : TMacros.code_at_I cde C (Pointer.inc (Pointer.inc pcD))
      (IBinOp op R_AUX1 R_COM R_COM :: i0 :: r0) by rewrite -Er0.
  have EcomA : Transitional.Register.get R_COM regsA
             = Transitional.Register.get R_COM tregs by rewrite HothA.
  have Ht1 : tvtag (Transitional.Register.get R_AUX1 regsA) = Other
    by rewrite HA1A.
  have Ht2 : tvtag (Transitional.Register.get R_COM regsA) = Other.
  { apply: (TInv.ti_regs HtagA). by []. }
  exists tmem',
    (Transitional.Register.set R_COM
       (eval_binop op (Transitional.val
                         (Transitional.Register.get R_AUX1 regsA))
                      (Transitional.val
                         (Transitional.Register.get R_COM regsA)))
       Other regsA),
    (Pointer.inc (Pointer.inc (Pointer.inc pcD))), rest0, temps'.
  split.
  - eapply star_plus_trans; [exact: Sd | | by []].
    eapply plus_star_trans; [exact: Pp | | by []].
    apply: star_one.
    eapply TS.BinOp;
      [exact: (TMacros.code_at_I_head HcA2)
      | exact: (TMacros.check_pc_at_I HcA2) | exact: Ht1 | exact: Ht2].
  - apply: TMatch.ValInv;
    last by eauto using TMatch.ei_anchor, TMatch.vi_anchor.
    + exact: TMatch.vi_plm HI.
    + exact: TMatch.vi_dom HI.
    + exact: Hmj'.
    + apply: (TSM.scrs_ok_store_same (TMatch.vi_scrs HI) Hw _ _ Hst);
        by [| rewrite /= Etw].
    + by rewrite TInv.get_set_neq // HothA //; exact: TMatch.vi_one HI.
    + rewrite TInv.get_set_neq // HSPA. congr MVal. congr Ptr. congr (_, _).
      by rewrite Etemps [size (_ :: _)]/=; lia.
    + by rewrite TInv.get_set_neq // HothA //; exact: TMatch.vi_arg HI.
    + rewrite TInv.get_set_eq /= HA1A EcomA /= Evw.
      (* `SimInject.v` has no [Set Implicit Arguments]: all six are explicit *)
      exact: (eval_binop_inject a op _ _ _ _
                (TInject.mj_ok (TMatch.vi_mem HI)) Hvtv
                (TMatch.vi_com HI)).
    + by rewrite TInv.get_set_neq // HothA //; exact: TMatch.vi_ra HI.
    + exact: TMatch.vi_rtag HI.
    + by rewrite !Pointer.inc_preserves_component; exact: Ec.
    + exact: (TMacros.code_at_I_tail HcA).
    + exact: Hk.
    + exact: TMatch.vi_uniq HI.
    + exact: TMatch.vi_priv HI.
    + exact: TMatch.vi_scrp HI.
    + (* the temps shift down by one; the memory is unchanged as [vload]/[tload]
         see it *)
      move=> i Hi.
      have Eoi : Z.of_nat (1 + size temps' - i)
               = Z.of_nat (1 + size temps - i.+1)
        by rewrite Etemps [size (_ :: _)]/=; lia.
      have Eni : nth Undef temps' i = nth Undef temps i.+1
        by rewrite Etemps.
      rewrite Eoi Eni Hvl Htl.
      apply: (TMatch.vi_temps HI).
      by rewrite Etemps [size (_ :: _)]/=; lia.
    + exact: Hcap'.
    + move: (TMatch.vi_budget HI). by rewrite Etemps /=.
    + exact: TMatch.vi_prot HI.
    + (* the popped cell is above the linkage slots, and no slot is in it *)
      apply: (TSM.stack_match_store (TMatch.vi_stack HI) Hst
                (TMatch.vi_prot HI)).
      * (* [/=] would turn [Z.of_nat n.+1] into a [Pos.of_succ_nat] term that
           [zify] does not see through — restrict it to the projection *)
        have Hsz : 0 < size temps by rewrite Etemps.
        move=> _.
        have -> : Pointer.offset (C, fb, (Z.of_nat (2 + size temps) - 1)%Z)
                = (Z.of_nat (2 + size temps) - 1)%Z by [].
        lia.
      * apply: (TStack.slots_ok_store _ Hst
                  (TSM.stack_match_slots (TMatch.vi_stack HI))).
        move=> s Hin E.
        have Hns2 : ~ List.In
            (TInv.CMem (C, fb, (Z.of_nat (2 + size temps) - 1)%Z))
            (TInv.sites (TStack.ledger_of Sl))
          by exact: (TSM.stack_match_nosite (TMatch.vi_stack HI)
                       (TMatch.vi_prot HI)).
        apply: Hns2. rewrite TStack.sites_ledger_of -E.
        exact: (List.in_map _ _ _ (TStack.in_addrs_of_slot Hin)).
    + apply: TInv.tag_inv_setreg; first by [].
      exact: HtagA.
Qed.


(* ================================================================== *)
(* KS_DerefEval — drain, then one [ILoad]                             *)
(* ================================================================== *)

(** One target step, and it is the one that made `minj` grow a tag field.
    `TS.Load` copies the CELL's tag into `R_COM`, which `ti_regs` requires to be
    `Other`; `mj_data` is what says a cell in the injection's range is. And T's
    load, unlike I's, WRITES THE CELL BACK — but at an `Other`-tagged cell the
    write-back reproduces the same tvalue, so every memory clause moves by
    `stack_match_same` / `*_store_same` with no side conditions at all. *)
Lemma diagram_deref_eval a scrs C stk mem k arg ret rtag Sl tmem tregs pct pc fb
      prot temps plm rest cap bp op' v :
  val_inv a scrs C stk mem (Kderef k) (Ptr (C, bp, op')) arg ret rtag Sl tmem
          tregs pct pc fb prot temps plm rest cap ->
  Common.Memory.Memory.load mem (C, bp, op') = Some v ->
  exists tmem' tregs' pcF rest',
    plus TS.step cde (tmem, tregs, pc, pct) E0 (tmem', tregs', pcF, pct)
    /\ val_inv a scrs C stk mem k v arg ret rtag Sl tmem' tregs' pct pcF fb
         prot temps plm rest' cap.
Proof.
  move=> HI Hld.
  case: (vi_drain HI) => [pcD [rest1 [Sd _ HcD Ec Hcm']]].
  case: (cont_match_deref_inv Hcm') => [rest0 [Erest Hk]].
  have HcL : TMacros.code_at_I cde C pcD (ILoad R_COM R_COM :: rest0)
    by rewrite -Erest.
  have [i0 [r0 Er0]] := TDrain.cont_matchJ_cons Hk.
  have HcL2 : TMacros.code_at_I cde C pcD (ILoad R_COM R_COM :: i0 :: r0)
    by rewrite -Er0.
  (* the address, and the cell it points at *)
  case: (val_inject_ptr_l _ _ _ _ _ (TMatch.vi_com HI)) => [b'' [Hab Ecom]].
  case: (TInject.minj_load (TMatch.vi_mem HI) Hab Hld) => [tv [Hvt Hvtv]].
  have [w Hw] := TMem.vload_load Hvt.
  have Etv : Transitional.val w.1 = tv
    by move: Hvt; rewrite /TMem.vload Hw /= => -[<-].
  (* ★ the cell is [Other]-tagged: [mj_data] *)
  have Etw : tvtag w.1 = Other
    by exact: (TInject.mj_data (TMatch.vi_mem HI) Hab Hw).
  case: (TMem.store_after_load
           ({| Transitional.val := Transitional.val w.1; tvtag := Other |},
            {| vtag := Other; color := C; entry := None; is_code := false |})
           Hw) => [tmem' Hst].
  have Hstr : Transitional.Memory.store tmem (C, b'', op')
      ({| Transitional.val := Transitional.val w.1;
          tvtag := moved_tag (tvtag w.1) |},
       {| vtag := moved_tag (tvtag w.1);
          color := Pointer.component pcD; entry := None;
          is_code := false |}) = Some tmem'
    by rewrite Ec Etw /=; exact: Hst.
  (* the write-back reproduces the tvalue, so the memory is invisible-changed *)
  have Hv' : forall q, TMem.vload tmem' q = TMem.vload tmem q.
  { move=> q. apply: (TMem.vload_store_same Hw _ Hst q). by []. }
  have Ht' : forall q, TMem.tload tmem' q = TMem.tload tmem q.
  { move=> q. apply: (TMem.tload_store_same Hw _ Hst q). by rewrite /= Etw. }
  have HCt : tvtag (Transitional.Register.get R_COM tregs) = Other.
  { apply: (TInv.ti_regs (TMatch.vi_tag HI)). by []. }
  exists tmem',
    (Transitional.Register.set R_COM (Transitional.val w.1) (tvtag w.1) tregs),
    (Pointer.inc pcD), rest0.
  split.
  - eapply star_plus_trans; [exact: Sd | | by []].
    apply: plus_one.
    eapply TS.Load.
    + exact: (TMacros.code_at_I_head HcL2).
    + exact: (TMacros.check_pc_at_I HcL2).
    + exact: HCt.
    + exact: Ecom.
    + by rewrite /= Ec.
    + exact: Hw.
    + exact: Hstr.
  - apply: TMatch.ValInv;
    last by eauto using TMatch.ei_anchor, TMatch.vi_anchor.
    + exact: TMatch.vi_plm HI.
    + exact: TMatch.vi_dom HI.
    + apply: (TInject.minj_store_same Hw _ _ Hst (TMatch.vi_mem HI));
        [by [] | by rewrite /= Etw].
    + apply: (TSM.scrs_ok_store_same (TMatch.vi_scrs HI) Hw _ _ Hst);
        by [| rewrite /= Etw].
    + by rewrite TInv.get_set_neq //; exact: TMatch.vi_one HI.
    + by rewrite TInv.get_set_neq //; exact: TMatch.vi_sp HI.
    + by rewrite TInv.get_set_neq //; exact: TMatch.vi_arg HI.
    + by rewrite TInv.get_set_eq /= Etv.
    + by rewrite TInv.get_set_neq //; exact: TMatch.vi_ra HI.
    + exact: TMatch.vi_rtag HI.
    + by rewrite Pointer.inc_preserves_component; exact: Ec.
    + exact: (TMacros.code_at_I_tail HcL).
    + exact: Hk.
    + exact: TMatch.vi_uniq HI.
    + exact: TMatch.vi_priv HI.
    + exact: TMatch.vi_scrp HI.
    + move=> i Hi. rewrite Hv' Ht'. exact: (TMatch.vi_temps HI Hi).
    + exact: (TStack.frame_cap_store Hst (TMatch.vi_cap HI)).
    + exact: TMatch.vi_budget HI.
    + exact: TMatch.vi_prot HI.
    + exact: (TSM.stack_match_same Hv' Ht' (TMatch.vi_stack HI)).
    + (* the heap cell is not a ledger site: sites live in frames, which are
         outside the injection's range — [stack_match_nosite_rng] *)
      have Hns : ~ List.In (TInv.CMem (C, b'', op'))
                   (TInv.sites (TMatch.ledger_at rtag Sl)).
      { move=> Hin. have [t Ht] := TInv.in_sites_pair Hin.
        move: Ht; rewrite /TMatch.ledger_at => -[E|Hin'];
          first by congruence.
        exact: (TSM.stack_match_nosite_rng (TMatch.vi_stack HI) Hab
                  (TInv.in_sites Hin')). }
      rewrite Etw.
      apply: (TInv.tag_inv_load_data _ Etw Hns Hw Hst).
      * by [].
      * exact: TMatch.vi_tag HI.
Qed.


(* ================================================================== *)
(* KS_AssignEval — drain, pop the value, store, restore [R_COM]       *)
(* ================================================================== *)

(** The longest diagram so far, and the only one whose memory changes TWICE:
    the pop's (invisible) write-back, then the assignment's real store.

    Both target cells need a "not a live capability site" premise, and they need
    DIFFERENT lemmas for it: the popped temp is in the current frame
    (`vi_nosite`, via `prot`), the stored cell is in the injection's range
    (`stack_match_nosite_rng`, via `frame_priv`). That the two arguments are
    genuinely different is the reason both exist. *)
Lemma diagram_assign_eval a scrs C stk mem mem' k v arg ret rtag Sl tmem tregs
      pct pc fb prot temps plm rest cap bp op' :
  val_inv a scrs C stk mem (Kassign2 v k) (Ptr (C, bp, op')) arg ret rtag Sl
          tmem tregs pct pc fb prot temps plm rest cap ->
  Common.Memory.Memory.store mem (C, bp, op') v = Some mem' ->
  exists tmem' tregs' pcF rest' temps',
    plus TS.step cde (tmem, tregs, pc, pct) E0 (tmem', tregs', pcF, pct)
    /\ val_inv a scrs C stk mem' k v arg ret rtag Sl tmem' tregs' pct pcF fb
         prot temps' plm rest' cap.
Proof.
  move=> HI Hs.
  case: (vi_drain HI) => [pcD [rest1 [Sd _ HcD Ec Hcm']]].
  case: (cont_match_assign2_inv Hcm')
    => [tv [temps' [rest0 [Hvtv Etemps Erest Hk]]]].
  (* the top temp, and the address *)
  have Eoff : (Z.of_nat (2 + size temps) - 1)%Z
            = Z.of_nat (1 + size temps - 0)
    by rewrite Etemps [size (_ :: _)]/=; lia.
  case: (TMatch.vi_temps HI (ltac:(by rewrite Etemps) : 0 < size temps))
    => [Hv0 Ht0].
  have [w Hw] : exists w,
      Transitional.Memory.load tmem (C, fb, (Z.of_nat (2 + size temps) - 1)%Z)
      = Some w
    by rewrite Eoff; exact: (TMem.vload_load Hv0).
  have Evw : Transitional.val w.1 = tv.
  { move: Hv0; rewrite /TMem.vload -Eoff Hw /= Etemps => -[<-]. by []. }
  have Etw : tvtag w.1 = Other.
  { by move: Ht0; rewrite /TMem.tload -Eoff Hw /= => -[<-]. }
  case: (val_inject_ptr_l _ _ _ _ _ (TMatch.vi_com HI)) => [b'' [Hab Ecom]].
  (* the two blocks the store must avoid *)
  (* [scratch_priv]/[frame_priv] are transparent [forall]s, so their binders are
     absorbed as implicits — give the EQUATION, not the indices *)
  have Hb1 : b'' <> 1.
  { move=> E. have Hx : a C bp = Some 1 by rewrite Hab E.
    exact: (TMatch.vi_scrp HI Hx). }
  have Hbfb : b'' <> fb.
  { move=> E. have Hx : a C bp = Some fb by rewrite Hab E.
    exact: (proj2 (TMatch.vi_priv HI) bp Hx). }
  (* --- the pop --- *)
  have HcP : TMacros.code_at_I cde C pcD
      (pop R_AUX1 ++ [:: IStore R_COM R_AUX1; IMov R_AUX1 R_COM] ++ rest0)
    by rewrite -Erest.
  have HtlP : [:: IStore R_COM R_AUX1; IMov R_AUX1 R_COM] ++ rest0 <> [::]
    by [].
  have Hns : ~ List.In
      (TInv.CMem (C, fb, (Z.of_nat (2 + size temps) - 1)%Z))
      (TInv.sites (TMatch.ledger_at rtag Sl)) by exact: (vi_nosite HI).
  case: (TProlog.pop_data_run HcP HtlP Ec
           (ltac:(by []) : R_AUX1 <> R_RA)
           (ltac:(by []) : R_SP <> R_AUX1)
           (ltac:(by []) : R_ONE <> R_AUX1)
           (TMatch.vi_sp HI) (TMatch.vi_one HI) Hw Etw Hns
           (TMatch.vi_cap HI) (TMatch.vi_mem HI) (TMatch.vi_tag HI))
    => [tmem1 [regsA [Pp [Hst1 Hvl Htl Hcap1 Hmj1] [HSPA HA1A HothA] HtagA]]].
  (* --- the store --- *)
  have HcA : TMacros.code_at_I cde C (Pointer.inc (Pointer.inc pcD))
      ([:: IStore R_COM R_AUX1; IMov R_AUX1 R_COM] ++ rest0)
    by exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail HcP)).
  have EcomA : Transitional.Register.get R_COM regsA
             = Transitional.Register.get R_COM tregs by rewrite HothA.
  case: (TInject.minj_store Hmj1 Hab Hvtv Hs) => [tmem2 [Hst2 Hmj2]].
  (* the rule's [color] is the component of the EXECUTING pc, two cells on *)
  have Hstr : Transitional.Memory.store tmem1 (C, b'', op')
      (Transitional.Register.get R_AUX1 regsA,
       {| vtag := Other;
          color := Pointer.component (Pointer.inc (Pointer.inc pcD));
          entry := None; is_code := false |}) = Some tmem2
    by rewrite HA1A Evw !Pointer.inc_preserves_component Ec; exact: Hst2.
  have SB : TS.step cde (tmem1, regsA, Pointer.inc (Pointer.inc pcD), pct) E0
            (tmem2,
             Transitional.Register.set R_AUX1
               (Transitional.val (Transitional.Register.get R_AUX1 regsA))
               Other regsA,
             Pointer.inc (Pointer.inc (Pointer.inc pcD)), pct).
  { have -> : Other = (moved_tag Other) by [].
    eapply TS.Store.
    - exact: (TMacros.code_at_I_head HcA).
    - exact: (TMacros.check_pc_at_I HcA).
    - by rewrite EcomA; apply: (TInv.ti_regs (TMatch.vi_tag HI)).
    - by rewrite EcomA; exact: Ecom.
    - by rewrite !Pointer.inc_preserves_component Ec.
    - apply: (TInv.ti_tag_other HtagA). by [].
    - exact: Hstr. }
  (* --- the mov that puts the value back in [R_COM] --- *)
  have HcB : TMacros.code_at_I cde C
      (Pointer.inc (Pointer.inc (Pointer.inc pcD)))
      (IMov R_AUX1 R_COM :: rest0)
    by exact: (TMacros.code_at_I_tail HcA).
  have [i0 [r0 Er0]] := TDrain.cont_matchJ_cons Hk.
  have HcB2 : TMacros.code_at_I cde C
      (Pointer.inc (Pointer.inc (Pointer.inc pcD)))
      (IMov R_AUX1 R_COM :: i0 :: r0) by rewrite -Er0.
  set regsB := Transitional.Register.set R_AUX1
                 (Transitional.val (Transitional.Register.get R_AUX1 regsA))
                 Other regsA.
  have HA1B : Transitional.Register.get R_AUX1 regsB
            = MVal Other (Transitional.val (Transitional.Register.get R_AUX1
                                              regsA))
    by rewrite /regsB TInv.get_set_eq.
  have HtagB : TInv.tag_inv (TMatch.ledger_at rtag Sl) tmem2 regsB pct.
  { apply: TInv.tag_inv_setreg; first by [].
    apply: (TInv.tag_inv_store_data _ _ Hst2 HtagA).
    - (* the stored cell is not a live site *)
      move=> Hin. have [t Ht] := TInv.in_sites_pair Hin.
      move: Ht; rewrite /TMatch.ledger_at => -[E|Hin']; first by congruence.
      exact: (TSM.stack_match_nosite_rng (TMatch.vi_stack HI) Hab
                (TInv.in_sites Hin')).
    - by []. }
  exists tmem2,
    (Transitional.Register.set R_AUX1
       (Transitional.val (Transitional.Register.get R_AUX1 regsB)) Other
       (Transitional.Register.set R_COM
          (Transitional.val (Transitional.Register.get R_AUX1 regsB))
          Other regsB)),
    (Pointer.inc (Pointer.inc (Pointer.inc (Pointer.inc pcD)))), rest0, temps'.
  (* the store misses the frame and the scratch block *)
  have Hnefb : forall o : Z, ((C, fb, o) : Pointer.t) <> (C, b'', op')
    by move=> o E; apply: Hbfb; move: (f_equal Pointer.block E) => /= ->.
  split.
  - eapply star_plus_trans; [exact: Sd | | by []].
    eapply plus_star_trans; [exact: Pp | | by []].
    eapply star_trans; [exact: star_one SB | | by []].
    apply: star_one.
    have Ht1 : tvtag (Transitional.Register.get R_AUX1 regsB) = Other
      by rewrite HA1B.
    move: (TS.Mov tmem2 regsB pct (TMacros.code_at_I_head HcB2)
                  (TMacros.check_pc_at_I HcB2)).
    rewrite Ht1. exact: id.
  - apply: TMatch.ValInv;
    last by eauto using TMatch.ei_anchor, TMatch.vi_anchor.
    + exact: TMatch.vi_plm HI.
    + exact: TMatch.vi_dom HI.
    + exact: Hmj2.
    + apply: (TSM.scrs_ok_store _ Hst2); last exact: Hb1.
      apply: (TSM.scrs_ok_store_same (TMatch.vi_scrs HI) Hw _ _ Hst1);
        by [| rewrite /= Etw].
    + rewrite TInv.get_set_neq // TInv.get_set_neq // /regsB TInv.get_set_neq // HothA //.
      exact: TMatch.vi_one HI.
    + rewrite TInv.get_set_neq // TInv.get_set_neq // /regsB TInv.get_set_neq // HSPA.
      congr MVal. congr Ptr. congr (_, _).
      by rewrite Etemps [size (_ :: _)]/=; lia.
    + rewrite TInv.get_set_neq // TInv.get_set_neq // /regsB
              TInv.get_set_neq // HothA //.
      exact: TMatch.vi_arg HI.
    + by rewrite TInv.get_set_neq // TInv.get_set_eq /= HA1B /= HA1A /= Evw.
    + rewrite TInv.get_set_neq // TInv.get_set_neq // /regsB TInv.get_set_neq // HothA //.
      exact: TMatch.vi_ra HI.
    + exact: TMatch.vi_rtag HI.
    + by rewrite !Pointer.inc_preserves_component; exact: Ec.
    + exact: (TMacros.code_at_I_tail HcB).
    + exact: Hk.
    + exact: TMatch.vi_uniq HI.
    + exact: TMatch.vi_priv HI.
    + exact: TMatch.vi_scrp HI.
    + (* the temps shift down, and the store misses the frame *)
      apply: (TStack.frame_temps_store_other _ Hst2); first by move=> i _.
      move=> i Hi. rewrite Hvl Htl.
      have Eoi : Z.of_nat (1 + size temps' - i)
               = Z.of_nat (1 + size temps - i.+1)
        by rewrite Etemps [size (_ :: _)]/=; lia.
      have Eni : nth Undef temps' i = nth Undef temps i.+1 by rewrite Etemps.
      rewrite Eoi Eni. apply: (TMatch.vi_temps HI).
      by rewrite Etemps [size (_ :: _)]/=; lia.
    + exact: (TStack.frame_cap_store Hst2 Hcap1).
    + move: (TMatch.vi_budget HI). by rewrite Etemps /=.
    + exact: TMatch.vi_prot HI.
    + apply: (TSM.stack_match_store _ Hst2
                (TSM.stack_match_rng_notin_prot (TMatch.vi_stack HI) Hab)).
      * exact: (TSM.stack_match_same Hvl Htl (TMatch.vi_stack HI)).
      * move=> E. exfalso. apply: Hbfb.
        by move: (f_equal (fun q => q.2) E) => /= ->.
      * apply: (TStack.slots_ok_store _ Hst2).
        { move=> s Hin E.
          have Hns2 : ~ List.In (TInv.CMem (C, b'', op'))
                        (TInv.sites (TStack.ledger_of Sl))
            by exact: (TSM.stack_match_nosite_rng (TMatch.vi_stack HI) Hab).
          apply: Hns2. rewrite TStack.sites_ledger_of -E.
          exact: (List.in_map _ _ _ (TStack.in_addrs_of_slot Hin)). }
        apply: (TStack.slots_ok_store _ Hst1
                  (TSM.stack_match_slots (TMatch.vi_stack HI))).
        move=> s Hin E.
        have Hns3 : ~ List.In
            (TInv.CMem (C, fb, (Z.of_nat (2 + size temps) - 1)%Z))
            (TInv.sites (TStack.ledger_of Sl))
          by exact: (TSM.stack_match_nosite (TMatch.vi_stack HI)
                       (TMatch.vi_prot HI)).
        apply: Hns3. rewrite TStack.sites_ledger_of -E.
        exact: (List.in_map _ _ _ (TStack.in_addrs_of_slot Hin)).
    + apply: TInv.tag_inv_setreg; first by [].
      apply: TInv.tag_inv_setreg; first by [].
      exact: HtagB.
Qed.


(* ================================================================== *)
(* KS_If2 — drain, then the branch                                    *)
(* ================================================================== *)

(** The only diagram that touches neither memory nor registers, and the only
    one that RESOLVES A LABEL: the taken branch jumps to `lconseq`, which at T
    means a scan of the whole component array (`code_at_I_label_find`, and the
    component-wide uniqueness premise `vi_uniq` behind it). The
    fallthrough branch is one step and lands on the `cont_matchJ` junk that
    `TDrain` was built to remove. *)
Lemma diagram_if2 a scrs C stk mem k arg ret rtag Sl tmem tregs pct pc fb prot
      temps plm rest cap e2 e3 e i :
  val_inv a scrs C stk mem (Kif e2 e3 k) (Int i) arg ret rtag Sl tmem tregs pct
          pc fb prot temps plm rest cap ->
  (* the branch the SOURCE took, as a disjunction rather than an [if]: the
     `!=` of `Source/CS.v`'s `KS_If2` needs a [Z] eqType instance that is not
     in scope here, and the caller has the source step to case on anyway *)
  (i <> 0%Z /\ e = e2) \/ (i = 0%Z /\ e = e3) ->
  exists pcF cd rest' sA sB,
    plus TS.step cde (tmem, tregs, pc, pct) E0 (tmem, tregs, pcF, pct)
    /\ expr_inv a scrs C stk mem k e arg ret rtag Sl tmem tregs pct pcF fb
         prot temps plm cd rest' sA sB cap.
Proof.
  move=> HI Hbr.
  case: (vi_drain HI) => [pcD [rest1 [Sd _ HcD Ec Hcm']]].
  case: (cont_match_if_inv Hcm')
    => [c2 [c3 [lconseq [lend [rest0 [s2a [s2b [s3a [s3b
       [E2 E3 Erest Hk]]]]]]]]]].
  have Ecom := val_inject_int_l _ _ _ (TMatch.vi_com HI).
  have HcB : TMacros.code_at_I cde C pcD
      (IBnz R_COM lconseq :: c3 ++ [:: IBnz R_ONE lend; ILabel lconseq]
       ++ c2 ++ ILabel lend :: rest0) by rewrite -Erest.
  have HCt : tvtag (Transitional.Register.get R_COM tregs) = Other.
  { apply: (TInv.ti_regs (TMatch.vi_tag HI)). by []. }
  (* the [check_pc] of the [Bnz]: the code continues past it *)
  have Hne0 : c3 ++ [:: IBnz R_ONE lend; ILabel lconseq]
              ++ c2 ++ ILabel lend :: rest0 <> [::]
    by apply: TDrain.cat_nonempty.
  have [j0 [t0 Ej]] := TDrain.nonempty_cons Hne0.
  have HcB2 : TMacros.code_at_I cde C pcD (IBnz R_COM lconseq :: j0 :: t0)
    by rewrite -Ej.
  case: Hbr => [[Hi Ee]|[Hi Ee]]; subst e.
  - (* --- then-branch: jump to [lconseq], then its [ILabel] --- *)
    have HcJ : TMacros.code_at_I cde C pcD
        ((IBnz R_COM lconseq :: c3 ++ [:: IBnz R_ONE lend])
         ++ ILabel lconseq :: (c2 ++ ILabel lend :: rest0))
      by move: HcB; do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
    have Hu : forall l0 C_code, getm cde C = Some C_code ->
        count (TLabel.is_tlabel l0) C_code <= 1.
    { move=> l0 C_code Hg. exact: (TMatch.vi_uniq HI l0 Hg). }
    case: (TMacros.code_at_I_label_find HcJ Ec Hu) => [pcL [Hfind EcL HcL]].
    (* the label cell has a successor: the code after it is nonempty *)
    have Hne1 : c2 ++ ILabel lend :: rest0 <> [::]
      by apply: TDrain.cat_nonempty.
    have [j1 [t1 Ej1]] := TDrain.nonempty_cons Hne1.
    have HcL2 : TMacros.code_at_I cde C pcL (ILabel lconseq :: j1 :: t1)
      by rewrite -Ej1.
    exists (Pointer.inc pcL), c2, (ILabel lend :: rest0), s2a, s2b.
    split.
    + eapply star_plus_trans; [exact: Sd | | by []].
      eapply plus_left with (t1 := E0) (t2 := E0); last by [].
      * eapply TS.BnzNZ.
        -- exact: (TMacros.code_at_I_head HcB2).
        -- exact: (TMacros.check_pc_at_I HcB2).
        -- exact: HCt.
        -- exact: Ecom.
        -- exact: Hi.
        -- by rewrite Ec; exact: Hfind.
        -- apply: PcJump; first exact: (TMacros.code_at_I_head HcL2).
           by rewrite EcL Ec.
      * apply: star_one.
        eapply TS.Label; [exact: (TMacros.code_at_I_head HcL2)
                         | exact: (TMacros.check_pc_at_I HcL2)].
    + apply: TMatch.ExprInv;
    last by eauto using TMatch.ei_anchor, TMatch.vi_anchor.
      * exact: TMatch.vi_plm HI.
      * exact: TMatch.vi_dom HI.
      * exact: TMatch.vi_mem HI.
      * exact: TMatch.vi_scrs HI.
      * exact: TMatch.vi_one HI.
      * exact: TMatch.vi_sp HI.
      * exact: TMatch.vi_arg HI.
      * exact: TMatch.vi_ra HI.
      * exact: TMatch.vi_rtag HI.
      * by rewrite Pointer.inc_preserves_component; exact: EcL.
      * exact: E2.
      * by rewrite Ej1; exact: (TMacros.code_at_I_tail HcL2).
      * apply: CMJ_label. exact: Hk.
      * exact: TMatch.vi_uniq HI.
      * exact: TMatch.vi_priv HI.
      * exact: TMatch.vi_scrp HI.
      * exact: TMatch.vi_temps HI.
      * exact: TMatch.vi_cap HI.
      * move: (TMatch.vi_budget HI) => /=. lia.
      * exact: TMatch.vi_prot HI.
      * exact: TMatch.vi_stack HI.
      * exact: TMatch.vi_tag HI.
  - (* --- else-branch: fallthrough --- *)
    exists (Pointer.inc pcD), c3,
           (IBnz R_ONE lend :: ILabel lconseq :: c2 ++ ILabel lend :: rest0),
           s3a, s3b.
    split.
    + eapply star_plus_trans; [exact: Sd | | by []].
      apply: plus_one.
      eapply TS.BnzZ.
      * exact: (TMacros.code_at_I_head HcB2).
      * exact: (TMacros.check_pc_at_I HcB2).
      * exact: HCt.
      * by rewrite Ecom Hi.
    + apply: TMatch.ExprInv;
    last by eauto using TMatch.ei_anchor, TMatch.vi_anchor.
      * exact: TMatch.vi_plm HI.
      * exact: TMatch.vi_dom HI.
      * exact: TMatch.vi_mem HI.
      * exact: TMatch.vi_scrs HI.
      * exact: TMatch.vi_one HI.
      * exact: TMatch.vi_sp HI.
      * exact: TMatch.vi_arg HI.
      * exact: TMatch.vi_ra HI.
      * exact: TMatch.vi_rtag HI.
      * by rewrite Pointer.inc_preserves_component; exact: Ec.
      * exact: E3.
      * by rewrite Ej; exact: (TMacros.code_at_I_tail HcB2).
      * apply: CMJ_bnzjoin. apply: CMJ_label. exact: Hk.
      * exact: TMatch.vi_uniq HI.
      * exact: TMatch.vi_priv HI.
      * exact: TMatch.vi_scrp HI.
      * exact: TMatch.vi_temps HI.
      * exact: TMatch.vi_cap HI.
      * move: (TMatch.vi_budget HI) => /=. lia.
      * exact: TMatch.vi_prot HI.
      * exact: TMatch.vi_stack HI.
      * exact: TMatch.vi_tag HI.
Qed.


(* ================================================================== *)
(* KS_AllocEval — drain, then one [IAlloc]                            *)
(* ================================================================== *)

(** Lock-step allocation: both machines allocate and the renaming EXTENDS onto
    the two fresh blocks. All the memory work is `TSM.minj_alloc_ext`; what is
    left here is the propagation of the extension through the register and
    frame facts, each of which is a two-case split on
    "old pair, or the new one".

    Note the shape of every such case: the new target block is FRESH, so it is
    not the frame (`ei_priv`), not the scratch block (`ei_scrp`), and holds no
    ledger site (`tag_inv_alloc`) — all three for the same reason, that a fresh
    block is unloadable in the old memory while those blocks are not. *)
Lemma diagram_alloc_eval a scrs C stk mem mem' k arg ret rtag Sl tmem tregs pct
      pc fb prot temps plm rest cap size bs :
  val_inv a scrs C stk mem (Kalloc k) (Int size) arg ret rtag Sl tmem tregs pct
          pc fb prot temps plm rest cap ->
  (size > 0)%Z ->
  Common.Memory.Memory.alloc mem C (Z.to_nat size) = Some (mem', (C, bs, 0%Z)) ->
  exists a' tmem' tregs' pcF rest',
    plus TS.step cde (tmem, tregs, pc, pct) E0 (tmem', tregs', pcF, pct)
    /\ val_inv a' scrs C stk mem' k (Ptr (C, bs, 0%Z)) arg ret rtag Sl tmem'
         tregs' pct pcF fb prot temps plm rest' cap.
Proof.
  move=> HI Hpos Hal.
  case: (vi_drain HI) => [pcD [rest1 [Sd _ HcD Ec Hcm']]].
  case: (cont_match_alloc_inv Hcm') => [rest0 [Erest Hk]].
  have HcA : TMacros.code_at_I cde C pcD (IAlloc R_COM R_COM :: rest0)
    by rewrite -Erest.
  have [i0 [r0 Er0]] := TDrain.nonempty_cons (TDrain.cont_matchJ_nonempty Hk).
  have HcA2 : TMacros.code_at_I cde C pcD (IAlloc R_COM R_COM :: i0 :: r0)
    by rewrite -Er0.
  have Ecom := val_inject_int_l _ _ _ (TMatch.vi_com HI).
  have HCt : tvtag (Transitional.Register.get R_COM tregs) = Other.
  { apply: (TInv.ti_regs (TMatch.vi_tag HI)). by []. }
  (* the lock-step allocation *)
  case: (TSM.minj_alloc_ext (TMatch.vi_mem HI) Hal)
    => [tmem' [bt [Halt Hrle Hfresh Hmj']]].
  have Hnew : forall Cx b0 bx, extend a C bs bt Cx b0 = Some bx ->
      a Cx b0 = Some bx \/ (Cx = C /\ bx = bt).
  { move=> Cx b0 bx. rewrite /extend.
    case: ifP => [/andP [/eqP -> _] [<-]|_ H]; [by right | by left]. }
  (* loads outside the fresh block are untouched *)
  have Ltr : forall q w, Transitional.Memory.load tmem q = Some w ->
      Transitional.Memory.load tmem' q = Some w.
  { move=> q w Hl.
    rewrite (TStack.load_alloc_other Halt) //.
    case: (@eqP _ (Pointer.component q) C) => [EC|HC]; last by left.
    case: (@eqP _ (Pointer.block q) bt) => [EB|HB]; last by right.
    by case: (Hfresh (Pointer.offset q) w);
       rewrite -EC -EB -TStack.ptr_expand. }
  have Lv : forall q w, TMem.vload tmem q = Some w ->
      TMem.vload tmem' q = Some w.
  { move=> q w. rewrite /TMem.vload.
    case Hl: (Transitional.Memory.load tmem q) => [w0|] //= E.
    by rewrite (Ltr _ _ Hl). }
  (* the fresh block is neither the frame nor the scratch block *)
  have Hnefb : bt <> fb.
  { move=> E. have [w0 Hw0] : exists w0, TMem.vload tmem (C, fb, 0%Z) = Some w0.
    { apply: (TMatch.vi_cap HI). split; first by [].
      have Hb := TMatch.vi_budget HI. by rewrite -/(_ < _)%Z; lia. }
    have [w1 Hw1] := TMem.vload_load Hw0.
    by case: (Hfresh 0%Z w1); rewrite E. }
  exists (extend a C bs bt), tmem',
    (Transitional.Register.set R_COM (Ptr (C, bt, 0%Z)) Other tregs),
    (Pointer.inc pcD), rest0.
  split.
  - eapply star_plus_trans; [exact: Sd | | by []].
    apply: plus_one.
    eapply TS.Alloc.
    + exact: (TMacros.code_at_I_head HcA2).
    + exact: (TMacros.check_pc_at_I HcA2).
    + exact: HCt.
    + exact: Ecom.
    + exact: Hpos.
    + by rewrite Ec; exact: Halt.
  - apply: TMatch.ValInv;
    last by eauto using TMatch.ei_anchor, TMatch.vi_anchor.
    + exact: TMatch.vi_plm HI.
    + exact: TMatch.vi_dom HI.
    + exact: Hmj'.
    + (* [scrs_ok] is [vload]-shaped, so the transport suffices *)
      case: (TMatch.vi_scrs HI) => [H1 H2 H3 H4]. split.
      * move=> C' v Hv. exact: Lv (H1 _ _ Hv).
      * case: H2 => [H2v H2t]. split; first exact: Lv H2v.
        move: H2t. rewrite /TMem.tload.
        case Hl: (Transitional.Memory.load tmem (Component.main, 1, 1%Z))
          => [w|] //=. by rewrite (Ltr _ _ Hl).
      * move=> C' Hc'. case: (H3 _ Hc') => [w Hw]. exists w. exact: Lv Hw.
      * move=> C' Hc'. move: (H4 _ Hc'). rewrite /TMem.tload.
        case Hl: (Transitional.Memory.load tmem (C', 1, 0%Z)) => [w|] //=.
        by rewrite (Ltr _ _ Hl).
    + by rewrite TInv.get_set_neq //; exact: TMatch.vi_one HI.
    + by rewrite TInv.get_set_neq //; exact: TMatch.vi_sp HI.
    + rewrite TInv.get_set_neq //.
      exact: (val_inject_rle a (extend a C bs bt) _ _ Hrle
                (TMatch.vi_arg HI)).
    + rewrite TInv.get_set_eq /=. apply: VI_ptr. exact: extend_new.
    + by rewrite TInv.get_set_neq //; exact: TMatch.vi_ra HI.
    + exact: TMatch.vi_rtag HI.
    + by rewrite Pointer.inc_preserves_component; exact: Ec.
    + exact: (TMacros.code_at_I_tail HcA).
    + exact: (cont_matchJ_rle _ _ _ _ _ _ _ Hrle Hk).
    + exact: TMatch.vi_uniq HI.
    + (* frame privacy survives the extension *)
      split; first by case: (TMatch.vi_priv HI).
      move=> b0 Hab. case: (Hnew _ _ _ Hab) => [Hold|[_ Ebt]].
      * exact: (proj2 (TMatch.vi_priv HI) b0 Hold).
      * by apply: Hnefb.
    + move=> C' b0 Hab. case: (Hnew _ _ _ Hab) => [Hold|[EC Ebt]].
      * exact: (TMatch.vi_scrp HI Hold).
      * (* the scratch block is loadable, the fresh one is not *)
        subst C' bt. case: (TMatch.vi_scrs HI) => [_ _ H3].
        case: (H3 _ (TMatch.vi_dom HI)) => [w Hw].
        have [w1 Hw1] := TMem.vload_load Hw.
        by case: (Hfresh 0%Z w1).
    + move=> i Hi. case: (TMatch.vi_temps HI Hi) => [Hv Ht].
      have [w0 Hl] := TMem.vload_load Hv. split.
      * exact: Lv Hv.
      * by move: Ht; rewrite /TMem.tload Hl (Ltr _ _ Hl).
    + move=> j Hj. case: (TMatch.vi_cap HI Hj) => [w Hw]. exists w.
      exact: Lv Hw.
    + exact: TMatch.vi_budget HI.
    + exact: TMatch.vi_prot HI.
    + apply: (TSM.stack_match_alloc (TMatch.vi_stack HI) Halt Hrle _ Hfresh).
      * move=> Cx b0 bx Hab. case: (Hnew _ _ _ Hab) => [Hold|[EC Ebt]];
          [by left | by right].
      * (* the chain's slots are all loadable, hence outside the fresh block *)
        move=> s Hin.
        case: (TSM.stack_match_slots (TMatch.vi_stack HI) Hin) => [Hv Ht].
        have [w0 Hl] := TMem.vload_load Hv. split.
        -- exact: Lv Hv.
        -- by move: Ht; rewrite /TMem.tload Hl (Ltr _ _ Hl).
    + apply: TInv.tag_inv_setreg; first by [].
      apply: (TStack.tag_inv_alloc Halt _ (TMatch.vi_tag HI)).
      move=> q t Hin.
      case: (@eqP _ (Pointer.component q) C) => [EC|HC]; last by left.
      case: (@eqP _ (Pointer.block q) bt) => [EB|HB]; last by right.
      move: (TInv.ti_site (TMatch.vi_tag HI) Hin).
      rewrite /TInv.tagat /TMem.tload.
      case Hl: (Transitional.Memory.load tmem q) => [w|] //= _.
      by case: (Hfresh (Pointer.offset q) w);
         rewrite -EC -EB -TStack.ptr_expand.
Qed.


(* ================================================================== *)
(* KS_InternalReturn — the epilogue, and the caller's [pop R_RA]      *)
(* ================================================================== *)

(** The first diagram in which the CAPABILITY MOVES, and the ledger arithmetic
    comes out exactly right:

      before   (CReg, IJ) :: (CMem (C,fb',2+|temps'|), IJ) :: ledger_of Sl1
      IJump    consumes the callee's capability          [tag_inv_drop_reg]
      pop      moves the caller's back into R_RA         [tag_inv_pop_ra]
      after    (CReg, IJ) :: ledger_of Sl1  =  ledger_at InternalJump Sl1

    — the caller's ledger, exactly the shape it had before the call. `pc_tag` is
    untouched throughout, so `ti_lvl` needs no work at all: an intra-component
    return changes no level.

    Everything else is `stack_match` INVERSION: `SM_internal` describes the
    caller's frame (its linkage slots, temps, capacity, continuation) and every
    field of the resulting `val_inv` is read off it. *)
Lemma diagram_return_int a scrs C stk mem k' v oldarg arg ret rtag Sl tmem
      tregs pct pc fb prot temps plm rest cap :
  val_inv a scrs C (S.CS.Frame C oldarg k' :: stk) mem Kstop v arg ret rtag Sl
          tmem tregs pct pc fb prot temps plm rest cap ->
  exists tmem1 tregs1 pcF rest' temps' fb' prot' cap' ret' Sl',
    plus TS.step cde (tmem, tregs, pc, pct) E0 (tmem1, tregs1, pcF, pct)
    /\ val_inv a scrs C stk mem k' v oldarg ret' InternalJump Sl' tmem1 tregs1
         pct pcF fb' prot' temps' plm rest' cap'.
Proof.
  move=> HI.
  case: (vi_drain HI) => [pcD [rest1 [Sd _ HcD Ec Hcm']]].
  case: (cont_match_stop_inv Hcm') => [Erest Etemps].
  have HcE : TMacros.code_at_I cde C pcD (pop R_ARG ++ pop R_SP ++ [:: IJump])
    by rewrite -Erest.
  case: (TSM.stack_match_internal_inv (TMatch.vi_stack HI))
    => [fb' [prot0 [targ [rest' [temps' [plm1 [sl [Sl1 [cap'
       [Hplm1 [Eprot [ESl [Hpcr [Hcoder [Hcontr [L0 [L1 [T0 [T1
       [Hinj [Hpriv' [Htemps' [Ea [Etg [Hslots [Hcap' [Hbud'
       [Hnp [Hnefb Htail]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  have Eplm : plm1 = plm
    by move: Hplm1; rewrite (TMatch.vi_plm HI) => -[->].
  subst plm1.
  (* --- the epilogue: five steps to the caller's [pop R_RA] --- *)
  have HSP2 : Transitional.Register.get R_SP tregs
            = MVal Other (Ptr (C, fb, 2%Z)).
  { move: (TMatch.vi_sp HI). rewrite Etemps.
    have -> : Z.of_nat (2 + size ([::] : seq value)) = 2%Z by [].
    by []. }
  have HRA : Transitional.Register.get R_RA tregs
           = MVal InternalJump (Ptr ret)
    by rewrite (TMatch.vi_ra HI) (TMatch.vi_rtag HI).
  have [w1 Hl1] := TMem.vload_load L1.
  have [w0 Hl0] := TMem.vload_load L0.
  have Et1 : tvtag w1.1 = Other
    by move: T1; rewrite /TMem.tload Hl1 /= => -[<-].
  have Et0 : tvtag w0.1 = Other
    by move: T0; rewrite /TMem.tload Hl0 /= => -[<-].
  have Ev0 : Transitional.val w0.1
           = Ptr (C, fb', Z.of_nat (2 + size temps' + 1))
    by move: L0; rewrite /TMem.vload Hl0 /= => -[<-].
  have Ev1 : Transitional.val w1.1 = targ
    by move: L1; rewrite /TMem.vload Hl1 /= => -[<-].
  have Hns : forall o : Z,
      ~ List.In (TInv.CMem (C, fb, o)) (TInv.sites (TMatch.ledger_at rtag Sl))
    by exact: (vi_nosite HI).
  have Hexr : exists i tni, Transitional.executing cde ret i tni C.
  { exists (Transitional.instr_to_transitional C
              (IBinOp Minus R_SP R_ONE R_SP)).1,
           (Transitional.instr_to_transitional C
              (IBinOp Minus R_SP R_ONE R_SP)).2.
    move: (TMacros.code_at_I_head Hcoder). by rewrite Hpcr. }
  case: (TProlog.epilogue_run HcE Ec HSP2 (TMatch.vi_one HI) HRA Hpcr Hexr
           Hl1 Et1 Hl0 Et0 Hns (TMatch.vi_cap HI) (TMatch.vi_mem HI)
           (TMatch.vi_tag HI))
    => [tmem1 [rs1 [Pe [Hv1 Ht1 Hraw1 Hcap1 Hmj1] [HARG1 HSPe Hothe]
                    Htage]]].
  (* --- the caller's [pop R_RA]: the capability comes back --- *)
  case: (Hslots sl (or_introl erefl)) => [Hvs [Hts Hlives]].
  have [ws Hls] := TMem.vload_load Hvs.
  have Evs : Transitional.val ws.1 = Ptr (TStack.ra_ret sl)
    by move: Hvs; rewrite /TMem.vload Hls /= => -[<-].
  have Ets : tvtag ws.1 = TStack.ra_tag sl
    by move: Hts; rewrite /TMem.tload Hls /= => -[<-].
  have Eaddr : ((C, fb', (Z.of_nat (2 + size temps' + 1) - 1)%Z) : Pointer.t)
             = TStack.ra_addr sl by rewrite Ea; congr (_, _); lia.
  (* the epilogue's write-backs are in the CALLEE's frame, so the caller's RA
     slot keeps its whole cell — mem_tag included *)
  have Hls1 : Transitional.Memory.load tmem1
      (C, fb', (Z.of_nat (2 + size temps' + 1) - 1)%Z) = Some ws.
  { rewrite Hraw1.
    - by rewrite Eaddr.
    - move=> E. apply: Hnefb.
      have Eb : fb' = fb := f_equal Pointer.block E. by rewrite Eb.
    - move=> E. apply: Hnefb.
      have Eb : fb' = fb := f_equal Pointer.block E. by rewrite Eb. }
  have HSP1 : Transitional.Register.get R_SP rs1
            = MVal Other (Ptr (C, fb', Z.of_nat (2 + size temps' + 1)))
    by rewrite HSPe Ev0.
  have HONE1 : Transitional.Register.get R_ONE rs1 = MVal Other (Int 1)
    by rewrite Hothe //; exact: TMatch.vi_one HI.
  have [j0 [r0 Er0]] := TDrain.nonempty_cons
                          (TDrain.cont_matchJ_nonempty Hcontr).
  have Hcoder2 : TMacros.code_at_I cde C ret (pop R_RA ++ j0 :: r0)
    by rewrite -Er0.
  have Htl : j0 :: r0 <> [::] by [].
  (* the ledger: retire the SPENT capability the [IJump] jumped through *)
  have Htagd : TInv.tag_inv
      ((TInv.CMem (C, fb', (Z.of_nat (2 + size temps' + 1) - 1)%Z),
        tvtag ws.1) :: TStack.ledger_of Sl1) tmem1 rs1 pct.
  { move: Htage. rewrite /TMatch.ledger_at ESl (TMatch.vi_rtag HI)
                         /TStack.ledger_of /= -/(TStack.ledger_of Sl1)
                         Eaddr Ets Etg.
    exact: (TInv.tag_inv_drop_reg (t := InternalJump) erefl). }
  have HnotReg : ~ List.In TInv.CReg (TInv.sites (TStack.ledger_of Sl1)).
  { rewrite TStack.sites_ledger_of => /List.in_map_iff [q [Eq _]].
    by move: Eq. }
  have Hcap1' : TStack.frame_cap tmem1 C fb' cap'
    by move=> j Hj; rewrite Hv1; exact: Hcap' Hj.
  case: (TProlog.pop_ra_run Hcoder2 Htl Hpcr HSP1 HONE1 Hls1
           (ltac:(by rewrite Ets) : TInv.is_live (tvtag ws.1))
           HnotReg (proj2 Hpriv') Hcap1' Hmj1 Htagd)
    => [tmem2 [rs2 [Pp [Hst2 Hv2 Ht2 Hcap2 Hmj2] [HSPf HRAf Hothf] Htag2]]].
  (* --- the caller's [val_inv] --- *)
  have Hslots1 : TStack.slots_ok tmem1 Sl1.
  { move=> s0 Hin. case: (Hslots s0 (or_intror Hin)) => [H1 [H2 H3]].
    by rewrite Hv1 Ht1. }
  have Hslots2 : TStack.slots_ok tmem2 Sl1.
  { apply: (TStack.slots_ok_store _ Hst2 Hslots1).
    move=> s0 Hin Eq.
    have Hmem0 := TSM.stack_match_slots_prot Htail Hin.
    move: Hmem0; rewrite Eq /= => Hmem0.
    by move: Hnp; rewrite Hmem0. }
  exists tmem2, rs2, (Pointer.inc (Pointer.inc ret)), rest', temps', fb',
         prot0, cap', (TStack.ra_ret sl), Sl1.
  split.
  - eapply star_plus_trans; [exact: Sd | | by []].
    eapply plus_trans; [exact: Pe | exact: Pp | by []].
  - apply: TMatch.ValInv;
    last by eauto using TMatch.ei_anchor, TMatch.vi_anchor.
    + exact: TMatch.vi_plm HI.
    + exact: TMatch.vi_dom HI.
    + exact: Hmj2.
    + apply: (TSM.scrs_ok_store _ Hst2); last exact: (proj1 Hpriv').
      case: (TMatch.vi_scrs HI) => [H1 H2 H3 H4]. split.
      * move=> C' v' Hv'. by rewrite Hv1; exact: H1 Hv'.
      * case: H2 => [H2v H2t]. split; first by rewrite Hv1.
        by rewrite Ht1.
      * move=> C' Hc'. case: (H3 _ Hc') => [w Hw]. exists w.
        by rewrite Hv1; exact: Hw.
      * move=> C' Hc'. by rewrite Ht1; exact: H4 Hc'.
    + by rewrite Hothf // Hothe //; exact: TMatch.vi_one HI.
    + rewrite HSPf. congr MVal. congr Ptr. congr (_, _). lia.
    + rewrite Hothf // HARG1 /= Ev1. exact: Hinj.
    + rewrite Hothf // Hothe //. exact: TMatch.vi_com HI.
    + by rewrite HRAf Evs Ets Etg.
    + by [].
    + by rewrite !Pointer.inc_preserves_component; exact: Hpcr.
    + rewrite Er0.
      exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hcoder2)).
    + exact: Hcontr.
    + exact: TMatch.vi_uniq HI.
    + exact: Hpriv'.
    + exact: TMatch.vi_scrp HI.
    + (* the temps sit BELOW the RA slot, so the write-back misses them *)
      apply: (TStack.frame_temps_store_other _ Hst2).
      * move=> i Hi E.
        have Eo : Z.of_nat (1 + size temps' - i)
                = (Z.of_nat (2 + size temps' + 1) - 1)%Z
          := f_equal Pointer.offset E.
        move: Eo. lia.
      * move=> i Hi. case: (Htemps' i Hi) => [Hvi Hti].
        by rewrite Hv1 Ht1.
    + exact: Hcap2.
    + exact: Hbud'.
    + exact: Hnp.
    + apply: (TSM.stack_match_store _ Hst2 Hnp _ Hslots2).
      * exact: (TSM.stack_match_same Hv1 Ht1 Htail).
      * move=> _.
        have -> : Pointer.offset
                    ((C, fb', (Z.of_nat (2 + size temps' + 1) - 1)%Z)
                     : Pointer.t)
                = (Z.of_nat (2 + size temps' + 1) - 1)%Z by [].
        lia.
    + by move: Htag2; rewrite /TMatch.ledger_at Ets Etg.
Qed.


(* ================================================================== *)
(* KS_ExternalReturn — the ERet                                       *)
(* ================================================================== *)

(** Body epilogue, wrapper cross-return, caller resumption. The ledger walks
    down in three steps and lands exactly on the caller's:

      start   (CReg,IJ) :: (CMem sE, Ret n) :: (CMem s'', IJ) :: ledger_of Sl1
      IJump   drop the body's spent capability      [tag_inv_drop_reg]
      IReturn consume the wrapper's [Ret n]         [tag_inv_return]
      pop     restore the caller's                  [tag_inv_pop_ra]
      end     (CReg,IJ) :: ledger_of Sl1  =  ledger_at InternalJump Sl1

    and `pc_tag` moves exactly once, at the `IReturn`. *)
Lemma diagram_return_ext a scrs C Cf stk mem k'' i oldarg arg ret rtag Sl tmem
      tregs pct pc fb prot temps plm rest cap :
  val_inv a scrs C (S.CS.Frame Cf oldarg k'' :: stk) mem Kstop (Int i) arg ret
          rtag Sl tmem tregs pct pc fb prot temps plm rest cap ->
  C <> Cf ->
  (forall l0 C_code, getm cde C = Some C_code ->
     count (TLabel.is_tlabel l0) C_code <= 1) ->
  (* the label map only has entries for components of the program *)
  (forall C0 plm0, getm labelsP C0 = Some plm0 -> C0 \in domm iface) ->
  exists scrs1 tmem1 tregs1 pcF rest1 temps1 fb1 prot1 cap1 plm1 ret1 Sl1,
    plus TS.step cde (tmem, tregs, pc, pct) [:: ERet C i Cf]
         (tmem1, tregs1, pcF, dec_pc_tag pct)
    /\ val_inv a scrs1 Cf stk mem k'' (Int i) oldarg ret1 InternalJump Sl1
         tmem1 tregs1 (dec_pc_tag pct) pcF fb1 prot1 temps1 plm1 rest1 cap1.
Proof.
  move=> HI HneCf Huniq Hdomm.
  case: (vi_drain HI) => [pcD [rest1 [Sd _ HcD Ec Hcm']]].
  case: (cont_match_stop_inv Hcm') => [Erest Etemps].
  have HcE : TMacros.code_at_I cde C pcD (pop R_ARG ++ pop R_SP ++ [:: IJump])
    by rewrite -Erest.
  case: (TSM.stack_match_external_inv HneCf (TMatch.vi_stack HI))
    => [fbE [spE [fb'' [prot0 [targ [plm2 [icall_ret [vscr [junkARG [sE
       [s'' [Sl1 [cap'' [temps'' [rest'' Hall]]]]]]]]]]]]]]].
  case: Hall => [G1 [G2 [G3 [G4 [G5 G6]]]]].
  case: G1 => [ESl Eprot Hplm2 Hext EretE].
  case: G2 => [EtagE Etag2 HprivE L0 L1].
  case: G3 => [L2 T0 T1 Eic Hcode2].
  case: G4 => [Hcont2 Hpriv2 Htemps2 Ea2 Hslots].
  case: G5 => [Ltarg Ttarg Hinj Hcap2 Hbud2].
  case: G6 => [Hscr Hnp2 HnpE HneE Htail].
  (* --- the level: the wrapper's capability is the maximum --- *)
  have Hlv : TStack.levels_ok Sl (level pct).
  { move: (TInv.ti_lvl (TMatch.vi_tag HI)).
    by rewrite /TMatch.ledger_at (TMatch.vi_rtag HI) /TStack.levels_ok
               -TStack.ledger_of_rets /= => H; exact: H. }
  have En : level pct = (size (TStack.ext_levels Sl1)).+1
    by apply: (TSM.ext_level_max EtagE Etag2); rewrite -ESl.
  set n := size (TStack.ext_levels Sl1).
  have Epct : pct = Level n.+1 by rewrite {1}(TInv.pc_tagE pct) En.
  have EcompE := TSM.ext_frame_comp Hext.
  have Hdom2 : Cf \in domm iface by exact: (Hdomm Cf plm2 Hplm2).
  (* --- 1. the body's epilogue, to the wrapper's return site --- *)
  have HSP2 : Transitional.Register.get R_SP tregs
            = MVal Other (Ptr (C, fb, 2%Z)).
  { move: (TMatch.vi_sp HI). rewrite Etemps.
    have -> : Z.of_nat (2 + size ([::] : seq value)) = 2%Z by [].
    by []. }
  have HRA : Transitional.Register.get R_RA tregs
           = MVal InternalJump (Ptr ret)
    by rewrite (TMatch.vi_ra HI) (TMatch.vi_rtag HI).
  have [w1 Hl1] := TMem.vload_load L2.
  have [w0 Hl0] := TMem.vload_load L0.
  have Et1 : tvtag w1.1 = Other
    by move: T1; rewrite /TMem.tload Hl1 /= => -[<-].
  have Et0 : tvtag w0.1 = Other
    by move: T0; rewrite /TMem.tload Hl0 /= => -[<-].
  have Ev0 : Transitional.val w0.1 = Ptr (C, fbE, spE)
    by move: L0; rewrite /TMem.vload Hl0 /= => -[<-].
  have Hns : forall o : Z,
      ~ List.In (TInv.CMem (C, fb, o)) (TInv.sites (TMatch.ledger_at rtag Sl))
    by exact: (vi_nosite HI).
  have Hexr : exists i0 tni, Transitional.executing cde ret i0 tni C.
  { (* both flavours start with a [pop], whose first cell is the same; take the
       [executing] from whichever code the relation supplies *)
    case: (TSM.ext_frame_cases Hext)
      => [[u0 [u1 [_ Hcw _ _]]]|[l0 [u0 [u1 [zz [_ Hcw _ _ _]]]]]];
      move: (TMacros.code_at_I_head Hcw); rewrite EcompE => Hx;
      by do 2!eexists; exact: Hx. }
  case: (TProlog.epilogue_run HcE Ec HSP2 (TMatch.vi_one HI) HRA EcompE Hexr
           Hl1 Et1 Hl0 Et0 Hns (TMatch.vi_cap HI) (TMatch.vi_mem HI)
           (TMatch.vi_tag HI))
    => [tmem1 [rs1 [Pe [Hv1 Ht1 Hraw1 Hcap1 Hmj1] [HARG1 HSPe Hothe] Htage]]].
  (* --- 2. the wrapper's cross-return --- *)
  have EaE : TStack.ra_addr sE = (C, fbE, 2%Z)
    by case: (TSM.ext_frame_slot Hext).
  have HslE : TStack.slots_ok tmem1 [:: sE].
  { move=> s0 [Es0|//]. case: (Hslots s0 (or_introl Es0)) => [A [B D]].
    by rewrite Hv1 Ht1. }
  have Hext1 : TSM.ext_frame_match cde tmem1 C fbE ret spE sE.
  { apply: (TSM.ext_frame_match_transport Hext) => //.
    - by move=> o w Hw; rewrite Hv1.
    - by move=> o t Ht; rewrite Ht1. }
  have HSP1 : Transitional.Register.get R_SP rs1
            = MVal Other (Ptr (C, fbE, spE)) by rewrite HSPe Ev0.
  have HONE1 : Transitional.Register.get R_ONE rs1 = MVal Other (Int 1)
    by rewrite Hothe //; exact: TMatch.vi_one HI.
  have HCOM1 : Transitional.val (Transitional.Register.get R_COM rs1) = Int i.
  { rewrite Hothe //.
    by move: (TMatch.vi_com HI) => /val_inject_int_l ->. }
  (* the scratch cell of [C], which the wrapper restores *)
  have [vsc Hvsc] : exists v, TMem.vload tmem1 (C, 1, 0%Z) = Some v.
  { case: (TMatch.vi_scrs HI) => [_ _ H3 _].
    case: (H3 _ (TMatch.vi_dom HI)) => [v Hv]. exists v. by rewrite Hv1. }
  have [mscr Hmscr] := TMem.vload_load Hvsc.
  (* no site of the DEEPER chain is in the wrapper's frame or the scratch *)
  have Hsite2 : forall p0, List.In (TInv.CMem p0)
      (TInv.sites (TStack.ledger_of (s'' :: Sl1))) ->
      (Pointer.component p0, Pointer.block p0) = (Cf, fb'')
      \/ (Pointer.component p0, Pointer.block p0) \in prot0.
  { move=> p0. rewrite TStack.sites_ledger_of /TStack.addrs
      => /List.in_map_iff [q [Eq Hin]].
    move: Hin => /List.in_map_iff [s0 [Es0 Hs0]].
    have Ep : q = p0 by congruence.
    move: Hs0 => [E2|Hin1].
    - left. by rewrite -Ep -Es0 -E2 Ea2.
    - right. move: (TSM.stack_match_slots_prot Htail Hin1).
      by rewrite Es0 Ep. }
  have HnotRegE : ~ List.In TInv.CReg
      (TInv.sites (TStack.ledger_of (s'' :: Sl1))).
  { rewrite TStack.sites_ledger_of => /List.in_map_iff [q [Eq _]].
    by move: Eq. }
  have HnosE : forall o : Z, ~ List.In (TInv.CMem (C, fbE, o))
      (TInv.sites (TStack.ledger_of (s'' :: Sl1))).
  { move=> o Hin. move: HnpE => /negP HnpE'. apply: HnpE'.
    case: (Hsite2 _ Hin) => [E|E].
    - apply/orP; left. by apply/eqP; exact: E.
    - by apply/orP; right; exact: E. }
  (* the scratch cell is [Other]-tagged, and every chain slot is LIVE — so no
     slot can be there. Much cheaper than arguing about [prot]. *)
  have HnosScr : ~ List.In (TInv.CMem (C, 1, 0%Z))
      (TInv.sites (TStack.ledger_of (s'' :: Sl1))).
  { rewrite TStack.sites_ledger_of /TStack.addrs
      => /List.in_map_iff [q [Eq Hin]].
    move: Hin => /List.in_map_iff [s0 [Es0 Hs0]].
    have Ep : TStack.ra_addr s0 = (C, 1, 0%Z) by congruence.
    case: (Hslots s0 (or_intror Hs0)) => [_ [Ht Hlive]].
    move: Ht; rewrite Ep.
    case: (TMatch.vi_scrs HI) => [_ _ _ H4].
    by rewrite (H4 _ (TMatch.vi_dom HI)) => -[E]; move: Hlive; rewrite -E. }
  (* the ledger at the wrapper: the body's spent capability leaves it *)
  have Htagw : TInv.tag_inv
      ((TInv.CMem (C, fbE, 2%Z), Ret n) :: TStack.ledger_of (s'' :: Sl1))
      tmem1 rs1 pct.
  { move: Htage. rewrite /TMatch.ledger_at (TMatch.vi_rtag HI) ESl
                         /TStack.ledger_of /= -/(TStack.ledger_of Sl1)
                         EaE EtagE.
    exact: (TInv.tag_inv_drop_reg (t := InternalJump) erefl). }
  have Hexc : exists i0 tni,
      Transitional.executing cde icall_ret i0 tni (Pointer.component icall_ret).
  { by do 2!eexists; exact: (TMacros.code_at_I_head Hcode2). }
  case: (TProlog.ef_cross_any Hext1 EtagE EretE EcompE Epct HSP1 HONE1 HCOM1
           Hmscr (proj1 HprivE)
           (ltac:(by rewrite Eic; move=> E; apply: HneCf; rewrite E)
            : Pointer.component icall_ret <> C)
           Hexc (proj2 HprivE) HnotRegE HnosE HnosScr
           (ltac:(by move=> b0 Hb0; exact: (TMatch.vi_scrp HI Hb0))
            : forall b0, a C b0 <> Some 1)
           Huniq (ltac:(by move=> j []; lia) :
             TStack.frame_cap tmem1 C fbE 0)
           Hmj1 Htagw)
    => [tmem2 [rs2 [vsc2 [Pw [Hmj2 Hraw2 Hsc2a [Hsc2b [Htsc2 Hcom2]]]
                        Htag2]]]].
  (* --- 3. the caller resumes --- *)
  have [j0 [r0 Er0]] := TDrain.nonempty_cons
                          (TDrain.cont_matchJ_nonempty Hcont2).
  have Hcode2' : TMacros.code_at_I cde Cf icall_ret
      (IConst (IInt 1) R_ONE :: reload_sp (scr Cf) ++ pop R_ARG ++ pop R_RA
         ++ j0 :: r0) by rewrite -Er0.
  (* the caller's own scratch cell, and its two spilled values *)
  have Hscrf : TMem.vload tmem (Cf, 1, 0%Z)
             = Some (Ptr (Cf, fb'', Z.of_nat (2 + size temps'' + 2))).
  { case: (TMatch.vi_scrs HI) => [H1 _ _ _]. exact: H1 Hscr. }
  have Htscrf : TMem.tload tmem (Cf, 1, 0%Z) = Some Other.
  { case: (TMatch.vi_scrs HI) => [_ _ _ H4]. exact: H4 Hdom2. }
  have Hnefb : forall (o o' : Z),
      ((Cf, fb'', o) : Pointer.t) <> (C, 1, o')
    by move=> o o' E; apply: HneCf;
       move: (f_equal Pointer.component E) => /= ->.
  have HnecC : forall (o o' : Z), ((Cf, 1, o) : Pointer.t) <> (C, 1, o')
    by move=> o o' E; apply: HneCf;
       move: (f_equal Pointer.component E) => /= ->.
  (* everything of the caller's survives both the epilogue and the wrapper *)
  have Ltr2 : forall q w, Pointer.component q = Cf ->
      Transitional.Memory.load tmem q = Some w ->
      Transitional.Memory.load tmem2 q = Some w.
  { move=> q w Eq Hl.
    have Hq1 : Pointer.component q <> C \/ Pointer.block q <> fbE
      by left; move=> E; apply: HneCf; rewrite -E Eq.
    have Hq2 : q <> ((C, 1, 0%Z) : Pointer.t)
      by move=> E; apply: HneCf; rewrite -Eq E.
    rewrite (Hraw2 q Hq1 Hq2) Hraw1 //.
    - by move=> E; apply: HneCf; rewrite -Eq E.
    - by move=> E; apply: HneCf; rewrite -Eq E. }
  have [mscrf Hmscrf] := TMem.vload_load Hscrf.
  have [wARG HlARG] := TMem.vload_load Ltarg.
  case: (Hslots s'' (or_intror (or_introl erefl))) => [Hvs2 [Hts2 Hlive2]].
  move: Hvs2 Hts2; rewrite Ea2 => Hvs2 Hts2.
  have [wRA HlRA] := TMem.vload_load Hvs2.
  (* the vload/tload transports for the caller's own component *)
  have Vtr2 : forall q v, Pointer.component q = Cf ->
      TMem.vload tmem q = Some v -> TMem.vload tmem2 q = Some v.
  { move=> q v Eq. rewrite /TMem.vload.
    case El: (Transitional.Memory.load tmem q) => [w|//].
    by rewrite (Ltr2 q w Eq El). }
  (* --- the caller's inputs, all at [tmem2] --- *)
  have Hmscr2 : Transitional.Memory.load tmem2 (Cf, 1, 0%Z) = Some mscrf
    by apply: (@Ltr2 _ _ _ Hmscrf).
  have Etm2 : tvtag mscrf.1 = Other
    by move: Htscrf; rewrite /TMem.tload Hmscrf /= => -[<-].
  have Evm2 : Transitional.val mscrf.1
            = Ptr (Cf, fb'', Z.of_nat (2 + size temps'' + 2))
    by move: Hscrf; rewrite /TMem.vload Hmscrf /= => -[<-].
  have HlA2 : Transitional.Memory.load tmem2
      (Cf, fb'', Z.of_nat (2 + size temps'' + 1)) = Some wARG
    by apply: (@Ltr2 _ _ _ HlARG).
  have EtA2 : tvtag wARG.1 = Other
    by move: Ttarg; rewrite /TMem.tload HlARG /= => -[<-].
  have EvA : Transitional.val wARG.1 = targ
    by move: Ltarg; rewrite /TMem.vload HlARG /= => -[<-].
  have HlR2 : Transitional.Memory.load tmem2
      (Cf, fb'', Z.of_nat (2 + size temps'')) = Some wRA
    by apply: (@Ltr2 _ _ _ HlRA).
  have EtR2 : tvtag wRA.1 = TStack.ra_tag s''
    by move: Hts2; rewrite /TMem.tload HlRA /= => -[<-].
  have EvR : Transitional.val wRA.1 = Ptr (TStack.ra_ret s'')
    by move: Hvs2; rewrite /TMem.vload HlRA /= => -[<-].
  have Hlive2' : TInv.is_live (tvtag wRA.1) by rewrite EtR2.
  have Hcap3 : TStack.frame_cap tmem2 Cf fb'' cap''
    by move=> j Hj; case: (Hcap2 j Hj) => [v Hv]; exists v;
       apply: (@Vtr2 _ _ _ Hv).
  (* the deeper chain's sites, exactly as for the wrapper *)
  have Hslots1 : TStack.slots_ok tmem Sl1
    by move=> s1 Hs1; apply: Hslots; right; right.
  have Hsite1 : forall p0, List.In (TInv.CMem p0)
      (TInv.sites (TStack.ledger_of Sl1)) ->
      (Pointer.component p0, Pointer.block p0) \in prot0.
  { move=> p0. rewrite TStack.sites_ledger_of /TStack.addrs
      => /List.in_map_iff [q [Eq Hin]].
    move: Hin => /List.in_map_iff [s0 [Es0 Hs0]].
    have Ep : q = p0 by congruence.
    move: (TSM.stack_match_slots_prot Htail Hs0). by rewrite Es0 Ep. }
  have HnotReg1 : ~ List.In TInv.CReg (TInv.sites (TStack.ledger_of Sl1)).
  { rewrite TStack.sites_ledger_of => /List.in_map_iff [q [Eq _]].
    by move: Eq. }
  have Hnos1 : forall o : Z, ~ List.In (TInv.CMem (Cf, fb'', o))
      (TInv.sites (TStack.ledger_of Sl1)).
  { move=> o Hin. move: Hnp2 => /negP Hx. apply: Hx. exact: (Hsite1 _ Hin). }
  have HnosScr1 : ~ List.In (TInv.CMem (Cf, 1, 0%Z))
      (TInv.sites (TStack.ledger_of Sl1)).
  { rewrite TStack.sites_ledger_of /TStack.addrs
      => /List.in_map_iff [q [Eq Hin]].
    move: Hin => /List.in_map_iff [s0 [Es0 Hs0]].
    have Ep : TStack.ra_addr s0 = (Cf, 1, 0%Z) by congruence.
    case: (Hslots1 s0 Hs0) => [_ [Ht Hlive]].
    by move: Ht; rewrite Ep Htscrf => -[E]; move: Hlive; rewrite -E. }
  have Htag2' : TInv.tag_inv
      ((TInv.CMem (Cf, fb'', Z.of_nat (2 + size temps'')), tvtag wRA.1)
         :: TStack.ledger_of Sl1) tmem2 rs2 (dec_pc_tag pct).
  { by move: Htag2; rewrite /TStack.ledger_of /= -/(TStack.ledger_of Sl1)
                            Ea2 EtR2. }
  case: (TProlog.icall_resume_run Hcode2' Eic Hmscr2 Etm2 Evm2 HlA2 EtA2
           HlR2 Hlive2' (proj1 Hpriv2) (proj2 Hpriv2)
           (ltac:(by move=> b0 Hb0; exact: (TMatch.vi_scrp HI Hb0))
            : forall b0, a Cf b0 <> Some 1)
           HnotReg1 Hnos1 HnosScr1 Hcap3 Hmj2 Htag2')
    => [tmem3 [rs3 [pcF [Pr3 [Hcap4 Hmj4 EcF HcF
                              [mmid [cc [Hvm Htm Hstm Hvm']]]]
                        [HONE3 HSP3 HARG3 HRA3 Hoth3] Htag3]]]].
  (* --- 4. the caller's invariant --- *)
  (* everything outside the two frames the return touched, and outside the
     scratch cell, is where it was *)
  have Ltr : forall q, (Pointer.component q, Pointer.block q) <> (C, fb) ->
      (Pointer.component q, Pointer.block q) <> (C, fbE) ->
      q <> ((C, 1, 0%Z) : Pointer.t) ->
      Transitional.Memory.load tmem2 q = Transitional.Memory.load tmem q.
  { move=> q Hb1 Hb2 Hb3.
    have E1 : forall o : Z, q <> ((C, fb, o) : Pointer.t)
      by move=> o E; apply: Hb1; rewrite E.
    have E2 : Pointer.component q <> C \/ Pointer.block q <> fbE.
    { case: (@eqP _ (Pointer.component q) C) => [E|H]; last by left.
      by right=> Eb; apply: Hb2; rewrite E Eb. }
    rewrite (Hraw2 q E2 Hb3) Hraw1.
    - by [].
    - exact: E1.
    - exact: E1. }
  (* the RA slot the caller's [pop R_RA] invalidated is the only cell whose
     TAG moved; every value is untouched *)
  have Hstne : forall (C' : Component.id) (o : Z),
      ((C', 1, o) : Pointer.t) <> (Cf, fb'', Z.of_nat (2 + size temps'')).
  { move=> C' o E. apply: (proj1 Hpriv2).
    by move: (f_equal Pointer.block E) => /= ->. }
  have Vtr3 : forall q v,
      (Pointer.component q, Pointer.block q) <> (C, fb) ->
      (Pointer.component q, Pointer.block q) <> (C, fbE) ->
      q <> ((C, 1, 0%Z) : Pointer.t) ->
      TMem.vload tmem q = Some v -> TMem.vload tmem3 q = Some v.
  { move=> q v H1 H2 H3 Hl.
    by rewrite Hvm' Hvm /TMem.vload (Ltr q H1 H2 H3). }
  have Ttr3 : forall q t,
      (Pointer.component q, Pointer.block q) <> (C, fb) ->
      (Pointer.component q, Pointer.block q) <> (C, fbE) ->
      q <> ((C, 1, 0%Z) : Pointer.t) ->
      q <> ((Cf, fb'', Z.of_nat (2 + size temps'')) : Pointer.t) ->
      TMem.tload tmem q = Some t -> TMem.tload tmem3 q = Some t.
  { move=> q t H1 H2 H3 H4 Hl.
    have E : TMem.tload tmem3 q = TMem.tload mmid q
      by rewrite /TMem.tload (TMem.load_store_neq Hstm H4).
    by rewrite E Htm /TMem.tload (Ltr q H1 H2 H3). }
  (* the two frames the diagram burned, as a block predicate *)
  have Hfb1 : fb <> 1 by case: (TMatch.vi_priv HI).
  have HfbE1 : fbE <> 1 by exact: (proj1 HprivE).
  (* --- the scratch map --- *)
  have Evsc : vsc2 = vscr by move: Hsc2a; rewrite Hv1 L1 => -[<-].
  have HscrC : TMem.vload tmem3 (C, 1, 0%Z) = Some vscr
    by rewrite Hvm' Hvm -Evsc.
  have HtscC : TMem.tload tmem3 (C, 1, 0%Z) = Some Other.
  { have E : TMem.tload tmem3 (C, 1, 0%Z) = TMem.tload mmid (C, 1, 0%Z)
      by rewrite /TMem.tload (TMem.load_store_neq Hstm (Hstne C 0%Z)).
    by rewrite E Htm. }
  have Hscrs3 : TSM.scrs_ok tmem3 iface (setm scrs C vscr).
  { case: (TMatch.vi_scrs HI) => [S1 S2 S3 S4]. split.
    - move=> C' v. rewrite setmE.
      case: (@eqP _ C' C) => [->|Hne] => [[<-]|Hg]; first exact: HscrC.
      apply: (@Vtr3 _ _ _ _ _ (S1 _ _ Hg)).
      + by move=> Ex; apply: Hne; move: (f_equal fst Ex) => /= ->.
      + by move=> Ex; apply: Hne; move: (f_equal fst Ex) => /= ->.
      + by move=> E; apply: Hne; move: (f_equal Pointer.component E) => /= ->.
    - case: S2 => [S2v S2t].
      have E1 : (Pointer.component ((Component.main, 1, 1%Z) : Pointer.t),
                 Pointer.block ((Component.main, 1, 1%Z) : Pointer.t))
                <> (C, fb).
      { case: (@eqP _ Component.main C) => [_|Hne].
        - by move=> Ex; apply: Hfb1; move: (f_equal snd Ex) => /= <-.
        - by move=> Ex; apply: Hne; move: (f_equal fst Ex) => /= ->. }
      have E2 : (Pointer.component ((Component.main, 1, 1%Z) : Pointer.t),
                 Pointer.block ((Component.main, 1, 1%Z) : Pointer.t))
                <> (C, fbE).
      { case: (@eqP _ Component.main C) => [_|Hne].
        - by move=> Ex; apply: HfbE1; move: (f_equal snd Ex) => /= <-.
        - by move=> Ex; apply: Hne; move: (f_equal fst Ex) => /= ->. }
      have E3 : ((Component.main, 1, 1%Z) : Pointer.t) <> (C, 1, 0%Z)
        by move=> Ex; move: (f_equal Pointer.offset Ex) => /=; lia.
      split.
      + exact: (@Vtr3 _ _ E1 E2 E3 S2v).
      + exact: (@Ttr3 _ _ E1 E2 E3 (Hstne Component.main 1%Z) S2t).
    - move=> C' Hd. case: (@eqP _ C' C) => [->|Hne]; first by exists vscr.
      case: (S3 _ Hd) => [v Hv]. exists v. apply: (@Vtr3 _ _ _ _ _ Hv).
      + by move=> Ex; apply: Hne; move: (f_equal fst Ex) => /= ->.
      + by move=> Ex; apply: Hne; move: (f_equal fst Ex) => /= ->.
      + by move=> E; apply: Hne; move: (f_equal Pointer.component E) => /= ->.
    - move=> C' Hd. case: (@eqP _ C' C) => [->|Hne]; first exact: HtscC.
      apply: (@Ttr3 _ _ _ _ _ _ (S4 _ Hd)).
      + by move=> Ex; apply: Hne; move: (f_equal fst Ex) => /= ->.
      + by move=> Ex; apply: Hne; move: (f_equal fst Ex) => /= ->.
      + by move=> E; apply: Hne; move: (f_equal Pointer.component E) => /= ->.
      + move=> E. apply: (proj1 Hpriv2).
        by move: (f_equal Pointer.block E) => /= ->. }
  (* --- the caller's frame, and the chain below it --- *)
  have Htemps3 : TStack.frame_temps tmem3 Cf fb'' temps''.
  { move=> ix Hix. case: (Htemps2 ix Hix) => [Hv Ht]. split.
    - apply: (@Vtr3 _ _ _ _ _ Hv).
      + by move=> Ex; apply: HneCf; move: (f_equal fst Ex) => /= ->.
      + by move=> Ex; apply: HneCf; move: (f_equal fst Ex) => /= ->.
      + by move=> Ex; apply: HneCf;
           move: (f_equal Pointer.component Ex) => /= ->.
    - apply: (@Ttr3 _ _ _ _ _ _ Ht).
      + by move=> Ex; apply: HneCf; move: (f_equal fst Ex) => /= ->.
      + by move=> Ex; apply: HneCf; move: (f_equal fst Ex) => /= ->.
      + by move=> Ex; apply: HneCf;
           move: (f_equal Pointer.component Ex) => /= ->.
      + move=> Ex.
        have Eo : Z.of_nat (1 + size temps'' - ix)
                = Z.of_nat (2 + size temps'') := f_equal Pointer.offset Ex.
        move: Eo Hix. lia. }
  pose bad := fun p : Component.id * Block.id =>
    [|| p == (C, fb), p == (C, fbE) | p == (C, 1)].
  have Lbv : forall q, ~~ bad (Pointer.component q, Pointer.block q) ->
      TMem.vload tmem2 q = TMem.vload tmem q.
  { move=> q. rewrite /bad !negb_or
      => /andP [/eqP H1 /andP [/eqP H2 /eqP H3]].
    rewrite /TMem.vload (Ltr q H1 H2 _) //.
    by move=> E; apply: H3; rewrite E. }
  have Lbt : forall q, ~~ bad (Pointer.component q, Pointer.block q) ->
      TMem.tload tmem2 q = TMem.tload tmem q.
  { move=> q. rewrite /bad !negb_or
      => /andP [/eqP H1 /andP [/eqP H2 /eqP H3]].
    rewrite /TMem.tload (Ltr q H1 H2 _) //.
    by move=> E; apply: H3; rewrite E. }
  have Hne3 : forall b1 : Block.id,
      ((Cf, fb'') : Component.id * Block.id) != (C, b1).
  { move=> b1. apply/eqP => E.
    by apply: HneCf; move: (f_equal fst E) => /= ->. }
  have Hbad0 : ~~ bad (Cf, fb'')
    by rewrite /bad !negb_or (Hne3 fb) (Hne3 fbE) (Hne3 1).
  have Hbadp : forall p, p \in prot0 -> ~~ bad p.
  { move=> p Hp. rewrite /bad !negb_or. apply/andP; split; last apply/andP.
    - apply/eqP => E. apply: (negP (TMatch.vi_prot HI)). rewrite Eprot.
      by apply/orP; right; apply/orP; right; rewrite -E.
    - split.
      + apply/eqP => E. apply: (negP HnpE).
        by apply/orP; right; rewrite -E.
      + apply/eqP => E.
        by apply: (TSM.stack_match_prot_nonscr Htail Hp); rewrite E. }
  have Hsm2 : TSM.stack_match cde labelsP a tmem2 (setm scrs C vscr) Cf fb''
                prot0 stk (TStack.ra_ret s'') Sl1
    := TSM.stack_match_raw Lbv Lbt Hbad0 Hbadp Htail.
  have Hsmm := TSM.stack_match_same Hvm Htm Hsm2.
  have Hslots3 : TStack.slots_ok tmem3 Sl1.
  { move=> s0 Hs0.
    have Hp := TSM.stack_match_slots_prot Htail Hs0.
    have Hne : TStack.ra_addr s0
             <> ((Cf, fb'', Z.of_nat (2 + size temps'')) : Pointer.t).
    { move=> E. move: Hnp2 => /negP Hx. apply: Hx. by move: Hp; rewrite E. }
    have Et3 : TMem.tload tmem3 (TStack.ra_addr s0)
             = TMem.tload mmid (TStack.ra_addr s0)
      by rewrite /TMem.tload (TMem.load_store_neq Hstm Hne).
    case: (Hslots1 s0 Hs0) => [A [B D]]. split; last split; last exact: D.
    - by rewrite Hvm' Hvm (Lbv _ (Hbadp _ Hp)).
    - by rewrite Et3 Htm (Lbt _ (Hbadp _ Hp)). }
  have Hsm3 : TSM.stack_match cde labelsP a tmem3 (setm scrs C vscr) Cf fb''
                prot0 stk (TStack.ra_ret s'') Sl1.
  { apply: (TSM.stack_match_store Hsmm Hstm Hnp2 _ Hslots3) => _.
    have -> : Pointer.offset
                ((Cf, fb'', Z.of_nat (2 + size temps'')) : Pointer.t)
            = Z.of_nat (2 + size temps'') by [].
    lia. }
  (* --- assembled --- *)
  exists (setm scrs C vscr), tmem3, rs3, pcF, rest'', temps'', fb'', prot0,
         cap'', plm2, (TStack.ra_ret s''), Sl1.
  split.
  - eapply star_plus_trans with (t1 := E0) (t2 := [:: ERet C i Cf]);
      [exact: Sd | | by []].
    eapply plus_trans with (t1 := E0) (t2 := [:: ERet C i Cf]);
      [exact: Pe | | by []].
    eapply plus_trans with (t1 := [:: ERet C i Cf]) (t2 := E0);
      [ | exact: Pr3 | by []].
    by move: Pw; rewrite Eic.
  - apply: TMatch.ValInv;
    last by eauto using TMatch.ei_anchor, TMatch.vi_anchor.
    + exact: Hplm2.
    + exact: Hdom2.
    + exact: Hmj4.
    + exact: Hscrs3.
    + exact: HONE3.
    + exact: HSP3.
    + by rewrite HARG3 /= EvA.
    + rewrite Hoth3 //; try by []. by rewrite Hcom2; exact: VI_int.
    + by rewrite HRA3 EtR2 Etag2 EvR.
    + by [].
    + exact: EcF.
    + by rewrite Er0.
    + exact: Hcont2.
    + exact: (TMatch.vi_uniq HI).
    + exact: Hpriv2.
    + exact: (TMatch.vi_scrp HI).
    + exact: Htemps3.
    + exact: Hcap4.
    + exact: Hbud2.
    + exact: Hnp2.
    + exact: Hsm3.
    + by move: Htag3; rewrite /TMatch.ledger_at EtR2 Etag2.
Qed.


(* ================================================================== *)
(* KS_InternalCall — drain, spill the caller's capability, [IJal] to   *)
(* the callee's entry label, run the callee's prologue                 *)
(* ================================================================== *)

(** The `IJal` is the only step in the campaign that CREATES a capability
    ([TInv.tag_inv_jal]), and the `push R_RA` before it is the only one that
    MOVES a ledger entry from [CReg] into memory ([TProlog.push_ra_run]).
    Together they are the intra-component half of T2: the caller's return
    address goes to its own frame, the callee gets a fresh [InternalJump] in
    [R_RA], and [ti_uniq] never sees two live copies.

    The label resolution is a PREMISE, and it is the T analogue of
    `S2I/SimCode.v:1637`'s `compiled_jal_resolution`: the entry label of a
    source procedure labels that procedure's internal entry, behind which sit
    the prologue, the compiled body and the epilogue. Stage 3 discharges it by
    computation on compiled programs — it is a static fact about the compiler's
    output, not an assumption about the machine. Note what makes it CHEAPER
    than the I version: T flattens a component into one array, so the target is
    an ordinary label and `TLabel`'s component-wide uniqueness (already carried
    as `ei_uniq`) turns "the label is here" into "the machine finds it here" —
    there is no per-procedure block to locate. *)
Lemma diagram_call_int a scrs C stk mem k P v arg ret rtag Sl tmem tregs pct pc
      fb prot temps plm rest cap P_expr :
  val_inv a scrs C stk mem (Kcall C P k) (Int v) arg ret rtag Sl tmem tregs pct
          pc fb prot temps plm rest cap ->
  (forall tl, getm plm P = Some tl ->
     exists pcE sA sB cbody,
       [/\ Pointer.component pcE = C,
           compile_expr C (lbp C) (scr C) plm P_expr sA = Some (cbody, sB)
         & TMacros.code_at_I cde C pcE
             ([:: ILabel tl; IMov R_SP R_AUX1;
                  IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
                  IAlloc R_SP R_SP]
              ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
              ++ cbody ++ pop R_ARG ++ pop R_SP ++ [:: IJump])]) ->
  exists tmem5 tregs5 pcF c1 rest1 sA sB fbN retN Sl1,
    plus TS.step cde (tmem, tregs, pc, pct) E0 (tmem5, tregs5, pcF, pct)
    /\ expr_inv a scrs C (S.CS.Frame C arg k :: stk) mem Kstop P_expr (Int v)
                retN InternalJump Sl1 tmem5 tregs5 pct pcF fbN
                ((C, fb) :: prot) [::] plm c1 rest1 sA sB
                (4 + stack_need P_expr).
Proof.
  move=> HI Hres.
  move: (TMatch.vi_rtag HI) => Ert; subst rtag.
  have Hu : TDrain.labels_uniq cde C
    by move=> l0 C_code Hg; exact: (TMatch.vi_uniq HI l0 Hg).
  case: (vi_drain HI) => [pcD [rest1 [Sd _ HcD Ec Hcm']]].
  case: (cont_match_call_inv Hcm') => [[tl [rest0 [_ Htl Erest Hk]]]
                                      |[rest0 [Hne _ _]]]; last by [].
  subst rest1.
  (* --- 1. push R_RA: the caller spills its own capability --- *)
  have HcD' : TMacros.code_at_I cde C pcD
      (push R_RA ++ IJal tl :: pop R_RA ++ rest0) by exact: HcD.
  have Hrt : Transitional.Register.get_tag R_RA tregs = Some InternalJump.
  { move: (TMatch.vi_ra HI).
    rewrite /Transitional.Register.get_tag /Transitional.Register.get.
    by case: (getm tregs _) => [tv|] //= ->. }
  have Hcapb : size temps + 3 <= cap.
  { move: (TMatch.vi_budget HI) => /=.
    set X := maxn (size temps + 2) (kneed k (size temps)).
    have HX : size temps + 2 <= X by rewrite /X leq_max leqnn.
    move: HX. lia. }
  have Hsp : (0 <= Z.of_nat (2 + size temps) < Z.of_nat cap)%Z
    by move: Hcapb; lia.
  have Hnos : ~ List.In (TInv.CMem (C, fb, Z.of_nat (2 + size temps)))
      (TInv.sites (TStack.ledger_of Sl)).
  { move=> Hin. apply: (vi_nosite HI (o := Z.of_nat (2 + size temps))).
    apply: List.in_cons. exact: Hin. }
  case: (TProlog.push_ra_run HcD'
           (ltac:(by []) : IJal tl :: pop R_RA ++ rest0 <> [::]) Ec
           (TMatch.vi_sp HI) (TMatch.vi_one HI) Hrt
           (ltac:(by []) : TInv.is_live InternalJump)
           Hsp (TMatch.vi_cap HI) Hnos (proj2 (TMatch.vi_priv HI))
           (TMatch.vi_mem HI) (TMatch.vi_tag HI))
    => [tmem1 [rs1 [Pp [Hsl Hpres1 Hst1 Hcap1 Hmj1] [HSP1 HRA1 Hoth1] Htag1]]].
  (* --- 2. the [IJal] --- *)
  set pcJ := Pointer.inc (Pointer.inc pcD).
  have EcJ : Pointer.component pcJ = C
    by rewrite /pcJ !Pointer.inc_preserves_component.
  have HcJ : TMacros.code_at_I cde C pcJ (IJal tl :: pop R_RA ++ rest0)
    by apply: TMacros.code_at_I_tail; apply: TMacros.code_at_I_tail;
       exact: HcD'.
  case: (Hres tl Htl) => [pcE [sA [sB [cbody [EcE Hcpl HcE]]]]].
  have [nxtB [restB EB]] :=
    TDrain.nonempty_cons (TDrain.cat_nonempty (s1 := cbody)
      (ltac:(by []) : pop R_ARG ++ pop R_SP ++ [:: IJump] <> [::])).
  have HcE0 : TMacros.code_at_I cde C pcE
      ([::] ++ ILabel tl
       :: ([:: IMov R_SP R_AUX1;
               IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
               IAlloc R_SP R_SP]
           ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
           ++ nxtB :: restB)) by rewrite -EB; exact: HcE.
  case: (TMacros.code_at_I_label_find HcE0 EcE Hu) => [pcL [Hfind EcL HcL]].
  have SJ : TS.step cde (tmem1, rs1, pcJ, pct) E0
            (tmem1, Transitional.Register.set R_RA (Ptr (Pointer.inc pcJ))
                      InternalJump rs1, pcL, pct).
  { eapply TS.Jal.
    - exact: (TMacros.code_at_I_head HcJ).
    - by rewrite EcJ; exact: Hfind.
    - apply: PcJump; first exact: (TMacros.code_at_I_head HcL).
      by rewrite EcL EcJ. }
  set rs2 := Transitional.Register.set R_RA (Ptr (Pointer.inc pcJ))
               InternalJump rs1 in SJ *.
  have HnotReg : ~ List.In TInv.CReg
      (TInv.sites ((TInv.CMem (C, fb, Z.of_nat (2 + size temps)), InternalJump)
                   :: TStack.ledger_of Sl)).
  { have Hx : ~ List.In TInv.CReg (TInv.sites (TStack.ledger_of Sl)).
    { rewrite TStack.sites_ledger_of => /List.in_map_iff [q [Eq _]].
      by move: Eq. }
    by move=> [E|Hin]; [move: E | exact: Hx Hin]. }
  have Htag2 := TInv.tag_inv_jal (Pointer.inc pcJ) HnotReg Htag1.
  (* --- 3. the callee's prologue on a fresh frame --- *)
  have HONE2 : Transitional.Register.get R_ONE rs2 = MVal Other (Int 1)
    by rewrite /rs2 TInv.get_set_neq // Hoth1 //; exact: (TMatch.vi_one HI).
  have Hfb1 : fb <> 1 by case: (TMatch.vi_priv HI).
  have [wsc Hwsc] : exists w,
      Transitional.Memory.load tmem1 (C, 1, 0%Z) = Some w.
  { case: (TMatch.vi_scrs HI) => [_ _ S3 _].
    case: (S3 _ (TMatch.vi_dom HI)) => [vv Hvv].
    case: (TMem.vload_load Hvv) => [w Hw]. exists w.
    apply: (Hpres1 _ _ Hw).
    by move=> E; apply: Hfb1; move: (f_equal Pointer.block E) => /= <-. }
  have HcmF : exists cm, getm tmem1 C = Some cm.
  { case Hg: (getm tmem1 C) => [cm|]; first by exists cm.
    by move: Hwsc; rewrite /Transitional.Memory.load /= Hg. }
  have HcL' : TMacros.code_at_I cde C pcL
      ([:: ILabel tl; IMov R_SP R_AUX1;
           IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
           IAlloc R_SP R_SP]
       ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
       ++ nxtB :: restB) by exact: HcL.
  case: (TProlog.prologue_run HcL' EcL HONE2 HcmF Hmj1 Htag2)
    => [tmem5 [rs5 [fbN [pcF [Sp [Hfresh Havoid Hmj5 Hcap5 Hpres5]
                                [Hsl0 Hsl1] [HONE5 HSP5 HARG5 HCOM5 HRA5]
                                [Htag5 EcF HcF]]]]]].
  (* --- 4. the caller's frame is not the callee's --- *)
  have HneN : fbN <> fb.
  { move=> E. apply: (Hfresh (Z.of_nat (2 + size temps))
      (Transitional.Register.get R_RA tregs,
       {| vtag := InternalJump; color := C; entry := None;
          is_code := false |})).
    by rewrite E. }
  have HfbN1 : fbN <> 1 by move=> E; apply: (Hfresh 0%Z wsc); rewrite E.
  have Ltr5 : forall q, Pointer.block q <> fbN ->
      Transitional.Memory.load tmem5 q = Transitional.Memory.load tmem1 q
    by move=> q Hq; exact: (Hpres5 q (or_intror Hq)).
  have Ltr : forall q w, Transitional.Memory.load tmem q = Some w ->
      q <> ((C, fb, Z.of_nat (2 + size temps)) : Pointer.t) ->
      Pointer.block q <> fbN ->
      Transitional.Memory.load tmem5 q = Some w
    by move=> q w Hl Hq1 Hq2; rewrite (Ltr5 q Hq2); exact: (Hpres1 _ _ Hl Hq1).
  (* the scratch cells, and the caller's own frame *)
  have Ltr1 : forall (C' : Component.id) (o : Z) w,
      Transitional.Memory.load tmem (C', 1, o) = Some w ->
      Transitional.Memory.load tmem5 (C', 1, o) = Some w.
  { move=> C' o w Hl. apply: (Ltr _ _ Hl).
    - by move=> E; apply: Hfb1; move: (f_equal Pointer.block E) => /= <-.
    - by move=> E; apply: HfbN1; rewrite -E. }
  have Vtr1 : forall (C' : Component.id) (o : Z) vv,
      TMem.vload tmem (C', 1, o) = Some vv ->
      TMem.vload tmem5 (C', 1, o) = Some vv.
  { move=> C' o vv. rewrite /TMem.vload.
    case El: (Transitional.Memory.load tmem (C', 1, o)) => [w|//].
    by rewrite (Ltr1 _ _ _ El). }
  have Ttr1 : forall (C' : Component.id) (o : Z) t,
      TMem.tload tmem (C', 1, o) = Some t ->
      TMem.tload tmem5 (C', 1, o) = Some t.
  { move=> C' o t. rewrite /TMem.tload.
    case El: (Transitional.Memory.load tmem (C', 1, o)) => [w|//].
    by rewrite (Ltr1 _ _ _ El). }
  have LtrF : forall (o : Z) w,
      Transitional.Memory.load tmem (C, fb, o) = Some w ->
      o <> Z.of_nat (2 + size temps) ->
      Transitional.Memory.load tmem5 (C, fb, o) = Some w.
  { move=> o w Hl Ho. apply: (Ltr _ _ Hl).
    - by move=> E; apply: Ho; move: (f_equal Pointer.offset E).
    - by move=> E; apply: HneN; rewrite -E. }
  have VtrF : forall (o : Z) vv, o <> Z.of_nat (2 + size temps) ->
      TMem.vload tmem (C, fb, o) = Some vv ->
      TMem.vload tmem5 (C, fb, o) = Some vv.
  { move=> o vv Ho. rewrite /TMem.vload.
    case El: (Transitional.Memory.load tmem (C, fb, o)) => [w|//].
    by rewrite (LtrF _ _ El Ho). }
  have TtrF : forall (o : Z) t, o <> Z.of_nat (2 + size temps) ->
      TMem.tload tmem (C, fb, o) = Some t ->
      TMem.tload tmem5 (C, fb, o) = Some t.
  { move=> o t Ho. rewrite /TMem.tload.
    case El: (Transitional.Memory.load tmem (C, fb, o)) => [w|//].
    by rewrite (LtrF _ _ El Ho). }
  (* --- 5. the chain below the caller --- *)
  have HslSl : TStack.slots_ok tmem Sl
    := TSM.stack_match_slots (TMatch.vi_stack HI).
  have HaddrNe : forall s0, List.In s0 Sl ->
      TStack.ra_addr s0 <> ((C, fb, Z.of_nat (2 + size temps)) : Pointer.t).
  { move=> s0 Hs0 E.
    have Hsite : List.In (TInv.CMem (C, fb, Z.of_nat (2 + size temps)))
        (TInv.sites (TStack.ledger_of Sl)).
    { rewrite TStack.sites_ledger_of /TStack.addrs. apply/List.in_map_iff.
      exists (TStack.ra_addr s0). split; first by rewrite E.
      by apply/List.in_map_iff; exists s0. }
    exact: Hnos Hsite. }
  have Hslots1 : TStack.slots_ok tmem1 Sl.
  { move=> s0 Hs0. case: (HslSl s0 Hs0) => [A [B D]].
    case: (TMem.vload_load A) => [w Hw].
    have Hw1 := Hpres1 _ _ Hw (HaddrNe s0 Hs0).
    split; last split; last exact: D.
    - by rewrite /TMem.vload Hw1; move: A; rewrite /TMem.vload Hw.
    - by rewrite /TMem.tload Hw1; move: B; rewrite /TMem.tload Hw. }
  have Hbadp : forall p, p \in prot ->
      ~~ (p == ((C, fbN) : Component.id * Block.id)).
  { move=> p Hp. apply/eqP => E.
    case: (TSM.stack_match_prot_loaded (TMatch.vi_stack HI) Hp) => [o [w Hw]].
    move: Hw; rewrite E /= => Hw.
    apply: (Hfresh o w). apply: (Hpres1 _ _ Hw).
    by move=> Ex; apply: HneN; move: (f_equal Pointer.block Ex) => /= ->. }
  have Hsm1 : TSM.stack_match cde labelsP a tmem1 scrs C fb prot stk ret Sl.
  { apply: (TSM.stack_match_store (TMatch.vi_stack HI) Hst1
              (TMatch.vi_prot HI) _ Hslots1) => _.
    have -> : Pointer.offset ((C, fb, Z.of_nat (2 + size temps)) : Pointer.t)
            = Z.of_nat (2 + size temps) by [].
    lia. }
  have Hraw5 : forall q,
      ~~ ((Pointer.component q, Pointer.block q)
          == ((C, fbN) : Component.id * Block.id)) ->
      Transitional.Memory.load tmem5 q = Transitional.Memory.load tmem1 q.
  { move=> q /eqP Hq. apply: Hpres5.
    case: (@eqP _ (Pointer.component q) C) => [EC|HC]; last by left.
    by right=> EB2; apply: Hq; rewrite EC EB2. }
  have Hb0 : ~~ (((C, fb) : Component.id * Block.id)
                 == ((C, fbN) : Component.id * Block.id))
    by apply/eqP => E; apply: HneN; move: (f_equal snd E) => /= <-.
  have Hsm5 : TSM.stack_match cde labelsP a tmem5 scrs C fb prot stk ret Sl.
  { apply: (TSM.stack_match_raw
              (bad := fun p : Component.id * Block.id => p == (C, fbN))
              _ _ Hb0 Hbadp Hsm1).
    - by move=> q Hq; rewrite /TMem.vload (Hraw5 q Hq).
    - by move=> q Hq; rewrite /TMem.tload (Hraw5 q Hq). }
  (* --- 6. assembled --- *)
  set sNew := TStack.RASlot (C, fb, Z.of_nat (2 + size temps)) ret
                InternalJump.
  have EARG2 : Transitional.Register.get R_ARG rs2
             = Transitional.Register.get R_ARG tregs
    by rewrite /rs2 TInv.get_set_neq // Hoth1.
  have ESP2 : Transitional.Register.get R_SP rs2
            = MVal Other (Ptr (C, fb, (Z.of_nat (2 + size temps) + 1)%Z))
    by rewrite /rs2 TInv.get_set_neq //.
  have Eoff : (Z.of_nat (2 + size temps) + 1)%Z = Z.of_nat (2 + size temps + 1)
    by lia.
  exists tmem5, rs5, pcF, cbody, (pop R_ARG ++ pop R_SP ++ [:: IJump]),
         sA, sB, fbN, (Pointer.inc pcJ), (sNew :: Sl).
  split.
  - eapply star_plus_trans with (t1 := E0) (t2 := E0); [exact: Sd | | by []].
    eapply plus_trans with (t1 := E0) (t2 := E0); [exact: Pp | | by []].
    eapply plus_left with (t1 := E0) (t2 := E0);
      [exact: SJ | exact: Sp | by []].
  - apply: TMatch.ExprInv;
    last by eauto using TMatch.ei_anchor, TMatch.vi_anchor.
    + exact: (TMatch.vi_plm HI).
    + exact: (TMatch.vi_dom HI).
    + exact: Hmj5.
    + case: (TMatch.vi_scrs HI) => [S1 S2 S3 S4]. split.
      * move=> C' vv Hg. exact: (@Vtr1 _ _ _ (S1 _ _ Hg)).
      * case: S2 => [S2v S2t]. split; first exact: (@Vtr1 _ _ _ S2v).
        exact: (@Ttr1 _ _ _ S2t).
      * move=> C' Hd. case: (S3 _ Hd) => [vv Hvv]. exists vv.
        exact: (@Vtr1 _ _ _ Hvv).
      * move=> C' Hd. exact: (@Ttr1 _ _ _ (S4 _ Hd)).
    + exact: HONE5.
    + by rewrite HSP5.
    + rewrite HARG5 /rs2 TInv.get_set_neq // Hoth1 //.
      exact: (TMatch.vi_com HI).
    + by rewrite HRA5 /rs2 TInv.get_set_eq.
    + by [].
    + exact: EcF.
    + exact: Hcpl.
    + by rewrite EB.
    + apply: CMJ_base. exact: CM_stop.
    + exact: (TMatch.vi_uniq HI).
    + by split; [exact: HfbN1 | exact: Havoid].
    + exact: (TMatch.vi_scrp HI).
    + by move=> ix; rewrite ltn0.
    + exact: Hcap5.
    + rewrite /= maxn0 add0n. by lia.
    + apply/negP => /orP [/eqP E|Hin].
      * by apply: HneN; move: (f_equal snd E) => /= ->.
      * by move: (Hbadp _ Hin) => /eqP.
    + apply: (@TSM.SM_internal cde labelsP a tmem5 scrs C fbN fb prot stk arg
                (Transitional.val (Transitional.Register.get R_ARG tregs))
                k rest0 temps plm (Pointer.inc pcJ) sNew Sl cap).
      * exact: (TMatch.vi_plm HI).
      * by rewrite /pcJ !Pointer.inc_preserves_component.
      * exact: (TMacros.code_at_I_tail HcJ).
      * exact: Hk.
      * have -> : Z.of_nat (2 + size temps + 1)
                = (Z.of_nat (2 + size temps) + 1)%Z by lia.
        by rewrite /TMem.vload Hsl0 ESP2.
      * by rewrite /TMem.vload Hsl1 EARG2.
      * by rewrite /TMem.tload Hsl0.
      * have -> : Other = tvtag (Transitional.Register.get R_ARG rs2).
        { by rewrite EARG2 (TInv.ti_regs (TMatch.vi_tag HI) (r := R_ARG)
                              (ltac:(by []))). }
        by rewrite /TMem.tload Hsl1.
      * exact: (TMatch.vi_arg HI).
      * exact: (TMatch.vi_priv HI).
      * move=> ix Hix. case: (TMatch.vi_temps HI Hix) => [Hv Ht].
        have Ho : Z.of_nat (1 + size temps - ix) <> Z.of_nat (2 + size temps)
          by move: Hix; lia.
        by split; [exact: (@VtrF _ _ Ho Hv) | exact: (@TtrF _ _ Ho Ht)].
      * by [].
      * by [].
      * move=> s0 [Es0|Hin].
        -- have Hl5 : Transitional.Memory.load tmem5
               (C, fb, Z.of_nat (2 + size temps))
             = Some (Transitional.Register.get R_RA tregs,
                     {| vtag := InternalJump; color := C; entry := None;
                        is_code := false |}).
           { rewrite Ltr5; first exact: Hsl.
             by move=> E; apply: HneN; rewrite -E. }
           rewrite -Es0.
           have Ev : TMem.vload tmem5 (TStack.ra_addr sNew)
                   = Some (Ptr (TStack.ra_ret sNew))
             by rewrite /sNew /TMem.vload /= Hl5 /= (TMatch.vi_ra HI).
           have Et : TMem.tload tmem5 (TStack.ra_addr sNew)
                   = Some (TStack.ra_tag sNew)
             by rewrite /sNew /TMem.tload /= Hl5 /= (TMatch.vi_ra HI).
           by split; [exact: Ev | split; [exact: Et | by rewrite /sNew]].
        -- case: (Hslots1 s0 Hin) => [A [B D]].
           case: (TMem.vload_load A) => [w Hw].
           have Hne5 : Pointer.component (TStack.ra_addr s0) <> C
                       \/ Pointer.block (TStack.ra_addr s0) <> fbN.
           { case: (@eqP _ (Pointer.component (TStack.ra_addr s0)) C)
               => [EC|HC]; last by left.
             right=> EBk.
             apply: (Hfresh (Pointer.offset (TStack.ra_addr s0)) w).
             have -> : ((C, fbN, Pointer.offset (TStack.ra_addr s0))
                        : Pointer.t) = TStack.ra_addr s0
               by rewrite -EC -EBk -TStack.ptr_expand.
             exact: Hw. }
           split; last split; last exact: D.
           ++ by rewrite /TMem.vload (Hpres5 _ Hne5).
           ++ by rewrite /TMem.tload (Hpres5 _ Hne5).
      * move=> j Hj.
        case: (TStack.frame_cap_store Hst1 (TMatch.vi_cap HI) Hj) => [vv Hvv].
        exists vv. move: Hvv. rewrite /TMem.vload (Ltr5 (C, fb, j)) //.
        by move=> E; apply: HneN; rewrite -E.
      * move: (TMatch.vi_budget HI) => /=.
        set X := maxn (size temps + 2) (kneed k (size temps)).
        have HX : kneed k (size temps) <= X
          by rewrite /X leq_max leqnn orbT.
        move: HX. lia.
      * exact: (TMatch.vi_prot HI).
      * exact: HneN.
      * exact: Hsm5.
    + exact: Htag5.
Qed.

(* ================================================================== *)
(* KS_ExternalCall — the longest run in the campaign                   *)
(* ================================================================== *)

(** The caller spills its capability and its argument, PARKS its stack pointer
    in the scratch cell (registers do not survive an [ICall]), and calls; the
    callee's WRAPPER builds its own activation and `IJal`s into the body.

    Three things happen here that happen nowhere else:

    - `pc_tag` goes UP ([TInv.tag_inv_call]), and the fresh `Ret n` it creates
      is immediately spilled into the wrapper's slot 2 — which is why
      `SM_external` records `ra_tag sE = Ret (size (ext_levels Sl))`: the level
      the machine hands out is exactly the number of live `Ret`s below, and
      `TStack.levels_ok_size` is what turns `ti_lvl`'s multiset into that
      equation;
    - the scratch map gains the caller's parked pointer, which is what
      `TSM.stack_match_scrs_update` is for;
    - the callee's INHERITED scratch value is saved in the wrapper's slot 1,
      and it is exactly the value the deeper `stack_match` already records for
      `Cf` — so `setm scrs Cf vscr` either collapses (`setmI`) or extends
      (`stack_match_scrs_extend`).

    As in `diagram_call_int` the entry resolution is a PREMISE for Stage 3 to
    discharge; here it names the `TrLabel (inr (Cf,P))` header the `ICall`
    lands on, its `check_pc_call` (the LRC entry check: `C` is allowed to call
    `Cf.P`), the wrapper's code, and the body's. *)
Lemma diagram_call_ext a scrs C Cf stk mem k P v arg ret rtag Sl tmem tregs pct
      pc fb prot temps plm rest cap P_expr :
  val_inv a scrs C stk mem (Kcall Cf P k) (Int v) arg ret rtag Sl tmem tregs
          pct pc fb prot temps plm rest cap ->
  C <> Cf ->
  Cf \in domm iface ->
  (exists pcW tniW plmf plf pcE sA sB cbody,
     [/\ [/\ Transitional.find_plabel_in_code cde Cf P = Some pcW,
             Transitional.executing cde pcW
               (Transitional.TrLabel (inr (Cf, P))) tniW Cf,
             Transitional.check_pc_call C tniW P
           & getm labelsP Cf = Some plmf],
         (* ★ EITHER wrapper. `(main, main)` gets `compile_proc`'s DUAL entry,
            not this one, and nothing in `well_formed_program` stops a
            component from importing it. *)
         (TMacros.code_at_I cde Cf (Pointer.inc pcW)
            (IConst (IInt 1) R_ONE
             :: [:: IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
                    IAlloc R_SP R_SP]
                ++ push R_AUX1 ++ load_arg (scr Cf) R_AUX1 ++ push R_AUX1
                ++ push R_RA
                ++ IJal plf
                   :: pop R_RA ++ pop R_AUX1
                      ++ store_arg (scr Cf) R_AUX1 R_AUX2
                      ++ pop R_SP ++ [:: IReturn])
          \/ (Cf = Component.main /\ exists lmain lret,
                TMacros.code_at_I cde Cf (Pointer.inc pcW)
                  (IConst (IInt 1) R_ONE
                   :: [:: IMov R_SP R_AUX1;
                          IConst (IInt (Z.of_nat (4 + stack_need P_expr)))
                            R_SP;
                          IAlloc R_SP R_SP]
                      ++ push R_AUX1 ++ load_arg (scr Cf) R_AUX1
                      ++ push R_AUX1 ++ push R_RA
                      ++ [:: IConst (IPtr (flag_buf_ptr (scr Cf))) R_AUX1;
                             ILoad R_AUX1 R_AUX2]
                      ++ push R_AUX2
                      ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM;
                             ILabel lmain; IConst (IInt 1) R_AUX2;
                             IStore R_AUX1 R_AUX2]
                      ++ IJal plf
                         :: pop R_ARG ++ pop R_RA ++ pop R_AUX1
                            ++ store_arg (scr Cf) R_AUX1 R_AUX2
                            ++ pop R_SP
                            ++ [:: IBnz R_ARG lret; IHalt; ILabel lret;
                                   IReturn]))
          \/ (Cf = Component.main /\ P = Procedure.main /\ exists tl,
                TMacros.code_at_I cde Cf (Pointer.inc pcW) (IHalt :: tl))),
         Pointer.component pcE = Cf,
         compile_expr Cf (lbp Cf) (scr Cf) plmf P_expr sA = Some (cbody, sB)
       & TMacros.code_at_I cde Cf pcE
           ([:: ILabel plf; IMov R_SP R_AUX1;
                IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
                IAlloc R_SP R_SP]
            ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
            ++ cbody ++ pop R_ARG ++ pop R_SP ++ [:: IJump])]) ->
  exists scrs1 tmem5 tregs5 pcF c1 rest1 sA' sB' fbN prot1 plmf retN Sl1,
    plus TS.step cde (tmem, tregs, pc, pct) [:: ECall C P v Cf]
         (tmem5, tregs5, pcF, inc_pc_tag pct)
    /\ expr_inv a scrs1 Cf (S.CS.Frame C arg k :: stk) mem Kstop P_expr (Int v)
                retN InternalJump Sl1 tmem5 tregs5 (inc_pc_tag pct) pcF fbN
                prot1 [::] plmf c1 rest1 sA' sB' (4 + stack_need P_expr).
Proof.
  move=> HI HneCf HdomF Hres.
  move: (TMatch.vi_rtag HI) => Ert; subst rtag.
  case: Hres => [pcW [tniW [plmf [plf [pcE [sA [sB [cbody
    [[Hfind HexW Hchk Hplmf] HcW EcE Hcpl HcE]]]]]]]]].
  have EcW : Pointer.component pcW = Cf.
  { move: Hfind. rewrite /Transitional.find_plabel_in_code.
    case: (getm cde Cf) => [C_code|] //.
    case: (Transitional.find_plabel _ _ _) => [o|] //. by move=> [<-]. }
  have Hu : forall C0, TDrain.labels_uniq cde C0
    := TMatch.vi_uniq HI.
  have HuC : TDrain.labels_uniq cde C
    by move=> l0 C_code Hg; exact: (TMatch.vi_uniq HI l0 Hg).
  case: (vi_drain HI) => [pcD [rest1 [Sd _ HcD Ec Hcm']]].
  case: (cont_match_call_inv Hcm') => [[tl [rest0 [EC _ _ _]]]
                                      |[rest0 [_ Erest Hk]]];
    first by case: HneCf; rewrite EC.
  subst rest1.
  have Ecom : Transitional.val (Transitional.Register.get R_COM tregs) = Int v
    by move: (TMatch.vi_com HI) => /val_inject_int_l ->.
  (* --- 1. push R_RA --- *)
  set sp := Z.of_nat (2 + size temps).
  have HcD' : TMacros.code_at_I cde C pcD
      (push R_RA ++ push R_ARG ++ store_arg (scr C) R_SP R_AUX2
       ++ ICall Cf P :: IConst (IInt 1) R_ONE
          :: reload_sp (scr C) ++ pop R_ARG ++ pop R_RA ++ rest0)
    by exact: HcD.
  have Hrt : Transitional.Register.get_tag R_RA tregs = Some InternalJump.
  { move: (TMatch.vi_ra HI).
    rewrite /Transitional.Register.get_tag /Transitional.Register.get.
    by case: (getm tregs _) => [tv|] //= ->. }
  have Hcapb : size temps + 5 <= cap.
  { move: (TMatch.vi_budget HI) => /=.
    set X := maxn (size temps + 2) (kneed k (size temps)).
    have HX : size temps + 2 <= X by rewrite /X leq_max leqnn.
    move: HX. lia. }
  have Hsp : (0 <= sp < Z.of_nat cap)%Z by rewrite /sp; move: Hcapb; lia.
  have Hnos : ~ List.In (TInv.CMem (C, fb, sp)) (TInv.sites (TStack.ledger_of Sl)).
  { move=> Hin. apply: (vi_nosite HI (o := sp)).
    apply: List.in_cons. exact: Hin. }
  have Hfb1 : fb <> 1 by case: (TMatch.vi_priv HI).
  case: (TProlog.push_ra_run HcD'
           (ltac:(by []) : push R_ARG ++ store_arg (scr C) R_SP R_AUX2
              ++ ICall Cf P :: IConst (IInt 1) R_ONE
                 :: reload_sp (scr C) ++ pop R_ARG ++ pop R_RA ++ rest0
              <> [::]) Ec
           (TMatch.vi_sp HI) (TMatch.vi_one HI) Hrt
           (ltac:(by []) : TInv.is_live InternalJump)
           Hsp (TMatch.vi_cap HI) Hnos (proj2 (TMatch.vi_priv HI))
           (TMatch.vi_mem HI) (TMatch.vi_tag HI))
    => [tmem1 [rs1 [Pp1 [Hsl Hpres1 Hst1 Hcap1 Hmj1] [HSP1 HRA1 Hoth1] Htag1]]].
  (* --- 2. push R_ARG --- *)
  set pc2 := Pointer.inc (Pointer.inc pcD).
  have Ec2 : Pointer.component pc2 = C
    by rewrite /pc2 !Pointer.inc_preserves_component.
  have Hc2 : TMacros.code_at_I cde C pc2
      (push R_ARG ++ store_arg (scr C) R_SP R_AUX2
       ++ ICall Cf P :: IConst (IInt 1) R_ONE
          :: reload_sp (scr C) ++ pop R_ARG ++ pop R_RA ++ rest0)
    by apply: TMacros.code_at_I_tail; apply: TMacros.code_at_I_tail;
       exact: HcD'.
  have HONE1 : Transitional.Register.get R_ONE rs1 = MVal Other (Int 1)
    by rewrite Hoth1 //; exact: (TMatch.vi_one HI).
  have Hsp1 : (0 <= sp + 1 < Z.of_nat cap)%Z by rewrite /sp; move: Hcapb; lia.
  have Hnos1 : ~ List.In (TInv.CMem (C, fb, (sp + 1)%Z))
      (TInv.sites ((TInv.CMem (C, fb, sp), InternalJump)
                   :: TStack.ledger_of Sl)).
  { move=> /= [E|Hin]; last first.
    { apply: (vi_nosite HI (o := (sp + 1)%Z)). apply: List.in_cons.
      exact: Hin. }
    by move: (f_equal (fun x => match x with
                                | TInv.CMem q => Pointer.offset q
                                | TInv.CReg => 0%Z end) E) => /=; lia. }
  case: (TProlog.push_data_run Hc2
           (ltac:(by []) : store_arg (scr C) R_SP R_AUX2
              ++ ICall Cf P :: IConst (IInt 1) R_ONE
                 :: reload_sp (scr C) ++ pop R_ARG ++ pop R_RA ++ rest0
              <> [::]) Ec2
           (ltac:(by []) : R_ARG <> R_RA)
           (ltac:(by []) : R_SP <> R_ARG)
           (ltac:(by []) : R_ONE <> R_ARG)
           HSP1 HONE1 Hsp1 Hcap1 Hnos1 (proj2 (TMatch.vi_priv HI)) Hmj1 Htag1)
    => [tmem2 [rs2 [Pp2 [Hsl2 Hpres2 Hst2 Hcap2 Hmj2]
                        [HSP2 HARG2 Hoth2] Htag2]]].
  (* --- 3. store_arg: park [R_SP] in the scratch cell --- *)
  set pc4 := Pointer.inc (Pointer.inc pc2).
  have Ec4 : Pointer.component pc4 = C
    by rewrite /pc4 /pc2 !Pointer.inc_preserves_component.
  have Hc4 : TMacros.code_at_I cde C pc4
      (store_arg (scr C) R_SP R_AUX2
       ++ ICall Cf P :: IConst (IInt 1) R_ONE
          :: reload_sp (scr C) ++ pop R_ARG ++ pop R_RA ++ rest0)
    by apply: TMacros.code_at_I_tail; apply: TMacros.code_at_I_tail;
       exact: Hc2.
  have Hnefb : forall (o o' : Z), ((C, 1, o) : Pointer.t) <> (C, fb, o')
    by move=> o o' E; apply: Hfb1;
       move: (f_equal Pointer.block E) => /= ->.
  have [mscr Hmscr] : exists w,
      Transitional.Memory.load tmem2 (C, 1, 0%Z) = Some w.
  { case: (TMatch.vi_scrs HI) => [_ _ S3 _].
    case: (S3 _ (TMatch.vi_dom HI)) => [vv Hvv].
    case: (TMem.vload_load Hvv) => [w Hw]. exists w.
    apply: (Hpres2 _ _ _ (Hnefb _ _)). exact: (Hpres1 _ _ Hw (Hnefb _ _)). }
  have Hnoscr : ~ List.In (TInv.CMem (C, 1, 0%Z))
      (TInv.sites ((TInv.CMem (C, fb, sp), InternalJump)
                   :: TStack.ledger_of Sl)).
  { move=> /= [E|Hin].
    { have E' : ((C, fb, sp) : Pointer.t) = (C, 1, 0%Z) by congruence.
      apply: Hfb1. exact: (f_equal Pointer.block E'). }
    move: Hin; rewrite TStack.sites_ledger_of /TStack.addrs
      => /List.in_map_iff [q [Eq Hin]].
    move: Hin => /List.in_map_iff [s0 [Es0 Hs0]].
    have Ep : TStack.ra_addr s0 = (C, 1, 0%Z) by congruence.
    case: (TSM.stack_match_slots (TMatch.vi_stack HI) Hs0) => [_ [Ht Hlive]].
    move: Ht; rewrite Ep.
    case: (TMatch.vi_scrs HI) => [_ _ _ S4].
    by rewrite (S4 _ (TMatch.vi_dom HI)) => -[E]; move: Hlive; rewrite -E. }
  have HSP2' : Transitional.Register.get R_SP rs2
             = MVal Other (Ptr (C, fb, (sp + 1 + 1)%Z)) by exact: HSP2.
  case: (TProlog.store_sp_run Hc4
           (ltac:(by []) : ICall Cf P :: IConst (IInt 1) R_ONE
              :: reload_sp (scr C) ++ pop R_ARG ++ pop R_RA ++ rest0 <> [::])
           Ec4 HSP2' Hmscr Hnoscr
           (ltac:(by move=> b0 Hb0; exact: (TMatch.vi_scrp HI Hb0))
            : forall b0, a C b0 <> Some 1)
           Hmj2 Htag2)
    => [tmem3 [rs3 [Pp3 [Hst3 Hvsc Htsc Hmj3] [HSP3 Hoth3] Htag3]]].
  (* --- 4. the [ICall] --- *)
  set pcC := Pointer.inc (Pointer.inc pc4).
  have EcC : Pointer.component pcC = C
    by rewrite /pcC /pc4 /pc2 !Pointer.inc_preserves_component.
  have HcC : TMacros.code_at_I cde C pcC
      (ICall Cf P :: IConst (IInt 1) R_ONE
       :: reload_sp (scr C) ++ pop R_ARG ++ pop R_RA ++ rest0)
    by apply: TMacros.code_at_I_tail; apply: TMacros.code_at_I_tail;
       exact: Hc4.
  have HCOM3 : Transitional.val (Transitional.Register.get R_COM rs3) = Int v
    by rewrite Hoth3 // Hoth2 // Hoth1 //.
  set n := level pct.
  have SC : TS.step cde (tmem3, rs3, pcC, pct) [:: ECall C P v Cf]
            (tmem3,
             Transitional.Register.set R_RA (Ptr (Pointer.inc pcC)) (Ret n)
               (Transitional.Register.invalidate rs3),
             pcW, inc_pc_tag pct).
  { have EIC : (Transitional.instr_to_transitional C (ICall Cf P)).1
             = Transitional.TrJalProc (Cf, P)
      by rewrite /Transitional.instr_to_transitional; case: (Nat.eqb C Cf).
    move: (TMacros.code_at_I_head HcC); rewrite EIC EcC => HexC.
    eapply TS.Call.
    - exact: HexC.
    - exact: Hfind.
    - exact: HexW.
    - exact: HneCf.
    - exact: Hchk.
    - exact: (TInv.pc_tagE pct).
    - exact: HCOM3. }
  set rsC := Transitional.Register.set R_RA (Ptr (Pointer.inc pcC)) (Ret n)
               (Transitional.Register.invalidate rs3) in SC *.
  have HnotReg : ~ List.In TInv.CReg
      (TInv.sites ((TInv.CMem (C, fb, sp), InternalJump)
                   :: TStack.ledger_of Sl)).
  { have Hx : ~ List.In TInv.CReg (TInv.sites (TStack.ledger_of Sl)).
    { rewrite TStack.sites_ledger_of => /List.in_map_iff [q [Eq _]].
      by move: Eq. }
    by move=> [E|Hin]; [move: E | exact: Hx Hin]. }
  have HtagC := TInv.tag_inv_call (Pointer.inc pcC) (TInv.pc_tagE pct)
                  HnotReg Htag3.
  (* --- 5. the callee's WRAPPER --- *)
  have HneFC : Cf <> C by move=> E; apply: HneCf; rewrite E.
  have Ltr3 : forall (o : Z) w,
      Transitional.Memory.load tmem (Cf, 1, o) = Some w ->
      Transitional.Memory.load tmem3 (Cf, 1, o) = Some w.
  { move=> o w Hl.
    rewrite (TMem.load_store_neq Hst3); last first.
    { by move=> E; apply: HneFC; move: (f_equal Pointer.component E) => /= ->. }
    apply: (Hpres2 _ _ _ _); last first.
    { by move=> E; apply: HneFC;
        move: (f_equal Pointer.component E) => /= ->. }
    apply: (Hpres1 _ _ Hl).
    by move=> E; apply: HneFC; move: (f_equal Pointer.component E) => /= ->. }
  have [mscrf Hmscrf] : exists w,
      Transitional.Memory.load tmem3 (Cf, 1, 0%Z) = Some w.
  { case: (TMatch.vi_scrs HI) => [_ _ S3 _]. case: (S3 _ HdomF) => [vv Hvv].
    case: (TMem.vload_load Hvv) => [w Hw]. exists w. exact: (Ltr3 _ _ Hw). }
  have Etmf : tvtag mscrf.1 = Other.
  { case: (TMatch.vi_scrs HI) => [_ _ S3 S4].
    case: (S3 _ HdomF) => [vv Hvv]. case: (TMem.vload_load Hvv) => [w Hw].
    move: (S4 _ HdomF); rewrite /TMem.tload Hw /=.
    have E : w = mscrf by move: (Ltr3 _ _ Hw); rewrite Hmscrf => -[->].
    by rewrite E => -[<-]. }
  have HcmF : exists cm, getm tmem3 Cf = Some cm.
  { case Hg: (getm tmem3 Cf) => [cm|]; first by exists cm.
    by move: Hmscrf; rewrite /Transitional.Memory.load /= Hg. }
  have HrtC : Transitional.Register.get_tag R_RA rsC = Some (Ret n).
  { have E : Transitional.Register.get R_RA rsC
           = MVal (Ret n) (Ptr (Pointer.inc pcC))
      by rewrite /rsC TInv.get_set_eq.
    move: E. rewrite /Transitional.Register.get_tag
                     /Transitional.Register.get.
    by case: (getm rsC _) => [tv|] //= ->. }
  have HnoscrF : ~ List.In (TInv.CMem (Cf, 1, 0%Z))
      (TInv.sites ((TInv.CMem (C, fb, sp), InternalJump)
                   :: TStack.ledger_of Sl)).
  { move=> /= [E|Hin].
    { have E' : ((C, fb, sp) : Pointer.t) = (Cf, 1, 0%Z) by congruence.
      by apply: HneCf; move: (f_equal Pointer.component E') => /= ->. }
    move: Hin; rewrite TStack.sites_ledger_of /TStack.addrs
      => /List.in_map_iff [q [Eq Hin]].
    move: Hin => /List.in_map_iff [s0 [Es0 Hs0]].
    have Ep : TStack.ra_addr s0 = (Cf, 1, 0%Z) by congruence.
    case: (TSM.stack_match_slots (TMatch.vi_stack HI) Hs0) => [_ [Ht Hlive]].
    move: Ht; rewrite Ep.
    case: (TMatch.vi_scrs HI) => [_ _ _ S4].
    by rewrite (S4 _ HdomF) => -[E]; move: Hlive; rewrite -E. }
  (* ★ the HALT PAD disjunct is impossible HERE, and this is where it dies.
     `main_anchored` — which the invariant carries, and whose holding at all is
     the evidence that the machine got past the pad — says main's WRAPPER is
     the cell one past main's header. Two [executing]s at one pc with different
     instructions. *)
  have HcW' :
    (TMacros.code_at_I cde Cf (Pointer.inc pcW)
       (IConst (IInt 1) R_ONE
        :: [:: IMov R_SP R_AUX1;
               IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
               IAlloc R_SP R_SP]
           ++ push R_AUX1 ++ load_arg (scr Cf) R_AUX1 ++ push R_AUX1
           ++ push R_RA
           ++ IJal plf
              :: pop R_RA ++ pop R_AUX1
                 ++ store_arg (scr Cf) R_AUX1 R_AUX2
                 ++ pop R_SP ++ [:: IReturn]))
    \/ (Cf = Component.main /\ exists lmain lret,
          TMacros.code_at_I cde Cf (Pointer.inc pcW)
            (IConst (IInt 1) R_ONE
             :: [:: IMov R_SP R_AUX1;
                    IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
                    IAlloc R_SP R_SP]
                ++ push R_AUX1 ++ load_arg (scr Cf) R_AUX1 ++ push R_AUX1
                ++ push R_RA
                ++ [:: IConst (IPtr (flag_buf_ptr (scr Cf))) R_AUX1;
                       ILoad R_AUX1 R_AUX2]
                ++ push R_AUX2
                ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM;
                       ILabel lmain; IConst (IInt 1) R_AUX2;
                       IStore R_AUX1 R_AUX2]
                ++ IJal plf
                   :: pop R_ARG ++ pop R_RA ++ pop R_AUX1
                      ++ store_arg (scr Cf) R_AUX1 R_AUX2 ++ pop R_SP
                      ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn])).
  { case: HcW => [Hstd|[Hm|[EcfM [EPm [tlH HcH]]]]];
      [by left | by right | exfalso].
    case: (TMatch.vi_anchor HI) => [pcWm [tlm [Hfm Hcm]]].
    have EpcW : pcW = pcWm
      by move: Hfind; rewrite EcfM EPm Hfm => -[->].
    move: (TMacros.code_at_I_head HcH) (TMacros.code_at_I_head Hcm).
    rewrite EcfM EpcW => -[Cc1 [_ [Hg1 [_ Hn1]]]] -[Cc2 [_ [Hg2 [_ Hn2]]]].
    move: Hg2; rewrite Hg1 => -[EC]. rewrite -EC Hn1 in Hn2.
    by move: Hn2 => -[]. }
  (* both surviving shapes start with the same [IConst 1 R_ONE], which is all
     the header's [check_pc] needs *)
  have [tl0 HcW1] : exists tl0, TMacros.code_at_I cde Cf (Pointer.inc pcW)
                                  (IConst (IInt 1) R_ONE :: tl0).
  { case: HcW' => [Hstd|[_ [lmain [lret Hmain]]]]; eexists;
      [exact: Hstd | exact: Hmain]. }
  have SL : TS.step cde (tmem3, rsC, pcW, inc_pc_tag pct) E0
            (tmem3, rsC, Pointer.inc pcW, inc_pc_tag pct).
  { eapply TS.Label; first exact: HexW.
    apply: PcFall. exact: (TMacros.code_at_I_head HcW1). }
  (* the two wrapper shapes, in the form [ef_call_entry_run] consumes; the
     flag facts for main's come from [scrs_ok]'s second clause, which is why
     that clause had to grow a TAG half *)
  have Hshape' :
    ((exists tl,
        TMacros.code_at_I cde Cf (Pointer.inc pcW)
          (IConst (IInt 1) R_ONE
           :: [:: IMov R_SP R_AUX1;
                  IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
                  IAlloc R_SP R_SP]
              ++ push R_AUX1 ++ load_arg (scr Cf) R_AUX1 ++ push R_AUX1
              ++ push R_RA
              ++ IJal plf :: tl)
        /\ tl = pop R_RA ++ pop R_AUX1 ++ store_arg (scr Cf) R_AUX1 R_AUX2
                ++ pop R_SP ++ [:: IReturn])
     \/ (exists lmain lret,
           [/\ TMacros.code_at_I cde Cf (Pointer.inc pcW)
                 (IConst (IInt 1) R_ONE
                  :: [:: IMov R_SP R_AUX1;
                         IConst (IInt (Z.of_nat (4 + stack_need P_expr)))
                           R_SP;
                         IAlloc R_SP R_SP]
                     ++ push R_AUX1 ++ load_arg (scr Cf) R_AUX1
                     ++ push R_AUX1 ++ push R_RA
                     ++ [:: IConst (IPtr (flag_buf_ptr (scr Cf))) R_AUX1;
                            ILoad R_AUX1 R_AUX2]
                     ++ push R_AUX2
                     ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM;
                            ILabel lmain; IConst (IInt 1) R_AUX2;
                            IStore R_AUX1 R_AUX2]
                     ++ IJal plf
                        :: pop R_ARG ++ pop R_RA ++ pop R_AUX1
                           ++ store_arg (scr Cf) R_AUX1 R_AUX2 ++ pop R_SP
                           ++ [:: IBnz R_ARG lret; IHalt; ILabel lret;
                                  IReturn]),
               TMem.vload tmem3 (Cf, 1, 1%Z) = Some (Int 1)
             & TMem.tload tmem3 (Cf, 1, 1%Z) = Some Other])).
  { case: HcW' => [Hstd|[EcfM [lmain [lret Hmain]]]].
    - by left; eexists; split; [exact: Hstd | ].
    - right. exists lmain, lret.
      case: (TMatch.vi_scrs HI) => [_ [S2v S2t] _ _].
      have [wf Hwf] : exists w,
          Transitional.Memory.load tmem (Cf, 1, 1%Z) = Some w
        by rewrite EcfM; case: (TMem.vload_load S2v) => [w Hw]; exists w.
      have Hwf3 := Ltr3 _ _ Hwf.
      split.
      + exact: Hmain.
      + rewrite /TMem.vload Hwf3.
        by move: S2v; rewrite -EcfM /TMem.vload Hwf /= => ->.
      + rewrite /TMem.tload Hwf3.
        by move: S2t; rewrite -EcfM /TMem.tload Hwf /= => ->. }
  case: (TProlog.ef_call_entry_run Hshape'
           (ltac:(by rewrite Pointer.inc_preserves_component)
            : Pointer.component (Pointer.inc pcW) = Cf)
           HrtC Hmscrf Etmf HcmF HnoscrF
           (ltac:(by move=> b0 Hb0; exact: (TMatch.vi_scrp HI Hb0))
            : forall b0, a Cf b0 <> Some 1)
           (Hu Cf) Hmj3 HtagC)
    => [tmem4 [rs4 [fbE [pcJ [spE
       [Pe [HfreshE HavoidE HfbE1 Hmj4 Hcap4]
           [Hw0 Ht0 Hw1 Ht1 Hw2]
           [Hpv4 Hpt4 EcJ [tlJ HcJ] [HONE4 HSP4 Hoth4 EFmk]]
           Htag4]]]]]].
  (* --- 6. the wrapper's [IJal] into the body --- *)
  have HcE0 : TMacros.code_at_I cde Cf pcE
      ([::] ++ ILabel plf
       :: ([:: IMov R_SP R_AUX1;
               IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
               IAlloc R_SP R_SP]
           ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
           ++ cbody ++ pop R_ARG ++ pop R_SP ++ [:: IJump])) by exact: HcE.
  case: (TMacros.code_at_I_label_find HcE0 EcE (Hu Cf))
    => [pcL [Hfl EcL HcL]].
  have SJ : TS.step cde (tmem4, rs4, pcJ, inc_pc_tag pct) E0
            (tmem4, Transitional.Register.set R_RA (Ptr (Pointer.inc pcJ))
                      InternalJump rs4, pcL, inc_pc_tag pct).
  { eapply TS.Jal.
    - exact: (TMacros.code_at_I_head HcJ).
    - by rewrite EcJ; exact: Hfl.
    - apply: PcJump; first exact: (TMacros.code_at_I_head HcL).
      by rewrite EcL EcJ. }
  set rs5 := Transitional.Register.set R_RA (Ptr (Pointer.inc pcJ))
               InternalJump rs4 in SJ *.
  have HnotReg4 : ~ List.In TInv.CReg
      (TInv.sites ((TInv.CMem (Cf, fbE, 2%Z), Ret n)
                   :: (TInv.CMem (C, fb, sp), InternalJump)
                   :: TStack.ledger_of Sl)).
  { move=> /= [E|[E|Hin]]; [by [] | by [] | ].
    move: Hin; rewrite TStack.sites_ledger_of
      => /List.in_map_iff [q [Eq _]]. by move: Eq. }
  have Htag5 := TInv.tag_inv_jal (Pointer.inc pcJ) HnotReg4 Htag4.
  (* --- 7. the body's prologue --- *)
  have HONE5 : Transitional.Register.get R_ONE rs5 = MVal Other (Int 1)
    by rewrite /rs5 TInv.get_set_neq //.
  have HcmF4 : exists cm, getm tmem4 Cf = Some cm.
  { case Hg: (getm tmem4 Cf) => [cm|]; first by exists cm.
    case: (Hcap4 0%Z (ltac:(by split; lia) :
             (0 <= 0 < Z.of_nat (4 + stack_need P_expr))%Z)) => [vv Hvv].
    by move: Hvv; rewrite /TMem.vload /Transitional.Memory.load /= Hg. }
  have HcL' : TMacros.code_at_I cde Cf pcL
      ([:: ILabel plf; IMov R_SP R_AUX1;
           IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
           IAlloc R_SP R_SP]
       ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
       ++ cbody ++ pop R_ARG ++ pop R_SP ++ [:: IJump]) by exact: HcL.
  have [nxtB [restB EB]] :=
    TDrain.nonempty_cons (TDrain.cat_nonempty (s1 := cbody)
      (ltac:(by []) : pop R_ARG ++ pop R_SP ++ [:: IJump] <> [::])).
  have HcL2 : TMacros.code_at_I cde Cf pcL
      ([:: ILabel plf; IMov R_SP R_AUX1;
           IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
           IAlloc R_SP R_SP]
       ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
       ++ nxtB :: restB) by rewrite -EB; exact: HcL'.
  case: (TProlog.prologue_run HcL2 EcL HONE5 HcmF4 Hmj4 Htag5)
    => [tmem5 [rs6 [fbN [pcF [Sp [HfreshN HavoidN Hmj5 Hcap5 Hpres5]
                                [Hsl0 Hsl1] [HONE6 HSP6 HARG6 HCOM6 HRA6]
                                [Htag6 EcF HcF]]]]]].
  (* --- 8. the transports, and the assembly --- *)
  have HfbN1 : fbN <> 1.
  { move=> E.
    have Hq : Pointer.component ((Cf, 1, 0%Z) : Pointer.t) <> Cf
              \/ Pointer.block ((Cf, 1, 0%Z) : Pointer.t) <> fbE
      by right=> Eb; apply: HfbE1; rewrite -Eb.
    have [w Hw] : exists w,
        Transitional.Memory.load tmem4 (Cf, 1, 0%Z) = Some w.
    { move: (Hpv4 _ Hq). rewrite /TMem.vload Hmscrf /=.
      case El: (Transitional.Memory.load tmem4 (Cf, 1, 0%Z)) => [w|] //= _.
      by exists w. }
    move: Hw; rewrite -E => Hw4. exact: (HfreshN 0%Z w Hw4). }
  have Lv5 : forall q,
      (Pointer.component q <> Cf \/ Pointer.block q <> fbE) ->
      (Pointer.component q <> Cf \/ Pointer.block q <> fbN) ->
      q <> ((C, fb, sp) : Pointer.t) ->
      q <> ((C, fb, (sp + 1)%Z) : Pointer.t) ->
      q <> ((C, 1, 0%Z) : Pointer.t) ->
      TMem.vload tmem5 q = TMem.vload tmem q.
  { move=> q HE HN H2 H3 H4.
    have E54 : TMem.vload tmem5 q = TMem.vload tmem4 q
      by rewrite /TMem.vload (Hpres5 q HN).
    have E30 : TMem.vload tmem3 q = TMem.vload tmem q
      by rewrite /TMem.vload (TMem.load_store_neq Hst3 H4)
                 (TMem.load_store_neq Hst2 H3) (TMem.load_store_neq Hst1 H2).
    by rewrite E54 (Hpv4 q HE) E30. }
  have Lt5 : forall q,
      (Pointer.component q <> Cf \/ Pointer.block q <> fbE) ->
      (Pointer.component q <> Cf \/ Pointer.block q <> fbN) ->
      q <> ((C, fb, sp) : Pointer.t) ->
      q <> ((C, fb, (sp + 1)%Z) : Pointer.t) ->
      q <> ((C, 1, 0%Z) : Pointer.t) ->
      TMem.tload tmem5 q = TMem.tload tmem q.
  { move=> q HE HN H2 H3 H4.
    have E54 : TMem.tload tmem5 q = TMem.tload tmem4 q
      by rewrite /TMem.tload (Hpres5 q HN).
    have E30 : TMem.tload tmem3 q = TMem.tload tmem q
      by rewrite /TMem.tload (TMem.load_store_neq Hst3 H4)
                 (TMem.load_store_neq Hst2 H3) (TMem.load_store_neq Hst1 H2).
    by rewrite E54 (Hpt4 q HE) E30. }
  have E45v : forall q,
      (Pointer.component q <> Cf \/ Pointer.block q <> fbN) ->
      TMem.vload tmem5 q = TMem.vload tmem4 q
    by move=> q H; rewrite /TMem.vload (Hpres5 q H).
  have E45t : forall q,
      (Pointer.component q <> Cf \/ Pointer.block q <> fbN) ->
      TMem.tload tmem5 q = TMem.tload tmem4 q
    by move=> q H; rewrite /TMem.tload (Hpres5 q H).
  have E45r : forall q,
      (Pointer.component q <> Cf \/ Pointer.block q <> fbN) ->
      Transitional.Memory.load tmem5 q = Transitional.Memory.load tmem4 q
    by move=> q H; exact: Hpres5.
  have Lv4 : forall q,
      (Pointer.component q <> Cf \/ Pointer.block q <> fbE) ->
      q <> ((C, fb, sp) : Pointer.t) ->
      q <> ((C, fb, (sp + 1)%Z) : Pointer.t) ->
      q <> ((C, 1, 0%Z) : Pointer.t) ->
      TMem.vload tmem4 q = TMem.vload tmem q.
  { move=> q HE H2 H3 H4.
    have E30 : TMem.vload tmem3 q = TMem.vload tmem q
      by rewrite /TMem.vload (TMem.load_store_neq Hst3 H4)
                 (TMem.load_store_neq Hst2 H3) (TMem.load_store_neq Hst1 H2).
    by rewrite (Hpv4 q HE) E30. }
  (* the callee's two fresh blocks are distinct, and neither is protected *)
  have HneNE : fbN <> fbE.
  { move=> E. case: (TMem.vload_load Hw0) => [w Hw].
    apply: (HfreshN 0%Z w). by rewrite E. }
  have Hprotl := TSM.stack_match_prot_loaded (TMatch.vi_stack HI).
  have HprotE : forall p, p \in prot -> p <> ((Cf, fbE) : Component.id * Block.id).
  { move=> p Hp E. case: (Hprotl p Hp) => [o [w Hw]].
    move: Hw; rewrite E /= => Hw.
    have Hw3 : Transitional.Memory.load tmem3 (Cf, fbE, o) = Some w.
    { rewrite (TMem.load_store_neq Hst3); last first.
      { by move=> Ex; apply: HneCf;
          move: (f_equal Pointer.component Ex) => /= <-. }
      apply: (Hpres2 _ _ _ _); last first.
      { by move=> Ex; apply: HneCf;
          move: (f_equal Pointer.component Ex) => /= <-. }
      apply: (Hpres1 _ _ Hw).
      by move=> Ex; apply: HneCf;
        move: (f_equal Pointer.component Ex) => /= <-. }
    exact: (HfreshE o w Hw3). }
  have HprotN : forall p, p \in prot -> p <> ((Cf, fbN) : Component.id * Block.id).
  { move=> p Hp E. case: (Hprotl p Hp) => [o [w Hw]].
    move: Hw; rewrite E /= => Hw.
    have Hv : TMem.vload tmem (Cf, fbN, o) = Some (Transitional.val w.1)
      by rewrite /TMem.vload Hw.
    have HqE : Pointer.component ((Cf, fbN, o) : Pointer.t) <> Cf
               \/ Pointer.block ((Cf, fbN, o) : Pointer.t) <> fbE
      by right; exact: HneNE.
    have Hq2 : ((Cf, fbN, o) : Pointer.t) <> (C, fb, sp)
      by move=> Ex; apply: HneCf;
         move: (f_equal Pointer.component Ex) => /= <-.
    have Hq3 : ((Cf, fbN, o) : Pointer.t) <> (C, fb, (sp + 1)%Z)
      by move=> Ex; apply: HneCf;
         move: (f_equal Pointer.component Ex) => /= <-.
    have Hq4 : ((Cf, fbN, o) : Pointer.t) <> (C, 1, 0%Z)
      by move=> Ex; apply: HneCf;
         move: (f_equal Pointer.component Ex) => /= <-.
    have Hv4 : TMem.vload tmem4 (Cf, fbN, o) = Some (Transitional.val w.1)
      by rewrite (Lv4 _ HqE Hq2 Hq3 Hq4).
    move: Hv4; rewrite /TMem.vload.
    case El: (Transitional.Memory.load tmem4 (Cf, fbN, o)) => [w4|] //= _.
    exact: (HfreshN o w4 El). }
  (* the chain's slots avoid every cell the call wrote *)
  have HslSl : TStack.slots_ok tmem Sl
    := TSM.stack_match_slots (TMatch.vi_stack HI).
  have Hsite : forall s0, List.In s0 Sl ->
      List.In (TInv.CMem (TStack.ra_addr s0))
              (TInv.sites (TStack.ledger_of Sl)).
  { move=> s0 Hs0. rewrite TStack.sites_ledger_of /TStack.addrs.
    apply/List.in_map_iff. exists (TStack.ra_addr s0). split; first by [].
    by apply/List.in_map_iff; exists s0. }
  have HslotFb : forall s0, List.In s0 Sl -> forall o : Z,
      TStack.ra_addr s0 <> ((C, fb, o) : Pointer.t).
  { move=> s0 Hs0 o E. apply: (vi_nosite HI (o := o)).
    apply: List.in_cons. by rewrite -E; exact: Hsite Hs0. }
  have HslotScr : forall s0, List.In s0 Sl ->
      TStack.ra_addr s0 <> ((C, 1, 0%Z) : Pointer.t).
  { move=> s0 Hs0 E. apply: Hnoscr. by right; rewrite -E; exact: Hsite Hs0. }
  have HslotNE : forall s0, List.In s0 Sl ->
      Pointer.component (TStack.ra_addr s0) <> Cf
      \/ Pointer.block (TStack.ra_addr s0) <> fbE.
  { move=> s0 Hs0.
    case: (@eqP _ (Pointer.component (TStack.ra_addr s0)) Cf) => [EC|HC];
      last by left.
    right=> EBs. case: (HslSl s0 Hs0) => [A _].
    case: (TMem.vload_load A) => [w Hw].
    have Hw3 : Transitional.Memory.load tmem3 (TStack.ra_addr s0) = Some w.
    { rewrite (TMem.load_store_neq Hst3 (HslotScr s0 Hs0)).
      apply: (Hpres2 _ _ _ (HslotFb s0 Hs0 _)).
      exact: (Hpres1 _ _ Hw (HslotFb s0 Hs0 _)). }
    apply: (HfreshE (Pointer.offset (TStack.ra_addr s0)) w).
    have -> : ((Cf, fbE, Pointer.offset (TStack.ra_addr s0)) : Pointer.t)
            = TStack.ra_addr s0 by rewrite -EC -EBs -TStack.ptr_expand.
    exact: Hw3. }
  have HslotNN : forall s0, List.In s0 Sl ->
      Pointer.component (TStack.ra_addr s0) <> Cf
      \/ Pointer.block (TStack.ra_addr s0) <> fbN.
  { move=> s0 Hs0.
    case: (@eqP _ (Pointer.component (TStack.ra_addr s0)) Cf) => [EC|HC];
      last by left.
    right=> EBs. case: (HslSl s0 Hs0) => [A _].
    have A4 : TMem.vload tmem4 (TStack.ra_addr s0)
            = Some (Ptr (TStack.ra_ret s0)).
    { rewrite (Lv4 _ (HslotNE s0 Hs0) (HslotFb s0 Hs0 _)
                 (HslotFb s0 Hs0 _) (HslotScr s0 Hs0)). exact: A. }
    move: A4; rewrite /TMem.vload.
    case El: (Transitional.Memory.load tmem4 (TStack.ra_addr s0))
      => [w4|] //= _.
    apply: (HfreshN (Pointer.offset (TStack.ra_addr s0)) w4).
    have -> : ((Cf, fbN, Pointer.offset (TStack.ra_addr s0)) : Pointer.t)
            = TStack.ra_addr s0 by rewrite -EC -EBs -TStack.ptr_expand.
    exact: El. }
  set sE := TStack.RASlot (Cf, fbE, 2%Z) (Pointer.inc pcC) (Ret n).
  set sNew := TStack.RASlot (C, fb, sp) ret InternalJump.
  set transit := Ptr (C, fb, (sp + 1 + 1)%Z).
  have Etr : (sp + 1 + 1)%Z = Z.of_nat (2 + size temps + 2)
    by rewrite /sp; lia.
  exists (setm scrs C transit), tmem5, rs6, pcF, cbody,
         (pop R_ARG ++ pop R_SP ++ [:: IJump]), sA, sB, fbN,
         ((Cf, fbE) :: (C, fb) :: prot), plmf, (Pointer.inc pcJ),
         (sE :: sNew :: Sl).
  split.
  - eapply star_plus_trans with (t1 := E0)
      (t2 := [:: ECall C P v Cf]); [exact: Sd | | by []].
    eapply plus_trans with (t1 := E0) (t2 := [:: ECall C P v Cf]);
      [exact: Pp1 | | by []].
    eapply plus_trans with (t1 := E0) (t2 := [:: ECall C P v Cf]);
      [exact: Pp2 | | by []].
    eapply plus_trans with (t1 := E0) (t2 := [:: ECall C P v Cf]);
      [exact: Pp3 | | by []].
    eapply plus_left with (t1 := [:: ECall C P v Cf]) (t2 := E0);
      [exact: SC | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: SL | | by []].
    eapply star_trans with (t1 := E0) (t2 := E0);
      [exact: (plus_star Pe) | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: SJ | | by []].
    exact: Sp.
  - apply: TMatch.ExprInv;
    last by eauto using TMatch.ei_anchor, TMatch.vi_anchor.
    + exact: Hplmf.
    + exact: HdomF.
    + exact: Hmj5.
    + case: (TMatch.vi_scrs HI) => [S1 S2 S3 S4].
      have HC0E : Pointer.component ((C, 1, 0%Z) : Pointer.t) <> Cf
                  \/ Pointer.block ((C, 1, 0%Z) : Pointer.t) <> fbE
        by left.
      have HC0N : Pointer.component ((C, 1, 0%Z) : Pointer.t) <> Cf
                  \/ Pointer.block ((C, 1, 0%Z) : Pointer.t) <> fbN
        by left.
      have HvC : TMem.vload tmem5 (C, 1, 0%Z) = Some transit
        by rewrite (E45v _ HC0N) (Hpv4 _ HC0E); exact: Hvsc.
      have HtC : TMem.tload tmem5 (C, 1, 0%Z) = Some Other
        by rewrite (E45t _ HC0N) (Hpt4 _ HC0E); exact: Htsc.
      have Hb1E : forall (C' : Component.id) (o : Z),
          Pointer.component ((C', 1, o) : Pointer.t) <> Cf
          \/ Pointer.block ((C', 1, o) : Pointer.t) <> fbE
        by move=> C' o; right=> Ex; apply: HfbE1; rewrite -Ex.
      have Hb1N : forall (C' : Component.id) (o : Z),
          Pointer.component ((C', 1, o) : Pointer.t) <> Cf
          \/ Pointer.block ((C', 1, o) : Pointer.t) <> fbN
        by move=> C' o; right=> Ex; apply: HfbN1; rewrite -Ex.
      have Hb1fb : forall (C' : Component.id) (o o' : Z),
          ((C', 1, o) : Pointer.t) <> (C, fb, o')
        by move=> C' o o' Ex; apply: Hfb1;
           move: (f_equal Pointer.block Ex) => /= <-.
      have Hb1C : forall (C' : Component.id), C' <> C ->
          ((C', 1, 0%Z) : Pointer.t) <> (C, 1, 0%Z)
        by move=> C' Hne Ex; apply: Hne;
           move: (f_equal Pointer.component Ex) => /= ->.
      split.
      * move=> C' u. rewrite setmE.
        case: (@eqP _ C' C) => [->|Hne] => [[<-]|Hg]; first exact: HvC.
        rewrite (@Lv5 (C', 1, 0%Z) (Hb1E _ _) (Hb1N _ _) (Hb1fb _ _ _)
                   (Hb1fb _ _ _) (Hb1C _ Hne)).
        exact: (S1 _ _ Hg).
      * have Hne10 : ((Component.main, 1, 1%Z) : Pointer.t) <> (C, 1, 0%Z)
          by move=> Ex; move: (f_equal Pointer.offset Ex) => /=; lia.
        case: S2 => [S2v S2t]. split.
        -- rewrite (@Lv5 (Component.main, 1, 1%Z) (Hb1E _ _) (Hb1N _ _)
                      (Hb1fb _ _ _) (Hb1fb _ _ _) Hne10).
           exact: S2v.
        -- rewrite (@Lt5 (Component.main, 1, 1%Z) (Hb1E _ _) (Hb1N _ _)
                      (Hb1fb _ _ _) (Hb1fb _ _ _) Hne10).
           exact: S2t.
      * move=> C' Hd. case: (@eqP _ C' C) => [->|Hne]; first by exists transit.
        case: (S3 _ Hd) => [u Hu']. exists u.
        rewrite (@Lv5 (C', 1, 0%Z) (Hb1E _ _) (Hb1N _ _) (Hb1fb _ _ _)
                   (Hb1fb _ _ _) (Hb1C _ Hne)).
        exact: Hu'.
      * move=> C' Hd. case: (@eqP _ C' C) => [->|Hne]; first exact: HtC.
        rewrite (@Lt5 (C', 1, 0%Z) (Hb1E _ _) (Hb1N _ _) (Hb1fb _ _ _)
                   (Hb1fb _ _ _) (Hb1C _ Hne)).
        exact: (S4 _ Hd).
    + exact: HONE6.
    + by rewrite HSP6.
    + rewrite HARG6 /rs5 TInv.get_set_neq // Hoth4 // /rsC
              TInv.get_set_neq // TInv.get_invalidateE //.
      by rewrite HCOM3; exact: VI_int.
    + by rewrite HRA6 /rs5 TInv.get_set_eq.
    + by [].
    + exact: EcF.
    + exact: Hcpl.
    + by rewrite EB.
    + apply: CMJ_base. exact: CM_stop.
    + exact: (TMatch.vi_uniq HI).
    + by split; [exact: HfbN1 | exact: HavoidN].
    + exact: (TMatch.vi_scrp HI).
    + by move=> ix; rewrite ltn0.
    + exact: Hcap5.
    + rewrite /= maxn0 add0n. by lia.
    + apply/negP => /orP [/eqP Ex|/orP [/eqP Ex|Hin]].
      * by apply: HneNE; move: (f_equal snd Ex) => /= ->.
      * by apply: HneFC; move: (f_equal fst Ex) => /= ->.
      * exact: (HprotN _ Hin erefl).
    + (* ---- the stack relation ---- *)
      (* the level the machine handed out is the chain's [Ret] count *)
      have Hlv : TStack.levels_ok Sl (level pct).
      { move: (TInv.ti_lvl (TMatch.vi_tag HI)).
        by rewrite /TMatch.ledger_at /TStack.levels_ok
                   -TStack.ledger_of_rets /= => H; exact: H. }
      have En : size (TStack.ext_levels Sl) = n
        by rewrite /n; exact: TStack.levels_ok_size Hlv.
      (* the caller-side transports, from just after each of its writes *)
      have Lv25 : forall q, Pointer.component q = C ->
          q <> ((C, 1, 0%Z) : Pointer.t) ->
          TMem.vload tmem5 q = TMem.vload tmem2 q.
      { move=> q Eq H4.
        have HD : Pointer.component q <> Cf \/ Pointer.block q <> fbE
          by left; rewrite Eq; exact: HneCf.
        have HD' : Pointer.component q <> Cf \/ Pointer.block q <> fbN
          by left; rewrite Eq; exact: HneCf.
        by rewrite (E45v _ HD') (Hpv4 _ HD) /TMem.vload
                   (TMem.load_store_neq Hst3 H4). }
      have Lt25 : forall q, Pointer.component q = C ->
          q <> ((C, 1, 0%Z) : Pointer.t) ->
          TMem.tload tmem5 q = TMem.tload tmem2 q.
      { move=> q Eq H4.
        have HD : Pointer.component q <> Cf \/ Pointer.block q <> fbE
          by left; rewrite Eq; exact: HneCf.
        have HD' : Pointer.component q <> Cf \/ Pointer.block q <> fbN
          by left; rewrite Eq; exact: HneCf.
        by rewrite (E45t _ HD') (Hpt4 _ HD) /TMem.tload
                   (TMem.load_store_neq Hst3 H4). }
      have HneSP : ((C, fb, sp) : Pointer.t) <> (C, fb, (sp + 1)%Z)
        by move=> Ex; move: (f_equal Pointer.offset Ex) => /=; lia.
      have Hsl1' : Transitional.Memory.load tmem2 (C, fb, sp)
                 = Some (Transitional.Register.get R_RA tregs,
                         {| vtag := InternalJump; color := C; entry := None;
                            is_code := false |})
        by rewrite (TMem.load_store_neq Hst2 HneSP).
      (* the two callee frames, at [tmem5] *)
      have HEN : forall o : Z,
          Pointer.component ((Cf, fbE, o) : Pointer.t) <> Cf
          \/ Pointer.block ((Cf, fbE, o) : Pointer.t) <> fbN
        by move=> o; right=> Ex; apply: HneNE; rewrite -Ex.
      have Hw0' : TMem.vload tmem5 (Cf, fbE, 0%Z)
                = Some (Transitional.val (Transitional.Register.get R_SP rsC))
        by rewrite (E45v _ (HEN 0%Z)).
      have Hw1' : TMem.vload tmem5 (Cf, fbE, 1%Z)
                = Some (Transitional.val mscrf.1)
        by rewrite (E45v _ (HEN 1%Z)).
      have Ht0' : TMem.tload tmem5 (Cf, fbE, 0%Z) = Some Other
        by rewrite (E45t _ (HEN 0%Z)).
      have Ht1' : TMem.tload tmem5 (Cf, fbE, 1%Z) = Some Other
        by rewrite (E45t _ (HEN 1%Z)).
      have Hw2' : Transitional.Memory.load tmem5 (Cf, fbE, 2%Z)
                = Some (Transitional.Register.get R_RA rsC,
                        {| vtag := Ret n; color := Cf; entry := None;
                           is_code := false |})
        by rewrite (E45r _ (HEN 2%Z)).
      have HRAC : Transitional.Register.get R_RA rsC
                = MVal (Ret n) (Ptr (Pointer.inc pcC))
        by rewrite /rsC TInv.get_set_eq.
      have HslE : TStack.slots_ok tmem5 [:: sE].
      { move=> s0 [Es0|//]. rewrite -Es0 /sE /=.
        by rewrite /TMem.vload /TMem.tload Hw2' HRAC. }
      (* whichever wrapper it was, [ef_call_entry_run] hands back the
         construction; all that is left is to show the frame survived the
         callee's prologue *)
      have HextF : TSM.ext_frame_match cde tmem5 Cf fbE (Pointer.inc pcJ)
                     spE sE.
      { apply: (EFmk tmem5 sE (ltac:(by []) :
                  TStack.ra_addr sE = ((Cf, fbE, 2%Z) : Pointer.t)) HslE).
        - by move=> o x Hx; rewrite (E45v _ (HEN o)).
        - by move=> o t Ht; rewrite (E45t _ (HEN o)). }
      (* the caller's own chain slot, and its argument slot *)
      have HneScr : forall o : Z, ((C, fb, o) : Pointer.t) <> (C, 1, 0%Z)
        by move=> o Ex; apply: Hfb1;
           move: (f_equal Pointer.block Ex) => /= ->.
      have HvNew : TMem.vload tmem5 (C, fb, sp) = Some (Ptr ret)
        by rewrite (@Lv25 (C, fb, sp) erefl (HneScr sp)) /TMem.vload Hsl1' /=
                   (TMatch.vi_ra HI).
      have HtNew : TMem.tload tmem5 (C, fb, sp) = Some InternalJump
        by rewrite (@Lt25 (C, fb, sp) erefl (HneScr sp)) /TMem.tload Hsl1' /=
                   (TMatch.vi_ra HI).
      have EARG1 : Transitional.Register.get R_ARG rs1
                 = Transitional.Register.get R_ARG tregs by rewrite Hoth1 //.
      have HvARG : TMem.vload tmem5 (C, fb, (sp + 1)%Z)
                 = Some (Transitional.val
                           (Transitional.Register.get R_ARG tregs))
        by rewrite (@Lv25 (C, fb, (sp + 1)%Z) erefl (HneScr _)) /TMem.vload
                   Hsl2 /= EARG1.
      have HtARG : TMem.tload tmem5 (C, fb, (sp + 1)%Z) = Some Other.
      { have -> : Other = tvtag (Transitional.Register.get R_ARG rs1)
          by rewrite (TInv.ti_regs Htag1 (r := R_ARG) (ltac:(by []))).
        by rewrite (@Lt25 (C, fb, (sp + 1)%Z) erefl (HneScr _)) /TMem.tload
                   Hsl2. }
      (* the chain below, and the caller's frame *)
      have HslSl5 : TStack.slots_ok tmem5 Sl.
      { move=> s0 Hs0. case: (HslSl s0 Hs0) => [A [B D]].
        split; last split; last exact: D.
        - by rewrite (@Lv5 _ (HslotNE s0 Hs0) (HslotNN s0 Hs0)
                        (HslotFb s0 Hs0 _) (HslotFb s0 Hs0 _)
                        (HslotScr s0 Hs0)).
        - by rewrite (@Lt5 _ (HslotNE s0 Hs0) (HslotNN s0 Hs0)
                        (HslotFb s0 Hs0 _) (HslotFb s0 Hs0 _)
                        (HslotScr s0 Hs0)). }
      have Hcap2' : TStack.frame_cap tmem2 C fb cap
        := TStack.frame_cap_store Hst2
             (TStack.frame_cap_store Hst1 (TMatch.vi_cap HI)).
      have Hcap5' : TStack.frame_cap tmem5 C fb cap.
      { move=> j Hj. case: (Hcap2' j Hj) => [u Hu2]. exists u.
        by rewrite (@Lv25 (C, fb, j) erefl (HneScr j)). }
      have Htemps5 : TStack.frame_temps tmem5 C fb temps.
      { move=> ix Hix. case: (TMatch.vi_temps HI Hix) => [Hv Ht].
        have HoA : ((C, fb, Z.of_nat (1 + size temps - ix)) : Pointer.t)
                 <> (C, fb, sp).
        { move=> Ex.
          have Eo : Z.of_nat (1 + size temps - ix) = sp
            := f_equal Pointer.offset Ex.
          move: Eo Hix; rewrite /sp. lia. }
        have HoB : ((C, fb, Z.of_nat (1 + size temps - ix)) : Pointer.t)
                 <> (C, fb, (sp + 1)%Z).
        { move=> Ex.
          have Eo : Z.of_nat (1 + size temps - ix) = (sp + 1)%Z
            := f_equal Pointer.offset Ex.
          move: Eo Hix; rewrite /sp. lia. }
        have HDE : Pointer.component
                     ((C, fb, Z.of_nat (1 + size temps - ix)) : Pointer.t)
                   <> Cf
                   \/ Pointer.block
                        ((C, fb, Z.of_nat (1 + size temps - ix)) : Pointer.t)
                      <> fbE by left.
        have HDN : Pointer.component
                     ((C, fb, Z.of_nat (1 + size temps - ix)) : Pointer.t)
                   <> Cf
                   \/ Pointer.block
                        ((C, fb, Z.of_nat (1 + size temps - ix)) : Pointer.t)
                      <> fbN by left.
        by split; [rewrite (@Lv5 _ HDE HDN HoA HoB (HneScr _))
                  |rewrite (@Lt5 _ HDE HDN HoA HoB (HneScr _))]. }
      (* the scratch map moves, then the memory *)
      have Hsm0 : TSM.stack_match cde labelsP a tmem (setm scrs C transit)
                    C fb prot stk ret Sl
        := TSM.stack_match_scrs_update transit (TMatch.vi_stack HI).
      have Hsm1 : TSM.stack_match cde labelsP a tmem
                    (setm (setm scrs C transit) Cf (Transitional.val mscrf.1))
                    C fb prot stk ret Sl.
      { case Hg: (getm scrs Cf) => [u|].
        - have Eu : u = Transitional.val mscrf.1.
          { case: (TMatch.vi_scrs HI) => [S1 _ _ _].
            move: (S1 _ _ Hg). rewrite /TMem.vload.
            case El: (Transitional.Memory.load tmem (Cf, 1, 0%Z))
              => [w|] //= [Ev].
            move: (Ltr3 _ _ El); rewrite Hmscrf => -[Ew]. by rewrite -Ev Ew. }
          have Hg' : getm (setm scrs C transit) Cf
                   = Some (Transitional.val mscrf.1)
            by rewrite setmE; case: eqP => [E|_];
               [case: (HneFC E) | rewrite Hg Eu].
          by rewrite (setmI Hg').
        - apply: (TSM.stack_match_scrs_extend (Transitional.val mscrf.1)
                    Hsm0).
          by rewrite setmE; case: eqP => [E|_]; [case: (HneFC E) | exact: Hg]. }
      have Hoff1 : (Pointer.component ((C, fb, sp) : Pointer.t),
                    Pointer.block ((C, fb, sp) : Pointer.t)) = (C, fb) ->
                   (2 <= Pointer.offset ((C, fb, sp) : Pointer.t))%Z
        by move=> _ /=; rewrite /sp; lia.
      have Hoff2 : (Pointer.component ((C, fb, (sp + 1)%Z) : Pointer.t),
                    Pointer.block ((C, fb, (sp + 1)%Z) : Pointer.t)) = (C, fb) ->
                   (2 <= Pointer.offset ((C, fb, (sp + 1)%Z) : Pointer.t))%Z
        by move=> _ /=; rewrite /sp; lia.
      have Hoff3 : (Pointer.component ((C, 1, 0%Z) : Pointer.t),
                    Pointer.block ((C, 1, 0%Z) : Pointer.t)) = (C, fb) ->
                   Z.le 2 (Pointer.offset ((C, 1, 0%Z) : Pointer.t))
        by move=> Ex; case: Hfb1; move: (f_equal snd Ex) => /= <-.
      have Hslots1 : TStack.slots_ok tmem1 Sl.
      { move=> s0 Hs0. case: (HslSl s0 Hs0) => [A [B D]].
        case: (TMem.vload_load A) => [w Hw].
        have Hw' := Hpres1 _ _ Hw (HslotFb s0 Hs0 _).
        split; last split; last exact: D.
        - by rewrite /TMem.vload Hw'; move: A; rewrite /TMem.vload Hw.
        - by rewrite /TMem.tload Hw'; move: B; rewrite /TMem.tload Hw. }
      have Hslots2 : TStack.slots_ok tmem2 Sl.
      { move=> s0 Hs0. case: (Hslots1 s0 Hs0) => [A [B D]].
        case: (TMem.vload_load A) => [w Hw].
        have Hw' := Hpres2 _ _ Hw (HslotFb s0 Hs0 _).
        split; last split; last exact: D.
        - by rewrite /TMem.vload Hw'; move: A; rewrite /TMem.vload Hw.
        - by rewrite /TMem.tload Hw'; move: B; rewrite /TMem.tload Hw. }
      have Hslots3 : TStack.slots_ok tmem3 Sl.
      { move=> s0 Hs0. case: (Hslots2 s0 Hs0) => [A [B D]].
        split; last split; last exact: D.
        - by rewrite /TMem.vload (TMem.load_store_neq Hst3 (HslotScr s0 Hs0)).
        - by rewrite /TMem.tload (TMem.load_store_neq Hst3 (HslotScr s0 Hs0)). }
      have HsmA := TSM.stack_match_store Hsm1 Hst1 (TMatch.vi_prot HI) Hoff1
                     Hslots1.
      have HsmB := TSM.stack_match_store HsmA Hst2 (TMatch.vi_prot HI) Hoff2
                     Hslots2.
      have Hnp1 : ((C, 1) : Component.id * Block.id) \notin prot.
      { apply/negP => Hin.
        exact: (TSM.stack_match_prot_nonscr (TMatch.vi_stack HI) Hin erefl). }
      have HsmC := TSM.stack_match_store HsmB Hst3 Hnp1 Hoff3 Hslots3.
      have HsmD : TSM.stack_match cde labelsP a tmem4
                    (setm (setm scrs C transit) Cf (Transitional.val mscrf.1))
                    C fb prot stk ret Sl.
      { apply: (TSM.stack_match_raw
                  (bad := fun p : Component.id * Block.id => p == (Cf, fbE))
                  _ _ _ _ HsmC).
        - move=> q /eqP Hq. apply: Hpv4.
          case: (@eqP _ (Pointer.component q) Cf) => [ECq|HCq]; last by left.
          by right=> EBq; apply: Hq; rewrite ECq EBq.
        - move=> q /eqP Hq. apply: Hpt4.
          case: (@eqP _ (Pointer.component q) Cf) => [ECq|HCq]; last by left.
          by right=> EBq; apply: Hq; rewrite ECq EBq.
        - by apply/eqP => Ex; apply: HneCf; move: (f_equal fst Ex) => /= ->.
        - by move=> p Hp; apply/eqP; exact: HprotE p Hp. }
      have HsmE : TSM.stack_match cde labelsP a tmem5
                    (setm (setm scrs C transit) Cf (Transitional.val mscrf.1))
                    C fb prot stk ret Sl.
      { apply: (TSM.stack_match_raw
                  (bad := fun p : Component.id * Block.id => p == (Cf, fbN))
                  _ _ _ _ HsmD).
        - move=> q /eqP Hq. rewrite /TMem.vload. apply: f_equal. apply: Hpres5.
          case: (@eqP _ (Pointer.component q) Cf) => [ECq|HCq]; last by left.
          by right=> EBq; apply: Hq; rewrite ECq EBq.
        - move=> q /eqP Hq. rewrite /TMem.tload. apply: f_equal. apply: Hpres5.
          case: (@eqP _ (Pointer.component q) Cf) => [ECq|HCq]; last by left.
          by right=> EBq; apply: Hq; rewrite ECq EBq.
        - by apply/eqP => Ex; apply: HneCf; move: (f_equal fst Ex) => /= ->.
        - by move=> p Hp; apply/eqP; exact: HprotN p Hp. }
      (* ---- and the constructor ---- *)
      apply: (@TSM.SM_external cde labelsP a tmem5 (setm scrs C transit)
                Cf C fbN fbE spE fb prot stk arg
                (Transitional.val (Transitional.Register.get R_ARG tregs))
                k rest0 temps plm (Pointer.inc pcJ) (Pointer.inc pcC)
                (Transitional.val mscrf.1)
                (Transitional.val (Transitional.Register.get R_ARG rs5))
                sE sNew Sl cap).
      * exact: HneCf.
      * exact: (TMatch.vi_plm HI).
      * exact: HextF.
      * by [].
      * by rewrite /sE /= En.
      * by split; [exact: HfbE1 | exact: HavoidE].
      * by rewrite /TMem.vload Hsl0 /= /rs5 TInv.get_set_neq // HSP4.
      * exact: Hw1'.
      * by rewrite /TMem.vload Hsl1.
      * by rewrite /TMem.tload Hsl0.
      * have -> : Other = tvtag (Transitional.Register.get R_ARG rs5)
          by rewrite (TInv.ti_regs Htag5 (r := R_ARG) (ltac:(by []))).
        by rewrite /TMem.tload Hsl1.
      * by rewrite /pcC /pc4 /pc2 !Pointer.inc_preserves_component.
      * exact: (TMacros.code_at_I_tail HcC).
      * exact: Hk.
      * exact: (TMatch.vi_priv HI).
      * exact: Htemps5.
      * by [].
      * by [].
      * move=> s0 [Es0|[Es0|Hin]]; last exact: HslSl5 Hin.
        -- rewrite -Es0 /sE /=.
           by rewrite /TMem.vload /TMem.tload Hw2' HRAC.
        -- rewrite -Es0 /sNew /=. by split; last split.
      * have -> : Z.of_nat (2 + size temps + 1) = (sp + 1)%Z
          by rewrite /sp; lia.
        exact: HvARG.
      * have -> : Z.of_nat (2 + size temps + 1) = (sp + 1)%Z
          by rewrite /sp; lia.
        exact: HtARG.
      * exact: (TMatch.vi_arg HI).
      * exact: Hcap5'.
      * move: (TMatch.vi_budget HI) => /=.
        set X := maxn (size temps + 2) (kneed k (size temps)).
        have HX : kneed k (size temps) <= X
          by rewrite /X leq_max leqnn orbT.
        move: HX. lia.
      * by rewrite setmE eqxx /transit Etr.
      * exact: (TMatch.vi_prot HI).
      * apply/negP => /orP [/eqP Ex|Hin].
        -- by apply: HneCf; move: (f_equal fst Ex) => /= <-.
        -- exact: (HprotE _ Hin erefl).
      * exact: HneNE.
      * exact: HsmE.
    + by move: Htag6; rewrite /TMatch.ledger_at /sE /sNew /=.
Qed.

(* ================================================================== *)
(* The exit — main's activation runs out                               *)
(* ================================================================== *)

(** An empty source stack under `Kstop` is main's initial activation finishing.
    The target still has work to do: the body's epilogue back into main's
    WRAPPER, and then the wrapper's own epilogue — whose closing `IBnz` reads
    the context marker, finds the `Int 0` that says "entered by the machine,
    not by a caller", and falls through to `IHalt`.

    This is the one diagram whose output is not an invariant but a `t_final`
    witness, and the only consumer of `SM_init`. *)
Lemma diagram_halt a scrs C mem v arg ret Sl tmem tregs pct pc fb prot
      temps plm rest cap :
  val_inv a scrs C [::] mem Kstop v arg ret InternalJump Sl tmem tregs pct pc
          fb prot temps plm rest cap ->
  exists tmem' tregs' pcH,
    [/\ plus TS.step cde (tmem, tregs, pc, pct) E0 (tmem', tregs', pcH, pct),
        TInject.minj a mem tmem'
      & exists tg c, Transitional.executing cde pcH Transitional.TrHalt tg c].
Proof.
  move=> HI.
  case: (vi_drain HI) => [pcD [rest1 [Sd _ HcD Ec Hcm']]].
  case: (cont_match_stop_inv Hcm') => [Erest Etemps].
  have HcE : TMacros.code_at_I cde C pcD (pop R_ARG ++ pop R_SP ++ [:: IJump])
    by rewrite -Erest.
  case: (TSM.stack_match_init_inv (TMatch.vi_stack HI))
    => [fb_ext [lret [v0 [v1 [vx [vs1
       [[EC Eprot ESl Hnefb] [L0 L1 T0 T1] [W0 W1 W2 W3 [TW0 TW1 TW3]]
        HprivE [Ecret Hcode]]]]]]]].
  (* [subst C] would orient against [Ec : Pointer.component pcD = C]; rewrite
     the three hypotheses that still mention [C] instead *)
  rewrite EC in HI HcE Ec. subst Sl. subst temps.
  (* --- the body's epilogue, back into main's wrapper --- *)
  have HSP2 : Transitional.Register.get R_SP tregs
            = MVal Other (Ptr (Component.main, fb, 2%Z))
    := TMatch.vi_sp HI.
  have HRA : Transitional.Register.get R_RA tregs
           = MVal InternalJump (Ptr ret)
    by rewrite (TMatch.vi_ra HI).
  have [w1 Hl1] := TMem.vload_load L1.
  have [w0 Hl0] := TMem.vload_load L0.
  have Et1 : tvtag w1.1 = Other
    by move: T1; rewrite /TMem.tload Hl1 /= => -[<-].
  have Et0 : tvtag w0.1 = Other
    by move: T0; rewrite /TMem.tload Hl0 /= => -[<-].
  have Ev0 : Transitional.val w0.1 = Ptr (Component.main, fb_ext, 4%Z)
    by move: L0; rewrite /TMem.vload Hl0 /= => -[<-].
  have Hns : forall o : Z,
      ~ List.In (TInv.CMem (Component.main, fb, o))
                (TInv.sites (TMatch.ledger_at InternalJump [::]))
    by exact: (vi_nosite HI).
  have Hexr : exists i0 tni,
      Transitional.executing cde ret i0 tni Component.main.
  { move: (TMacros.code_at_I_head Hcode); rewrite Ecret => Hx.
    by do 2!eexists; exact: Hx. }
  case: (TProlog.epilogue_run HcE Ec HSP2 (TMatch.vi_one HI) HRA Ecret Hexr
           Hl1 Et1 Hl0 Et0 Hns (TMatch.vi_cap HI) (TMatch.vi_mem HI)
           (TMatch.vi_tag HI))
    => [tmem1 [rs1 [Pe [Hv1 Ht1 Hraw1 Hcap1 Hmj1] [HARG1 HSPe Hothe] Htage]]].
  (* --- the wrapper's own epilogue, ending at [IHalt] --- *)
  have HSP1 : Transitional.Register.get R_SP rs1
            = MVal Other (Ptr (Component.main, fb_ext, 4%Z))
    by rewrite HSPe Ev0.
  have HONE1 : Transitional.Register.get R_ONE rs1 = MVal Other (Int 1)
    by rewrite Hothe //; exact: TMatch.vi_one HI.
  have [wM HlM] : exists w,
      Transitional.Memory.load tmem1 (Component.main, fb_ext, 3%Z) = Some w
    by case: (TMem.vload_load W3) => [w Hw]; exists w; rewrite Hraw1 //;
       move=> Ex; move: (f_equal Pointer.block Ex) => /= Eb;
       apply: Hnefb; rewrite Eb.
  have [wRA HlRA] : exists w,
      Transitional.Memory.load tmem1 (Component.main, fb_ext, 2%Z) = Some w
    by case: (TMem.vload_load W2) => [w Hw]; exists w; rewrite Hraw1 //;
       move=> Ex; move: (f_equal Pointer.block Ex) => /= Eb;
       apply: Hnefb; rewrite Eb.
  have [wsc Hlsc] : exists w,
      Transitional.Memory.load tmem1 (Component.main, fb_ext, 1%Z) = Some w
    by case: (TMem.vload_load W1) => [w Hw]; exists w; rewrite Hraw1 //;
       move=> Ex; move: (f_equal Pointer.block Ex) => /= Eb;
       apply: Hnefb; rewrite Eb.
  have [wSP HlSP] : exists w,
      Transitional.Memory.load tmem1 (Component.main, fb_ext, 0%Z) = Some w
    by case: (TMem.vload_load W0) => [w Hw]; exists w; rewrite Hraw1 //;
       move=> Ex; move: (f_equal Pointer.block Ex) => /= Eb;
       apply: Hnefb; rewrite Eb.
  have TW3' : TMem.tload tmem1 (Component.main, fb_ext, 3%Z) = Some Other
    by rewrite Ht1.
  have W3' : TMem.vload tmem1 (Component.main, fb_ext, 3%Z) = Some (Int 0)
    by rewrite Hv1.
  have TW1' : TMem.tload tmem1 (Component.main, fb_ext, 1%Z) = Some Other
    by rewrite Ht1.
  have TW0' : TMem.tload tmem1 (Component.main, fb_ext, 0%Z) = Some Other
    by rewrite Ht1.
  have EtM : tvtag wM.1 = Other
    by move: TW3'; rewrite /TMem.tload HlM /= => -[<-].
  have EvM : Transitional.val wM.1 = Int 0
    by move: W3'; rewrite /TMem.vload HlM /= => -[<-].
  have Etsc : tvtag wsc.1 = Other
    by move: TW1'; rewrite /TMem.tload Hlsc /= => -[<-].
  have EtSP : tvtag wSP.1 = Other
    by move: TW0'; rewrite /TMem.tload HlSP /= => -[<-].
  (* slot 2 is junk: the ledger has no memory site at all, so [ti_data]
     forbids a live tag there *)
  have HdeadRA : ~~ TInv.is_ret (tvtag wRA.1).
  { apply/negP => Hlive.
    have Ht : TMem.tload tmem1 (Component.main, fb_ext, 2%Z)
            = Some (tvtag wRA.1) by rewrite /TMem.tload HlRA.
    by case: (TInv.ti_data Htage Ht Hlive) => [//|]. }
  have [mscr Hmscr] : exists w,
      Transitional.Memory.load tmem1 (Component.main, 1, 0%Z) = Some w.
  { case: (TMatch.vi_scrs HI) => [_ _ S3 _].
    case: (S3 _ (TMatch.vi_dom HI)) => [u Hu].
    case: (TMem.vload_load Hu) => [w Hw]. exists w.
    have Hfb1 : fb <> 1 by case: (TMatch.vi_priv HI).
    rewrite Hraw1 //;
      by move=> Ex; apply: Hfb1; move: (f_equal Pointer.block Ex) => /= <-. }
  have HnotReg : ~ List.In TInv.CReg (TInv.sites (TStack.ledger_of [::]))
    by [].
  case: (TProlog.ef_halt_run Hcode Ecret HSP1 HONE1 HlM EtM EvM HlRA HdeadRA
           Hlsc Etsc HlSP EtSP Hmscr (proj1 HprivE) (proj2 HprivE) HnotReg
           (ltac:(by []) : forall o : Z,
              ~ List.In (TInv.CMem (Component.main, fb_ext, o))
                        (TInv.sites (TStack.ledger_of [::])))
           (ltac:(by []) : ~ List.In (TInv.CMem (Component.main, 1, 0%Z))
                             (TInv.sites (TStack.ledger_of [::])))
           (ltac:(by move=> b0 Hb0; exact: (TMatch.vi_scrp HI Hb0))
            : forall b0, a Component.main b0 <> Some 1)
           (ltac:(by []) : TInv.is_ret InternalJump = false)
           (ltac:(by move=> j []; lia) :
              TStack.frame_cap tmem1 Component.main fb_ext 0)
           Hmj1 Htage)
    => [tmem2 [rs2 [pcH [Ph Hmj2 Hex]]]].
  exists tmem2, rs2, pcH. split=> //.
  eapply star_plus_trans with (t1 := E0) (t2 := E0); [exact: Sd | | by []].
  eapply plus_trans with (t1 := E0) (t2 := E0); [exact: Pe | | by []].
  exact: Ph.
Qed.


(* ================================================================== *)
(* The DESCENDS — zero machine steps, pure re-association              *)
(* ================================================================== *)

(** The compiler emitted `c1 ++ <glue> ++ rest` for a compound expression, and
    the simulation reads that as "`c1` for the subexpression, with the glue
    absorbed into the continuation". No target step happens; the whole content
    is `TReplumb`'s re-association plus the budget arithmetic.

    Every field of `expr_inv` carries over untouched except the four that
    mention the expression — which is the point of having stated the invariant
    over an abstract `c`/`rest` pair in the first place. *)
Lemma expr_descend a scrs C stk mem k k' e e' arg ret Sl tmem tregs pct pc fb
      prot temps plm c c1 rest rest' s1 s2 sA sB cap :
  expr_inv a scrs C stk mem k e arg ret InternalJump Sl tmem tregs pct pc fb
           prot temps plm c rest s1 s2 cap ->
  compile_expr C (lbp C) (scr C) plm e' sA = Some (c1, sB) ->
  TMacros.code_at_I cde C pc (c1 ++ rest') ->
  cont_matchJ a C plm k' rest' temps ->
  3 + maxn (size temps + stack_need e') (kneed k' (size temps)) <= cap ->
  expr_inv a scrs C stk mem k' e' arg ret InternalJump Sl tmem tregs pct pc fb
           prot temps plm c1 rest' sA sB cap.
Proof.
  move=> HI Hcp Hcode Hcont Hbud.
  apply: TMatch.ExprInv;
    last by eauto using TMatch.ei_anchor, TMatch.vi_anchor.
  - exact: (TMatch.ei_plm HI).
  - exact: (TMatch.ei_dom HI).
  - exact: (TMatch.ei_mem HI).
  - exact: (TMatch.ei_scrs HI).
  - exact: (TMatch.ei_one HI).
  - exact: (TMatch.ei_sp HI).
  - exact: (TMatch.ei_arg HI).
  - exact: (TMatch.ei_ra HI).
  - by [].
  - exact: (TMatch.ei_pc HI).
  - exact: Hcp.
  - exact: Hcode.
  - exact: Hcont.
  - exact: (TMatch.ei_uniq HI).
  - exact: (TMatch.ei_priv HI).
  - exact: (TMatch.ei_scrp HI).
  - exact: (TMatch.ei_temps HI).
  - exact: (TMatch.ei_cap HI).
  - exact: Hbud.
  - exact: (TMatch.ei_prot HI).
  - exact: (TMatch.ei_stack HI).
  - exact: (TMatch.ei_tag HI).
Qed.

Local Notation Pcode C pc := (TMacros.code_at_I cde C pc).

Lemma descend_binop a scrs C stk mem k op e1 e2 arg ret Sl tmem tregs pct pc fb
      prot temps plm c rest s1 s2 cap :
  expr_inv a scrs C stk mem k (E_binop op e1 e2) arg ret InternalJump Sl tmem
           tregs pct pc fb prot temps plm c rest s1 s2 cap ->
  exists c1 rest' sA sB,
    expr_inv a scrs C stk mem (Kbinop1 op e2 k) e1 arg ret InternalJump Sl tmem
             tregs pct pc fb prot temps plm c1 rest' sA sB cap.
Proof.
  move=> HI.
  case: (TReplumb.binop1_replumb (P := Pcode C pc)
           (TMatch.ei_comp HI) (TMatch.ei_code HI) (TMatch.ei_cont HI))
    => [c1 [rest' [sA [sB [Hcp Hcode Hcont]]]]].
  exists c1, rest', sA, sB. apply: (expr_descend HI Hcp Hcode Hcont).
  by move: (TMatch.ei_budget HI) => /=; lia.
Qed.

Lemma descend_seq a scrs C stk mem k e1 e2 arg ret Sl tmem tregs pct pc fb
      prot temps plm c rest s1 s2 cap :
  expr_inv a scrs C stk mem k (E_seq e1 e2) arg ret InternalJump Sl tmem
           tregs pct pc fb prot temps plm c rest s1 s2 cap ->
  exists c1 rest' sA sB,
    expr_inv a scrs C stk mem (Kseq e2 k) e1 arg ret InternalJump Sl tmem
             tregs pct pc fb prot temps plm c1 rest' sA sB cap.
Proof.
  move=> HI.
  case: (TReplumb.seq1_replumb (P := Pcode C pc)
           (TMatch.ei_comp HI) (TMatch.ei_code HI) (TMatch.ei_cont HI))
    => [c1 [rest' [sA [sB [Hcp Hcode Hcont]]]]].
  exists c1, rest', sA, sB. apply: (expr_descend HI Hcp Hcode Hcont).
  by move: (TMatch.ei_budget HI) => /=; lia.
Qed.

Lemma descend_if a scrs C stk mem k e1 e2 e3 arg ret Sl tmem tregs pct pc fb
      prot temps plm c rest s1 s2 cap :
  expr_inv a scrs C stk mem k (E_if e1 e2 e3) arg ret InternalJump Sl tmem
           tregs pct pc fb prot temps plm c rest s1 s2 cap ->
  exists c1 rest' sA sB,
    expr_inv a scrs C stk mem (Kif e2 e3 k) e1 arg ret InternalJump Sl tmem
             tregs pct pc fb prot temps plm c1 rest' sA sB cap.
Proof.
  move=> HI.
  case: (TReplumb.if1_replumb (P := Pcode C pc)
           (TMatch.ei_comp HI) (TMatch.ei_code HI) (TMatch.ei_cont HI))
    => [c1 [rest' [sA [sB [Hcp Hcode Hcont]]]]].
  exists c1, rest', sA, sB. apply: (expr_descend HI Hcp Hcode Hcont).
  by move: (TMatch.ei_budget HI) => /=; lia.
Qed.

Lemma descend_alloc a scrs C stk mem k e arg ret Sl tmem tregs pct pc fb
      prot temps plm c rest s1 s2 cap :
  expr_inv a scrs C stk mem k (E_alloc e) arg ret InternalJump Sl tmem
           tregs pct pc fb prot temps plm c rest s1 s2 cap ->
  exists c1 rest' sA sB,
    expr_inv a scrs C stk mem (Kalloc k) e arg ret InternalJump Sl tmem
             tregs pct pc fb prot temps plm c1 rest' sA sB cap.
Proof.
  move=> HI.
  case: (TReplumb.alloc1_replumb (P := Pcode C pc)
           (TMatch.ei_comp HI) (TMatch.ei_code HI) (TMatch.ei_cont HI))
    => [c1 [rest' [sA [sB [Hcp Hcode Hcont]]]]].
  exists c1, rest', sA, sB. apply: (expr_descend HI Hcp Hcode Hcont).
  by move: (TMatch.ei_budget HI) => /=; lia.
Qed.

Lemma descend_deref a scrs C stk mem k e arg ret Sl tmem tregs pct pc fb
      prot temps plm c rest s1 s2 cap :
  expr_inv a scrs C stk mem k (E_deref e) arg ret InternalJump Sl tmem
           tregs pct pc fb prot temps plm c rest s1 s2 cap ->
  exists c1 rest' sA sB,
    expr_inv a scrs C stk mem (Kderef k) e arg ret InternalJump Sl tmem
             tregs pct pc fb prot temps plm c1 rest' sA sB cap.
Proof.
  move=> HI.
  case: (TReplumb.deref1_replumb (P := Pcode C pc)
           (TMatch.ei_comp HI) (TMatch.ei_code HI) (TMatch.ei_cont HI))
    => [c1 [rest' [sA [sB [Hcp Hcode Hcont]]]]].
  exists c1, rest', sA, sB. apply: (expr_descend HI Hcp Hcode Hcont).
  by move: (TMatch.ei_budget HI) => /=; lia.
Qed.

Lemma descend_assign a scrs C stk mem k e1 e2 arg ret Sl tmem tregs pct pc fb
      prot temps plm c rest s1 s2 cap :
  expr_inv a scrs C stk mem k (E_assign e1 e2) arg ret InternalJump Sl tmem
           tregs pct pc fb prot temps plm c rest s1 s2 cap ->
  exists c2 rest' sA sB,
    expr_inv a scrs C stk mem (Kassign1 e1 k) e2 arg ret InternalJump Sl tmem
             tregs pct pc fb prot temps plm c2 rest' sA sB cap.
Proof.
  move=> HI.
  case: (TReplumb.assign1_replumb (P := Pcode C pc)
           (TMatch.ei_comp HI) (TMatch.ei_code HI) (TMatch.ei_cont HI))
    => [c2 [rest' [sA [sB [Hcp Hcode Hcont]]]]].
  exists c2, rest', sA, sB. apply: (expr_descend HI Hcp Hcode Hcont).
  by move: (TMatch.ei_budget HI) => /=; lia.
Qed.

Lemma descend_call a scrs C stk mem k C' P' e arg ret Sl tmem tregs pct pc fb
      prot temps plm c rest s1 s2 cap :
  expr_inv a scrs C stk mem k (E_call C' P' e) arg ret InternalJump Sl tmem
           tregs pct pc fb prot temps plm c rest s1 s2 cap ->
  exists ce rest' sA sB,
    expr_inv a scrs C stk mem (Kcall C' P' k) e arg ret InternalJump Sl tmem
             tregs pct pc fb prot temps plm ce rest' sA sB cap.
Proof.
  move=> HI.
  case: (TReplumb.initcall_replumb (P := Pcode C pc)
           (TMatch.ei_comp HI) (TMatch.ei_code HI) (TMatch.ei_cont HI))
    => [ce [rest' [sA [sB [Hcp Hcode Hcont]]]]].
  exists ce, rest', sA, sB. apply: (expr_descend HI Hcp Hcode Hcont).
  by move: (TMatch.ei_budget HI) => /=; lia.
Qed.

End WithProgram.

End TDiagram.
