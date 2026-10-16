(** * Stage 4, part 1 — the macro archetype.

    See plan-i2t-redo.md §4 (Stage 4).

    Stage 4 is the bulk of the campaign: `S2I/Simulation.v` retargeted at T.
    This file builds the piece every one of its 14 diagrams will call, and it
    is the first thing to put the two halves of the work together:

      - `S2T/TSem.v`  — the machine steps  (Stage 1)
      - `S2T/TInv.v`  — the invariant transitions (Stage 2)

    A *macro lemma* does both at once: "executing this compiler macro from a
    state satisfying `tag_inv` reaches a state satisfying `tag_inv`, in this
    many steps". The diagrams then never touch a rule constructor or a
    `tag_inv` clause directly — they chain macro lemmas.

    `push R_RA` is the archetype, because it is the one that MOVES a
    capability. If the two halves fit here, they fit. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.
Require Import S2T.TMem.
Require Import S2T.TInv.
Require Import S2T.TLabel.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Require Import Coq.ZArith.ZArith.
Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.

Module TMacros.

Notation tcode := (seq (Transitional.instr * mem_tag)).

Lemma nth_error_cat_l' {A : Type} (l1 l2 : seq A) :
  List.nth_error (l1 ++ l2) (size l1) = List.nth_error l2 0.
Proof. by elim: l1. Qed.

Section WithCode.

Variable cde : Transitional.code.

(* ================================================================== *)
(* T9 — code_at over the flattened per-component array                *)
(* ================================================================== *)

Definition code_at (pc : Pointer.t) (c : tcode) : Prop :=
  exists C_code pre post,
    [/\ getm cde (Pointer.component pc) = Some C_code,
        C_code = pre ++ c ++ post
      & Pointer.offset pc = Z.of_nat (size pre)].

Lemma code_at_head pc i tg c :
  code_at pc ((i, tg) :: c) ->
  Transitional.executing cde pc i tg (Pointer.component pc).
Proof.
  move=> [C_code [pre [post [Hg Hc Hoff]]]].
  exists C_code. split; first by []. split; first by [].
  split; first by rewrite Hoff; lia.
  by rewrite Hoff Nat2Z.id Hc nth_error_cat_l'.
Qed.

Lemma code_at_tail pc x c :
  code_at pc (x :: c) -> code_at (Pointer.inc pc) c.
Proof.
  move=> [C_code [pre [post [Hg Hc Hoff]]]].
  exists C_code, (pre ++ [:: x]), post.
  split.
  - by rewrite Pointer.inc_preserves_component.
  - by rewrite Hc -catA.
  - rewrite /Pointer.inc. case: pc Hg Hoff => [[C b] o] /= _ ->.
    by rewrite size_cat /= Nat2Z.inj_add.
Qed.

(** T8: the successor obligation, discharged whenever the residual code has one
    more instruction. For compiled code that is always — every procedure ends
    with a control instruction, which carries no [check_pc] premise. *)
Lemma check_pc_at pc x y c :
  code_at pc (x :: y :: c) -> Transitional.check_pc cde pc x.2.
Proof.
  move=> H. have H1 := code_at_tail H.
  case: y H H1 => i tg _ /code_at_head Hex.
  by apply: PcFall Hex.
Qed.

(* ================================================================== *)
(* code_at for the IMAGE of Intermediate code                         *)
(* ================================================================== *)

(** `S2I/Simulation.v`'s `stack_match` and `cont_matchJ` pin residual code as
    Intermediate `code` (`code_at G ret (pop R_RA ++ rest')`). At T the same
    clauses hold of that code's IMAGE under the Pass-1 opcode map, so the
    retarget needs `code_at` in that form plus mirrors of
    `S2I/SimCode.v`'s four `code_at` lemmas (`:64`, `:74`, `:87`, `:95`).

    Note what this means for `cont_matchJ` itself: it mentions memory ZERO
    times — it relates a source continuation to Intermediate code and
    `val_inject`ed temps — so it needs **no port at all**. Only its consumption
    site changes, from `code_at` to `code_at_I`. *)
Definition code_at_I (C : Component.id) (pc : Pointer.t)
                     (c : Intermediate.Machine.code) : Prop :=
  code_at pc [seq Transitional.instr_to_transitional C i | i <- c].

Lemma code_at_I_head C pc i c :
  code_at_I C pc (i :: c) ->
  Transitional.executing cde pc
    (Transitional.instr_to_transitional C i).1
    (Transitional.instr_to_transitional C i).2 (Pointer.component pc).
Proof.
  rewrite /code_at_I /=.
  by case: (Transitional.instr_to_transitional C i) => x y /code_at_head.
Qed.

Lemma code_at_I_tail C pc i c :
  code_at_I C pc (i :: c) -> code_at_I C (Pointer.inc pc) c.
Proof. rewrite /code_at_I /=. exact: code_at_tail. Qed.

(** T8 at the [code_at_I] level. *)
Lemma check_pc_at_I C pc i j c :
  code_at_I C pc (i :: j :: c) ->
  Transitional.check_pc cde pc (Transitional.instr_to_transitional C i).2.
Proof.
  rewrite /code_at_I /=.
  by case: (Transitional.instr_to_transitional C i) => x y /check_pc_at.
Qed.

(* ================================================================== *)
(* The compiler's macros, viewed at T                                 *)
(* ================================================================== *)

(* the image of S2I's own [push]/[pop] under the Pass-1 opcode map — defining
   them this way is what keeps the file tied to the actual compiler *)
Definition push_T (C : Component.id) (r : register) : tcode :=
  [seq Transitional.instr_to_transitional C i | i <- push r].

Definition pop_T (C : Component.id) (r : register) : tcode :=
  [seq Transitional.instr_to_transitional C i | i <- pop r].

(** The bridge the diagrams actually use: compiled code is presented as
    Intermediate code via [code_at_I], while the macros ask for [push_T]/[pop_T]
    at [Pointer.component pc]. Both directions are definitional — [push_T C r]
    IS the image of [push r] — so these are just the [map]-over-[cat]
    bookkeeping, done once here instead of in every diagram. *)
Lemma code_at_I_push C pc r nxt rest :
  Pointer.component pc = C ->
  code_at_I C pc (push r ++ nxt :: rest) ->
  code_at pc (push_T (Pointer.component pc) r
              ++ Transitional.instr_to_transitional C nxt
                 :: [seq Transitional.instr_to_transitional C i | i <- rest]).
Proof. by move=> Hc; rewrite /code_at_I map_cat /= /push_T Hc. Qed.

Lemma code_at_I_pop C pc r nxt rest :
  Pointer.component pc = C ->
  code_at_I C pc (pop r ++ nxt :: rest) ->
  code_at pc (pop_T (Pointer.component pc) r
              ++ Transitional.instr_to_transitional C nxt
                 :: [seq Transitional.instr_to_transitional C i | i <- rest]).
Proof. by move=> Hc; rewrite /code_at_I map_cat /= /pop_T Hc. Qed.

(** ★ Where a forward [Bnz] lands. The T machine resolves a label by scanning
    the whole COMPONENT array from offset 0, so "the label is in the residual
    code" is not enough — it must be the ONLY one in the component. That is the
    premise here, in the form `S2I/LabelUniq.v`'s `compiled_labels_unique`
    produces (see `S2T/TLabel.v`). *)
Lemma code_at_I_label_find C pc c1 l rest :
  code_at_I C pc (c1 ++ ILabel l :: rest) ->
  Pointer.component pc = C ->
  (forall l0 C_code, getm cde C = Some C_code ->
     count (TLabel.is_tlabel l0) C_code <= 1) ->
  exists pcL,
    [/\ Transitional.find_label_in_comp cde C l = Some pcL,
        Pointer.component pcL = C
      & code_at_I C pcL (ILabel l :: rest)].
Proof.
  rewrite /code_at_I map_cat map_cons.
  move=> [C_code [pre [post [Hg Hc Hoff]]]] Hpc Hu.
  set img1 := [seq Transitional.instr_to_transitional C i | i <- c1].
  set imgr := [seq Transitional.instr_to_transitional C i | i <- rest].
  have HgC : getm cde C = Some C_code by rewrite -Hpc.
  have HcL : C_code = (pre ++ img1)
             ++ (Transitional.TrLabel (inl l), def_mem_tag C true)
                :: (imgr ++ post)
    by rewrite Hc -!catA.
  exists (C, 0, Z.of_nat (size (pre ++ img1))). split.
  - exact: (TLabel.find_label_in_comp_at HgC HcL (Hu l _ HgC)).
  - by [].
  - exists C_code, (pre ++ img1), post. by split.
Qed.

(* ================================================================== *)
(* Machine steps                                                      *)
(* ================================================================== *)

(** [push r], as two [TS] steps. Ported from the spike onto [TS.step]. *)
Lemma exec_push m rs pc pct r nxt c C0 fb0 sp m' vt :
  code_at pc (push_T (Pointer.component pc) r ++ nxt :: c) ->
  Transitional.Register.get_tag r rs = Some vt ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C0, fb0, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  R_SP <> r -> R_ONE <> r ->
  Pointer.component pc = C0 ->
  Transitional.Memory.store m (C0, fb0, sp)
    (Transitional.Register.get r rs,
     {| vtag := vt; color := C0; entry := None; is_code := false |})
    = Some m' ->
  plus TS.step cde (m, rs, pc, pct) E0
    (m',
     Transitional.Register.set R_SP (Ptr (C0, fb0, (sp + 1)%Z)) Other
       (Transitional.Register.set r
          (Transitional.val (Transitional.Register.get r rs))
          (moved_tag vt) rs),
     Pointer.inc (Pointer.inc pc), pct).
Proof.
  rewrite /push_T /= => Hcode Htag HSP HONE HrSP HrONE Hcomp Hstore.
  have Hc0 : code_at pc
    ((TrStore R_SP r, def_mem_tag (Pointer.component pc) true)
       :: (TrBinOp Add R_SP R_ONE R_SP,
           def_mem_tag (Pointer.component pc) true) :: nxt :: c)
    by exact: Hcode.
  eapply plus_left with (t1 := E0) (t2 := E0); [| | by []].
  - eapply TS.Store.
    + exact: (code_at_head Hc0).
    + exact: (check_pc_at Hc0).
    + by rewrite HSP.
    + by rewrite HSP.
    + by rewrite Hcomp.
    + exact: Htag.
    + by rewrite Hcomp in Hstore *; exact: Hstore.
  - apply: star_one.
    have Hc1 := code_at_tail Hc0.
    set rs1 := Transitional.Register.set r _ _ rs.
    have HSP1 : Transitional.Register.get R_SP rs1
              = MVal Other (Ptr (C0, fb0, sp))
      by rewrite /rs1 TInv.get_set_neq // HSP.
    have HONE1 : Transitional.Register.get R_ONE rs1 = MVal Other (Int 1)
      by rewrite /rs1 TInv.get_set_neq // HONE.
    (* [TS.BinOp] states its result inline, so the goal must be put into the
       rule's shape before applying it *)
    have -> : Ptr (C0, fb0, (sp + 1)%Z)
            = eval_binop Add
                (Transitional.val (Transitional.Register.get R_SP rs1))
                (Transitional.val (Transitional.Register.get R_ONE rs1))
      by rewrite HSP1 HONE1.
    eapply TS.BinOp.
    + exact: (code_at_head Hc1).
    + exact: (check_pc_at Hc1).
    + by rewrite HSP1.
    + by rewrite HONE1.
Qed.

(* ================================================================== *)
(* ★ The archetype: machine steps AND invariant transition            *)
(* ================================================================== *)

(** [push R_RA] — the macro that spills a live capability.

    This is the shape every Stage-4 diagram consumes: hypotheses about the
    source-derived state, a [plus] of target steps, and [tag_inv] carried
    across with the ledger updated. The diagram never sees a rule constructor
    or a [tag_inv] clause.

    Note what the proof is: [exec_push] for the steps, then
    [tag_inv_push_ra] followed by [tag_inv_setreg] for the invariant. The two
    halves compose without any glue — which is the thing this file exists to
    check. *)
Lemma push_ra_macro L m rs pc pct nxt c C0 fb0 sp m' t :
  code_at pc (push_T (Pointer.component pc) R_RA ++ nxt :: c) ->
  Pointer.component pc = C0 ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C0, fb0, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  Transitional.Register.get_tag R_RA rs = Some t ->
  TInv.is_live t ->
  ~ List.In (TInv.CMem (C0, fb0, sp)) (TInv.sites L) ->
  Transitional.Memory.store m (C0, fb0, sp)
    (Transitional.Register.get R_RA rs,
     {| vtag := t; color := C0; entry := None; is_code := false |})
    = Some m' ->
  TInv.tag_inv ((TInv.CReg, t) :: L) m rs pct ->
  let rs' := Transitional.Register.set R_SP (Ptr (C0, fb0, (sp + 1)%Z)) Other
               (Transitional.Register.set R_RA
                  (Transitional.val (Transitional.Register.get R_RA rs))
                  (moved_tag t) rs) in
    plus TS.step cde (m, rs, pc, pct) E0
      (m', rs', Pointer.inc (Pointer.inc pc), pct)
    /\ TInv.tag_inv ((TInv.CMem (C0, fb0, sp), t) :: L) m' rs' pct.
Proof.
  move=> Hcode Hcomp HSP HONE Htag Hlive Hfresh Hstore HI.
  have Et : tvtag (Transitional.Register.get R_RA rs) = t.
  { move: Htag.
    rewrite /Transitional.Register.get_tag /Transitional.Register.get.
    by case: (getm rs _) => [tv|] //= [] ->. }
  rewrite /=. split.
  - exact: (@exec_push m rs pc pct R_RA nxt c C0 fb0 sp m' t
              Hcode Htag HSP HONE (ltac:(by [])) (ltac:(by []))
              Hcomp Hstore).
  - apply: TInv.tag_inv_setreg; first by [].
    exact: (TInv.tag_inv_push_ra Et Hfresh Hstore HI).
Qed.

(** [pop r], as two [TS] steps: the [R_SP] decrement, then the load.

    Note the conclusion carries [m'], not [m]: T's [Load] writes the cell back
    retagged. That is Stage-0b's discovery, and it is harmless only because
    every memory clause of [tag_inv] goes through [TMem.vload] (Stage 2
    part 1). *)
Lemma exec_pop m rs pc pct r nxt c C0 fb0 sp v m' :
  code_at pc (pop_T (Pointer.component pc) r ++ nxt :: c) ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C0, fb0, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  Pointer.component pc = C0 ->
  Transitional.Memory.load m (C0, fb0, (sp - 1)%Z) = Some v ->
  Transitional.Memory.store m (C0, fb0, (sp - 1)%Z)
    ({| Transitional.val := Transitional.val v.1;
        tvtag := moved_tag (tvtag v.1) |},
     {| vtag := moved_tag (tvtag v.1);
        color := C0; entry := None; is_code := false |}) = Some m' ->
  plus TS.step cde (m, rs, pc, pct) E0
    (m',
     Transitional.Register.set r (Transitional.val v.1) (tvtag v.1)
       (Transitional.Register.set R_SP (Ptr (C0, fb0, (sp - 1)%Z)) Other rs),
     Pointer.inc (Pointer.inc pc), pct).
Proof.
  rewrite /pop_T /= => Hcode HSP HONE Hcomp Hload Hstore.
  have Hc0 : code_at pc
    ((TrBinOp Minus R_SP R_ONE R_SP,
      def_mem_tag (Pointer.component pc) true)
       :: (TrLoad R_SP r, def_mem_tag (Pointer.component pc) true)
       :: nxt :: c) by exact: Hcode.
  have Hcomp1 : Pointer.component (Pointer.inc pc) = C0
    by rewrite Pointer.inc_preserves_component.
  eapply plus_left with (t1 := E0) (t2 := E0); [| | by []].
  - eapply TS.BinOp.
    + exact: (code_at_head Hc0).
    + exact: (check_pc_at Hc0).
    + by rewrite HSP.
    + by rewrite HONE.
  - rewrite HSP HONE /=.
    apply: star_one.
    have Hc1 := code_at_tail Hc0.
    eapply TS.Load.
    + exact: (code_at_head Hc1).
    + exact: (check_pc_at Hc1).
    + by rewrite TInv.get_set_eq.
    + by rewrite TInv.get_set_eq.
    + by rewrite /= Hcomp1.
    + exact: Hload.
    + by rewrite Hcomp1; exact: Hstore.
Qed.

(** ★ [pop R_RA] — the mirror of [push_ra_macro]. The capability moves back
    from the spill slot into [R_RA], and the vacated cell is left
    [Invalidated], i.e. dead. *)
Lemma pop_ra_macro L m rs pc pct nxt c C0 fb0 sp v m' :
  code_at pc (pop_T (Pointer.component pc) R_RA ++ nxt :: c) ->
  Pointer.component pc = C0 ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C0, fb0, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  TInv.is_live (tvtag v.1) ->
  ~ List.In TInv.CReg (TInv.sites L) ->
  Transitional.Memory.load m (C0, fb0, (sp - 1)%Z) = Some v ->
  Transitional.Memory.store m (C0, fb0, (sp - 1)%Z)
    ({| Transitional.val := Transitional.val v.1; tvtag := moved_tag (tvtag v.1) |},
     {| vtag := moved_tag (tvtag v.1); color := C0; entry := None; is_code := false |})
    = Some m' ->
  TInv.tag_inv ((TInv.CMem (C0, fb0, (sp - 1)%Z), tvtag v.1) :: L) m rs pct ->
  let rs' := Transitional.Register.set R_RA (Transitional.val v.1) (tvtag v.1)
               (Transitional.Register.set R_SP
                  (Ptr (C0, fb0, (sp - 1)%Z)) Other rs) in
    plus TS.step cde (m, rs, pc, pct) E0
      (m', rs', Pointer.inc (Pointer.inc pc), pct)
    /\ TInv.tag_inv ((TInv.CReg, tvtag v.1) :: L) m' rs' pct.
Proof.
  move=> Hcode Hcomp HSP HONE Hlive HnotReg Hload Hstore HI.
  rewrite /=. split.
  - eapply exec_pop;
      [exact: Hcode | exact: HSP | exact: HONE | exact: Hcomp
      | exact: Hload | exact: Hstore].
  - apply: (TInv.tag_inv_pop_ra Hlive HnotReg Hload Hstore).
    by apply: TInv.tag_inv_setreg.
Qed.

(* ================================================================== *)
(* The data macros: ledger unchanged                                  *)
(* ================================================================== *)

(** [push r] for a DATA register — [push R_COM], [push R_ARG], [push R_AUX1],
    [push R_AUX2]. The stored cell is [Other]-tagged, so it is not a
    capability and the ledger is untouched. *)
Lemma push_data_macro L m rs pc pct r nxt c C0 fb0 sp m' :
  code_at pc (push_T (Pointer.component pc) r ++ nxt :: c) ->
  Pointer.component pc = C0 ->
  r <> R_RA -> R_SP <> r -> R_ONE <> r ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C0, fb0, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  Transitional.Register.get_tag r rs = Some Other ->
  ~ List.In (TInv.CMem (C0, fb0, sp)) (TInv.sites L) ->
  Transitional.Memory.store m (C0, fb0, sp)
    (Transitional.Register.get r rs,
     {| vtag := Other; color := C0; entry := None; is_code := false |})
    = Some m' ->
  TInv.tag_inv L m rs pct ->
  let rs' := Transitional.Register.set R_SP (Ptr (C0, fb0, (sp + 1)%Z)) Other
               (Transitional.Register.set r
                  (Transitional.val (Transitional.Register.get r rs))
                  Other rs) in
    plus TS.step cde (m, rs, pc, pct) E0
      (m', rs', Pointer.inc (Pointer.inc pc), pct)
    /\ TInv.tag_inv L m' rs' pct.
Proof.
  move=> Hcode Hcomp HrRA HSPr HONEr HSP HONE Htag Hfresh Hstore HI.
  have Et : tvtag (Transitional.Register.get r rs) = Other.
  { move: Htag.
    rewrite /Transitional.Register.get_tag /Transitional.Register.get.
    by case: (getm rs _) => [tv|] //= [] ->. }
  rewrite /=. split.
  - (* [is_address Other] computes, so the rule's shape IS the stated one *)
    exact: (@exec_push m rs pc pct r nxt c C0 fb0 sp m' Other
              Hcode Htag HSP HONE HSPr HONEr Hcomp Hstore).
  - apply: TInv.tag_inv_setreg; first by [].
    apply: TInv.tag_inv_setreg; first exact: HrRA.
    apply: (TInv.tag_inv_store_data Hfresh _ Hstore HI).
    by rewrite /= Et.
Qed.

(** [pop r] into a DATA register. The source cell must not be a live site —
    otherwise the pop would move a capability into a data register, which
    [ti_regs] forbids. Compiled code respects this by the push/pop
    bracketing. *)
Lemma pop_data_macro L m rs pc pct r nxt c C0 fb0 sp v m' :
  code_at pc (pop_T (Pointer.component pc) r ++ nxt :: c) ->
  Pointer.component pc = C0 ->
  r <> R_RA ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C0, fb0, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  tvtag v.1 = Other ->
  ~ List.In (TInv.CMem (C0, fb0, (sp - 1)%Z)) (TInv.sites L) ->
  Transitional.Memory.load m (C0, fb0, (sp - 1)%Z) = Some v ->
  Transitional.Memory.store m (C0, fb0, (sp - 1)%Z)
    ({| Transitional.val := Transitional.val v.1; tvtag := Other |},
     {| vtag := Other; color := C0; entry := None; is_code := false |})
    = Some m' ->
  TInv.tag_inv L m rs pct ->
  let rs' := Transitional.Register.set r (Transitional.val v.1) Other
               (Transitional.Register.set R_SP
                  (Ptr (C0, fb0, (sp - 1)%Z)) Other rs) in
    plus TS.step cde (m, rs, pc, pct) E0
      (m', rs', Pointer.inc (Pointer.inc pc), pct)
    /\ TInv.tag_inv L m' rs' pct.
Proof.
  move=> Hcode Hcomp HrRA HSP HONE Ev Hfresh Hload Hstore HI.
  have Hstore' : Transitional.Memory.store m (C0, fb0, (sp - 1)%Z)
      ({| Transitional.val := Transitional.val v.1;
          tvtag := moved_tag (tvtag v.1) |},
       {| vtag := moved_tag (tvtag v.1);
          color := C0; entry := None; is_code := false |}) = Some m'
    by rewrite Ev /=; exact: Hstore.
  rewrite /=. split.
  - have H := @exec_pop m rs pc pct r nxt c C0 fb0 sp v m'
                Hcode HSP HONE Hcomp Hload Hstore'.
    rewrite Ev in H. exact: H.
  - apply: (TInv.tag_inv_load_data HrRA Ev Hfresh Hload Hstore).
    by apply: TInv.tag_inv_setreg.
Qed.

(* ================================================================== *)
(* The control transfers                                              *)
(* ================================================================== *)

(* ================================================================== *)
(* The intra-component call bracket — the first diagram's skeleton     *)
(* ================================================================== *)

End WithCode.

End TMacros.
