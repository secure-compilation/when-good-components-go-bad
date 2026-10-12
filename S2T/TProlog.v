(** * Stage 4, part 6 — the callee prologue at T.

    See plan-i2t-redo.md §4 (Stage 4).

    `S2I/Simulation.v:2698`'s `internal_prologue_run` executes the whole body
    prologue in one lemma. Here it is split at the allocation, because that is
    where the content is:

        ILabel plf ; IMov R_SP R_AUX1 ; IConst (4+ne) R_SP ; IAlloc R_SP R_SP
        ------------------------------------------------- prologue_alloc_run
        push R_AUX1 ; push R_ARG ; IMov R_COM R_ARG
        ------------------------------------------------- (next)

    The first half is where the four alloc lemmas land — `tag_inv_alloc`,
    `minj_alloc`, `alloc_frame_cap`, `alloc_fresh_outside` — each of which had
    to be added first, and three of which did not exist a few increments ago. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.
Require Import S2I.SimInject.
Require Import S2I.Simulation.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.
Require Import S2T.TMem.
Require Import S2T.TInv.
Require Import S2T.TInject.
Require Import S2T.TStack.
Require Import S2T.TLabel.
Require Import S2T.TMacros.
Require Import S2T.TStackMatch.

Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Require Import Coq.ZArith.ZArith.
From mathcomp Require Import zify.
Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.

Module TProlog.

Notation icode := Intermediate.Machine.code.

Section WithCode.

Variable cde : Transitional.code.

(** ★ The prologue up to and including the frame allocation.

    Register discipline: only [R_SP] and [R_AUX1] move ([R_AUX1] receives the
    caller's [R_SP], which the first push will spill), so everything else —
    crucially [R_RA], carrying the activation's return capability — is
    untouched. That is stated as one clause rather than four. *)
Lemma prologue_alloc_run Cf ne nxt rest a mem tmemIn regsIn pct pc0 L :
  TMacros.code_at_I cde Cf pc0
    ([:: IMov R_SP R_AUX1;
         IConst (IInt (Z.of_nat (4 + ne))) R_SP;
         IAlloc R_SP R_SP] ++ nxt :: rest) ->
  Pointer.component pc0 = Cf ->
  tvtag (Transitional.Register.get R_SP regsIn) = Other ->
  (exists cm, getm tmemIn Cf = Some cm) ->
  TInject.minj a mem tmemIn ->
  TInv.tag_inv L tmemIn regsIn pct ->
  exists tmem1 regs3 fbN,
    [/\ star TS.step cde (tmemIn, regsIn, pc0, pct) E0
             (tmem1, regs3,
              Pointer.inc (Pointer.inc (Pointer.inc pc0)), pct),
        [/\ (forall (o : Z) w,
               Transitional.Memory.load tmemIn (Cf, fbN, o) = Some w -> False),
            (forall b0, a Cf b0 <> Some fbN),
            (* no ledger site is in the fresh frame — the premise the pushes
               need, and already proved here for [tag_inv_alloc] — together
               with the fact that nothing OUTSIDE the fresh frame moved *)
            ((forall o : Z, ~ List.In (TInv.CMem (Cf, fbN, o)) (TInv.sites L))
             /\ (forall q, Pointer.component q <> Cf \/ Pointer.block q <> fbN ->
                    Transitional.Memory.load tmem1 q
                    = Transitional.Memory.load tmemIn q)),
            TInject.minj a mem tmem1
          & TStack.frame_cap tmem1 Cf fbN (4 + ne)],
        [/\ Transitional.Register.get R_SP regs3
              = MVal Other (Ptr (Cf, fbN, 0%Z)),
            Transitional.Register.get R_AUX1 regs3
              = MVal Other
                  (Transitional.val (Transitional.Register.get R_SP regsIn))
          & forall r, r <> R_SP -> r <> R_AUX1 ->
              Transitional.Register.get r regs3
              = Transitional.Register.get r regsIn]
      & TInv.tag_inv L tmem1 regs3 pct].
Proof.
  move=> Hcode Hcomp HSPt [cm HcmF] HI Htag.
  (* --- the four code cells --- *)
  have Hc0 := Hcode.
  have Hc1 := TMacros.code_at_I_tail Hc0.
  have Hc2 := TMacros.code_at_I_tail Hc1.
  (* --- the allocation succeeds, and its size is the frame size --- *)
  have Hsz : (Z.of_nat (4 + ne) > 0)%Z by lia.
  have Ento : Z.to_nat (Z.of_nat (4 + ne)) = 4 + ne by rewrite Nat2Z.id.
  have [tmem1 [fbN Halloc]] :
    exists tmem1 fbN,
      Transitional.Memory.alloc tmemIn Cf (Z.to_nat (Z.of_nat (4 + ne)))
      = Some (tmem1, (Cf, fbN, 0%Z)).
  { rewrite /Transitional.Memory.alloc HcmF /=.
    by eexists; eexists. }
  (* the fresh block is unloadable in the OLD memory — used twice below *)
  have Hfresh : forall (o : Z) w,
      Transitional.Memory.load tmemIn (Cf, fbN, o) = Some w -> False.
  { move=> o w. exact: (TStack.alloc_fresh_unloadable HI Halloc). }
  (* …hence no ledger entry lives there: entries are loadable *)
  have Hnoblk : forall q t, List.In (TInv.CMem q, t) L ->
      Pointer.component q <> Cf \/ Pointer.block q <> fbN.
  { move=> q t Hin.
    case: (@eqP _ (Pointer.component q) Cf) => [EC|HC]; last by left.
    case: (@eqP _ (Pointer.block q) fbN) => [EB|HB]; last by right.
    move: (TInv.ti_site Htag Hin). rewrite /TInv.tagat /TMem.tload.
    case Hl: (Transitional.Memory.load tmemIn q) => [w|] //= _.
    by case: (Hfresh (Pointer.offset q) w);
       rewrite -EC -EB -TStack.ptr_expand. }
  have Hnosite : forall o : Z,
      ~ List.In (TInv.CMem (Cf, fbN, o)) (TInv.sites L).
  { move=> o /TInv.in_sites_pair [t Hin].
    by case: (Hnoblk _ _ Hin). }
  exists tmem1,
    (Transitional.Register.set R_SP (Ptr (Cf, fbN, 0%Z)) Other
      (Transitional.Register.set R_SP (Int (Z.of_nat (4 + ne))) Other
        (Transitional.Register.set R_SP
           (Transitional.val (Transitional.Register.get R_SP regsIn))
           (if is_address (tvtag (Transitional.Register.get R_SP regsIn))
            then Invalidated else Other)
          (Transitional.Register.set R_AUX1
             (Transitional.val (Transitional.Register.get R_SP regsIn))
             (tvtag (Transitional.Register.get R_SP regsIn)) regsIn)))), fbN.
  split.
  - (* --- the three steps --- *)
    eapply star_step with (t1 := E0) (t2 := E0); [| | by []].
    { eapply TS.Mov; [exact: (TMacros.code_at_I_head Hc0)
                     | exact: (TMacros.check_pc_at_I Hc0)]. }
    eapply star_step with (t1 := E0) (t2 := E0); [| | by []].
    { eapply TS.Const; [exact: (TMacros.code_at_I_head Hc1)
                       | exact: (TMacros.check_pc_at_I Hc1)]. }
    eapply star_step with (t1 := E0) (t2 := E0); [| | by []].
    { eapply TS.Alloc.
      - exact: (TMacros.code_at_I_head Hc2).
      - exact: (TMacros.check_pc_at_I Hc2).
      - by rewrite TInv.get_set_eq.
      - by rewrite TInv.get_set_eq.
      - exact: Hsz.
      - rewrite !Pointer.inc_preserves_component Hcomp. exact: Halloc. }
    exact: star_refl.
  - (* --- the memory facts --- *)
    split.
    + exact: Hfresh.
    + move=> b0. exact: (TInject.alloc_fresh_outside HI Halloc).
    + split; first exact: Hnosite.
      move=> q Hne. exact: (TStack.load_alloc_other Halloc Hne).
    + exact: (TStack.minj_alloc HI Halloc).
    + rewrite -Ento. exact: (TStack.alloc_frame_cap Halloc).
  - (* --- the register facts --- *)
    split.
    + by rewrite TInv.get_set_eq.
    + rewrite TInv.get_set_neq // TInv.get_set_neq // TInv.get_set_neq //.
      by rewrite TInv.get_set_eq HSPt.
    + move=> r H1 H2.
      by rewrite !TInv.get_set_neq //.
  - (* --- tag_inv --- *)
    rewrite HSPt /=.
    apply: TInv.tag_inv_setreg; first by [].
    apply: TInv.tag_inv_setreg; first by [].
    apply: TInv.tag_inv_setreg; first by [].
    apply: TInv.tag_inv_setreg; first by [].
    exact: (TStack.tag_inv_alloc Halloc Hnoblk Htag).
Qed.



(** ★ One data push, with its output state described by FACTS rather than by
    the explicit nest of [Register.set]s that [push_data_macro] returns.

    This is the same move [prologue_alloc_run] makes, and for the same reason:
    a diagram that chains four macros otherwise carries a four-deep [set] term
    through every subsequent rewrite. It also absorbs two obligations the
    caller would otherwise repeat at every push — that the target cell is
    storable (from [frame_cap]) and that the injection survives (from
    [minj_store_outside]). *)
Lemma push_data_run C fb sp r cap a mem m rs pc pct L tl :
  (* the tail is an arbitrary NONEMPTY list, not a literal cons: a diagram has
     it as [cd ++ pop R_AUX1 ++ …] with [cd] a variable, which would not unify
     with [nxt :: rest] *)
  TMacros.code_at_I cde C pc (push r ++ tl) ->
  tl <> [::] ->
  Pointer.component pc = C ->
  r <> R_RA -> R_SP <> r -> R_ONE <> r ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C, fb, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  (0 <= sp < Z.of_nat cap)%Z ->
  TStack.frame_cap m C fb cap ->
  ~ List.In (TInv.CMem (C, fb, sp)) (TInv.sites L) ->
  (forall b, a C b <> Some fb) ->
  TInject.minj a mem m ->
  TInv.tag_inv L m rs pct ->
  exists m' rs',
    [/\ plus TS.step cde (m, rs, pc, pct) E0
             (m', rs', Pointer.inc (Pointer.inc pc), pct),
        [/\ Transitional.Memory.load m' (C, fb, sp)
              = Some (Transitional.Register.get r rs,
                      {| vtag := Other; color := C; entry := None;
                         is_code := false |}),
            (forall q w, Transitional.Memory.load m q = Some w ->
               q <> (C, fb, sp) -> Transitional.Memory.load m' q = Some w),
            (* the store itself, so the caller can use the store-shaped
               transport lemmas ([scrs_ok_store], [stack_match_store], …) *)
            Transitional.Memory.store m (C, fb, sp)
              (Transitional.Register.get r rs,
               {| vtag := Other; color := C; entry := None;
                  is_code := false |}) = Some m',
            TStack.frame_cap m' C fb cap
          & TInject.minj a mem m'],
        [/\ Transitional.Register.get R_SP rs'
              = MVal Other (Ptr (C, fb, (sp + 1)%Z)),
            Transitional.Register.get r rs'
              = MVal Other (Transitional.val (Transitional.Register.get r rs))
          & forall r', r' <> R_SP -> r' <> r ->
              Transitional.Register.get r' rs'
              = Transitional.Register.get r' rs]
      & TInv.tag_inv L m' rs' pct].
Proof.
  move=> Hcode Htl Hcomp HrRA HSPr HONEr HSP HONE Hsp Hcap Hnosite Havoid HI
         Htag.
  case: tl Hcode Htl => [|nxt rest] Hcode _ //.
  have HrSP : r <> R_SP by move=> E; apply: HSPr; rewrite E.
  (* the cell is in the frame, hence loadable, hence storable *)
  have [w Hw] : exists w, Transitional.Memory.load m (C, fb, sp) = Some w
    by case: (Hcap sp Hsp) => [v Hv]; exact: (TMem.vload_load Hv).
  case: (TMem.store_after_load
           (Transitional.Register.get r rs,
            {| vtag := Other; color := C; entry := None; is_code := false |})
           Hw) => [m' Hst].
  have Hrt : Transitional.Register.get_tag r rs = Some Other.
  { apply: (TInv.ti_tag_other Htag). exact: HrRA. }
  case: (TMacros.push_data_macro (TMacros.code_at_I_push Hcomp Hcode)
           Hcomp HrRA HSPr HONEr HSP HONE Hrt Hnosite Hst Htag)
    => [Sp Htag'].
  eexists; eexists. split; first exact: Sp.
  - split.
    + exact: (TMem.load_store_eq Hst).
    + move=> q w' Hq Hne.
      by rewrite (TMem.load_store_neq Hst Hne); exact: Hq.
    + exact: Hst.
    + exact: (TStack.frame_cap_store Hst Hcap).
    + apply: (TInject.minj_store_outside _ Hst HI) => b.
      exact: Havoid b.
  - split.
    + by rewrite TInv.get_set_eq.
    + by rewrite TInv.get_set_neq // TInv.get_set_eq.
    + move=> r' H1 H2. by rewrite !TInv.get_set_neq //.
  - exact: Htag'.
Qed.

(** ★ One CAPABILITY push — the caller spilling its own return address before
    an [IJal]. The mirror of [pop_ra_run], and the only push whose ledger entry
    MOVES: `(CReg, t)` becomes `(CMem (C, fb, sp), t)`, and [R_RA] is left
    [Invalidated] so the capability is not duplicated.

    That duplication check is the whole point of the ledger: `ti_uniq` would be
    violated if the rule kept [R_RA] live, and the machine's [Store] rule is
    what enforces it — the register write-back is part of the rule, not of the
    invariant. *)
Lemma push_ra_run C fb sp cap a mem m rs pc pct L tl t :
  TMacros.code_at_I cde C pc (push R_RA ++ tl) ->
  tl <> [::] ->
  Pointer.component pc = C ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C, fb, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  Transitional.Register.get_tag R_RA rs = Some t ->
  TInv.is_live t ->
  (0 <= sp < Z.of_nat cap)%Z ->
  TStack.frame_cap m C fb cap ->
  ~ List.In (TInv.CMem (C, fb, sp)) (TInv.sites L) ->
  (forall b, a C b <> Some fb) ->
  TInject.minj a mem m ->
  TInv.tag_inv ((TInv.CReg, t) :: L) m rs pct ->
  exists m' rs',
    [/\ plus TS.step cde (m, rs, pc, pct) E0
             (m', rs', Pointer.inc (Pointer.inc pc), pct),
        [/\ Transitional.Memory.load m' (C, fb, sp)
              = Some (Transitional.Register.get R_RA rs,
                      {| vtag := t; color := C; entry := None;
                         is_code := false |}),
            (forall q w, Transitional.Memory.load m q = Some w ->
               q <> (C, fb, sp) -> Transitional.Memory.load m' q = Some w),
            Transitional.Memory.store m (C, fb, sp)
              (Transitional.Register.get R_RA rs,
               {| vtag := t; color := C; entry := None;
                  is_code := false |}) = Some m',
            TStack.frame_cap m' C fb cap
          & TInject.minj a mem m'],
        [/\ Transitional.Register.get R_SP rs'
              = MVal Other (Ptr (C, fb, (sp + 1)%Z)),
            Transitional.Register.get R_RA rs'
              = MVal Invalidated
                  (Transitional.val (Transitional.Register.get R_RA rs))
          & forall r', r' <> R_SP -> r' <> R_RA ->
              Transitional.Register.get r' rs'
              = Transitional.Register.get r' rs]
      & TInv.tag_inv ((TInv.CMem (C, fb, sp), t) :: L) m' rs' pct].
Proof.
  move=> Hcode Htl Hcomp HSP HONE Hrt Hlive Hsp Hcap Hnosite Havoid HI Htag.
  case: tl Hcode Htl => [|nxt rest] Hcode _ //.
  have [w Hw] : exists w, Transitional.Memory.load m (C, fb, sp) = Some w
    by case: (Hcap sp Hsp) => [v Hv]; exact: (TMem.vload_load Hv).
  case: (TMem.store_after_load
           (Transitional.Register.get R_RA rs,
            {| vtag := t; color := C; entry := None; is_code := false |})
           Hw) => [m' Hst].
  case: (TMacros.push_ra_macro (TMacros.code_at_I_push Hcomp Hcode)
           Hcomp HSP HONE Hrt Hlive Hnosite Hst Htag) => [Sp Htag'].
  eexists; eexists. split; first exact: Sp.
  - split.
    + exact: (TMem.load_store_eq Hst).
    + move=> q w' Hq Hne.
      by rewrite (TMem.load_store_neq Hst Hne); exact: Hq.
    + exact: Hst.
    + exact: (TStack.frame_cap_store Hst Hcap).
    + apply: (TInject.minj_store_outside _ Hst HI) => b. exact: Havoid b.
  - split.
    + by rewrite TInv.get_set_eq.
    + by rewrite TInv.get_set_neq // TInv.get_set_eq.
    + move=> r' H1 H2. by rewrite !TInv.get_set_neq //.
  - exact: Htag'.
Qed.

(** ★ [store_arg (scr C) R_SP R_AUX2] — the caller PARKING its stack pointer in
    the scratch cell across a cross-component call.

    [ICall] invalidates the register file, so [R_SP] cannot survive in a
    register; the per-component scratch cell is where it goes, and
    [icall_resume_run] is what takes it back out. Two steps, and the only
    obligation beyond the store is that the cell is not a ledger site: it takes
    DATA, and [ti_data] would otherwise have to explain a live capability
    appearing where the ledger has none.

    Note the [Store] rule ALSO writes the source register back, retagged. For
    an [Other] operand that is the identity — the same observation that makes
    the data pops free. *)
Lemma store_sp_run C fb sp a mem m rs pc pct L tl mscr :
  TMacros.code_at_I cde C pc (store_arg (scr C) R_SP R_AUX2 ++ tl) ->
  tl <> [::] ->
  Pointer.component pc = C ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C, fb, sp)) ->
  Transitional.Memory.load m (C, 1, 0%Z) = Some mscr ->
  ~ List.In (TInv.CMem (C, 1, 0%Z)) (TInv.sites L) ->
  (forall b0, a C b0 <> Some 1) ->
  TInject.minj a mem m ->
  TInv.tag_inv L m rs pct ->
  exists m' rs',
    [/\ plus TS.step cde (m, rs, pc, pct) E0
             (m', rs', Pointer.inc (Pointer.inc pc), pct),
        [/\ Transitional.Memory.store m (C, 1, 0%Z)
              (MVal Other (Ptr (C, fb, sp)),
               {| vtag := Other; color := C; entry := None;
                  is_code := false |}) = Some m',
            TMem.vload m' (C, 1, 0%Z) = Some (Ptr (C, fb, sp)),
            TMem.tload m' (C, 1, 0%Z) = Some Other
          & TInject.minj a mem m'],
        [/\ Transitional.Register.get R_SP rs'
              = MVal Other (Ptr (C, fb, sp))
          & forall r', r' <> R_SP -> r' <> R_AUX2 ->
              Transitional.Register.get r' rs'
              = Transitional.Register.get r' rs]
      & TInv.tag_inv L m' rs' pct].
Proof.
  move=> Hcode Htl Hcomp HSP Hmscr Hnoscr Hscrp HI Htag.
  case: tl Hcode Htl => [|nxt rest] Hcode _ //.
  have Hc0 : TMacros.code_at_I cde C pc
      (IConst (IPtr (scr C)) R_AUX2 :: IStore R_AUX2 R_SP :: nxt :: rest)
    by exact: Hcode.
  have Hc1 := TMacros.code_at_I_tail Hc0.
  have SC : TS.step cde (m, rs, pc, pct) E0
            (m, Transitional.Register.set R_AUX2 (Ptr (scr C)) Other rs,
             Pointer.inc pc, pct).
  { have -> : Ptr (scr C) = imm_to_val (IPtr (scr C)) by [].
    eapply TS.Const; [exact: (TMacros.code_at_I_head Hc0)
                     | exact: (TMacros.check_pc_at_I Hc0)]. }
  set rsA := (Transitional.Register.set R_AUX2 (Ptr (scr C)) Other rs) in SC *.
  have HSPA : Transitional.Register.get R_SP rsA
            = MVal Other (Ptr (C, fb, sp))
    by rewrite /rsA TInv.get_set_neq //.
  have HtagA : TInv.tag_inv L m rsA pct
    by apply: TInv.tag_inv_setreg; [by [] | exact: Htag].
  case: (TMem.store_after_load
           (Transitional.Register.get R_SP rsA,
            {| vtag := Other; color := C; entry := None; is_code := false |})
           Hmscr) => [m' Hst].
  have SS : TS.step cde (m, rsA, Pointer.inc pc, pct) E0
            (m', Transitional.Register.set R_SP
                   (Transitional.val (Transitional.Register.get R_SP rsA))
                   Other rsA,
             Pointer.inc (Pointer.inc pc), pct).
  { have -> : Other = (if is_address Other then Invalidated else Other) by [].
    eapply TS.Store.
    - exact: (TMacros.code_at_I_head Hc1).
    - exact: (TMacros.check_pc_at_I Hc1).
    - by rewrite /rsA TInv.get_set_eq.
    - by rewrite /rsA TInv.get_set_eq.
    - by rewrite /= Pointer.inc_preserves_component Hcomp.
    - apply: (TInv.ti_tag_other HtagA). by [].
    - by rewrite Pointer.inc_preserves_component Hcomp; exact: Hst. }
  exists m',
    (Transitional.Register.set R_SP
       (Transitional.val (Transitional.Register.get R_SP rsA)) Other rsA).
  split.
  - eapply plus_left with (t1 := E0) (t2 := E0); [exact: SC | | by []].
    exact: star_one SS.
  - split.
    + by move: Hst; rewrite HSPA.
    + by rewrite /TMem.vload (TMem.load_store_eq Hst) /= HSPA.
    + by rewrite /TMem.tload (TMem.load_store_eq Hst) /= HSPA.
    + apply: (TInject.minj_store_outside _ Hst HI) => b0. exact: Hscrp b0.
  - split.
    + by rewrite TInv.get_set_eq HSPA.
    + move=> r' H1 H2. by rewrite TInv.get_set_neq // /rsA TInv.get_set_neq //.
  - apply: TInv.tag_inv_setreg; first by [].
    apply: (TInv.tag_inv_store_data Hnoscr _ Hst HtagA).
    by rewrite /= HSPA.
Qed.

(** ★ One data pop, the mirror of [push_data_run].

    The T-specific fact that makes this cheap: for a DATA pop the write-back is
    **observationally invisible**. The rule rewrites the cell with
    `{| val := val v.1; tvtag := if is_address (tvtag v.1) … |}`, which for
    `tvtag v.1 = Other` has the SAME value and the SAME tag as what was there;
    only the cell's `mem_tag` changes, and no clause of the invariant reads a
    `mem_tag` (everything goes through `TMem.vload` / `TMem.tload`, both
    projections of the tvalue — Stage 2 part 1's design decision, paying off
    again).

    So the memory outputs are equalities `vload m' q = vload m q` and
    `tload m' q = tload m q` at EVERY `q`, which is the strongest form a caller
    could want; the store equation is handed back too, for the store-shaped
    transport lemmas that need it ([stack_match_store]). *)
Lemma pop_data_run C fb sp r cap a mem m rs pc pct L tl v :
  TMacros.code_at_I cde C pc (pop r ++ tl) ->
  tl <> [::] ->
  Pointer.component pc = C ->
  r <> R_RA -> R_SP <> r -> R_ONE <> r ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C, fb, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  Transitional.Memory.load m (C, fb, (sp - 1)%Z) = Some v ->
  tvtag v.1 = Other ->
  ~ List.In (TInv.CMem (C, fb, (sp - 1)%Z)) (TInv.sites L) ->
  TStack.frame_cap m C fb cap ->
  TInject.minj a mem m ->
  TInv.tag_inv L m rs pct ->
  exists m' rs',
    [/\ plus TS.step cde (m, rs, pc, pct) E0
             (m', rs', Pointer.inc (Pointer.inc pc), pct),
        [/\ Transitional.Memory.store m (C, fb, (sp - 1)%Z)
              ({| Transitional.val := Transitional.val v.1; tvtag := Other |},
               {| vtag := Other; color := C; entry := None;
                  is_code := false |}) = Some m',
            (forall q, TMem.vload m' q = TMem.vload m q),
            (forall q, TMem.tload m' q = TMem.tload m q),
            TStack.frame_cap m' C fb cap
          & TInject.minj a mem m'],
        [/\ Transitional.Register.get R_SP rs'
              = MVal Other (Ptr (C, fb, (sp - 1)%Z)),
            Transitional.Register.get r rs'
              = MVal Other (Transitional.val v.1)
          & forall r', r' <> R_SP -> r' <> r ->
              Transitional.Register.get r' rs'
              = Transitional.Register.get r' rs]
      & TInv.tag_inv L m' rs' pct].
Proof.
  move=> Hcode Htl Hcomp HrRA HSPr HONEr HSP HONE Hld Ev Hnosite Hcap HI Htag.
  case: tl Hcode Htl => [|nxt rest] Hcode _ //.
  have HrSP : r <> R_SP by move=> E; apply: HSPr; rewrite E.
  case: (TMem.store_after_load
           ({| Transitional.val := Transitional.val v.1; tvtag := Other |},
            {| vtag := Other; color := C; entry := None; is_code := false |})
           Hld) => [m' Hst].
  case: (TMacros.pop_data_macro (TMacros.code_at_I_pop Hcomp Hcode)
           Hcomp HrRA HSP HONE Ev Hnosite Hld Hst Htag) => [Pp Htag'].
  (* the write-back preserves the tvalue outright, hence both projections *)
  have Hv' : forall q, TMem.vload m' q = TMem.vload m q.
  { move=> q. apply: (TMem.vload_store_same Hld _ Hst q). by []. }
  have Ht' : forall q, TMem.tload m' q = TMem.tload m q.
  { move=> q. apply: (TMem.tload_store_same Hld _ Hst q). by rewrite /= Ev. }
  eexists; eexists. split; first exact: Pp.
  - split=> //.
    + exact: (TStack.frame_cap_store Hst Hcap).
    + apply: (TInject.minj_store_same Hld _ _ Hst HI); [by [] | by rewrite Ev].
  - split.
    + by rewrite TInv.get_set_neq // TInv.get_set_eq.
    + by rewrite TInv.get_set_eq.
    + move=> r' H1 H2. by rewrite !TInv.get_set_neq //.
  - exact: Htag'.
Qed.

(** ★ The pop INTO [R_SP] — the epilogue's frame-pointer restore.

    [pop_data_run] cannot serve: its register-output clause says "every register
    other than [R_SP] and [r] is unchanged", which is vacuous when [r] IS
    [R_SP], and the caller needs to know what [R_SP] ends up holding. Note that
    the underlying [exec_pop] needs no adjustment at all — unlike [exec_push] it
    never assumed the target differs from [R_SP], because the [Load] writes the
    target AFTER the decrement. *)
Lemma pop_sp_run C fb sp cap a mem m rs pc pct L tl v :
  TMacros.code_at_I cde C pc (pop R_SP ++ tl) ->
  tl <> [::] ->
  Pointer.component pc = C ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C, fb, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  Transitional.Memory.load m (C, fb, (sp - 1)%Z) = Some v ->
  tvtag v.1 = Other ->
  ~ List.In (TInv.CMem (C, fb, (sp - 1)%Z)) (TInv.sites L) ->
  TStack.frame_cap m C fb cap ->
  TInject.minj a mem m ->
  TInv.tag_inv L m rs pct ->
  exists m' rs',
    [/\ plus TS.step cde (m, rs, pc, pct) E0
             (m', rs', Pointer.inc (Pointer.inc pc), pct),
        [/\ Transitional.Memory.store m (C, fb, (sp - 1)%Z)
              ({| Transitional.val := Transitional.val v.1; tvtag := Other |},
               {| vtag := Other; color := C; entry := None;
                  is_code := false |}) = Some m',
            (forall q, TMem.vload m' q = TMem.vload m q),
            (forall q, TMem.tload m' q = TMem.tload m q),
            TStack.frame_cap m' C fb cap
          & TInject.minj a mem m'],
        [/\ Transitional.Register.get R_SP rs'
              = MVal Other (Transitional.val v.1)
          & forall r', r' <> R_SP ->
              Transitional.Register.get r' rs'
              = Transitional.Register.get r' rs]
      & TInv.tag_inv L m' rs' pct].
Proof.
  move=> Hcode Htl Hcomp HSP HONE Hld Ev Hnosite Hcap HI Htag.
  case: tl Hcode Htl => [|nxt rest] Hcode _ //.
  case: (TMem.store_after_load
           ({| Transitional.val := Transitional.val v.1; tvtag := Other |},
            {| vtag := Other; color := C; entry := None; is_code := false |})
           Hld) => [m' Hst].
  case: (TMacros.pop_data_macro (TMacros.code_at_I_pop Hcomp Hcode)
           Hcomp (ltac:(by []) : R_SP <> R_RA) HSP HONE Ev Hnosite Hld Hst
           Htag) => [Pp Htag'].
  have Hv' : forall q, TMem.vload m' q = TMem.vload m q.
  { move=> q. apply: (TMem.vload_store_same Hld _ Hst q). by []. }
  have Ht' : forall q, TMem.tload m' q = TMem.tload m q.
  { move=> q. apply: (TMem.tload_store_same Hld _ Hst q). by rewrite /= Ev. }
  eexists; eexists. split; first exact: Pp.
  - split=> //.
    + exact: (TStack.frame_cap_store Hst Hcap).
    + apply: (TInject.minj_store_same Hld _ _ Hst HI); by [].
  - split.
    + by rewrite TInv.get_set_eq.
    + move=> r' H1. by rewrite !TInv.get_set_neq //.
  - exact: Htag'.
Qed.

(** ★ The pop that MOVES A CAPABILITY: the caller's `pop R_RA`, restoring the
    return capability it spilled before the call.

    Unlike every other pop this one is NOT invisible: the write-back leaves
    `Invalidated` where a live capability was, so `tload` changes AT THE POPPED
    CELL (its value does not). That is why the outputs separate the two — `vload`
    everywhere, `tload` only away from the slot — and why the injection needs
    `frame_priv` rather than value-preservation: the cell is in the frame, which
    is outside the injection's range, so `minj_store_outside` applies where
    `minj_store_same` would not (the tag moved). *)
Lemma pop_ra_run C fb sp cap a mem m rs pc pct L tl v :
  TMacros.code_at_I cde C pc (pop R_RA ++ tl) ->
  tl <> [::] ->
  Pointer.component pc = C ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C, fb, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  Transitional.Memory.load m (C, fb, (sp - 1)%Z) = Some v ->
  TInv.is_live (tvtag v.1) ->
  ~ List.In TInv.CReg (TInv.sites L) ->
  (forall b0, a C b0 <> Some fb) ->
  TStack.frame_cap m C fb cap ->
  TInject.minj a mem m ->
  TInv.tag_inv ((TInv.CMem (C, fb, (sp - 1)%Z), tvtag v.1) :: L) m rs pct ->
  exists m' rs',
    [/\ plus TS.step cde (m, rs, pc, pct) E0
             (m', rs', Pointer.inc (Pointer.inc pc), pct),
        [/\ Transitional.Memory.store m (C, fb, (sp - 1)%Z)
              ({| Transitional.val := Transitional.val v.1;
                  tvtag := Invalidated |},
               {| vtag := Invalidated; color := C; entry := None;
                  is_code := false |}) = Some m',
            (forall q, TMem.vload m' q = TMem.vload m q),
            (forall q, q <> (C, fb, (sp - 1)%Z) ->
               TMem.tload m' q = TMem.tload m q),
            TStack.frame_cap m' C fb cap
          & TInject.minj a mem m'],
        [/\ Transitional.Register.get R_SP rs'
              = MVal Other (Ptr (C, fb, (sp - 1)%Z)),
            Transitional.Register.get R_RA rs'
              = MVal (tvtag v.1) (Transitional.val v.1)
          & forall r', r' <> R_SP -> r' <> R_RA ->
              Transitional.Register.get r' rs'
              = Transitional.Register.get r' rs]
      & TInv.tag_inv ((TInv.CReg, tvtag v.1) :: L) m' rs' pct].
Proof.
  move=> Hcode Htl Hcomp HSP HONE Hld Hlive HnotReg Hpriv Hcap HI Htag.
  case: tl Hcode Htl => [|nxt rest] Hcode _ //.
  case: (TMem.store_after_load
           ({| Transitional.val := Transitional.val v.1;
               tvtag := Invalidated |},
            {| vtag := Invalidated; color := C; entry := None;
               is_code := false |}) Hld) => [m' Hst].
  case: (TMacros.pop_ra_macro (TMacros.code_at_I_pop Hcomp Hcode)
           Hcomp HSP HONE Hlive HnotReg Hld Hst Htag) => [Pp Htag'].
  have Hv' : forall q, TMem.vload m' q = TMem.vload m q.
  { move=> q. apply: (TMem.vload_store_same Hld _ Hst q). by []. }
  eexists; eexists. split; first exact: Pp.
  - split=> //.
    + move=> q Hq. by rewrite /TMem.tload (TMem.load_store_neq Hst Hq).
    + exact: (TStack.frame_cap_store Hst Hcap).
    + apply: (TInject.minj_store_outside _ Hst HI) => b0. exact: Hpriv b0.
  - split.
    + by rewrite TInv.get_set_neq // TInv.get_set_eq.
    + by rewrite TInv.get_set_eq.
    + move=> r' H1 H2. by rewrite !TInv.get_set_neq //.
  - exact: Htag'.
Qed.

(** ★ [push R_RA] of a NON-capability — main's INITIAL activation, entered by
    the machine with [Register.init] in the register file, so [R_RA] holds
    [tUndef] rather than a return address.

    The mirror of [pop_junk_ra_run], and the counterpart of [push_ra_run] with
    the liveness premise replaced by an [Other] tag: no ledger entry appears,
    because no capability is being spilled. The [Store] rule's write-back
    leaves [R_RA] [Other] (it only invalidates ADDRESSES), which is why the
    register side is [tag_inv_setra] rather than [tag_inv_setreg] — the latter
    refuses [R_RA] outright. *)
Lemma push_junk_ra_run C fb sp cap a mem m rs pc pct L tl :
  TMacros.code_at_I cde C pc (push R_RA ++ tl) ->
  tl <> [::] ->
  Pointer.component pc = C ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C, fb, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  Transitional.Register.get_tag R_RA rs = Some Other ->
  (0 <= sp < Z.of_nat cap)%Z ->
  TStack.frame_cap m C fb cap ->
  ~ List.In (TInv.CMem (C, fb, sp)) (TInv.sites L) ->
  ~ List.In TInv.CReg (TInv.sites L) ->
  (forall b, a C b <> Some fb) ->
  TInject.minj a mem m ->
  TInv.tag_inv L m rs pct ->
  exists m' rs',
    [/\ plus TS.step cde (m, rs, pc, pct) E0
             (m', rs', Pointer.inc (Pointer.inc pc), pct),
        [/\ Transitional.Memory.load m' (C, fb, sp)
              = Some (Transitional.Register.get R_RA rs,
                      {| vtag := Other; color := C; entry := None;
                         is_code := false |}),
            (forall q w, Transitional.Memory.load m q = Some w ->
               q <> (C, fb, sp) -> Transitional.Memory.load m' q = Some w),
            Transitional.Memory.store m (C, fb, sp)
              (Transitional.Register.get R_RA rs,
               {| vtag := Other; color := C; entry := None;
                  is_code := false |}) = Some m',
            TStack.frame_cap m' C fb cap
          & TInject.minj a mem m'],
        [/\ Transitional.Register.get R_SP rs'
              = MVal Other (Ptr (C, fb, (sp + 1)%Z))
          & forall r', r' <> R_SP -> r' <> R_RA ->
              Transitional.Register.get r' rs'
              = Transitional.Register.get r' rs]
      & TInv.tag_inv L m' rs' pct].
Proof.
  move=> Hcode Htl Hcomp HSP HONE Hrt Hsp Hcap Hnosite HnotReg Havoid HI Htag.
  case: tl Hcode Htl => [|nxt rest] Hcode _ //.
  have [w Hw] : exists w, Transitional.Memory.load m (C, fb, sp) = Some w
    by case: (Hcap sp Hsp) => [v Hv]; exact: (TMem.vload_load Hv).
  case: (TMem.store_after_load
           (Transitional.Register.get R_RA rs,
            {| vtag := Other; color := C; entry := None; is_code := false |})
           Hw) => [m' Hst].
  have Pp := TMacros.exec_push pct (TMacros.code_at_I_push Hcomp Hcode) Hrt
               HSP HONE (ltac:(by []) : R_SP <> R_RA)
               (ltac:(by []) : R_ONE <> R_RA) Hcomp Hst.
  exists m',
    (Transitional.Register.set R_SP (Ptr (C, fb, (sp + 1)%Z)) Other
       (Transitional.Register.set R_RA
          (Transitional.val (Transitional.Register.get R_RA rs)) Other rs)).
  split.
  - by move: Pp; rewrite /=.
  - split.
    + exact: (TMem.load_store_eq Hst).
    + move=> q w' Hq Hne.
      by rewrite (TMem.load_store_neq Hst Hne); exact: Hq.
    + exact: Hst.
    + exact: (TStack.frame_cap_store Hst Hcap).
    + apply: (TInject.minj_store_outside _ Hst HI) => b. exact: Havoid b.
  - split.
    + by rewrite TInv.get_set_eq.
    + move=> r' H1 H2. by rewrite !TInv.get_set_neq //.
  - apply: TInv.tag_inv_setreg; first by [].
    apply: (@TInv.tag_inv_setra _ _ _ _ _ _ HnotReg).
    apply: (TInv.tag_inv_store_data Hnosite _ Hst Htag).
    have Et : tvtag (Transitional.Register.get R_RA rs) = Other.
    { move: Hrt. rewrite /Transitional.Register.get_tag
                         /Transitional.Register.get.
      by case: (getm rs _) => [tv|] //= [] ->. }
    by rewrite /= Et.
Qed.

(** ★ [pop R_RA] of a NON-capability — main's initial activation, whose
    wrapper slot 2 holds junk rather than a return capability (the machine
    entered `main` directly; it leaves through the wrapper's `IHalt`, not
    through an `IReturn`).

    The mirror of [pop_ra_run] with the liveness premise NEGATED: no ledger
    entry appears, because none was spent. [ti_regs] never constrains [R_RA],
    so a dead value landing there is invisible to the invariant — which is the
    formal content of "main's activation has no return capability". *)
Lemma pop_junk_ra_run C fb sp cap a mem m rs pc pct L tl v told :
  TMacros.code_at_I cde C pc (pop R_RA ++ tl) ->
  tl <> [::] ->
  Pointer.component pc = C ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C, fb, sp)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  Transitional.Memory.load m (C, fb, (sp - 1)%Z) = Some v ->
  ~~ TInv.is_live (tvtag v.1) ->
  ~ List.In (TInv.CMem (C, fb, (sp - 1)%Z)) (TInv.sites L) ->
  (forall b0, a C b0 <> Some fb) ->
  TInv.is_ret told = false ->
  TStack.frame_cap m C fb cap ->
  TInject.minj a mem m ->
  TInv.tag_inv ((TInv.CReg, told) :: L) m rs pct ->
  exists m' rs',
    [/\ plus TS.step cde (m, rs, pc, pct) E0
             (m', rs', Pointer.inc (Pointer.inc pc), pct),
        [/\ (forall q, TMem.vload m' q = TMem.vload m q),
            (forall q, q <> ((C, fb, (sp - 1)%Z) : Pointer.t) ->
               Transitional.Memory.load m' q = Transitional.Memory.load m q),
            TStack.frame_cap m' C fb cap
          & TInject.minj a mem m'],
        [/\ Transitional.Register.get R_SP rs'
              = MVal Other (Ptr (C, fb, (sp - 1)%Z))
          & forall r', r' <> R_SP -> r' <> R_RA ->
              Transitional.Register.get r' rs'
              = Transitional.Register.get r' rs]
      & TInv.tag_inv L m' rs' pct].
Proof.
  move=> Hcode Htl Hcomp HSP HONE Hld Hdead Hnosite Hpriv Hret Hcap HI Htag.
  have HnotReg : ~ List.In TInv.CReg (TInv.sites L)
    by move: (TInv.ti_uniq Htag) => /= /List.NoDup_cons_iff [].
  have Htag0 := TInv.tag_inv_drop_reg Hret Htag.
  case: tl Hcode Htl => [|nxt rest] Hcode _ //.
  case: (TMem.store_after_load
           ({| Transitional.val := Transitional.val v.1;
               tvtag := if is_address (tvtag v.1) then Invalidated
                        else Other |},
            {| vtag := if is_address (tvtag v.1) then Invalidated else Other;
               color := C; entry := None; is_code := false |}) Hld)
    => [m' Hst].
  have Pp := TMacros.exec_pop pct (TMacros.code_at_I_pop Hcomp Hcode)
               HSP HONE Hcomp Hld Hst.
  have Hv' : forall q, TMem.vload m' q = TMem.vload m q.
  { move=> q. apply: (TMem.vload_store_same Hld _ Hst q). by []. }
  exists m',
    (Transitional.Register.set R_RA (Transitional.val v.1) (tvtag v.1)
       (Transitional.Register.set R_SP (Ptr (C, fb, (sp - 1)%Z)) Other rs)).
  split.
  - exact: Pp.
  - split.
    + exact: Hv'.
    + by move=> q Hq; exact: (TMem.load_store_neq Hst Hq).
    + exact: (TStack.frame_cap_store Hst Hcap).
    + apply: (TInject.minj_store_outside _ Hst HI) => b0. exact: Hpriv b0.
  - split.
    + by rewrite TInv.get_set_neq // TInv.get_set_eq.
    + move=> r' H1 H2. by rewrite !TInv.get_set_neq //.
  - apply: (@TInv.tag_inv_setra _ _ _ _ _ _ HnotReg).
    apply: TInv.tag_inv_setreg; first by [].
    apply: (TInv.tag_inv_store_data Hnosite _ Hst Htag0).
    by move: Hdead; case: (is_address (tvtag v.1)).
Qed.

(** ★ The [Kstop] epilogue: pop the saved argument, pop the caller's frame
    pointer, and RETURN through [R_RA].

    Five steps, and the last of them is the one the whole capability apparatus
    exists for: `TS.Jump` fires only if `R_RA` holds `MVal InternalJump (Ptr
    ret)`. At the I level the corresponding `IJump` reads the `gps` stack and
    `R_RA` is `Undef` throughout; here the return address and its tag must BE in
    the register, which is `ei_ra`.

    That the tag is `InternalJump` (rather than a `Ret n`) is a premise here and
    an invariant of the stack shape: a procedure BODY is always entered by the
    wrapper's `IJal`, never by a cross-component call — the `Ret n` of an
    external call is spilled in the wrapper's own frame. So the same value
    serves all three `stack_match` constructors. *)
Lemma epilogue_run C fb cap a mem m rs pc pct L ret v0 v1 :
  TMacros.code_at_I cde C pc (pop R_ARG ++ pop R_SP ++ [:: IJump]) ->
  Pointer.component pc = C ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C, fb, 2%Z)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  Transitional.Register.get R_RA rs = MVal InternalJump (Ptr ret) ->
  Pointer.component ret = C ->
  (exists i tni, Transitional.executing cde ret i tni C) ->
  (* the frame's two linkage slots, from the stack relation *)
  Transitional.Memory.load m (C, fb, 1%Z) = Some v1 ->
  tvtag v1.1 = Other ->
  Transitional.Memory.load m (C, fb, 0%Z) = Some v0 ->
  tvtag v0.1 = Other ->
  (forall o : Z, ~ List.In (TInv.CMem (C, fb, o)) (TInv.sites L)) ->
  TStack.frame_cap m C fb cap ->
  TInject.minj a mem m ->
  TInv.tag_inv L m rs pct ->
  exists m' rs',
    [/\ plus TS.step cde (m, rs, pc, pct) E0 (m', rs', ret, pct),
        [/\ (forall q, TMem.vload m' q = TMem.vload m q),
            (forall q, TMem.tload m' q = TMem.tload m q),
            (* the two write-backs touch only this frame's linkage slots, so
               cells elsewhere keep their MEM_TAG too, not just their
               projections *)
            (forall q, q <> (C, fb, 1%Z) -> q <> (C, fb, 0%Z) ->
               Transitional.Memory.load m' q = Transitional.Memory.load m q),
            TStack.frame_cap m' C fb cap
          & TInject.minj a mem m'],
        [/\ Transitional.Register.get R_ARG rs'
              = MVal Other (Transitional.val v1.1),
            Transitional.Register.get R_SP rs'
              = MVal Other (Transitional.val v0.1)
          & forall r', r' <> R_SP -> r' <> R_ARG ->
              Transitional.Register.get r' rs'
              = Transitional.Register.get r' rs]
      & TInv.tag_inv L m' rs' pct].
Proof.
  move=> Hcode Hcomp HSP HONE HRA Hret [ir [tnir Hexr]]
         Hl1 Et1 Hl0 Et0 Hnosite Hcap HI Htag.
  (* --- pop R_ARG: the saved argument, at offset 1 --- *)
  have Hc1 : TMacros.code_at_I cde C pc
      (pop R_ARG ++ pop R_SP ++ [:: IJump]) by exact: Hcode.
  have Htl1 : pop R_SP ++ [:: IJump] <> [::] by [].
  have Hl1' : Transitional.Memory.load m (C, fb, (2 - 1)%Z) = Some v1
    by rewrite (_ : (2 - 1)%Z = 1%Z) //.
  case: (pop_data_run Hc1 Htl1 Hcomp
           (ltac:(by []) : R_ARG <> R_RA)
           (ltac:(by []) : R_SP <> R_ARG)
           (ltac:(by []) : R_ONE <> R_ARG)
           HSP HONE Hl1' Et1 (Hnosite (2 - 1)%Z) Hcap HI Htag)
    => [m1 [rs1 [Pp1 [Hst1 Hv1 Ht1 Hcap1 Hmj1] [HSP1 HARG1 Hoth1] Htag1]]].
  (* --- pop R_SP: the caller's frame pointer, at offset 0 --- *)
  set pc2 := Pointer.inc (Pointer.inc pc).
  have Hcomp2 : Pointer.component pc2 = C
    by rewrite /pc2 !Pointer.inc_preserves_component.
  have Hc2 : TMacros.code_at_I cde C pc2 (pop R_SP ++ [:: IJump])
    by exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hc1)).
  have Htl2 : [:: IJump] <> [::] by [].
  have HSP1' : Transitional.Register.get R_SP rs1
             = MVal Other (Ptr (C, fb, (2 - 1)%Z)) by exact: HSP1.
  have HONE1 : Transitional.Register.get R_ONE rs1 = MVal Other (Int 1)
    by rewrite Hoth1.
  (* the untouched linkage slot travels across the first pop's write-back *)
  have Hl0' : Transitional.Memory.load m1 (C, fb, ((2 - 1) - 1)%Z) = Some v0.
  { have Hne : ((C, fb, 0%Z) : Pointer.t) <> (C, fb, (2 - 1)%Z)
      by move=> E; move: (f_equal Pointer.offset E) => /=; lia.
    by rewrite (_ : ((2 - 1) - 1)%Z = 0%Z) // (TMem.load_store_neq Hst1 Hne). }
  case: (pop_sp_run Hc2 Htl2 Hcomp2 HSP1' HONE1 Hl0' Et0
           (Hnosite ((2 - 1) - 1)%Z) Hcap1 Hmj1 Htag1)
    => [m2 [rs2 [Pp2 [Hst2 Hv2 Ht2 Hcap2 Hmj2] [HSP2 Hoth2] Htag2]]].
  (* --- the [IJump]: the capability in [R_RA] is what makes it fire --- *)
  set pc4 := Pointer.inc (Pointer.inc pc2).
  have Hc4 : TMacros.code_at_I cde C pc4 [:: IJump]
    by exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hc2)).
  have HRA2 : Transitional.Register.get R_RA rs2
            = MVal InternalJump (Ptr ret)
    by rewrite Hoth2 // Hoth1 //.
  have SB : TS.step cde (m2, rs2, pc4, pct) E0 (m2, rs2, ret, pct).
  { eapply TS.Jump.
    - exact: (TMacros.code_at_I_head Hc4).
    - exact: HRA2.
    - by rewrite /pc4 /pc2 !Pointer.inc_preserves_component Hcomp; exact: Hret.
    - apply: PcJump; first exact: Hexr.
      by rewrite /pc4 /pc2 !Pointer.inc_preserves_component Hcomp. }
  exists m2, rs2. split.
  - eapply plus_trans; [exact: Pp1 | | by []].
    eapply plus_right'; [exact: Pp2 | exact: SB | by []].
  - split.
    + by move=> q; rewrite Hv2 Hv1.
    + by move=> q; rewrite Ht2 Ht1.
    + move=> q Hq1 Hq0.
      have Hne0 : q <> ((C, fb, ((2 - 1) - 1)%Z) : Pointer.t)
        by move=> E; apply: Hq0; rewrite E; congr (_, _); lia.
      have Hne1 : q <> ((C, fb, (2 - 1)%Z) : Pointer.t)
        by move=> E; apply: Hq1; rewrite E; congr (_, _); lia.
      by rewrite (TMem.load_store_neq Hst2 Hne0)
                 (TMem.load_store_neq Hst1 Hne1).
    + exact: Hcap2.
    + exact: Hmj2.
  - split.
    + by rewrite Hoth2 // HARG1.
    + by rewrite HSP2.
    + move=> r' H1 H2. by rewrite Hoth2 // Hoth1 //.
  - exact: Htag2.
Qed.

(** ★ The WRAPPER's cross-component return — nine steps ending in the `IReturn`
    that emits the `ERet` event:

        pop R_RA ; pop R_AUX1 ; store_arg (scr C) R_AUX1 R_AUX2 ;
        pop R_SP ; IReturn

    This is the only place in the campaign where `pc_tag` MOVES:

      - `TS.JumpRet` fires only if `value_to_pc_tag (tvtag R_RA) = Some pct`,
        i.e. the capability is `Ret n` and the pc is at `Level n.+1` — the
        premise `TSM.ext_level_max` supplies from the stack shape;
      - it lands at `dec_pc_tag pct = Level n`, with `TS.invalidate_ret` killing
        the spent capability (plan §3.6 — without that fix a spent `Ret n`
        survives at `Level n`, exactly what the Stage-0 harness caught);
      - `TInv.tag_inv_return` retires the ledger's `Ret n` entry, and `ti_lvl`'s
        multiset shrinks by one. *)
Lemma ef_restore_run C fbE cap a mem m rs pc pct L n pc' vRA vscr vSP mscr
      tailc :
  TMacros.code_at_I cde C pc
    (pop R_RA ++ pop R_AUX1 ++ store_arg (scr C) R_AUX1 R_AUX2
       ++ pop R_SP ++ tailc) ->
  tailc <> [::] ->
  Pointer.component pc = C ->
  pct = Level n.+1 ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C, fbE, 3%Z)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  Transitional.Memory.load m (C, fbE, 2%Z) = Some vRA ->
  tvtag vRA.1 = Ret n ->
  Transitional.val vRA.1 = Ptr pc' ->
  Transitional.Memory.load m (C, fbE, 1%Z) = Some vscr ->
  tvtag vscr.1 = Other ->
  Transitional.Memory.load m (C, fbE, 0%Z) = Some vSP ->
  tvtag vSP.1 = Other ->
  Transitional.Memory.load m (C, 1, 0%Z) = Some mscr ->
  fbE <> 1 ->
  (forall b0, a C b0 <> Some fbE) ->
  ~ List.In TInv.CReg (TInv.sites L) ->
  (forall o : Z, ~ List.In (TInv.CMem (C, fbE, o)) (TInv.sites L)) ->
  ~ List.In (TInv.CMem (C, 1, 0%Z)) (TInv.sites L) ->
  (forall b0, a C b0 <> Some 1) ->
  TStack.frame_cap m C fbE cap ->
  TInject.minj a mem m ->
  TInv.tag_inv ((TInv.CMem (C, fbE, 2%Z), Ret n) :: L) m rs pct ->
  exists m' rs' pcF,
    [/\ plus TS.step cde (m, rs, pc, pct) E0 (m', rs', pcF, pct),
        [/\ Pointer.component pcF = C,
            TMacros.code_at_I cde C pcF tailc,
            TInject.minj a mem m',
            (* what the wrapper touched: its own frame, and the scratch cell,
               which it restores to the value it inherited *)
            (forall q, (Pointer.component q <> C \/ Pointer.block q <> fbE) ->
               q <> ((C, 1, 0%Z) : Pointer.t) ->
               Transitional.Memory.load m' q = Transitional.Memory.load m q)
          & TMem.vload m' (C, 1, 0%Z) = Some (Transitional.val vscr.1)
            /\ TMem.tload m' (C, 1, 0%Z) = Some Other],
        [/\ Transitional.Register.get R_RA rs' = MVal (Ret n) (Ptr pc'),
            Transitional.Register.get R_SP rs'
              = MVal Other (Transitional.val vSP.1),
            Transitional.Register.get R_ONE rs' = MVal Other (Int 1)
          & forall r', r' <> R_SP -> r' <> R_RA -> r' <> R_AUX1 ->
              r' <> R_AUX2 ->
              Transitional.Register.get r' rs'
              = Transitional.Register.get r' rs]
      & TInv.tag_inv ((TInv.CReg, Ret n) :: L) m' rs' pct].
Proof.
  move=> Hcode Htailc Hcomp Epct HSP HONE HlRA EtRA EvRA Hlsc Etsc HlSP EtSP
         Hmscr HfbE1 Hpriv HnotReg Hnosite Hnoscr Hscrp Hcap HI Htag.
  (* --- 1. pop R_RA: the wrapper's own capability --- *)
  have Htl1 : pop R_AUX1 ++ store_arg (scr C) R_AUX1 R_AUX2
              ++ pop R_SP ++ tailc <> [::] by [].
  have HlRA' : Transitional.Memory.load m (C, fbE, (3 - 1)%Z) = Some vRA
    by rewrite (_ : (3 - 1)%Z = 2%Z).
  have Htagd : TInv.tag_inv
      ((TInv.CMem (C, fbE, (3 - 1)%Z), tvtag vRA.1) :: L) m rs pct
    by rewrite (_ : (3 - 1)%Z = 2%Z) // EtRA.
  case: (pop_ra_run Hcode Htl1 Hcomp HSP HONE HlRA'
           (ltac:(by rewrite EtRA) : TInv.is_live (tvtag vRA.1))
           HnotReg Hpriv Hcap HI Htagd)
    => [m1 [rs1 [Pp1 [Hst1 Hv1 Ht1 Hcap1 Hmj1] [HSP1 HRA1 Hoth1] Htag1]]].
  (* the ledger now carries the capability in [CReg]; a [CMem] site is never
     that head, so the freshness premises lift verbatim *)
  have Hnosite1 : forall o : Z,
      ~ List.In (TInv.CMem (C, fbE, o))
                (TInv.sites ((TInv.CReg, tvtag vRA.1) :: L)).
  { move=> o /= [E|Hin]; [by [] | exact: Hnosite Hin]. }
  have Hnoscr1 : ~ List.In (TInv.CMem (C, 1, 0%Z))
                   (TInv.sites ((TInv.CReg, tvtag vRA.1) :: L)).
  { move=> /= [E|Hin]; [by [] | exact: Hnoscr Hin]. }
  (* --- 2. pop R_AUX1: the inherited scratch value --- *)
  set pc2 := Pointer.inc (Pointer.inc pc).
  have Hcomp2 : Pointer.component pc2 = C
    by rewrite /pc2 !Pointer.inc_preserves_component.
  have Hc2 : TMacros.code_at_I cde C pc2
      (pop R_AUX1 ++ store_arg (scr C) R_AUX1 R_AUX2 ++ pop R_SP ++ tailc)
    by exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hcode)).
  have Htl2 : store_arg (scr C) R_AUX1 R_AUX2 ++ pop R_SP ++ tailc
              <> [::] by [].
  have Hne21 : ((C, fbE, 1%Z) : Pointer.t) <> (C, fbE, (3 - 1)%Z)
    by move=> E; move: (f_equal Pointer.offset E) => /=; lia.
  have Hlsc1 : Transitional.Memory.load m1 (C, fbE, ((3 - 1) - 1)%Z)
             = Some vscr
    by rewrite (_ : ((3 - 1) - 1)%Z = 1%Z) // (TMem.load_store_neq Hst1 Hne21).
  have HSP1' : Transitional.Register.get R_SP rs1
             = MVal Other (Ptr (C, fbE, (3 - 1)%Z)) by exact: HSP1.
  have HONE1 : Transitional.Register.get R_ONE rs1 = MVal Other (Int 1)
    by rewrite Hoth1.
  case: (pop_data_run Hc2 Htl2 Hcomp2
           (ltac:(by []) : R_AUX1 <> R_RA)
           (ltac:(by []) : R_SP <> R_AUX1)
           (ltac:(by []) : R_ONE <> R_AUX1)
           HSP1' HONE1 Hlsc1 Etsc (Hnosite1 ((3 - 1) - 1)%Z) Hcap1 Hmj1 Htag1)
    => [m2 [rs2 [Pp2 [Hst2 Hv2 Ht2 Hcap2 Hmj2] [HSP2 HA12 Hoth2] Htag2]]].
  (* --- 3. store_arg: put the inherited scratch back --- *)
  set pc4 := Pointer.inc (Pointer.inc pc2).
  have Hcomp4 : Pointer.component pc4 = C
    by rewrite /pc4 /pc2 !Pointer.inc_preserves_component.
  have Hc4 : TMacros.code_at_I cde C pc4
      (store_arg (scr C) R_AUX1 R_AUX2 ++ pop R_SP ++ tailc)
    by exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hc2)).
  have Hc4a : TMacros.code_at_I cde C pc4
      (IConst (IPtr (scr C)) R_AUX2
         :: IStore R_AUX2 R_AUX1 :: pop R_SP ++ tailc)
    by exact: Hc4.
  have Hc4b := TMacros.code_at_I_tail Hc4a.
  have SC : TS.step cde (m2, rs2, pc4, pct) E0
            (m2, Transitional.Register.set R_AUX2 (Ptr (scr C)) Other rs2,
             Pointer.inc pc4, pct).
  { have -> : Ptr (scr C) = imm_to_val (IPtr (scr C)) by [].
    eapply TS.Const; [exact: (TMacros.code_at_I_head Hc4a)
                     | exact: (TMacros.check_pc_at_I Hc4a)]. }
  set rsA := (Transitional.Register.set R_AUX2 (Ptr (scr C)) Other rs2) in SC *.
  (* the scratch cell is still there, and still storable *)
  have Hmscr2 : Transitional.Memory.load m2 (C, 1, 0%Z) = Some mscr.
  { have Hne1 : ((C, 1, 0%Z) : Pointer.t) <> (C, fbE, (3 - 1)%Z)
      by move=> E; apply: HfbE1; move: (f_equal Pointer.block E) => /= ->.
    have Hne2 : ((C, 1, 0%Z) : Pointer.t) <> (C, fbE, ((3 - 1) - 1)%Z)
      by move=> E; apply: HfbE1; move: (f_equal Pointer.block E) => /= ->.
    by rewrite (TMem.load_store_neq Hst2 Hne2) (TMem.load_store_neq Hst1 Hne1). }
  case: (TMem.store_after_load
           (Transitional.Register.get R_AUX1 rsA,
            {| vtag := Other; color := C; entry := None; is_code := false |})
           Hmscr2) => [m3 Hst3].
  have HA1A : Transitional.Register.get R_AUX1 rsA
            = MVal Other (Transitional.val vscr.1)
    by rewrite /rsA TInv.get_set_neq // HA12.
  have HtagA : TInv.tag_inv ((TInv.CReg, tvtag vRA.1) :: L) m2 rsA pct
    by apply: TInv.tag_inv_setreg; [by [] | exact: Htag2].
  have SS : TS.step cde (m2, rsA, Pointer.inc pc4, pct) E0
            (m3, Transitional.Register.set R_AUX1
                   (Transitional.val (Transitional.Register.get R_AUX1 rsA))
                   Other rsA,
             Pointer.inc (Pointer.inc pc4), pct).
  { have -> : Other = (if is_address Other then Invalidated else Other) by [].
    eapply TS.Store.
    - exact: (TMacros.code_at_I_head Hc4b).
    - exact: (TMacros.check_pc_at_I Hc4b).
    - by rewrite /rsA TInv.get_set_eq.
    - by rewrite /rsA TInv.get_set_eq.
    - by rewrite /= Pointer.inc_preserves_component Hcomp4.
    - apply: (TInv.ti_tag_other HtagA). by [].
    - by rewrite Pointer.inc_preserves_component Hcomp4; exact: Hst3. }
  set rsB := Transitional.Register.set R_AUX1
               (Transitional.val (Transitional.Register.get R_AUX1 rsA))
               Other rsA.
  have HtagB : TInv.tag_inv ((TInv.CReg, tvtag vRA.1) :: L) m3 rsB pct.
  { apply: TInv.tag_inv_setreg; first by [].
    apply: (TInv.tag_inv_store_data Hnoscr1 _ Hst3 HtagA).
    by rewrite /= HA1A. }
  (* --- 4. pop R_SP: the caller's frame pointer --- *)
  set pc6 := Pointer.inc (Pointer.inc pc4).
  have Hcomp6 : Pointer.component pc6 = C
    by rewrite /pc6 !Pointer.inc_preserves_component.
  have Hc6 : TMacros.code_at_I cde C pc6 (pop R_SP ++ tailc)
    by exact: (TMacros.code_at_I_tail Hc4b).
  have Htl6 : tailc <> [::] by exact: Htailc.
  have HSPB : Transitional.Register.get R_SP rsB
            = MVal Other (Ptr (C, fbE, ((3 - 1) - 1)%Z))
    by rewrite /rsB TInv.get_set_neq // /rsA TInv.get_set_neq //; exact: HSP2.
  have HONEB : Transitional.Register.get R_ONE rsB = MVal Other (Int 1)
    by rewrite /rsB TInv.get_set_neq // /rsA TInv.get_set_neq // Hoth2 //.
  have HlSP3 : Transitional.Memory.load m3
      (C, fbE, (((3 - 1) - 1) - 1)%Z) = Some vSP.
  { have Hne3 : ((C, fbE, 0%Z) : Pointer.t) <> (C, 1, 0%Z)
      by move=> E; apply: HfbE1; move: (f_equal Pointer.block E) => /= ->.
    have Hne2 : ((C, fbE, 0%Z) : Pointer.t) <> (C, fbE, ((3 - 1) - 1)%Z)
      by move=> E; move: (f_equal Pointer.offset E) => /=; lia.
    have Hne1 : ((C, fbE, 0%Z) : Pointer.t) <> (C, fbE, (3 - 1)%Z)
      by move=> E; move: (f_equal Pointer.offset E) => /=; lia.
    rewrite (_ : (((3 - 1) - 1) - 1)%Z = 0%Z) //.
    by rewrite (TMem.load_store_neq Hst3 Hne3) (TMem.load_store_neq Hst2 Hne2)
               (TMem.load_store_neq Hst1 Hne1). }
  have Hcap3 : TStack.frame_cap m3 C fbE cap
    by exact: (TStack.frame_cap_store Hst3 Hcap2).
  have Hmj3 : TInject.minj a mem m3.
  { apply: (TInject.minj_store_outside _ Hst3 Hmj2) => b0. exact: Hscrp b0. }
  case: (pop_sp_run Hc6 Htl6 Hcomp6 HSPB HONEB HlSP3 EtSP
           (Hnosite1 (((3 - 1) - 1) - 1)%Z) Hcap3 Hmj3 HtagB)
    => [m4 [rs4 [Pp4 [Hst4 Hv4 Ht4 Hcap4 Hmj4] [HSP4 Hoth4] Htag4]]].
  (* --- the state just before the flavour-specific tail --- *)
  set pc8 := Pointer.inc (Pointer.inc pc6).
  have Hc8 : TMacros.code_at_I cde C pc8 tailc
    by exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hc6)).
  have HRA4 : Transitional.Register.get R_RA rs4 = MVal (Ret n) (Ptr pc').
  { rewrite Hoth4 // /rsB TInv.get_set_neq // /rsA TInv.get_set_neq //
            Hoth2 // HRA1.
    by rewrite EtRA EvRA. }
  exists m4, rs4, pc8. split.
  - eapply plus_trans; [exact: Pp1 | | by []].
    eapply plus_trans; [exact: Pp2 | | by []].
    eapply plus_left with (t1 := E0) (t2 := E0); [exact: SC | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: SS | | by []].
    exact: (plus_star Pp4).
  - split.
    + by rewrite /pc8 /pc6 /pc4 /pc2 !Pointer.inc_preserves_component.
    + exact: Hc8.
    + exact: Hmj4.
    + (* the four writes are all in [fbE] or the scratch cell *)
      move=> q Hq1 Hq2.
      have Hne : forall o : Z, q <> ((C, fbE, o) : Pointer.t)
        by move=> o E; case: Hq1 => H; apply: H; rewrite E.
      rewrite (TMem.load_store_neq Hst4 (Hne _))
              (TMem.load_store_neq Hst3 Hq2)
              (TMem.load_store_neq Hst2 (Hne _))
              (TMem.load_store_neq Hst1 (Hne _)).
      by [].
    + (* the scratch cell holds what [store_arg] put there *)
      have Hne4 : ((C, 1, 0%Z) : Pointer.t) <> (C, fbE, (((3 - 1) - 1) - 1)%Z)
        by move=> E; apply: HfbE1; move: (f_equal Pointer.block E) => /= ->.
      split.
      * rewrite /TMem.vload (TMem.load_store_neq Hst4 Hne4)
                (TMem.load_store_eq Hst3) /= HA1A /=. by [].
      * rewrite /TMem.tload (TMem.load_store_neq Hst4 Hne4)
                (TMem.load_store_eq Hst3) /= HA1A /=. by [].
  - split.
    + exact: HRA4.
    + exact: HSP4.
    + by rewrite Hoth4 // /rsB TInv.get_set_neq // /rsA TInv.get_set_neq //
                 Hoth2 // Hoth1 //.
    + move=> r' H1 H2 H3 H4.
      by rewrite Hoth4 // /rsB TInv.get_set_neq // /rsA TInv.get_set_neq //
                 Hoth2 // Hoth1 //.
  - by move: Htag4; rewrite EtRA.
Qed.

(** ★ The EF_std flavour, finished: the restore, then the `IReturn` that emits
    the `ERet` and steps the level down. Two lines of assembly on top of
    [ef_restore_run] — which is the point of the split, since the EF_main
    flavour reuses the same restore under a longer tail. *)
Lemma ef_cross_run C fbE cap a mem m rs pc pct L n pc' vRA vscr vSP mscr
      rcom :
  TMacros.code_at_I cde C pc
    (pop R_RA ++ pop R_AUX1 ++ store_arg (scr C) R_AUX1 R_AUX2
       ++ pop R_SP ++ [:: IReturn]) ->
  Pointer.component pc = C ->
  pct = Level n.+1 ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C, fbE, 3%Z)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  Transitional.val (Transitional.Register.get R_COM rs) = Int rcom ->
  Transitional.Memory.load m (C, fbE, 2%Z) = Some vRA ->
  tvtag vRA.1 = Ret n ->
  Transitional.val vRA.1 = Ptr pc' ->
  Transitional.Memory.load m (C, fbE, 1%Z) = Some vscr ->
  tvtag vscr.1 = Other ->
  Transitional.Memory.load m (C, fbE, 0%Z) = Some vSP ->
  tvtag vSP.1 = Other ->
  Transitional.Memory.load m (C, 1, 0%Z) = Some mscr ->
  fbE <> 1 ->
  Pointer.component pc' <> C ->
  (exists i tni,
     Transitional.executing cde pc' i tni (Pointer.component pc')) ->
  (forall b0, a C b0 <> Some fbE) ->
  ~ List.In TInv.CReg (TInv.sites L) ->
  (forall o : Z, ~ List.In (TInv.CMem (C, fbE, o)) (TInv.sites L)) ->
  ~ List.In (TInv.CMem (C, 1, 0%Z)) (TInv.sites L) ->
  (forall b0, a C b0 <> Some 1) ->
  TStack.frame_cap m C fbE cap ->
  TInject.minj a mem m ->
  TInv.tag_inv ((TInv.CMem (C, fbE, 2%Z), Ret n) :: L) m rs pct ->
  exists m' rs',
    [/\ plus TS.step cde (m, rs, pc, pct)
             [:: ERet C rcom (Pointer.component pc')]
             (m', rs', pc', dec_pc_tag pct),
        [/\ TInject.minj a mem m',
            (forall q, (Pointer.component q <> C \/ Pointer.block q <> fbE) ->
               q <> ((C, 1, 0%Z) : Pointer.t) ->
               Transitional.Memory.load m' q = Transitional.Memory.load m q),
            TMem.vload m' (C, 1, 0%Z) = Some (Transitional.val vscr.1)
          & TMem.tload m' (C, 1, 0%Z) = Some Other
            /\ Transitional.val (Transitional.Register.get R_COM rs')
               = Int rcom]
      & TInv.tag_inv L m' rs' (dec_pc_tag pct)].
Proof.
  move=> Hcode Hcomp Epct HSP HONE Hrcom HlRA EtRA EvRA Hlsc Etsc HlSP EtSP
         Hmscr HfbE1 Hnec Hex Hpriv HnotReg Hnosite Hnoscr Hscrp Hcap HI Htag.
  case: (ef_restore_run Hcode (ltac:(by []) : [:: IReturn] <> [::]) Hcomp Epct
           HSP HONE HlRA EtRA EvRA Hlsc Etsc HlSP EtSP Hmscr HfbE1 Hpriv
           HnotReg Hnosite Hnoscr Hscrp Hcap HI Htag)
    => [m4 [rs4 [pcF [Pr [EcF HcF Hmj4 Hraw4 [Hscr4 Htsc4]]
                       [HRA4 HSP4 HONE4 Hoth4] Htag4]]]].
  exists m4, (TS.invalidate_ret rs4). split.
  - eapply plus_right' with (t1 := E0)
      (t2 := [:: ERet C rcom (Pointer.component pc')]); [exact: Pr | | by []].
    rewrite -[C in ERet C _ _]EcF.
    eapply TS.JumpRet.
    + exact: (TMacros.code_at_I_head HcF).
    + by rewrite HRA4.
    + by rewrite EcF.
    + by rewrite HRA4 /= Epct.
    + by rewrite Hoth4 //.
    + case: Hex => [i0 [tni0 Hex0]]. apply: PcJump; first exact: Hex0. by [].
  - split; [exact: Hmj4 | exact: Hraw4 | exact: Hscr4
           | split; first exact: Htsc4].
    rewrite /TS.invalidate_ret TInv.get_set_neq // TInv.get_invalidateE //.
    by rewrite Hoth4.
  - rewrite Epct. apply: (TInv.tag_inv_return (n := n) erefl).
    by move: Htag4; rewrite Epct.
Qed.

(** ★ The EF_main flavour: `main`'s wrapper carries an extra CONTEXT MARKER in
    slot 3, so it pops that first and then branches on it — a nonzero marker
    means "entered from a genuine cross-component call", and the wrapper
    returns; zero would mean the machine entered `main` directly and it halts.

    The whole middle is [ef_restore_run] again; only the extra `pop R_ARG` and
    the `IBnz`/`ILabel` detour to the same `IReturn` are new. The branch
    resolves its label through the flattened component array, so this is the
    second consumer of `TLabel`'s component-wide uniqueness premise. *)
Lemma ef_cross_run_main C fbE cap a mem m rs pc pct L n pc' lret vM vRA vscr
      vSP mscr rcom z :
  TMacros.code_at_I cde C pc
    (pop R_ARG ++ pop R_RA ++ pop R_AUX1 ++ store_arg (scr C) R_AUX1 R_AUX2
       ++ pop R_SP ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn]) ->
  Pointer.component pc = C ->
  pct = Level n.+1 ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C, fbE, 4%Z)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  Transitional.val (Transitional.Register.get R_COM rs) = Int rcom ->
  (* slot 3: the context marker *)
  Transitional.Memory.load m (C, fbE, 3%Z) = Some vM ->
  tvtag vM.1 = Other ->
  Transitional.val vM.1 = Int z ->
  z <> 0%Z ->
  Transitional.Memory.load m (C, fbE, 2%Z) = Some vRA ->
  tvtag vRA.1 = Ret n ->
  Transitional.val vRA.1 = Ptr pc' ->
  Transitional.Memory.load m (C, fbE, 1%Z) = Some vscr ->
  tvtag vscr.1 = Other ->
  Transitional.Memory.load m (C, fbE, 0%Z) = Some vSP ->
  tvtag vSP.1 = Other ->
  Transitional.Memory.load m (C, 1, 0%Z) = Some mscr ->
  fbE <> 1 ->
  Pointer.component pc' <> C ->
  (exists i tni,
     Transitional.executing cde pc' i tni (Pointer.component pc')) ->
  (forall b0, a C b0 <> Some fbE) ->
  ~ List.In TInv.CReg (TInv.sites L) ->
  (forall o : Z, ~ List.In (TInv.CMem (C, fbE, o)) (TInv.sites L)) ->
  ~ List.In (TInv.CMem (C, 1, 0%Z)) (TInv.sites L) ->
  (forall b0, a C b0 <> Some 1) ->
  (forall l0 C_code, getm cde C = Some C_code ->
     count (TLabel.is_tlabel l0) C_code <= 1) ->
  TStack.frame_cap m C fbE cap ->
  TInject.minj a mem m ->
  TInv.tag_inv ((TInv.CMem (C, fbE, 2%Z), Ret n) :: L) m rs pct ->
  exists m' rs',
    [/\ plus TS.step cde (m, rs, pc, pct)
             [:: ERet C rcom (Pointer.component pc')]
             (m', rs', pc', dec_pc_tag pct),
        [/\ TInject.minj a mem m',
            (forall q, (Pointer.component q <> C \/ Pointer.block q <> fbE) ->
               q <> ((C, 1, 0%Z) : Pointer.t) ->
               Transitional.Memory.load m' q = Transitional.Memory.load m q),
            TMem.vload m' (C, 1, 0%Z) = Some (Transitional.val vscr.1)
          & TMem.tload m' (C, 1, 0%Z) = Some Other
            /\ Transitional.val (Transitional.Register.get R_COM rs')
               = Int rcom]
      & TInv.tag_inv L m' rs' (dec_pc_tag pct)].
Proof.
  move=> Hcode Hcomp Epct HSP HONE Hrcom HlM EtM EvM Hz HlRA EtRA EvRA Hlsc
         Etsc HlSP EtSP Hmscr HfbE1 Hnec Hex Hpriv HnotReg Hnosite Hnoscr
         Hscrp Huniq Hcap HI Htag.
  (* --- the extra pop: the context marker --- *)
  have Htl0 : pop R_RA ++ pop R_AUX1 ++ store_arg (scr C) R_AUX1 R_AUX2
              ++ pop R_SP ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn]
              <> [::] by [].
  have HlM' : Transitional.Memory.load m (C, fbE, (4 - 1)%Z) = Some vM
    by rewrite (_ : (4 - 1)%Z = 3%Z).
  have HnosM : ~ List.In (TInv.CMem (C, fbE, (4 - 1)%Z))
      (TInv.sites ((TInv.CMem (C, fbE, 2%Z), Ret n) :: L)).
  { rewrite (_ : (4 - 1)%Z = 3%Z) // /TInv.sites => -[E|Hin];
      last exact: Hnosite Hin.
    have Eo : 2%Z = 3%Z
      := f_equal (fun s => match s with
                           | TInv.CMem q => Pointer.offset q
                           | TInv.CReg => 0%Z
                           end) E.
    by move: Eo. }
  case: (pop_data_run Hcode Htl0 Hcomp
           (ltac:(by []) : R_ARG <> R_RA)
           (ltac:(by []) : R_SP <> R_ARG)
           (ltac:(by []) : R_ONE <> R_ARG)
           HSP HONE HlM' EtM HnosM Hcap HI Htag)
    => [m1 [rs1 [Pp0 [Hst0 Hv0 Ht0 Hcap0 Hmj0] [HSP0 HARG0 Hoth0] Htag0]]].
  (* --- the shared restore --- *)
  set pc2 := Pointer.inc (Pointer.inc pc).
  have Hcomp2 : Pointer.component pc2 = C
    by rewrite /pc2 !Pointer.inc_preserves_component.
  have Hc2 : TMacros.code_at_I cde C pc2
      (pop R_RA ++ pop R_AUX1 ++ store_arg (scr C) R_AUX1 R_AUX2
         ++ pop R_SP ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn])
    by exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hcode)).
  have HSP0' : Transitional.Register.get R_SP rs1
             = MVal Other (Ptr (C, fbE, 3%Z))
    by rewrite HSP0 (_ : (4 - 1)%Z = 3%Z).
  have HONE0 : Transitional.Register.get R_ONE rs1 = MVal Other (Int 1)
    by rewrite Hoth0.
  (* the three slots survive the marker's write-back: it is at offset 3 *)
  have Hlift : forall (o : Z) w, (o < 3)%Z ->
      Transitional.Memory.load m (C, fbE, o) = Some w ->
      Transitional.Memory.load m1 (C, fbE, o) = Some w.
  { move=> o w Ho Hl.
    have Hne : ((C, fbE, o) : Pointer.t) <> (C, fbE, (4 - 1)%Z)
      by move=> E; move: (f_equal Pointer.offset E) => /=; lia.
    by rewrite (TMem.load_store_neq Hst0 Hne). }
  have Hmscr1 : Transitional.Memory.load m1 (C, 1, 0%Z) = Some mscr.
  { have Hne : ((C, 1, 0%Z) : Pointer.t) <> (C, fbE, (4 - 1)%Z)
      by move=> E; apply: HfbE1; move: (f_equal Pointer.block E) => /= ->.
    by rewrite (TMem.load_store_neq Hst0 Hne). }
  case: (ef_restore_run Hc2 (ltac:(by []) :
           [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn] <> [::])
           Hcomp2 Epct HSP0' HONE0
           (Hlift 2%Z vRA (ltac:(by [])) HlRA) EtRA EvRA
           (Hlift 1%Z vscr (ltac:(by [])) Hlsc) Etsc
           (Hlift 0%Z vSP (ltac:(by [])) HlSP) EtSP
           Hmscr1 HfbE1 Hpriv HnotReg Hnosite Hnoscr Hscrp Hcap0 Hmj0 Htag0)
    => [m4 [rs4 [pcF [Pr [EcF HcF Hmj4 Hraw4 [Hscr4 Htsc4]]
                       [HRA4 HSP4 HONE4 Hoth4] Htag4]]]].
  (* --- the branch on the marker, then the [IReturn] --- *)
  have HARG4 : Transitional.Register.get R_ARG rs4
             = MVal Other (Transitional.val vM.1)
    by rewrite Hoth4 // HARG0.
  have HcJ : TMacros.code_at_I cde C pcF
      ([:: IBnz R_ARG lret; IHalt] ++ ILabel lret :: [:: IReturn])
    by exact: HcF.
  case: (TMacros.code_at_I_label_find HcJ EcF Huniq) => [pcL [Hfind EcL HcL]].
  have HcB : TMacros.code_at_I cde C pcF
      (IBnz R_ARG lret :: IHalt :: [:: ILabel lret; IReturn]) by exact: HcF.
  have SB : TS.step cde (m4, rs4, pcF, pct) E0 (m4, rs4, pcL, pct).
  { eapply TS.BnzNZ.
    - exact: (TMacros.code_at_I_head HcB).
    - exact: (TMacros.check_pc_at_I HcB).
    - by rewrite HARG4.
    - by rewrite HARG4 /= EvM.
    - exact: Hz.
    - by rewrite EcF; exact: Hfind.
    - apply: PcJump; first exact: (TMacros.code_at_I_head HcL).
      by rewrite EcL EcF. }
  have HcL2 : TMacros.code_at_I cde C pcL (ILabel lret :: [:: IReturn])
    by exact: HcL.
  have SL : TS.step cde (m4, rs4, pcL, pct) E0
            (m4, rs4, Pointer.inc pcL, pct).
  { eapply TS.Label; [exact: (TMacros.code_at_I_head HcL2)
                     | exact: (TMacros.check_pc_at_I HcL2)]. }
  have HcR : TMacros.code_at_I cde C (Pointer.inc pcL) [:: IReturn]
    by exact: (TMacros.code_at_I_tail HcL2).
  exists m4, (TS.invalidate_ret rs4). split.
  - eapply plus_trans; [exact: Pp0 | | by []].
    eapply plus_trans; [exact: Pr | | by []].
    eapply plus_left with (t1 := E0)
      (t2 := [:: ERet C rcom (Pointer.component pc')]); [exact: SB | | by []].
    eapply star_step with (t1 := E0)
      (t2 := [:: ERet C rcom (Pointer.component pc')]); [exact: SL | | by []].
    apply: star_one.
    have EcR : Pointer.component (Pointer.inc pcL) = C
      by rewrite Pointer.inc_preserves_component.
    rewrite -[C in ERet C _ _]EcR.
    eapply TS.JumpRet.
    + exact: (TMacros.code_at_I_head HcR).
    + by rewrite HRA4.
    + by rewrite EcR.
    + by rewrite HRA4 /= Epct.
    + by rewrite Hoth4 // Hoth0 //.
    + case: Hex => [i0 [tni0 Hex0]]. apply: PcJump; first exact: Hex0. by [].
  - split.
    + exact: Hmj4.
    + (* compose with the marker pop's write-back, which is also in [fbE] *)
      move=> q Hq1 Hq2. rewrite (Hraw4 q Hq1 Hq2).
      have Hne : q <> ((C, fbE, (4 - 1)%Z) : Pointer.t)
        by move=> E; case: Hq1 => H; apply: H; rewrite E.
      by rewrite (TMem.load_store_neq Hst0 Hne).
    + exact: Hscr4.
    + split; first exact: Htsc4.
      rewrite /TS.invalidate_ret TInv.get_set_neq // TInv.get_invalidateE //.
      by rewrite Hoth4 // Hoth0 //.
  - rewrite Epct. apply: (TInv.tag_inv_return (n := n) erefl).
    by move: Htag4; rewrite Epct.
Qed.

(** ★ MAIN's exit. The same wrapper epilogue as [ef_cross_run_main], but for
    the activation the MACHINE entered rather than a caller: the context marker
    in slot 3 is `Int 0`, so the closing `IBnz` is NOT taken and control falls
    through to the `IHalt`.

    Two things distinguish it from every other epilogue in the file, and both
    come from the same fact — main's initial activation has no caller:

    - slot 2 holds JUNK rather than a return capability ([pop_junk_ra_run]),
      and the body's own [InternalJump] is simply dropped from the ledger;
    - the run ends at an instruction rather than at a jump target, so what it
      exports is an [executing … TrHalt], which is exactly `t_final`. *)
Lemma ef_halt_run C fbE cap a mem m rs pc pct L lret vM vRA vscr vSP mscr
      told :
  TMacros.code_at_I cde C pc
    (pop R_ARG ++ pop R_RA ++ pop R_AUX1 ++ store_arg (scr C) R_AUX1 R_AUX2
       ++ pop R_SP ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn]) ->
  Pointer.component pc = C ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C, fbE, 4%Z)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  Transitional.Memory.load m (C, fbE, 3%Z) = Some vM ->
  tvtag vM.1 = Other ->
  Transitional.val vM.1 = Int 0 ->
  Transitional.Memory.load m (C, fbE, 2%Z) = Some vRA ->
  ~~ TInv.is_live (tvtag vRA.1) ->
  Transitional.Memory.load m (C, fbE, 1%Z) = Some vscr ->
  tvtag vscr.1 = Other ->
  Transitional.Memory.load m (C, fbE, 0%Z) = Some vSP ->
  tvtag vSP.1 = Other ->
  Transitional.Memory.load m (C, 1, 0%Z) = Some mscr ->
  fbE <> 1 ->
  (forall b0, a C b0 <> Some fbE) ->
  ~ List.In TInv.CReg (TInv.sites L) ->
  (forall o : Z, ~ List.In (TInv.CMem (C, fbE, o)) (TInv.sites L)) ->
  ~ List.In (TInv.CMem (C, 1, 0%Z)) (TInv.sites L) ->
  (forall b0, a C b0 <> Some 1) ->
  TInv.is_ret told = false ->
  TStack.frame_cap m C fbE cap ->
  TInject.minj a mem m ->
  TInv.tag_inv ((TInv.CReg, told) :: L) m rs pct ->
  exists m' rs' pcH,
    [/\ plus TS.step cde (m, rs, pc, pct) E0 (m', rs', pcH, pct),
        TInject.minj a mem m'
      & exists tg c, Transitional.executing cde pcH Transitional.TrHalt tg c].
Proof.
  move=> Hcode Hcomp HSP HONE HlM EtM EvM HlRA HdeadRA Hlsc Etsc HlSP EtSP
         Hmscr HfbE1 Hpriv HnotReg Hnosite Hnoscr Hscrp Hret Hcap HI Htag.
  have Hnosite1 : forall o : Z,
      ~ List.In (TInv.CMem (C, fbE, o))
                (TInv.sites ((TInv.CReg, told) :: L))
    by move=> o /= [E|Hin]; [ | exact: Hnosite Hin].
  have Hnoscr1 : ~ List.In (TInv.CMem (C, 1, 0%Z))
                   (TInv.sites ((TInv.CReg, told) :: L))
    by move=> /= [E|Hin]; [ | exact: Hnoscr Hin].
  (* --- 1. pop R_ARG: the context marker --- *)
  have Htl0 : pop R_RA ++ pop R_AUX1 ++ store_arg (scr C) R_AUX1 R_AUX2
              ++ pop R_SP ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn]
              <> [::] by [].
  have HlM' : Transitional.Memory.load m (C, fbE, (4 - 1)%Z) = Some vM
    by rewrite (_ : (4 - 1)%Z = 3%Z).
  case: (pop_data_run Hcode Htl0 Hcomp
           (ltac:(by []) : R_ARG <> R_RA)
           (ltac:(by []) : R_SP <> R_ARG)
           (ltac:(by []) : R_ONE <> R_ARG)
           HSP HONE HlM' EtM (Hnosite1 (4 - 1)%Z) Hcap HI Htag)
    => [m1 [rs1 [Pp0 [Hst0 Hv0 Ht0 Hcap0 Hmj0] [HSP0 HARG0 Hoth0] Htag0]]].
  have Hlift : forall (o : Z) w, (o < 3)%Z ->
      Transitional.Memory.load m (C, fbE, o) = Some w ->
      Transitional.Memory.load m1 (C, fbE, o) = Some w.
  { move=> o w Ho Hl.
    have Hne : ((C, fbE, o) : Pointer.t) <> (C, fbE, (4 - 1)%Z)
      by move=> E; move: (f_equal Pointer.offset E) => /=; lia. 
    by rewrite (TMem.load_store_neq Hst0 Hne). }
  have Hmscr1 : Transitional.Memory.load m1 (C, 1, 0%Z) = Some mscr.
  { have Hne : ((C, 1, 0%Z) : Pointer.t) <> (C, fbE, (4 - 1)%Z)
      by move=> E; apply: HfbE1; move: (f_equal Pointer.block E) => /= ->.
    by rewrite (TMem.load_store_neq Hst0 Hne). }
  (* --- 2. pop R_RA: the JUNK where a caller would have left a capability *)
  set pc2 := Pointer.inc (Pointer.inc pc).
  have Hcomp2 : Pointer.component pc2 = C
    by rewrite /pc2 !Pointer.inc_preserves_component.
  have Hc2 : TMacros.code_at_I cde C pc2
      (pop R_RA ++ pop R_AUX1 ++ store_arg (scr C) R_AUX1 R_AUX2
         ++ pop R_SP ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn])
    by exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hcode)).
  have HSP0' : Transitional.Register.get R_SP rs1
             = MVal Other (Ptr (C, fbE, 3%Z))
    by rewrite HSP0 (_ : (4 - 1)%Z = 3%Z).
  have HONE0 : Transitional.Register.get R_ONE rs1 = MVal Other (Int 1)
    by rewrite Hoth0.
  have HlRA1 : Transitional.Memory.load m1 (C, fbE, (3 - 1)%Z) = Some vRA
    by rewrite (_ : (3 - 1)%Z = 2%Z) //; exact: (Hlift 2%Z vRA (ltac:(by []))).
  case: (pop_junk_ra_run Hc2
           (ltac:(by []) : pop R_AUX1 ++ store_arg (scr C) R_AUX1 R_AUX2
              ++ pop R_SP ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn]
              <> [::])
           Hcomp2 HSP0' HONE0 HlRA1 HdeadRA
           (ltac:(by rewrite (_ : (3 - 1)%Z = 2%Z) //; exact: Hnosite 2%Z)
            : ~ List.In (TInv.CMem (C, fbE, (3 - 1)%Z)) (TInv.sites L))
           Hpriv Hret Hcap0 Hmj0 Htag0)
    => [m2 [rs2 [Pp1 [Hv1 Hraw1 Hcap1 Hmj1] [HSP1 Hoth1] Htag1]]].
  (* --- 3. pop R_AUX1: the inherited scratch value --- *)
  set pc4 := Pointer.inc (Pointer.inc pc2).
  have Hcomp4 : Pointer.component pc4 = C
    by rewrite /pc4 /pc2 !Pointer.inc_preserves_component.
  have Hc4 : TMacros.code_at_I cde C pc4
      (pop R_AUX1 ++ store_arg (scr C) R_AUX1 R_AUX2
         ++ pop R_SP ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn])
    by exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hc2)).
  have Hne21 : ((C, fbE, 1%Z) : Pointer.t) <> (C, fbE, (3 - 1)%Z)
    by move=> E; move: (f_equal Pointer.offset E) => /=; lia.
  have Hlsc2 : Transitional.Memory.load m2 (C, fbE, ((3 - 1) - 1)%Z)
             = Some vscr
    by rewrite (_ : ((3 - 1) - 1)%Z = 1%Z) // (Hraw1 _ Hne21);
       exact: (Hlift 1%Z vscr (ltac:(by []))).
  have HSP1' : Transitional.Register.get R_SP rs2
             = MVal Other (Ptr (C, fbE, (3 - 1)%Z)) by exact: HSP1.
  have HONE1 : Transitional.Register.get R_ONE rs2 = MVal Other (Int 1)
    by rewrite Hoth1.
  case: (pop_data_run Hc4
           (ltac:(by []) : store_arg (scr C) R_AUX1 R_AUX2 ++ pop R_SP
              ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn] <> [::])
           Hcomp4
           (ltac:(by []) : R_AUX1 <> R_RA)
           (ltac:(by []) : R_SP <> R_AUX1)
           (ltac:(by []) : R_ONE <> R_AUX1)
           HSP1' HONE1 Hlsc2 Etsc (Hnosite ((3 - 1) - 1)%Z) Hcap1 Hmj1 Htag1)
    => [m3 [rs3 [Pp2 [Hst2 Hv2 Ht2 Hcap2 Hmj2] [HSP2 HA12 Hoth2] Htag2]]].
  (* --- 4. store_arg: hand the inherited scratch back --- *)
  set pc6 := Pointer.inc (Pointer.inc pc4).
  have Hcomp6 : Pointer.component pc6 = C
    by rewrite /pc6 /pc4 /pc2 !Pointer.inc_preserves_component.
  have Hc6 : TMacros.code_at_I cde C pc6
      (IConst (IPtr (scr C)) R_AUX2
         :: IStore R_AUX2 R_AUX1 :: pop R_SP
            ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn])
    by exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hc4)).
  have Hc7 := TMacros.code_at_I_tail Hc6.
  have SC : TS.step cde (m3, rs3, pc6, pct) E0
            (m3, Transitional.Register.set R_AUX2 (Ptr (scr C)) Other rs3,
             Pointer.inc pc6, pct).
  { have -> : Ptr (scr C) = imm_to_val (IPtr (scr C)) by [].
    eapply TS.Const; [exact: (TMacros.code_at_I_head Hc6)
                     | exact: (TMacros.check_pc_at_I Hc6)]. }
  set rsA := (Transitional.Register.set R_AUX2 (Ptr (scr C)) Other rs3) in SC *.
  have Hmscr3 : Transitional.Memory.load m3 (C, 1, 0%Z) = Some mscr.
  { have Hne1 : ((C, 1, 0%Z) : Pointer.t) <> (C, fbE, (3 - 1)%Z)
      by move=> E; apply: HfbE1; move: (f_equal Pointer.block E) => /= ->.
    have Hne2 : ((C, 1, 0%Z) : Pointer.t) <> (C, fbE, ((3 - 1) - 1)%Z)
      by move=> E; apply: HfbE1; move: (f_equal Pointer.block E) => /= ->.
    by rewrite (TMem.load_store_neq Hst2 Hne2) (Hraw1 _ Hne1). }
  case: (TMem.store_after_load
           (Transitional.Register.get R_AUX1 rsA,
            {| vtag := Other; color := C; entry := None; is_code := false |})
           Hmscr3) => [m4 Hst3].
  have HA1A : Transitional.Register.get R_AUX1 rsA
            = MVal Other (Transitional.val vscr.1)
    by rewrite /rsA TInv.get_set_neq // HA12.
  have HtagA : TInv.tag_inv L m3 rsA pct
    by apply: TInv.tag_inv_setreg; [by [] | exact: Htag2].
  have SS : TS.step cde (m3, rsA, Pointer.inc pc6, pct) E0
            (m4, Transitional.Register.set R_AUX1
                   (Transitional.val (Transitional.Register.get R_AUX1 rsA))
                   Other rsA,
             Pointer.inc (Pointer.inc pc6), pct).
  { have -> : Other = (if is_address Other then Invalidated else Other) by [].
    eapply TS.Store.
    - exact: (TMacros.code_at_I_head Hc7).
    - exact: (TMacros.check_pc_at_I Hc7).
    - by rewrite /rsA TInv.get_set_eq.
    - by rewrite /rsA TInv.get_set_eq.
    - by rewrite /= Pointer.inc_preserves_component Hcomp6.
    - apply: (TInv.ti_tag_other HtagA). by [].
    - by rewrite Pointer.inc_preserves_component Hcomp6; exact: Hst3. }
  set rsB := Transitional.Register.set R_AUX1
               (Transitional.val (Transitional.Register.get R_AUX1 rsA))
               Other rsA.
  have HtagB : TInv.tag_inv L m4 rsB pct.
  { apply: TInv.tag_inv_setreg; first by [].
    apply: (TInv.tag_inv_store_data Hnoscr _ Hst3 HtagA). by rewrite /= HA1A. }
  have Hmj4 : TInject.minj a mem m4
    by apply: (TInject.minj_store_outside _ Hst3 Hmj2) => b0; exact: Hscrp b0.
  have Hcap4 : TStack.frame_cap m4 C fbE cap
    by exact: (TStack.frame_cap_store Hst3 Hcap2).
  (* --- 5. pop R_SP: the caller's frame pointer --- *)
  set pc8 := Pointer.inc (Pointer.inc pc6).
  have Hcomp8 : Pointer.component pc8 = C
    by rewrite /pc8 /pc6 /pc4 /pc2 !Pointer.inc_preserves_component.
  have Hc8 : TMacros.code_at_I cde C pc8
      (pop R_SP ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn])
    by exact: (TMacros.code_at_I_tail Hc7).
  have HSPB : Transitional.Register.get R_SP rsB
            = MVal Other (Ptr (C, fbE, ((3 - 1) - 1)%Z))
    by rewrite /rsB TInv.get_set_neq // /rsA TInv.get_set_neq //; exact: HSP2.
  have HONEB : Transitional.Register.get R_ONE rsB = MVal Other (Int 1)
    by rewrite /rsB TInv.get_set_neq // /rsA TInv.get_set_neq // Hoth2 //.
  have HlSP4 : Transitional.Memory.load m4
      (C, fbE, (((3 - 1) - 1) - 1)%Z) = Some vSP.
  { have Hne3 : ((C, fbE, 0%Z) : Pointer.t) <> (C, 1, 0%Z)
      by move=> E; apply: HfbE1; move: (f_equal Pointer.block E) => /= ->.
    have Hne2 : ((C, fbE, 0%Z) : Pointer.t) <> (C, fbE, ((3 - 1) - 1)%Z)
      by move=> E; move: (f_equal Pointer.offset E) => /=; lia.
    have Hne1 : ((C, fbE, 0%Z) : Pointer.t) <> (C, fbE, (3 - 1)%Z)
      by move=> E; move: (f_equal Pointer.offset E) => /=; lia.
    rewrite (_ : (((3 - 1) - 1) - 1)%Z = 0%Z) //.
    by rewrite (TMem.load_store_neq Hst3 Hne3) (TMem.load_store_neq Hst2 Hne2)
               (Hraw1 _ Hne1); exact: (Hlift 0%Z vSP (ltac:(by []))). }
  case: (pop_sp_run Hc8
           (ltac:(by []) :
              [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn] <> [::])
           Hcomp8 HSPB HONEB HlSP4 EtSP (Hnosite (((3 - 1) - 1) - 1)%Z)
           Hcap4 Hmj4 HtagB)
    => [m5 [rs5 [Pp4 [Hst4 Hv4 Ht4 Hcap5 Hmj5] [HSP4 Hoth4] Htag4]]].
  (* --- 6. the branch is NOT taken: control falls through to [IHalt] --- *)
  set pc10 := Pointer.inc (Pointer.inc pc8).
  have Hc10 : TMacros.code_at_I cde C pc10
      (IBnz R_ARG lret :: IHalt :: [:: ILabel lret; IReturn])
    by exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hc8)).
  have HARG4 : Transitional.Register.get R_ARG rs5
             = MVal Other (Transitional.val vM.1).
  { by rewrite Hoth4 // /rsB TInv.get_set_neq // /rsA TInv.get_set_neq //
               Hoth2 // Hoth1 //. }
  have SB : TS.step cde (m5, rs5, pc10, pct) E0
            (m5, rs5, Pointer.inc pc10, pct).
  { eapply TS.BnzZ.
    - exact: (TMacros.code_at_I_head Hc10).
    - exact: (TMacros.check_pc_at_I Hc10).
    - by rewrite HARG4.
    - by rewrite HARG4 /= EvM. }
  have HcH := TMacros.code_at_I_tail Hc10.
  exists m5, rs5, (Pointer.inc pc10). split.
  - eapply plus_trans with (t1 := E0) (t2 := E0); [exact: Pp0 | | by []].
    eapply plus_trans with (t1 := E0) (t2 := E0); [exact: Pp1 | | by []].
    eapply plus_trans with (t1 := E0) (t2 := E0); [exact: Pp2 | | by []].
    eapply plus_left with (t1 := E0) (t2 := E0); [exact: SC | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: SS | | by []].
    eapply star_trans with (t1 := E0) (t2 := E0);
      [exact: (plus_star Pp4) | | by []].
    exact: star_one SB.
  - exact: Hmj5.
  - by do 2!eexists; exact: (TMacros.code_at_I_head HcH).
Qed.

(** ★ Either flavour, from the relation rather than the slots: the diagram has
    an `ext_frame_match`, not a pile of `vload`s, so this is the interface it
    actually wants. Casing on the two constructors dispatches to
    [ef_cross_run] / [ef_cross_run_main]; both `spE` values (3 and 4) come out
    of the relation, so the caller never has to know which wrapper it has. *)
Lemma ef_cross_any C fbE spE sE cap a mem m rs pc pct L n pc' mscr rcom :
  TSM.ext_frame_match cde m C fbE pc spE sE ->
  TStack.ra_tag sE = Ret n ->
  TStack.ra_ret sE = pc' ->
  Pointer.component pc = C ->
  pct = Level n.+1 ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C, fbE, spE)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  Transitional.val (Transitional.Register.get R_COM rs) = Int rcom ->
  Transitional.Memory.load m (C, 1, 0%Z) = Some mscr ->
  fbE <> 1 ->
  Pointer.component pc' <> C ->
  (exists i tni,
     Transitional.executing cde pc' i tni (Pointer.component pc')) ->
  (forall b0, a C b0 <> Some fbE) ->
  ~ List.In TInv.CReg (TInv.sites L) ->
  (forall o : Z, ~ List.In (TInv.CMem (C, fbE, o)) (TInv.sites L)) ->
  ~ List.In (TInv.CMem (C, 1, 0%Z)) (TInv.sites L) ->
  (forall b0, a C b0 <> Some 1) ->
  (forall l0 C_code, getm cde C = Some C_code ->
     count (TLabel.is_tlabel l0) C_code <= 1) ->
  TStack.frame_cap m C fbE cap ->
  TInject.minj a mem m ->
  TInv.tag_inv ((TInv.CMem (C, fbE, 2%Z), Ret n) :: L) m rs pct ->
  exists m' rs' v,
    [/\ plus TS.step cde (m, rs, pc, pct)
             [:: ERet C rcom (Pointer.component pc')]
             (m', rs', pc', dec_pc_tag pct),
        [/\ TInject.minj a mem m',
            (forall q, (Pointer.component q <> C \/ Pointer.block q <> fbE) ->
               q <> ((C, 1, 0%Z) : Pointer.t) ->
               Transitional.Memory.load m' q = Transitional.Memory.load m q),
            TMem.vload m (C, fbE, 1%Z) = Some v
          & TMem.vload m' (C, 1, 0%Z) = Some v
            /\ TMem.tload m' (C, 1, 0%Z) = Some Other
            /\ Transitional.val (Transitional.Register.get R_COM rs')
               = Int rcom]
      & TInv.tag_inv L m' rs' (dec_pc_tag pct)].
Proof.
  move=> Hef EtagE EretE Hcomp Epct HSP HONE Hrcom Hmscr HfbE1 Hnec Hex Hpriv
         HnotReg Hnosite Hnoscr Hscrp Huniq Hcap HI Htag.
  (* the capability slot's contents, from the chain fact the relation carries *)
  have Hslot : TStack.slots_ok m [:: sE]
    by case: (TSM.ext_frame_slot Hef).
  case: (Hslot sE (or_introl erefl)) => [Hvs [Hts _]].
  have EaE : TStack.ra_addr sE = (C, fbE, 2%Z)
    by case: (TSM.ext_frame_slot Hef).
  have [vRA HlRA] : exists vRA,
      Transitional.Memory.load m (C, fbE, 2%Z) = Some vRA
    by move: Hvs; rewrite EaE; exact: TMem.vload_load.
  have EtRA : tvtag vRA.1 = Ret n
    by move: Hts; rewrite EaE /TMem.tload HlRA /= EtagE => -[<-].
  have EvRA : Transitional.val vRA.1 = Ptr pc'
    by move: Hvs; rewrite EaE /TMem.vload HlRA /= EretE => -[<-].
  case: (TSM.ext_frame_cases Hef)
    => [[v0 [v1 [Esp Hcode [L0 L1] [T0 T1]]]]
       |[lret [v0 [v1 [z [Esp Hcode [L0 [L1 L3]] [T0 [T1 T3]] Hz]]]]]].
  - (* EF_std: [spE = 3] *)
    have [w0 Hl0] := TMem.vload_load L0.
    have [w1 Hl1] := TMem.vload_load L1.
    move: HSP; rewrite Esp => HSP.
    case: (ef_cross_run Hcode Hcomp Epct HSP HONE Hrcom HlRA EtRA EvRA
             Hl1 (ltac:(by move: T1; rewrite /TMem.tload Hl1 /= => -[<-]))
             Hl0 (ltac:(by move: T0; rewrite /TMem.tload Hl0 /= => -[<-]))
             Hmscr HfbE1 Hnec Hex Hpriv HnotReg Hnosite Hnoscr Hscrp Hcap HI
             Htag) => [m' [rs' [Pl [Hmj Hraw Hscr [Htsc Hcom]] Htg]]].
    exists m', rs', (Transitional.val w1.1). split=> //.
    split; [exact: Hmj | exact: Hraw
           | by move: L1; rewrite /TMem.vload Hl1
           | by split; last split].
  - (* EF_main: [spE = 4], with the context marker in slot 3 *)
    have [w0 Hl0] := TMem.vload_load L0.
    have [w1 Hl1] := TMem.vload_load L1.
    have [w3 Hl3] := TMem.vload_load L3.
    move: HSP; rewrite Esp => HSP.
    have Et3 : tvtag w3.1 = Other
      by move: T3; rewrite /TMem.tload Hl3 /= => -[<-].
    have Ev3 : Transitional.val w3.1 = Int z
      by move: L3; rewrite /TMem.vload Hl3 /= => -[<-].
    case: (ef_cross_run_main Hcode Hcomp Epct HSP HONE Hrcom
             Hl3 Et3 Ev3 Hz
              HlRA EtRA EvRA
              Hl1 (ltac:(by move: T1; rewrite /TMem.tload Hl1 /= => -[<-]))
              Hl0 (ltac:(by move: T0; rewrite /TMem.tload Hl0 /= => -[<-]))
             Hmscr HfbE1 Hnec Hex Hpriv HnotReg Hnosite Hnoscr Hscrp Huniq
             Hcap HI Htag) => [m' [rs' [Pl [Hmj Hraw Hscr [Htsc Hcom]] Htg]]].
    exists m', rs', (Transitional.val w1.1). split=> //.
    split; [exact: Hmj | exact: Hraw
           | by move: L1; rewrite /TMem.vload Hl1
           | by split; last split].
Qed.

(** ★ The CALLER's resumption after its own `ICall`:

        IConst 1 R_ONE ; reload_sp (scr C) ; pop R_ARG ; pop R_RA

    `ICall` invalidates the register file, so the caller reconstructs itself:
    `R_ONE` by a constant, `R_SP` from the scratch cell it saved before the
    call, then the two spilled values. The last is `pop_ra_run` — the caller's
    own `InternalJump` capability coming back out of memory.

    Note the third step is an `ILoad`, so it WRITES THE SCRATCH CELL BACK. That
    is harmless here for the usual reason (an `Other`-tagged cell is rewritten
    with the same tvalue), but it is why `tvtag mscr.1 = Other` is a premise:
    the load copies the cell's tag into `R_SP`, and `ti_regs` requires `Other`.
    This is the fifth place the machine forces a tag to be pinned, and the
    invariant clause that will discharge it — a tag clause on `scrs_ok` — is the
    one remaining strengthening of the same family. *)
Lemma icall_resume_run C fb cap a mem m rs pc pct L (temps : seq value)
      mscr vARG vRA nxt rest :
  TMacros.code_at_I cde C pc
    (IConst (IInt 1) R_ONE :: reload_sp (scr C) ++ pop R_ARG ++ pop R_RA
       ++ nxt :: rest) ->
  Pointer.component pc = C ->
  Transitional.Memory.load m (C, 1, 0%Z) = Some mscr ->
  tvtag mscr.1 = Other ->
  Transitional.val mscr.1 = Ptr (C, fb, Z.of_nat (2 + size temps + 2)) ->
  Transitional.Memory.load m (C, fb, Z.of_nat (2 + size temps + 1))
    = Some vARG ->
  tvtag vARG.1 = Other ->
  Transitional.Memory.load m (C, fb, Z.of_nat (2 + size temps)) = Some vRA ->
  TInv.is_live (tvtag vRA.1) ->
  fb <> 1 ->
  (forall b0, a C b0 <> Some fb) ->
  (forall b0, a C b0 <> Some 1) ->
  ~ List.In TInv.CReg (TInv.sites L) ->
  (forall o : Z, ~ List.In (TInv.CMem (C, fb, o)) (TInv.sites L)) ->
  ~ List.In (TInv.CMem (C, 1, 0%Z)) (TInv.sites L) ->
  TStack.frame_cap m C fb cap ->
  TInject.minj a mem m ->
  TInv.tag_inv
    ((TInv.CMem (C, fb, Z.of_nat (2 + size temps)), tvtag vRA.1) :: L)
    m rs pct ->
  exists m' rs' pcF,
    [/\ plus TS.step cde (m, rs, pc, pct) E0 (m', rs', pcF, pct),
        [/\ TStack.frame_cap m' C fb cap,
            TInject.minj a mem m',
            Pointer.component pcF = C,
            TMacros.code_at_I cde C pcF (nxt :: rest)
          & exists mmid c,
              [/\ (forall q, TMem.vload mmid q = TMem.vload m q),
                  (forall q, TMem.tload mmid q = TMem.tload m q),
                  Transitional.Memory.store mmid
                    (C, fb, Z.of_nat (2 + size temps)) c = Some m'
                & forall q, TMem.vload m' q = TMem.vload mmid q]],
        [/\ Transitional.Register.get R_ONE rs' = MVal Other (Int 1),
            Transitional.Register.get R_SP rs'
              = MVal Other (Ptr (C, fb, Z.of_nat (2 + size temps))),
            Transitional.Register.get R_ARG rs'
              = MVal Other (Transitional.val vARG.1),
            Transitional.Register.get R_RA rs'
              = MVal (tvtag vRA.1) (Transitional.val vRA.1)
          & forall r', r' <> R_ONE -> r' <> R_AUX2 -> r' <> R_SP ->
              r' <> R_ARG -> r' <> R_RA ->
              Transitional.Register.get r' rs'
              = Transitional.Register.get r' rs]
      & TInv.tag_inv ((TInv.CReg, tvtag vRA.1) :: L) m' rs' pct].
Proof.
  move=> Hcode Hcomp Hmscr Etm Evm HlA EtA HlR HliveR Hfb1 Hpriv Hscrp
         HnotReg Hnosite Hnoscr Hcap HI Htag.
  have Hc0 : TMacros.code_at_I cde C pc
      (IConst (IInt 1) R_ONE :: IConst (IPtr (scr C)) R_AUX2
         :: ILoad R_AUX2 R_SP :: pop R_ARG ++ pop R_RA ++ nxt :: rest)
    by exact: Hcode.
  have Hc1 := TMacros.code_at_I_tail Hc0.
  have Hc2 := TMacros.code_at_I_tail Hc1.
  have Hc3 := TMacros.code_at_I_tail Hc2.
  (* --- 1/2. the two constants --- *)
  have S1 : TS.step cde (m, rs, pc, pct) E0
            (m, Transitional.Register.set R_ONE (Int 1) Other rs,
             Pointer.inc pc, pct).
  { have -> : Int 1 = imm_to_val (IInt 1) by [].
    eapply TS.Const; [exact: (TMacros.code_at_I_head Hc0)
                     | exact: (TMacros.check_pc_at_I Hc0)]. }
  set rs1 := (Transitional.Register.set R_ONE (Int 1) Other rs) in S1 *.
  have S2 : TS.step cde (m, rs1, Pointer.inc pc, pct) E0
            (m, Transitional.Register.set R_AUX2 (Ptr (scr C)) Other rs1,
             Pointer.inc (Pointer.inc pc), pct).
  { have -> : Ptr (scr C) = imm_to_val (IPtr (scr C)) by [].
    eapply TS.Const; [exact: (TMacros.code_at_I_head Hc1)
                     | exact: (TMacros.check_pc_at_I Hc1)]. }
  set rs2 := (Transitional.Register.set R_AUX2 (Ptr (scr C)) Other rs1) in S2 *.
  (* --- 3. reload R_SP from the scratch cell --- *)
  case: (TMem.store_after_load
           ({| Transitional.val := Transitional.val mscr.1; tvtag := Other |},
            {| vtag := Other; color := C; entry := None; is_code := false |})
           Hmscr) => [m1 Hst1].
  have Hstr1 : Transitional.Memory.store m (C, 1, 0%Z)
      ({| Transitional.val := Transitional.val mscr.1;
          tvtag := if is_address (tvtag mscr.1) then Invalidated else Other |},
       {| vtag := if is_address (tvtag mscr.1) then Invalidated else Other;
          color := Pointer.component (Pointer.inc (Pointer.inc pc));
          entry := None; is_code := false |}) = Some m1
    by rewrite Etm /= !Pointer.inc_preserves_component Hcomp; exact: Hst1.
  have S3 : TS.step cde (m, rs2, Pointer.inc (Pointer.inc pc), pct) E0
            (m1, Transitional.Register.set R_SP (Transitional.val mscr.1)
                   (tvtag mscr.1) rs2,
             Pointer.inc (Pointer.inc (Pointer.inc pc)), pct).
  { eapply TS.Load.
    - exact: (TMacros.code_at_I_head Hc2).
    - exact: (TMacros.check_pc_at_I Hc2).
    - by rewrite /rs2 TInv.get_set_eq.
    - by rewrite /rs2 TInv.get_set_eq.
    - by rewrite /= !Pointer.inc_preserves_component Hcomp.
    - exact: Hmscr.
    - exact: Hstr1. }
  set rs3 := (Transitional.Register.set R_SP (Transitional.val mscr.1)
                (tvtag mscr.1) rs2) in S3 *.
  (* the reload is invisible: the cell keeps its tvalue *)
  have Hv1 : forall q, TMem.vload m1 q = TMem.vload m q.
  { move=> q. apply: (TMem.vload_store_same Hmscr _ Hst1 q). by []. }
  have Ht1 : forall q, TMem.tload m1 q = TMem.tload m q.
  { move=> q. apply: (TMem.tload_store_same Hmscr _ Hst1 q). by rewrite /= Etm. }
  have Hraw1 : forall q, q <> ((C, 1, 0%Z) : Pointer.t) ->
      Transitional.Memory.load m1 q = Transitional.Memory.load m q
    by move=> q Hq; exact: (TMem.load_store_neq Hst1 Hq).
  have Hnefb : forall (o o' : Z),
      ((C, fb, o) : Pointer.t) <> (C, 1, o')
    by move=> o o' E; apply: Hfb1; move: (f_equal Pointer.block E) => /= ->.
  have Htag3 : TInv.tag_inv
      ((TInv.CMem (C, fb, Z.of_nat (2 + size temps)), tvtag vRA.1) :: L)
      m1 rs3 pct.
  { rewrite /rs3 Etm.
    apply: TInv.tag_inv_setreg; first by [].
    apply: (TInv.tag_inv_store_data _ _ Hst1); last first.
    - rewrite /rs2 /rs1. apply: TInv.tag_inv_setreg; first by [].
      apply: TInv.tag_inv_setreg; first by []. exact: Htag.
    - by [].
    - move=> /= [E|Hin]; last exact: Hnoscr Hin.
      apply: Hfb1.
      have Ep : ((C, 1, 0%Z) : Pointer.t)
              = (C, fb, Z.of_nat (2 + size temps)) by congruence.
      have Eb : 1 = fb := f_equal Pointer.block Ep. by rewrite Eb. }
  (* --- 4. pop R_ARG --- *)
  set pc3 := Pointer.inc (Pointer.inc (Pointer.inc pc)).
  have Hcomp3 : Pointer.component pc3 = C
    by rewrite /pc3 !Pointer.inc_preserves_component.
  have Htl3 : pop R_RA ++ nxt :: rest <> [::] by [].
  have HSP3 : Transitional.Register.get R_SP rs3
            = MVal Other (Ptr (C, fb, Z.of_nat (2 + size temps + 2)))
    by rewrite /rs3 TInv.get_set_eq Etm Evm.
  have HONE3 : Transitional.Register.get R_ONE rs3 = MVal Other (Int 1)
    by rewrite /rs3 TInv.get_set_neq // /rs2 TInv.get_set_neq // /rs1
               TInv.get_set_eq.
  have Eoff1 : (Z.of_nat (2 + size temps + 2) - 1)%Z
             = Z.of_nat (2 + size temps + 1) by lia.
  have HlA1 : Transitional.Memory.load m1
      (C, fb, (Z.of_nat (2 + size temps + 2) - 1)%Z) = Some vARG
    by rewrite Eoff1 Hraw1 //; exact: (Hnefb _ 0%Z).
  have Hcap1 : TStack.frame_cap m1 C fb cap
    by move=> j Hj; rewrite Hv1; exact: Hcap Hj.
  have Hmj1 : TInject.minj a mem m1.
  { apply: (TInject.minj_store_outside _ Hst1 HI) => b0. exact: Hscrp b0. }
  (* the ARG slot is one ABOVE the capability's, so it is not that site *)
  have HnosA : ~ List.In
      (TInv.CMem (C, fb, (Z.of_nat (2 + size temps + 2) - 1)%Z))
      (TInv.sites ((TInv.CMem (C, fb, Z.of_nat (2 + size temps)),
                    tvtag vRA.1) :: L)).
  { rewrite Eoff1 /TInv.sites => -[E|Hin]; last exact: Hnosite Hin.
    (* project the offset straight out of the [capsite] equation *)
    have Eo : Z.of_nat (2 + size temps) = Z.of_nat (2 + size temps + 1)
      := f_equal (fun s => match s with
                           | TInv.CMem q => Pointer.offset q
                           | TInv.CReg => 0%Z
                           end) E.
    move: Eo. lia. }
  case: (pop_data_run Hc3 Htl3 Hcomp3
           (ltac:(by []) : R_ARG <> R_RA)
           (ltac:(by []) : R_SP <> R_ARG)
           (ltac:(by []) : R_ONE <> R_ARG)
           HSP3 HONE3 HlA1 EtA HnosA Hcap1 Hmj1 Htag3)
    => [m2 [rs4 [Pp4 [Hst4 Hv4 Ht4 Hcap4 Hmj4] [HSP4 HARG4 Hoth4] Htag4]]].
  (* --- 5. pop R_RA: the caller's own capability --- *)
  set pc5 := Pointer.inc (Pointer.inc pc3).
  have Hcomp5 : Pointer.component pc5 = C
    by rewrite /pc5 !Pointer.inc_preserves_component.
  have Hc5 : TMacros.code_at_I cde C pc5 (pop R_RA ++ nxt :: rest)
    by exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hc3)).
  have Htl5 : nxt :: rest <> [::] by [].
  have Eoff2 : ((Z.of_nat (2 + size temps + 2) - 1) - 1)%Z
             = Z.of_nat (2 + size temps) by lia.
  have HlR2 : Transitional.Memory.load m2
      (C, fb, ((Z.of_nat (2 + size temps + 2) - 1) - 1)%Z) = Some vRA.
  { rewrite Eoff2.
    have Hne : ((C, fb, Z.of_nat (2 + size temps)) : Pointer.t)
             <> (C, fb, (Z.of_nat (2 + size temps + 2) - 1)%Z).
    { move=> E.
      have Eo : Z.of_nat (2 + size temps)
              = (Z.of_nat (2 + size temps + 2) - 1)%Z
        := f_equal Pointer.offset E.
      move: Eo. lia. }
    by rewrite (TMem.load_store_neq Hst4 Hne) Hraw1 //; exact: (Hnefb _ 0%Z). }
  have Htagd : TInv.tag_inv
      ((TInv.CMem (C, fb, ((Z.of_nat (2 + size temps + 2) - 1) - 1)%Z),
        tvtag vRA.1) :: L) m2 rs4 pct by rewrite Eoff2.
  case: (pop_ra_run Hc5 Htl5 Hcomp5 HSP4 (ltac:(by rewrite Hoth4) :
           Transitional.Register.get R_ONE rs4 = MVal Other (Int 1))
           HlR2 HliveR HnotReg Hpriv Hcap4 Hmj4 Htagd)
    => [m3 [rs5 [Pp5 [Hst5 Hv5 Ht5 Hcap5 Hmj5] [HSP5 HRA5 Hoth5] Htag5]]].
  exists m3, rs5, (Pointer.inc (Pointer.inc pc5)). split.
  - eapply plus_left with (t1 := E0) (t2 := E0); [exact: S1 | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: S2 | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: S3 | | by []].
    eapply star_trans with (t1 := E0) (t2 := E0);
      [exact: (plus_star Pp4) | | by []].
    exact: (plus_star Pp5).
  - split.
    + exact: Hcap5.
    + exact: Hmj5.
    + by rewrite /pc5 /pc3 !Pointer.inc_preserves_component.
    + exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hc5)).
    + exists m2, ({| Transitional.val := Transitional.val vRA.1;
                     tvtag := Invalidated |},
                  {| vtag := Invalidated; color := C; entry := None;
                     is_code := false |}).
      split.
      * by move=> q; rewrite Hv4 Hv1.
      * by move=> q; rewrite Ht4 Ht1.
      * by rewrite -Eoff2.
      * exact: Hv5.
  - split.
    + by rewrite Hoth5 // Hoth4 //.
    + by rewrite HSP5 Eoff2.
    + by rewrite Hoth5 // HARG4.
    + exact: HRA5.
    + move=> r' H1 H2 H3 H4 H5.
      by rewrite Hoth5 // Hoth4 // /rs3 TInv.get_set_neq // /rs2
                 TInv.get_set_neq // /rs1 TInv.get_set_neq //.
  - exact: Htag5.
Qed.

(** ★ The WRAPPER's entry — the mirror of [ef_restore_run], and the piece
    `diagram_call_ext` needs between the [ICall] and the body's own prologue:

        IConst 1 R_ONE ; IMov R_SP R_AUX1 ; IConst sfs R_SP ; IAlloc R_SP R_SP ;
        push R_AUX1 ; load_arg (scr C) R_AUX1 ; push R_AUX1 ; push R_RA

    Twelve steps that build the wrapper activation's frame:

      - slot 0 — the CALLER's [R_SP], which arrived in [R_AUX1] via [IMov];
      - slot 1 — the INHERITED scratch value, read out before this activation
        overwrites the cell (a re-entrant activation of [C] would otherwise
        lose the outer one's parked stack pointer);
      - slot 2 — the [Ret n] capability [ICall] put in [R_RA]. This is the only
        capability push on the entry side, and where the ledger entry moves
        from [CReg] to [CMem (C, fbE, 2)] — exactly what `SM_external` records
        and what `ef_cross_any` consumes on the way out.

    The [load_arg] in the middle is an [ILoad], so it WRITES THE CELL BACK.
    Harmless for the usual reason: the parked value is [Other]-tagged data, so
    the write-back is the identity on [vload]/[tload] — which is why
    [tvtag mscr.1 = Other] is a premise. *)
Lemma ef_entry_run C ne a mem m rs pc pct L n mscr tailc :
  TMacros.code_at_I cde C pc
    (IConst (IInt 1) R_ONE
     :: [:: IMov R_SP R_AUX1; IConst (IInt (Z.of_nat (4 + ne))) R_SP;
            IAlloc R_SP R_SP]
        ++ push R_AUX1 ++ load_arg (scr C) R_AUX1 ++ push R_AUX1
        ++ push R_RA ++ tailc) ->
  tailc <> [::] ->
  Pointer.component pc = C ->
  Transitional.Register.get_tag R_RA rs = Some (Ret n) ->
  Transitional.Memory.load m (C, 1, 0%Z) = Some mscr ->
  tvtag mscr.1 = Other ->
  (exists cm, getm m C = Some cm) ->
  ~ List.In (TInv.CMem (C, 1, 0%Z)) (TInv.sites L) ->
  (forall b0, a C b0 <> Some 1) ->
  TInject.minj a mem m ->
  TInv.tag_inv ((TInv.CReg, Ret n) :: L) m rs pct ->
  exists m' rs' fbE pcF,
    [/\ plus TS.step cde (m, rs, pc, pct) E0 (m', rs', pcF, pct),
        [/\ (forall (o : Z) w,
               Transitional.Memory.load m (C, fbE, o) = Some w -> False),
            (forall b0, a C b0 <> Some fbE),
            fbE <> 1,
            TInject.minj a mem m'
          & TStack.frame_cap m' C fbE (4 + ne)],
        [/\ TMem.vload m' (C, fbE, 0%Z)
              = Some (Transitional.val (Transitional.Register.get R_SP rs)),
            TMem.tload m' (C, fbE, 0%Z) = Some Other,
            TMem.vload m' (C, fbE, 1%Z) = Some (Transitional.val mscr.1),
            TMem.tload m' (C, fbE, 1%Z) = Some Other
          & Transitional.Memory.load m' (C, fbE, 2%Z)
              = Some (Transitional.Register.get R_RA rs,
                      {| vtag := Ret n; color := C; entry := None;
                         is_code := false |})],
        [/\ (forall q, Pointer.component q <> C \/ Pointer.block q <> fbE ->
               TMem.vload m' q = TMem.vload m q),
            (forall q, Pointer.component q <> C \/ Pointer.block q <> fbE ->
               TMem.tload m' q = TMem.tload m q),
            Pointer.component pcF = C,
            TMacros.code_at_I cde C pcF tailc
          & [/\ Transitional.Register.get R_ONE rs' = MVal Other (Int 1),
                Transitional.Register.get R_SP rs'
                  = MVal Other (Ptr (C, fbE, 3%Z))
              & forall r', r' <> R_ONE -> r' <> R_SP -> r' <> R_AUX1 ->
                  r' <> R_RA ->
                  Transitional.Register.get r' rs'
                  = Transitional.Register.get r' rs]]
      & TInv.tag_inv ((TInv.CMem (C, fbE, 2%Z), Ret n) :: L) m' rs' pct].
Proof.
  move=> Hcode Htailc Hcomp Hrt Hmscr Etm HcmF Hnoscr Hscrp HI Htag.
  (* --- 1. IConst 1 R_ONE --- *)
  have Hc0 := Hcode.
  have S1 : TS.step cde (m, rs, pc, pct) E0
            (m, Transitional.Register.set R_ONE (Int 1) Other rs,
             Pointer.inc pc, pct).
  { have -> : Int 1 = imm_to_val (IInt 1) by [].
    eapply TS.Const; [exact: (TMacros.code_at_I_head Hc0)
                     | exact: (TMacros.check_pc_at_I Hc0)]. }
  set rs1 := (Transitional.Register.set R_ONE (Int 1) Other rs) in S1 *.
  have Htag1 : TInv.tag_inv ((TInv.CReg, Ret n) :: L) m rs1 pct
    by apply: TInv.tag_inv_setreg; [by [] | exact: Htag].
  set pc1 := Pointer.inc pc.
  have Hcomp1 : Pointer.component pc1 = C
    by rewrite /pc1 Pointer.inc_preserves_component.
  have Hc1 : TMacros.code_at_I cde C pc1
      ([:: IMov R_SP R_AUX1; IConst (IInt (Z.of_nat (4 + ne))) R_SP;
           IAlloc R_SP R_SP]
       ++ IStore R_SP R_AUX1
          :: (IBinOp Add R_SP R_ONE R_SP
              :: load_arg (scr C) R_AUX1 ++ push R_AUX1 ++ push R_RA
                 ++ tailc))
    by exact: (TMacros.code_at_I_tail Hc0).
  (* --- 2-4. the wrapper's own frame --- *)
  case: (prologue_alloc_run Hc1 Hcomp1
           (TInv.ti_regs Htag1 (r := R_SP) (ltac:(by []))) HcmF HI Htag1)
    => [m1 [rs2 [fbE [Sal [Hfresh Havoid [Hnosite Hpres] Hmj1 Hcap1]
                          [HSP2 HA12 Hoth2] Htag2]]]].
  have HfbE1 : fbE <> 1 by move=> E; apply: (Hfresh 0%Z mscr); rewrite E.
  have Hd1 : Pointer.component ((C, 1, 0%Z) : Pointer.t) <> C
             \/ Pointer.block ((C, 1, 0%Z) : Pointer.t) <> fbE
    by right=> E; apply: HfbE1; rewrite -E.
  have Hmscr1 : Transitional.Memory.load m1 (C, 1, 0%Z) = Some mscr
    by rewrite (Hpres _ Hd1).
  set pc4 := Pointer.inc (Pointer.inc (Pointer.inc pc1)).
  have Hcomp4 : Pointer.component pc4 = C
    by rewrite /pc4 !Pointer.inc_preserves_component.
  have Hc4 : TMacros.code_at_I cde C pc4
      (push R_AUX1 ++ load_arg (scr C) R_AUX1 ++ push R_AUX1 ++ push R_RA
       ++ tailc).
  { apply: TMacros.code_at_I_tail. apply: TMacros.code_at_I_tail.
    apply: TMacros.code_at_I_tail. exact: Hc1. }
  (* --- 5-6. push R_AUX1: the caller's [R_SP] into slot 0 --- *)
  have HONE2 : Transitional.Register.get R_ONE rs2 = MVal Other (Int 1)
    by rewrite Hoth2 // /rs1 TInv.get_set_eq.
  have Hsp0 : (0 <= 0 < Z.of_nat (4 + ne))%Z by split; lia.
  have Htl4 : load_arg (scr C) R_AUX1 ++ push R_AUX1 ++ push R_RA ++ tailc
              <> [::] by [].
  case: (push_data_run Hc4 Htl4 Hcomp4
           (ltac:(by []) : R_AUX1 <> R_RA)
           (ltac:(by []) : R_SP <> R_AUX1)
           (ltac:(by []) : R_ONE <> R_AUX1)
           HSP2 HONE2 Hsp0 Hcap1 (Hnosite 0%Z) Havoid Hmj1 Htag2)
    => [m2 [rs3 [Sp0 [Hsl0 Hpres0 Hst0 Hcap2 Hmj2] [HSP3 HA13 Hoth3] Htag3]]].
  have Hne0 : ((C, 1, 0%Z) : Pointer.t) <> (C, fbE, 0%Z)
    by move=> E; apply: HfbE1; move: (f_equal Pointer.block E) => /= ->.
  have Hmscr2 : Transitional.Memory.load m2 (C, 1, 0%Z) = Some mscr
    by rewrite (TMem.load_store_neq Hst0 Hne0).
  (* --- 7-8. load_arg: the INHERITED scratch value into [R_AUX1] --- *)
  set pc6 := Pointer.inc (Pointer.inc pc4).
  have Hcomp6 : Pointer.component pc6 = C
    by rewrite /pc6 !Pointer.inc_preserves_component.
  have Hc6 : TMacros.code_at_I cde C pc6
      (IConst (IPtr (scr C)) R_AUX1
       :: ILoad R_AUX1 R_AUX1 :: push R_AUX1 ++ push R_RA ++ tailc).
  { apply: TMacros.code_at_I_tail. apply: TMacros.code_at_I_tail.
    exact: Hc4. }
  have Hc7 := TMacros.code_at_I_tail Hc6.
  have S7 : TS.step cde (m2, rs3, pc6, pct) E0
            (m2, Transitional.Register.set R_AUX1 (Ptr (scr C)) Other rs3,
             Pointer.inc pc6, pct).
  { have -> : Ptr (scr C) = imm_to_val (IPtr (scr C)) by [].
    eapply TS.Const; [exact: (TMacros.code_at_I_head Hc6)
                     | exact: (TMacros.check_pc_at_I Hc6)]. }
  set rs4 := (Transitional.Register.set R_AUX1 (Ptr (scr C)) Other rs3)
    in S7 *.
  case: (TMem.store_after_load
           ({| Transitional.val := Transitional.val mscr.1;
               tvtag := if is_address (tvtag mscr.1) then Invalidated
                        else Other |},
            {| vtag := if is_address (tvtag mscr.1) then Invalidated
                       else Other;
               color := C; entry := None; is_code := false |})
           Hmscr2) => [m3 Hst3].
  have S8 : TS.step cde (m2, rs4, Pointer.inc pc6, pct) E0
            (m3, Transitional.Register.set R_AUX1
                   (Transitional.val mscr.1) (tvtag mscr.1) rs4,
             Pointer.inc (Pointer.inc pc6), pct).
  { eapply TS.Load.
    - exact: (TMacros.code_at_I_head Hc7).
    - exact: (TMacros.check_pc_at_I Hc7).
    - by rewrite /rs4 TInv.get_set_eq.
    - by rewrite /rs4 TInv.get_set_eq.
    - by rewrite /= Pointer.inc_preserves_component Hcomp6.
    - exact: Hmscr2.
    - by rewrite /= Pointer.inc_preserves_component Hcomp6; exact: Hst3. }
  set rs5 := (Transitional.Register.set R_AUX1
                (Transitional.val mscr.1) (tvtag mscr.1) rs4) in S8 *.
  (* the reload is invisible: the parked value is data *)
  have Hv3 : forall q, TMem.vload m3 q = TMem.vload m2 q.
  { move=> q. apply: (TMem.vload_store_same Hmscr2 _ Hst3 q). by []. }
  have Ht3 : forall q, TMem.tload m3 q = TMem.tload m2 q.
  { move=> q. apply: (TMem.tload_store_same Hmscr2 _ Hst3 q).
    by rewrite /= Etm. }
  have Hraw3 : forall q, q <> ((C, 1, 0%Z) : Pointer.t) ->
      Transitional.Memory.load m3 q = Transitional.Memory.load m2 q
    by move=> q Hq; exact: (TMem.load_store_neq Hst3 Hq).
  have Hcap3 : TStack.frame_cap m3 C fbE (4 + ne)
    by move=> j Hj; rewrite Hv3; exact: Hcap2 Hj.
  have Hmj3 : TInject.minj a mem m3
    by apply: (TInject.minj_store_outside _ Hst3 Hmj2) => b0; exact: Hscrp b0.
  have Hnoscr1 : ~ List.In (TInv.CMem (C, 1, 0%Z))
      (TInv.sites ((TInv.CReg, Ret n) :: L))
    by move=> /= [E|Hin]; [ | exact: Hnoscr Hin].
  have Htag5 : TInv.tag_inv ((TInv.CReg, Ret n) :: L) m3 rs5 pct.
  { rewrite /rs5 /rs4 Etm. apply: TInv.tag_inv_setreg; first by [].
    apply: TInv.tag_inv_setreg; first by [].
    apply: (TInv.tag_inv_store_data Hnoscr1 _ Hst3 Htag3).
    by rewrite /= Etm. }
  (* --- 9-10. push R_AUX1: the inherited scratch into slot 1 --- *)
  set pc8 := Pointer.inc (Pointer.inc pc6).
  have Hcomp8 : Pointer.component pc8 = C
    by rewrite /pc8 /pc6 !Pointer.inc_preserves_component.
  have Hc8 : TMacros.code_at_I cde C pc8
      (push R_AUX1 ++ push R_RA ++ tailc)
    by exact: (TMacros.code_at_I_tail Hc7).
  have HSP5 : Transitional.Register.get R_SP rs5
            = MVal Other (Ptr (C, fbE, (0 + 1)%Z))
    by rewrite /rs5 TInv.get_set_neq // /rs4 TInv.get_set_neq //.
  have HONE5 : Transitional.Register.get R_ONE rs5 = MVal Other (Int 1)
    by rewrite /rs5 TInv.get_set_neq // /rs4 TInv.get_set_neq // Hoth3 //;
       exact: HONE2.
  have Hsp1 : (0 <= 0 + 1 < Z.of_nat (4 + ne))%Z by split; lia.
  have Htl8 : push R_RA ++ tailc <> [::] by [].
  case: (push_data_run Hc8 Htl8 Hcomp8
           (ltac:(by []) : R_AUX1 <> R_RA)
           (ltac:(by []) : R_SP <> R_AUX1)
           (ltac:(by []) : R_ONE <> R_AUX1)
           HSP5 HONE5 Hsp1 Hcap3 (Hnosite (0 + 1)%Z) Havoid Hmj3 Htag5)
    => [m4 [rs6 [Sp1 [Hsl1 Hpres1 Hst1 Hcap4 Hmj4] [HSP6 HA16 Hoth6] Htag6]]].
  (* --- 11-12. push R_RA: the [Ret n] capability into slot 2 --- *)
  set pc10 := Pointer.inc (Pointer.inc pc8).
  have Hcomp10 : Pointer.component pc10 = C
    by rewrite /pc10 /pc8 /pc6 !Pointer.inc_preserves_component.
  have Hc10 : TMacros.code_at_I cde C pc10 (push R_RA ++ tailc)
    by exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hc8)).
  have HONE6 : Transitional.Register.get R_ONE rs6 = MVal Other (Int 1)
    by rewrite Hoth6 //.
  have HRA6 : Transitional.Register.get R_RA rs6
            = Transitional.Register.get R_RA rs
    by rewrite Hoth6 // /rs5 TInv.get_set_neq // /rs4 TInv.get_set_neq //
               Hoth3 // Hoth2 // /rs1 TInv.get_set_neq //.
  have Hrt6 : Transitional.Register.get_tag R_RA rs6 = Some (Ret n).
  { move: (TInv.ti_dom Htag6 R_RA) => [tv6 Hg6]. move: Hrt HRA6.
    rewrite /Transitional.Register.get_tag /Transitional.Register.get Hg6 /=.
    case: (getm rs _) => [tv|] /=.
    - by move=> [E1] E2; rewrite E2 E1.
    - by move=> []. }
  have Hnos2 : ~ List.In (TInv.CMem (C, fbE, (0 + 1 + 1)%Z)) (TInv.sites L)
    by move=> Hin; exact: (Hnosite (0 + 1 + 1)%Z (or_intror Hin)).
  have Hsp2 : (0 <= 0 + 1 + 1 < Z.of_nat (4 + ne))%Z by split; lia.
  case: (push_ra_run Hc10 Htailc Hcomp10 HSP6 HONE6 Hrt6
           (ltac:(by []) : TInv.is_live (Ret n))
           Hsp2 Hcap4 Hnos2 Havoid Hmj4 Htag6)
    => [m5 [rs7 [Sp2 [Hsl2 Hpres2 Hst2 Hcap5 Hmj5] [HSP7 HRA7 Hoth7] Htag7]]].
  (* --- assembled --- *)
  have E1 : (0 + 1)%Z = 1%Z by [].
  have E2 : (0 + 1 + 1)%Z = 2%Z by [].
  have E3 : (0 + 1 + 1 + 1)%Z = 3%Z by [].
  exists m5, rs7, fbE, (Pointer.inc (Pointer.inc pc10)).
  split.
  - eapply plus_left with (t1 := E0) (t2 := E0); [exact: S1 | | by []].
    eapply star_trans with (t1 := E0) (t2 := E0); [exact: Sal | | by []].
    eapply star_trans with (t1 := E0) (t2 := E0);
      [exact: (plus_star Sp0) | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: S7 | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: S8 | | by []].
    eapply star_trans with (t1 := E0) (t2 := E0);
      [exact: (plus_star Sp1) | | by []].
    exact: (plus_star Sp2).
  - split.
    + exact: Hfresh.
    + exact: Havoid.
    + exact: HfbE1.
    + exact: Hmj5.
    + exact: Hcap5.
  - (* the three slots *)
    have Hsl0' : Transitional.Memory.load m5 (C, fbE, 0%Z)
               = Some (Transitional.Register.get R_AUX1 rs2,
                       {| vtag := Other; color := C; entry := None;
                          is_code := false |}).
    { apply: (Hpres2 _ _ _ _).
      - apply: (Hpres1 _ _ _ _); last first.
        { by move=> E; move: (f_equal Pointer.offset E) => /=; lia. }
        rewrite Hraw3; last by move=> E; apply: HfbE1;
          move: (f_equal Pointer.block E) => /= <-.
        exact: Hsl0.
      - by move=> E; move: (f_equal Pointer.offset E) => /=; lia. }
    have EA1 : Transitional.Register.get R_AUX1 rs2
             = MVal Other
                 (Transitional.val (Transitional.Register.get R_SP rs))
      by rewrite HA12 /rs1 TInv.get_set_neq //.
    have Hsl1' : Transitional.Memory.load m5 (C, fbE, 1%Z)
               = Some (Transitional.Register.get R_AUX1 rs5,
                       {| vtag := Other; color := C; entry := None;
                          is_code := false |}).
    { apply: (Hpres2 _ _ _ _).
      - by move: Hsl1; rewrite E1.
      - by move=> E; move: (f_equal Pointer.offset E) => /=; lia. }
    have EA5 : Transitional.Register.get R_AUX1 rs5
             = MVal Other (Transitional.val mscr.1)
      by rewrite /rs5 TInv.get_set_eq Etm.
    split.
    + by rewrite /TMem.vload Hsl0' EA1.
    + by rewrite /TMem.tload Hsl0' EA1.
    + by rewrite /TMem.vload Hsl1' EA5.
    + by rewrite /TMem.tload Hsl1' EA5.
    + by move: Hsl2; rewrite E2 HRA6 => ->.
  - have Hne5 : forall q, Pointer.component q <> C \/ Pointer.block q <> fbE ->
        forall o : Z, q <> ((C, fbE, o) : Pointer.t)
      by move=> q Hq o E; case: Hq => [H|H]; apply: H; rewrite E.
    split.
    + move=> q Hq.
      have E53 : TMem.vload m5 q = TMem.vload m3 q
        by rewrite /TMem.vload (TMem.load_store_neq Hst2 (Hne5 q Hq _))
                   (TMem.load_store_neq Hst1 (Hne5 q Hq _)).
      have E2m : TMem.vload m2 q = TMem.vload m q
        by rewrite /TMem.vload (TMem.load_store_neq Hst0 (Hne5 q Hq _))
                   (Hpres q Hq).
      by rewrite E53 Hv3 E2m.
    + move=> q Hq.
      have E53 : TMem.tload m5 q = TMem.tload m3 q
        by rewrite /TMem.tload (TMem.load_store_neq Hst2 (Hne5 q Hq _))
                   (TMem.load_store_neq Hst1 (Hne5 q Hq _)).
      have E2m : TMem.tload m2 q = TMem.tload m q
        by rewrite /TMem.tload (TMem.load_store_neq Hst0 (Hne5 q Hq _))
                   (Hpres q Hq).
      by rewrite E53 Ht3 E2m.
    + by rewrite /pc10 /pc8 /pc6 /pc4 /pc1 !Pointer.inc_preserves_component.
    + exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hc10)).
    + split.
      * by rewrite Hoth7 //.
      * by rewrite HSP7 E3.
      * move=> r' H1 H2 H3 H4.
        by rewrite Hoth7 // Hoth6 // /rs5 TInv.get_set_neq //
                   /rs4 TInv.get_set_neq // Hoth3 // Hoth2 //
                   /rs1 TInv.get_set_neq //.
  - by move: Htag7; rewrite E2.
Qed.

(** ★ MAIN's FLAG PROTOCOL, on the branch-TAKEN path.

        IConst (IPtr flag) R_AUX1 ; ILoad R_AUX1 R_AUX2 ; push R_AUX2 ;
        IBnz R_AUX2 lmain ; IConst 0 R_COM ; ILabel lmain ;
        IConst 1 R_AUX2 ; IStore R_AUX1 R_AUX2

    Main's dual entry serves TWO callers: the machine, on the initial run, and
    a genuine cross-component `ICall` to `(main, main)` afterwards. The flag
    cell tells them apart — `Int 0` on the initial run, `Int 1` ever after —
    and `ef_main_entry_run` covers the first. This lemma covers the second, and
    is the piece that was missing: without it `entry_ext` at `(main, main)` is
    not just unproved but FALSE, since main's wrapper is not the standard one.

    The two paths differ by exactly two steps — taken, the `IBnz` jumps over
    `IConst 0 R_COM` and lands ON the `ILabel lmain` cell, so the incoming
    `R_COM` (the caller's argument) survives instead of being overwritten by
    main's initial `Int 0`. Everything else is shared, which is why this is a
    segment lemma rather than a second copy of `ef_main_entry_run`: the prefix
    it sits on is `ef_entry_run`'s, verbatim. *)
Lemma flag_protocol_taken_run C ne fbE a mem m rs pc pct L lmain mflag tailc :
  TMacros.code_at_I cde C pc
    ([:: IConst (IPtr (flag_buf_ptr (scr C))) R_AUX1; ILoad R_AUX1 R_AUX2]
     ++ push R_AUX2
     ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
            IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2]
     ++ tailc) ->
  tailc <> [::] ->
  Pointer.component pc = C ->
  Transitional.Memory.load m (C, 1, 1%Z) = Some mflag ->
  tvtag mflag.1 = Other ->
  Transitional.val mflag.1 = Int 1 ->
  Transitional.Register.get R_SP rs = MVal Other (Ptr (C, fbE, 3%Z)) ->
  Transitional.Register.get R_ONE rs = MVal Other (Int 1) ->
  fbE <> 1 ->
  (forall b0, a C b0 <> Some fbE) ->
  (forall b0, a C b0 <> Some 1) ->
  ~ List.In (TInv.CMem ((C, fbE, 3%Z) : Pointer.t)) (TInv.sites L) ->
  (forall l0 C_code, getm cde C = Some C_code ->
     count (TLabel.is_tlabel l0) C_code <= 1) ->
  TStack.frame_cap m C fbE (4 + ne) ->
  TInject.minj a mem m ->
  TInv.tag_inv L m rs pct ->
  exists m' rs' pcF,
    [/\ plus TS.step cde (m, rs, pc, pct) E0 (m', rs', pcF, pct),
        [/\ TInject.minj a mem m',
            TStack.frame_cap m' C fbE (4 + ne),
            (forall q, q <> ((C, fbE, 3%Z) : Pointer.t) ->
               q <> ((C, 1, 1%Z) : Pointer.t) ->
               Transitional.Memory.load m' q = Transitional.Memory.load m q)
          & Transitional.Memory.load m' (C, fbE, 3%Z)
              = Some (MVal Other (Int 1),
                      {| vtag := Other; color := C; entry := None;
                         is_code := false |})],
        [/\ TMem.vload m' (C, 1, 1%Z) = Some (Int 1),
            TMem.tload m' (C, 1, 1%Z) = Some Other,
            Pointer.component pcF = C
          & TMacros.code_at_I cde C pcF tailc],
        [/\ Transitional.Register.get R_ONE rs' = MVal Other (Int 1),
            Transitional.Register.get R_SP rs'
              = MVal Other (Ptr (C, fbE, 4%Z))
          & forall r', r' <> R_SP -> r' <> R_AUX1 -> r' <> R_AUX2 ->
              Transitional.Register.get r' rs'
              = Transitional.Register.get r' rs]
      & TInv.tag_inv L m' rs' pct].
Proof.
  move=> Hcode Htailc Hcomp Hmflag Etf Evf HSP HONE HfbE1 Havoid Hscrp Hnosite3
         Huniq Hcap HI Htag.
  (* the flag cell is not a ledger site: a site's tag is LIVE, and this one is
     [Other]. Derived rather than assumed — the caller has no easy handle on
     it, whereas here [Etf] is right there. *)
  have Hnoflag : ~ List.In (TInv.CMem ((C, 1, 1%Z) : Pointer.t))
                   (TInv.sites L).
  { move=> /List.in_map_iff [[s t] [/= Es Hin]].
    rewrite Es in Hin.
    move: (TInv.ti_site Htag Hin) (TInv.ti_live Htag Hin).
    rewrite /TInv.tagat /TMem.tload Hmflag /= => -[Et] Hlive.
    by move: Hlive; rewrite -Et Etf. }
  (* the [check_pc] of the last [IStore] needs a cell after it *)
  case: tailc Hcode Htailc => [|nxt rest] Hcode Htailc;
    first by exfalso; apply: Htailc.
  have Eflag : flag_buf_ptr (scr C) = ((C, 1, 1%Z) : Pointer.t) by [].
  (* --- 1. IConst (IPtr flag) R_AUX1 --- *)
  have Hc0 := Hcode.
  have S1 : TS.step cde (m, rs, pc, pct) E0
            (m, Transitional.Register.set R_AUX1
                  (Ptr (flag_buf_ptr (scr C))) Other rs, Pointer.inc pc, pct).
  { have -> : Ptr (flag_buf_ptr (scr C))
            = imm_to_val (IPtr (flag_buf_ptr (scr C))) by [].
    eapply TS.Const; [exact: (TMacros.code_at_I_head Hc0)
                     | exact: (TMacros.check_pc_at_I Hc0)]. }
  set rs1 := (Transitional.Register.set R_AUX1
                (Ptr (flag_buf_ptr (scr C))) Other rs) in S1 *.
  have Htag1 : TInv.tag_inv L m rs1 pct
    by apply: TInv.tag_inv_setreg; [by [] | exact: Htag].
  have Hc1 := TMacros.code_at_I_tail Hc0.
  (* --- 2. ILoad R_AUX1 R_AUX2: the flag, with its write-back --- *)
  case: (TMem.store_after_load
           ({| Transitional.val := Transitional.val mflag.1;
               tvtag := if is_address (tvtag mflag.1) then Invalidated
                        else Other |},
            {| vtag := if is_address (tvtag mflag.1) then Invalidated
                       else Other;
               color := C; entry := None; is_code := false |})
           Hmflag) => [m1 Hst1].
  have S2 : TS.step cde (m, rs1, Pointer.inc pc, pct) E0
            (m1, Transitional.Register.set R_AUX2
                   (Transitional.val mflag.1) (tvtag mflag.1) rs1,
             Pointer.inc (Pointer.inc pc), pct).
  { eapply TS.Load.
    - exact: (TMacros.code_at_I_head Hc1).
    - exact: (TMacros.check_pc_at_I Hc1).
    - by rewrite /rs1 TInv.get_set_eq.
    - by rewrite /rs1 TInv.get_set_eq.
    - by rewrite Eflag /= Pointer.inc_preserves_component Hcomp.
    - by rewrite Eflag; exact: Hmflag.
    - by rewrite Eflag /= Pointer.inc_preserves_component Hcomp; exact: Hst1. }
  set rs2 := (Transitional.Register.set R_AUX2
                (Transitional.val mflag.1) (tvtag mflag.1) rs1) in S2 *.
  have Hv1 : forall q, TMem.vload m1 q = TMem.vload m q
    by move=> q; apply: (TMem.vload_store_same Hmflag _ Hst1 q).
  have Ht1 : forall q, TMem.tload m1 q = TMem.tload m q
    by move=> q; apply: (TMem.tload_store_same Hmflag _ Hst1 q);
       rewrite /= Etf.
  have Hraw1 : forall q, q <> ((C, 1, 1%Z) : Pointer.t) ->
      Transitional.Memory.load m1 q = Transitional.Memory.load m q
    by move=> q Hq; exact: (TMem.load_store_neq Hst1 Hq).
  have Hcap1 : TStack.frame_cap m1 C fbE (4 + ne)
    by move=> j Hj; rewrite Hv1; exact: Hcap Hj.
  have Hmj1 : TInject.minj a mem m1
    by apply: (TInject.minj_store_outside _ Hst1 HI) => b0; exact: Hscrp b0.
  have Htag2 : TInv.tag_inv L m1 rs2 pct.
  { rewrite /rs2 Etf. apply: TInv.tag_inv_setreg; first by [].
    apply: (TInv.tag_inv_store_data Hnoflag _ Hst1 Htag1).
    by rewrite /= Etf. }
  (* --- 3-4. push R_AUX2: the CONTEXT MARKER into slot 3 --- *)
  set pc2 := Pointer.inc (Pointer.inc pc).
  have Hcomp2 : Pointer.component pc2 = C
    by rewrite /pc2 !Pointer.inc_preserves_component.
  have Hc2 : TMacros.code_at_I cde C pc2
      (push R_AUX2
       ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
              IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2]
       ++ (nxt :: rest)) by exact: (TMacros.code_at_I_tail Hc1).
  have HSP2 : Transitional.Register.get R_SP rs2
            = MVal Other (Ptr (C, fbE, 3%Z))
    by rewrite /rs2 TInv.get_set_neq // /rs1 TInv.get_set_neq //.
  have HONE2 : Transitional.Register.get R_ONE rs2 = MVal Other (Int 1)
    by rewrite /rs2 TInv.get_set_neq // /rs1 TInv.get_set_neq //.
  have EA22 : Transitional.Register.get R_AUX2 rs2 = MVal Other (Int 1)
    by rewrite /rs2 TInv.get_set_eq Etf Evf.
  have Hsp3 : (0 <= 3 < Z.of_nat (4 + ne))%Z by split; lia.
  case: (push_data_run Hc2 (ltac:(by []) :
           [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
               IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2] ++ (nxt :: rest) <> [::])
           Hcomp2 (ltac:(by []) : R_AUX2 <> R_RA)
           (ltac:(by []) : R_SP <> R_AUX2)
           (ltac:(by []) : R_ONE <> R_AUX2)
           HSP2 HONE2 Hsp3 Hcap1 Hnosite3 Havoid Hmj1 Htag2)
    => [m2 [rs3 [Sp [Hsl3 Hpres3 Hst3 Hcap2 Hmj2] [HSP3 HA23 Hoth3] Htag3]]].
  have Hne3 : ((C, 1, 1%Z) : Pointer.t) <> (C, fbE, 3%Z)
    by move=> E; apply: HfbE1; move: (f_equal Pointer.block E) => /= ->.
  have Hmflag2 : Transitional.Memory.load m2 (C, 1, 1%Z)
               = Some (MVal Other (Int 1),
                       {| vtag := Other; color := C; entry := None;
                          is_code := false |}).
  { rewrite (TMem.load_store_neq Hst3 Hne3) (TMem.load_store_eq Hst1).
    by rewrite /= Etf /= Evf. }
  (* --- 5. the IBnz: TAKEN --- *)
  set pc4 := Pointer.inc (Pointer.inc pc2).
  have Hcomp4 : Pointer.component pc4 = C
    by rewrite /pc4 /pc2 !Pointer.inc_preserves_component.
  have Hc4 : TMacros.code_at_I cde C pc4
      ([:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM]
       ++ ILabel lmain
          :: ([:: IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2] ++ (nxt :: rest)))
    by exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hc2)).
  case: (TMacros.code_at_I_label_find Hc4 Hcomp4 Huniq)
    => [pcL [HfindL EcL HcL]].
  have EA23' : Transitional.Register.get R_AUX2 rs3 = MVal Other (Int 1)
    by rewrite HA23 EA22.
  have S5 : TS.step cde (m2, rs3, pc4, pct) E0 (m2, rs3, pcL, pct).
  { eapply TS.BnzNZ.
    - exact: (TMacros.code_at_I_head Hc4).
    - exact: (TMacros.check_pc_at_I Hc4).
    - by rewrite EA23'.
    - by rewrite EA23'.
    - by [].
    - by rewrite Hcomp4; exact: HfindL.
    - apply: PcJump; first exact: (TMacros.code_at_I_head HcL).
      by rewrite EcL Hcomp4. }
  (* --- 6. the ILabel it landed on --- *)
  have Hc6 := TMacros.code_at_I_tail HcL.
  have S6 : TS.step cde (m2, rs3, pcL, pct) E0
            (m2, rs3, Pointer.inc pcL, pct)
    by eapply TS.Label; [exact: (TMacros.code_at_I_head HcL)
                        | exact: (TMacros.check_pc_at_I HcL)].
  (* --- 7. IConst 1 R_AUX2 --- *)
  have S7 : TS.step cde (m2, rs3, Pointer.inc pcL, pct) E0
            (m2, Transitional.Register.set R_AUX2 (Int 1) Other rs3,
             Pointer.inc (Pointer.inc pcL), pct).
  { have -> : Int 1 = imm_to_val (IInt 1) by [].
    eapply TS.Const; [exact: (TMacros.code_at_I_head Hc6)
                     | exact: (TMacros.check_pc_at_I Hc6)]. }
  set rs4 := (Transitional.Register.set R_AUX2 (Int 1) Other rs3) in S7 *.
  have Htag4 : TInv.tag_inv L m2 rs4 pct
    by apply: TInv.tag_inv_setreg; [by [] | exact: Htag3].
  have Hc7 := TMacros.code_at_I_tail Hc6.
  (* --- 8. IStore R_AUX1 R_AUX2: the flag stays Int 1 --- *)
  have EA14 : Transitional.Register.get R_AUX1 rs4
            = MVal Other (Ptr (C, 1, 1%Z)).
  { rewrite /rs4 TInv.get_set_neq // Hoth3 // /rs2 TInv.get_set_neq //
            /rs1 TInv.get_set_eq. by rewrite Eflag. }
  have EA24 : Transitional.Register.get R_AUX2 rs4 = MVal Other (Int 1)
    by rewrite /rs4 TInv.get_set_eq.
  case: (TMem.store_after_load
           (Transitional.Register.get R_AUX2 rs4,
            {| vtag := Other; color := C; entry := None; is_code := false |})
           Hmflag2) => [m3 Hst4].
  have S8 : TS.step cde (m2, rs4, Pointer.inc (Pointer.inc pcL), pct) E0
            (m3, Transitional.Register.set R_AUX2
                   (Transitional.val (Transitional.Register.get R_AUX2 rs4))
                   Other rs4,
             Pointer.inc (Pointer.inc (Pointer.inc pcL)), pct).
  { have -> : Other = (if is_address Other then Invalidated else Other) by [].
    eapply TS.Store.
    - exact: (TMacros.code_at_I_head Hc7).
    - exact: (TMacros.check_pc_at_I Hc7).
    - by rewrite EA14.
    - by rewrite EA14.
    - have -> : Pointer.component ((C, 1, 1%Z) : Pointer.t) = C by [].
      by rewrite !Pointer.inc_preserves_component EcL.
    - apply: (TInv.ti_tag_other Htag4). by [].
    - rewrite !Pointer.inc_preserves_component EcL. exact: Hst4. }
  set rs5 := (Transitional.Register.set R_AUX2
                (Transitional.val (Transitional.Register.get R_AUX2 rs4))
                Other rs4) in S8 *.
  have Htag5 : TInv.tag_inv L m3 rs5 pct.
  { rewrite /rs5. apply: TInv.tag_inv_setreg; first by [].
    apply: (TInv.tag_inv_store_data Hnoflag _ Hst4 Htag4).
    by rewrite /= EA24. }
  (* --- the memory facts at [m3] --- *)
  have Hmj3 : TInject.minj a mem m3
    by apply: (TInject.minj_store_outside _ Hst4 Hmj2) => b0; exact: Hscrp b0.
  have Hv3 : forall q, TMem.vload m3 q = TMem.vload m2 q.
  { move=> q. apply: (TMem.vload_store_same Hmflag2 _ Hst4 q).
    by rewrite /= EA24. }
  have Ht3 : forall q, TMem.tload m3 q = TMem.tload m2 q.
  { move=> q. apply: (TMem.tload_store_same Hmflag2 _ Hst4 q).
    by rewrite /= EA24. }
  have Hcap3 : TStack.frame_cap m3 C fbE (4 + ne)
    by move=> j Hj; rewrite Hv3; exact: Hcap2 Hj.
  exists m3, rs5, (Pointer.inc (Pointer.inc (Pointer.inc pcL))).
  split.
  - eapply plus_left with (t1 := E0) (t2 := E0); [exact: S1 | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: S2 | | by []].
    eapply star_trans with (t1 := E0) (t2 := E0);
      [exact: (plus_star Sp) | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: S5 | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: S6 | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: S7 | | by []].
    exact: star_one S8.
  - split.
    + exact: Hmj3.
    + exact: Hcap3.
    + move=> q H3 H1.
      rewrite (TMem.load_store_neq Hst4 H1) (TMem.load_store_neq Hst3 H3).
      by rewrite (TMem.load_store_neq Hst1 H1).
    + rewrite (TMem.load_store_neq Hst4 (nesym Hne3)) Hsl3.
      by rewrite EA22.
  - split.
    + by rewrite /TMem.vload (TMem.load_store_eq Hst4) /= EA24.
    + by rewrite /TMem.tload (TMem.load_store_eq Hst4) /= EA24.
    + by rewrite !Pointer.inc_preserves_component EcL.
    + exact: (TMacros.code_at_I_tail Hc7).
  - split.
    + by rewrite /rs5 TInv.get_set_neq // /rs4 TInv.get_set_neq // Hoth3.
    + by rewrite /rs5 TInv.get_set_neq // /rs4 TInv.get_set_neq // HSP3.
    + move=> r' H1 H2 H3.
      rewrite /rs5 TInv.get_set_neq // /rs4 TInv.get_set_neq //
              Hoth3 // /rs2 TInv.get_set_neq // /rs1 TInv.get_set_neq //.
  - exact: Htag5.
Qed.

(** ★ MAIN's ENTRY, entered by a GENUINE cross-component `ICall`.

    `ef_entry_run` already covers the shared prefix — everything up to and
    including `push R_RA` — because it is parameterised by the code that
    follows. So this is that lemma composed with [flag_protocol_taken_run],
    and the result has exactly the shape [TSM.EF_main] consumes: four slots
    (caller's `R_SP`, inherited scratch, the spilled `Ret n`, and the context
    marker `Int 1`), `R_SP` pointing one past them.

    Without it, `TSim.entry_ext` at `(main, main)` is FALSE, not merely
    unproved: main's wrapper is not the standard one, and a program in which
    some component imports `(main, main)` is perfectly well formed. *)
Lemma ef_main_cross_entry_run C ne lmain a mem m rs pc pct L n mscr tailc :
  TMacros.code_at_I cde C pc
    (IConst (IInt 1) R_ONE
     :: [:: IMov R_SP R_AUX1; IConst (IInt (Z.of_nat (4 + ne))) R_SP;
            IAlloc R_SP R_SP]
        ++ push R_AUX1 ++ load_arg (scr C) R_AUX1 ++ push R_AUX1
        ++ push R_RA
        ++ [:: IConst (IPtr (flag_buf_ptr (scr C))) R_AUX1;
               ILoad R_AUX1 R_AUX2]
        ++ push R_AUX2
        ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
               IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2]
        ++ tailc) ->
  tailc <> [::] ->
  Pointer.component pc = C ->
  Transitional.Register.get_tag R_RA rs = Some (Ret n) ->
  Transitional.Memory.load m (C, 1, 0%Z) = Some mscr ->
  tvtag mscr.1 = Other ->
  TMem.vload m (C, 1, 1%Z) = Some (Int 1) ->
  TMem.tload m (C, 1, 1%Z) = Some Other ->
  (exists cm, getm m C = Some cm) ->
  ~ List.In (TInv.CMem ((C, 1, 0%Z) : Pointer.t)) (TInv.sites L) ->
  (forall b0, a C b0 <> Some 1) ->
  (forall l0 C_code, getm cde C = Some C_code ->
     count (TLabel.is_tlabel l0) C_code <= 1) ->
  TInject.minj a mem m ->
  TInv.tag_inv ((TInv.CReg, Ret n) :: L) m rs pct ->
  exists m' rs' fbE pcF,
    [/\ plus TS.step cde (m, rs, pc, pct) E0 (m', rs', pcF, pct),
        [/\ (forall (o : Z) w,
               Transitional.Memory.load m (C, fbE, o) = Some w -> False),
            (forall b0, a C b0 <> Some fbE),
            fbE <> 1,
            TInject.minj a mem m'
          & TStack.frame_cap m' C fbE (4 + ne)],
        [/\ TMem.vload m' (C, fbE, 0%Z)
              = Some (Transitional.val (Transitional.Register.get R_SP rs)),
            TMem.tload m' (C, fbE, 0%Z) = Some Other,
            TMem.vload m' (C, fbE, 1%Z) = Some (Transitional.val mscr.1),
            TMem.tload m' (C, fbE, 1%Z) = Some Other
          & [/\ Transitional.Memory.load m' (C, fbE, 2%Z)
                  = Some (Transitional.Register.get R_RA rs,
                          {| vtag := Ret n; color := C; entry := None;
                             is_code := false |}),
                TMem.vload m' (C, fbE, 3%Z) = Some (Int 1)
              & TMem.tload m' (C, fbE, 3%Z) = Some Other]],
        (* ★ NO flag exception: the protocol rewrites `(C,1,1)` with the SAME
           value and the SAME tag it already held, so the two projections the
           invariants are phrased over do not move. That is what lets this
           lemma and [ef_entry_run] share one interface. *)
        [/\ (forall q, (Pointer.component q <> C \/ Pointer.block q <> fbE) ->
               TMem.vload m' q = TMem.vload m q),
            (forall q, (Pointer.component q <> C \/ Pointer.block q <> fbE) ->
               TMem.tload m' q = TMem.tload m q),
            TMem.vload m' (C, 1, 1%Z) = Some (Int 1)
              /\ TMem.tload m' (C, 1, 1%Z) = Some Other,
            Pointer.component pcF = C
          & [/\ TMacros.code_at_I cde C pcF tailc,
                Transitional.Register.get R_ONE rs' = MVal Other (Int 1),
                Transitional.Register.get R_SP rs'
                  = MVal Other (Ptr (C, fbE, 4%Z))
              & forall r', r' <> R_ONE -> r' <> R_SP -> r' <> R_AUX1 ->
                  r' <> R_AUX2 -> r' <> R_RA ->
                  Transitional.Register.get r' rs'
                  = Transitional.Register.get r' rs]]
      & TInv.tag_inv ((TInv.CMem ((C, fbE, 2%Z) : Pointer.t), Ret n) :: L)
                     m' rs' pct].
Proof.
  move=> Hcode Htailc Hcomp Hrt Hmscr Etm Hvflag Htflag HcmF Hnoscr
         Hscrp Huniq HI Htag.
  (* --- the shared prefix, verbatim [ef_entry_run] --- *)
  case: (ef_entry_run Hcode (ltac:(by []) :
           [:: IConst (IPtr (flag_buf_ptr (scr C))) R_AUX1;
               ILoad R_AUX1 R_AUX2]
           ++ push R_AUX2
           ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
                  IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2]
           ++ tailc <> [::])
           Hcomp Hrt Hmscr Etm HcmF Hnoscr Hscrp HI Htag)
    => [m1 [rs1 [fbE [pc1
       [P1 [Hfresh Havoid HfbE1 Hmj1 Hcap1]
           [Hw0 Ht0 Hw1 Ht1 Hsl2]
           [Hpv Hpt Ecp1 Hc1 [HONE1 HSP1 Hoth1]] Htag1]]]]].
  set L' := ((TInv.CMem ((C, fbE, 2%Z) : Pointer.t), Ret n) :: L).
  (* --- block 1 is not the fresh frame, so the flag survived the prefix --- *)
  have Hb1E : forall (C' : Component.id) (o : Z),
      Pointer.component ((C', 1, o) : Pointer.t) <> C
      \/ Pointer.block ((C', 1, o) : Pointer.t) <> fbE
    by move=> C' o; right => /= E; apply: HfbE1; rewrite -E.
  have Hvflag1 : TMem.vload m1 (C, 1, 1%Z) = Some (Int 1)
    by rewrite (Hpv _ (Hb1E C 1%Z)).
  have Htflag1 : TMem.tload m1 (C, 1, 1%Z) = Some Other
    by rewrite (Hpt _ (Hb1E C 1%Z)).
  have [mflag Hmflag] : exists w,
      Transitional.Memory.load m1 (C, 1, 1%Z) = Some w
    by case: (TMem.vload_load Hvflag1) => [w Hw]; exists w.
  have Etf : tvtag mflag.1 = Other
    by move: Htflag1; rewrite /TMem.tload Hmflag => -[].
  have Evf : Transitional.val mflag.1 = Int 1
    by move: Hvflag1; rewrite /TMem.vload Hmflag => -[].
  (* --- the fresh frame carries no ledger site, because nothing loads --- *)
  have Hnos : forall o : Z,
      ~ List.In (TInv.CMem ((C, fbE, o) : Pointer.t)) (TInv.sites L).
  { move=> o /List.in_map_iff [[s t] [/= Es Hin]].
    rewrite Es in Hin.
    have Hin' : List.In (TInv.CMem ((C, fbE, o) : Pointer.t), t)
                  ((TInv.CReg, Ret n) :: L) by right.
    move: (TInv.ti_site Htag Hin'). rewrite /TInv.tagat /TMem.tload.
    case E: (Transitional.Memory.load m (C, fbE, o)) => [w|] //= _.
    exact: (Hfresh o w E). }
  have Hnosite3 : ~ List.In (TInv.CMem ((C, fbE, 3%Z) : Pointer.t))
                    (TInv.sites L').
  { move=> [E|Hin]; last exact: (Hnos 3%Z Hin). by case: E. }
  (* --- the flag protocol, branch taken --- *)
  case: (flag_protocol_taken_run (ne := ne) Hc1 Htailc Ecp1 Hmflag Etf Evf
           HSP1 HONE1 HfbE1 Havoid Hscrp Hnosite3 Huniq Hcap1 Hmj1
           Htag1)
    => [m2 [rs2 [pcF [P2 [Hmj2 Hcap2 Hpres2 Hsl3]
                         [Hvf2 Htf2 Ecp2 Hc2] [HONE2 HSP2 Hoth2] Htag2]]]].
  have Hne31 : ((C, fbE, 3%Z) : Pointer.t) <> (C, 1, 1%Z)
    by move=> E; apply: HfbE1; move: (f_equal Pointer.block E) => /= ->.
  have Hne21 : ((C, fbE, 2%Z) : Pointer.t) <> (C, 1, 1%Z)
    by move=> E; apply: HfbE1; move: (f_equal Pointer.block E) => /= ->.
  have Hne23 : ((C, fbE, 2%Z) : Pointer.t) <> (C, fbE, 3%Z)
    by move=> E; move: (f_equal Pointer.offset E) => /=; lia.
  have Hout : forall q, (Pointer.component q <> C \/ Pointer.block q <> fbE) ->
      q <> ((C, 1, 1%Z) : Pointer.t) ->
      Transitional.Memory.load m2 q = Transitional.Memory.load m1 q.
  { move=> q HD H1. apply: (Hpres2 q _ H1).
    by move=> E; case: HD => [H|H]; apply: H; rewrite E. }
  exists m2, rs2, fbE, pcF.
  split.
  - eapply plus_trans with (t1 := E0) (t2 := E0);
      [exact: P1 | exact: P2 | by []].
  - by split.
  - split.
    + rewrite -Hw0 /TMem.vload.
      by rewrite (Hpres2 _ (ltac:(by move=> E;
           move: (f_equal Pointer.offset E) => /=; lia)
           : ((C, fbE, 0%Z) : Pointer.t) <> (C, fbE, 3%Z))
           (ltac:(by move=> E; apply: HfbE1;
              move: (f_equal Pointer.block E) => /= ->)
           : ((C, fbE, 0%Z) : Pointer.t) <> (C, 1, 1%Z))).
    + rewrite -Ht0 /TMem.tload.
      by rewrite (Hpres2 _ (ltac:(by move=> E;
           move: (f_equal Pointer.offset E) => /=; lia)
           : ((C, fbE, 0%Z) : Pointer.t) <> (C, fbE, 3%Z))
           (ltac:(by move=> E; apply: HfbE1;
              move: (f_equal Pointer.block E) => /= ->)
           : ((C, fbE, 0%Z) : Pointer.t) <> (C, 1, 1%Z))).
    + rewrite -Hw1 /TMem.vload.
      by rewrite (Hpres2 _ (ltac:(by move=> E;
           move: (f_equal Pointer.offset E) => /=; lia)
           : ((C, fbE, 1%Z) : Pointer.t) <> (C, fbE, 3%Z))
           (ltac:(by move=> E; apply: HfbE1;
              move: (f_equal Pointer.block E) => /= ->)
           : ((C, fbE, 1%Z) : Pointer.t) <> (C, 1, 1%Z))).
    + rewrite -Ht1 /TMem.tload.
      by rewrite (Hpres2 _ (ltac:(by move=> E;
           move: (f_equal Pointer.offset E) => /=; lia)
           : ((C, fbE, 1%Z) : Pointer.t) <> (C, fbE, 3%Z))
           (ltac:(by move=> E; apply: HfbE1;
              move: (f_equal Pointer.block E) => /= ->)
           : ((C, fbE, 1%Z) : Pointer.t) <> (C, 1, 1%Z))).
    + split.
      * by rewrite (Hpres2 _ Hne23 Hne21).
      * by rewrite /TMem.vload Hsl3.
      * by rewrite /TMem.tload Hsl3.
  - split.
    + move=> q HD. case: (@eqP _ q ((C, 1, 1%Z) : Pointer.t)) => [->|H1].
      * by rewrite Hvf2.
      * rewrite /TMem.vload (Hout q HD H1). exact: (Hpv q HD).
    + move=> q HD. case: (@eqP _ q ((C, 1, 1%Z) : Pointer.t)) => [->|H1].
      * by rewrite Htf2.
      * rewrite /TMem.tload (Hout q HD H1). exact: (Hpt q HD).
    + by split.
    + exact: Ecp2.
    + split.
      * exact: Hc2.
      * exact: HONE2.
      * exact: HSP2.
      * move=> r' H1 H2 H3 H4 H5. by rewrite Hoth2 // Hoth1 //.
  - exact: Htag2.
Qed.

(** ★ THE CALLEE ENTRY, whichever wrapper `compile_proc` gave it.

    One interface over [ef_entry_run] and [ef_main_cross_entry_run], so that
    `diagram_call_ext` never has to know which of the two it is running. The
    two differ in exactly three observable ways, and all three are absorbed
    here:

    - the frame is three slots deep or four, so `R_SP` lands at `spE` rather
      than at a literal `3`;
    - main's wrapper additionally clobbers `R_AUX2`, so the "other registers
      survive" clause excludes it (which the standard run also satisfies);
    - the suspended activation is an [EF_std] or an [EF_main]. Rather than
      export the two epilogue shapes, the lemma exports the CONSTRUCTION: give
      it a memory that still shows the wrapper's frame and it hands back the
      [ext_frame_match] the caller's `stack_match` needs.

    Preservation is stated identically for both — see the note on
    [ef_main_cross_entry_run] for why the flag rewrite is invisible. *)
Lemma ef_call_entry_run C ne plf a mem m rs pc pct L n mscr :
  ((exists tl,
      TMacros.code_at_I cde C pc
        (IConst (IInt 1) R_ONE
         :: [:: IMov R_SP R_AUX1; IConst (IInt (Z.of_nat (4 + ne))) R_SP;
                IAlloc R_SP R_SP]
            ++ push R_AUX1 ++ load_arg (scr C) R_AUX1 ++ push R_AUX1
            ++ push R_RA
            ++ IJal plf :: tl)
      /\ tl = pop R_RA ++ pop R_AUX1 ++ store_arg (scr C) R_AUX1 R_AUX2
              ++ pop R_SP ++ [:: IReturn])
   \/ (exists lmain lret,
         [/\ TMacros.code_at_I cde C pc
               (IConst (IInt 1) R_ONE
                :: [:: IMov R_SP R_AUX1;
                       IConst (IInt (Z.of_nat (4 + ne))) R_SP;
                       IAlloc R_SP R_SP]
                   ++ push R_AUX1 ++ load_arg (scr C) R_AUX1 ++ push R_AUX1
                   ++ push R_RA
                   ++ [:: IConst (IPtr (flag_buf_ptr (scr C))) R_AUX1;
                          ILoad R_AUX1 R_AUX2]
                   ++ push R_AUX2
                   ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM;
                          ILabel lmain; IConst (IInt 1) R_AUX2;
                          IStore R_AUX1 R_AUX2]
                   ++ IJal plf
                      :: pop R_ARG ++ pop R_RA ++ pop R_AUX1
                         ++ store_arg (scr C) R_AUX1 R_AUX2 ++ pop R_SP
                         ++ [:: IBnz R_ARG lret; IHalt; ILabel lret;
                                IReturn]),
             TMem.vload m (C, 1, 1%Z) = Some (Int 1)
           & TMem.tload m (C, 1, 1%Z) = Some Other])) ->
  Pointer.component pc = C ->
  Transitional.Register.get_tag R_RA rs = Some (Ret n) ->
  Transitional.Memory.load m (C, 1, 0%Z) = Some mscr ->
  tvtag mscr.1 = Other ->
  (exists cm, getm m C = Some cm) ->
  ~ List.In (TInv.CMem ((C, 1, 0%Z) : Pointer.t)) (TInv.sites L) ->
  (forall b0, a C b0 <> Some 1) ->
  (forall l0 C_code, getm cde C = Some C_code ->
     count (TLabel.is_tlabel l0) C_code <= 1) ->
  TInject.minj a mem m ->
  TInv.tag_inv ((TInv.CReg, Ret n) :: L) m rs pct ->
  exists m' rs' fbE pcF spE,
    [/\ plus TS.step cde (m, rs, pc, pct) E0 (m', rs', pcF, pct),
        [/\ (forall (o : Z) w,
               Transitional.Memory.load m (C, fbE, o) = Some w -> False),
            (forall b0, a C b0 <> Some fbE),
            fbE <> 1,
            TInject.minj a mem m'
          & TStack.frame_cap m' C fbE (4 + ne)],
        [/\ TMem.vload m' (C, fbE, 0%Z)
              = Some (Transitional.val (Transitional.Register.get R_SP rs)),
            TMem.tload m' (C, fbE, 0%Z) = Some Other,
            TMem.vload m' (C, fbE, 1%Z) = Some (Transitional.val mscr.1),
            TMem.tload m' (C, fbE, 1%Z) = Some Other
          & Transitional.Memory.load m' (C, fbE, 2%Z)
              = Some (Transitional.Register.get R_RA rs,
                      {| vtag := Ret n; color := C; entry := None;
                         is_code := false |})],
        [/\ (forall q, Pointer.component q <> C \/ Pointer.block q <> fbE ->
               TMem.vload m' q = TMem.vload m q),
            (forall q, Pointer.component q <> C \/ Pointer.block q <> fbE ->
               TMem.tload m' q = TMem.tload m q),
            Pointer.component pcF = C,
            (exists tl, TMacros.code_at_I cde C pcF (IJal plf :: tl))
          & [/\ Transitional.Register.get R_ONE rs' = MVal Other (Int 1),
                Transitional.Register.get R_SP rs'
                  = MVal Other (Ptr (C, fbE, spE)),
                (forall r', r' <> R_ONE -> r' <> R_SP -> r' <> R_AUX1 ->
                   r' <> R_AUX2 -> r' <> R_RA ->
                   Transitional.Register.get r' rs'
                   = Transitional.Register.get r' rs)
              & forall m'' s,
                  TStack.ra_addr s = ((C, fbE, 2%Z) : Pointer.t) ->
                  TStack.slots_ok m'' [:: s] ->
                  (forall (o : Z) (x : value),
                     TMem.vload m' (C, fbE, o) = Some x ->
                     TMem.vload m'' (C, fbE, o) = Some x) ->
                  (forall (o : Z) (t : value_tag),
                     TMem.tload m' (C, fbE, o) = Some t ->
                     TMem.tload m'' (C, fbE, o) = Some t) ->
                  TSM.ext_frame_match cde m'' C fbE (Pointer.inc pcF) spE s]]
      & TInv.tag_inv ((TInv.CMem ((C, fbE, 2%Z) : Pointer.t), Ret n) :: L)
                     m' rs' pct].
Proof.
  move=> Hshape Hcomp Hrt Hmscr Etm HcmF Hnoscr Hscrp Huniq HI Htag.
  case: Hshape => [[tl [Hcode Etl]]|[lmain [lret [Hcode Hvf Htf]]]].
  - (* ---- the STANDARD wrapper ---- *)
    subst tl.
    case: (ef_entry_run Hcode (ltac:(by []) :
             IJal plf :: pop R_RA ++ pop R_AUX1
               ++ store_arg (scr C) R_AUX1 R_AUX2 ++ pop R_SP
               ++ [:: IReturn] <> [::])
             Hcomp Hrt Hmscr Etm HcmF Hnoscr Hscrp HI Htag)
      => [m' [rs' [fbE [pcF
         [P1 [Hfresh Havoid HfbE1 Hmj Hcap] [Hw0 Ht0 Hw1 Ht1 Hw2]
             [Hpv Hpt Ecp HcF [HONE HSP Hoth]] Htag']]]]].
    exists m', rs', fbE, pcF, 3%Z. split.
    + exact: P1.
    + by split.
    + by split.
    + split.
      * exact: Hpv.
      * exact: Hpt.
      * exact: Ecp.
      * by exists (pop R_RA ++ pop R_AUX1 ++ store_arg (scr C) R_AUX1 R_AUX2
                     ++ pop R_SP ++ [:: IReturn]).
      * split.
        -- exact: HONE.
        -- exact: HSP.
        -- by move=> r' H1 H2 H3 _ H5; exact: Hoth.
        -- move=> m'' s Ea Hs Vtr Ttr.
           apply: (@TSM.EF_std cde m'' C fbE (Pointer.inc pcF)
                     (Transitional.val (Transitional.Register.get R_SP rs))
                     (Transitional.val mscr.1) s).
           ++ by rewrite Pointer.inc_preserves_component.
           ++ exact: (TMacros.code_at_I_tail HcF).
           ++ exact: (Vtr 0%Z _ Hw0).
           ++ exact: (Vtr 1%Z _ Hw1).
           ++ exact: (Ttr 0%Z _ Ht0).
           ++ exact: (Ttr 1%Z _ Ht1).
           ++ exact: Ea.
           ++ exact: Hs.
    + exact: Htag'.
  - (* ---- MAIN's dual entry, on a genuine cross-component call ---- *)
    case: (ef_main_cross_entry_run Hcode (ltac:(by []) :
             IJal plf :: pop R_ARG ++ pop R_RA ++ pop R_AUX1
               ++ store_arg (scr C) R_AUX1 R_AUX2 ++ pop R_SP
               ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn] <> [::])
             Hcomp Hrt Hmscr Etm Hvf Htf HcmF Hnoscr Hscrp Huniq HI Htag)
      => [m' [rs' [fbE [pcF
         [P1 [Hfresh Havoid HfbE1 Hmj Hcap] [Hw0 Ht0 Hw1 Ht1 [Hw2 Hw3 Ht3]]
             [Hpv Hpt _ Ecp [HcF HONE HSP Hoth]] Htag']]]]].
    exists m', rs', fbE, pcF, 4%Z. split.
    + exact: P1.
    + by split.
    + by split.
    + split.
      * exact: Hpv.
      * exact: Hpt.
      * exact: Ecp.
      * by exists (pop R_ARG ++ pop R_RA ++ pop R_AUX1
                     ++ store_arg (scr C) R_AUX1 R_AUX2 ++ pop R_SP
                     ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn]).
      * split.
        -- exact: HONE.
        -- exact: HSP.
        -- exact: Hoth.
        -- move=> m'' s Ea Hs Vtr Ttr.
           apply: (@TSM.EF_main cde m'' C fbE (Pointer.inc pcF) lret
                     (Transitional.val (Transitional.Register.get R_SP rs))
                     (Transitional.val mscr.1) s 1%Z).
           ++ by rewrite Pointer.inc_preserves_component.
           ++ exact: (TMacros.code_at_I_tail HcF).
           ++ exact: (Vtr 0%Z _ Hw0).
           ++ exact: (Vtr 1%Z _ Hw1).
           ++ exact: (Ttr 0%Z _ Ht0).
           ++ exact: (Ttr 1%Z _ Ht1).
           ++ exact: Ea.
           ++ exact: Hs.
           ++ exact: (Vtr 3%Z _ Hw3).
           ++ exact: (Ttr 3%Z _ Ht3).
           ++ by [].
    + exact: Htag'.
Qed.

(** ★ MAIN's ENTRY — the wrapper the MACHINE lands on, and the longest run in
    the campaign:

        IConst 1 R_ONE ; IMov R_SP R_AUX1 ; IConst sfs R_SP ; IAlloc R_SP R_SP ;
        push R_AUX1 ; load_arg (scr C) R_AUX1 ; push R_AUX1 ; push R_RA ;
        IConst (IPtr (flag)) R_AUX1 ; ILoad R_AUX1 R_AUX2 ; push R_AUX2 ;
        IBnz R_AUX2 lmain ; IConst 0 R_COM ; ILabel lmain ;
        IConst 1 R_AUX2 ; IStore R_AUX1 R_AUX2 ; IJal plf

    Two things make it different from [ef_entry_run], and both come from there
    being no caller:

    - [R_RA] holds [Register.init]'s junk, so slot 2 takes a non-capability
      ([push_junk_ra_run]) and the ledger is untouched — main's activation
      creates no [Ret];
    - the CONTEXT MARKER in slot 3 is the FLAG cell's old value. On the initial
      run that is [Int 0], so the [IBnz] is not taken, `IConst 0 R_COM` installs
      main's argument, and the flag is then set to [Int 1] so that a later
      genuine call to [main] takes the other branch.

    The marker is what [ef_halt_run] reads back on the way out. *)
Lemma ef_main_entry_run C ne lmain plf a mem m rs pc pct L mscr mflag tailc :
  TMacros.code_at_I cde C pc
    (IConst (IInt 1) R_ONE
     :: [:: IMov R_SP R_AUX1; IConst (IInt (Z.of_nat (4 + ne))) R_SP;
            IAlloc R_SP R_SP]
        ++ push R_AUX1 ++ load_arg (scr C) R_AUX1 ++ push R_AUX1
        ++ push R_RA
        ++ [:: IConst (IPtr (flag_buf_ptr (scr C))) R_AUX1;
               ILoad R_AUX1 R_AUX2]
        ++ push R_AUX2
        ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
               IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2; IJal plf]
        ++ tailc) ->
  Pointer.component pc = C ->
  Transitional.Register.get_tag R_RA rs = Some Other ->
  Transitional.Memory.load m (C, 1, 0%Z) = Some mscr ->
  tvtag mscr.1 = Other ->
  Transitional.Memory.load m (C, 1, 1%Z) = Some mflag ->
  tvtag mflag.1 = Other ->
  Transitional.val mflag.1 = Int 0 ->
  (exists cm, getm m C = Some cm) ->
  ~ List.In TInv.CReg (TInv.sites L) ->
  ~ List.In (TInv.CMem (C, 1, 0%Z)) (TInv.sites L) ->
  ~ List.In (TInv.CMem (C, 1, 1%Z)) (TInv.sites L) ->
  (forall b0, a C b0 <> Some 1) ->
  TInject.minj a mem m ->
  TInv.tag_inv L m rs pct ->
  exists m' rs' fbE pcF,
    [/\ plus TS.step cde (m, rs, pc, pct) E0 (m', rs', pcF, pct),
        [/\ (forall (o : Z) w,
               Transitional.Memory.load m (C, fbE, o) = Some w -> False),
            (forall b0, a C b0 <> Some fbE),
            fbE <> 1,
            TInject.minj a mem m'
          & TStack.frame_cap m' C fbE (4 + ne)],
        [/\ TMem.vload m' (C, fbE, 0%Z)
              = Some (Transitional.val (Transitional.Register.get R_SP rs)),
            TMem.tload m' (C, fbE, 0%Z) = Some Other,
            TMem.vload m' (C, fbE, 1%Z) = Some (Transitional.val mscr.1),
            TMem.tload m' (C, fbE, 1%Z) = Some Other
          & [/\ TMem.vload m' (C, fbE, 2%Z)
                  = Some (Transitional.val
                            (Transitional.Register.get R_RA rs)),
                TMem.tload m' (C, fbE, 2%Z) = Some Other,
                TMem.vload m' (C, fbE, 3%Z) = Some (Int 0)
              & TMem.tload m' (C, fbE, 3%Z) = Some Other]],
        [/\ (forall q, (Pointer.component q <> C \/ Pointer.block q <> fbE) ->
               q <> ((C, 1, 1%Z) : Pointer.t) ->
               TMem.vload m' q = TMem.vload m q),
            (forall q, (Pointer.component q <> C \/ Pointer.block q <> fbE) ->
               q <> ((C, 1, 1%Z) : Pointer.t) ->
               TMem.tload m' q = TMem.tload m q),
            Pointer.component pcF = C,
            TMacros.code_at_I cde C pcF (IJal plf :: tailc)
          & [/\ Transitional.Register.get R_ONE rs' = MVal Other (Int 1),
                Transitional.Register.get R_SP rs'
                  = MVal Other (Ptr (C, fbE, 4%Z))
              & Transitional.val (Transitional.Register.get R_COM rs')
                = Int 0]]
      & [/\ TInv.tag_inv L m' rs' pct,
            (* ★ the FLAG, now set: the wrapper's own [IStore]. This is
               [scrs_ok]'s second clause, and the reason a LATER genuine call
               to [main] takes the other branch of the [IBnz]. *)
            TMem.vload m' (C, 1, 1%Z) = Some (Int 1)
          & TMem.tload m' (C, 1, 1%Z) = Some Other]].
Proof.
  move=> Hcode Hcomp Hrt Hmscr Etm Hmflag Etf Evf HcmF HnotReg Hnoscr Hnoflag
         Hscrp HI Htag.
  (* --- 1. IConst 1 R_ONE --- *)
  have Hc0 := Hcode.
  have S1 : TS.step cde (m, rs, pc, pct) E0
            (m, Transitional.Register.set R_ONE (Int 1) Other rs,
             Pointer.inc pc, pct).
  { have -> : Int 1 = imm_to_val (IInt 1) by [].
    eapply TS.Const; [exact: (TMacros.code_at_I_head Hc0)
                     | exact: (TMacros.check_pc_at_I Hc0)]. }
  set rs1 := (Transitional.Register.set R_ONE (Int 1) Other rs) in S1 *.
  have Htag1 : TInv.tag_inv L m rs1 pct
    by apply: TInv.tag_inv_setreg; [by [] | exact: Htag].
  set pc1 := Pointer.inc pc.
  have Hcomp1 : Pointer.component pc1 = C
    by rewrite /pc1 Pointer.inc_preserves_component.
  have Hc1 : TMacros.code_at_I cde C pc1
      ([:: IMov R_SP R_AUX1; IConst (IInt (Z.of_nat (4 + ne))) R_SP;
           IAlloc R_SP R_SP]
       ++ IStore R_SP R_AUX1
          :: (IBinOp Add R_SP R_ONE R_SP
              :: load_arg (scr C) R_AUX1 ++ push R_AUX1 ++ push R_RA
                 ++ [:: IConst (IPtr (flag_buf_ptr (scr C))) R_AUX1;
                        ILoad R_AUX1 R_AUX2]
                 ++ push R_AUX2
                 ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM;
                        ILabel lmain; IConst (IInt 1) R_AUX2;
                        IStore R_AUX1 R_AUX2; IJal plf]
                 ++ tailc))
    by exact: (TMacros.code_at_I_tail Hc0).
  case: (prologue_alloc_run Hc1 Hcomp1
           (TInv.ti_regs Htag1 (r := R_SP) (ltac:(by []))) HcmF HI Htag1)
    => [m1 [rs2 [fbE [Sal [Hfresh Havoid [Hnosite Hpres] Hmj1 Hcap1]
                          [HSP2 HA12 Hoth2] Htag2]]]].
  have HfbE1 : fbE <> 1 by move=> E; apply: (Hfresh 0%Z mscr); rewrite E.
  have Hd1 : Pointer.component ((C, 1, 0%Z) : Pointer.t) <> C
             \/ Pointer.block ((C, 1, 0%Z) : Pointer.t) <> fbE
    by right=> E; apply: HfbE1; rewrite -E.
  have Hd2 : Pointer.component ((C, 1, 1%Z) : Pointer.t) <> C
             \/ Pointer.block ((C, 1, 1%Z) : Pointer.t) <> fbE
    by right=> E; apply: HfbE1; rewrite -E.
  have Hmscr1 : Transitional.Memory.load m1 (C, 1, 0%Z) = Some mscr
    by rewrite (Hpres _ Hd1).
  have Hmflag1 : Transitional.Memory.load m1 (C, 1, 1%Z) = Some mflag
    by rewrite (Hpres _ Hd2).
  set pc4 := Pointer.inc (Pointer.inc (Pointer.inc pc1)).
  have Hcomp4 : Pointer.component pc4 = C
    by rewrite /pc4 !Pointer.inc_preserves_component.
  have Hc4 : TMacros.code_at_I cde C pc4
      (push R_AUX1 ++ load_arg (scr C) R_AUX1 ++ push R_AUX1 ++ push R_RA
       ++ [:: IConst (IPtr (flag_buf_ptr (scr C))) R_AUX1;
              ILoad R_AUX1 R_AUX2]
       ++ push R_AUX2
       ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
              IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2; IJal plf]
       ++ tailc).
  { apply: TMacros.code_at_I_tail. apply: TMacros.code_at_I_tail.
    apply: TMacros.code_at_I_tail. exact: Hc1. }
  (* --- 5-6. push R_AUX1: the caller's [R_SP] into slot 0 --- *)
  have HONE2 : Transitional.Register.get R_ONE rs2 = MVal Other (Int 1)
    by rewrite Hoth2 // /rs1 TInv.get_set_eq.
  have Hsp0 : (0 <= 0 < Z.of_nat (4 + ne))%Z by split; lia.
  case: (push_data_run Hc4 (ltac:(by []) :
           load_arg (scr C) R_AUX1 ++ push R_AUX1 ++ push R_RA
           ++ [:: IConst (IPtr (flag_buf_ptr (scr C))) R_AUX1;
                  ILoad R_AUX1 R_AUX2]
           ++ push R_AUX2
           ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
                  IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2; IJal plf]
           ++ tailc <> [::]) Hcomp4
           (ltac:(by []) : R_AUX1 <> R_RA)
           (ltac:(by []) : R_SP <> R_AUX1)
           (ltac:(by []) : R_ONE <> R_AUX1)
           HSP2 HONE2 Hsp0 Hcap1 (Hnosite 0%Z) Havoid Hmj1 Htag2)
    => [m2 [rs3 [Sp0 [Hsl0 Hpres0 Hst0 Hcap2 Hmj2] [HSP3 HA13 Hoth3] Htag3]]].
  have Hne0 : forall o : Z, ((C, 1, o) : Pointer.t) <> (C, fbE, 0%Z)
    by move=> o E; apply: HfbE1; move: (f_equal Pointer.block E) => /= ->.
  have Hmscr2 : Transitional.Memory.load m2 (C, 1, 0%Z) = Some mscr
    by rewrite (TMem.load_store_neq Hst0 (Hne0 0%Z)).
  have Hmflag2 : Transitional.Memory.load m2 (C, 1, 1%Z) = Some mflag
    by rewrite (TMem.load_store_neq Hst0 (Hne0 1%Z)).
  (* --- 7-8. load_arg: the INHERITED scratch value into [R_AUX1] --- *)
  set pc6 := Pointer.inc (Pointer.inc pc4).
  have Hcomp6 : Pointer.component pc6 = C
    by rewrite /pc6 /pc4 !Pointer.inc_preserves_component.
  have Hc6 : TMacros.code_at_I cde C pc6
      (IConst (IPtr (scr C)) R_AUX1
       :: ILoad R_AUX1 R_AUX1 :: push R_AUX1 ++ push R_RA
          ++ [:: IConst (IPtr (flag_buf_ptr (scr C))) R_AUX1;
                 ILoad R_AUX1 R_AUX2]
          ++ push R_AUX2
          ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
                 IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2; IJal plf]
          ++ tailc).
  { apply: TMacros.code_at_I_tail. apply: TMacros.code_at_I_tail.
    exact: Hc4. }
  have Hc7 := TMacros.code_at_I_tail Hc6.
  have S7 : TS.step cde (m2, rs3, pc6, pct) E0
            (m2, Transitional.Register.set R_AUX1 (Ptr (scr C)) Other rs3,
             Pointer.inc pc6, pct).
  { have -> : Ptr (scr C) = imm_to_val (IPtr (scr C)) by [].
    eapply TS.Const; [exact: (TMacros.code_at_I_head Hc6)
                     | exact: (TMacros.check_pc_at_I Hc6)]. }
  set rs4 := (Transitional.Register.set R_AUX1 (Ptr (scr C)) Other rs3)
    in S7 *.
  case: (TMem.store_after_load
           ({| Transitional.val := Transitional.val mscr.1;
               tvtag := if is_address (tvtag mscr.1) then Invalidated
                        else Other |},
            {| vtag := if is_address (tvtag mscr.1) then Invalidated
                       else Other;
               color := C; entry := None; is_code := false |})
           Hmscr2) => [m3 Hst3].
  have S8 : TS.step cde (m2, rs4, Pointer.inc pc6, pct) E0
            (m3, Transitional.Register.set R_AUX1
                   (Transitional.val mscr.1) (tvtag mscr.1) rs4,
             Pointer.inc (Pointer.inc pc6), pct).
  { eapply TS.Load.
    - exact: (TMacros.code_at_I_head Hc7).
    - exact: (TMacros.check_pc_at_I Hc7).
    - by rewrite /rs4 TInv.get_set_eq.
    - by rewrite /rs4 TInv.get_set_eq.
    - by rewrite /= Pointer.inc_preserves_component Hcomp6.
    - exact: Hmscr2.
    - by rewrite /= Pointer.inc_preserves_component Hcomp6; exact: Hst3. }
  set rs5 := (Transitional.Register.set R_AUX1
                (Transitional.val mscr.1) (tvtag mscr.1) rs4) in S8 *.
  have Hv3 : forall q, TMem.vload m3 q = TMem.vload m2 q.
  { move=> q. apply: (TMem.vload_store_same Hmscr2 _ Hst3 q). by []. }
  have Ht3 : forall q, TMem.tload m3 q = TMem.tload m2 q.
  { move=> q. apply: (TMem.tload_store_same Hmscr2 _ Hst3 q).
    by rewrite /= Etm. }
  have Hraw3 : forall q, q <> ((C, 1, 0%Z) : Pointer.t) ->
      Transitional.Memory.load m3 q = Transitional.Memory.load m2 q
    by move=> q Hq; exact: (TMem.load_store_neq Hst3 Hq).
  have Hcap3 : TStack.frame_cap m3 C fbE (4 + ne)
    by move=> j Hj; rewrite Hv3; exact: Hcap2 Hj.
  have Hmj3 : TInject.minj a mem m3
    by apply: (TInject.minj_store_outside _ Hst3 Hmj2) => b0; exact: Hscrp b0.
  have Htag5 : TInv.tag_inv L m3 rs5 pct.
  { rewrite /rs5 /rs4 Etm. apply: TInv.tag_inv_setreg; first by [].
    apply: TInv.tag_inv_setreg; first by [].
    apply: (TInv.tag_inv_store_data Hnoscr _ Hst3 Htag3). by rewrite /= Etm. }
  have Hmflag3 : Transitional.Memory.load m3 (C, 1, 1%Z) = Some mflag.
  { rewrite Hraw3.
    - exact: Hmflag2.
    - by move=> E; move: (f_equal Pointer.offset E) => /=; lia. }
  (* --- 9-10. push R_AUX1: the inherited scratch into slot 1 --- *)
  set pc8 := Pointer.inc (Pointer.inc pc6).
  have Hcomp8 : Pointer.component pc8 = C
    by rewrite /pc8 /pc6 /pc4 !Pointer.inc_preserves_component.
  have Hc8 : TMacros.code_at_I cde C pc8
      (push R_AUX1 ++ push R_RA
       ++ [:: IConst (IPtr (flag_buf_ptr (scr C))) R_AUX1;
              ILoad R_AUX1 R_AUX2]
       ++ push R_AUX2
       ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
              IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2; IJal plf]
       ++ tailc) by exact: (TMacros.code_at_I_tail Hc7).
  have HSP5 : Transitional.Register.get R_SP rs5
            = MVal Other (Ptr (C, fbE, (0 + 1)%Z))
    by rewrite /rs5 TInv.get_set_neq // /rs4 TInv.get_set_neq //.
  have HONE5 : Transitional.Register.get R_ONE rs5 = MVal Other (Int 1)
    by rewrite /rs5 TInv.get_set_neq // /rs4 TInv.get_set_neq // Hoth3 //.
  have Hsp1 : (0 <= 0 + 1 < Z.of_nat (4 + ne))%Z by split; lia.
  case: (push_data_run Hc8 (ltac:(by []) :
           push R_RA
           ++ [:: IConst (IPtr (flag_buf_ptr (scr C))) R_AUX1;
                  ILoad R_AUX1 R_AUX2]
           ++ push R_AUX2
           ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
                  IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2; IJal plf]
           ++ tailc <> [::]) Hcomp8
           (ltac:(by []) : R_AUX1 <> R_RA)
           (ltac:(by []) : R_SP <> R_AUX1)
           (ltac:(by []) : R_ONE <> R_AUX1)
           HSP5 HONE5 Hsp1 Hcap3 (Hnosite (0 + 1)%Z) Havoid Hmj3 Htag5)
    => [m4 [rs6 [Sp1 [Hsl1 Hpres1 Hst1 Hcap4 Hmj4] [HSP6 HA16 Hoth6] Htag6]]].
  have Hne1 : forall o : Z, ((C, 1, o) : Pointer.t) <> (C, fbE, (0 + 1)%Z)
    by move=> o E; apply: HfbE1; move: (f_equal Pointer.block E) => /= ->.
  have Hmflag4 : Transitional.Memory.load m4 (C, 1, 1%Z) = Some mflag
    by rewrite (TMem.load_store_neq Hst1 (Hne1 1%Z)).
  (* --- 11-12. push R_RA: main's activation has no capability to spill --- *)
  set pc10 := Pointer.inc (Pointer.inc pc8).
  have Hcomp10 : Pointer.component pc10 = C
    by rewrite /pc10 /pc8 /pc6 /pc4 !Pointer.inc_preserves_component.
  have Hc10 : TMacros.code_at_I cde C pc10
      (push R_RA
       ++ [:: IConst (IPtr (flag_buf_ptr (scr C))) R_AUX1;
              ILoad R_AUX1 R_AUX2]
       ++ push R_AUX2
       ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
              IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2; IJal plf]
       ++ tailc) by exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hc8)).
  have HONE6 : Transitional.Register.get R_ONE rs6 = MVal Other (Int 1)
    by rewrite Hoth6 //.
  have Hrt6 : Transitional.Register.get_tag R_RA rs6 = Some Other.
  { have HRA6 : Transitional.Register.get R_RA rs6
              = Transitional.Register.get R_RA rs
      by rewrite Hoth6 // /rs5 TInv.get_set_neq // /rs4 TInv.get_set_neq //
                 Hoth3 // Hoth2 // /rs1 TInv.get_set_neq //.
    move: (TInv.ti_dom Htag6 R_RA) => [tv6 Hg6]. move: Hrt HRA6.
    rewrite /Transitional.Register.get_tag /Transitional.Register.get Hg6 /=.
    case: (getm rs _) => [tv|] /=.
    - by move=> [E1] E2; rewrite E2 E1.
    - by move=> []. }
  have Hsp2 : (0 <= 0 + 1 + 1 < Z.of_nat (4 + ne))%Z by split; lia.
  case: (push_junk_ra_run Hc10 (ltac:(by []) :
           [:: IConst (IPtr (flag_buf_ptr (scr C))) R_AUX1;
               ILoad R_AUX1 R_AUX2]
           ++ push R_AUX2
           ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
                  IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2; IJal plf]
           ++ tailc <> [::]) Hcomp10 HSP6 HONE6 Hrt6 Hsp2 Hcap4
           (Hnosite (0 + 1 + 1)%Z) HnotReg Havoid Hmj4 Htag6)
    => [m5 [rs7 [Sp2 [Hsl2 Hpres2 Hst2 Hcap5 Hmj5] [HSP7 Hoth7] Htag7]]].
  have Hne2 : forall o : Z, ((C, 1, o) : Pointer.t) <> (C, fbE, (0 + 1 + 1)%Z)
    by move=> o E; apply: HfbE1; move: (f_equal Pointer.block E) => /= ->.
  have Hmflag5 : Transitional.Memory.load m5 (C, 1, 1%Z) = Some mflag
    by rewrite (TMem.load_store_neq Hst2 (Hne2 1%Z)).
  (* --- 13-14. the FLAG load: the context marker --- *)
  set pc12 := Pointer.inc (Pointer.inc pc10).
  have Hcomp12 : Pointer.component pc12 = C
    by rewrite /pc12 /pc10 /pc8 /pc6 /pc4 !Pointer.inc_preserves_component.
  have Hc12 : TMacros.code_at_I cde C pc12
      (IConst (IPtr (flag_buf_ptr (scr C))) R_AUX1
       :: ILoad R_AUX1 R_AUX2 :: push R_AUX2
          ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
                 IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2; IJal plf]
          ++ tailc)
    by exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hc10)).
  have Hc13 := TMacros.code_at_I_tail Hc12.
  have Eflagc : Pointer.component (flag_buf_ptr (scr C)) = C by [].
  have Eflag : flag_buf_ptr (scr C) = (C, 1, 1%Z) by [].
  have S13 : TS.step cde (m5, rs7, pc12, pct) E0
             (m5, Transitional.Register.set R_AUX1
                    (Ptr (flag_buf_ptr (scr C))) Other rs7,
              Pointer.inc pc12, pct).
  { have -> : Ptr (flag_buf_ptr (scr C)) = imm_to_val (IPtr (flag_buf_ptr (scr C)))
      by [].
    eapply TS.Const; [exact: (TMacros.code_at_I_head Hc12)
                     | exact: (TMacros.check_pc_at_I Hc12)]. }
  set rs8 := (Transitional.Register.set R_AUX1
                (Ptr (flag_buf_ptr (scr C))) Other rs7) in S13 *.
  case: (TMem.store_after_load
           ({| Transitional.val := Transitional.val mflag.1;
               tvtag := if is_address (tvtag mflag.1) then Invalidated
                        else Other |},
            {| vtag := if is_address (tvtag mflag.1) then Invalidated
                       else Other;
               color := C; entry := None; is_code := false |})
           Hmflag5) => [m6 Hst6].
  have S14 : TS.step cde (m5, rs8, Pointer.inc pc12, pct) E0
             (m6, Transitional.Register.set R_AUX2
                    (Transitional.val mflag.1) (tvtag mflag.1) rs8,
              Pointer.inc (Pointer.inc pc12), pct).
  { eapply TS.Load.
    - exact: (TMacros.code_at_I_head Hc13).
    - exact: (TMacros.check_pc_at_I Hc13).
    - by rewrite /rs8 TInv.get_set_eq.
    - by rewrite /rs8 TInv.get_set_eq.
    - by rewrite Eflag /= Pointer.inc_preserves_component Hcomp12.
    - by rewrite Eflag; exact: Hmflag5.
    - by rewrite Eflag /= Pointer.inc_preserves_component Hcomp12;
         exact: Hst6. }
  set rs9 := (Transitional.Register.set R_AUX2
                (Transitional.val mflag.1) (tvtag mflag.1) rs8) in S14 *.
  have Hv6 : forall q, TMem.vload m6 q = TMem.vload m5 q.
  { move=> q. apply: (TMem.vload_store_same Hmflag5 _ Hst6 q). by []. }
  have Ht6 : forall q, TMem.tload m6 q = TMem.tload m5 q.
  { move=> q. apply: (TMem.tload_store_same Hmflag5 _ Hst6 q).
    by rewrite /= Etf. }
  have Hraw6 : forall q, q <> ((C, 1, 1%Z) : Pointer.t) ->
      Transitional.Memory.load m6 q = Transitional.Memory.load m5 q
    by move=> q Hq; exact: (TMem.load_store_neq Hst6 Hq).
  have Hcap6 : TStack.frame_cap m6 C fbE (4 + ne)
    by move=> j Hj; rewrite Hv6; exact: Hcap5 Hj.
  have Hmj6 : TInject.minj a mem m6
    by apply: (TInject.minj_store_outside _ Hst6 Hmj5) => b0; exact: Hscrp b0.
  have Htag9 : TInv.tag_inv L m6 rs9 pct.
  { rewrite /rs9 /rs8 Etf. apply: TInv.tag_inv_setreg; first by [].
    apply: TInv.tag_inv_setreg; first by [].
    apply: (TInv.tag_inv_store_data Hnoflag _ Hst6 Htag7).
    by rewrite /= Etf. }
  (* --- 15-16. push R_AUX2: the marker into slot 3 --- *)
  set pc14 := Pointer.inc (Pointer.inc pc12).
  have Hcomp14 : Pointer.component pc14 = C
    by rewrite /pc14 /pc12 /pc10 /pc8 /pc6 /pc4
               !Pointer.inc_preserves_component.
  have Hc14 : TMacros.code_at_I cde C pc14
      (push R_AUX2
       ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
              IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2; IJal plf]
       ++ tailc) by exact: (TMacros.code_at_I_tail Hc13).
  have HSP9 : Transitional.Register.get R_SP rs9
            = MVal Other (Ptr (C, fbE, (0 + 1 + 1 + 1)%Z))
    by rewrite /rs9 TInv.get_set_neq // /rs8 TInv.get_set_neq //;
       exact: HSP7.
  have HONE9 : Transitional.Register.get R_ONE rs9 = MVal Other (Int 1)
    by rewrite /rs9 TInv.get_set_neq // /rs8 TInv.get_set_neq // Hoth7 //;
       exact: HONE6.
  have Hsp3 : (0 <= 0 + 1 + 1 + 1 < Z.of_nat (4 + ne))%Z by split; lia.
  case: (push_data_run Hc14 (ltac:(by []) :
           [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
               IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2; IJal plf]
           ++ tailc <> [::]) Hcomp14
           (ltac:(by []) : R_AUX2 <> R_RA)
           (ltac:(by []) : R_SP <> R_AUX2)
           (ltac:(by []) : R_ONE <> R_AUX2)
           HSP9 HONE9 Hsp3 Hcap6 (Hnosite (0 + 1 + 1 + 1)%Z) Havoid Hmj6
           Htag9)
    => [m7 [rs10 [Sp3 [Hsl3 Hpres3 Hst7 Hcap7 Hmj7]
                       [HSP10 HA210 Hoth10] Htag10]]].
  have EA2 : Transitional.Register.get R_AUX2 rs9 = MVal Other (Int 0)
    by rewrite /rs9 TInv.get_set_eq Etf Evf.
  have EA210 : Transitional.Register.get R_AUX2 rs10 = MVal Other (Int 0)
    by rewrite HA210 EA2.
  (* --- 17-21. the branch is not taken; install the argument; set the flag *)
  set pc16 := Pointer.inc (Pointer.inc pc14).
  have Hcomp16 : Pointer.component pc16 = C
    by rewrite /pc16 /pc14 /pc12 /pc10 /pc8 /pc6 /pc4
               !Pointer.inc_preserves_component.
  have Hc16 : TMacros.code_at_I cde C pc16
      (IBnz R_AUX2 lmain
       :: IConst (IInt 0) R_COM
          :: ILabel lmain
             :: IConst (IInt 1) R_AUX2
                :: IStore R_AUX1 R_AUX2 :: IJal plf :: tailc)
    by exact: (TMacros.code_at_I_tail (TMacros.code_at_I_tail Hc14)).
  have S17 : TS.step cde (m7, rs10, pc16, pct) E0
             (m7, rs10, Pointer.inc pc16, pct).
  { eapply TS.BnzZ.
    - exact: (TMacros.code_at_I_head Hc16).
    - exact: (TMacros.check_pc_at_I Hc16).
    - by rewrite EA210.
    - by rewrite EA210. }
  have Hc17 := TMacros.code_at_I_tail Hc16.
  have S18 : TS.step cde (m7, rs10, Pointer.inc pc16, pct) E0
             (m7, Transitional.Register.set R_COM (Int 0) Other rs10,
              Pointer.inc (Pointer.inc pc16), pct).
  { have -> : Int 0 = imm_to_val (IInt 0) by [].
    eapply TS.Const; [exact: (TMacros.code_at_I_head Hc17)
                     | exact: (TMacros.check_pc_at_I Hc17)]. }
  set rs11 := (Transitional.Register.set R_COM (Int 0) Other rs10) in S18 *.
  have Hc18 := TMacros.code_at_I_tail Hc17.
  have S19 : TS.step cde (m7, rs11, Pointer.inc (Pointer.inc pc16), pct) E0
             (m7, rs11, Pointer.inc (Pointer.inc (Pointer.inc pc16)), pct)
    by eapply TS.Label; [exact: (TMacros.code_at_I_head Hc18)
                        | exact: (TMacros.check_pc_at_I Hc18)].
  have Hc19 := TMacros.code_at_I_tail Hc18.
  set pc19 := Pointer.inc (Pointer.inc (Pointer.inc pc16)).
  have S20 : TS.step cde (m7, rs11, pc19, pct) E0
             (m7, Transitional.Register.set R_AUX2 (Int 1) Other rs11,
              Pointer.inc pc19, pct).
  { have -> : Int 1 = imm_to_val (IInt 1) by [].
    eapply TS.Const; [exact: (TMacros.code_at_I_head Hc19)
                     | exact: (TMacros.check_pc_at_I Hc19)]. }
  set rs12 := (Transitional.Register.set R_AUX2 (Int 1) Other rs11) in S20 *.
  have Hc20 := TMacros.code_at_I_tail Hc19.
  have Hmflag7 : exists w,
      Transitional.Memory.load m7 (C, 1, 1%Z) = Some w.
  { have Hne3 : ((C, 1, 1%Z) : Pointer.t) <> (C, fbE, (0 + 1 + 1 + 1)%Z)
      by move=> E; apply: HfbE1; move: (f_equal Pointer.block E) => /= ->.
    rewrite (TMem.load_store_neq Hst7 Hne3) (TMem.load_store_eq Hst6).
    by eexists. }
  case: Hmflag7 => [wf Hwf].
  case: (TMem.store_after_load
           (Transitional.Register.get R_AUX2 rs12,
            {| vtag := Other; color := C; entry := None; is_code := false |})
           Hwf) => [m8 Hst8].
  have EA212 : Transitional.Register.get R_AUX2 rs12 = MVal Other (Int 1)
    by rewrite /rs12 TInv.get_set_eq.
  have EA112 : Transitional.Register.get R_AUX1 rs12
             = MVal Other (Ptr (C, 1, 1%Z)).
  { rewrite /rs12 TInv.get_set_neq // /rs11 TInv.get_set_neq //
            Hoth10 // /rs9 TInv.get_set_neq // /rs8 TInv.get_set_eq.
    by rewrite Eflag. }
  have Htag12 : TInv.tag_inv L m7 rs12 pct.
  { rewrite /rs12 /rs11. apply: TInv.tag_inv_setreg; first by [].
    apply: TInv.tag_inv_setreg; first by []. exact: Htag10. }
  have S21 : TS.step cde (m7, rs12, Pointer.inc pc19, pct) E0
             (m8, Transitional.Register.set R_AUX2
                    (Transitional.val (Transitional.Register.get R_AUX2 rs12))
                    Other rs12,
              Pointer.inc (Pointer.inc pc19), pct).
  { have -> : Other = (if is_address Other then Invalidated else Other) by [].
    eapply TS.Store.
    - exact: (TMacros.code_at_I_head Hc20).
    - exact: (TMacros.check_pc_at_I Hc20).
    - by rewrite EA112.
    - by rewrite EA112.
    - have -> : Pointer.component ((C, 1, 1%Z) : Pointer.t) = C by [].
      by rewrite /pc19 /pc16 /pc14 /pc12 /pc10 /pc8 /pc6 /pc4
                 !Pointer.inc_preserves_component.
    - apply: (TInv.ti_tag_other Htag12). by [].
    - rewrite Pointer.inc_preserves_component /pc19 /pc16 /pc14 /pc12
              /pc10 /pc8 /pc6 /pc4 !Pointer.inc_preserves_component Hcomp.
      exact: Hst8. }
  set rs13 := Transitional.Register.set R_AUX2
                (Transitional.val (Transitional.Register.get R_AUX2 rs12))
                Other rs12.
  have Htag13 : TInv.tag_inv L m8 rs13 pct.
  { rewrite /rs13 /rs12 /rs11. apply: TInv.tag_inv_setreg; first by [].
    apply: TInv.tag_inv_setreg; first by [].
    apply: TInv.tag_inv_setreg; first by [].
    apply: (TInv.tag_inv_store_data Hnoflag _ Hst8 Htag10).
    by rewrite /= EA212. }
  have Hmj8 : TInject.minj a mem m8
    by apply: (TInject.minj_store_outside _ Hst8 Hmj7) => b0; exact: Hscrp b0.
  (* --- the slots, at the final memory --- *)
  have Lfb : forall (o : Z) w, o <> (0 + 1 + 1 + 1)%Z ->
      Transitional.Memory.load m5 (C, fbE, o) = Some w ->
      Transitional.Memory.load m8 (C, fbE, o) = Some w.
  { move=> o w Ho Hl.
    have HneF : ((C, fbE, o) : Pointer.t) <> (C, 1, 1%Z)
      by move=> E; apply: HfbE1; move: (f_equal Pointer.block E) => /= <-.
    have HneS : ((C, fbE, o) : Pointer.t) <> (C, fbE, (0 + 1 + 1 + 1)%Z)
      by move=> E; apply: Ho; move: (f_equal Pointer.offset E).
    by rewrite (TMem.load_store_neq Hst8 HneF)
               (TMem.load_store_neq Hst7 HneS)
               (TMem.load_store_neq Hst6 HneF). }
  have Hsl3' : Transitional.Memory.load m8 (C, fbE, (0 + 1 + 1 + 1)%Z)
             = Some (Transitional.Register.get R_AUX2 rs9,
                     {| vtag := Other; color := C; entry := None;
                        is_code := false |}).
  { have HneF : ((C, fbE, (0 + 1 + 1 + 1)%Z) : Pointer.t) <> (C, 1, 1%Z)
      by move=> E; apply: HfbE1; move: (f_equal Pointer.block E) => /= <-.
    by rewrite (TMem.load_store_neq Hst8 HneF). }
  have Hsl2' := Lfb (0 + 1 + 1)%Z _ (ltac:(by move=> E; move: E => /=; lia))
                  Hsl2.
  have Hsl1' : Transitional.Memory.load m8 (C, fbE, (0 + 1)%Z)
             = Some (Transitional.Register.get R_AUX1 rs5,
                     {| vtag := Other; color := C; entry := None;
                        is_code := false |}).
  { apply: (Lfb (0 + 1)%Z _ (ltac:(by move=> E; move: E => /=; lia))).
    have HneS : ((C, fbE, (0 + 1)%Z) : Pointer.t)
              <> (C, fbE, (0 + 1 + 1)%Z)
      by move=> E; move: (f_equal Pointer.offset E) => /=; lia.
    by rewrite (TMem.load_store_neq Hst2 HneS). }
  have Hsl0' : Transitional.Memory.load m8 (C, fbE, 0%Z)
             = Some (Transitional.Register.get R_AUX1 rs2,
                     {| vtag := Other; color := C; entry := None;
                        is_code := false |}).
  { apply: (Lfb 0%Z _ (ltac:(by move=> E; move: E => /=; lia))).
    have Hn1 : ((C, fbE, 0%Z) : Pointer.t) <> (C, fbE, (0 + 1 + 1)%Z)
      by move=> E; move: (f_equal Pointer.offset E) => /=; lia.
    have Hn2 : ((C, fbE, 0%Z) : Pointer.t) <> (C, fbE, (0 + 1)%Z)
      by move=> E; move: (f_equal Pointer.offset E) => /=; lia.
    have Hn3 : ((C, fbE, 0%Z) : Pointer.t) <> (C, 1, 0%Z)
      by move=> E; apply: HfbE1; move: (f_equal Pointer.block E) => /= <-.
    by rewrite (TMem.load_store_neq Hst2 Hn1) (TMem.load_store_neq Hst1 Hn2)
               (TMem.load_store_neq Hst3 Hn3). }
  (* --- assembled --- *)
  have E1z : (0 + 1)%Z = 1%Z by [].
  have E2z : (0 + 1 + 1)%Z = 2%Z by [].
  have E3z : (0 + 1 + 1 + 1)%Z = 3%Z by [].
  have E4z : (0 + 1 + 1 + 1 + 1)%Z = 4%Z by [].
  have EA1rs2 : Transitional.Register.get R_AUX1 rs2
              = MVal Other
                  (Transitional.val (Transitional.Register.get R_SP rs))
    by rewrite HA12 /rs1 TInv.get_set_neq //.
  have EA1rs5 : Transitional.Register.get R_AUX1 rs5
              = MVal Other (Transitional.val mscr.1)
    by rewrite /rs5 TInv.get_set_eq Etm.
  have ERArs7 : Transitional.Register.get R_RA rs6
              = MVal Other
                  (Transitional.val (Transitional.Register.get R_RA rs)).
  { have HRA6 : Transitional.Register.get R_RA rs6
              = Transitional.Register.get R_RA rs
      by rewrite Hoth6 // /rs5 TInv.get_set_neq // /rs4 TInv.get_set_neq //
                 Hoth3 // Hoth2 // /rs1 TInv.get_set_neq //.
    rewrite HRA6. move: Hrt.
    rewrite /Transitional.Register.get_tag /Transitional.Register.get.
    case: (getm rs _) => [tv|] //=.
    by case: tv => [t u] /= [->]. }
  exists m8, rs13, fbE, (Pointer.inc (Pointer.inc pc19)).
  split.
  - eapply plus_left with (t1 := E0) (t2 := E0); [exact: S1 | | by []].
    eapply star_trans with (t1 := E0) (t2 := E0); [exact: Sal | | by []].
    eapply star_trans with (t1 := E0) (t2 := E0);
      [exact: (plus_star Sp0) | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: S7 | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: S8 | | by []].
    eapply star_trans with (t1 := E0) (t2 := E0);
      [exact: (plus_star Sp1) | | by []].
    eapply star_trans with (t1 := E0) (t2 := E0);
      [exact: (plus_star Sp2) | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: S13 | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: S14 | | by []].
    eapply star_trans with (t1 := E0) (t2 := E0);
      [exact: (plus_star Sp3) | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: S17 | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: S18 | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: S19 | | by []].
    eapply star_step with (t1 := E0) (t2 := E0); [exact: S20 | | by []].
    exact: star_one S21.
  - split.
    + exact: Hfresh.
    + exact: Havoid.
    + exact: HfbE1.
    + exact: Hmj8.
    + move=> j Hj. case: (Hcap7 j Hj) => [u Hu]. exists u.
      move: Hu; rewrite /TMem.vload.
      have HneF : ((C, fbE, j) : Pointer.t) <> (C, 1, 1%Z)
        by move=> E; apply: HfbE1; move: (f_equal Pointer.block E) => /= <-.
      by rewrite (TMem.load_store_neq Hst8 HneF).
  - split.
    + by rewrite /TMem.vload Hsl0' EA1rs2.
    + by rewrite /TMem.tload Hsl0' EA1rs2.
    + by rewrite E1z in Hsl1'; rewrite /TMem.vload Hsl1' EA1rs5.
    + by rewrite E1z in Hsl1'; rewrite /TMem.tload Hsl1' EA1rs5.
    + split.
      * by rewrite E2z in Hsl2'; rewrite /TMem.vload Hsl2' ERArs7.
      * by rewrite E2z in Hsl2'; rewrite /TMem.tload Hsl2' ERArs7.
      * by rewrite E3z in Hsl3'; rewrite /TMem.vload Hsl3' EA2.
      * by rewrite E3z in Hsl3'; rewrite /TMem.tload Hsl3' EA2.
  - have Hne8 : forall q,
        (Pointer.component q <> C \/ Pointer.block q <> fbE) ->
        forall o : Z, q <> ((C, fbE, o) : Pointer.t)
      by move=> q HD o E; case: HD => [H|H]; apply: H; rewrite E.
    split.
    + move=> q HD Hq.
      have E87 : TMem.vload m8 q = TMem.vload m7 q
        by rewrite /TMem.vload (TMem.load_store_neq Hst8 Hq).
      have E76 : TMem.vload m7 q = TMem.vload m6 q
        by rewrite /TMem.vload (TMem.load_store_neq Hst7 (Hne8 q HD _)).
      have E54 : TMem.vload m5 q = TMem.vload m4 q
        by rewrite /TMem.vload (TMem.load_store_neq Hst2 (Hne8 q HD _)).
      have E43 : TMem.vload m4 q = TMem.vload m3 q
        by rewrite /TMem.vload (TMem.load_store_neq Hst1 (Hne8 q HD _)).
      have E21 : TMem.vload m2 q = TMem.vload m1 q
        by rewrite /TMem.vload (TMem.load_store_neq Hst0 (Hne8 q HD _)).
      have E10 : TMem.vload m1 q = TMem.vload m q
        by rewrite /TMem.vload (Hpres q HD).
      by rewrite E87 E76 Hv6 E54 E43 Hv3 E21 E10.
    + move=> q HD Hq.
      have E87 : TMem.tload m8 q = TMem.tload m7 q
        by rewrite /TMem.tload (TMem.load_store_neq Hst8 Hq).
      have E76 : TMem.tload m7 q = TMem.tload m6 q
        by rewrite /TMem.tload (TMem.load_store_neq Hst7 (Hne8 q HD _)).
      have E54 : TMem.tload m5 q = TMem.tload m4 q
        by rewrite /TMem.tload (TMem.load_store_neq Hst2 (Hne8 q HD _)).
      have E43 : TMem.tload m4 q = TMem.tload m3 q
        by rewrite /TMem.tload (TMem.load_store_neq Hst1 (Hne8 q HD _)).
      have E21 : TMem.tload m2 q = TMem.tload m1 q
        by rewrite /TMem.tload (TMem.load_store_neq Hst0 (Hne8 q HD _)).
      have E10 : TMem.tload m1 q = TMem.tload m q
        by rewrite /TMem.tload (Hpres q HD).
      by rewrite E87 E76 Ht6 E54 E43 Ht3 E21 E10.
    + by rewrite /pc19 /pc16 /pc14 /pc12 /pc10 /pc8 /pc6 /pc4
                 !Pointer.inc_preserves_component.
    + exact: (TMacros.code_at_I_tail Hc20).
    + split.
      * by rewrite /rs13 TInv.get_set_neq // /rs12 TInv.get_set_neq //
                   /rs11 TInv.get_set_neq // Hoth10 //; exact: HONE9.
      * by rewrite /rs13 TInv.get_set_neq // /rs12 TInv.get_set_neq //
                   /rs11 TInv.get_set_neq // HSP10 E4z.
      * by rewrite /rs13 TInv.get_set_neq // /rs12 TInv.get_set_neq //
                   /rs11 TInv.get_set_eq.
  - split; first exact: Htag13.
    + by rewrite /TMem.vload (TMem.load_store_eq Hst8) /= EA212.
    + by rewrite /TMem.tload (TMem.load_store_eq Hst8) /= EA212.
Qed.

(** ★ The whole callee prologue
 — the T counterpart of
    `S2I/Simulation.v:2698`'s [internal_prologue_run].

    Nine steps: [ILabel], [IMov], [IConst], [IAlloc], two pushes (2 steps
    each), and the [IMov R_COM R_ARG] that installs the argument. The first
    four are [prologue_alloc_run]; the rest are two [push_data_macro]s and one
    [TS.Mov].

    Two things are stated here that `Simulation.v` cannot state, and they are
    the reason this file exists:

    - [R_RA] comes out UNTOUCHED, still carrying the activation's return
      capability with its tag. At the I level [R_RA] is [Undef] throughout, so
      there is nothing to say; at T this is what [ei_ra] needs.
    - [tag_inv] comes out over the SAME ledger [L]. The prologue moves no
      capability: both pushes are data pushes. That is why the whole thing
      costs two [push_data_macro] calls and no ledger arithmetic.

    The memory is reported both abstractly (the two slots, and loads outside
    the frame preserved) and via [frame_cap], which is what the body's
    [ei_cap] budget consumes. Loads-outside-preserved is the form the caller's
    [scrs_ok] / [stack_match] / [frame_temps] all transfer along, since every
    clause of each is a [vload] or [tload] — i.e. a projection of a raw
    load. *)
Lemma prologue_run Cf plf ne nxtB restB a mem tmemIn regsIn pct pc0 L :
  TMacros.code_at_I cde Cf pc0
    ([:: ILabel plf; IMov R_SP R_AUX1;
         IConst (IInt (Z.of_nat (4 + ne))) R_SP; IAlloc R_SP R_SP]
     ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
     ++ nxtB :: restB) ->
  Pointer.component pc0 = Cf ->
  Transitional.Register.get R_ONE regsIn = MVal Other (Int 1) ->
  (exists cm, getm tmemIn Cf = Some cm) ->
  TInject.minj a mem tmemIn ->
  TInv.tag_inv L tmemIn regsIn pct ->
  exists tmemOut regsOut fbN pcF,
    [/\ star TS.step cde (tmemIn, regsIn, pc0, pct) E0
             (tmemOut, regsOut, pcF, pct),
        [/\ (forall (o : Z) w,
               Transitional.Memory.load tmemIn (Cf, fbN, o) = Some w -> False),
            (forall b0, a Cf b0 <> Some fbN),
            TInject.minj a mem tmemOut,
            TStack.frame_cap tmemOut Cf fbN (4 + ne)
          & forall q, Pointer.component q <> Cf \/ Pointer.block q <> fbN ->
              Transitional.Memory.load tmemOut q
              = Transitional.Memory.load tmemIn q],
        (* the two linkage slots: the caller's [R_SP] and the argument.
           Reported with their TAGS, because the epilogue's pops need
           [tvtag = Other] to be data pops. *)
        [/\ Transitional.Memory.load tmemOut (Cf, fbN, 0%Z)
              = Some (MVal Other (Transitional.val
                        (Transitional.Register.get R_SP regsIn)),
                      {| vtag := Other; color := Cf; entry := None;
                         is_code := false |})
          & Transitional.Memory.load tmemOut (Cf, fbN, 1%Z)
              = Some (Transitional.Register.get R_ARG regsIn,
                      {| vtag := Other; color := Cf; entry := None;
                         is_code := false |})],
        [/\ Transitional.Register.get R_ONE regsOut = MVal Other (Int 1),
            Transitional.Register.get R_SP regsOut
              = MVal Other (Ptr (Cf, fbN, (0 + 1 + 1)%Z)),
            Transitional.val (Transitional.Register.get R_ARG regsOut)
              = Transitional.val (Transitional.Register.get R_COM regsIn),
            Transitional.val (Transitional.Register.get R_COM regsOut)
              = Transitional.val (Transitional.Register.get R_COM regsIn)
          & Transitional.Register.get R_RA regsOut
              = Transitional.Register.get R_RA regsIn]
      & [/\ TInv.tag_inv L tmemOut regsOut pct,
             Pointer.component pcF = Cf
           & TMacros.code_at_I cde Cf pcF (nxtB :: restB)]].
Proof.
  move=> Hcode Hcomp HONE HcmF HI Htag.
  (* --- the first four steps --- *)
  have Hc0L : TMacros.code_at_I cde Cf pc0
    (ILabel plf
     :: ([:: IMov R_SP R_AUX1;
             IConst (IInt (Z.of_nat (4 + ne))) R_SP; IAlloc R_SP R_SP]
         ++ IStore R_SP R_AUX1
            :: (IBinOp Add R_SP R_ONE R_SP :: push R_ARG
                ++ [:: IMov R_COM R_ARG] ++ nxtB :: restB))) by exact: Hcode.
  have SL : TS.step cde (tmemIn, regsIn, pc0, pct) E0
            (tmemIn, regsIn, Pointer.inc pc0, pct)
    by eapply TS.Label; [exact: (TMacros.code_at_I_head Hc0L)
                        | exact: (TMacros.check_pc_at_I Hc0L)].
  have Hcode4 := TMacros.code_at_I_tail Hc0L.
  have Hcomp0 : Pointer.component (Pointer.inc pc0) = Cf
    by rewrite Pointer.inc_preserves_component.
  case: (prologue_alloc_run Hcode4 Hcomp0
           (TInv.ti_regs Htag (r := R_SP) (ltac:(by []))) HcmF HI Htag)
    => [tmem1 [regs3 [fbN [Sal [Hfresh Havoid [Hnosite Hpres] Hmj1 Hcap1]
                              [HSP3 HA13 Hoth3] Htag3]]]].
  (* --- where the remaining five instructions sit --- *)
  set pc4 := Pointer.inc (Pointer.inc (Pointer.inc (Pointer.inc pc0))).
  have Hcomp4 : Pointer.component pc4 = Cf
    by rewrite /pc4 !Pointer.inc_preserves_component.
  have Hc4 : TMacros.code_at_I cde Cf pc4
    (push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG] ++ nxtB :: restB).
  { apply: TMacros.code_at_I_tail. apply: TMacros.code_at_I_tail.
    apply: TMacros.code_at_I_tail. apply: TMacros.code_at_I_tail.
    exact: Hcode. }
  (* --- push R_AUX1: the caller's R_SP into slot 0 --- *)
  have HONE3 : Transitional.Register.get R_ONE regs3 = MVal Other (Int 1)
    by rewrite Hoth3.
  have Hsp0 : (0 <= 0 < Z.of_nat (4 + ne))%Z by split; lia.
  have Htl4 : push R_ARG ++ [:: IMov R_COM R_ARG] ++ nxtB :: restB <> [::]
    by [].
  case: (push_data_run Hc4 Htl4 Hcomp4
           (ltac:(by []) : R_AUX1 <> R_RA)
           (ltac:(by []) : R_SP <> R_AUX1)
           (ltac:(by []) : R_ONE <> R_AUX1)
           HSP3 HONE3 Hsp0 Hcap1 (Hnosite 0%Z) Havoid Hmj1 Htag3)
    => [tmem2 [regs4 [Sp0 [Hsl0 Hpres0 Hst0 Hcap2 Hmj2]
                          [HSP4 HA14 Hoth4] Htag4]]].
  (* --- push R_ARG: the argument into slot 1 --- *)
  set pc6 := Pointer.inc (Pointer.inc pc4).
  have Hcomp6 : Pointer.component pc6 = Cf
    by rewrite /pc6 !Pointer.inc_preserves_component.
  have Hc6 : TMacros.code_at_I cde Cf pc6
    (push R_ARG ++ [:: IMov R_COM R_ARG] ++ nxtB :: restB).
  { apply: TMacros.code_at_I_tail. apply: TMacros.code_at_I_tail.
    exact: Hc4. }
  have HONE4 : Transitional.Register.get R_ONE regs4 = MVal Other (Int 1)
    by rewrite Hoth4.
  have Hsp1 : (0 <= 0 + 1 < Z.of_nat (4 + ne))%Z by split; lia.
  have Htl6 : [:: IMov R_COM R_ARG] ++ nxtB :: restB <> [::] by [].
  case: (push_data_run Hc6 Htl6 Hcomp6
           (ltac:(by []) : R_ARG <> R_RA)
           (ltac:(by []) : R_SP <> R_ARG)
           (ltac:(by []) : R_ONE <> R_ARG)
           HSP4 HONE4 Hsp1 Hcap2 (Hnosite (0 + 1)%Z) Havoid Hmj2 Htag4)
    => [tmem3 [regs5 [Sp1 [Hsl1 Hpres1 Hst1 Hcap3 Hmj3]
                          [HSP5 HARG5 Hoth5] Htag5]]].
  (* --- IMov R_COM R_ARG: install the argument --- *)
  set pc8 := Pointer.inc (Pointer.inc pc6).
  have Hc8 : TMacros.code_at_I cde Cf pc8
    ([:: IMov R_COM R_ARG] ++ nxtB :: restB).
  { apply: TMacros.code_at_I_tail. apply: TMacros.code_at_I_tail.
    exact: Hc6. }
  have HCOMt : tvtag (Transitional.Register.get R_COM regs5) = Other.
  { apply: (TInv.ti_regs Htag5). by []. }
  (* [R_COM] is unmoved by everything before the [IMov] *)
  have HCOM5 : Transitional.Register.get R_COM regs5
             = Transitional.Register.get R_COM regsIn
    by rewrite Hoth5 // Hoth4 // Hoth3.
  exists tmem3,
    (Transitional.Register.set R_COM
       (Transitional.val (Transitional.Register.get R_COM regs5))
       (if is_address (tvtag (Transitional.Register.get R_COM regs5))
        then Invalidated else Other)
       (Transitional.Register.set R_ARG
          (Transitional.val (Transitional.Register.get R_COM regs5))
          (tvtag (Transitional.Register.get R_COM regs5)) regs5)),
    fbN, (Pointer.inc pc8).
  split.
  - (* --- the nine steps --- *)
    eapply star_step with (t1 := E0) (t2 := E0); [exact: SL | | by []].
    eapply star_trans with (t1 := E0) (t2 := E0); [exact: Sal | | by []].
    eapply star_trans with (t1 := E0) (t2 := E0);
      [exact: (plus_star Sp0) | | by []].
    eapply star_trans with (t1 := E0) (t2 := E0);
      [exact: (plus_star Sp1) | | by []].
    apply: star_one.
    eapply TS.Mov; [exact: (TMacros.code_at_I_head Hc8)
                   | exact: (TMacros.check_pc_at_I Hc8)].
  - (* --- the memory facts --- *)
    split=> //.
    move=> q Hne.
    have Hne0 : q <> ((Cf, fbN, 0%Z) : Pointer.t)
      by move=> E; case: Hne => [H|H]; apply: H; rewrite E.
    have Hne1 : q <> ((Cf, fbN, (0 + 1)%Z) : Pointer.t)
      by move=> E; case: Hne => [H|H]; apply: H; rewrite E.
    rewrite (TMem.load_store_neq Hst1 Hne1) (TMem.load_store_neq Hst0 Hne0).
    exact: (Hpres q Hne).
  - (* --- the two linkage slots --- *)
    split.
    + have Hne01 : (Cf, fbN, 0%Z) <> (Cf, fbN, (0 + 1)%Z)
        by move=> E; move: (f_equal Pointer.offset E) => /=; lia.
      apply: (Hpres1 _ _ _ Hne01).
      by move: Hsl0; rewrite HA13.
    + have -> : (1 = 0 + 1)%Z by [].
      by move: Hsl1; rewrite Hoth4 // Hoth3.
  - (* --- the registers --- *)
    split.
    + by rewrite TInv.get_set_neq // TInv.get_set_neq // Hoth5 // Hoth4.
    + by rewrite TInv.get_set_neq // TInv.get_set_neq //.
    + by rewrite TInv.get_set_neq // TInv.get_set_eq /= HCOM5.
    + by rewrite TInv.get_set_eq /= HCOM5.
    + by rewrite TInv.get_set_neq // TInv.get_set_neq // Hoth5 // Hoth4 // Hoth3.
  - (* --- tag_inv, and where the pc landed --- *)
    split.
    + rewrite HCOMt /=. apply: TInv.tag_inv_setreg; first by [].
      apply: TInv.tag_inv_setreg; first by [].
      exact: Htag5.
    + by rewrite /pc8 /pc6 /pc4 !Pointer.inc_preserves_component.
    + exact: (TMacros.code_at_I_tail Hc8).
Qed.

End WithCode.

End TProlog.
