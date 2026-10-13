(** * Stage 4, part 3 — the memory injection at T.

    See plan-i2t-redo.md §4 (Stage 4).

    ⚠ **A structural finding that changes the join's cost.**

    The obvious route was to erase a `Transitional.Memory.t` into a
    `Common.Memory.t` and reuse `S2I/SimInject.v`'s `mem_inject` verbatim.
    That does not work: `Common/Memory.v` declares

        Module ComponentMemory : AbstractComponentMemory.

    i.e. it is SEALED, so its representation is opaque and no erasure function
    into it can be written. `Transitional.Memory` by contrast is transparent
    (its sealing is commented out). The two memory types are genuinely
    different, and `mem_inject`'s ten fields split:

      - `mi_ok`, `mi_domm`, `mi_wf_s`, `mi_local_s`, `mi_dom` — SOURCE side,
        port unchanged;
      - `mi_wf_t`, `mi_local_t`, `mi_rng` — stated over `ComponentMemory.wf` /
        `ComponentMemory.domm`, so they need T-side analogues;
      - `mi_load` — the workhorse, and the one this file settles.

    So the join is not "compose with an erasure"; it is re-proving SimInject's
    theory (554 lines) for T memory. This file does the load half, which is
    what the diagrams actually consume, and leaves the allocation-side fields
    explicitly for later rather than pretending they are free.

    The payoff is that the load half really is free: T's load-write-back —
    Stage 0b's discovery, the thing that looked like it would cost a per-pop
    framing obligation — **preserves the injection by one application of
    `TMem.vload_store_same`.** *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Intermediate.Machine.
Require Import S2I.SimInject.
Require Import Lib.Extra.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.
Require Import S2T.TMem.
Require Import S2T.TInv.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Require Import Coq.ZArith.ZArith.

Set Implicit Arguments.
Unset Strict Implicit.

Module TInject.

(* ================================================================== *)
(* T-side [wf] and [domm]                                             *)
(* ================================================================== *)

(** Mirrors of `Common/Memory.v`'s `ComponentMemory.domm` / `.wf`
    (`Definition wf m := forall b, b \in domm m -> b < nextblock m`). They have
    to be restated rather than reused because `ComponentMemory` is sealed —
    but T's memory is transparent, so the mirrors are direct. *)
Definition cdomm (cm : Transitional.Memory.mem) : {fset Block.id} :=
  domm (Transitional.Memory.content cm).

Definition cwf (cm : Transitional.Memory.mem) : Prop :=
  forall b, b \in cdomm cm -> b < Transitional.Memory.nextblock cm.

(** A component-level store touches neither the domain nor [nextblock]: it
    overwrites a block that was already present. *)
Lemma store_b_shape cm b i v cm' :
  Transitional.Memory.store_b cm b i v = Some cm' ->
  cdomm cm' = cdomm cm
  /\ Transitional.Memory.nextblock cm' = Transitional.Memory.nextblock cm.
Proof.
  rewrite /Transitional.Memory.store_b /cdomm.
  case E: (getm (Transitional.Memory.content cm) b) => [chunk|] //.
  case: (0 <=? i)%Z => //.
  case: (list_upd chunk _ v) => [chunk'|] // [<-] /=.
  by split; last by []; exact: domm_setm_existing E.
Qed.

Lemma store_b_cwf cm b i v cm' :
  cwf cm -> Transitional.Memory.store_b cm b i v = Some cm' -> cwf cm'.
Proof.
  move=> H Hst b0. case: (store_b_shape Hst) => [Ed En].
  by rewrite Ed En; exact: H.
Qed.

(** …and the same, lifted to a whole memory. *)
Lemma store_shape mt p c mt' :
  Transitional.Memory.store mt p c = Some mt' ->
  forall C cm', getm mt' C = Some cm' ->
    exists cm, [/\ getm mt C = Some cm, cdomm cm' = cdomm cm
              & Transitional.Memory.nextblock cm'
                = Transitional.Memory.nextblock cm].
Proof.
  rewrite /Transitional.Memory.store.
  case Em: (mt (Pointer.component p)) => [cm|] //=.
  case Eb: (Transitional.Memory.store_b cm _ _ c) => [cm0|] //= [<-] C cm'.
  rewrite setmE. case: (C =P Pointer.component p) => [->|Hne].
  - move=> [<-]. exists cm. split=> //; by case: (store_b_shape Eb).
  - move=> HC. by exists cm'.
Qed.

(** …and forward: a store never REMOVES a component. *)
Lemma store_domm_fwd mt p c mt' C cm :
  Transitional.Memory.store mt p c = Some mt' ->
  getm mt C = Some cm -> exists cm', getm mt' C = Some cm'.
Proof.
  rewrite /Transitional.Memory.store.
  case Em: (mt (Pointer.component p)) => [cmp|] //=.
  case Eb: (Transitional.Memory.store_b cmp _ _ c) => [cmp'|] //= [<-] HC.
  rewrite setmE. case: (C == Pointer.component p); first by exists cmp'.
  by exists cm.
Qed.

(* ================================================================== *)
(* Allocation                                                         *)
(* ================================================================== *)

Lemma alloc_shape mt C n mt' p :
  Transitional.Memory.alloc mt C n = Some (mt', p) ->
  exists cm, [/\ getm mt C = Some cm,
                 p = (C, Transitional.Memory.nextblock cm, 0%Z)
               & mt' = setm mt C
                   (Transitional.Memory.alloc_bis C cm n).1].
Proof.
  rewrite /Transitional.Memory.alloc.
  case Em: (mt C) => [cm|] //= [<- <-]. by exists cm.
Qed.

Lemma alloc_b_cdomm_in C cm n b :
  (b \in cdomm (Transitional.Memory.alloc_bis C cm n).1)
  = (b == Transitional.Memory.nextblock cm) || (b \in cdomm cm).
Proof. by rewrite /cdomm /= domm_set in_fsetU1. Qed.

Lemma alloc_b_nextblock C cm n :
  Transitional.Memory.nextblock (Transitional.Memory.alloc_bis C cm n).1
  = (1 + Transitional.Memory.nextblock cm)%nat.
Proof. by []. Qed.

(** The freshly allocated block was NOT in the old domain — the [cwf]
    invariant is exactly what says so. *)
Lemma alloc_fresh_notin cm :
  cwf cm -> Transitional.Memory.nextblock cm \notin cdomm cm.
Proof. move=> H. apply/negP => Hin. by move: (H _ Hin); rewrite ltnn. Qed.

Lemma alloc_b_cwf C cm n :
  cwf cm -> cwf (Transitional.Memory.alloc_bis C cm n).1.
Proof.
  move=> H b. rewrite alloc_b_cdomm_in alloc_b_nextblock.
  case/orP => [/eqP ->|Hin]; first by rewrite add1n.
  by rewrite add1n ltnS ltnW //; exact: H.
Qed.

(** Loads away from the fresh block are untouched. *)
Lemma vload_alloc_other mt C n mt' p q :
  Transitional.Memory.alloc mt C n = Some (mt', p) ->
  (Pointer.component q <> C \/ Pointer.block q <> Pointer.block p) ->
  TMem.vload mt' q = TMem.vload mt q.
Proof.
  move=> Ha Hne. case: (alloc_shape Ha) => [cm [Hcm Ep Emt]].
  rewrite /TMem.vload /Transitional.Memory.load Emt setmE.
  case EC: (Pointer.component q == C); last by [].
  move/eqP: EC => EC. rewrite EC Hcm /=.
  rewrite /Transitional.Memory.load_b /= setmE.
  have -> : (Pointer.block q == Transitional.Memory.nextblock cm) = false.
  { apply/negP => /eqP Eb. case: Hne => [H|H]; first by apply: H.
    by apply: H; rewrite Eb Ep. }
  by [].
Qed.

(** The load half of the injection, from a SOURCE memory to a T memory.

    Note the asymmetry that the sealing forces: the source side is
    `Common.Memory.load`, the target side is `TMem.vload` — the value view of
    T memory, which is exactly the projection Stage 2 part 1 introduced so that
    tag traffic would be invisible here. *)
Record minj (a : renaming) (ms : Common.Memory.Memory.t)
            (mt : Transitional.Memory.t) : Prop := MInj {
  mj_ok : inj_ok a;
  mj_load : forall C b b' i, a C b = Some b' ->
      option_rel (val_inject a)
                 (Common.Memory.Memory.load ms (C, b, i))
                 (TMem.vload mt (C, b', i));
  (* the three fields that [mem_inject] states over [ComponentMemory.wf] /
     [.domm], here over their T-side mirrors *)
  mj_wf_t : forall C cm, getm mt C = Some cm -> cwf cm;
  mj_local_t : forall C cm, getm mt C = Some cm ->
      Block.local \in cdomm cm;
  mj_rng : forall C b b', a C b = Some b' -> b != Block.local ->
      exists cm, getm mt C = Some cm /\ b' \in cdomm cm;

  (* the SOURCE side's well-formedness and domain — [mem_inject]'s [mi_wf_s] and
     [mi_dom]. Dropped from the first cut of this record because no diagram
     needed them; the LOCK-STEP allocation does (freshness of the new source
     block is exactly [ComponentMemory.alloc_fresh] against [mj_wf_s], and
     [a C bs = None] is [mj_dom] contrapositive). *)
  mj_wf_s : forall C cm, getm ms C = Some cm -> ComponentMemory.wf cm;
  mj_local_s : forall C cm, getm ms C = Some cm ->
      Block.local \in ComponentMemory.domm cm;
  mj_dom : forall C b b', a C b = Some b' -> b != Block.local ->
      exists cm, getm ms C = Some cm /\ b \in ComponentMemory.domm cm;

  (* the T memory has every component the source has — needed so that the
     LOCK-STEP allocation can be performed on the target side at all *)
  mj_domm : forall C cm, getm ms C = Some cm ->
      exists cm', getm mt C = Some cm';

  (* ★ every cell in the injection's RANGE is [Other]-tagged.

     Forced by the machine, like [frame_temps]' tag clause: `TS.Load` copies the
     CELL's tag into the target register, and `E_deref` loads through the
     α-image of a source pointer straight into [R_COM] — which [ti_regs] requires
     to be [Other]. A heap cell holding an [Invalidated] husk would make every
     dereference stuck.

     True because source-visible cells are only ever written by `IStore` of a
     data register (tag [Other] by [ti_regs]), by `IAlloc` (fresh cells are
     [tUndef]), or by the initial buffer setup. *)
  mj_data : forall C b b' i w, a C b = Some b' ->
      Transitional.Memory.load mt (C, b', i) = Some w -> tvtag w.1 = Other
}.

(** The three shape fields transfer across any store, since a store changes
    neither domain nor [nextblock]. Factored out so the three preservation
    lemmas below share it. *)
(** The T counterpart of `SimInject.v:229`'s `load_inject`: a source load has a
    matching target load through the injection. Together with [mj_data] — which
    says that target cell is [Other]-tagged — this is everything `E_deref`
    needs. *)
Lemma minj_load a ms mt C b b' i v :
  minj a ms mt -> a C b = Some b' ->
  Common.Memory.Memory.load ms (C, b, i) = Some v ->
  exists tv, TMem.vload mt (C, b', i) = Some tv /\ val_inject a v tv.
Proof.
  move=> HI Hab Hl. move: (mj_load HI i Hab). rewrite Hl.
  case: (TMem.vload mt (C, b', i)) => [tv|] //= HR. by exists tv.
Qed.

Lemma minj_shape_store a ms mt p c mt' :
  Transitional.Memory.store mt p c = Some mt' ->
  minj a ms mt ->
  [/\ forall C cm, getm mt' C = Some cm -> cwf cm,
      forall C cm, getm mt' C = Some cm -> Block.local \in cdomm cm
    & forall C b b', a C b = Some b' -> b != Block.local ->
      exists cm, getm mt' C = Some cm /\ b' \in cdomm cm].
Proof.
  move=> Hst [_ _ Hwf Hloc Hrng]. split.
  - move=> C cm HC. case: (store_shape Hst HC) => [cm0 [H0 Ed En]].
    move=> b0. rewrite Ed En. exact: (Hwf C cm0 H0).
  - move=> C cm HC. case: (store_shape Hst HC) => [cm0 [H0 Ed _]].
    rewrite Ed. exact: (Hloc C cm0 H0).
  - move=> C b b' Hab Hb. case: (Hrng C b b' Hab Hb) => [cm0 [H0 Hin]].
    (* the stored component still has [cm0]'s domain *)
    have [cm1 HC] : exists cm1, getm mt' C = Some cm1.
    { move: Hst. rewrite /Transitional.Memory.store.
      case Em: (mt (Pointer.component p)) => [cmp|] //=.
      case Eb: (Transitional.Memory.store_b cmp _ _ c) => [cmp'|] //= [<-].
      rewrite setmE.
      case: (C == Pointer.component p); first by exists cmp'.
      by exists cm0. }
    exists cm1. split=> //.
    case: (store_shape Hst HC) => [cm2 [H2 Ed _]].
    by rewrite Ed; move: H2; rewrite H0 => -[<-].
Qed.

(** ★ A value-preserving store on the T side preserves the injection.

    This is what makes T's load-write-back free at the injection level, the
    same way `TMem.vload_store_same` made it free at the `tag_inv` level. *)
Lemma minj_store_same a ms mt p c c' mt' :
  Transitional.Memory.load mt p = Some c ->
  Transitional.val c'.1 = Transitional.val c.1 ->
  tvtag c'.1 = tvtag c.1 ->
  Transitional.Memory.store mt p c' = Some mt' ->
  minj a ms mt -> minj a ms mt'.
Proof.
  move=> Hld Ev Et Hst HI. case: (minj_shape_store Hst HI) => [Hwf Hloc Hrng].
  case: HI => [Hok Hload _ _ _ Hwfs Hlocs Hdoms Hdomm Hdata]. split=> //.
  - move=> C b b' i Hab.
    by rewrite (TMem.vload_store_same Hld Ev Hst); exact: Hload.
  - move=> C cm HC. case: (Hdomm C cm HC) => [cm' HC'].
    exact: (store_domm_fwd Hst HC').
  - (* the tag clause: the store rewrites the cell's tag to the SAME tag *)
    move=> C b b' i w Hab.
    case: (@eqP _ ((C, b', i) : Pointer.t) p) => [Ep|Hne].
    + have Hld' : Transitional.Memory.load mt (C, b', i) = Some c
        by rewrite Ep.
      rewrite Ep (TMem.load_store_eq Hst) => -[<-].
      by rewrite Et; exact: (Hdata C b b' i c Hab Hld').
    + rewrite (TMem.load_store_neq Hst Hne). exact: Hdata Hab.
Qed.

(** The pop-shaped corollary: every `TrLoad` — hence every `pop` — leaves the
    injection alone. The premise is exactly the write-back the `TS.Load` rule
    performs. *)
Corollary minj_pop a ms mt p v mt' :
  Transitional.Memory.load mt p = Some v ->
  tvtag v.1 = Other ->
  Transitional.Memory.store mt p
    ({| Transitional.val := Transitional.val v.1;
        tvtag := moved_tag (tvtag v.1) |},
     {| vtag := moved_tag (tvtag v.1);
        color := Pointer.component p; entry := None; is_code := false |})
    = Some mt' ->
  minj a ms mt -> minj a ms mt'.
Proof.
  move=> Hld Et Hst HI.
  apply: (minj_store_same Hld _ _ Hst HI); [by [] | by rewrite /= Et].
Qed.

(** A store OUTSIDE the injection's range — the compiler's own frame and
    scratch traffic — also preserves it. This is `store_outside_inject`'s T
    counterpart, and it is what `frame_priv` / `scratch_priv` will feed:
    those say precisely that the frame and hidden blocks are not in the range
    of [a]. *)
(** Only the store's OWN component has to avoid the touched block: the
    injection's image of a component sits in that component. (The prologue can
    only supply the fact for [Cf], which is why this is stated this way.) *)
Lemma minj_store_outside a ms mt p c mt' :
  (forall b, a (Pointer.component p) b <> Some (Pointer.block p)) ->
  Transitional.Memory.store mt p c = Some mt' ->
  minj a ms mt -> minj a ms mt'.
Proof.
  move=> Hout Hst HI. case: (minj_shape_store Hst HI) => [Hwf Hloc Hrng].
  case: HI => [Hok Hload _ _ _ Hwfs Hlocs Hdoms Hdomm Hdata].
  have Hne : forall C b b' (i : Z), a C b = Some b' -> (C, b', i) <> p.
  { move=> C b b' i Hab.
    case: p Hout Hst => [[pc pb] po] /= Hout _ [Ec Eb Ei].
    by move: (Hout b); rewrite -Ec Hab Eb. }
  split=> //.
  - move=> C b b' i Hab.
    by rewrite /TMem.vload (TMem.load_store_neq Hst (Hne _ _ _ _ Hab));
       exact: Hload.
  - move=> C cm HC. case: (Hdomm C cm HC) => [cm' HC'].
    exact: (store_domm_fwd Hst HC').
  - move=> C b b' i w Hab.
    rewrite (TMem.load_store_neq Hst (Hne _ _ _ _ Hab)). exact: Hdata Hab.
Qed.

(** ★ The T counterpart of `SimInject.v:254`'s `store_inject`: a source store has
    a matching target store, and the injection survives. Unlike the source
    version this does not dissect the two memories — the source side is sealed —
    it goes through the load/store laws on each side, with `inj_injective`
    settling the one interesting case (a DIFFERENT source block mapping to the
    block just written).

    The stored tvalue is [Other]-tagged, which is what re-establishes
    [mj_data]: an assignment writes a data register, so the cell stays data. *)
Lemma minj_store a ms mt C b b' i v tv ms' :
  minj a ms mt -> a C b = Some b' -> val_inject a v tv ->
  Common.Memory.Memory.store ms (C, b, i) v = Some ms' ->
  exists mt',
    Transitional.Memory.store mt (C, b', i)
      (MVal Other tv, {| vtag := Other; color := C; entry := None;
                         is_code := false |}) = Some mt'
    /\ minj a ms' mt'.
Proof.
  move=> HI Hab Hv Hs.
  have [w Hlw] := store_some_load_some Hs.
  case: (minj_load HI Hab Hlw) => [tw [Hvt _]].
  have [wt Hlt] := TMem.vload_load Hvt.
  case: (TMem.store_after_load
           (MVal Other tv, {| vtag := Other; color := C; entry := None;
                              is_code := false |}) Hlt) => [mt' Hst].
  exists mt'. split; first exact: Hst.
  case: (minj_shape_store Hst HI) => [Hwf Hloc Hrng].
  case: (HI) => [Hok Hload _ _ _ Hwfs Hlocs Hdoms Hdomm Hdata].
  (* dissect the SOURCE store once: [Memory] is transparent even though
     [ComponentMemory] is sealed *)
  have [cmc [cmc' [Ems [Ecm Ems']]]] :
    exists cmc cmc', [/\ getm ms C = Some cmc,
                        ComponentMemory.store cmc b i v = Some cmc'
                      & ms' = setm ms C cmc'].
  { move: Hs. rewrite /Common.Memory.Memory.store /=.
    case E1: (getm ms C) => [cmc|] //=.
    case E2: (ComponentMemory.store cmc b i v) => [cmc'|] //= [<-].
    by exists cmc, cmc'. }
  split=> //.
  - (* the load clause *)
    move=> C0 b0 b0' i0 Hab0.
    case: (@eqP _ ((C0, b0', i0) : Pointer.t) ((C, b', i) : Pointer.t))
      => [E|Hne].
    + (* same TARGET cell — so the same source cell, by injectivity *)
      move: E => [EC Eb Ei].
      have Hab0' : a C b0 = Some b' by rewrite -EC -Eb.
      have Eb0 : b0 = b by exact: (inj_injective _ Hok C b0 b b' Hab0' Hab).
      rewrite EC Eb Ei Eb0 /TMem.vload (TMem.load_store_eq Hst) /=
              (Common.Memory.Memory.load_after_store_eq _ _ _ _ Hs).
      exact: Hv.
    + (* a different target cell; the source cell may still be the stored one *)
      have Hnes : ((C0, b0, i0) : Pointer.t) <> (C, b, i).
      { move=> Ep. apply: Hne.
        have EC : C0 = C by exact: (f_equal Pointer.component Ep).
        have Eb : b0 = b by exact: (f_equal Pointer.block Ep).
        have Ei : i0 = i by exact: (f_equal Pointer.offset Ep).
        have Eb0' : b0' = b' by congruence.
        congruence. }
      rewrite /TMem.vload (TMem.load_store_neq Hst Hne)
              (Common.Memory.Memory.load_after_store_neq _ _ _ _ _ (nesym Hnes) Hs).
      exact: Hload Hab0.
  - (* source well-formedness: a store preserves it *)
    move=> C0 cm0. rewrite Ems' setmE. case: (C0 =P C) => [_|_]; last exact: Hwfs.
    move=> [<-]. exact: (ComponentMemory.wf_store _ _ _ _ _ (Hwfs _ _ Ems) Ecm).
  - (* the source's local block is still there *)
    move=> C0 cm0. rewrite Ems' setmE. case: (C0 =P C) => [EC|_];
      last exact: Hlocs.
    move=> [<-]. rewrite (ComponentMemory.domm_store _ _ _ _ _ Ecm).
    exact: (Hlocs _ _ Ems).
  - (* the source domain: a store does not change it *)
    move=> C0 b0 b0' Hab0 Hb0. case: (Hdoms _ _ _ Hab0 Hb0) => [cm0 [Hcm0 Hin]].
    rewrite Ems' setmE. case: (C0 =P C) => [EC|_]; last by exists cm0.
    exists cmc'. split; first by [].
    rewrite (ComponentMemory.domm_store _ _ _ _ _ Ecm).
    by move: Hcm0; rewrite EC Ems => -[->].
  - (* the target keeps every component the source has *)
    move=> C0 cm0. rewrite Ems' setmE.
    have Hfwd : forall cm1, getm ms C0 = Some cm1 ->
        exists cm2, getm mt' C0 = Some cm2.
    { move=> cm1 HC1. case: (Hdomm C0 cm1 HC1) => [cm2 HC2].
      exact: (store_domm_fwd Hst HC2). }
    case: (C0 =P C) => [EC|_]; last exact: Hfwd.
    move=> _. apply: (Hfwd cmc). by rewrite EC.
  - (* the tag clause: what was written is [Other] *)
    move=> C0 b0 b0' i0 w0 Hab0.
    case: (@eqP _ ((C0, b0', i0) : Pointer.t) ((C, b', i) : Pointer.t))
      => [E|Hne].
    + by rewrite E (TMem.load_store_eq Hst) => -[<-].
    + rewrite (TMem.load_store_neq Hst Hne). exact: Hdata Hab0.
Qed.

(** ★ Allocation yields FRAME PRIVACY. The block just allocated is outside the
    injection's range, because the range lives in the old domain and the fresh
    block does not.

    This is `frame_priv`'s content — "no source block maps to this frame" —
    and it is the fact the old pass's `fb` / `mem_fb` layer existed to
    establish and was PROVED UNSATISFIABLE trying to
    (`mem_fb_park_refutation`). Here it falls out of `cwf` and `mj_rng` in four
    lines. *)
Lemma alloc_fresh_outside a ms mt C n mt' b :
  minj a ms mt ->
  Transitional.Memory.alloc mt C n = Some (mt', (C, b, 0%Z)) ->
  forall b0, a C b0 <> Some b.
Proof.
  move=> HI Ha b0 Hab.
  case: (alloc_shape Ha) => [cm [Hcm Ep _]].
  have Eb : b = Transitional.Memory.nextblock cm
    by move: (f_equal Pointer.block Ep).
  have Hfresh := alloc_fresh_notin (mj_wf_t HI Hcm).
  (* the fresh block is outside the OLD domain; the range — and [Block.local]
     itself — are inside it *)
  case: (b0 =P Block.local) => [Eloc|Hb0].
  { move: Hab; rewrite Eloc (inj_local _ (mj_ok HI) C) => -[Eb'].
    by move: Hfresh; rewrite -Eb -Eb' (mj_local_t HI Hcm). }
  case: (mj_rng HI Hab _) => [|cm0 [Hcm0 Hin]]; first by apply/eqP.
  move: Hcm0; rewrite Hcm => -[Ecm]; rewrite -Ecm in Hin.
  by move: Hfresh; rewrite -Eb Hin.
Qed.


End TInject.
