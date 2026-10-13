(** * Stage 2, part 1 — retiring the pop-write-back risk.

    See plan-i2t-redo.md §4 (Stage 0b) for the risk this file exists to kill.

    Stage 0b found that T's [Load] rule WRITES BACK a retagged cell, so every
    POP perturbs memory where the I-level [exec_pop_plus] leaves it alone. The
    worry was that [frame_temps], [stack_match], [mem_inject] and every other
    memory-shaped conjunct would then need re-establishing after every pop —
    a per-pop framing obligation with no I-level counterpart, and pops are
    everywhere. That was the largest unquantified cost in the plan.

    **It costs one definition and one lemma.** The perturbation is tag-only: the
    stored value is exactly the loaded value. So if the memory conjuncts are
    phrased over the VALUE PROJECTION [vload] rather than over raw T memory,
    the write-back is invisible to them *by construction* — [vload_store_same]
    below, applied once, discharges all of them.

    This is a design constraint on Stage 2, not just a lemma: every memory
    conjunct of [tag_inv] / the ported [stack_match] must be stated via [vload]
    (or via [tload] for the few that genuinely care about tags, which are
    exactly the RA slots, T2). *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Intermediate.Machine.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.

Require Import Lib.Extra.
Require Import Lib.Monads.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Require Import Coq.ZArith.ZArith.
Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.

Module TMem.

Notation mem := Transitional.Memory.t.

(* ================================================================== *)
(* Load/store laws for T's memory                                     *)
(* ================================================================== *)

(** T's [Memory] module ships no reasoning lemmas at all (unlike
    [Common/Memory.v] for Intermediate's), so the two laws are proved here. *)

Lemma ptr_eq (p q : Pointer.t) :
  Pointer.component q = Pointer.component p ->
  Pointer.block q = Pointer.block p ->
  Pointer.offset q = Pointer.offset p ->
  q = p.
Proof. by case: q => [[qc qb] qo]; case: p => [[pc pb] po] /= -> -> ->. Qed.

Lemma load_store_eq m p c m' :
  Transitional.Memory.store m p c = Some m' ->
  Transitional.Memory.load m' p = Some c.
Proof.
  rewrite /Transitional.Memory.store.
  case Em: (m (Pointer.component p)) => [cm|] //=.
  rewrite /Transitional.Memory.store_b.
  case Eb: (getm (Transitional.Memory.content cm) (Pointer.block p))
    => [chunk|] //=.
  case Eo: (0 <=? Pointer.offset p)%Z => //.
  case Eu: (list_upd chunk (Z.to_nat (Pointer.offset p)) c) => [chunk'|] //=.
  move=> [<-].
  rewrite /Transitional.Memory.load setmE eqxx /=.
  rewrite /Transitional.Memory.load_b /= setmE eqxx Eo.
  exact: list_upd_nth_error_same Eu.
Qed.

Lemma load_store_neq m p c m' q :
  Transitional.Memory.store m p c = Some m' ->
  q <> p ->
  Transitional.Memory.load m' q = Transitional.Memory.load m q.
Proof.
  rewrite /Transitional.Memory.store.
  case Em: (m (Pointer.component p)) => [cm|] //=.
  rewrite /Transitional.Memory.store_b.
  case Eb: (getm (Transitional.Memory.content cm) (Pointer.block p))
    => [chunk|] //=.
  case Eo: (0 <=? Pointer.offset p)%Z => //.
  case Eu: (list_upd chunk (Z.to_nat (Pointer.offset p)) c) => [chunk'|] //=.
  move=> [<-] Hne.
  rewrite /Transitional.Memory.load setmE.
  case EC: (Pointer.component q == Pointer.component p); last by [].
  move/eqP: EC => EC.
  rewrite EC Em /= /Transitional.Memory.load_b /= setmE.
  case EB: (Pointer.block q == Pointer.block p); last by [].
  move/eqP: EB => EB.
  rewrite EB Eb.
  case EO: (0 <=? Pointer.offset q)%Z; last by [].
  apply: (list_upd_nth_error_other Eu).
  move=> Hoff. apply: Hne. apply: ptr_eq => //.
  apply: Z2Nat.inj.
  - by move/Z.leb_le: EO.
  - by move/Z.leb_le: Eo.
  - by rewrite Hoff.
Qed.

(** [list_upd] succeeds wherever [nth_error] does. `Lib/Extra.v` proves what
    [list_upd] DOES when it succeeds, but not that it succeeds. *)
Lemma list_upd_total {A : Type} (l : seq A) k (x y : A) :
  List.nth_error l k = Some x -> exists l', list_upd l k y = Some l'.
Proof.
  elim: l k => [|a l IH] [|k] //=; first by move=> _; exists (y :: l).
  move=> H. case: (IH k H) => [l' Hl']. by rewrite Hl'; exists (a :: l').
Qed.

(** ★ A loadable cell is storable — the T counterpart of
    `ComponentMemory.store_after_load`. Needed because the prologue's two
    pushes must be shown to SUCCEED on the freshly allocated frame; nothing
    before this had to produce a store rather than consume one. *)
Lemma store_after_load m p c v :
  Transitional.Memory.load m p = Some c ->
  exists m', Transitional.Memory.store m p v = Some m'.
Proof.
  rewrite /Transitional.Memory.load /Transitional.Memory.store.
  case Em: (m (Pointer.component p)) => [cm|] //=.
  rewrite /Transitional.Memory.load_b /Transitional.Memory.store_b.
  case Eb: (getm (Transitional.Memory.content cm) (Pointer.block p))
    => [chunk|] //=.
  case Eo: (0 <=? Pointer.offset p)%Z => // Hnth.
  case: (@list_upd_total _ chunk (Z.to_nat (Pointer.offset p)) c v Hnth)
    => [chunk' ->].
  by eexists.
Qed.

(* ================================================================== *)
(* The value projection                                               *)
(* ================================================================== *)

(** What the memory conjuncts should be phrased over. *)
Definition vload (m : mem) (p : Pointer.t) : option value :=
  omap (fun c => Transitional.val c.1) (Transitional.Memory.load m p).

(** The tag view, for the few conjuncts that genuinely care — the RA spill
    slots (invariant T2). *)
Definition tload (m : mem) (p : Pointer.t) : option value_tag :=
  omap (fun c => tvtag c.1) (Transitional.Memory.load m p).

(** ★ THE LEMMA. A store that preserves the cell's VALUE is invisible to
    [vload], everywhere. This is what makes T's load-write-back free. *)
(** Loadability is store-STABLE: a store never destroys a cell, whatever it
    writes. Needed by [frame_cap], whose clauses the prologue's pushes overwrite
    with new values — [vload_store_same] only covers value-PRESERVING stores. *)
Lemma vload_store_total m p c m' q v :
  Transitional.Memory.store m p c = Some m' ->
  vload m q = Some v -> exists v', vload m' q = Some v'.
Proof.
  move=> Hst. rewrite /vload.
  case: (p =P q) => [Ep|Hne].
  { rewrite -Ep (load_store_eq Hst) /= => _. by exists (Transitional.val c.1). }
  rewrite (load_store_neq Hst (nesym Hne)).
  by case: (Transitional.Memory.load m q) => [w|] //= _; exists (Transitional.val w.1).
Qed.

(** [vload] is defined by projection, so it witnesses the raw load — which is
    what [store_after_load] consumes. Used to turn [frame_cap] (a [vload] fact)
    into "the prologue's pushes succeed". *)
Lemma vload_load m p v :
  vload m p = Some v -> exists w, Transitional.Memory.load m p = Some w.
Proof.
  rewrite /vload. case: (Transitional.Memory.load m p) => [w|] //= _.
  by exists w.
Qed.

(** …and the same for the TAG projection, which the strengthened [frame_temps]
    needs: the pop's write-back must leave a temp cell [Other]-tagged, not just
    same-valued. *)
Lemma tload_store_same m p c c' m' :
  Transitional.Memory.load m p = Some c ->
  tvtag c'.1 = tvtag c.1 ->
  Transitional.Memory.store m p c' = Some m' ->
  forall q, tload m' q = tload m q.
Proof.
  move=> Hld Etag Hst q.
  case: (@eqP _ q p) => [->|Hne].
  - by rewrite /tload (load_store_eq Hst) Hld /= Etag.
  - by rewrite /tload (load_store_neq Hst Hne).
Qed.

Lemma vload_store_same m p c c' m' :
  Transitional.Memory.load m p = Some c ->
  Transitional.val c'.1 = Transitional.val c.1 ->
  Transitional.Memory.store m p c' = Some m' ->
  forall q, vload m' q = vload m q.
Proof.
  move=> Hld Eval Hst q.
  case: (@eqP _ q p) => [->|Hne].
  - by rewrite /vload (load_store_eq Hst) Hld /= Eval.
  - by rewrite /vload (load_store_neq Hst Hne).
Qed.

(* ================================================================== *)
(* Consequence: a [TS] Load step does not move any value              *)
(* ================================================================== *)

(** Every [TrLoad] — hence every [pop] — leaves the value view of memory
    completely unchanged, so a memory conjunct phrased over [vload] needs NO
    per-pop re-establishment. The Stage-0b risk is retired. *)

(** The statement that actually matters, done directly on the Load rule's
    premises (the shape [exec_pop_T] produces). *)
Theorem pop_preserves_vload m p v m' :
  Transitional.Memory.load m p = Some v ->
  Transitional.Memory.store m p
    ({| Transitional.val := Transitional.val v.1;
        tvtag := moved_tag (tvtag v.1) |},
     {| vtag := moved_tag (tvtag v.1);
        color := Pointer.component p; entry := None; is_code := false |})
    = Some m' ->
  forall q, vload m' q = vload m q.
Proof.
  move=> Hld Hst q.
  case: (@eqP _ q p) => [->|Hne].
  - by rewrite /vload (load_store_eq Hst) Hld /=.
  - by rewrite /vload (load_store_neq Hst Hne).
Qed.

End TMem.
