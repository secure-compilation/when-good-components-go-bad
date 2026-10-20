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

Lemma list_upd_total {A : Type} (l : seq A) k (x y : A) :
  List.nth_error l k = Some x -> exists l', list_upd l k y = Some l'.
Proof.
  elim: l k => [|a l IH] [|k] //=; first by move=> _; exists (y :: l).
  move=> H. case: (IH k H) => [l' Hl']. by rewrite Hl'; exists (a :: l').
Qed.

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


Definition vload (m : mem) (p : Pointer.t) : option value :=
  omap (fun c => Transitional.val c.1) (Transitional.Memory.load m p).

Definition tload (m : mem) (p : Pointer.t) : option value_tag :=
  omap (fun c => tvtag c.1) (Transitional.Memory.load m p).

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

Lemma vload_load m p v :
  vload m p = Some v -> exists w, Transitional.Memory.load m p = Some w.
Proof.
  rewrite /vload. case: (Transitional.Memory.load m p) => [w|] //= _.
  by exists w.
Qed.

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


End TMem.
