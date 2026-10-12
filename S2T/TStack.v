(** * Stage 4, part 2 — the `stack_match` retarget: the RA-slot chain.

    See plan-i2t-redo.md §2.3 (T2, T3) and §4 (Stage 4).

    `S2I/Simulation.v`'s `stack_match` relates the source stack to the
    Intermediate `gps`. Retargeting it at T means three changes:

      1. the `gps` argument is REPLACED by the ledger (`TInv.ledger`);
      2. each suspended activation's RA slot — currently loaded but left
         unconstrained as `junkRA` (`Simulation.v:335`, `:368`) — carries the
         concrete spilled return and its tag (T2);
      3. the `SM_external` frames' count drives `ti_lvl` (T3).

    This file builds (1) and (2): the chain of RA slots, the ledger derived
    from it, and the framing lemmas that make memory writes cheap. It is
    deliberately independent of `Simulation.v`'s source-side fields
    (`mem_inject`, `frame_temps`, `cont_matchJ`, …) — those port mechanically
    because they do not mention the stack discipline, and pulling them in here
    would couple this to the whole file.

    The slot ADDRESS is exactly the one `stack_match` already uses:
    `(C, fb, 2 + size temps)`. Nothing is invented; what changes is that the
    cell's contents stop being junk.

    ⚠ Every memory clause goes through `TMem.vload` / `TMem.tload`, per Stage 2
    part 1 — that is what makes T's load-write-back invisible. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Intermediate.Machine.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.
Require Import S2T.TMem.
Require Import S2T.TInv.
Require Import S2I.SimInject.
Require Import S2T.TInject.

Require Import Lib.Extra.
Require Import Lib.Monads.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Require Import Coq.ZArith.ZArith.
Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.

Module TStack.

Notation mem := Transitional.Memory.t.

(* ================================================================== *)
(* One suspended activation's return-address slot                     *)
(* ================================================================== *)

(** [ra_addr] is `stack_match`'s existing slot address `(C, fb, 2 + size
    temps)`; [ra_ret] is the return address spilled there; [ra_tag] is
    [InternalJump] for a frame suspended at an `IJal` and [Ret n] for one
    suspended at an `ICall`. *)
Record ra_slot := RASlot {
  ra_addr : Pointer.t;
  ra_ret  : Pointer.t;
  ra_tag  : value_tag
}.

Definition addrs (S : seq ra_slot) : seq Pointer.t := List.map ra_addr S.

(** What the slots say about memory. This is T2. *)
Definition slots_ok (m : mem) (S : seq ra_slot) : Prop :=
  forall s, List.In s S ->
    TMem.vload m (ra_addr s) = Some (Ptr (ra_ret s))
    /\ TMem.tload m (ra_addr s) = Some (ra_tag s)
    /\ TInv.is_live (ra_tag s).

(** The ledger the chain induces — the `gps` argument's replacement. *)
Definition ledger_of (S : seq ra_slot) : TInv.ledger :=
  List.map (fun s => (TInv.CMem (ra_addr s), ra_tag s)) S.

Lemma sites_ledger_of S :
  TInv.sites (ledger_of S) = List.map (fun a => TInv.CMem a) (addrs S).
Proof.
  rewrite /TInv.sites /ledger_of /addrs.
  by elim: S => //= s S ->.
Qed.

(** The freshness side condition the macros ask for
    ([push_ra_macro]'s `~ List.In (CMem p) (sites L)`) reduces to "p is not one
    of the live slot addresses" — which is what the frame layout gives. *)
Lemma fresh_of_addrs S p :
  ~ List.In p (addrs S) -> ~ List.In (TInv.CMem p) (TInv.sites (ledger_of S)).
Proof.
  move=> Hp. rewrite sites_ledger_of => Hin. apply: Hp.
  elim: (addrs S) Hin => //= a as' IH [E|Hin].
  - by left; case: E.
  - by right; exact: IH.
Qed.

Lemma in_addrs_of_slot S s : List.In s S -> List.In (ra_addr s) (addrs S).
Proof. move=> H. exact: (List.in_map ra_addr S s H). Qed.

(* ================================================================== *)
(* Framing                                                            *)
(* ================================================================== *)

(** ★ The one framing lemma. `PASS1_RESTRUCTURE.md` observed that the old
    design needed a per-operation transfer lemma for every stack-shaped
    conjunct (`stack_hgt_store_foreign`, `_alloc`, `_retag`, …), each redoing
    the induction. Here a store that misses every slot address transfers the
    whole chain, once. *)
Lemma slots_ok_store m p c m' S :
  (forall s, List.In s S -> ra_addr s <> p) ->
  Transitional.Memory.store m p c = Some m' ->
  slots_ok m S -> slots_ok m' S.
Proof.
  move=> Hne Hst H s Hin.
  have Hq := TMem.load_store_neq Hst (Hne s Hin).
  rewrite /TMem.vload /TMem.tload Hq.
  exact: (H s Hin).
Qed.

(** The same, phrased against the [addrs] list, which is how a diagram will
    have it. *)
Lemma slots_ok_store_fresh m p c m' S :
  ~ List.In p (addrs S) ->
  Transitional.Memory.store m p c = Some m' ->
  slots_ok m S -> slots_ok m' S.
Proof.
  move=> Hp Hst H. apply: (slots_ok_store _ Hst H).
  move=> s Hin Eq. apply: Hp. rewrite -Eq. exact: in_addrs_of_slot Hin.
Qed.

(* ================================================================== *)
(* The chain feeds tag_inv                                            *)
(* ================================================================== *)

(** The ledger's entries hold what the ledger says ([ti_slot]) and are live
    capabilities ([ti_addr]) — both directly from [slots_ok]. This is the
    connection that lets a diagram discharge two of `tag_inv`'s six clauses
    from the frame layout alone. *)
Lemma slots_ti_slot m rs S :
  slots_ok m S ->
  forall s t, List.In (s, t) (ledger_of S) -> TInv.tagat m rs s = Some t.
Proof.
  move=> H s t. rewrite /ledger_of => Hin.
  have [x [Ex Hx]] : exists x, (TInv.CMem (ra_addr x), ra_tag x) = (s, t)
                            /\ List.In x S
    by move: Hin => /List.in_map_iff [x [Ex Hx]]; exists x.
  case: (H x Hx) => [_ [Ht _]].
  by case: Ex => <- <-; rewrite /TInv.tagat.
Qed.

Lemma slots_ti_live m S :
  slots_ok m S ->
  forall s t, List.In (s, t) (ledger_of S) -> TInv.is_live t.
Proof.
  move=> H s t. rewrite /ledger_of => Hin.
  have [x [Ex Hx]] : exists x, (TInv.CMem (ra_addr x), ra_tag x) = (s, t)
                            /\ List.In x S
    by move: Hin => /List.in_map_iff [x [Ex Hx]]; exists x.
  case: (H x Hx) => [_ [_ Hl]].
  by case: Ex => _ <-.
Qed.

(* ================================================================== *)
(* T3 — the external-frame count drives ti_lvl                        *)
(* ================================================================== *)

(** The levels of the CROSS-component capabilities held in the chain. A slot
    is "external" exactly when its tag is a [Ret]; an [InternalJump] slot is an
    intra-component suspension and contributes nothing. *)
Definition ext_levels (S : seq ra_slot) : seq nat :=
  pmap (fun s => if ra_tag s is Ret n then Some n else None) S.

(** T3's well-formedness: the live [Ret] levels in the chain are exactly
    [0 .. k-1]. Stated with [perm_eq] because that is all [ti_lvl] needs —
    the ORDER of the levels down the stack is not part of the invariant, which
    is one reason this is cheaper than the old `sh`/`ret_heights` chain. *)
Definition levels_ok (S : seq ra_slot) (k : nat) : Prop :=
  perm_eq (ext_levels S) (iota 0 k).

(** ★ How many live [Ret]s a chain carries — [levels_ok] pins it exactly. This
    is the arithmetic the CROSS-COMPONENT return needs: `TS.JumpRet` fires only
    if the capability is `Ret (level pct - 1)`, i.e. the MAXIMUM live level, and
    `levels_ok` alone gives only the multiset. Combined with `SM_external`'s
    "the wrapper's tag is `Ret (size (ext_levels Sl))`" — a statement about the
    chain BELOW it — it pins the maximum. *)
Lemma levels_ok_size S k : levels_ok S k -> size (ext_levels S) = k.
Proof. by move=> /perm_size ->; rewrite size_iota. Qed.

(** The ledger's [Ret]-level projection IS [ext_levels]. Everything below is a
    corollary of this one computation. *)
Lemma ledger_of_rets S :
  [seq TInv.ret_lvl st.2 | st <- ledger_of S & TInv.is_ret st.2]
  = ext_levels S.
Proof.
  rewrite /ledger_of /ext_levels.
  elim: S => //= s S IH.
  by case: (ra_tag s) => [n| | |] /=; rewrite IH.
Qed.

(** T3, with no capability in [R_RA]. *)
Lemma ti_lvl_of_slots S pct :
  levels_ok S (level pct) ->
  perm_eq [seq TInv.ret_lvl st.2 | st <- ledger_of S & TInv.is_ret st.2]
          (iota 0 (level pct)).
Proof. by rewrite ledger_of_rets. Qed.

(** T3, with an INTRA-component capability in [R_RA]: the head is filtered
    out, so the count is untouched. *)
Lemma ti_lvl_of_slots_ij S pct :
  levels_ok S (level pct) ->
  perm_eq [seq TInv.ret_lvl st.2
          | st <- (TInv.CReg, InternalJump) :: ledger_of S & TInv.is_ret st.2]
          (iota 0 (level pct)).
Proof. by rewrite /= ledger_of_rets. Qed.

(** T3, with a CROSS-component capability in [R_RA] — the state between an
    [ICall] and the callee's spill. Here the register holds the innermost
    level and the chain holds the rest, which is exactly [perm_iota_push]. *)
Lemma ti_lvl_of_slots_ret S n pct :
  level pct = n.+1 ->
  levels_ok S n ->
  perm_eq [seq TInv.ret_lvl st.2
          | st <- (TInv.CReg, Ret n) :: ledger_of S & TInv.is_ret st.2]
          (iota 0 (level pct)).
Proof.
  move=> El H. rewrite /= ledger_of_rets El.
  exact: TInv.perm_iota_push.
Qed.

(** The chain-level transition an [ICall]'s spill performs: the capability
    moves from [R_RA] into a new slot, and the external count goes up by one.
    (The ledger-level counterpart is [TInv.tag_inv_push_ra].) *)
Lemma levels_ok_spill S n a r :
  levels_ok S n -> levels_ok (RASlot a r (Ret n) :: S) n.+1.
Proof.
  rewrite /levels_ok /ext_levels /= => H. exact: TInv.perm_iota_push.
Qed.

(** …and its inverse, performed by the matching reload. *)
Lemma levels_ok_reload S n a r :
  levels_ok (RASlot a r (Ret n) :: S) n.+1 -> levels_ok S n.
Proof.
  rewrite /levels_ok /ext_levels /= => H. exact: TInv.perm_iota_pop.
Qed.

(** An INTRA-component spill leaves the external count alone. *)
Lemma levels_ok_spill_ij S k a r :
  levels_ok S k -> levels_ok (RASlot a r InternalJump :: S) k.
Proof. by rewrite /levels_ok /ext_levels /=. Qed.

(* ================================================================== *)
(* frame_temps / frame_cap, retargeted                                *)
(* ================================================================== *)

(** Direct ports of `S2I/Simulation.v`'s `frame_temps` / `frame_cap`
    (`:140`, `:147`), with `Memory.load` replaced by [TMem.vload]. The slot
    arithmetic is unchanged — [R_SP] sits at `2 + size temps` and temp [i] at
    `1 + size temps - i`. *)
(** ★ The temps clause carries a TAG as well as a value, and the tag clause is
    FORCED by the machine, not chosen for convenience: MP's [BinOp] (and
    [Load]/[Store]/[Alloc]) require their operand registers to be
    [Other]-tagged, and a [pop] copies the CELL's tag into the register. So if a
    temp cell could hold an [Invalidated] husk, the pop-then-binop that every
    `Kbinop2` continuation performs would be STUCK.

    It is true because a temp is written by [push R_COM] with [R_COM]'s tag,
    which [ti_regs] pins to [Other]; the [Invalidated] husks a [pop R_RA] leaves
    behind sit AT [R_SP], one above the top temp, never inside the temps
    region. *)
Definition frame_temps (m : mem) (C : Component.id) (fb : Block.id)
           (temps : seq value) : Prop :=
  forall i, i < size temps ->
    TMem.vload m (C, fb, Z.of_nat (1 + size temps - i))
      = Some (nth Undef temps i)
    /\ TMem.tload m (C, fb, Z.of_nat (1 + size temps - i)) = Some Other.

Definition frame_cap (m : mem) (C : Component.id) (fb : Block.id)
           (cap : nat) : Prop :=
  forall j : Z, (0 <= j < Z.of_nat cap)%Z ->
    exists v, TMem.vload m (C, fb, j) = Some v.

(** An ARBITRARY store keeps the frame's capacity: a store never destroys a
    cell. This is what the prologue's two pushes need — they overwrite the
    linkage slots with new values, so [frame_temps_store_same] does not
    apply. *)
Lemma frame_cap_store m p c m' C fb cap :
  Transitional.Memory.store m p c = Some m' ->
  frame_cap m C fb cap -> frame_cap m' C fb cap.
Proof.
  move=> Hst H j Hj. case: (H j Hj) => [v Hv].
  exact: (TMem.vload_store_total Hst Hv).
Qed.

(** Both are [vload]-shaped, so a VALUE-PRESERVING store — the pop write-back —
    leaves them alone outright. No per-pop obligation, in either. *)
Lemma frame_temps_store_same m p c c' m' C fb temps :
  Transitional.Memory.load m p = Some c ->
  Transitional.val c'.1 = Transitional.val c.1 ->
  tvtag c'.1 = tvtag c.1 ->
  Transitional.Memory.store m p c' = Some m' ->
  frame_temps m C fb temps -> frame_temps m' C fb temps.
Proof.
  move=> Hld Ev Et Hst H i Hi.
  rewrite (TMem.vload_store_same Hld Ev Hst)
          (TMem.tload_store_same Hld Et Hst).
  exact: H.
Qed.

Lemma frame_cap_store_same m p c c' m' C fb cap :
  Transitional.Memory.load m p = Some c ->
  Transitional.val c'.1 = Transitional.val c.1 ->
  Transitional.Memory.store m p c' = Some m' ->
  frame_cap m C fb cap -> frame_cap m' C fb cap.
Proof.
  move=> Hld Ev Hst H j Hj.
  by rewrite (TMem.vload_store_same Hld Ev Hst); exact: H.
Qed.

(** A store elsewhere also leaves them alone. *)
Lemma frame_temps_store_other m p c m' C fb temps :
  (forall i, i < size temps ->
     (C, fb, Z.of_nat (1 + size temps - i)) <> p) ->
  Transitional.Memory.store m p c = Some m' ->
  frame_temps m C fb temps -> frame_temps m' C fb temps.
Proof.
  move=> Hne Hst H i Hi.
  rewrite /TMem.vload /TMem.tload (TMem.load_store_neq Hst (Hne i Hi)).
  exact: H.
Qed.

(* ================================================================== *)
(* A fresh frame satisfies frame_cap                                  *)
(* ================================================================== *)

Lemma nth_error_repeat_lt {A : Type} (x : A) n k :
  k < n -> List.nth_error (repeat x n) k = Some x.
Proof. by elim: n k => [|n IH] [|k] //= H; exact: IH. Qed.

(** Every cell of a freshly allocated block reads as [Undef]. *)
Lemma vload_alloc_fresh mt C n mt' b j :
  Transitional.Memory.alloc mt C n = Some (mt', (C, b, 0%Z)) ->
  (0 <= j)%Z -> Z.to_nat j < n ->
  TMem.vload mt' (C, b, j) = Some Undef.
Proof.
  move=> Ha Hj0 Hjn. case: (TInject.alloc_shape Ha) => [cm [Hcm Ep Emt]].
  have Eb : b = Transitional.Memory.nextblock cm
    by move: (f_equal Pointer.block Ep).
  rewrite /TMem.vload /Transitional.Memory.load Emt /= setmE eqxx /=.
  rewrite /Transitional.Memory.load_b /= setmE Eb eqxx.
  have -> : (0 <=? j)%Z = true by apply/Z.leb_le.
  by rewrite (nth_error_repeat_lt _ Hjn).
Qed.

Lemma nth_error_repeat_ge {A : Type} (x : A) n k :
  n <= k -> List.nth_error (repeat x n) k = None.
Proof. by elim: n k => [|n IH] [|k] //= H; exact: IH. Qed.

(** ★ The fresh block, at EVERY offset: [Undef] inside the allocated range and
    unreadable outside. The combined form is what the lock-step allocation needs
    — it must match the SOURCE's `ComponentMemory.load_after_alloc_eq`, which is
    stated the same way. *)
Lemma vload_alloc_fresh_eq mt C n mt' b (j : Z) :
  Transitional.Memory.alloc mt C n = Some (mt', (C, b, 0%Z)) ->
  TMem.vload mt' (C, b, j)
  = (if ((0 <=? j) && (j <? Z.of_nat n))%Z then Some Undef else None).
Proof.
  move=> Ha. case: (TInject.alloc_shape Ha) => [cm [Hcm Ep Emt]].
  have Eb : b = Transitional.Memory.nextblock cm
    by move: (f_equal Pointer.block Ep).
  rewrite /TMem.vload /Transitional.Memory.load Emt /= setmE eqxx /=.
  rewrite /Transitional.Memory.load_b /= setmE Eb eqxx.
  case E0: (0 <=? j)%Z; last by rewrite andFb.
  rewrite andTb. case En: (j <? Z.of_nat n)%Z.
  - rewrite (nth_error_repeat_lt _ (_ : Z.to_nat j < n)) //.
    by move/Z.leb_le: E0 => E0; move/Z.ltb_lt: En => En; lia.
  - rewrite nth_error_repeat_ge //.
    by move/Z.leb_le: E0 => E0; move/Z.ltb_ge: En => En; lia.
Qed.

(** Allocation changes no existing cell — the raw-load version, from which the
    value and tag views both follow. *)
Lemma load_alloc_other mt C n mt' p q :
  Transitional.Memory.alloc mt C n = Some (mt', p) ->
  (Pointer.component q <> C \/ Pointer.block q <> Pointer.block p) ->
  Transitional.Memory.load mt' q = Transitional.Memory.load mt q.
Proof.
  move=> Ha Hne. case: (TInject.alloc_shape Ha) => [cm [Hcm Ep Emt]].
  rewrite /Transitional.Memory.load Emt setmE.
  case EC: (Pointer.component q == C); last by [].
  move/eqP: EC => EC. rewrite EC Hcm /=.
  rewrite /Transitional.Memory.load_b /= setmE.
  have -> : (Pointer.block q == Transitional.Memory.nextblock cm) = false.
  { apply/negP => /eqP Eb. case: Hne => [H|H]; first by apply: H.
    by apply: H; rewrite Eb (f_equal Pointer.block Ep). }
  by [].
Qed.

Lemma tload_alloc_other mt C n mt' p q :
  Transitional.Memory.alloc mt C n = Some (mt', p) ->
  (Pointer.component q <> C \/ Pointer.block q <> Pointer.block p) ->
  TMem.tload mt' q = TMem.tload mt q.
Proof. move=> Ha Hne. by rewrite /TMem.tload (load_alloc_other Ha Hne). Qed.

Lemma ptr_expand (q : Pointer.t) :
  q = (Pointer.component q, Pointer.block q, Pointer.offset q).
Proof. by case: q => [[x y] z]. Qed.

(** A live slot cannot be in the block just allocated: slots are loadable and
    the fresh block was not. *)
Lemma slot_not_fresh mt C n mt' p Sl :
  Transitional.Memory.alloc mt C n = Some (mt', p) ->
  (forall (o : Z) w,
     Transitional.Memory.load mt (C, Pointer.block p, o) = Some w -> False) ->
  slots_ok mt Sl ->
  forall s, List.In s Sl ->
    Pointer.component (ra_addr s) <> C
    \/ Pointer.block (ra_addr s) <> Pointer.block p.
Proof.
  move=> Ha Hfresh H s Hin.
  case: (H s Hin) => [Hv _].
  case: (@eqP _ (Pointer.component (ra_addr s)) C) => [EC|HC]; last by left.
  case: (@eqP _ (Pointer.block (ra_addr s)) (Pointer.block p)) => [EB|HB];
    last by right.
  move: Hv. rewrite /TMem.vload.
  case Hl: (Transitional.Memory.load mt (ra_addr s)) => [w|] //= _.
  by case: (Hfresh (Pointer.offset (ra_addr s)) w);
     rewrite -EC -EB -ptr_expand.
Qed.

(** …so the chain survives an allocation. *)
Lemma slots_ok_alloc mt C n mt' p Sl :
  Transitional.Memory.alloc mt C n = Some (mt', p) ->
  (forall s, List.In s Sl ->
     Pointer.component (ra_addr s) <> C
     \/ Pointer.block (ra_addr s) <> Pointer.block p) ->
  slots_ok mt Sl -> slots_ok mt' Sl.
Proof.
  move=> Ha Hne H s Hin.
  rewrite /TMem.vload /TMem.tload (load_alloc_other Ha (Hne s Hin)).
  exact: (H s Hin).
Qed.

(** A freshly allocated cell reads back the tag it was initialised with —
    [Other], since the chunk is [repeat tUndef n]. Needed because [tag_inv]'s
    [ti_data] must not see a NEW capability cell appear. *)
Lemma nth_error_repeat_inv {A : Type} (x y : A) n k :
  List.nth_error (repeat x n) k = Some y -> y = x.
Proof. by elim: n k => [|n IH] [|k] //= => [[]|]; last exact: IH. Qed.

Lemma tload_alloc_in_fresh mt C n mt' b j t :
  Transitional.Memory.alloc mt C n = Some (mt', (C, b, 0%Z)) ->
  TMem.tload mt' (C, b, j) = Some t -> t = Other.
Proof.
  move=> Ha. case: (TInject.alloc_shape Ha) => [cm [Hcm Ep Emt]].
  have Eb : b = Transitional.Memory.nextblock cm
    by move: (f_equal Pointer.block Ep).
  rewrite /TMem.tload /Transitional.Memory.load Emt /= setmE eqxx /=.
  rewrite /Transitional.Memory.load_b /= setmE Eb eqxx.
  case: (0 <=? j)%Z => //=.
  case E: (List.nth_error _ _) => [[tv tg]|] //= [Et].
  by rewrite -Et (f_equal (fun c => tvtag c.1) (nth_error_repeat_inv E)).
Qed.

(** A block outside a component's domain is not loadable. Together with
    [TInject.alloc_fresh_notin] this is what says the about-to-be-allocated
    frame holds nothing — which every "fresh" side condition needs. *)
Lemma load_notin_domm mt C cm b (o : Z) :
  getm mt C = Some cm -> b \notin TInject.cdomm cm ->
  Transitional.Memory.load mt (C, b, o) = None.
Proof.
  move=> Hcm Hb. rewrite /Transitional.Memory.load Hcm /=.
  rewrite /Transitional.Memory.load_b /=.
  by move: Hb; rewrite /TInject.cdomm mem_domm; case: (getm _ b).
Qed.

Lemma alloc_fresh_unloadable a ms mt C n mt' b :
  TInject.minj a ms mt ->
  Transitional.Memory.alloc mt C n = Some (mt', (C, b, 0%Z)) ->
  forall (o : Z) w, Transitional.Memory.load mt (C, b, o) = Some w -> False.
Proof.
  move=> HI Ha o w Hl.
  case: (TInject.alloc_shape Ha) => [cm [Hcm Ep _]].
  have Eb : b = Transitional.Memory.nextblock cm
    by move: (f_equal Pointer.block Ep).
  have Hnb : b \notin TInject.cdomm cm
    by rewrite Eb; exact: TInject.alloc_fresh_notin (TInject.mj_wf_t HI Hcm).
  by move: Hl; rewrite (@load_notin_domm mt C cm b o Hcm Hnb).
Qed.

(** ★ [minj] survives a TARGET-ONLY allocation, with the SAME renaming.

    The prologue's frame allocation has no source counterpart, so the renaming
    must not move. What makes that work: the fresh block is outside [a]'s image
    at [C]. For a non-local source block that is [mj_rng] plus [cwf]; for the
    LOCAL block it is [inj_local] (which pins [a C local = Some local]) plus
    [mj_local_t]. The local case is easy to miss — [mj_rng] is guarded by
    [b0 != Block.local] and so says nothing about it. *)
Lemma minj_alloc a ms mt C n mt' b :
  TInject.minj a ms mt ->
  Transitional.Memory.alloc mt C n = Some (mt', (C, b, 0%Z)) ->
  TInject.minj a ms mt'.
Proof.
  move=> HI Ha.
  case: (TInject.alloc_shape Ha) => [cm [Hcm Ep Emt]].
  have Eb : b = Transitional.Memory.nextblock cm
    by move: (f_equal Pointer.block Ep).
  have Hbfresh : b \notin TInject.cdomm cm
    by rewrite Eb; exact: TInject.alloc_fresh_notin (TInject.mj_wf_t HI Hcm).
  have Himg : forall b0 b', a C b0 = Some b' -> b' <> b.
  { move=> b0 b' Hab Eb'. move: Hbfresh; rewrite -Eb' => Hnb.
    case: (@eqP _ b0 Block.local) => [E0|Hn0].
    - move: Hab; rewrite E0 (inj_local _ (TInject.mj_ok HI) C) => -[El].
      by move: Hnb; rewrite -El (TInject.mj_local_t HI Hcm).
    - case: (TInject.mj_rng HI Hab (introN eqP Hn0)) => [cm0 [Hcm0 Hin]].
      move: Hcm0; rewrite Hcm => -[Ecm]. rewrite -Ecm in Hin.
      by move: Hnb; rewrite Hin. }
  have EpB : Pointer.block (C, b, 0%Z) = b by [].
  case: HI => [Hok Hload Hwf Hloc Hrng Hwfs Hlocs Hdoms Hdomm Hdata].
  have Hout : forall C0 b0 (b' : Block.id) (i : Z), a C0 b0 = Some b' ->
      Pointer.component ((C0, b', i) : Pointer.t) <> C
      \/ Pointer.block ((C0, b', i) : Pointer.t)
         <> Pointer.block ((C, b, 0%Z) : Pointer.t).
  { move=> C0 b0 b' i Hab.
    case: (@eqP _ C0 C); last by move=> HC; left.
    move=> EC. right. rewrite EpB /=. apply: (Himg b0). by rewrite -EC. }
  split.
  - exact: Hok.
  - move=> C0 b0 b' i Hab.
    rewrite /TMem.vload (load_alloc_other Ha); first exact: Hload Hab.
    case: (@eqP _ C0 C); last by move=> HC; left.
    move=> EC. right. rewrite EpB /=. apply: (Himg b0). by rewrite -EC.
  - move=> C0 cm0. rewrite Emt setmE. case: (C0 =P C).
    + move=> _ [<-]. exact: TInject.alloc_b_cwf (Hwf _ _ Hcm).
    + move=> _. exact: Hwf.
  - move=> C0 cm0. rewrite Emt setmE. case: (C0 =P C).
    + move=> _ [<-]. rewrite TInject.alloc_b_cdomm_in.
      by apply/orP; right; exact: Hloc Hcm.
    + move=> _. exact: Hloc.
  - move=> C0 b0 b' Hab Hn0.
    case: (Hrng _ _ _ Hab Hn0) => [cm0 [Hcm0 Hin]].
    rewrite Emt setmE. case: (C0 =P C).
    + move=> EC. exists (Transitional.Memory.alloc_bis C cm n).1. split=> //.
      rewrite TInject.alloc_b_cdomm_in. apply/orP; right.
      have Ecm : cm0 = cm by move: Hcm0; rewrite EC Hcm => -[->].
      by rewrite -Ecm.
    + move=> _. by exists cm0.
  - (* the source is untouched by a T-side frame allocation *)
    exact: Hwfs.
  - exact: Hlocs.
  - exact: Hdoms.
  - (* the domain is untouched: the T alloc [setm]s a component already there *)
    move=> C0 cm0 HC0. case: (Hdomm C0 cm0 HC0) => [cm1 HC1].
    rewrite Emt setmE. case: (C0 =P C) => [_|_];
      [by eexists | by exists cm1].
  - (* the tag clause: range cells are untouched by the fresh block *)
    move=> C0 b0 b' i w Hab.
    rewrite (load_alloc_other Ha (Hout _ _ _ i Hab)). exact: Hdata Hab.
Qed.

(** ★ [tag_inv] survives an allocation.

    Discovered missing while planning the prologue port: the `IAlloc` in
    `compile_proc`'s prologue needs it, and nothing before this had to allocate.
    Two obligations, both discharged above: existing cells keep their tags
    ([tload_alloc_other]), and the FRESH cells are [Other]-tagged so no new live
    capability cell appears ([tload_alloc_in_fresh]). *)
Lemma tag_inv_alloc L mt rs pct C n mt' b :
  Transitional.Memory.alloc mt C n = Some (mt', (C, b, 0%Z)) ->
  (forall q t, List.In (TInv.CMem q, t) L ->
     Pointer.component q <> C \/ Pointer.block q <> b) ->
  TInv.tag_inv L mt rs pct -> TInv.tag_inv L mt' rs pct.
Proof.
  move=> Ha Hne [H1 H2 H3 H4 H5 H6 H7]; split=> //.
  - (* the ledger's sites still hold their tags *)
    move=> [q|] t Hin; last exact: H2 Hin.
    rewrite /TInv.tagat (tload_alloc_other Ha); first exact: H2 Hin.
    by move: (Hne q t Hin) => [H|H]; [left | right; rewrite -/(Pointer.block _)].
  - (* no NEW live capability cell appeared *)
    move=> q t Hq Hl.
    case: (@eqP _ (Pointer.component q) C) => [EC|HC]; last first.
    { apply: (H4 q t) => //. by rewrite -(tload_alloc_other Ha (or_introl HC)). }
    case: (@eqP _ (Pointer.block q) b) => [EB|HB]; last first.
    { apply: (H4 q t) => //. by rewrite -(tload_alloc_other Ha (or_intror HB)). }
    (* q is in the fresh block: its tag is [Other], so it is not live *)
    move: Hq. rewrite (ptr_expand q) EC EB => Hq.
    by move: Hl; rewrite (tload_alloc_in_fresh Ha Hq).
  (* the register file stays total ([//] closes it when [rs] is untouched) *)
  all: by do ?[apply: TInv.regs_dom_set];
           first [exact: H7 | apply: TInv.regs_dom_invalidate].
Qed.

(** ★ The prologue's [IAlloc] establishes [frame_cap] on the new frame
    outright — the frame is exactly as big as it was asked to be. Together
    with [TInject.alloc_fresh_outside] (frame PRIVACY), this is everything the
    callee's prologue needs from its own allocation. *)
Lemma alloc_frame_cap mt C n mt' b :
  Transitional.Memory.alloc mt C n = Some (mt', (C, b, 0%Z)) ->
  frame_cap mt' C b n.
Proof.
  move=> Ha j [Hj0 Hjn]. exists Undef.
  apply: (vload_alloc_fresh Ha Hj0).
  have Hn0 : (0 <= Z.of_nat n)%Z by lia.
  apply/ltP. rewrite -(Nat2Z.id n).
  by apply: (proj1 (Z2Nat.inj_lt j (Z.of_nat n) Hj0 Hn0)).
Qed.

End TStack.
