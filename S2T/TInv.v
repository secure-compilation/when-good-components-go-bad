(** * Stage 2, part 2 — [tag_inv].

    See plan-i2t-redo.md §2.3 (T1–T4) and §4 (Stage 2).

    [tag_inv] is the T-SIDE half of the invariant: everything that can be said
    about tags without mentioning the source. It is parameterised by a
    **ledger** [L] — the live return capabilities, innermost first — which in
    Stage 4 is supplied by the ported [stack_match]:

      - the ledger's ADDRESSES are the RA spill slots ([SM_internal] /
        [SM_external]'s currently-unconstrained [junkRA] cells, T2);
      - the ledger's [Ret] entries count the cross-component frames (T3).

    Splitting it this way is deliberate. T1's and T2's *content* — WHICH return
    address belongs in which slot — is a statement about the source stack and
    belongs with [stack_match]. What lives here is the part that must hold of
    the machine state alone, and it is exactly what the Stage-0 harness checks
    by execution ([S2T/T_Audit.v]):

      [ti_regs]  ↔ harness [bad_regs] = []
      [ti_addr]  ↔ harness [cap_not_ptr] = []   (an address tag sits on a Ptr)
      [ti_uniq]  ↔ harness [uniq (mem_rets ++ reg_rets)]
      [ti_lvl]   ↔ harness [all (fun k => k < level pct) (mem_rets)]

    ⚠ DESIGN CONSTRAINT (Stage 2 part 1, [S2T/TMem.v]): every memory
    clause is phrased over [TMem.vload] / [TMem.tload], never over raw
    [Memory.load]. That is what makes T's load-write-back invisible, so there is
    no per-pop framing obligation. Do not add a clause that inspects a cell's
    [mem_tag] directly. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Intermediate.Machine.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.
Require Import S2T.TMem.

Require Import Lib.Extra.
Require Import Lib.Monads.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From extructures Require Import ord fmap fset.

Require Import Coq.ZArith.ZArith.
Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.

Module TInv.

Notation mem := Transitional.Memory.t.
Notation regs := Transitional.Register.t.

(* ================================================================== *)
(* Register lemmas                                                    *)
(* ================================================================== *)

(* [Transitional.Register] ships none of the [get_set_*] lemmas
   [S2I/SimCode.v] provides for [Intermediate.Register]. (Also re-proved in
   the Stage-0b spike, which is a measurement file and will be deleted.) *)

(* [register] has no eqType instance either. *)
Lemma reg_eq_dec (r r' : register) : {r = r'} + {r <> r'}.
Proof. by case: r; case: r'; try (by left); right. Qed.

Lemma to_nat_inj r r' :
  Transitional.Register.to_nat r = Transitional.Register.to_nat r' -> r = r'.
Proof. by case: r; case: r'. Qed.

Lemma get_set_eq r v t rs :
  Transitional.Register.get r (Transitional.Register.set r v t rs) = MVal t v.
Proof.
  by rewrite /Transitional.Register.get /Transitional.Register.set setmE eqxx.
Qed.

Lemma get_set_neq r r' v t rs :
  r <> r' ->
  Transitional.Register.get r (Transitional.Register.set r' v t rs)
  = Transitional.Register.get r rs.
Proof.
  move=> Hne.
  rewrite /Transitional.Register.get /Transitional.Register.set setmE.
  case E: (Transitional.Register.to_nat r == Transitional.Register.to_nat r')=> //.
  by move/eqP/to_nat_inj: E => E; case: Hne.
Qed.
(* symmetric orientation, needed when the SET target is the data register and
   the READ target is [R_RA] *)
Lemma get_set_neq' r r' v t rs :
  r' <> r ->
  Transitional.Register.get r (Transitional.Register.set r' v t rs)
  = Transitional.Register.get r rs.
Proof. move=> H. apply: get_set_neq => E. by apply: H; rewrite E. Qed.

(* ================================================================== *)
(* Capability sites                                                   *)
(* ================================================================== *)

(** ⚠ REVISED (2026-07-29), while proving the capability cases. The first cut
    of [tag_inv] had the ledger range over MEMORY only, and keyed [ti_data] on
    [is_address]. Both are wrong:

    1. A live capability is not always in memory. Immediately after an [ICall]
       at [Level n.+1], the innermost capability [Ret n] sits in [R_RA] and the
       spill slots hold only [Ret 0 .. Ret n-1] — so a memory-only [ti_lvl]
       cannot equal [iota 0 (level pct)].

    2. [is_address] is true of [Invalidated], which is precisely the DEAD
       marker. [pop R_RA] leaves the vacated slot tagged [Invalidated], and
       [Register.invalidate] at a cross-return keeps a stale [Ret n] husk in
       [R_RA] at [Level n] — the case the Stage-0 harness flagged and exempted.
       Keying on [is_address] would demand both husks be in the ledger.

    Fix: sites range over memory OR [R_RA], and the ledger tracks LIVE
    capabilities only. [Invalidated] is dead and unconstrained, which is exactly
    what the policy means by it. *)

Inductive capsite := CMem of Pointer.t | CReg.

Notation ledger := (seq (capsite * value_tag)).

Definition sites (L : ledger) : seq capsite := List.map fst L.

Definition is_ret (t : value_tag) : bool := if t is Ret _ then true else false.
Definition ret_lvl (t : value_tag) : nat := if t is Ret n then n else 0.

(** a USABLE capability: [Invalidated] is spent, [Other] is data *)
Definition is_live (t : value_tag) : bool :=
  match t with Ret _ | InternalJump => true | _ => false end.

Lemma is_live_address t : is_live t -> is_address t.
Proof. by case: t. Qed.

Lemma is_ret_live t : is_ret t -> is_live t.
Proof. by case: t. Qed.

Lemma is_ret_moved t : is_ret (moved_tag t) = false.
Proof. by case: t. Qed.

Definition tagat (m : mem) (rs : regs) (s : capsite) : option value_tag :=
  match s with
  | CMem p => TMem.tload m p
  | CReg => Some (tvtag (Transitional.Register.get R_RA rs))
  end.

Lemma in_sites s t L : List.In (s, t) L -> List.In s (sites L).
Proof. move=> H. exact: (List.in_map fst L (s, t) H). Qed.

(* ================================================================== *)
(* tag_inv                                                            *)
(* ================================================================== *)

(** Every register is PRESENT. [Transitional.Register.get_tag] returns [None]
    off-domain, and [TS.Store] genuinely needs [Some] — so a store of an absent
    register is stuck. This is not bookkeeping: without it the prologue's
    [push R_ARG] cannot be shown to step at all. [Register.init] satisfies it
    and every register write preserves it ([regs_dom_set] below). *)
Definition regs_dom (rs : regs) : Prop :=
  forall r, exists tv, getm rs (Transitional.Register.to_nat r) = Some tv.

Record tag_inv (L : ledger) (m : mem) (rs : regs) (pct : pc_tag) : Prop :=
  TagInv {
  (* T4, registers: only [R_RA] may carry a capability. *)
  ti_regs : forall r, r <> R_RA ->
            tvtag (Transitional.Register.get r rs) = Other;

  (* T1/T2: each site holds the capability the ledger records. *)
  ti_site : forall s t, List.In (s, t) L -> tagat m rs s = Some t;

  (* a ledger entry is a LIVE capability *)
  ti_live : forall s t, List.In (s, t) L -> is_live t;

  (* T4, memory: the only LIVE capability cells are the ledger's.
     (Dead [Invalidated] husks are deliberately unconstrained.) *)
  ti_data : forall p t, TMem.tload m p = Some t -> is_ret t ->
            List.In (CMem p) (sites L);

  ti_uniq : List.NoDup (sites L);

  (* T3: the live [Ret] levels are exactly [0 .. level pct - 1], each once —
     now counted across BOTH memory and [R_RA]. *)
  ti_lvl  : perm_eq [seq ret_lvl st.2 | st <- L & is_ret st.2]
                    (iota 0 (level pct));

  (* the register file is total *)
  ti_dom  : regs_dom rs
}.

(** [regs_dom] is preserved by every register write, and holds of
    [Register.invalidate] outright (it is a literal seven-key map). *)
Lemma regs_dom_set rs r v t : regs_dom rs ->
  regs_dom (Transitional.Register.set r v t rs).
Proof.
  move=> H r'. rewrite /Transitional.Register.set setmE.
  case: eqP => [_|_]; first by eexists.
  exact: H r'.
Qed.

Lemma regs_dom_invalidate rs : regs_dom (Transitional.Register.invalidate rs).
Proof. by case=> /=; eexists. Qed.

(** …which is what turns [ti_regs] into the [get_tag] premise the store rule
    asks for. *)
Lemma ti_get_tag L m rs pct r : tag_inv L m rs pct ->
  Transitional.Register.get_tag r rs
  = Some (tvtag (Transitional.Register.get r rs)).
Proof.
  move=> HI. case: (ti_dom HI r) => [tv Etv].
  by rewrite /Transitional.Register.get_tag /Transitional.Register.get Etv.
Qed.

Lemma ti_tag_other L m rs pct r : tag_inv L m rs pct -> r <> R_RA ->
  Transitional.Register.get_tag r rs = Some Other.
Proof. by move=> HI Hr; rewrite (ti_get_tag r HI) (ti_regs HI Hr). Qed.

(** [pc_tag] is a one-field wrapper, so a level determines it. Needed wherever a
    rule's premise is stated as [pct = Level n] but the invariant only gives
    [level pct = n]. *)
Lemma pc_tagE (pct : pc_tag) : pct = Level (level pct).
Proof. by case: pct. Qed.

(** A site in [sites L] carries some tag. Used to turn the "no ledger entry is
    in this block" facts into the [~ List.In (CMem p) (sites L)] premise the
    macros ask for. *)
Lemma in_sites_pair L s : List.In s (sites L) -> exists t, List.In (s, t) L.
Proof.
  rewrite /sites => /List.in_map_iff [[s' t] [/= Es Hin]].
  by exists t; rewrite -Es.
Qed.

(* ================================================================== *)
(* Framing — the data cases                                           *)
(* ================================================================== *)

Lemma not_address_Other t : ~~ is_address t -> t = Other.
Proof. by case: t. Qed.

(** Writing an [Other]-tagged value to a register other than [R_RA]. Covers
    every [IConst], [IBinOp] and data [IMov]. ([R_RA] is excluded now only
    because the ledger may hold a [CReg] entry that such a write would
    destroy — the data opcodes never target [R_RA] anyway.) *)
Lemma tag_inv_setreg L m rs pct r v :
  r <> R_RA ->
  tag_inv L m rs pct ->
  tag_inv L m (Transitional.Register.set r v Other rs) pct.
Proof.
  move=> Hr [H1 H2 H3 H4 H5 H6 H7]; split=> //.
  - move=> r' Hr'. case: (reg_eq_dec r' r) => [->|Hne].
    + by rewrite get_set_eq.
    + by rewrite get_set_neq //; exact: H1.
  - move=> [q|] t Hin; last first.
    + rewrite /tagat get_set_neq'; [exact: H2 Hin | exact: Hr].
    + exact: H2 Hin.
  (* the register file stays total ([//] closes it when [rs] is untouched) *)
  all: by do ?[apply: regs_dom_set];
           first [exact: H7 | apply: regs_dom_invalidate].
Qed.

(** Storing a non-capability at an address that is not a live site. *)
Lemma tag_inv_store_data L m rs pct p c m' :
  ~ List.In (CMem p) (sites L) ->
  ~~ is_ret (tvtag c.1) ->
  Transitional.Memory.store m p c = Some m' ->
  tag_inv L m rs pct ->
  tag_inv L m' rs pct.
Proof.
  move=> Hp Hc Hst [H1 H2 H3 H4 H5 H6 H7]; split=> //.
  - move=> [q|] t Hin; last exact: H2 Hin.
    rewrite /tagat /TMem.tload (TMem.load_store_neq Hst).
    + exact: H2 Hin.
    + move=> Eq. apply: Hp. rewrite -Eq. exact: in_sites Hin.
  - move=> q t. case: (@eqP _ q p) => [->|Hne].
    + rewrite /TMem.tload (TMem.load_store_eq Hst) /= => [[<-]].
      by move/negP: Hc.
    + by rewrite /TMem.tload (TMem.load_store_neq Hst Hne); exact: H4.
  (* the register file stays total ([//] closes it when [rs] is untouched) *)
  all: by do ?[apply: regs_dom_set];
           first [exact: H7 | apply: regs_dom_invalidate].
Qed.

(* ================================================================== *)
(* Framing — the capability cases                                     *)
(* ================================================================== *)

(** ★ [push R_RA]: the capability MOVES from [R_RA] to the spill slot [p].

    The ledger entry is renamed [CReg -> CMem p]; its TAG is unchanged, which
    is why [ti_lvl] needs no work at all — the [Ret]-level multiset is literally
    the same list. [R_RA] is left [Invalidated], i.e. dead, and dead husks are
    unconstrained by construction. *)
Lemma tag_inv_push_ra L m rs pct p t m' :
  tvtag (Transitional.Register.get R_RA rs) = t ->
  ~ List.In (CMem p) (sites L) ->
  Transitional.Memory.store m p
    (Transitional.Register.get R_RA rs,
     {| vtag := t; color := Pointer.component p; entry := None;
        is_code := false |}) = Some m' ->
  tag_inv ((CReg, t) :: L) m rs pct ->
  tag_inv ((CMem p, t) :: L) m'
    (Transitional.Register.set R_RA
       (Transitional.val (Transitional.Register.get R_RA rs)) (moved_tag t) rs)
    pct.
Proof.
  move=> Et Hp Hst HI.
  have HnotReg : ~ List.In CReg (sites L).
  { by move: (ti_uniq HI) => /= /List.NoDup_cons_iff [] . }
  have Hmem : forall s u, List.In (s, u) L -> exists q, s = CMem q.
  { move=> [q|] u Hin; first by exists q.
    by case: HnotReg; exact: in_sites Hin. }
  have Hnew : TMem.tload m' p = Some t
    by rewrite /TMem.tload (TMem.load_store_eq Hst) /= Et.
  case: HI => [H1 H2 H3 H4 H5 H6 H7]; split.
  - (* registers other than R_RA are untouched *)
    move=> r Hr. by rewrite get_set_neq //; exact: H1.
  - (* the sites *)
    move=> s u /= [[Es Eu]|Hin].
    + by rewrite -Es -Eu.
    + case: (Hmem _ _ Hin) => [q Eq]. rewrite Eq /tagat /TMem.tload.
      rewrite (TMem.load_store_neq Hst).
      * by move: (H2 s u (or_intror Hin)); rewrite Eq.
      * move=> Eqp. apply: Hp. rewrite -Eqp -Eq. exact: in_sites Hin.
  - (* still live *)
    move=> s u /= [[_ <-]|Hin]; first exact: (H3 CReg t (or_introl erefl)).
    exact: (H3 s u (or_intror Hin)).
  - (* no unaccounted live cell *)
    move=> q u. case: (@eqP _ q p) => [->|Hne].
    + by move=> _ _ /=; left.
    + rewrite /TMem.tload (TMem.load_store_neq Hst Hne) => Hq Hl.
      move: (H4 q u Hq Hl) => /= [E|Hin]; first by [].
      by right.
  - (* uniqueness *)
    by move: H5 => /= /List.NoDup_cons_iff [_ H5]; apply/List.NoDup_cons_iff.
  - (* the Ret multiset is unchanged: only the SITE was renamed, the TAG is
       the same, so both sides reduce to the same list once [is_ret t] is
       decided. *)
    move: H6 => /=. by case: (is_ret t) => H; exact: H.
  (* the register file stays total ([//] closes it when [rs] is untouched) *)
  all: by do ?[apply: regs_dom_set];
           first [exact: H7 | apply: regs_dom_invalidate].
Qed.

(** ★ [pop R_RA]: the mirror of [tag_inv_push_ra] — the capability moves BACK
    from the spill slot to [R_RA]. The ledger entry is renamed
    [CMem p -> CReg]; the vacated cell is left [Invalidated], i.e. dead, and
    dead husks are unconstrained.

    The [~ List.In CReg (sites L)] premise is what says [R_RA] is not already
    holding a live capability that this load would destroy. True of compiled
    code: at a [pop R_RA] the register holds the [Invalidated] husk that the
    matching [push R_RA] left there. *)
Lemma tag_inv_pop_ra L m rs pct p v m' :
  is_live (tvtag v.1) ->
  ~ List.In CReg (sites L) ->
  Transitional.Memory.load m p = Some v ->
  Transitional.Memory.store m p
    ({| Transitional.val := Transitional.val v.1; tvtag := moved_tag (tvtag v.1) |},
     {| vtag := moved_tag (tvtag v.1); color := Pointer.component p; entry := None;
        is_code := false |}) = Some m' ->
  tag_inv ((CMem p, tvtag v.1) :: L) m rs pct ->
  tag_inv ((CReg, tvtag v.1) :: L) m'
    (Transitional.Register.set R_RA (Transitional.val v.1) (tvtag v.1) rs) pct.
Proof.
  move=> Hlive HnotReg Hld Hst HI.
  have Hfresh : ~ List.In (CMem p) (sites L)
    by move: (ti_uniq HI) => /= /List.NoDup_cons_iff [].
  have Hmem : forall s u, List.In (s, u) L -> exists q, s = CMem q.
  { move=> [q|] u Hin; first by exists q.
    by case: HnotReg; exact: in_sites Hin. }
  case: HI => [H1 H2 H3 H4 H5 H6 H7]; split.
  - move=> r Hr. by rewrite get_set_neq //; exact: H1.
  - move=> s u /= [[Es Eu]|Hin].
    + by rewrite -Es -Eu /tagat get_set_eq.
    + case: (Hmem _ _ Hin) => [q Eq]. rewrite Eq /tagat /TMem.tload.
      rewrite (TMem.load_store_neq Hst).
      * by move: (H2 s u (or_intror Hin)); rewrite Eq.
      * move=> Eqp. apply: Hfresh. rewrite -Eqp -Eq. exact: in_sites Hin.
  - move=> s u /= [[_ <-]|Hin]; first exact: Hlive.
    exact: (H3 s u (or_intror Hin)).
  - move=> q u. case: (@eqP _ q p) => [->|Hne].
    + by rewrite /TMem.tload (TMem.load_store_eq Hst) /= => [[<-]]; rewrite is_ret_moved.
    + rewrite /TMem.tload (TMem.load_store_neq Hst Hne) => Hq Hl.
      move: (H4 q u Hq Hl) => /= [E|Hin]; first by case: E => Ep; case: Hne.
      by right.
  - by apply/List.NoDup_cons_iff; split=> //;
       move: H5 => /= /List.NoDup_cons_iff [].
  - move: H6 => /=. by case: (is_ret (tvtag v.1)) => H; exact: H.
  (* the register file stays total ([//] closes it when [rs] is untouched) *)
  all: by do ?[apply: regs_dom_set];
           first [exact: H7 | apply: regs_dom_invalidate].
Qed.

(** ★ [IJal]: a fresh intra-component capability is CREATED in [R_RA].

    [ti_lvl] needs no work: [InternalJump] is not a [Ret], so the level
    multiset is untouched. That is the formal content of "intra-component
    calls do not change the cross-component depth". *)
Lemma tag_inv_jal L m rs pct ret :
  ~ List.In CReg (sites L) ->
  tag_inv L m rs pct ->
  tag_inv ((CReg, InternalJump) :: L) m
    (Transitional.Register.set R_RA (Ptr ret) InternalJump rs) pct.
Proof.
  move=> HnotReg HI.
  have Hmem : forall s u, List.In (s, u) L -> exists q, s = CMem q.
  { move=> [q|] u Hin; first by exists q.
    by case: HnotReg; exact: in_sites Hin. }
  case: HI => [H1 H2 H3 H4 H5 H6 H7]; split.
  - move=> r Hr. by rewrite get_set_neq //; exact: H1.
  - move=> s u /= [[Es Eu]|Hin].
    + by rewrite -Es -Eu /tagat get_set_eq.
    + case: (Hmem _ _ Hin) => [q Eq].
      move: (H2 s u Hin); rewrite Eq /tagat => Hq; exact: Hq.
  - move=> s u /= [[_ <-]|Hin]; first by [].
    exact: (H3 s u Hin).
  - move=> q u Hq Hl. by right; exact: (H4 q u Hq Hl).
  - by apply/List.NoDup_cons_iff.
  - exact: H6.
  (* the register file stays total ([//] closes it when [rs] is untouched) *)
  all: by do ?[apply: regs_dom_set];
           first [exact: H7 | apply: regs_dom_invalidate].
Qed.

(** The pop-of-DATA case. Restored after the capsite redesign, and with a
    STRONGER premise than the first version had: the loaded cell must be
    [Other]-tagged, not merely "not a live site".

    Reason: a cell can hold a dead [Invalidated] husk — [pop R_RA] leaves one
    behind. That is not [is_live], so the site premise alone permits it; but it
    IS [is_address], so the load would put [Invalidated] into a data register
    and break [ti_regs]. Compiled code never does this (a slot is always
    re-pushed before being re-popped), and the diagram will know it from the
    frame contents. *)
Lemma tag_inv_load_data L m rs pct p v m' r2 :
  r2 <> R_RA ->
  tvtag v.1 = Other ->
  ~ List.In (CMem p) (sites L) ->
  Transitional.Memory.load m p = Some v ->
  Transitional.Memory.store m p
    ({| Transitional.val := Transitional.val v.1; tvtag := Other |},
     {| vtag := Other; color := Pointer.component p; entry := None;
        is_code := false |}) = Some m' ->
  tag_inv L m rs pct ->
  tag_inv L m'
    (Transitional.Register.set r2 (Transitional.val v.1) Other rs) pct.
Proof.
  move=> Hr2 Ev Hp Hld Hst HI.
  apply: tag_inv_setreg; first exact: Hr2.
  apply: (tag_inv_store_data Hp _ Hst HI).
  by [].
Qed.

(** Dropping a NON-[Ret] capability from [R_RA]'s ledger slot.

    Needed at an intra-component return: MP's internal JUMP rule leaves the
    register tags untouched, so after the jump [R_RA] still carries the
    [InternalJump] it jumped through. The caller's [pop R_RA] is about to
    overwrite it, so the ledger must stop claiming it first.

    Sound because [ti_data] constrains MEMORY only — a register capability the
    ledger has forgotten is simply untracked, not contradicted — and because a
    non-[Ret] entry contributes nothing to [ti_lvl]. *)
(** Writing [R_RA] when the ledger has NO register entry: invisible. [ti_regs]
    never constrains [R_RA], and [tagat] reads it only at the [CReg] site —
    which the premise excludes. This is what lets main's wrapper pop junk into
    [R_RA] after the body's capability has been retired. *)
Lemma tag_inv_setra L m rs pct v t :
  ~ List.In CReg (sites L) ->
  tag_inv L m rs pct ->
  tag_inv L m (Transitional.Register.set R_RA v t rs) pct.
Proof.
  move=> HnotReg [H1 H2 H3 H4 H5 H6 H7]; split=> //.
  - move=> r Hr. rewrite get_set_neq //. exact: H1 r Hr.
  - move=> s u Hin. move: (H2 s u Hin). case: s Hin => [q|] Hin //.
    by case: HnotReg; exact: in_sites Hin.
  - by apply: regs_dom_set.
Qed.

Lemma tag_inv_drop_reg L m rs pct t :
  is_ret t = false ->
  tag_inv ((CReg, t) :: L) m rs pct -> tag_inv L m rs pct.
Proof.
  move=> Ht [H1 H2 H3 H4 H5 H6 H7]; split.
  - exact: H1.
  - move=> s u Hin. exact: (H2 s u (or_intror Hin)).
  - move=> s u Hin. exact: (H3 s u (or_intror Hin)).
  - move=> q u Hq Hl.
    move: (H4 q u Hq Hl) => /= [E|Hin]; [by [] | exact: Hin].
  - by move: H5 => /= /List.NoDup_cons_iff [].
  - move: H6 => /=. rewrite Ht. exact: id.
  (* the register file stays total ([//] closes it when [rs] is untouched) *)
  all: by do ?[apply: regs_dom_set];
           first [exact: H7 | apply: regs_dom_invalidate].
Qed.

(* ================================================================== *)
(* Cross-component: the level shifts                                  *)
(* ================================================================== *)

(** The two directions of "the live [Ret] levels are [0 .. k-1]" under a
    push/pop of the top level. This is the only genuinely arithmetic content in
    the whole invariant. *)
(* no [iota]/[rcons] lemma exists in mathcomp, so: *)
Lemma iota_rcons m k : iota m k.+1 = rcons (iota m k) (m + k).
Proof.
  elim: k m => [|k IH] m; first by rewrite addn0.
  have -> : iota m k.+1.+1 = m :: iota m.+1 k.+1 by [].
  have -> : iota m k.+1 = m :: iota m.+1 k by [].
  by rewrite IH rcons_cons addnS addSn.
Qed.

Lemma perm_iota_push n A :
  perm_eq A (iota 0 n) -> perm_eq (n :: A) (iota 0 n.+1).
Proof.
  move=> H.
  have E : iota 0 n.+1 = rcons (iota 0 n) n by rewrite iota_rcons add0n.
  rewrite E perm_sym perm_rcons perm_cons perm_sym. exact: H.
Qed.

Lemma perm_iota_pop n A :
  perm_eq (n :: A) (iota 0 n.+1) -> perm_eq A (iota 0 n).
Proof.
  move=> H.
  have E : iota 0 n.+1 = rcons (iota 0 n) n by rewrite iota_rcons add0n.
  move: H; rewrite E perm_sym perm_rcons perm_cons perm_sym; exact: id.
Qed.

(** [Register.invalidate] keeps only [R_COM] and [R_RA]; everything else
    becomes [tUndef], whose tag is [Other]. *)
Lemma get_invalidateE r rs :
  Transitional.Register.get r (Transitional.Register.invalidate rs)
  = match r with
    | R_COM => Transitional.Register.get R_COM rs
    | R_RA => Transitional.Register.get R_RA rs
    | _ => tUndef
    end.
Proof. by case: r. Qed.

Lemma tvtag_invalidate r rs :
  r <> R_RA ->
  tvtag (Transitional.Register.get r rs) = Other ->
  tvtag (Transitional.Register.get r (Transitional.Register.invalidate rs))
  = Other.
Proof. by case: r => // _ H; rewrite get_invalidateE. Qed.

(** ★ [ICall]: a fresh CROSS-component capability [Ret n] is created in [R_RA],
    the other registers are invalidated, and the level goes up by one.

    Unlike [tag_inv_jal] this DOES move [ti_lvl] — by exactly one, which is
    [perm_iota_push]. *)
Lemma tag_inv_call L m rs pct n ret :
  pct = Level n ->
  ~ List.In CReg (sites L) ->
  tag_inv L m rs pct ->
  tag_inv ((CReg, Ret n) :: L) m
    (Transitional.Register.set R_RA (Ptr ret) (Ret n)
       (Transitional.Register.invalidate rs))
    (inc_pc_tag pct).
Proof.
  move=> Epct HnotReg HI.
  have Hmem : forall s u, List.In (s, u) L -> exists q, s = CMem q.
  { move=> [q|] u Hin; first by exists q.
    by case: HnotReg; exact: in_sites Hin. }
  case: HI => [H1 H2 H3 H4 H5 H6 H7]; split.
  - move=> r Hr. rewrite get_set_neq //. exact: tvtag_invalidate (H1 r Hr).
  - move=> s u /= [[Es Eu]|Hin].
    + by rewrite -Es -Eu /tagat get_set_eq.
    + case: (Hmem _ _ Hin) => [q Eq].
      move: (H2 s u Hin); rewrite Eq /tagat => Hq; exact: Hq.
  - move=> s u /= [[_ <-]|Hin]; first by [].
    exact: (H3 s u Hin).
  - move=> q u Hq Hl. by right; exact: (H4 q u Hq Hl).
  - by apply/List.NoDup_cons_iff.
  - have El : level (inc_pc_tag pct) = n.+1 by rewrite Epct; cbn; lia.
    rewrite El /=. apply: perm_iota_push.
    move: H6; rewrite Epct /= => H; exact: H.
  - (* the register file stays total *)
    apply: regs_dom_set. apply: regs_dom_invalidate.
Qed.

(** ★ [IReturn]: the cross-component capability is CONSUMED — removed from the
    ledger, and [R_RA] left [Invalidated] by [TS.invalidate_ret] (plan §3.6).

    Without that fix this lemma is FALSE: the spent [Ret n] would survive in
    [R_RA] at [Level n], which is precisely the violation the Stage-0 harness
    reported. *)
Lemma tag_inv_return L m rs pct n :
  pct = Level n.+1 ->
  tag_inv ((CReg, Ret n) :: L) m rs pct ->
  tag_inv L m (TS.invalidate_ret rs) (dec_pc_tag pct).
Proof.
  move=> Epct HI.
  have HnotReg : ~ List.In CReg (sites L)
    by move: (ti_uniq HI) => /= /List.NoDup_cons_iff [].
  have Hmem : forall s u, List.In (s, u) L -> exists q, s = CMem q.
  { move=> [q|] u Hin; first by exists q.
    by case: HnotReg; exact: in_sites Hin. }
  case: HI => [H1 H2 H3 H4 H5 H6 H7]; split.
  - move=> r Hr. rewrite /TS.invalidate_ret get_set_neq //.
    exact: tvtag_invalidate (H1 r Hr).
  - move=> s u Hin. case: (Hmem _ _ Hin) => [q Eq].
    move: (H2 s u (or_intror Hin)); rewrite Eq /tagat => Hq; exact: Hq.
  - move=> s u Hin. exact: (H3 s u (or_intror Hin)).
  - move=> q u Hq Hl.
    move: (H4 q u Hq Hl) => /= [E|Hin]; [by [] | exact: Hin].
  - by move: H5 => /= /List.NoDup_cons_iff [].
  - have El : level (dec_pc_tag pct) = n by rewrite Epct; cbn; lia.
    rewrite El. apply: perm_iota_pop.
    move: H6; rewrite Epct /= => H; exact: H.
  - (* the register file stays total *)
    rewrite /TS.invalidate_ret. apply: regs_dom_set.
    apply: regs_dom_invalidate.
Qed.

End TInv.
