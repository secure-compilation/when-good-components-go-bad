(* Block-renaming injections for the S2I forward simulation (FCC).

   Source and compiled programs allocate DIFFERENT block ids for the same
   source-level allocation: the compiled code additionally allocates stack
   frames, and its static layout adds the hidden calling-convention block 1.
   The simulation therefore relates memories through a per-component partial
   INJECTIVE block renaming [α] that is the identity on the static-buffer
   block [Block.local] of EVERY component — so static-buffer pointer
   literals (the only pointers well-formed buffers may contain, see
   [Source.well_formed_buffer]) relate to themselves.

   The layer is language-agnostic: it only speaks about [Common.Memory]. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
From extructures Require Import ord fset fmap.

Set Bullet Behavior "Strict Subproofs".
Local Open Scope fset_scope.

(* ==================== renamings ==================== *)

Definition renaming := Component.id -> Block.id -> option Block.id.

Record inj_ok (α : renaming) : Prop := InjOk {
  inj_local : forall C, α C Block.local = Some Block.local;
  inj_injective : forall C b1 b2 b',
      α C b1 = Some b' -> α C b2 = Some b' -> b1 = b2
}.

(* the initial renaming: only the static buffer blocks, identically *)
Definition init_renaming : renaming :=
  fun C b => if b == Block.local then Some Block.local else None.

Lemma init_renaming_ok : inj_ok init_renaming.
Proof.
  split=> [C|C b1 b2 b'].
  - by rewrite /init_renaming eqxx.
  - rewrite /init_renaming.
    by case: (b1 =P Block.local) => [->|] //; case: (b2 =P Block.local) => [->|].
Qed.

(* extension with one fresh pair *)
Definition extend (α : renaming) (C : Component.id) (b b' : Block.id) : renaming :=
  fun C0 b0 => if (C0 == C) && (b0 == b) then Some b' else α C0 b0.

(* renaming inclusion *)
Definition rle (α α' : renaming) : Prop :=
  forall C b b', α C b = Some b' -> α' C b = Some b'.

Lemma rle_refl α : rle α α.
Proof. by []. Qed.

Lemma extend_new α C b b' :
  extend α C b b' C b = Some b'.
Proof. by rewrite /extend !eqxx. Qed.

Lemma extend_rle {α C b b'} :
  α C b = None ->
  rle α (extend α C b b').
Proof.
  move=> Hnone C0 b0 b0' H0. rewrite /extend.
  case E1: (C0 == C) => //=. case E2: (b0 == b) => //=.
  move/eqP: E1 => E1; move/eqP: E2 => E2. subst C0 b0. congruence.
Qed.

Lemma extend_ok {α C b b'} :
  inj_ok α ->
  b != Block.local ->
  α C b = None ->
  (forall b0, α C b0 <> Some b') ->
  inj_ok (extend α C b b').
Proof.
  move=> [Hloc Hinj] Hbl Hnone Hfresh. split.
  - move=> C0. rewrite /extend.
    case E1: (C0 == C) => /=; last exact: Hloc.
    case E2: (Block.local == b) => /=; last exact: Hloc.
    by move/eqP: E2 Hbl => <-; rewrite eqxx.
  - move=> C0 b1 b2 b0'. rewrite /extend.
    case E1: (C0 == C) => /=.
    + move/eqP: E1 => E1; subst C0.
      case E2: (b1 == b) => /=; case E3: (b2 == b) => /=.
      * by move/eqP: E2 => ->; move/eqP: E3 => ->.
      * move=> [<-] Hb2. by case: (Hfresh _ Hb2).
      * move=> Hb1 [E]. rewrite -E in Hb1. by case: (Hfresh _ Hb1).
      * exact: Hinj.
    + exact: Hinj.
Qed.

(* ==================== the value relation ==================== *)

Inductive val_inject (α : renaming) : value -> value -> Prop :=
| VI_int : forall z, val_inject α (Int z) (Int z)
| VI_ptr : forall C b b' o,
    α C b = Some b' ->
    val_inject α (Ptr (C, b, o)) (Ptr (C, b', o))
| VI_undef : val_inject α Undef Undef.

Lemma val_inject_int_l α z v' : val_inject α (Int z) v' -> v' = Int z.
Proof. by move=> H; inversion H. Qed.

Lemma val_inject_ptr_l α C b o v' :
  val_inject α (Ptr (C, b, o)) v' ->
  exists b', α C b = Some b' /\ v' = Ptr (C, b', o).
Proof. move=> H; inversion H; subst. by exists b'. Qed.

Lemma val_inject_rle α α' v v' :
  rle α α' -> val_inject α v v' -> val_inject α' v v'.
Proof.
  move=> Hle H. case: H => [z|C b b' o Ha|]; constructor.
  exact: Hle Ha.
Qed.

(* block-equality tests transfer along an injective renaming *)
Lemma inj_block_eqb {α C b1 b2 b1' b2'} :
  inj_ok α ->
  α C b1 = Some b1' -> α C b2 = Some b2' ->
  Nat.eqb b1 b2 = Nat.eqb b1' b2'.
Proof.
  move=> [_ Hinj] H1 H2.
  case: (PeanoNat.Nat.eqb_spec b1 b2) => [E|NE];
  case: (PeanoNat.Nat.eqb_spec b1' b2') => [E'|NE'] //.
  - subst b2. rewrite H1 in H2. case: H2 => E. by case: (NE' E).
  - subst b2'. by case: (NE (Hinj _ _ _ _ H1 H2)).
Qed.

(* THE closure fact: [eval_binop] respects the relation. *)
Lemma eval_binop_inject α op v1 v1' v2 v2' :
  inj_ok α ->
  val_inject α v1 v1' -> val_inject α v2 v2' ->
  val_inject α (eval_binop op v1 v2) (eval_binop op v1' v2').
Proof.
  move=> Hok H1 H2.
  case: H1 => [z1|C1 b1 b1' o1 Ha1|]; case: H2 => [z2|C2 b2 b2' o2 Ha2|];
    case: op => //=; try by constructor.
  (* Ptr/Ptr: Minus *)
  - case: (PeanoNat.Nat.eqb_spec C1 C2) => [EC|NC] /=; last by constructor.
    subst C2.
    rewrite (inj_block_eqb Hok Ha1 Ha2).
    case: (Nat.eqb b1' b2') => /=; by constructor.
  (* Ptr/Ptr: Eq *)
  - rewrite /Pointer.eq.
    case: (PeanoNat.Nat.eqb_spec C1 C2) => [EC|NC] /=; last by constructor.
    subst C2.
    rewrite (inj_block_eqb Hok Ha1 Ha2).
    case: (Nat.eqb b1' b2') => /=; by constructor.
  (* Ptr/Ptr: Leq *)
  - rewrite /Pointer.leq.
    case: (PeanoNat.Nat.eqb_spec C1 C2) => [EC|NC] /=; last by constructor.
    subst C2.
    rewrite (inj_block_eqb Hok Ha1 Ha2).
    case: (Nat.eqb b1' b2') => /=; by constructor.
Qed.

(* ==================== the memory relation ==================== *)

Definition option_rel {A B : Type} (R : A -> B -> Prop)
           (x : option A) (y : option B) : Prop :=
  match x, y with
  | Some a, Some b => R a b
  | None, None => True
  | _, _ => False
  end.

Record mem_inject (α : renaming) (ms mt : Memory.t) : Prop := MemInject {
  mi_ok : inj_ok α;
  mi_domm : domm ms = domm mt;
  mi_wf_s : forall C cm, getm ms C = Some cm -> ComponentMemory.wf cm;
  mi_wf_t : forall C cm, getm mt C = Some cm -> ComponentMemory.wf cm;
  mi_local_s : forall C cm, getm ms C = Some cm ->
      Block.local \in ComponentMemory.domm cm;
  mi_local_t : forall C cm, getm mt C = Some cm ->
      Block.local \in ComponentMemory.domm cm;
  mi_dom : forall C b b', α C b = Some b' -> b != Block.local ->
      exists cm, getm ms C = Some cm /\ b \in ComponentMemory.domm cm;
  mi_rng : forall C b b', α C b = Some b' -> b != Block.local ->
      exists cm, getm mt C = Some cm /\ b' \in ComponentMemory.domm cm;
  mi_load : forall C b b' i, α C b = Some b' ->
      option_rel (val_inject α)
                 (Memory.load ms (C, b, i)) (Memory.load mt (C, b', i))
}.

(* ---- small fmap helper ---- *)
Lemma domm_setm_existing {T : ordType} {S : Type}
      {m : {fmap T -> S}} {k} {v v0 : S} :
  getm m k = Some v0 -> domm (setm m k v) = domm m.
Proof.
  move=> Hk. apply/eq_fset => x. rewrite domm_set in_fsetU1.
  case: (x =P k) => [->|] //=. by rewrite mem_domm Hk.
Qed.

(* Memory-level: a successful store implies the cell was loadable. *)
Lemma store_some_load_some {ms ptr v ms'} :
  Memory.store ms ptr v = Some ms' ->
  exists w, Memory.load ms ptr = Some w.
Proof.
  rewrite /Memory.store /Memory.load.
  case Hc: (getm ms (Pointer.component ptr)) => [cm|] //.
  case Hs: (ComponentMemory.store cm (Pointer.block ptr) (Pointer.offset ptr) v)
    => [cm'|] // _.
  exact: ComponentMemory.store_load Hs.
Qed.

(* ==================== load transfer ==================== *)

Lemma load_inject {α ms mt C b b' i v} :
  mem_inject α ms mt ->
  α C b = Some b' ->
  Memory.load ms (C, b, i) = Some v ->
  exists v', Memory.load mt (C, b', i) = Some v' /\ val_inject α v v'.
Proof.
  move=> Hm Ha Hl.
  have := mi_load _ _ _ Hm _ _ _ i Ha.
  rewrite Hl. case Hl': (Memory.load mt (C, b', i)) => [v'|] //= HR.
  by exists v'.
Qed.

(* ==================== store transfer ==================== *)

Lemma store_inject {α ms mt C b b' i v v' ms'} :
  mem_inject α ms mt ->
  α C b = Some b' ->
  val_inject α v v' ->
  Memory.store ms (C, b, i) v = Some ms' ->
  exists mt', Memory.store mt (C, b', i) v' = Some mt'
         /\ mem_inject α ms' mt'.
Proof.
  move=> Hm Ha Hv Hs.
  (* the target cell is loadable, hence storable *)
  have [w Hlw] := store_some_load_some Hs.
  have [w' [Hlw' _]] := load_inject Hm Ha Hlw.
  have [mt' Hs'] := Memory.store_after_load mt (C, b', i) w' v' Hlw'.
  exists mt'. split; first exact: Hs'.
  (* dissect the two stores *)
  move: (Hs) (Hs'). rewrite /Memory.store /=.
  case Hcs: (getm ms C) => [cms|] //.
  case Hcs2: (ComponentMemory.store cms b i v) => [cms'|] // [Ems].
  case Hct: (getm mt C) => [cmt|] //.
  case Hct2: (ComponentMemory.store cmt b' i v') => [cmt'|] // [Emt].
  case: (Hm) => Hok Hdomm Hwfs Hwft Hlocs Hloct Hdom Hrng Hload.
  rewrite -Ems -Emt.
  split.
  - exact: Hok.
  - rewrite (domm_setm_existing Hcs) (domm_setm_existing Hct).
    exact: Hdomm.
  - move=> C0 cm0. rewrite setmE. case: (C0 =P C) => [_|_].
    + move=> [<-]. exact: ComponentMemory.wf_store (Hwfs _ _ Hcs) Hcs2.
    + exact: Hwfs.
  - move=> C0 cm0. rewrite setmE. case: (C0 =P C) => [_|_].
    + move=> [<-]. exact: ComponentMemory.wf_store (Hwft _ _ Hct) Hct2.
    + exact: Hwft.
  - move=> C0 cm0. rewrite setmE. case: (C0 =P C) => [_|_].
    + move=> [<-]. rewrite (ComponentMemory.domm_store _ _ _ _ _ Hcs2).
      exact: Hlocs Hcs.
    + exact: Hlocs.
  - move=> C0 cm0. rewrite setmE. case: (C0 =P C) => [_|_].
    + move=> [<-]. rewrite (ComponentMemory.domm_store _ _ _ _ _ Hct2).
      exact: Hloct Hct.
    + exact: Hloct.
  - move=> C0 b0 b0' Ha0 Hb0.
    have [cm0 [Hcm0 Hbin]] := Hdom _ _ _ Ha0 Hb0.
    rewrite setmE. case: (C0 =P C) => [E|_]; last by exists cm0.
    subst C0. rewrite Hcs in Hcm0. case: Hcm0 => E; subst cm0.
    eexists; split; first by [].
    by rewrite (ComponentMemory.domm_store _ _ _ _ _ Hcs2).
  - move=> C0 b0 b0' Ha0 Hb0.
    have [cm0 [Hcm0 Hbin]] := Hrng _ _ _ Ha0 Hb0.
    rewrite setmE. case: (C0 =P C) => [E|_]; last by exists cm0.
    subst C0. rewrite Hct in Hcm0. case: Hcm0 => E; subst cm0.
    eexists; split; first by [].
    by rewrite (ComponentMemory.domm_store _ _ _ _ _ Hct2).
  - move=> C0 b0 b0' j Ha0.
    have Hls := Memory.load_after_store _ _ _ _ (C0, b0, j) Hs.
    have Hlt := Memory.load_after_store _ _ _ _ (C0, b0', j) Hs'.
    rewrite -Ems in Hls. rewrite -Emt in Hlt.
    rewrite Hls Hlt !xpair_eqE.
    case: (C0 =P C) => [EC|NC] /=; last exact: Hload Ha0.
    subst C0.
    case: (b0 =P b) => [EB|NB] /=.
    + subst b0. rewrite Ha0 in Ha. case: Ha => E; subst b0'.
      rewrite eqxx /=.
      case: (j =P i) => [_|NJ] /=; first exact: Hv.
      exact: Hload Ha0.
    + have -> /= : (b0' == b') = false.
      { apply/eqP => E. subst b0'.
        by case: (NB (inj_injective _ Hok _ _ _ _ Ha0 Ha)). }
      exact: Hload Ha0.
Qed.

(* Target-only store at a block OUTSIDE the renaming's range (a
   compiler-owned cell: scratch, flag, or a stack-frame slot). *)
Lemma store_outside_inject {α ms mt ptr v mt'} :
  mem_inject α ms mt ->
  (forall b0, α (Pointer.component ptr) b0 <> Some (Pointer.block ptr)) ->
  Memory.store mt ptr v = Some mt' ->
  mem_inject α ms mt'.
Proof.
  case: ptr => [[Cp bp] op] Hm Hout Hs.
  move: (Hs). rewrite /Memory.store /=.
  case Hct: (getm mt Cp) => [cmt|] //.
  case Hct2: (ComponentMemory.store cmt bp op v) => [cmt'|] // [Emt].
  case: (Hm) => Hok Hdomm Hwfs Hwft Hlocs Hloct Hdom Hrng Hload.
  rewrite -Emt.
  split=> //.
  - by rewrite (domm_setm_existing Hct).
  - move=> C0 cm0. rewrite setmE. case: (C0 =P Cp) => [_|_].
    + move=> [<-]. exact: ComponentMemory.wf_store (Hwft _ _ Hct) Hct2.
    + exact: Hwft.
  - move=> C0 cm0. rewrite setmE. case: (C0 =P Cp) => [_|_].
    + move=> [<-]. rewrite (ComponentMemory.domm_store _ _ _ _ _ Hct2).
      exact: Hloct Hct.
    + exact: Hloct.
  - move=> C0 b0 b0' Ha0 Hb0.
    have [cm0 [Hcm0 Hbin]] := Hrng _ _ _ Ha0 Hb0.
    rewrite setmE. case: (C0 =P Cp) => [E|_]; last by exists cm0.
    subst C0. rewrite Hct in Hcm0. case: Hcm0 => E; subst cm0.
    eexists; split; first by [].
    by rewrite (ComponentMemory.domm_store _ _ _ _ _ Hct2).
  - move=> C0 b0 b0' j Ha0.
    have Hlt := Memory.load_after_store _ _ _ _ (C0, b0', j) Hs.
    rewrite -Emt in Hlt.
    rewrite Hlt !xpair_eqE.
    case: (C0 =P Cp) => [EC|NC] /=; last exact: Hload Ha0.
    subst C0.
    have -> /= : (b0' == bp) = false.
    { apply/eqP => E. subst b0'. by case: (Hout _ Ha0). }
    exact: Hload Ha0.
Qed.

(* ==================== alloc transfer ==================== *)

Lemma alloc_inject {α ms mt C n ms' ptrs} :
  mem_inject α ms mt ->
  Memory.alloc ms C n = Some (ms', ptrs) ->
  exists mt' ptrt bs bt,
    [/\ Memory.alloc mt C n = Some (mt', ptrt),
        ptrs = (C, bs, 0%Z) /\ ptrt = (C, bt, 0%Z),
        rle α (extend α C bs bt),
        extend α C bs bt C bs = Some bt
      & mem_inject (extend α C bs bt) ms' mt'].
Proof.
  move=> Hm Halloc.
  move: (Halloc). rewrite /Memory.alloc.
  case Hcs: (getm ms C) => [cms|] //.
  case Hcs2: (ComponentMemory.alloc cms n) => [cms' bs] [E1 E2].
  have HCt : C \in domm mt by rewrite -(mi_domm _ _ _ Hm) mem_domm Hcs.
  case/dommP: HCt => cmt Hct.
  case Hct2: (ComponentMemory.alloc cmt n) => [cmt' bt].
  exists (setm mt C cmt'), (C, bt, 0%Z), bs, bt.
  case: (Hm) => Hok Hdomm Hwfs Hwft Hlocs Hloct Hdom Hrng Hload.
  (* freshness on both sides *)
  have Hfs : bs \notin ComponentMemory.domm cms
    := ComponentMemory.alloc_fresh _ _ _ _ (Hwfs _ _ Hcs) Hcs2.
  have Hft : bt \notin ComponentMemory.domm cmt
    := ComponentMemory.alloc_fresh _ _ _ _ (Hwft _ _ Hct) Hct2.
  have Hbsl : bs != Block.local.
  { apply/eqP => E. subst bs. by rewrite (Hlocs _ _ Hcs) in Hfs. }
  have Hbtl : bt != Block.local.
  { apply/eqP => E. subst bt. by rewrite (Hloct _ _ Hct) in Hft. }
  have Hnone : α C bs = None.
  { case E: (α C bs) => [x|] //.
    have [cm0 [Hcm0 Hin0]] := Hdom _ _ _ E Hbsl.
    rewrite Hcs in Hcm0. case: Hcm0 => ?; subst cm0.
    by rewrite Hin0 in Hfs. }
  have Hfreshr : forall b0, α C b0 <> Some bt.
  { move=> b0 E.
    case Eb0: (b0 == Block.local).
    - move/eqP: Eb0 => Eb0. subst b0.
      rewrite (inj_local _ Hok _) in E. case: E => E. subst bt.
      by rewrite eqxx in Hbtl.
    - have [cm0 [Hcm0 Hin0]] := Hrng _ _ _ E (negbT Eb0).
      rewrite Hct in Hcm0. case: Hcm0 => ?; subst cm0.
      by rewrite Hin0 in Hft. }
  have Hle : rle α (extend α C bs bt) := extend_rle Hnone.
  have Hok' : inj_ok (extend α C bs bt) := extend_ok Hok Hbsl Hnone Hfreshr.
  have Hmi : mem_inject (extend α C bs bt) (setm ms C cms') (setm mt C cmt').
  { split.
    - exact: Hok'.
    - rewrite (domm_setm_existing Hcs) (domm_setm_existing Hct).
      exact: Hdomm.
    - move=> C0 cm0. rewrite setmE. case: (C0 =P C) => [_|_].
      + move=> [<-]. exact: ComponentMemory.wf_alloc (Hwfs _ _ Hcs) Hcs2.
      + exact: Hwfs.
    - move=> C0 cm0. rewrite setmE. case: (C0 =P C) => [_|_].
      + move=> [<-]. exact: ComponentMemory.wf_alloc (Hwft _ _ Hct) Hct2.
      + exact: Hwft.
    - move=> C0 cm0. rewrite setmE. case: (C0 =P C) => [_|_].
      + move=> [<-]. rewrite (ComponentMemory.domm_alloc_eq _ _ _ _ Hcs2) in_fsetU1.
        by rewrite (Hlocs _ _ Hcs) orbT.
      + exact: Hlocs.
    - move=> C0 cm0. rewrite setmE. case: (C0 =P C) => [_|_].
      + move=> [<-]. rewrite (ComponentMemory.domm_alloc_eq _ _ _ _ Hct2) in_fsetU1.
        by rewrite (Hloct _ _ Hct) orbT.
      + exact: Hloct.
    - move=> C0 b0 b0'. rewrite {1}/extend.
      case EC: (C0 == C) => /=.
      + move/eqP: EC => EC. subst C0.
        case EB: (b0 == bs) => /=.
        * move/eqP: EB => EB. subst b0. move=> _ _.
          rewrite setmE eqxx. eexists; split; first by [].
          by rewrite (ComponentMemory.domm_alloc_eq _ _ _ _ Hcs2) in_fsetU1 eqxx.
        * move=> Ha0 Hb0.
          have [cm0 [Hcm0 Hin0]] := Hdom _ _ _ Ha0 Hb0.
          rewrite setmE eqxx. rewrite Hcs in Hcm0. case: Hcm0 => ?; subst cm0.
          eexists; split; first by [].
          by rewrite (ComponentMemory.domm_alloc_eq _ _ _ _ Hcs2) in_fsetU1 Hin0 orbT.
      + move=> Ha0 Hb0.
        have [cm0 [Hcm0 Hin0]] := Hdom _ _ _ Ha0 Hb0.
        rewrite setmE EC. by exists cm0.
    - move=> C0 b0 b0'. rewrite {1}/extend.
      case EC: (C0 == C) => /=.
      + move/eqP: EC => EC. subst C0.
        case EB: (b0 == bs) => /=.
        * move=> [<-] _.
          rewrite setmE eqxx. eexists; split; first by [].
          by rewrite (ComponentMemory.domm_alloc_eq _ _ _ _ Hct2) in_fsetU1 eqxx.
        * move=> Ha0 Hb0.
          have [cm0 [Hcm0 Hin0]] := Hrng _ _ _ Ha0 Hb0.
          rewrite setmE eqxx. rewrite Hct in Hcm0. case: Hcm0 => ?; subst cm0.
          eexists; split; first by [].
          by rewrite (ComponentMemory.domm_alloc_eq _ _ _ _ Hct2) in_fsetU1 Hin0 orbT.
      + move=> Ha0 Hb0.
        have [cm0 [Hcm0 Hin0]] := Hrng _ _ _ Ha0 Hb0.
        rewrite setmE EC. by exists cm0.
    - (* loads *)
      move=> C0 b0 b0' j.
      rewrite {1}/extend.
      case EC: (C0 == C) => /=.
      + move/eqP: EC => EC. subst C0.
        case EB: (b0 == bs) => /=.
        * (* the fresh pair *)
          move/eqP: EB => EB. subst b0. move=> [<-].
          rewrite /Memory.load /= !setmE eqxx.
          rewrite (ComponentMemory.load_after_alloc_eq _ _ _ _ Hcs2)
                  (ComponentMemory.load_after_alloc_eq _ _ _ _ Hct2).
          case: ((0 <=? j)%Z && (j <? Z.of_nat n)%Z) => //=.
          by constructor.
        * (* old pairs in the allocating component *)
          move=> Ha0.
          have Hb0ne : b0 <> bs by move=> E; rewrite E eqxx in EB.
          have Hb0'ne : b0' <> bt.
          { move=> E. subst b0'. by case: (Hfreshr _ Ha0). }
          have := Hload _ _ _ j Ha0.
          rewrite /Memory.load /= !setmE eqxx Hcs Hct.
          rewrite (ComponentMemory.load_after_alloc _ _ _ _ Hcs2 _ j Hb0ne)
                  (ComponentMemory.load_after_alloc _ _ _ _ Hct2 _ j Hb0'ne).
          case: (ComponentMemory.load cms b0 j) => [w|];
            case: (ComponentMemory.load cmt b0' j) => [w'|] //= HR.
          exact: val_inject_rle Hle HR.
      + (* other components untouched *)
        move=> Ha0.
        have := Hload _ _ _ j Ha0.
        rewrite /Memory.load /= !setmE EC.
        case: (getm ms C0) => [cm0|]; case: (getm mt C0) => [cm0'|] //=.
        case: (ComponentMemory.load cm0 b0 j) => [w|];
          case: (ComponentMemory.load cm0' b0' j) => [w'|] //= HR.
        exact: val_inject_rle Hle HR.
  }
  split.
  - by rewrite /Memory.alloc Hct Hct2.
  - by rewrite -E2.
  - exact: Hle.
  - exact: extend_new.
  - by rewrite -E1.
Qed.

(* Target-only alloc (a stack frame): the relation survives unchanged, and
   the fresh block is outside the renaming's range. *)
Lemma alloc_outside_inject {α ms mt C n mt' ptrt} :
  mem_inject α ms mt ->
  Memory.alloc mt C n = Some (mt', ptrt) ->
  [/\ mem_inject α ms mt',
      Pointer.component ptrt = C, Pointer.offset ptrt = 0%Z
    & forall b0, α C b0 <> Some (Pointer.block ptrt)].
Proof.
  move=> Hm Halloc.
  move: (Halloc). rewrite /Memory.alloc.
  case Hct: (getm mt C) => [cmt|] //.
  case Hct2: (ComponentMemory.alloc cmt n) => [cmt' bt] [E1 E2].
  case: (Hm) => Hok Hdomm Hwfs Hwft Hlocs Hloct Hdom Hrng Hload.
  have Hft : bt \notin ComponentMemory.domm cmt
    := ComponentMemory.alloc_fresh _ _ _ _ (Hwft _ _ Hct) Hct2.
  have Hbtl : bt != Block.local.
  { apply/eqP => E. subst bt. by rewrite (Hloct _ _ Hct) in Hft. }
  have Hfreshr : forall b0, α C b0 <> Some bt.
  { move=> b0 E.
    case Eb0: (b0 == Block.local).
    - move/eqP: Eb0 => Eb0. subst b0.
      rewrite (inj_local _ Hok _) in E. case: E => E. subst bt.
      by rewrite eqxx in Hbtl.
    - have [cm0 [Hcm0 Hin0]] := Hrng _ _ _ E (negbT Eb0).
      rewrite Hct in Hcm0. case: Hcm0 => ?; subst cm0.
      by rewrite Hin0 in Hft. }
  have Hmi : mem_inject α ms (setm mt C cmt').
  { split=> //.
    - by rewrite (domm_setm_existing Hct).
    - move=> C0 cm0. rewrite setmE. case: (C0 =P C) => [_|_].
      + move=> [<-]. exact: ComponentMemory.wf_alloc (Hwft _ _ Hct) Hct2.
      + exact: Hwft.
    - move=> C0 cm0. rewrite setmE. case: (C0 =P C) => [_|_].
      + move=> [<-]. rewrite (ComponentMemory.domm_alloc_eq _ _ _ _ Hct2) in_fsetU1.
        by rewrite (Hloct _ _ Hct) orbT.
      + exact: Hloct.
    - move=> C0 b0 b0' Ha0 Hb0.
      have [cm0 [Hcm0 Hin0]] := Hrng _ _ _ Ha0 Hb0.
      rewrite setmE. case: (C0 =P C) => [E|_]; last by exists cm0.
      subst C0. rewrite Hct in Hcm0. case: Hcm0 => ?; subst cm0.
      eexists; split; first by [].
      by rewrite (ComponentMemory.domm_alloc_eq _ _ _ _ Hct2) in_fsetU1 Hin0 orbT.
    - move=> C0 b0 b0' j Ha0.
      have := Hload _ _ _ j Ha0.
      rewrite /Memory.load /= setmE.
      case EC: (C0 == C) => //=.
      move/eqP: EC => EC. subst C0. rewrite Hct.
      have Hb0'ne : b0' <> bt.
      { move=> E. subst b0'. by case: (Hfreshr _ Ha0). }
      by rewrite (ComponentMemory.load_after_alloc _ _ _ _ Hct2 _ j Hb0'ne).
  }
  rewrite -E1 -E2. by split.
Qed.
