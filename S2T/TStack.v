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


Record ra_slot := RASlot {
  ra_addr : Pointer.t;
  ra_ret  : Pointer.t;
  ra_tag  : value_tag
}.

Definition addrs (S : seq ra_slot) : seq Pointer.t := List.map ra_addr S.

Definition slots_ok (m : mem) (S : seq ra_slot) : Prop :=
  forall s, List.In s S ->
    TMem.vload m (ra_addr s) = Some (Ptr (ra_ret s))
    /\ TMem.tload m (ra_addr s) = Some (ra_tag s)
    /\ TInv.is_live (ra_tag s).

Definition ledger_of (S : seq ra_slot) : TInv.ledger :=
  List.map (fun s => (TInv.CMem (ra_addr s), ra_tag s)) S.

Lemma sites_ledger_of S :
  TInv.sites (ledger_of S) = List.map (fun a => TInv.CMem a) (addrs S).
Proof.
  rewrite /TInv.sites /ledger_of /addrs.
  by elim: S => //= s S ->.
Qed.

Lemma in_addrs_of_slot S s : List.In s S -> List.In (ra_addr s) (addrs S).
Proof. move=> H. exact: (List.in_map ra_addr S s H). Qed.


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



Definition ext_levels (S : seq ra_slot) : seq nat :=
  pmap (fun s => if ra_tag s is Ret n then Some n else None) S.

Definition levels_ok (S : seq ra_slot) (k : nat) : Prop :=
  perm_eq (ext_levels S) (iota 0 k).

Lemma levels_ok_size S k : levels_ok S k -> size (ext_levels S) = k.
Proof. by move=> /perm_size ->; rewrite size_iota. Qed.

Lemma ledger_of_rets S :
  [seq TInv.ret_lvl st.2 | st <- ledger_of S & TInv.is_ret st.2]
  = ext_levels S.
Proof.
  rewrite /ledger_of /ext_levels.
  elim: S => //= s S IH.
  by case: (ra_tag s) => [n| | |] /=; rewrite IH.
Qed.


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

Lemma frame_cap_store m p c m' C fb cap :
  Transitional.Memory.store m p c = Some m' ->
  frame_cap m C fb cap -> frame_cap m' C fb cap.
Proof.
  move=> Hst H j Hj. case: (H j Hj) => [v Hv].
  exact: (TMem.vload_store_total Hst Hv).
Qed.

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


Lemma nth_error_repeat_lt {A : Type} (x : A) n k :
  k < n -> List.nth_error (repeat x n) k = Some x.
Proof. by elim: n k => [|n IH] [|k] //= H; exact: IH. Qed.

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
  -
    exact: Hwfs.
  - exact: Hlocs.
  - exact: Hdoms.
  -
    move=> C0 cm0 HC0. case: (Hdomm C0 cm0 HC0) => [cm1 HC1].
    rewrite Emt setmE. case: (C0 =P C) => [_|_];
      [by eexists | by exists cm1].
  -
    move=> C0 b0 b' i w Hab.
    rewrite (load_alloc_other Ha (Hout _ _ _ i Hab)). exact: Hdata Hab.
Qed.

Lemma tag_inv_alloc L mt rs pct C n mt' b :
  Transitional.Memory.alloc mt C n = Some (mt', (C, b, 0%Z)) ->
  (forall q t, List.In (TInv.CMem q, t) L ->
     Pointer.component q <> C \/ Pointer.block q <> b) ->
  TInv.tag_inv L mt rs pct -> TInv.tag_inv L mt' rs pct.
Proof.
  move=> Ha Hne [H1 H2 H3 H4 H5 H6 H7]; split=> //.
  -
    move=> [q|] t Hin; last exact: H2 Hin.
    rewrite /TInv.tagat (tload_alloc_other Ha); first exact: H2 Hin.
    by move: (Hne q t Hin) => [H|H]; [left | right; rewrite -/(Pointer.block _)].
  -
    move=> q t Hq Hl.
    case: (@eqP _ (Pointer.component q) C) => [EC|HC]; last first.
    { apply: (H4 q t) => //. by rewrite -(tload_alloc_other Ha (or_introl HC)). }
    case: (@eqP _ (Pointer.block q) b) => [EB|HB]; last first.
    { apply: (H4 q t) => //. by rewrite -(tload_alloc_other Ha (or_intror HB)). }
    move: Hq. rewrite (ptr_expand q) EC EB => Hq.
    by move: Hl; rewrite (tload_alloc_in_fresh Ha Hq).
  all: by do ?[apply: TInv.regs_dom_set];
           first [exact: H7 | apply: TInv.regs_dom_invalidate].
Qed.

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
