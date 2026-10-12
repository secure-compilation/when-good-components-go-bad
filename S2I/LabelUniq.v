(* Task #14 (I→Merged correctness), T14.3 (partial): LABEL UNIQUENESS of
   compiled code.

   [fresh_label C] returns component C's counter and bumps it, so labels
   emitted while compiling C form a strictly increasing stream.  This file
   proves the interval invariant ([lbl_ok lo hi c]: every ILabel of c lies
   in [lo,hi) and occurs at most once) through [compile_expr], on the way to
   the per-component uniqueness sum the linearizer's Bnz-label resolution
   needs (LinPos's [Huniq] premise). *)

Require Import Common.Definitions.
Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import S2I.CompMonad.
Require Import S2I.Definitions.
Require Import S2I.Compiler.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import zify.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Import MonadNotations.
Open Scope monad_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* the Intermediate-level "is the label-l0 marker" predicate (definitionally
   LinPos.ilab; kept local so S2I does not depend on MicroPolicies) *)
Definition is_ilabel (l0 : nat) (mi : instr) : bool :=
  if mi is ILabel l' then l' == l0 else false.

(* component C's fresh-label counter *)
Definition nlab (s : comp_env) (comp : Component.id) : nat :=
  odflt 0 (getm (next_label s) comp).

Lemma fresh_label_inv (C : Component.id) (s : comp_env) l s' :
  fresh_label C s = Some (l, s') ->
  l = nlab s C /\ nlab s' C = (nlab s C).+1.
Proof.
rewrite fresh_labelE => -[<- <-].
split; first by [].
by rewrite /nlab /= setmE eqxx.
Qed.

(* ==================== the interval invariant ==================== *)

(* labels of c lie in [lo,hi) and each occurs at most once *)
Definition lbl_ok (lo hi : nat) (c : code) : Prop :=
  [/\ (forall l, List.In (ILabel l) c -> lo <= l /\ l < hi)
    & (forall l, count (is_ilabel l) c <= 1)].

Lemma catA_code (a b c : code) : a ++ (b ++ c) = (a ++ b) ++ c.
Proof. by elim: a => //= x a ->. Qed.

Lemma count_ilabel_cat (l : nat) (c1 c2 : code) :
  count (is_ilabel l) (c1 ++ c2)
  = count (is_ilabel l) c1 + count (is_ilabel l) c2.
Proof.
elim: c1 => [|mi c1 IH] //=.
by rewrite IH addnA.
Qed.

Lemma In_count_ilabel (l : nat) (c : code) :
  List.In (ILabel l) c -> 0 < count (is_ilabel l) c.
Proof.
elim: c => [|mi c IH] //= [E|HIn].
- subst mi. rewrite /= eqxx. by lia.
- have := IH HIn. by lia.
Qed.

Lemma count_ilabel_In (l : nat) (c : code) :
  0 < count (is_ilabel l) c -> List.In (ILabel l) c.
Proof.
elim: c => [|mi c IH] //=.
case Emi: (is_ilabel l mi) => /=.
- move=> _. left.
  case: mi Emi => //= l' /eqP ->. by [].
- move=> Hc. right. exact: IH Hc.
Qed.

Lemma lbl_ok_nil (lo hi : nat) : lbl_ok lo hi [::].
Proof. by split=> [l []|l]. Qed.

Lemma lbl_ok_widen (lo' hi' lo hi : nat) (c : code) :
  lo' <= lo -> hi <= hi' -> lbl_ok lo hi c -> lbl_ok lo' hi' c.
Proof.
move=> Hlo Hhi [Hb Hc].
split=> [l HIn|l]; last exact: Hc.
have [H1 H2] := Hb l HIn. by lia.
Qed.

(* code with no labels at all satisfies any interval *)
Lemma lbl_ok_nolab (c : code) :
  (forall l, count (is_ilabel l) c = 0) ->
  forall lo hi, lbl_ok lo hi c.
Proof.
move=> H0 lo hi.
split=> [l HIn|l]; last by rewrite H0.
have := In_count_ilabel HIn.
by rewrite H0.
Qed.

Lemma lbl_ok_label1 (l0 : nat) : lbl_ok l0 l0.+1 [:: ILabel l0].
Proof.
split=> [l [E|[]]|l].
- case: E => <-. by lia.
- rewrite /= addn0 /is_ilabel. by case: (l0 == l).
Qed.

Lemma lbl_ok_cons_nolab (mi : instr) (lo hi : nat) (c : code) :
  (forall l, is_ilabel l mi = false) ->
  lbl_ok lo hi c -> lbl_ok lo hi (mi :: c).
Proof.
move=> Hmi [Hb Hc].
split=> [l [E|HIn]|l].
- exfalso. subst mi.
  have := Hmi l.
  by rewrite /is_ilabel eqxx.
- exact: Hb HIn.
- rewrite /= Hmi. exact: Hc.
Qed.

(* concatenation with DISJOINT label intervals, either order in the code *)
Lemma lbl_ok_cat_disj (lo hi lo1 hi1 lo2 hi2 : nat) (c1 c2 : code) :
  lbl_ok lo1 hi1 c1 -> lbl_ok lo2 hi2 c2 ->
  hi1 <= lo2 \/ hi2 <= lo1 ->
  lo <= lo1 -> lo <= lo2 -> hi1 <= hi -> hi2 <= hi ->
  lbl_ok lo hi (c1 ++ c2).
Proof.
move=> [Hb1 Hc1] [Hb2 Hc2] Hdisj Hl1 Hl2 Hh1 Hh2.
split=> [l HIn|l].
- move/List.in_app_iff: HIn => [HIn|HIn].
  + have [H1 H2] := Hb1 l HIn. by lia.
  + have [H1 H2] := Hb2 l HIn. by lia.
- rewrite count_ilabel_cat.
  case E1: (count (is_ilabel l) c1) => [|n1].
  + have := Hc2 l. by lia.
  + (* l occurs in c1, hence in [lo1,hi1): it cannot also occur in c2 *)
    have HIn1 : List.In (ILabel l) c1.
    { apply: count_ilabel_In. by rewrite E1. }
    have [Hll1 Hlh1] := Hb1 l HIn1.
    case E2: (count (is_ilabel l) c2) => [|n2].
    * have := Hc1 l. rewrite E1. by lia.
    * exfalso.
      have HIn2 : List.In (ILabel l) c2.
      { apply: count_ilabel_In. by rewrite E2. }
      have [Hll2 Hlh2] := Hb2 l HIn2.
      by lia.
Qed.

(* ordered special case *)
Lemma lbl_ok_cat (lo mid hi : nat) (c1 c2 : code) :
  lbl_ok lo mid c1 -> lbl_ok mid hi c2 ->
  lo <= mid -> mid <= hi ->
  lbl_ok lo hi (c1 ++ c2).
Proof.
move=> H1 H2 Hlm Hmh.
apply: (lbl_ok_cat_disj H1 H2); by lia.
Qed.

(* ---- the emitted label-free blocks ---- *)

Lemma lbl_ok_push (r : register) (lo hi : nat) : lbl_ok lo hi (push r).
Proof. by apply: lbl_ok_nolab => l. Qed.

Lemma lbl_ok_pop (r : register) (lo hi : nat) : lbl_ok lo hi (pop r).
Proof. by apply: lbl_ok_nolab => l. Qed.

Lemma lbl_ok_load_arg (b : Pointer.t) (r : register) (lo hi : nat) :
  lbl_ok lo hi (load_arg b r).
Proof. by apply: lbl_ok_nolab => l. Qed.

Lemma lbl_ok_store_arg (b : Pointer.t) (r rt : register) (lo hi : nat) :
  lbl_ok lo hi (store_arg b r rt).
Proof. by apply: lbl_ok_nolab => l. Qed.

(* ==================== one extra (entry) label ==================== *)

(* labels of c are the distinguished [extra] plus an interval, all unique *)
Definition lbl_ok1 (extra lo hi : nat) (c : code) : Prop :=
  [/\ (forall l, List.In (ILabel l) c -> l = extra \/ (lo <= l /\ l < hi))
    & (forall l, count (is_ilabel l) c <= 1)].

Lemma lbl1_widen (lo' hi' extra lo hi : nat) (c : code) :
  lo' <= lo -> hi <= hi' -> lbl_ok1 extra lo hi c -> lbl_ok1 extra lo' hi' c.
Proof.
move=> Hlo Hhi [Hb Hc].
split=> [l HIn|l]; last exact: Hc.
case: (Hb l HIn) => [->|[H1 H2]]; first by left.
right. by lia.
Qed.

Lemma lbl1_cons_nolab (mi : instr) (extra lo hi : nat) (c : code) :
  (forall l, is_ilabel l mi = false) ->
  lbl_ok1 extra lo hi c -> lbl_ok1 extra lo hi (mi :: c).
Proof.
move=> Hmi [Hb Hc].
split=> [l [E|HIn]|l].
- exfalso. subst mi.
  have := Hmi l.
  by rewrite /is_ilabel eqxx.
- exact: Hb HIn.
- rewrite /= Hmi. exact: Hc.
Qed.

(* the tail's labels sit strictly above l0, so prepending ILabel l0 is safe *)
Lemma lbl1_cons_label (extra l0 lo2 hi2 : nat) (c : code) :
  lbl_ok1 extra lo2 hi2 c -> l0 < lo2 -> l0 <> extra -> l0 < hi2 ->
  lbl_ok1 extra l0 hi2 (ILabel l0 :: c).
Proof.
move=> [Hb Hc] Hlt Hne Hlh.
split=> [l [E|HIn]|l].
- case: E => <-. right. split; first by lia.
  by lia.
- case: (Hb l HIn) => [->|[H1 H2]]; first by left.
  right. by lia.
- rewrite /=.
  case El0: (l0 == l) => /=; last exact (Hc l).
  move/eqP: El0 => El0. subst l.
  (* l0 does not occur in c *)
  case Ec: (count (is_ilabel l0) c) => [|n] //.
  exfalso.
  have HIn : List.In (ILabel l0) c.
  { apply: count_ilabel_In. by rewrite Ec. }
  case: (Hb _ HIn) => [E|[H1 H2]]; first exact: Hne E.
  by lia.
Qed.

(* introducing the distinguished label over an interval-only tail *)
Lemma lbl1_cons_extra (extra lo2 hi2 : nat) (c : code) :
  lbl_ok lo2 hi2 c -> extra < lo2 ->
  lbl_ok1 extra lo2 hi2 (ILabel extra :: c).
Proof.
move=> [Hb Hc] Hlt.
split=> [l [E|HIn]|l].
- case: E => <-. by left.
- right. exact: Hb HIn.
- rewrite /=.
  case El0: (extra == l) => /=; last exact (Hc l).
  move/eqP: El0 => El0. subst l.
  case Ec: (count (is_ilabel extra) c) => [|n] //.
  exfalso.
  have HIn : List.In (ILabel extra) c.
  { apply: count_ilabel_In. by rewrite Ec. }
  have [H1 H2] := Hb _ HIn.
  by lia.
Qed.

Lemma lbl1_of_ok (extra lo hi : nat) (c : code) :
  lbl_ok lo hi c -> lbl_ok1 extra lo hi c.
Proof.
move=> [Hb Hc].
split=> [l HIn|l]; last exact: Hc.
right. exact: Hb HIn.
Qed.

Ltac lbl1_step := apply: lbl1_cons_nolab; [by move=> ?|].
Ltac lbl_step0 := apply: lbl_ok_cons_nolab; [by move=> ?|].

(* ==================== compile_expr ==================== *)

Lemma compile_expr_labels (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (e : expr) :
  forall (s : comp_env) (c : code) (s' : comp_env),
  compile_expr C lbp scr P_labels e s = Some (c, s') ->
  nlab s C <= nlab s' C /\ lbl_ok (nlab s C) (nlab s' C) c.
Proof.
elim: e => [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
           |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc.
- (* E_val *)
  case: v Hc => [i|p|] //= [<- <-].
  split; first by [].
  by apply: lbl_ok_nolab => l.
- (* E_arg *)
  move: Hc => /= [<- <-].
  split; first by [].
  by apply: lbl_ok_nolab => l.
- (* E_local *)
  move: Hc => /= [<- <-].
  split; first by [].
  by apply: lbl_ok_nolab => l.
- (* E_binop *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|]; last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|]; last by [].
  rewrite /=. move=> [<- <-].
  have [Hm1 Hok1] := IH1 _ _ _ E1.
  have [Hm2 Hok2] := IH2 _ _ _ E2.
  split; first by lia.
  apply: (lbl_ok_cat_disj Hok1
            (lo2 := nlab s1 C) (hi2 := nlab s2 C)); try by lia.
  apply: (lbl_ok_cat_disj (lbl_ok_push R_COM (nlab s1 C) (nlab s1 C))
            (lo2 := nlab s1 C) (hi2 := nlab s2 C)); try by lia.
  apply: (lbl_ok_cat_disj Hok2
            (lo2 := nlab s2 C) (hi2 := nlab s2 C)); try by lia.
  apply: (lbl_ok_cat_disj (lbl_ok_pop R_AUX1 (nlab s2 C) (nlab s2 C))
            (lo2 := nlab s2 C) (hi2 := nlab s2 C)); try by lia.
  by apply: lbl_ok_nolab => l.
- (* E_seq *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|]; last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|]; last by [].
  rewrite /=. move=> [<- <-].
  have [Hm1 Hok1] := IH1 _ _ _ E1.
  have [Hm2 Hok2] := IH2 _ _ _ E2.
  split; first by lia.
  apply: (lbl_ok_cat Hok1 Hok2); by lia.
- (* E_if *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|]; last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|]; last by [].
  rewrite /=.
  case E3: (compile_expr C lbp scr P_labels e3 s2) => [[c3 s3]|]; last by [].
  rewrite /=.
  case E4: (fresh_label C s3) => [[lconseq s4]|]; last by [].
  rewrite /=.
  case E5: (fresh_label C s4) => [[lend s5]|]; last by [].
  rewrite /=. move=> [<- <-].
  have [Hm1 Hok1] := IH1 _ _ _ E1.
  have [Hm2 Hok2] := IH2 _ _ _ E2.
  have [Hm3 Hok3] := IH3 _ _ _ E3.
  have [Ec4 Hn4] := fresh_label_inv E4.
  have [Ec5 Hn5] := fresh_label_inv E5.
  subst lconseq lend.
  split; first by lia.
  (* code = c1 ++ [IBnz _] ++ c3 ++ [IBnz _; ILabel n3] ++ c2 ++ [ILabel n4];
     label sets: c1 ⊆ [n0,n1), c3 ⊆ [n2,n3), {n3}, c2 ⊆ [n1,n2), {n4} —
     assemble LEFT-grouped so interval hulls stay disjoint at each step *)
  have HM : lbl_ok (nlab s3 C) (nlab s4 C)
              [:: IBnz R_ONE (nlab s4 C); ILabel (nlab s3 C)].
  { apply: lbl_ok_cons_nolab; first by move=> l.
    rewrite Hn4. exact: lbl_ok_label1. }
  have HG1 : lbl_ok (nlab s2 C) (nlab s4 C)
               (c3 ++ [:: IBnz R_ONE (nlab s4 C); ILabel (nlab s3 C)]).
  { apply: (lbl_ok_cat Hok3 HM); by lia. }
  have HG2 : lbl_ok (nlab s1 C) (nlab s4 C)
               ((c3 ++ [:: IBnz R_ONE (nlab s4 C); ILabel (nlab s3 C)]) ++ c2).
  { apply: (lbl_ok_cat_disj HG1 Hok2); by lia. }
  have HG3 : lbl_ok (nlab s1 C) (nlab s5 C)
               (((c3 ++ [:: IBnz R_ONE (nlab s4 C); ILabel (nlab s3 C)]) ++ c2)
                ++ [:: ILabel (nlab s4 C)]).
  { apply: (lbl_ok_cat_disj HG2 (lbl_ok_label1 (nlab s4 C))); by lia. }
  rewrite -!catA_code in HG3.
  apply: (lbl_ok_cat_disj Hok1
            (lbl_ok_cons_nolab (mi := IBnz R_COM (nlab s3 C))
               (fun l => erefl) HG3)); by lia.
- (* E_alloc *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|]; last by [].
  rewrite /=. move=> [<- <-].
  have [Hm1 Hok1] := IH _ _ _ E1.
  split; first by lia.
  apply: (lbl_ok_cat_disj Hok1
            (lo2 := nlab s1 C) (hi2 := nlab s1 C)); try by lia.
  by apply: lbl_ok_nolab => l.
- (* E_deref *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|]; last by [].
  rewrite /=. move=> [<- <-].
  have [Hm1 Hok1] := IH _ _ _ E1.
  split; first by lia.
  apply: (lbl_ok_cat_disj Hok1
            (lo2 := nlab s1 C) (hi2 := nlab s1 C)); try by lia.
  by apply: lbl_ok_nolab => l.
- (* E_assign *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|]; last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|]; last by [].
  rewrite /=. move=> [<- <-].
  have [Hm1 Hok1] := IH1 _ _ _ E1.
  have [Hm2 Hok2] := IH2 _ _ _ E2.
  split; first by lia.
  (* code = c2 ++ push ++ c1 ++ pop ++ [IStore; IMov] — c2's interval is ABOVE c1's *)
  apply: (lbl_ok_cat_disj Hok2
            (lo2 := nlab s C) (hi2 := nlab s1 C)); try by lia.
  apply: (lbl_ok_cat_disj (lbl_ok_push R_COM (nlab s C) (nlab s C))
            (lo2 := nlab s C) (hi2 := nlab s1 C)); try by lia.
  apply: (lbl_ok_cat_disj Hok1
            (lo2 := nlab s1 C) (hi2 := nlab s1 C)); try by lia.
  apply: (lbl_ok_cat_disj (lbl_ok_pop R_AUX1 (nlab s1 C) (nlab s1 C))
            (lo2 := nlab s1 C) (hi2 := nlab s1 C)); try by lia.
  by apply: lbl_ok_nolab => l.
- (* E_call *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|]; last by [].
  rewrite /=.
  case Heqb: (Component.eqb C' C).
  + (* intra-component: Jal to the procedure's entry label *)
    rewrite /find_proc_label /Comp.lift.
    case EL: (getm P_labels P') => [tl|]; last by [].
    rewrite /=. move=> [<- <-].
    have [Hm1 Hok1] := IH _ _ _ E1.
    split; first by lia.
    apply: (lbl_ok_cat_disj Hok1
              (lo2 := nlab s1 C) (hi2 := nlab s1 C)); try by lia.
    apply: (lbl_ok_cat_disj (lbl_ok_push R_RA (nlab s1 C) (nlab s1 C))
              (lo2 := nlab s1 C) (hi2 := nlab s1 C)); try by lia.
    apply: (lbl_ok_cat_disj
              (lbl_ok_cons_nolab (mi := IJal tl)
                 (fun l => erefl) (lbl_ok_nil (nlab s1 C) (nlab s1 C)))
              (lo2 := nlab s1 C) (hi2 := nlab s1 C)); try by lia.
    exact: lbl_ok_pop.
  + (* cross-component call *)
    move=> [<- <-].
    have [Hm1 Hok1] := IH _ _ _ E1.
    split; first by lia.
    apply: (lbl_ok_cat_disj Hok1
              (lo2 := nlab s1 C) (hi2 := nlab s1 C)); try by lia.
    by apply: lbl_ok_nolab => l.
- (* E_exit *)
  move: Hc => /= [<- <-].
  split; first by [].
  by apply: lbl_ok_nolab => l.
Qed.

(* ==================== compile_proc ==================== *)

(* the compiled procedure's labels are its OWN entry label pl (from P_labels,
   below the counter) plus the fresh interval, each occurring at most once *)
Lemma compile_proc_labels (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (P : Procedure.id) (e : expr)
    (s : comp_env) (c : code) (s' : comp_env) (pl : label) :
  getm P_labels P = Some pl ->
  pl < nlab s C ->
  compile_proc C lbp scr P_labels P e s = Some (c, s') ->
  nlab s C <= nlab s' C /\ lbl_ok1 pl (nlab s C) (nlab s' C) c.
Proof.
move=> EL Hpl.
rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift /Comp.ret EL /=.
case E2: (fresh_label C s) => [[lmain s2]|]; last by [].
rewrite /=.
case E3: (fresh_label C s2) => [[lreturn s3]|]; last by [].
rewrite /=.
case E4: (compile_expr C lbp scr P_labels e s3) => [[pcode s4]|]; last by [].
rewrite /=. move=> [<- <-].
have [Em2 En2] := fresh_label_inv E2.
have [Em3 En3] := fresh_label_inv E3.
have [Hm4 Hok4] := compile_expr_labels E4.
subst lmain lreturn.
split; first by lia.
case Hm: (Component.eqb C Component.main && Procedure.eqb P Procedure.main)
  => /=.
- (* main: the external entry defines lmain and lreturn *)
  case Hf: (immediately_final e) => /=; [lbl1_step|];
    (repeat lbl1_step);
    (apply: (lbl1_cons_label (lo2 := nlab s2 C)); [|by lia|by lia|by lia]);
    (repeat lbl1_step);
    (apply: (lbl1_cons_label (lo2 := nlab s3 C)); [|by lia|by lia|by lia]);
    (repeat lbl1_step);
    (apply: lbl1_cons_extra; [|by lia]);
    (repeat lbl_step0);
    (apply: (lbl_ok_cat_disj Hok4
               (lo2 := nlab s4 C) (hi2 := nlab s4 C)); try by lia);
    by apply: lbl_ok_nolab => ?.
- (* non-main *)
  (repeat lbl1_step);
    (apply: lbl1_cons_extra; [|by lia]);
    (repeat lbl_step0);
    (apply: (lbl_ok_cat_disj Hok4
               (lo2 := nlab s4 C) (hi2 := nlab s4 C)); try by lia);
    by apply: lbl_ok_nolab => ?.
Qed.

(* counter monotonicity of one procedure's compilation *)
Lemma compile_proc_mono (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (P : Procedure.id) (e : expr)
    (s : comp_env) (c : code) (s' : comp_env) :
  compile_proc C lbp scr P_labels P e s = Some (c, s') ->
  nlab s C <= nlab s' C.
Proof.
rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift
  /Comp.ret.
case EL: (getm P_labels P) => [pl|]; last by [].
rewrite /=.
case E2: (fresh_label C s) => [[lmain s2]|]; last by [].
rewrite /=.
case E3: (fresh_label C s2) => [[lreturn s3]|]; last by [].
rewrite /=.
case E4: (compile_expr C lbp scr P_labels e s3) => [[pcode s4]|];
  last by [].
rewrite /=. move=> [_ <-].
have [_ En2] := fresh_label_inv E2.
have [_ En3] := fresh_label_inv E3.
have [Hm4 _] := compile_expr_labels E4.
by lia.
Qed.

(* a compiled procedure has an entry label *)
Lemma compile_proc_pl (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (P : Procedure.id) (e : expr)
    (s : comp_env) (c : code) (s' : comp_env) :
  compile_proc C lbp scr P_labels P e s = Some (c, s') ->
  exists pl, getm P_labels P = Some pl.
Proof.
rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift
  /Comp.ret.
case EL: (getm P_labels P) => [pl|]; last by [].
move=> _. by exists pl.
Qed.

(* ==================== label-map generation ==================== *)

(* the generated per-component label map: values below the counter,
   pairwise distinct *)
Definition plm_ok (m : NMap label) (bound : nat) : Prop :=
  [/\ (forall P l, getm m P = Some l -> l < bound)
    & (forall P1 P2 l, getm m P1 = Some l -> getm m P2 = Some l -> P1 = P2)].

Lemma gen_labels_aux_ok (comp : Component.id)
    (ps : list (Procedure.id * expr)) :
  forall (acc : NMap label) (s : comp_env) (m : NMap label) (s' : comp_env),
  gen_component_procedures_labels_aux comp acc ps s = Some (m, s') ->
  plm_ok acc (nlab s comp) ->
  nlab s comp <= nlab s' comp /\ plm_ok m (nlab s' comp).
Proof.
elim: ps => [|[P e] ps IH] acc s m s' /=.
- rewrite /Comp.ret. move=> [<- <-] Hok. by split.
- rewrite /Comp.bind fresh_labelE /=. move=> Hrest [Hb Hinj].
  have Hn1 : nlab {| next_label := setm (next_label s) comp
                       (1 + odflt 0 (getm (next_label s) comp)) |} comp
             = (nlab s comp).+1.
  { by rewrite /nlab /= setmE eqxx. }
  have Hok1 : plm_ok (setm acc P (odflt 0 (getm (next_label s) comp)))
                (nlab {| next_label := setm (next_label s) comp
                           (1 + odflt 0 (getm (next_label s) comp)) |} comp).
  { rewrite Hn1. split.
    - move=> P0 l0. rewrite setmE. case: (P0 == P).
      + move=> [<-]. exact (ltnSn _).
      + move=> HP0. have := Hb _ _ HP0. by lia.
    - move=> P1 P2 l0. rewrite !setmE.
      case E1: (P1 == P); case E2: (P2 == P).
      + move/eqP: E1 => ->. by move/eqP: E2 => ->.
      + move=> [<-] HP2. exfalso.
        have HH := Hb _ _ HP2.
        rewrite /nlab in HH. by rewrite ltnn in HH.
      + move=> HP1 [E]. exfalso.
        rewrite -E in HP1.
        have HH := Hb _ _ HP1.
        rewrite /nlab in HH. by rewrite ltnn in HH.
      + move=> HP1 HP2. exact: Hinj HP1 HP2. }
  have [Hm Hok2] := IH _ _ _ _ Hrest Hok1.
  rewrite Hn1 in Hm.
  split; last exact: Hok2.
  by lia.
Qed.

Lemma gen_component_labels_ok (comp : Component.id)
    (ps : list (Procedure.id * expr)) (s : comp_env)
    (m : NMap label) (s' : comp_env) :
  gen_component_procedures_labels comp ps s = Some (m, s') ->
  nlab s comp <= nlab s' comp /\ plm_ok m (nlab s' comp).
Proof.
move=> Hgen.
apply: (gen_labels_aux_ok Hgen).
split.
- by move=> P l; rewrite emptymE.
- by move=> P1 P2 l; rewrite emptymE.
Qed.

(* the fold does not touch other components' counters *)
Lemma gen_all_frame (cs : list (Component.id * NMap expr)) :
  forall acc s ml s' (K : Component.id),
  gen_all_procedures_labels_aux acc cs s = Some (ml, s') ->
  K \notin unzip1 cs ->
  getm (next_label s') K = getm (next_label s) K.
Proof.
elim: cs => [|[C0 Cprocs0] cs IH] acc s ml s' K /=.
- rewrite /Comp.ret. by move=> [_ <-].
- rewrite /Comp.bind.
  case Eg: (gen_component_procedures_labels C0 (elementsm Cprocs0) s)
    => [[m0 s1]|]; last by [].
  rewrite /=. move=> Hrest.
  rewrite inE negb_or => /andP [HneqK HnotinK].
  rewrite (IH _ _ _ _ _ Hrest HnotinK).
  move/eqP: HneqK => HneqK.
  exact: (gen_component_labels_aux_frame _ _ HneqK _ _ _ _ _ Eg).
Qed.

(* every listed component gets a bounded, injective label map *)
Lemma gen_all_labels_ok (cs : list (Component.id * NMap expr)) :
  forall acc s ml s',
  gen_all_procedures_labels_aux acc cs s = Some (ml, s') ->
  uniq (unzip1 cs) ->
  forall (C : Component.id) (Cprocs : NMap expr), List.In (C, Cprocs) cs ->
  exists plm,
    [/\ getm ml C = Some plm,
        (forall P l, getm plm P = Some l -> l < nlab s' C)
      & (forall P1 P2 l,
           getm plm P1 = Some l -> getm plm P2 = Some l -> P1 = P2)].
Proof.
elim: cs => [|[C0 Cprocs0] cs IH] acc s ml s' //=.
rewrite /Comp.bind.
case Eg: (gen_component_procedures_labels C0 (elementsm Cprocs0) s)
  => [[m0 s1]|]; last by [].
rewrite /=. move=> Hrest /andP [HC0nin Huniq] C Cprocs [E|HIn].
- case: E => ? ?; subst C0 Cprocs0.
  have [Hmono [Hb Hinj]] := gen_component_labels_ok Eg.
  exists m0. split.
  + by rewrite (gen_all_labels_aux_untouched _ _ _ _ _ _ Hrest HC0nin)
               setmE eqxx.
  + move=> P l HP.
    have Hl := Hb _ _ HP.
    have Hfr := gen_all_frame Hrest HC0nin.
    have -> : nlab s' C = nlab s1 C by rewrite /nlab Hfr.
    exact: Hl.
  + exact: Hinj.
- exact: (IH _ _ _ _ Hrest Huniq _ _ HIn).
Qed.

(* ==================== counting helpers ==================== *)

Lemma count_ilabel_0 (l : nat) (c : code) :
  ~ List.In (ILabel l) c -> count (is_ilabel l) c = 0.
Proof.
move=> Hnin.
case Ec: (count (is_ilabel l) c) => [|n] //.
exfalso. apply: Hnin. apply: count_ilabel_In. by rewrite Ec.
Qed.

Lemma sumn_counts0 (l : nat) (acc : list (Procedure.id * code)) :
  (forall P cd, List.In (P, cd) acc -> ~ List.In (ILabel l) cd) ->
  sumn [seq count (is_ilabel l) pc.2 | pc <- acc] = 0.
Proof.
elim: acc => [|[P cd] acc IH] //= H0.
rewrite count_ilabel_0; last by apply: (H0 P cd); left.
rewrite IH //. by move=> P0 cd0 HIn; apply: (H0 P0 cd0); right.
Qed.

(* ==================== the per-component procedures fold ==================== *)

Lemma compile_procedures_aux_labels (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (lo0 : nat)
    (ps : list (Procedure.id * expr)) :
  forall (acc : list (Procedure.id * code)) (s : comp_env)
         (res : list (Procedure.id * code)) (s' : comp_env),
  compile_procedures_aux C lbp scr P_labels acc ps s = Some (res, s') ->
  (forall P l, getm P_labels P = Some l -> l < lo0) ->
  (forall P1 P2 l, getm P_labels P1 = Some l -> getm P_labels P2 = Some l ->
     P1 = P2) ->
  lo0 <= nlab s C ->
  uniq (unzip1 acc ++ unzip1 ps) ->
  (forall P cd l, List.In (P, cd) acc -> List.In (ILabel l) cd ->
     getm P_labels P = Some l \/ (lo0 <= l /\ l < nlab s C)) ->
  (forall l, sumn [seq count (is_ilabel l) pc.2 | pc <- acc] <= 1) ->
  [/\ nlab s C <= nlab s' C,
      uniq (unzip1 res),
      (forall P cd l, List.In (P, cd) res -> List.In (ILabel l) cd ->
         getm P_labels P = Some l \/ (lo0 <= l /\ l < nlab s' C))
    & (forall l, sumn [seq count (is_ilabel l) pc.2 | pc <- res] <= 1)].
Proof.
elim: ps => [|[P e] ps IH] acc s res s' /=.
- rewrite /Comp.ret. move=> [<- <-] Hplb Hplinj Hlo Huniq Hshape Hsums.
  split=> //.
  move: Huniq. by rewrite cats0.
- rewrite /Comp.bind.
  case E1: (compile_proc C lbp scr P_labels P e s) => [[cd s1]|]; last by [].
  rewrite /=. move=> Hrest Hplb Hplinj Hlo Huniq Hshape Hsums.
  (* the successful compile_proc pins P's entry label *)
  have [pl EL] : exists pl, getm P_labels P = Some pl.
  { move: E1. rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift.
    case ELx: (getm P_labels P) => [pl|]; last by [].
    move=> _. by exists pl. }
  have Hpl_lt : pl < nlab s C.
  { have := Hplb _ _ EL. by lia. }
  have [Hmono Hok1] := compile_proc_labels EL Hpl_lt E1.
  case: Hok1 => Hbnd1 Hcnt1.
  have HPnin : P \notin unzip1 acc.
  { move: Huniq. rewrite cat_uniq => /and3P [_ Hhas _].
    move: Hhas => /=. rewrite negb_or => /andP [HP _].
    exact: HP. }
  have Huniq' : uniq (unzip1 ((P, cd) :: acc) ++ unzip1 ps).
  { rewrite /=.
    move: Huniq. rewrite cat_uniq => /and3P [Hu1 Hhas Hu2].
    move: Hhas => /=. rewrite negb_or => /andP [HPa Hhas'].
    move: Hu2 => /= /andP [HPp Hu2'].
    apply/andP; split.
    - rewrite mem_cat negb_or. apply/andP. by split.
    - rewrite cat_uniq. apply/and3P. by split. }
  have Hshape' : forall P0 cd0 l, List.In (P0, cd0) ((P, cd) :: acc) ->
      List.In (ILabel l) cd0 ->
      getm P_labels P0 = Some l \/ (lo0 <= l /\ l < nlab s1 C).
  { move=> P0 cd0 l [E|HIn] HInL.
    - case: E => ? ?; subst P0 cd0.
      case: (Hbnd1 _ HInL) => [->|[H1 H2]]; first by left.
      right. by lia.
    - case: (Hshape _ _ _ HIn HInL) => [HL|[H1 H2]]; first by left.
      right. by lia. }
  have Hsums' : forall l,
      sumn [seq count (is_ilabel l) pc.2 | pc <- (P, cd) :: acc] <= 1.
  { move=> l. rewrite /=.
    case Ecd: (count (is_ilabel l) cd) => [|n].
    - have := Hsums l. by lia.
    - (* l occurs in cd: it occurs nowhere in acc *)
      have HInL : List.In (ILabel l) cd.
      { apply: count_ilabel_In. by rewrite Ecd. }
      have Hacc0 : sumn [seq count (is_ilabel l) pc.2 | pc <- acc] = 0.
      { apply: sumn_counts0 => P0 cd0 HIn0 HInL0.
        case: (Hshape _ _ _ HIn0 HInL0) => [HL0|[Hg1 Hg2]].
        - case: (Hbnd1 _ HInL) => [El|[Hh1 Hh2]].
          + subst l.
            have EP0 : P0 = P := Hplinj _ _ _ HL0 EL.
            subst P0.
            have : P \in unzip1 acc := In_unzip1_mem HIn0.
            by rewrite (negbTE HPnin).
          + have := Hplb _ _ HL0. by lia.
        - case: (Hbnd1 _ HInL) => [El|[Hh1 Hh2]].
          + subst l. have := Hplb _ _ EL. by lia.
          + by lia. }
      rewrite Hacc0.
      have := Hcnt1 l. by lia. }
  have Hlo1 : lo0 <= nlab s1 C by lia.
  have [Hm2 Hu2 Hs2 Hc2]
    := IH _ _ _ _ Hrest Hplb Hplinj Hlo1 Huniq' Hshape' Hsums'.
  split=> //.
  by lia.
Qed.

(* entry point: empty accumulator *)
Lemma compile_procedures_labels (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (lo0 : nat)
    (ps : list (Procedure.id * expr)) (s : comp_env)
    (res : list (Procedure.id * code)) (s' : comp_env) :
  compile_procedures C lbp scr P_labels ps s = Some (res, s') ->
  (forall P l, getm P_labels P = Some l -> l < lo0) ->
  (forall P1 P2 l, getm P_labels P1 = Some l -> getm P_labels P2 = Some l ->
     P1 = P2) ->
  lo0 <= nlab s C ->
  uniq (unzip1 ps) ->
  [/\ uniq (unzip1 res)
    & (forall l, sumn [seq count (is_ilabel l) pc.2 | pc <- res] <= 1)].
Proof.
move=> Hcp Hplb Hplinj Hlo Huniq.
have [_ Hu _ Hc] := compile_procedures_aux_labels Hcp Hplb Hplinj Hlo
                      Huniq (fun P cd l HIn => False_ind _ HIn)
                      (fun l => leq0n 1).
by split.
Qed.

(* ==================== fmap-level accounting ==================== *)

Lemma getm_def_In_uniq (A : Type) (cds : list (nat * A)) (P : nat) (cd : A) :
  uniq (unzip1 cds) -> List.In (P, cd) cds -> getm_def cds P = Some cd.
Proof.
elim: cds => [|[P0 cd0] cds IH] //= /andP [HP0 Hu] [E|HIn].
- case: E => -> ->. by rewrite eqxx.
- case: ifP => [/eqP EP|_]; last exact: IH.
  exfalso. subst P.
  have := In_unzip1_mem HIn.
  by rewrite (negbTE HP0).
Qed.

Lemma sum_unzip1_getm (l : nat) (m : NMap code)
    (cds : list (Procedure.id * code)) :
  (forall P cd, List.In (P, cd) cds -> getm m P = Some cd) ->
  sumn [seq count (is_ilabel l) (odflt [::] (getm m k)) | k <- unzip1 cds]
  = sumn [seq count (is_ilabel l) pc.2 | pc <- cds].
Proof.
elim: cds => [|[P cd] cds IH] //= Hg.
rewrite (Hg P cd); last by left.
rewrite /= IH //.
by move=> P0 cd0 HIn; apply: Hg; right.
Qed.

Lemma sumn_count_mkfmap (l : nat) (cds : list (Procedure.id * code)) :
  uniq (unzip1 cds) ->
  sumn [seq count (is_ilabel l) (odflt [::] (getm (mkfmap cds) k))
       | k <- domm (mkfmap cds)]
  = sumn [seq count (is_ilabel l) pc.2 | pc <- cds].
Proof.
move=> Hu.
have Hgm : forall P cd, List.In (P, cd) cds ->
    getm (mkfmap cds) P = Some cd.
{ move=> P cd HIn. rewrite mkfmapE. exact: getm_def_In_uniq Hu HIn. }
have Hperm : perm_eq (domm (mkfmap cds) : seq _) (unzip1 cds).
{ apply: uniq_perm; [exact: uniq_fset | exact: Hu |].
  move=> k.
  by rewrite mem_domm mkfmapE getm_def_isSome. }
have := perm_map
          (fun k => count (is_ilabel l) (odflt [::] (getm (mkfmap cds) k)))
          Hperm.
move=> /perm_sumn ->.
exact: (sum_unzip1_getm l Hgm).
Qed.

Lemma sumn_count_setm (l : nat) (m : NMap code) (P' : Procedure.id)
    (w : code) :
  P' \notin domm m ->
  count (is_ilabel l) w = 0 ->
  sumn [seq count (is_ilabel l) (odflt [::] (getm (setm m P' w) k))
       | k <- domm (setm m P' w)]
  = sumn [seq count (is_ilabel l) (odflt [::] (getm m k)) | k <- domm m].
Proof.
move=> HP' Hw.
have Hperm : perm_eq (domm (setm m P' w) : seq _) (P' :: domm m).
{ apply: uniq_perm; [exact: uniq_fset | |].
  - rewrite /=. apply/andP. split; [exact: HP' | exact: uniq_fset].
  - move=> k. rewrite in_cons !mem_domm setmE.
    by case: (k == P'). }
have := perm_map
          (fun k => count (is_ilabel l) (odflt [::] (getm (setm m P' w) k)))
          Hperm.
move=> /perm_sumn ->.
rewrite /= setmE eqxx /= Hw add0n.
have -> : [seq count (is_ilabel l) (odflt [::] (getm (setm m P' w) k))
          | k <- domm m]
          = [seq count (is_ilabel l) (odflt [::] (getm m k)) | k <- domm m].
{ apply/eq_in_map => k Hk /=.
  rewrite setmE.
  case E: (k == P') => //.
  move/eqP: E => E. subst k.
  by rewrite Hk in HP'. }
by [].
Qed.

Lemma uniq_unzip1_elementsm (A : Type) (m : NMap A) :
  uniq (unzip1 (elementsm m)).
Proof.
exact: (sorted_uniq (@Ord.lt_trans _) (@Ord.ltxx _) (valP m)).
Qed.

(* ==================== THE theorem ==================== *)

(* compiled programs declare each label at most once per component — the
   [Huniq] premise of the linearizer's Bnz-label resolution (LinPos) *)
Theorem compiled_labels_unique (p : Source.program)
    (tp : Intermediate.program) :
  compile_program p = Some tp ->
  forall (C : Component.id) (Cprocs : NMap code) (l : nat),
    Intermediate.prog_procedures tp C = Some Cprocs ->
    sumn [seq count (is_ilabel l) (odflt [::] (getm Cprocs p'))
         | p' <- domm Cprocs] <= 1.
Proof.
rewrite /compile_program /run /= /Comp.bind /=.
case Eg: (gen_all_procedures_labels
            (elementsm (Source.prog_procedures p)) init_env)
  => [[labels cenv1]|]; last by [].
rewrite /=.
case Ec: (compile_components (gen_buffers (Source.prog_buffers p)) labels
            (elementsm (Source.prog_procedures p)) cenv1)
  => [[codeL cenv2]|]; last by rewrite /=.
rewrite /=.
have Hbase : forall (C : Component.id) (Cprocs : NMap code) (l : nat),
    getm (mkfmap codeL) C = Some Cprocs ->
    sumn [seq count (is_ilabel l) (odflt [::] (getm Cprocs p'))
         | p' <- domm Cprocs] <= 1.
{ move=> C Cprocs l Hget.
  have Hin_cs : C \in unzip1 (elementsm (Source.prog_procedures p)).
  { case Ein: (C \in unzip1 (elementsm (Source.prog_procedures p))) => //.
    have := compile_components_aux_untouched _ _ _ _ _ _ _ _ Ec (negbT Ein).
    move: Hget. rewrite mkfmapE => -> //. }
  have [Cprocs_src HIn] := mem_unzip1_In Hin_cs.
  have Huniq_cs := uniq_unzip1_elementsm (Source.prog_procedures p).
  have [plm [sC [cds [sC' [Hpls Hloc Hcp Hout]]]]]
    := compile_components_aux_getC _ _ _ _ _ _ _ _ _ Ec Huniq_cs HIn.
  (* identify Cprocs with the compiled component map *)
  have Ecp' : Cprocs = mkfmap cds.
  { move: Hget. rewrite mkfmapE Hout. by move=> [->]. }
  subst Cprocs.
  (* the label map's facts, at C's counter after generation *)
  have [plm' [Hpls' Hplb Hplinj]]
    := gen_all_labels_ok Eg Huniq_cs HIn.
  have Eplm : plm' = plm.
  { move: Hpls'. rewrite Hpls. by move=> [->]. }
  subst plm'.
  (* C's counter is untouched between generation and its compilation *)
  have Elo : nlab sC C = nlab cenv1 C by rewrite /nlab Hloc.
  have Hle : nlab cenv1 C <= nlab sC C by rewrite Elo.
  have [Hucds Hsums] := compile_procedures_labels Hcp Hplb Hplinj
                          Hle (uniq_unzip1_elementsm Cprocs_src).
  rewrite (sumn_count_mkfmap l Hucds).
  exact: Hsums. }
(* wrap_main REMOVED: the record is used as built *)
rewrite /Comp.ret. move=> [<-] C Cprocs l /=.
move=> Hget. exact: (Hbase _ _ _ Hget).
Qed.

(* ==================== compiled procedures are nonempty ==================== *)

(* a successful [compile_proc] emits a nonempty body *)
Lemma compile_proc_shape0 (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (P : Procedure.id) (e : expr)
    (s : comp_env) (cd : code) (s' : comp_env) :
  compile_proc C lbp scr P_labels P e s = Some (cd, s') ->
  exists i0, List.nth_error cd 0 = Some i0.
Proof.
rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift.
case ELx: (getm P_labels P) => [pl|]; last by [].
rewrite /= !fresh_labelE /=.
case EE: (compile_expr C lbp scr P_labels e _) => [[pcode s4]|]; last by [].
rewrite /=. move=> [<- _].
cbv zeta.
case: (Component.eqb C Component.main && Procedure.eqb P Procedure.main)
  => /=; last by eexists.
case: (immediately_final e) => /=; by eexists.
Qed.

(* fold-level origin: every produced body comes from a [compile_proc]
   call (or sat in the accumulator) *)
Lemma compile_procedures_aux_origin (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (ps : list (Procedure.id * expr)) :
  forall (acc : list (Procedure.id * code)) (s : comp_env)
         (res : list (Procedure.id * code)) (s' : comp_env),
  compile_procedures_aux C lbp scr P_labels acc ps s = Some (res, s') ->
  forall (P : Procedure.id) (cd : code),
    List.In (P, cd) res ->
    List.In (P, cd) acc
    \/ exists (e : expr) (s0 s1 : comp_env),
        compile_proc C lbp scr P_labels P e s0 = Some (cd, s1).
Proof.
elim: ps => [|[P0 e0] ps IH] acc s res s' /=.
- rewrite /Comp.ret. move=> [<- _] P cd HIn. by left.
- rewrite /Comp.bind.
  case E1: (compile_proc C lbp scr P_labels P0 e0 s) => [[cd0 s1]|];
    last by [].
  rewrite /=. move=> Hrest P cd HIn.
  have [HInacc | Hnew] := IH _ _ _ _ Hrest _ _ HIn; last by right.
  case: HInacc => [Heq | HIn'].
  + case: Heq => <- <-. right. by exists e0, s, s1.
  + by left.
Qed.

(* origin with the fold-start counter bound *)
Lemma compile_procedures_aux_origin' (C : Component.id)
    (lbp scr : Pointer.t) (P_labels : NMap label)
    (ps : list (Procedure.id * expr)) :
  forall (acc : list (Procedure.id * code)) (s : comp_env)
         (res : list (Procedure.id * code)) (s' : comp_env),
  compile_procedures_aux C lbp scr P_labels acc ps s = Some (res, s') ->
  forall (P : Procedure.id) (cd : code),
    List.In (P, cd) res ->
    List.In (P, cd) acc
    \/ exists (e : expr) (s0 s1 : comp_env),
        compile_proc C lbp scr P_labels P e s0 = Some (cd, s1)
        /\ nlab s C <= nlab s0 C.
Proof.
elim: ps => [|[P0 e0] ps IH] acc s res s' /=.
- rewrite /Comp.ret. move=> [<- _] P cd HIn. by left.
- rewrite /Comp.bind.
  case E1: (compile_proc C lbp scr P_labels P0 e0 s) => [[cd0 s1]|];
    last by [].
  rewrite /=. move=> Hrest P cd HIn.
  have [HInacc | [e [s0 [s2 [Hcp Hb]]]]] := IH _ _ _ _ Hrest _ _ HIn.
  + case: HInacc => [Heq | HIn'].
    * case: Heq => <- <-. right. exists e0, s, s1. by split.
    * by left.
  + right. exists e, s0, s2. split=> //.
    have := compile_proc_mono E1. by lia.
Qed.

(* the fold only grows its accumulator *)
Lemma compile_procedures_aux_mono (C : Component.id)
    (lbp scr : Pointer.t) (P_labels : NMap label)
    (ps : list (Procedure.id * expr)) :
  forall (acc : list (Procedure.id * code)) (s : comp_env)
         (res : list (Procedure.id * code)) (s' : comp_env),
  compile_procedures_aux C lbp scr P_labels acc ps s = Some (res, s') ->
  forall x, List.In x acc -> List.In x res.
Proof.
elim: ps => [|[P0 e0] ps IH] acc s res s' /=.
- rewrite /Comp.ret. move=> [<- _] x Hx. exact: Hx.
- rewrite /Comp.bind.
  case E1: (compile_proc C lbp scr P_labels P0 e0 s) => [[cd0 s1]|];
    last by [].
  rewrite /=. move=> Hrest x Hx.
  apply: (IH _ _ _ _ Hrest). by right.
Qed.

(* every source procedure lands in the output with a compile origin *)
Lemma compile_procedures_aux_forward (C : Component.id)
    (lbp scr : Pointer.t) (P_labels : NMap label)
    (ps : list (Procedure.id * expr)) :
  forall (acc : list (Procedure.id * code)) (s : comp_env)
         (res : list (Procedure.id * code)) (s' : comp_env),
  compile_procedures_aux C lbp scr P_labels acc ps s = Some (res, s') ->
  forall (P : Procedure.id) (e : expr),
    List.In (P, e) ps ->
    exists cd s0 s1,
      List.In (P, cd) res
      /\ compile_proc C lbp scr P_labels P e s0 = Some (cd, s1).
Proof.
elim: ps => [|[P0 e0] ps IH] acc s res s' //=.
rewrite /Comp.bind.
case E1: (compile_proc C lbp scr P_labels P0 e0 s) => [[cd0 s1]|];
  last by [].
rewrite /=. move=> Hrest P e [Heq | HIn].
- case: Heq => <- <-.
  exists cd0, s, s1. split=> //.
  apply: (compile_procedures_aux_mono Hrest). by left.
- exact: (IH _ _ _ _ Hrest _ _ HIn).
Qed.

(* the output keys are a permutation of source keys and accumulator *)
Lemma compile_procedures_aux_keys (C : Component.id)
    (lbp scr : Pointer.t) (P_labels : NMap label)
    (ps : list (Procedure.id * expr)) :
  forall (acc : list (Procedure.id * code)) (s : comp_env)
         (res : list (Procedure.id * code)) (s' : comp_env),
  compile_procedures_aux C lbp scr P_labels acc ps s = Some (res, s') ->
  perm_eq (unzip1 res) (unzip1 ps ++ unzip1 acc).
Proof.
elim: ps => [|[P0 e0] ps IH] acc s res s' /=.
- rewrite /Comp.ret. move=> [<- _]. exact: perm_refl.
- rewrite /Comp.bind.
  case E1: (compile_proc C lbp scr P_labels P0 e0 s) => [[cd0 s1]|];
    last by [].
  rewrite /=. move=> Hrest.
  have H := IH _ _ _ _ Hrest.
  apply: (perm_trans H).
  rewrite /=.
  by rewrite -cat1s perm_catCA.
Qed.

(* every compiled procedure of a compiled program is nonempty *)
Theorem compiled_proc_nonempty (p : Source.program)
    (tp : Intermediate.program) :
  compile_program p = Some tp ->
  forall (C : Component.id) (Cprocs : NMap code) (P : Procedure.id)
         (cd : code),
    Intermediate.prog_procedures tp C = Some Cprocs ->
    getm Cprocs P = Some cd ->
    exists i0, List.nth_error cd 0 = Some i0.
Proof.
rewrite /compile_program /run /= /Comp.bind /=.
case Eg: (gen_all_procedures_labels
            (elementsm (Source.prog_procedures p)) init_env)
  => [[labels cenv1]|]; last by [].
rewrite /=.
case Ec: (compile_components (gen_buffers (Source.prog_buffers p)) labels
            (elementsm (Source.prog_procedures p)) cenv1)
  => [[codeL cenv2]|]; last by rewrite /=.
rewrite /=.
have Hbase : forall (C : Component.id) (Cprocs : NMap code)
                    (P : Procedure.id) (cd : code),
    getm (mkfmap codeL) C = Some Cprocs ->
    getm Cprocs P = Some cd ->
    exists i0, List.nth_error cd 0 = Some i0.
{ move=> C Cprocs P cd Hget HgetP.
  have Hin_cs : C \in unzip1 (elementsm (Source.prog_procedures p)).
  { case Ein: (C \in unzip1 (elementsm (Source.prog_procedures p))) => //.
    have := compile_components_aux_untouched _ _ _ _ _ _ _ _ Ec (negbT Ein).
    move: Hget. rewrite mkfmapE => -> //. }
  have [Cprocs_src HIn] := mem_unzip1_In Hin_cs.
  have Huniq_cs := uniq_unzip1_elementsm (Source.prog_procedures p).
  have [plm [sC [cds [sC' [Hpls Hloc Hcp Hout]]]]]
    := compile_components_aux_getC _ _ _ _ _ _ _ _ _ Ec Huniq_cs HIn.
  have Ecp' : Cprocs = mkfmap cds.
  { move: Hget. rewrite mkfmapE Hout. by move=> [->]. }
  subst Cprocs.
  move: HgetP. rewrite mkfmapE => /getm_def_In HInP.
  have [HInnil | [e [s0 [s1 Hcpc]]]]
    := compile_procedures_aux_origin Hcp HInP; first by [].
  exact: compile_proc_shape0 Hcpc. }
(* wrap_main REMOVED: the record is used as built *)
rewrite /Comp.ret. move=> [<-] C Cprocs P cd /=.
move=> Hget HgetP. exact: (Hbase _ _ _ _ Hget HgetP).
Qed.

(* ==================== compiled bodies end in a terminal ==================== *)

(* positions before the trailing element always have successors *)
Lemma nth_error_last_shape (A : Type) (l : list A) (t : A)
    (o : nat) (i : A) :
  List.nth_error (l ++ [:: t]) o = Some i ->
  (exists i', List.nth_error (l ++ [:: t]) o.+1 = Some i') \/ i = t.
Proof.
move=> Hnth.
have Ho' : o < size (l ++ [:: t]).
{ apply/ltP; apply/List.nth_error_Some. by rewrite Hnth. }
move: Ho'; rewrite size_cat /= addn1 ltnS leq_eqVlt
  => /orP[/eqP Heq | Hlt].
- right.
  have Heq' : o = length l := Heq.
  move: Hnth.
  rewrite Heq' List.nth_error_app2; last by apply/leP.
  rewrite Nat.sub_diag /=. by move=> [Eti]; rewrite Eti.
- left.
  have Hlt1 : o.+1 < size (l ++ [:: t])
    by rewrite size_cat /= addn1 ltnS.
  have Hne : List.nth_error (l ++ [:: t]) o.+1 <> None.
  { apply/List.nth_error_Some. by apply/ltP. }
  case E: (List.nth_error (l ++ [:: t]) o.+1) => [i'|];
    first by exists i'.
  by have := Hne E.
Qed.

(* a nonempty list splits off its last element *)
Lemma seq_last_ex (A : Type) (d : A) (l : seq A) :
  l <> [::] -> exists pre, l = pre ++ [:: seq.last d l].
Proof.
case: l => [|a l] // _.
exists (belast a l).
by rewrite /= cats1 -lastI.
Qed.

(* a successful [compile_proc] ends on IJump *)
Lemma compile_proc_lastE (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (P : Procedure.id) (e : expr)
    (s : comp_env) (cd : code) (s' : comp_env) (d : instr) :
  compile_proc C lbp scr P_labels P e s = Some (cd, s') ->
  seq.last d cd = IJump.
Proof.
rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift.
case ELx: (getm P_labels P) => [pl|]; last by [].
rewrite /= !fresh_labelE /=.
case EE: (compile_expr C lbp scr P_labels e _) => [[pcode s4]|]; last by [].
rewrite /=. move=> [<- _].
cbv zeta.
by rewrite !last_cat /= last_cat /=.
Qed.

(* the general origin of every compiled procedure body *)
Theorem compiled_proc_origin (p : Source.program)
    (tp : Intermediate.program) :
  compile_program p = Some tp ->
  forall (C : Component.id) (Cprocs : NMap code) (P : Procedure.id)
         (cd : code),
    Intermediate.prog_procedures tp C = Some Cprocs ->
    getm Cprocs P = Some cd ->
    (exists plm (e : expr) (s0 s1 : comp_env),
        compile_proc C (C, 0, 0%Z) (C, 1, 0%Z) plm P e s0 = Some (cd, s1))
    \/ exists lab, cd = [:: IConst (IInt 1) R_ONE; IJal lab; IHalt].
Proof.
rewrite /compile_program /run /= /Comp.bind /=.
case Eg: (gen_all_procedures_labels
            (elementsm (Source.prog_procedures p)) init_env)
  => [[labels cenv1]|]; last by [].
rewrite /=.
case Ec: (compile_components (gen_buffers (Source.prog_buffers p)) labels
            (elementsm (Source.prog_procedures p)) cenv1)
  => [[codeL cenv2]|]; last by rewrite /=.
rewrite /=.
have Hbase : forall (C : Component.id) (Cprocs : NMap code)
                    (P : Procedure.id) (cd : code),
    getm (mkfmap codeL) C = Some Cprocs ->
    getm Cprocs P = Some cd ->
    exists plm (e : expr) (s0 s1 : comp_env),
      compile_proc C (C, 0, 0%Z) (C, 1, 0%Z) plm P e s0 = Some (cd, s1).
{ move=> C Cprocs P cd Hget HgetP.
  have Hin_cs : C \in unzip1 (elementsm (Source.prog_procedures p)).
  { case Ein: (C \in unzip1 (elementsm (Source.prog_procedures p))) => //.
    have := compile_components_aux_untouched _ _ _ _ _ _ _ _ Ec (negbT Ein).
    move: Hget. rewrite mkfmapE => -> //. }
  have [Cprocs_src HIn] := mem_unzip1_In Hin_cs.
  have Huniq_cs := uniq_unzip1_elementsm (Source.prog_procedures p).
  have [plm [sC [cds [sC' [Hpls Hloc Hcp Hout]]]]]
    := compile_components_aux_getC _ _ _ _ _ _ _ _ _ Ec Huniq_cs HIn.
  have Ecp' : Cprocs = mkfmap cds.
  { move: Hget. rewrite mkfmapE Hout. by move=> [->]. }
  subst Cprocs.
  move: HgetP. rewrite mkfmapE => /getm_def_In HInP.
  have [HInnil | [e [s0 [s1 Hcpc]]]]
    := compile_procedures_aux_origin Hcp HInP; first by [].
  by exists plm, e, s0, s1. }
(* wrap_main REMOVED: the record is used as built *)
rewrite /Comp.ret. move=> [<-] C Cprocs P cd /=.
move=> Hget HgetP. left. exact: (Hbase _ _ _ _ Hget HgetP).
Qed.

(* origin strengthened with the entry label and its counter bound *)
Theorem compiled_proc_origin' (p : Source.program)
    (tp : Intermediate.program) :
  compile_program p = Some tp ->
  forall (C : Component.id) (Cprocs : NMap code) (P : Procedure.id)
         (cd : code),
    Intermediate.prog_procedures tp C = Some Cprocs ->
    getm Cprocs P = Some cd ->
    (exists plm (e : expr) (s0 s1 : comp_env) (pl : label),
        [/\ compile_proc C (C, 0, 0%Z) (C, 1, 0%Z) plm P e s0
              = Some (cd, s1),
            getm plm P = Some pl,
            pl < nlab s0 C
          & forall P' l', getm plm P' = Some l' -> l' < nlab s0 C])
    \/ exists lab, cd = [:: IConst (IInt 1) R_ONE; IJal lab; IHalt].
Proof.
rewrite /compile_program /run /= /Comp.bind /=.
case Eg: (gen_all_procedures_labels
            (elementsm (Source.prog_procedures p)) init_env)
  => [[labels cenv1]|]; last by [].
rewrite /=.
case Ec: (compile_components (gen_buffers (Source.prog_buffers p)) labels
            (elementsm (Source.prog_procedures p)) cenv1)
  => [[codeL cenv2]|]; last by rewrite /=.
rewrite /=.
have Hbase : forall (C : Component.id) (Cprocs : NMap code)
                    (P : Procedure.id) (cd : code),
    getm (mkfmap codeL) C = Some Cprocs ->
    getm Cprocs P = Some cd ->
    exists plm (e : expr) (s0 s1 : comp_env) (pl : label),
      [/\ compile_proc C (C, 0, 0%Z) (C, 1, 0%Z) plm P e s0
            = Some (cd, s1),
          getm plm P = Some pl,
          pl < nlab s0 C
        & forall P' l', getm plm P' = Some l' -> l' < nlab s0 C].
{ move=> C Cprocs P cd Hget HgetP.
  have Hin_cs : C \in unzip1 (elementsm (Source.prog_procedures p)).
  { case Ein: (C \in unzip1 (elementsm (Source.prog_procedures p))) => //.
    have := compile_components_aux_untouched _ _ _ _ _ _ _ _ Ec
              (negbT Ein).
    move: Hget. rewrite mkfmapE => -> //. }
  have [Cprocs_src HIn] := mem_unzip1_In Hin_cs.
  have Huniq_cs := uniq_unzip1_elementsm (Source.prog_procedures p).
  have [plm [sC [cds [sC' [Hpls Hloc Hcp Hout]]]]]
    := compile_components_aux_getC _ _ _ _ _ _ _ _ _ Ec Huniq_cs HIn.
  have [plm' [Hpls' Hbound' _]]
    := gen_all_labels_ok Eg Huniq_cs HIn.
  have Eplm : plm' = plm.
  { move: Hpls'. rewrite Hpls. by move=> [->]. }
  subst plm'.
  have Ecp' : Cprocs = mkfmap cds.
  { move: Hget. rewrite mkfmapE Hout. by move=> [->]. }
  subst Cprocs.
  move: HgetP. rewrite mkfmapE => /getm_def_In HInP.
  have [HInnil | [e [s0 [s1 [Hcpc Hmon]]]]]
    := compile_procedures_aux_origin' Hcp HInP; first by [].
  have [pl Hpl] := compile_proc_pl Hcpc.
  have EnC : nlab sC C = nlab cenv1 C by rewrite /nlab Hloc.
  exists plm, e, s0, s1, pl.
  split=> //.
  - have Hb := Hbound' _ _ Hpl. by lia.
  - move=> P' l' Hg'.
    have Hb := Hbound' _ _ Hg'. by lia. }
(* wrap_main REMOVED: the record is used as built *)
rewrite /Comp.ret. move=> [<-] C Cprocs P cd /=.
move=> Hget HgetP. left. exact: (Hbase _ _ _ _ Hget HgetP).
Qed.

(* component-level origin: one shared label map per component, all its
   values below a bound that every procedure's compile start dominates *)
Theorem compiled_comp_origin (p : Source.program)
    (tp : Intermediate.program) :
  compile_program p = Some tp ->
  forall (C : Component.id) (Cprocs : NMap code),
    Intermediate.prog_procedures tp C = Some Cprocs ->
    exists (plm : NMap label) (nb : nat),
      [/\ (forall P' l', getm plm P' = Some l' -> l' < nb)
        & forall (P : Procedure.id) (cd : code),
            getm Cprocs P = Some cd ->
            (exists (e : expr) (s0 s1 : comp_env) (pl : label),
                [/\ compile_proc C (C, 0, 0%Z) (C, 1, 0%Z) plm P e s0
                      = Some (cd, s1),
                    getm plm P = Some pl
                  & nb <= nlab s0 C])
            \/ exists lab,
                cd = [:: IConst (IInt 1) R_ONE; IJal lab; IHalt]
                /\ getm plm Procedure.main = Some lab].
Proof.
rewrite /compile_program /run /= /Comp.bind /=.
case Eg: (gen_all_procedures_labels
            (elementsm (Source.prog_procedures p)) init_env)
  => [[labels cenv1]|]; last by [].
rewrite /=.
case Ec: (compile_components (gen_buffers (Source.prog_buffers p)) labels
            (elementsm (Source.prog_procedures p)) cenv1)
  => [[codeL cenv2]|]; last by rewrite /=.
rewrite /=.
have Hbase : forall (C : Component.id) (Cprocs : NMap code),
    getm (mkfmap codeL) C = Some Cprocs ->
    exists (plm : NMap label) (nb : nat),
      [/\ getm labels C = Some plm,
          (forall P' l', getm plm P' = Some l' -> l' < nb)
        & forall (P : Procedure.id) (cd : code),
            getm Cprocs P = Some cd ->
            exists (e : expr) (s0 s1 : comp_env) (pl : label),
              [/\ compile_proc C (C, 0, 0%Z) (C, 1, 0%Z) plm P e s0
                    = Some (cd, s1),
                  getm plm P = Some pl
                & nb <= nlab s0 C]].
{ move=> C Cprocs Hget.
  have Hin_cs : C \in unzip1 (elementsm (Source.prog_procedures p)).
  { case Ein: (C \in unzip1 (elementsm (Source.prog_procedures p))) => //.
    have := compile_components_aux_untouched _ _ _ _ _ _ _ _ Ec
              (negbT Ein).
    move: Hget. rewrite mkfmapE => -> //. }
  have [Cprocs_src HIn] := mem_unzip1_In Hin_cs.
  have Huniq_cs := uniq_unzip1_elementsm (Source.prog_procedures p).
  have [plm [sC [cds [sC' [Hpls Hloc Hcp Hout]]]]]
    := compile_components_aux_getC _ _ _ _ _ _ _ _ _ Ec Huniq_cs HIn.
  have [plm' [Hpls' Hbound' _]]
    := gen_all_labels_ok Eg Huniq_cs HIn.
  have Eplm : plm' = plm.
  { move: Hpls'. rewrite Hpls. by move=> [->]. }
  subst plm'.
  have EnC : nlab sC C = nlab cenv1 C by rewrite /nlab Hloc.
  have Ecp' : Cprocs = mkfmap cds.
  { move: Hget. rewrite mkfmapE Hout. by move=> [->]. }
  subst Cprocs.
  exists plm, (nlab cenv1 C).
  split; [exact: Hpls | exact: Hbound' |].
  move=> P cd HgetP.
  move: HgetP. rewrite mkfmapE => /getm_def_In HInP.
  have [HInnil | [e [s0 [s1 [Hcpc Hmon]]]]]
    := compile_procedures_aux_origin' Hcp HInP; first by [].
  have [pl Hpl] := compile_proc_pl Hcpc.
  exists e, s0, s1, pl.
  split=> //.
  by lia. }
(* wrap_main REMOVED: the record is used as built *)
rewrite /Comp.ret. move=> [<-] C Cprocs /=.
move=> Hget.
have [plm [nb [_ Hb Hper]]] := Hbase _ _ Hget.
exists plm, nb.
split; first exact: Hb.
move=> P cd HgetP. left. exact: (Hper _ _ HgetP).
Qed.

(* compiled bodies have a successor after every non-terminal
   instruction (discharges Onext) *)
Theorem compiled_proc_terminal (p : Source.program)
    (tp : Intermediate.program) :
  compile_program p = Some tp ->
  forall (C : Component.id) (Cprocs : NMap code) (P : Procedure.id)
         (cd : code) (o : nat) (i : instr),
    Intermediate.prog_procedures tp C = Some Cprocs ->
    getm Cprocs P = Some cd ->
    List.nth_error cd o = Some i ->
    i <> IHalt -> i <> IReturn -> i <> IJump ->
    exists i', List.nth_error cd o.+1 = Some i'.
Proof.
move=> Hcomp C Cprocs P cd o i Hget HgetP Hnth Hh Hr Hj.
have [[plm [e [s0 [s1 Hcpc]]]] | [lab Ecd]]
  := compiled_proc_origin Hcomp Hget HgetP.
- have Hne : cd <> [::].
  { have [i0 H0] := compile_proc_shape0 Hcpc.
    move=> Ecd. rewrite Ecd in H0. by case: H0. }
  have El : seq.last IJump cd = IJump := compile_proc_lastE IJump Hcpc.
  have [pre Ecd] := seq_last_ex IJump Hne.
  rewrite El in Ecd.
  move: Hnth. rewrite Ecd => Hnth.
  have [Hnext | Ei] := nth_error_last_shape Hnth.
  + exact: Hnext.
  + by have := Hj Ei.
- move: Hnth. rewrite Ecd.
  case: o => [|[|[|o]]] /=.
  + move=> [Ei]. by exists (IJal lab).
  + move=> [Ei]. by exists IHalt.
  + by move=> [Ei]; have := Hh (esym Ei).
  + by move=> Hx; have := List.nth_error_In _ _ Hx.
Qed.

(* ==================== R_RA-freeness of compiled code ==================== *)

(* Compiled instructions never name R_RA in a constrained position: not as
   a Const/Mov/BinOp/Bnz/Alloc operand and not as Load/Store's ADDRESS
   register.  (The MOVED register of Load/Store is R_RA exactly at the
   push/pop-R_RA sites — allowed.)  This is the boolean shape predicate;
   the MicroPolicies side bridges it to [ra_free_instr]. *)

Definition reg_ra_b (r : register) : bool :=
  match r with R_RA => true | _ => false end.

Definition ra_free_b (i : instr) : bool :=
  match i with
  | IConst _ r => ~~ reg_ra_b r
  | IMov r1 r2 => ~~ reg_ra_b r1 && ~~ reg_ra_b r2
  | IBinOp _ r1 r2 r3 =>
      [&& ~~ reg_ra_b r1, ~~ reg_ra_b r2 & ~~ reg_ra_b r3]
  | ILoad r1 _ => ~~ reg_ra_b r1
  | IStore r1 _ => ~~ reg_ra_b r1
  | IBnz r _ => ~~ reg_ra_b r
  | IAlloc rp rs => ~~ reg_ra_b rp && ~~ reg_ra_b rs
  | _ => true
  end.

Definition ra_free_code (c : code) : Prop :=
  List.Forall (fun i => ra_free_b i = true) c.

Lemma ra_free_cat (c1 c2 : code) :
  ra_free_code c1 -> ra_free_code c2 -> ra_free_code (c1 ++ c2).
Proof. move=> H1 H2. apply/List.Forall_app. by split. Qed.

Lemma compile_expr_ra (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (e : expr) :
  forall (s : comp_env) (c : code) (s' : comp_env),
  compile_expr C lbp scr P_labels e s = Some (c, s') ->
  ra_free_code c.
Proof.
elim: e => [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
           |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc.
- (* E_val *)
  case: v Hc => [i|p|] //= [<- _].
  by repeat constructor.
- (* E_arg *)
  move: Hc => /= [<- _].
  by repeat constructor.
- (* E_local *)
  move: Hc => /= [<- _].
  by repeat constructor.
- (* E_binop *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|]; last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|]; last by [].
  rewrite /=. move=> [<- _].
  have Hc1 := IH1 _ _ _ E1.
  have Hc2 := IH2 _ _ _ E2.
  by rewrite /push /pop /=;
     repeat first [ apply List.Forall_nil
                  | constructor; first by []
                  | exact: Hc1 | exact: Hc2
                  | apply: ra_free_cat ].
- (* E_seq *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|]; last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|]; last by [].
  rewrite /=. move=> [<- _].
  exact: (ra_free_cat (IH1 _ _ _ E1) (IH2 _ _ _ E2)).
- (* E_if *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|]; last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|]; last by [].
  rewrite /=.
  case E3: (compile_expr C lbp scr P_labels e3 s2) => [[c3 s3]|]; last by [].
  rewrite /=.
  case E4: (fresh_label C s3) => [[lconseq s4]|]; last by [].
  rewrite /=.
  case E5: (fresh_label C s4) => [[lend s5]|]; last by [].
  rewrite /=. move=> [<- _].
  have Hc1 := IH1 _ _ _ E1.
  have Hc2 := IH2 _ _ _ E2.
  have Hc3 := IH3 _ _ _ E3.
  by rewrite /=;
     repeat first [ apply List.Forall_nil
                  | constructor; first by []
                  | exact: Hc1 | exact: Hc2 | exact: Hc3
                  | apply: ra_free_cat ].
- (* E_alloc *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|]; last by [].
  rewrite /=. move=> [<- _].
  have Hc1 := IH _ _ _ E1.
  by repeat first [ apply List.Forall_nil
                  | constructor; first by []
                  | exact: Hc1
                  | apply: ra_free_cat ].
- (* E_deref *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|]; last by [].
  rewrite /=. move=> [<- _].
  have Hc1 := IH _ _ _ E1.
  by repeat first [ apply List.Forall_nil
                  | constructor; first by []
                  | exact: Hc1
                  | apply: ra_free_cat ].
- (* E_assign *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|]; last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|]; last by [].
  rewrite /=. move=> [<- _].
  have Hc1 := IH1 _ _ _ E1.
  have Hc2 := IH2 _ _ _ E2.
  by rewrite /push /pop /=;
     repeat first [ apply List.Forall_nil
                  | constructor; first by []
                  | exact: Hc1 | exact: Hc2
                  | apply: ra_free_cat ].
- (* E_call *)
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|]; last by [].
  rewrite /=.
  have Hc1 := IH _ _ _ E1.
  case Heqb: (Component.eqb C' C).
  + rewrite /find_proc_label /Comp.lift.
    case EL: (getm P_labels P') => [tl|]; last by [].
    rewrite /=. move=> [<- _].
    by rewrite /push /pop /=;
       repeat first [ apply List.Forall_nil
                    | constructor; first by []
                    | exact: Hc1
                    | apply: ra_free_cat ].
  + move=> [<- _].
    by rewrite /push /pop /load_arg /store_arg /=;
       repeat first [ apply List.Forall_nil
                    | constructor; first by []
                    | exact: Hc1
                    | apply: ra_free_cat ].
- (* E_exit *)
  move: Hc => /= [<- _].
  by repeat constructor.
Qed.

Lemma compile_proc_ra (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (P : Procedure.id) (e : expr)
    (s : comp_env) (c : code) (s' : comp_env) :
  compile_proc C lbp scr P_labels P e s = Some (c, s') ->
  ra_free_code c.
Proof.
rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift /Comp.ret.
case EL: (getm P_labels P) => [pl|]; last by [].
rewrite /=.
case E2: (fresh_label C s) => [[lmain s2]|]; last by [].
rewrite /=.
case E3: (fresh_label C s2) => [[lreturn s3]|]; last by [].
rewrite /=.
case E4: (compile_expr C lbp scr P_labels e s3) => [[pcode s4]|]; last by [].
rewrite /=. move=> [<- _].
have Hc4 := compile_expr_ra E4.
case Hm: (Component.eqb C Component.main && Procedure.eqb P Procedure.main)
  => /=.
- case Hf: (immediately_final e) => /=;
    by rewrite /push /pop /load_arg /store_arg /=;
       repeat first [ apply List.Forall_nil
                    | constructor; first by []
                    | exact: Hc4
                    | apply: ra_free_cat ].
- by rewrite /push /pop /load_arg /store_arg /=;
     repeat first [ apply List.Forall_nil
                  | constructor; first by []
                  | exact: Hc4
                  | apply: ra_free_cat ].
Qed.

(* every instruction of every compiled procedure body is R_RA-free
   (discharges [sr_ra] for compiled sides) *)
Theorem compiled_ra_free (p : Source.program) (tp : Intermediate.program) :
  compile_program p = Some tp ->
  forall (C : Component.id) (Cprocs : NMap code) (P : Procedure.id)
         (cd : code) (o : nat) (i : instr),
    Intermediate.prog_procedures tp C = Some Cprocs ->
    getm Cprocs P = Some cd ->
    List.nth_error cd o = Some i ->
    ra_free_b i = true.
Proof.
move=> Hcomp C Cprocs P cd o i Hget HgetP Hnth.
have Hin := List.nth_error_In _ _ Hnth.
have [[plm [e [s0 [s1 Hcpc]]]] | [lab Ecd]]
  := compiled_proc_origin Hcomp Hget HgetP.
- have Hra := compile_proc_ra Hcpc.
  exact: (proj1 (List.Forall_forall _ _) Hra i Hin).
- rewrite Ecd in Hin.
  by case: Hin => [<-|[<-|[<-|//]]].
Qed.
