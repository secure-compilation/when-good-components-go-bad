Require Import Common.Definitions.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
Require Import Coq.micromega.Lia.

Require Import Intermediate.Machine.
Require Import Source.Language.
Require Import S2I.CompMonad.
Require Import S2I.Definitions.
Require Import S2I.Compiler.
Require Import S2I.LabelUniq.
Require Import MicroPolicies.Recomposition.LinSim.
Require Import MicroPolicies.Recomposition.LinInv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Lemma ra_dead_scan_cat_l (c1 c2 : code) (dead : bool) (o : nat) :
  o <= size c1 ->
  ra_dead_scan (c1 ++ c2) dead o = ra_dead_scan c1 dead o.
Proof.
elim: c1 dead o => [|i c1' IH] dead o /=.
- rewrite leqn0 => /eqP ->.
  by rewrite ra_dead_scan0.
- case: o => [|o] //= Ho.
  exact: IH.
Qed.

Lemma ra_dead_scan_cat_r (c1 c2 : code) (dead : bool) (o : nat) :
  ra_dead_scan (c1 ++ c2) dead (size c1 + o)
  = ra_dead_scan c2 (ra_dead_scan c1 dead (size c1)) o.
Proof.
elim: c1 dead => [|i c1' IH] dead //=.
Qed.

Record frag_ok (c : code) : Prop := FragOk {
  fr_bal : ra_dead_scan c false (size c) = false;
  fr_label : forall o l,
      List.nth_error c o = Some (ILabel l) ->
      ra_dead_scan c false o = false;
  fr_bnz : forall o r l,
      List.nth_error c o = Some (IBnz r l) ->
      ra_dead_scan c false o = false;
  fr_jump : forall o,
      List.nth_error c o = Some IJump ->
      ra_dead_scan c false o = false;
  fr_ret : forall o,
      List.nth_error c o = Some IReturn ->
      ra_dead_scan c false o = false;
  fr_jal : forall o l,
      List.nth_error c o = Some (IJal l) ->
      ra_dead_scan c false o = true;
  fr_call : forall o C' P',
      List.nth_error c o = Some (ICall C' P') ->
      ra_dead_scan c false o = true;
  fr_storera : forall o r,
      List.nth_error c o = Some (IStore r R_RA) ->
      ra_dead_scan c false o = false
}.

Definition frag_cond (i : instr) (dead : bool) : bool :=
  match i with
  | ILabel _ | IBnz _ _ | IJump | IReturn => ~~ dead
  | IStore _ r2 => match r2 with R_RA => ~~ dead | _ => true end
  | IJal _ | ICall _ _ => dead
  | _ => true
  end.

Fixpoint frag_scan_check (c : code) (dead : bool) : bool :=
  match c with
  | [::] => ~~ dead
  | i :: c' => frag_cond i dead && frag_scan_check c' (ra_dead_step i dead)
  end.

Lemma frag_scan_check_sound (c : code) (d : bool) :
  frag_scan_check c d ->
  ra_dead_scan c d (size c) = false
  /\ (forall o i, List.nth_error c o = Some i ->
        frag_cond i (ra_dead_scan c d o)).
Proof.
elim: c d => [|i c' IH] d /=.
- move=> /negbTE Hd.
  split=> //.
  by move=> o i; rewrite List.nth_error_nil.
- case/andP=> Hc /IH [Hbal Hfacts].
  split; first exact: Hbal.
  move=> [|o] i0 /=.
  + move=> [<-].
    exact: Hc.
  + exact: Hfacts.
Qed.

Lemma frag_scan_check_ok (c : code) :
  frag_scan_check c false -> frag_ok c.
Proof.
move=> /frag_scan_check_sound [Hbal Hfacts].
constructor=> //.
- move=> o l Hn. by have := Hfacts _ _ Hn => /= /negbTE.
- move=> o r l Hn. by have := Hfacts _ _ Hn => /= /negbTE.
- move=> o Hn. by have := Hfacts _ _ Hn => /= /negbTE.
- move=> o Hn. by have := Hfacts _ _ Hn => /= /negbTE.
- move=> o l Hn. by have := Hfacts _ _ Hn => /=.
- move=> o C' P' Hn. by have := Hfacts _ _ Hn => /=.
- move=> o r Hn. by have := Hfacts _ _ Hn => /= /negbTE.
Qed.

Lemma nth_error_size (c : code) (o : nat) (i : instr) :
  List.nth_error c o = Some i -> o < size c.
Proof.
elim: c o => [|i0 c' IH] [|o] //=.
move=> /IH Ho.
by [].
Qed.

Lemma frag_ok_cat (c1 c2 : code) :
  frag_ok c1 -> frag_ok c2 -> frag_ok (c1 ++ c2).
Proof.
move=> F1 F2.
have SPLIT : forall (o : nat) (i : instr),
    List.nth_error (c1 ++ c2) o = Some i ->
    (o < size c1 /\ List.nth_error c1 o = Some i
     /\ ra_dead_scan (c1 ++ c2) false o = ra_dead_scan c1 false o)
    \/ (exists o2,
          [/\ o = size c1 + o2, List.nth_error c2 o2 = Some i
            & ra_dead_scan (c1 ++ c2) false o
              = ra_dead_scan c2 false o2]).
{ move=> o i Hnth.
  case: (ltnP o (size c1)) => Ho.
  - left.
    have Hn1 : List.nth_error c1 o = Some i.
    { move: Hnth.
      rewrite List.nth_error_app1 //.
      by apply/ltP. }
    split=> //; split=> //.
    apply: ra_dead_scan_cat_l.
    exact: ltnW.
  - right.
    exists (o - size c1).
    have Eo : o = size c1 + (o - size c1) by rewrite subnKC.
    have Hn2 : List.nth_error c2 (o - size c1) = Some i.
    { move: Hnth.
      rewrite List.nth_error_app2; last by apply/leP.
      by have -> : (o - size c1)%coq_nat = o - size c1 by lia. }
    split=> //.
    rewrite {1}Eo ra_dead_scan_cat_r.
    by rewrite (fr_bal F1). }
constructor.
-
  have -> : size (c1 ++ c2) = size c1 + size c2 by rewrite size_cat.
  rewrite ra_dead_scan_cat_r (fr_bal F1).
  exact: (fr_bal F2).
- move=> o l /SPLIT [[_ [Hn ->]] | [o2 [_ Hn ->]]];
    [exact: (fr_label F1 Hn) | exact: (fr_label F2 Hn)].
- move=> o r l /SPLIT [[_ [Hn ->]] | [o2 [_ Hn ->]]];
    [exact: (fr_bnz F1 Hn) | exact: (fr_bnz F2 Hn)].
- move=> o /SPLIT [[_ [Hn ->]] | [o2 [_ Hn ->]]];
    [exact: (fr_jump F1 Hn) | exact: (fr_jump F2 Hn)].
- move=> o /SPLIT [[_ [Hn ->]] | [o2 [_ Hn ->]]];
    [exact: (fr_ret F1 Hn) | exact: (fr_ret F2 Hn)].
- move=> o l /SPLIT [[_ [Hn ->]] | [o2 [_ Hn ->]]];
    [exact: (fr_jal F1 Hn) | exact: (fr_jal F2 Hn)].
- move=> o C' P' /SPLIT [[_ [Hn ->]] | [o2 [_ Hn ->]]];
    [exact: (fr_call F1 Hn) | exact: (fr_call F2 Hn)].
- move=> o r /SPLIT [[_ [Hn ->]] | [o2 [_ Hn ->]]];
    [exact: (fr_storera F1 Hn) | exact: (fr_storera F2 Hn)].
Qed.

Definition shape_cond (i : instr) (dead : bool) : bool :=
  match i with
  | IJump | IReturn => ~~ dead
  | IStore _ r2 => match r2 with R_RA => ~~ dead | _ => true end
  | IJal _ | ICall _ _ => dead
  | _ => true
  end.

Fixpoint shape_scan_check (c : code) (dead : bool) : bool :=
  match c with
  | [::] => ~~ dead
  | i :: c' =>
      shape_cond i dead && shape_scan_check c' (ra_dead_step i dead)
  end.

Lemma shape_scan_check_sound (c : code) (d : bool) :
  shape_scan_check c d ->
  ra_dead_scan c d (size c) = false
  /\ (forall o i, List.nth_error c o = Some i ->
        shape_cond i (ra_dead_scan c d o)).
Proof.
elim: c d => [|i c' IH] d /=.
- move=> /negbTE Hd.
  split=> //.
  by move=> o i; rewrite List.nth_error_nil.
- case/andP=> Hc /IH [Hbal Hfacts].
  split; first exact: Hbal.
  move=> [|o] i0 /=.
  + move=> [<-].
    exact: Hc.
  + exact: Hfacts.
Qed.

Lemma frag_cond_shape (i : instr) (d : bool) :
  frag_cond i d -> shape_cond i d.
Proof. by case: i => //=. Qed.

Lemma frag_ok_cons (i : instr) (c : code) :
  frag_cond i false ->
  ra_dead_step i false = false ->
  frag_ok c -> frag_ok (i :: c).
Proof.
move=> Hcond Hstep F.
constructor.
- rewrite /= Hstep. exact: (fr_bal F).
- move=> [|o] l //= Hn.
  rewrite Hstep. exact: (fr_label F Hn).
- move=> [|o] r l //= Hn.
  rewrite Hstep. exact: (fr_bnz F Hn).
- move=> [|o] //= Hn.
  rewrite Hstep. exact: (fr_jump F Hn).
- move=> [|o] //= Hn.
  rewrite Hstep. exact: (fr_ret F Hn).
- move=> [|o] l /= Hn; last first.
  + rewrite Hstep. exact: (fr_jal F Hn).
  + case: Hn => Ei. by rewrite Ei in Hcond.
- move=> [|o] C' P' /= Hn; last first.
  + rewrite Hstep. exact: (fr_call F Hn).
  + case: Hn => Ei. by rewrite Ei in Hcond.
- move=> [|o] r //= Hn.
  rewrite Hstep. exact: (fr_storera F Hn).
Qed.

Lemma frag_ok_shape_cond (c : code) :
  frag_ok c ->
  forall o i, List.nth_error c o = Some i ->
    shape_cond i (ra_dead_scan c false o).
Proof.
move=> F o i Hn.
case: i Hn => //=.
- move=> r1 r2 Hn.
  case: r2 Hn => // Hn.
  by rewrite (fr_storera F Hn).
- move=> Hn.
  by rewrite (fr_jump F Hn).
- move=> l Hn.
  by rewrite (fr_jal F Hn).
- move=> C' P' Hn.
  by rewrite (fr_call F Hn).
- move=> Hn.
  by rewrite (fr_ret F Hn).
Qed.

Lemma sandwich_shape_facts (pre body post : code) :
  shape_scan_check pre false ->
  frag_ok body ->
  shape_scan_check post false ->
  forall o i,
    List.nth_error (pre ++ body ++ post) o = Some i ->
    shape_cond i (dead_at (pre ++ body ++ post) o).
Proof.
move=> Hpre Fbody Hpost.
have [HpreB HpreF] := shape_scan_check_sound Hpre.
have [HpostB HpostF] := shape_scan_check_sound Hpost.
have SPLIT2 : forall o i,
    List.nth_error (body ++ post) o = Some i ->
    shape_cond i (ra_dead_scan (body ++ post) false o).
{ move=> o i Hn.
  case: (ltnP o (size body)) => Ho.
  - have Hn1 : List.nth_error body o = Some i.
    { move: Hn. rewrite List.nth_error_app1 //. by apply/ltP. }
    rewrite (ra_dead_scan_cat_l _ _ (ltnW Ho)).
    exact: (frag_ok_shape_cond Fbody Hn1).
  - have Eo : o = size body + (o - size body) by rewrite subnKC.
    have Hn2 : List.nth_error post (o - size body) = Some i.
    { move: Hn.
      rewrite List.nth_error_app2; last by apply/leP.
      by have -> : (o - size body)%coq_nat = o - size body by lia. }
    rewrite Eo ra_dead_scan_cat_r (fr_bal Fbody).
    exact: (HpostF _ _ Hn2). }
move=> o i Hn.
rewrite /dead_at.
case: (ltnP o (size pre)) => Ho.
- have Hn1 : List.nth_error pre o = Some i.
  { move: Hn. rewrite List.nth_error_app1 //. by apply/ltP. }
  rewrite (ra_dead_scan_cat_l _ _ (ltnW Ho)).
  exact: (HpreF _ _ Hn1).
- have Eo : o = size pre + (o - size pre) by rewrite subnKC.
  have Hn2 : List.nth_error (body ++ post) (o - size pre) = Some i.
  { move: Hn.
    rewrite List.nth_error_app2; last by apply/leP.
    by have -> : (o - size pre)%coq_nat = o - size pre by lia. }
  rewrite Eo ra_dead_scan_cat_r HpreB.
  exact: (SPLIT2 _ _ Hn2).
Qed.

Lemma sandwich_at (c pre body post : code) :
  c = pre ++ body ++ post ->
  shape_scan_check pre false ->
  frag_ok body ->
  shape_scan_check post false ->
  forall o i,
    List.nth_error c o = Some i -> shape_cond i (dead_at c o).
Proof.
move=> -> Hpre Fb Hpost.
exact: sandwich_shape_facts.
Qed.

Definition bnz_in (lo hi : nat) (c : code) : Prop :=
  forall r l, List.In (IBnz r l) c -> lo <= l < hi.

Lemma bnz_in_nil (lo hi : nat) : bnz_in lo hi [::].
Proof. by move=> r l []. Qed.

Lemma bnz_in_widen (lo' hi' lo hi : nat) (c : code) :
  lo' <= lo -> hi <= hi' -> bnz_in lo hi c -> bnz_in lo' hi' c.
Proof. move=> Hlo Hhi H r l /H ?; by lia. Qed.

Lemma bnz_in_cat (lo hi : nat) (c1 c2 : code) :
  bnz_in lo hi c1 -> bnz_in lo hi c2 -> bnz_in lo hi (c1 ++ c2).
Proof.
move=> H1 H2 r l HIn.
case: (List.in_app_or _ _ _ HIn); [exact: H1|exact: H2].
Qed.

Lemma bnz_in_cons_nobnz (mi : instr) (lo hi : nat) (c : code) :
  (forall r l, mi <> IBnz r l) ->
  bnz_in lo hi c -> bnz_in lo hi (mi :: c).
Proof.
move=> Hmi H r l [E|HIn]; last exact: H HIn.
exfalso. exact: (Hmi _ _ E).
Qed.

Lemma bnz_in_cons_bnz (r0 : register) (l0 lo hi : nat) (c : code) :
  lo <= l0 < hi -> bnz_in lo hi c -> bnz_in lo hi (IBnz r0 l0 :: c).
Proof.
move=> Hl H r l [E|HIn]; last exact: H HIn.
by case: E => _ <-.
Qed.

Lemma bnz_in_push (r0 : register) (lo hi : nat) :
  bnz_in lo hi (push r0).
Proof. by move=> r l [E|[E|[]]]; case: E. Qed.

Lemma bnz_in_pop (r0 : register) (lo hi : nat) :
  bnz_in lo hi (pop r0).
Proof. by move=> r l [E|[E|[]]]; case: E. Qed.

Fixpoint bnz_free (c : code) : bool :=
  match c with
  | [::] => true
  | IBnz _ _ :: _ => false
  | _ :: c' => bnz_free c'
  end.

Lemma bnz_free_in (lo hi : nat) (c : code) :
  bnz_free c = true -> bnz_in lo hi c.
Proof.
elim: c => [|mi c IH]; first by move=> _; exact: bnz_in_nil.
by case: mi => /=;
  try by move=> *; apply: bnz_in_cons_nobnz => //; apply: IH.
Qed.

Lemma compile_expr_bnz (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (e : expr) :
  forall (s : comp_env) (c : code) (s' : comp_env),
  compile_expr C lbp scr P_labels e s = Some (c, s') ->
  bnz_in (nlab s C) (nlab s' C) c.
Proof.
elim: e => [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
           |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc.
-
  case: v Hc => [i|p|] //= [<- <-]; by apply: bnz_free_in.
-
  move: Hc => /= [<- <-]. by apply: bnz_free_in.
-
  move: Hc => /= [<- <-]. by apply: bnz_free_in.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- <-].
  have [Hm1 _] := compile_expr_labels E1.
  have [Hm2 _] := compile_expr_labels E2.
  apply: bnz_in_cat.
  { apply: (bnz_in_widen _ _ (IH1 _ _ _ E1)); by lia. }
  apply: bnz_in_cons_nobnz => //.
  apply: bnz_in_cons_nobnz => //.
  apply: bnz_in_cat.
  { apply: (bnz_in_widen _ _ (IH2 _ _ _ E2)); by lia. }
  by apply: bnz_free_in.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- <-].
  have [Hm1 _] := compile_expr_labels E1.
  have [Hm2 _] := compile_expr_labels E2.
  apply: bnz_in_cat.
  { apply: (bnz_in_widen _ _ (IH1 _ _ _ E1)); by lia. }
  apply: (bnz_in_widen _ _ (IH2 _ _ _ E2)); by lia.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=.
  case E3: (compile_expr C lbp scr P_labels e3 s2) => [[c3 s3]|];
    last by [].
  rewrite /=.
  case E4: (fresh_label C s3) => [[lconseq s4]|]; last by [].
  rewrite /=.
  case E5: (fresh_label C s4) => [[lend s5]|]; last by [].
  rewrite /=. move=> [<- <-].
  have [Hm1 _] := compile_expr_labels E1.
  have [Hm2 _] := compile_expr_labels E2.
  have [Hm3 _] := compile_expr_labels E3.
  have [Ec4 Hn4] := fresh_label_inv E4.
  have [Ec5 Hn5] := fresh_label_inv E5.
  subst lconseq lend.
  apply: bnz_in_cat.
  { apply: (bnz_in_widen _ _ (IH1 _ _ _ E1)); by lia. }
  apply: bnz_in_cons_bnz; first by lia.
  apply: bnz_in_cat.
  { apply: (bnz_in_widen _ _ (IH3 _ _ _ E3)); by lia. }
  apply: bnz_in_cons_bnz; first by lia.
  apply: bnz_in_cons_nobnz => //.
  apply: bnz_in_cat.
  { apply: (bnz_in_widen _ _ (IH2 _ _ _ E2)); by lia. }
  by apply: bnz_free_in.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=. move=> [<- <-].
  apply: bnz_in_cat; first exact: (IH _ _ _ E1).
  by apply: bnz_free_in.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=. move=> [<- <-].
  apply: bnz_in_cat; first exact: (IH _ _ _ E1).
  by apply: bnz_free_in.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- <-].
  have [Hm1 _] := compile_expr_labels E1.
  have [Hm2 _] := compile_expr_labels E2.
  apply: bnz_in_cat.
  { apply: (bnz_in_widen _ _ (IH2 _ _ _ E2)); by lia. }
  apply: bnz_in_cons_nobnz => //.
  apply: bnz_in_cons_nobnz => //.
  apply: bnz_in_cat.
  { apply: (bnz_in_widen _ _ (IH1 _ _ _ E1)); by lia. }
  by apply: bnz_free_in.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case Heqb: (Component.eqb C' C).
  + rewrite /find_proc_label /Comp.lift.
    case EL: (getm P_labels P') => [tl|]; last by [].
    rewrite /=. move=> [<- <-].
    apply: bnz_in_cat; first exact: (IH _ _ _ E1).
    by apply: bnz_free_in.
  + move=> [<- <-].
    apply: bnz_in_cat; first exact: (IH _ _ _ E1).
    by apply: bnz_free_in.
-
  move: Hc => /= [<- <-]. by apply: bnz_free_in.
Qed.

Fixpoint bnz_ops (c : code) : seq nat :=
  match c with
  | [::] => [::]
  | IBnz _ l :: c' => l :: bnz_ops c'
  | _ :: c' => bnz_ops c'
  end.

Lemma In_bnz_ops (r : register) (l : nat) (c : code) :
  List.In (IBnz r l) c -> List.In l (bnz_ops c).
Proof.
elim: c => [|mi c IH] //= [E|HIn].
- subst mi. by left.
- case: mi => //= *; try exact: IH HIn.
  right. exact: IH HIn.
Qed.

Fixpoint lab_vals (c : code) : seq nat :=
  match c with
  | [::] => [::]
  | ILabel l :: c' => l :: lab_vals c'
  | _ :: c' => lab_vals c'
  end.

Lemma In_lab_vals (l : nat) (c : code) :
  List.In (ILabel l) c -> List.In l (lab_vals c).
Proof.
elim: c => [|mi c IH] //= [E|HIn].
- subst mi. by left.
- case: mi => //= *; try exact: IH HIn.
  right. exact: IH HIn.
Qed.

Lemma bnz_ops_cat (c1 c2 : code) :
  bnz_ops (c1 ++ c2) = bnz_ops c1 ++ bnz_ops c2.
Proof. by elim: c1 => [|mi c1 IH] //=; case: mi => //= *; rewrite IH. Qed.

Lemma lab_vals_cat (c1 c2 : code) :
  lab_vals (c1 ++ c2) = lab_vals c1 ++ lab_vals c2.
Proof. by elim: c1 => [|mi c1 IH] //=; case: mi => //= *; rewrite IH. Qed.

Fixpoint class_check (test : instr -> bool) (want : bool) (c : code)
    (dead : bool) : bool :=
  match c with
  | [::] => true
  | i :: c' =>
      (if test i then dead == want else true)
      && class_check test want c' (ra_dead_step i dead)
  end.

Lemma class_check_sound (test : instr -> bool) (want : bool) (c : code) :
  forall (d : bool) (o : nat) (i : instr),
  class_check test want c d = true ->
  List.nth_error c o = Some i ->
  test i = true ->
  ra_dead_scan c d o = want.
Proof.
elim: c => [|mi c IH] d o i.
- by rewrite List.nth_error_nil.
- move=> /andP [Hhead Hrest].
  case: o => [|o'] /=.
  + move=> [<-] Ht.
    move: Hhead. rewrite Ht.
    by move/eqP => <-.
  + move=> Hnth Ht. exact: (IH _ _ _ Hrest Hnth Ht).
Qed.

Lemma class_check_cat (test : instr -> bool) (want : bool)
    (c1 c2 : code) (d : bool) :
  class_check test want (c1 ++ c2) d
  = class_check test want c1 d
    && class_check test want c2 (ra_dead_scan c1 d (size c1)).
Proof.
elim: c1 d => [|mi c1 IH] d /=.
- by [].
- by rewrite IH andbA.
Qed.

Lemma sandwich_bnz_label (pre body post : code) (lo hi : nat) :
  ra_dead_scan pre false (size pre) = false ->
  frag_ok body ->
  bnz_in lo hi body ->
  (forall l, List.In (ILabel l) body -> lo <= l < hi) ->
  (forall l, List.In l (bnz_ops pre) -> l < lo) ->
  (forall l, List.In l (lab_vals pre) -> l < lo) ->
  bnz_ops post = [::] ->
  lab_vals post = [::] ->
  (forall o o' r l,
      List.nth_error pre o = Some (IBnz r l) ->
      List.nth_error pre o' = Some (ILabel l) ->
      dead_at pre o' = dead_at pre o) ->
  forall o o' r l,
    List.nth_error (pre ++ body ++ post) o = Some (IBnz r l) ->
    List.nth_error (pre ++ body ++ post) o' = Some (ILabel l) ->
    dead_at (pre ++ body ++ post) o' = dead_at (pre ++ body ++ post) o.
Proof.
move=> Hbal F Hbnzb Hlabb Hbnzp Hlabp Hbnzpost Hlabpost Hpair
  o o' r l Ho Ho'.
rewrite /dead_at.
have Hbn : (o < size pre /\ List.nth_error pre o = Some (IBnz r l))
           \/ (exists ob, [/\ o = size pre + ob, ob < size body
                 & List.nth_error body ob = Some (IBnz r l)]).
{ case: (ltnP o (size pre)) => Hlt.
  - left. split=> //.
    move: Ho. rewrite List.nth_error_app1 //. by apply/ltP.
  - right.
    have Eo : o = size pre + (o - size pre) by rewrite subnKC.
    have Hb2 : List.nth_error (body ++ post) (o - size pre)
               = Some (IBnz r l).
    { move: Ho.
      rewrite List.nth_error_app2; last by apply/leP.
      by have -> : (o - size pre)%coq_nat = o - size pre by lia. }
    case: (ltnP (o - size pre) (size body)) => Hlt2.
    + exists (o - size pre). split=> //.
      move: Hb2. rewrite List.nth_error_app1 //. by apply/ltP.
    + exfalso.
      have Hb3 : List.nth_error post (o - size pre - size body)
                 = Some (IBnz r l).
      { move: Hb2.
        rewrite List.nth_error_app2; last by apply/leP.
        by have -> : (o - size pre - size body)%coq_nat
                     = o - size pre - size body by lia. }
      have := In_bnz_ops (List.nth_error_In _ _ Hb3).
      by rewrite Hbnzpost. }
have Hlb : (o' < size pre /\ List.nth_error pre o' = Some (ILabel l))
           \/ (exists ob', [/\ o' = size pre + ob', ob' < size body
                 & List.nth_error body ob' = Some (ILabel l)]).
{ case: (ltnP o' (size pre)) => Hlt.
  - left. split=> //.
    move: Ho'. rewrite List.nth_error_app1 //. by apply/ltP.
  - right.
    have Eo : o' = size pre + (o' - size pre) by rewrite subnKC.
    have Hb2 : List.nth_error (body ++ post) (o' - size pre)
               = Some (ILabel l).
    { move: Ho'.
      rewrite List.nth_error_app2; last by apply/leP.
      by have -> : (o' - size pre)%coq_nat = o' - size pre by lia. }
    case: (ltnP (o' - size pre) (size body)) => Hlt2.
    + exists (o' - size pre). split=> //.
      move: Hb2. rewrite List.nth_error_app1 //. by apply/ltP.
    + exfalso.
      have Hb3 : List.nth_error post (o' - size pre - size body)
                 = Some (ILabel l).
      { move: Hb2.
        rewrite List.nth_error_app2; last by apply/leP.
        by have -> : (o' - size pre - size body)%coq_nat
                     = o' - size pre - size body by lia. }
      have := In_lab_vals (List.nth_error_In _ _ Hb3).
      by rewrite Hlabpost. }
case: Hbn => [[Hlt1 Hp1]|[ob [Eo Hltb Hp1]]];
  case: Hlb => [[Hlt1' Hp1']|[ob' [Eo' Hltb' Hp1']]].
-
  rewrite (ra_dead_scan_cat_l _ _ (ltnW Hlt1)).
  rewrite (ra_dead_scan_cat_l _ _ (ltnW Hlt1')).
  exact: (Hpair _ _ _ _ Hp1 Hp1').
-
  exfalso.
  have Hlow := Hbnzp _ (In_bnz_ops (List.nth_error_In _ _ Hp1)).
  have Hhigh := Hlabb _ (List.nth_error_In _ _ Hp1').
  by lia.
-
  exfalso.
  have Hlow := Hlabp _ (In_lab_vals (List.nth_error_In _ _ Hp1')).
  have Hhigh := Hbnzb _ _ (List.nth_error_In _ _ Hp1).
  by lia.
-
  rewrite Eo Eo' !ra_dead_scan_cat_r Hbal.
  rewrite (ra_dead_scan_cat_l _ _ (ltnW Hltb)).
  rewrite (ra_dead_scan_cat_l _ _ (ltnW Hltb')).
  by rewrite (fr_label F Hp1') (fr_bnz F Hp1).
Qed.

Lemma sandwich_bnz_label_at (c pre body post : code) (lo hi : nat) :
  c = pre ++ body ++ post ->
  ra_dead_scan pre false (size pre) = false ->
  frag_ok body ->
  bnz_in lo hi body ->
  (forall l, List.In (ILabel l) body -> lo <= l < hi) ->
  (forall l, List.In l (bnz_ops pre) -> l < lo) ->
  (forall l, List.In l (lab_vals pre) -> l < lo) ->
  bnz_ops post = [::] ->
  lab_vals post = [::] ->
  (forall o o' r l,
      List.nth_error pre o = Some (IBnz r l) ->
      List.nth_error pre o' = Some (ILabel l) ->
      dead_at pre o' = dead_at pre o) ->
  forall o o' r l,
    List.nth_error c o = Some (IBnz r l) ->
    List.nth_error c o' = Some (ILabel l) ->
    dead_at c o' = dead_at c o.
Proof. move=> ->. exact: sandwich_bnz_label. Qed.

Definition is_bnz_to (l0 : nat) (i : instr) : bool :=
  match i with IBnz _ l => l == l0 | _ => false end.

Definition is_lab_of (l0 : nat) (i : instr) : bool :=
  match i with ILabel l => l == l0 | _ => false end.

Definition ext_wrap (lm lr pl : label) (scr : Pointer.t) (sfz : Z)
  : code :=
  [:: IConst (IInt 1) R_ONE] ++
  [:: IMov R_SP R_AUX1; IConst (IInt sfz) R_SP; IAlloc R_SP R_SP] ++
  push R_AUX1 ++ push R_RA ++
  [:: IConst (IPtr (flag_buf_ptr scr)) R_AUX1; ILoad R_AUX1 R_AUX2] ++
  push R_AUX2 ++
  [:: IBnz R_AUX2 lm; IConst (IInt 0) R_COM; ILabel lm;
      IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2; IJal pl] ++
  pop R_AUX1 ++ pop R_RA ++ pop R_SP ++
  [:: IBnz R_AUX1 lr; IHalt; ILabel lr; IReturn] ++
  [:: ILabel pl; IMov R_SP R_AUX1; IConst (IInt sfz) R_SP;
      IAlloc R_SP R_SP] ++
  push R_AUX1 ++ load_arg scr R_AUX1 ++ push R_AUX1 ++ push R_ARG ++
  [:: IMov R_COM R_ARG].

Lemma ext_wrap_pair (lm lr pl : label) (scr : Pointer.t) (sfz : Z) :
  (lr == lm) = false -> (lm == lr) = false ->
  (pl == lm) = false -> (pl == lr) = false ->
  forall o o' r l,
    List.nth_error (ext_wrap lm lr pl scr sfz) o = Some (IBnz r l) ->
    List.nth_error (ext_wrap lm lr pl scr sfz) o' = Some (ILabel l) ->
    dead_at (ext_wrap lm lr pl scr sfz) o'
    = dead_at (ext_wrap lm lr pl scr sfz) o.
Proof.
move=> Mrm Mmr Mpm Mpr o o' r l Hp Hp'.
have CHbm : class_check (is_bnz_to lm) true
              (ext_wrap lm lr pl scr sfz) false = true.
{ by rewrite /= ?eqxx ?Mrm ?Mmr ?Mpm ?Mpr. }
have CHlm : class_check (is_lab_of lm) true
              (ext_wrap lm lr pl scr sfz) false = true.
{ by rewrite /= ?eqxx ?Mrm ?Mmr ?Mpm ?Mpr. }
have CHbr : class_check (is_bnz_to lr) false
              (ext_wrap lm lr pl scr sfz) false = true.
{ by rewrite /= ?eqxx ?Mrm ?Mmr ?Mpm ?Mpr. }
have CHlr : class_check (is_lab_of lr) false
              (ext_wrap lm lr pl scr sfz) false = true.
{ by rewrite /= ?eqxx ?Mrm ?Mmr ?Mpm ?Mpr. }
have := In_bnz_ops (List.nth_error_In _ _ Hp).
move=> /= [El|[El|[]]]; subst l.
- rewrite /dead_at.
  have Hd' : ra_dead_scan (ext_wrap lm lr pl scr sfz) false o' = true.
  { apply: class_check_sound;
      [exact: CHlm | exact: Hp' | exact: (eqxx _)]. }
  have Hd : ra_dead_scan (ext_wrap lm lr pl scr sfz) false o = true.
  { apply: class_check_sound;
      [exact: CHbm | exact: Hp | exact: (eqxx _)]. }
  by rewrite Hd Hd'.
- rewrite /dead_at.
  have Hd' : ra_dead_scan (ext_wrap lm lr pl scr sfz) false o' = false.
  { apply: class_check_sound;
      [exact: CHlr | exact: Hp' | exact: (eqxx _)]. }
  have Hd : ra_dead_scan (ext_wrap lm lr pl scr sfz) false o = false.
  { apply: class_check_sound;
      [exact: CHbr | exact: Hp | exact: (eqxx _)]. }
  by rewrite Hd Hd'.
Qed.

Lemma pair_cons_skip (mi : instr) (c : code) :
  ra_dead_step mi = id ->
  (forall r l, mi <> IBnz r l) ->
  (forall l, mi <> ILabel l) ->
  (forall o o' r l,
      List.nth_error c o = Some (IBnz r l) ->
      List.nth_error c o' = Some (ILabel l) ->
      dead_at c o' = dead_at c o) ->
  forall o o' r l,
    List.nth_error (mi :: c) o = Some (IBnz r l) ->
    List.nth_error (mi :: c) o' = Some (ILabel l) ->
    dead_at (mi :: c) o' = dead_at (mi :: c) o.
Proof.
move=> Hstep Hnb Hnl Hpair o o' r l Hp Hp'.
case: o Hp => [|o] Hp; first by case: Hp => Hp; exfalso;
  exact: (Hnb _ _ Hp).
case: o' Hp' => [|o'] Hp'; first by case: Hp' => Hp'; exfalso;
  exact: (Hnl _ Hp').
move: Hp Hp' => /= Hp Hp'.
rewrite /dead_at /= Hstep.
exact: (Hpair _ _ _ _ Hp Hp').
Qed.

Definition jal_tgt (plm : NMap label) (c : code) : Prop :=
  forall l, List.In (IJal l) c ->
    exists P', getm plm P' = Some l.

Lemma jal_tgt_nil (plm : NMap label) : jal_tgt plm [::].
Proof. by move=> l []. Qed.

Lemma jal_tgt_cat (plm : NMap label) (c1 c2 : code) :
  jal_tgt plm c1 -> jal_tgt plm c2 -> jal_tgt plm (c1 ++ c2).
Proof.
move=> H1 H2 l HIn.
case: (List.in_app_or _ _ _ HIn); [exact: H1|exact: H2].
Qed.

Lemma jal_tgt_cons_nojal (plm : NMap label) (mi : instr) (c : code) :
  (forall l, mi <> IJal l) ->
  jal_tgt plm c -> jal_tgt plm (mi :: c).
Proof.
move=> Hmi H l [E|HIn]; last exact: H HIn.
exfalso. exact: (Hmi _ E).
Qed.

Lemma jal_tgt_cons_jal (plm : NMap label) (l0 : label)
    (P0 : Procedure.id) (c : code) :
  getm plm P0 = Some l0 ->
  jal_tgt plm c -> jal_tgt plm (IJal l0 :: c).
Proof.
move=> Hget H l [E|HIn]; last exact: H HIn.
case: E => <-. by exists P0.
Qed.

Fixpoint jal_free (c : code) : bool :=
  match c with
  | [::] => true
  | IJal _ :: _ => false
  | _ :: c' => jal_free c'
  end.

Lemma jal_free_tgt (plm : NMap label) (c : code) :
  jal_free c = true -> jal_tgt plm c.
Proof.
elim: c => [|mi c IH]; first by move=> _; exact: jal_tgt_nil.
by case: mi => /=;
  try by move=> *; apply: jal_tgt_cons_nojal => //; apply: IH.
Qed.

Lemma compile_expr_jal (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (e : expr) :
  forall (s : comp_env) (c : code) (s' : comp_env),
  compile_expr C lbp scr P_labels e s = Some (c, s') ->
  jal_tgt P_labels c.
Proof.
elim: e => [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
           |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc.
-
  case: v Hc => [i|p|] //= [<- _]; by apply: jal_free_tgt.
-
  move: Hc => /= [<- _]. by apply: jal_free_tgt.
-
  move: Hc => /= [<- _]. by apply: jal_free_tgt.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: jal_tgt_cat; first exact: (IH1 _ _ _ E1).
  apply: jal_tgt_cons_nojal => //.
  apply: jal_tgt_cons_nojal => //.
  apply: jal_tgt_cat; first exact: (IH2 _ _ _ E2).
  by apply: jal_free_tgt.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  exact: (jal_tgt_cat (IH1 _ _ _ E1) (IH2 _ _ _ E2)).
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=.
  case E3: (compile_expr C lbp scr P_labels e3 s2) => [[c3 s3]|];
    last by [].
  rewrite /=.
  case E4: (fresh_label C s3) => [[lconseq s4]|]; last by [].
  rewrite /=.
  case E5: (fresh_label C s4) => [[lend s5]|]; last by [].
  rewrite /=. move=> [<- _].
  apply: jal_tgt_cat; first exact: (IH1 _ _ _ E1).
  apply: jal_tgt_cons_nojal => //.
  apply: jal_tgt_cat; first exact: (IH3 _ _ _ E3).
  apply: jal_tgt_cons_nojal => //.
  apply: jal_tgt_cons_nojal => //.
  apply: jal_tgt_cat; first exact: (IH2 _ _ _ E2).
  by apply: jal_free_tgt.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: jal_tgt_cat; first exact: (IH _ _ _ E1).
  by apply: jal_free_tgt.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: jal_tgt_cat; first exact: (IH _ _ _ E1).
  by apply: jal_free_tgt.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: jal_tgt_cat; first exact: (IH2 _ _ _ E2).
  apply: jal_tgt_cons_nojal => //.
  apply: jal_tgt_cons_nojal => //.
  apply: jal_tgt_cat; first exact: (IH1 _ _ _ E1).
  by apply: jal_free_tgt.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case Heqb: (Component.eqb C' C).
  + rewrite /find_proc_label /Comp.lift.
    case EL: (getm P_labels P') => [tl|]; last by [].
    rewrite /=. move=> [<- _].
    apply: jal_tgt_cat; first exact: (IH _ _ _ E1).
    apply: jal_tgt_cons_nojal => //.
    apply: jal_tgt_cons_nojal => //.
    apply: (jal_tgt_cons_jal EL).
    by apply: jal_free_tgt.
  + move=> [<- _].
    apply: jal_tgt_cat; first exact: (IH _ _ _ E1).
    by apply: jal_free_tgt.
-
  move: Hc => /= [<- _]. by apply: jal_free_tgt.
Qed.

Lemma compile_expr_frag (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (e : expr) :
  forall (s : comp_env) (c : code) (s' : comp_env),
  compile_expr C lbp scr P_labels e s = Some (c, s') ->
  frag_ok c.
Proof.
elim: e => [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
           |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc.
-
  case: v Hc => [i|p|] //= [<- _].
  by apply: frag_scan_check_ok.
-
  move: Hc => /= [<- _].
  by apply: frag_scan_check_ok.
-
  move: Hc => /= [<- _].
  by apply: frag_scan_check_ok.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: frag_ok_cat; first exact: (IH1 _ _ _ E1).
  apply: frag_ok_cons => //.
  apply: frag_ok_cons => //.
  apply: frag_ok_cat; first exact: (IH2 _ _ _ E2).
  by apply: frag_scan_check_ok.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  exact: (frag_ok_cat (IH1 _ _ _ E1) (IH2 _ _ _ E2)).
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=.
  case E3: (compile_expr C lbp scr P_labels e3 s2) => [[c3 s3]|];
    last by [].
  rewrite /=.
  case E4: (fresh_label C s3) => [[lconseq s4]|]; last by [].
  rewrite /=.
  case E5: (fresh_label C s4) => [[lend s5]|]; last by [].
  rewrite /=. move=> [<- _].
  apply: frag_ok_cat; first exact: (IH1 _ _ _ E1).
  apply: frag_ok_cons => //.
  apply: frag_ok_cat; first exact: (IH3 _ _ _ E3).
  apply: frag_ok_cons => //.
  apply: frag_ok_cons => //.
  apply: frag_ok_cat; first exact: (IH2 _ _ _ E2).
  by apply: frag_scan_check_ok.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: frag_ok_cat; first exact: (IH _ _ _ E1).
  by apply: frag_scan_check_ok.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: frag_ok_cat; first exact: (IH _ _ _ E1).
  by apply: frag_scan_check_ok.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- _].
  apply: frag_ok_cat; first exact: (IH2 _ _ _ E2).
  apply: frag_ok_cons => //.
  apply: frag_ok_cons => //.
  apply: frag_ok_cat; first exact: (IH1 _ _ _ E1).
  by apply: frag_scan_check_ok.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  have Hc1 := IH _ _ _ E1.
  case Heqb: (Component.eqb C' C).
  + rewrite /find_proc_label /Comp.lift.
    case EL: (getm P_labels P') => [tl|]; last by [].
    rewrite /=. move=> [<- _].
    apply: frag_ok_cat; first exact: Hc1.
    by apply: frag_scan_check_ok.
  + move=> [<- _].
    apply: frag_ok_cat; first exact: Hc1.
    by apply: frag_scan_check_ok.
-
  move: Hc => /= [<- _].
  by apply: frag_scan_check_ok.
Qed.

Lemma compile_proc_shape_facts (C0 : Component.id)
    (lbp scr : Pointer.t) (plm : NMap label) (P0 : Procedure.id)
    (e : expr) (s : comp_env) (cd : code) (s' : comp_env) :
  compile_proc C0 lbp scr plm P0 e s = Some (cd, s') ->
  forall o i, List.nth_error cd o = Some i ->
    shape_cond i (dead_at cd o).
Proof.
rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift
  /Comp.ret.
case EL: (getm plm P0) => [pl|]; last by [].
rewrite /=.
case E2: (fresh_label C0 s) => [[lmain s2]|]; last by [].
rewrite /=.
case E3: (fresh_label C0 s2) => [[lreturn s3]|]; last by [].
rewrite /=.
case E4: (compile_expr C0 lbp scr plm e s3) => [[pcode s4]|];
  last by [].
rewrite /=. move=> [<- _].
have Fbody := compile_expr_frag E4.
set POST := pop R_ARG ++ pop R_AUX1 ++ store_arg scr R_AUX1 R_AUX2
            ++ pop R_SP ++ [:: IJump].
set SFZ := Z.of_nat (4 + stack_need e).
set PROL := [:: ILabel pl; IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
                IAlloc R_SP R_SP] ++ push R_AUX1
            ++ load_arg scr R_AUX1 ++ push R_AUX1 ++ push R_ARG
            ++ [:: IMov R_COM R_ARG].
set EEM := [:: IConst (IInt 1) R_ONE] ++
           [:: IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
               IAlloc R_SP R_SP] ++ push R_AUX1 ++ push R_RA ++
           [:: IConst (IPtr (flag_buf_ptr scr)) R_AUX1;
               ILoad R_AUX1 R_AUX2] ++ push R_AUX2 ++
           [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM;
               ILabel lmain; IConst (IInt 1) R_AUX2;
               IStore R_AUX1 R_AUX2; IJal pl] ++
           pop R_AUX1 ++ pop R_RA ++ pop R_SP ++
           [:: IBnz R_AUX1 lreturn; IHalt; ILabel lreturn; IReturn].
set EEN := [:: IConst (IInt 1) R_ONE] ++
           [:: IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
               IAlloc R_SP R_SP] ++ push R_AUX1 ++ push R_RA ++
           [:: IJal pl] ++ pop R_RA ++ pop R_SP ++ [:: IReturn].
case Hm: (Component.eqb C0 Component.main
          && Procedure.eqb P0 Procedure.main) => /=.
- case Hf: (immediately_final e) => /=.
  + by apply: (sandwich_at
      (pre := [:: IHalt] ++ EEM ++ PROL)
      (body := pcode) (post := POST)).
  + by apply: (sandwich_at
      (pre := EEM ++ PROL)
      (body := pcode) (post := POST)).
- by apply: (sandwich_at
    (pre := EEN ++ PROL)
    (body := pcode) (post := POST)).
Qed.

Lemma compile_proc_pair (C0 : Component.id) (lbp scr : Pointer.t)
    (plm : NMap label) (P0 : Procedure.id) (e : expr)
    (s : comp_env) (cd : code) (s' : comp_env) (pl0 : label) :
  getm plm P0 = Some pl0 ->
  pl0 < nlab s C0 ->
  compile_proc C0 lbp scr plm P0 e s = Some (cd, s') ->
  forall o o' r l,
    List.nth_error cd o = Some (IBnz r l) ->
    List.nth_error cd o' = Some (ILabel l) ->
    dead_at cd o' = dead_at cd o.
Proof.
move=> Hpl0 Hplb.
rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift
  /Comp.ret Hpl0 /=.
case E2: (fresh_label C0 s) => [[lmain s2]|]; last by [].
rewrite /=.
case E3: (fresh_label C0 s2) => [[lreturn s3]|]; last by [].
rewrite /=.
case E4: (compile_expr C0 lbp scr plm e s3) => [[pcode s4]|];
  last by [].
rewrite /=. move=> [<- _].
have Fbody := compile_expr_frag E4.
have Hbnzb := compile_expr_bnz E4.
have [Hm4 [HlabIn _]] := compile_expr_labels E4.
have [Ec2 Hn2] := fresh_label_inv E2.
have [Ec3 Hn3] := fresh_label_inv E3.
have Hlabb : forall l0, List.In (ILabel l0) pcode ->
    nlab s3 C0 <= l0 < nlab s4 C0.
{ move=> l0 HIn. have [H1 H2] := HlabIn _ HIn. by lia. }
have Mrm : (lreturn == lmain) = false by apply/eqP => E; lia.
have Mmr : (lmain == lreturn) = false by apply/eqP => E; lia.
have Mpm : (pl0 == lmain) = false by apply/eqP => E; lia.
have Mpr : (pl0 == lreturn) = false by apply/eqP => E; lia.
set SFZ := Z.of_nat (4 + stack_need e).
set POST := pop R_ARG ++ pop R_AUX1 ++ store_arg scr R_AUX1 R_AUX2
            ++ pop R_SP ++ [:: IJump].
set EENP := ([:: IConst (IInt 1) R_ONE] ++
             [:: IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
                 IAlloc R_SP R_SP] ++ push R_AUX1 ++ push R_RA ++
             [:: IJal pl0] ++ pop R_RA ++ pop R_SP ++ [:: IReturn]) ++
            [:: ILabel pl0; IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
                IAlloc R_SP R_SP] ++ push R_AUX1
            ++ load_arg scr R_AUX1 ++ push R_AUX1 ++ push R_ARG
            ++ [:: IMov R_COM R_ARG].
case Hm: (Component.eqb C0 Component.main
          && Procedure.eqb P0 Procedure.main) => /=.
- case Hf: (immediately_final e) => /=.
  + apply: (sandwich_bnz_label_at
      (pre := IHalt :: ext_wrap lmain lreturn pl0 scr SFZ)
      (body := pcode) (post := POST)
      (lo := nlab s3 C0) (hi := nlab s4 C0)) => //.
    * move=> l0 /= [E|[E|[]]]; by lia.
    * move=> l0 /= [E|[E|[E|[]]]]; by lia.
    * apply: pair_cons_skip => //.
      exact: (ext_wrap_pair Mrm Mmr Mpm Mpr).
  + apply: (sandwich_bnz_label_at
      (pre := ext_wrap lmain lreturn pl0 scr SFZ)
      (body := pcode) (post := POST)
      (lo := nlab s3 C0) (hi := nlab s4 C0)) => //.
    * move=> l0 /= [E|[E|[]]]; by lia.
    * move=> l0 /= [E|[E|[E|[]]]]; by lia.
    * exact: (ext_wrap_pair Mrm Mmr Mpm Mpr).
- apply: (sandwich_bnz_label_at
    (pre := EENP)
    (body := pcode) (post := POST)
    (lo := nlab s3 C0) (hi := nlab s4 C0)) => //.
  + move=> l0 /= [E|[]]; by lia.
  + move=> o o' r l Hp _.
    have := In_bnz_ops (List.nth_error_In _ _ Hp).
    by [].
Qed.

Theorem compiled_code_shape (p : Source.program)
    (tp : Intermediate.program) :
  compile_program p = Some tp ->
  forall (C : Component.id) (Cprocs : NMap Machine.code)
         (P : Procedure.id) (cd : Machine.code),
    Intermediate.prog_procedures tp C = Some Cprocs ->
    getm Cprocs P = Some cd ->
    code_shape cd.
Proof.
move=> Hcomp C Cprocs P cd Hget HgetP.
have [[plm [e [s0 [s1 [pl [Hcpc Hpl Hb _]]]]]] | [lab Ecd]]
  := compiled_proc_origin' Hcomp Hget HgetP.
- constructor.
  + move=> o r l o' H1 H2.
    exact: (compile_proc_pair Hpl Hb Hcpc H1 H2).
  + move=> o Hn.
    by have := compile_proc_shape_facts Hcpc Hn => /= /negbTE.
  + move=> o Hn.
    by have := compile_proc_shape_facts Hcpc Hn => /= /negbTE.
  + move=> o C' P' Hn.
    by have := compile_proc_shape_facts Hcpc Hn => /=.
  + move=> o r Hn.
    by have := compile_proc_shape_facts Hcpc Hn => /= /negbTE.
  + move=> o i Hn H1 H2 H3.
    exact: (compiled_proc_terminal Hcomp Hget HgetP Hn H1 H2 H3).
- subst cd.
  constructor.
  + move=> o r l o' H1 _.
    have := List.nth_error_In _ _ H1.
    by move=> /= [E|[E|[E|[]]]]; case: E.
  + move=> o H1.
    have := List.nth_error_In _ _ H1.
    by move=> /= [E|[E|[E|[]]]]; case: E.
  + move=> o H1.
    have := List.nth_error_In _ _ H1.
    by move=> /= [E|[E|[E|[]]]]; case: E.
  + move=> o C' P' H1.
    have := List.nth_error_In _ _ H1.
    by move=> /= [E|[E|[E|[]]]]; case: E.
  + move=> o r H1.
    have := List.nth_error_In _ _ H1.
    by move=> /= [E|[E|[E|[]]]]; case: E.
  + move=> o i.
    case: o => [|[|[|o]]] /=.
    * move=> [<-] H1 H2 H3. by exists (IJal lab).
    * move=> [<-] H1 H2 H3. by exists IHalt.
    * move=> [<-] H1 H2 H3. exfalso. exact: (H1 erefl).
    * by rewrite List.nth_error_nil.
Qed.

Fixpoint nb_check (c : code) (seen : seq nat) : bool :=
  match c with
  | [::] => true
  | IBnz _ l :: c' => (l \notin seen) && nb_check c' seen
  | ILabel l :: c' => nb_check c' (l :: seen)
  | _ :: c' => nb_check c' seen
  end.

Lemma nb_check_subset (c : code) (seen seen' : seq nat) :
  {subset seen <= seen'} ->
  nb_check c seen' = true -> nb_check c seen = true.
Proof.
elim: c seen seen' => [|mi c IH] seen seen' Hsub //=.
case: mi => //=; try by move=> *; apply: (IH _ _ Hsub).
-
  move=> l Hrest.
  apply: (IH _ (l :: seen')) Hrest.
  move=> x. rewrite !in_cons.
  case/orP => [-> //|Hx].
  by rewrite (Hsub _ Hx) orbT.
-
  move=> r l /andP [Hnotin Hrest].
  apply/andP; split; last exact: (IH _ _ Hsub Hrest).
  apply/negP => Hin.
  by rewrite (Hsub _ Hin) in Hnotin.
Qed.

Lemma nb_check_seen (c : code) (seen : seq nat) (o : nat)
    (r : register) (l : nat) :
  nb_check c seen = true ->
  l \in seen ->
  List.nth_error c o = Some (IBnz r l) -> False.
Proof.
elim: c seen o => [|mi c IH] seen o Hc Hin Hnth;
  first by rewrite List.nth_error_nil in Hnth.
case: o Hnth => [|o] Hnth.
- case: Hnth => E; subst mi.
  move: Hc => /= /andP [Hnotin _].
  by rewrite Hin in Hnotin.
- move: Hnth => /= Hnth.
  move: Hc => /=.
  case: mi => //=; try by move=> *; apply: (IH _ _ _ Hin Hnth) => //.
  + move=> l0 Hrest.
    apply: (IH _ _ Hrest _ Hnth).
    by rewrite in_cons Hin orbT.
  + move=> r0 l0 /andP [_ Hrest].
    exact: (IH _ _ Hrest Hin Hnth).
Qed.

Lemma nb_check_tail (mi : instr) (c : code) (seen : seq nat) :
  nb_check (mi :: c) seen = true ->
  exists seen2, nb_check c seen2 = true.
Proof.
case: mi => /=; try by move=> *; exists seen.
- by move=> l Hc; exists (l :: seen).
- by move=> r l /andP [_ Hc]; exists seen.
Qed.

Lemma nb_check_cat (c1 c2 : code) (seen : seq nat) :
  nb_check c1 seen = true ->
  nb_check c2 (lab_vals c1 ++ seen) = true ->
  nb_check (c1 ++ c2) seen = true.
Proof.
elim: c1 seen => [|mi c1 IH] seen /=; first by [].
case: mi => //=; try by move=> *; apply: IH => //.
-
  move=> l Hc1 Hc2.
  apply: IH => //.
  apply: (nb_check_subset _ Hc2).
  move=> x. rewrite mem_cat in_cons in_cons mem_cat.
  by case/orP => [Hx | /orP [Hx|Hx]]; rewrite Hx ?orbT.
-
  move=> r l /andP [Hnotin Hc1] Hc2.
  apply/andP; split=> //.
  exact: IH Hc1 Hc2.
Qed.

Lemma nb_check_fwd (c : code) (seen : seq nat) :
  nb_check c seen = true ->
  forall (o o' : nat) (r : register) (l : nat),
    List.nth_error c o = Some (IBnz r l) ->
    List.nth_error c o' = Some (ILabel l) ->
    o < o'.
Proof.
elim: c seen => [|mi c IH] seen Hc o o' r l Hb Hl;
  first by rewrite List.nth_error_nil in Hb.
case: o Hb => [|o] Hb; case: o' Hl => [|o'] Hl //.
- case: Hb => E; subst mi. by case: Hl.
-
  case: Hl => E; subst mi.
  move: Hc => /= Hc.
  exfalso.
  apply: (nb_check_seen Hc _ Hb).
  by rewrite in_cons eqxx.
-
  rewrite ltnS.
  move: Hb Hl => /= Hb Hl.
  have [seen2 Hc2] := nb_check_tail Hc.
  exact: (IH _ Hc2 _ _ _ _ Hb Hl).
Qed.

Lemma lab_vals_mem (l : nat) (c : code) :
  l \in lab_vals c -> List.In (ILabel l) c.
Proof.
elim: c => [|mi c IH] //=.
case: mi => /=; try by move=> *; right; apply: IH => //.
move=> l0. rewrite in_cons.
by case/orP => [/eqP ->|Hx]; [left|right; apply: IH].
Qed.

Lemma compile_expr_nb (C : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (e : expr) :
  forall (s : comp_env) (c : code) (s' : comp_env),
  compile_expr C lbp scr P_labels e s = Some (c, s') ->
  forall seen : seq nat,
  (forall l0, l0 \in seen ->
     (l0 < nlab s C) \/ (nlab s' C <= l0)) ->
  nb_check c seen = true.
Proof.
elim: e => [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
           |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc.
-
  by case: v Hc => [i|p|] //= [<- <-] seen _.
-
  by move: Hc => /= [<- <-] seen _.
-
  by move: Hc => /= [<- <-] seen _.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- <-] seen Hout.
  have [Hm1 [HlabIn1 _]] := compile_expr_labels E1.
  have [Hm2 [HlabIn2 _]] := compile_expr_labels E2.
  apply: nb_check_cat.
  { apply: (IH1 _ _ _ E1) => l0 /Hout ?. by lia. }
  rewrite /=.
  apply: nb_check_cat.
  { apply: (IH2 _ _ _ E2) => l0.
    rewrite mem_cat. case/orP => [Hx|Hx].
    - have [? ?] := HlabIn1 _ (lab_vals_mem Hx). by lia.
    - have := Hout _ Hx. by lia. }
  by [].
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- <-] seen Hout.
  have [Hm1 [HlabIn1 _]] := compile_expr_labels E1.
  have [Hm2 [HlabIn2 _]] := compile_expr_labels E2.
  apply: nb_check_cat.
  { apply: (IH1 _ _ _ E1) => l0 /Hout ?. by lia. }
  apply: (IH2 _ _ _ E2) => l0.
  rewrite mem_cat. case/orP => [Hx|Hx].
  + have [? ?] := HlabIn1 _ (lab_vals_mem Hx). by lia.
  + have := Hout _ Hx. by lia.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=.
  case E3: (compile_expr C lbp scr P_labels e3 s2) => [[c3 s3]|];
    last by [].
  rewrite /=.
  case E4: (fresh_label C s3) => [[lconseq s4]|]; last by [].
  rewrite /=.
  case E5: (fresh_label C s4) => [[lend s5]|]; last by [].
  rewrite /=. move=> [<- <-] seen Hout.
  have [Hm1 [HlabIn1 _]] := compile_expr_labels E1.
  have [Hm2 [HlabIn2 _]] := compile_expr_labels E2.
  have [Hm3 [HlabIn3 _]] := compile_expr_labels E3.
  have [Ec4 Hn4] := fresh_label_inv E4.
  have [Ec5 Hn5] := fresh_label_inv E5.
  subst lconseq lend.
  apply: nb_check_cat.
  { apply: (IH1 _ _ _ E1) => l0 /Hout ?. by lia. }
  rewrite /=.
  apply/andP; split.
  { apply/negP. rewrite mem_cat. case/orP => [Hx|Hx].
    - have [? ?] := HlabIn1 _ (lab_vals_mem Hx). by lia.
    - have := Hout _ Hx. by lia. }
  apply: nb_check_cat.
  { apply: (IH3 _ _ _ E3) => l0.
    rewrite mem_cat. case/orP => [Hx|Hx].
    - have [? ?] := HlabIn1 _ (lab_vals_mem Hx). by lia.
    - have := Hout _ Hx. by lia. }
  rewrite /=.
  apply/andP; split.
  { apply/negP. rewrite mem_cat. case/orP => [Hx|Hx].
    - have [? ?] := HlabIn3 _ (lab_vals_mem Hx). by lia.
    - rewrite mem_cat in Hx. case/orP: Hx => [Hx|Hx].
      + have [? ?] := HlabIn1 _ (lab_vals_mem Hx). by lia.
      + have := Hout _ Hx. by lia. }
  rewrite /=.
  apply: nb_check_cat.
  { apply: (IH2 _ _ _ E2) => l0.
    rewrite in_cons mem_cat. case/orP => [/eqP -> | Hx]; first by lia.
    case/orP: Hx => [Hx|Hx].
    - have [? ?] := HlabIn3 _ (lab_vals_mem Hx). by lia.
    - rewrite mem_cat in Hx. case/orP: Hx => [Hx|Hx].
      + have [? ?] := HlabIn1 _ (lab_vals_mem Hx). by lia.
      + have := Hout _ Hx. by lia. }
  by [].
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=. move=> [<- <-] seen Hout.
  apply: nb_check_cat.
  { apply: (IH _ _ _ E1) => l0 /Hout ?. by lia. }
  by [].
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=. move=> [<- <-] seen Hout.
  apply: nb_check_cat.
  { apply: (IH _ _ _ E1) => l0 /Hout ?. by lia. }
  by [].
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e1 s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case E2: (compile_expr C lbp scr P_labels e2 s1) => [[c2 s2]|];
    last by [].
  rewrite /=. move=> [<- <-] seen Hout.
  have [Hm1 [HlabIn1 _]] := compile_expr_labels E1.
  have [Hm2 [HlabIn2 _]] := compile_expr_labels E2.
  apply: nb_check_cat.
  { apply: (IH2 _ _ _ E2) => l0 /Hout ?. by lia. }
  rewrite /=.
  apply: nb_check_cat.
  { apply: (IH1 _ _ _ E1) => l0.
    rewrite mem_cat. case/orP => [Hx|Hx].
    - have [? ?] := HlabIn2 _ (lab_vals_mem Hx). by lia.
    - have := Hout _ Hx. by lia. }
  by [].
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C lbp scr P_labels e s) => [[c1 s1]|];
    last by [].
  rewrite /=.
  case Heqb: (Component.eqb C' C).
  + rewrite /find_proc_label /Comp.lift.
    case EL: (getm P_labels P') => [tl|]; last by [].
    rewrite /=. move=> [<- <-] seen Hout.
    apply: nb_check_cat.
    { apply: (IH _ _ _ E1) => l0 /Hout ?. by lia. }
    by [].
  + move=> [<- <-] seen Hout.
    apply: nb_check_cat.
    { apply: (IH _ _ _ E1) => l0 /Hout ?. by lia. }
    by [].
-
  by move: Hc => /= [<- <-] seen _.
Qed.

Lemma compile_proc_nb (C0 : Component.id) (lbp scr : Pointer.t)
    (plm : NMap label) (P0 : Procedure.id) (e : expr)
    (s : comp_env) (cd : code) (s' : comp_env) (pl0 : label) :
  getm plm P0 = Some pl0 ->
  pl0 < nlab s C0 ->
  compile_proc C0 lbp scr plm P0 e s = Some (cd, s') ->
  nb_check cd [::] = true.
Proof.
move=> Hpl0 Hplb.
rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift
  /Comp.ret Hpl0 /=.
case E2: (fresh_label C0 s) => [[lmain s2]|]; last by [].
rewrite /=.
case E3: (fresh_label C0 s2) => [[lreturn s3]|]; last by [].
rewrite /=.
case E4: (compile_expr C0 lbp scr plm e s3) => [[pcode s4]|];
  last by [].
rewrite /=. move=> [<- _].
have [Ec2 Hn2] := fresh_label_inv E2.
have [Ec3 Hn3] := fresh_label_inv E3.
have [Hm4 _] := compile_expr_labels E4.
have Mrm : (lreturn == lmain) = false by apply/eqP => E; lia.
have HOUT : forall l0, l0 \in [:: pl0; lreturn; lmain] ->
    (l0 < nlab s3 C0) \/ (nlab s4 C0 <= l0).
{ move=> l0. rewrite !in_cons.
  case/orP => [/eqP ->|]; first by left; lia.
  case/orP => [/eqP ->|]; first by left; lia.
  case/orP => [/eqP ->|//]; by left; lia. }
case Hm: (Component.eqb C0 Component.main
          && Procedure.eqb P0 Procedure.main) => /=.
- case Hf: (immediately_final e) => /=.
  + rewrite in_cons in_nil orbF Mrm /=.
    apply: nb_check_cat; last by [].
    exact: (compile_expr_nb E4 HOUT).
  + rewrite in_cons in_nil orbF Mrm /=.
    apply: nb_check_cat; last by [].
    exact: (compile_expr_nb E4 HOUT).
- apply: nb_check_cat; last by [].
  apply: (compile_expr_nb E4) => l0.
  rewrite in_cons.
  case/orP => [/eqP ->|//]; by left; lia.
Qed.

Lemma compile_proc_size (C0 : Component.id) (lbp scr : Pointer.t)
    (plm : NMap label) (P0 : Procedure.id) (e : expr)
    (s : comp_env) (cd : code) (s' : comp_env) :
  compile_proc C0 lbp scr plm P0 e s = Some (cd, s') ->
  3 < size cd.
Proof.
rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift
  /Comp.ret.
case EL: (getm plm P0) => [pl|]; last by [].
rewrite /=.
case E2: (fresh_label C0 s) => [[lmain s2]|]; last by [].
rewrite /=.
case E3: (fresh_label C0 s2) => [[lreturn s3]|]; last by [].
rewrite /=.
case E4: (compile_expr C0 lbp scr plm e s3) => [[pcode s4]|];
  last by [].
rewrite /=. move=> [<- _].
case Hm: (Component.eqb C0 Component.main
          && Procedure.eqb P0 Procedure.main) => /=.
- by case Hf: (immediately_final e) => /=.
- by [].
Qed.

Theorem compiled_stub_not_exported (p : Source.program)
    (tp : Intermediate.program) :
  Source.well_formed_program p ->
  compile_program p = Some tp ->
  forall (C : Component.id) (Cprocs : NMap Machine.code)
         (P : Procedure.id) (lab : label)
         (CI : Component.interface),
    Intermediate.prog_procedures tp C = Some Cprocs ->
    getm Cprocs P = Some [:: IConst (IInt 1) R_ONE; IJal lab; IHalt] ->
    getm (Intermediate.prog_interface tp) C = Some CI ->
    ~ Component.is_exporting CI P.
Proof.
move=> Hwf Hcomp C Cprocs P lab CI Hget HgetP HgetCI Hexp.
have Eiface := compilation_preserves_interface _ _ Hcomp.
have Hexp_src : exported_procedure (Source.prog_interface p) C P.
{ exists CI. split=> //. by rewrite -Eiface. }
have Hfind := Source.wfprog_exported_procedures_existence Hwf Hexp_src.
have [SrcProcs [e_src [HgetSrcC HgetSrcP]]] :
    exists SrcProcs e_src,
      getm (Source.prog_procedures p) C = Some SrcProcs
      /\ getm SrcProcs P = Some e_src.
{ move: Hfind. rewrite /Source.find_procedure.
  case E1: (getm (Source.prog_procedures p) C) => [SrcProcs|] //=.
  case E2: (getm SrcProcs P) => [e_src|] //= _.
  by exists SrcProcs, e_src. }
move: Hcomp Hget. rewrite /compile_program /run /= /Comp.bind /=.
case Eg: (gen_all_procedures_labels
            (elementsm (Source.prog_procedures p)) init_env)
  => [[labels cenv1]|]; last by [].
rewrite /=.
case Ec: (compile_components (gen_buffers (Source.prog_buffers p))
            labels (elementsm (Source.prog_procedures p)) cenv1)
  => [[codeL cenv2]|]; last by rewrite /=.
rewrite /=.
have HIn : List.In (C, SrcProcs) (elementsm (Source.prog_procedures p))
  := getm_In_elementsm HgetSrcC.
have Huniq_cs := uniq_unzip1_elementsm (Source.prog_procedures p).
have [plm [sC [cds [sC' [Hpls Hloc Hcp Hout]]]]]
  := compile_components_aux_getC _ _ _ _ _ _ _ _ _ Ec Huniq_cs HIn.
have HIn_src : List.In (P, e_src) (elementsm SrcProcs)
  := getm_In_elementsm HgetSrcP.
have [cd [s0 [s1 [HIncd Hcpc]]]]
  := compile_procedures_aux_forward Hcp HIn_src.
have Hsize := compile_proc_size Hcpc.
have Hkeys := compile_procedures_aux_keys Hcp.
have Huniq_cds : uniq (unzip1 cds).
{ rewrite (perm_uniq Hkeys) cats0.
  exact: uniq_unzip1_elementsm. }
have HgetCd : getm (mkfmap cds) P = Some cd.
{ rewrite mkfmapE. exact: (getm_def_In_uniq Huniq_cds HIncd). }
case Em: (isSome (Source.prog_main p)).
- rewrite /wrap_main /= /Comp.bind /Comp.lift.
  case Ep: (getm (mkfmap codeL) Component.main) => [procs|];
    last by rewrite /=.
  rewrite /=.
  case El1: (getm labels Component.main) => [PLM|]; last by rewrite /=.
  rewrite /=.
  case El2: (getm PLM Procedure.main) => [mlab|]; last by rewrite /=.
  rewrite /= /Comp.ret. move=> [<-] /=.
  rewrite setmE.
  case EC: (C == Component.main).
  + move=> [Ecpr].
    move/eqP: EC => EC. subst C.
    have Ecp' : procs = mkfmap cds.
    { move: Ep. rewrite mkfmapE Hout. by move=> [->]. }
    move: HgetP. rewrite -Ecpr setmE.
    case EP: (P == generate_fresh_procedure_id Component.main
                     (mkfmap codeL)).
    * move=> _.
      have Hfresh := generate_fresh_procedure_id_fresh _ _ _ Ep.
      move/eqP: EP => EP.
      have : P \in domm procs by rewrite Ecp' mem_domm HgetCd.
      by rewrite EP Hfresh.
    * move=> HgetP'.
      move: HgetCd. rewrite -Ecp' HgetP'. move=> [Ecd].
      move: Hsize. rewrite -Ecd /=. by lia.
  + move=> Hget'.
    have Ecp' : Cprocs = mkfmap cds.
    { move: Hget'. rewrite mkfmapE Hout. by move=> [->]. }
    move: HgetP. rewrite Ecp' HgetCd. move=> [Ecd].
    move: Hsize. rewrite Ecd /=. by lia.
- rewrite /wrap_main /= /Comp.ret. move=> [<-] Hget' /=.
  have Ecp' : Cprocs = mkfmap cds.
  { move: Hget'. rewrite /= mkfmapE Hout. by move=> [->]. }
  move: HgetP. rewrite Ecp' HgetCd. move=> [Ecd].
  move: Hsize. rewrite Ecd /=. by lia.
Qed.

Theorem compiled_bnz_forward (p : Source.program)
    (tp : Intermediate.program) :
  compile_program p = Some tp ->
  forall (C : Component.id) (Cprocs : NMap Machine.code)
         (P : Procedure.id) (cd : Machine.code)
         (o o' : nat) (r : register) (l : nat),
    Intermediate.prog_procedures tp C = Some Cprocs ->
    getm Cprocs P = Some cd ->
    List.nth_error cd o = Some (IBnz r l) ->
    List.nth_error cd o' = Some (ILabel l) ->
    o < o'.
Proof.
move=> Hcomp C Cprocs P cd o o' r l Hget HgetP Hb Hl.
have [plm [nb [Hbound Hper]]] := compiled_comp_origin Hcomp Hget.
case: (Hper _ _ HgetP)
  => [[e0 [s0 [s1 [pl [Hcpc Hpl Hnb]]]]] | [lab [Ecd _]]].
- have Hplb : pl < nlab s0 C.
  { have := Hbound _ _ Hpl. by lia. }
  have Hchk := compile_proc_nb Hpl Hplb Hcpc.
  exact: (nb_check_fwd Hchk Hb Hl).
- subst cd.
  have := List.nth_error_In _ _ Hb.
  by move=> /= [E|[E|[E|[]]]]; case: E.
Qed.

Lemma compile_proc_jal (C0 : Component.id) (lbp scr : Pointer.t)
    (plm : NMap label) (P0 : Procedure.id) (e : expr)
    (s : comp_env) (cd : code) (s' : comp_env) :
  compile_proc C0 lbp scr plm P0 e s = Some (cd, s') ->
  jal_tgt plm cd.
Proof.
rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift
  /Comp.ret.
case EL: (getm plm P0) => [pl|]; last by [].
rewrite /=.
case E2: (fresh_label C0 s) => [[lmain s2]|]; last by [].
rewrite /=.
case E3: (fresh_label C0 s2) => [[lreturn s3]|]; last by [].
rewrite /=.
case E4: (compile_expr C0 lbp scr plm e s3) => [[pcode s4]|];
  last by [].
rewrite /=. move=> [<- _].
have Hbody := compile_expr_jal E4.
case Hm: (Component.eqb C0 Component.main
          && Procedure.eqb P0 Procedure.main) => /=.
- case Hf: (immediately_final e) => /=.
  + repeat first [ apply: (jal_tgt_cons_jal EL)
                 | apply: jal_tgt_cons_nojal; first by [] ].
    apply: jal_tgt_cat; first exact: Hbody.
    by apply: jal_free_tgt.
  + repeat first [ apply: (jal_tgt_cons_jal EL)
                 | apply: jal_tgt_cons_nojal; first by [] ].
    apply: jal_tgt_cat; first exact: Hbody.
    by apply: jal_free_tgt.
- repeat first [ apply: (jal_tgt_cons_jal EL)
               | apply: jal_tgt_cons_nojal; first by [] ].
  apply: jal_tgt_cat; first exact: Hbody.
  by apply: jal_free_tgt.
Qed.

Lemma sandwich_low_label (pre body post : code) (lo : nat) (l : label) :
  ra_dead_scan pre false (size pre) = false ->
  (forall l0, List.In (ILabel l0) body -> lo <= l0) ->
  lab_vals post = [::] ->
  l < lo ->
  class_check (is_lab_of l) false pre false = true ->
  forall o,
    List.nth_error (pre ++ body ++ post) o = Some (ILabel l) ->
    dead_at (pre ++ body ++ post) o = false.
Proof.
move=> Hbal Hlabb Hlabpost Hlt CH o Ho.
rewrite /dead_at.
case: (ltnP o (size pre)) => Hlt1.
- have Hp1 : List.nth_error pre o = Some (ILabel l).
  { move: Ho. rewrite List.nth_error_app1 //. by apply/ltP. }
  rewrite (ra_dead_scan_cat_l _ _ (ltnW Hlt1)).
  apply: class_check_sound; [exact: CH | exact: Hp1 | exact: (eqxx _)].
- have Hb2 : List.nth_error (body ++ post) (o - size pre)
             = Some (ILabel l).
  { move: Ho. rewrite List.nth_error_app2; last by apply/leP.
    by have -> : (o - size pre)%coq_nat = o - size pre by lia. }
  case: (ltnP (o - size pre) (size body)) => Hlt2.
  + exfalso.
    have Hp2 : List.nth_error body (o - size pre) = Some (ILabel l).
    { move: Hb2. rewrite List.nth_error_app1 //. by apply/ltP. }
    have := Hlabb _ (List.nth_error_In _ _ Hp2). by lia.
  + exfalso.
    have Hp3 : List.nth_error post (o - size pre - size body)
               = Some (ILabel l).
    { move: Hb2. rewrite List.nth_error_app2; last by apply/leP.
      by have -> : (o - size pre - size body)%coq_nat
                   = o - size pre - size body by lia. }
    have := In_lab_vals (List.nth_error_In _ _ Hp3).
    by rewrite Hlabpost.
Qed.

Lemma sandwich_low_label_at (c pre body post : code) (lo : nat)
    (l : label) :
  c = pre ++ body ++ post ->
  ra_dead_scan pre false (size pre) = false ->
  (forall l0, List.In (ILabel l0) body -> lo <= l0) ->
  lab_vals post = [::] ->
  l < lo ->
  class_check (is_lab_of l) false pre false = true ->
  forall o,
    List.nth_error c o = Some (ILabel l) ->
    dead_at c o = false.
Proof. move=> ->. exact: sandwich_low_label. Qed.

Lemma compile_proc_label_low (C0 : Component.id) (lbp scr : Pointer.t)
    (plm : NMap label) (P0 : Procedure.id) (e : expr)
    (s : comp_env) (cd : code) (s' : comp_env) (l : label) :
  l < nlab s C0 ->
  compile_proc C0 lbp scr plm P0 e s = Some (cd, s') ->
  forall o,
    List.nth_error cd o = Some (ILabel l) ->
    dead_at cd o = false.
Proof.
move=> Hlt.
rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift
  /Comp.ret.
case EL: (getm plm P0) => [pl|]; last by [].
rewrite /=.
case E2: (fresh_label C0 s) => [[lmain s2]|]; last by [].
rewrite /=.
case E3: (fresh_label C0 s2) => [[lreturn s3]|]; last by [].
rewrite /=.
case E4: (compile_expr C0 lbp scr plm e s3) => [[pcode s4]|];
  last by [].
rewrite /=. move=> [<- _].
have [Ec2 Hn2] := fresh_label_inv E2.
have [Ec3 Hn3] := fresh_label_inv E3.
have [Hm4 [HlabIn _]] := compile_expr_labels E4.
have Hlm : (lmain == l) = false by apply/eqP => E; lia.
have Hlr : (lreturn == l) = false by apply/eqP => E; lia.
have Hlabb : forall l0, List.In (ILabel l0) pcode -> nlab s3 C0 <= l0.
{ move=> l0 HIn. have [H1 H2] := HlabIn _ HIn. by lia. }
have Hlo : l < nlab s3 C0 by lia.
set SFZ := Z.of_nat (4 + stack_need e).
set POST := pop R_ARG ++ pop R_AUX1 ++ store_arg scr R_AUX1 R_AUX2
            ++ pop R_SP ++ [:: IJump].
set EENP := ([:: IConst (IInt 1) R_ONE] ++
             [:: IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
                 IAlloc R_SP R_SP] ++ push R_AUX1 ++ push R_RA ++
             [:: IJal pl] ++ pop R_RA ++ pop R_SP ++ [:: IReturn]) ++
            [:: ILabel pl; IMov R_SP R_AUX1; IConst (IInt SFZ) R_SP;
                IAlloc R_SP R_SP] ++ push R_AUX1
            ++ load_arg scr R_AUX1 ++ push R_AUX1 ++ push R_ARG
            ++ [:: IMov R_COM R_ARG].
case Hm: (Component.eqb C0 Component.main
          && Procedure.eqb P0 Procedure.main) => /=.
- case Hf: (immediately_final e) => /=.
  + apply: (sandwich_low_label_at
      (pre := IHalt :: ext_wrap lmain lreturn pl scr SFZ)
      (body := pcode) (post := POST) (lo := nlab s3 C0)) => //.
    by rewrite /= Hlm Hlr ?if_same.
  + apply: (sandwich_low_label_at
      (pre := ext_wrap lmain lreturn pl scr SFZ)
      (body := pcode) (post := POST) (lo := nlab s3 C0)) => //.
    by rewrite /= Hlm Hlr ?if_same.
- apply: (sandwich_low_label_at
    (pre := EENP)
    (body := pcode) (post := POST) (lo := nlab s3 C0)) => //.
  by rewrite /= ?if_same.
Qed.

Theorem compiled_jal_target (p : Source.program)
    (tp : Intermediate.program) :
  compile_program p = Some tp ->
  forall (C : Component.id) (Cprocs : NMap Machine.code)
         (P1 : Procedure.id) (Pcode1 : Machine.code) (o1 : nat)
         (l : label)
         (P2 : Procedure.id) (Pcode2 : Machine.code) (o2 : nat),
    Intermediate.prog_procedures tp C = Some Cprocs ->
    getm Cprocs P1 = Some Pcode1 ->
    getm Cprocs P2 = Some Pcode2 ->
    List.nth_error Pcode1 o1 = Some (IJal l) ->
    List.nth_error Pcode2 o2 = Some (ILabel l) ->
    dead_at Pcode2 o2 = false.
Proof.
move=> Hcomp C Cprocs P1 Pcode1 o1 l P2 Pcode2 o2 Hget Hg1 Hg2 Hn1 Hn2.
have [plm [nb [Hb Hper]]] := compiled_comp_origin Hcomp Hget.
have Hlow : l < nb.
{ case: (Hper _ _ Hg1)
    => [[e1 [s01 [s11 [pl1 [Hcpc1 _ _]]]]] | [lab1 [E1 Hlab1]]].
  - have [P' HP'] := compile_proc_jal Hcpc1 (List.nth_error_In _ _ Hn1).
    exact: (Hb _ _ HP').
  - subst Pcode1.
    have := List.nth_error_In _ _ Hn1.
    move=> /= [E|[E|[E|[]]]]; try by case: E.
    case: E => El. subst l.
    exact: (Hb _ _ Hlab1). }
case: (Hper _ _ Hg2)
  => [[e2 [s02 [s12 [pl2 [Hcpc2 _ Hnb2]]]]] | [lab2 [E2 _]]].
- have Hlt2 : l < nlab s02 C by lia.
  exact: (compile_proc_label_low Hlt2 Hcpc2 Hn2).
- subst Pcode2.
  have := List.nth_error_In _ _ Hn2.
  by move=> /= [E|[E|[E|[]]]]; case: E.
Qed.
