Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import CompCert.Events.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.LabelScheme.
Require Import T2M.MPos.
Require Import Backtranslation_ME_MP.
Require Import Backtranslation_ME_MP_Step.
Require Import Backtranslation_ME_MP_Seg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Notation minstr := (@Merged.instr mt).

Lemma nth_error_tagged cid (l : seq minstr) i :
  List.nth_error (rp_tagged cid l) i
  = omap (fun x => (x, def_mem_tag cid true)) (List.nth_error l i).
Proof. rewrite /rp_tagged. elim: l i => [|x l IH] [|i] //=. Qed.

Lemma size_tagged cid (l : seq minstr) : size (rp_tagged cid l) = size l.
Proof. by rewrite /rp_tagged size_map. Qed.

Lemma nth_error_cat_l {A : Type} (l1 l2 : seq A) i :
  i < size l1 -> List.nth_error (l1 ++ l2) i = List.nth_error l1 i.
Proof. elim: l1 i => [|x l1 IH] [|i] //= H. exact: IH. Qed.

Lemma nth_error_cat_r {A : Type} (l1 l2 : seq A) i :
  List.nth_error (l1 ++ l2) (size l1 + i) = List.nth_error l2 i.
Proof. by elim: l1. Qed.

Lemma nth_error_nth' {A : Type} (d : A) (l : seq A) i :
  i < size l -> List.nth_error l i = Some (nth d l i).
Proof. elim: l i => [|x l IH] [|i] //= H. exact: IH. Qed.

Lemma blk_of_tagged (cde A B : @Merged.code mt) cid (l : seq minstr) :
  cde = A ++ rp_tagged cid l ++ B -> blk cde (size A) cid l.
Proof.
move=> -> i Hi.
rewrite nth_error_cat_r nth_error_cat_l ?size_tagged //.
by rewrite nth_error_tagged (nth_error_nth' (@MrNop mt) Hi).
Qed.

Section Layout.

Variables (L P C : nat) (PI : Program.interface)
          (PB : NMap {fmap Block.id -> nat + seq value}) (t : trace).
Variables (Ip Ic : Program.interface)
          (Bp Bc : NMap {fmap Block.id -> nat + seq value}).

Local Notation cc := (rp_comp_code L P C PI PB t).
Local Notation codeP := (code (rp_program L P C PI PB t Ip Bp)).
Local Notation codeC := (code (rp_program L P C PI PB t Ic Bc)).
Local Notation cde := (codeP ++ codeC).

Definition Sc cid : @Merged.code mt :=
  if cid == Component.main
  then rp_tagged cid (rp_init L t cid (rp_addr PB cid) 1 ++ rp_goto L cid 0)
  else [::].

Definition Ec cid : @Merged.code mt :=
  flatten [seq rp_entry L P C PI cid p | p <- rp_exports PI cid].

Definition Tl cid : seq minstr :=
  let es := rp_events t cid in
  MrLabel (rp_lab L cid 3) :: rp_init L t cid (rp_addr PB cid) 2 ++ rp_push
    ++ rp_goto L cid 0 ++ rp_disp L cid (rp_addr PB cid) (size es)
    ++ flatten [seq rp_case L P C cid ke | ke <- zip (iota 0 (size es)) es]
    ++ [:: MrHalt].

Lemma cc_split cid : cc cid = Sc cid ++ Ec cid ++ rp_tagged cid (Tl cid).
Proof. by []. Qed.

End Layout.

Definition ilabs (l : seq minstr) : seq nat :=
  pmap (fun i => if i is MrLabel x then Some x else None) l.

Definition clabs (cd : @Merged.code mt) : seq nat := ilabs (map fst cd).

Lemma ilabs_cat l1 l2 : ilabs (l1 ++ l2) = ilabs l1 ++ ilabs l2.
Proof. by rewrite /ilabs pmap_cat. Qed.

Lemma clabs_cat c1 c2 : clabs (c1 ++ c2) = clabs c1 ++ clabs c2.
Proof. by rewrite /clabs map_cat ilabs_cat. Qed.

Lemma clabs_tagged cid l : clabs (rp_tagged cid l) = ilabs l.
Proof. by rewrite /clabs /rp_tagged -map_comp map_id. Qed.

Lemma clabs_flatten (cs : seq (@Merged.code mt)) :
  clabs (flatten cs) = flatten (map clabs cs).
Proof. elim: cs => [//|c cs IH] /=. by rewrite clabs_cat IH. Qed.

Lemma ilabs_flatten (ls : seq (seq minstr)) :
  ilabs (flatten ls) = flatten (map ilabs ls).
Proof. elim: ls => [//|l ls IH] /=. by rewrite ilabs_cat IH. Qed.

Lemma count_label_clabs x (cd : @Merged.code mt) :
  count (is_label_def x) cd = count (pred1 x) (clabs cd).
Proof.
elim: cd => [//|[i tg] cd IH] /=.
rewrite /clabs /= -/(clabs cd) IH.
by case: i => //= l; rewrite eq_sym.
Qed.

Lemma ilabs_load N r tmp : ilabs (rp_load N r tmp) = [::].
Proof.
rewrite /rp_load. by case: ifP.
Qed.

Lemma ilabs_init L t cid A j : ilabs (rp_init L t cid A j) = [:: rp_lab L cid j].
Proof. by rewrite /rp_init !ilabs_cat ilabs_load. Qed.

Lemma ilabs_test L cid k : ilabs (rp_test L cid k) = [::].
Proof. by rewrite /rp_test ilabs_cat ilabs_load. Qed.

Lemma ilabs_disp L cid A n : ilabs (rp_disp L cid A n) = [:: rp_lab L cid 0].
Proof.
rewrite /rp_disp !ilabs_cat ilabs_flatten.
have -> : flatten (map ilabs [seq rp_test L cid k | k <- iota 0 n]) = [::].
{ rewrite -map_comp. elim: (iota 0 n) => [|k ks IH] /=; first by [].
  by rewrite ilabs_test IH. }
by [].
Qed.

Lemma ilabs_case_body L P C cid e : ilabs (rp_case_body L P C cid e) = [::].
Proof. case: e => [? ? z ?|? z ?]; by rewrite /rp_case_body !ilabs_cat ilabs_load. Qed.

Lemma ilabs_case L P C cid ke : ilabs (rp_case L P C cid ke) = [:: rp_lab L cid (4 + ke.1)].
Proof. by rewrite /rp_case ilabs_cat ilabs_case_body. Qed.

Lemma clabs_entry L P C PI cid p :
  clabs (rp_entry L P C PI cid p) = [:: mk_entry L P C cid p].
Proof. by rewrite /rp_entry /clabs /=. Qed.

Lemma clabs_comp L P C PI PB t cid :
  clabs (rp_comp_code L P C PI PB t cid)
  = (if cid == Component.main then [:: rp_lab L cid 1] else [::])
    ++ [seq mk_entry L P C cid p | p <- rp_exports PI cid]
    ++ [:: rp_lab L cid 3; rp_lab L cid 2; rp_lab L cid 0]
    ++ [seq rp_lab L cid (4 + k) | k <- iota 0 (size (rp_events t cid))].
Proof.
rewrite /rp_comp_code !clabs_cat.
congr (_ ++ _).
- case: (cid == Component.main) => //.
  by rewrite clabs_tagged ilabs_cat ilabs_init.
- congr (_ ++ _).
  + rewrite clabs_flatten -map_comp.
    rewrite (eq_map (fun p => clabs_entry L P C PI cid p)).
    by elim: (rp_exports PI cid) => [|p ps IH] //=; rewrite IH.
  + have Ec : forall x (l : seq minstr), ilabs (MrLabel x :: l) = x :: ilabs l by [].
    have Ep : ilabs rp_push = [::] by [].
    have Eg : forall j, ilabs (rp_goto L cid j) = [::] by [].
    have Eh : ilabs [:: @MrHalt mt] = [::] by [].
    rewrite clabs_tagged Ec ilabs_cat ilabs_init ilabs_cat Ep ilabs_cat Eg ilabs_cat ilabs_disp.
    rewrite ilabs_cat ilabs_flatten Eh cats0 /=.
    congr (_ :: _ :: _ :: _).
    have -> : map ilabs [seq rp_case L P C cid ke
                          | ke <- zip (iota 0 (size (rp_events t cid))) (rp_events t cid)]
              = [seq [:: rp_lab L cid (4 + ke.1)]
                  | ke <- zip (iota 0 (size (rp_events t cid))) (rp_events t cid)].
    { rewrite -map_comp. apply: eq_map => ke /=. exact: ilabs_case. }
    have Efl : forall (A B : Type) (f : A -> B) (s : seq A),
        flatten [seq [:: f x] | x <- s] = map f s.
    { move=> A B f. by elim => //= x s ->. }
    rewrite (Efl _ _ (fun ke : nat * event => rp_lab L cid (4 + ke.1))).
    rewrite -[in RHS](@unzip1_zip _ _ (iota 0 (size (rp_events t cid))) (rp_events t cid));
      last by rewrite size_iota.
    rewrite -map_comp. by [].
Qed.

Lemma count_label_le1 x (cd : @Merged.code mt) :
  uniq (clabs cd) -> count (is_label_def x) cd <= 1.
Proof. move=> H. rewrite count_label_clabs (count_uniq_mem _ H). by case: (x \in _). Qed.

Section Uniq.

Variables (L P C : nat) (PI : Program.interface)
          (PB : NMap {fmap Block.id -> nat + seq value}) (t : trace).

Local Notation cc := (rp_comp_code L P C PI PB t).

Definition comp_ok (cid : nat) : Prop :=
  [/\ cid < C, 4 + size (rp_events t cid) <= L
    & forall p, p \in rp_exports PI cid -> p < P].

Definition owned (cid x : nat) : Prop :=
  (exists j, j < L /\ x = mk_body L cid j) \/ (exists p, p < P /\ x = mk_entry L P C cid p).

Lemma clabs_owned cid x : comp_ok cid -> x \in clabs (cc cid) -> owned cid x.
Proof.
case=> HC HL HP. rewrite clabs_comp !mem_cat.
have Hb : forall j, j < 4 + size (rp_events t cid) -> x = rp_lab L cid j -> owned cid x.
{ move=> j Hj ->. left. exists j. split=> //. exact: leq_trans Hj HL. }
case/or4P.
- case: (cid == Component.main); last by [].
  rewrite inE => /eqP E. by apply: (Hb 1).
- move/mapP => [p Hp ->]. right. exists p. split=> //. exact: HP.
- rewrite !inE => /or3P [/eqP E|/eqP E|/eqP E].
  + by apply: (Hb 3).
  + by apply: (Hb 2).
  + by apply: (Hb 0).
- move/mapP => [k Hk E]. apply: (Hb (4 + k)); last exact: E.
  move: Hk. rewrite mem_iota add0n => /andP [_ Hk]. by rewrite ltn_add2l.
Qed.

Lemma owned_inj c1 c2 x : c1 < C -> c2 < C -> owned c1 x -> owned c2 x -> c1 = c2.
Proof.
move=> H1 H2 [[j1 [Hj1 E1]]|[p1 [Hp1 E1]]] [[j2 [Hj2 E2]]|[p2 [Hp2 E2]]].
- by case: (mk_body_inj Hj1 Hj2 (etrans (esym E1) E2)).
- by case: (mk_body_entry_disjoint H1 Hj1 (etrans (esym E1) E2)).
- by case: (mk_body_entry_disjoint H2 Hj2 (etrans (esym E2) E1)).
- by case: (mk_entry_inj Hp1 Hp2 (etrans (esym E1) E2)).
Qed.

Lemma clabs_uniq cid : comp_ok cid -> uniq (clabs (cc cid)).
Proof.
move=> Hok.
have [HC HL HP] := Hok.
set J := (if cid == Component.main then [:: 1] else [::]) ++ [:: 3; 2; 0]
           ++ iota 4 (size (rp_events t cid)).
have EJ : (if cid == Component.main then [:: rp_lab L cid 1] else [::])
          ++ [:: rp_lab L cid 3; rp_lab L cid 2; rp_lab L cid 0]
          ++ [seq rp_lab L cid (4 + k) | k <- iota 0 (size (rp_events t cid))]
          = map (rp_lab L cid) J.
{ rewrite /J !map_cat. congr (_ ++ _); first by case: (cid == Component.main).
  congr (_ ++ _). by rewrite -[4]addn0 iotaDl -map_comp. }
have HJL : forall j, j \in J -> j < L.
{ move=> j. rewrite /J !mem_cat => /or3P [|Hj|Hj].
  - case: (cid == Component.main) => //. rewrite inE => /eqP ->. exact: leq_trans _ HL.
  - move: Hj. rewrite !inE => /or3P [/eqP ->|/eqP ->|/eqP ->]; exact: leq_trans _ HL.
  - move: Hj. rewrite mem_iota => /andP [_ Hj]. exact: leq_trans Hj HL. }
have HuJ : uniq J.
{ rewrite /J catA cat_uniq iota_uniq andbT.
  have Hs : all (fun k => k < 4)
              ((if cid == Component.main then [:: 1] else [::]) ++ [:: 3; 2; 0])
    by case: (cid == Component.main).
  apply/andP; split; first by case: (cid == Component.main).
  apply/hasPn => k. rewrite mem_iota => /andP [Hk _].
  apply/negP => Hin. have := allP Hs k Hin. by rewrite ltnNge Hk. }
have Huniq_map : forall (f : nat -> nat) (s : seq nat),
    {in s &, injective f} -> uniq s -> uniq (map f s).
{ move=> f s Hi Hs. by rewrite (map_inj_in_uniq Hi). }
rewrite clabs_comp.
set M := (if cid == Component.main then [:: rp_lab L cid 1] else [::]).
set E := [seq mk_entry L P C cid p | p <- rp_exports PI cid].
set X := [:: rp_lab L cid 3; rp_lab L cid 2; rp_lab L cid 0]
           ++ [seq rp_lab L cid (4 + k) | k <- iota 0 (size (rp_events t cid))].
have Hp : perm_eq (M ++ E ++ X) (E ++ M ++ X) by rewrite perm_catCA.
rewrite (perm_uniq Hp) EJ cat_uniq.
apply/and3P; split.
- apply: Huniq_map; last exact: uniq_fset.
  move=> p1 p2 Hp1 Hp2 Ee. by case: (mk_entry_inj (HP _ Hp1) (HP _ Hp2) Ee).
- apply/hasPn => x /mapP [j Hj ->].
  apply/negP => /mapP [p Hpp Ee].
  exact: (mk_body_entry_disjoint HC (HJL _ Hj) Ee).
- apply: Huniq_map; last exact: HuJ.
  move=> j1 j2 Hj1 Hj2 Ee. by case: (mk_body_inj (HJL _ Hj1) (HJL _ Hj2) Ee).
Qed.

Lemma flatten_clabs_uniq (cs : seq nat) :
  uniq cs -> (forall c, c \in cs -> comp_ok c) ->
  uniq (flatten [seq clabs (cc c) | c <- cs]).
Proof.
elim: cs => [//|c cs IH] /= /andP [Hc Hcs] Hok.
rewrite cat_uniq. apply/and3P; split.
- apply: clabs_uniq. apply: Hok. exact: mem_head.
- apply/hasPn => x /flattenP [lx /mapP [c' Hc' ->] Hx'].
  apply/negP => Hx.
  have Hin' : c' \in c :: cs by rewrite inE Hc' orbT.
  have Ho := clabs_owned (Hok c (mem_head _ _)) Hx.
  have Ho' := clabs_owned (Hok c' Hin') Hx'.
  have [HC _ _] := Hok c (mem_head _ _).
  have [HC' _ _] := Hok c' Hin'.
  have E := owned_inj HC HC' Ho Ho'. subst c'. by rewrite Hc' in Hc.
- apply: IH => // c' Hc'. apply: Hok. by rewrite inE Hc' orbT.
Qed.

End Uniq.

Lemma code_uniq L P C PI PB t (Ip Ic : Program.interface) Bp Bc :
  fdisjoint (domm Ip) (domm Ic) ->
  (forall c, (c \in domm Ip) || (c \in domm Ic) -> comp_ok L P C PI t c) ->
  uniq (clabs (code (rp_program L P C PI PB t Ip Bp) ++ code (rp_program L P C PI PB t Ic Bc))).
Proof.
move=> Hdis Hok.
rewrite clabs_cat /= !clabs_flatten -!map_comp -flatten_cat -map_cat.
apply: flatten_clabs_uniq.
- rewrite cat_uniq !uniq_fset /= andbT. apply/hasPn => c Hc.
  apply/negP => Hc'. move: (fdisjointP Hdis c Hc'). by rewrite Hc.
- move=> c. rewrite mem_cat => H. exact: Hok.
Qed.
