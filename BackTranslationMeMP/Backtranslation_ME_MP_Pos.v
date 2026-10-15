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
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import MicroPolicies.Recomposition.EncodeCode.
Require Import T2M.MPos.
Require Import Backtranslation_ME_MP.
Require Import Backtranslation_ME_MP_Step.
Require Import Backtranslation_ME_MP_Seg.
Require Import Backtranslation_ME_MP_Layout.
Require Import Backtranslation_ME_MP_Run.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Notation minstr := (@Merged.instr mt).

Section Pos.

Variables (L P C : nat) (PI : Program.interface)
          (PB : NMap {fmap Block.id -> nat + seq value}) (t : trace).
Variable cde : @Merged.code mt.
Hypothesis Huniq : uniq (clabs cde).

Variable cid : nat.
Variables (Apre Bpost : @Merged.code mt).
Hypothesis Hsplit : cde = Apre ++ rp_comp_code L P C PI PB t cid ++ Bpost.

Local Notation es := (rp_events t cid).
Local Notation ne := (size (rp_events t cid)).
Local Notation AD := (rp_addr PB cid).

Definition nT := size Apre + size (Sc L PB t cid) + size (Ec L P C PI cid).
Definition nI := nT.+1.
Definition nPu := nI + size (rp_init L t cid AD 2).
Definition nG := nPu + size rp_push.
Definition nD := nG.+1.
Definition nCs := nD + size (rp_disp L cid AD ne).
Definition cases_l := [seq rp_case L P C cid ke | ke <- zip (iota 0 ne) es].
Definition nCk (k : nat) := nCs + size (flatten (take k cases_l)).

Lemma blk_T : blk cde nT cid (Tl L P C PB t cid).
Proof.
have H := @blk_of_tagged cde (Apre ++ Sc L PB t cid ++ Ec L P C PI cid) Bpost cid
            (Tl L P C PB t cid).
rewrite !size_cat addnA in H. apply: H.
by rewrite Hsplit (cc_split L P C PI PB t) -!catA.
Qed.

Lemma Tl_split :
  Tl L P C PB t cid
  = MrLabel (rp_lab L cid 3)
    :: rp_init L t cid AD 2 ++ rp_push ++ rp_goto L cid 0 ++ rp_disp L cid AD ne
       ++ flatten cases_l ++ [:: MrHalt].
Proof. by []. Qed.

Lemma blk_init2 : blk cde nI cid (rp_init L t cid AD 2).
Proof.
have H := blk_T. rewrite Tl_split in H. have [_ H1] := blk_cons H.
by have [H2 _] := blk_cat H1.
Qed.

Lemma blk_after_init :
  blk cde nPu cid (rp_push ++ rp_goto L cid 0 ++ rp_disp L cid AD ne
                    ++ flatten cases_l ++ [:: MrHalt]).
Proof.
have H := blk_T. rewrite Tl_split in H. have [_ H1] := blk_cons H.
by have [_ H2] := blk_cat H1.
Qed.

Lemma blk_after_push :
  blk cde nG cid (rp_goto L cid 0 ++ rp_disp L cid AD ne ++ flatten cases_l ++ [:: MrHalt]).
Proof. have [_ H] := blk_cat blk_after_init. exact: H. Qed.

Lemma blk_disp : blk cde nD cid (rp_disp L cid AD ne).
Proof.
have [_ H] := blk_cons blk_after_push.
by have [H2 _] := blk_cat H.
Qed.

Lemma blk_cases : blk cde nCs cid (flatten cases_l ++ [:: MrHalt]).
Proof.
have [_ H] := blk_cons blk_after_push.
by have [_ H2] := blk_cat H.
Qed.

Lemma blk_case k ev0 :
  k < ne -> blk cde (nCk k) cid (rp_case L P C cid (k, nth ev0 es k)).
Proof.
move=> Hk.
have H := blk_cases.
have Hsz : k < size cases_l by rewrite /cases_l size_map size_zip size_iota minnn.
have E : flatten cases_l = flatten (take k cases_l)
                           ++ (rp_case L P C cid (k, nth ev0 es k) ++ flatten (drop k.+1 cases_l)).
{ have Efc : forall (A : Type) (x : seq A) (xs : seq (seq A)),
      flatten (x :: xs) = x ++ flatten xs by [].
  rewrite -{1}(cat_take_drop k cases_l) flatten_cat (drop_nth [::] Hsz) Efc.
  congr (_ ++ (_ ++ _)).
  rewrite /cases_l (nth_map (0, ev0)); last by rewrite size_zip size_iota minnn.
  by rewrite nth_zip ?size_iota // nth_iota. }
rewrite E -catA in H.
have [_ H2] := blk_cat H.
have [H3 _] := blk_cat H2.
have [H4 _] := blk_cat H3.
exact: H4.
Qed.

Lemma nxt_after_case k ev0 :
  k < ne -> nxt cde (nCk k + size (rp_case L P C cid (k, nth ev0 es k))) cid.
Proof.
move=> Hk.
have H := blk_cases.
have Hsz : k < size cases_l by rewrite /cases_l size_map size_zip size_iota minnn.
have E : flatten cases_l = flatten (take k cases_l)
                           ++ (rp_case L P C cid (k, nth ev0 es k) ++ flatten (drop k.+1 cases_l)).
{ have Efc : forall (A : Type) (x : seq A) (xs : seq (seq A)),
      flatten (x :: xs) = x ++ flatten xs by [].
  rewrite -{1}(cat_take_drop k cases_l) flatten_cat (drop_nth [::] Hsz) Efc.
  congr (_ ++ (_ ++ _)).
  rewrite /cases_l (nth_map (0, ev0)); last by rewrite size_zip size_iota minnn.
  by rewrite nth_zip ?size_iota // nth_iota. }
rewrite E -catA in H.
have [_ H2] := blk_cat H.
rewrite -catA in H2.
have [_ H3] := blk_cat H2.
apply: (blk_nxt H3). by rewrite size_cat /= addn1.
Qed.

Lemma lab_at_of n x :
  List.nth_error cde n = Some (MrLabel x, def_mem_tag cid true) ->
  lab_at cde x n cid.
Proof.
move=> Hn. split; last exact: Hn.
apply: (findopt_unique_pos (count_label_le1 x Huniq) Hn).
by rewrite /is_label_def /= eqxx.
Qed.

Lemma lab_at_3 : lab_at cde (rp_lab L cid 3) nT cid.
Proof. apply: lab_at_of. have [H _] := blk_cons blk_T. exact: H. Qed.

Lemma lab_at_0 : lab_at cde (rp_lab L cid 0) nD cid.
Proof. apply: lab_at_of. have [H _] := blk_cons blk_disp. exact: H. Qed.

Lemma lab_at_2 : lab_at cde (rp_lab L cid 2) (nI + size (init_pre L t cid AD 2)) cid.
Proof.
apply: lab_at_of. have H := blk_init2. rewrite rp_init_split in H.
have [_ H2] := blk_cat H. have [H3 _] := blk_cons H2. exact: H3.
Qed.

Lemma lab_at_case k (ev0 : event) :
  k < ne -> lab_at cde (rp_lab L cid (4 + k)) (nCk k) cid.
Proof.
move=> Hk. apply: lab_at_of. have H := blk_case (ev0 := ev0) Hk.
have [H1 _] := blk_cons H. exact: H1.
Qed.

Definition nE (i : nat) := size Apre + size (Sc L PB t cid) + 3 * i.

Lemma entry_cells i p :
  List.nth_error (rp_exports PI cid) i = Some p ->
  [/\ List.nth_error cde (nE i)
        = Some (MrLabel (mk_entry L P C cid p), Transitional.head_tag_gen PI cid p),
      blk cde (nE i).+1 cid (MrMov (inl R_RA) (inl R_AUX2) :: rp_goto L cid 3)
    & findopt (is_label_def (mk_entry L P C cid p)) cde = Some (nE i)].
Proof.
move=> Hi.
have Hsz : forall q, size (rp_entry L P C PI cid q) = 3 by [].
have Ec_split : Ec L P C PI cid
  = flatten [seq rp_entry L P C PI cid q | q <- take i (rp_exports PI cid)]
    ++ rp_entry L P C PI cid p
    ++ flatten [seq rp_entry L P C PI cid q | q <- drop i.+1 (rp_exports PI cid)].
{ have Hlt : i < size (rp_exports PI cid) := nth_error_size Hi.
  rewrite /Ec -{1}(cat_take_drop i (rp_exports PI cid)) map_cat flatten_cat.
  congr (_ ++ _).
  rewrite (drop_nth p Hlt).
  have -> : nth p (rp_exports PI cid) i = p.
  { have := nth_error_nth' p Hlt. by rewrite Hi => -[]. }
  by []. }
have Hpre : size (flatten [seq rp_entry L P C PI cid q | q <- take i (rp_exports PI cid)]) = 3 * i.
{ have Hlt : i < size (rp_exports PI cid) := nth_error_size Hi.
  have Hc3 : forall (s : seq nat), sumn [seq 3 | _ <- s] = 3 * size s.
  { by elim => [|x s IH] //=; rewrite IH mulnS. }
  rewrite size_flatten /shape -map_comp (eq_map (fun q => Hsz q)) Hc3 size_take Hlt. by []. }
have Ecell : cde = (Apre ++ Sc L PB t cid
                    ++ flatten [seq rp_entry L P C PI cid q | q <- take i (rp_exports PI cid)])
                   ++ rp_entry L P C PI cid p
                   ++ (flatten [seq rp_entry L P C PI cid q | q <- drop i.+1 (rp_exports PI cid)]
                       ++ rp_tagged cid (Tl L P C PB t cid) ++ Bpost).
{ by rewrite Hsplit (cc_split L P C PI PB t) Ec_split -!catA. }
have HnE : nE i = size (Apre ++ Sc L PB t cid
                    ++ flatten [seq rp_entry L P C PI cid q | q <- take i (rp_exports PI cid)]).
{ by rewrite !size_cat Hpre addnA. }
have Hcell : List.nth_error cde (nE i)
             = Some (MrLabel (mk_entry L P C cid p), Transitional.head_tag_gen PI cid p).
{ have E0 : forall (A : Type) (l1 l2 : seq A),
      List.nth_error (l1 ++ l2) (size l1) = List.nth_error l2 0.
  { move=> A l1 l2. by elim: l1. }
  by rewrite HnE Ecell E0. }
split.
- exact: Hcell.
- move=> j Hj. rewrite HnE addSn -addnS Ecell nth_error_cat_r.
  by case: j Hj => [|[|j]].
- apply: (findopt_unique_pos (count_label_le1 _ Huniq) Hcell).
  by rewrite /is_label_def /= eqxx.
Qed.

Lemma cc_color x :
  List.In x (rp_comp_code L P C PI PB t cid) -> color x.2 = cid.
Proof.
rewrite (cc_split L P C PI PB t) => Hx.
have Htag : forall l y, List.In y (rp_tagged cid l) -> color y.2 = cid.
{ move=> l y. rewrite /rp_tagged => /List.in_map_iff [i [<- _]]. by []. }
case: (List.in_app_or _ _ _ Hx) => {}Hx.
- move: Hx. rewrite /Sc. case: (cid == Component.main) => // Hx. exact: Htag Hx.
- case: (List.in_app_or _ _ _ Hx) => {}Hx; last exact: Htag Hx.
  move: Hx. rewrite /Ec => /In_flatten_map [p [_ Hy]].
  by move: Hy => /= [<-|[<-|[<-|[]]]].
Qed.

Lemma nxt_block n :
  size Apre <= n -> n < size Apre + size (rp_comp_code L P C PI PB t cid) -> nxt cde n cid.
Proof.
move=> H1 H2.
have Hn : n - size Apre < size (rp_comp_code L P C PI PB t cid) by lia.
have Hn' : n - size Apre < length (rp_comp_code L P C PI PB t cid) by rewrite lin_size_length.
have [x Hx] := nth_error_Some_ex Hn'.
exists x.1, x.2. split.
- rewrite Hsplit -(subnKC H1) nth_error_cat_r nth_error_cat_l //. by case: x Hx.
- apply: cc_color. exact: List.nth_error_In Hx.
Qed.

Lemma size_cc :
  size (rp_comp_code L P C PI PB t cid)
  = size (Sc L PB t cid) + 3 * size (rp_exports PI cid) + size (Tl L P C PB t cid).
Proof.
rewrite (cc_split L P C PI PB t) !size_cat size_tagged addnA.
congr (_ + _ + _).
rewrite /Ec size_flatten /shape -map_comp.
have -> : map (size \o rp_entry L P C PI cid) (rp_exports PI cid)
          = map (fun _ => 3) (rp_exports PI cid) by apply: eq_map.
elim: (rp_exports PI cid) => [|x s IH] //=. by rewrite IH mulnS.
Qed.

Lemma blk_start :
  cid = Component.main ->
  blk cde (size Apre) cid (rp_init L t cid AD 1 ++ rp_goto L cid 0).
Proof.
move=> Hm.
apply: (@blk_of_tagged cde Apre (Ec L P C PI cid ++ rp_tagged cid (Tl L P C PB t cid) ++ Bpost)).
rewrite Hsplit (cc_split L P C PI PB t) /Sc Hm eqxx.
by rewrite -!catA.
Qed.

End Pos.
