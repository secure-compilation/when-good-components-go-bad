Require Import Common.Definitions.
Require Import Common.Values.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import zify.
From CoqUtils Require Import word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.EncodeCode.
Require Import MicroPolicies.Recomposition.LabelScheme.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.LinearizeMerged.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Lemma lin_size_length (T : Type) (l : seq T) : length l = size l.
Proof. by elim: l => //= x l ->. Qed.

Lemma app_catE (T : Type) (l1 l2 : seq T) : List.app l1 l2 = l1 ++ l2.
Proof. by elim: l1 => //= x l1 ->. Qed.

Lemma map_nth_error_seq (A B : Type) (f : A -> B) n (l : seq A) d :
  List.nth_error l n = Some d ->
  List.nth_error [seq f x | x <- l] n = Some (f d).
Proof.
elim: l n => [|a l IH] [|n] //=.
- by move=> [= ->].
- exact: IH.
Qed.

Section T2MPos.

Variables (make : proc_label -> nat) (upd : Component.id -> nat -> nat).
Variable msz : NMap (NMap nat).

Definition cell_exp (itrt : Transitional.instr * mem_tag) :=
  [seq (i, itrt.2)
  | i <- instr_translation (mt := mt) make (upd (color itrt.2)) msz itrt.1].

Definition t2m_flat (l : seq (Transitional.instr * mem_tag)) :=
  foldr (fun itrt c => cell_exp itrt ++ c) [::] l.

Lemma t2m_genE (pb : NMap {fmap Block.id -> nat + seq value})
      (cde : Transitional.code) :
  msz = memory_lengths pb ->
  transitional_to_merged_gen (mt := mt) make upd pb cde
  = t2m_flat (flatten (map snd (Maps.elementsm cde))).
Proof.
move=> E.
rewrite /transitional_to_merged_gen /t2m_flat /cell_exp E; cbv zeta.
elim: (flatten _) => [|[itr t] l IH] //=.
by rewrite app_catE IH.
Qed.

Definition texp_size (itr : Transitional.instr) : nat :=
  match itr with TrAlloc _ _ => 5 | _ => 1 end.

Lemma size_cell_exp itrt : size (cell_exp itrt) = texp_size itrt.1.
Proof.
case: itrt => itr t.
rewrite /cell_exp size_map.
case: itr => //=.
by move=> [l|pl].
Qed.

Definition tseg_size (l : seq (Transitional.instr * mem_tag)) : nat :=
  sumn [seq texp_size x.1 | x <- l].

Lemma tseg_size_cons x l :
  tseg_size (x :: l) = texp_size x.1 + tseg_size l.
Proof. by []. Qed.

Lemma t2m_flat_cat l1 l2 :
  t2m_flat (l1 ++ l2) = t2m_flat l1 ++ t2m_flat l2.
Proof.
elim: l1 => [|x l1 IH] //=.
by rewrite IH catA.
Qed.

Lemma size_t2m_flat l : size (t2m_flat l) = tseg_size l.
Proof.
elim: l => [|x l IH] //=.
by rewrite size_cat size_cell_exp IH.
Qed.

Lemma t2m_flat_nth l j x k :
  List.nth_error l j = Some x ->
  k < texp_size x.1 ->
  List.nth_error (t2m_flat l) (tseg_size (take j l) + k)
  = List.nth_error (cell_exp x) k.
Proof.
elim: l j => [|y l IH] [|j] //.
-
  move=> [= E] Hk; subst x.
  rewrite take0.
  have -> : tseg_size [::] = 0 by [].
  have -> : t2m_flat (y :: l) = cell_exp y ++ t2m_flat l by [].
  rewrite List.nth_error_app1 //.
  rewrite lin_size_length size_cell_exp. by lia.
-
  move=> Hj Hk.
  have -> : take j.+1 (y :: l) = y :: take j l by [].
  have -> : tseg_size (y :: take j l) = texp_size y.1 + tseg_size (take j l) by [].
  have -> : t2m_flat (y :: l) = cell_exp y ++ t2m_flat l by [].
  have Hlen : length (cell_exp y) = texp_size y.1.
  { by rewrite lin_size_length size_cell_exp. }
  rewrite List.nth_error_app2; last by rewrite Hlen; lia.
  rewrite Hlen.
  have -> : Nat.sub (texp_size y.1 + tseg_size (take j l) + k) (texp_size y.1)
            = tseg_size (take j l) + k by lia.
  exact: (IH j Hj Hk).
Qed.

End T2MPos.

Definition isize (i : Machine.instr) : nat :=
  match i with IAlloc _ _ => 5 | _ => 1 end.

Lemma texp_isize c i : texp_size (instr_to_transitional c i).1 = isize i.
Proof.
case: i => //=.
by move=> c' P; case: (Nat.eqb c c').
Qed.

Lemma tseg_size_map c (l : seq Machine.instr) :
  tseg_size [seq instr_to_transitional c i | i <- l]
  = sumn [seq isize i | i <- l].
Proof.
elim: l => [|i0 l IH] //.
rewrite map_cons tseg_size_cons IH texp_isize.
by [].
Qed.

Definition proc_off (Pcode : seq Machine.instr) (o : nat) : nat :=
  1 + sumn [seq isize i | i <- take o Pcode].

Section ProcSegment.

Variables (make : proc_label -> nat) (upd : Component.id -> nat -> nat).
Variable msz : NMap (NMap nat).
Variable pr : Intermediate.program.

Lemma linearize_proc_nth c p Cprocs Pcode o i k :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some i ->
  k < isize i ->
  List.nth_error (t2m_flat make upd msz (linearize_proc pr c p))
                 (proc_off Pcode o + k)
  = List.nth_error (cell_exp make upd msz (instr_to_transitional c i)) k.
Proof.
move=> HC HP Ho Hk.
have -> : linearize_proc pr c p
          = (TrLabel (inr (c, p)), head_tag pr c p)
              :: [seq instr_to_transitional c i0 | i0 <- Pcode].
{ by rewrite /linearize_proc HC /= HP. }
have -> : t2m_flat make upd msz
            ((TrLabel (inr (c, p)), head_tag pr c p)
               :: [seq instr_to_transitional c i0 | i0 <- Pcode])
          = List.app
              (cell_exp make upd msz (TrLabel (inr (c, p)), head_tag pr c p))
              (t2m_flat make upd msz [seq instr_to_transitional c i0 | i0 <- Pcode])
  by rewrite app_catE.
have Hentry :
  length (cell_exp make upd msz (TrLabel (inr (c, p)), head_tag pr c p)) = 1.
{ by rewrite lin_size_length size_cell_exp. }
rewrite List.nth_error_app2; last by rewrite Hentry /proc_off; lia.
rewrite Hentry.
have -> : Nat.sub (proc_off Pcode o + k) 1
          = tseg_size (take o [seq instr_to_transitional c i0 | i0 <- Pcode]) + k.
{ rewrite /proc_off -map_take tseg_size_map. by lia. }
apply: t2m_flat_nth.
- apply: map_nth_error_seq. exact: Ho.
- by rewrite texp_isize.
Qed.

End ProcSegment.

Lemma sumn_consE (a : nat) (l : seq nat) : sumn (a :: l) = a + sumn l.
Proof. by []. Qed.

Lemma take_consSE (A : Type) (x : A) (s : seq A) j :
  take j.+1 (x :: s) = x :: take j s.
Proof. by []. Qed.

Lemma nth_error_cat1 (A : Type) (l1 l2 : seq A) n :
  n < size l1 ->
  List.nth_error (l1 ++ l2) n = List.nth_error l1 n.
Proof.
elim: l1 n => [|x l1 IH] [|n] //=.
exact: IH.
Qed.

Lemma nth_error_cat2 (A : Type) (l1 l2 : seq A) n :
  List.nth_error (l1 ++ l2) (size l1 + n) = List.nth_error l2 n.
Proof.
by elim: l1 => [|x l1 IH] //=.
Qed.

Lemma flatten_nth_error (A : Type) (ll : seq (seq A)) j l k :
  List.nth_error ll j = Some l ->
  k < size l ->
  List.nth_error (flatten ll) (sumn [seq size s | s <- take j ll] + k)
  = List.nth_error l k.
Proof.
elim: ll j => [|s ll IH] [|j] //.
-
  move=> [= E] Hk; subst s.
  have -> : flatten (l :: ll) = l ++ flatten ll by [].
  have -> : sumn [seq size s0 | s0 <- take 0 (l :: ll)] + k = k by [].
  by rewrite nth_error_cat1.
-
  move=> Hj Hk.
  have -> : take j.+1 (s :: ll) = s :: take j ll by [].
  have -> : sumn [seq size s0 | s0 <- s :: take j ll]
            = size s + sumn [seq size s0 | s0 <- take j ll] by [].
  have -> : flatten (s :: ll) = s ++ flatten ll by [].
  have -> : size s + sumn [seq size s0 | s0 <- take j ll] + k
            = size s + (sumn [seq size s0 | s0 <- take j ll] + k)
    by rewrite addnA.
  rewrite nth_error_cat2.
  exact: (IH j Hj Hk).
Qed.

Lemma sumn_take_le (l : seq nat) j a :
  List.nth_error l j = Some a ->
  sumn (take j l) + a <= sumn l.
Proof.
elim: l j => [|x l IH] [|j] //=.
- move=> [= E]; subst a. by lia.
- move=> Ho. have := IH j Ho. by lia.
Qed.

Lemma nth_error_index (T : eqType) (s : seq T) x :
  x \in s ->
  List.nth_error s (seq.index x s) = Some x.
Proof.
elim: s => [|a s IH] //=.
move=> Hin; rewrite in_cons in Hin.
case E: (a == x) => /=.
- by move/eqP: E => ->.
- case/orP: Hin => [Hxa|Hx].
  + by rewrite eq_sym E in Hxa.
  + exact: (IH Hx).
Qed.

Lemma nth_error_index_assoc (A : Type) (l : seq (nat * A)) c v :
  uniq (unzip1 l) ->
  List.In (c, v) l ->
  List.nth_error l (seq.index c (unzip1 l)) = Some (c, v).
Proof.
elim: l => [|[k a] l IH] //=.
move=> /andP [Hk Hu] [E|HIn].
- case: E => Ek Ea; subst k a. by rewrite eqxx.
- case E: (k == c) => /=.
  + move/eqP: E => ?; subst k.
    have Hcin : c \in unzip1 l.
    { apply: List_In_mem. exact: (List.in_map fst l (c, v) HIn). }
    by rewrite Hcin in Hk.
  + exact: (IH Hu HIn).
Qed.

Lemma elementsm_keys_uniq (A : Type) (m : NMap A) :
  uniq (unzip1 (Maps.elementsm m)).
Proof.
have Hs : sorted Ord.lt (unzip1 (Maps.elementsm m)) by case: m.
exact: (sorted_uniq (@Ord.lt_trans _) (@Ord.ltxx _) Hs).
Qed.

Lemma nth_error_elementsm (A : Type) (m : NMap A) c v :
  m c = Some v ->
  List.nth_error (Maps.elementsm m)
                 (seq.index c (unzip1 (Maps.elementsm m)))
  = Some (c, v).
Proof.
move=> Hc.
apply: nth_error_index_assoc; first exact: elementsm_keys_uniq.
exact: (getm_In Hc).
Qed.

Lemma nth_error_size (A : Type) (l : seq A) o x :
  List.nth_error l o = Some x -> o < size l.
Proof.
elim: l o => [|a l IH] [|o] //=.
exact: IH.
Qed.

Lemma nth_error_nth_d (A : Type) (d : A) (l : seq A) o x :
  List.nth_error l o = Some x -> nth d l o = x.
Proof.
elim: l o => [|a l IH] [|o] //=.
- by move=> [= ->].
- exact: IH.
Qed.

Lemma tseg_size_cat (l1 l2 : seq (Transitional.instr * mem_tag)) :
  tseg_size (l1 ++ l2) = tseg_size l1 + tseg_size l2.
Proof.
elim: l1 => [|x l1 IH] //.
have -> : (x :: l1) ++ l2 = x :: (l1 ++ l2) by [].
rewrite !tseg_size_cons IH.
by rewrite addnA.
Qed.

Lemma tseg_size_flatten (ll : seq (seq (Transitional.instr * mem_tag))) :
  tseg_size (flatten ll) = sumn [seq tseg_size l | l <- ll].
Proof.
elim: ll => [|s ll IH] //.
have -> : flatten (s :: ll) = s ++ flatten ll by [].
rewrite tseg_size_cat IH.
by rewrite map_cons sumn_consE.
Qed.

Lemma isize_gt0 (i : Machine.instr) : 0 < isize i.
Proof. by case: i. Qed.

Lemma proc_off_S (Pcode : seq Machine.instr) o i :
  List.nth_error Pcode o = Some i ->
  proc_off Pcode o.+1 = proc_off Pcode o + isize i.
Proof.
move=> Ho.
rewrite /proc_off (take_nth i (nth_error_size Ho)) (nth_error_nth_d i Ho).
rewrite -cats1 map_cat sumn_cat /=.
by lia.
Qed.

Definition comp_procs (pr : Intermediate.program) (c : Component.id)
  : seq Procedure.id :=
  domm (odflt emptym (Intermediate.prog_procedures pr c)).

Definition proc_base (pr : Intermediate.program) (c : Component.id)
    (p : Procedure.id) : nat :=
  sumn (take (seq.index p (comp_procs pr c))
             [seq tseg_size (linearize_proc pr c p') | p' <- comp_procs pr c]).

Definition comp_base (cde : Transitional.code) (c : Component.id) : nat :=
  sumn (take (seq.index c (unzip1 (Maps.elementsm cde)))
             [seq tseg_size x.2 | x <- Maps.elementsm cde]).

Definition flat_pos (pr : Intermediate.program) (c : Component.id)
    (p : Procedure.id) (Pcode : seq Machine.instr) (o : nat) : nat :=
  comp_base (intermediate_to_transitional pr) c
  + (proc_base pr c p + proc_off Pcode o).

Section Assembly.

Variables (make : proc_label -> nat) (upd : Component.id -> nat -> nat).
Variable msz : NMap (NMap nat).
Variable pr : Intermediate.program.

Lemma t2m_flat_flatten (ll : seq (seq (Transitional.instr * mem_tag))) :
  t2m_flat make upd msz (flatten ll)
  = flatten [seq t2m_flat make upd msz l | l <- ll].
Proof.
elim: ll => [|s ll IH] //.
have -> : flatten (s :: ll) = s ++ flatten ll by [].
rewrite t2m_flat_cat IH.
have -> : [seq t2m_flat make upd msz l | l <- s :: ll]
          = t2m_flat make upd msz s :: [seq t2m_flat make upd msz l | l <- ll]
  by [].
have -> : flatten (t2m_flat make upd msz s
                     :: [seq t2m_flat make upd msz l | l <- ll])
          = t2m_flat make upd msz s
            ++ flatten [seq t2m_flat make upd msz l | l <- ll] by [].
by [].
Qed.

Lemma sumn_size_take_t2m_linproc (c : Component.id)
    (procs : seq Procedure.id) j :
  sumn [seq size s
       | s <- take j [seq t2m_flat make upd msz (linearize_proc pr c p')
                     | p' <- procs]]
  = sumn (take j [seq tseg_size (linearize_proc pr c p') | p' <- procs]).
Proof.
elim: procs j => [|q procs IH] [|j] //.
have -> : take j.+1 [seq t2m_flat make upd msz (linearize_proc pr c p')
                    | p' <- q :: procs]
          = t2m_flat make upd msz (linearize_proc pr c q)
            :: take j [seq t2m_flat make upd msz (linearize_proc pr c p')
                      | p' <- procs] by [].
have -> : take j.+1 [seq tseg_size (linearize_proc pr c p') | p' <- q :: procs]
          = tseg_size (linearize_proc pr c q)
            :: take j [seq tseg_size (linearize_proc pr c p') | p' <- procs]
  by [].
have -> : [seq size s
          | s <- t2m_flat make upd msz (linearize_proc pr c q)
                 :: take j [seq t2m_flat make upd msz (linearize_proc pr c p')
                           | p' <- procs]]
          = size (t2m_flat make upd msz (linearize_proc pr c q))
            :: [seq size s
               | s <- take j [seq t2m_flat make upd msz (linearize_proc pr c p')
                             | p' <- procs]] by [].
rewrite !sumn_consE size_t2m_flat IH.
by [].
Qed.

Lemma sumn_size_take_t2m_snd
    (l : seq (nat * seq (Transitional.instr * mem_tag))) j :
  sumn [seq size s
       | s <- take j [seq t2m_flat make upd msz s0 | s0 <- map snd l]]
  = sumn (take j [seq tseg_size x.2 | x <- l]).
Proof.
elim: l j => [|x l IH] [|j] //.
have -> : take j.+1 [seq t2m_flat make upd msz s0 | s0 <- map snd (x :: l)]
          = t2m_flat make upd msz (snd x)
            :: take j [seq t2m_flat make upd msz s0 | s0 <- map snd l] by [].
have -> : take j.+1 [seq tseg_size x0.2 | x0 <- x :: l]
          = tseg_size x.2 :: take j [seq tseg_size x0.2 | x0 <- l] by [].
have -> : [seq size s
          | s <- t2m_flat make upd msz (snd x)
                 :: take j [seq t2m_flat make upd msz s0 | s0 <- map snd l]]
          = size (t2m_flat make upd msz (snd x))
            :: [seq size s
               | s <- take j [seq t2m_flat make upd msz s0 | s0 <- map snd l]]
  by [].
rewrite !sumn_consE size_t2m_flat IH.
by [].
Qed.

Lemma proc_off_lt (c : Component.id) Cprocs p Pcode o i k :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some i ->
  k < isize i ->
  proc_off Pcode o + k < tseg_size (linearize_proc pr c p).
Proof.
move=> HC HP Ho Hk.
have -> : linearize_proc pr c p
          = (TrLabel (inr (c, p)), head_tag pr c p)
              :: [seq instr_to_transitional c i0 | i0 <- Pcode].
{ by rewrite /linearize_proc HC /= HP. }
rewrite tseg_size_cons tseg_size_map /proc_off.
have -> : texp_size (TrLabel (inr (c, p)), head_tag pr c p).1 = 1 by [].
have Hnth : List.nth_error [seq isize x | x <- Pcode] o = Some (isize i).
{ apply: map_nth_error_seq. exact: Ho. }
have Hle := sumn_take_le Hnth.
rewrite -map_take in Hle.
by lia.
Qed.

Lemma tseg_size_lincomp (c : Component.id) Cprocs :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  tseg_size (linearize_component pr c)
  = sumn [seq tseg_size (linearize_proc pr c p') | p' <- domm Cprocs].
Proof.
move=> HC.
have -> : linearize_component pr c
          = flatten [seq linearize_proc pr c p' | p' <- domm Cprocs].
{ by rewrite /linearize_component HC. }
rewrite tseg_size_flatten.
by rewrite -map_comp.
Qed.

Lemma linearize_component_nth (c : Component.id) Cprocs p Pcode o i k :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some i ->
  k < isize i ->
  List.nth_error (t2m_flat make upd msz (linearize_component pr c))
                 (proc_base pr c p + (proc_off Pcode o + k))
  = List.nth_error (cell_exp make upd msz (instr_to_transitional c i)) k.
Proof.
move=> HC HP Ho Hk.
have -> : linearize_component pr c
          = flatten [seq linearize_proc pr c p' | p' <- domm Cprocs].
{ by rewrite /linearize_component HC. }
rewrite t2m_flat_flatten.
have -> : [seq t2m_flat make upd msz l
          | l <- [seq linearize_proc pr c p' | p' <- domm Cprocs]]
          = [seq t2m_flat make upd msz (linearize_proc pr c p')
            | p' <- domm Cprocs].
{ by rewrite -map_comp. }
have Hpin : p \in domm Cprocs by rewrite mem_domm HP.
have Hprocs : comp_procs pr c = domm Cprocs.
{ by rewrite /comp_procs HC. }
rewrite /proc_base Hprocs.
rewrite -(sumn_size_take_t2m_linproc c (domm Cprocs)
            (seq.index p (domm Cprocs))).
have Hj : List.nth_error
            [seq t2m_flat make upd msz (linearize_proc pr c p')
            | p' <- domm Cprocs]
            (seq.index p (domm Cprocs))
          = Some (t2m_flat make upd msz (linearize_proc pr c p)).
{ apply: map_nth_error_seq. exact: (nth_error_index Hpin). }
have Hb : proc_off Pcode o + k
          < size (t2m_flat make upd msz (linearize_proc pr c p)).
{ rewrite size_t2m_flat. exact: (proc_off_lt HC HP Ho Hk). }
rewrite (flatten_nth_error Hj Hb).
exact: (linearize_proc_nth make upd msz HC HP Ho Hk).
Qed.

Lemma t2m_flat_code_nth (cde : Transitional.code) (c : Component.id) cseg q :
  cde c = Some cseg ->
  q < tseg_size cseg ->
  List.nth_error
    (t2m_flat make upd msz (flatten (map snd (Maps.elementsm cde))))
    (comp_base cde c + q)
  = List.nth_error (t2m_flat make upd msz cseg) q.
Proof.
move=> Hc Hq.
rewrite t2m_flat_flatten.
have He := nth_error_elementsm Hc.
have Hj : List.nth_error
            [seq t2m_flat make upd msz l | l <- map snd (Maps.elementsm cde)]
            (seq.index c (unzip1 (Maps.elementsm cde)))
          = Some (t2m_flat make upd msz cseg).
{ apply: map_nth_error_seq.
  exact: (map_nth_error_seq snd He). }
rewrite /comp_base.
rewrite -(sumn_size_take_t2m_snd (Maps.elementsm cde)
            (seq.index c (unzip1 (Maps.elementsm cde)))).
have Hqb : q < size (t2m_flat make upd msz cseg) by rewrite size_t2m_flat.
rewrite (flatten_nth_error Hj Hqb).
by [].
Qed.

Lemma lin_gen_nth (c : Component.id) Cprocs p Pcode o i k :
  msz = memory_lengths (Intermediate.prog_buffers pr) ->
  Intermediate.prog_procedures pr c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some i ->
  k < isize i ->
  List.nth_error (lin_gen pr make upd) (flat_pos pr c p Pcode o + k)
  = List.nth_error (cell_exp make upd msz (instr_to_transitional c i)) k.
Proof.
move=> E HC HP Ho Hk.
have -> : lin_gen pr make upd
          = transitional_to_merged_gen (mt := mt) make upd
              (Intermediate.prog_buffers pr)
              (intermediate_to_transitional pr) by [].
rewrite (t2m_genE make upd (intermediate_to_transitional pr) E).
rewrite /flat_pos.
have Hcget : intermediate_to_transitional pr c
             = Some (linearize_component pr c).
{ by rewrite i2t_getm HC. }
have -> : comp_base (intermediate_to_transitional pr) c
            + (proc_base pr c p + proc_off Pcode o) + k
          = comp_base (intermediate_to_transitional pr) c
            + (proc_base pr c p + (proc_off Pcode o + k)) by lia.
have Hpin : p \in domm Cprocs by rewrite mem_domm HP.
have Hprocs : comp_procs pr c = domm Cprocs.
{ by rewrite /comp_procs HC. }
have Hb1 := proc_off_lt HC HP Ho Hk.
have Hnths : List.nth_error
               [seq tseg_size (linearize_proc pr c p') | p' <- domm Cprocs]
               (seq.index p (domm Cprocs))
             = Some (tseg_size (linearize_proc pr c p)).
{ apply: map_nth_error_seq. exact: (nth_error_index Hpin). }
have Hb2 := sumn_take_le Hnths.
have Htotal := tseg_size_lincomp HC.
have Hbound : proc_base pr c p + (proc_off Pcode o + k)
              < tseg_size (linearize_component pr c).
{ rewrite /proc_base Hprocs Htotal.
  apply: leq_trans Hb2.
  rewrite ltn_add2l.
  exact: Hb1. }
rewrite (t2m_flat_code_nth Hcget Hbound).
exact: (linearize_component_nth HC HP Ho Hk).
Qed.

Lemma tseg_size_linproc_gt0 (c : Component.id) Cprocs p Pcode :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  0 < tseg_size (linearize_proc pr c p).
Proof.
move=> HC HP.
have -> : linearize_proc pr c p
          = (TrLabel (inr (c, p)), head_tag pr c p)
              :: [seq instr_to_transitional c i0 | i0 <- Pcode].
{ by rewrite /linearize_proc HC /= HP. }
by [].
Qed.

Lemma linearize_proc_entry (c : Component.id) Cprocs p Pcode :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  List.nth_error (t2m_flat make upd msz (linearize_proc pr c p)) 0
  = Some (MrLabel (make (c, p)), head_tag pr c p).
Proof.
move=> HC HP.
have -> : linearize_proc pr c p
          = (TrLabel (inr (c, p)), head_tag pr c p)
              :: [seq instr_to_transitional c i0 | i0 <- Pcode].
{ by rewrite /linearize_proc HC /= HP. }
by [].
Qed.

Lemma linearize_component_seg (c : Component.id) Cprocs p q :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  p \in domm Cprocs ->
  q < tseg_size (linearize_proc pr c p) ->
  List.nth_error (t2m_flat make upd msz (linearize_component pr c))
                 (proc_base pr c p + q)
  = List.nth_error (t2m_flat make upd msz (linearize_proc pr c p)) q.
Proof.
move=> HC Hpin Hq.
have -> : linearize_component pr c
          = flatten [seq linearize_proc pr c p' | p' <- domm Cprocs].
{ by rewrite /linearize_component HC. }
rewrite t2m_flat_flatten.
have -> : [seq t2m_flat make upd msz l
          | l <- [seq linearize_proc pr c p' | p' <- domm Cprocs]]
          = [seq t2m_flat make upd msz (linearize_proc pr c p')
            | p' <- domm Cprocs].
{ by rewrite -map_comp. }
have Hprocs : comp_procs pr c = domm Cprocs.
{ by rewrite /comp_procs HC. }
rewrite /proc_base Hprocs.
rewrite -(sumn_size_take_t2m_linproc c (domm Cprocs)
            (seq.index p (domm Cprocs))).
have Hj : List.nth_error
            [seq t2m_flat make upd msz (linearize_proc pr c p')
            | p' <- domm Cprocs]
            (seq.index p (domm Cprocs))
          = Some (t2m_flat make upd msz (linearize_proc pr c p)).
{ apply: map_nth_error_seq. exact: (nth_error_index Hpin). }
have Hb : q < size (t2m_flat make upd msz (linearize_proc pr c p)).
{ by rewrite size_t2m_flat. }
by rewrite (flatten_nth_error Hj Hb).
Qed.

Lemma lin_gen_seg (c : Component.id) cseg q :
  msz = memory_lengths (Intermediate.prog_buffers pr) ->
  intermediate_to_transitional pr c = Some cseg ->
  q < tseg_size cseg ->
  List.nth_error (lin_gen pr make upd)
                 (comp_base (intermediate_to_transitional pr) c + q)
  = List.nth_error (t2m_flat make upd msz cseg) q.
Proof.
move=> E Hc Hq.
have -> : lin_gen pr make upd
          = transitional_to_merged_gen (mt := mt) make upd
              (Intermediate.prog_buffers pr)
              (intermediate_to_transitional pr) by [].
rewrite (t2m_genE make upd (intermediate_to_transitional pr) E).
exact: (t2m_flat_code_nth Hc Hq).
Qed.

Lemma lin_gen_entry_nth (c : Component.id) Cprocs p Pcode :
  msz = memory_lengths (Intermediate.prog_buffers pr) ->
  Intermediate.prog_procedures pr c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  List.nth_error (lin_gen pr make upd)
                 (comp_base (intermediate_to_transitional pr) c
                  + (proc_base pr c p + 0))
  = Some (MrLabel (make (c, p)), head_tag pr c p).
Proof.
move=> E HC HP.
have Hcget : intermediate_to_transitional pr c
             = Some (linearize_component pr c).
{ by rewrite i2t_getm HC. }
have Hpin : p \in domm Cprocs by rewrite mem_domm HP.
have Hprocs : comp_procs pr c = domm Cprocs.
{ by rewrite /comp_procs HC. }
have Hb1 := tseg_size_linproc_gt0 HC HP.
have Hnths : List.nth_error
               [seq tseg_size (linearize_proc pr c p') | p' <- domm Cprocs]
               (seq.index p (domm Cprocs))
             = Some (tseg_size (linearize_proc pr c p)).
{ apply: map_nth_error_seq. exact: (nth_error_index Hpin). }
have Hb2 := sumn_take_le Hnths.
have Htotal := tseg_size_lincomp HC.
have Hbound : proc_base pr c p + 0 < tseg_size (linearize_component pr c).
{ rewrite /proc_base Hprocs Htotal.
  apply: leq_trans Hb2.
  rewrite ltn_add2l.
  exact: Hb1. }
rewrite (lin_gen_seg E Hcget Hbound).
rewrite (linearize_component_seg HC Hpin Hb1).
exact: (linearize_proc_entry HC HP).
Qed.

End Assembly.

Lemma count_In0 (A : Type) (pe : A -> bool) (l : seq A) :
  (forall x, List.In x l -> pe x = false) -> count pe l = 0.
Proof.
elim: l => [|a l IH] //= Hz.
rewrite Hz; last by left.
rewrite IH //. by move=> x Hx; apply: Hz; right.
Qed.

Lemma sumn_le_pred (T : eqType) (s : seq T) (x : T) (g : T -> nat) :
  uniq s ->
  (forall y, List.In y s -> g y <= nat_of_bool (y == x)) ->
  sumn [seq g y | y <- s] <= 1.
Proof.
elim: s => [|a s IH] //= /andP [Ha Hu] Hb.
case E: (a == x).
- move/eqP: E => ?; subst a.
  have H0 : sumn [seq g y | y <- s] = 0.
  { apply: sumn_map_eq0 => y HIn.
    have := Hb y (or_intror HIn).
    case Ey: (y == x) => //=; last by lia.
    move/eqP: Ey => ?; subst y.
    by rewrite (List_In_mem HIn) in Ha. }
  rewrite H0 addn0.
  have := Hb x (or_introl erefl). by rewrite eqxx.
- have := Hb a (or_introl erefl). rewrite E => /= Hga.
  have Hg0 : g a = 0 by lia.
  rewrite Hg0 add0n. apply: IH => // y HIn. by apply: Hb; right.
Qed.

Lemma findopt_unique_pos (A : Type) (pe : A -> bool) (l : seq A) n x :
  count pe l <= 1 ->
  List.nth_error l n = Some x ->
  pe x ->
  findopt pe l = Some n.
Proof.
move=> Hc Hn Hpx.
have HIn := List.nth_error_In _ _ Hn.
have [m Hm] := findopt_In_ex HIn Hpx.
have [y [Hym Hpy]] := findopt_nth Hm.
have Enm : n = m.
{ exact: (count_le1_nth_unique Hc Hn Hpx Hym Hpy). }
by rewrite Hm Enm.
Qed.

Definition code_label_pos (cde : @Merged.code mt) (pc0 : nat)
    (l default : nat) : nat :=
  match findopt (is_label_def l) cde with
  | Some m => pc0 + m
  | None => if l == alloc_label then l else default
  end.

Lemma encode_code_fetch (cde : @Merged.code mt) (pc0 n : nat)
    (i : @Merged.instr mt) (t : mem_tag) :
  pc0 + size cde < 2 ^ word_size mt ->
  List.nth_error cde n = Some (i, t) ->
  exists v : matom,
    encode_code cde pc0 (word_of_nat (n + pc0)) = Some v
    /\ taga v = t
    /\ vala v = encode_instr_mp
                  (instr_merged_to_mp i (code_label_pos cde pc0) (pc0 + n)).
Proof.
move=> Hbound Hn.
have Hlt : n < size cde := nth_error_size Hn.
pose flist : seq matom
  := (foldr (fun (x : Merged.instr * mem_tag) (acc : seq matom * nat) =>
    (encode_instr_atom (ops := ops) x
      (fun l default =>
         match findopt (fun p => match p.1 with
                                 | MrLabel l0 => l == l0
                                 | _ => false end) cde
         with Some m => pc0 + m
            | None => if l == alloc_label then l else default end)
      (pc0 + size cde - 1 - acc.2) :: acc.1, acc.2.+1)) ([::], 0) cde).1.
have Hsz : size flist = size cde by exact: encode_code_foldr_size.
have Hlen : n < length flist.
{ rewrite lin_size_length Hsz. exact: Hlt. }
have [v Hv] := nth_error_Some_ex Hlen.
have [i' [t' [Hn' [Htag Hval]]]] := encode_code_foldr_nth Hv.
rewrite Hn in Hn'. case: Hn' => Ei Et. subst i'.
have Epos : pc0 + size cde - 1 - (size cde - 1 - n) = pc0 + n by lia.
rewrite Epos in Hval.
exists v.
split.
- exact: (encode_code_nth (@won_inj (word_size mt)) Hbound Hv).
- split.
  + by rewrite Htag -Et.
  + exact: Hval.
Qed.

Definition tlab_pred (lab : nat) (make : proc_label -> nat)
    (upd : Component.id -> nat -> nat)
    (cell : Transitional.instr * mem_tag) : bool :=
  match cell.1 with
  | TrLabel (inl l) => lab == upd (color cell.2) l
  | TrLabel (inr pl) => lab == make pl
  | _ => false
  end.

Lemma t2m_count_label (lab : nat) (make : proc_label -> nat)
    (upd : Component.id -> nat -> nat)
    (pb : NMap {fmap Block.id -> nat + seq value}) (cde : Transitional.code) :
  count (is_label_def lab)
        (transitional_to_merged_gen (mt := mt) make upd pb cde)
  = count (tlab_pred lab make upd)
          (flatten (map snd (Maps.elementsm cde))).
Proof.
rewrite /transitional_to_merged_gen.
elim: (flatten (map snd (Maps.elementsm cde))) => [|[itr t] s IH] //=.
rewrite app_cat count_cat IH.
congr (_ + _).
case: itr => //=.
by move=> [l|pl] /=; rewrite ssrnat.addn0.
Qed.

Section LabelResolution.

Variables L P C : nat.
Variable pr : Intermediate.program.

Hypothesis Hlab_bound : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures pr cid = Some Cprocs ->
  Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hproc_bound : forall cid Cprocs Pid,
  Intermediate.prog_procedures pr cid = Some Cprocs ->
  Pid \in domm Cprocs -> Pid < P.
Hypothesis Hcomp_bound : forall cid,
  cid \in domm (Intermediate.prog_procedures pr) -> cid < C.

Variables (c : Component.id) (p : Procedure.id).
Hypothesis HpP : p < P.

Let lab := mk_entry L P C c p.

Lemma tlab_pred_entry (cp : Component.id) (pp : Procedure.id) :
  pp < P ->
  (lab == can_make L P C (cp, pp)) = ((cp == c) && (pp == p)).
Proof.
move=> HppP.
case E: ((cp == c) && (pp == p)).
- move/andP: E => [/eqP Ec /eqP Ep]; subst cp pp.
  by rewrite /lab /can_make /= eqxx.
- case El: (lab == can_make L P C (cp, pp)) => //.
  move/eqP: El. rewrite /lab /can_make /= => El.
  have [Ec Ep] := mk_entry_inj HpP HppP El.
  subst cp pp.
  by rewrite !eqxx in E.
Qed.

Lemma tlab_pred_body (cp : Component.id) (pp : Procedure.id)
    Cprocs' Pcode' (mi : Machine.instr) :
  Intermediate.prog_procedures pr cp = Some Cprocs' ->
  Cprocs' pp = Some Pcode' ->
  cp < C ->
  List.In mi Pcode' ->
  tlab_pred lab (can_make L P C) (can_upd L) (instr_to_transitional cp mi)
  = false.
Proof.
move=> HC' HP' HcpC HIn.
case: mi HIn => //=.
-
  move=> l HIn.
  case El: (lab == can_upd L cp l) => //.
  exfalso.
  move/eqP: El. rewrite /lab /can_upd => El.
  have HlL := Hlab_bound HC' HP' HIn.
  exact: (mk_body_entry_disjoint HcpC HlL (esym El)).
-
  move=> c0 P0 _. by case: (Nat.eqb cp c0).
Qed.

Lemma count_entry_linproc (cp : Component.id) (pp : Procedure.id)
    Cprocs' Pcode' :
  Intermediate.prog_procedures pr cp = Some Cprocs' ->
  Cprocs' pp = Some Pcode' ->
  cp < C -> pp < P ->
  count (tlab_pred lab (can_make L P C) (can_upd L)) (linearize_proc pr cp pp)
  = ((cp == c) && (pp == p)).
Proof.
move=> HC' HP' HcpC HppP.
have -> : linearize_proc pr cp pp
          = (TrLabel (inr (cp, pp)), head_tag pr cp pp)
              :: [seq instr_to_transitional cp i0 | i0 <- Pcode'].
{ by rewrite /linearize_proc HC' /= HP'. }
rewrite /=.
have -> : tlab_pred lab (can_make L P C) (can_upd L)
            (TrLabel (inr (cp, pp)), head_tag pr cp pp)
          = (lab == can_make L P C (cp, pp)) by [].
rewrite (tlab_pred_entry cp HppP).
have -> : count (tlab_pred lab (can_make L P C) (can_upd L))
                [seq instr_to_transitional cp i0 | i0 <- Pcode'] = 0.
{ apply: count_In0 => x Hx.
  move/List.in_map_iff: Hx => [mi [Emi HmiIn]].
  rewrite -Emi.
  exact: (tlab_pred_body HC' HP' HcpC HmiIn). }
by rewrite addn0.
Qed.

Lemma count_entry_lincomp (cp : Component.id) Cprocs' :
  Intermediate.prog_procedures pr cp = Some Cprocs' ->
  cp < C ->
  count (tlab_pred lab (can_make L P C) (can_upd L))
        (linearize_component pr cp)
  <= nat_of_bool (cp == c).
Proof.
move=> HC' HcpC.
have -> : linearize_component pr cp
          = flatten [seq linearize_proc pr cp p' | p' <- domm Cprocs'].
{ by rewrite /linearize_component HC'. }
rewrite count_flatten.
have -> : [seq count (tlab_pred lab (can_make L P C) (can_upd L)) l
          | l <- [seq linearize_proc pr cp p' | p' <- domm Cprocs']]
          = [seq count (tlab_pred lab (can_make L P C) (can_upd L))
                       (linearize_proc pr cp p')
            | p' <- domm Cprocs'].
{ by rewrite -map_comp. }
case Ecp: (cp == c).
-
  move/eqP: Ecp => ?; subst cp.
  apply: sumn_le_pred; first exact: uniq_fset.
  move=> p' HIn.
  have Hp'in : p' \in domm Cprocs' := List_In_mem HIn.
  move/dommP: (Hp'in) => [Pcode' HP'].
  rewrite (count_entry_linproc HC' HP' HcpC (Hproc_bound HC' Hp'in)).
  rewrite eqxx andTb.
  exact: leqnn.
-
  have H0 : sumn [seq count (tlab_pred lab (can_make L P C) (can_upd L))
                            (linearize_proc pr cp p')
                 | p' <- domm Cprocs'] = 0.
  { apply: sumn_map_eq0 => p' HIn.
    have Hp'in : p' \in domm Cprocs' := List_In_mem HIn.
    move/dommP: (Hp'in) => [Pcode' HP'].
    rewrite (count_entry_linproc HC' HP' HcpC (Hproc_bound HC' Hp'in)).
    by rewrite Ecp. }
  by rewrite H0.
Qed.

Lemma count_entry_flat :
  count (tlab_pred lab (can_make L P C) (can_upd L))
        (flatten (map snd (Maps.elementsm (intermediate_to_transitional pr))))
  <= 1.
Proof.
rewrite count_flatten.
have -> : [seq count (tlab_pred lab (can_make L P C) (can_upd L)) x
          | x <- map snd (Maps.elementsm (intermediate_to_transitional pr))]
          = [seq count (tlab_pred lab (can_make L P C) (can_upd L)) x.2
            | x <- Maps.elementsm (intermediate_to_transitional pr)].
{ by rewrite -map_comp. }
apply: (sumn_le1_uniq_keys (c0 := c)); first exact: elementsm_keys_uniq.
move=> k v HIn.
have Hkv : intermediate_to_transitional pr k = Some v := In_fmap_getm HIn.
move: Hkv. rewrite i2t_getm.
case Eprocs: (Intermediate.prog_procedures pr k) => [Cprocs'|] //= [Ev].
subst v.
have HkC : k < C.
{ apply: Hcomp_bound. by rewrite mem_domm Eprocs. }
have := count_entry_lincomp Eprocs HkC.
by case: (k == c).
Qed.

Lemma count_entry_lin_body :
  count (is_label_def lab) (lin_body L P C pr) <= 1.
Proof.
have -> : lin_body L P C pr
          = transitional_to_merged_gen (mt := mt) (can_make L P C) (can_upd L)
              (Intermediate.prog_buffers pr)
              (intermediate_to_transitional pr) by [].
rewrite t2m_count_label.
exact: count_entry_flat.
Qed.

Lemma count_entry_lin_code :
  count (is_label_def lab) (lin_code L P C pr) <= 1.
Proof.
rewrite /lin_code.
case E: (lin_body L P C pr) => [|cell rest] //.
have Hb := count_entry_lin_body. rewrite E in Hb.
rewrite -cats1 count_cat.
have -> : count (is_label_def lab)
            [:: (MrHalt, def_mem_tag (color (last cell rest).2) true)] = 0
  by [].
rewrite ssrnat.addn0.
exact: Hb.
Qed.

Lemma count_entry_flat_absent :
  c \notin domm (Intermediate.prog_procedures pr) ->
  count (tlab_pred lab (can_make L P C) (can_upd L))
        (flatten (map snd (Maps.elementsm (intermediate_to_transitional pr))))
  = 0.
Proof.
move=> Hnotin.
rewrite count_flatten.
have -> : [seq count (tlab_pred lab (can_make L P C) (can_upd L)) x
          | x <- map snd (Maps.elementsm (intermediate_to_transitional pr))]
          = [seq count (tlab_pred lab (can_make L P C) (can_upd L)) x.2
            | x <- Maps.elementsm (intermediate_to_transitional pr)].
{ by rewrite -map_comp. }
apply: sumn_map_eq0 => -[k v] HIn /=.
have Hkv : intermediate_to_transitional pr k = Some v := In_fmap_getm HIn.
move: Hkv. rewrite i2t_getm.
case Eprocs: (Intermediate.prog_procedures pr k) => [Cprocs'|] //= [Ev].
subst v.
have HkC : k < C.
{ apply: Hcomp_bound. by rewrite mem_domm Eprocs. }
have Hle := count_entry_lincomp Eprocs HkC.
have Ekc : (k == c) = false.
{ case Ekc: (k == c) => //. move/eqP: Ekc => ?; subst k.
  by rewrite mem_domm Eprocs in Hnotin. }
rewrite Ekc in Hle. by lia.
Qed.

Lemma count_entry_lin_code_absent :
  c \notin domm (Intermediate.prog_procedures pr) ->
  count (is_label_def lab) (lin_code L P C pr) = 0.
Proof.
move=> Hnotin.
have Hb : count (is_label_def lab) (lin_body L P C pr) = 0.
{ have -> : lin_body L P C pr
            = transitional_to_merged_gen (mt := mt) (can_make L P C) (can_upd L)
                (Intermediate.prog_buffers pr)
                (intermediate_to_transitional pr) by [].
  rewrite t2m_count_label.
  exact: (count_entry_flat_absent Hnotin). }
rewrite /lin_code.
case E: (lin_body L P C pr) => [|cell rest] //.
rewrite E in Hb.
rewrite -cats1 count_cat.
have -> : count (is_label_def lab)
            [:: (MrHalt, def_mem_tag (color (last cell rest).2) true)] = 0
  by [].
rewrite ssrnat.addn0.
exact: Hb.
Qed.

Lemma lin_code_entry_nth Cprocs Pcode :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  List.nth_error (lin_code L P C pr)
                 (comp_base (intermediate_to_transitional pr) c
                  + (proc_base pr c p + 0))
  = Some (MrLabel (can_make L P C (c, p)), head_tag pr c p).
Proof.
move=> HCc HPp.
have Hg := lin_gen_entry_nth (can_make L P C) (can_upd L)
             (erefl (memory_lengths (Intermediate.prog_buffers pr))) HCc HPp.
have Hg' : List.nth_error (lin_body L P C pr)
             (comp_base (intermediate_to_transitional pr) c
              + (proc_base pr c p + 0))
           = Some (MrLabel (can_make L P C (c, p)), head_tag pr c p)
  by exact: Hg.
rewrite /lin_code.
case E: (lin_body L P C pr) => [|cell rest].
- rewrite E in Hg'.
  by case: (comp_base (intermediate_to_transitional pr) c
            + (proc_base pr c p + 0)) Hg'.
- rewrite E in Hg'.
  rewrite -cats1 nth_error_cat1; first exact: Hg'.
  exact: (nth_error_size Hg').
Qed.

Lemma lin_code_entry_findopt Cprocs Pcode :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  findopt (is_label_def lab) (lin_code L P C pr)
  = Some (comp_base (intermediate_to_transitional pr) c
          + (proc_base pr c p + 0)).
Proof.
move=> HCc HPp.
apply: (findopt_unique_pos count_entry_lin_code (lin_code_entry_nth HCc HPp)).
by rewrite /is_label_def /= /lab /can_make /= eqxx.
Qed.

Lemma code_label_pos_entry Cprocs Pcode (pc0 default : nat) :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  code_label_pos (lin_code L P C pr) pc0 lab default
  = pc0 + (comp_base (intermediate_to_transitional pr) c
           + (proc_base pr c p + 0)).
Proof.
move=> HCc HPp.
rewrite /code_label_pos (lin_code_entry_findopt HCc HPp).
by [].
Qed.

End LabelResolution.

Section LinkResolution.

Variables L P C : nat.
Variables pra prb : Intermediate.program.

Hypothesis Hlab_a : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures pra cid = Some Cprocs ->
  Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hproc_a : forall cid Cprocs Pid,
  Intermediate.prog_procedures pra cid = Some Cprocs ->
  Pid \in domm Cprocs -> Pid < P.
Hypothesis Hcomp_a : forall cid,
  cid \in domm (Intermediate.prog_procedures pra) -> cid < C.
Hypothesis Hlab_b : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures prb cid = Some Cprocs ->
  Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hproc_b : forall cid Cprocs Pid,
  Intermediate.prog_procedures prb cid = Some Cprocs ->
  Pid \in domm Cprocs -> Pid < P.
Hypothesis Hcomp_b : forall cid,
  cid \in domm (Intermediate.prog_procedures prb) -> cid < C.

Hypothesis Hdisj :
  fdisjoint (domm (Intermediate.prog_procedures pra))
            (domm (Intermediate.prog_procedures prb)).

Let codeW := lin_code L P C pra ++ lin_code L P C prb.

Section LeftTarget.

Variables (c : Component.id) (p : Procedure.id).
Variable Cprocs : NMap Machine.code.
Variable Pcode : Machine.code.
Hypothesis HCc : Intermediate.prog_procedures pra c = Some Cprocs.
Hypothesis HPp : Cprocs p = Some Pcode.

Let lab := mk_entry L P C c p.

Let HpP : p < P.
Proof. apply: (Hproc_a HCc). by rewrite mem_domm HPp. Qed.

Let Hcb : c \notin domm (Intermediate.prog_procedures prb).
Proof.
apply: (fdisjointP Hdisj).
by rewrite mem_domm HCc.
Qed.

Lemma link_count_entry_l : count (is_label_def lab) codeW <= 1.
Proof.
rewrite /codeW count_cat.
have Ha := count_entry_lin_code Hlab_a Hproc_a Hcomp_a c HpP.
have Hb := count_entry_lin_code_absent Hlab_b Hproc_b Hcomp_b HpP Hcb.
rewrite /lab.
by lia.
Qed.

Lemma link_entry_nth_l :
  List.nth_error codeW
                 (comp_base (intermediate_to_transitional pra) c
                  + (proc_base pra c p + 0))
  = Some (MrLabel (can_make L P C (c, p)), head_tag pra c p).
Proof.
have Hn := lin_code_entry_nth L P C HCc HPp.
rewrite /codeW nth_error_cat1; first exact: Hn.
exact: (nth_error_size Hn).
Qed.

Lemma link_entry_findopt_l :
  findopt (is_label_def lab) codeW
  = Some (comp_base (intermediate_to_transitional pra) c
          + (proc_base pra c p + 0)).
Proof.
apply: (findopt_unique_pos link_count_entry_l link_entry_nth_l).
by rewrite /is_label_def /= /lab /can_make /= eqxx.
Qed.

Lemma link_label_pos_entry_l (pc0 default : nat) :
  code_label_pos codeW pc0 lab default
  = pc0 + (comp_base (intermediate_to_transitional pra) c
           + (proc_base pra c p + 0)).
Proof.
rewrite /code_label_pos link_entry_findopt_l.
by [].
Qed.

End LeftTarget.

Section RightTarget.

Variables (c : Component.id) (p : Procedure.id).
Variable Cprocs : NMap Machine.code.
Variable Pcode : Machine.code.
Hypothesis HCc : Intermediate.prog_procedures prb c = Some Cprocs.
Hypothesis HPp : Cprocs p = Some Pcode.

Let lab := mk_entry L P C c p.

Let HpP : p < P.
Proof. apply: (Hproc_b HCc). by rewrite mem_domm HPp. Qed.

Let Hca : c \notin domm (Intermediate.prog_procedures pra).
Proof.
move: Hdisj. rewrite fdisjointC => /fdisjointP HD.
apply: HD. by rewrite mem_domm HCc.
Qed.

Lemma link_count_entry_r : count (is_label_def lab) codeW <= 1.
Proof.
rewrite /codeW count_cat.
have Hb := count_entry_lin_code Hlab_b Hproc_b Hcomp_b c HpP.
have Ha := count_entry_lin_code_absent Hlab_a Hproc_a Hcomp_a HpP Hca.
rewrite /lab.
by lia.
Qed.

Lemma link_entry_nth_r :
  List.nth_error codeW
                 (size (lin_code L P C pra)
                  + (comp_base (intermediate_to_transitional prb) c
                     + (proc_base prb c p + 0)))
  = Some (MrLabel (can_make L P C (c, p)), head_tag prb c p).
Proof.
have Hn := lin_code_entry_nth L P C HCc HPp.
rewrite /codeW nth_error_cat2.
exact: Hn.
Qed.

Lemma link_entry_findopt_r :
  findopt (is_label_def lab) codeW
  = Some (size (lin_code L P C pra)
          + (comp_base (intermediate_to_transitional prb) c
             + (proc_base prb c p + 0))).
Proof.
apply: (findopt_unique_pos link_count_entry_r link_entry_nth_r).
by rewrite /is_label_def /= /lab /can_make /= eqxx.
Qed.

Lemma link_label_pos_entry_r (pc0 default : nat) :
  code_label_pos codeW pc0 lab default
  = pc0 + (size (lin_code L P C pra)
           + (comp_base (intermediate_to_transitional prb) c
              + (proc_base prb c p + 0))).
Proof.
rewrite /code_label_pos link_entry_findopt_r.
by [].
Qed.

End RightTarget.

End LinkResolution.

Section LinCodeFetch.

Variables L P C : nat.
Variable pr : Intermediate.program.

Let can_msz := memory_lengths (Intermediate.prog_buffers pr).

Lemma lin_code_nth (c : Component.id) Cprocs p Pcode o i k :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some i ->
  k < isize i ->
  List.nth_error (lin_code L P C pr) (flat_pos pr c p Pcode o + k)
  = List.nth_error
      (cell_exp (can_make L P C) (can_upd L) can_msz
                (instr_to_transitional c i)) k.
Proof.
move=> HC HP Ho Hk.
have Hg := lin_gen_nth (can_make L P C) (can_upd L)
             (erefl (memory_lengths (Intermediate.prog_buffers pr))) HC HP Ho Hk.
have Hg' : List.nth_error (lin_body L P C pr) (flat_pos pr c p Pcode o + k)
           = List.nth_error
               (cell_exp (can_make L P C) (can_upd L) can_msz
                         (instr_to_transitional c i)) k
  by exact: Hg.
have Hcs : exists cell,
    List.nth_error
      (cell_exp (can_make L P C) (can_upd L) can_msz
                (instr_to_transitional c i)) k = Some cell.
{ apply: nth_error_Some_ex.
  rewrite lin_size_length size_cell_exp texp_isize. exact: Hk. }
case: Hcs => cell Hcell.
rewrite /lin_code.
case E: (lin_body L P C pr) => [|hd rest].
- exfalso.
  rewrite E Hcell in Hg'.
  by case: (flat_pos pr c p Pcode o + k) Hg'.
- rewrite E in Hg'.
  rewrite -cats1 nth_error_cat1; first exact: Hg'.
  rewrite Hcell in Hg'.
  exact: (nth_error_size Hg').
Qed.

Lemma lin_code_encoded_fetch (c : Component.id) Cprocs p Pcode o i k
    (pc0 : nat) (cell : @Merged.instr mt * mem_tag) :
  pc0 + size (lin_code L P C pr) < 2 ^ word_size mt ->
  Intermediate.prog_procedures pr c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some i ->
  k < isize i ->
  List.nth_error
    (cell_exp (can_make L P C) (can_upd L) can_msz
              (instr_to_transitional c i)) k = Some cell ->
  exists v : matom,
    encode_code (lin_code L P C pr) pc0
      (word_of_nat ((flat_pos pr c p Pcode o + k) + pc0)) = Some v
    /\ taga v = cell.2
    /\ Types.decode_instr (vala v)
       = Some (instr_merged_to_mp cell.1
                 (code_label_pos (lin_code L P C pr) pc0)
                 (pc0 + (flat_pos pr c p Pcode o + k))).
Proof.
move=> Hbound HC HP Ho Hk Hcell.
have Hnth : List.nth_error (lin_code L P C pr)
              (flat_pos pr c p Pcode o + k) = Some cell.
{ by rewrite (lin_code_nth HC HP Ho Hk). }
case: cell Hnth Hcell => mi tg Hnth Hcell.
have [v [Hv [Htag Hval]]] := encode_code_fetch Hbound Hnth.
exists v.
split; first exact: Hv.
split; first exact: Htag.
rewrite Hval /encode_instr_mp.
by rewrite encodeK.
Qed.

End LinCodeFetch.

Section LinkFetch.

Variables L P C : nat.
Variables pra prb : Intermediate.program.

Let codeW := lin_code L P C pra ++ lin_code L P C prb.
Let msza := memory_lengths (Intermediate.prog_buffers pra).
Let mszb := memory_lengths (Intermediate.prog_buffers prb).

Lemma link_code_nth_l (c : Component.id) Cprocs p Pcode o i k :
  Intermediate.prog_procedures pra c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some i ->
  k < isize i ->
  List.nth_error codeW (flat_pos pra c p Pcode o + k)
  = List.nth_error
      (cell_exp (can_make L P C) (can_upd L) msza
                (instr_to_transitional c i)) k.
Proof.
move=> HC HP Ho Hk.
have Hn := lin_code_nth L P C HC HP Ho Hk.
have Hcs : exists cell,
    List.nth_error
      (cell_exp (can_make L P C) (can_upd L) msza
                (instr_to_transitional c i)) k = Some cell.
{ apply: nth_error_Some_ex.
  rewrite lin_size_length size_cell_exp texp_isize. exact: Hk. }
case: Hcs => cell Hcell.
rewrite /codeW nth_error_cat1; first exact: Hn.
rewrite Hcell in Hn.
exact: (nth_error_size Hn).
Qed.

Lemma link_code_nth_r (c : Component.id) Cprocs p Pcode o i k :
  Intermediate.prog_procedures prb c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some i ->
  k < isize i ->
  List.nth_error codeW
                 (size (lin_code L P C pra) + (flat_pos prb c p Pcode o + k))
  = List.nth_error
      (cell_exp (can_make L P C) (can_upd L) mszb
                (instr_to_transitional c i)) k.
Proof.
move=> HC HP Ho Hk.
rewrite /codeW nth_error_cat2.
exact: (lin_code_nth L P C HC HP Ho Hk).
Qed.

Lemma link_encoded_fetch_l (c : Component.id) Cprocs p Pcode o i k
    (pc0 : nat) (cell : @Merged.instr mt * mem_tag) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures pra c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some i ->
  k < isize i ->
  List.nth_error
    (cell_exp (can_make L P C) (can_upd L) msza
              (instr_to_transitional c i)) k = Some cell ->
  exists v : matom,
    encode_code codeW pc0
      (word_of_nat ((flat_pos pra c p Pcode o + k) + pc0)) = Some v
    /\ taga v = cell.2
    /\ Types.decode_instr (vala v)
       = Some (instr_merged_to_mp cell.1 (code_label_pos codeW pc0)
                 (pc0 + (flat_pos pra c p Pcode o + k))).
Proof.
move=> Hbound HC HP Ho Hk Hcell.
have Hn : List.nth_error codeW (flat_pos pra c p Pcode o + k) = Some cell.
{ by rewrite (link_code_nth_l HC HP Ho Hk). }
case: cell Hn Hcell => mi tg Hn _.
have [v [Hv [Htag Hval]]] := encode_code_fetch Hbound Hn.
exists v.
split; first exact: Hv.
split; first exact: Htag.
rewrite Hval /encode_instr_mp.
by rewrite encodeK.
Qed.

Lemma link_encoded_fetch_r (c : Component.id) Cprocs p Pcode o i k
    (pc0 : nat) (cell : @Merged.instr mt * mem_tag) :
  pc0 + size codeW < 2 ^ word_size mt ->
  Intermediate.prog_procedures prb c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some i ->
  k < isize i ->
  List.nth_error
    (cell_exp (can_make L P C) (can_upd L) mszb
              (instr_to_transitional c i)) k = Some cell ->
  exists v : matom,
    encode_code codeW pc0
      (word_of_nat
         ((size (lin_code L P C pra) + (flat_pos prb c p Pcode o + k)) + pc0))
    = Some v
    /\ taga v = cell.2
    /\ Types.decode_instr (vala v)
       = Some (instr_merged_to_mp cell.1 (code_label_pos codeW pc0)
                 (pc0 + (size (lin_code L P C pra)
                         + (flat_pos prb c p Pcode o + k)))).
Proof.
move=> Hbound HC HP Ho Hk Hcell.
have Hn : List.nth_error codeW
            (size (lin_code L P C pra) + (flat_pos prb c p Pcode o + k))
          = Some cell.
{ by rewrite (link_code_nth_r HC HP Ho Hk). }
case: cell Hn Hcell => mi tg Hn _.
have [v [Hv [Htag Hval]]] := encode_code_fetch Hbound Hn.
exists v.
split; first exact: Hv.
split; first exact: Htag.
rewrite Hval /encode_instr_mp.
by rewrite encodeK.
Qed.

End LinkFetch.

Definition ilab (l0 : nat) (mi : Machine.instr) : bool :=
  if mi is ILabel l' then l' == l0 else false.

Lemma eq_sumn_map_In (T : Type) (f g : T -> nat) (s : seq T) :
  (forall x, List.In x s -> f x = g x) ->
  sumn [seq f x | x <- s] = sumn [seq g x | x <- s].
Proof.
elim: s => [|a s IH] //= H.
rewrite H; last by left.
rewrite IH //. by move=> x Hx; apply: H; right.
Qed.

Section BodyLabelResolution.

Variables L P C : nat.
Variable pr : Intermediate.program.

Hypothesis Hlab_bound : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures pr cid = Some Cprocs ->
  Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hproc_bound : forall cid Cprocs Pid,
  Intermediate.prog_procedures pr cid = Some Cprocs ->
  Pid \in domm Cprocs -> Pid < P.
Hypothesis Hcomp_bound : forall cid,
  cid \in domm (Intermediate.prog_procedures pr) -> cid < C.

Variables (c : Component.id) (l : nat).
Hypothesis HcC : c < C.
Hypothesis HlL : l < L.

Let lab := mk_body L c l.

Lemma mk_body_eqE (cp : Component.id) (l' : nat) :
  l' < L ->
  (lab == can_upd L cp l') = ((cp == c) && (l' == l)).
Proof.
move=> Hl'.
case E: ((cp == c) && (l' == l)).
- move/andP: E => [/eqP Ec /eqP El]; subst cp l'.
  by rewrite /lab /can_upd eqxx.
- case El: (lab == can_upd L cp l') => //.
  move/eqP: El. rewrite /lab /can_upd => El.
  have [Ec El'] := mk_body_inj HlL Hl' El.
  subst cp l'.
  by rewrite !eqxx in E.
Qed.

Lemma blab_entry_false (cp : Component.id) (pp : Procedure.id) :
  (lab == can_make L P C (cp, pp)) = false.
Proof.
case El: (lab == can_make L P C (cp, pp)) => //.
exfalso.
move/eqP: El. rewrite /lab /can_make /= => El.
exact: (mk_body_entry_disjoint HcC HlL El).
Qed.

Lemma count_body_map (cp : Component.id) (Pcode' : Machine.code) :
  (forall l0, List.In (ILabel l0) Pcode' -> l0 < L) ->
  count (tlab_pred lab (can_make L P C) (can_upd L))
        [seq instr_to_transitional cp mi | mi <- Pcode']
  = if cp == c then count (ilab l) Pcode' else 0.
Proof.
elim: Pcode' => [|mi Pcode' IH] Hb /=.
- by case: (cp == c).
- have Hbrest : forall l0, List.In (ILabel l0) Pcode' -> l0 < L.
  { move=> l0 HIn. apply: Hb. by right. }
  rewrite (IH Hbrest).
  have -> : tlab_pred lab (can_make L P C) (can_upd L)
              (instr_to_transitional cp mi)
            = (cp == c) && ilab l mi.
  { case: mi Hb
      => [ |l0 |iv r |r1 r2 |op r1 r2 r3 |r1 r2 |r1 r2 |r1 r2 |r l0
          | |l0 |c0 P0 | | ] Hb;
      try by rewrite andbF.
    - have Hl0 : l0 < L. { apply: (Hb l0). by left. }
      exact (mk_body_eqE cp Hl0).
    - by rewrite /instr_to_transitional /=; case: (Nat.eqb cp c0) => /=;
        rewrite andbF. }
  by case: (cp == c).
Qed.

Lemma count_body_linproc (cp : Component.id) (pp : Procedure.id)
    Cprocs' Pcode' :
  Intermediate.prog_procedures pr cp = Some Cprocs' ->
  Cprocs' pp = Some Pcode' ->
  count (tlab_pred lab (can_make L P C) (can_upd L)) (linearize_proc pr cp pp)
  = if cp == c then count (ilab l) Pcode' else 0.
Proof.
move=> HC' HP'.
have -> : linearize_proc pr cp pp
          = (TrLabel (inr (cp, pp)), head_tag pr cp pp)
              :: [seq instr_to_transitional cp mi | mi <- Pcode'].
{ by rewrite /linearize_proc HC' /= HP'. }
rewrite /=.
have -> : tlab_pred lab (can_make L P C) (can_upd L)
            (TrLabel (inr (cp, pp)), head_tag pr cp pp)
          = false.
{ have -> : tlab_pred lab (can_make L P C) (can_upd L)
              (TrLabel (inr (cp, pp)), head_tag pr cp pp)
            = (lab == can_make L P C (cp, pp)) by [].
  exact: blab_entry_false. }
rewrite count_body_map.
- by case: (cp == c).
- move=> l0 HIn. exact: (Hlab_bound HC' HP' HIn).
Qed.

Lemma count_body_lincomp (cp : Component.id) Cprocs' :
  Intermediate.prog_procedures pr cp = Some Cprocs' ->
  count (tlab_pred lab (can_make L P C) (can_upd L))
        (linearize_component pr cp)
  = if cp == c
    then sumn [seq count (ilab l) (odflt [::] (Cprocs' p'))
              | p' <- domm Cprocs']
    else 0.
Proof.
move=> HC'.
have -> : linearize_component pr cp
          = flatten [seq linearize_proc pr cp p' | p' <- domm Cprocs'].
{ by rewrite /linearize_component HC'. }
rewrite count_flatten.
have -> : [seq count (tlab_pred lab (can_make L P C) (can_upd L)) x
          | x <- [seq linearize_proc pr cp p' | p' <- domm Cprocs']]
          = [seq count (tlab_pred lab (can_make L P C) (can_upd L))
                       (linearize_proc pr cp p')
            | p' <- domm Cprocs'].
{ by rewrite -map_comp. }
case Ecp: (cp == c).
- move/eqP: Ecp => ?; subst cp.
  apply: eq_sumn_map_In => p' HIn.
  have Hp'in : p' \in domm Cprocs' := List_In_mem HIn.
  move/dommP: (Hp'in) => [Pcode' HP'].
  rewrite (count_body_linproc HC' HP') eqxx HP' /=.
  by [].
- have H0 : sumn [seq count (tlab_pred lab (can_make L P C) (can_upd L))
                            (linearize_proc pr cp p')
                 | p' <- domm Cprocs'] = 0.
  { apply: sumn_map_eq0 => p' HIn.
    have Hp'in : p' \in domm Cprocs' := List_In_mem HIn.
    move/dommP: (Hp'in) => [Pcode' HP'].
    by rewrite (count_body_linproc HC' HP') Ecp. }
  by rewrite H0.
Qed.

Hypothesis Huniq : forall Cprocs,
  Intermediate.prog_procedures pr c = Some Cprocs ->
  sumn [seq count (ilab l) (odflt [::] (Cprocs p')) | p' <- domm Cprocs] <= 1.

Lemma count_body_flat :
  count (tlab_pred lab (can_make L P C) (can_upd L))
        (flatten (map snd (Maps.elementsm (intermediate_to_transitional pr))))
  <= 1.
Proof.
rewrite count_flatten.
have -> : [seq count (tlab_pred lab (can_make L P C) (can_upd L)) x
          | x <- map snd (Maps.elementsm (intermediate_to_transitional pr))]
          = [seq count (tlab_pred lab (can_make L P C) (can_upd L)) x.2
            | x <- Maps.elementsm (intermediate_to_transitional pr)].
{ by rewrite -map_comp. }
apply: (sumn_le1_uniq_keys (c0 := c)); first exact: elementsm_keys_uniq.
move=> k v HIn.
have Hkv : intermediate_to_transitional pr k = Some v := In_fmap_getm HIn.
move: Hkv. rewrite i2t_getm.
case Eprocs: (Intermediate.prog_procedures pr k) => [Cprocs'|] //= [Ev].
subst v.
rewrite (count_body_lincomp Eprocs).
case Ekc: (k == c) => //.
move/eqP: Ekc => ?; subst k.
exact: (Huniq Eprocs).
Qed.

Lemma count_body_lin_code :
  count (is_label_def lab) (lin_code L P C pr) <= 1.
Proof.
have Hb : count (is_label_def lab) (lin_body L P C pr) <= 1.
{ have -> : lin_body L P C pr
            = transitional_to_merged_gen (mt := mt) (can_make L P C) (can_upd L)
                (Intermediate.prog_buffers pr)
                (intermediate_to_transitional pr) by [].
  rewrite t2m_count_label.
  exact: count_body_flat. }
rewrite /lin_code.
case E: (lin_body L P C pr) => [|cell rest] //.
rewrite E in Hb.
rewrite -cats1 count_cat.
have -> : count (is_label_def lab)
            [:: (MrHalt, def_mem_tag (color (last cell rest).2) true)] = 0
  by [].
rewrite ssrnat.addn0.
exact: Hb.
Qed.

Lemma lin_code_body_nth Cprocs p Pcode o :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some (ILabel l) ->
  List.nth_error (lin_code L P C pr) (flat_pos pr c p Pcode o + 0)
  = Some (MrLabel (can_upd L c l), def_mem_tag c true).
Proof.
move=> HCc HPp Ho.
have Hk : 0 < isize (ILabel l) by [].
by rewrite (lin_code_nth L P C HCc HPp Ho Hk).
Qed.

Lemma lin_code_body_findopt Cprocs p Pcode o :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some (ILabel l) ->
  findopt (is_label_def lab) (lin_code L P C pr)
  = Some (flat_pos pr c p Pcode o + 0).
Proof.
move=> HCc HPp Ho.
apply: (findopt_unique_pos count_body_lin_code
          (lin_code_body_nth HCc HPp Ho)).
by rewrite /is_label_def /= /lab /can_upd eqxx.
Qed.

Lemma code_label_pos_body Cprocs p Pcode o (pc0 default : nat) :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some (ILabel l) ->
  code_label_pos (lin_code L P C pr) pc0 lab default
  = pc0 + (flat_pos pr c p Pcode o + 0).
Proof.
move=> HCc HPp Ho.
rewrite /code_label_pos (lin_code_body_findopt HCc HPp Ho).
by [].
Qed.

Lemma count_body_lin_code_absent (pr' : Intermediate.program) :
  (forall cid Cprocs Pid Pcode l0,
      Intermediate.prog_procedures pr' cid = Some Cprocs ->
      Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L) ->
  c \notin domm (Intermediate.prog_procedures pr') ->
  count (is_label_def lab) (lin_code L P C pr') = 0.
Proof.
move=> Hlab' Hnotin.
have Hflat : count (tlab_pred lab (can_make L P C) (can_upd L))
               (flatten (map snd (Maps.elementsm
                                    (intermediate_to_transitional pr'))))
             = 0.
{ rewrite count_flatten.
  have -> : [seq count (tlab_pred lab (can_make L P C) (can_upd L)) x
            | x <- map snd (Maps.elementsm (intermediate_to_transitional pr'))]
            = [seq count (tlab_pred lab (can_make L P C) (can_upd L)) x.2
              | x <- Maps.elementsm (intermediate_to_transitional pr')].
  { by rewrite -map_comp. }
  apply: sumn_map_eq0 => -[k v] HIn /=.
  have Hkv : intermediate_to_transitional pr' k = Some v := In_fmap_getm HIn.
  move: Hkv. rewrite i2t_getm.
  case Eprocs: (Intermediate.prog_procedures pr' k) => [Cprocs'|] //= [Ev].
  subst v.
  have Ekc : (k == c) = false.
  { case Ekc: (k == c) => //. move/eqP: Ekc => ?; subst k.
    by rewrite mem_domm Eprocs in Hnotin. }
  have -> : linearize_component pr' k
            = flatten [seq linearize_proc pr' k p' | p' <- domm Cprocs'].
  { by rewrite /linearize_component Eprocs. }
  rewrite count_flatten.
  have -> : [seq count (tlab_pred lab (can_make L P C) (can_upd L)) x
            | x <- [seq linearize_proc pr' k p' | p' <- domm Cprocs']]
            = [seq count (tlab_pred lab (can_make L P C) (can_upd L))
                         (linearize_proc pr' k p')
              | p' <- domm Cprocs'].
  { by rewrite -map_comp. }
  apply: sumn_map_eq0 => p' HIn'.
  have Hp'in : p' \in domm Cprocs' := List_In_mem HIn'.
  move/dommP: (Hp'in) => [Pcode' HP'].
  have -> : linearize_proc pr' k p'
            = (TrLabel (inr (k, p')), head_tag pr' k p')
                :: [seq instr_to_transitional k mi | mi <- Pcode'].
  { by rewrite /linearize_proc Eprocs /= HP'. }
  rewrite /=.
  have -> : tlab_pred lab (can_make L P C) (can_upd L)
              (TrLabel (inr (k, p')), head_tag pr' k p')
            = false.
  { have -> : tlab_pred lab (can_make L P C) (can_upd L)
                (TrLabel (inr (k, p')), head_tag pr' k p')
              = (lab == can_make L P C (k, p')) by [].
    exact: blab_entry_false. }
  rewrite count_body_map.
  - by rewrite Ekc.
  - move=> l0 HIn0. exact: (Hlab' _ _ _ _ _ Eprocs HP' HIn0). }
have Hbody : count (is_label_def lab) (lin_body L P C pr') = 0.
{ have -> : lin_body L P C pr'
            = transitional_to_merged_gen (mt := mt) (can_make L P C) (can_upd L)
                (Intermediate.prog_buffers pr')
                (intermediate_to_transitional pr') by [].
  by rewrite t2m_count_label. }
rewrite /lin_code.
case E: (lin_body L P C pr') => [|cell rest] //.
rewrite E in Hbody.
rewrite -cats1 count_cat.
have -> : count (is_label_def lab)
            [:: (MrHalt, def_mem_tag (color (last cell rest).2) true)] = 0
  by [].
rewrite ssrnat.addn0.
exact: Hbody.
Qed.

End BodyLabelResolution.

Section LinkBodyResolution.

Variables L P C : nat.
Variables pra prb : Intermediate.program.

Hypothesis Hlab_a : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures pra cid = Some Cprocs ->
  Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hcomp_a : forall cid,
  cid \in domm (Intermediate.prog_procedures pra) -> cid < C.
Hypothesis Hlab_b : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures prb cid = Some Cprocs ->
  Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Hypothesis Hcomp_b : forall cid,
  cid \in domm (Intermediate.prog_procedures prb) -> cid < C.

Hypothesis Hdisj :
  fdisjoint (domm (Intermediate.prog_procedures pra))
            (domm (Intermediate.prog_procedures prb)).

Let codeW := lin_code L P C pra ++ lin_code L P C prb.

Section BodyLeft.

Variables (c : Component.id) (l : nat).
Variable Cprocs : NMap Machine.code.
Variable Pcode : Machine.code.
Variables (p : Procedure.id) (o : nat).
Hypothesis HCc : Intermediate.prog_procedures pra c = Some Cprocs.
Hypothesis HPp : Cprocs p = Some Pcode.
Hypothesis Ho : List.nth_error Pcode o = Some (ILabel l).
Hypothesis Huniq_a : forall Cprocs0,
  Intermediate.prog_procedures pra c = Some Cprocs0 ->
  sumn [seq count (ilab l) (odflt [::] (Cprocs0 p')) | p' <- domm Cprocs0]
  <= 1.

Let lab := mk_body L c l.

Let HcC : c < C.
Proof. apply: Hcomp_a. by rewrite mem_domm HCc. Qed.

Let HlL : l < L.
Proof.
have HIn := List.nth_error_In _ _ Ho.
exact (Hlab_a HCc HPp HIn).
Qed.

Let Hcb : c \notin domm (Intermediate.prog_procedures prb).
Proof. apply: (fdisjointP Hdisj). by rewrite mem_domm HCc. Qed.

Lemma link_count_body_l : count (is_label_def lab) codeW <= 1.
Proof.
rewrite /codeW count_cat.
have Ha := @count_body_lin_code L P C pra Hlab_a c l HcC HlL Huniq_a.
have Hb := @count_body_lin_code_absent L P C c l HcC HlL prb Hlab_b Hcb.
rewrite /lab.
by lia.
Qed.

Lemma link_body_nth_l :
  List.nth_error codeW (flat_pos pra c p Pcode o + 0)
  = Some (MrLabel (can_upd L c l), def_mem_tag c true).
Proof.
have Hn := @lin_code_body_nth L P C pra c l Cprocs p Pcode o HCc HPp Ho.
rewrite /codeW nth_error_cat1; first exact: Hn.
exact: (nth_error_size Hn).
Qed.

Lemma link_body_findopt_l :
  findopt (is_label_def lab) codeW = Some (flat_pos pra c p Pcode o + 0).
Proof.
apply: (findopt_unique_pos link_count_body_l link_body_nth_l).
by rewrite /is_label_def /= /lab /can_upd eqxx.
Qed.

Lemma link_label_pos_body_l (pc0 default : nat) :
  code_label_pos codeW pc0 lab default
  = pc0 + (flat_pos pra c p Pcode o + 0).
Proof.
rewrite /code_label_pos link_body_findopt_l.
by [].
Qed.

End BodyLeft.

Section BodyRight.

Variables (c : Component.id) (l : nat).
Variable Cprocs : NMap Machine.code.
Variable Pcode : Machine.code.
Variables (p : Procedure.id) (o : nat).
Hypothesis HCc : Intermediate.prog_procedures prb c = Some Cprocs.
Hypothesis HPp : Cprocs p = Some Pcode.
Hypothesis Ho : List.nth_error Pcode o = Some (ILabel l).
Hypothesis Huniq_b : forall Cprocs0,
  Intermediate.prog_procedures prb c = Some Cprocs0 ->
  sumn [seq count (ilab l) (odflt [::] (Cprocs0 p')) | p' <- domm Cprocs0]
  <= 1.

Let lab := mk_body L c l.

Let HcC : c < C.
Proof. apply: Hcomp_b. by rewrite mem_domm HCc. Qed.

Let HlL : l < L.
Proof.
have HIn := List.nth_error_In _ _ Ho.
exact (Hlab_b HCc HPp HIn).
Qed.

Let Hca : c \notin domm (Intermediate.prog_procedures pra).
Proof.
move: Hdisj. rewrite fdisjointC => /fdisjointP HD.
apply: HD. by rewrite mem_domm HCc.
Qed.

Lemma link_count_body_r : count (is_label_def lab) codeW <= 1.
Proof.
rewrite /codeW count_cat.
have Hb := @count_body_lin_code L P C prb Hlab_b c l HcC HlL Huniq_b.
have Ha := @count_body_lin_code_absent L P C c l HcC HlL pra Hlab_a Hca.
rewrite /lab.
by lia.
Qed.

Lemma link_body_nth_r :
  List.nth_error codeW
                 (size (lin_code L P C pra) + (flat_pos prb c p Pcode o + 0))
  = Some (MrLabel (can_upd L c l), def_mem_tag c true).
Proof.
have Hn := @lin_code_body_nth L P C prb c l Cprocs p Pcode o HCc HPp Ho.
rewrite /codeW nth_error_cat2.
exact: Hn.
Qed.

Lemma link_body_findopt_r :
  findopt (is_label_def lab) codeW
  = Some (size (lin_code L P C pra) + (flat_pos prb c p Pcode o + 0)).
Proof.
apply: (findopt_unique_pos link_count_body_r link_body_nth_r).
by rewrite /is_label_def /= /lab /can_upd eqxx.
Qed.

Lemma link_label_pos_body_r (pc0 default : nat) :
  code_label_pos codeW pc0 lab default
  = pc0 + (size (lin_code L P C pra) + (flat_pos prb c p Pcode o + 0)).
Proof.
rewrite /code_label_pos link_body_findopt_r.
by [].
Qed.

End BodyRight.

End LinkBodyResolution.

Lemma find_first_pos (A : Type) (pred : A -> bool) (l : seq A) :
  forall (n : nat) (x : A),
  List.nth_error l n = Some x ->
  pred x ->
  (forall k y, k < n -> List.nth_error l k = Some y -> pred y = false) ->
  find pred l = n.
Proof.
elim: l => [|a l IH] [|n] x //=.
- move=> [= E] Hp _; subst a.
  by rewrite Hp.
- move=> Hn Hp Hbefore.
  have Ha : pred a = false.
  { apply: (Hbefore 0 a) => //. }
  rewrite Ha.
  congr S.
  apply: (IH _ _ Hn Hp) => k y Hk Hky.
  apply: (Hbefore k.+1 y) => //.
Qed.

Lemma flatten_pos_inv (A : Type) (ll : seq (seq A)) :
  forall (k : nat) (x : A),
  List.nth_error (flatten ll) k = Some x ->
  exists j l' k',
    [/\ List.nth_error ll j = Some l',
        k = sumn [seq size s | s <- take j ll] + k',
        k' < size l'
      & List.nth_error l' k' = Some x].
Proof.
elim: ll => [|s ll IH] k x //=; first by case: k.
move=> Hnth.
case Hk: (k < size s).
- exists 0, s, k.
  split=> //.
  move: Hnth.
  by rewrite (nth_error_cat1 _ Hk).
- have Hk' : size s <= k by lia.
  have Ek : k = size s + (k - size s) by lia.
  move: Hnth.
  rewrite Ek nth_error_cat2 => Hnth.
  have [j [l' [k' [H1 H2 H3 H4]]]] := IH _ _ Hnth.
  exists j.+1, l', k'.
  split=> //.
  have -> : take j.+1 (s :: ll) = s :: take j ll by [].
  have -> : sumn [seq size s0 | s0 <- s :: take j ll]
            = size s + sumn [seq size s0 | s0 <- take j ll] by [].
  by lia.
Qed.

Lemma nth_error_map_inv (A B : Type) (f : A -> B) (s : seq A) :
  forall (j : nat) (y : B),
  List.nth_error [seq f x | x <- s] j = Some y ->
  exists x, List.nth_error s j = Some x /\ y = f x.
Proof.
elim: s => [|a s IH] [|j] y //=.
- move=> [= <-]. by exists a.
- exact: IH.
Qed.

Lemma sumn_take_leq (xs : seq nat) :
  forall (a b : nat), a <= b -> sumn (take a xs) <= sumn (take b xs).
Proof.
elim: xs => [|x xs IH] a b Hab; first by [].
case: a Hab => [|a]; case: b => [|b] //= Hab.
have := IH a b Hab.
by lia.
Qed.

Lemma nth_index_neq (T : eqType) (s : seq T) :
  forall (x : T) (j : nat) (y : T),
  j < seq.index x s ->
  List.nth_error s j = Some y ->
  y != x.
Proof.
elim: s => [|a s IH] x [|j] y //=.
- case Eax: (a == x) => //.
  move=> _ [= <-]. by rewrite Eax.
- case Eax: (a == x) => //.
  move=> Hlt Hnth.
  exact: (IH x j y _ Hnth).
Qed.

Section T2MIn.

Variables (make : proc_label -> nat) (upd : Component.id -> nat -> nat).
Variable msz : NMap (NMap nat).

Lemma t2m_flat_In (ll : seq (Transitional.instr * mem_tag))
    (cell : @Merged.instr mt * mem_tag) :
  List.In cell (t2m_flat make upd msz ll) ->
  exists itrt, List.In itrt ll /\ cell.2 = itrt.2.
Proof.
elim: ll => [|itrt0 ll IH] //= HIn.
move/List.in_app_iff: HIn => [HL|HR].
- move/List.in_map_iff: HL => [i0 [Ei0 _]].
  exists itrt0. split; first by left.
  by rewrite -Ei0.
- have [itrt [H1 H2]] := IH HR.
  exists itrt. split; [by right | exact: H2].
Qed.

End T2MIn.

Lemma lincomp_cell_color (make : proc_label -> nat)
    (upd : Component.id -> nat -> nat) (msz : NMap (NMap nat))
    (pr : Intermediate.program) (c' : Component.id)
    (cell : @Merged.instr mt * mem_tag) :
  List.In cell (t2m_flat make upd msz (linearize_component pr c')) ->
  color cell.2 = c'.
Proof.
move=> HIn.
have [itrt [HIn' Etag]] := t2m_flat_In HIn.
rewrite Etag.
move/lin_comp_In: HIn' => [Cprocs [Pid [HCp [HPd Hcell]]]].
move/lin_proc_In: Hcell => [Hhd|[mi [_ Hcell]]].
- rewrite Hhd /=. exact: color_head_tag.
- rewrite Hcell i2t_snd. exact: color_def_mem_tag.
Qed.

Section FindComp.

Variables (make : proc_label -> nat) (upd : Component.id -> nat -> nat).
Variable msz : NMap (NMap nat).
Variable pr : Intermediate.program.

Lemma find_color_comp_base (c : Component.id) (Cprocs : NMap Machine.code)
    (p0 : Procedure.id) :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  p0 \in domm Cprocs ->
  find (fun cell : @Merged.instr mt * mem_tag => color cell.2 == c)
       (t2m_flat make upd msz
          (flatten (map snd (Maps.elementsm (intermediate_to_transitional pr)))))
  = comp_base (intermediate_to_transitional pr) c.
Proof.
move=> HC Hp0.
have Hcget : intermediate_to_transitional pr c
             = Some (linearize_component pr c).
{ by rewrite i2t_getm HC. }
have Hb0 : 0 < tseg_size (linearize_component pr c).
{ rewrite (tseg_size_lincomp HC).
  move/dommP: (Hp0) => [Pcode0 HP0].
  have Hn : List.nth_error
              [seq tseg_size (linearize_proc pr c p') | p' <- domm Cprocs]
              (seq.index p0 (domm Cprocs))
            = Some (tseg_size (linearize_proc pr c p0)).
  { apply: map_nth_error_seq. exact: (nth_error_index Hp0). }
  have Hle := sumn_take_le Hn.
  have Hgt := tseg_size_linproc_gt0 HC HP0.
  by lia. }
have Hnth0 := t2m_flat_code_nth make upd msz Hcget Hb0.
rewrite ssrnat.addn0 in Hnth0.
have [cell0 Hcell0] : exists cell0,
    List.nth_error (t2m_flat make upd msz (linearize_component pr c)) 0
    = Some cell0.
{ apply: nth_error_Some_ex.
  by rewrite lin_size_length size_t2m_flat. }
apply: (find_first_pos (x := cell0)).
- by rewrite Hnth0.
- have HIn := List.nth_error_In _ _ Hcell0.
  by rewrite (lincomp_cell_color HIn) eqxx.
-
  move=> k y Hk Hky.
  move: Hky.
  rewrite (t2m_flat_flatten make upd msz) => Hky.
  have [j [l' [k' [H1 H2 H3 H4]]]] := flatten_pos_inv Hky.
  have [l0 [Hl0 El']] := nth_error_map_inv H1.
  have [[cj vj] [Hpair El0]] := nth_error_map_inv Hl0.
  have Hcj : intermediate_to_transitional pr cj = Some vj.
  { apply: In_fmap_getm. exact: (List.nth_error_In _ _ Hpair). }
  have Evj : vj = linearize_component pr cj.
  { move: Hcj. rewrite i2t_getm.
    by case Ep: (Intermediate.prog_procedures pr cj) => [Cprocsj|] //= [<-]. }
  have Hcol : color y.2 = cj.
  { apply: (lincomp_cell_color (make := make) (upd := upd) (msz := msz)
              (pr := pr)).
    rewrite -Evj -El0 -El'.
    exact: (List.nth_error_In _ _ H4). }
  have Hjlt : j < seq.index c (unzip1 (Maps.elementsm
                                          (intermediate_to_transitional pr))).
  { move: Hk. rewrite /comp_base H2.
    rewrite (sumn_size_take_t2m_snd make upd msz
               (Maps.elementsm (intermediate_to_transitional pr)) j).
    move=> Hk.
    case Hjge: (j < seq.index c (unzip1 (Maps.elementsm
                    (intermediate_to_transitional pr)))) => //.
    have Hge : seq.index c (unzip1 (Maps.elementsm
                    (intermediate_to_transitional pr))) <= j by lia.
    have := sumn_take_leq
              [seq tseg_size x.2
              | x <- Maps.elementsm (intermediate_to_transitional pr)] Hge.
    by lia. }
  have Hcjkey : List.nth_error
                  (unzip1 (Maps.elementsm (intermediate_to_transitional pr))) j
                = Some cj.
  { have := map_nth_error_seq fst Hpair.
    by []. }
  have Hneq := nth_index_neq Hjlt Hcjkey.
  rewrite Hcol.
  exact: negbTE Hneq.
Qed.

End FindComp.

Lemma find_pred_pairE (c : Component.id)
    (l : seq (@Merged.instr mt * mem_tag)) :
  find (fun '(_, tag) => color tag == c) l
  = find (fun cell : @Merged.instr mt * mem_tag => color cell.2 == c) l.
Proof.
apply: eq_find => -[i t] /=.
by [].
Qed.

Section FindLin.

Variables L P C : nat.
Variable pr : Intermediate.program.

Let can_msz := memory_lengths (Intermediate.prog_buffers pr).

Let Eb : lin_body L P C pr
         = t2m_flat (can_make L P C) (can_upd L) can_msz
             (flatten (map snd (Maps.elementsm
                                  (intermediate_to_transitional pr)))).
Proof.
have -> : lin_body L P C pr
          = transitional_to_merged_gen (mt := mt) (can_make L P C) (can_upd L)
              (Intermediate.prog_buffers pr)
              (intermediate_to_transitional pr) by [].
exact: (t2m_genE (can_make L P C) (can_upd L)
          (intermediate_to_transitional pr) (erefl _)).
Qed.

Lemma comp_base_lt_size_body (c : Component.id) (Cprocs : NMap Machine.code)
    (p0 : Procedure.id) :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  p0 \in domm Cprocs ->
  comp_base (intermediate_to_transitional pr) c < size (lin_body L P C pr).
Proof.
move=> HC Hp0.
have Hcget : intermediate_to_transitional pr c
             = Some (linearize_component pr c).
{ by rewrite i2t_getm HC. }
have Hb0 : 0 < tseg_size (linearize_component pr c).
{ rewrite (tseg_size_lincomp HC).
  move/dommP: (Hp0) => [Pcode0 HP0].
  have Hn : List.nth_error
              [seq tseg_size (linearize_proc pr c p') | p' <- domm Cprocs]
              (seq.index p0 (domm Cprocs))
            = Some (tseg_size (linearize_proc pr c p0)).
  { apply: map_nth_error_seq. exact: (nth_error_index Hp0). }
  have Hle := sumn_take_le Hn.
  have Hgt := tseg_size_linproc_gt0 HC HP0.
  by lia. }
rewrite Eb size_t2m_flat tseg_size_flatten.
have -> : [seq tseg_size l
          | l <- map snd (Maps.elementsm (intermediate_to_transitional pr))]
          = [seq tseg_size x.2
            | x <- Maps.elementsm (intermediate_to_transitional pr)].
{ by rewrite -map_comp. }
have Hfetch := map_nth_error_seq
                 (fun x : nat * seq (Transitional.instr * mem_tag) =>
                    tseg_size x.2)
                 (nth_error_elementsm Hcget).
have Hle := sumn_take_le Hfetch.
rewrite /comp_base.
move: Hle => /= Hle.
apply: (leq_trans _ Hle).
rewrite -addn1 leq_add2l.
exact: Hb0.
Qed.

Lemma find_color_body (c : Component.id) (Cprocs : NMap Machine.code)
    (p0 : Procedure.id) :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  p0 \in domm Cprocs ->
  find (fun cell : @Merged.instr mt * mem_tag => color cell.2 == c)
       (lin_body L P C pr)
  = comp_base (intermediate_to_transitional pr) c.
Proof.
move=> HC Hp0.
rewrite Eb.
exact: (find_color_comp_base (can_make L P C) (can_upd L) can_msz HC Hp0).
Qed.

Lemma find_color_lin_code (c : Component.id) (Cprocs : NMap Machine.code)
    (p0 : Procedure.id) :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  p0 \in domm Cprocs ->
  find (fun cell : @Merged.instr mt * mem_tag => color cell.2 == c)
       (lin_code L P C pr)
  = comp_base (intermediate_to_transitional pr) c.
Proof.
move=> HC Hp0.
have Hlt := comp_base_lt_size_body HC Hp0.
have Hfb := find_color_body HC Hp0.
rewrite /lin_code.
case E: (lin_body L P C pr) => [|cell rest].
- exfalso. move: Hlt. rewrite E /=. by lia.
- rewrite E in Hfb Hlt.
  rewrite -cats1 find_cat.
  have Hhas : has (fun cell0 : @Merged.instr mt * mem_tag =>
                     color cell0.2 == c) (cell :: rest).
  { by rewrite has_find Hfb. }
  rewrite Hhas.
  exact: Hfb.
Qed.

End FindLin.

Section FindLink.

Variables L P C : nat.
Variables pra prb : Intermediate.program.

Lemma find_color_link (c : Component.id) (Cprocs : NMap Machine.code)
    (p0 : Procedure.id) :
  Intermediate.prog_procedures pra c = Some Cprocs ->
  p0 \in domm Cprocs ->
  find (fun cell : @Merged.instr mt * mem_tag => color cell.2 == c)
       (lin_code L P C pra ++ lin_code L P C prb)
  = comp_base (intermediate_to_transitional pra) c.
Proof.
move=> HC Hp0.
have Hlt := comp_base_lt_size_body L P C HC Hp0.
have Hfc := find_color_lin_code L P C HC Hp0.
rewrite find_cat.
have Hltc : comp_base (intermediate_to_transitional pra) c
            < size (lin_code L P C pra).
{ move: Hlt. rewrite /lin_code.
  case E: (lin_body L P C pra) => [|cell rest].
  - rewrite /=. by lia.
  - rewrite size_rcons -E. by lia. }
have Hhas : has (fun cell : @Merged.instr mt * mem_tag =>
                   color cell.2 == c) (lin_code L P C pra).
{ by rewrite has_find Hfc. }
rewrite Hhas.
exact: Hfc.
Qed.

Lemma mem_seq_In_lp (T : eqType) (l : seq T) (x : T) :
  x \in l -> List.In x l.
Proof.
elim: l => [|a l IH] //=.
rewrite in_cons => /orP[/eqP -> | /IH H].
- by left.
- by right.
Qed.

Lemma has_color_false (c : Component.id)
    (l : seq (@Merged.instr mt * mem_tag)) :
  (forall i t, List.In (i, t) l -> color t <> c) ->
  has (fun cell : @Merged.instr mt * mem_tag => color cell.2 == c) l
  = false.
Proof.
elim: l => [|[i t] l IH] //= Hno.
case Ec: (color t == c) => /=.
- move/eqP: Ec => Ec. exfalso.
  exact: (Hno i t (or_introl (erefl _)) Ec).
- apply: IH => i' t' HIn'.
  exact: (Hno i' t' (or_intror HIn')).
Qed.

Lemma find_color_link_r (c : Component.id) (Cprocs : NMap Machine.code)
    (p0 : Procedure.id) :
  Intermediate.well_formed_program pra ->
  c \notin domm (Intermediate.prog_interface pra) ->
  Intermediate.prog_procedures prb c = Some Cprocs ->
  p0 \in domm Cprocs ->
  find (fun cell : @Merged.instr mt * mem_tag => color cell.2 == c)
       (lin_code L P C pra ++ lin_code L P C prb)
  = size (lin_code L P C pra)
    + comp_base (intermediate_to_transitional prb) c.
Proof.
move=> Hwfa HnotA HC Hp0.
have Hfc := find_color_lin_code L P C HC Hp0.
rewrite find_cat.
have Hhas : has (fun cell : @Merged.instr mt * mem_tag =>
                   color cell.2 == c) (lin_code L P C pra) = false.
{ apply: has_color_false => i t HInL Ec.
  have Hcol := lin_low_colors Hwfa HInL.
  by rewrite Ec in Hcol; rewrite Hcol in HnotA. }
rewrite Hhas.
by rewrite Hfc.
Qed.

End FindLink.
