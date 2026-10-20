Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.SmallstepUB.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
From CoqUtils Require Import hseq word.
From extructures Require Import fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Merged.
Require Import Coq.micromega.Lia.

Require Import MicroPolicies.Utils.
Import DoNotation.
Import Types.

Require Import MicroPolicies.Recomposition.Definitions.

Section Padding.

Local Notation mcell := ((@Merged.instr mt) * mem_tag)%type.
Local Notation mcode := (@Merged.code mt).

Definition nop_cell (c : Component.id) : mcell :=
  (MrNop, MTag Other c None true).

Definition is_entry (x : mcell) : bool :=
  if entry (snd x) is Some _ then true else false.

Fixpoint proc_split_fuel (n : nat) (cde : mcode) : seq mcode :=
  match n with
  | 0 => if cde is [::] then [::] else [:: cde]
  | S n' =>
      match cde with
      | [::] => [::]
      | x :: xs =>
          let k := find is_entry xs in
          (x :: take k xs) :: proc_split_fuel n' (drop k xs)
      end
  end.

Definition proc_split (cde : mcode) : seq mcode :=
  proc_split_fuel (size cde) cde.

Definition block_color (b : mcode) : Component.id :=
  if b is x :: _ then color (snd x) else Component.main.

Definition block_pad (n : nat) (b : mcode) : mcode :=
  b ++ nseq (n - size b) (nop_cell (block_color b)).

Fixpoint align_blocks (bs bs' : seq mcode) : mcode * mcode :=
  match bs, bs' with
  | b :: bs2, b' :: bs2' =>
      let n := maxn (size b) (size b') in
      let (r, r') := align_blocks bs2 bs2' in
      (block_pad n b ++ r, block_pad n b' ++ r')
  | _, _ => (flatten bs, flatten bs')
  end.

Definition pad_code (cde cde' : mcode) : mcode * mcode :=
  align_blocks (proc_split cde) (proc_split cde').

Definition pad_align (q q' : program) : program * program :=
  let cc := pad_code (code q) (code q') in
  ({| prog_interface := prog_interface q; code := cc.1;
      prog_buffers := prog_buffers q; prog_main := prog_main q |},
   {| prog_interface := prog_interface q'; code := cc.2;
      prog_buffers := prog_buffers q'; prog_main := prog_main q' |}).

Lemma pad_align_interface q q' :
  prog_interface (pad_align q q').1 = prog_interface q /\
  prog_interface (pad_align q q').2 = prog_interface q'.
Proof. by []. Qed.

Lemma pad_align_buffers q q' :
  prog_buffers (pad_align q q').1 = prog_buffers q /\
  prog_buffers (pad_align q q').2 = prog_buffers q'.
Proof. by []. Qed.

Lemma pad_align_main q q' :
  prog_main (pad_align q q').1 = prog_main q /\
  prog_main (pad_align q q').2 = prog_main q'.
Proof. by []. Qed.

Lemma proc_split_fuel_flatten n cde : size cde <= n -> flatten (proc_split_fuel n cde) = cde.
Proof.
  elim: n cde => [|n IH] cde Hsz /=.
  - by move: Hsz; case: cde.
  - move: Hsz; case: cde => [|x xs] //= Hsz.
    rewrite IH /=; first by rewrite cat_take_drop.
    rewrite size_drop. move: Hsz; rewrite ltnS => H. lia.
Qed.

Lemma proc_split_flatten cde : flatten (proc_split cde) = cde.
Proof. rewrite /proc_split. exact: (proc_split_fuel_flatten (leqnn _)). Qed.

Lemma block_pad_size n b : size (block_pad n b) = maxn (size b) n.
Proof. by rewrite /block_pad size_cat size_nseq maxnE. Qed.

Lemma align_blocks_size bs bs' :
  size bs = size bs' -> size (align_blocks bs bs').1 = size (align_blocks bs bs').2.
Proof.
  elim: bs bs' => [|b bs IH] [|b' bs'] //= [] Hsz.
  case E: (align_blocks bs bs') => [r r'].
  have Hr : size r = size r' by have := IH bs' Hsz; rewrite E.
  cbn [fst snd]. rewrite /block_pad !size_cat !size_nseq Hr. by lia.
Qed.

Lemma pad_align_code_size q q' :
  size (proc_split (code q)) = size (proc_split (code q')) ->
  size (code (pad_align q q').1) = size (code (pad_align q q').2).
Proof. move=> H. rewrite /pad_align /= /pad_code. exact: align_blocks_size. Qed.

Lemma in_nseq_eq (T : Type) (v : T) k x : List.In x (nseq k v) -> x = v.
Proof. elim: k => [|k IH] //=. by case=> [<-|/IH ->]. Qed.

Lemma align_blocks_cells_l bs bs' x :
  List.In x (align_blocks bs bs').1 ->
  List.In x (flatten bs) \/ exists b, List.In b bs /\ x = nop_cell (block_color b).
Proof.
  elim: bs bs' => [|b bs IH] [|b' bs'] //=.
  - by move=> H; left.
  - case E: (align_blocks bs bs') => [r r'] /=.
    rewrite /block_pad -catA => /List.in_app_iff [Hb | Hrest].
    + by left; apply/List.in_or_app; left.
    + move: Hrest => /List.in_app_iff [Hnop | Hr].
      * by right; exists b; split; [left | exact: (in_nseq_eq Hnop)].
      * have := IH bs'; rewrite E /= => /(_ Hr) [Hflat | [b0 [Hb0 Hx]]].
        -- by left; apply/List.in_or_app; right.
        -- by right; exists b0; split; [right |].
Qed.

Lemma pad_code_cells cde cde' x :
  List.In x (pad_code cde cde').1 ->
  List.In x cde \/ exists col, x = nop_cell col.
Proof.
  rewrite /pad_code => /align_blocks_cells_l.
  rewrite proc_split_flatten => -[H|[b [_ ->]]]; [by left | by right; exists (block_color b)].
Qed.

Lemma align_blocks_cells_r bs bs' x :
  List.In x (align_blocks bs bs').2 ->
  List.In x (flatten bs') \/ exists b, List.In b bs' /\ x = nop_cell (block_color b).
Proof.
  elim: bs bs' => [|b bs IH] [|b' bs'] //=.
  - by move=> H; left.
  - case E: (align_blocks bs bs') => [r r'] /=.
    rewrite /block_pad -catA => /List.in_app_iff [Hb | Hrest].
    + by left; apply/List.in_or_app; left.
    + move: Hrest => /List.in_app_iff [Hnop | Hr].
      * by right; exists b'; split; [left | exact: (in_nseq_eq Hnop)].
      * have := IH bs'; rewrite E /= => /(_ Hr) [Hflat | [b0 [Hb0 Hx]]].
        -- by left; apply/List.in_or_app; right.
        -- by right; exists b0; split; [right |].
Qed.

Lemma pad_code_cells' cde cde' x :
  List.In x (pad_code cde cde').2 ->
  List.In x cde' \/ exists col, x = nop_cell col.
Proof.
  rewrite /pad_code => /align_blocks_cells_r.
  rewrite proc_split_flatten => -[H|[b [_ ->]]]; [by left | by right; exists (block_color b)].
Qed.

Lemma pad_code_tags_wf cde cde' :
  (forall i t, List.In (i, t) cde -> is_code t = true /\ vtag t = Other) ->
  forall i t, List.In (i, t) (pad_code cde cde').1 -> is_code t = true /\ vtag t = Other.
Proof.
  move=> Hwf i t /pad_code_cells [Hin | [col Hcol]]; first exact: Hwf Hin.
  by have -> : t = snd (nop_cell col) by rewrite -Hcol.
Qed.

Lemma pad_code_tags_wf' cde cde' :
  (forall i t, List.In (i, t) cde' -> is_code t = true /\ vtag t = Other) ->
  forall i t, List.In (i, t) (pad_code cde cde').2 -> is_code t = true /\ vtag t = Other.
Proof.
  move=> Hwf i t /pad_code_cells' [Hin | [col Hcol]]; first exact: Hwf Hin.
  by have -> : t = snd (nop_cell col) by rewrite -Hcol.
Qed.

Lemma pad_code_entry_orig cde cde' i t e :
  entry t = Some e -> List.In (i, t) (pad_code cde cde').1 -> List.In (i, t) cde.
Proof.
  move=> He /pad_code_cells [//|[col Hcol]].
  by move: He; have -> : t = snd (nop_cell col) by rewrite -Hcol.
Qed.

Lemma pad_code_mrlabel_orig cde cde' i t l :
  i = @MrLabel mt l -> List.In (i, t) (pad_code cde cde').1 -> List.In (i, t) cde.
Proof.
  move=> Hi /pad_code_cells [//|[col Hcol]].
  by move: Hi; have -> : i = fst (nop_cell col) by rewrite -Hcol.
Qed.

Lemma proc_split_fuel_nonempty n cde b : List.In b (proc_split_fuel n cde) -> b <> [::].
Proof.
  elim: n cde => [|n IH] cde /=.
  - by case: cde => [|x xs] /=; [move=> [] | move=> [<-|[]]].
  - by case: cde => [|x xs] /=; [move=> [] | move=> [<-|/IH]].
Qed.

Lemma proc_split_nonempty cde b : List.In b (proc_split cde) -> b <> [::].
Proof. exact: proc_split_fuel_nonempty. Qed.

Lemma in_flatten_intro (T : Type) (y : T) b bs :
  List.In y b -> List.In b bs -> List.In y (flatten bs).
Proof.
  move=> Hy. elim: bs => [|c bs IH] /=; first by move=> [].
  move=> [Hcb|Hb]; first by subst c; apply/List.in_or_app; left.
  by apply/List.in_or_app; right; exact: IH.
Qed.

Lemma block_color_in cde b :
  List.In b (proc_split cde) ->
  exists i t, List.In (i, t) cde /\ block_color b = color t.
Proof.
  move=> Hb. have Hne := proc_split_nonempty Hb.
  case: b Hb Hne => [|[i t] b'] Hb Hne; first by case: (Hne erefl).
  exists i, t; split; last by [].
  have Hin : List.In (i, t) (flatten (proc_split cde)).
  { apply: (in_flatten_intro (b := (i, t) :: b')); [by left | exact Hb]. }
  by move: Hin; rewrite proc_split_flatten.
Qed.

Lemma pad_code_color cde cde' (Dom : {fset Component.id}) :
  (forall i t, List.In (i, t) cde -> color t \in Dom) ->
  forall i t, List.In (i, t) (pad_code cde cde').1 -> color t \in Dom.
Proof.
  move=> Hc i t. rewrite /pad_code => /align_blocks_cells_l.
  rewrite proc_split_flatten => -[Hin | [b [Hb Hx]]]; first exact: Hc Hin.
  have [i0 [t0 [Hin0 Hcol]]] := block_color_in Hb.
  have Hcc : color (snd (nop_cell (block_color b))) = block_color b by [].
  have Ht : t = snd (nop_cell (block_color b)) by rewrite -Hx.
  rewrite Ht Hcc Hcol. exact: Hc Hin0.
Qed.

Lemma pad_code_color' cde cde' (Dom : {fset Component.id}) :
  (forall i t, List.In (i, t) cde' -> color t \in Dom) ->
  forall i t, List.In (i, t) (pad_code cde cde').2 -> color t \in Dom.
Proof.
  move=> Hc i t. rewrite /pad_code => /align_blocks_cells_r.
  rewrite proc_split_flatten => -[Hin | [b [Hb Hx]]]; first exact: Hc Hin.
  have [i0 [t0 [Hin0 Hcol]]] := block_color_in Hb.
  have Hcc : color (snd (nop_cell (block_color b))) = block_color b by [].
  have Ht : t = snd (nop_cell (block_color b)) by rewrite -Hx.
  rewrite Ht Hcc Hcol. exact: Hc Hin0.
Qed.

End Padding.
