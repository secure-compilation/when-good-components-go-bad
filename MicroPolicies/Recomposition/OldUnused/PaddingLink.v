(* ============================================================================
   PaddingLink.v — [pad_align] DISTRIBUTES over [program_link].

   Goal: [pad_align (program_link p c) (program_link p' c')] = the link of the padded components,
   so the padded linked program equals [program_link (pad p) (pad c)].  This connects [RecPadded]'s
   semantics (on the padded linked programs) to [pad_align] of the ORIGINAL linked programs, enabling
   the [does_prefix] transfer via [padding_forward_closed]/[padding_backward_closed].

   Pieces: [align_blocks_cat] (align_blocks over ++, equal left block-counts) and [proc_split_cat]
   (proc_split over ++ at an entry boundary), assembled into [pad_align_link_code].
   ============================================================================ *)
Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Linking.

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
Require Import MicroPolicies.Recomposition.Padding.

Section PaddingLink.

Local Notation mcell := ((@Merged.instr mt) * mem_tag)%type.
Local Notation mcode := (@Merged.code mt).

(* [align_blocks] distributes over block-list concatenation when the left parts match in length. *)
Lemma align_blocks_cat (bs1 bs1' bs2 bs2' : seq mcode) :
  size bs1 = size bs1' ->
  align_blocks (bs1 ++ bs2) (bs1' ++ bs2') =
  ((align_blocks bs1 bs1').1 ++ (align_blocks bs2 bs2').1,
   (align_blocks bs1 bs1').2 ++ (align_blocks bs2 bs2').2).
Proof.
  elim: bs1 bs1' => [|b bs1 IH] [|b' bs1'] Hsz //=.
  - by case: (align_blocks bs2 bs2').
  - have Hsz' : size bs1 = size bs1' by move: Hsz => /=; lia.
    move: (IH _ Hsz').
    case E1: (align_blocks bs1 bs1') => [r1 r2].
    case E2: (align_blocks bs2 bs2') => [q1 q2].
    case E12: (align_blocks (bs1 ++ bs2) (bs1' ++ bs2')) => [R1 R2] /= [-> ->].
    by rewrite !catA.
Qed.

(* [align_blocks] is symmetric: padding [bs'] against [bs] (right output) = padding [bs'] against
   [bs] (left output of the swap). Per-pair the pad target [maxn |b| |b'|] is symmetric. *)
Lemma align_blocks_sym (bs bs' : seq mcode) :
  (align_blocks bs bs').2 = (align_blocks bs' bs).1.
Proof.
  elim: bs bs' => [|b bs IH] [|b' bs'] //.
  rewrite /=.
  case E:  (align_blocks bs bs') => [r1 r2].
  case E': (align_blocks bs' bs) => [r1' r2'].
  have := IH bs'. rewrite E E' /= => ->. by rewrite maxnC.
Qed.

(* [proc_split_fuel] is fuel-independent once the fuel covers the code size. *)
Lemma proc_split_fuel_ge : forall f cde n m,
  size cde <= f -> size cde <= n -> size cde <= m ->
  proc_split_fuel n cde = proc_split_fuel m cde.
Proof.
  elim => [|f IH] cde n m Hf Hn Hm.
  - by move: Hf Hn Hm; rewrite leqn0 => /eqP/size0nil -> _ _; case: n; case: m.
  - case: cde Hf Hn Hm => [|x xs] Hf Hn Hm; first by move: Hn Hm => _ _; case: n; case: m.
    move: Hn; case: n => [|n] Hn; first by [].
    move: Hm; case: m => [|m] Hm; first by [].
    congr cons. apply: (IH (drop (find is_entry xs) xs) n m);
      rewrite size_drop; move: Hf Hn Hm => /=; lia.
Qed.

(* a sufficiently-fuelled [proc_split_fuel] equals [proc_split]. *)
Lemma proc_split_fuelE cde n : size cde <= n -> proc_split_fuel n cde = proc_split cde.
Proof. move=> Hn. exact: (proc_split_fuel_ge Hn Hn (leqnn _)). Qed.

(* recursive characterisation of [proc_split] (fuel-free). *)
Lemma proc_split_cons_eq (y : mcell) (ys : mcode) :
  proc_split (y :: ys)
  = (y :: take (find is_entry ys) ys) :: proc_split (drop (find is_entry ys) ys).
Proof.
  rewrite {1}/proc_split /=. congr cons.
  apply: (proc_split_fuel_ge (f := size ys)); rewrite size_drop; lia.
Qed.

(* [proc_split] distributes over concatenation when the right part begins at a procedure entry. *)
Lemma proc_split_cat : forall f cde1 cde2,
  size cde1 <= f ->
  (if cde2 is x :: _ then is_entry x else true) ->
  proc_split (cde1 ++ cde2) = proc_split cde1 ++ proc_split cde2.
Proof.
  elim => [|f IH] cde1 cde2 Hf Hc2.
  - by move: Hf; rewrite leqn0 => /eqP/size0nil ->; rewrite cat0s.
  - case: cde1 Hf => [|y cde1'] Hf; first by rewrite cat0s.
    rewrite cat_cons proc_split_cons_eq (proc_split_cons_eq y cde1') find_cat.
    case Hhas: (has is_entry cde1').
    + have Hk1 : find is_entry cde1' < size cde1' by rewrite -has_find Hhas.
      rewrite take_cat drop_cat Hk1 cat_cons.
      congr cons. apply: (IH (drop (find is_entry cde1') cde1') cde2); last exact: Hc2.
      rewrite size_drop; move: Hf => /=; lia.
    + have Hk1 : find is_entry cde1' = size cde1'.
      { apply/eqP; rewrite eqn_leq find_size /=. by rewrite leqNgt -has_find Hhas. }
      have Hf2 : find is_entry cde2 = 0.
      { case: cde2 Hc2 {IH} => [//|x2 cde2'] Hc2 /=. by rewrite Hc2. }
      by rewrite Hk1 Hf2 addn0 take_size_cat // drop_size_cat // take_size drop_size.
Qed.

(* [pad_align] distributes over [program_link] at the code level: padding the linked program
   equals linking the padded components (given equal p-block-counts and entry-headed [code c]/[c']). *)
Lemma pad_align_link_code (p c p' c' : program) :
  size (proc_split (code p)) = size (proc_split (code p')) ->
  (if code c  is x :: _ then is_entry x else true) ->
  (if code c' is x :: _ then is_entry x else true) ->
  code (pad_align (program_link p c) (program_link p' c')).1
  = code (pad_align p p').1 ++ code (pad_align c c').1.
Proof.
  move=> Hblk Hc Hc'.
  rewrite /pad_align /= /pad_code /program_link /=.
  rewrite (proc_split_cat (leqnn (size (code p))) Hc).
  rewrite (proc_split_cat (leqnn (size (code p'))) Hc').
  by rewrite (align_blocks_cat (proc_split (code c)) (proc_split (code c')) Hblk).
Qed.

(* [pad_align] distributes over [program_link] as PROGRAMS (code via [pad_align_link_code];
   interface/buffers/main are preserved by padding and unioned by [program_link]). *)
Lemma pad_align_link (p c p' c' : program) :
  size (proc_split (code p)) = size (proc_split (code p')) ->
  (if code c  is x :: _ then is_entry x else true) ->
  (if code c' is x :: _ then is_entry x else true) ->
  (pad_align (program_link p c) (program_link p' c')).1
  = program_link (pad_align p p').1 (pad_align c c').1.
Proof.
  move=> Hblk Hc Hc'.
  have Hcode := pad_align_link_code Hblk Hc Hc'.
  rewrite {1}/pad_align /= /program_link /=.
  congr Build_program.
  by move: Hcode; rewrite /program_link /= => ->.
Qed.

(* [pad_align] is symmetric: padding [q'] against [q] (right output) equals padding [q'] against
   [q] (left output of the swap).  Needed for the mixed run [prog'' = p + c'] whose [c'] component is
   padded against [c] ([(pad_align c c').2]) — the same program as [(pad_align c' c).1]. *)
Lemma pad_align_sym (q q' : program) :
  (pad_align q q').2 = (pad_align q' q).1.
Proof.
  rewrite /pad_align /= /pad_code.
  congr Build_program.
  exact: (align_blocks_sym (proc_split (code q)) (proc_split (code q'))).
Qed.

End PaddingLink.
