(* ============================================================================
   PaddingAlign.v — the padding wrapper's ALIGNMENT-FACT providers.

   Proves, for the NOP-padded programs ([pad_align p p']), the two genuine padding roots of group E:
     - [align_code_size]            : the two padded codes have equal size
                                      (= [pad_align_code_size], given equal #procedure-blocks);
     - [align_find_rank_main_right] : main's entry sits at the same position
                                      (reduces to "main is the FIRST cell", which padding PRESERVES).
   [labels_disjoint_prefix] stays a linearizer-output spec (not a padding fact).
   These discharge the [AlignmentFacts] parameter (Definitions.v) for padded programs.
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
Require Import MicroPolicies.Recomposition.RecompositionTop.

Section PaddingAlign.

Local Notation mcell := ((@Merged.instr mt) * mem_tag)%type.
Local Notation mcode := (@Merged.code mt).

(* [find_rank] returns index 0 exactly when the head cell matches. *)
Lemma find_rank_head {T} (f : pred T) (x : T) (l : seq T) :
  f x -> find_rank f (x :: l) = Some 0.
Proof. move=> Hfx. by rewrite /find_rank /= Hfx. Qed.

(* [proc_split] of a non-empty code: its first block begins with the code's head. *)
Lemma proc_split_cons (x : mcell) (s : mcode) :
  exists b0 bs0, proc_split (x :: s) = (x :: b0) :: bs0.
Proof. rewrite /proc_split /=. by eexists; eexists. Qed.

(* Padding keeps the LEFT output's head cell = [code q]'s head. *)
Lemma pad_align_head (q q' : program) (x : mcell) (s : mcode) :
  code q = x :: s -> exists s', code (pad_align q q').1 = x :: s'.
Proof.
  move=> Hq. rewrite /pad_align /= /pad_code Hq.
  have [b0 [bs0 ->]] := proc_split_cons x s.
  case Hps': (proc_split (code q')) => [| b' bs'] /=.
  - by eexists.
  - case Hab: (align_blocks bs0 bs') => [r r'] /=.
    by rewrite /block_pad /=; eexists.
Qed.

(* Padding keeps the RIGHT output's head cell = [code q']'s head. *)
Lemma pad_align_head2 (q q' : program) (x : mcell) (s : mcode) :
  code q' = x :: s -> exists s', code (pad_align q q').2 = x :: s'.
Proof.
  move=> Hq'. rewrite /pad_align /= /pad_code Hq'.
  have [b0 [bs0 ->]] := proc_split_cons x s.
  case Hps: (proc_split (code q)) => [| b bs] /=.
  - by eexists.
  - case Hab: (align_blocks bs bs0) => [r r'] /=.
    by rewrite /block_pad /=; eexists.
Qed.

(* [align_code_size] for padded programs (= [pad_align_code_size]; given equal #procedure-blocks). *)
Lemma pad_align_code_size_eq (q q' : program) :
  size (proc_split (code q)) = size (proc_split (code q')) ->
  size (code (pad_align q q').1) = size (code (pad_align q q').2).
Proof. exact: pad_align_code_size. Qed.

(* [find_rank main] over a linked program whose left code starts main-coloured is [Some 0]
   ([a] kept abstract so [program_link]/[pad_align] are not over-unfolded). *)
Lemma find_rank_main_link (a r : program) (x : mcell) (s : mcode) :
  code a = x :: s -> color x.2 = Component.main ->
  find_rank (fun '(_, tag) => color tag == Component.main) (code (program_link a r)) = Some 0.
Proof.
  move=> Ha Hx.
  have Hfx : (fun '(_, tag) => color tag == Component.main) x.
  { by rewrite (surjective_pairing x) /= Hx. }
  rewrite /program_link /= Ha /=. exact: (find_rank_head _ Hfx).
Qed.

(* [align_find_rank_main_right] for the padded programs [pad_align p p'].  Both [find_rank main]s
   are [Some 0]: [(pad_align p p').2]'s head = [code p']'s head (main) and [.1]'s head =
   [code p]'s head (main), and [find_rank main] over a main-headed code (++ anything) is [Some 0]. *)
Lemma pad_align_find_rank_main_right (p p' c' : program) (xp xp' : mcell) (sp sp' : mcode) :
  code p  = xp  :: sp  -> color xp.2  = Component.main ->
  code p' = xp' :: sp' -> color xp'.2 = Component.main ->
  find_rank (fun '(_, tag) => color tag == Component.main)
            (code (program_link (pad_align p p').2 c'))
  = find_rank (fun '(_, tag) => color tag == Component.main)
              (code (program_link (pad_align p p').1 c')).
Proof.
  move=> Hp Hxp Hp' Hxp'.
  have [s2 H2] := pad_align_head2 p Hp'.
  have [s1 H1] := pad_align_head p' Hp.
  by rewrite (find_rank_main_link _ H2 Hxp') (find_rank_main_link _ H1 Hxp).
Qed.

End PaddingAlign.

(* ============================================================================
   THE PADDING WRAPPER.  For a [RecompositionContext] [S] whose programs are NOP-padded
   ([S.p]/[S.p'] = the two outputs of [pad_align] on some base pair), [PadAlignFacts] DISCHARGES
   the [AlignmentFacts S] parameter: [align_code_size] + [align_find_rank_main_right] are PROVEN
   from the padding lemmas above; [labels_disjoint_prefix] is the (passed-through) linearizer spec.
   So [RecTop S (PadAlignFacts S H)] yields [recomposition_blame] with the alignment roots
   discharged by padding.
   ============================================================================ *)

(* The padding-structure witnesses for an already-padded context [S]. *)
Module Type PadCtxHyps (S : RecompositionContext).
  Module D := RecompositionDefinitions S.
  Import D.

  (* [S.p]/[S.p'] are the two [pad_align] outputs of a base pair [bp]/[bp']. *)
  Parameters bp bp' : program.
  Axiom Hp_pad  : p  = (pad_align bp bp').1.
  Axiom Hp'_pad : p' = (pad_align bp bp').2.

  (* equal number of procedure-blocks (same interface) ⇒ equal padded code sizes *)
  Axiom Hblocks : size (proc_split (code bp)) = size (proc_split (code bp')).

  (* main is the first cell of each base prefix (linearizer emits main first) — preserved by padding *)
  Axiom Hmain_bp  : exists x s, code bp  = x :: s /\ color x.2 = Component.main.
  Axiom Hmain_bp' : exists x s, code bp' = x :: s /\ color x.2 = Component.main.

  (* labels-disjoint stays the linearizer-output spec *)
  Axiom Hlbl : forall l,
    findopt (fun pc : @Merged.instr mt * mem_tag => match pc.1 with MrLabel l0 => l == l0 | _ => false end) (code p) <> None ->
    findopt (fun pc : @Merged.instr mt * mem_tag => match pc.1 with MrLabel l0 => l == l0 | _ => false end) (code c) = None
    /\ findopt (fun pc : @Merged.instr mt * mem_tag => match pc.1 with MrLabel l0 => l == l0 | _ => false end) (code c') = None.
End PadCtxHyps.

Module PadAlignFacts (S : RecompositionContext) (H : PadCtxHyps S) <: AlignmentFacts S.
  Module D := RecompositionDefinitions S.
  Import D.

  Lemma align_code_size : size (code p) = size (code p').
  Proof. rewrite H.Hp_pad H.Hp'_pad. exact: (pad_align_code_size_eq H.Hblocks). Qed.

  Lemma align_find_rank_main_right :
    find_rank (fun '(_, tag) => color tag == Component.main) (code (program_link p' c'))
    = find_rank (fun '(_, tag) => color tag == Component.main) (code (program_link p c')).
  Proof.
    have [xp  [sp  [Hbpc  Hxp ]]] := H.Hmain_bp.
    have [xp' [sp' [Hbp'c Hxp']]] := H.Hmain_bp'.
    rewrite H.Hp_pad H.Hp'_pad.
    exact: (pad_align_find_rank_main_right c' Hbpc Hxp Hbp'c Hxp').
  Qed.

  Definition labels_disjoint_prefix := H.Hlbl.
End PadAlignFacts.

(* The full discharge: for a padded context [S] (+ padding witnesses [H]), [recomposition_blame]
   holds with the two alignment roots provided by the NOP-padding pass (not assumed).  [RecPadded]'s
   [recomposition_blame] / [recomposition_blame'] are the recomposition theorems for padded programs
   whose [AlignmentFacts] is [PadAlignFacts] — align_code_size + align_find_rank_main_right come from
   [pad_align]; only [labels_disjoint_prefix] remains a linearizer-output assumption. *)
Module RecPadded (S : RecompositionContext) (H : PadCtxHyps S).
  Module AF := PadAlignFacts S H.
  Include RecTop S AF.
End RecPadded.


