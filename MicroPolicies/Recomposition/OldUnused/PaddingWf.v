(* ============================================================================
   PaddingWf.v — [pad_align] PRESERVES [well_formed_program] and [closed_program].

   Piece (a) of the does_prefix wiring: to APPLY [RecPadded.recomposition_blame] to the padded
   programs we must supply a [RecompositionContext] for them, whose content is exactly that
   [pad_align] preserves [well_formed_program] / [closed_program] (the ~13 context axioms; the
   ~37 RecInit hypotheses are standing module-level axioms, not preconditions).

   [well_formed_program] has 7 fields; 4 are trivial under padding (interface/buffers/main are
   UNCHANGED by [pad_align] — [pad_align_interface]/[pad_align_buffers]/[pad_align_main]); the
   real content is [get_procedures], [find_procedure] (= [exported_procedures_existence]) and
   [unique_entry_points], all built here from the cell-level preservation lemmas in [Padding.v].
   ============================================================================ *)
Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Memory.
Require Import Common.Linking.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fset fmap.

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

Section PaddingWf.

Local Notation mcell := ((@Merged.instr mt) * mem_tag)%type.
Local Notation mcode := (@Merged.code mt).

(* ===== cell-SUBSET direction: every ORIGINAL cell survives padding (blocks keep their cells). ===== *)

(* the left output of [align_blocks] keeps every cell of [flatten bs]. *)
Lemma align_blocks_orig_in_l (bs bs' : seq mcode) x :
  List.In x (flatten bs) -> List.In x (align_blocks bs bs').1.
Proof.
  elim: bs bs' => [|b bs IH] [|b' bs'] //=.
  case E: (align_blocks bs bs') => [r r'] /=.
  rewrite /block_pad -catA => /List.in_app_iff [Hb | Hrest].
  - by apply/List.in_or_app; left.
  - apply/List.in_or_app; right; apply/List.in_or_app; right.
    by have := IH bs'; rewrite E /= => /(_ Hrest).
Qed.

(* hence every original cell is a cell of the padded (left) code. *)
Lemma pad_code_orig_in (cde cde' : mcode) x :
  List.In x cde -> List.In x (pad_code cde cde').1.
Proof.
  rewrite /pad_code -{1}(proc_split_flatten cde). exact: align_blocks_orig_in_l.
Qed.

(* same at the program level (unfold [code (pad_align ...).1] to [pad_code ...] by conversion). *)
Lemma pad_align_orig_in (q q' : program) x :
  List.In x (code q) -> List.In x (code (pad_align q q').1).
Proof.
  move=> H. have -> : code (pad_align q q').1 = (pad_code (code q) (code q')).1 by [].
  exact: (pad_code_orig_in (code q') H).
Qed.

(* RIGHT-output mirrors. *)
Lemma align_blocks_orig_in_r (bs bs' : seq mcode) x :
  List.In x (flatten bs') -> List.In x (align_blocks bs bs').2.
Proof.
  elim: bs bs' => [|b bs IH] [|b' bs'] //=.
  case E: (align_blocks bs bs') => [r r'] /=.
  rewrite /block_pad -catA => /List.in_app_iff [Hb | Hrest].
  - by apply/List.in_or_app; left.
  - apply/List.in_or_app; right; apply/List.in_or_app; right.
    by have := IH bs'; rewrite E /= => /(_ Hrest).
Qed.

Lemma pad_code_orig_in2 (cde cde' : mcode) x :
  List.In x cde' -> List.In x (pad_code cde cde').2.
Proof.
  rewrite /pad_code -{1}(proc_split_flatten cde'). exact: align_blocks_orig_in_r.
Qed.

Lemma pad_align_orig_in2 (q q' : program) x :
  List.In x (code q') -> List.In x (code (pad_align q q').2).
Proof.
  move=> H. have -> : code (pad_align q q').2 = (pad_code (code q) (code q')).2 by [].
  exact: (pad_code_orig_in2 (code q) H).
Qed.

(* bridge between Coq's [List.In] (used by the cell lemmas) and ssreflect's [\in] (used by [fset]). *)
Lemma In_inP {T : eqType} {x : T} {s : seq T} : reflect (List.In x s) (x \in s).
Proof.
  elim: s => [|y s IH] /=; first by rewrite in_nil; right; case.
  rewrite inE; apply: (iffP orP).
  - by case=> [/eqP->|/IH H]; [left | right].
  - by case=> [->|/IH H]; [left; rewrite eqxx | right].
Qed.

(* [List.In] commutes with [seq.map] (cells are not an eqType, so we stay in [List.In] for them). *)
Lemma in_map_seq (T1 T2 : Type) (f : T1 -> T2) (l : seq T1) (x : T1) :
  List.In x l -> List.In (f x) (map f l).
Proof. elim: l => [|a l IH] //=. by case=> [->|/IH H]; [left | right]. Qed.

Lemma in_map_seq_inv (T1 T2 : Type) (f : T1 -> T2) (l : seq T1) (y : T2) :
  List.In y (map f l) -> exists x, List.In x l /\ y = f x.
Proof.
  elim: l => [|a l IH] /=; first by move=> [].
  case=> [Heq | /IH [x [Hx Hy]]].
  - by exists a; split; [left | rewrite Heq].
  - by exists x; split; [right |].
Qed.

(* a cell's colour is in its program's [get_procedures]. *)
Lemma color_in_get_procedures (q : program) i t :
  List.In (i, t) (code q) -> color t \in get_procedures q.
Proof.
  move=> Hin. rewrite /get_procedures in_fset. apply/In_inP.
  exact: (in_map_seq (fun '(_, tag) => color tag) Hin).
Qed.

(* ===== [get_procedures] preservation: padding adds no new component colours, and keeps every
   original colour (original cells survive). ===== *)
Lemma get_procedures_pad (q q' : program) :
  get_procedures (pad_align q q').1 = get_procedures q.
Proof.
  apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => x.
  - (* padded ⊆ original — via [pad_code_color] with the original colour-set as the domain *)
    rewrite {1}/get_procedures in_fset => Hx.
    have Hin0 := elimT In_inP Hx.
    have [[i t] [Hin Hxeq]] := in_map_seq_inv Hin0.
    rewrite Hxeq.
    move: Hin; rewrite /pad_align /= => Hin.
    apply: (pad_code_color (Dom := get_procedures q)).
    + exact: color_in_get_procedures.
    + exact: Hin.
  - (* original ⊆ padded — original cells survive padding *)
    rewrite {1}/get_procedures in_fset => Hx.
    have Hin0 := elimT In_inP Hx.
    have [[i t] [Hin Hxeq]] := in_map_seq_inv Hin0.
    rewrite Hxeq.
    apply: (color_in_get_procedures (q := (pad_align q q').1)).
    exact: (pad_align_orig_in q' Hin).
Qed.

(* ===== [find_procedure] preservation (backward): an original procedure stays defined. ===== *)
Lemma find_procedure_pad (q q' : program) comp proc :
  find_procedure q comp proc -> find_procedure (pad_align q q').1 comp proc.
Proof.
  rewrite /find_procedure => /List.Exists_exists [x [Hin HP]].
  apply/List.Exists_exists; exists x; split => //.
  exact: (pad_align_orig_in q' Hin).
Qed.

(* ===== [has_required_local_buffers] preservation: buffers are unchanged by padding. ===== *)
Lemma has_required_local_buffers_pad (q q' : program) C :
  has_required_local_buffers q C -> has_required_local_buffers (pad_align q q').1 C.
Proof.
  rewrite /has_required_local_buffers => H.
  by have [-> _] := pad_align_buffers q q'.
Qed.

(* ===== [well_formed_program] preservation.  6 of the 7 fields follow from the preservation lemmas
   above + the unchanged interface/buffers/main; the 7th, [unique_entry_points] (positional), is
   supplied as a parameter (it is preserved — NOPs carry [entry = None] so only the original entry
   cells, kept in order, ever match — but its proof is a separate positional argument). ===== *)
Lemma well_formed_pad (q q' : program) :
  well_formed_program q ->
  unique_entry_points (code (pad_align q q').1) ->
  well_formed_program (pad_align q q').1.
Proof.
  move=> Hwf Huep.
  have [Hi _] := pad_align_interface q q'.
  have [Hb _] := pad_align_buffers  q q'.
  have [Hm _] := pad_align_main     q q'.
  constructor.
  - rewrite Hi. exact: (wfprog_interface_soundness Hwf).
  - rewrite Hi get_procedures_pad. exact: (wfprog_defined_procedures Hwf).
  - rewrite Hi => C P Hexp. apply: find_procedure_pad.
    exact: (wfprog_exported_procedures_existence Hwf Hexp).
  - exact: Huep.
  - rewrite Hi Hb. exact: (wfprog_defined_buffers Hwf).
  - rewrite Hi => C HC. apply: has_required_local_buffers_pad.
    apply: (wfprog_well_formed_buffers Hwf). exact: HC.
  - rewrite Hi Hm. exact: (wfprog_main_existence Hwf).
Qed.

(* RIGHT-output preservation mirrors. *)
Lemma get_procedures_pad2 (q q' : program) :
  get_procedures (pad_align q q').2 = get_procedures q'.
Proof.
  apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => x.
  - rewrite {1}/get_procedures in_fset => Hx.
    have Hin0 := elimT In_inP Hx. have [[i t] [Hin Hxeq]] := in_map_seq_inv Hin0.
    rewrite Hxeq. move: Hin; rewrite /pad_align /= => Hin.
    apply: (pad_code_color' (Dom := get_procedures q')).
    + exact: color_in_get_procedures.
    + exact: Hin.
  - rewrite {1}/get_procedures in_fset => Hx.
    have Hin0 := elimT In_inP Hx. have [[i t] [Hin Hxeq]] := in_map_seq_inv Hin0.
    rewrite Hxeq. apply: (color_in_get_procedures (q := (pad_align q q').2)).
    exact: (pad_align_orig_in2 q Hin).
Qed.

Lemma find_procedure_pad2 (q q' : program) comp proc :
  find_procedure q' comp proc -> find_procedure (pad_align q q').2 comp proc.
Proof.
  rewrite /find_procedure => /List.Exists_exists [x [Hin HP]].
  apply/List.Exists_exists; exists x; split => //.
  exact: (pad_align_orig_in2 q Hin).
Qed.

Lemma has_required_local_buffers_pad2 (q q' : program) C :
  has_required_local_buffers q' C -> has_required_local_buffers (pad_align q q').2 C.
Proof.
  rewrite /has_required_local_buffers => H.
  by have [_ ->] := pad_align_buffers q q'.
Qed.

(* mirror of [well_formed_pad] for the RIGHT output. *)
Lemma well_formed_pad2 (q q' : program) :
  well_formed_program q' ->
  unique_entry_points (code (pad_align q q').2) ->
  well_formed_program (pad_align q q').2.
Proof.
  move=> Hwf Huep.
  have [_ Hi] := pad_align_interface q q'.
  have [_ Hb] := pad_align_buffers  q q'.
  have [_ Hm] := pad_align_main     q q'.
  constructor.
  - rewrite Hi. exact: (wfprog_interface_soundness Hwf).
  - rewrite Hi get_procedures_pad2. exact: (wfprog_defined_procedures Hwf).
  - rewrite Hi => C P Hexp. apply: find_procedure_pad2.
    exact: (wfprog_exported_procedures_existence Hwf Hexp).
  - exact: Huep.
  - rewrite Hi Hb. exact: (wfprog_defined_buffers Hwf).
  - rewrite Hi => C HC. apply: has_required_local_buffers_pad2.
    apply: (wfprog_well_formed_buffers Hwf). exact: HC.
  - rewrite Hi Hm. exact: (wfprog_main_existence Hwf).
Qed.

(* ===== [closed_program] preservation for a padded LINK (interface closedness + main). ===== *)
Lemma closed_program_pad_link (bp bp' bc bc' : program) :
  closed_program (program_link bp bc) ->
  closed_program (program_link (pad_align bp bp').1 (pad_align bc bc').1).
Proof.
  case=> Hci Hmain; constructor.
  - move: Hci; rewrite /program_link /= => H; exact: H.
  - move: Hmain; rewrite /program_link /= => H; exact: H.
Qed.

(* RIGHT-output mirror. *)
Lemma closed_program_pad_link2 (bp bp' bc bc' : program) :
  closed_program (program_link bp' bc') ->
  closed_program (program_link (pad_align bp bp').2 (pad_align bc bc').2).
Proof.
  case=> Hci Hmain; constructor.
  - move: Hci; rewrite /program_link /= => H; exact: H.
  - move: Hmain; rewrite /program_link /= => H; exact: H.
Qed.

End PaddingWf.
