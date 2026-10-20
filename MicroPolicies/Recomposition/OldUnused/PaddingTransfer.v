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
Require Import MicroPolicies.Recomposition.PaddingWf.
Require Import MicroPolicies.Recomposition.PaddingLink.
Require Import MicroPolicies.Recomposition.RecompositionTop.
Require Import MicroPolicies.Recomposition.PaddingAlign.
Require Import MicroPolicies.Recomposition.PaddingCorrect.
Require Import MicroPolicies.Recomposition.PaddingFinal.

Local Opaque Merged.initial_state Merged.encode_code Merged.initial_memory
  pad_align pad_code proc_split align_blocks block_pad.

Module Type PadExtra (S0 : RecompositionContext).
  Axiom Huep_p  : unique_entry_points (code (pad_align S0.p S0.p').1).
  Axiom Huep_p' : unique_entry_points (code (pad_align S0.p S0.p').2).
  Axiom Huep_c  : unique_entry_points (code (pad_align S0.c S0.c').1).
  Axiom Huep_c' : unique_entry_points (code (pad_align S0.c S0.c').2).

  Axiom Hblocks_p : size (proc_split (code S0.p)) = size (proc_split (code S0.p')).
  Axiom Hentry_c  : if code S0.c  is x :: _ then is_entry x else true.
  Axiom Hentry_c' : if code S0.c' is x :: _ then is_entry x else true.
  Axiom Hmain_p  : exists x s, code S0.p  = x :: s /\ color x.2 = Component.main.
  Axiom Hmain_p' : exists x s, code S0.p' = x :: s /\ color x.2 = Component.main.
  Axiom Hlbl : forall l,
    findopt (fun pc : @Merged.instr mt * mem_tag => match pc.1 with MrLabel l0 => l == l0 | _ => false end)
            (code (pad_align S0.p S0.p').1) <> None ->
    findopt (fun pc : @Merged.instr mt * mem_tag => match pc.1 with MrLabel l0 => l == l0 | _ => false end)
            (code (pad_align S0.c S0.c').1) = None
    /\ findopt (fun pc : @Merged.instr mt * mem_tag => match pc.1 with MrLabel l0 => l == l0 | _ => false end)
               (code (pad_align S0.c S0.c').2) = None.

  Notation qM  := (program_link S0.p S0.c').
  Notation qM' := (program_link S0.p' S0.c).
  Axiom Mwf : forall i t, List.In (i, t) (code qM) -> is_code t = true /\ vtag t = Other.
  Axiom Mcount : size (proc_split (code qM)) = size (proc_split (code qM')).
  Axiom Mnoterm : forall (j : nat) (dflt : Merged.instr * mem_tag),
    j.+1 < size (code qM) -> PaddingSim.is_term (fst (nth dflt (code qM) j)) = false ->
    is_entry (nth dflt (code qM) j.+1) = false.
  Axiom Mbound : size (@Merged.initial_memory mt (prog_buffers qM)) +
    (size (code qM) + size (code qM')) < alloc_label.
  Axiom Mcolors : forall w a,
    encode_code (code qM) (size (@Merged.initial_memory mt (prog_buffers qM))) w = Some a ->
    1 + color (taga a) < 2 ^ S0.NC.
  Axiom Mlast : forall n i t, n.+1 = size (code qM) ->
    nth_error (code qM) n = Some (i, t) -> PaddingSim.is_term i = true.
  Axiom Mbnz : forall n r l t, nth_error (code qM) n = Some (MrBnz r l, t) ->
    exists m, findopt (fun p : Merged.instr * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code qM) = Some m.
  Axiom Mjal : forall n l t, nth_error (code qM) n = Some (MrJal l, t) ->
    findopt (fun p : Merged.instr * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code qM) = None -> l = alloc_label.
  Axiom Minit : forall w v t,
    unionm (encode_code (code qM) (size (@Merged.initial_memory mt (prog_buffers qM)))) (@Merged.initial_memory mt (prog_buffers qM)) w = Some (v @ t) ->
    PaddingSim.is_codeptr (vtag t) = false.
  Axiom Mmain : find (fun '(_, tag) => color tag == Component.main) (code qM) < size (code qM).
  Axiom Mdomm : forall b, domm (@Merged.initial_memory mt b) =
    fset (map (@word_of_nat (word_size mt)) (List.seq 0 (size (@Merged.initial_memory mt b)))).
  Axiom Mnotcode : forall (w : mword mt) (v : matom), @Merged.initial_memory mt (prog_buffers qM) w = Some v -> is_code (taga v) = false.
  Axiom Mvtag : forall (w : mword mt) (v : matom), @Merged.initial_memory mt (prog_buffers qM) w = Some v -> vtag (taga v) = Other.

  Notation qR  := (program_link S0.p' S0.c').
  Notation qR' := (program_link S0.p S0.c).
  Axiom Rwf : forall i t, List.In (i, t) (code qR) -> is_code t = true /\ vtag t = Other.
  Axiom Rcount : size (proc_split (code qR)) = size (proc_split (code qR')).
  Axiom Rnoterm : forall (j : nat) (dflt : Merged.instr * mem_tag),
    j.+1 < size (code qR) -> PaddingSim.is_term (fst (nth dflt (code qR) j)) = false ->
    is_entry (nth dflt (code qR) j.+1) = false.
  Axiom Rbound : size (@Merged.initial_memory mt (prog_buffers qR)) +
    (size (code qR) + size (code qR')) < alloc_label.
  Axiom Rcolors : forall w a,
    encode_code (code qR) (size (@Merged.initial_memory mt (prog_buffers qR))) w = Some a ->
    1 + color (taga a) < 2 ^ S0.NC.
  Axiom Rlast : forall n i t, n.+1 = size (code qR) ->
    nth_error (code qR) n = Some (i, t) -> PaddingSim.is_term i = true.
  Axiom Rbnz : forall n r l t, nth_error (code qR) n = Some (MrBnz r l, t) ->
    exists m, findopt (fun p : Merged.instr * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code qR) = Some m.
  Axiom Rjal : forall n l t, nth_error (code qR) n = Some (MrJal l, t) ->
    findopt (fun p : Merged.instr * mem_tag => match p.1 with MrLabel l0 => l == l0 | _ => false end) (code qR) = None -> l = alloc_label.
  Axiom Rinit : forall w v t,
    unionm (encode_code (code qR) (size (@Merged.initial_memory mt (prog_buffers qR)))) (@Merged.initial_memory mt (prog_buffers qR)) w = Some (v @ t) ->
    PaddingSim.is_codeptr (vtag t) = false.
  Axiom Rmain : find (fun '(_, tag) => color tag == Component.main) (code qR) < size (code qR).
  Axiom Rnotcode : forall (w : mword mt) (v : matom), @Merged.initial_memory mt (prog_buffers qR) w = Some v -> is_code (taga v) = false.
  Axiom Rvtag : forall (w : mword mt) (v : matom), @Merged.initial_memory mt (prog_buffers qR) w = Some v -> vtag (taga v) = Other.
End PadExtra.

Module PadCtx (S0 : RecompositionContext) (E : PadExtra S0) <: RecompositionContext.
  Definition p  := (pad_align S0.p S0.p').1.
  Definition p' := (pad_align S0.p S0.p').2.
  Definition c  := (pad_align S0.c S0.c').1.
  Definition c' := (pad_align S0.c S0.c').2.
  Definition NC := S0.NC.

  Lemma Hwfp  : well_formed_program p.
  Proof. exact: (@well_formed_pad  S0.p S0.p' S0.Hwfp  E.Huep_p ). Qed.
  Lemma Hwfp' : well_formed_program p'.
  Proof. exact: (@well_formed_pad2 S0.p S0.p' S0.Hwfp' E.Huep_p'). Qed.
  Lemma Hwfc  : well_formed_program c.
  Proof. exact: (@well_formed_pad  S0.c S0.c' S0.Hwfc  E.Huep_c ). Qed.
  Lemma Hwfc' : well_formed_program c'.
  Proof. exact: (@well_formed_pad2 S0.c S0.c' S0.Hwfc' E.Huep_c'). Qed.

  Lemma Hmergeable_ifaces :
    mergeable_interfaces (prog_interface p) (prog_interface c).
  Proof.
    rewrite /p /c.
    have [-> _] := pad_align_interface S0.p S0.p'.
    have [-> _] := pad_align_interface S0.c S0.c'.
    exact: S0.Hmergeable_ifaces.
  Qed.

  Lemma Hifacep : prog_interface p = prog_interface p'.
  Proof.
    rewrite /p /p'.
    have [Hi1 Hi2] := pad_align_interface S0.p S0.p'.
    rewrite Hi1 Hi2. exact: S0.Hifacep.
  Qed.
  Lemma Hifacec : prog_interface c = prog_interface c'.
  Proof.
    rewrite /c /c'.
    have [Hi1 Hi2] := pad_align_interface S0.c S0.c'.
    rewrite Hi1 Hi2. exact: S0.Hifacec.
  Qed.

  Lemma Hprog_is_closed  : closed_program (program_link p  c ).
  Proof. exact: (@closed_program_pad_link  S0.p S0.p' S0.c S0.c' S0.Hprog_is_closed ). Qed.
  Lemma Hprog_is_closed' : closed_program (program_link p' c').
  Proof. exact: (@closed_program_pad_link2 S0.p S0.p' S0.c S0.c' S0.Hprog_is_closed'). Qed.

  Lemma colors_bounded : forall x,
    (x \in domm (prog_interface p)) || (x \in domm (prog_interface c)) -> 1 + x < 2 ^ NC.
  Proof.
    rewrite /p /c /NC.
    have [-> _] := pad_align_interface S0.p S0.p'.
    have [-> _] := pad_align_interface S0.c S0.c'.
    exact: S0.colors_bounded.
  Qed.

  Lemma NC_lt_word : NC < word_size mt.
  Proof. exact: S0.NC_lt_word. Qed.
  Lemma alloc_label_lt_word_NC : alloc_label < expn 2 (word_size mt - NC).
  Proof. exact: S0.alloc_label_lt_word_NC. Qed.
End PadCtx.

Lemma transfer_chain (DPsem DPsem' DPsem'' DPsemP DPsemP' DPsemP'' : Prop) :
  (DPsemP -> DPsemP' -> DPsemP'') ->
  (DPsem  -> DPsemP ) ->
  (DPsem' -> DPsemP') ->
  (DPsemP'' -> DPsem'') ->
  DPsem -> DPsem' -> DPsem''.
Proof. move=> Hpad Hf Hf' Hb HA HB. exact: (Hb (Hpad (Hf HA) (Hf' HB))). Qed.

Module RecOriginal (S0 : RecompositionContext) (E : PadExtra S0).
  Module PC := PadCtx S0 E.

  Module H <: PadCtxHyps PC.
    Module D := RecompositionDefinitions PC.
    Definition bp  := S0.p.
    Definition bp' := S0.p'.
    Lemma Hp_pad  : PC.p  = (pad_align bp bp').1.  Proof. by []. Qed.
    Lemma Hp'_pad : PC.p' = (pad_align bp bp').2.  Proof. by []. Qed.
    Lemma Hblocks : size (proc_split (code bp)) = size (proc_split (code bp')).
    Proof. exact: E.Hblocks_p. Qed.
    Lemma Hmain_bp  : exists x s, code bp  = x :: s /\ color x.2 = Component.main.
    Proof. exact: E.Hmain_p. Qed.
    Lemma Hmain_bp' : exists x s, code bp' = x :: s /\ color x.2 = Component.main.
    Proof. exact: E.Hmain_p'. Qed.
    Lemma Hlbl : forall l,
      findopt (fun pc : @Merged.instr mt * mem_tag => match pc.1 with MrLabel l0 => l == l0 | _ => false end) (code PC.p) <> None ->
      findopt (fun pc : @Merged.instr mt * mem_tag => match pc.1 with MrLabel l0 => l == l0 | _ => false end) (code PC.c) = None
      /\ findopt (fun pc : @Merged.instr mt * mem_tag => match pc.1 with MrLabel l0 => l == l0 | _ => false end) (code PC.c') = None.
    Proof. exact: E.Hlbl. Qed.
  End H.

  Module RP := RecPadded PC H.

  Module D0 := RecompositionDefinitions S0.

  Lemma RP_sem''_eq : RP.sem'' = mergedsem S0.NC RP.prog''.
  Proof. exact_no_check (erefl RP.sem''). Qed.
  Lemma RP_sem'_eq : RP.sem' = mergedsem S0.NC RP.prog'.
  Proof. exact_no_check (erefl RP.sem'). Qed.

  Lemma prog_mixed_id :
    RP.prog'' = (pad_align (program_link S0.p S0.c') (program_link S0.p' S0.c)).1.
  Proof.
    have -> : RP.prog'' = program_link (pad_align S0.p S0.p').1 (pad_align S0.c S0.c').2
      by reflexivity.
    rewrite (pad_align_sym S0.c S0.c').
    symmetry. exact: (pad_align_link E.Hblocks_p E.Hentry_c' E.Hentry_c).
  Qed.

  Lemma HbM_derived (m : finpref_behavior) :
    does_prefix RP.sem'' m -> does_prefix D0.sem'' m.
  Proof.
    have HD : D0.sem'' = mergedsem S0.NC (program_link S0.p S0.c') by reflexivity.
    rewrite RP_sem''_eq prog_mixed_id HD.
    exact: (@padding_backward_closed (program_link S0.p S0.c') (program_link S0.p' S0.c)
      E.Mwf E.Mcount E.Mnoterm E.Mbound S0.NC S0.alloc_label_lt_word_NC E.Mcolors E.Mlast
      E.Mbnz E.Mjal E.Minit E.Mmain E.Mdomm E.Mnotcode E.Mvtag m).
  Qed.

  Lemma prog_right_id :
    RP.prog' = (pad_align (program_link S0.p' S0.c') (program_link S0.p S0.c)).1.
  Proof.
    have -> : RP.prog' = program_link (pad_align S0.p S0.p').2 (pad_align S0.c S0.c').2
      by reflexivity.
    rewrite (pad_align_sym S0.p S0.p') (pad_align_sym S0.c S0.c').
    symmetry. exact: (pad_align_link (esym E.Hblocks_p) E.Hentry_c' E.Hentry_c).
  Qed.

  Lemma HfR_derived (m : finpref_behavior) :
    does_prefix D0.sem' m -> does_prefix RP.sem' m.
  Proof.
    have HD : D0.sem' = mergedsem S0.NC (program_link S0.p' S0.c') by reflexivity.
    rewrite RP_sem'_eq prog_right_id HD.
    exact: (@padding_forward_closed (program_link S0.p' S0.c') (program_link S0.p S0.c)
      E.Rwf E.Rcount E.Rnoterm E.Rbound S0.NC S0.alloc_label_lt_word_NC E.Rcolors E.Rlast
      E.Rbnz E.Rjal E.Rinit E.Rmain E.Mdomm E.Rnotcode E.Rvtag m).
  Qed.

  Theorem recomposition_blame_original :
    forall m,
      (does_prefix D0.sem m -> does_prefix RP.sem m) ->
      does_prefix D0.sem m -> does_prefix D0.sem' m -> does_prefix D0.sem'' m.
  Proof.
    move=> m HfL HA HB.
    apply: HbM_derived. apply: RP.recomposition_blame.
    - exact: (HfL HA).
    - exact: (HfR_derived HB).
  Qed.
End RecOriginal.
