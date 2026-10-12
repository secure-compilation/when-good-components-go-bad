(* Task #14 (I→Merged correctness): COMPILED-program instantiations.

   S2I/LabelUniq's [compiled_labels_unique] discharges LinPos's [Huniq]
   premise (per-component label uniqueness), so the body-label (IBnz)
   resolution lemmas hold unconditionally for compiled programs. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import zify.
From CoqUtils Require Import word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import Common.Memory.
Require Import Intermediate.Machine.
Require Import Source.Language.
Require Import S2I.Compiler.
Require Import S2I.LabelUniq.
Require Import MicroPolicies.Recomposition.LinMem.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.LabelScheme.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import MicroPolicies.Recomposition.LinPos.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* the two marker predicates are definitionally equal *)
Lemma is_ilabelE (l : nat) (mi : Machine.instr) :
  LabelUniq.is_ilabel l mi = ilab l mi.
Proof. by []. Qed.

(* [compiled_labels_unique] in LinPos's [Huniq] shape *)
Lemma compiled_Huniq (sp : Source.program) (p : Intermediate.program) :
  compile_program sp = Some p ->
  forall (c : Component.id) (l : nat) (Cprocs : NMap Machine.code),
    Intermediate.prog_procedures p c = Some Cprocs ->
    sumn [seq count (ilab l) (odflt [::] (Cprocs p')) | p' <- domm Cprocs]
    <= 1.
Proof.
move=> Hcomp c l Cprocs Hget.
have := compiled_labels_unique Hcomp l Hget.
have -> : [seq count (LabelUniq.is_ilabel l) (odflt [::] (Cprocs p'))
          | p' <- domm Cprocs]
          = [seq count (ilab l) (odflt [::] (Cprocs p'))
            | p' <- domm Cprocs].
{ apply: eq_map => p' /=.
  apply: eq_count => mi.
  exact: is_ilabelE. }
by [].
Qed.

(* body-label (IBnz target) resolution, unconditional for compiled programs *)
Section CompiledBody.

Variables L P C : nat.
Variable sp : Source.program.
Variable pr : Intermediate.program.
Hypothesis Hcomp : compile_program sp = Some pr.

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

Lemma compiled_body_findopt Cprocs p Pcode o :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some (ILabel l) ->
  findopt (is_label_def (mk_body L c l)) (lin_code L P C pr)
  = Some (flat_pos pr c p Pcode o + 0).
Proof.
move=> HCc HPp Ho.
apply: (@lin_code_body_findopt L P C pr Hlab_bound c l HcC HlL _
          Cprocs p Pcode o HCc HPp Ho).
move=> Cprocs0 HCc0.
exact: (compiled_Huniq Hcomp l HCc0).
Qed.

Lemma compiled_label_pos_body Cprocs p Pcode o (pc0 default : nat) :
  Intermediate.prog_procedures pr c = Some Cprocs ->
  Cprocs p = Some Pcode ->
  List.nth_error Pcode o = Some (ILabel l) ->
  code_label_pos (lin_code L P C pr) pc0 (mk_body L c l) default
  = pc0 + (flat_pos pr c p Pcode o + 0).
Proof.
move=> HCc HPp Ho.
apply: (@code_label_pos_body L P C pr Hlab_bound c l HcC HlL _
          Cprocs p Pcode o pc0 default HCc HPp Ho).
move=> Cprocs0 HCc0.
exact: (compiled_Huniq Hcomp l HCc0).
Qed.

End CompiledBody.

(* ==================== initial-memory pointer discharge ==================== *)

(* a defined load from the prepared initial memory reads a static buffer
   chunk (or the inl-filler Undef) *)
Lemma prepare_load_chunk (p : Intermediate.program)
    (C : Component.id) (b : Block.id) (o : Z) (v : value) :
  Memory.Memory.load (Intermediate.prepare_procedures_memory p) (C, b, o)
    = Some v ->
  (exists bm chunk,
     [/\ Intermediate.prog_buffers p C = Some bm,
         getm bm b = Some (inr chunk)
       & List.nth_error chunk (Z.to_nat o) = Some v])
  \/ v = Undef.
Proof.
rewrite prepare_procedures_memory_load.
rewrite /Memory.Memory.load /= prepare_initial_memoryE.
case: (C \in domm (Intermediate.prog_interface p)) => //=.
rewrite ComponentMemory.load_prealloc.
case: (0 <=? o)%Z => //.
case Eb: (getm (odflt emptym (Intermediate.prog_buffers p C)) b)
  => [buf|] //.
case: buf Eb => [sz|chunk] Eb.
- by case: (o <? Z.of_nat sz)%Z => // [[<-]]; right.
- move=> Hnth. left.
  move: Eb.
  case EC: (Intermediate.prog_buffers p C) => [bm|] /=;
    last by rewrite emptymE.
  move=> Eb. by exists bm, chunk; split.
Qed.

(* the buffer maps of a union of gen_buffers images are gen_buffers
   blocks: pointer values in them are pinned by the sides' wf *)
Lemma compiled_Hptr_union (spa spb : Source.program)
    (p : Intermediate.program) :
  Source.well_formed_program spa ->
  Source.well_formed_program spb ->
  Intermediate.prog_buffers p
    = unionm (gen_buffers (Source.prog_buffers spa))
             (gen_buffers (Source.prog_buffers spb)) ->
  forall (C0 : Component.id) (b b' : Block.id) (off o' : Z)
         (c' : Component.id),
    Memory.Memory.load (Intermediate.prepare_procedures_memory p)
      (C0, b, off) = Some (Ptr (c', b', o')) ->
    exists bm',
      Intermediate.prog_buffers p c' = Some bm' /\ b' \in domm bm'.
Proof.
move=> Hwfa Hwfb Hbuf C0 b b' off o' c' Hload.
have [[bm [chunk [HgetC Hgetb Hnth]]] | //] := prepare_load_chunk Hload.
move: HgetC. rewrite Hbuf unionmE.
case Ega: (getm (gen_buffers (Source.prog_buffers spa)) C0) => [bma|] /=.
- (* left side *)
  move=> [Ebm]. subst bma.
  move: Ega. rewrite /gen_buffers mapmE.
  case Esrc: (Source.prog_buffers spa C0) => [srcbuf|] //= [Ebm2].
  subst bm.
  move: Hgetb. rewrite !setmE.
  case: eqP => [Eb0 | Hne0].
  + case: srcbuf Esrc => [sz|vals] Esrc //= [Echunk].
    subst chunk.
    have Hwfbv := Source.wfprog_buffer_values Hwfa Esrc.
    have HIn := List.nth_error_In _ _ Hnth.
    have Hv := proj1 (List.forallb_forall _ _) Hwfbv _ HIn.
    move: Hv => /=.
    case/andP=> /PeanoNat.Nat.eqb_eq Eb' /PeanoNat.Nat.eqb_eq Ec'.
    subst b' c'.
    eexists. split.
    * by rewrite unionmE mapmE Esrc /=.
    * by rewrite mem_domm setmE eqxx.
  + case: eqP => [Eb1 | //] [Echunk].
    subst chunk.
    move: Hnth.
    case: (Z.to_nat off) => [|[|k]] /=.
    * by move=> H; discriminate H.
    * by move=> H; discriminate H.
    * by rewrite List.nth_error_nil; move=> H; discriminate H.
- (* right side *)
  move=> HgetC.
  move: HgetC. rewrite /gen_buffers mapmE.
  case Esrc: (Source.prog_buffers spb C0) => [srcbuf|] //= [Ebm2].
  subst bm.
  move: Hgetb. rewrite !setmE.
  case: eqP => [Eb0 | Hne0].
  + case: srcbuf Esrc => [sz|vals] Esrc //= [Echunk].
    subst chunk.
    have Hwfbv := Source.wfprog_buffer_values Hwfb Esrc.
    have HIn := List.nth_error_In _ _ Hnth.
    have Hv := proj1 (List.forallb_forall _ _) Hwfbv _ HIn.
    move: Hv => /=.
    case/andP=> /PeanoNat.Nat.eqb_eq Eb' /PeanoNat.Nat.eqb_eq Ec'.
    subst b' c'.
    eexists. split.
    * move: Ega; rewrite /gen_buffers !mapmE => Ega.
      by rewrite unionmE !mapmE Ega Esrc /=.
    * by rewrite mem_domm setmE eqxx.
  + case: eqP => [Eb1 | //] [Echunk].
    subst chunk.
    move: Hnth.
    case: (Z.to_nat off) => [|[|k]] /=.
    * by move=> H; discriminate H.
    * by move=> H; discriminate H.
    * by rewrite List.nth_error_nil; move=> H; discriminate H.
Qed.

(* pointer values loaded from the compiled initial memory target the
   declared local block of their own component (discharges Hptr) *)
Lemma compiled_Hptr (sp : Source.program) (p : Intermediate.program) :
  Source.well_formed_program sp ->
  Intermediate.prog_buffers p = gen_buffers (Source.prog_buffers sp) ->
  forall (C0 : Component.id) (b b' : Block.id) (off o' : Z)
         (c' : Component.id),
    Memory.Memory.load (Intermediate.prepare_procedures_memory p)
      (C0, b, off) = Some (Ptr (c', b', o')) ->
    exists bm',
      Intermediate.prog_buffers p c' = Some bm' /\ b' \in domm bm'.
Proof.
move=> Hwf Hbuf C0 b b' off o' c' Hload.
have [[bm [chunk [HgetC Hgetb Hnth]]] | //] := prepare_load_chunk Hload.
move: HgetC. rewrite Hbuf /gen_buffers mapmE.
case Esrc: (Source.prog_buffers sp C0) => [srcbuf|] //= [Ebm].
subst bm.
move: Hgetb. rewrite !setmE.
case: eqP => [Eb0 | Hne0].
- (* block 0: the source buffer, wf pins the pointer *)
  case: srcbuf Esrc => [sz|vals] Esrc //= [Echunk].
  subst chunk.
  have Hwfb := Source.wfprog_buffer_values Hwf Esrc.
  have HIn := List.nth_error_In _ _ Hnth.
  have Hv := proj1 (List.forallb_forall _ _) Hwfb _ HIn.
  move: Hv => /=.
  case/andP=> /PeanoNat.Nat.eqb_eq Eb' /PeanoNat.Nat.eqb_eq Ec'.
  subst b' c'.
  eexists. split.
  + by rewrite mapmE Esrc /=.
  + by rewrite mem_domm setmE eqxx.
- (* block 1: the [Undef; Int 0] filler has no pointers *)
  case: eqP => [Eb1 | //] [Echunk].
  subst chunk.
  move: Hnth.
  case: (Z.to_nat off) => [|[|k]] /=.
  + by move=> H; discriminate H.
  + by move=> H; discriminate H.
  + by rewrite List.nth_error_nil; move=> H; discriminate H.
Qed.
