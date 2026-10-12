(** * T2M — frozen statements for the T → Merged/me simulation.

    No proofs: defines the per-program statics [t2m_ok], the fit
    conditions [state_fits]/[binop_ok]/[run_fits], and the two prefix-
    level statements [t2me_fwd_statement]/[t2me_bwd_statement]. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Util.
Require Import Common.Linking.
Require Import Common.CompCertExtensions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssrint seq.
From extructures Require Import ord fmap fset.
From CoqUtils Require Import word.

Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.

Require Import MicroPolicies.Types.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.LabelScheme.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import MicroPolicies.Recomposition.BackTranslation.

Require Import S2T.TSem.
Require Import S2T.TSim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition NC : nat := 14.

(* ================================================================== *)
(* 1. Fit bounds.                                                     *)
(* ================================================================== *)

(* me reads R_COM as a SIGNED 32-bit word, so exact payload agreement
   needs the value inside [-2^31, 2^31) *)
Definition int_fits (z : Z) : Prop :=
  BinInt.Z.le (BinInt.Z.opp (BinInt.Z.pow 2 31)) z /\
  BinInt.Z.lt z (BinInt.Z.pow 2 31).

(* representable [IConst] immediates: 15 bits, expanded UNSIGNED *)
Definition imm_ok (z : Z) : Prop :=
  BinInt.Z.le 0 z /\ BinInt.Z.lt z (BinInt.Z.pow 2 15).

(* per-component heap region of the me bump allocator *)
Definition heap_capacity : nat := 2 ^ (word_size Int32.mt - NC).

(* ================================================================== *)
(* 2. Per-program statics: [t2m_ok].                                  *)
(*    [lin_ok_at] packages the canonical-bound conditions; this file  *)
(*    adds branch-forwardness and immediate representability. All     *)
(*    conditions are decidable.                                       *)
(* ================================================================== *)

Section Statics.

Variables L P C : nat.
Variable pr : Intermediate.program.

(* Every [IBnz l] has [ILabel l] LATER in the SAME procedure body.
   (S2I labels are block-local, so this gives forwardness of the whole
   flattened component array, which the unsigned relative [Bnz]
   encoding needs.) *)
Definition branches_forward : Prop :=
  forall cid Cprocs Pid Pcode n r l,
    Intermediate.prog_procedures pr cid = Some Cprocs ->
    getm Cprocs Pid = Some Pcode ->
    List.nth_error Pcode n = Some (IBnz r l) ->
    exists m, n < m /\ List.nth_error Pcode m = Some (ILabel l).

Definition buf_size (b : nat + seq value) : nat :=
  match b with inl n => n | inr l => size l end.

(* Every [IConst] immediate is representable: integers in the unsigned
   15-bit window, pointers into a DECLARED block of the instruction's
   own component at an in-range offset. *)
Definition imm_fits : Prop :=
  forall cid Cprocs Pid Pcode n v r,
    Intermediate.prog_procedures pr cid = Some Cprocs ->
    getm Cprocs Pid = Some Pcode ->
    List.nth_error Pcode n = Some (IConst v r) ->
    match v with
    | IInt z => imm_ok z
    | IPtr p =>
      [/\ Pointer.component p = cid,
          BinInt.Z.le 0 (Pointer.offset p)
        & exists bufs bf,
            getm (Intermediate.prog_buffers pr) (Pointer.component p) = Some bufs /\
            getm bufs (Pointer.block p) = Some bf /\
            BinInt.Z.to_nat (Pointer.offset p) < buf_size bf]
    end.

Definition t2m_ok : Prop :=
  [/\ lin_ok_at L P C pr, branches_forward & imm_fits].

End Statics.

(* the canonical joint buffer map and joint interface of a linked pair;
   both sides compile against them *)
Definition PBw (a b : Intermediate.program) :=
  unionm (Intermediate.prog_buffers a) (Intermediate.prog_buffers b).
Definition PIw (a b : Intermediate.program) :=
  unionm (Intermediate.prog_interface a) (Intermediate.prog_interface b).

(* the linked pair fits the 15-bit absolute-Jal / alloc_label window,
   and component colours fit NC *)
Definition link_fits (L P C : nat) (a b : Intermediate.program) : Prop :=
  let W := Definitions.program_link (compiler L P C (PBw a b) (PIw a b) a)
                                    (compiler L P C (PBw a b) (PIw a b) b) in
  [/\ size (linearize_bufs (Definitions.prog_buffers W))
       + size (Definitions.code W) < Merged.alloc_label
    & forall cid,
        cid \in domm (Definitions.prog_interface W) -> 1 + cid < 2 ^ NC].

(* ================================================================== *)
(* 3. The fit condition: [state_fits] over T states, [run_fits] over  *)
(*    the (deterministic) T run up to a trace prefix.                 *)
(* ================================================================== *)

Section Fit.

Variable cde : Transitional.code.
Variable tp : Intermediate.program.

(* A pointer is confined to a declared block, at a nonnegative offset
   no greater than the block size.  The [<=] tolerates a one-past-end
   pointer. *)
Definition ptr_fits (mem : Transitional.Memory.t) (p : Pointer.t) : Prop :=
  BinInt.Z.le 0 (Pointer.offset p) /\
  exists cm blk,
    getm mem (Pointer.component p) = Some cm /\
    getm (Transitional.Memory.content cm) (Pointer.block p) = Some blk /\
    BinInt.Z.to_nat (Pointer.offset p) <= size blk.

Definition value_fits (mem : Transitional.Memory.t) (v : value) : Prop :=
  match v with
  | Int z => int_fits z
  | Ptr p => ptr_fits mem p
  | Undef => True
  end.

(* total footprint of a component's blocks, in me-allocator terms
   (each block costs size+1 — the bump allocator's one-word gap) *)
Definition heap_used (cm : Transitional.Memory.mem) : nat :=
  sumn [seq (size p.2).+1
       | p <- Maps.elementsm (Transitional.Memory.content cm)].

Definition state_fits (s : TS.state) : Prop :=
  let '(mem, regs, _, _) := s in
  [/\
      (forall r, value_fits mem (Transitional.Register.get_value r regs)),
      (forall cid cm b blk n cell,
          getm mem cid = Some cm ->
          getm (Transitional.Memory.content cm) b = Some blk ->
          List.nth_error blk n = Some cell ->
          value_fits mem (Transitional.val (fst cell)))
    &
      (forall cid cm, getm mem cid = Some cm -> heap_used cm < heap_capacity)].

(* binop_ok: me computes 32-bit words, so [Leq]/[Eq] agree with T only
   under placement constraints — signed [Leq] on nonnegative operands,
   pointer [Eq] same-block at strictly-in-block offsets (one-past-end
   pointers at the address-space edge can wrap) *)
Definition binop_ok (s : TS.state) : Prop :=
  let '(mem, regs, pc, _) := s in
  forall op r1 r2 r3 tg c,
    Transitional.executing cde pc (TrBinOp op r1 r2 r3) tg c ->
    match op,
          Transitional.val (Transitional.Register.get r1 regs),
          Transitional.val (Transitional.Register.get r2 regs) with
    | Leq, Ptr p1, Ptr p2 => False
    | Eq, Ptr p1, Ptr p2 =>
        [/\ Pointer.component p1 = Pointer.component p2,
            Pointer.block p1 = Pointer.block p2
          & exists cm blk,
              [/\ getm mem (Pointer.component p1) = Some cm,
                  getm (Transitional.Memory.content cm)
                    (Pointer.block p1) = Some blk,
                  BinInt.Z.to_nat (Pointer.offset p1) < size blk
                & BinInt.Z.to_nat (Pointer.offset p2) < size blk]]
    | _, _, _ => True
    end.

Definition trace_leq (t1 t2 : Events.trace) : Prop :=
  exists t, t2 = t1 ++ t.

(* T is deterministic, so the states reached while [tp]'s trace stays a
   prefix of [m] form a well-defined set; [run_fits m] says they all
   satisfy [state_fits] and [binop_ok] *)
Definition run_fits (m : Events.trace) : Prop :=
  forall s0 tr s,
    TSim.t_initial_base cde tp s0 ->
    star TS.step cde s0 tr s ->
    trace_leq tr m ->
    [/\ state_fits s & binop_ok s].

End Fit.

(* ================================================================== *)
(* 4. The two simulation statements.  Prefix-level (not a CompCert    *)
(*    [forward_simulation] record): a T step leaving fit has no me    *)
(*    counterpart, and both machines are determinate.                 *)
(* ================================================================== *)

Section Statements.

Variables L P C : nat.
Variables a b : Intermediate.program.

Definition tp  := Intermediate.program_link a b.
Definition cde := Transitional.intermediate_to_transitional tp.
Definition Wme :=
  Definitions.program_link (compiler L P C (PBw a b) (PIw a b) a)
                           (compiler L P C (PBw a b) (PIw a b) b).

Definition tsem  := TSim.t_sem cde tp.
Definition mesem := RSCDefs.me_sem NC Wme.

(* the standing premises, shared by both statements *)
Definition t2me_premises : Prop :=
  [/\ (exists sa, Source.well_formed_program sa /\ compile_program sa = Some a),
      (exists sb, Source.well_formed_program sb /\ compile_program sb = Some b),
      Intermediate.well_formed_program a,
      Intermediate.well_formed_program b
    & linkable (Intermediate.prog_interface a) (Intermediate.prog_interface b)]
  /\ Intermediate.closed_program tp
  /\ [/\ t2m_ok L P C a, t2m_ok L P C b & link_fits L P C a b].

(* fwd: what [bt_run] needs *)
Definition t2me_fwd_statement : Prop :=
  t2me_premises ->
  forall m,
    does_prefix tsem m ->
    not_wrong_finpref m ->
    run_fits cde tp (finpref_trace m) ->
    does_prefix mesem m.

(* bwd: what [H_bwd_src] needs (composed with S2T's backward simulation) *)
Definition t2me_bwd_statement : Prop :=
  t2me_premises ->
  forall m,
    does_prefix mesem m ->
    run_fits cde tp (finpref_trace m) ->
    exists beh,
      program_behaves tsem beh /\
      (CompCertExtensions.prefix m beh \/ behavior_improves_finpref beh m).

End Statements.
