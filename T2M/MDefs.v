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


Definition int_fits (z : Z) : Prop :=
  BinInt.Z.le (BinInt.Z.opp (BinInt.Z.pow 2 31)) z /\
  BinInt.Z.lt z (BinInt.Z.pow 2 31).

Definition imm_ok (z : Z) : Prop :=
  BinInt.Z.le 0 z /\ BinInt.Z.lt z (BinInt.Z.pow 2 15).

Definition heap_capacity : nat := 2 ^ (word_size Int32.mt - NC).


Section Statics.

Variables L P C : nat.
Variable pr : Intermediate.program.

Definition branches_forward : Prop :=
  forall cid Cprocs Pid Pcode n r l,
    Intermediate.prog_procedures pr cid = Some Cprocs ->
    getm Cprocs Pid = Some Pcode ->
    List.nth_error Pcode n = Some (IBnz r l) ->
    exists m, n < m /\ List.nth_error Pcode m = Some (ILabel l).

Definition buf_size (b : nat + seq value) : nat :=
  match b with inl n => n | inr l => size l end.

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

Definition PBw (a b : Intermediate.program) :=
  unionm (Intermediate.prog_buffers a) (Intermediate.prog_buffers b).
Definition PIw (a b : Intermediate.program) :=
  unionm (Intermediate.prog_interface a) (Intermediate.prog_interface b).

Definition link_fits (L P C : nat) (a b : Intermediate.program) : Prop :=
  let W := Definitions.program_link (compiler L P C (PBw a b) (PIw a b) a)
                                    (compiler L P C (PBw a b) (PIw a b) b) in
  [/\ size (linearize_bufs (Definitions.prog_buffers W))
       + size (Definitions.code W) < Merged.alloc_label
    & forall cid,
        cid \in domm (Definitions.prog_interface W) -> 1 + cid < 2 ^ NC].


Section Fit.

Variable cde : Transitional.code.
Variable tp : Intermediate.program.

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

Definition run_fits (m : Events.trace) : Prop :=
  forall s0 tr s,
    TSim.t_initial_base cde tp s0 ->
    star TS.step cde s0 tr s ->
    trace_leq tr m ->
    [/\ state_fits s & binop_ok s].

End Fit.


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

Definition t2me_premises : Prop :=
  [/\ (exists sa, Source.well_formed_program sa /\ compile_program sa = Some a),
      (exists sb, Source.well_formed_program sb /\ compile_program sb = Some b),
      Intermediate.well_formed_program a,
      Intermediate.well_formed_program b
    & linkable (Intermediate.prog_interface a) (Intermediate.prog_interface b)]
  /\ Intermediate.closed_program tp
  /\ [/\ t2m_ok L P C a, t2m_ok L P C b & link_fits L P C a b].

Definition t2me_fwd_statement : Prop :=
  t2me_premises ->
  forall m,
    does_prefix tsem m ->
    not_wrong_finpref m ->
    run_fits cde tp (finpref_trace m) ->
    does_prefix mesem m.

Definition t2me_bwd_statement : Prop :=
  t2me_premises ->
  forall m,
    does_prefix mesem m ->
    run_fits cde tp (finpref_trace m) ->
    exists beh,
      program_behaves tsem beh /\
      (CompCertExtensions.prefix m beh \/ behavior_improves_finpref beh m).

End Statements.
