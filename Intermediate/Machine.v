Require Import Common.Definitions.
Require Import Common.Util.
Require Export Common.Values.
Require Export Common.Linking.
Require Import Common.Memory.
Require Import Lib.Monads.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.
From extructures Require Import fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* NOTE: Technically a [Variant], i.e., there is no use for the [Inductive]
   principle in proofs, but it is required to derive a QuickChick generator. *)
Inductive register : Type :=
  R_ONE | R_COM | R_AUX1 | R_AUX2 | R_RA | R_SP | R_ARG.

Definition register_eqb (r1 r2 : register) : bool :=
  match r1, r2 with
  | R_ONE, R_ONE
  | R_COM, R_COM
  | R_AUX1, R_AUX1
  | R_AUX2, R_AUX2
  | R_RA, R_RA
  | R_SP, R_SP
  | R_ARG, R_ARG
    => true
  | _, _
    => false
  end.

Lemma registerP : Equality.axiom register_eqb.
Proof.
  intros [] []; by constructor.
Qed.

Definition register_eqMixin: Equality.mixin_of register := EqMixin registerP.
Canonical register_eqType := Eval hnf in EqType register register_eqMixin.

Definition label := nat.

Variant imvalue : Type :=
| IInt : Z -> imvalue
| IPtr : Pointer.t -> imvalue.

Definition imvalue_eqb (v1 v2 : imvalue) : bool :=
  match v1, v2 with
  | IInt i1, IInt i2 => Z.eqb i1 i2
  | IPtr p1, IPtr p2 => Pointer.eq p1 p2
  | _, _ => false
  end.

Lemma imvalueP : Equality.axiom imvalue_eqb.
Proof.
  intros [] [];
    try (by constructor);
    simpl.
  - destruct (Z.eqb_spec z z0); constructor.
    + subst. reflexivity.
    + injection. contradiction.
  - destruct (Pointer.eqP t t0); constructor.
    + subst. reflexivity.
    + injection. contradiction.
Qed.

Definition imvalue_eqMixin: Equality.mixin_of imvalue := EqMixin imvalueP.
Canonical imvalue_eqType := Eval hnf in EqType imvalue imvalue_eqMixin.

Definition imm_to_val (im : imvalue) : value :=
  match im with
  | IInt n => Int n
  | IPtr p => Ptr p
  end.

Variant instr :=
| INop : instr
| ILabel : label -> instr
(* register operations *)
| IConst : imvalue -> register -> instr
| IMov : register -> register -> instr
| IBinOp : binop -> register -> register -> register -> instr
| IPtrOfLabel : label -> register -> instr
(* memory operations *)
| ILoad : register -> register -> instr
| IStore : register -> register -> instr
| IAlloc : register -> register -> instr
(* conditional and unconditional jumps *)
| IBnz : register -> label -> instr
| IJump : register -> instr
| IJal : label -> instr
(* components interaction *)
| ICall : Component.id -> Procedure.id -> instr
| IReturn : instr
(* termination *)
| IHalt : instr.

Definition instr_eqb (i1 i2 : instr) : bool :=
  match i1, i2 with
  | INop, INop
  | IReturn, IReturn
  | IHalt, IHalt
    => true
  | ILabel l1, ILabel l2
  | IJal l1, IJal l2
    => ssrnat.eqn l1 l2
  | ICall C1 P1, ICall C2 P2
    => ssrnat.eqn C1 C2 && ssrnat.eqn P1 P2
  | IJump r1, IJump r2
    => register_eqb r1 r2
  | ILoad r1 r1', ILoad r2 r2'
  | IStore r1 r1', IStore r2 r2'
  | IAlloc r1 r1', IAlloc r2 r2'
  | IMov r1 r1', IMov r2 r2'
    => register_eqb r1 r2 && register_eqb r1' r2'
  | IPtrOfLabel l1 r1, IPtrOfLabel l2 r2
  | IBnz r1 l1, IBnz r2 l2
    => ssrnat.eqn l1 l2 && register_eqb r1 r2
  | IConst v1 r1, IConst v2 r2
    => imvalue_eqb v1 v2 && register_eqb r1 r2
  | IBinOp op1 r1 r1' r1'', IBinOp op2 r2 r2' r2''
    => binop_eqb op1 op2 &&
       register_eqb r1 r2 && register_eqb r1' r2' && register_eqb r1'' r2''
  | _, _
    => false
  end.

(* TODO: Is this available anywhere? Move in any case. *)
Lemma eqnP : Equality.axiom ssrnat.eqn.
  intros n.
  induction n as [| n' IHn'].
  - intros [| m']; by constructor.
  - intros [| m'].
    + by constructor.
    + simpl.
      specialize (IHn' m').
      inversion IHn'; subst;
        constructor.
      * reflexivity.
      * injection. contradiction.
Qed.

(* TODO: Complete and reuse tactic above. *)
Ltac t_reflecter :=
  repeat
    (* From the rightto account for the associativity of the conjunction. *)
    (match goal with
     | |- ssrbool.reflect _ (ssrnat.eqn ?N1 ?N2) =>
       destruct (eqnP N1 N2)
     | |- ssrbool.reflect _ (_ && ssrnat.eqn ?N1 ?N2) =>
       destruct (eqnP N1 N2)
     | |- ssrbool.reflect _ (imvalue_eqb ?N1 ?N2) =>
       destruct (imvalueP N1 N2)
     | |- ssrbool.reflect _ (binop_eqb ?OP1 ?OP2) =>
       destruct (binopP OP1 OP2)
     | |- ssrbool.reflect _ (register_eqb ?R1 ?R2) =>
       destruct (registerP R1 R2)
     | |- ssrbool.reflect _ (_ && register_eqb ?R1 ?R2) =>
       destruct (registerP R1 R2)
     end;
     subst;
     (* Rearrange conjuncts so that simplification and recursion work. *)
     try rewrite andb_true_r; try rewrite andb_false_r;
     simpl);
  (* Phase 2: solve appropriate reflection case. *)
  constructor;
  (* True cases are solved by reflexivity... *)
  try reflexivity;
  (* ... and false cases by contradiction on injective constructors. *)
  injection; contradiction.

Lemma instrP : Equality.axiom instr_eqb.
Proof.
  intros [] [];
    try (by constructor);
    simpl;
    t_reflecter.
Qed.

Definition instr_eqMixin: Equality.mixin_of instr := EqMixin instrP.
Canonical instr_eqType := Eval hnf in EqType instr instr_eqMixin.

Definition code := list instr.

Definition code_eqb (c1 c2 : code) : bool :=
  eqseq c1 c2.

Lemma codeP : Equality.axiom code_eqb.
Proof.
  intros c1.
  induction c1 as [| i1 c1' IHc1'];
    intros c2.
  - destruct c2 as [| i2 c2'];
      by constructor.
  - destruct c2 as [| i2 c2'].
    + by constructor.
    + simpl. destruct (i1 == i2) eqn:Hcase.
      * move: Hcase => /eqP ->.
        specialize (IHc1' c2').
        inversion IHc1'; subst;
          constructor.
        -- reflexivity.
        -- injection as ?; subst.
           contradiction.
      * constructor.
        injection as ? ?; subst.
        move: Hcase => /eqP.
        contradiction.
Qed.

Definition code_eqMixin: Equality.mixin_of code := EqMixin codeP.
Canonical code_eqType := Eval hnf in EqType code code_eqMixin.

Module Intermediate.

Module Register.
  Definition t : Type := NMap value.

  Definition to_nat (r : register) : nat :=
    match r with
    | R_ONE  => 0
    | R_COM  => 1
    | R_AUX1 => 2
    | R_AUX2 => 3
    | R_RA   => 4
    | R_SP   => 5
    | R_ARG  => 6
    end.

  Definition init :=
    mkfmap [(to_nat R_ONE, Undef);
            (to_nat R_COM, Undef);
            (to_nat R_AUX1, Undef);
            (to_nat R_AUX2, Undef);
            (to_nat R_RA, Undef);
            (to_nat R_SP, Undef);
            (to_nat R_ARG, Undef)].

  Definition get (r : register) (regs : t) : value :=
    match getm regs (to_nat r) with
    | Some val => val
    (* this should never happen (i.e. regs should be well-formed) *)
    | None => Undef
    end.

  Definition set (r : register) (val : value) (regs : t) : t :=
    setm regs (to_nat r) val.

  Definition invalidate (regs : t) : t :=
    mkfmap [(to_nat R_ONE, Undef);
            (to_nat R_COM, get R_COM regs);
            (to_nat R_AUX1, Undef);
            (to_nat R_AUX2, Undef);
            (to_nat R_RA, Undef);
            (to_nat R_SP, Undef);
            (to_nat R_ARG, Undef)].

  Lemma invalidate_eq : forall regs1 regs2,
    get R_COM regs1 = get R_COM regs2 ->
    invalidate regs1 = invalidate regs2.
  Proof.
    intros regs1 regs2 Hregs.
    unfold invalidate.
    congruence.
  Qed.

  Lemma reg_in_domm_init_Undef r:
    r \in domm init ->
    init r = Some Undef.
  Proof.
    unfold init. intros regdomm.
    rewrite !domm_set in regdomm.
    simpl in *.
    repeat match goal with
    | N : nat |- _ => destruct N as [| N]; first by simpl
    end.
    by rewrite !in_fsetU1 domm0 in regdomm.
  Qed.

  Definition eqb (r1 r2 : register) : bool :=
    match r1, r2 with
    | R_ONE, R_ONE
    | R_COM, R_COM
    | R_AUX1, R_AUX1
    | R_AUX2, R_AUX2
    | R_RA, R_RA
    | R_SP, R_SP
    | R_ARG, R_ARG => true
    | _, _ => false
    end.

  Lemma eqP : Equality.axiom eqb.
  Proof.
    intros [] []; by constructor.
  Qed.

  Definition eqMixin: Equality.mixin_of register := EqMixin eqP.
  Canonical eqType := Eval hnf in EqType register eqMixin.

  Lemma to_nat_inv r1 r2 :
    to_nat r1 = to_nat r2 ->
    r1 = r2.
  Proof.
    intros Heq.
    destruct r1;
      destruct r2;
      by inversion Heq.
  Qed.

  Lemma gss reg val regs :
    get reg (Register.set reg val regs) = val.
  Proof.
    by rewrite /get /set setmE eqxx.
  Qed.

  Lemma gso reg reg' val regs :
    reg <> reg' ->
    get reg (Register.set reg' val regs) = Register.get reg regs.
  Proof.
    intros Heq.
    assert (Heqb : reg != reg') by (by apply /eqP).
    unfold get, set. rewrite setmE. unfold eq_op. simpl.
    destruct (ssrnat.eqn (to_nat reg) (to_nat reg')) eqn:Hcase.
    - move: Hcase => /ssrnat.eqnP => Hcase.
      apply to_nat_inv in Hcase.
      contradiction.
    - reflexivity.
  Qed.

  Lemma gicom regs :
    get R_COM (invalidate regs) = get R_COM regs.
  Proof. reflexivity. Qed.

  Lemma gio reg regs :
    reg <> R_COM ->
    get reg (invalidate regs) = Undef.
  Proof. now destruct reg. Qed.

  Lemma gi reg regs :
    get reg (invalidate regs) = if eqb reg R_COM then get reg regs else Undef.
  Proof. now destruct reg. Qed.
End Register.

Module EntryPoint.
  Definition t := NMap (NMap Block.id).

  Definition get (C: Component.id) (P: Procedure.id) (E: t) : option Block.id :=
    match getm E C with
    | Some addrs => getm addrs P
    | None => None
    end.

  Lemma get_some C P E b : get C P E = Some b -> C \in domm E.
  Proof.
    unfold get. intros Hget.
    destruct (E C) as [M |] eqn:Hcase; last discriminate.
    apply /dommP. eauto.
  Qed.
End EntryPoint.

(* programs *)

Record program := mkProg {
  prog_interface: Program.interface;
  prog_procedures: NMap (NMap code);
  prog_buffers: NMap {fmap Block.id -> nat + list value};
  prog_main: bool
}.

(* well-formedness of programs *)

Definition well_formed_instruction
           (p: program) (C: Component.id) (P: Procedure.id) (i: instr) : Prop :=
  match i with
  | IBnz r l =>
    (* the branch refers to a label inside the current procedure C.P *)
    exists Cprocs Pcode,
      getm (prog_procedures p) C = Some Cprocs /\
      getm Cprocs P = Some Pcode /\
      In (ILabel l) Pcode
  | IJal l
  | IPtrOfLabel l _
    =>
    (* the jump refers to a label inside the current component C *)
    exists Cprocs P' P'code,
      getm (prog_procedures p) C = Some Cprocs /\
      getm Cprocs P' = Some P'code /\
      In (ILabel l) P'code
  | ICall C' P' =>
    (* a call is well-formed only if it targets another component and the
       interface is allowing it to happen *)
    C <> C' /\ imported_procedure (prog_interface p) C C' P'
  | IConst (IPtr ptr) r =>
    (* static pointers refer to static buffers *)
    (* [DynShare] NOTE: Pointers can (and need to) be forged as constant
       expressions. The guarantee that these point only to static buffers is
       obtained in tandem with a program semantics that disallows the use of bad
       pointers, and a representation of the program as environment which maps
       static buffers to runtime buffers with exactly the same buffer
       identifiers. At the moment, no symbol substitution/concretization is
       possible, i.e., runtime pointers are exactly those hardcoded in the
       program. *)
    (* [DynShare] Add the restriction that pointers can only be forged to point
       to buffers in the same component. What were the implications of the
       absence of this condition in the existing proof? *)
    Pointer.component ptr = C /\
    exists bufs,
      getm (prog_buffers p) (Pointer.component ptr) = Some bufs /\
      In (Pointer.block ptr) (map fst bufs)
  (* the other instruction are well-formed by construction *)
  | IConst (IInt i) r => True
  | ILabel l => True
  | INop => True
  | IMov r1 r2 => True
  | IBinOp bop r1 r2 r3 => True
  | ILoad r1 r2 => True
  | IStore r1 r2 => True
  | IAlloc r1 r2 => True
  | IJump r => True
  | IReturn => True
  | IHalt => True
  end.

(* RB: TODO: Because program buffers can contain pointers as values, we need to
   consider its impact in initial program state, global environments, and even
   program well-formedness. *)
Record well_formed_program (p: program) := {
  (* the interface is sound (but maybe not closed)
     RB: Currently not used in the proofs. *)
  wfprog_interface_soundness:
    sound_interface (prog_interface p);
  (* there are procedures only for the declared components *)
  wfprog_defined_procedures:
    domm (prog_interface p) = domm (prog_procedures p);
  (* each exported procedure actually exists *)
  wfprog_exported_procedures_existence:
    forall C CI,
      getm (prog_interface p) C = Some CI ->
    forall P,
      Component.is_exporting CI P ->
    exists Cprocs Pcode,
      getm (prog_procedures p) C = Some Cprocs /\
      getm Cprocs P = Some Pcode;
  (* each instruction of each procedure is well-formed *)
  wfprog_well_formed_instructions:
    forall C Cprocs,
      getm (prog_procedures p) C = Some Cprocs ->
    forall P Pcode,
      getm Cprocs P = Some Pcode ->
    forall i, In i Pcode -> well_formed_instruction p C P i;
  (* there are buffers only for the declared components *)
  wfprog_defined_buffers:
    domm (prog_interface p) = domm (prog_buffers p);
  (* buffers may not contain pointer values *)
  wfprog_well_formed_buffers:
    forall C bufs b,
      prog_buffers p C = Some bufs ->
      b \in domm bufs ->
      Buffer.well_formed_buffer_opt (bufs b);
  (* if the main component exists, then the main procedure must exist as well *)
  wfprog_main_existence:
      prog_main p ->
    exists main_procs,
      getm (prog_procedures p) Component.main = Some main_procs /\ Procedure.main \in domm main_procs;
  (* Iff the main component is in the interface, a main procedure is given. *)
  wfprog_main_component:
    (* (RB: Old-style fix, later changed from a simple implication.) *)
    (* prog_main p = None -> *)
    (* Component.main \notin domm (prog_interface p) *)
    Component.main \in domm (prog_interface p) <->
    prog_main p;
  (* wfprog_main_id: *)
  (*   forall mainP, *)
  (*     prog_main p = Some mainP -> *)
  (*     mainP = 0 *)
}.

(* a closed program is a program with a closed interface and an existing main
   procedure *)
Record closed_program (p: program) := {
  (* the interface must be closed (and consequently sound) *)
  cprog_closed_interface:
    closed_interface (prog_interface p);
  (* the main procedure must exist *)
  cprog_main_existence:
    exists main_procs,
      prog_main p /\
      getm (prog_procedures p) Component.main = Some main_procs /\ 0 \in domm main_procs
}.

Definition linkable_mains (prog1 prog2 : program) : Prop :=
  ~~ (prog_main prog1 && prog_main prog2).

Lemma linkable_mains_sym : forall (prog1 prog2 : program),
  linkable_mains prog1 prog2 -> linkable_mains prog2 prog1.
Proof.
  intros prog1 prog2.
  unfold linkable_mains, andb, negb.
  destruct (prog_main prog1);
    destruct (prog_main prog2);
    intuition.
Qed.

(* RB: TODO: Remove superfluous linkable_main assumptions from development.
   Observe the relation to PS.domm_partition_in_union_in_neither. *)
Theorem linkable_implies_linkable_mains : forall (p1 p2 : program),
  well_formed_program p1 ->
  well_formed_program p2 ->
  linkable (prog_interface p1) (prog_interface p2) ->
  linkable_mains p1 p2.
Proof.
  intros p1 p2 Hwf1 Hwf2 [_ Hdisjoint].
  unfold linkable_mains.
  destruct (prog_main p1) as [|] eqn:Hmain1;
    destruct (prog_main p2) as [|] eqn:Hmain2;
    try reflexivity.
  (* All that remains is the contradictory case. *)
  pose proof (proj2 (wfprog_main_component Hwf1)) as Hdomm1.
  rewrite Hmain1 in Hdomm1. specialize (Hdomm1 isT).
  pose proof (proj2 (wfprog_main_component Hwf2)) as Hdomm2.
  rewrite Hmain2 in Hdomm2. specialize (Hdomm2 isT).
  pose proof fdisjointP _ _ Hdisjoint _ Hdomm1 as Hcontra.
  now rewrite Hdomm2 in Hcontra.
Qed.

Definition matching_mains (prog1 prog2 : program) : Prop :=
  prog_main prog1 <-> prog_main prog2.

Definition program_link (p1 p2: program): program :=
  {| prog_interface := unionm (prog_interface p1) (prog_interface p2);
     prog_procedures := unionm (prog_procedures p1) (prog_procedures p2);
     prog_buffers := unionm (prog_buffers p1) (prog_buffers p2);
     prog_main := prog_main p1 || prog_main p2 |}.

Lemma program_linkC p1 p2 :
  well_formed_program p1 ->
  well_formed_program p2 ->
  linkable (prog_interface p1) (prog_interface p2) ->
  program_link p1 p2 = program_link p2 p1.
Proof.
  case: p1 p2 => [i1 p1 b1 m1] [i2 p2 b2 m2] /= Hwf1 Hwf2 [_ Hdis_i].
  have Hdis_p: fdisjoint (domm p1) (domm p2).
    by rewrite -(wfprog_defined_procedures Hwf1) -(wfprog_defined_procedures Hwf2).
  congr mkProg=> /=; try rewrite unionmC //.
    by rewrite -(wfprog_defined_buffers Hwf1) -(wfprog_defined_buffers Hwf2).
      by rewrite orb_comm.
Qed.

Theorem linking_well_formedness:
  forall p1 p2,
    well_formed_program p1 ->
    well_formed_program p2 ->
    linkable (prog_interface p1) (prog_interface p2) ->
    well_formed_program (program_link p1 p2).
Proof.
  move=> p1 p2 Hwf1 Hwf2 [Hsound Hdis_i]; split=> //.
  - simpl.
    repeat rewrite domm_union.
    by do 2![rewrite wfprog_defined_procedures //].
  - move=> /= C CI H1 P H2.
    rewrite unionmE -mem_domm -(wfprog_defined_procedures Hwf1) !mem_domm.
    rewrite unionmE in H1.
    case Hwhere: (prog_interface p1 C) H1 => [CI'|] //=.
    + move=> [?]; subst CI'.
      destruct (wfprog_exported_procedures_existence Hwf1 Hwhere H2)
        as [Cprocs [Pcode [Hproc Hcode]]].
      rewrite Hproc. simpl.
      exists Cprocs. exists Pcode.
      split; auto.
    + suffices Hno_p1 : prog_procedures p1 C = None.
        move=> H1.
        destruct (wfprog_exported_procedures_existence Hwf2 H1 H2)
          as [Cprocs [Pcode [Hproc Hcode]]].
        exists Cprocs. exists Pcode.
        split; auto.
      now apply/dommPn; rewrite -(wfprog_defined_procedures Hwf1); apply/dommPn.
  - move=> C Cprocs H1 P Pcode H2.
    without loss H: p1 p2 Hwf1 Hwf2 Hsound Hdis_i H1 / prog_procedures p1 C = Some Cprocs.
    { move: H1; rewrite /= unionmE.
      case e: (prog_procedures p1 C)=> [Cprocs'|] //=.
        move=> [<-]; apply=> //.
        by rewrite unionmE e.
      move=> Hp2_C Hgen i Hi; rewrite program_linkC //.
      apply Hgen=> //.
      + by rewrite unionmC // fdisjointC.
      + by rewrite fdisjointC.
      + by rewrite unionmE Hp2_C. }
    move=> i Hi.
    move: (wfprog_well_formed_instructions Hwf1 H H2 Hi).
    case: i Hi=> //=.
    + (* IConst *)
      case=> // ptr r Hi [Hptr [bufs [p1_bufs Hbufs]]].
      split; first assumption.
        by (exists bufs; rewrite unionmE p1_bufs).
    + (* IPtrPfLabel *)
      move=> l reg Hi [Cprocs' [P' [Pcode']]].
      rewrite H=> - [[<-] {Cprocs'}].
      case=> H2' Hl.
      by exists Cprocs, P', Pcode'; rewrite unionmE H.
    + (* IBnz *)
      move=> r l Hi [Cprocs' [Pcode']].
      rewrite H=> - [[<-] {Cprocs'}].
      rewrite H2=> - [[<-] {Pcode'}] Hl.
      by exists Cprocs, Pcode; rewrite unionmE H.
    + (* IJal *)
      move=> l Hi [Cprocs' [P' [Pcode']]].
      rewrite H=> - [[<-] {Cprocs'}].
      case=> H2' Hl.
      by exists Cprocs, P', Pcode'; rewrite unionmE H.
    + (* ICall *)
      move=> C' P' Hi [CC' [CI [p1_C Himport]]]; split=> //.
      exists CI; split=> //.
      by rewrite /Program.has_component unionmE p1_C.
  - rewrite /= !domm_union.
    by do 2![rewrite wfprog_defined_buffers //].
  - intros C bufs b Hbufs Hdomm.
    destruct (C \in domm (prog_interface p1)) eqn:Hcase1;
      destruct (C \in domm (prog_interface p2)) eqn:Hcase2.
    + pose proof (fdisjointP _ _ Hdis_i) C Hcase1 as Hcontra.
      now rewrite Hcase2 in Hcontra.
    + apply wfprog_well_formed_buffers with p1 C; auto.
      rewrite (wfprog_defined_buffers Hwf1) in Hcase1.
      pose proof dommP Hcase1 as [bufs1 Hbufs1].
      rewrite unionmE in Hbufs.
      destruct (prog_buffers p1 C) eqn:Hcase; easy.
    + apply wfprog_well_formed_buffers with p2 C; auto.
      rewrite (wfprog_defined_buffers Hwf2) in Hcase2.
      pose proof dommP Hcase2 as [bufs2 Hbufs2].
      apply negb_true_iff in Hcase1.
      rewrite (wfprog_defined_buffers Hwf1) in Hcase1.
      pose proof dommPn Hcase1 as Hbufs1.
      rewrite unionmE Hbufs1 in Hbufs.
      destruct (prog_buffers p2 C) eqn:Hcase; easy.
    + apply negb_true_iff in Hcase1.
      apply negb_true_iff in Hcase2.
      rewrite (wfprog_defined_buffers Hwf1) in Hcase1.
      rewrite (wfprog_defined_buffers Hwf2) in Hcase2.
      rewrite unionmE in Hbufs.
      rewrite (dommPn Hcase1) (dommPn Hcase2) in Hbufs.
      discriminate.
  - rewrite /=. case /orP => [mainP | mainP].
    + have Hmain1 := @wfprog_main_existence _ Hwf1 mainP.
      case: Hmain1 => [main_procs [p1_main HmainP]] //=.
        by exists main_procs; rewrite unionmE p1_main.
    + have Hmain2 := @wfprog_main_existence _ Hwf2 mainP.
      case: Hmain2 => [main_procs [p2_main HmainP]] //=.
      exists main_procs; rewrite unionmC 1?unionmE 1?p2_main //.
      by rewrite -(wfprog_defined_procedures Hwf1) -(wfprog_defined_procedures Hwf2).
  - (* Coq 8.11.2: *)
    (* Error: Anomaly "make_elim_branch_assumptions." Please report at http://coq.inria.fr/bugs/. *)
    inversion Hwf1 as [_ _ _ _ _ _ DUMMY Hmain_comp1]; clear DUMMY.
    inversion Hwf2 as [_ _ _ _ _ _ DUMMY Hmain_comp2]; clear DUMMY.
    split;
      intros Hprog_main1.
    + assert (Hprog_main2 := Hprog_main1).
      simpl in *.
      destruct (Component.main \in domm (prog_interface p1)) eqn:Hcase1;
        destruct (Component.main \in domm (prog_interface p2)) eqn:Hcase2.
      * (* Contra/easy. *)
        pose proof (proj1 Hmain_comp1 Hcase1) as Hmain1. now rewrite Hmain1.
      * apply proj1 in Hmain_comp1.
        specialize (Hmain_comp1 Hcase1). rewrite Hmain_comp1. by [].
      * destruct (prog_main p1) as [main1 |] eqn:Hmain1.
        -- reflexivity.
        -- apply proj1 in Hmain_comp2.
           specialize (Hmain_comp2 Hcase2). assumption.
      * (* Contra. *)
        destruct (@dommP _ _ _ _ Hprog_main1) as [CI HCI]. rewrite unionmE in HCI.
        apply negb_true_iff in Hcase1. apply negb_true_iff in Hcase2.
        now rewrite (@dommPn _ _ _ _ Hcase1) (@dommPn _ _ _ _ Hcase2) in HCI.
    + inversion Hprog_main1 as [Hmain].
      destruct (prog_main p1) as [main1 |] eqn:Hcase1;
        destruct (prog_main p2) as [main2 |] eqn:Hcase2.
      * (* Contra/easy. RB: NOTE: Three cases can be solved as instances of a
           little lemma, or a tactic. Is it useful elsewhere? *)
        apply proj2 in Hmain_comp1. specialize (Hmain_comp1 isT).
        destruct (@dommP _ _ _ _ Hmain_comp1) as [CI HCI].
        apply /dommP. exists CI. now rewrite unionmE HCI.
      * apply proj2 in Hmain_comp1. specialize (Hmain_comp1 isT).
        destruct (@dommP _ _ _ _ Hmain_comp1) as [CI HCI].
        apply /dommP. exists CI. now rewrite unionmE HCI.
      * apply proj2 in Hmain_comp2. specialize (Hmain_comp2 isT).
        destruct (@dommP _ _ _ _ Hmain_comp2) as [CI HCI].
        apply /dommP. exists CI. simpl. now rewrite (unionmC Hdis_i) unionmE HCI.
      * discriminate.
Qed.

(* Given a list of components, create the map that associates to
   each component the preallocated buffers according to program p.
   If no buffers are found, use the empty map as a default (this
   will not happen in regular use!). *)
Definition alloc_static_buffers p comps :=
  mkfmapf (fun C =>
    ComponentMemory.prealloc (odflt emptym (prog_buffers p C))) comps.

Definition prepare_initial_memory (p: program) : Memory.t :=
  alloc_static_buffers p (domm (prog_interface p)).

(* RB: Are the names of reserve_[component|procedure]_blocks swapped? *)
(* For each pair of procedure id and code in procs_code, build the triad of
   component memory, procedure code map and component entry point map by
   folding over them:
    - Reserve a new block id in the component memory.
    - Map that block id to the procedure code in the procedure block map.
    - If the procedure is public, map the procedure id to the memory block id
      in the component entry point map.
   From the calling point, observe on the one hand that the initial values of
   the accumulators are the existing component memory and two empty maps. On the
   other hand, observe also that procs_code are the contents of a map in
   associative list form, and each procedure is is therefore unique. *)
Definition reserve_component_blocks' p C acc procs_code
  : ComponentMemory.t * NMap code * NMap Block.id :=
  let is_main_proc comp_id proc_id :=
      match prog_main p with
      | true =>
        (Component.main =? comp_id) && (Procedure.main =? proc_id)
      | false => false
      end in
  let aux acc procs_code :=
      let '(Cmem, Cprocs, Centrypoints) := acc in
      let '(P, Pcode) := procs_code in
    let (Cmem', b) := ComponentMemory.reserve_block Cmem in
    let Cprocs' := setm Cprocs b Pcode in
    (* if P is exported or is the main procedure, add an external entrypoint *)
    match getm (prog_interface p) C with
    | Some Ciface =>
      if (P \in Component.export Ciface) || is_main_proc C P then
        let Centrypoints' := setm Centrypoints P b in
        (Cmem', Cprocs', Centrypoints')
      else
        (Cmem', Cprocs', Centrypoints)
    | None =>
      (* this case shouldn't happen for well formed p *)
      (Cmem', Cprocs', Centrypoints)
    end
  in fold_left aux procs_code acc.

(* The simplified version substitutes the accumulator for the component memory.
   It reserves as many new memory blocks as needed at once (one for each item in
   procs_code) and in the process obtains the new component memory, exploiting
   the independence of the operations on each item in procs_code in what follows.
    - Zip the list of new blocks matching the list of procedure code and create a
      new piecewise map from it.
    - Zip the list of procedure ids and the list of new block ids and create a
      partial map from it, refactoring the code handling entry points in the old
      function.
   If the new function to reserve a number of blocks does not present new blocks
   in the same order as the sequential run, slightly different, but isomorphic,
   maps may be produced. *)
Definition reserve_component_blocks p C Cmem procs_code
  : ComponentMemory.t * NMap code * NMap Block.id :=
  let is_main_proc comp_id proc_id :=
      match prog_main p with
      | true =>
        (Component.main =? comp_id) && (Procedure.main =? proc_id)
      | false => false
      end in
  (* if P is exported or is the main procedure, add an external entrypoint *)
  let map_entrypoint '(P, b) :=
      match getm (prog_interface p) C with
      | Some Ciface =>
        if (P \in Component.export Ciface) || is_main_proc C P then Some (P, b)
        else None
      | None => None (* this case shouldn't happen for well formed p *)
      end in
  let (Cmem', bs) := ComponentMemoryExtra.reserve_blocks Cmem (length procs_code) in
  let (procs, code) := (unzip1 procs_code, unzip2 procs_code) in
  let Cprocs := mkfmap (zip bs code) in
  let Centrypoints := mkfmap (pmap map_entrypoint (zip procs bs)) in
  (Cmem', Cprocs, Centrypoints).

Section Zip.
  Lemma in_zip1 {X Y : eqType} (x : X) (y : Y) xs ys :
    (x, y) \in zip xs ys ->
    x \in xs.
  Admitted.

  Lemma in_zip2 {X Y : eqType} (x : X) (y : Y) xs ys :
    (x, y) \in zip xs ys ->
    y \in ys.
  Admitted.

  (* Lemma in_unzip2 {X Y : eqType} (x : X) (y : Y) xs ys : *)
  (*   (x, y) \in zip xs ys -> *)
  (*   y \in ys. *)
  (* Admitted. *)

  Lemma in_unzip2 {X : eqType} x (xs : NMap X) :
    x \in unzip2 xs ->
  exists n,
    (* (n, x) \in xs. *)
    xs n = Some x.
  Admitted.

  (* Lemma in_unzip2 {X Y : eqType} y (xys : seq (X * Y)) : *)
  (*   y \in unzip2 xys -> *)
  (* exists x, *)
  (*   (x, y) \in xys. *)
End Zip.

Lemma reserve_component_blocks_some p C mem (Cprocs : NMap code) b Pcode :
  (reserve_component_blocks p C mem Cprocs).1.2 b = Some Pcode ->
exists (b' : nat_ordType),
  Cprocs b' = Some Pcode.
Proof.
  unfold reserve_component_blocks.
  destruct (ComponentMemoryExtra.reserve_blocks mem (length Cprocs))
    as [Cmem bs] eqn:HCmem.
  simpl.
  intro HPcode.
  apply mkfmap_Some in HPcode.
  assert (HPcode' := in_zip2 HPcode).
  apply in_unzip2 in HPcode'.
  now eauto.
Qed.

(* In the foreseen, controlled use of this function, we always go on the Some
   branch. For each component C, we read its (initial) memory and use it to
   construct the initial state of C, recursing after we update its maps. Given
   identical inputs (component memories, which we have by compositionality of
   that piece of code) the outputs will be identical. *)
(* For each pair of component id and component procedures in comps_code, build
   the triad of program memory memory, component code map and entry point map by
   folding over them. For each pair, reserve component blocks and update the maps
   for the current component.
     As in the function to reserve component blocks, from the calling point,
   observe that the initial values of the accumulators are, again, the existing
   memory, partially initialized, and two empty maps; and that, again, comps_proc
   is an alternative representation of a map, and the procedure on each pair is
   independent from all others. *)
Fixpoint reserve_procedure_blocks' p acc comps_code
  : Memory.t * NMap (NMap code) * EntryPoint.t :=
  let aux acc comps_code :=
      let '(mem, procs, entrypoints) := acc in
      let '(C, Cprocs) := comps_code in
    match getm mem C with
    | Some Cmem =>
      let '(Cmem', Cprocs, Centrypoints) :=
          reserve_component_blocks' p C (Cmem, emptym, emptym) (elementsm Cprocs) in
      let mem' := setm mem C Cmem' in
      let procs' := setm procs C Cprocs in
      let entrypoints' := setm entrypoints C Centrypoints in
      (mem', procs', entrypoints')
    | None =>
      (* this shouldn't happen if memory was initialized before the call *)
      (* we just skip initialization for this component *)
      (mem, procs, entrypoints)
    end
  in fold_left aux comps_code acc.

(* The simplified function builds a partial map by applying the refactored
   per-component process over each pair, noting that in some cases (which should
   never occur!) initialization is skipped, then unpack the parts and repack them
   in the expected map formats.
     Note that we are creating a new memory instead of explicitly updating the
   old memory. Both processes should be equivalent if the map is actually total,
   as is expected. *)
Fixpoint reserve_procedure_blocks p (mem : Memory.t) comps_code
  : Memory.t * NMap (NMap code) * EntryPoint.t :=
  let map_component_memory '(C, Cprocs) :=
    match getm mem C with
    | Some Cmem => Some (C, reserve_component_blocks p C Cmem (elementsm Cprocs))
      (* this shouldn't happen if memory was initialized before the call *)
      (* we just skip initialization for this component *)
    | None => None
    end in
  let acc := pmap map_component_memory comps_code in
  let '(comps', mems, procs, eps) := (unzip1 acc, unzip1 (unzip1 (unzip2 acc)),
                                      unzip2 (unzip1 (unzip2 acc)), unzip2 (unzip2 acc)) in
  (mkfmap (zip comps' mems), mkfmap (zip comps' procs), mkfmap (zip comps' eps)).

(* RB: TODO: Make sure these functions are only used with initial memories. *)
Definition prepare_procedures' (p: program) (mem: Memory.t)
  : Memory.t * NMap (NMap code) * EntryPoint.t :=
  reserve_procedure_blocks' p (mem, emptym, emptym) (elementsm (prog_procedures p)).

(* The main function to prepare the procedures of a program from a memory simply
   calls the helper, now without a trivial accumulator. *)
Definition prepare_procedures (p: program) (mem: Memory.t)
  : Memory.t * NMap (NMap code) * EntryPoint.t :=
  reserve_procedure_blocks p mem (elementsm (prog_procedures p)).

(* For each component, integrate the (now separate) fetching of its procedures,
   obtention of its initial component memory and then reserve_component_blocks.
   The logic of reserve_procedure_blocks is implicit in the map-like nature of
   its results. (By splitting the definition and proving some intermediate
   results on the auxiliary, the composition of the parts will be easier.) *)
(* Definition prepare_procedures_initial_memory_aux (p: program) := *)
(*   mkfmapf *)
(*     (fun C => *)
(*        let Cprocs := odflt emptym ((prog_procedures p) C) in *)
(*        let Cmem := ComponentMemory.prealloc (odflt emptym ((prog_buffers p) C)) in *)
(*        reserve_component_blocks p C (Cmem, emptym, emptym) (elementsm Cprocs)) *)
(*     (domm (prog_interface p)). *)

Definition prepare_procedures_initial_memory_aux' (p: program) :=
  mkfmapf
    (fun C =>
       let Cprocs := odflt emptym ((prog_procedures p) C) in
       let Cmem := ComponentMemory.prealloc (odflt emptym ((prog_buffers p) C)) in
       reserve_component_blocks' p C (Cmem, emptym, emptym) (elementsm Cprocs))
    (domm (prog_interface p)).

(* As above, replace the old function with the new, and remove accumulators. *)
Definition prepare_procedures_initial_memory_aux (p: program) :=
  mkfmapf
    (fun C =>
       let Cprocs := odflt emptym ((prog_procedures p) C) in
       let Cmem := ComponentMemory.prealloc (odflt emptym ((prog_buffers p) C)) in
       reserve_component_blocks p C Cmem (elementsm Cprocs))
    (domm (prog_interface p)).

(* Ultimately, we want this equivalence -- possibly modulo an isomorphism on
   concrete block id values -- to hold. *)
Theorem prepare_procedures_initial_memory_aux_equiv (p: program) :
  prepare_procedures_initial_memory_aux p = (* New version. *)
  prepare_procedures_initial_memory_aux' p. (* Old version. *)
Proof.
Admitted.

(* Decompose the results of the auxiliary call, composed as a whole in the
   result of reserving component blocks, turning a map of triples into a triple
   of identically indexed maps *)
Definition prepare_procedures_initial_memory (p: program)
  : Memory.t * NMap (NMap code) * EntryPoint.t :=
  let m := prepare_procedures_initial_memory_aux p in
  (mapm (fun x => x.1.1) m, mapm (fun x => x.1.2) m, mapm snd m).

(* We want to ensure something like this:
     Goal
       forall p, prepare_procedures_initial_memory p =
                 prepare_procedures p (prepare_initial_memory p).
  Possibly assuming the well-formedness of the program. *)
Theorem prepare_procedures_initial_memory_equiv :
  forall p,
    prepare_procedures_initial_memory p =
    prepare_procedures p (prepare_initial_memory p).
Admitted.

(* initialization of a linked program *)

Definition prepare_procedures_memory (p: program) : Memory.t :=
  let '(mem, _, _) := prepare_procedures_initial_memory p in
  mem.

(* RB: TODO: Relocate these simple helpers, review names, etc.
   For now, trying to keep cruft out of the higher-level proofs. *)
Lemma mapm_eq: forall (T : ordType) (S S' : Type) (m1 m2 : {fmap T -> S}) (f : S -> S'),
  m1 = m2 -> (mapm f m1) = (mapm f m2).
Proof.
  intros T S S' m1 m2 f Heq.
  subst.
  reflexivity.
Qed.

Lemma in_domm_program_link:
  forall Cid p,
    Cid \in domm (prog_interface p) ->
  forall c,
    Cid \in domm (prog_interface (program_link p c)).
Proof.
  intros Cid p Hin c.
  simpl.
  rewrite mem_domm.
  rewrite mem_domm in Hin.
  rewrite unionmE.
  rewrite Hin.
  assumption.
Qed.

Lemma domm_partition_program_link_in_neither p c :
  well_formed_program p ->
  well_formed_program c ->
  closed_program (program_link p c) ->
  Component.main \notin domm (prog_interface p) ->
  Component.main \notin domm (prog_interface c) ->
  False.
Proof.
  intros [_ _ _ _ _ _ _ [_ Hmainp]] [_ _ _ _ _ _ _ [_ Hmainc]]
         [_ [main [Hmain [_ _]]]] Hmainp' Hmainc'.
  destruct (prog_main p) as [|] eqn:Hcasep.
  - specialize (Hmainp is_true_true).
    rewrite Hmainp in Hmainp'.
    discriminate.
  - destruct (prog_main c) as [|] eqn:Hcasec.
    +  specialize (Hmainc is_true_true).
       rewrite Hmainc in Hmainc'.
       discriminate.
    + simpl in Hmain.
      rewrite Hcasep Hcasec in Hmain.
      discriminate.
Qed.

Lemma fsetid (T : ordType) (s: seq.seq T) :
  fset (fset s) = fset s.
Proof. by apply /eq_fset => x; rewrite in_fset. Qed.

(* First, prove domain preservation for all of the (already existing, plus
   recent improvements) initialization code. *)
Lemma domm_prepare_procedures_initial_memory_aux: forall p,
  (*well_formed_program p ->*)
  domm (prepare_procedures_initial_memory_aux p) = domm (prog_interface p).
Proof.
  intros p.
  unfold prepare_procedures_initial_memory_aux.
  rewrite domm_mkfmapf.
  apply fsetid.
Qed.

(* FG : maybe relocate this in extructures? (when rewritten in proper SSReflect) *)
Lemma fdisjoint_partition_notinboth (T: ordType) (s1 s2 : {fset T}) :
  fdisjoint s1 s2 ->
  forall x,
    x \in s2 ->
    x \in s1 ->
    False.
Proof.
  unfold fdisjoint. move => Hinter x Hs2 Hs1.
  have H' : x \in (s1 :&: s2)%fset by rewrite in_fsetI Hs1 Hs2.
  have H'' : (s1 :&: s2)%fset = fset0 by apply /eqP.
  rewrite H'' in H'. inversion H'.
Qed.

(* Better name, maybe ? *)
(* keeping it generic over program/context *)
Lemma prog_link_procedures_unionm :
  forall p1 p2 Cid,
    well_formed_program p1 ->
    (* well_formed_program p2 -> *)
    (Cid \in domm (prog_interface p1)) = true ->
    (Cid \in domm (prog_interface p2)) = false -> (* not used, to remove  or keep as sanity check ? *)
    (prog_procedures (program_link p1 p2)) Cid = (prog_procedures p1) Cid.
Proof.
  intros p1 p2 Cid Hwfp Hp _.
  rewrite unionmE. rewrite <- mem_domm. inversion Hwfp as [? Hproc _ _ _ _ _]. (* if no binding of 1st hypothesis : anomaly : "make_elim_branch_assumptions" *)
  rewrite Hproc in Hp. rewrite Hp. reflexivity.
Qed.

(* maybe write a tactic that does the core except the inversion ... ? *)
(* or suppress the prog_smth part and keep it generic for all types of program_link ? *)
Lemma prog_link_buffers_unionm :
  forall p1 p2 Cid,
    well_formed_program p1 ->
    (* well_formed_program p2 -> *)
    (Cid \in domm (prog_interface p1)) = true ->
    (Cid \in domm (prog_interface p2)) = false -> (* same *)
    (prog_buffers (program_link p1 p2)) Cid = (prog_buffers p1) Cid.
Proof.
  intros p1 p2 Cid Hwfp Hp _. simpl.
  rewrite unionmE. rewrite <- mem_domm. inversion Hwfp as [? _ _ _ Hbuf _ _]. (* if no binding of 1st hypothesis : anomaly : "make_elim_branch_assumptions" *)
  rewrite Hbuf in Hp. rewrite Hp. reflexivity.
Qed.

(* RB: TODO: Simplify hypotheses if possible. *)
Lemma prepare_procedures_initial_memory_aux_after_linking:
  forall p c,
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    prepare_procedures_initial_memory_aux (program_link p c) =
    unionm (prepare_procedures_initial_memory_aux p)
           (prepare_procedures_initial_memory_aux c).
Proof.
  intros p c Hwfp Hwfc Hlinkable.
  pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmains.
  unfold prepare_procedures_initial_memory_aux.
  apply eq_fmap. intros Cid.
  (* Case analysis on component provenance after some common preprocessing. *)
  destruct (Cid \in domm (prog_interface p)) eqn:Hp;
    destruct (Cid \in domm (prog_interface c)) eqn:Hc.
  - (* Contra. *)
    inversion Hlinkable as [_ Hdisjoint].
    have Hcontra : False by apply (fdisjoint_partition_notinboth Hdisjoint Hc Hp).
    inversion Hcontra.
  - rewrite unionmE.
    rewrite !mkfmapfE.
    rewrite Hp Hc.
    have Hpc : Cid \in domm (prog_interface (program_link p c))
      by apply in_domm_program_link.
    rewrite Hpc.
    have Helts : (elementsm (odflt emptym ((prog_procedures (program_link p c)) Cid))) =
            (elementsm (odflt emptym ((prog_procedures p) Cid)))
      by rewrite (prog_link_procedures_unionm Hwfp Hp Hc).
    rewrite Helts.
    have Hprealloc : ComponentMemory.prealloc (odflt emptym ((prog_buffers (program_link p c)) Cid)) =
            ComponentMemory.prealloc (odflt emptym ((prog_buffers p) Cid))
      by rewrite (prog_link_buffers_unionm Hwfp Hp Hc).
    rewrite Hprealloc.
    simpl.
    unfold reserve_component_blocks.
    rewrite unionmE.
    have [Cid_int Hp']: (exists x, (prog_interface p) Cid = Some x)
      by  apply /dommP.
    rewrite Hp'.
    simpl.
    destruct (prog_main p) as [|] eqn:Hmainp;
      destruct (prog_main c) as [|] eqn:Hmainc.
    + easy. (* Contra. *)
    + reflexivity.
    + destruct Cid as [| n].
      * (* Contra. *)
        inversion Hwfp as [_ _ _ _ _ _ _ Hmain_compp].
        (* specialize (Hmain_compp Hmainp). *)
        (* have Hp'' : (prog_interface p) 0 = None by apply /dommPn. *)
        (* rewrite Hp'' in Hp'. *)
        apply proj1 in Hmain_compp.
        specialize (Hmain_compp Hp).
        rewrite Hmainp in Hmain_compp.
        discriminate.
      * reflexivity.
    + reflexivity. (* Easy case. *)
  - (* RB: TODO: Refactor symmetric case to last one. *)
    rewrite unionmE.
    rewrite !mkfmapfE.
    rewrite Hp Hc.
    have Hpc : Cid \in domm (prog_interface (program_link p c))
      by rewrite (program_linkC Hwfp Hwfc Hlinkable) ;
      apply in_domm_program_link.
    rewrite Hpc.
    have Helts: (elementsm (odflt emptym ((prog_procedures (program_link p c)) Cid))) =
            (elementsm (odflt emptym ((prog_procedures c) Cid)))
      by rewrite (program_linkC Hwfp Hwfc Hlinkable) (prog_link_procedures_unionm Hwfc Hc Hp).
    rewrite Helts.
    have Hprealloc : ComponentMemory.prealloc (odflt emptym ((prog_buffers (program_link p c)) Cid)) =
            ComponentMemory.prealloc (odflt emptym ((prog_buffers c) Cid))
      by rewrite (program_linkC Hwfp Hwfc Hlinkable) (prog_link_buffers_unionm Hwfc Hc Hp).
    rewrite Hprealloc.
    simpl.
    unfold reserve_component_blocks.
    rewrite unionmE.
    have Hp': (prog_interface p) Cid = None
      by apply /dommPn; rewrite Hp.
    rewrite Hp'.
    have [Cid_int Hc'] : exists x, (prog_interface c) Cid = Some x
      by apply /dommP.
    rewrite Hc'.
    destruct (prog_main p) as [|] eqn:Hmainp;
      destruct (prog_main c) as [|] eqn:Hmainc.
    + (* Contra. *)
      unfold linkable_mains in Hmains.
      rewrite Hmainp Hmainc in Hmains.
      discriminate.
    + simpl. rewrite Hmainp Hmainc.
      destruct Cid as [| n].
      * (* Contra, *)
        inversion Hwfc as [_ _ _ _ _ _ _ Hmain_compc].
        (* specialize (Hmain_compc Hmainc). *)
        (* have Hc'' : (prog_interface c) 0 = None by apply /dommPn. *)
        (* rewrite Hc'' in Hc'. *)
        apply proj1 in Hmain_compc.
        specialize (Hmain_compc Hc).
        rewrite Hmainc in Hmain_compc.
        discriminate.
      * reflexivity.
    + simpl. rewrite Hmainp Hmainc. reflexivity.
    + simpl. rewrite Hmainp Hmainc. reflexivity.
  - (* in neither, pretty immediate *)
    by rewrite unionmE !mkfmapfE domm_union in_fsetU Hp Hc.
Qed.

(* Now it's easy to extend this to the parts of the final result. *)
Lemma domm_prepare_procedures_memory: forall p,
  domm (prepare_procedures_memory p) = domm (prog_interface p).
Proof.
  intros p.
  unfold prepare_procedures_memory, prepare_procedures_initial_memory.
  rewrite domm_map.
  rewrite domm_prepare_procedures_initial_memory_aux.
  reflexivity.
Qed.

Theorem prepare_procedures_memory_after_linking:
  forall p c,
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    prepare_procedures_memory (program_link p c) =
    unionm (prepare_procedures_memory p) (prepare_procedures_memory c).
Proof.
  intros p c Hwfp Hwfc Hlinkable.
  unfold prepare_procedures_memory,
         prepare_procedures_initial_memory, prepare_procedures_initial_memory_aux.
  rewrite <- mapm_unionm. apply mapm_eq.
  apply prepare_procedures_initial_memory_aux_after_linking; assumption.
Qed.

(* Search _ prepare_procedures_memory. *)
(* Search _ PS.to_partial_memory unionm. *)
Lemma prepare_procedures_memory_left p c :
  linkable (prog_interface p) (prog_interface c) ->
  to_partial_memory
    (unionm (prepare_procedures_memory p) (prepare_procedures_memory c))
    (domm (prog_interface c)) =
  prepare_procedures_memory p.
Proof.
  intros [_ Hdisjoint].
  unfold to_partial_memory, merge_memories.
  rewrite <- domm_prepare_procedures_memory,
         -> filterm_union,
         -> fdisjoint_filterm_full,
         -> fdisjoint_filterm_empty, -> unionm0;
    first reflexivity;
    try rewrite -> !domm_prepare_procedures_memory; congruence.
Qed.

Lemma prepare_procedures_memory_right p c :
  linkable (prog_interface p) (prog_interface c) ->
  to_partial_memory
    (unionm (prepare_procedures_memory p) (prepare_procedures_memory c))
    (domm (prog_interface p)) =
  prepare_procedures_memory c.
Proof.
  intros Hlinkable.
  rewrite unionmC; try assumption.
  apply prepare_procedures_memory_left with (c := p) (p := c).
  now apply linkable_sym.
  inversion Hlinkable.
  now rewrite !domm_prepare_procedures_memory.
Qed.

Definition prepare_procedures_procs (p: program) : NMap (NMap code) :=
  let '(_, procs, _) := prepare_procedures_initial_memory p in
  procs.

Theorem prepare_procedures_procs_after_linking:
  forall p c,
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    prepare_procedures_procs (program_link p c) =
    unionm (prepare_procedures_procs p) (prepare_procedures_procs c).
Proof.
  intros p c Hwfp Hwfc Hlinkable.
  unfold prepare_procedures_procs,
         prepare_procedures_initial_memory, prepare_procedures_initial_memory_aux.
  rewrite <- mapm_unionm. apply mapm_eq.
  apply prepare_procedures_initial_memory_aux_after_linking; assumption.
Qed.

Theorem prepare_procedures_procs_prog_procedures :
  forall p C Cprocs b Pcode,
    well_formed_program p ->
    prepare_procedures_procs p C = Some Cprocs ->
    Cprocs b = Some Pcode ->
  exists Cprocs' b',
    prog_procedures p C = Some Cprocs' /\
    Cprocs' b' = Some Pcode.
Proof.
  unfold prepare_procedures_procs,
        prepare_procedures_initial_memory,
        prepare_procedures_initial_memory_aux.
  setoid_rewrite mapmE.
  unfold omap, obind, oapp.
  setoid_rewrite mkfmapfE.
  intros p C Cprocs b Pcode Hwf Hprocs Hcode.
  destruct (C \in domm (prog_interface p)) eqn:Hdomm;
    rewrite Hdomm in Hprocs;
    [| discriminate].
  injection Hprocs as Hprocs; subst Cprocs.
  destruct (prog_procedures p C) as [Cprocs |] eqn:Hprocs;
    [| rewrite (wfprog_defined_procedures Hwf) in Hdomm;
       destruct (dommP Hdomm) as [procs Hcontra];
       discriminate].
  unfold elementsm in Hcode. simpl in Hcode.
  rewrite (wfprog_defined_buffers Hwf) in Hdomm.
  destruct (dommP Hdomm) as [Cbufs HCbufs].
  rewrite HCbufs in Hcode. simpl in Hcode.
  destruct (reserve_component_blocks_some Hcode) as [b' HPcode].
  now exists Cprocs, b'.
Qed.

Definition prepare_procedures_entrypoints (p: program) : EntryPoint.t :=
  let '(_, _, entrypoints) := prepare_procedures_initial_memory p in
  entrypoints.

Lemma domm_prepare_procedures_entrypoints: forall p,
  domm (prepare_procedures_entrypoints p) = domm (prog_interface p).
Proof.
  intros p.
  unfold prepare_procedures_entrypoints, prepare_procedures_initial_memory.
  rewrite domm_map.
  rewrite domm_prepare_procedures_initial_memory_aux.
  reflexivity.
Qed.

Theorem prepare_procedures_entrypoints_after_linking:
  forall p c,
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    prepare_procedures_entrypoints (program_link p c) =
    unionm (prepare_procedures_entrypoints p)
           (prepare_procedures_entrypoints c).
Proof.
  intros p c Hwfp Hwfc Hlinkable.
  unfold prepare_procedures_entrypoints,
         prepare_procedures_initial_memory, prepare_procedures_initial_memory_aux.
  rewrite <- mapm_unionm. apply mapm_eq.
  apply prepare_procedures_initial_memory_aux_after_linking; assumption.
Qed.

Corollary prepare_procedures_initial_memory_after_linking:
  forall p c,
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    prepare_procedures_initial_memory (program_link p c) =
    (unionm (prepare_procedures_memory p)
            (prepare_procedures_memory c),
     unionm (prepare_procedures_procs p)
            (prepare_procedures_procs c),
     unionm (prepare_procedures_entrypoints p)
            (prepare_procedures_entrypoints c)).
Proof.
  intros p c Hwfp Hwfc Hlinkable.
  rewrite <- prepare_procedures_memory_after_linking; try assumption.
  rewrite <- prepare_procedures_procs_after_linking; try assumption.
  rewrite <- prepare_procedures_entrypoints_after_linking; try assumption.
  reflexivity.
Qed.

(* We can prove a stronger theorem stating the correspondence of static buffer
   identifiers in the program and the environment. *)
(* Use ComponentMemoryExtra.reserve_blocks_prealloc *)
Theorem prepare_procedures_memory_prog_buffers :
  forall p ptr v,
    well_formed_program p ->
    Memory.load (prepare_procedures_memory p) ptr = Some v ->
  exists Cbufs buf,
    (prog_buffers p (Pointer.component ptr)) = Some Cbufs /\
    Cbufs (Pointer.block ptr) = Some buf /\
    Buffer.nth_error buf (Pointer.offset ptr) = Some v.
Admitted.

(* Alternative statements? *)
Theorem prog_buffer_ptr :
  forall p C bufs b buf o ptr,
    well_formed_program p ->
    prog_buffers p C = Some bufs ->
    bufs b = Some buf ->
    Buffer.nth_error buf o = Some (Ptr ptr) ->
    False.
Proof.
  intros p C bufs b buf o ptr Hwf Hbufs Hbuf Hptr.
  assert (Hdomm : b \in domm bufs) by (apply /dommP; now eauto).
  pose proof wfprog_well_formed_buffers Hwf Hbufs Hdomm as Hwfb.
  unfold Buffer.well_formed_buffer_opt in Hwfb.
  rewrite Hbuf in Hwfb.
  destruct buf as [n | vs].
  - destruct o as [| o | o]; simpl in Hptr.
    + admit. (* easy *)
    + admit. (* easy *)
    + discriminate.
  - destruct o as [| o | o]; simpl in Hptr.
    + destruct vs as [| v vs];
        [discriminate |].
      injection Hptr as Hptr; subst v.
      move: Hwfb => /andP => [[Hsize Hptrs]].
      discriminate.
    + move: Hwfb => /andP => [[Hsize Hptrs]].
      admit. (* contra, similar as above *)
    + discriminate.
Admitted.
(* RB: Slight "misnomer" because of the presence of matching_mains.
   Closely connected to linkable, but not exactly the same at this
   level. Is there a benefit to combining these two in a definition? *)
Lemma interface_preserves_closedness_r :
  forall p1 p2 p2',
    well_formed_program p1 ->
    well_formed_program p2' ->
    prog_interface p2 = prog_interface p2' ->
    linkable (prog_interface p1) (prog_interface p2) ->
    closed_program (program_link p1 p2) ->
    linkable_mains p1 p2 ->
    matching_mains p2 p2' ->
    closed_program (program_link p1 p2').
Proof.
  intros p1 p2 p2'
         Hwf1 Hwf2' Hsame_int Hlinkable
         [Hclosed [mainP [Hmain [Hprocs]]]]
         Hlinkable_mains Hmatching_mains.
  constructor.
  - simpl in Hclosed.
    rewrite Hsame_int in Hclosed.
    apply Hclosed.
  - destruct (prog_main p1) as [|] eqn:Hmain1;
      destruct (prog_main p2) as [|] eqn:Hmain2.
    + unfold linkable_mains in Hlinkable_mains.
      rewrite Hmain1 Hmain2 in Hlinkable_mains.
      discriminate.
    + (* main is in p1.*)
      (* unfold program_link in Hmain. *)
      (* rewrite Hmain1 in Hmain. *)
      (* simpl in Hmain. *)
      (* inversion Hmain; subst mainP; clear Hmain. *)
      (* Likewise main_procs (used only in second sub-goal). *)
      unfold program_link in Hprocs; simpl in Hprocs.
      destruct (wfprog_main_existence Hwf1 Hmain1)
        as [main_procs1 [Hmain_procs1 Hin1]].
      rewrite unionmE Hmain_procs1 in Hprocs.
      (* inversion Hprocs; subst main_procs; clear Hprocs. *)
      (* Instantiate and solve. *)
      exists main_procs1. split; [| split].
      * unfold program_link.
        rewrite Hmain1.
        reflexivity.
      * unfold program_link; simpl.
        rewrite unionmE Hmain_procs1.
        reflexivity.
      * assumption.
    + (* main is in p2'. *)
      destruct (prog_main p2') as [|] eqn:Hmain2';
      last (destruct Hmatching_mains as [Hmatching_mains _];
            rewrite Hmatching_mains in Hmain2';
            last assumption;
            inversion Hmain2').
      (* Likewise main_procs (used only in second sub-goal). *)
      destruct (wfprog_main_existence Hwf2' Hmain2')
        as [main_procs2' [Hmain_procs2' Hin2']].
      exists main_procs2'. split; [| split].
      * unfold program_link.
        rewrite Hmain1 Hmain2'.
        reflexivity.
      * unfold program_link; simpl.
        inversion Hlinkable as [_ Hdisjoint].
        inversion Hwf1 as [_ Hdomm1 _ _ _ _].
        inversion Hwf2' as [_ Hdomm2' _ _ _ _].
        rewrite Hsame_int Hdomm1 Hdomm2' in Hdisjoint.
        rewrite (unionmC Hdisjoint) unionmE Hmain_procs2'.
        reflexivity.
      * assumption.
    + simpl in Hmain.
      rewrite Hmain1 in Hmain.
      rewrite Hmain2 in Hmain.
      discriminate.
Qed.

(* RB: TODO: Revisit uses of matching_mains as hypotheses and see when they can
   be removed due to their being derivable from this result. *)
Lemma interface_implies_matching_mains :
  forall p1 p2,
    well_formed_program p1 ->
    well_formed_program p2 ->
    prog_interface p1 = prog_interface p2 ->
    matching_mains p1 p2.
Proof.
  intros p1 p2 Hwf1 Hwf2 Hiface.
  unfold matching_mains.
  destruct (prog_main p1) as [|] eqn:Hcase1;
    destruct (prog_main p2) as [|] eqn:Hcase2.
  - easy.
  - split; last easy.
    exfalso.
    inversion Hwf2 as [_ _ _ _ _ _ _ [Hmain2' _]].
    inversion Hwf1 as [_ _ _ _ _ _ _ [_ Hmain1']].
    rewrite Hcase1 in Hmain1'. specialize (Hmain1' is_true_true).
    rewrite -> Hcase2, <- Hiface in Hmain2'. apply Hmain2' in  Hmain1'.
    discriminate.
  - split; first easy.
    exfalso.
    inversion Hwf1 as [_ _ _ _ _ _ _ [Hmain1' _]].
    inversion Hwf2 as [_ _ _ _ _ _ _ [_ Hmain2']].
    rewrite Hcase2 in Hmain2'. specialize (Hmain2' is_true_true).
    rewrite -> Hcase1, -> Hiface in Hmain1'. apply Hmain1' in  Hmain2'.
    discriminate.
  - easy.
Qed.

Lemma closed_interface_union : forall p1 p2,
  closed_interface (prog_interface (program_link p1 p2)) =
  closed_interface (unionm (prog_interface p1) (prog_interface p2)).
Proof.
  easy.
Qed.

Lemma compose_mergeable_interfaces : forall p1 p2,
  linkable (prog_interface p1) (prog_interface p2) ->
  closed_program (program_link p1 p2) ->
  mergeable_interfaces (prog_interface p1) (prog_interface p2).
Proof.
  intros p1 p2 Hlinkable Hclosed.
  split.
  - assumption.
  - inversion Hclosed as [Hclosed_iface _].
    rewrite closed_interface_union in Hclosed_iface.
    assumption.
Qed.

End Intermediate.
