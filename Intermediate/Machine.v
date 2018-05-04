Require Import Common.Definitions.
Require Import Common.Util.
Require Export Common.Values.
Require Export Common.Linking.
Require Import Common.Memory.
Require Import Lib.Monads.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From CoqUtils Require Import fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Inductive register : Type :=
  R_ONE | R_COM | R_AUX1 | R_AUX2 | R_RA | R_SP.

Definition label := nat.

Inductive imvalue : Type :=
| IInt : Z -> imvalue
| IPtr : Pointer.t -> imvalue.

Definition imm_to_val (im : imvalue) : value :=
  match im with
  | IInt n => Int n
  | IPtr p => Ptr p
  end.

Inductive instr :=
| INop : instr
| ILabel : label -> instr
(* register operations *)
| IConst : imvalue -> register -> instr
| IMov : register -> register -> instr
| IBinOp : binop -> register -> register -> register -> instr
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

Definition code := list instr.

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
    end.

  Definition init :=
    mkfmap [(to_nat R_ONE, Undef);
            (to_nat R_COM, Undef);
            (to_nat R_AUX1, Undef);
            (to_nat R_AUX2, Undef);
            (to_nat R_RA, Undef);
            (to_nat R_SP, Undef)].

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
            (to_nat R_SP, Undef)].

  Lemma init_registers_wf:
    forall r, exists val, get r init = val.
  Proof.
    intros r. unfold get.
    exists Undef. destruct r; auto.
  Qed.
End Register.

Module EntryPoint.
  Definition t := NMap (NMap Block.id).

  Definition get (C: Component.id) (P: Procedure.id) (E: t) : option Block.id :=
    match getm E C with
    | Some addrs => getm addrs P
    | None => None
    end.
End EntryPoint.

(* programs *)

Record program := mkProg {
  prog_interface: Program.interface;
  prog_procedures: NMap (NMap code);
  prog_buffers: NMap {fmap Block.id -> nat + list value};
  prog_main: option Procedure.id
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
  | IJal l =>
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
    (* static pointers refers to static buffers *)
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

Record well_formed_program (p: program) := {
  (* the interface is sound (but maybe not closed) *)
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
  (* if the main component exists, then the main procedure must exist as well *)
  wfprog_main_existence:
    forall mainP,
      prog_main p = Some mainP ->
    exists main_procs,
      getm (prog_procedures p) Component.main = Some main_procs /\ mainP \in domm main_procs
}.

(* a closed program is a program with a closed interface and an existing main
   procedure *)
Record closed_program (p: program) := {
  (* the interface must be closed (and consequently sound) *)
  cprog_closed_interface:
    closed_interface (prog_interface p);
  (* the main procedure must exist *)
  cprog_main_existence:
    exists mainP main_procs,
      prog_main p = Some mainP /\
      getm (prog_procedures p) Component.main = Some main_procs /\ mainP \in domm main_procs
}.

Theorem linkability_disjoint_procedures :
  forall prog1 prog2,
    well_formed_program prog1 ->
    well_formed_program prog2 ->
    linkable (prog_interface prog1) (prog_interface prog2) ->
    fdisjoint (domm (prog_procedures prog1)) (domm (prog_procedures prog2)).
Proof.
  intros prog1 prog2 Hwell_formed1 Hwell_formed2
    [_ Hdisjoint_interface].
  inversion Hwell_formed1 as [_ Hwell_formed_procs1 _ _ _ _].
  inversion Hwell_formed2 as [_ Hwell_formed_procs2 _ _ _ _].
  by rewrite -Hwell_formed_procs1 -Hwell_formed_procs2.
Qed.

Theorem linkability_disjoint_buffers :
  forall prog1 prog2,
    well_formed_program prog1 ->
    well_formed_program prog2 ->
    linkable (prog_interface prog1) (prog_interface prog2) ->
    fdisjoint (domm (prog_buffers prog1)) (domm (prog_buffers prog2)).
Proof.
  intros prog1 prog2 Hwell_formed1 Hwell_formed2 [_ Hdisjoint_interface].
  inversion Hwell_formed1 as [_ _ _ _ Hwell_formed_buffers1 _].
  inversion Hwell_formed2 as [_ _ _ _ Hwell_formed_buffers2 _].
  by rewrite -Hwell_formed_buffers1 -Hwell_formed_buffers2.
Qed.

(*
Theorem linkability_disjoint_mains :
  forall prog1 prog2,
    well_formed_program prog1 ->
    well_formed_program prog2 ->
    linkable (prog_interface prog1) (prog_interface prog2) ->
    linkable_mains (prog_main prog1) (prog_main prog2).
Proof.
  intros prog1 prog2 Hwell_formed1 Hwell_formed2 [Hsound_interface Hdisjoint_interface].
  inversion Hwell_formed1 as [_ _ _ _ _ Hmain_existence1].
  inversion Hwell_formed2 as [_ _ _ _ _ Hmain_existence2].
  (* All cases except one, which leads to contradiction, are trivial. *)
  unfold linkable_mains.
  destruct (prog_main prog1) as [(cid1, pid1) |];
    destruct (prog_main prog2) as [(cid2, pid2) |];
    try (apply I; fail).
  (* The interesting case remains. *)
  specialize (Hmain_existence1 cid1 pid1).
  specialize (Hmain_existence2 cid2 pid2).
  (* RB: Short story, there is a main in prog_procedures for each prog1 and
     prog2, which are however disjoint, and main is unique (may need to
     shuffle things a bit). *)
  admit.
Admitted.
*)

Definition linkable_mains (prog1 prog2 : program) : Prop :=
  ~~ (prog_main prog1 && prog_main prog2).

Lemma linkable_mains_sym : forall (prog1 prog2 : program),
  linkable_mains prog1 prog2 <-> linkable_mains prog2 prog1.
Proof.
  intros prog1 prog2.
  unfold linkable_mains, andb, negb.
  destruct (isSome (prog_main prog1));
    destruct (isSome (prog_main prog2));
    intuition.
Qed.

Definition program_link (p1 p2: program): program :=
  {| prog_interface := unionm (prog_interface p1) (prog_interface p2);
     prog_procedures := unionm (prog_procedures p1) (prog_procedures p2);
     prog_buffers := unionm (prog_buffers p1) (prog_buffers p2);
     prog_main := if prog_main p1 then prog_main p1 else prog_main p2 |}.

Definition partialize_program (p: program) (ctx: Program.interface) : program :=
  {| prog_interface :=
       filterm (fun k _ => negb (k \in domm ctx)) (prog_interface p);
     prog_procedures :=
       filterm (fun k _ => negb (k \in domm ctx)) (prog_procedures p);
     prog_buffers :=
       filterm (fun k _ => negb (k \in domm ctx)) (prog_buffers p);
     prog_main := prog_main p |}.

Definition empty_prog := {| prog_interface := emptym;
                            prog_procedures := emptym;
                            prog_buffers := emptym;
                            prog_main := None |}.

Theorem empty_interface_implies_empty_program:
  forall p,
    well_formed_program p ->
    prog_interface p = emptym ->
    p = empty_prog.
Proof.
  move=> [intf procs bufs main] [/= _ e_procs _ _ e_bufs Hmain] e_intf.
  subst intf; congr mkProg.
  - apply/eq_fmap=> ?; rewrite emptymE; apply/dommPn.
    by rewrite -e_procs mem_domm emptymE.
  - apply/eq_fmap=> ?; rewrite emptymE; apply/dommPn.
    by rewrite -e_bufs mem_domm emptymE.
  - case e: main Hmain=> [mainP|] //= /(_ _ erefl) [main_procs].
    by move/eqP: e_procs; rewrite domm0 eq_sym => /emptymP -> [].
Qed.

Lemma empty_prog_is_well_formed:
  well_formed_program empty_prog.
Proof. by constructor. Qed.

Theorem linking_empty_program:
  forall p,
    program_link p empty_prog = p.
Proof.
  intros p.
  destruct p. unfold program_link. simpl.
  repeat rewrite unionm0.
  by case: prog_main0.
Qed.

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
  have {Hwf1} /implyP Hm1 : m1 -> Component.main \in domm p1.
    move/wfprog_main_existence: Hwf1 => /=.
    case: m1 => [mainP|] //= /(_ mainP erefl) [main_procs [e _]].
    by rewrite mem_domm e.
  have {Hwf2} /implyP Hm2 : m2 -> Component.main \in domm p2.
    move/wfprog_main_existence: Hwf2 => /=.
    case: m2 => [mainP|] //= /(_ mainP erefl) [main_procs [e _]].
    by rewrite mem_domm e.
  case: m1 Hm1=> [mainP|] //=; last by case: m2 Hm2.
  move=> in_p1.
  move: Hm2; rewrite -implybNN.
  move/fdisjointP/(_ Component.main in_p1): Hdis_p => -> /=.
  by case: m2.
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
      case=> // ptr r Hi [bufs [p1_bufs Hbufs]].
      by exists bufs; rewrite unionmE p1_bufs.
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
  - move=> mainP /=.
    have Hmain1 := @wfprog_main_existence _ Hwf1 mainP.
    have Hmain2 := @wfprog_main_existence _ Hwf2 mainP.
    case Hmain_p1: (prog_main p1) Hmain1=> [mainP'|] //=.
      move=> H1; case/H1=> [main_procs [p1_main HmainP]].
      by exists main_procs; rewrite unionmE p1_main.
    move=> _ /Hmain2 [main_procs [p2_main HmainP]].
    exists main_procs; rewrite unionmC 1?unionmE 1?p2_main //.
    by rewrite -(wfprog_defined_procedures Hwf1) -(wfprog_defined_procedures Hwf2).
Qed.

Definition alloc_static_buffers p comps :=
  mkfmapf (fun C =>
    ComponentMemory.prealloc (odflt emptym (prog_buffers p C))) comps.

Definition prepare_initial_memory (p: program) : Memory.t :=
  alloc_static_buffers p (domm (prog_interface p)).

Fixpoint reserve_component_blocks p C Cmem Cprocs Centrypoints procs_code
  : ComponentMemory.t * NMap code * NMap Block.id :=
  let is_main_proc comp_id proc_id :=
      match prog_main p with
      | Some main_proc_id =>
        (Component.main =? comp_id) && (main_proc_id =? proc_id)
      | None => false
      end in
  match procs_code with
  | [] => (Cmem, Cprocs, Centrypoints)
  | (P, Pcode) :: procs_code' =>
    let (Cmem', b) := ComponentMemory.reserve_block Cmem in
    let Cprocs' := setm Cprocs b Pcode in
    (* if P is exported or is the main procedure, add an external entrypoint *)
    match getm (prog_interface p) C with
    | Some Ciface =>
      if (P \in Component.export Ciface) || is_main_proc C P then
        let Centrypoints' := setm Centrypoints P b in
        reserve_component_blocks p C Cmem' Cprocs' Centrypoints' procs_code'
      else
        reserve_component_blocks p C Cmem' Cprocs' Centrypoints procs_code'
    | None =>
      (* this case shouldn't happen for well formed p *)
      reserve_component_blocks p C Cmem' Cprocs' Centrypoints procs_code'
    end
  end.

Fixpoint reserve_procedure_blocks p mem procs entrypoints comps_code
  : Memory.t * NMap (NMap code) * EntryPoint.t :=
  match comps_code with
  | [] => (mem, procs, entrypoints)
  | (C, Cprocs) :: comps_code' =>
    match getm mem C with
    | Some Cmem =>
      let '(Cmem', Cprocs, Centrypoints) :=
          reserve_component_blocks p C Cmem emptym emptym (elementsm Cprocs) in
      let mem' := setm mem C Cmem' in
      let procs' := setm procs C Cprocs in
      let entrypoints' := setm entrypoints C Centrypoints in
      reserve_procedure_blocks p mem' procs' entrypoints' comps_code'
    | None =>
      (* this shouldn't happen if memory was initialized before the call *)
      (* we just skip initialization for this component *)
      reserve_procedure_blocks p mem procs entrypoints comps_code'
    end
  end.

Definition prepare_procedures (p: program) (mem: Memory.t)
  : Memory.t * NMap (NMap code) * EntryPoint.t :=
  reserve_procedure_blocks p mem emptym emptym (elementsm (prog_procedures p)).

(* initialization of the empty program *)

Theorem prepare_initial_memory_empty_program:
  prepare_initial_memory empty_prog = emptym.
Proof.
  unfold prepare_initial_memory.
  simpl. rewrite domm0.
  reflexivity.
Qed.

Theorem prepare_procedures_empty_program:
  prepare_procedures empty_prog emptym = (emptym, emptym, emptym).
Proof.
  unfold prepare_procedures.
  reflexivity.
Qed.

(* initialization of a linked program *)

(* Lemma placeholder: alloc_static_buffers_after_linking *)
(* Lemma placeholder: prepare_initial_memory_after_linking *)

Definition prepare_procedures_memory (p: program) (mem: Memory.t) : Memory.t :=
  let '(mem, _, _) := prepare_procedures p mem in
  mem.

(* Lemma placeholder: prepare_procedures_memory_after_linking *)

Definition prepare_procedures_entrypoints (p: program) (mem: Memory.t) : EntryPoint.t :=
  let '(_, _, entrypoints) := prepare_procedures p mem in
  entrypoints.

(* Lemma placeholder: prepare_procedures_entrypoints_after_linking *)

Lemma link_sym:
  forall p c,
    well_formed_program p ->
    well_formed_program c ->
    linkable_mains p c  ->
    linkable (prog_interface p) (prog_interface c) ->
    program_link p c = program_link c p.
Proof.
  rewrite /linkable.
  rewrite /linkable_mains /program_link.
  move=> p c Hp_wf Hc_wf Hmain_link [Hsound Hdisj] /=.
  rewrite (unionmC (m1:=prog_interface p) (m2:=prog_interface c)); auto.
  rewrite (unionmC (m1:=prog_procedures p) (m2:=prog_procedures c)); auto.
  rewrite (unionmC (m1:=prog_buffers p) (m2:=prog_buffers c)); auto.
  case: ifP => main_p;
  case: ifP => main_c //.
  - case main_p_: (prog_main p) => [|].
    + rewrite main_p_ in Hmain_link.
      case main_c_: (prog_main c) => [|].
      * by rewrite main_c_ /= in Hmain_link.
      * rewrite main_c_ /= in Hmain_link.
        rewrite main_c_ in main_c.
        by [].
    + rewrite main_p_ in Hmain_link.
      case main_c_: (prog_main c) => [|].
      * rewrite main_c_ /= in Hmain_link.
        rewrite main_p_ in main_p.
        by [].
      * by rewrite main_c_ /= in Hmain_link.
  - case main_p_: (prog_main p) => [|].
    + rewrite main_p_ in Hmain_link.
      case main_c_: (prog_main c) => [|].
      * by rewrite main_c_ /= in Hmain_link.
      * rewrite main_c_ /= in Hmain_link.
        rewrite main_p_ in main_p.
        by [].
    + rewrite main_p_ in Hmain_link.
      case main_c_: (prog_main c) => [|].
      * rewrite main_c_ /= in Hmain_link.
        rewrite main_c_ in main_c.
        by [].
      * by rewrite main_c_ /= in Hmain_link.
  - rewrite -(wfprog_defined_buffers Hp_wf).
    rewrite -(wfprog_defined_buffers Hc_wf).
    by [].
  - rewrite -(wfprog_defined_procedures Hp_wf).
    rewrite -(wfprog_defined_procedures Hc_wf).
    by [].
Qed.

Lemma interface_preserves_closedness_r :
  forall p1 p2 p2',
    closed_program (program_link p1 p2) ->
    prog_interface p2 = prog_interface p2' ->
    closed_program (program_link p1 p2').
Admitted.

(*
Lemma interface_preserves_closedness_r :
  forall p1 p2 p2',
    closed_program (program_link p1 p2) ->
    prog_interface p2 = prog_interface p2' ->
    linkable_mains p1 p2 ->
    linkable_mains p1 p2' ->
    closed_program (program_link p1 p2').
Proof.
  intros p1 p2 p2'
         [Hclosed [mainP [main_procs [Hmain [Hprocs Hin]]]]] Hsame_int Hlinkable_mains Hlinkable_mains'.
  constructor.
  - simpl in Hclosed.
    rewrite Hsame_int in Hclosed.
    apply Hclosed.
  - destruct (prog_main p1) as [main1 |] eqn:Hmain1;
      destruct (prog_main p2) as [main2 |] eqn:Hmain2. 
    + unfold linkable_mains in Hlinkable_mains.
      rewrite Hmain1 in Hlinkable_mains.
      rewrite Hmain2 in Hlinkable_mains.
      discriminate.
    + destruct (prog_main p2') eqn: Hmain2';
      unfold linkable_mains in Hlinkable_mains';
      rewrite Hmain1 in Hlinkable_mains';
      rewrite Hmain2' in Hlinkable_mains';
      simpl in Hlinkable_mains'; try now auto.
      exists mainP, main_procs. split; try now auto.
      ++  simpl in Hmain. rewrite Hmain1 in Hmain.
          inversion Hmain. subst.
          simpl. now rewrite Hmain1.
      ++ split; try now auto.
          admit. (* CA :true ??*)
    + admit. (* CA: true?? I am not sure we can use mainP and main_procs here *)
    + simpl in Hmain.
      rewrite Hmain1 in Hmain.
      rewrite Hmain2 in Hmain.
      discriminate.
Admitted.
 *)


Lemma closed_program_link_sym p1 p2 :
  well_formed_program p1 ->
  well_formed_program p2 ->
  linkable (prog_interface p1) (prog_interface p2) ->
  linkable_mains p1 p2 ->
  closed_program (program_link p1 p2) = closed_program (program_link p2 p1).
Proof.
  intros Hwf1 Hwf2 Hlinkable Hmains.
  rewrite (link_sym Hwf1 Hwf2 Hmains Hlinkable).
  reflexivity.
Qed.

End Intermediate.
