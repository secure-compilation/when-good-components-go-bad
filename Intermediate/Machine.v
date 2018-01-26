Require Import Common.Definitions.
Require Import Common.Util.
Require Export Common.Values.
Require Export Common.Linking.
Require Import Common.Memory.
Require Import Lib.Monads.

From mathcomp Require Import ssreflect ssrfun ssrbool.

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
  prog_main: option (Component.id * Procedure.id)
}.

Definition main_comp (p: Intermediate.program): Component.id :=
  match prog_main p with
  | Some (mainC, _) => mainC
  | None => 0
  end.

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
  wfprog_well_formed_procedures:
    fsubset (domm (prog_procedures p)) (domm (prog_interface p));
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
  wfprog_well_formed_buffers:
    fsubset (domm (prog_buffers p)) (domm (prog_interface p));
  (* if the main component exists, then the main procedure must exist as well *)
  wfprog_main_existence:
    forall mainC mainP,
      prog_main p = Some (mainC, mainP) ->
    exists main_procs,
      getm (prog_procedures p) mainC = Some main_procs /\ mainP \in domm main_procs
}.

(* a closed program is a program with a closed interface and an existing main
   procedure *)
Record closed_program (p: program) := {
  (* the interface must be closed (and consequently sound) *)
  cprog_closed_interface:
    closed_interface (prog_interface p);
  (* the main procedure must exist *)
  cprog_main_existence:
    exists mainC mainP main_procs,
      prog_main p = Some (mainC, mainP) /\
      getm (prog_procedures p) mainC = Some main_procs /\ mainP \in domm main_procs
}.

Inductive linkable_programs: program -> program -> Prop :=
| linkable_programs_intro:
   forall prog1 prog2,
     well_formed_program prog1 ->
     well_formed_program prog2 ->
     sound_interface (unionm (prog_interface prog1) (prog_interface prog2)) ->
     fdisjoint (domm (prog_interface prog1)) (domm (prog_interface prog2)) ->
     fdisjoint (domm (prog_procedures prog1)) (domm (prog_procedures prog2)) ->
       (* CH: prev follows from well_formed_program and disjointness of interfaces, can we remove? *)
     fdisjoint (domm (prog_buffers prog1)) (domm (prog_buffers prog2)) ->
       (* CH: prev follows from well_formed_program and disjointness of interfaces, can we remove? *)
     linkable_mains (prog_main prog1) (prog_main prog2) ->
       (* CH: prev follows from well_formed_program and disjointness of interfaces, can we remove? *)
     linkable_programs prog1 prog2.

Definition program_link (p1 p2: program): program :=
  {| prog_interface := unionm (prog_interface p1) (prog_interface p2);
     prog_procedures := unionm (prog_procedures p1) (prog_procedures p2);
     prog_buffers := unionm (prog_buffers p1) (prog_buffers p2);
     prog_main := main_link (prog_main p1) (prog_main p2) |}.

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
  intros p Hwf Hempty_iface.
  remember p as prog.
  destruct p.
  rewrite Heqprog.
  rewrite Heqprog in Hwf, Hempty_iface.
  simpl in *.
  rewrite Hempty_iface.
  enough (prog_procedures0 = emptym) as Hempty_procs.
  enough (prog_buffers0 = emptym) as Hempty_bufs.
  enough (prog_main0 = None) as Hempty_main.
  rewrite Hempty_procs Hempty_bufs Hempty_main.
  reflexivity.
  (* show that there is no main *)
  - rewrite <- Heqprog in Hwf.
    pose proof (wfprog_main_existence Hwf) as Hmain_existence.
    destruct (prog_main prog) as [[mainC mainP]|] eqn:Hmain.
    + destruct (Hmain_existence mainC mainP) as [main_procs []].
      reflexivity.
      rewrite Heqprog in H. simpl in *.
      rewrite Hempty_procs in H.
      inversion H.
    + rewrite Heqprog in Hmain. simpl in *.
      assumption.
  (* show that there are no buffers *)
  - rewrite <- Heqprog in Hwf.
    pose proof (wfprog_well_formed_buffers Hwf) as Hbufs_wf.
    rewrite Heqprog in Hbufs_wf. rewrite Hempty_iface in Hbufs_wf. simpl in *.
    rewrite domm0 in Hbufs_wf.
    rewrite fsubset0 in Hbufs_wf.
    (* not able to use eq_domm0 *)
    pose proof eq_domm0 as Hempty.
    admit.
  (* show that there are no procedures *)
  - rewrite <- Heqprog in Hwf.
    pose proof (wfprog_well_formed_procedures Hwf) as Hprocs_wf.
    rewrite Heqprog in Hprocs_wf. rewrite Hempty_iface in Hprocs_wf. simpl in *.
    rewrite domm0 in Hprocs_wf.
    rewrite fsubset0 in Hprocs_wf.
    (* not able to use eq_domm0 *)
    pose proof eq_domm0 as Hempty.
    admit.
Admitted.

Lemma empty_prog_is_well_formed:
  well_formed_program empty_prog.
Proof.
  constructor; simpl.
  - unfold sound_interface.
    intros. inversion H0.
  - repeat rewrite domm0. apply fsubsetxx.
  - intros. inversion H.
  - intros. inversion H.
  - repeat rewrite domm0. apply fsubsetxx.
  - intros. discriminate.
Qed.

Theorem empty_prog_linkability:
  forall p,
    well_formed_program p ->
    linkable_programs p empty_prog.
Proof.
  intros p Hwf.
  constructor.
  - assumption.
  - apply empty_prog_is_well_formed.
  - simpl. rewrite unionm0.
    apply (wfprog_interface_soundness Hwf).
  - simpl. rewrite domm0. apply fdisjoints0.
  - simpl. rewrite domm0. apply fdisjoints0.
  - simpl. rewrite domm0. apply fdisjoints0.
  - simpl. unfold linkable_mains.
    destruct (prog_main p); auto.
Qed.

Theorem linking_empty_program:
  forall p,
    program_link p empty_prog = p.
Proof.
  intros p.
  destruct p. unfold program_link. simpl.
  repeat rewrite unionm0.
  rewrite main_link_with_empty_main.
  reflexivity.
Qed.

Theorem linkable_sym:
  forall p c,
    linkable_programs p c -> linkable_programs c p.
Proof.
  intros p c Hlinkable.
  inversion Hlinkable; subst.
  constructor;
    try assumption.
  - rewrite unionmC; auto.
    unfold fdisjoint. rewrite fsetIC. auto.
  - unfold fdisjoint. rewrite fsetIC. auto.
  - unfold fdisjoint. rewrite fsetIC. auto.
  - unfold fdisjoint. rewrite fsetIC. auto.
  - apply linkable_mains_sym; auto.
Qed.

Theorem linking_well_formedness:
  forall p1 p2,
    linkable_programs p1 p2 ->
    well_formed_program (program_link p1 p2).
Proof.
  intros p1 p2 Hlinkability.
  inversion Hlinkability; subst.
  constructor.
  - simpl. assumption.
  - simpl.
    repeat rewrite domm_union.
    apply fsetUSS.
    + apply (wfprog_well_formed_procedures H).
    + apply (wfprog_well_formed_procedures H0).
  - intros.
    simpl in *.
    rewrite unionmE.
    rewrite unionmE in H6.
    destruct ((prog_interface p1) C) eqn:Hwhere; simpl in *.
    + rewrite Hwhere in H6.
      inversion H6; subst.
      destruct (wfprog_exported_procedures_existence H Hwhere H7)
        as [Cprocs [Pcode [Hproc Hcode]]].
      rewrite Hproc. simpl.
      exists Cprocs. exists Pcode.
      split; auto.
    + enough ((prog_procedures p1) C = None) as Hno_p1.
      * rewrite Hno_p1. rewrite Hwhere in H6. simpl in *.
        destruct (wfprog_exported_procedures_existence H0 H6 H7)
          as [Cprocs [Pcode [Hproc Hcode]]].
        exists Cprocs. exists Pcode.
        split; auto.
      * destruct ((prog_procedures p1) C) eqn:Hin_p1.
        ** rewrite Hwhere in H6. simpl in H6.
           destruct (wfprog_exported_procedures_existence H0 H6 H7)
             as [Cprocs [Pcode [Hproc Hcode]]].
           unfold fdisjoint in H3.
           admit.
        ** reflexivity.
  - intros.
    unfold well_formed_instruction.
    destruct i; auto.
    + destruct i; auto.
      simpl in *.
      rewrite unionmE.
      rewrite unionmE in H6.
      admit.
    + admit.
    + admit.
    + admit.
  - simpl.
    repeat rewrite domm_union.
    apply fsetUSS.
    + apply (wfprog_well_formed_buffers H).
    + apply (wfprog_well_formed_buffers H0).
  - intros. simpl in *.
    pose proof (wfprog_main_existence H) as Hmain1.
    pose proof (wfprog_main_existence H0) as Hmain2.
    destruct (prog_main p1) as [[]|] eqn:Hmain_p1;
    destruct (prog_main p2) as [[]|] eqn:Hmain_p2.
    + simpl in *.
      inversion H6; subst.
      destruct (Hmain1 mainC mainP eq_refl) as [main_procs []].
      exists main_procs.
      split.
      * rewrite unionmE.
        rewrite H7. reflexivity.
      * assumption.
    + simpl in *.
      inversion H6; subst.
      destruct (Hmain1 mainC mainP eq_refl) as [main_procs []].
      exists main_procs.
      split.
      * rewrite unionmE.
        rewrite H7. reflexivity.
      * assumption.
    + inversion H6; subst.
      destruct (Hmain2 mainC mainP eq_refl) as [main_procs []].
      exists main_procs.
      split.
      * rewrite unionmE.
        admit.
      * assumption.
    + simpl in *. discriminate.
Admitted.

Definition alloc_static_buffers p comps :=
  mkfmapf (fun C =>
    ComponentMemory.prealloc (odflt emptym (prog_buffers p C))) comps.

Definition prepare_initial_memory (p: program) : Memory.t :=
  alloc_static_buffers p (domm (prog_interface p)).

Fixpoint reserve_component_blocks p C Cmem Cprocs Centrypoints procs_code
  : ComponentMemory.t * NMap code * NMap Block.id :=
  match procs_code with
  | [] => (Cmem, Cprocs, Centrypoints)
  | (P, Pcode) :: procs_code' =>
    let (Cmem', b) := ComponentMemory.reserve_block Cmem in
    let Cprocs' := setm Cprocs b Pcode in
    (* if P is exported, add an external entrypoint *)
    match getm (prog_interface p) C with
    | Some Ciface =>
      if P \in Component.export Ciface then
        let Centrypoints' := setm Centrypoints P b in
        reserve_component_blocks p C Cmem' Cprocs' Centrypoints' procs_code'
      else
        reserve_component_blocks p C Cmem' Cprocs' Centrypoints procs_code'
    | None =>
      (* this case shouldn't happen for well formed p *)
      reserve_component_blocks p C Cmem' Cprocs' Centrypoints procs_code'
    end
  end.

Fixpoint reserve_procedures_blocks p mem procs entrypoints comps_code
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
      reserve_procedures_blocks p mem' procs' entrypoints' comps_code'
    | None =>
      (* this shouldn't happen if memory was initialized before the call *)
      (* we just skip initialization for this component *)
      reserve_procedures_blocks p mem procs entrypoints comps_code'
    end
  end.

Definition prepare_procedures (p: program) (mem: Memory.t)
  : Memory.t * NMap (NMap code) * EntryPoint.t :=
  reserve_procedures_blocks p mem emptym emptym (elementsm (prog_procedures p)).

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

Lemma alloc_static_buffers_after_linking:
  forall p c,
    linkable_programs p c ->
    let pc := program_link p c in
    alloc_static_buffers pc (domm (prog_interface pc)) =
    unionm (alloc_static_buffers p (domm (prog_interface p)))
           (alloc_static_buffers c (domm (prog_interface c))).
Proof.
  intros p c Hlinkable Hpc.
  subst Hpc. simpl.
  apply eq_fmap. intros k.
  rewrite unionmE.
  destruct (isSome ((alloc_static_buffers p (domm (prog_interface p))) k))
           eqn:Hin.
  - admit.
  - admit.
Admitted.

Theorem prepare_initial_memory_after_linking:
  forall p c,
    linkable_programs p c ->
    prepare_initial_memory (program_link p c) =
    unionm (prepare_initial_memory p) (prepare_initial_memory c).
Proof.
  intros p c Hlinkable.
  unfold prepare_initial_memory.
  apply alloc_static_buffers_after_linking; auto.
Qed.

End Intermediate.
