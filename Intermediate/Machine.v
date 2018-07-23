Require Import Common.Definitions.
Require Import Common.Util.
Require Export Common.Values.
Require Export Common.Linking.
Require Import Common.Memory.
Require Import Lib.Monads.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From extructures Require Import fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Inductive register : Type :=
  R_ONE | R_COM | R_AUX1 | R_AUX2 | R_RA | R_SP | R_ARG.

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

  Lemma init_registers_wf:
    forall r, exists val, get r init = val.
  Proof.
    intros r. unfold get.
    exists Undef. destruct r; auto.
  Qed.

  Lemma invalidate_eq : forall regs1 regs2,
    get R_COM regs1 = get R_COM regs2 ->
    invalidate regs1 = invalidate regs2.
  Proof.
    intros regs1 regs2 Hregs.
    unfold invalidate.
    congruence.
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
      getm (prog_procedures p) Component.main = Some main_procs /\ mainP \in domm main_procs;
  (* The main component is not in the interface if no main procedure is given. *)
  wfprog_main_component:
    prog_main p = None ->
    Component.main \notin domm (prog_interface p)
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
*)

Definition linkable_mains (prog1 prog2 : program) : Prop :=
  ~~ (prog_main prog1 && prog_main prog2).

Lemma linkable_mains_sym : forall (prog1 prog2 : program),
  linkable_mains prog1 prog2 -> linkable_mains prog2 prog1.
Proof.
  intros prog1 prog2.
  unfold linkable_mains, andb, negb.
  destruct (isSome (prog_main prog1));
    destruct (isSome (prog_main prog2));
    intuition.
Qed.

Definition matching_mains (prog1 prog2 : program) : Prop :=
  prog_main prog1 = None <-> prog_main prog2 = None.

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
  move=> [intf procs bufs main] [/= _ e_procs _ _ e_bufs Hmain _] e_intf.
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
Proof.
  constructor; try by [].
  - by rewrite domm0.
Qed.

Theorem linking_empty_program:
  forall p,
    program_link p empty_prog = p.
Proof.
  intros p.
  destruct p. unfold program_link. simpl.
  repeat rewrite unionm0.
  by case: prog_main0.
Qed.

Lemma linkable_mains_empty_prog:
  forall p,
    linkable_mains p empty_prog.
Proof.
  intros p.
  destruct p. unfold linkable_mains.
  now rewrite andb_comm.
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

Lemma prog_main_link_none_left: forall p1 p2,
  prog_main (program_link p1 p2) = None ->
  prog_main p1 = None.
Proof.
  intros p1 p2 Hprog_main.
  unfold program_link in Hprog_main. simpl in Hprog_main.
  destruct (prog_main p1);
    destruct (prog_main p2);
    easy.
Qed.

Lemma prog_main_link_none_right: forall p1 p2,
  prog_main (program_link p1 p2) = None ->
  prog_main p2 = None.
Proof.
  intros p1 p2 Hprog_main.
  unfold program_link in Hprog_main. simpl in Hprog_main.
  destruct (prog_main p1);
    destruct (prog_main p2);
    easy.
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
  - inversion Hwf1 as [_ _ _ _ _ _ Hmain_comp1].
    inversion Hwf2 as [_ _ _ _ _ _ Hmain_comp2].
    intros Hprog_main1.
    assert (Hprog_main2 := Hprog_main1).
    apply prog_main_link_none_left in Hprog_main1.
    apply prog_main_link_none_right in Hprog_main2.
    specialize (Hmain_comp1 Hprog_main1).
    specialize (Hmain_comp2 Hprog_main2).
    rewrite domm_union in_fsetU.
    rewrite negb_or Hmain_comp1 Hmain_comp2.
    reflexivity.
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
Definition reserve_component_blocks p C acc procs_code
  : ComponentMemory.t * NMap code * NMap Block.id :=
  let is_main_proc comp_id proc_id :=
      match prog_main p with
      | Some main_proc_id =>
        (Component.main =? comp_id) && (main_proc_id =? proc_id)
      | None => false
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

(* In the foreseen, controlled use of this function, we always go on the Some
   branch. For each component C, we read its (initial) memory and use it to
   construct the initial state of C, recursing after we update its maps. Given
   identical inputs (component memories, which we have by compositionality of
   that piece of code) the outputs will be identical. *)
Fixpoint reserve_procedure_blocks p acc comps_code
  : Memory.t * NMap (NMap code) * EntryPoint.t :=
  let aux acc comps_code :=
      let '(mem, procs, entrypoints) := acc in
      let '(C, Cprocs) := comps_code in
    match getm mem C with
    | Some Cmem =>
      let '(Cmem', Cprocs, Centrypoints) :=
          reserve_component_blocks p C (Cmem, emptym, emptym) (elementsm Cprocs) in
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

Definition prepare_procedures (p: program) (mem: Memory.t)
  : Memory.t * NMap (NMap code) * EntryPoint.t :=
  reserve_procedure_blocks p (mem, emptym, emptym) (elementsm (prog_procedures p)).

(* For each component, integrate the (now separate) fetching of its procedures,
   obtention of its initial component memory and then reserve_component_blocks.
   The logic of reserve_procedure_blocks is implicit in the map-like nature of
   its results. (By splitting the definition and proving some intermediate
   results on the auxiliary, the composition of the parts will be easier.) *)
Definition prepare_procedures_initial_memory_aux (p: program) :=
  mkfmapf
    (fun C =>
       let Cprocs := odflt emptym ((prog_procedures p) C) in
       let Cmem := ComponentMemory.prealloc (odflt emptym ((prog_buffers p) C)) in
       reserve_component_blocks p C (Cmem, emptym, emptym) (elementsm Cprocs))
    (domm (prog_interface p)).

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

Lemma prepare_procedures_initial_memory_aux_empty_program:
  prepare_procedures_initial_memory_aux empty_prog = emptym.
Proof.
  unfold prepare_procedures_initial_memory_aux.
  rewrite domm0.
  reflexivity.
Qed.

(* RB: Relocate this. *)
(* Maybe can be pushed in Arthur's extructures *)
Lemma mapm_empty: forall (T : ordType) (S S' : Type) (f : S -> S'),
  mapm f (@emptym T S) = emptym.
Proof.
    by move => T S S' f; apply /eq_fmap => n; rewrite emptymE.
Qed.

Theorem prepare_procedures_initial_memory_empty_program:
  prepare_procedures_initial_memory empty_prog = (emptym, emptym, emptym).
Proof.
  unfold prepare_procedures_initial_memory.
  rewrite prepare_procedures_initial_memory_aux_empty_program.
  rewrite !mapm_empty.
  reflexivity.
Qed.

(* initialization of a linked program *)

(* The following two lemmas are quick conveniences for the proper
   result of the partition lemma that follows.*)
Lemma prog_buffers_in_domm :
  forall p Cid,
    well_formed_program p ->
    Cid \in domm (prog_interface p) ->
  exists bufs,
    (prog_buffers p) Cid = Some bufs.
Proof.
  intros p Cid [_ _ _ _ Hbufs _] Hin.
  apply /dommP.
  congruence.
Qed.

Lemma prog_buffers_notin_domm :
  forall p Cid,
    well_formed_program p ->
    Cid \notin domm (prog_interface p) ->
    (prog_buffers p) Cid = None.
Proof.
  intros p Cid [_ _ _ _ Hbufs _] Hin.
  apply /dommPn.
  congruence.
Qed.

(* TODO: Refactor proof (easy). Inline or relocate auxiliary lemmas. *)
Lemma alloc_static_buffers_after_linking:
  forall p c,
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    alloc_static_buffers (program_link p c)
                         (domm (prog_interface (program_link p c))) =
    unionm (alloc_static_buffers p (domm (prog_interface p)))
           (alloc_static_buffers c (domm (prog_interface c))).
Proof.
  intros p c Hwfp Hwfc [Hsound Hdisjoint].
  unfold alloc_static_buffers.
  rewrite <- eq_fmap. (* Operate from extensional equality. *)
  unfold eqfun. simpl. intros Cid.
  rewrite !(mkfmapfE, unionmE).
  destruct (Cid \in domm (prog_interface p)) eqn:Hintp;
    destruct (Cid \in domm (prog_interface c)) eqn:Hintc.
  - (* Contra.
       However, note this case works out with the current definition. *)
    pose proof prog_buffers_in_domm Hwfp Hintp as [bufsp Hbufsp].
    rewrite !mem_domm.
    rewrite unionmE.
    rewrite mem_domm in Hintp. rewrite !Hintp.
    rewrite mem_domm in Hintc. rewrite !Hintc.
    rewrite Hbufsp.
    reflexivity.
  - pose proof prog_buffers_in_domm Hwfp Hintp as [bufsp Hbufsp].
    rewrite !mem_domm.
    rewrite unionmE.
    rewrite mem_domm in Hintp. rewrite !Hintp.
    rewrite mem_domm in Hintc. rewrite !Hintc.
    rewrite Hbufsp.
    reflexivity.
  - apply negb_true_iff in Hintp.
    pose proof prog_buffers_notin_domm Hwfp Hintp as Hbufsp.
    apply negb_true_iff in Hintp.
    rewrite !mem_domm.
    rewrite unionmE.
    rewrite mem_domm in Hintp. rewrite !Hintp.
    rewrite mem_domm in Hintc. rewrite !Hintc.
    rewrite Hbufsp.
    reflexivity.
  - (* Trivial case. *)
    rewrite !mem_domm.
    rewrite unionmE.
    rewrite mem_domm in Hintp. rewrite Hintp.
    rewrite mem_domm in Hintc. rewrite Hintc.
    reflexivity.
Qed.

Theorem prepare_initial_memory_after_linking:
  forall p c,
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    prepare_initial_memory (program_link p c) =
    unionm (prepare_initial_memory p) (prepare_initial_memory c).
Proof.
  intros p c Hwf1 Hwf2 Hlinkable.
  unfold prepare_initial_memory.
  apply alloc_static_buffers_after_linking; auto.
Qed.

(*
Definition prepare_procedures_memory (p: program) (mem: Memory.t) : Memory.t :=
  let '(mem, _, _) := prepare_procedures p mem in
  mem.
*)

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
    linkable_mains p c ->
    prepare_procedures_initial_memory_aux (program_link p c) =
    unionm (prepare_procedures_initial_memory_aux p)
           (prepare_procedures_initial_memory_aux c).
Proof.
  intros p c Hwfp Hwfc Hlinkable Hmains.
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
    destruct (prog_main p) as [mainp |] eqn:Hmainp;
      destruct (prog_main c) as [mainc |] eqn:Hmainc.
    + easy. (* Contra. *)
    + reflexivity.
    + destruct Cid as [| n].
      * (* Contra. *)
        inversion Hwfp as [_ _ _ _ _ _ Hmain_compp].
        specialize (Hmain_compp Hmainp).
        have Hp'' : (prog_interface p) 0 = None by apply /dommPn.
        rewrite Hp'' in Hp'.
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
    destruct (prog_main p) as [mainp |] eqn:Hmainp;
      destruct (prog_main c) as [mainc |] eqn:Hmainc.
    + (* Contra. *)
      unfold linkable_mains in Hmains.
      rewrite Hmainp Hmainc in Hmains.
      discriminate.
    + simpl. rewrite Hmainp Hmainc.
      destruct Cid as [| n].
      * (* Contra, *)
        inversion Hwfc as [_ _ _ _ _ _ Hmain_compc].
        specialize (Hmain_compc Hmainc).
        have Hc'' : (prog_interface c) 0 = None by apply /dommPn.
        rewrite Hc'' in Hc'.
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
    linkable_mains p c ->
    prepare_procedures_memory (program_link p c) =
    unionm (prepare_procedures_memory p) (prepare_procedures_memory c).
Proof.
  intros p c Hwfp Hwfc Hlinkable Hmains.
  unfold prepare_procedures_memory,
         prepare_procedures_initial_memory, prepare_procedures_initial_memory_aux.
  rewrite <- mapm_unionm. apply mapm_eq.
  apply prepare_procedures_initial_memory_aux_after_linking; assumption.
Qed.

(*
Definition prepare_procedures_entrypoints (p: program) (mem: Memory.t) : EntryPoint.t :=
  let '(_, _, entrypoints) := prepare_procedures p mem in
  entrypoints.
*)

Definition prepare_procedures_entrypoints (p: program) : EntryPoint.t :=
  let '(_, _, entrypoints) := prepare_procedures_initial_memory p in
  entrypoints.

Theorem prepare_procedures_entrypoints_after_linking:
  forall p c,
    well_formed_program p ->
    well_formed_program c ->
    linkable (prog_interface p) (prog_interface c) ->
    linkable_mains p c ->
    prepare_procedures_entrypoints (program_link p c) =
    unionm (prepare_procedures_entrypoints p)
           (prepare_procedures_entrypoints c).
Proof.
  intros p c Hwfp Hwfc Hlinkable Hmains.
  unfold prepare_procedures_entrypoints,
         prepare_procedures_initial_memory, prepare_procedures_initial_memory_aux.
  rewrite <- mapm_unionm. apply mapm_eq.
  apply prepare_procedures_initial_memory_aux_after_linking; assumption.
Qed.

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
         [Hclosed [mainP [main_procs [Hmain [Hprocs Hin]]]]]
         Hlinkable_mains Hmatching_mains.
  constructor.
  - simpl in Hclosed.
    rewrite Hsame_int in Hclosed.
    apply Hclosed.
  - destruct (prog_main p1) as [main1 |] eqn:Hmain1;
      destruct (prog_main p2) as [main2 |] eqn:Hmain2.
    + unfold linkable_mains in Hlinkable_mains.
      rewrite Hmain1 Hmain2 in Hlinkable_mains.
      discriminate.
    + (* main is in p1.*)
      unfold program_link in Hmain.
      rewrite Hmain1 in Hmain.
      simpl in Hmain.
      inversion Hmain; subst mainP; clear Hmain.
      (* Likewise main_procs (used only in second sub-goal). *)
      unfold program_link in Hprocs; simpl in Hprocs.
      destruct (wfprog_main_existence Hwf1 Hmain1)
        as [main_procs1 [Hmain_procs1 Hin1]].
      rewrite unionmE Hmain_procs1 in Hprocs.
      inversion Hprocs; subst main_procs; clear Hprocs.
      (* Instantiate and solve. *)
      exists main1, main_procs1. split; [| split].
      * unfold program_link.
        rewrite Hmain1.
        reflexivity.
      * unfold program_link; simpl.
        rewrite unionmE Hmain_procs1.
        reflexivity.
      * assumption.
    + (* main is in p2'. *)
      destruct (prog_main p2') as [main2' |] eqn:Hmain2';
        last (apply Hmatching_mains in Hmain2';
              rewrite Hmain2' in Hmain2;
              inversion Hmain2).
      (* Likewise main_procs (used only in second sub-goal). *)
      destruct (wfprog_main_existence Hwf2' Hmain2')
        as [main_procs2' [Hmain_procs2' Hin2']].
      exists main2', main_procs2'. split; [| split].
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

Lemma closed_program_link_sym p1 p2 :
  well_formed_program p1 ->
  well_formed_program p2 ->
  linkable (prog_interface p1) (prog_interface p2) ->
  closed_program (program_link p1 p2) = closed_program (program_link p2 p1).
Proof.
  intros Hwf1 Hwf2 Hlinkable.
  rewrite (program_linkC Hwf1 Hwf2 Hlinkable).
  reflexivity.
Qed.

End Intermediate.
