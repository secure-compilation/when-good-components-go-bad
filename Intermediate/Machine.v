Require Import Common.Definitions.
Require Import Common.Util.
Require Export Common.Values.
Require Export Common.Linking.
Require Import Common.Memory.
Require Import Lib.Monads.

Inductive register : Type :=
  R_ONE | R_COM | R_AUX1 | R_AUX2 | R_RA | R_SP.

Definition label := positive.

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
  Definition t : Type := list value.

  Definition to_nat (r : register) : nat :=
    match r with
    | R_ONE  => 0
    | R_COM  => 1
    | R_AUX1 => 2
    | R_AUX2 => 3
    | R_RA   => 4
    | R_SP   => 5
    end.

  Definition init := repeat Undef 7.

  Definition get (r : register) (regs : t) : value :=
    match nth_error regs (to_nat r) with
    | Some val => val
    (* this should never happen (i.e. regs should be well-formed) *)
    | None => Undef
    end.

  Definition set (r : register) (val : value) (regs : t) : t :=
    Util.Lists.update regs (to_nat r) val.

  Definition invalidate (regs : t) : t :=
    [Undef; get R_COM regs; Undef; Undef; Undef; Undef].

  Lemma init_registers_wf:
    forall r, exists val, get r init = val.
  Proof.
    intros r. unfold get.
    exists Undef. destruct r; auto.
  Qed.
End Register.

Module EntryPoint.
  Definition t := PMap.t (PMap.t Block.id).

  Definition get C P E : option Block.id :=
    match PMap.find C E with
    | Some addrs => PMap.find P addrs
    | None => None
    end.
End EntryPoint.

(* programs *)

Record program := mkProg {
  prog_interface : Program.interface;
  prog_procedures : PMap.t (PMap.t code);
  prog_buffers : PMap.t (list (Block.id * (nat + list value)));
  prog_main : Component.id * Procedure.id
}.

Inductive prog_eq : program -> program -> Prop :=
| prog_eq_intro: forall iface1 procs1 bufs1 iface2 procs2 bufs2 main1 main2,
    PMap.Equal iface1 iface2 ->
    PMap.Equal procs1 procs2 ->
    PMap.Equal bufs1 bufs2 ->
    main1 = main2 ->
    prog_eq (mkProg iface1 procs1 bufs1 main1) (mkProg iface2 procs2 bufs2 main2).

Lemma prog_eq_refl:
  forall p,
    prog_eq p p.
Proof.
  intros p.
  destruct p; constructor; reflexivity.
Qed.

Lemma prog_eq_sym:
  forall p1 p2,
    prog_eq p1 p2 -> prog_eq p2 p1.
Proof.
  intros p1 p2 H.
  inversion H; subst.
  constructor;
    try reflexivity;
    try symmetry; assumption.
Qed.

Lemma prog_eq_trans:
  forall p1 p2 p3,
    prog_eq p1 p2 -> prog_eq p2 p3 -> prog_eq p1 p3.
Proof.
  intros p1 p2 p3 H1 H2.
  inversion H1; subst; inversion H2; subst;
    constructor;
    try reflexivity;
    try etransitivity; eauto.
Qed.

Add Parametric Relation: (program) (prog_eq)
    reflexivity proved by (prog_eq_refl)
    symmetry proved by (prog_eq_sym)
    transitivity proved by (prog_eq_trans)
      as prog_eq_rel.

Definition single_component (p: program) : Prop :=
  PMap.cardinal (prog_interface p) = 1%nat.

(* well-formedness of programs *)

Definition well_formed_instruction
           (p: program) (C: Component.id) (P: Procedure.id) (i: instr) : Prop :=
  match i with
  | IBnz r l =>
    (* the branch refers to a label inside the current procedure C.P *)
    exists Cprocs Pcode, PMap.MapsTo C Cprocs (prog_procedures p) /\
                    PMap.MapsTo P Pcode Cprocs /\
                    In (ILabel l) Pcode
  | IJal l =>
    (* the jump refers to a label inside the current component C *)
    exists Cprocs P' P'code, PMap.MapsTo C Cprocs (prog_procedures p) /\
                        PMap.MapsTo P' P'code Cprocs /\
                        In (ILabel l) P'code
  | ICall C' P' =>
    (* a call is well-formed only if it targets another component and the
       interface is allowing it to happen *)
    C <> C' /\ imported_procedure (prog_interface p) C C' P'
  | IConst (IPtr ptr) r =>
    (* static pointers refers to static buffers *)
    exists bufs, PMap.MapsTo (Pointer.component ptr) bufs (prog_buffers p) /\
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
  (* each exported procedure actually exists *)
  wfprog_exported_procedures_existence:
    forall C CI,
      PMap.MapsTo C CI (prog_interface p) ->
    forall P,
      Component.is_exporting CI P ->
    exists Cprocs Pcode,
      PMap.MapsTo C Cprocs (prog_procedures p) /\
      PMap.MapsTo P Pcode Cprocs;
  (* each instruction of each procedure is well-formed *)
  wfprog_well_formed_instructions:
    forall C Cprocs,
      PMap.MapsTo C Cprocs (prog_procedures p) ->
    forall P Pcode,
      PMap.MapsTo P Pcode Cprocs ->
    forall i, In i Pcode -> well_formed_instruction p C P i;
  (* if the main component exists, then the main procedure must exist as well *)
  wfprog_main_existence:
    forall main_procs,
      PMap.MapsTo (fst (prog_main p)) main_procs (prog_procedures p) ->
      PMap.In (snd (prog_main p)) main_procs
}.

(* a closed program is a program with a closed interface and an existing main
   procedure *)
Record closed_program (p: program) := {
  (* the interface must be closed (and consequently sound) *)
  cprog_closed_interface:
    closed_interface (prog_interface p);
  (* the main procedure must exist *)
  cprog_main_existence:
    exists procs,
      PMap.MapsTo (fst (prog_main p)) procs (prog_procedures p) /\
      PMap.In (snd (prog_main p)) procs;
}.

Definition linkable_programs (p1 p2: program) : Prop :=
  (* both programs are well-formed *)
  well_formed_program p1 /\ well_formed_program p2 /\
  (* their interfaces are disjoint *)
  PMapExtra.Disjoint (prog_interface p1) (prog_interface p2) /\
  (*  the sets of components having buffers are disjoint *)
  PMapExtra.Disjoint (prog_buffers p1) (prog_buffers p2) /\
  (* ^ APT added 
     Need something like this in order to prove linking_well_formedness, 
     for example the buffers_existence clause.  Interface disjointness is not enough.
     For suppose C is in interface of p1 (hence not in interface of p2) but has buffers defined in p2
     (about which we know nothing).  Since p2 wins over p1 when combining buffers, we have to show
     that these p2 buffers are the required ones, which we don't know. *)
  (* the sets of components having procedures are disjoint *)
  PMapExtra.Disjoint (prog_procedures p1) (prog_procedures p2) /\
  (* ^ APT added 
     For similar reasons, needed to prove exported_procedures_existence. *)  
  (* the union of their interfaces is sound *)
  sound_interface (PMapExtra.update (prog_interface p1) (prog_interface p2)).

Definition program_link (p1 p2: program) mainC mainP : program :=
  {| prog_interface := PMapExtra.update (prog_interface p1) (prog_interface p2);
     prog_procedures := PMapExtra.update (prog_procedures p1) (prog_procedures p2);
     prog_buffers := PMapExtra.update (prog_buffers p1) (prog_buffers p2);
     prog_main := (mainC, mainP) |}.

(*
Ltac inv H := (inversion H; subst; clear H).

(* TODO: Figure out what to do about the last clause. *)
Theorem linking_well_formedness:
  forall p1 p2 mainC mainP,
    linkable_programs p1 p2 ->
    well_formed_program (program_link p1 p2 mainC mainP).
Proof.
  intros. destruct H as (WF1 & WF2 & IDISJ & BDISJ & PDISJ & SND). 
  constructor. 
  + auto. 
  + simpl. 
    intros. 
    rewrite PMapExtra.update_in_iff in H.
    inv H. 
    - destruct WF1. pose proof (wfprog_buffers_existence0 C H0).
      clear - H BDISJ. unfold has_required_local_buffers in *. simpl. 
      destruct H as (b1 & b2 & bufs & FND & B1 & B2).
      exists b1, b2, bufs. 
      intuition.
      rewrite <- PMapFacts.find_mapsto_iff in FND|-*.  
      rewrite PMapExtra.update_mapsto_iff.  
      right.
      intuition.
      eapply BDISJ. 
      split; [| apply H].
      rewrite PMapFacts.find_mapsto_iff in FND.  
      rewrite PMapFacts.in_find_iff.
      rewrite FND. discriminate.
    - destruct WF2. pose proof (wfprog_buffers_existence0 C H0).
      clear - H BDISJ. unfold has_required_local_buffers in *. simpl. 
      destruct H as (b1 & b2 & bufs & FND & B1 & B2).
      exists b1, b2, bufs. 
      intuition.
      rewrite <- PMapFacts.find_mapsto_iff in FND|-*.  
      rewrite PMapExtra.update_mapsto_iff.  
      left.
      intuition.
  + simpl. intros. 
    rewrite PMapExtra.update_mapsto_iff in H. 
    inv H.
    - destruct WF2. 
      edestruct wfprog_exported_procedures_existence0 as [cprocs [pcode [Q1 Q2]]]; eauto.
      exists cprocs, pcode. intuition.
      rewrite  PMapExtra.update_mapsto_iff. intuition.
    - inv H1. destruct WF1. 
      edestruct wfprog_exported_procedures_existence0 as [cprocs [pcode [Q1 Q2]]]; eauto.
      exists cprocs, pcode. intuition.
      rewrite PMapExtra.update_mapsto_iff. right. intuition.
      eapply PDISJ. split; eauto.
      rewrite PMapFacts.find_mapsto_iff in Q1.
      rewrite PMapFacts.in_find_iff. rewrite Q1. discriminate.
  + simpl. intros.
    rewrite PMapExtra.update_mapsto_iff in H. 
    inv H. 
    - destruct WF2.
      pose proof (wfprog_well_formed_instructions0 _ _ H2 _ _ H0 _ H1).
      destruct i; auto. 
      * simpl in H |-*.  destruct i; auto. 
        destruct H as [bufs [Q1 Q2]].
        exists bufs; intuition. 
        rewrite PMapExtra.update_mapsto_iff. left; auto.
      * simpl in H |-*. 
        destruct H as [cprocs [pcode Q]].
        exists cprocs, pcode. intuition.
        rewrite PMapExtra.update_mapsto_iff. left; auto.
      * simpl in H|-*.
        destruct H as [cprocs [P' [PC Q]]].
        exists cprocs, P', PC; intuition.
        rewrite PMapExtra.update_mapsto_iff. left; auto.
      * simpl in H|-*.
        destruct H. 
        intuition.
        unfold imported_procedure in *.
        destruct H3 as [CI Q].
        exists CI; intuition.
        unfold Program.has_component in *. 
        rewrite PMapExtra.update_mapsto_iff. left; auto.
    - inv H2. destruct WF1. 
      pose proof (wfprog_well_formed_instructions0 _ _ H _ _ H0 _ H1).
      destruct i; auto. 
      * simpl in H2 |-*.  destruct i; auto. 
        destruct H2 as [bufs [Q1 Q2]].
        exists bufs; intuition. 
        rewrite PMapExtra.update_mapsto_iff. right; intuition. 
        eapply BDISJ; split; eauto.
        apply PMapFacts.find_mapsto_iff in Q1.
        apply PMapFacts.in_find_iff.  rewrite Q1; discriminate.
      * simpl in H2 |-*. 
        destruct H2 as [cprocs [pcode Q]].
        exists cprocs, pcode. intuition.
        rewrite PMapExtra.update_mapsto_iff. right; intuition.
      * simpl in H2 |-*.
        destruct H2 as [cprocs [P' [PC Q]]].
        exists cprocs, P', PC; intuition.
        rewrite PMapExtra.update_mapsto_iff. right; intuition.
      * simpl in H2 |-*.
        destruct H2. 
        split. auto.
        unfold imported_procedure in *.
        destruct H4 as [CI Q].
        exists CI; intuition.
        unfold Program.has_component in *. 
        rewrite PMapExtra.update_mapsto_iff. right; intuition. 
        eapply IDISJ; split; eauto.
        apply PMapFacts.find_mapsto_iff in H4. 
        rewrite PMapFacts.in_find_iff. rewrite H4. discriminate.
  + Admitted. (* This obviously isn't true for arbitrary (mainC,mainP) ! *)
*)

Fixpoint init_component m E ps C Cprocs bufs
  : Memory.t * EntryPoint.t * PMap.t (PMap.t code) :=
  match Cprocs with
  | [] => (m, E, ps)
  | (P, bytecode) :: Cprocs' =>
    let Cmem :=
        match PMap.find C m with
        | Some Cmem => Cmem
        | None =>
          match PMap.find C bufs with
          | Some Cbufs => ComponentMemory.prealloc Cbufs
          (* the following should never happen, since every
             component has at least one buffer *)
          | None => ComponentMemory.empty
          end
        end in
    let '(Cmem', b) := ComponentMemory.reserve_block Cmem in
    let m' := PMap.add C Cmem' m in
    let Centrypoints :=
        match PMap.find C E with
        | None => PMap.empty Block.id
        | Some old_Centrypoints => old_Centrypoints
        end in
    let Centrypoints' := PMap.add P b Centrypoints in
    let E' := PMap.add C Centrypoints' E in
    let Cps :=
        match PMap.find C ps with
        | None => PMap.empty code
        | Some oldCps => oldCps
        end in
    let Cps' := PMap.add b bytecode Cps in
    let ps' := PMap.add C Cps' ps in
    init_component m' E' ps' C Cprocs' bufs
  end.

Definition init_all (p: program)
  : Memory.t * EntryPoint.t * PMap.t (PMap.t code) :=
  let fix init_all_procs m E ps procs :=
      match procs with
      | [] => (m, E, ps)
      | (C, Cprocs) :: procs' =>
        let '(m', E', ps') := init_component m E ps C
                                             (PMap.elements Cprocs)
                                             (prog_buffers p) in
        init_all_procs m' E' ps' procs'
      end
  in
  init_all_procs (Memory.empty [])
                 (PMap.empty (PMap.t Block.id)) (PMap.empty (PMap.t code))
                 (PMap.elements (prog_procedures p)).

End Intermediate.