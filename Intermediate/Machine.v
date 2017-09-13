Require Import Common.Definitions.
Require Import Common.Util.
Require Export Common.Values.
Require Export Common.Linking.
Require Import Common.Memory.
Require Import Lib.Monads.

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
    [Undef; get R_COM regs; Undef; Undef; get R_RA regs; Undef].

  Lemma init_registers_wf:
    forall r, exists val, get r init = val.
  Proof.
    intros r. unfold get.
    exists Undef. destruct r; auto.
  Qed.
End Register.

Module EntryPoint.
  Definition t := NMap.t (NMap.t Block.id).

  Definition get C P E : option Block.id :=
    match NMap.find C E with
    | Some addrs => NMap.find P addrs
    | None => None
    end.

  Lemma get_on_compatible_entrypoints :
    forall E E' C P addrs,
      NMap.MapsTo C addrs E ->
      NMap.MapsTo C addrs E' ->
      get C P E = get C P E'.
  Proof.
    intros E E' C P addrs HEaddrs HE'addrs.
    unfold get.
    rewrite NMapFacts.find_mapsto_iff in HEaddrs, HE'addrs.
    rewrite <- HEaddrs in HE'addrs.
    inversion HE'addrs as [HEeqE'].
    rewrite HEeqE'.
    reflexivity.
  Qed.
End EntryPoint.

(* programs *)

Record program := {
  prog_interface : Program.interface;
  prog_procedures : NMap.t (NMap.t code);
  prog_buffers : NMap.t (list (Block.id * nat));
  prog_main : Component.id * Procedure.id
}.

(* well-formedness of programs *)

Definition well_formed_instruction
           (p: program) (C: Component.id) (P: Procedure.id) (i: instr) : Prop :=
  match i with
  | IBnz r l =>
    (* the branch refers to a label inside the current procedure C.P *)
    exists Cprocs Pcode, NMap.MapsTo C Cprocs (prog_procedures p) /\
                    NMap.MapsTo P Pcode Cprocs /\
                    In (ILabel l) Pcode
  | IJal l =>
    (* the jump refers to a label inside the current component C *)
    exists Cprocs P' P'code, NMap.MapsTo C Cprocs (prog_procedures p) /\
                        NMap.MapsTo P' P'code Cprocs /\
                        In (ILabel l) P'code
  | ICall C' P' =>
    (* a call is well-formed only if one of the following holds:
       1) it targets the current component and the procedure exists
       2) it targets another component and the interface is allowing it to happen *)
    (C' = C /\ exists Cprocs, NMap.MapsTo C Cprocs (prog_procedures p) /\
                        NMap.In P' Cprocs) \/
    imported_procedure (prog_interface p) C C' P'
  | IConst (IPtr ptr) r =>
    (* static pointers refers to static buffers *)
    exists bufs, NMap.MapsTo (Pointer.component ptr) bufs (prog_buffers p) /\
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

(* Component C has at least two buffers of size at least one:
   the first one is for passing the call argument, whereas the second one is used
   as a temporary store when passing controls between components *)
Definition has_required_local_buffers (p: program) (C: Component.id) : Prop :=
  exists b1 b2 bufs,
    NMap.find C (prog_buffers p) = Some (b1 :: b2 :: bufs) /\
    snd b1 > 0 /\ snd b2 > 0.

Record well_formed_program (p: program) := {
  (* the interface is sound (but maybe not closed) *)
  wfprog_interface_soundness:
    sound_interface (prog_interface p);
  (* each declared component has the required static buffers *)
  wfprog_buffers_existence:
    forall C, NMap.In C (prog_interface p) ->
         has_required_local_buffers p C;
  (* each exported procedure actually exists *)
  wfprog_exported_procedures_existence:
    forall C CI,
      NMap.MapsTo C CI (prog_interface p) ->
    forall P,
      Component.is_exporting CI P ->
    exists Cprocs Pcode,
      NMap.MapsTo C Cprocs (prog_procedures p) /\
      NMap.MapsTo P Pcode Cprocs;
  (* each instruction of each procedure is well-formed *)
  wfprog_well_formed_instructions:
    forall C Cprocs,
      NMap.MapsTo C Cprocs (prog_procedures p) ->
    forall P Pcode,
      NMap.MapsTo P Pcode Cprocs ->
    forall i, In i Pcode -> well_formed_instruction p C P i;
  (* if the main component exists, then the main procedure must exist as well *)
  wfprog_main_existence:
    forall main_procs,
      NMap.MapsTo (fst (prog_main p)) main_procs (prog_procedures p) ->
      NMap.In (snd (prog_main p)) main_procs
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
      NMap.MapsTo (fst (prog_main p)) procs (prog_procedures p) /\
      NMap.In (snd (prog_main p)) procs;
}.

Definition prog_eq (p1 p2: program) : Prop :=
  NMap.Equal (prog_interface p1) (prog_interface p2) /\
  NMap.Equal (prog_procedures p1) (prog_procedures p2) /\
  NMap.Equal (prog_buffers p1) (prog_buffers p2) /\
  prog_main p1 = prog_main p2.

Definition linkable_programs (p1 p2: program) : Prop :=
  (* both programs are well-formed *)
  well_formed_program p1 /\ well_formed_program p2 /\
  (* their interfaces are disjoint *)
  NMapExtra.Disjoint (prog_interface p1) (prog_interface p2) /\
  (*  the sets of components having buffers are disjoint *)
  NMapExtra.Disjoint (prog_buffers p1) (prog_buffers p2) /\
  (* ^ APT added 
     Need something like this in order to prove linking_well_formedness, 
     for example the buffers_existence clause.  Interface disjointness is not enough.
     For suppose C is in interface of p1 (hence not in interface of p2) but has buffers defined in p2
     (about which we know nothing).  Since p2 wins over p1 when combining buffers, we have to show
     that these p2 buffers are the required ones, which we don't know. *)
  (* the sets of components having procedures are disjoint *)
  NMapExtra.Disjoint (prog_procedures p1) (prog_procedures p2) /\
  (* ^ APT added 
     For similar reasons, needed to prove exported_procedures_existence. *)  
  (* the union of their interfaces is sound *)
  sound_interface (NMapExtra.update (prog_interface p1) (prog_interface p2)).

Definition program_link (p1 p2: program) mainC mainP : program :=
  {| prog_interface := NMapExtra.update (prog_interface p1) (prog_interface p2);
     prog_procedures := NMapExtra.update (prog_procedures p1) (prog_procedures p2);
     prog_buffers := NMapExtra.update (prog_buffers p1) (prog_buffers p2);
     prog_main := (mainC, mainP) |}.

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
    rewrite NMapExtra.update_in_iff in H.
    inv H. 
    - destruct WF1. pose proof (wfprog_buffers_existence0 C H0).
      clear - H BDISJ. unfold has_required_local_buffers in *. simpl. 
      destruct H as (b1 & b2 & bufs & FND & B1 & B2).
      exists b1, b2, bufs. 
      intuition.
      rewrite <- NMapFacts.find_mapsto_iff in FND|-*.  
      rewrite NMapExtra.update_mapsto_iff.  
      right.
      intuition.
      eapply BDISJ. 
      split; [| apply H].
      rewrite NMapFacts.find_mapsto_iff in FND.  
      rewrite NMapFacts.in_find_iff.
      rewrite FND. discriminate.
    - destruct WF2. pose proof (wfprog_buffers_existence0 C H0).
      clear - H BDISJ. unfold has_required_local_buffers in *. simpl. 
      destruct H as (b1 & b2 & bufs & FND & B1 & B2).
      exists b1, b2, bufs. 
      intuition.
      rewrite <- NMapFacts.find_mapsto_iff in FND|-*.  
      rewrite NMapExtra.update_mapsto_iff.  
      left.
      intuition.
  + simpl. intros. 
    rewrite NMapExtra.update_mapsto_iff in H. 
    inv H.
    - destruct WF2. 
      edestruct wfprog_exported_procedures_existence0 as [cprocs [pcode [Q1 Q2]]]; eauto.
      exists cprocs, pcode. intuition.
      rewrite  NMapExtra.update_mapsto_iff. intuition.
    - inv H1. destruct WF1. 
      edestruct wfprog_exported_procedures_existence0 as [cprocs [pcode [Q1 Q2]]]; eauto.
      exists cprocs, pcode. intuition.
      rewrite NMapExtra.update_mapsto_iff. right. intuition.
      eapply PDISJ. split; eauto.
      rewrite NMapFacts.find_mapsto_iff in Q1.
      rewrite NMapFacts.in_find_iff. rewrite Q1. discriminate.
  + simpl. intros.
    rewrite NMapExtra.update_mapsto_iff in H. 
    inv H. 
    - destruct WF2.
      pose proof (wfprog_well_formed_instructions0 _ _ H2 _ _ H0 _ H1).
      destruct i; auto. 
      * simpl in H |-*.  destruct i; auto. 
        destruct H as [bufs [Q1 Q2]].
        exists bufs; intuition. 
        rewrite NMapExtra.update_mapsto_iff. left; auto.
      * simpl in H |-*. 
        destruct H as [cprocs [pcode Q]].
        exists cprocs, pcode. intuition.
        rewrite NMapExtra.update_mapsto_iff. left; auto.
      * simpl in H|-*.
        destruct H as [cprocs [P' [PC Q]]].
        exists cprocs, P', PC; intuition.
        rewrite NMapExtra.update_mapsto_iff. left; auto.
      * simpl in H|-*.
        destruct H. 
        ** left. intuition.
           destruct H4 as [cp Q].
           exists cp; intuition.
           rewrite NMapExtra.update_mapsto_iff. left; auto.
        ** right. unfold imported_procedure in *.
           destruct H as [CI Q].
           exists CI; intuition.
           unfold Program.has_component in *. 
           rewrite NMapExtra.update_mapsto_iff. left; auto.
    - inv H2. destruct WF1. 
      pose proof (wfprog_well_formed_instructions0 _ _ H _ _ H0 _ H1).
      destruct i; auto. 
      * simpl in H2 |-*.  destruct i; auto. 
        destruct H2 as [bufs [Q1 Q2]].
        exists bufs; intuition. 
        rewrite NMapExtra.update_mapsto_iff. right; intuition. 
        eapply BDISJ; split; eauto.
        apply NMapFacts.find_mapsto_iff in Q1.
        apply NMapFacts.in_find_iff.  rewrite Q1; discriminate.
      * simpl in H2 |-*. 
        destruct H2 as [cprocs [pcode Q]].
        exists cprocs, pcode. intuition.
        rewrite NMapExtra.update_mapsto_iff. right; intuition.
      * simpl in H2 |-*.
        destruct H2 as [cprocs [P' [PC Q]]].
        exists cprocs, P', PC; intuition.
        rewrite NMapExtra.update_mapsto_iff. right; intuition.
      * simpl in H2 |-*.
        destruct H2. 
        ** left. intuition.
           destruct H5 as [cp Q].
           exists cp; intuition.
           rewrite NMapExtra.update_mapsto_iff. right; intuition. 
        ** right. unfold imported_procedure in *.
           destruct H2 as [CI Q].
           exists CI; intuition.
           unfold Program.has_component in *. 
           rewrite NMapExtra.update_mapsto_iff. right; intuition. 
           eapply IDISJ; split; eauto.
           apply NMapFacts.find_mapsto_iff in H2. 
           rewrite NMapFacts.in_find_iff. rewrite H2. discriminate.
  + Admitted. (* This obviously isn't true for arbitrary (mainC,mainP) ! *)


Import MonadNotations.
Open Scope monad_scope.

(*
Fixpoint init_mem m bufs :=
  match bufs with
  | [] => m
  | (C, Cbufs) :: bufs' =>
    let m' := NMap.add C (ComponentMemory.prealloc Cbufs) m in
    init_mem m' bufs'
  end.

Fixpoint init_comp_procs m E ps C Cprocs
  : option (Memory.t * EntryPoint.t * NMap.t (NMap.t code)) :=
  match Cprocs with
  | [] => Some (m, E, ps)
  | (P, bytecode) :: Cprocs' =>
    do Cmem <- NMap.find C m;
    let '(Cmem', b) := ComponentMemory.reserve_block Cmem in
    let m' := NMap.add C Cmem' m in
    let Centrypoints :=
        match NMap.find C E with
        | None => NMap.empty Block.id
        | Some old_Centrypoints => old_Centrypoints
        end in
    let Centrypoints' := NMap.add P b Centrypoints in
    let E' := NMap.add C Centrypoints' E in
    let Cps :=
        match NMap.find C ps with
        | None => NMap.empty code
        | Some oldCps => oldCps
        end in
    let Cps' := NMap.add b bytecode Cps in
    let ps' := NMap.add C Cps' ps in
    init_comp_procs m' E' ps' C Cprocs'
  end.

Definition init_all (p: program) :=
  let fix init_all_procs m E ps procs :=
      match procs with
      | [] => Some (m, E, ps)
      | (C, Cprocs) :: procs' =>
        do (m', E', ps') <- init_comp_procs m E ps C (NMap.elements Cprocs);
        init_all_procs m' E' ps' procs'
      end
  in
  let m := init_mem (Memory.empty []) (NMap.elements (prog_buffers p)) in
  init_all_procs m (NMap.empty (NMap.t Block.id)) (NMap.empty (NMap.t code))
                 (NMap.elements (prog_procedures p)).

Definition init
           (p: program) (mainC: Component.id) (mainP: Procedure.id)
  : option (global_env * Memory.t) :=
  do (mem, entrypoints, procs) <- init_all p;
  let G := {| genv_interface := prog_interface p;
              genv_procedures := procs;
              genv_entrypoints := entrypoints |} in
  ret (G, mem).

Definition init_genv
           (p: program) (mainC: Component.id) (mainP: Procedure.id)
  : option global_env :=
  do (G, mem) <- init p mainC mainP;
  ret G.

Definition init_genv_and_state
           (p: program) (mainC: Component.id) (mainP: Procedure.id)
  : option (global_env * state) :=
  do (G, mem) <- init p mainC mainP;
  do b <- EntryPoint.get mainC mainP (genv_entrypoints G);
  ret (G, ([], mem, Register.init, (mainC, b, 0))).
*)

Fixpoint init_component m E ps C Cprocs bufs
  : Memory.t * EntryPoint.t * NMap.t (NMap.t code) :=
  match Cprocs with
  | [] => (m, E, ps)
  | (P, bytecode) :: Cprocs' =>
    let Cmem :=
        match NMap.find C m with
        | Some Cmem => Cmem
        | None =>
          match NMap.find C bufs with
          | Some Cbufs => ComponentMemory.prealloc Cbufs
          (* the following should never happen, since every
             component has at least one buffer *)
          | None => ComponentMemory.empty
          end
        end in
    let '(Cmem', b) := ComponentMemory.reserve_block Cmem in
    let m' := NMap.add C Cmem' m in
    let Centrypoints :=
        match NMap.find C E with
        | None => NMap.empty Block.id
        | Some old_Centrypoints => old_Centrypoints
        end in
    let Centrypoints' := NMap.add P b Centrypoints in
    let E' := NMap.add C Centrypoints' E in
    let Cps :=
        match NMap.find C ps with
        | None => NMap.empty code
        | Some oldCps => oldCps
        end in
    let Cps' := NMap.add b bytecode Cps in
    let ps' := NMap.add C Cps' ps in
    init_component m' E' ps' C Cprocs' bufs
  end.

Definition init_all (p: program)
  : Memory.t * EntryPoint.t * NMap.t (NMap.t code) :=
  let fix init_all_procs m E ps procs :=
      match procs with
      | [] => (m, E, ps)
      | (C, Cprocs) :: procs' =>
        let '(m', E', ps') := init_component m E ps C
                                             (NMap.elements Cprocs)
                                             (prog_buffers p) in
        init_all_procs m' E' ps' procs'
      end
  in
  init_all_procs (Memory.empty [])
                 (NMap.empty (NMap.t Block.id)) (NMap.empty (NMap.t code))
                 (NMap.elements (prog_procedures p)).

Close Scope monad_scope.

End Intermediate.