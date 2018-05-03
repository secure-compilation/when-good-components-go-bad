Require Import Common.Definitions.
Require Import Common.Memory.
Require Import Intermediate.Machine.
Require Import Lib.Monads.

Import Intermediate.

Record global_env := mkGlobalEnv {
  genv_interface: Program.interface;
  genv_procedures: NMap (NMap code);
  genv_entrypoints: EntryPoint.t;
}.

Definition executing G (pc : Pointer.t) (i : instr) : Prop :=
  exists C_procs P_code,
    getm (genv_procedures G) (Pointer.component pc) = Some C_procs /\
    getm C_procs (Pointer.block pc) = Some P_code /\
    (Pointer.offset pc >= 0) % Z /\
    nth_error P_code (Z.to_nat (Pointer.offset pc)) = Some i.

Definition prepare_global_env (p: program) : global_env :=
  let mem := prepare_initial_memory p in
  let '(_, procs, entrypoints) := prepare_procedures p mem in
  {| genv_interface := prog_interface p;
     genv_procedures := procs;
     genv_entrypoints := entrypoints |}.

Definition empty_global_env := {|
  genv_interface := emptym;
  genv_procedures := emptym;
  genv_entrypoints := emptym
|}.

Lemma prepare_global_env_empty_prog:
  prepare_global_env empty_prog = empty_global_env.
Proof.
  reflexivity.
Qed.

Lemma genv_procedures_program_link_left_notin :
  forall {c Cid},
    Cid \notin domm (prog_interface c) ->
  forall {p},
    (genv_procedures (prepare_global_env (program_link p c))) Cid =
    (genv_procedures (prepare_global_env p)) Cid.
Admitted. (* Grade 2, check. Possibly add linkability conditions, etc. *)

Lemma genv_entrypoints_program_link_left :
  forall {C P p c b},
    EntryPoint.get C P (genv_entrypoints (prepare_global_env (program_link p c))) = b ->
    C \notin domm (prog_interface c) ->
    EntryPoint.get C P (genv_entrypoints (prepare_global_env p)) = b.
Admitted. (* Grade 2, check. Rephrase in the style of genv_procedures_program_link_left. *)

Fixpoint find_label (c : code) (l : label) : option Z :=
  let fix aux c o :=
      match c with
      | [] => None
      | ILabel l' :: c' =>
        if Nat.eqb l l' then
          Some o
        else
          aux c' (1 + o)%Z
      | _ :: c' =>
        aux c' (1 + o)%Z
      end
  in aux c 0%Z.

Definition find_label_in_procedure G (pc : Pointer.t) (l : label) : option Pointer.t :=
  match getm (genv_procedures G) (Pointer.component pc) with
  | Some C_procs =>
    match getm C_procs (Pointer.block pc) with
    | Some P_code =>
      match find_label P_code l with
      | Some offset => Some (Pointer.component pc, Pointer.block pc, offset)
      | None => None
      end
    | None => None
    end
  | None => None
  end.

Fixpoint find_label_in_component_helper
         G (procs: list (Block.id * code))
         (pc: Pointer.t) (l: label) : option Pointer.t :=
  match procs with
  | [] => None
  | (p_block,p_code) :: procs' =>
    match find_label_in_procedure G (Pointer.component pc, p_block, 0%Z) l with
    | None => find_label_in_component_helper G procs' pc l
    | Some ptr => Some ptr
    end
  end.

Definition find_label_in_component G (pc : Pointer.t) (l : label) : option Pointer.t :=
  match getm (genv_procedures G) (Pointer.component pc) with
  | Some C_procs =>
    find_label_in_component_helper G (elementsm C_procs) pc l
  | None => None
  end.

Lemma find_label_in_procedure_guarantees:
  forall G pc pc' l,
    find_label_in_procedure G pc l = Some pc' ->
    Pointer.component pc = Pointer.component pc' /\
    Pointer.block pc = Pointer.block pc'.
Proof.
  intros G pc pc' l Hfind.
  unfold find_label_in_procedure in Hfind.
  destruct (getm (genv_procedures G) (Pointer.component pc)) as [procs|];
    try discriminate.
  destruct (getm procs (Pointer.block pc)) as [code|];
    try discriminate.
  destruct (find_label code l) as [offset|];
    try discriminate.
  destruct pc'. destruct p.
  inversion Hfind. subst.
  split; reflexivity.
Qed.

Lemma find_label_in_procedure_1:
  forall G pc pc' l,
    find_label_in_procedure G pc l = Some pc' ->
    Pointer.component pc = Pointer.component pc'.
Proof.
  eapply find_label_in_procedure_guarantees.
Qed.

Lemma find_label_in_procedure_2:
  forall G pc pc' l,
    find_label_in_procedure G pc l = Some pc' ->
    Pointer.block pc = Pointer.block pc'.
Proof.
  eapply find_label_in_procedure_guarantees.
Qed.

Lemma find_label_in_procedure_program_link_left:
  forall {p c pc l pc'},
    find_label_in_procedure (prepare_global_env (program_link p c)) pc l = pc' ->
    Pointer.component pc \notin domm (prog_interface c) ->
    find_label_in_procedure (prepare_global_env p) pc l = pc'.
Admitted. (* Grade 2, check. Rephrase in the style of genv_procedures_program_link_left. *)

Lemma find_label_in_component_helper_guarantees:
  forall G procs pc pc' l,
    find_label_in_component_helper G procs pc l = Some pc' ->
    Pointer.component pc = Pointer.component pc'.
Proof.
  intros G procs pc pc' l Hfind.
  induction procs.
  - discriminate.
  - simpl in *.
    destruct a.
    destruct (find_label_in_procedure
                G (Pointer.component pc, i, 0%Z) l)
             eqn:Hfind'.
    + apply find_label_in_procedure_1 in Hfind'.
      simpl in *. inversion Hfind. subst. auto.
    + apply IHprocs; auto.
Qed.

Lemma find_label_in_component_1:
  forall G pc pc' l,
    find_label_in_component G pc l = Some pc' ->
    Pointer.component pc = Pointer.component pc'.
Proof.
  intros G pc pc' l Hfind.
  unfold find_label_in_component in Hfind.
  destruct (getm (genv_procedures G) (Pointer.component pc)) as [procs|];
    try discriminate.
  eapply find_label_in_component_helper_guarantees in Hfind; auto.
Qed.

Lemma find_label_in_component_program_link_left:
  forall {p c pc l pc'},
    find_label_in_component (prepare_global_env (program_link p c)) pc l = pc' ->
    Pointer.component pc \notin domm (prog_interface c) ->
    find_label_in_component (prepare_global_env p) pc l = pc'.
Admitted. (* Grade 2, check. Rephrase in the style of genv_procedures_program_link_left. *)

Lemma execution_invariant_to_linking:
  forall p c1 c2 pc instr,
    linkable (prog_interface p) (prog_interface c1) ->
    linkable (prog_interface p) (prog_interface c2) ->
    well_formed_program p ->
    well_formed_program c1 ->
    well_formed_program c2 ->
    Pointer.component pc \in domm (prog_interface p) ->
    executing (prepare_global_env (program_link p c1)) pc instr ->
    executing (prepare_global_env (program_link p c2)) pc instr.
Proof.
  intros p c1 c2 pc instr Hlinkable1 Hlinkable2 Hwf Hwf1 Hwf2 Hpc Hexec.
  inversion Hexec as [procs [proc [Hgenv_procs [Hprocs_proc [Hoffset Hproc_instr]]]]].
  exists procs, proc.
  split; [| split; [| split]];
    [| assumption | assumption | assumption].
  assert (Pointer.component pc \notin domm (prog_interface c1)) as Hcc1 by admit.
  assert (Pointer.component pc \notin domm (prog_interface c2)) as Hcc2 by admit.
  rewrite (genv_procedures_program_link_left_notin Hcc1) in Hgenv_procs.
  rewrite (genv_procedures_program_link_left_notin Hcc2).
  assumption.
Admitted. (* Grade 1. Easy lemma for the admits. *)