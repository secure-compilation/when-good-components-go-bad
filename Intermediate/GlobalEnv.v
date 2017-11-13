Require Import Common.Definitions.
Require Import Common.Memory.
Require Import Intermediate.Machine.
Require Import Lib.Monads.

Import Intermediate.

Record global_env := mkGlobalEnv {
  genv_interface: Program.interface;
  genv_procedures: PMap.t (PMap.t code);
  genv_entrypoints: EntryPoint.t;
}.

Record well_formed_global_env (G: global_env) := {
  (* the interface is sound (but maybe not closed) *)
  wfgenv_interface_soundness:
    sound_interface (genv_interface G);
  (* the entrypoints and the interface are in sync *)
  wfgenv_entrypoints_soundness:
    forall C, PMap.In C (genv_entrypoints G) <-> PMap.In C (genv_interface G);
  (* the procedures and the interface are in sync *)
  wfgenv_procedures_soundness:
    forall C, PMap.In C (genv_procedures G) <-> PMap.In C (genv_interface G)
}.

Definition executing G (pc : Pointer.t) (i : instr) : Prop :=
  exists C_procs P_code,
    PMap.find (Pointer.component pc) (genv_procedures G) = Some C_procs /\
    PMap.find (Pointer.block pc) C_procs = Some P_code /\
    Pointer.offset pc >= 0 /\
    nth_error P_code (Z.to_nat (Pointer.offset pc)) = Some i.

Fixpoint find_label (c : code) (l : label) : option Z :=
  let fix aux c o :=
      match c with
      | [] => None
      | ILabel l' :: c' =>
        if Pos.eqb l l' then
          Some o
        else
          aux c' (1+o)
      | _ :: c' =>
        aux c' (1+o)
      end
  in aux c 0.

Definition find_label_in_procedure G (pc : Pointer.t) (l : label) : option Pointer.t :=
  match PMap.find (Pointer.component pc) (genv_procedures G) with
  | Some C_procs =>
    match PMap.find (Pointer.block pc) C_procs with
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
    match find_label_in_procedure G (Pointer.component pc, p_block, 0) l with
    | None => find_label_in_component_helper G procs' pc l
    | Some ptr => Some ptr
    end
  end.

Definition find_label_in_component G (pc : Pointer.t) (l : label) : option Pointer.t :=
  match PMap.find (Pointer.component pc) (genv_procedures G) with
  | Some C_procs =>
    find_label_in_component_helper G
                                   (PMap.elements C_procs)
                                   pc l
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
  destruct (PMap.find (Pointer.component pc)
                      (genv_procedures G)) as [procs|];
    try discriminate.
  destruct (PMap.find (Pointer.block pc) procs) as [code|];
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
                G (Pointer.component pc, i, 0) l)
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
  destruct (PMap.find (Pointer.component pc)
                      (genv_procedures G)) as [procs|];
    try discriminate.
  eapply find_label_in_component_helper_guarantees in Hfind; auto.
Qed.

Definition init_genv (p: program) : global_env :=
  let '(m, E, ps) := init_all p in
  {| genv_interface := prog_interface p;
     genv_procedures := ps;
     genv_entrypoints := E |}.