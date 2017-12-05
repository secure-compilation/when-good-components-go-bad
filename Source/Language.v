Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Common.Linking.

Inductive expr : Type :=
| E_val : value -> expr
| E_local : expr
| E_binop : binop -> expr -> expr -> expr
| E_seq : expr -> expr -> expr
| E_if : expr -> expr -> expr -> expr
| E_alloc : expr -> expr
| E_deref : expr -> expr
| E_assign : expr -> expr -> expr
| E_call : Component.id -> Procedure.id -> expr -> expr
| E_exit : expr.

Module Source.
  Record program : Type := mkProg {
    prog_interface : Program.interface;
    prog_procedures : NMap (NMap expr);
    prog_buffers : NMap (nat + list value);
    prog_main : option (Component.id * Procedure.id)
  }.

  (* An expression is well-formed when:
     1) calls outside the component are allowed by the interface
     2) calls inside the component are targeting existing procedures
     3) the undef value is not present
     4) pointers are not present (no pointer forging) *)
  (* AAA: I find the term "well-formed" a bit misleading, because this notion is
     not preserved by evaluation: if the result of an expression is a pointer,
     that result is ill-formed.  We could consider refactoring it as the
     conjunction of two predicates: surface_syntax, asserting that pointers and
     undef do not occur in expressions, and well_formed, asserting that the
     expression respects the interface.  *)
  Fixpoint well_formed_expr (p: program) (cur_comp: Component.id) (e: expr) : Prop :=
    match e with
    | E_val val => exists i, val = Int i
    | E_local => True
    | E_exit => True
    | E_binop op e1 e2 =>
      well_formed_expr p cur_comp e1 /\ well_formed_expr p cur_comp e2
    | E_seq e1 e2 =>
      well_formed_expr p cur_comp e1 /\ well_formed_expr p cur_comp e2
    | E_if e1 e2 e3 =>
      well_formed_expr p cur_comp e1 /\ well_formed_expr p cur_comp e2 /\
      well_formed_expr p cur_comp e3
    | E_alloc e' => well_formed_expr p cur_comp e'
    | E_deref e' => well_formed_expr p cur_comp e'
    | E_assign e1 e2 =>
      well_formed_expr p cur_comp e1 /\ well_formed_expr p cur_comp e2
    | E_call C' P' e' =>
      well_formed_expr p cur_comp e' /\
      (imported_procedure (prog_interface p) cur_comp C' P' \/
       (cur_comp = C' /\
        exists C'procs, getm (prog_procedures p) C' = Some C'procs  /\
                        P' \in domm C'procs))
    end.

  (* Component C has a buffer of size at least one *)
  Definition has_required_local_buffers (p: program) (C: Component.id) : Prop :=
    (exists size, getm (prog_buffers p) C = Some (inl size) /\
                  (size > 0)%nat) \/
    (exists values, getm (prog_buffers p) C = Some (inr values) /\
                  (length values > 0)%nat).

  (** Lookup definition of procedure [C.P] in the map [procs]. *)
  Definition find_procedure
             (procs: NMap (NMap expr))
             (C: Component.id) (P: Procedure.id) : option expr :=
    match getm procs C with
    | Some C_procs => getm C_procs P
    | None         => None
    end.

  Record well_formed_program (p: program) := {
    (* the interface is sound (but maybe not closed) *)
    wfprog_interface_soundness:
      sound_interface (prog_interface p);
    (* each declared component has the required static buffers *)
    wfprog_buffers_existence:
      forall C, C \in domm (prog_interface p) ->
                has_required_local_buffers p C;
    (* each exported procedure is actually defined *)
    wfprog_exported_procedures_existence:
      forall C P, exported_procedure (prog_interface p) C P ->
      exists Pexpr, find_procedure (prog_procedures p) C P = Some Pexpr;
    (* each instruction of each procedure is well-formed *)
    wfprog_well_formed_procedures:
      forall C P Pexpr,
        find_procedure (prog_procedures p) C P = Some Pexpr ->
        well_formed_expr p C Pexpr;
    (* if the main component exists, then the main procedure must exist as well *)
    wfprog_main_existence:
      forall mainC mainP main_procs,
        prog_main p = Some (mainC, mainP) ->
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
        fdisjoint (domm (prog_buffers prog1)) (domm (prog_buffers prog2)) ->
        linkable_mains (prog_main prog1) (prog_main prog2) ->
        linkable_programs prog1 prog2.

  Definition program_link (p1 p2: program) : program :=
    {| prog_interface := unionm (prog_interface p1) (prog_interface p2);
       prog_procedures := unionm (prog_procedures p1) (prog_procedures p2);
       prog_buffers := unionm (prog_buffers p1) (prog_buffers p2);
       prog_main := main_link (prog_main p1) (prog_main p2) |}.

  Fixpoint initialize_buffer
           (Cmem: ComponentMemory.t) (b: Block.id) (values: list value)
    : ComponentMemory.t :=
    let fix init m vs i :=
        match vs with
        | [] => m
        | v :: vs' =>
          match ComponentMemory.store m b i v with
          | Some m' =>
            init m' vs' (1+i)%Z
          | None =>
            (* bad case that shouldn't happen, just return memory *)
            init m vs' (1+i)%Z
          end
        end
    in init Cmem values 0%Z.

  Definition prepare_buffers (p: program) : Memory.t * NMap Block.id :=
    let fix alloc mem addrs bufs :=
        match bufs with
        | [] => (mem, addrs)
        | (C, init) :: bufs' =>
          match init with
          | inl size =>
            let '(Cmem', b) := ComponentMemory.alloc ComponentMemory.empty size in
            alloc (setm mem C Cmem') (setm addrs C b) bufs'
          | inr values =>
            let '(Cmem', b) := ComponentMemory.alloc ComponentMemory.empty
                                                     (length values) in
            let Cmem'' := initialize_buffer Cmem' b values in
            alloc (setm mem C Cmem'') (setm addrs C b) bufs'
          end
        end
    in
    alloc emptym emptym (elementsm (prog_buffers p)).
End Source.
