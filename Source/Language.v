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
    prog_procedures : NMap.t (NMap.t expr);
    prog_buffers : NMap.t nat;
    prog_main : Component.id * Procedure.id
  }.

  Definition only_allowed_calls (p: program) : bool :=
    let fix check_expr cur_comp e :=
        match e with
        | E_val _ => true
        | E_local => true
        | E_binop _ e1 e2 =>
          andb (check_expr cur_comp e1) (check_expr cur_comp e2)
        | E_seq e1 e2 =>
          andb (check_expr cur_comp e1) (check_expr cur_comp e2)
        | E_if e1 e2 e3 =>
          andb (andb (check_expr cur_comp e1) (check_expr cur_comp e2))
               (check_expr cur_comp e3)
        | E_alloc e =>
          check_expr cur_comp e
        | E_deref e =>
          check_expr cur_comp e
        | E_assign e1 e2 =>
          andb (check_expr cur_comp e1) (check_expr cur_comp e2)
        | E_call C' P' e =>
          andb (orb (imported_procedure_b (prog_interface p) cur_comp C' P')
                    (cur_comp =? C'))
               (check_expr cur_comp e)
        | E_exit => true
        end
    in
    let fix check_procedures cur_comp procs :=
        match procs with
        | [] => true
        | (_, e) :: procs' =>
          andb (check_expr cur_comp e) (check_procedures cur_comp procs')
        end
    in
    let fix check_components comps :=
        match comps with
        | [] => true
        | (C, Cprocs) :: comps' =>
          andb (check_procedures C (NMap.elements Cprocs))
               (check_components comps')
        end
    in check_components (NMap.elements (prog_procedures p)).

  Definition required_local_buffers (p: program) : bool :=
    let check_for_comp C :=
        match NMap.find C (prog_buffers p) with
        | Some size => 0 <? size
        | None => false
        end
    in
    let fix check_components comps :=
        match comps with
        | [] => true
        | (C, _) :: comps' =>
          andb (check_for_comp C) (check_components comps')
        end
    in
    check_components (NMap.elements (prog_procedures p)).

  Definition valid_main (p: program) : bool :=
    match NMap.find (fst (prog_main p)) (prog_procedures p) with
    | Some procs => NMap.mem (snd (prog_main p)) procs
    | None => false
    end.

  (* TODO check for interface soundness *)
  Definition well_formed_program (p: program) : bool:=
    (only_allowed_calls p) &&
    (required_local_buffers p) &&
    (valid_main p).

  Fixpoint alloc_buffers
           (bufs: list (Component.id * nat))
           (m: Memory.t) (addrs: NMap.t Block.id)
    : Memory.t * NMap.t Block.id :=
    match bufs with
    | [] => (m, addrs)
    | (C,size)::bufs' =>
      let memC := match NMap.find C m with
                  | Some memC => memC
                  | None => ComponentMemory.empty
                  end in
      let '(memC', b) := ComponentMemory.alloc memC size in
      alloc_buffers bufs' (NMap.add C memC' m) (NMap.add C b addrs)
    end.

  Definition init_all (p: program) : NMap.t Block.id * Memory.t :=
    let pbufs := NMap.elements (prog_buffers p) in
    let init_mem := Memory.empty (map fst pbufs) in
    let '(mem, bufs) := alloc_buffers pbufs init_mem (@NMap.empty Block.id) in
    (bufs, mem).
End Source.