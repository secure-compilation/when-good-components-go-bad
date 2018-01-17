(*
The calling conventions adepted is described as follows:

Main ideas:

1. The external entry point has jal to the internal entrypoint.
   This simplifies the code, although it does result in one needless but
   harmless push/pop for external calls.
2. We use a single static buffer per component to store both the
   current proc arg (when executing in the component) and the saved sp
   (when executing in a different component).

In the following:
- We write B_C for the (sole) static buffer (of size 1) associated with component C
- Each procedure has an external entry point (accessed by ICall) and an internal entry label.

Internal caller (within same component):
  push R_RA
  Jal to callee internal label
  pop into R_RA

External caller (between components):
  push R_RA
  push contents of B_C (caller's arg)
  store R_SP into B_C
  ICall C' P'
  set R_ONE = 1
  set R_SP to contents of B_C
  pop caller's arg into B_C
  pop into R_RA

Code at external entry point:
  set R_ONE = 1
  IJal internal_entry_label
  IReturn

Code at internal entry label:
  save R_SP to R_AUX1
  allocate stack frame for this procedure, pointed to by R_SP
  push R_AUX1 (old R_SP) [for an external call this is random garbage, but harmless]
  push contents of B_C [for an internal call, this is caller's arg; for an external call, this is SP at point when callee component last called externally]
  store R_COM into B_C
  ...body of function...
  pop into B_C
  pop into R_SP [for an external call this is pointless, but harmless]
  [if we did stack frame deallocation, it would happen here]
  IJump R_RA
*)

Require Import Common.Definitions.
Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import S2I.CompMonad.

Import MonadNotations.
Open Scope monad_scope.

(* the compilation environment *)

Record comp_env : Type := {
  next_label: label;
}.

(* easy environments updates *)

Definition with_next_label l (env:comp_env) :=
  {| next_label := l; |}.

(* simplify notations *)

Notation COMP := (Comp.t comp_env).
Notation get := (Comp.get comp_env).
Notation put := (Comp.put comp_env).
Notation modify := (Comp.modify comp_env).
Notation lift := (Comp.lift comp_env).
Notation fail := (Comp.fail comp_env).
Notation run := (Comp.run comp_env).

(* auxiliary environment operations *)

Definition fresh_label : COMP label :=
  do cenv <- get;
  let l := next_label cenv in
  do! modify (with_next_label (1 + l));
  ret l.

(* code generation *)

Definition push (r: register) : code :=
  [IStore R_SP r;
   IBinOp Add R_SP R_ONE R_SP].

Definition pop (r: register) : code :=
  [IBinOp Minus R_SP R_ONE R_SP;
   ILoad R_SP r].

Definition load_arg (buf: Pointer.t) (r: register) : code :=
  [IConst (IPtr buf) r;
   ILoad r r].

Definition store_arg (buf: Pointer.t) (r rtemp: register) : code :=
  [IConst (IPtr buf) rtemp;
   IStore rtemp r].

Section WithComponent.

Variable C: Component.id. (* the current component *)
Variable local_buf_ptr : Pointer.t. (* pointer to the local buffer for current component *)
Variable P_labels : NMap label.  (* map from procedure id's to start labels for current component *)

Definition find_proc_label P : COMP label :=
  lift (getm P_labels P).

Fixpoint compile_expr (e: expr) : COMP code :=
  match e with
  | E_val (Int i) =>
    ret [IConst (IInt i) R_COM]
  | E_val (Ptr p) =>
    ret [IConst (IPtr p) R_COM]
  | E_val Undef => fail (* we don't compile undef *)
  | E_local =>
    ret [IConst (IPtr local_buf_ptr) R_COM]
  | E_binop bop e1 e2 =>
    do c1 <- compile_expr e1;
    do c2 <- compile_expr e2;
    ret (c1 ++
         push R_COM ++
         c2 ++
         pop R_AUX1 ++
         IBinOp bop R_AUX1 R_COM R_COM :: nil)
  | E_seq e1 e2 =>
    do c1 <- compile_expr e1;
    do c2 <- compile_expr e2;
    ret (c1 ++ c2)
  | E_if e1 e2 e3 =>
    do c1 <- compile_expr e1;
    do c2 <- compile_expr e2;
    do c3 <- compile_expr e3;
    do lconseq <- fresh_label;
    do lend <- fresh_label;
    ret (c1 ++
         [IBnz R_COM lconseq] ++
         c3 ++
         [IBnz R_ONE lend;
          ILabel lconseq] ++
         c2 ++
         ILabel lend :: nil)
  | E_alloc e =>
    do c <- compile_expr e;
    ret (c ++
         IAlloc R_COM R_COM :: nil)
  | E_deref e =>
    do c <- compile_expr e;
    ret (c ++
         ILoad R_COM R_COM :: nil)
  | E_assign e1 e2 =>
    do c1 <- compile_expr e1;
    do c2 <- compile_expr e2;
    ret (c1 ++
         push R_COM ++
         c2 ++
         pop R_AUX1 ++
         IStore R_COM R_AUX1 :: nil)
  | E_call C' P' e =>
    do call_arg_code <- compile_expr e;
    if Component.eqb C' C then
      do target_label <- find_proc_label P';
      ret (call_arg_code ++
           push R_RA ++
           [IJal target_label] ++
           pop R_RA)
    else
      ret (call_arg_code ++
           push R_RA ++
           load_arg local_buf_ptr R_AUX1 ++
           push R_AUX1 ++
           store_arg local_buf_ptr R_SP R_AUX2 ++
           [ICall C' P'] ++
           [IConst (IInt 1) R_ONE] ++
           load_arg local_buf_ptr R_SP ++
           pop R_AUX1 ++
           store_arg local_buf_ptr R_AUX1 R_AUX2 ++
           pop R_RA
           )
  | E_exit => ret [IHalt]
  end.

Definition compile_proc (P: Procedure.id) (e: expr)
  : COMP code :=
  do proc_label <- find_proc_label P;
  do lmain <- fresh_label;
  do lreturn <- fresh_label;
  do proc_code <- compile_expr e;
  let stack_frame_size := 20%Z in
  ret ([IConst (IInt 1) R_ONE;
        IJal proc_label;
        IReturn;
        ILabel proc_label;
        IMov R_SP R_AUX1;
        IConst (IInt stack_frame_size) R_SP;
        IAlloc R_SP R_SP] ++
        push R_AUX1 ++
        load_arg local_buf_ptr R_AUX1 ++
        push R_AUX1 ++
        store_arg local_buf_ptr R_COM R_AUX2 ++
        proc_code ++
        pop R_AUX1 ++
        store_arg local_buf_ptr R_AUX1 R_AUX2 ++
        pop R_SP ++
        [IJump R_RA]).

Definition compile_procedures
         (procs: list (Procedure.id * expr))
  : COMP (list (Procedure.id * code)) :=
  let fix compile acc ps :=
      match ps with
      | [] => ret acc
      | (P,e) :: ps' =>
        do proc_code <- compile_proc P e;
        let acc' := (P,proc_code) :: acc in
        compile acc' ps'
      end
  in compile [] procs.

End WithComponent.

Definition gen_component_procedures_labels
         (procs: list (Procedure.id * expr))
  : COMP (NMap label) :=
  let fix gen acc procs :=
      match procs with
      | [] => ret acc
      | (P, _) :: procs' =>
        do freshl <- fresh_label;
        gen (setm acc P freshl) procs'
      end
  in gen emptym procs.

Definition gen_all_procedures_labels
         (procs: list (Component.id * NMap expr))
  : COMP (NMap (NMap label)) :=
  let fix gen acc procs :=
      match procs with
      | [] => ret acc
      | (C, Cprocs) :: procs' =>
        do map <- gen_component_procedures_labels (elementsm Cprocs);
        gen (setm acc C map) procs'
      end
  in gen emptym procs.

Definition gen_buffers
         (bufs: {fmap Component.id -> nat + list value})
  : NMap {fmap Block.id -> nat + list value} :=
  mapm (fun init_info => mkfmap [(0, init_info)]) bufs.

Definition compile_components
         (local_buffers : NMap {fmap Block.id -> nat + list value})
         (procs_labels : NMap (NMap label))
         (comps: list (Component.id * NMap expr))
  : COMP (list (Component.id * NMap code)) :=
  let fix compile acc cs :=
      match cs with
      | [] => ret acc
      | (C,procs) :: cs' =>
        do blocks <- lift (getm local_buffers C);
        do local_buf <- lift (nth_error blocks 0);
        do P_labels <- lift (getm procs_labels C);
        do procs_code <- compile_procedures C (C, fst local_buf, 0%Z) P_labels
                                            (elementsm procs);
        let acc' := (C, mkfmap procs_code) :: acc in
        compile acc' cs'
      end
  in compile [] comps.

Definition init_env : comp_env :=
  {| next_label := 1; |}.

(* In intermediate program, main will be a tiny wrapper routine (in the same component)
   that simply calls the  (translation of the) original main and then halts. *)

(* A fresh procedure id can be calculated by, e.g., taking the max of all procedure id's and adding 1 *)

Definition generate_fresh_procedure_id (procs: NMap (NMap code)) : Procedure.id :=
  let max_id ps := fold_left (fun id P => Nat.max id (fst P)) (elementsm ps) 0 in
  Nat.succ (fold_left (fun id C => Nat.max id (max_id (snd C))) (elementsm procs) 0).

Lemma generate_fresh_procedure_id_fresh:
  forall procs,
    generate_fresh_procedure_id procs \in domm procs = false.
Proof.
Admitted.

Definition wrap_main (procs_labels: NMap (NMap label)) (p: Intermediate.program) : COMP Intermediate.program :=
  match p.(Intermediate.prog_main) with
  | Some (C, P) =>
    do iface <- lift (getm p.(Intermediate.prog_interface) C);
    do procs <- lift (getm p.(Intermediate.prog_procedures) C);
    do P_labels <- lift (getm procs_labels C);
    do lab <- lift (getm P_labels P);
    let P' := generate_fresh_procedure_id (p.(Intermediate.prog_procedures)) in
    let iface' :=  {| Component.export := fsetU (fset1 P') iface.(Component.export);
                      Component.import := iface.(Component.import) |} in
    let procs' := setm procs P' [IConst (IInt 1) R_ONE; IJal lab ; IHalt] in
    ret {| Intermediate.prog_interface := setm p.(Intermediate.prog_interface) C iface';
           Intermediate.prog_procedures := setm p.(Intermediate.prog_procedures) C procs';
           Intermediate.prog_buffers := p.(Intermediate.prog_buffers);
           Intermediate.prog_main := Some (C, P') |}
  | None => ret p
  end.

Definition compile_program
           (p: Source.program) : option Intermediate.program :=
  let comps := elementsm (Source.prog_procedures p) in
  let bufs := Source.prog_buffers p in
  let local_buffers := gen_buffers bufs in
  run init_env (
    do procs_labels <- gen_all_procedures_labels comps;
    do code <- compile_components local_buffers procs_labels comps;
    let p :=
        {| Intermediate.prog_interface := Source.prog_interface p;
           Intermediate.prog_procedures := mkfmap code;
           Intermediate.prog_buffers := local_buffers;
           Intermediate.prog_main := Source.prog_main p |} in
   wrap_main procs_labels p).
