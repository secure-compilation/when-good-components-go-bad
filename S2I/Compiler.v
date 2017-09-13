Require Import Common.Definitions.
Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import S2I.CompMonad.

Import MonadNotations.
Open Scope monad_scope.

(* the compilation environment *)

Record comp_env : Type := {
  next_label: label;
  current_component : Component.id;
  local_buffers : ZMap.t (list Block.id);
  procs_labels : ZMap.t (ZMap.t label)
}.

(* easy environments updates *)

Definition with_next_label l env :=
  {| next_label := l;
     current_component := current_component env;
     local_buffers := local_buffers env;
     procs_labels := procs_labels env |}.

Definition with_current_component C env :=
  {| next_label := next_label env;
     current_component := C;
     local_buffers := local_buffers env;
     procs_labels := procs_labels env |}.

Definition with_component_buffers C bufs env :=
  {| next_label := next_label env;
     current_component := current_component env;
     local_buffers := ZMap.add C bufs (local_buffers env);
     procs_labels := procs_labels env |}.

Definition with_new_proc_label C P l env :=
  {| next_label := next_label env;
     current_component := current_component env;
     local_buffers := local_buffers env;
     procs_labels :=
       let proc_labels' :=
           match ZMap.find C (procs_labels env) with
           | None => ZMap.add P l (@ZMap.empty label)
           | Some labels => ZMap.add P l labels
           end
       in ZMap.add C proc_labels' (procs_labels env) |}.

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
  do! modify (with_next_label (1+l));
  ret l.

Definition get_local_buffer : COMP Pointer.t :=
  do cenv <- get;
  let C := current_component cenv in
  do blocks <- lift (ZMap.find C (local_buffers cenv));
  do b <- lift (nth_error blocks 0);
  ret (C, b, 0).

Definition get_temp_buffer : COMP Pointer.t:=
  do cenv <- get;
  let C := current_component cenv in
  do blocks <- lift (ZMap.find C (local_buffers cenv));
  do b <- lift (nth_error blocks (length blocks - 1));
  ret (C, b, 0).

Definition find_proc_label C P : COMP label :=
  do cenv <- get;
  do P_labels <- lift (ZMap.find C (procs_labels cenv));
  lift (ZMap.find P P_labels).

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

Definition store_arg (buf: Pointer.t) (r r': register) : code :=
  [IConst (IPtr buf) r';
   IStore r' r].

Definition store_stack_frame_pointer (buf: Pointer.t) (r: register) : code :=
  [IConst (IPtr buf) r;
   IStore r R_SP].

Definition restore_stack_frame_pointer (buf: Pointer.t) : code :=
  [IConst (IPtr buf) R_SP;
   ILoad R_SP R_SP].

Definition store_environment (buf: Pointer.t) : code :=
  store_stack_frame_pointer buf R_AUX1.

Definition restore_environment (buf: Pointer.t) : code :=
  IConst (IInt 1) R_ONE ::
  restore_stack_frame_pointer buf.

Fixpoint compile_expr (e: expr) : COMP code :=
  match e with
  | E_val (Int i) =>
    ret [IConst (IInt i) R_COM]
  | E_val (Ptr p) =>
    ret [IConst (IPtr p) R_COM]
  | E_val Undef => fail (* we don't compile undef *)
  | E_local =>
    do local_buf_ptr <- get_local_buffer;
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
    do cenv <- get;
    let C := current_component cenv in
    do local_buf_ptr <- get_local_buffer;
    do call_arg_code <- compile_expr e;
    if C' =? C then
      do target_label <- find_proc_label C' P';
      ret (call_arg_code ++
           push R_AUX2 ++
           load_arg local_buf_ptr R_AUX1 ++
           push R_AUX1 ++
           [IJal target_label] ++
           pop R_AUX1 ++
           store_arg local_buf_ptr R_AUX1 R_AUX2 ++
           pop R_AUX2)
    else
      do temp_buf_ptr <- get_temp_buffer;
      ret (call_arg_code ++
           push R_AUX2 ++
           load_arg local_buf_ptr R_AUX1 ++
           push R_AUX1 ++
           store_environment temp_buf_ptr ++
           [ICall C' P'] ++
           restore_environment temp_buf_ptr ++
           pop R_AUX1 ++
           store_arg local_buf_ptr R_AUX1 R_AUX2 ++
           pop R_AUX2)
  | E_exit => ret [IHalt]
  end.

Definition compile_proc
           (C: Component.id) (P: Procedure.id) (e: expr)
  : COMP code :=
  do! modify (with_current_component C);
  do proc_label <- find_proc_label C P;
  do local_buf_ptr <- get_local_buffer;
  do lmain <- fresh_label;
  do lreturn <- fresh_label;
  do proc_code <- compile_expr e;
  (* TODO compute stack size *)
  let stack_frame_size := 10 in
  ret ([IConst (IInt 1) R_ONE;
        IConst (IInt 1) R_AUX2;
        IConst (IInt stack_frame_size) R_SP;
        IAlloc R_SP R_SP;
        IBnz R_ONE lmain;
        ILabel proc_label;
        IConst (IInt 0) R_AUX2;
        IMov R_SP R_AUX1;
        IConst (IInt stack_frame_size) R_SP;
        IAlloc R_SP R_SP] ++
        push R_AUX1 ++
       [ILabel lmain] ++
        push R_RA ++
        store_arg local_buf_ptr R_COM R_AUX1 ++
        proc_code ++
        pop R_RA ++
       [IBnz R_AUX2 lreturn] ++
        pop R_SP ++
       [IJump R_RA;
        ILabel lreturn;
        IReturn]).

Fixpoint gen_component_procedures_labels
         (C: Component.id) (procs: list (Procedure.id * expr))
  : COMP unit :=
  match procs with
  | [] => ret tt
  | (P, _) :: procs' =>
    do freshl <- fresh_label;
    do! modify (with_new_proc_label C P freshl);
    gen_component_procedures_labels C procs'
  end.

(* think about labels collision when linking partial programs *)
Fixpoint gen_all_procedures_labels
         (procs: list (Component.id * ZMap.t expr))
  : COMP unit :=
  match procs with
  | [] => ret tt
  | (C, Cprocs) :: procs' =>
    do! gen_component_procedures_labels C (ZMap.elements Cprocs);
    gen_all_procedures_labels procs'
  end.

Fixpoint add_temporary_buffers
         (bufs: list (Component.id * nat))
  : COMP (ZMap.t (list (Block.id * nat))) :=
  let fix instrument acc bs :=
      match bs with
      | [] => ret acc
      | (C,size) :: bs' =>
        let Cbufs := [(0,size%nat); (1,1%nat)] in
        let acc' := ZMap.add C Cbufs acc in
        do! modify (with_component_buffers C (map fst Cbufs));
        instrument acc' bs'
      end
  in instrument (ZMap.empty (list (Block.id * nat))) bufs.

Fixpoint compile_procedures
         (C: Component.id)
         (procs: list (Procedure.id * expr))
  : COMP (list (Procedure.id * code)) :=
  let fix compile acc ps :=
      match ps with
      | [] => ret acc
      | (P,e) :: ps' =>
        do proc_code <- compile_proc C P e;
        let acc' := (P,proc_code) :: acc in
        compile acc' ps'
      end
  in compile [] procs.

Fixpoint compile_components
         (comps: list (Component.id * ZMap.t expr))
  : COMP (list (Component.id * ZMap.t code)) :=
  let fix compile acc cs :=
      match cs with
      | [] => ret acc
      | (C,procs) :: cs' =>
        do procs_code <- compile_procedures C (ZMap.elements procs);
        let acc' := (C, ZMapExtra.of_list procs_code) :: acc in
        compile acc' cs'
      end
  in compile [] comps.

Definition init_env : comp_env :=
  {| next_label := 0;
     current_component := 0;
     local_buffers := @ZMap.empty (list Block.id);
     procs_labels := @ZMap.empty (ZMap.t label) |}.

Definition compile_program
           (p: Source.program) : option Intermediate.program :=
  let procs := ZMap.elements (Source.prog_procedures p) in
  let bufs := ZMap.elements (Source.prog_buffers p) in
  run init_env (
    do! gen_all_procedures_labels procs;
    do bufs' <- add_temporary_buffers bufs;
    do code <- compile_components procs;
    ret {| Intermediate.prog_interface := Source.prog_interface p;
           Intermediate.prog_procedures := ZMapExtra.of_list code;
           Intermediate.prog_buffers := bufs';
           Intermediate.prog_main := Source.prog_main p |}).