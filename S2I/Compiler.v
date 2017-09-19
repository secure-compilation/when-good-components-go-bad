Require Import Common.Definitions.
Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import S2I.CompMonad.

Import MonadNotations.
Open Scope monad_scope.

(* the compilation environment *)

Record comp_env : Type := {
  next_label: label;
  (* facts about this? *)
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
  do! modify (with_next_label (1+l)%positive);
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

Section WithComponent.

Variable C: Component.id. (* the current component *)  
Variable local_buf_ptr : Pointer.t. (* pointer to the local buffer for current component *)
Variable temp_buf_ptr : Pointer.t.  (* pointer to the temp buffer for current component. *)
Variable P_labels : PMap.t label.  (* map from procedure id's to start labels for current component *)

Definition find_proc_label P : COMP label :=
  lift (PMap.find P P_labels).

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
    if Pos.eqb C' C then
      do target_label <- find_proc_label P';
      ret (call_arg_code ++
           push R_AUX2 ++
           load_arg local_buf_ptr R_AUX1 ++
           push R_AUX1 ++
           [IJal target_label] ++
           pop R_AUX1 ++
           store_arg local_buf_ptr R_AUX1 R_AUX2 ++
           pop R_AUX2)
    else
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


Definition compile_proc (P: Procedure.id) (e: expr)
  : COMP code :=
  do proc_label <- find_proc_label P;
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
  : COMP (PMap.t label) :=
  let fix gen acc procs := 
      match procs with
      | [] => ret acc 
      | (P, _) :: procs' =>
        do freshl <- fresh_label;
          gen (PMap.add P freshl acc) procs'
      end
  in gen (@PMap.empty label) procs.

(* think about labels collision when linking partial programs *)
Definition gen_all_procedures_labels
         (procs: list (Component.id * PMap.t expr))
  : COMP (PMap.t (PMap.t label)) :=
  let fix gen acc procs := 
      match procs with
      | [] => ret acc 
      | (C, Cprocs) :: procs' =>
        do map <- gen_component_procedures_labels (PMap.elements Cprocs);
          gen (PMap.add C map acc) procs'
      end
  in gen (@PMap.empty (PMap.t label)) procs.

Definition add_temporary_buffers
         (bufs: list (Component.id * nat))
  : PMap.t (list (Block.id * nat)) :=
  let fix instrument acc bs :=
      match bs with
      | [] => acc
      | (C,size) :: bs' =>
        let Cbufs := [(1%positive,size%nat); (2%positive,1%nat)] in
        let acc' := PMap.add C Cbufs acc in
        instrument acc' bs'
      end
  in instrument (PMap.empty (list (Block.id * nat))) bufs.

Definition compile_components
         (local_buffers : PMap.t (list (Block.id * nat)))
         (procs_labels : PMap.t (PMap.t label))
         (comps: list (Component.id * PMap.t expr))
  : COMP (list (Component.id * PMap.t code)) :=
  let fix compile acc cs :=
      match cs with
      | [] => ret acc
      | (C,procs) :: cs' =>
        do blocks <- lift (PMap.find C local_buffers);
        do local_buf <- lift (nth_error blocks 0);
        do tmp_buf <- lift (nth_error blocks (length blocks - 1));
        do P_labels <- lift (PMap.find C procs_labels);
        do procs_code <- compile_procedures C (C,fst local_buf,0%Z) (C,fst tmp_buf,0%Z) P_labels (PMap.elements procs);
        let acc' := (C, PMapExtra.of_list procs_code) :: acc in
        compile acc' cs'
      end
  in compile [] comps.

Definition init_env : comp_env :=
  {| next_label := 1%positive; |}.


(* In intermediate program, main will be a tiny wrapper routine (in the same component) 
   that simply calls the  (translation of the) original main and then halts. *)

(* A fresh procedure id can be calculated by, e.g., taking the max of all procedure id's and adding 1 *)
Axiom generate_fresh_procedure_id : forall (procs: PMap.t (PMap.t code)), Procedure.id. 

Definition wrap_main (procs_labels: PMap.t (PMap.t label)) (p: Intermediate.program) : COMP Intermediate.program :=
  let '(C,P) := p.(Intermediate.prog_main) in
  do iface <- lift (PMap.find C p.(Intermediate.prog_interface));
  do procs <- lift (PMap.find C p.(Intermediate.prog_procedures));     
  do P_labels <- lift (PMap.find C procs_labels); 
  do lab <- lift (PMap.find P P_labels);
  let P' := generate_fresh_procedure_id (p.(Intermediate.prog_procedures)) in
  let iface' :=  {| Component.export := P'::iface.(Component.export);
                    Component.import := iface.(Component.import) |} in
  let procs' := PMap.add P' [IJal lab ; IHalt] procs in
  ret 
      {| Intermediate.prog_interface := PMap.add C iface' p.(Intermediate.prog_interface);
         Intermediate.prog_procedures := PMap.add C procs' p.(Intermediate.prog_procedures);
         Intermediate.prog_buffers := p.(Intermediate.prog_buffers);
         Intermediate.prog_main := (C,P') |}
.

Definition compile_program
           (p: Source.program) : option Intermediate.program :=
  let comps := PMap.elements (Source.prog_procedures p) in
  let bufs := PMap.elements (Source.prog_buffers p) in
  let local_buffers := add_temporary_buffers bufs in  
  run init_env (
    do procs_labels <- gen_all_procedures_labels comps;
    do code <- compile_components local_buffers procs_labels comps;
    let p := 
        {| Intermediate.prog_interface := Source.prog_interface p;
           Intermediate.prog_procedures := PMapExtra.of_list code;
           Intermediate.prog_buffers := local_buffers;
           Intermediate.prog_main := Source.prog_main p |} in
   wrap_main procs_labels p).
