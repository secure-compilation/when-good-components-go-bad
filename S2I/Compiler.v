(*
The calling conventions are roughly the following:

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
  push contents of R_ARG (caller's arg)
  store R_SP into B_C
  ICall C' P'
  set R_ONE = 1
  set R_SP to contents of B_C
  pop caller's arg into R_ARG
  pop into R_RA

Code at external entry point:
  set R_ONE = 1
  IJal internal_entry_label
  IReturn

Code at internal entry label:
  save R_SP to R_AUX1
  allocate stack frame for this procedure, pointed to by R_SP
  push R_AUX1 (old R_SP) [for an external call this is random garbage, but harmless]
  push contents of B_C [for an internal call, this is random garbage, but harmless.
                        for an external call, this is SP at point when callee component
                        last called externally]
  push R_ARG [caller argument]
  move R_COM to R_ARG
  ...body of function...
  pop into R_ARG
  pop into B_C
  pop into R_SP [for an external call this is pointless, but harmless]
  [if we did stack frame deallocation, it would happen here]
  IJump R_RA
*)

Require Import Common.Definitions.
Require Import Common.CompCertExtensions.
Require Import Common.RenamingOption.
Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import Intermediate.CSInvariants.
Require Import S2I.CompMonad.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import S2I.Definitions.

Import MonadNotations.
Open Scope monad_scope.

(* the compilation environment *)

Record comp_env : Type := {
  next_label: NMap label;
}.

(* easy environments updates *)

Definition with_next_label (comp: Component.id) l (env:comp_env) : comp_env :=
  {| next_label := setm (next_label env) comp l |}.

(* simplify notations *)

Notation COMP := (Comp.t comp_env).
Notation get := (Comp.get comp_env).
Notation put := (Comp.put comp_env).
Notation modify := (Comp.modify comp_env).
Notation lift := (Comp.lift comp_env).
Notation fail := (Comp.fail comp_env).
Notation run := (Comp.run comp_env).

(* auxiliary environment operations *)

Definition fresh_label (comp: Component.id) : COMP label :=
  do cenv <- get;
  match getm (next_label cenv) comp with
  | None =>
    do! modify (with_next_label comp 1);
    ret 0
  | Some l =>
    do! modify (with_next_label comp (1 + l));
    ret l
  end.

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
  | E_arg =>
    ret [IMov R_ARG R_COM]
  | E_local =>
    ret [IConst (IPtr local_buf_ptr) R_COM]
  | E_binop bop e1 e2 =>
    do c1 <- compile_expr e1;
    do c2 <- compile_expr e2;
    ret (c2 ++
         push R_COM ++ (* compute right operand, store it on the stack*)
         c1 ++ (* compute left operand, /don't/ store it on the stack *)
         pop R_AUX1 ++ (* get back the operand from the stack *)
         IBinOp bop R_AUX1 R_COM R_COM :: nil) (* do the operation *)
  | E_seq e1 e2 =>
    do c1 <- compile_expr e1;
    do c2 <- compile_expr e2;
    ret (c1 ++ c2)
  | E_if e1 e2 e3 =>
    do c1 <- compile_expr e1;
    do c2 <- compile_expr e2;
    do c3 <- compile_expr e3;
    do lconseq <- fresh_label C;
    do lend <- fresh_label C;
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
    ret (c2 ++
         push R_COM ++ (* compute argument first, store it in the stack. *)
         c1 ++ (* then compute ptr, /don't/ store it in the stack *)
         pop R_AUX1 ++ (* pop the stack into R_AUX to get back the argument *)
         IStore R_COM R_AUX1 ::
         IMov R_AUX1 R_COM :: (* write back the argument into R_COM *)
         nil)
  | E_call C' P' e =>
    do call_arg_code <- compile_expr e;
    if Component.eqb C' C then
      do target_label <- find_proc_label P';
      ret (call_arg_code ++
           push R_RA ++
           [IJal target_label] ++
           pop R_RA)
          (** NOTE: When the callee is internal, we do not need to save R_ARG because *)
          (** the callee will follow the convention and save it for us.               *)
    else
      (** However, when the callee is external, we save R_ARG ourselves. The callee *)
      (** can fail to follow the convention.                                        *)
      ret (call_arg_code ++
           push R_RA ++
           push R_ARG ++
           store_arg local_buf_ptr R_SP R_AUX2 ++
           [ICall C' P'] ++
           [IConst (IInt 1) R_ONE] ++
           load_arg local_buf_ptr R_SP ++
           pop R_ARG ++
           pop R_RA
          )
  | E_funptr P' =>
    do target_label <- find_proc_label P';
    ret [IPtrOfLabel target_label R_COM]
  | E_callptr eptr earg =>
    do call_arg_code <- compile_expr earg;
    do ptr_code <- compile_expr eptr;
    do ret_label <- fresh_label C;
    ret (call_arg_code ++         (* value of arg is in R_COM *)
         push R_COM ++            (* value of arg is on top of the stack *)
         ptr_code ++              (* value of the callee ptr is in R_COM *)
         [IMov R_COM R_AUX1] ++   (* value of the callee ptr is in R_AUX1 *)
         pop R_COM ++             (* value of arg is popped, and is now in R_COM *)
                                  (* as expected by the prologue (see compile_proc) *)
         push R_RA ++
         [IPtrOfLabel ret_label R_RA] ++
         [IJumpFunPtr R_AUX1] ++
         [ILabel ret_label] ++
         pop R_RA)
  | E_exit => ret [IHalt]
  end.

Definition compile_proc (P: Procedure.id) (e: expr)
  : COMP code :=
  do proc_label <- find_proc_label P;
  do lmain <- fresh_label C;
  do lreturn <- fresh_label C;
  do proc_code <- compile_expr e;
  let stack_frame_size := 20%Z in
  ret ([
        (** prologue. This is code that the callee is executing. *)
        IConst (IInt 1) R_ONE;
        IJal proc_label;
        IReturn;
        ILabel proc_label;
        IMov R_SP R_AUX1;
        IConst (IInt stack_frame_size) R_SP;
        IAlloc R_SP R_SP] ++
        push R_AUX1 ++
        load_arg local_buf_ptr R_AUX1 ++
        push R_AUX1 ++
        (** The callee saves R_ARG *)
        push R_ARG ++
        [IMov R_COM R_ARG] ++

        (** function body *)
        proc_code ++

        (** epilogue. This is code that the callee is executing. *)
        pop R_ARG ++
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
         (comp: Component.id) (procs: list (Procedure.id * expr))
  : COMP (NMap label) :=
  let fix gen acc procs :=
      match procs with
      | [] => ret acc
      | (P, _) :: procs' =>
        do freshl <- fresh_label comp;
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
        do map <- gen_component_procedures_labels C (elementsm Cprocs);
        gen (setm acc C map) procs'
      end
  in gen emptym procs.

(*****************************************
Definition gen_buffers
         (bufs: {fmap Component.id -> nat + list value})
  : NMap {fmap Block.id -> nat + list value} := bufs.
*******************************************)

Definition compile_components
         (procs_labels : NMap (NMap label))
         (comps: list (Component.id * NMap expr))
  : COMP (list (Component.id * NMap code)) :=
  let fix compile acc cs :=
      match cs with
      | [] => ret acc
      | (C,procs) :: cs' =>
        let local_buffer_block_id := 0 in
        do P_labels <- lift (procs_labels C);
        do procs_code <- compile_procedures C
           (Permission.data, C, local_buffer_block_id, 0%Z)
           (* Used Permission.data here because this permission
              is consistent with the way the local_buf_ptr
              is used in section WithComponent.
            *)
           P_labels
           (elementsm procs);
        let acc' := (C, mkfmap procs_code) :: acc in
        compile acc' cs'
      end
  in compile [] comps.

Definition init_env : comp_env :=
  {| next_label := emptym; |}.

(* In intermediate program, main will be a tiny wrapper routine (in the same component)
   that simply calls the  (translation of the) original main and then halts. *)

(* A fresh procedure id can be calculated by, e.g., taking the max of all procedure id's and adding 1 *)

Definition generate_fresh_procedure_id comp (procs: NMap (NMap code)) : Procedure.id :=
  match getm procs comp with
  | None => 0
  | Some comp_procs =>
    Nat.succ (fold_left (fun proc_id proc => Nat.max proc_id (fst proc)) (elementsm comp_procs) 0)
  end.

Lemma generate_fresh_procedure_id_fresh:
  forall comp procs,
    generate_fresh_procedure_id comp procs \in domm procs = false.
Proof.
Admitted.

Definition wrap_main (procs_labels: NMap (NMap label)) (p: Intermediate.program) : COMP Intermediate.program :=
  match p.(Intermediate.prog_main) with
  | true =>
    do procs <- lift (getm p.(Intermediate.prog_procedures) Component.main);
    do P_labels <- lift (getm procs_labels Component.main);
    do lab <- lift (getm P_labels Procedure.main);
    let P' := generate_fresh_procedure_id Component.main (p.(Intermediate.prog_procedures)) in
    let procs' := setm procs P' [IConst (IInt 1) R_ONE; IJal lab ; IHalt] in
    ret {| Intermediate.prog_interface := p.(Intermediate.prog_interface);
           Intermediate.prog_procedures := setm p.(Intermediate.prog_procedures) Component.main procs';
           Intermediate.prog_buffers := p.(Intermediate.prog_buffers);
           Intermediate.prog_main := Some P' |}
  | false => ret p
  end.

Definition compile_program
           (p: Source.program) (stksize: {fmap Component.id -> nat})
  : option Intermediate.program :=
  let comps := elementsm (Source.prog_procedures p) in
  (* let localbuf := *) 
  let bufs := Source.prog_buffers p in
  run init_env (
    do procs_labels <- gen_all_procedures_labels comps;
    do code <- compile_components procs_labels comps;
    let p :=
        {| Intermediate.prog_interface := Source.prog_interface p;
           Intermediate.prog_procedures := mkfmap code;
           Intermediate.prog_buffers := bufs;
           Intermediate.prog_main := Some Procedure.main |} in
   wrap_main procs_labels p).

Lemma compilation_preserves_interface:
  forall p p_compiled stksize,
    compile_program p stksize = Some p_compiled ->
    Intermediate.prog_interface p_compiled = Source.prog_interface p.
Proof.
  intros p p_compiled ? Hcompile.
  unfold compile_program, run, wrap_main in Hcompile.
  simpl in Hcompile. unfold Comp.bind in Hcompile.

  destruct (gen_all_procedures_labels (elementsm (Source.prog_procedures p)) init_env)
    as [[labels cenv1]|] eqn:Hlabs;
    try discriminate.
  destruct (compile_components  labels
                                (elementsm (Source.prog_procedures p)) cenv1)
    as [[code cenv2]|] eqn:Hcompiled_comps;
    try discriminate.
  simpl in Hcompile.
  destruct (lift ((mkfmap (T:=nat_ordType) code) Component.main) cenv2) as [[]|] eqn:Hlift_mkfmap;
    simpl in *;
    rewrite Hlift_mkfmap in Hcompile || idtac "ExStructures 0.1 legacy rewrite inactive";
    try discriminate.
  destruct (lift (labels Component.main) c) as [[main_label cenv3]|] eqn:Hlift_main_label_C;
    try discriminate.
  destruct (lift (main_label Procedure.main) cenv3) as [[]|] eqn:Hlift_main_label_P;
      try discriminate.
  simpl in Hcompile. inversion Hcompile.
  reflexivity.
Qed.

Lemma compilation_preserves_linkability:
  forall {p pstksize p_compiled c cstksize c_compiled},
    Source.well_formed_program p ->
    Source.well_formed_program c ->
    linkable (Source.prog_interface p) (Source.prog_interface c) ->
    compile_program p pstksize = Some p_compiled ->
    compile_program c cstksize = Some c_compiled ->
    linkable (Intermediate.prog_interface p_compiled) (Intermediate.prog_interface c_compiled).
Proof.
  intros.
  repeat (erewrite compilation_preserves_interface; eauto).
Qed.

(* RB: TODO: Abstract find_procedure in Source (cprog_main_existence).
   Try to get rid of unnecessary clutter in statement and propagate. *)
Lemma compilation_preserves_main :
  forall {p pstksize p_compiled},
    Source.well_formed_program p ->
    compile_program p pstksize = Some p_compiled ->
    (exists main, Source.prog_main p = Some main) <->
    Intermediate.prog_main p_compiled.
Proof.
  intros p p_compiled Hp_well_formed Hp_compiles.
  split; intros [].
  - admit.
  - admit.
Admitted.

Lemma compilation_preserves_linkable_mains : forall p1 p1sz p1' p2 p2sz p2',
  Source.well_formed_program p1 ->
  Source.well_formed_program p2 ->
  Source.linkable_mains p1 p2 ->
  compile_program p1 p1sz = Some p1' ->
  compile_program p2 p2sz = Some p2' ->
  Intermediate.linkable_mains p1' p2'.
Proof.
  unfold Source.linkable_mains, Intermediate.linkable_mains.
  intros p1 ? p1' p2 ? p2' Hwf1 Hwf2 Hmains Hcomp1 Hcomp2.
  pose proof compilation_preserves_main Hwf1 Hcomp1 as Hmain1.
  pose proof compilation_preserves_main Hwf2 Hcomp2 as Hmain2.
  destruct (Source.prog_main p1) as [mainp1 |];
    destruct (Source.prog_main p2) as [mainp2 |];
    destruct (Intermediate.prog_main p1') as [|];
    destruct (Intermediate.prog_main p2') as [|];
    try reflexivity.
  - inversion Hmains.
    Ltac some_eq_none_contra Hcontra id :=
      destruct Hcontra as [_ Hcontra];
      specialize (Hcontra (ex_intro (fun x => Some id = Some x) id eq_refl));
      now destruct Hcontra.
  - destruct Hmain2 as [Hmain2 Hmain2'].
    destruct (Hmain2' eq_refl) as [? Hcontra]; inversion Hcontra.
  - destruct Hmain1 as [Hmain1 Hmain1'].
    destruct (Hmain1' eq_refl) as [? Hcontra]; inversion Hcontra.
  - destruct Hmain1 as [Hmain1 Hmain1'].
    destruct (Hmain1' eq_refl) as [? Hcontra]; inversion Hcontra.
Qed.

Remark mains_without_source : forall p psz pc pc',
  Source.well_formed_program p ->
  compile_program p psz = Some pc ->
  Source.prog_main p = None ->
  Intermediate.linkable_mains pc pc'.
Proof.
  intros p ? pc pc' Hwf Hcomp Hmain.
  pose proof compilation_preserves_main Hwf Hcomp as [Hpreserve1 Hpreserve2].
  rewrite Hmain in Hpreserve2.
  destruct (Intermediate.prog_main pc) as [|] eqn: Hpc.
  - specialize (Hpreserve2 eq_refl) as [? Hcontra]; inversion Hcontra.
  - unfold Intermediate.linkable_mains. rewrite Hpc. reflexivity.
Qed.

Lemma compilation_preserves_main_linkability :
  forall {p psz p_compiled c csz c_compiled},
    Source.well_formed_program p ->
    Source.well_formed_program c ->
    linkable (Source.prog_interface p) (Source.prog_interface c) ->
    compile_program p psz = Some p_compiled ->
    compile_program c csz = Some c_compiled ->
    Intermediate.linkable_mains p_compiled c_compiled.
Proof.
  intros p psz p_compiled c csz c_compiled Hwfp Hwfc Hlinkable Hcompp Hcompc.
  pose proof Source.linkable_disjoint_mains Hwfp Hwfc Hlinkable as Hmains.
  destruct (Source.prog_main p) as [mp |] eqn:Hmainp;
    destruct (Source.prog_main c) as [mc |] eqn:Hmainc.
  - unfold Source.linkable_mains in Hmains.
    rewrite Hmainp in Hmains.
    rewrite Hmainc in Hmains.
    inversion Hmains.
  - apply Intermediate.linkable_mains_sym.
    now eapply (mains_without_source c).
  - now eapply (mains_without_source p).
  - now eapply (mains_without_source p).
    Unshelve. all: eauto.
Qed.

Lemma compilation_has_matching_mains :
  forall {p psz p_compiled},
    Source.well_formed_program p ->
    compile_program p psz = Some p_compiled ->
    matching_mains p p_compiled.
Admitted.

(****************************************
Axiom separate_compilation:
  forall p c pcsz pc_compiled t s,
    Source.well_formed_program p ->
    Source.well_formed_program c ->
    linkable (Source.prog_interface p) (Source.prog_interface c) ->
    compile_program (Source.program_link p c) pcsz = Some pc_compiled ->
    Star (I.CS.sem_non_inform pc_compiled)
         (I.CS.initial_machine_state pc_compiled) t s ->
    exists t' s' psz csz p_comp c_comp size_meta size_meta',
      compile_program p psz = Some p_comp
      /\
      compile_program c csz = Some c_comp
      /\
      Star (I.CS.sem_non_inform (Intermediate.program_link p_comp c_comp))
           (I.CS.initial_machine_state (Intermediate.program_link p_comp c_comp))
           t' s'
      /\
      traces_shift_each_other_option size_meta size_meta' t t'.
***********************************************)

Axiom separate_compilation:
  forall p psz c csz p_comp c_comp,
    Source.well_formed_program p ->
    Source.well_formed_program c ->
    linkable (Source.prog_interface p) (Source.prog_interface c) ->
    compile_program p psz = Some p_comp ->
    compile_program c csz = Some c_comp ->
    compile_program (Source.program_link p c) (unionm psz csz)
    = Some (Intermediate.program_link p_comp c_comp).

(* We can currently do with a weaker notion of separate compilation *)
(*************************************************
Local Axiom separate_compilation_weaker:
  forall p psz c csz pc_comp p_comp c_comp pcsz,
    Source.well_formed_program p ->
    Source.well_formed_program c ->
    linkable (Source.prog_interface p) (Source.prog_interface c) ->
    compile_program p psz = Some p_comp ->
    compile_program c csz = Some c_comp ->
    compile_program (Source.program_link p c) pcsz = Some pc_comp ->
    forall b, program_behaves (I.CS.sem_inform pc_comp) b <->
              program_behaves (I.CS.sem_inform (Intermediate.program_link p_comp c_comp)) b.
*******************************************************)
(* Proof. *)
(*   intros p c pc_comp p_comp c_comp Hwf_p Hwf_c Hlinkable Hcomp_p Hcomp_c Hcomp_link b. *)
(*   pose proof separate_compilation p c p_comp c_comp Hwf_p Hwf_c Hlinkable Hcomp_p Hcomp_c as Hsc. *)
(*   rewrite Hcomp_link in Hsc. *)
(*   injection Hsc; intro Heq. *)
(*   now rewrite Heq. *)
(* Qed. *)

Local Axiom compilation_preserves_well_formedness:
  forall {p psz p_compiled},
    Source.well_formed_program p ->
    compile_program p psz = Some p_compiled ->
    Intermediate.well_formed_program p_compiled.

(* FCC *)

Axiom metadata_size_transformer: (Component.id -> nat) -> (Component.id -> nat).

Local Axiom forward_simulation_star:
  forall p t s size_meta,
    Source.closed_program p ->
    Source.well_formed_program p ->
    Star (S.CS.sem p) (S.CS.initial_machine_state p) t s ->
    exists s' psz p_compiled t',
      domm psz = domm (Source.prog_interface p) /\
      compile_program p psz = Some p_compiled /\
      Star (I.CS.sem_non_inform p_compiled)
           (I.CS.initial_machine_state p_compiled) t' s' /\
      traces_shift_each_other_option
        size_meta (metadata_size_transformer size_meta) t t'.

Local Axiom backward_simulation_star:
  forall p psz p_compiled t s size_meta,
    Source.closed_program p ->
    Source.well_formed_program p ->
    compile_program p psz = Some p_compiled ->
    Star (I.CS.sem_non_inform p_compiled)
         (I.CS.initial_machine_state p_compiled) t s ->
    exists s' t',
      Star (S.CS.sem p) (S.CS.initial_machine_state p) t' s' /\
      traces_shift_each_other_option
        (metadata_size_transformer size_meta) size_meta t t'.

Local Axiom well_formed_compilable :
  forall p psz,
    Source.well_formed_program p ->
  exists pc,
    compile_program p psz = Some pc.

Definition private_pointers_never_leak_I p metadata_size :=
  forall (s : I.CS.state) (t : Events.trace Events.event),
    CSInvariants.CSInvariants.is_prefix s p t ->
    good_trace_extensional (left_addr_good_for_shifting metadata_size) t /\
    (forall (mem : eqtype.Equality.sort Memory.Memory.t),
        I.CS.state_mem s = mem ->
        shared_locations_have_only_shared_values mem metadata_size
    ).

Local Axiom compiler_preserves_non_leakage_of_private_pointers:
  forall p psz p_compiled metadata_size,
    Source.closed_program p ->
    Source.well_formed_program p ->
    compile_program p psz = Some p_compiled ->
    S.CS.private_pointers_never_leak_S p          metadata_size ->
    private_pointers_never_leak_I p_compiled (metadata_size_transformer metadata_size).

(***********************************************
Local Axiom non_leakage_of_private_pointers_compatible_with_separate_compilation:
  forall p p_compiled c c_compiled pcsz pc_compiled,
    Source.closed_program (Source.program_link p c) ->
    Source.well_formed_program p ->
    compile_program p psz = Some p_compiled ->
    compile_program c csz = Some c_compiled ->
    pcsz = unionm psz csz
    compile_program (Source.program_link p c) pcsz = Some pc_compiled -> 
    private_pointers_never_leak_I (pc_compiled) metadata_size ->
    forall s t,
      CSInvariants.CSInvariants.is_prefix
        s
        (Intermediate.program_link p_compiled c_compiled) t ->
      
      private_pointers_never_leak_I (pc_compiled) metadata_size.
    
************************************************)
