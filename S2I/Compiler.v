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
  push R_RA
  IJal internal_entry_label
  pop R_RA
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
Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import S2I.CompMonad.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import S2I.Definitions.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import zify.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

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


Lemma getm_def_In {A : Type} {s : list (nat * A)} {k v} :
  getm_def s k = Some v -> List.In (k, v) s.
Proof.
  elim: s => [|[k' v'] s IH] //=.
  case: ifP => [/eqP Ek [Ev]|_ /IH HIn]; [left|by right].
  by rewrite Ek Ev.
Qed.

Lemma In_unzip1_mem {A : Type} {s : list (nat * A)} {k v} :
  List.In (k, v) s -> k \in unzip1 s.
Proof.
  elim: s => [|[k' v'] s IH] //= [[-> _]|HIn]; first by rewrite inE eqxx.
  by rewrite inE IH // orbT.
Qed.

Lemma mem_unzip1_In {A : Type} {s : list (nat * A)} {k} :
  k \in unzip1 s -> exists v, List.In (k, v) s.
Proof.
  elim: s => [|[k' v'] s IH] //=.
  rewrite inE => /orP [/eqP ->|/IH [v HIn]].
  - by exists v'; left.
  - by exists v; right.
Qed.

Lemma In_getm_def_sorted {A : Type} {s : list (nat * A)} {k v} :
  sorted Ord.lt (unzip1 s) ->
  List.In (k, v) s -> getm_def s k = Some v.
Proof.
  elim: s => [|[k' v'] s IH] //= Hsort [E|HIn].
  - by case: E => -> ->; rewrite eqxx.
  - case: ifP => [/eqP Ek|_]; last by apply: IH => //; exact: (path_sorted Hsort).
    exfalso. subst k.
    have Hall := order_path_min (@Ord.lt_trans _) Hsort.
    move/allP: Hall => Hall.
    have Hk := In_unzip1_mem HIn.
    have := Hall _ Hk. by rewrite Ord.ltxx.
Qed.

Lemma In_elementsm_getm {A : Type} {m : NMap A} {k v} :
  List.In (k, v) (elementsm m) -> m k = Some v.
Proof. exact: In_getm_def_sorted (valP m). Qed.

Lemma getm_In_elementsm {A : Type} {m : NMap A} {k v} :
  m k = Some v -> List.In (k, v) (elementsm m).
Proof. exact: getm_def_In. Qed.

Lemma unzip1_elementsm_domm {A : Type} (m : NMap A) k :
  (k \in unzip1 (elementsm m)) = (k \in domm m).
Proof.
  rewrite mem_domm.
  apply/idP/idP.
  - move/mem_unzip1_In => [v HIn]. by rewrite (In_elementsm_getm HIn).
  - case E: (m k) => [v|] // _. exact: In_unzip1_mem (getm_In_elementsm E).
Qed.

Lemma domm_pointwise {A B : Type} {m1 : NMap A} {m2 : NMap B} :
  (forall k, isSome (m1 k) = isSome (m2 k)) -> domm m1 = domm m2.
Proof. move=> H. apply/eq_fset => k. by rewrite !mem_domm H. Qed.

Lemma getm_def_isSome {A : Type} (s : list (nat * A)) k :
  isSome (getm_def s k) = (k \in unzip1 s).
Proof.
  elim: s => [|[k' v'] s IH] //=.
  rewrite inE. case: ifP => [Heq|Hne] /=.
  - by [].
  - by rewrite IH.
Qed.

Lemma In_appl {A : Type} (x : A) (s1 s2 : list A) :
  List.In x s1 -> List.In x (s1 ++ s2).
Proof. move=> H. apply/List.in_app_iff. by left. Qed.

Lemma In_appr {A : Type} (x : A) (s1 s2 : list A) :
  List.In x s2 -> List.In x (s1 ++ s2).
Proof. move=> H. apply/List.in_app_iff. by right. Qed.

Ltac in_discr HIn :=
  repeat match type of HIn with
  | List.In _ (_ :: _) => destruct HIn as [HIn|HIn]; [discriminate HIn|]
  | List.In _ nil => destruct HIn
  end.

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

Lemma fresh_label_total (comp : Component.id) (s : comp_env) :
  exists l s', fresh_label comp s = Some (l, s').
Proof.
  rewrite /fresh_label /=.
  rewrite /Comp.bind /Comp.get /Comp.modify /Comp.ret.
  by case: (getm (next_label s) comp) => [l|] /=; do 2 eexists.
Qed.

Lemma fresh_labelE (comp : Component.id) (s : comp_env) :
  fresh_label comp s =
  Some (odflt 0 (getm (next_label s) comp),
        {| next_label := setm (next_label s) comp
                              (1 + odflt 0 (getm (next_label s) comp)) |}).
Proof.
  rewrite /fresh_label /=.
  rewrite /Comp.bind /Comp.get /Comp.modify /Comp.ret.
  by case: (getm (next_label s) comp) => [l|] /=.
Qed.

(* code generation *)

Definition immediately_final (e: expr) : bool :=
  match e with
  | E_val _ | E_exit => true
  | _ => false
  end.

Fixpoint stack_need (e: expr) : nat :=
  match e with
  | E_val _ | E_arg | E_local | E_exit => 0
  | E_binop _ e1 e2 => maxn (stack_need e1) (1 + stack_need e2)
  | E_seq e1 e2 => maxn (stack_need e1) (stack_need e2)
  | E_if e1 e2 e3 => maxn (stack_need e1) (maxn (stack_need e2) (stack_need e3))
  | E_alloc e1 => stack_need e1
  | E_deref e1 => stack_need e1
  | E_assign e1 e2 => maxn (stack_need e2) (1 + stack_need e1)
  | E_call C' P e1 => maxn (stack_need e1) 2
  end.

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

Definition reload_sp (buf: Pointer.t) : code :=
  [IConst (IPtr buf) R_AUX2;
   ILoad R_AUX2 R_SP].

Section WithComponent.

Variable C: Component.id. (* the current component *)
Variable local_buf_ptr : Pointer.t. (* pointer to the local buffer for current component *)
Variable scratch_buf_ptr : Pointer.t.
Variable P_labels : NMap label.  (* map from procedure id's to start labels for current component *)

Definition find_proc_label P : COMP label :=
  lift (getm P_labels P).

Fixpoint compile_expr (e: expr) : COMP code :=
  match e with
  | E_val (Int i) =>
    ret [IConst (IInt i) R_COM]
  | E_val (Ptr p) =>
    fail
  | E_val Undef => fail (* we don't compile undef *)
  | E_arg =>
    ret [IMov R_ARG R_COM]
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
         push R_COM ++
         c1 ++
         pop R_AUX1 ++
         [IStore R_COM R_AUX1;
          IMov R_AUX1 R_COM])
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
           push R_ARG ++
           store_arg scratch_buf_ptr R_SP R_AUX2 ++
           [ICall C' P'] ++
           [IConst (IInt 1) R_ONE] ++
           reload_sp scratch_buf_ptr ++
           pop R_ARG ++
           pop R_RA
           )
  | E_exit => ret [IHalt]
  end.

Definition flag_buf_ptr : Pointer.t := Pointer.add scratch_buf_ptr 1.

Definition compile_proc (P: Procedure.id) (e: expr)
  : COMP code :=
  do proc_label <- find_proc_label P;
  do lmain <- fresh_label C;
  do lreturn <- fresh_label C;
  do proc_code <- compile_expr e;
  let stack_frame_size := Z.of_nat (4 + stack_need e) in
  let is_main := Component.eqb C Component.main && Procedure.eqb P Procedure.main in
  let halt_pad := if is_main && immediately_final e then [IHalt] else [] in
  let ext_entry :=
    if is_main then
      [IConst (IInt 1) R_ONE] ++
      [IMov R_SP R_AUX1;
       IConst (IInt stack_frame_size) R_SP;
       IAlloc R_SP R_SP] ++
       push R_AUX1 ++
       load_arg scratch_buf_ptr R_AUX1 ++
       push R_AUX1 ++
       push R_RA ++
      [IConst (IPtr flag_buf_ptr) R_AUX1;
       ILoad R_AUX1 R_AUX2] ++
       push R_AUX2 ++
      [IBnz R_AUX2 lmain;
       IConst (IInt 0) R_COM;
       ILabel lmain;
       IConst (IInt 1) R_AUX2;
       IStore R_AUX1 R_AUX2;
       IJal proc_label] ++
       pop R_ARG ++
       pop R_RA ++
       pop R_AUX1 ++
       store_arg scratch_buf_ptr R_AUX1 R_AUX2 ++
       pop R_SP ++
      [IBnz R_ARG lreturn;
       IHalt;
       ILabel lreturn;
       IReturn]
    else
      [IConst (IInt 1) R_ONE] ++
      [IMov R_SP R_AUX1;
       IConst (IInt stack_frame_size) R_SP;
       IAlloc R_SP R_SP] ++
       push R_AUX1 ++
       load_arg scratch_buf_ptr R_AUX1 ++
       push R_AUX1 ++
       push R_RA ++
      [IJal proc_label] ++
       pop R_RA ++
       pop R_AUX1 ++
       store_arg scratch_buf_ptr R_AUX1 R_AUX2 ++
       pop R_SP ++
      [IReturn] in
  ret (halt_pad ++
       ext_entry ++
       [ILabel proc_label;
        IMov R_SP R_AUX1;
        IConst (IInt stack_frame_size) R_SP;
        IAlloc R_SP R_SP] ++
        push R_AUX1 ++
        push R_ARG ++
        [IMov R_COM R_ARG] ++
        proc_code ++
        pop R_ARG ++
        pop R_SP ++
        [IJump]).

Fixpoint compile_procedures_aux
         (acc: list (Procedure.id * code)) (ps: list (Procedure.id * expr))
  : COMP (list (Procedure.id * code)) :=
  match ps with
  | [] => ret acc
  | (P,e) :: ps' =>
    do proc_code <- compile_proc P e;
    compile_procedures_aux ((P,proc_code) :: acc) ps'
  end.

Definition compile_procedures
         (procs: list (Procedure.id * expr))
  : COMP (list (Procedure.id * code)) :=
  compile_procedures_aux [] procs.

Section Shape.

Variable procs : NMap (NMap expr).
Variable intf  : Program.interface.

Definition code_shape (c : code) : Prop :=
  [/\ (forall r l, List.In (IBnz r l) c -> List.In (ILabel l) c),
      (forall l, List.In (IJal l) c ->
         exists P', getm P_labels P' = Some l /\ Source.find_procedure procs C P'),
      (forall C' P', List.In (ICall C' P') c ->
         C <> C' /\ imported_procedure intf C C' P')
    & (forall v r, List.In (IConst v r) c ->
         [\/ exists i, v = IInt i, v = IPtr local_buf_ptr,
             v = IPtr scratch_buf_ptr | v = IPtr flag_buf_ptr])].

Lemma code_shape_nil : code_shape [::].
Proof. by split=> [r l|l|C' P'|v r] []. Qed.

Lemma code_shape_cat c1 c2 :
  code_shape c1 -> code_shape c2 -> code_shape (c1 ++ c2).
Proof.
  move=> [B1 J1 K1 V1] [B2 J2 K2 V2]. split.
  - move=> r l /List.in_app_iff [HIn|HIn]; apply/List.in_app_iff.
    + left. exact: B1 HIn.
    + right. exact: B2 HIn.
  - by move=> l /List.in_app_iff [HIn|HIn]; [exact: J1 HIn|exact: J2 HIn].
  - by move=> C' P' /List.in_app_iff [HIn|HIn]; [exact: K1 HIn|exact: K2 HIn].
  - by move=> v r /List.in_app_iff [HIn|HIn]; [exact: V1 HIn|exact: V2 HIn].
Qed.

Lemma code_shape_int i r : code_shape [:: IConst (IInt i) r].
Proof.
  split=> [r' l HIn|l HIn|C' P' HIn|v r' HIn]; try by in_discr HIn.
  destruct HIn as [E|HIn]; [|by in_discr HIn].
  case: E => <- _. apply/Or41. by exists i.
Qed.

Lemma code_shape_local r : code_shape [:: IConst (IPtr local_buf_ptr) r].
Proof.
  split=> [r' l HIn|l HIn|C' P' HIn|v r' HIn]; try by in_discr HIn.
  destruct HIn as [E|HIn]; [|by in_discr HIn].
  case: E => <- _. by apply/Or42.
Qed.

Lemma code_shape_mov1 r1 r2 : code_shape [:: IMov r1 r2].
Proof. split=> [r' l HIn|l HIn|C' P' HIn|v r' HIn]; by in_discr HIn. Qed.

Lemma code_shape_halt1 : code_shape [:: IHalt].
Proof. split=> [r' l HIn|l HIn|C' P' HIn|v r' HIn]; by in_discr HIn. Qed.

Lemma valid_calls_weaken (calls calls' : {fset Component.id * Procedure.id}) cur :
  {subset calls <= calls'} ->
  Source.valid_calls procs intf cur calls' -> Source.valid_calls procs intf cur calls.
Proof. move=> Hsub Hv C' P' HIn. apply: Hv. exact: Hsub. Qed.

Lemma code_shape_cons_store r1 r2 c :
  code_shape c -> code_shape (IStore r1 r2 :: c).
Proof.
  move=> [Bc Jc Kc Vc]. split.
  - move=> r' l' HIn. destruct HIn as [E|HIn]; [discriminate E|right; exact: Bc HIn].
  - move=> l' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Jc HIn].
  - move=> C0 P0 HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Kc HIn].
  - move=> v' r' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Vc HIn].
Qed.

Lemma code_shape_cons_binop bop r1 r2 r3 c :
  code_shape c -> code_shape (IBinOp bop r1 r2 r3 :: c).
Proof.
  move=> [Bc Jc Kc Vc]. split.
  - move=> r' l' HIn. destruct HIn as [E|HIn]; [discriminate E|right; exact: Bc HIn].
  - move=> l' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Jc HIn].
  - move=> C0 P0 HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Kc HIn].
  - move=> v' r' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Vc HIn].
Qed.

Lemma code_shape_cons_load r1 r2 c :
  code_shape c -> code_shape (ILoad r1 r2 :: c).
Proof.
  move=> [Bc Jc Kc Vc]. split.
  - move=> r' l' HIn. destruct HIn as [E|HIn]; [discriminate E|right; exact: Bc HIn].
  - move=> l' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Jc HIn].
  - move=> C0 P0 HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Kc HIn].
  - move=> v' r' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Vc HIn].
Qed.

Lemma code_shape_cons_mov r1 r2 c :
  code_shape c -> code_shape (IMov r1 r2 :: c).
Proof.
  move=> [Bc Jc Kc Vc]. split.
  - move=> r' l' HIn. destruct HIn as [E|HIn]; [discriminate E|right; exact: Bc HIn].
  - move=> l' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Jc HIn].
  - move=> C0 P0 HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Kc HIn].
  - move=> v' r' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Vc HIn].
Qed.

Lemma code_shape_cons_alloc r1 r2 c :
  code_shape c -> code_shape (IAlloc r1 r2 :: c).
Proof.
  move=> [Bc Jc Kc Vc]. split.
  - move=> r' l' HIn. destruct HIn as [E|HIn]; [discriminate E|right; exact: Bc HIn].
  - move=> l' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Jc HIn].
  - move=> C0 P0 HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Kc HIn].
  - move=> v' r' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Vc HIn].
Qed.

Lemma code_shape_cons_halt c :
  code_shape c -> code_shape (IHalt :: c).
Proof.
  move=> [Bc Jc Kc Vc]. split.
  - move=> r' l' HIn. destruct HIn as [E|HIn]; [discriminate E|right; exact: Bc HIn].
  - move=> l' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Jc HIn].
  - move=> C0 P0 HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Kc HIn].
  - move=> v' r' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Vc HIn].
Qed.

Lemma code_shape_cons_ret c :
  code_shape c -> code_shape (IReturn :: c).
Proof.
  move=> [Bc Jc Kc Vc]. split.
  - move=> r' l' HIn. destruct HIn as [E|HIn]; [discriminate E|right; exact: Bc HIn].
  - move=> l' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Jc HIn].
  - move=> C0 P0 HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Kc HIn].
  - move=> v' r' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Vc HIn].
Qed.

Lemma code_shape_cons_jump c :
  code_shape c -> code_shape (IJump :: c).
Proof.
  move=> [Bc Jc Kc Vc]. split.
  - move=> r' l' HIn. destruct HIn as [E|HIn]; [discriminate E|right; exact: Bc HIn].
  - move=> l' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Jc HIn].
  - move=> C0 P0 HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Kc HIn].
  - move=> v' r' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Vc HIn].
Qed.

Lemma code_shape_cons_const_int i r c :
  code_shape c -> code_shape (IConst (IInt i) r :: c).
Proof.
  move=> [Bc Jc Kc Vc]. split.
  - move=> r' l' HIn. destruct HIn as [E|HIn]; [discriminate E|right; exact: Bc HIn].
  - move=> l' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Jc HIn].
  - move=> C0 P0 HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Kc HIn].
  - move=> v' r' HIn. destruct HIn as [E|HIn]; [|exact: Vc HIn].
    case: E => <- _. apply/Or41. by exists i.
Qed.

Lemma code_shape_cons_const_local r c :
  code_shape c -> code_shape (IConst (IPtr local_buf_ptr) r :: c).
Proof.
  move=> [Bc Jc Kc Vc]. split.
  - move=> r' l' HIn. destruct HIn as [E|HIn]; [discriminate E|right; exact: Bc HIn].
  - move=> l' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Jc HIn].
  - move=> C0 P0 HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Kc HIn].
  - move=> v' r' HIn. destruct HIn as [E|HIn]; [|exact: Vc HIn].
    case: E => <- _. by apply/Or42.
Qed.

Lemma code_shape_cons_const_scratch r c :
  code_shape c -> code_shape (IConst (IPtr scratch_buf_ptr) r :: c).
Proof.
  move=> [Bc Jc Kc Vc]. split.
  - move=> r' l' HIn. destruct HIn as [E|HIn]; [discriminate E|right; exact: Bc HIn].
  - move=> l' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Jc HIn].
  - move=> C0 P0 HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Kc HIn].
  - move=> v' r' HIn. destruct HIn as [E|HIn]; [|exact: Vc HIn].
    case: E => <- _. by apply/Or43.
Qed.

Lemma code_shape_cons_const_flag r c :
  code_shape c -> code_shape (IConst (IPtr flag_buf_ptr) r :: c).
Proof.
  move=> [Bc Jc Kc Vc]. split.
  - move=> r' l' HIn. destruct HIn as [E|HIn]; [discriminate E|right; exact: Bc HIn].
  - move=> l' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Jc HIn].
  - move=> C0 P0 HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Kc HIn].
  - move=> v' r' HIn. destruct HIn as [E|HIn]; [|exact: Vc HIn].
    case: E => <- _. by apply/Or44.
Qed.

Lemma code_shape_cons_bnz r l c :
  List.In (ILabel l) c ->
  code_shape c -> code_shape (IBnz r l :: c).
Proof.
  move=> Hl [Bc Jc Kc Vc]. split.
  - move=> r' l' HIn. destruct HIn as [E|HIn]; [|right; exact: Bc HIn].
    case: E => _ <-. by right.
  - move=> l' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Jc HIn].
  - move=> C0 P0 HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Kc HIn].
  - move=> v' r' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Vc HIn].
Qed.

Lemma code_shape_cons_jal l c :
  (exists P', getm P_labels P' = Some l /\ Source.find_procedure procs C P') ->
  code_shape c -> code_shape (IJal l :: c).
Proof.
  move=> Hl [Bc Jc Kc Vc]. split.
  - move=> r' l' HIn. destruct HIn as [E|HIn]; [discriminate E|right; exact: Bc HIn].
  - move=> l' HIn. destruct HIn as [E|HIn]; [|exact: Jc HIn].
    case: E => <-. exact: Hl.
  - move=> C0 P0 HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Kc HIn].
  - move=> v' r' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Vc HIn].
Qed.

Lemma code_shape_cons_call C' P' c :
  C <> C' -> imported_procedure intf C C' P' ->
  code_shape c -> code_shape (ICall C' P' :: c).
Proof.
  move=> Hne Himp [Bc Jc Kc Vc]. split.
  - move=> r' l' HIn. destruct HIn as [E|HIn]; [discriminate E|right; exact: Bc HIn].
  - move=> l' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Jc HIn].
  - move=> C0 P0 HIn. destruct HIn as [E|HIn]; [|exact: Kc HIn].
    case: E => <- <-. by split.
  - move=> v' r' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Vc HIn].
Qed.

Ltac shape_step :=
  first [ exact: code_shape_nil
        | apply: code_shape_cons_store
        | apply: code_shape_cons_binop
        | apply: code_shape_cons_load
        | apply: code_shape_cons_mov
        | apply: code_shape_cons_alloc
        | apply: code_shape_cons_halt
        | apply: code_shape_cons_ret
        | apply: code_shape_cons_jump
        | apply: code_shape_cons_const_int
        | apply: code_shape_cons_const_local
        | apply: code_shape_cons_const_scratch
        | apply: code_shape_cons_const_flag ].

Lemma compile_expr_shape :
  forall e s c s',
    compile_expr e s = Some (c, s') ->
    Source.valid_calls procs intf C (called_procedures e) ->
    Source.values_are_integers e ->
    code_shape c.
Proof.
  elim=> [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
         |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc Hvc Hvi.
  -
    case: v Hc Hvc Hvi => [i|p|] Hc _ Hvi.
    + move: Hc => /= [<- _]. exact: code_shape_int.
    + by move: Hvi.
    + by move: Hc => /=.
  -
    move: Hc => /= [<- _]. exact: code_shape_mov1.
  -
    move: Hc => /= [<- _]. exact: code_shape_local.
  -
    have Hvc1 : Source.valid_calls procs intf C (called_procedures e1).
    { apply: valid_calls_weaken Hvc => x Hx. by rewrite /= in_fsetU Hx. }
    have Hvc2 : Source.valid_calls procs intf C (called_procedures e2).
    { apply: valid_calls_weaken Hvc => x Hx. by rewrite /= in_fsetU Hx orbT. }
    move: Hvi => /= /andP [Hvi1 Hvi2].
    move: Hc; rewrite /= /Comp.bind /Comp.ret.
    case E1: (compile_expr e1 s) => [[c1 s1]|]; last by [].
    rewrite /=.
    case E2: (compile_expr e2 s1) => [[c2 s2]|]; last by [].
    rewrite /=. move=> [<- _].
    apply: code_shape_cat; first exact: (IH1 _ _ _ E1 Hvc1 Hvi1).
    do 2!shape_step.
    apply: code_shape_cat; first exact: (IH2 _ _ _ E2 Hvc2 Hvi2).
    by do 4!shape_step.
  -
    have Hvc1 : Source.valid_calls procs intf C (called_procedures e1).
    { apply: valid_calls_weaken Hvc => x Hx. by rewrite /= in_fsetU Hx. }
    have Hvc2 : Source.valid_calls procs intf C (called_procedures e2).
    { apply: valid_calls_weaken Hvc => x Hx. by rewrite /= in_fsetU Hx orbT. }
    move: Hvi => /= /andP [Hvi1 Hvi2].
    move: Hc; rewrite /= /Comp.bind /Comp.ret.
    case E1: (compile_expr e1 s) => [[c1 s1]|]; last by [].
    rewrite /=.
    case E2: (compile_expr e2 s1) => [[c2 s2]|]; last by [].
    rewrite /=. move=> [<- _].
    apply: code_shape_cat; first exact: (IH1 _ _ _ E1 Hvc1 Hvi1).
    exact: (IH2 _ _ _ E2 Hvc2 Hvi2).
  -
    have Hvc1 : Source.valid_calls procs intf C (called_procedures e1).
    { apply: valid_calls_weaken Hvc => x Hx. by rewrite /= !in_fsetU Hx. }
    have Hvc2 : Source.valid_calls procs intf C (called_procedures e2).
    { apply: valid_calls_weaken Hvc => x Hx. by rewrite /= !in_fsetU Hx orbT. }
    have Hvc3 : Source.valid_calls procs intf C (called_procedures e3).
    { apply: valid_calls_weaken Hvc => x Hx. by rewrite /= !in_fsetU Hx !orbT. }
    move: Hvi => /= /and3P [Hvi1 Hvi2 Hvi3].
    move: Hc; rewrite /= /Comp.bind /Comp.ret.
    case E1: (compile_expr e1 s) => [[c1 s1]|]; last by [].
    rewrite /=.
    case E2: (compile_expr e2 s1) => [[c2 s2]|]; last by [].
    rewrite /=.
    case E3: (compile_expr e3 s2) => [[c3 s3]|]; last by [].
    rewrite /=.
    case E4: (fresh_label C s3) => [[lconseq s4]|]; last by [].
    rewrite /=.
    case E5: (fresh_label C s4) => [[lend s5]|]; last by [].
    rewrite /=. move=> [<- _].
    have [B1 J1 K1 V1] := IH1 _ _ _ E1 Hvc1 Hvi1.
    have [B2 J2 K2 V2] := IH2 _ _ _ E2 Hvc2 Hvi2.
    have [B3 J3 K3 V3] := IH3 _ _ _ E3 Hvc3 Hvi3.
    have Hlab1 : List.In (ILabel lconseq)
      (c1 ++ IBnz R_COM lconseq
          :: c3 ++ IBnz R_ONE lend :: ILabel lconseq :: c2 ++ [:: ILabel lend]).
    { apply: In_appr. right. apply: In_appr. right. by left. }
    have Hlab2 : List.In (ILabel lend)
      (c1 ++ IBnz R_COM lconseq
          :: c3 ++ IBnz R_ONE lend :: ILabel lconseq :: c2 ++ [:: ILabel lend]).
    { apply: In_appr. right. apply: In_appr. right. right. apply: In_appr. by left. }
    split.
    + move=> r l HIn.
      move: HIn => /List.in_app_iff [HIn|HIn]; first by apply: In_appl; exact: B1 HIn.
      destruct HIn as [E|HIn]; first by case: E => _ <-; exact: Hlab1.
      move: HIn => /List.in_app_iff [HIn|HIn].
      { apply: In_appr. right. apply: In_appl. exact: B3 HIn. }
      destruct HIn as [E|HIn]; first by case: E => _ <-; exact: Hlab2.
      destruct HIn as [E|HIn]; first by discriminate E.
      move: HIn => /List.in_app_iff [HIn|HIn].
      { apply: In_appr. right. apply: In_appr. right. right. apply: In_appl.
        exact: B2 HIn. }
      destruct HIn as [E|HIn]; [discriminate E|by in_discr HIn].
    + move=> l HIn.
      move: HIn => /List.in_app_iff [HIn|HIn]; first exact: J1 HIn.
      destruct HIn as [E|HIn]; first by discriminate E.
      move: HIn => /List.in_app_iff [HIn|HIn]; first exact: J3 HIn.
      destruct HIn as [E|HIn]; first by discriminate E.
      destruct HIn as [E|HIn]; first by discriminate E.
      move: HIn => /List.in_app_iff [HIn|HIn]; first exact: J2 HIn.
      destruct HIn as [E|HIn]; [discriminate E|by in_discr HIn].
    + move=> C0 P0 HIn.
      move: HIn => /List.in_app_iff [HIn|HIn]; first exact: K1 HIn.
      destruct HIn as [E|HIn]; first by discriminate E.
      move: HIn => /List.in_app_iff [HIn|HIn]; first exact: K3 HIn.
      destruct HIn as [E|HIn]; first by discriminate E.
      destruct HIn as [E|HIn]; first by discriminate E.
      move: HIn => /List.in_app_iff [HIn|HIn]; first exact: K2 HIn.
      destruct HIn as [E|HIn]; [discriminate E|by in_discr HIn].
    + move=> v r HIn.
      move: HIn => /List.in_app_iff [HIn|HIn]; first exact: V1 HIn.
      destruct HIn as [E|HIn]; first by discriminate E.
      move: HIn => /List.in_app_iff [HIn|HIn]; first exact: V3 HIn.
      destruct HIn as [E|HIn]; first by discriminate E.
      destruct HIn as [E|HIn]; first by discriminate E.
      move: HIn => /List.in_app_iff [HIn|HIn]; first exact: V2 HIn.
      destruct HIn as [E|HIn]; [discriminate E|by in_discr HIn].
  -
    move: Hc; rewrite /= /Comp.bind /Comp.ret.
    case E1: (compile_expr e s) => [[c0 s1]|]; last by [].
    rewrite /=. move=> [<- _].
    apply: code_shape_cat; first exact: (IH _ _ _ E1 Hvc Hvi).
    by do 2!shape_step.
  -
    move: Hc; rewrite /= /Comp.bind /Comp.ret.
    case E1: (compile_expr e s) => [[c0 s1]|]; last by [].
    rewrite /=. move=> [<- _].
    apply: code_shape_cat; first exact: (IH _ _ _ E1 Hvc Hvi).
    by do 2!shape_step.
  -
    have Hvc1 : Source.valid_calls procs intf C (called_procedures e1).
    { apply: valid_calls_weaken Hvc => x Hx. by rewrite /= in_fsetU Hx. }
    have Hvc2 : Source.valid_calls procs intf C (called_procedures e2).
    { apply: valid_calls_weaken Hvc => x Hx. by rewrite /= in_fsetU Hx orbT. }
    move: Hvi => /= /andP [Hvi1 Hvi2].
    move: Hc; rewrite /= /Comp.bind /Comp.ret.
    case E1: (compile_expr e1 s) => [[c1 s1]|]; last by [].
    rewrite /=.
    case E2: (compile_expr e2 s1) => [[c2 s2]|]; last by [].
    rewrite /=. move=> [<- _].
    apply: code_shape_cat; first exact: (IH2 _ _ _ E2 Hvc2 Hvi2).
    do 2!shape_step.
    apply: code_shape_cat; first exact: (IH1 _ _ _ E1 Hvc1 Hvi1).
    by do 5!shape_step.
  -
    have Hvce : Source.valid_calls procs intf C (called_procedures e).
    { apply: valid_calls_weaken Hvc => x Hx. by rewrite /= in_fsetU1 Hx orbT. }
    have Hcall : (C', P') \in called_procedures (E_call C' P' e).
    { by rewrite /= in_fsetU1 eqxx. }
    have Hvcall := Hvc _ _ Hcall.
    move: Hvi => /= Hvi.
    move: Hc; rewrite /= /Comp.bind /Comp.ret /find_proc_label /Comp.lift.
    case E1: (compile_expr e s) => [[carg s1]|]; last by [].
    rewrite /=.
    have Se := IH _ _ _ E1 Hvce Hvi.
    case Heqb: (Component.eqb C' C).
    +
      have EC : C' = C by apply/Nat.eqb_eq.
      subst C'.
      move: Hvcall. rewrite eqxx => Hfind.
      case EL: (getm P_labels P') => [tl|]; last by [].
      rewrite /=. move=> [<- _].
      apply: code_shape_cat; first exact: Se.
      do 2!shape_step.
      apply: code_shape_cons_jal; first by exists P'.
      by do 3!shape_step.
    +
      have HneC : C <> C'.
      { move=> E. rewrite -E /Component.eqb Nat.eqb_refl in Heqb. discriminate Heqb. }
      have HneqOp : (C' == C) = false.
      { apply: negbTE. apply/negP => /eqP E. exact: HneC (esym E). }
      move: Hvcall. rewrite HneqOp => Himp.
      rewrite /=. move=> [<- _].
      apply: code_shape_cat; first exact: Se.
      do 6!shape_step.
      apply: code_shape_cons_call => //.
      by do 8!shape_step.
  -
    move: Hc => /= [<- _]. exact: code_shape_halt1.
Qed.

Lemma code_shape_cons_label l c :
  code_shape c -> code_shape (ILabel l :: c).
Proof.
  move=> [Bc Jc Kc Vc]. split.
  - move=> r' l' HIn. destruct HIn as [E|HIn]; [discriminate E|right; exact: Bc HIn].
  - move=> l' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Jc HIn].
  - move=> C0 P0 HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Kc HIn].
  - move=> v' r' HIn. destruct HIn as [E|HIn]; [discriminate E|exact: Vc HIn].
Qed.

Lemma compile_proc_shape :
  forall P e s c s',
    compile_proc P e s = Some (c, s') ->
    Source.valid_calls procs intf C (called_procedures e) ->
    Source.values_are_integers e ->
    Source.find_procedure procs C P ->
    code_shape c
    /\ exists pl, getm P_labels P = Some pl /\ List.In (ILabel pl) c.
Proof.
  move=> P e s c s' Hc Hvc Hvi Hfind.
  move: Hc; rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift /Comp.ret /=.
  case EL: (getm P_labels P) => [pl|]; last by [].
  rewrite /=.
  case E2: (fresh_label C s) => [[lmain s2]|]; last by [].
  rewrite /=.
  case E3: (fresh_label C s2) => [[lreturn s3]|]; last by [].
  rewrite /=.
  case E4: (compile_expr e s3) => [[pcode s4]|]; last by [].
  rewrite /=. move=> [<- _].
  have Se := compile_expr_shape _ _ _ _ E4 Hvc Hvi.
  case: (Component.eqb C Component.main && Procedure.eqb P Procedure.main).
  -
    case: (immediately_final e) => /=.
    + split.
      * repeat shape_step.
        apply: code_shape_cons_bnz; first by right; left.
        repeat shape_step.
        apply: code_shape_cons_label.
        repeat shape_step.
        apply: code_shape_cons_jal; first by exists P.
        repeat shape_step.
        apply: code_shape_cons_bnz; first by right; left.
        repeat shape_step.
        apply: code_shape_cons_label.
        repeat shape_step.
        apply: code_shape_cons_label.
        repeat shape_step.
        apply: code_shape_cat; first exact: Se.
        by repeat shape_step.
      * exists pl. split; first by [].
        rewrite /=. do 37![right]. by left.
    + split.
      * repeat shape_step.
        apply: code_shape_cons_bnz; first by right; left.
        repeat shape_step.
        apply: code_shape_cons_label.
        repeat shape_step.
        apply: code_shape_cons_jal; first by exists P.
        repeat shape_step.
        apply: code_shape_cons_bnz; first by right; left.
        repeat shape_step.
        apply: code_shape_cons_label.
        repeat shape_step.
        apply: code_shape_cons_label.
        repeat shape_step.
        apply: code_shape_cat; first exact: Se.
        by repeat shape_step.
      * exists pl. split; first by [].
        rewrite /=. do 36![right]. by left.
  -
    split.
    + repeat shape_step.
      apply: code_shape_cons_jal; first by exists P.
      repeat shape_step.
      apply: code_shape_cons_label.
      repeat shape_step.
      apply: code_shape_cat; first exact: Se.
      by repeat shape_step.
    + exists pl. split; first by [].
      rewrite /=. do 22![right]. by left.
Qed.

Lemma compile_procedures_aux_shape :
  forall (ps : list (Procedure.id * expr)) acc s cds s',
    compile_procedures_aux acc ps s = Some (cds, s') ->
    (forall P e, List.In (P, e) ps ->
       [/\ Source.find_procedure procs C P,
           Source.valid_calls procs intf C (called_procedures e)
         & Source.values_are_integers e]) ->
    [/\ (forall P, (P \in unzip1 cds) = (P \in unzip1 ps) || (P \in unzip1 acc))
      & (forall P cd, List.In (P, cd) cds ->
           List.In (P, cd) acc
           \/ (code_shape cd
               /\ exists pl, getm P_labels P = Some pl /\ List.In (ILabel pl) cd))].
Proof.
  elim=> [|[P e] ps IH] acc s cds s' /=.
  - rewrite /Comp.ret. move=> [<- _] _.
    split=> [P|P cd HIn]; [by []|by left].
  - rewrite /Comp.bind.
    case Ep: (compile_proc P e s) => [[cd0 s1]|]; last by [].
    rewrite /=. move=> Hc Hps.
    have [Hfind Hvc Hvi] := Hps P e (or_introl erefl).
    have [Scd Hlab] := compile_proc_shape _ _ _ _ _ Ep Hvc Hvi Hfind.
    have Hps' : forall P0 e0, List.In (P0, e0) ps ->
       [/\ Source.find_procedure procs C P0,
           Source.valid_calls procs intf C (called_procedures e0)
         & Source.values_are_integers e0].
    { move=> P0 e0 HIn0. exact: Hps _ _ (or_intror HIn0). }
    have [Hkeys Hcells] := IH _ _ _ _ Hc Hps'.
    split.
    + move=> P0. rewrite Hkeys /= !inE.
      by case: (P0 == P); rewrite //= ?orbT.
    + move=> P0 cd HIn0.
      case: (Hcells _ _ HIn0) => [HInacc|Hgood]; last by right.
      destruct HInacc as [E|HInacc]; last by left.
      case: E => E1 E2. subst P0 cd.
      right. by split; [exact: Scd|exact: Hlab].
Qed.

Lemma compile_procedures_shape :
  forall (ps : list (Procedure.id * expr)) s cds s',
    compile_procedures ps s = Some (cds, s') ->
    (forall P e, List.In (P, e) ps ->
       [/\ Source.find_procedure procs C P,
           Source.valid_calls procs intf C (called_procedures e)
         & Source.values_are_integers e]) ->
    [/\ (forall P, (P \in unzip1 cds) = (P \in unzip1 ps))
      & (forall P cd, List.In (P, cd) cds ->
           code_shape cd
           /\ exists pl, getm P_labels P = Some pl /\ List.In (ILabel pl) cd)].
Proof.
  move=> ps s cds s' Hc Hps.
  have [Hkeys Hcells] := compile_procedures_aux_shape _ _ _ _ _ Hc Hps.
  split.
  - move=> P. by rewrite Hkeys /= orbF.
  - move=> P cd HIn.
    by case: (Hcells _ _ HIn) => [[]|Hgood].
Qed.

End Shape.


Lemma compile_expr_frame :
  forall C' , C' <> C ->
  forall e s c s',
    compile_expr e s = Some (c, s') ->
    getm (next_label s') C' = getm (next_label s) C'.
Proof.
  move=> C' Hne.
  have HneqE : (C' == C) = false.
  { apply: negbTE. apply/negP => /eqP E. exact: Hne E. }
  elim=> [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
         |e IH|e IH|e1 IH1 e2 IH2|C0 P0 e IH|] s c s' Hc.
  - case: v Hc => [i|p|] Hc.
    + by move: Hc => /= [_ <-].
    + by move: Hc => /=.
    + by move: Hc => /=.
  - by move: Hc => /= [_ <-].
  - by move: Hc => /= [_ <-].
  -
    move: Hc; rewrite /= /Comp.bind /Comp.ret.
    case E1: (compile_expr e1 s) => [[c1 s1]|]; last by [].
    rewrite /=.
    case E2: (compile_expr e2 s1) => [[c2 s2]|]; last by [].
    rewrite /=. move=> [_ <-].
    by rewrite (IH2 _ _ _ E2) (IH1 _ _ _ E1).
  -
    move: Hc; rewrite /= /Comp.bind /Comp.ret.
    case E1: (compile_expr e1 s) => [[c1 s1]|]; last by [].
    rewrite /=.
    case E2: (compile_expr e2 s1) => [[c2 s2]|]; last by [].
    rewrite /=. move=> [_ <-].
    by rewrite (IH2 _ _ _ E2) (IH1 _ _ _ E1).
  -
    move: Hc; rewrite /= /Comp.bind /Comp.ret.
    case E1: (compile_expr e1 s) => [[c1 s1]|]; last by [].
    rewrite /=.
    case E2: (compile_expr e2 s1) => [[c2 s2]|]; last by [].
    rewrite /=.
    case E3: (compile_expr e3 s2) => [[c3 s3]|]; last by [].
    rewrite /= !fresh_labelE /=. move=> [_ <-].
    rewrite /= !setmE HneqE.
    by rewrite (IH3 _ _ _ E3) (IH2 _ _ _ E2) (IH1 _ _ _ E1).
  -
    move: Hc; rewrite /= /Comp.bind /Comp.ret.
    case E1: (compile_expr e s) => [[c1 s1]|]; last by [].
    rewrite /=. move=> [_ <-].
    exact: IH E1.
  -
    move: Hc; rewrite /= /Comp.bind /Comp.ret.
    case E1: (compile_expr e s) => [[c1 s1]|]; last by [].
    rewrite /=. move=> [_ <-].
    exact: IH E1.
  -
    move: Hc; rewrite /= /Comp.bind /Comp.ret.
    case E1: (compile_expr e1 s) => [[c1 s1]|]; last by [].
    rewrite /=.
    case E2: (compile_expr e2 s1) => [[c2 s2]|]; last by [].
    rewrite /=. move=> [_ <-].
    by rewrite (IH2 _ _ _ E2) (IH1 _ _ _ E1).
  -
    move: Hc; rewrite /= /Comp.bind /Comp.ret /find_proc_label /Comp.lift.
    case E1: (compile_expr e s) => [[carg s1]|]; last by [].
    rewrite /=.
    case Heqb: (Component.eqb C0 C).
    + case EL: (getm P_labels P0) => [tl|]; last by [].
      rewrite /=. move=> [_ <-].
      exact: IH E1.
    + move=> [_ <-].
      exact: IH E1.
  - by move: Hc => /= [_ <-].
Qed.

Lemma compile_expr_agree :
  forall e s1 s2 c1 c2 s1' s2',
    getm (next_label s1) C = getm (next_label s2) C ->
    compile_expr e s1 = Some (c1, s1') ->
    compile_expr e s2 = Some (c2, s2') ->
    c1 = c2 /\ getm (next_label s1') C = getm (next_label s2') C.
Proof.
  elim=> [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
         |e IH|e IH|e1 IH1 e2 IH2|C0 P0 e IH|] s1 s2 c1 c2 s1' s2' Hag Hc1 Hc2.
  - case: v Hc1 Hc2 => [i|p|] Hc1 Hc2.
    + move: Hc1 Hc2 => /= [<- <-] [<- <-]. by split.
    + by move: Hc1 => /=.
    + by move: Hc1 => /=.
  - move: Hc1 Hc2 => /= [<- <-] [<- <-]. by split.
  - move: Hc1 Hc2 => /= [<- <-] [<- <-]. by split.
  -
    move: Hc1; rewrite /= /Comp.bind /Comp.ret.
    case E1a: (compile_expr e1 s1) => [[c1a s1a]|]; last by [].
    rewrite /=.
    case E2a: (compile_expr e2 s1a) => [[c2a s2a]|]; last by [].
    rewrite /=. move=> [<- <-].
    move: Hc2; rewrite /= /Comp.bind /Comp.ret.
    case E1b: (compile_expr e1 s2) => [[c1b s1b]|]; last by [].
    rewrite /=.
    case E2b: (compile_expr e2 s1b) => [[c2b s2b]|]; last by [].
    rewrite /=. move=> [<- <-].
    have [Ec1 Hag1] := IH1 _ _ _ _ _ _ Hag E1a E1b.
    have [Ec2 Hag2] := IH2 _ _ _ _ _ _ Hag1 E2a E2b.
    subst c1b c2b. by split.
  -
    move: Hc1; rewrite /= /Comp.bind /Comp.ret.
    case E1a: (compile_expr e1 s1) => [[c1a s1a]|]; last by [].
    rewrite /=.
    case E2a: (compile_expr e2 s1a) => [[c2a s2a]|]; last by [].
    rewrite /=. move=> [<- <-].
    move: Hc2; rewrite /= /Comp.bind /Comp.ret.
    case E1b: (compile_expr e1 s2) => [[c1b s1b]|]; last by [].
    rewrite /=.
    case E2b: (compile_expr e2 s1b) => [[c2b s2b]|]; last by [].
    rewrite /=. move=> [<- <-].
    have [Ec1 Hag1] := IH1 _ _ _ _ _ _ Hag E1a E1b.
    have [Ec2 Hag2] := IH2 _ _ _ _ _ _ Hag1 E2a E2b.
    subst c1b c2b. by split.
  -
    move: Hc1; rewrite /= /Comp.bind /Comp.ret.
    case E1a: (compile_expr e1 s1) => [[c1a s1a]|]; last by [].
    rewrite /=.
    case E2a: (compile_expr e2 s1a) => [[c2a s2a]|]; last by [].
    rewrite /=.
    case E3a: (compile_expr e3 s2a) => [[c3a s3a]|]; last by [].
    rewrite /= !fresh_labelE /=. move=> [<- <-].
    move: Hc2; rewrite /= /Comp.bind /Comp.ret.
    case E1b: (compile_expr e1 s2) => [[c1b s1b]|]; last by [].
    rewrite /=.
    case E2b: (compile_expr e2 s1b) => [[c2b s2b]|]; last by [].
    rewrite /=.
    case E3b: (compile_expr e3 s2b) => [[c3b s3b]|]; last by [].
    rewrite /= !fresh_labelE /=. move=> [<- <-].
    have [Ec1 Hag1] := IH1 _ _ _ _ _ _ Hag E1a E1b.
    have [Ec2 Hag2] := IH2 _ _ _ _ _ _ Hag1 E2a E2b.
    have [Ec3 Hag3] := IH3 _ _ _ _ _ _ Hag2 E3a E3b.
    subst c1b c2b c3b.
    rewrite !setmE !eqxx /= Hag3.
    by split.
  -
    move: Hc1; rewrite /= /Comp.bind /Comp.ret.
    case E1a: (compile_expr e s1) => [[c1a s1a]|]; last by [].
    rewrite /=. move=> [<- <-].
    move: Hc2; rewrite /= /Comp.bind /Comp.ret.
    case E1b: (compile_expr e s2) => [[c1b s1b]|]; last by [].
    rewrite /=. move=> [<- <-].
    have [Ec1 Hag1] := IH _ _ _ _ _ _ Hag E1a E1b.
    subst c1b. by split.
  -
    move: Hc1; rewrite /= /Comp.bind /Comp.ret.
    case E1a: (compile_expr e s1) => [[c1a s1a]|]; last by [].
    rewrite /=. move=> [<- <-].
    move: Hc2; rewrite /= /Comp.bind /Comp.ret.
    case E1b: (compile_expr e s2) => [[c1b s1b]|]; last by [].
    rewrite /=. move=> [<- <-].
    have [Ec1 Hag1] := IH _ _ _ _ _ _ Hag E1a E1b.
    subst c1b. by split.
  -
    move: Hc1; rewrite /= /Comp.bind /Comp.ret.
    case E1a: (compile_expr e1 s1) => [[c1a s1a]|]; last by [].
    rewrite /=.
    case E2a: (compile_expr e2 s1a) => [[c2a s2a]|]; last by [].
    rewrite /=. move=> [<- <-].
    move: Hc2; rewrite /= /Comp.bind /Comp.ret.
    case E1b: (compile_expr e1 s2) => [[c1b s1b]|]; last by [].
    rewrite /=.
    case E2b: (compile_expr e2 s1b) => [[c2b s2b]|]; last by [].
    rewrite /=. move=> [<- <-].
    have [Ec1 Hag1] := IH1 _ _ _ _ _ _ Hag E1a E1b.
    have [Ec2 Hag2] := IH2 _ _ _ _ _ _ Hag1 E2a E2b.
    subst c1b c2b. by split.
  -
    move: Hc1; rewrite /= /Comp.bind /Comp.ret /find_proc_label /Comp.lift.
    case E1a: (compile_expr e s1) => [[carga s1a]|]; last by [].
    rewrite /=.
    move: Hc2; rewrite /= /Comp.bind /Comp.ret /find_proc_label /Comp.lift.
    case E1b: (compile_expr e s2) => [[cargb s1b]|]; last by [].
    rewrite /=.
    have [Ec1 Hag1] := IH _ _ _ _ _ _ Hag E1a E1b.
    subst cargb.
    case Heqb: (Component.eqb C0 C).
    + case EL: (getm P_labels P0) => [tl|]; last by [].
      rewrite /=. move=> [<- <-] [<- <-]. by split.
    + move=> [<- <-] [<- <-]. by split.
  - move: Hc1 Hc2 => /= [<- <-] [<- <-]. by split.
Qed.

Lemma compile_proc_frame :
  forall C', C' <> C ->
  forall P e s c s',
    compile_proc P e s = Some (c, s') ->
    getm (next_label s') C' = getm (next_label s) C'.
Proof.
  move=> C' Hne.
  have HneqE : (C' == C) = false.
  { apply: negbTE. apply/negP => /eqP E. exact: Hne E. }
  move=> P e s c s'.
  rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift /Comp.ret.
  case EL: (getm P_labels P) => [pl|]; last by [].
  rewrite /= !fresh_labelE /=.
  case E4: (compile_expr e _) => [[pcode s4]|]; last by [].
  rewrite /=. move=> [_ <-].
  rewrite (compile_expr_frame _ Hne _ _ _ _ E4) /= !setmE HneqE.
  by [].
Qed.

Lemma compile_proc_agree :
  forall P e s1 s2 c1 c2 s1' s2',
    getm (next_label s1) C = getm (next_label s2) C ->
    compile_proc P e s1 = Some (c1, s1') ->
    compile_proc P e s2 = Some (c2, s2') ->
    c1 = c2 /\ getm (next_label s1') C = getm (next_label s2') C.
Proof.
  move=> P e s1 s2 c1 c2 s1' s2' Hag.
  rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift /Comp.ret.
  case EL: (getm P_labels P) => [pl|]; last by [].
  rewrite /= !fresh_labelE /=.
  case E4a: (compile_expr e _) => [[pcodea s4a]|]; last by [].
  rewrite /=. move=> [<- <-].
  case E4b: (compile_expr e _) => [[pcodeb s4b]|]; last by [].
  rewrite /=. move=> [<- <-].
  have Hag2 : getm (next_label {| next_label := setm (setm (next_label s1) C
                     (1 + odflt 0 (getm (next_label s1) C))) C
                     (1 + odflt 0 (getm (setm (next_label s1) C
                        (1 + odflt 0 (getm (next_label s1) C))) C)) |}) C
            = getm (next_label {| next_label := setm (setm (next_label s2) C
                     (1 + odflt 0 (getm (next_label s2) C))) C
                     (1 + odflt 0 (getm (setm (next_label s2) C
                        (1 + odflt 0 (getm (next_label s2) C))) C)) |}) C.
  { by rewrite /= !setmE !eqxx /= Hag. }
  have [Ec Hag4] := compile_expr_agree _ _ _ _ _ _ _ Hag2 E4a E4b.
  subst pcodeb. split; last exact: Hag4.
  by rewrite !setmE !eqxx /= Hag.
Qed.

Lemma compile_procedures_aux_frame :
  forall C', C' <> C ->
  forall ps acc s out s',
    compile_procedures_aux acc ps s = Some (out, s') ->
    getm (next_label s') C' = getm (next_label s) C'.
Proof.
  move=> C' Hne.
  elim=> [|[P e] ps IH] acc s out s' /=.
  - rewrite /Comp.ret. by move=> [_ <-].
  - rewrite /Comp.bind.
    case Ep: (compile_proc P e s) => [[cd s1]|]; last by [].
    rewrite /=. move=> Hrest.
    by rewrite (IH _ _ _ _ Hrest) (compile_proc_frame _ Hne _ _ _ _ _ Ep).
Qed.

Lemma compile_procedures_aux_agree :
  forall ps acc s1 s2 out1 out2 s1' s2',
    getm (next_label s1) C = getm (next_label s2) C ->
    compile_procedures_aux acc ps s1 = Some (out1, s1') ->
    compile_procedures_aux acc ps s2 = Some (out2, s2') ->
    out1 = out2 /\ getm (next_label s1') C = getm (next_label s2') C.
Proof.
  elim=> [|[P e] ps IH] acc s1 s2 out1 out2 s1' s2' Hag /=.
  - rewrite /Comp.ret. move=> [<- <-] [<- <-]. by split.
  - rewrite /Comp.bind.
    case Epa: (compile_proc P e s1) => [[cda s1a]|]; last by [].
    rewrite /=. move=> Hrest1.
    case Epb: (compile_proc P e s2) => [[cdb s1b]|]; last by [].
    rewrite /=. move=> Hrest2.
    have [Ecd Hag1] := compile_proc_agree _ _ _ _ _ _ _ _ Hag Epa Epb.
    subst cdb.
    exact: IH Hag1 Hrest1 Hrest2.
Qed.

End WithComponent.

Lemma compile_expr_total :
  forall (C : Component.id) (lbp scr : Pointer.t) (P_labels : NMap label)
         (procs : NMap (NMap expr)) (intf : Program.interface) e,
    Source.valid_calls procs intf C (called_procedures e) ->
    Source.values_are_integers e ->
    (forall P', Source.find_procedure procs C P' -> isSome (getm P_labels P')) ->
    forall s, exists c s', compile_expr C lbp scr P_labels e s = Some (c, s').
Proof.
  move=> C lbp scr P_labels procs intf.
  elim=> [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
         |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] Hvc Hvi Hlab s.
  -
    case: v Hvc Hvi => [i|p|] _ Hvi.
    + by do 2 eexists.
    + by move: Hvi.
    + by move: Hvi.
  - by do 2 eexists.
  - by do 2 eexists.
  -
    have Hvc1 : Source.valid_calls procs intf C (called_procedures e1).
    { move=> x P0 Hx. apply: Hvc. by rewrite /= in_fsetU Hx. }
    have Hvc2 : Source.valid_calls procs intf C (called_procedures e2).
    { move=> x P0 Hx. apply: Hvc. by rewrite /= in_fsetU Hx orbT. }
    move: Hvi => /= /andP [Hvi1 Hvi2].
    have [c1 [s1 E1]] := IH1 Hvc1 Hvi1 Hlab s.
    have [c2 [s2 E2]] := IH2 Hvc2 Hvi2 Hlab s1.
    do 2 eexists.
    rewrite /= /Comp.bind E1 /= E2 /=. reflexivity.
  -
    have Hvc1 : Source.valid_calls procs intf C (called_procedures e1).
    { move=> x P0 Hx. apply: Hvc. by rewrite /= in_fsetU Hx. }
    have Hvc2 : Source.valid_calls procs intf C (called_procedures e2).
    { move=> x P0 Hx. apply: Hvc. by rewrite /= in_fsetU Hx orbT. }
    move: Hvi => /= /andP [Hvi1 Hvi2].
    have [c1 [s1 E1]] := IH1 Hvc1 Hvi1 Hlab s.
    have [c2 [s2 E2]] := IH2 Hvc2 Hvi2 Hlab s1.
    do 2 eexists.
    rewrite /= /Comp.bind E1 /= E2 /=. reflexivity.
  -
    have Hvc1 : Source.valid_calls procs intf C (called_procedures e1).
    { move=> x P0 Hx. apply: Hvc. by rewrite /= !in_fsetU Hx. }
    have Hvc2 : Source.valid_calls procs intf C (called_procedures e2).
    { move=> x P0 Hx. apply: Hvc. by rewrite /= !in_fsetU Hx orbT. }
    have Hvc3 : Source.valid_calls procs intf C (called_procedures e3).
    { move=> x P0 Hx. apply: Hvc. by rewrite /= !in_fsetU Hx !orbT. }
    move: Hvi => /= /and3P [Hvi1 Hvi2 Hvi3].
    have [c1 [s1 E1]] := IH1 Hvc1 Hvi1 Hlab s.
    have [c2 [s2 E2]] := IH2 Hvc2 Hvi2 Hlab s1.
    have [c3 [s3 E3]] := IH3 Hvc3 Hvi3 Hlab s2.
    have [l4 [s4 E4]] := fresh_label_total C s3.
    have [l5 [s5 E5]] := fresh_label_total C s4.
    do 2 eexists.
    rewrite /= /Comp.bind E1 /= E2 /= E3 /= E4 /= E5 /=. reflexivity.
  -
    have [c1 [s1 E1]] := IH Hvc Hvi Hlab s.
    do 2 eexists.
    rewrite /= /Comp.bind E1 /=. reflexivity.
  -
    have [c1 [s1 E1]] := IH Hvc Hvi Hlab s.
    do 2 eexists.
    rewrite /= /Comp.bind E1 /=. reflexivity.
  -
    have Hvc1 : Source.valid_calls procs intf C (called_procedures e1).
    { move=> x P0 Hx. apply: Hvc. by rewrite /= in_fsetU Hx. }
    have Hvc2 : Source.valid_calls procs intf C (called_procedures e2).
    { move=> x P0 Hx. apply: Hvc. by rewrite /= in_fsetU Hx orbT. }
    move: Hvi => /= /andP [Hvi1 Hvi2].
    have [c1 [s1 E1]] := IH1 Hvc1 Hvi1 Hlab s.
    have [c2 [s2 E2]] := IH2 Hvc2 Hvi2 Hlab s1.
    do 2 eexists.
    rewrite /= /Comp.bind E1 /= E2 /=. reflexivity.
  -
    have Hvce : Source.valid_calls procs intf C (called_procedures e).
    { move=> x P0 Hx. apply: Hvc. by rewrite /= in_fsetU1 Hx orbT. }
    have Hcall : (C', P') \in called_procedures (E_call C' P' e).
    { by rewrite /= in_fsetU1 eqxx. }
    have Hvcall := Hvc _ _ Hcall.
    move: Hvi => /= Hvi.
    have [carg [s1 E1]] := IH Hvce Hvi Hlab s.
    case Heqb: (Component.eqb C' C).
    +
      have EC : C' = C by apply/Nat.eqb_eq.
      subst C'.
      move: Hvcall. rewrite eqxx => Hfind.
      have Hl := Hlab _ Hfind.
      case EL: (getm P_labels P') Hl => [tl|] Hl; last by discriminate Hl.
      do 2 eexists.
      rewrite /Comp.bind E1 /= /find_proc_label /Comp.lift EL /=. reflexivity.
    + do 2 eexists.
      rewrite /Comp.bind E1 /=. reflexivity.
  - by do 2 eexists.
Qed.

Lemma compile_proc_total :
  forall (C : Component.id) (lbp scr : Pointer.t) (P_labels : NMap label)
         (procs : NMap (NMap expr)) (intf : Program.interface) P e,
    Source.valid_calls procs intf C (called_procedures e) ->
    Source.values_are_integers e ->
    (forall P', Source.find_procedure procs C P' -> isSome (getm P_labels P')) ->
    isSome (getm P_labels P) ->
    forall s, exists c s', compile_proc C lbp scr P_labels P e s = Some (c, s').
Proof.
  move=> C lbp scr P_labels procs intf P e Hvc Hvi Hlab HlabP s.
  case EL: (getm P_labels P) HlabP => [pl|] HlabP; last by discriminate HlabP.
  have [l2 [s2 E2]] := fresh_label_total C s.
  have [l3 [s3 E3]] := fresh_label_total C s2.
  have [pcode [s4 E4]] := compile_expr_total C lbp scr P_labels _ _ _ Hvc Hvi Hlab s3.
  do 2 eexists.
  rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift /Comp.ret EL /=.
  rewrite E2 /= E3 /= E4 /=. reflexivity.
Qed.

Lemma compile_procedures_aux_total :
  forall (C : Component.id) (lbp scr : Pointer.t) (P_labels : NMap label)
         (procs : NMap (NMap expr)) (intf : Program.interface)
         (ps : list (Procedure.id * expr)) acc s,
    (forall P e, List.In (P, e) ps ->
       [/\ Source.valid_calls procs intf C (called_procedures e),
           Source.values_are_integers e
         & isSome (getm P_labels P)]) ->
    (forall P', Source.find_procedure procs C P' -> isSome (getm P_labels P')) ->
    exists cds s', compile_procedures_aux C lbp scr P_labels acc ps s = Some (cds, s').
Proof.
  move=> C lbp scr P_labels procs intf.
  elim=> [|[P e] ps IH] acc s Hps Hlab /=.
  - by do 2 eexists.
  - have [Hvc Hvi HlabP] := Hps _ _ (or_introl erefl).
    have [cd [s1 E1]] := compile_proc_total C lbp scr P_labels _ _ _ _ Hvc Hvi Hlab HlabP s.
    have Hps' : forall P0 e0, List.In (P0, e0) ps ->
       [/\ Source.valid_calls procs intf C (called_procedures e0),
           Source.values_are_integers e0
         & isSome (getm P_labels P0)].
    { move=> P0 e0 HIn0. exact: Hps _ _ (or_intror HIn0). }
    have [cds [s' E']] := IH ((P, cd) :: acc) s1 Hps' Hlab.
    do 2 eexists.
    rewrite /Comp.bind E1 /=. exact: E'.
Qed.

Fixpoint gen_component_procedures_labels_aux
         (comp: Component.id) (acc: NMap label) (procs: list (Procedure.id * expr))
  : COMP (NMap label) :=
  match procs with
  | [] => ret acc
  | (P, _) :: procs' =>
    do freshl <- fresh_label comp;
    gen_component_procedures_labels_aux comp (setm acc P freshl) procs'
  end.

Definition gen_component_procedures_labels
         (comp: Component.id) (procs: list (Procedure.id * expr))
  : COMP (NMap label) :=
  gen_component_procedures_labels_aux comp emptym procs.

Fixpoint gen_all_procedures_labels_aux
         (acc: NMap (NMap label)) (procs: list (Component.id * NMap expr))
  : COMP (NMap (NMap label)) :=
  match procs with
  | [] => ret acc
  | (C, Cprocs) :: procs' =>
    do map <- gen_component_procedures_labels C (elementsm Cprocs);
    gen_all_procedures_labels_aux (setm acc C map) procs'
  end.

Definition gen_all_procedures_labels
         (procs: list (Component.id * NMap expr))
  : COMP (NMap (NMap label)) :=
  gen_all_procedures_labels_aux emptym procs.

Lemma gen_component_labels_aux_frame :
  forall comp C', C' <> comp ->
  forall ps acc s m s',
    gen_component_procedures_labels_aux comp acc ps s = Some (m, s') ->
    getm (next_label s') C' = getm (next_label s) C'.
Proof.
  move=> comp C' Hne.
  have HneqE : (C' == comp) = false.
  { apply: negbTE. apply/negP => /eqP E. exact: Hne E. }
  elim=> [|[P e] ps IH] acc s m s' /=.
  - rewrite /Comp.ret. by move=> [_ <-].
  - rewrite /Comp.bind fresh_labelE /=. move=> Hrest.
    by rewrite (IH _ _ _ _ Hrest) /= setmE HneqE.
Qed.

Lemma gen_component_labels_aux_agree :
  forall comp ps acc s1 s2 m1 m2 s1' s2',
    getm (next_label s1) comp = getm (next_label s2) comp ->
    gen_component_procedures_labels_aux comp acc ps s1 = Some (m1, s1') ->
    gen_component_procedures_labels_aux comp acc ps s2 = Some (m2, s2') ->
    m1 = m2
    /\ getm (next_label s1') comp = getm (next_label s2') comp.
Proof.
  move=> comp.
  elim=> [|[P e] ps IH] acc s1 s2 m1 m2 s1' s2' Hag /=.
  - rewrite /Comp.ret. move=> [<- <-] [<- <-]. by split.
  - rewrite /Comp.bind !fresh_labelE /=.
    rewrite Hag. move=> Hrest1 Hrest2.
    have Hag' : getm (next_label {| next_label := setm (next_label s1) comp
                    (1 + odflt 0 (getm (next_label s2) comp)) |}) comp
              = getm (next_label {| next_label := setm (next_label s2) comp
                    (1 + odflt 0 (getm (next_label s2) comp)) |}) comp.
    { by rewrite /= !setmE !eqxx. }
    exact: IH Hag' Hrest1 Hrest2.
Qed.

Lemma gen_all_labels_aux_untouched :
  forall (cs : list (Component.id * NMap expr)) acc s ml s' K,
    gen_all_procedures_labels_aux acc cs s = Some (ml, s') ->
    K \notin unzip1 cs ->
    getm ml K = getm acc K.
Proof.
  elim=> [|[C0 Cprocs0] cs IH] acc s ml s' K /=.
  - rewrite /Comp.ret. by move=> [<- _] _.
  - rewrite /Comp.bind.
    case Eg: (gen_component_procedures_labels C0 (elementsm Cprocs0) s)
      => [[m0 s1]|]; last by [].
    rewrite /=. move=> Hrest.
    rewrite inE negb_or => /andP [HneqK HnotinK].
    rewrite (IH _ _ _ _ _ Hrest HnotinK) setmE.
    by rewrite (negbTE HneqK).
Qed.

Lemma gen_all_labels_aux_frame :
  forall (cs : list (Component.id * NMap expr)) acc s ml s' C',
    gen_all_procedures_labels_aux acc cs s = Some (ml, s') ->
    C' \notin unzip1 cs ->
    getm (next_label s') C' = getm (next_label s) C'.
Proof.
  elim=> [|[C0 Cprocs0] cs IH] acc s ml s' C' /=.
  - rewrite /Comp.ret. by move=> [_ <-] _.
  - rewrite /Comp.bind.
    case Eg: (gen_component_procedures_labels C0 (elementsm Cprocs0) s)
      => [[m0 s1]|]; last by [].
    rewrite /=. move=> Hrest.
    rewrite inE negb_or => /andP [HneqK HnotinK].
    have HneC0 : C' <> C0.
    { move=> E. move: HneqK. by rewrite E eqxx. }
    rewrite (IH _ _ _ _ _ Hrest HnotinK).
    exact: (gen_component_labels_aux_frame _ _ HneC0 _ _ _ _ _ Eg).
Qed.

Lemma gen_all_labels_aux_getC :
  forall (cs : list (Component.id * NMap expr)) acc s ml s' C Cprocs,
    gen_all_procedures_labels_aux acc cs s = Some (ml, s') ->
    uniq (unzip1 cs) ->
    List.In (C, Cprocs) cs ->
    exists sC m sC',
      [/\ getm (next_label sC) C = getm (next_label s) C,
          gen_component_procedures_labels C (elementsm Cprocs) sC = Some (m, sC'),
          getm ml C = Some m
        & getm (next_label s') C = getm (next_label sC') C].
Proof.
  elim=> [|[C0 Cprocs0] cs IH] acc s ml s' C Cprocs //=.
  rewrite /Comp.bind.
  case Eg: (gen_component_procedures_labels C0 (elementsm Cprocs0) s)
    => [[m0 s1]|]; last by [].
  rewrite /=. move=> Hrest /andP [HC0 Huniq] [E|HIn].
  - case: E => E1 E2. subst C0 Cprocs0.
    exists s, m0, s1. split=> //.
    + by rewrite (gen_all_labels_aux_untouched _ _ _ _ _ _ Hrest HC0) setmE eqxx.
    + exact: (gen_all_labels_aux_frame _ _ _ _ _ _ Hrest HC0).
  - have HneC0 : C <> C0.
    { move=> E. subst C0. move: HC0. by rewrite (In_unzip1_mem HIn). }
    have [sC [m [sC' [Hag Hg Hml Hfin]]]] := IH _ _ _ _ _ _ Hrest Huniq HIn.
    exists sC, m, sC'. split=> //.
    rewrite Hag.
    exact: (gen_component_labels_aux_frame _ _ HneC0 _ _ _ _ _ Eg).
Qed.

Lemma gen_component_procedures_labels_aux_spec :
  forall comp (ps : list (Procedure.id * expr)) acc s,
  exists m s',
    gen_component_procedures_labels_aux comp acc ps s = Some (m, s')
    /\ forall P, isSome (m P) = (P \in unzip1 ps) || isSome (acc P).
Proof.
  move=> comp. elim=> [|[P e] ps IH] acc s /=.
  - by exists acc, s.
  - have [l [s1 Hfl]] := fresh_label_total comp s.
    have [m [s' [Haux Hdom]]] := IH (setm acc P l) s1.
    exists m, s'. split.
    + rewrite /Comp.bind Hfl. exact: Haux.
    + move=> P0. rewrite Hdom setmE inE.
      by case: (P0 == P); rewrite /= ?orbT ?orbF.
Qed.

Lemma gen_component_procedures_labels_spec :
  forall comp (ps : list (Procedure.id * expr)) s,
  exists m s',
    gen_component_procedures_labels comp ps s = Some (m, s')
    /\ forall P, isSome (m P) = (P \in unzip1 ps).
Proof.
  move=> comp ps s.
  have [m [s' [Hgen Hdom]]] := gen_component_procedures_labels_aux_spec comp ps emptym s.
  exists m, s'. split=> // P.
  by rewrite Hdom emptymE orbF.
Qed.

Lemma gen_all_procedures_labels_aux_spec :
  forall (cs : list (Component.id * NMap expr)) acc s,
    uniq (unzip1 cs) ->
    exists ml s',
      gen_all_procedures_labels_aux acc cs s = Some (ml, s')
      /\ (forall C, C \notin unzip1 cs -> ml C = acc C)
      /\ (forall C, isSome (ml C) = (C \in unzip1 cs) || isSome (acc C))
      /\ (forall C Cprocs, List.In (C, Cprocs) cs ->
            exists plm, ml C = Some plm
              /\ forall P, isSome (plm P) = (P \in domm Cprocs)).
Proof.
  elim=> [|[C0 Cprocs0] cs IH] acc s /= Huniq.
  - exists acc, s.
    split; first by [].
    split; first by [].
    split; first by [].
    by move=> C Cprocs [].
  - move: Huniq => /andP [HC0 Huniq].
    have [plm0 [s1 [Hgen0 Hdom0]]]
      := gen_component_procedures_labels_spec C0 (elementsm Cprocs0) s.
    have [ml [s' [Haux [Huntouched [Hdom HIn]]]]] := IH (setm acc C0 plm0) s1 Huniq.
    exists ml, s'. split; last split; last split.
    + rewrite /Comp.bind Hgen0. exact: Haux.
    + move=> C. rewrite inE negb_or => /andP [HneqC HnotinC].
      rewrite (Huntouched _ HnotinC) setmE.
      by rewrite (negbTE HneqC).
    + move=> C. rewrite Hdom setmE inE.
      by case: (C == C0); rewrite /= ?orbT ?orbF.
    + move=> C Cprocs [E|HInC].
      * case: E => E1 E2. subst C0 Cprocs0.
        exists plm0. split.
        { rewrite (Huntouched _ HC0) setmE eqxx. by []. }
        { move=> P. by rewrite Hdom0 unzip1_elementsm_domm. }
      * exact: HIn HInC.
Qed.

Lemma gen_all_procedures_labels_spec :
  forall (cs : list (Component.id * NMap expr)) s,
    uniq (unzip1 cs) ->
    exists ml s',
      gen_all_procedures_labels cs s = Some (ml, s')
      /\ (forall C, isSome (ml C) = (C \in unzip1 cs))
      /\ (forall C Cprocs, List.In (C, Cprocs) cs ->
            exists plm, ml C = Some plm
              /\ forall P, isSome (plm P) = (P \in domm Cprocs)).
Proof.
  move=> cs s Huniq.
  have [ml [s' [Hgen [_ [Hdom HIn]]]]]
    := gen_all_procedures_labels_aux_spec cs emptym s Huniq.
  exists ml, s'. split=> //. split=> // C.
  by rewrite Hdom emptymE orbF.
Qed.

Definition gen_buffers
         (bufs: {fmap Component.id -> nat + list value})
  : NMap {fmap Block.id -> nat + list value} :=
  mapm (fun init_info => mkfmap [(0, init_info); (1, inr [:: Undef; Int 0])]) bufs.

Lemma gen_buffers_domm bufs : domm (gen_buffers bufs) = domm bufs.
Proof. exact: domm_map. Qed.

Lemma gen_buffers_block0 bufs Cid bs :
  getm (gen_buffers bufs) Cid = Some bs -> List.In 0 (map fst bs).
Proof.
  rewrite /gen_buffers mapmE.
  case E: (getm bufs Cid) => [bi|] //= [<-].
  have H0 : getm (mkfmap [:: (0, bi); (1, inr [:: Undef; Int 0])]) 0 = Some bi
    by rewrite mkfmapE.
  have := getm_In_elementsm H0.
  exact: (List.in_map fst).
Qed.

Lemma gen_buffers_block1 bufs Cid bs :
  getm (gen_buffers bufs) Cid = Some bs -> List.In 1 (map fst bs).
Proof.
  rewrite /gen_buffers mapmE.
  case E: (getm bufs Cid) => [bi|] //= [<-].
  have H1 : getm (mkfmap [:: (0, bi); (1, inr [:: Undef; Int 0])]) 1
            = Some (inr [:: Undef; Int 0]) by rewrite mkfmapE.
  have := getm_In_elementsm H1.
  exact: (List.in_map fst).
Qed.

Fixpoint compile_components_aux
         (local_buffers : NMap {fmap Block.id -> nat + list value})
         (procs_labels : NMap (NMap label))
         (acc: list (Component.id * NMap code))
         (cs: list (Component.id * NMap expr))
  : COMP (list (Component.id * NMap code)) :=
  match cs with
  | [] => ret acc
  | (C,procs) :: cs' =>
    let local_buffer_block_id := 0 in
    let scratch_block_id := 1 in
    do blocks <- lift (local_buffers C);
    do! lift (blocks local_buffer_block_id );
    do P_labels <- lift (procs_labels C);
    do procs_code <- compile_procedures C (C, local_buffer_block_id, 0%Z)
                                        (C, scratch_block_id, 0%Z) P_labels
                                        (elementsm procs);
    compile_components_aux local_buffers procs_labels
                           ((C, mkfmap procs_code) :: acc) cs'
  end.

Definition compile_components
         (local_buffers : NMap {fmap Block.id -> nat + list value})
         (procs_labels : NMap (NMap label))
         (comps: list (Component.id * NMap expr))
  : COMP (list (Component.id * NMap code)) :=
  compile_components_aux local_buffers procs_labels [] comps.

Lemma compile_components_aux_untouched :
  forall lb pls (cs : list (Component.id * NMap expr)) acc s out s' K,
    compile_components_aux lb pls acc cs s = Some (out, s') ->
    K \notin unzip1 cs ->
    getm_def out K = getm_def acc K.
Proof.
  move=> lb pls.
  elim=> [|[C0 Cprocs0] cs IH] acc s out s' K /=.
  - rewrite /Comp.ret. by move=> [<- _] _.
  - rewrite /Comp.bind /Comp.lift.
    case El1: (getm lb C0) => [blocks|]; last by [].
    rewrite /=.
    case El2: (getm blocks 0) => [binfo|]; last by [].
    rewrite /=.
    case El3: (getm pls C0) => [plm|]; last by [].
    rewrite /=.
    case Ecp: (compile_procedures C0 (C0, 0, 0%Z) (C0, 1, 0%Z) plm (elementsm Cprocs0) s)
      => [[cds s1]|]; last by [].
    rewrite /=. move=> Hrest.
    rewrite inE negb_or => /andP [HneqK HnotinK].
    rewrite (IH _ _ _ _ _ Hrest HnotinK) /=.
    by rewrite (negbTE HneqK).
Qed.

Lemma compile_components_aux_getC :
  forall lb pls (cs : list (Component.id * NMap expr)) acc s out s' C Cprocs,
    compile_components_aux lb pls acc cs s = Some (out, s') ->
    uniq (unzip1 cs) ->
    List.In (C, Cprocs) cs ->
    exists plm sC cds sC',
      [/\ getm pls C = Some plm,
          getm (next_label sC) C = getm (next_label s) C,
          compile_procedures C (C, 0, 0%Z) (C, 1, 0%Z) plm (elementsm Cprocs) sC
            = Some (cds, sC')
        & getm_def out C = Some (mkfmap cds)].
Proof.
  move=> lb pls.
  elim=> [|[C0 Cprocs0] cs IH] acc s out s' C Cprocs //=.
  rewrite /Comp.bind /Comp.lift.
  case El1: (getm lb C0) => [blocks|]; last by [].
  rewrite /=.
  case El2: (getm blocks 0) => [binfo|]; last by [].
  rewrite /=.
  case El3: (getm pls C0) => [plm0|]; last by [].
  rewrite /=.
  case Ecp: (compile_procedures C0 (C0, 0, 0%Z) (C0, 1, 0%Z) plm0 (elementsm Cprocs0) s)
    => [[cds0 s1]|]; last by [].
  rewrite /=. move=> Hrest /andP [HC0 Huniq] [E|HIn].
  - case: E => E1 E2. subst C0 Cprocs0.
    exists plm0, s, cds0, s1. split=> //.
    by rewrite (compile_components_aux_untouched _ _ _ _ _ _ _ _ Hrest HC0) /= eqxx.
  - have HneC0 : C <> C0.
    { move=> E. subst C0. move: HC0. by rewrite (In_unzip1_mem HIn). }
    have [plm [sC [cds [sC' [Hpls Hag Hg Hout]]]]] := IH _ _ _ _ _ _ Hrest Huniq HIn.
    exists plm, sC, cds, sC'. split=> //.
    rewrite Hag.
    exact: (compile_procedures_aux_frame _ _ _ _ _ HneC0 _ _ _ _ _ Ecp).
Qed.


Lemma compile_components_aux_total :
  forall (procs : NMap (NMap expr)) (intf : Program.interface)
         (lb : NMap {fmap Block.id -> nat + list value})
         (pls : NMap (NMap label))
         (cs : list (Component.id * NMap expr)) acc s,
    (forall Cid Cprocs, List.In (Cid, Cprocs) cs ->
       [/\ procs Cid = Some Cprocs,
           isSome (getm lb Cid),
           (forall bs, getm lb Cid = Some bs -> isSome (getm bs 0)),
           (exists plm, getm pls Cid = Some plm
              /\ forall P, isSome (getm plm P) = (P \in domm Cprocs))
         & forall P e, getm Cprocs P = Some e ->
             Source.valid_calls procs intf Cid (called_procedures e)
             /\ Source.values_are_integers e]) ->
    exists out s', compile_components_aux lb pls acc cs s = Some (out, s').
Proof.
  move=> procs intf lb pls.
  elim=> [|[C0 Cprocs0] cs IH] acc s Hcs /=.
  - by do 2 eexists.
  - have [Hproc Hlb Hbs0 [plm [Hplm Hplmdom]] Hwfes] := Hcs _ _ (or_introl erefl).
    case Elb: (getm lb C0) Hlb => [blocks|] Hlb; last by discriminate Hlb.
    have Hb0 := Hbs0 _ Elb.
    case Eb0: (getm blocks 0) Hb0 => [binfo|] Hb0; last by discriminate Hb0.
    have Hps : forall P e, List.In (P, e) (elementsm Cprocs0) ->
       [/\ Source.valid_calls procs intf C0 (called_procedures e),
           Source.values_are_integers e
         & isSome (getm plm P)].
    { move=> P e HIn.
      have He := In_elementsm_getm HIn.
      have [Hv Hi] := Hwfes _ _ He.
      split=> //.
      rewrite Hplmdom mem_domm He. by []. }
    have Hlabt : forall P', Source.find_procedure procs C0 P' -> isSome (getm plm P').
    { move=> P'. rewrite /Source.find_procedure Hproc.
      case Ee: (getm Cprocs0 P') => [e0|] // _.
      rewrite Hplmdom mem_domm Ee. by []. }
    have [cds [s1 E1]] := compile_procedures_aux_total C0 (C0, 0, 0%Z) (C0, 1, 0%Z) plm _ _ _ [::] s Hps Hlabt.
    have Hcs' : forall Cid Cprocs, List.In (Cid, Cprocs) cs ->
       [/\ procs Cid = Some Cprocs,
           isSome (getm lb Cid),
           (forall bs, getm lb Cid = Some bs -> isSome (getm bs 0)),
           (exists plm0, getm pls Cid = Some plm0
              /\ forall P, isSome (getm plm0 P) = (P \in domm Cprocs))
         & forall P e, getm Cprocs P = Some e ->
             Source.valid_calls procs intf Cid (called_procedures e)
             /\ Source.values_are_integers e].
    { move=> Cid Cp HIn. exact: Hcs _ _ (or_intror HIn). }
    have [out [s' E']] := IH ((C0, mkfmap cds) :: acc) s1 Hcs'.
    do 2 eexists.
    rewrite /Comp.bind /Comp.lift /= Eb0 /= Hplm /= /compile_procedures E1 /=. exact: E'.
Qed.


Lemma compile_components_aux_shape :
  forall (procs : NMap (NMap expr)) (intf : Program.interface)
         (local_buffers : NMap {fmap Block.id -> nat + list value})
         (procs_labels : NMap (NMap label))
         (cs : list (Component.id * NMap expr)),
  forall acc s out s',
    compile_components_aux local_buffers procs_labels acc cs s = Some (out, s') ->
    (forall Cid Cprocs, List.In (Cid, Cprocs) cs ->
       procs Cid = Some Cprocs
       /\ (forall P e, getm Cprocs P = Some e ->
             Source.valid_calls procs intf Cid (called_procedures e)
             /\ Source.values_are_integers e)) ->
    [/\ (forall Cid, (Cid \in unzip1 out) = (Cid \in unzip1 cs) || (Cid \in unzip1 acc))
      & (forall Cid cmap, List.In (Cid, cmap) out ->
           List.In (Cid, cmap) acc
           \/ exists Cprocs plm,
               [/\ procs Cid = Some Cprocs,
                   getm procs_labels Cid = Some plm,
                   (forall P, isSome (getm cmap P) = (P \in domm Cprocs))
                 & forall P cd, getm cmap P = Some cd ->
                     code_shape Cid (Cid, 0, 0%Z) (Cid, 1, 0%Z) plm procs intf cd
                     /\ exists pl, getm plm P = Some pl /\ List.In (ILabel pl) cd])].
Proof.
  move=> procs intf lb pls.
  elim=> [|[C0 Cprocs0] cs IH] acc s out s' /=.
  - rewrite /Comp.ret. move=> [<- _] _.
    split=> [Cid|Cid cmap HIn]; [by []|by left].
  - rewrite /Comp.bind /Comp.lift.
    case El1: (getm lb C0) => [blocks|]; last by [].
    rewrite /=.
    case El2: (getm blocks 0) => [binfo|]; last by [].
    rewrite /=.
    case El3: (getm pls C0) => [plm|]; last by [].
    rewrite /=.
    case Ecp: (compile_procedures C0 (C0, 0, 0%Z) (C0, 1, 0%Z) plm (elementsm Cprocs0) s)
      => [[cds s1]|]; last by [].
    rewrite /=. move=> Hc Hcs.
    have [Hproc Hwfes] := Hcs _ _ (or_introl erefl).
    have Hps : forall P e, List.In (P, e) (elementsm Cprocs0) ->
       [/\ Source.find_procedure procs C0 P,
           Source.valid_calls procs intf C0 (called_procedures e)
         & Source.values_are_integers e].
    { move=> P e HIn.
      have He := In_elementsm_getm HIn.
      have [Hv Hi] := Hwfes _ _ He.
      split=> //.
      by rewrite /Source.find_procedure Hproc He. }
    have [Hkeys Hcells] := compile_procedures_shape _ _ _ _ _ _ _ _ _ _ Ecp Hps.
    have Hcs' : forall Cid Cprocs, List.In (Cid, Cprocs) cs ->
       procs Cid = Some Cprocs
       /\ (forall P e, getm Cprocs P = Some e ->
             Source.valid_calls procs intf Cid (called_procedures e)
             /\ Source.values_are_integers e).
    { move=> Cid Cp HIn. exact: Hcs _ _ (or_intror HIn). }
    have [HkeysIH HcellsIH] := IH _ _ _ _ Hc Hcs'.
    split.
    + move=> Cid. rewrite HkeysIH /= !inE.
      by case: (Cid == C0); rewrite //= ?orbT.
    + move=> Cid cmap HIn0.
      case: (HcellsIH _ _ HIn0) => [HInacc|]; last by right.
      destruct HInacc as [E|HInacc]; last by left.
      case: E => E1 E2. subst Cid cmap.
      right. exists Cprocs0, plm. split.
      * exact: Hproc.
      * exact: El3.
      * move=> P. by rewrite mkfmapE getm_def_isSome Hkeys unzip1_elementsm_domm.
      * move=> P cd Hcd.
        move: Hcd. rewrite mkfmapE => Hcd.
        have HIncd := getm_def_In Hcd.
        exact: Hcells _ _ HIncd.
Qed.

Lemma compile_components_shape :
  forall (procs : NMap (NMap expr)) (intf : Program.interface)
         (local_buffers : NMap {fmap Block.id -> nat + list value})
         (procs_labels : NMap (NMap label))
         (cs : list (Component.id * NMap expr)) s out s',
    compile_components local_buffers procs_labels cs s = Some (out, s') ->
    (forall Cid Cprocs, List.In (Cid, Cprocs) cs ->
       procs Cid = Some Cprocs
       /\ (forall P e, getm Cprocs P = Some e ->
             Source.valid_calls procs intf Cid (called_procedures e)
             /\ Source.values_are_integers e)) ->
    [/\ (forall Cid, (Cid \in unzip1 out) = (Cid \in unzip1 cs))
      & (forall Cid cmap, List.In (Cid, cmap) out ->
           exists Cprocs plm,
               [/\ procs Cid = Some Cprocs,
                   getm procs_labels Cid = Some plm,
                   (forall P, isSome (getm cmap P) = (P \in domm Cprocs))
                 & forall P cd, getm cmap P = Some cd ->
                     code_shape Cid (Cid, 0, 0%Z) (Cid, 1, 0%Z) plm procs intf cd
                     /\ exists pl, getm plm P = Some pl /\ List.In (ILabel pl) cd])].
Proof.
  move=> procs intf lb pls cs s out s' Hc Hcs.
  have [Hkeys Hcells] := compile_components_aux_shape procs intf lb pls cs [::] s _ _ Hc Hcs.
  split.
  - move=> Cid. by rewrite Hkeys /= orbF.
  - move=> Cid cmap HIn.
    by case: (Hcells _ _ HIn) => [[]|Hgood].
Qed.


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
           Intermediate.prog_main := true |}
  | false => ret p
  end.

Definition compile_program
           (p: Source.program) : option Intermediate.program :=
  let comps := elementsm (Source.prog_procedures p) in
  let bufs := Source.prog_buffers p in
  let local_buffers := gen_buffers bufs in
  run init_env (
    do procs_labels <- gen_all_procedures_labels comps;
    do code <- compile_components local_buffers procs_labels comps;
    ret {| Intermediate.prog_interface := Source.prog_interface p;
           Intermediate.prog_procedures := mkfmap code;
           Intermediate.prog_buffers := local_buffers;
           Intermediate.prog_main := isSome (Source.prog_main p) |}).

Lemma compilation_preserves_interface:
  forall p p_compiled,
    compile_program p = Some p_compiled ->
    Intermediate.prog_interface p_compiled = Source.prog_interface p.
Proof.
  intros p p_compiled Hcompile.
  unfold compile_program, run in Hcompile.
  simpl in Hcompile. unfold Comp.bind in Hcompile.

  destruct (gen_all_procedures_labels (elementsm (Source.prog_procedures p)) init_env)
    as [[labels cenv1]|] eqn:Hlabs;
    try discriminate.
  destruct (compile_components (gen_buffers (Source.prog_buffers p)) labels
                               (elementsm (Source.prog_procedures p)) cenv1)
    as [[code cenv2]|] eqn:Hcompiled_comps;
    try discriminate.
  simpl in Hcompile.
  inversion Hcompile.
  reflexivity.
Qed.

Lemma compilation_preserves_linkability:
  forall {p p_compiled c c_compiled},
    Source.well_formed_program p ->
    Source.well_formed_program c ->
    linkable (Source.prog_interface p) (Source.prog_interface c) ->
    compile_program p = Some p_compiled ->
    compile_program c = Some c_compiled ->
    linkable (Intermediate.prog_interface p_compiled) (Intermediate.prog_interface c_compiled).
Proof.
  intros.
  repeat (erewrite compilation_preserves_interface; eauto).
Qed.

(* RB: TODO: Abstract find_procedure in Source (cprog_main_existence).
   Try to get rid of unnecessary clutter in statement and propagate. *)
Lemma compilation_preserves_main_flag:
  forall p p_compiled,
    compile_program p = Some p_compiled ->
    Intermediate.prog_main p_compiled = isSome (Source.prog_main p).
Proof.
  intros p p_compiled Hcompile.
  unfold compile_program, run in Hcompile.
  simpl in Hcompile. unfold Comp.bind in Hcompile.
  destruct (gen_all_procedures_labels (elementsm (Source.prog_procedures p)) init_env)
    as [[labels cenv1]|] eqn:Hlabs; try discriminate.
  destruct (compile_components (gen_buffers (Source.prog_buffers p)) labels
                               (elementsm (Source.prog_procedures p)) cenv1)
    as [[code cenv2]|] eqn:Hcompiled_comps; try discriminate.
  simpl in Hcompile.
  inversion Hcompile. reflexivity.
Qed.

Lemma compilation_preserves_main :
  forall {p p_compiled},
    Source.well_formed_program p ->
    compile_program p = Some p_compiled ->
    (exists main, Source.prog_main p = Some main) <->
    Intermediate.prog_main p_compiled.
Proof.
  intros p p_compiled Hp_well_formed Hp_compiles.
  rewrite (compilation_preserves_main_flag _ _ Hp_compiles).
  split.
  - intros [main Hm]. now rewrite Hm.
  - destruct (Source.prog_main p) as [m|] eqn:E; intros H.
    + now exists m.
    + discriminate H.
Qed.

Lemma compilation_preserves_linkable_mains : forall p1 p1' p2 p2',
  Source.well_formed_program p1 ->
  Source.well_formed_program p2 ->
  Source.linkable_mains p1 p2 ->
  compile_program p1 = Some p1' ->
  compile_program p2 = Some p2' ->
  Intermediate.linkable_mains p1' p2'.
Proof.
  unfold Source.linkable_mains, Intermediate.linkable_mains.
  intros p1 p1' p2 p2' Hwf1 Hwf2 Hmains Hcomp1 Hcomp2.
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
      specialize (Hcontra (ex_intro (fun x => Some id = Some x) id Logic.eq_refl));
      now destruct Hcontra.
  - destruct Hmain2 as [Hmain2 Hmain2'].
    destruct (Hmain2' Logic.eq_refl) as [? Hcontra]; inversion Hcontra.
  - destruct Hmain1 as [Hmain1 Hmain1'].
    destruct (Hmain1' Logic.eq_refl) as [? Hcontra]; inversion Hcontra.
  - destruct Hmain1 as [Hmain1 Hmain1'].
    destruct (Hmain1' Logic.eq_refl) as [? Hcontra]; inversion Hcontra.
Qed.

Lemma compilation_has_matching_mains :
  forall {p p_compiled},
    Source.well_formed_program p ->
    compile_program p = Some p_compiled ->
    matching_mains p p_compiled.
Proof.
  intros p p_compiled Hwf Hcomp.
  unfold matching_mains.
  rewrite (compilation_preserves_main_flag _ _ Hcomp).
  exact: iff_refl.
Qed.

Lemma compile_per_key :
  forall (csA csB : list (Component.id * NMap expr)) K Kprocs
         gbA gbB labelsA labelsB sA sB s1A s1B outA outB s2A s2B,
    uniq (unzip1 csA) -> uniq (unzip1 csB) ->
    List.In (K, Kprocs) csA -> List.In (K, Kprocs) csB ->
    gen_all_procedures_labels_aux emptym csA sA = Some (labelsA, s1A) ->
    gen_all_procedures_labels_aux emptym csB sB = Some (labelsB, s1B) ->
    getm (next_label sA) K = getm (next_label sB) K ->
    compile_components_aux gbA labelsA [::] csA s1A = Some (outA, s2A) ->
    compile_components_aux gbB labelsB [::] csB s1B = Some (outB, s2B) ->
    getm labelsA K = getm labelsB K /\ getm_def outA K = getm_def outB K.
Proof.
  move=> csA csB K Kprocs gbA gbB labelsA labelsB sA sB s1A s1B outA outB s2A s2B.
  move=> HuA HuB HInA HInB HlabA HlabB Hag0 HcompA HcompB.
  have [sKA [mA [sKA' [HagA HgA HmlA HfinA]]]]
    := gen_all_labels_aux_getC _ _ _ _ _ _ _ HlabA HuA HInA.
  have [sKB [mB [sKB' [HagB HgB HmlB HfinB]]]]
    := gen_all_labels_aux_getC _ _ _ _ _ _ _ HlabB HuB HInB.
  have HagK : getm (next_label sKA) K = getm (next_label sKB) K.
  { by rewrite HagA HagB Hag0. }
  have [Em HagK'] := gen_component_labels_aux_agree _ _ _ _ _ _ _ _ _ HagK HgA HgB.
  subst mB.
  have Hlabels_eq : getm labelsA K = getm labelsB K.
  { by rewrite HmlA HmlB. }
  split; first exact: Hlabels_eq.
  have [plmA [sCA [cdsA [sCA' [HplsA HagCA HgCA HoutA]]]]]
    := compile_components_aux_getC _ _ _ _ _ _ _ _ _ HcompA HuA HInA.
  have [plmB [sCB [cdsB [sCB' [HplsB HagCB HgCB HoutB]]]]]
    := compile_components_aux_getC _ _ _ _ _ _ _ _ _ HcompB HuB HInB.
  have EplmA : plmA = mA.
  { move: HplsA. rewrite HmlA. by case. }
  have EplmB : plmB = mA.
  { move: HplsB. rewrite HmlB. by case. }
  subst plmA plmB.
  have HagC : getm (next_label sCA) K = getm (next_label sCB) K.
  { rewrite HagCA HagCB HfinA HfinB. exact: HagK'. }
  have [Ecds _] := compile_procedures_aux_agree _ _ _ _ _ _ _ _ _ _ _ _ HagC HgCA HgCB.
  subst cdsB.
  by rewrite HoutA HoutB.
Qed.

Lemma gen_buffers_union bp bc :
  gen_buffers (unionm bp bc) = unionm (gen_buffers bp) (gen_buffers bc).
Proof.
  apply/eq_fmap => k.
  rewrite /gen_buffers mapmE !unionmE !mapmE.
  by case: (getm bp k) => [v|] /=.
Qed.

Lemma prog_main_link_flag (p c : Source.program) :
  fdisjoint (domm (Source.prog_procedures p)) (domm (Source.prog_procedures c)) ->
  isSome (Source.prog_main (Source.program_link p c))
  = isSome (Source.prog_main p) || isSome (Source.prog_main c).
Proof.
  move=> Hdisj.
  rewrite /Source.prog_main /Source.find_procedure /= unionmE.
  case Ep: (getm (Source.prog_procedures p) Component.main) => [mp|] /=.
  - case Emp: (getm mp Procedure.main) => //=.
    have Hmemp : Component.main \in domm (Source.prog_procedures p).
    { by rewrite mem_domm Ep. }
    have Hnotc := fdisjointP Hdisj _ Hmemp.
    case Ec: (getm (Source.prog_procedures c) Component.main) => [mc|] //=.
    move: Hnotc. by rewrite mem_domm Ec.
  - by [].
Qed.

(* Local Axiom separate_compilation: *)
(*   forall p c p_comp c_comp, *)
(*     Source.well_formed_program p -> *)
(*     Source.well_formed_program c -> *)
(*     linkable (Source.prog_interface p) (Source.prog_interface c) -> *)
(*     compile_program p = Some p_comp -> *)
(*     compile_program c = Some c_comp -> *)
(*     compile_program (Source.program_link p c) *)
(*     = Some (Intermediate.program_link p_comp c_comp). *)

Theorem separate_compilation:
  forall p c p_comp c_comp pc_comp,
    Source.well_formed_program p ->
    Source.well_formed_program c ->
    linkable (Source.prog_interface p) (Source.prog_interface c) ->
    compile_program p = Some p_comp ->
    compile_program c = Some c_comp ->
    compile_program (Source.program_link p c) = Some pc_comp ->
    pc_comp = Intermediate.program_link p_comp c_comp.
Proof.
  move=> p c p_comp c_comp pc_comp Hwfp Hwfc Hlinkable Hcp Hcc Hcl.
  have Hdefp_p := Source.wfprog_defined_procedures Hwfp.
  have Hdefp_c := Source.wfprog_defined_procedures Hwfc.
  have Hwfpr_p := Source.wfprog_well_formed_procedures Hwfp.
  have Hwfpr_c := Source.wfprog_well_formed_procedures Hwfc.
  have Hwfl : Source.well_formed_program (Source.program_link p c)
    := Source.linking_well_formedness Hwfp Hwfc Hlinkable.
  have Hwfpr_l := Source.wfprog_well_formed_procedures Hwfl.
  have Hdisj_iface : fdisjoint (domm (Source.prog_interface p))
                               (domm (Source.prog_interface c)).
  { by case: Hlinkable. }
  have Hdisj_procs : fdisjoint (domm (Source.prog_procedures p))
                               (domm (Source.prog_procedures c)).
  { by rewrite -Hdefp_p -Hdefp_c. }
  have Hexcl : isSome (Source.prog_main p) -> isSome (Source.prog_main c) -> False.
  { rewrite /Source.prog_main /Source.find_procedure.
    case Ep: (getm (Source.prog_procedures p) Component.main) => [mp|] //.
    case Ec: (getm (Source.prog_procedures c) Component.main) => [mc|] // _ _.
    have Hmp : Component.main \in domm (Source.prog_procedures p)
      by rewrite mem_domm Ep.
    have := fdisjointP Hdisj_procs _ Hmp.
    by rewrite mem_domm Ec. }
  have Huniq_p : uniq (unzip1 (elementsm (Source.prog_procedures p)))
    := sorted_uniq (@Ord.lt_trans _) (@Ord.ltxx _) (valP (Source.prog_procedures p)).
  have Huniq_c : uniq (unzip1 (elementsm (Source.prog_procedures c)))
    := sorted_uniq (@Ord.lt_trans _) (@Ord.ltxx _) (valP (Source.prog_procedures c)).
  have Huniq_l : uniq (unzip1 (elementsm (unionm (Source.prog_procedures p)
                                                 (Source.prog_procedures c))))
    := sorted_uniq (@Ord.lt_trans _) (@Ord.ltxx _)
         (valP (unionm (Source.prog_procedures p) (Source.prog_procedures c))).
  move: Hcl. rewrite {1}/compile_program /Comp.run /= /Comp.bind /=.
  case ElabL: (gen_all_procedures_labels
                 (elementsm (Source.prog_procedures (Source.program_link p c))) init_env)
    => [[labelsL cenvL1]|]; last by [].
  rewrite /=.
  case EcompL: (compile_components _ labelsL _ cenvL1) => [[codeL cenvL2]|]; last by [].
  rewrite /=.
  move: Hcp. rewrite {1}/compile_program /Comp.run /= /Comp.bind /=.
  case ElabP: (gen_all_procedures_labels (elementsm (Source.prog_procedures p)) init_env)
    => [[labelsP cenvP1]|]; last by [].
  rewrite /=.
  case EcompP: (compile_components _ labelsP _ cenvP1) => [[codeP cenvP2]|]; last by [].
  rewrite /=.
  move: Hcc. rewrite {1}/compile_program /Comp.run /= /Comp.bind /=.
  case ElabC: (gen_all_procedures_labels (elementsm (Source.prog_procedures c)) init_env)
    => [[labelsC cenvC1]|]; last by [].
  rewrite /=.
  case EcompC: (compile_components _ labelsC _ cenvC1) => [[codeC cenvC2]|]; last by [].
  rewrite /=.
  have Hcs_of : forall (x : Source.program),
      Source.well_formed_program x ->
      forall Cid Cprocs,
        List.In (Cid, Cprocs) (elementsm (Source.prog_procedures x)) ->
        Source.prog_procedures x Cid = Some Cprocs
        /\ (forall P e, getm Cprocs P = Some e ->
              Source.valid_calls (Source.prog_procedures x) (Source.prog_interface x)
                Cid (called_procedures e)
              /\ Source.values_are_integers e).
  { move=> x Hwfx Cid Cprocs HIn.
    have Hget := In_elementsm_getm HIn.
    split=> // P e He.
    have Hfp : Source.find_procedure (Source.prog_procedures x) Cid P = Some e.
    { by rewrite /Source.find_procedure Hget He. }
    by case: (Source.wfprog_well_formed_procedures Hwfx Hfp). }
  have [HkeysL _] := compile_components_shape
    (Source.prog_procedures (Source.program_link p c))
    (Source.prog_interface (Source.program_link p c)) _ _ _ _ _ _ EcompL (Hcs_of _ Hwfl).
  have [HkeysP _] := compile_components_shape
    (Source.prog_procedures p) (Source.prog_interface p) _ _ _ _ _ _ EcompP (Hcs_of _ Hwfp).
  have [HkeysC _] := compile_components_shape
    (Source.prog_procedures c) (Source.prog_interface c) _ _ _ _ _ _ EcompC (Hcs_of _ Hwfc).
  have HdomL : forall K, isSome (getm (mkfmap codeL) K)
                  = (K \in domm (unionm (Source.prog_procedures p)
                                        (Source.prog_procedures c))).
  { move=> K. by rewrite mkfmapE getm_def_isSome HkeysL unzip1_elementsm_domm. }
  have HdomP : forall K, isSome (getm (mkfmap codeP) K)
                  = (K \in domm (Source.prog_procedures p)).
  { move=> K. by rewrite mkfmapE getm_def_isSome HkeysP unzip1_elementsm_domm. }
  have HdomC : forall K, isSome (getm (mkfmap codeC) K)
                  = (K \in domm (Source.prog_procedures c)).
  { move=> K. by rewrite mkfmapE getm_def_isSome HkeysC unzip1_elementsm_domm. }
  have Hkey : forall K, getm (mkfmap codeL) K
                 = getm (unionm (mkfmap codeP) (mkfmap codeC)) K.
  { move=> K. rewrite unionmE.
    case EKp: (getm (Source.prog_procedures p) K) => [Kprocs|].
    -
      have HInP : List.In (K, Kprocs) (elementsm (Source.prog_procedures p))
        := getm_In_elementsm EKp.
      have EKl : getm (unionm (Source.prog_procedures p) (Source.prog_procedures c)) K
                 = Some Kprocs.
      { by rewrite unionmE EKp. }
      have HInL : List.In (K, Kprocs)
                    (elementsm (unionm (Source.prog_procedures p)
                                       (Source.prog_procedures c)))
        := getm_In_elementsm EKl.
      have [_ Hout_eq] := compile_per_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Huniq_l Huniq_p HInL HInP ElabL ElabP erefl EcompL EcompP.
      have HL : getm (mkfmap codeL) K = getm (mkfmap codeP) K.
      { by rewrite !mkfmapE Hout_eq. }
      rewrite HL.
      have HPk : isSome (getm (mkfmap codeP) K) = true.
      { by rewrite HdomP mem_domm EKp. }
      by case: (getm (mkfmap codeP) K) HPk.
    -
      have HPnone : getm (mkfmap codeP) K = None.
      { have := HdomP K. rewrite mem_domm EKp /=.
        by case: (getm (mkfmap codeP) K). }
      rewrite HPnone.
      case EKc: (getm (Source.prog_procedures c) K) => [Kprocs|].
      + have HInC : List.In (K, Kprocs) (elementsm (Source.prog_procedures c))
          := getm_In_elementsm EKc.
        have EKl : getm (unionm (Source.prog_procedures p) (Source.prog_procedures c)) K
                   = Some Kprocs.
        { by rewrite unionmE EKp. }
        have HInL : List.In (K, Kprocs)
                      (elementsm (unionm (Source.prog_procedures p)
                                         (Source.prog_procedures c)))
          := getm_In_elementsm EKl.
        have [_ Hout_eq] := compile_per_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          Huniq_l Huniq_c HInL HInC ElabL ElabC erefl EcompL EcompC.
        by rewrite !mkfmapE Hout_eq.
      + have HLnone : getm (mkfmap codeL) K = None.
        { have := HdomL K. rewrite mem_domm unionmE EKp EKc /=.
          by case: (getm (mkfmap codeL) K). }
        have HCnone : getm (mkfmap codeC) K = None.
        { have := HdomC K. rewrite mem_domm EKc /=.
          by case: (getm (mkfmap codeC) K). }
        by rewrite HLnone HCnone. }
  have Hlab_main : getm labelsL Component.main = getm labelsP Component.main
                   \/ getm labelsL Component.main = getm labelsC Component.main.
  { case EKp: (getm (Source.prog_procedures p) Component.main) => [Kprocs|].
    - left.
      have HInP := getm_In_elementsm EKp.
      have EKl : getm (unionm (Source.prog_procedures p) (Source.prog_procedures c))
                   Component.main = Some Kprocs.
      { by rewrite unionmE EKp. }
      have HInL := getm_In_elementsm EKl.
      have [Hlab_eq _] := compile_per_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Huniq_l Huniq_p HInL HInP ElabL ElabP erefl EcompL EcompP.
      exact: Hlab_eq.
    - case EKc: (getm (Source.prog_procedures c) Component.main) => [Kprocs|].
      + right.
        have HInC := getm_In_elementsm EKc.
        have EKl : getm (unionm (Source.prog_procedures p) (Source.prog_procedures c))
                     Component.main = Some Kprocs.
        { by rewrite unionmE EKp. }
        have HInL := getm_In_elementsm EKl.
        have [Hlab_eq _] := compile_per_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          Huniq_l Huniq_c HInL HInC ElabL ElabC erefl EcompL EcompC.
        exact: Hlab_eq.
      + left.
        have H1 : getm labelsL Component.main = None.
        { have [ml [sl [El [Hd _]]]] := gen_all_procedures_labels_spec
            (elementsm (unionm (Source.prog_procedures p) (Source.prog_procedures c)))
            init_env Huniq_l.
          rewrite El in ElabL. case: ElabL => ? ?; subst ml sl.
          have := Hd Component.main.
          rewrite unzip1_elementsm_domm mem_domm unionmE EKp EKc /=.
          by case: (getm labelsL Component.main). }
        have H2 : getm labelsP Component.main = None.
        { have [ml [sl [El [Hd _]]]] := gen_all_procedures_labels_spec
            (elementsm (Source.prog_procedures p)) init_env Huniq_p.
          rewrite El in ElabP. case: ElabP => ? ?; subst ml sl.
          have := Hd Component.main.
          rewrite unzip1_elementsm_domm mem_domm EKp /=.
          by case: (getm labelsP Component.main). }
        by rewrite H1 H2. }
  have Hflag : isSome (Source.prog_main (Source.program_link p c))
               = isSome (Source.prog_main p) || isSome (Source.prog_main c)
    := prog_main_link_flag _ _ Hdisj_procs.
  rewrite Hflag.
  move=> [<-] [<-] [<-].
  rewrite /Intermediate.program_link /=.
  congr Intermediate.mkProg.
  + apply/eq_fmap => K. exact: Hkey.
  + exact: gen_buffers_union.
Qed.

Lemma separate_compilation_weaker:
  forall p c pc_comp p_comp c_comp,
    Source.well_formed_program p ->
    Source.well_formed_program c ->
    linkable (Source.prog_interface p) (Source.prog_interface c) ->
    compile_program p = Some p_comp ->
    compile_program c = Some c_comp ->
    compile_program (Source.program_link p c) = Some pc_comp ->
    forall b, program_behaves (I.CS.sem pc_comp) b <->
              program_behaves (I.CS.sem (Intermediate.program_link p_comp c_comp)) b.
Proof.
  move=> p c pc_comp p_comp c_comp Hwfp Hwfc Hlinkable Hcp Hcc Hcl b.
  by rewrite (separate_compilation _ _ _ _ _ Hwfp Hwfc Hlinkable Hcp Hcc Hcl).
Qed.

Lemma compilation_preserves_well_formedness:
  forall {p p_compiled},
    Source.well_formed_program p ->
    compile_program p = Some p_compiled ->
    Intermediate.well_formed_program p_compiled.
Proof.
  move=> p pc Hwf Hcomp.
  have Hsound := Source.wfprog_interface_soundness Hwf.
  have Hdefp := Source.wfprog_defined_procedures Hwf.
  have Hexpe := Source.wfprog_exported_procedures_existence Hwf.
  have Hwfpr := Source.wfprog_well_formed_procedures Hwf.
  have Hdefb := Source.wfprog_defined_buffers Hwf.
  have Hmain_iff := Source.wfprog_main_existence Hwf.
  move: Hcomp.
  rewrite /compile_program /Comp.run /= /Comp.bind /=.
  case Elab: (gen_all_procedures_labels (elementsm (Source.prog_procedures p)) init_env)
    => [[labels cenv1]|]; last by [].
  rewrite /=.
  case Ecomp: (compile_components (gen_buffers (Source.prog_buffers p)) labels
                 (elementsm (Source.prog_procedures p)) cenv1) => [[code cenv2]|];
    last by [].
  rewrite /=.
  have Huniq : uniq (unzip1 (elementsm (Source.prog_procedures p))).
  { exact: (sorted_uniq (@Ord.lt_trans _) (@Ord.ltxx _)
              (valP (Source.prog_procedures p))). }
  have [ml [sl [Elab' [Hldom HlIn]]]]
    := gen_all_procedures_labels_spec (elementsm (Source.prog_procedures p)) init_env Huniq.
  rewrite Elab in Elab'. case: Elab' => E1 E2. subst ml sl.
  have Hcs : forall Cid Cprocs,
      List.In (Cid, Cprocs) (elementsm (Source.prog_procedures p)) ->
      Source.prog_procedures p Cid = Some Cprocs
      /\ (forall P e, getm Cprocs P = Some e ->
            Source.valid_calls (Source.prog_procedures p) (Source.prog_interface p)
              Cid (called_procedures e)
            /\ Source.values_are_integers e).
  { move=> Cid Cprocs HIn.
    have Hget := In_elementsm_getm HIn.
    split=> // P e He.
    have Hfp : Source.find_procedure (Source.prog_procedures p) Cid P = Some e.
    { by rewrite /Source.find_procedure Hget He. }
    have Hwfe := Hwfpr _ _ _ Hfp.
    by case: Hwfe. }
  have [HkeysC HcellsC]
    := compile_components_shape (Source.prog_procedures p) (Source.prog_interface p)
         _ _ _ _ _ _ Ecomp Hcs.
  have Hdomm_code : domm (mkfmap code) = domm (Source.prog_procedures p).
  { apply: domm_pointwise => k.
    by rewrite mkfmapE getm_def_isSome HkeysC unzip1_elementsm_domm mem_domm. }
  have Hcell : forall Cid cmap, getm (mkfmap code) Cid = Some cmap ->
      exists Cprocs plm,
        [/\ Source.prog_procedures p Cid = Some Cprocs,
            getm labels Cid = Some plm,
            (forall P, isSome (getm cmap P) = (P \in domm Cprocs))
          & forall P cd, getm cmap P = Some cd ->
              code_shape Cid (Cid, 0, 0%Z) (Cid, 1, 0%Z) plm (Source.prog_procedures p)
                         (Source.prog_interface p) cd
              /\ exists pl, getm plm P = Some pl /\ List.In (ILabel pl) cd].
  { move=> Cid cmap Hget.
    move: Hget. rewrite mkfmapE => /getm_def_In HIn.
    exact: HcellsC _ _ HIn. }
  have Hwfi_core : forall (pcF : Intermediate.program),
      Intermediate.prog_interface pcF = Source.prog_interface p ->
      Intermediate.prog_buffers pcF = gen_buffers (Source.prog_buffers p) ->
      (forall Cid cmap0 P0 Pc0,
          getm (mkfmap code) Cid = Some cmap0 -> getm cmap0 P0 = Some Pc0 ->
          exists cmapF, getm (Intermediate.prog_procedures pcF) Cid = Some cmapF
                   /\ getm cmapF P0 = Some Pc0) ->
      forall Cid cmap P Pcode,
        getm (mkfmap code) Cid = Some cmap ->
        getm cmap P = Some Pcode ->
        forall i, List.In i Pcode -> Intermediate.well_formed_instruction pcF Cid P i.
  { move=> pcF HFintf HFbuf HFemb Cid cmap P Pcode Hget HgetP i HIni.
    have [CprocsS [plm [HpsS Hplm Hkeys4 Hcells4]]] := Hcell _ _ Hget.
    have [Hshape _] := Hcells4 _ _ HgetP.
    case: Hshape => [Bs Js Ks Vs].
    case: i HIni => [|l|v r|r1 r2|bop r1 r2 r3|r1 r2|r1 r2|r1 r2|r l| |l|C' P'| |] HIni //.
    -
      case: v HIni => [z|ptr] HIni //.
      have Hv := Vs _ _ HIni.
      have HCdom : Cid \in domm (gen_buffers (Source.prog_buffers p)).
      { rewrite gen_buffers_domm -Hdefb Hdefp -Hdomm_code mem_domm Hget. by []. }
      case/dommP: HCdom => bs Hbs.
      case: Hv => [[iz Ez]|Eptr|Eptr|Eptr]; first by rewrite Ez.
      + rewrite Eptr /= HFbuf.
        exists bs. split; first exact: Hbs.
        exact: gen_buffers_block0 Hbs.
      + rewrite Eptr /= HFbuf.
        exists bs. split; first exact: Hbs.
        exact: gen_buffers_block1 Hbs.
      +
        rewrite Eptr /= HFbuf.
        exists bs. split; first exact: Hbs.
        exact: gen_buffers_block1 Hbs.
    -
      have Hlab := Bs _ _ HIni.
      have [cmapF [HgF HgFP]] := HFemb _ _ _ _ Hget HgetP.
      by exists cmapF, Pcode.
    -
      have [P'0 [Hpl Hfind0]] := Js _ HIni.
      move: Hfind0. rewrite /Source.find_procedure HpsS.
      case Ee: (getm CprocsS P'0) => [e0|] // _.
      have HP'dom : isSome (getm cmap P'0).
      { rewrite Hkeys4 mem_domm Ee. by []. }
      case Ec: (getm cmap P'0) HP'dom => [P'code|] // _.
      have [_ [pl0 [Hpl0 HInLab]]] := Hcells4 _ _ Ec.
      have Epl : pl0 = l. { move: Hpl0. rewrite Hpl. by case. }
      subst pl0.
      have [cmapF [HgF HgFP']] := HFemb _ _ _ _ Hget Ec.
      by exists cmapF, P'0, P'code.
    -
      have [Hne Himp] := Ks _ _ HIni.
      split; first exact: Hne.
      by rewrite HFintf.
  }
  rewrite /Comp.ret. move=> [<-].
  set pcF := {| Intermediate.prog_interface := Source.prog_interface p;
                Intermediate.prog_procedures := mkfmap code;
                Intermediate.prog_buffers := gen_buffers (Source.prog_buffers p);
                Intermediate.prog_main := isSome (Source.prog_main p) |}.
  split=> /=.
  + exact: Hsound.
  + by rewrite Hdefp -Hdomm_code.
  + move=> C CI HCI P Hexp.
    have Hfp := Hexpe _ _ (ex_intro _ CI (conj HCI Hexp)).
    move: Hfp. rewrite /Source.find_procedure.
    case Eps: (Source.prog_procedures p C) => [CprocsS|] //.
    case Ee: (getm CprocsS P) => [e|] // _.
    have HCc : isSome (getm (mkfmap code) C).
    { by rewrite -mem_domm Hdomm_code mem_domm Eps. }
    case Ecm: (getm (mkfmap code) C) HCc => [cmap|] // _.
    have [CprocsS' [plm' [HpsS' _ Hkeys' _]]] := Hcell _ _ Ecm.
    have E : CprocsS' = CprocsS.
    { move: HpsS'. rewrite Eps. by case. }
    subst CprocsS'.
    have HPk : isSome (getm cmap P).
    { rewrite Hkeys' mem_domm Ee. by []. }
    case Ecp: (getm cmap P) HPk => [Pcode|] HPk'; last by discriminate HPk'.
    exists cmap, Pcode. by split.
  + move=> C Cprocs0 HgetC P Pcode HgetP i HIni.
    have HFemb : forall Cid cmap0 P0 Pc0,
        getm (mkfmap code) Cid = Some cmap0 -> getm cmap0 P0 = Some Pc0 ->
        exists cmapF, getm (mkfmap code) Cid = Some cmapF /\ getm cmapF P0 = Some Pc0.
    { move=> Cid cmap0 P0 Pc0 Hg1 Hg2. exists cmap0. by split. }
    exact: (Hwfi_core pcF erefl erefl HFemb _ _ _ _ HgetC HgetP _ HIni).
  + by rewrite Hdefb gen_buffers_domm.
  +
    rewrite /pcF /= /Source.prog_main /Source.find_procedure.
    case Eps: (Source.prog_procedures p Component.main) => [CprocsS|] //.
    case Ee: (getm CprocsS Procedure.main) => [e|] // _.
    have HCc : isSome (getm (mkfmap code) Component.main).
    { by rewrite -mem_domm Hdomm_code mem_domm Eps. }
    case Ecm: (getm (mkfmap code) Component.main) HCc => [cmap|] // _.
    have [CprocsS' [plm' [HpsS' _ Hkeys' _]]] := Hcell _ _ Ecm.
    have E : CprocsS' = CprocsS.
    { move: HpsS'. rewrite Eps. by case. }
    subst CprocsS'.
    exists cmap. split; first by [].
    by rewrite mem_domm Hkeys' mem_domm Ee.
  +
    exact: Hmain_iff.
Qed.

Theorem well_formed_compilable :
  forall p,
    Source.well_formed_program p ->
  exists pc,
    compile_program p = Some pc.
Proof.
  move=> p Hwf.
  have Hdefp := Source.wfprog_defined_procedures Hwf.
  have Hwfpr := Source.wfprog_well_formed_procedures Hwf.
  have Hdefb := Source.wfprog_defined_buffers Hwf.
  have Hmain_iff := Source.wfprog_main_existence Hwf.
  have Huniq : uniq (unzip1 (elementsm (Source.prog_procedures p))).
  { exact: (sorted_uniq (@Ord.lt_trans _) (@Ord.ltxx _)
              (valP (Source.prog_procedures p))). }
  have [labels [s1 [Elab [Hldom HlIn]]]]
    := gen_all_procedures_labels_spec (elementsm (Source.prog_procedures p)) init_env Huniq.
  have Hcs : forall Cid Cprocs,
      List.In (Cid, Cprocs) (elementsm (Source.prog_procedures p)) ->
      [/\ Source.prog_procedures p Cid = Some Cprocs,
          isSome (getm (gen_buffers (Source.prog_buffers p)) Cid),
          (forall bs, getm (gen_buffers (Source.prog_buffers p)) Cid = Some bs ->
             isSome (getm bs 0)),
          (exists plm, getm labels Cid = Some plm
             /\ forall P, isSome (getm plm P) = (P \in domm Cprocs))
        & forall P e, getm Cprocs P = Some e ->
            Source.valid_calls (Source.prog_procedures p) (Source.prog_interface p)
              Cid (called_procedures e)
            /\ Source.values_are_integers e].
  { move=> Cid Cprocs HIn.
    have Hget := In_elementsm_getm HIn.
    split.
    - exact: Hget.
    - rewrite -mem_domm gen_buffers_domm -Hdefb Hdefp mem_domm Hget. by [].
    - move=> bs. rewrite /gen_buffers mapmE.
      case: (getm (Source.prog_buffers p) Cid) => [bi|] //.
      move=> [<-].
      have H0 : getm (mkfmap [:: (0, bi); (1, inr [:: Undef; Int 0])]) 0 = Some bi
    by rewrite mkfmapE.
      by rewrite H0.
    - exact: HlIn _ _ HIn.
    - move=> P e He.
      have Hfp : Source.find_procedure (Source.prog_procedures p) Cid P = Some e.
      { by rewrite /Source.find_procedure Hget He. }
      by case: (Hwfpr _ _ _ Hfp). }
  have [code [s2 Ecomp]]
    := compile_components_aux_total (Source.prog_procedures p) (Source.prog_interface p)
         _ _ _ [::] s1 Hcs.
  have Ecomp' : compile_components (gen_buffers (Source.prog_buffers p)) labels
                  (elementsm (Source.prog_procedures p)) s1 = Some (code, s2) := Ecomp.
  eexists.
  rewrite /compile_program /Comp.run /= /Comp.bind /= Elab /=.
  rewrite Ecomp' /=.
  reflexivity.
Qed.

