Require Import Common.Definitions.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Source.Language.
Require Import Source.CS.
Require Import Intermediate.Machine.
Require Import Intermediate.CS.
Require Import S2I.Compiler.
Require Import S2I.Definitions.

(*
Taking inspiration from DSSS17 Leroy's lectures:
https://github.com/DeepSpec/dsss17/blob/master/compiler/Compiler.v

We want to prove a forward simulation from the source to the
intermediate level. In order to do that, we need to define a relation
between source states and intermediate states that we will use to
prove the main argument: starting from related states s1 (source) and
s2 (intermediate), if s1 takes a step to s1', then s2 can take zero or
more steps ending in a state s2' which is related to s1'.

        (s1)           related_states           (s2)
     Source.state ----------------------- Intermediate.state
                  |                     |
                  |                     | *
                  |                     |
       (s1')      v                     v       (s2')
    Source.state' ----------------------- Intermediate.state'
                       related_states

With the above simulation diagram, we have to take into account the
infinite stuttering problem: s1 takes infinitely many silent steps, whereas
s2 stays still forever (the source program diverges, but the
intermediate one doesn't). In all those cases in which s2 takes zero
steps, we have to invent a strictly decreasing measure on terms.

When does infinite stuttering occur in our case? We need to look at all
the source steps which do not correspond to the execution of a machine instruction:
- KS_Binop1: (C, s, mem, k, E_binop op e1 e2) -> (C, s, mem, Kbinop1 op e2 k, e1)
- KS_Seq1: (C, s, mem, k, E_seq e1 e2) -> (C, s, mem, Kseq e2 k, e1)
- KS_If: (C, s, mem, k, E_if e1 e2 e3) -> (C, s, mem, Kif e2 e3 k, e1)
- KS_Alloc1: (C, s, mem, k, E_alloc e) -> (C, s, mem, Kalloc k, e)
- KS_Deref1: (C, s, mem, k, E_deref e) -> (C, s, mem, Kderef k, e)
- KS_Assign1: (C, s, mem, k, E_assign e1 e2) -> (C, s, mem, Kassign1 e1 k, e2)
- KS_Call1: (C, s, mem, k, E_call C' P e) -> (C, s, mem, Kcall C' P k, e)

TODO find a measure for those cases

To relate source states with intermediate states, we need to define:
1. how a source expression is related to an instruction sequence
   (see codeseq_at in DSSS17)
2. how a source continuation is related to the remaining instructions
   (see compile_cont in DSSS17)

TODO define these two relations

Invariants of our compiled code:
- at the end of a sequence of compiled instructions, the register RCOM
  contains the evaluation result of the compiled expression
- at the end of a sequence of compiled instructions, the stack pointer
  is the same as the one with which the sequence started (basically, we
  handle the stack correctly, each PUSH has an associated POP)
- the register R_ONE always contains the value 1 (whenever we invalidate
  it during calls/returns, we have to restore it)
- the register R_AUX2 contains the origin of the call (1 if external, 0 otherwise)

At some point we will have to show that we allocated enough space for
the current stack frame (i.e. temporary values).

TODO how do we prove this fact?

Finally, we need to prove that initial states are related, and that final states
are quasi-related (we can take zero or more steps to reach an halt instruction).

TODO define and prove these lemmas

Once we have the above things, we can package them in forward_simulation object
defined by CompCert. Determinacy and receptiveness will then allow us to turn the
forward simulation into a backward one.

TODO prove determinacy and receptiveness
*)

Module S.
  Import Source.CS.
  Module CS := CS.
End S.

Module I.
  Import Intermediate.CS.
  Module CS := CS.
End I.

Section Correctness.
Variable p: Source.program.
Variable tp: Intermediate.program.

Hypothesis input_program_well_formedness:
  Source.well_formed_program p.

Hypothesis input_program_closedness:
  Source.closed_program p.

Hypothesis successful_compilation:
  compile_program p = Some tp.


(* APT: Some issues to think about.

+ What about refactoring Source semantics to use an expression reduction function wherever possible?
  Can't see what the continuation-based approach is buying except for divergence case.

+ Maybe need a relational spec?  (cf compcert/rtlgen)
+ Will need to figure out how to carry fact about max stack size

Each subexpression of source corresponds to a contiguous sequence of machine code, which
executes from top to bottom or (for exit) immediately halts.

*)


(* APT: Following are some very vague thoughts.

Inductive relate_stacks (mem:Memory.t) : Component.id -> S.stack -> I.stack -> Pointer.t -> Pointer.t -> Prop :=
  | rs_empty : forall sp0, relate_stacks mem nil nil sp0 sp0
  | rs_diff_comp: 
      relate_stacks C0 imem0 regs0 s0 gps spb0 sp0 ->
      ((s0 = [] /\ C <> Main) \/ (exists C0, s0 = (C0,_,_)::_ /\ C <> C0)) ->
      imem at sp0 contains an RA which is in sync with k0 and s (or whatever) ->
      imem at sp0+1 contains arg ->
      imem at spb contains sp0 -> 
      imem at spb+1 contains arg  (* which was in locaxl buf ptr for C0 *) -> 
      imem at (local buf ptr for C0) contains regs0(R_COM) -> maybe the current arg is just a parameter?
      relate_stacks C imem ((C,arg,k)::s) ra??::gps spb (spb+??) ->  

  | rs_same_comp : forall C0 arg0 k0 s gps spb0 sp0 -> 
      relate_stacks mem s0 gps spb0 sp0 ->
      ((s0 = [] /\ C == Main) \/ (s0 = (C,_,_)::_) -> 
      imem at sp0 contains an RA which is in sync with k0 and s ?? -> 
      -or ??? -- imem at sp0 contains regs0(RA) ->  ???
      (* (imem at spb contains a block of appropriate stack_frame_sizep) -> *)
      imem at spb contains sp0 -> 
      imem at spb+1 contains arg  (* which was in local buf ptr for C0 *) -> 
      imem at (local buf ptr for C0) contains regs0(R_COM) -> maybe the current arg is just a parameter?
      XXX where are arg and k ??? 
      relate_stacks imem ((C0,arg,k)::s) gps spb (spb+2)
.


(* Some basic definitions. *)



Section WithMN.

Require Import Lib.Monads.
Import MonadNotations.
Open Scope monad_scope.


Definition code_at (G: Intermediate.GlobalEnv.global_env) (pc: Pointer.t) : option instr := 
  do C_procs <- PMap.find (Pointer.component pc) (Intermediate.GlobalEnv.genv_procedures G);
  do P_code <- PMap.find (Pointer.block pc) C_procs;
  if Pointer.offset pc <? 0 then
    None
  else
    nth_error P_code (Z.to_nat (Pointer.offset pc))
.

(*Lemma code_at_app:
  forall i c2 c1 pc,
  pc = length c1 ->
  code_at (c1 ++ i :: c2) pc = Some i.
Proof.
  induction c1; simpl; intros; subst pc; auto.
Qed.
 *)

End WithMN.

Inductive codeseq_at (G:Intermediate.GlobalEnv.global_env) : Pointer.t -> code -> Prop :=
  | codeseq_at_intro: forall C_procs C1 C2 C3 pc,
      PMap.find (Pointer.component pc) (Intermediate.GlobalEnv.genv_procedures G) = Some C_procs ->
      PMap.find (Pointer.block pc) C_procs = Some (C1 ++ C2 ++ C3) ->
      Z.to_nat (Pointer.offset pc) = length C1 ->
      codeseq_at G pc C2.

(* ?? how do we handle compiling single expressions within the overall monadic structure? *)

(* only next label matters; we will need to parameterize by that somehow *)
Inductive expr_codeseq_at (G: Intermediate.GlobalEnv.global_env) : Pointer.t -> code -> expr -> Prop :=
  | expr_codeseq_at_intro: forall C comp_env pc e,
      run comp_env (compile_expr e) = Some C ->  (* BOGUS *)
      codeseq_at G pc C ->
      expr_codeseq_at G pc C e.


Inductive compile_cont (G: Intermediate.GlobalEnv.global_env) : cont -> Pointer.t -> Prop :=
  | ccont_binop1 : forall b e k C pc pc',
      expr_codeseq_at G pc C e -> 
      pc' = Pointer.add pc (Z.of_nat (length C + 1)) -> 
      compile_cont G k pc' ->                                              
      compile_cont G (Kbinop1 b e k) pc
  | ccont_binop2 : forall b v k pc pc',
      pc' = Pointer.add pc 2%Z -> 
      compile_cont G k pc' ->                                              
      compile_cont G (Kbinop2 b v k) pc
  | ccont_seq : forall e k C pc pc',
      expr_codeseq_at G pc C e -> 
      pc' = Pointer.add pc (Z.of_nat (length C)) -> 
      compile_cont G (Kseq e k) pc.
(*  | ccont_if :
      codeseq_at G pc [IBnz R_COM l1] ->  
      codeseq_at G 
      pc' = Pointer.add pc (Z.of_nat (length Ct + length Cf + 4)) -> 
      compile_cont G (Kif et ef) pc.
  
| Kseq (e: expr) (k: cont)
| Kif (e1: expr) (e2: expr) (k: cont)
| Kalloc (k: cont)
| Kderef (k: cont)
| Kassign1 (e: expr) (k: cont)
| Kassign2 (v: value) (k: cont)
| Kcall (C: Component.id) (P: Procedure.id) (k: cont).
 *)


Inductive match_config (SG: Source.GlobalEnv.global_env) (IG: Intermediate.GlobalEnv.global_env): S.CS.state -> I.CS.state -> Prop :=
  | match_config_intro: forall comp C s mem k e gps regs pc,
      expr_codeseq_at IG pc C e -> 
      compile_cont IG k (Pointer.add pc (Z.of_nat (length C))) -> 
      (* some matching condintion on SG IG *)
      match_config SG IG (comp, s, mem, k, e) (gps, mem, regs, pc).

Ltac inv H := (inversion H; subst; clear H). 

About CompMonad.Comp.bind.

Remark bind_inversion:
  forall (env A B: Type) (f: CompMonad.Comp.t env A) (g: A -> CompMonad.Comp.t env B) (y: B) (e e':env),
  CompMonad.Comp.bind env _ _ f g e = Some (y,e') ->
  exists x, f = Some x /\ g x = Some y.
Proof.
  intros until y. destruct f; simpl; intros.
  exists a; auto.
  discriminate.
Qed.


(*

Ltac monadInv1 H :=
  match type of H with
  | (Some _ = Some _) =>
      inversion H; clear H; try subst
  | (None = Some _) => 
      discriminate
  | (CompMonad.Comp.bind ?F ?G = OK ?X) =>
      let x := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion F G H) as [x [EQ1 EQ2]];
      clear H;
      try (monadInv1 EQ2))))
  | (bind2 ?F ?G = OK ?X) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion F G H) as [x1 [x2 [EQ1 EQ2]]];
      clear H;
      try (monadInv1 EQ2)))))
  | (match ?X with left _ => _ | right _ => assertion_failed end = OK _) =>
      destruct X; [try (monadInv1 H) | discriminate]
  | (match (negb ?X) with true => _ | false => assertion_failed end = OK _) =>
      destruct X as [] eqn:?; [discriminate | try (monadInv1 H)]
  | (match ?X with true => _ | false => assertion_failed end = OK _) =>
      destruct X as [] eqn:?; [try (monadInv1 H) | discriminate]
  | (mmap ?F ?L = OK ?M) =>
      generalize (mmap_inversion F L H); intro
  end.

Ltac monadInv H :=
  monadInv1 H ||
  match type of H with
  | (?F _ _ _ _ _ _ _ _ = OK _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = OK _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = OK _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = OK _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = OK _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = OK _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = OK _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = OK _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.
 *)

Lemma simulation_step:
  forall SG IG sstate1 sstate2 istate1 t,
  S.CS.kstep SG sstate1 t sstate2 ->
  match_config SG IG sstate1 istate1 -> 
  exists istate2,
      star (I.CS.sem tp).(step) IG istate1 t istate2
(*       (plus (transition C) machstate1 machstate2
       \/ (star (transition C) machstate1 machstate2 /\ measure impstate2 < measure impstate1)) *)
   /\ match_config SG IG sstate2 istate2.
Proof.
  intros until t; intros KSTEP MATCH. 
  inversion KSTEP; clear KSTEP; subst; inversion MATCH; clear MATCH; subst; simpl in *.

  - (* binop1 *)
    econstructor; split.
    apply star_refl. 
    econstructor. 
    inv H5. simpl in H. unfold run in H. 
    destruct (        CompMonad.Comp.bind Compiler.comp_env code (list instr) (compile_expr e1)
          (fun c1 : code =>
           CompMonad.Comp.bind Compiler.comp_env code (list instr) (compile_expr e2)
             (fun c2 : code =>
              CompMonad.Comp.ret Compiler.comp_env (list instr)
                (c1 ++
                 IStore R_SP R_COM
                 :: IBinOp Add R_SP R_ONE R_SP
                    :: c2 ++ [IBinOp Minus R_SP R_ONE R_SP; ILoad R_SP R_AUX1; IBinOp op R_AUX1 R_COM R_COM])))
          comp_env) eqn:X; [|inv H]. 
    destruct p0; inv H. 

    destruct (CompMonad.Comp.bind Compiler.comp_env code (list instr) (compile_expr e1)
           (fun c1 : code =>
            CompMonad.Comp.bind Compiler.comp_env code (list instr) (compile_expr e2)
              (fun c2 : code =>
               CompMonad.Comp.ret Compiler.comp_env (list instr)
                 (c1 ++
                  IStore R_SP R_COM
                  :: IBinOp Add R_SP R_ONE R_SP
                     :: c2 ++ [IBinOp Minus R_SP R_ONE R_SP; ILoad R_SP R_AUX1; IBinOp op R_AUX1 R_COM R_COM])))
           comp_env) eqn:?; inv X. 
    destruct (CompMonad.Comp.bind Compiler.comp_env code (list instr) (compile_expr e1)
            (fun c1 : code =>
             CompMonad.Comp.bind Compiler.comp_env code (list instr) (compile_expr e2)
               (fun c2 : code =>
                CompMonad.Comp.ret Compiler.comp_env (list instr)
                  (c1 ++
                   IStore R_SP R_COM
                   :: IBinOp Add R_SP R_ONE R_SP
                   :: c2 ++ [IBinOp Minus R_SP R_ONE R_SP; ILoad R_SP R_AUX1; IBinOp op R_AUX1 R_COM R_COM])))
            comp_env) eqn: X; inv Heqo. 
    destruct (CompMonad.Comp.bind Compiler.comp_env code (list instr) (compile_expr e1)
           (fun c1 : code =>
            CompMonad.Comp.bind Compiler.comp_env code (list instr) (compile_expr e2)
              (fun c2 : code =>
               CompMonad.Comp.ret Compiler.comp_env (list instr)
                 (c1 ++
                  IStore R_SP R_COM
                  :: IBinOp Add R_SP R_ONE R_SP
                     :: c2 ++ [IBinOp Minus R_SP R_ONE R_SP; ILoad R_SP R_AUX1; IBinOp op R_AUX1 R_COM R_COM])))
           comp_env) eqn:?; inv X. 
 CompMonad.Comp.bind Compiler.comp_env code (list instr) (compile_expr e1)
           (fun c1 : code =>
            CompMonad.Comp.bind Compiler.comp_env code (list instr) (compile_expr e2)
              (fun c2 : code =>
               CompMonad.Comp.ret Compiler.comp_env (list instr)
                 (c1 ++
                  IStore R_SP R_COM
                  :: IBinOp Add R_SP R_ONE R_SP
                     :: c2 ++ [IBinOp Minus R_SP R_ONE R_SP; ILoad R_SP R_AUX1; IBinOp op R_AUX1 R_COM R_COM])))
           comp_env



(* As a warm-up, some facts about stack use. *)

Fixpoint stack_usage (e:expr) : nat :=
  match e with
  | E_val _ => 0
  | E_local => 0
  | E_binop _ e1 e2 => max (stack_usage e1) (1 + stack_usage e2)
  | E_seq e1 e2 => max (stack_usage e1) (stack_usage e2)
  | E_if e1 e2 e3 => max (stack_usage e1) (max (stack_usage e2) (stack_usage e3))
  | E_alloc e0 => stack_usage e0
  | E_deref e0 => stack_usage e0
  | E_assign e1 e2 => max (stack_usage e1) (1 + stack_usage e2)
  | E_call C P e0 => max (stack_usage e0) 2   (* subject to change? *)
  | E_exit => 0
  end.
                         
(* In reality, may want to prove this simultaneously with correctness... *)

Import Intermediate.

Lemma stack_usage_correct:
  forall (e:expr) C G pc (m:nat) st mem regs sp sp' pc' st' mem' regs' t,
  run init_env (compile_expr e) = Some C  ->  (* temporary -- nonsense? *)
  codeseq_at G pc C -> 
  stack_usage e = m -> 
  Register.get R_SP regs = Ptr sp ->  
  plus (I.CS.sem tp).(step) G (st,mem,regs,pc) t (st',mem',regs',pc') ->
  Pointer.leq pc pc' = Some true ->
  Pointer.leq pc' (Pointer.add pc (Z.of_nat (length C))) = Some true ->   
  Register.get R_SP regs' = Ptr sp' -> 
  Pointer.leq sp sp' = Some true /\ Pointer.leq sp' (Pointer.add sp (Z.of_nat m)) = Some true.
Proof.
  unfold run.
  induction e; intros.
  - destruct v; simpl in H; inv H. 
    + simpl in H5.
      inv H3. 
      inv H1. 
      * (* one step *)
        rewrite <- I.CS.eval_step_correct in H.  simpl in H. 
        inv H0.  rewrite H1 in H. rewrite H3 in H. 
        assert (Pointer.offset pc <? 0 = false). admit.
        rewrite H0 in H. 
        inv H0. inv H10.
        destruct H0 as [CC [P1 [P2 [P3 P4]]]].
        rewrite P1 in H.  inv H.  rewrite H1 in P2.  inv P2. 
      inv H1. 

  simpl in H. 
*)

Theorem well_formedness_preservation:
  Intermediate.well_formed_program tp.
Proof.
Admitted.

Theorem closedness_preservation:
  Intermediate.closed_program tp.
Proof.
Admitted.

Theorem I_simulates_S:
  forward_simulation (S.CS.sem p) (I.CS.sem tp).
Proof.
Admitted.

Corollary correct_compilation:
  backward_simulation (S.CS.sem p) (I.CS.sem tp).
Proof.
  apply forward_to_backward_simulation.
  - apply I_simulates_S.
  - apply S.CS.receptiveness.
  - apply I.CS.determinacy.
Qed.
End Correctness.