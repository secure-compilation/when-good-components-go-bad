(* MBnz.v — [compiled_branches_forward]: S2I output has forward branches
   only; every [IBnz r l] in a compiled procedure sees [ILabel l] later
   in the same body, via the suffix-checker [bnzfwdb]. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Maps.
Require Import Lib.Extra.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.
Require Import Intermediate.Machine.
Require Import Source.Language.
Require Import S2I.CompMonad.
Require Import S2I.Definitions.
Require Import S2I.Compiler.
Require Import S2I.LabelUniq.
Require T2M.MDefs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* ================================================================== *)
(* 1. The suffix checker and its kit.                                  *)
(* ================================================================== *)

Definition is_labelb (l : label) (i : instr) : bool :=
  if i is ILabel l' then l == l' else false.

Fixpoint bnzfwdb (c : code) : bool :=
  match c with
  | [::] => true
  | IBnz _ l :: rest => has (is_labelb l) rest && bnzfwdb rest
  | _ :: rest => bnzfwdb rest
  end.

Lemma bnzcat (c1 c2 : code) :
  bnzfwdb c1 -> bnzfwdb c2 -> bnzfwdb (c1 ++ c2).
Proof.
elim: c1 => [|i c1 IH] //= H1 H2.
case: i H1 => [|l|v r|r1 r2|op r1 r2 r3|r1 r2|r1 r2|r1 r2|r l| |l|C' P'| |]
  /= H1; try by exact: (IH H1 H2).
case/andP: H1 => Hh Hb.
by rewrite has_cat Hh /= (IH Hb H2).
Qed.

Lemma bnzfwdb_tail (i : instr) (c : code) :
  bnzfwdb (i :: c) -> bnzfwdb c.
Proof.
case: i => [|l|v r|r1 r2|op r1 r2 r3|r1 r2|r1 r2|r1 r2|r l| |l|C' P'| |]
  //=.
by case/andP.
Qed.

Lemma has_label_nth (l : label) (c : code) :
  has (is_labelb l) c ->
  exists k, List.nth_error c k = Some (ILabel l).
Proof.
elim: c => [|j c IH] //= /orP [Hj|Hh].
- case: j Hj => //= l' /eqP El. subst l'. by exists 0.
- have [k Hk] := IH Hh. by exists k.+1.
Qed.

Lemma bnzfwdbP (c : code) (n : nat) (r : register) (l : label) :
  bnzfwdb c ->
  List.nth_error c n = Some (IBnz r l) ->
  exists m, n < m /\ List.nth_error c m = Some (ILabel l).
Proof.
elim: c n => [|i c IH] [|n] //=.
- move=> Hb [Ei]. subst i.
  move: Hb => /= /andP [Hh _].
  have [k Hk] := has_label_nth Hh.
  exists k.+1. by split.
- move=> Hb Hn.
  have [m [Hm Hnth]] := IH n (bnzfwdb_tail Hb) Hn.
  exists m.+1. by split.
Qed.

(* ================================================================== *)
(* 2. The emission walk.                                               *)
(* ================================================================== *)

Lemma compile_expr_bnz (C0 : Component.id)
    (lb sb : Pointer.t) (P_labels : NMap label) (e : expr) :
  forall (s : comp_env) (c : Machine.code) (s' : comp_env),
  compile_expr C0 lb sb P_labels e s = Some (c, s') ->
  bnzfwdb c.
Proof.
elim: e => [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
           |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc.
- by case: v Hc => [i|p|] //= [<- _].
- by move: Hc => /= [<- _].
- by move: Hc => /= [<- _].
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lb sb P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C0 lb sb P_labels e2 s1) => [[c2 s2]|] //=.
  move=> [<- _].
  apply: bnzcat; first exact: (IH1 _ _ _ E1).
  rewrite /=.
  apply: bnzcat; first exact: (IH2 _ _ _ E2).
  by [].
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lb sb P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C0 lb sb P_labels e2 s1) => [[c2 s2]|] //=.
  move=> [<- _].
  apply: bnzcat; first exact: (IH1 _ _ _ E1).
  exact: (IH2 _ _ _ E2).
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lb sb P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C0 lb sb P_labels e2 s1) => [[c2 s2]|] //=.
  case E3: (compile_expr C0 lb sb P_labels e3 s2) => [[c3 s3]|] //=.
  case E4: (fresh_label C0 s3) => [[lconseq s4]|] //=.
  case E5: (fresh_label C0 s4) => [[lend s5]|] //=.
  move=> [<- _].
  apply: bnzcat; first exact: (IH1 _ _ _ E1).
  rewrite /= has_cat /= eqxx /= orbT /=.
  apply: bnzcat; first exact: (IH3 _ _ _ E3).
  rewrite /= has_cat /= eqxx /= !orbT /=.
  apply: bnzcat; first exact: (IH2 _ _ _ E2).
  by [].
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lb sb P_labels e s) => [[c1 s1]|] //=.
  move=> [<- _].
  apply: bnzcat; first exact: (IH _ _ _ E1).
  by [].
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lb sb P_labels e s) => [[c1 s1]|] //=.
  move=> [<- _].
  apply: bnzcat; first exact: (IH _ _ _ E1).
  by [].
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lb sb P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C0 lb sb P_labels e2 s1) => [[c2 s2]|] //=.
  move=> [<- _].
  apply: bnzcat; first exact: (IH2 _ _ _ E2).
  rewrite /=.
  apply: bnzcat; first exact: (IH1 _ _ _ E1).
  by [].
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lb sb P_labels e s) => [[c1 s1]|] //=.
  case: (Component.eqb C' C0).
  + case E2: (find_proc_label P_labels P' s1) => [[tl s2]|] //=.
    move=> [<- _].
    apply: bnzcat; first exact: (IH _ _ _ E1).
    by [].
  + move=> [<- _].
    apply: bnzcat; first exact: (IH _ _ _ E1).
    by [].
- by move: Hc => /= [<- _].
Qed.

Lemma compile_proc_bnz (C0 : Component.id)
    (lb sb : Pointer.t) (P_labels : NMap label) (P0 : Procedure.id)
    (e : expr) :
  forall (s : comp_env) (c : Machine.code) (s' : comp_env),
  compile_proc C0 lb sb P_labels P0 e s = Some (c, s') ->
  bnzfwdb c.
Proof.
move=> s c s' Hc.
move: Hc; rewrite /compile_proc.
cbv beta iota delta [Monads.bind Monads.ret compilation_monad
  CompMonad.Comp.bind CompMonad.Comp.ret].
case E0: (find_proc_label P_labels P0 s) => [[pl s0]|] //=.
case E1: (fresh_label C0 s0) => [[lmain s1]|] //=.
case E2: (fresh_label C0 s1) => [[lreturn s2]|] //=.
case E3: (compile_expr C0 lb sb P_labels e s2) => [[pc s3]|] //=.
have Hpc := compile_expr_bnz E3.
case: (Component.eqb C0 Component.main && Procedure.eqb P0 Procedure.main).
-
  case: (immediately_final e) => -[<- _] /=;
    rewrite !eqxx /=;
    by apply: bnzcat; [exact: Hpc | ].
-
  move=> -[<- _] /=.
  by apply: bnzcat; [exact: Hpc | ].
Qed.

(* ================================================================== *)
(* 3. The program level.                                               *)
(* ================================================================== *)

Theorem compiled_branches_forward
    (sa : Source.program) (tp : Intermediate.program) :
  compile_program sa = Some tp ->
  MDefs.branches_forward tp.
Proof.
move=> Hc cid Cprocs Pid Pcode n r l Hproc HPd Hnth.
case: (compiled_proc_origin Hc Hproc HPd)
  => [[plm [e [s0 [s1 Hcp]]]]|[lab Ecd]].
- exact: (bnzfwdbP (compile_proc_bnz Hcp) Hnth).
-
  subst Pcode.
  case: n Hnth => [|n] //=.
  case: n => [|n] //=.
  case: n => [|n] //=.
  by case: n.
Qed.
