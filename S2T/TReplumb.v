(** * Stage 4, part 10 — the replumb lemmas, generic in the code predicate.

    See plan-i2t-redo.md §4 (Stage 4).

    Ports of `S2I/Simulation.v:541-700` (`binop1_replumb`, `seq1_replumb`,
    `if1_replumb`, `alloc1_replumb`, `deref1_replumb`, `assign1_replumb`,
    `initcall_replumb`). A replumb is the zero-step half of a descend: the
    compiler emitted `c1 ++ <glue> ++ rest` for a compound expression, and the
    simulation needs to read that as "`c1` for the subexpression, with the glue
    absorbed into the continuation".

    **These needed no T-specific content at all.** Look at what the I proofs do
    with their `code_at` hypothesis: nothing but
    `by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0` — the two code lists are
    equal modulo associativity, and the predicate is never inspected. So the
    lemmas are stated here over an ABSTRACT `P : icode -> Prop` and instantiated
    at `TMacros.code_at_I cde C pc`. The same statements would serve
    `S2I/Simulation.v`'s seven, at `code_at G pc` — they are not re-proved here,
    they are proved once.

    That is the first place in Stage 4 where the retarget cost is *zero* rather
    than small, and it is worth naming why: these lemmas are about the
    COMPILER's output shape, and Pass 1 changes the machine, not the compiler. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Language.
Require Import Source.CS.
Require Import Intermediate.Machine.
Require Import S2I.CompMonad.
Require Import S2I.Compiler.
Require Import S2I.SimInject.
Require Import S2I.Simulation.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Require Import Coq.ZArith.ZArith.

Set Implicit Arguments.
Unset Strict Implicit.

Module TReplumb.

Notation icode := Intermediate.Machine.code.

Section WithCodePred.

(* the only thing the seven proofs need of a code predicate: nothing *)
Variable P : icode -> Prop.

Variable a : renaming.
Variable C : Component.id.
Variable plm : NMap label.

Lemma binop1_replumb op e1 e2 k c rest temps s1 s2 :
  compile_expr C (lbp C) (scr C) plm (E_binop op e1 e2) s1 = Some (c, s2) ->
  P (c ++ rest) ->
  cont_matchJ a C plm k rest temps ->
  exists c1 rest' sA sB,
    [/\ compile_expr C (lbp C) (scr C) plm e1 sA = Some (c1, sB),
        P (c1 ++ rest')
      & cont_matchJ a C plm (Kbinop1 op e2 k) rest' temps].
Proof.
  rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C (lbp C) (scr C) plm e1 s1) => [[c1 sA]|]; last by [].
  rewrite /=.
  case E2: (compile_expr C (lbp C) (scr C) plm e2 sA) => [[c2 sB]|]; last by [].
  rewrite /=. move=> [Ec _] Hcode Hk. subst c.
  exists c1,
    (push R_COM ++ c2 ++ pop R_AUX1 ++ IBinOp op R_AUX1 R_COM R_COM :: rest),
    s1, sA.
  split=> //.
  - move: Hcode. rewrite /push /pop.
    by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
  - apply: CMJ_base. exact: CM_binop1 E2 Hk.
Qed.

Lemma seq1_replumb e1 e2 k c rest temps s1 s2 :
  compile_expr C (lbp C) (scr C) plm (E_seq e1 e2) s1 = Some (c, s2) ->
  P (c ++ rest) ->
  cont_matchJ a C plm k rest temps ->
  exists c1 rest' sA sB,
    [/\ compile_expr C (lbp C) (scr C) plm e1 sA = Some (c1, sB),
        P (c1 ++ rest')
      & cont_matchJ a C plm (Kseq e2 k) rest' temps].
Proof.
  rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C (lbp C) (scr C) plm e1 s1) => [[c1 sA]|]; last by [].
  rewrite /=.
  case E2: (compile_expr C (lbp C) (scr C) plm e2 sA) => [[c2 sB]|]; last by [].
  rewrite /=. move=> [Ec _] Hcode Hk. subst c.
  exists c1, (c2 ++ rest), s1, sA.
  split=> //.
  - move: Hcode. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
  - apply: CMJ_base. exact: CM_seq E2 Hk.
Qed.

Lemma if1_replumb e1 e2 e3 k c rest temps s1 s2 :
  compile_expr C (lbp C) (scr C) plm (E_if e1 e2 e3) s1 = Some (c, s2) ->
  P (c ++ rest) ->
  cont_matchJ a C plm k rest temps ->
  exists c1 rest' sA sB,
    [/\ compile_expr C (lbp C) (scr C) plm e1 sA = Some (c1, sB),
        P (c1 ++ rest')
      & cont_matchJ a C plm (Kif e2 e3 k) rest' temps].
Proof.
  rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C (lbp C) (scr C) plm e1 s1) => [[c1 sA]|]; last by [].
  rewrite /=.
  case E2: (compile_expr C (lbp C) (scr C) plm e2 sA) => [[c2 sB]|]; last by [].
  rewrite /=.
  case E3: (compile_expr C (lbp C) (scr C) plm e3 sB) => [[c3 sC]|]; last by [].
  rewrite /= !fresh_labelE /=. move=> [Ec _] Hcode Hk. subst c.
  exists c1, (IBnz R_COM (odflt 0 (next_label sC C))
      :: c3 ++ [:: IBnz R_ONE (odflt 0 (setm (next_label sC) C
                                          (1 + odflt 0 (next_label sC C)) C));
                   ILabel (odflt 0 (next_label sC C))]
      ++ c2 ++ ILabel (odflt 0 (setm (next_label sC) C
                                  (1 + odflt 0 (next_label sC C)) C)) :: rest),
    s1, sA.
  split=> //.
  - move: Hcode. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
  - apply: CMJ_base. exact: CM_if E2 E3 Hk.
Qed.

Lemma alloc1_replumb e k c rest temps s1 s2 :
  compile_expr C (lbp C) (scr C) plm (E_alloc e) s1 = Some (c, s2) ->
  P (c ++ rest) ->
  cont_matchJ a C plm k rest temps ->
  exists c0 rest' sA sB,
    [/\ compile_expr C (lbp C) (scr C) plm e sA = Some (c0, sB),
        P (c0 ++ rest')
      & cont_matchJ a C plm (Kalloc k) rest' temps].
Proof.
  rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C (lbp C) (scr C) plm e s1) => [[c0 sA]|]; last by [].
  rewrite /=. move=> [Ec _] Hcode Hk. subst c.
  exists c0, (IAlloc R_COM R_COM :: rest), s1, sA.
  split=> //.
  - move: Hcode. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
  - apply: CMJ_base. exact: CM_alloc Hk.
Qed.

Lemma deref1_replumb e k c rest temps s1 s2 :
  compile_expr C (lbp C) (scr C) plm (E_deref e) s1 = Some (c, s2) ->
  P (c ++ rest) ->
  cont_matchJ a C plm k rest temps ->
  exists c0 rest' sA sB,
    [/\ compile_expr C (lbp C) (scr C) plm e sA = Some (c0, sB),
        P (c0 ++ rest')
      & cont_matchJ a C plm (Kderef k) rest' temps].
Proof.
  rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C (lbp C) (scr C) plm e s1) => [[c0 sA]|]; last by [].
  rewrite /=. move=> [Ec _] Hcode Hk. subst c.
  exists c0, (ILoad R_COM R_COM :: rest), s1, sA.
  split=> //.
  - move: Hcode. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
  - apply: CMJ_base. exact: CM_deref Hk.
Qed.

Lemma assign1_replumb e1 e2 k c rest temps s1 s2 :
  compile_expr C (lbp C) (scr C) plm (E_assign e1 e2) s1 = Some (c, s2) ->
  P (c ++ rest) ->
  cont_matchJ a C plm k rest temps ->
  exists c2 rest' sA sB,
    [/\ compile_expr C (lbp C) (scr C) plm e2 sA = Some (c2, sB),
        P (c2 ++ rest')
      & cont_matchJ a C plm (Kassign1 e1 k) rest' temps].
Proof.
  rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C (lbp C) (scr C) plm e1 s1) => [[c1 sA]|]; last by [].
  rewrite /=.
  case E2: (compile_expr C (lbp C) (scr C) plm e2 sA) => [[c2 sB]|]; last by [].
  rewrite /=. move=> [Ec _] Hcode Hk. subst c.
  exists c2, (push R_COM ++ c1 ++ pop R_AUX1
      ++ [:: IStore R_COM R_AUX1; IMov R_AUX1 R_COM] ++ rest), sA, sB.
  split=> //.
  - move: Hcode. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
  - apply: CMJ_base. exact: CM_assign1 E1 Hk.
Qed.

Lemma initcall_replumb C' P' e k c rest temps s1 s2 :
  compile_expr C (lbp C) (scr C) plm (E_call C' P' e) s1 = Some (c, s2) ->
  P (c ++ rest) ->
  cont_matchJ a C plm k rest temps ->
  exists ce rest' sA sB,
    [/\ compile_expr C (lbp C) (scr C) plm e sA = Some (ce, sB),
        P (ce ++ rest')
      & cont_matchJ a C plm (Kcall C' P' k) rest' temps].
Proof.
  rewrite /= /Comp.bind /Comp.ret /find_proc_label /Comp.lift.
  case E1: (compile_expr C (lbp C) (scr C) plm e s1) => [[ce sA]|]; last by [].
  rewrite /=.
  case Heqb: (Component.eqb C' C).
  - (* internal call *)
    case EL: (getm plm P') => [tl|]; last by [].
    rewrite /=. move=> [Ec _] Hcode Hk. subst c.
    have EC : C' = C by apply/PeanoNat.Nat.eqb_eq.
    exists ce, (push R_RA ++ IJal tl :: pop R_RA ++ rest), s1, sA.
    split=> //.
    + move: Hcode. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
    + apply: CMJ_base. exact: CM_call_int EC EL Hk.
  - (* external call *)
    move=> [Ec _] Hcode Hk. subst c.
    have HneC : C' <> C.
    { move=> E. by rewrite E /Component.eqb PeanoNat.Nat.eqb_refl in Heqb. }
    exists ce, (push R_RA ++ push R_ARG ++ store_arg (scr C) R_SP R_AUX2
        ++ ICall C' P' :: IConst (IInt 1) R_ONE
        :: reload_sp (scr C) ++ pop R_ARG ++ pop R_RA ++ rest), s1, sA.
    split=> //.
    + move: Hcode. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
    + apply: CMJ_base. exact: CM_call_ext HneC Hk.
Qed.

End WithCodePred.

End TReplumb.
