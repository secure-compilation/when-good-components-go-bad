(** * Stage 3 — the static facts about the LINEARIZED compiled program.

    See plan-i2t-redo.md §3.

    Everything Stage 4 and Stage 5 took as a premise — `entry_int`,
    `entry_ext`, the `labelsP`-domain fact, and `start_ok`'s code half — is a
    statement about `intermediate_to_transitional tp`, and all of them rest on
    ONE decomposition: a component's array is the concatenation, over its
    procedures, of a HEADER cell followed by that procedure's mapped
    instructions. Locate the header and everything else follows.

    The standing rule of the redo applies here with full force: no
    `Hypothesis`, no `Variable` standing in for a fact. Every lemma below is
    about the linearizer's actual output. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Intermediate.Machine.
Require Import S2I.CompMonad.
Require Import S2I.Compiler.
Require Import S2I.SimInject.
Require Import S2I.SimCode.
Require Import S2I.Simulation.
Require Import S2I.LabelUniq.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TMem.
Require Import S2T.TInv.
Require Import S2T.TInject.
Require Import S2T.TLabel.
Require Import S2T.TMacros.
Require Import S2T.TDrain.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From extructures Require Import ord fmap fset.

Require Import Coq.ZArith.ZArith.
Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.

Module TStatic.

Notation icode := Intermediate.Machine.code.

Lemma seq_split (T : eqType) (s : seq T) (x : T) :
  x \in s -> exists s1 s2, s = s1 ++ x :: s2.
Proof.
  elim: s => [|y s IH] //. rewrite inE => /orP [/eqP ->|Hin].
  - by exists [::], s.
  - case: (IH Hin) => [s1 [s2 E]]. by exists (y :: s1), s2; rewrite E.
Qed.

(** The component array of a component that HAS procedures. *)
Lemma cde_getm pr c Cprocs :
  getm (Intermediate.prog_procedures pr) c = Some Cprocs ->
  getm (Transitional.intermediate_to_transitional pr) c
  = Some (Transitional.linearize_component pr c).
Proof.
  move=> Hg. rewrite /Transitional.intermediate_to_transitional /Transitional.intermediate_to_transitional_gen mkfmapE.
  have Hin : List.In (c, Cprocs)
               (elementsm (Intermediate.prog_procedures pr))
    by exact: getm_In_elementsm Hg.
  move: Hin. elim: (elementsm (Intermediate.prog_procedures pr))
    => [|[c0 x0] l IH] //=.
  case: ifP => [/eqP Ec _|Hne].
  - by rewrite Ec.
  - move=> [E|Hin]; last exact: IH Hin.
    by case: E => Ec _; move: Hne; rewrite ?Ec -?Ec eqxx.
Qed.

(* ================================================================== *)
(* Where a procedure HEADER is, and that the machine finds it there    *)
(* ================================================================== *)

(** The cells a cross-component call can land on. Only [inr] — an ordinary
    [ILabel] is [inl], which is what keeps `Bnz` and `ICall` from confusing
    each other's targets. *)
Definition is_phdr (c : Component.id) (p : Procedure.id)
                   (x : Transitional.instr * mem_tag) : bool :=
  if x.1 is Transitional.TrLabel (inr (c', p')) then
    Nat.eqb c c' && Nat.eqb p p' else false.

(** The same accumulator trick as `TLabel`: [find_plabel]'s counter is a local
    [let fix], so it cannot be named in a lemma; give it a top-level twin and
    bridge the two by generalising the accumulator. *)
Fixpoint pfaux (cd : seq (Transitional.instr * mem_tag))
               (c : Component.id) (p : Procedure.id) (o : Z) : option Z :=
  match cd with
  | [::] => None
  | (Transitional.TrLabel (inr (c', p')), _) :: cd' =>
      if Nat.eqb c c' && Nat.eqb p p' then Some o else pfaux cd' c p (1 + o)%Z
  | _ :: cd' => pfaux cd' c p (1 + o)%Z
  end.

Lemma find_plabel_pfaux cd c p :
  Transitional.find_plabel cd c p = pfaux cd c p 0%Z.
Proof.
  rewrite /Transitional.find_plabel.
  elim: cd (0%Z) => [|[i tg] cd IH] o //=.
  by case: i => [|[l'|[c' p']]|v r|r1 r2|op r1 r2 r3|r1 r2|r1 r2|r1 r2
                |r l0|r|l0|lp|] /=; rewrite -?IH; case: cd {IH}.
Qed.

Lemma pfaux_cat_notin pre c p tg post o :
  count (is_phdr c p) pre = 0 ->
  pfaux (pre ++ (Transitional.TrLabel (inr (c, p)), tg) :: post) c p o
  = Some (Z.of_nat (size pre) + o)%Z.
Proof.
  elim: pre o => [|[i tg'] pre IH] o Hc.
  - by rewrite /= !Nat.eqb_refl ?Z.add_0_l.
  - have Ho : (Z.of_nat (size ((i, tg') :: pre)) + o)%Z
            = (Z.of_nat (size pre) + (1 + o))%Z
      by rewrite [size (_ :: _)]/= Nat2Z.inj_succ; lia.
    have [Hh Ht] : is_phdr c p (i, tg') = false
                   /\ count (is_phdr c p) pre = 0.
    { move: Hc => /eqP. rewrite /= addn_eq0 => /andP [H1 /eqP H2].
      split; last exact: H2. by move: H1; case: (is_phdr c p (i, tg')). }
    rewrite Ho cat_cons -(IH (1 + o)%Z Ht).
    move: {Hc Ho} Hh; rewrite /is_phdr /=.
    by case: i => [|[l'|[c' p']]|v r|r1 r2|op r1 r2 r3|r1 r2|r1 r2|r1 r2
                  |r l0|r|l0|lp|] //= ->.
Qed.

Lemma find_plabel_at pre c p tg post :
  count (is_phdr c p) pre = 0 ->
  Transitional.find_plabel
    (pre ++ (Transitional.TrLabel (inr (c, p)), tg) :: post) c p
  = Some (Z.of_nat (size pre)).
Proof.
  move=> H. by rewrite find_plabel_pfaux pfaux_cat_notin // Z.add_0_r.
Qed.

(** A procedure's MAPPED instructions contain no header: [instr_to_transitional]
    sends [ILabel] to [inl], and nothing to [inr]. *)
Lemma no_phdr_map c p cd :
  count (is_phdr c p) [seq Transitional.instr_to_transitional c i | i <- cd]
  = 0.
Proof.
  elim: cd => [|i cd IH] //=. rewrite IH addn0 /is_phdr.
  by case: i => * //=; case: (Nat.eqb c _).
Qed.

(** …so a procedure's whole block contributes a header only for ITSELF. *)
Lemma no_phdr_proc pr c p q :
  q <> p ->
  count (is_phdr c p) (Transitional.linearize_proc pr c q) = 0.
Proof.
  move=> Hne. rewrite /Transitional.linearize_proc /Transitional.linearize_proc_gen /= no_phdr_map addn0.
  rewrite /is_phdr /= Nat.eqb_refl /=.
  have -> : Nat.eqb p q = false
    by apply/PeanoNat.Nat.eqb_neq => E; apply: Hne; rewrite E.
  by [].
Qed.

Lemma no_phdr_flatten pr c p l :
  p \notin l ->
  count (is_phdr c p)
        (flatten [seq Transitional.linearize_proc pr c q | q <- l]) = 0.
Proof.
  elim: l => [|q l IH] //=. rewrite inE negb_or => /andP [Hq Hl].
  rewrite count_cat IH // addn0. apply: no_phdr_proc.
  by move=> E; move: Hq; rewrite E eqxx.
Qed.

(* ================================================================== *)
(* The payoff: where a cross-component call lands                      *)
(* ================================================================== *)

(** ★ For a compiled program, `find_plabel_in_code` resolves a procedure to the
    HEADER cell of its block, and the procedure's own code sits immediately
    after it. Both halves of Stage 4's `entry_ext` premise come from here: the
    resolution itself, and the `code_at_I` at `Pointer.inc pcW`.

    The uniqueness the resolution needs is not assumed — it is `domm`'s, and
    the only header in the prefix belongs to some OTHER procedure. *)
Lemma find_plabel_in_code_at pr c Cprocs P cd :
  getm (Intermediate.prog_procedures pr) c = Some Cprocs ->
  getm Cprocs P = Some cd ->
  exists pre post,
    [/\ Transitional.linearize_component pr c
        = pre ++ (Transitional.TrLabel (inr (c, P)),
                  Transitional.head_tag pr c P)
                :: [seq Transitional.instr_to_transitional c i | i <- cd]
                ++ post,
        count (is_phdr c P) pre = 0
      & Transitional.find_plabel_in_code
          (Transitional.intermediate_to_transitional pr) c P
        = Some (c, 0, Z.of_nat (size pre))].
Proof.
  move=> Hg HgP.
  have HP : P \in domm Cprocs by rewrite mem_domm HgP.
  have Hu : uniq (domm Cprocs) by exact: uniq_fset.
  case: (seq_split HP) => [l1 [l2 Esp]].
  have HnotP : P \notin l1.
  { move: Hu; rewrite Esp cat_uniq => /and3P [_ Hh _].
    by move: Hh => /hasPn /(_ P (mem_head P l2)). }
  exists (flatten [seq Transitional.linearize_proc pr c q | q <- l1]),
         (flatten [seq Transitional.linearize_proc pr c q | q <- l2]).
  have Elin : Transitional.linearize_component pr c
            = flatten [seq Transitional.linearize_proc pr c q | q <- l1]
              ++ (Transitional.TrLabel (inr (c, P)),
                  Transitional.head_tag pr c P)
                 :: [seq Transitional.instr_to_transitional c i | i <- cd]
                 ++ flatten [seq Transitional.linearize_proc pr c q | q <- l2].
  { rewrite /Transitional.linearize_component /Transitional.linearize_component_gen Hg /= Esp.
    rewrite map_cat flatten_cat map_cons /=. congr (_ ++ _).
    by rewrite /Transitional.linearize_proc /Transitional.linearize_proc_gen Hg HgP. }
  have Hcount := no_phdr_flatten pr c HnotP.
  split=> //.
  rewrite /Transitional.find_plabel_in_code (cde_getm Hg) Elin.
  by rewrite find_plabel_at.
Qed.

(* ================================================================== *)
(* From the decomposition to [code_at_I]                               *)
(* ================================================================== *)

(** ★ Any CONTIGUOUS slice of a compiled procedure's code is a [code_at_I] at
    a COMPUTABLE pc — `size pre + 1 + size A`, i.e. the header's offset, one
    past it, then whatever precedes the slice. This is the bridge Stage 4's two
    entry premises are instantiated through: give it the split of
    `compile_proc`'s output and it hands back the program point.

    Stated non-existentially on purpose: `entry_ext` needs the wrapper's code
    at `Pointer.inc pcW` SPECIFICALLY — the cell an `ICall` reaches after the
    administrative header step — and that is the `A = [::]` instance. *)
Lemma code_at_I_in_proc pr c Cprocs P cd A B D pre post :
  getm (Intermediate.prog_procedures pr) c = Some Cprocs ->
  getm Cprocs P = Some cd ->
  Transitional.linearize_component pr c
  = pre ++ (Transitional.TrLabel (inr (c, P)),
            Transitional.head_tag pr c P)
          :: [seq Transitional.instr_to_transitional c i | i <- cd] ++ post ->
  cd = A ++ B ++ D ->
  TMacros.code_at_I (Transitional.intermediate_to_transitional pr) c
    (c, 0, Z.of_nat (size pre + 1 + size A)) B.
Proof.
  move=> Hg HgP Elin Ecd.
  rewrite /TMacros.code_at_I /TMacros.code_at /=.
  exists (Transitional.linearize_component pr c),
         (pre ++ (Transitional.TrLabel (inr (c, P)),
                  Transitional.head_tag pr c P)
                 :: [seq Transitional.instr_to_transitional c i | i <- A]),
         ([seq Transitional.instr_to_transitional c i | i <- D] ++ post).
  split.
  - exact: (cde_getm Hg).
  - by rewrite Elin Ecd !map_cat -!catA.
  - rewrite size_cat /= size_map. congr (Z.of_nat _). by lia.
Qed.

(** The [A = [::]] instance, with the pc in the form the [ICall] rule leaves
    it: one past the header that [find_plabel_in_code] resolved to. *)
Lemma code_at_I_after_header pr c Cprocs P cd B D pre post :
  getm (Intermediate.prog_procedures pr) c = Some Cprocs ->
  getm Cprocs P = Some cd ->
  Transitional.linearize_component pr c
  = pre ++ (Transitional.TrLabel (inr (c, P)),
            Transitional.head_tag pr c P)
          :: [seq Transitional.instr_to_transitional c i | i <- cd] ++ post ->
  cd = B ++ D ->
  TMacros.code_at_I (Transitional.intermediate_to_transitional pr) c
    (Pointer.inc (c, 0, Z.of_nat (size pre))) B.
Proof.
  move=> Hg HgP Elin Ecd.
  have -> : Pointer.inc ((c, 0, Z.of_nat (size pre)) : Pointer.t)
          = (c, 0, Z.of_nat (size pre + 1 + size ([::] : icode)))
    by rewrite /Pointer.inc /=; congr (_, _, _); rewrite addn0 Nat2Z.inj_add.
  by apply: (code_at_I_in_proc (A := [::]) (D := D) Hg HgP Elin);
     rewrite Ecd.
Qed.

(* ================================================================== *)
(* [compile_proc]'s output, main's flavour                             *)
(* ================================================================== *)

(** The companion of `S2I/Simulation.v:1546`'s `compile_proc_shape_std`, for the
    one procedure the MACHINE enters rather than a caller. Main's wrapper is
    longer by the FLAG protocol — load the flag, push its old value as the
    context marker, branch on it, install `Int 0` as the argument on the initial
    run, then set the flag — and it ends at an `IHalt`/`IReturn` pair rather
    than a bare `IReturn`. That is precisely the code `ef_main_entry_run` and
    `ef_halt_run` consume, at the two ends.

    `immediately_final e = false` is a premise because it is what makes the
    `halt_pad` empty, so the first cell after the procedure header really is
    the `IConst 1 R_ONE` the entry run expects. It is the same condition the
    I-level development carries as `vi_mainnf`. *)
Lemma compile_proc_shape_main C0 plm P e s cd s' pl :
  compile_proc C0 (lbp C0) (scr C0) plm P e s = Some (cd, s') ->
  getm plm P = Some pl ->
  Component.eqb C0 Component.main && Procedure.eqb P Procedure.main = true ->
  immediately_final e = false ->
  exists bodyc sA sB lmain lreturn,
    compile_expr C0 (lbp C0) (scr C0) plm e sA = Some (bodyc, sB) /\
    cd = ([:: IConst (IInt 1) R_ONE] ++
          [:: IMov R_SP R_AUX1;
              IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
              IAlloc R_SP R_SP] ++
          push R_AUX1 ++ load_arg (scr C0) R_AUX1 ++ push R_AUX1 ++
          push R_RA ++
          [:: IConst (IPtr (flag_buf_ptr (scr C0))) R_AUX1;
              ILoad R_AUX1 R_AUX2] ++
          push R_AUX2 ++
          [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
              IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2; IJal pl] ++
          pop R_ARG ++ pop R_RA ++ pop R_AUX1 ++
          store_arg (scr C0) R_AUX1 R_AUX2 ++ pop R_SP ++
          [:: IBnz R_ARG lreturn; IHalt; ILabel lreturn; IReturn])
         ++ ILabel pl ::
         ([:: IMov R_SP R_AUX1;
              IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
              IAlloc R_SP R_SP] ++
          push R_AUX1 ++
          push R_ARG ++ [:: IMov R_COM R_ARG] ++ bodyc ++
          (pop R_ARG ++ pop R_SP ++ [:: IJump])).
Proof.
  rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift /Comp.ret /=.
  case EL: (getm plm P) => [pl0|]; last by [].
  rewrite /= !fresh_labelE /=.
  case EE: (compile_expr C0 (lbp C0) (scr C0) plm e _) => [[pcode s4]|];
    last by [].
  rewrite /=. move=> [Ecd _] [Epl]. subst pl0.
  move=> Hmain Hnf.
  exists pcode. do 4!eexists. split; first exact: EE.
  by rewrite -Ecd Hmain Hnf.
Qed.

(** ★ The PAD-TOLERANT version, and the one `entry_int` needs at `(main, main)`.

    `compile_proc` emits `halt_pad ++ ext_entry ++ ILabel pl :: body`
    (`S2I/Compiler.v:422`), with `halt_pad = [:: IHalt]` exactly when main's
    body is immediately final. `compile_proc_shape_main` assumes the pad away
    because `start_ok`'s ordinary case needs the wrapper to sit right after the
    header; but the BODY is emitted either way, and an intra-component call to
    `(main, main)` resolves through `ILabel pl` and so does not care where the
    wrapper begins. Keeping the pad symbolic is the whole difference. *)
Lemma compile_proc_shape_main_gen C0 plm P e s cd s' pl :
  compile_proc C0 (lbp C0) (scr C0) plm P e s = Some (cd, s') ->
  getm plm P = Some pl ->
  Component.eqb C0 Component.main && Procedure.eqb P Procedure.main = true ->
  exists pad bodyc sA sB lmain lreturn,
    [/\ pad = (if immediately_final e then [:: IHalt] else [::]),
        compile_expr C0 (lbp C0) (scr C0) plm e sA = Some (bodyc, sB)
      & cd = pad
             ++ ([:: IConst (IInt 1) R_ONE] ++
                 [:: IMov R_SP R_AUX1;
                     IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                     IAlloc R_SP R_SP] ++
                 push R_AUX1 ++ load_arg (scr C0) R_AUX1 ++ push R_AUX1 ++
                 push R_RA ++
                 [:: IConst (IPtr (flag_buf_ptr (scr C0))) R_AUX1;
                     ILoad R_AUX1 R_AUX2] ++
                 push R_AUX2 ++
                 [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
                     IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2; IJal pl] ++
                 pop R_ARG ++ pop R_RA ++ pop R_AUX1 ++
                 store_arg (scr C0) R_AUX1 R_AUX2 ++ pop R_SP ++
                 [:: IBnz R_ARG lreturn; IHalt; ILabel lreturn; IReturn])
             ++ ILabel pl ::
                ([:: IMov R_SP R_AUX1;
                     IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                     IAlloc R_SP R_SP] ++
                 push R_AUX1 ++
                 push R_ARG ++ [:: IMov R_COM R_ARG] ++ bodyc ++
                 (pop R_ARG ++ pop R_SP ++ [:: IJump]))].
Proof.
  rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift /Comp.ret /=.
  case EL: (getm plm P) => [pl0|]; last by [].
  rewrite /= !fresh_labelE /=.
  case EE: (compile_expr C0 (lbp C0) (scr C0) plm e _) => [[pcode s4]|];
    last by [].
  rewrite /=. move=> [Ecd _] [Epl]. subst pl0. move=> Hmain.
  exists (if immediately_final e then [:: IHalt] else [::]), pcode.
  do 4!eexists. split; [by [] | exact: EE | by rewrite -Ecd Hmain].
Qed.

(* ================================================================== *)
(* Discharging Stage 4's entry premises                                *)
(* ================================================================== *)

(** ★ `entry_ext`, for one callee. Everything composes: `compile_proc_shape_std`
    (`S2I/Simulation.v:1546`) splits the compiled procedure into its WRAPPER and
    its BODY at the `ILabel pl`; `find_plabel_in_code_at` locates the header;
    `code_at_I_after_header` puts the wrapper one cell past it — where an
    `ICall` lands after the administrative header step — and
    `code_at_I_in_proc` puts the body after the wrapper. *)
Lemma entry_ext_of_compiled pr c Cprocs P cd plm pl e s s' :
  getm (Intermediate.prog_procedures pr) c = Some Cprocs ->
  getm Cprocs P = Some cd ->
  compile_proc c (lbp c) (scr c) plm P e s = Some (cd, s') ->
  getm plm P = Some pl ->
  Component.eqb c Component.main && Procedure.eqb P Procedure.main = false ->
  exists pcW pcE cbody sA sB,
    [/\ Transitional.find_plabel_in_code
          (Transitional.intermediate_to_transitional pr) c P = Some pcW,
        TMacros.code_at_I (Transitional.intermediate_to_transitional pr) c
          (Pointer.inc pcW)
          (IConst (IInt 1) R_ONE
           :: [:: IMov R_SP R_AUX1;
                  IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                  IAlloc R_SP R_SP]
              ++ push R_AUX1 ++ load_arg (scr c) R_AUX1 ++ push R_AUX1
              ++ push R_RA
              ++ IJal pl
                 :: pop R_RA ++ pop R_AUX1
                    ++ store_arg (scr c) R_AUX1 R_AUX2
                    ++ pop R_SP ++ [:: IReturn]),
        Pointer.component pcE = c,
        compile_expr c (lbp c) (scr c) plm e sA = Some (cbody, sB)
      & TMacros.code_at_I (Transitional.intermediate_to_transitional pr) c pcE
          ([:: ILabel pl; IMov R_SP R_AUX1;
               IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
               IAlloc R_SP R_SP]
           ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
           ++ cbody ++ pop R_ARG ++ pop R_SP ++ [:: IJump])].
Proof.
  move=> Hg HgP Hcp Hpl Hmain.
  case: (@compile_proc_shape_std c plm P e s cd s' pl Hcp Hpl Hmain)
    => [bodyc [sA [sB [Hce Ecd]]]].
  case: (find_plabel_in_code_at Hg HgP) => [pre [post [Elin _ Hfind]]].
  set W := ([:: IConst (IInt 1) R_ONE; IMov R_SP R_AUX1;
                IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                IAlloc R_SP R_SP] ++
            push R_AUX1 ++ load_arg (scr c) R_AUX1 ++ push R_AUX1
            ++ push R_RA ++ [:: IJal pl] ++
            pop R_RA ++ pop R_AUX1 ++ store_arg (scr c) R_AUX1 R_AUX2
              ++ pop R_SP ++ [:: IReturn]).
  set B := (ILabel pl ::
            ([:: IMov R_SP R_AUX1;
                 IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                 IAlloc R_SP R_SP] ++
             push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG] ++ bodyc ++
             (pop R_ARG ++ pop R_SP ++ [:: IJump]))).
  have EcdWB : cd = W ++ B ++ [::] by rewrite cats0.
  exists (c, 0, Z.of_nat (size pre)),
         (c, 0, Z.of_nat (size pre + 1 + size W)), bodyc, sA, sB.
  split.
  - exact: Hfind.
  - apply: (code_at_I_after_header (B := W) (D := B) Hg HgP Elin).
    by rewrite Ecd.
  - by [].
  - exact: Hce.
  - exact: (code_at_I_in_proc (A := W) (B := B) (D := [::]) Hg HgP Elin EcdWB).
Qed.

(** ★ `entry_int`, the same composition minus the wrapper: an intra-component
    call resolves through the ORDINARY label `pl`, so only the body slice is
    needed. *)
Lemma entry_int_of_compiled pr c Cprocs P cd plm pl e s s' :
  getm (Intermediate.prog_procedures pr) c = Some Cprocs ->
  getm Cprocs P = Some cd ->
  compile_proc c (lbp c) (scr c) plm P e s = Some (cd, s') ->
  getm plm P = Some pl ->
  Component.eqb c Component.main && Procedure.eqb P Procedure.main = false ->
  exists pcE cbody sA sB,
    [/\ Pointer.component pcE = c,
        compile_expr c (lbp c) (scr c) plm e sA = Some (cbody, sB)
      & TMacros.code_at_I (Transitional.intermediate_to_transitional pr) c pcE
          ([:: ILabel pl; IMov R_SP R_AUX1;
               IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
               IAlloc R_SP R_SP]
           ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
           ++ cbody ++ pop R_ARG ++ pop R_SP ++ [:: IJump])].
Proof.
  move=> Hg HgP Hcp Hpl Hmain.
  case: (entry_ext_of_compiled Hg HgP Hcp Hpl Hmain)
    => [pcW [pcE [cbody [sA [sB [_ _ EcE Hce HcodeE]]]]]].
  by exists pcE, cbody, sA, sB.
Qed.

(** …and at `(main, main)`, where the body sits after a possible one-cell halt
    pad AND the longer dual entry. The conclusion is IDENTICAL to
    `entry_int_of_compiled`'s — only the offset of `pcE` differs, and that is
    existential. *)
Lemma entry_int_of_compiled_main pr c Cprocs P cd plm pl e s s' :
  getm (Intermediate.prog_procedures pr) c = Some Cprocs ->
  getm Cprocs P = Some cd ->
  compile_proc c (lbp c) (scr c) plm P e s = Some (cd, s') ->
  getm plm P = Some pl ->
  Component.eqb c Component.main && Procedure.eqb P Procedure.main = true ->
  exists pcE cbody sA sB,
    [/\ Pointer.component pcE = c,
        compile_expr c (lbp c) (scr c) plm e sA = Some (cbody, sB)
      & TMacros.code_at_I (Transitional.intermediate_to_transitional pr) c pcE
          ([:: ILabel pl; IMov R_SP R_AUX1;
               IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
               IAlloc R_SP R_SP]
           ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
           ++ cbody ++ pop R_ARG ++ pop R_SP ++ [:: IJump])].
Proof.
  move=> Hg HgP Hcp Hpl Hmain.
  case: (compile_proc_shape_main_gen Hcp Hpl Hmain)
    => [pad [bodyc [sA [sB [lmain [lreturn [_ Hce Ecd]]]]]]].
  case: (find_plabel_in_code_at Hg HgP) => [pre [post [Elin _ _]]].
  set A := (pad ++ ([:: IConst (IInt 1) R_ONE] ++
                    [:: IMov R_SP R_AUX1;
                        IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                        IAlloc R_SP R_SP] ++
                    push R_AUX1 ++ load_arg (scr c) R_AUX1 ++ push R_AUX1 ++
                    push R_RA ++
                    [:: IConst (IPtr (flag_buf_ptr (scr c))) R_AUX1;
                        ILoad R_AUX1 R_AUX2] ++
                    push R_AUX2 ++
                    [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM;
                        ILabel lmain; IConst (IInt 1) R_AUX2;
                        IStore R_AUX1 R_AUX2; IJal pl] ++
                    pop R_ARG ++ pop R_RA ++ pop R_AUX1 ++
                    store_arg (scr c) R_AUX1 R_AUX2 ++ pop R_SP ++
                    [:: IBnz R_ARG lreturn; IHalt; ILabel lreturn; IReturn])).
  set B := (ILabel pl ::
            ([:: IMov R_SP R_AUX1;
                 IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                 IAlloc R_SP R_SP] ++
             push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG] ++ bodyc ++
             (pop R_ARG ++ pop R_SP ++ [:: IJump]))).
  have EcdAB : cd = A ++ B ++ [::] by rewrite cats0 /A -catA.
  exists (c, 0, Z.of_nat (size pre + 1 + size A)), bodyc, sA, sB.
  split.
  - by [].
  - exact: Hce.
  - have Hc := code_at_I_in_proc (A := A) (B := B) (D := [::]) Hg HgP Elin EcdAB.
    move: Hc. rewrite /B. by do 10!rewrite -?catA ?cat_cons ?cat0s ?cats0.
Qed.

(** ★ …hence `entry_int` for EVERY callee, main included. *)
Lemma entry_int_any_of_compiled pr c Cprocs P cd plm pl e s s' :
  getm (Intermediate.prog_procedures pr) c = Some Cprocs ->
  getm Cprocs P = Some cd ->
  compile_proc c (lbp c) (scr c) plm P e s = Some (cd, s') ->
  getm plm P = Some pl ->
  exists pcE cbody sA sB,
    [/\ Pointer.component pcE = c,
        compile_expr c (lbp c) (scr c) plm e sA = Some (cbody, sB)
      & TMacros.code_at_I (Transitional.intermediate_to_transitional pr) c pcE
          ([:: ILabel pl; IMov R_SP R_AUX1;
               IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
               IAlloc R_SP R_SP]
           ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
           ++ cbody ++ pop R_ARG ++ pop R_SP ++ [:: IJump])].
Proof.
  move=> Hg HgP Hcp Hpl.
  case Hm: (Component.eqb c Component.main && Procedure.eqb P Procedure.main).
  - exact: (entry_int_of_compiled_main Hg HgP Hcp Hpl Hm).
  - exact: (entry_int_of_compiled Hg HgP Hcp Hpl Hm).
Qed.

(** ★ …and the same composition for main: the header resolution, the ENTRY the
    machine lands on, and the body. This is the code half of `start_ok`. *)
Lemma entry_main_of_compiled pr c Cprocs P cd plm pl e s s' :
  getm (Intermediate.prog_procedures pr) c = Some Cprocs ->
  getm Cprocs P = Some cd ->
  compile_proc c (lbp c) (scr c) plm P e s = Some (cd, s') ->
  getm plm P = Some pl ->
  Component.eqb c Component.main && Procedure.eqb P Procedure.main = true ->
  immediately_final e = false ->
  exists pcW pcE cbody sA sB lmain lreturn,
    [/\ Transitional.find_plabel_in_code
          (Transitional.intermediate_to_transitional pr) c P = Some pcW,
        TMacros.code_at_I (Transitional.intermediate_to_transitional pr) c
          (Pointer.inc pcW)
          (IConst (IInt 1) R_ONE
           :: [:: IMov R_SP R_AUX1;
                  IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                  IAlloc R_SP R_SP]
              ++ push R_AUX1 ++ load_arg (scr c) R_AUX1 ++ push R_AUX1
              ++ push R_RA
              ++ [:: IConst (IPtr (flag_buf_ptr (scr c))) R_AUX1;
                     ILoad R_AUX1 R_AUX2]
              ++ push R_AUX2
              ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
                     IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2; IJal pl]
              ++ pop R_ARG ++ pop R_RA ++ pop R_AUX1
                 ++ store_arg (scr c) R_AUX1 R_AUX2 ++ pop R_SP
                 ++ [:: IBnz R_ARG lreturn; IHalt; ILabel lreturn; IReturn]),
        Pointer.component pcE = c,
        compile_expr c (lbp c) (scr c) plm e sA = Some (cbody, sB)
      & TMacros.code_at_I (Transitional.intermediate_to_transitional pr) c pcE
          ([:: ILabel pl; IMov R_SP R_AUX1;
               IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
               IAlloc R_SP R_SP]
           ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
           ++ cbody ++ pop R_ARG ++ pop R_SP ++ [:: IJump])].
Proof.
  move=> Hg HgP Hcp Hpl Hmain Hnf.
  case: (@compile_proc_shape_main c plm P e s cd s' pl Hcp Hpl Hmain Hnf)
    => [bodyc [sA [sB [lmain [lreturn [Hce Ecd]]]]]].
  case: (find_plabel_in_code_at Hg HgP) => [pre [post [Elin _ Hfind]]].
  set W := ([:: IConst (IInt 1) R_ONE] ++
            [:: IMov R_SP R_AUX1;
                IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                IAlloc R_SP R_SP] ++
            push R_AUX1 ++ load_arg (scr c) R_AUX1 ++ push R_AUX1 ++
            push R_RA ++
            [:: IConst (IPtr (flag_buf_ptr (scr c))) R_AUX1;
                ILoad R_AUX1 R_AUX2] ++
            push R_AUX2 ++
            [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
                IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2; IJal pl] ++
            pop R_ARG ++ pop R_RA ++ pop R_AUX1 ++
            store_arg (scr c) R_AUX1 R_AUX2 ++ pop R_SP ++
            [:: IBnz R_ARG lreturn; IHalt; ILabel lreturn; IReturn]).
  set B := (ILabel pl ::
            ([:: IMov R_SP R_AUX1;
                 IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                 IAlloc R_SP R_SP] ++
             push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG] ++ bodyc ++
             (pop R_ARG ++ pop R_SP ++ [:: IJump]))).
  have EcdWB : cd = W ++ B ++ [::] by rewrite cats0.
  exists (c, 0, Z.of_nat (size pre)),
         (c, 0, Z.of_nat (size pre + 1 + size W)), bodyc, sA, sB,
         lmain, lreturn.
  split.
  - exact: Hfind.
  - apply: (code_at_I_after_header (B := W) (D := B) Hg HgP Elin).
    by rewrite Ecd.
  - by [].
  - exact: Hce.
  - exact: (code_at_I_in_proc (A := W) (B := B) (D := [::]) Hg HgP Elin EcdWB).
Qed.

(** The header cell IS what the machine reads at the resolved address — the
    third premise of `TS.Call`, and the carrier of the `entry` tag its
    `check_pc_call` inspects. *)
Lemma nth_error_cat_size {A : Type} (l1 l2 : seq A) (x : A) :
  List.nth_error (l1 ++ x :: l2) (size l1) = Some x.
Proof. by elim: l1 => [|y l1 IH] //=. Qed.

Lemma executing_header pr c Cprocs P cd pre post :
  getm (Intermediate.prog_procedures pr) c = Some Cprocs ->
  getm Cprocs P = Some cd ->
  Transitional.linearize_component pr c
  = pre ++ (Transitional.TrLabel (inr (c, P)),
            Transitional.head_tag pr c P)
          :: [seq Transitional.instr_to_transitional c i | i <- cd] ++ post ->
  Transitional.executing (Transitional.intermediate_to_transitional pr)
    (c, 0, Z.of_nat (size pre)) (Transitional.TrLabel (inr (c, P)))
    (Transitional.head_tag pr c P) c.
Proof.
  move=> Hg HgP Elin.
  exists (Transitional.linearize_component pr c).
  split; first by []. split; first exact: (cde_getm Hg).
  split; first by rewrite /=; lia.
  by rewrite /= Nat2Z.id Elin nth_error_cat_size.
Qed.

(* ================================================================== *)
(* …and up to the whole compiled program                               *)
(* ================================================================== *)

(** ★ …and the guard-free version, which is `TSim.entry_int` itself once the
    global environment's procedure map is unfolded. *)
Lemma entry_int_whole_any p tp C P P_expr plm tl :
  Source.well_formed_program p ->
  compile_program p = Some tp ->
  Source.find_procedure (Source.prog_procedures p) C P = Some P_expr ->
  getm (labelsP p) C = Some plm ->
  getm plm P = Some tl ->
  exists pcE cbody sA sB,
    [/\ Pointer.component pcE = C,
        compile_expr C (lbp C) (scr C) plm P_expr sA = Some (cbody, sB)
      & TMacros.code_at_I (Transitional.intermediate_to_transitional tp) C pcE
          ([:: ILabel tl; IMov R_SP R_AUX1;
               IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
               IAlloc R_SP R_SP]
           ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
           ++ cbody ++ pop R_ARG ++ pop R_SP ++ [:: IJump])].
Proof.
  move=> Hwf Hcomp Hfind Hplm Htl.
  move: Hfind. rewrite /Source.find_procedure.
  case HgC: (getm (Source.prog_procedures p) C) => [Cprocs|] //= HgP.
  case: (compile_prog_procedures_spec Hwf Hcomp)
    => [labels [cenv1 [Egen HSPEC]]].
  have Elab : labelsP p = labels by rewrite /labelsP Egen.
  case: (HSPEC _ _ _ _ HgC HgP)
    => [plm' [Cprocs' [cd [s1 [s2 [Hplm' HgT HgTP Hcp]]]]]].
  have Eplm : plm' = plm by move: Hplm; rewrite Elab Hplm' => -[->].
  subst plm'.
  exact: (entry_int_any_of_compiled HgT HgTP Hcp Htl).
Qed.

(** The LRC entry check, discharged. `head_tag`'s allowed-caller list is
    `filter allowed_call_by (domm I)`, and `allowed_call_by C` unfolds to the
    conjunction of the callee EXPORTING the procedure and the caller IMPORTING
    it — so `check_pc_call` needs both halves of the interface agreement, not
    just the caller's import. *)
Lemma check_comp_belongs_in (C : Component.id) (l : seq Component.id) :
  C \in l -> Transitional.check_comp_belongs C l.
Proof.
  elim: l => [|c0 l IH] //. rewrite inE => /orP [/eqP ->|Hin].
  - by left.
  - by right; exact: IH.
Qed.

Lemma check_pc_call_header pr c P C CIc CIC :
  getm (Intermediate.prog_interface pr) c = Some CIc ->
  P \in Component.export CIc ->
  getm (Intermediate.prog_interface pr) C = Some CIC ->
  (c, P) \in Component.import CIC ->
  Transitional.check_pc_call C (Transitional.head_tag pr c P) P.
Proof.
  move=> Hc Hex HC Him.
  apply: Transitional.PcCall; first by [].
  apply: check_comp_belongs_in.
  rewrite mem_filter. apply/andP; split; last by rewrite mem_domm HC.
  by rewrite /= Hc HC Hex Him.
Qed.

(** ★ `entry_ext`'s CODE half for every callee, main included — a THREE-way
    disjunction, because `compile_proc` gives `(main, main)` its dual entry and,
    when main's body is immediately final, puts the HALT PAD in front of that.
    All three are real shapes of real compiled programs; the diagram kills the
    third from the invariant. *)
Lemma entry_ext_any_of_compiled pr c Cprocs P cd plm pl e s s' :
  getm (Intermediate.prog_procedures pr) c = Some Cprocs ->
  getm Cprocs P = Some cd ->
  compile_proc c (lbp c) (scr c) plm P e s = Some (cd, s') ->
  getm plm P = Some pl ->
  exists pcW pcE cbody sA sB,
    [/\ Transitional.find_plabel_in_code
          (Transitional.intermediate_to_transitional pr) c P = Some pcW,
        (TMacros.code_at_I (Transitional.intermediate_to_transitional pr) c
           (Pointer.inc pcW)
           (IConst (IInt 1) R_ONE
            :: [:: IMov R_SP R_AUX1;
                   IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                   IAlloc R_SP R_SP]
               ++ push R_AUX1 ++ load_arg (scr c) R_AUX1 ++ push R_AUX1
               ++ push R_RA
               ++ IJal pl
                  :: pop R_RA ++ pop R_AUX1
                     ++ store_arg (scr c) R_AUX1 R_AUX2
                     ++ pop R_SP ++ [:: IReturn])
         \/ (c = Component.main /\ exists lmain lret,
               TMacros.code_at_I (Transitional.intermediate_to_transitional pr)
                 c (Pointer.inc pcW)
                 (IConst (IInt 1) R_ONE
                  :: [:: IMov R_SP R_AUX1;
                         IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                         IAlloc R_SP R_SP]
                     ++ push R_AUX1 ++ load_arg (scr c) R_AUX1
                     ++ push R_AUX1 ++ push R_RA
                     ++ [:: IConst (IPtr (flag_buf_ptr (scr c))) R_AUX1;
                            ILoad R_AUX1 R_AUX2]
                     ++ push R_AUX2
                     ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM;
                            ILabel lmain; IConst (IInt 1) R_AUX2;
                            IStore R_AUX1 R_AUX2]
                     ++ IJal pl
                        :: pop R_ARG ++ pop R_RA ++ pop R_AUX1
                           ++ store_arg (scr c) R_AUX1 R_AUX2 ++ pop R_SP
                           ++ [:: IBnz R_ARG lret; IHalt; ILabel lret;
                                  IReturn]))
         \/ (c = Component.main /\ P = Procedure.main /\ exists tl,
               TMacros.code_at_I (Transitional.intermediate_to_transitional pr)
                 c (Pointer.inc pcW) (IHalt :: tl))),
        Pointer.component pcE = c,
        compile_expr c (lbp c) (scr c) plm e sA = Some (cbody, sB)
      & TMacros.code_at_I (Transitional.intermediate_to_transitional pr) c pcE
          ([:: ILabel pl; IMov R_SP R_AUX1;
               IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
               IAlloc R_SP R_SP]
           ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
           ++ cbody ++ pop R_ARG ++ pop R_SP ++ [:: IJump])].
Proof.
  move=> Hg HgP Hcp Hpl.
  case Hm: (Component.eqb c Component.main && Procedure.eqb P Procedure.main);
    last first.
  { case: (entry_ext_of_compiled Hg HgP Hcp Hpl Hm)
      => [pcW [pcE [cbody [sA [sB [Hfind HcodeW EcE Hce HcodeE]]]]]].
    exists pcW, pcE, cbody, sA, sB. split=> //. by left. }
  have [Ec EP] : c = Component.main /\ P = Procedure.main.
  { move: Hm => /andP [/PeanoNat.Nat.eqb_eq -> /PeanoNat.Nat.eqb_eq ->].
    by split. }
  case: (compile_proc_shape_main_gen Hcp Hpl Hm)
    => [pad [bodyc [sA [sB [lmain [lreturn [Epad Hce Ecd]]]]]]].
  rewrite Epad in Ecd.
  case: (find_plabel_in_code_at Hg HgP) => [pre [post [Elin _ Hfind]]].
  case: (entry_int_of_compiled_main Hg HgP Hcp Hpl Hm)
    => [pcE [cbody [sA' [sB' [EcE Hce' HcodeE]]]]].
  set W := ([:: IConst (IInt 1) R_ONE] ++
            [:: IMov R_SP R_AUX1;
                IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                IAlloc R_SP R_SP] ++
            push R_AUX1 ++ load_arg (scr c) R_AUX1 ++ push R_AUX1 ++
            push R_RA ++
            [:: IConst (IPtr (flag_buf_ptr (scr c))) R_AUX1;
                ILoad R_AUX1 R_AUX2] ++
            push R_AUX2 ++
            [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM; ILabel lmain;
                IConst (IInt 1) R_AUX2; IStore R_AUX1 R_AUX2; IJal pl] ++
            pop R_ARG ++ pop R_RA ++ pop R_AUX1 ++
            store_arg (scr c) R_AUX1 R_AUX2 ++ pop R_SP ++
            [:: IBnz R_ARG lreturn; IHalt; ILabel lreturn; IReturn])
    in Ecd *.
  set B := (ILabel pl ::
            ([:: IMov R_SP R_AUX1;
                 IConst (IInt (Z.of_nat (4 + stack_need e))) R_SP;
                 IAlloc R_SP R_SP] ++
             push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG] ++ bodyc ++
             (pop R_ARG ++ pop R_SP ++ [:: IJump]))) in Ecd *.
  exists (c, 0, Z.of_nat (size pre)), pcE, cbody, sA', sB'.
  split=> //.
  case Hfin: (immediately_final e); rewrite Hfin /= in Ecd.
  - (* the HALT PAD is there *)
    right; right. split; first exact: Ec. split; first exact: EP.
    exists [::].
    apply: (code_at_I_after_header (B := [:: IHalt]) (D := W ++ B)
              Hg HgP Elin).
    by rewrite Ecd.
  - (* no pad: main's dual entry sits right after the header *)
    right; left. split; first exact: Ec. exists lmain, lreturn.
    have Hc := code_at_I_after_header (B := W) (D := B) Hg HgP Elin
                 (ltac:(by rewrite Ecd) : cd = W ++ B).
    move: Hc. rewrite /W. by do 12!rewrite -?catA ?cat_cons ?cat0s ?cats0.
Qed.

(** ★ `entry_ext` for a whole compiled program, at EVERY callee.

    The four interface facts `check_pc_call_header` needs come from the two
    halves of the interface story: `imported_procedure` (a premise — the source
    step that triggers this carries it) gives the CALLER's side, and
    `closed_interface` turns it into the CALLEE's export. Neither is derivable
    from "Cf has a procedure P", which is why the premise had to be added. *)
Lemma entry_ext_whole_any p tp C Cf P P_expr :
  Source.well_formed_program p ->
  Source.closed_program p ->
  compile_program p = Some tp ->
  imported_procedure (Source.prog_interface p) C Cf P ->
  Source.find_procedure (Source.prog_procedures p) Cf P = Some P_expr ->
  Cf \in domm (Source.prog_interface p) /\
  exists pcW tniW plmf pl pcE cbody sA sB,
    [/\ [/\ Transitional.find_plabel_in_code
              (Transitional.intermediate_to_transitional tp) Cf P = Some pcW,
            Transitional.executing
              (Transitional.intermediate_to_transitional tp) pcW
              (Transitional.TrLabel (inr (Cf, P))) tniW Cf,
            Transitional.check_pc_call C tniW P
          & getm (labelsP p) Cf = Some plmf],
        (TMacros.code_at_I (Transitional.intermediate_to_transitional tp) Cf
           (Pointer.inc pcW)
           (IConst (IInt 1) R_ONE
            :: [:: IMov R_SP R_AUX1;
                   IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
                   IAlloc R_SP R_SP]
               ++ push R_AUX1 ++ load_arg (scr Cf) R_AUX1 ++ push R_AUX1
               ++ push R_RA
               ++ IJal pl
                  :: pop R_RA ++ pop R_AUX1
                     ++ store_arg (scr Cf) R_AUX1 R_AUX2
                     ++ pop R_SP ++ [:: IReturn])
         \/ (Cf = Component.main /\ exists lmain lret,
               TMacros.code_at_I (Transitional.intermediate_to_transitional tp)
                 Cf (Pointer.inc pcW)
                 (IConst (IInt 1) R_ONE
                  :: [:: IMov R_SP R_AUX1;
                         IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
                         IAlloc R_SP R_SP]
                     ++ push R_AUX1 ++ load_arg (scr Cf) R_AUX1
                     ++ push R_AUX1 ++ push R_RA
                     ++ [:: IConst (IPtr (flag_buf_ptr (scr Cf))) R_AUX1;
                            ILoad R_AUX1 R_AUX2]
                     ++ push R_AUX2
                     ++ [:: IBnz R_AUX2 lmain; IConst (IInt 0) R_COM;
                            ILabel lmain; IConst (IInt 1) R_AUX2;
                            IStore R_AUX1 R_AUX2]
                     ++ IJal pl
                        :: pop R_ARG ++ pop R_RA ++ pop R_AUX1
                           ++ store_arg (scr Cf) R_AUX1 R_AUX2 ++ pop R_SP
                           ++ [:: IBnz R_ARG lret; IHalt; ILabel lret;
                                  IReturn]))
         \/ (Cf = Component.main /\ P = Procedure.main /\ exists tl,
               TMacros.code_at_I (Transitional.intermediate_to_transitional tp)
                 Cf (Pointer.inc pcW) (IHalt :: tl))),
        Pointer.component pcE = Cf,
        compile_expr Cf (lbp Cf) (scr Cf) plmf P_expr sA = Some (cbody, sB)
      & TMacros.code_at_I (Transitional.intermediate_to_transitional tp) Cf pcE
          ([:: ILabel pl; IMov R_SP R_AUX1;
               IConst (IInt (Z.of_nat (4 + stack_need P_expr))) R_SP;
               IAlloc R_SP R_SP]
           ++ push R_AUX1 ++ push R_ARG ++ [:: IMov R_COM R_ARG]
           ++ cbody ++ pop R_ARG ++ pop R_SP ++ [:: IJump])].
Proof.
  move=> Hwf Hclosed Hcomp Him Hfind.
  (* --- the four interface facts --- *)
  case: Him => [CIC [HgCIC Himp]].
  have Him' : imported_procedure (Source.prog_interface p) C Cf P
    by exists CIC.
  case: (Source.cprog_closed_interface Hclosed Him') => [CIf [HgCIf Hexp]].
  have Eif : Intermediate.prog_interface tp = Source.prog_interface p
    := compilation_preserves_interface _ _ Hcomp.
  split; first by rewrite mem_domm HgCIf.
  (* --- the code --- *)
  move: Hfind. rewrite /Source.find_procedure.
  case HgC: (getm (Source.prog_procedures p) Cf) => [Cprocs|] //= HgP.
  case: (compile_prog_procedures_spec Hwf Hcomp)
    => [labels [cenv1 [Egen HSPEC]]].
  have Elab : labelsP p = labels by rewrite /labelsP Egen.
  case: (HSPEC _ _ _ _ HgC HgP)
    => [plmf [Cprocs' [cd [s1 [s2 [Hplm' HgT HgTP Hcp]]]]]].
  have [pl Hpl] : exists pl, getm plmf P = Some pl.
  { move: Hcp. rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift.
    case: (getm plmf P) => [x|] //=. by exists x. }
  case: (find_plabel_in_code_at HgT HgTP) => [pre [post [Elin _ Hfind0]]].
  case: (entry_ext_any_of_compiled HgT HgTP Hcp Hpl)
    => [pcW [pcE [cbody [sA [sB [Hfind1 Hwrap EcE Hce HcodeE]]]]]].
  have EpcW : pcW = (Cf, 0, Z.of_nat (size pre))
    by move: Hfind1; rewrite Hfind0 => -[->].
  exists pcW, (Transitional.head_tag tp Cf P), plmf, pl, pcE, cbody, sA, sB.
  split=> //.
  split.
  - exact: Hfind1.
  - rewrite EpcW. exact: (executing_header HgT HgTP Elin).
  - apply: (check_pc_call_header (CIc := CIf) (CIC := CIC));
      by rewrite ?Eif; eassumption.
  - by rewrite Elab.
Qed.

(** ★ The `labelsP`-domain fact: a component with a label map is a component
    of the program. `gen_all_procedures_labels_spec` characterises the map's
    domain as the procedure map's, and well-formedness identifies that with the
    INTERFACE's — which is the form Stage 4's `vi_dom` and `diagram_return_ext`
    consume. *)
Lemma labelsP_domm p C plm :
  Source.well_formed_program p ->
  getm (labelsP p) C = Some plm ->
  C \in domm (Source.prog_interface p).
Proof.
  move=> Hwf Hg.
  have Huniq : uniq (unzip1 (elementsm (Source.prog_procedures p)))
    := sorted_uniq (@Ord.lt_trans _) (@Ord.ltxx _)
         (valP (Source.prog_procedures p)).
  case: (gen_all_procedures_labels_spec
           (elementsm (Source.prog_procedures p)) init_env Huniq)
    => [ml [s' [Hgen [Hdom _]]]].
  have Elab : labelsP p = ml by rewrite /labelsP Hgen.
  move: Hg; rewrite Elab => Hg.
  have Hs : isSome (ml C) by rewrite Hg.
  move: Hs; rewrite Hdom unzip1_elementsm_domm => Hin.
  by rewrite (Source.wfprog_defined_procedures Hwf).
Qed.

(* ================================================================== *)
(* Component-wide label uniqueness                                     *)
(* ================================================================== *)

(** `cde_getm`'s converse-in-shape: whatever the code map returns for a
    component, it is that component's linearization. Enough on its own —
    a component with no procedures linearizes to `[::]`, whose label count is
    trivially 0. *)
Lemma cde_getm_shape pr c C_code :
  getm (Transitional.intermediate_to_transitional pr) c = Some C_code ->
  C_code = Transitional.linearize_component pr c.
Proof.
  rewrite /Transitional.intermediate_to_transitional /Transitional.intermediate_to_transitional_gen mkfmapE.
  elim: (elementsm (Intermediate.prog_procedures pr)) => [|[c0 x0] l IH] //=.
  by case: ifP => [/eqP -> [<-]|_ H] //; exact: IH H.
Qed.

(** The opcode map takes `ILabel` to `TrLabel (inl _)` and everything else to
    something that is not a `TrLabel (inl _)`, so the two label counts agree
    cell for cell. `is_tlabel`/`is_ilabel` compare their arguments in opposite
    orders, which is the only wrinkle. *)
Lemma is_tlabel_map c l i :
  TLabel.is_tlabel l (Transitional.instr_to_transitional c i) = is_ilabel l i.
Proof.
  (* [ICall] is the one non-label case that does not compute away: its image is
     an [if Nat.eqb c c'] whose two branches are both [TrJalProc]. *)
  case: i => [|l'|v r|r1 r2|op r1 r2 r3|r1 r2|r1 r2|r1 r2|r l0|
              |l0|c' P||] //=. by case: (Nat.eqb c c').
Qed.

(** ★ `TDrain.labels_uniq` for a compiled program: `S2I/LabelUniq.v:834`'s
    `compiled_labels_unique` states the bound as a `sumn` of per-procedure
    counts, and `linearize_component` is a `flatten` of per-procedure
    linearizations — so `count_flatten` lines the two up directly. The
    procedure HEADERS are `TrLabel (inr _)` and are not counted, which is what
    makes flattening procedures into one array safe. *)
Lemma labels_uniq_compiled p tp :
  compile_program p = Some tp ->
  forall C0, TDrain.labels_uniq (Transitional.intermediate_to_transitional tp)
               C0.
Proof.
  move=> Hcomp C0 l C_code Hg.
  rewrite (cde_getm_shape Hg) /Transitional.linearize_component /Transitional.linearize_component_gen.
  case Hp: (getm (Intermediate.prog_procedures tp) C0) => [Cprocs|] //=.
  rewrite count_flatten -map_comp.
  have -> : [seq (count (TLabel.is_tlabel l)
                  \o Transitional.linearize_proc tp C0) p'
            | p' <- domm Cprocs]
          = [seq count (is_ilabel l) (odflt [::] (getm Cprocs p'))
            | p' <- domm Cprocs].
  { apply: eq_map => p' /=. rewrite /Transitional.linearize_proc /Transitional.linearize_proc_gen /= Hp /=.
    rewrite count_map. by apply: eq_count => i /=; exact: is_tlabel_map. }
  exact: (compiled_labels_unique Hcomp l Hp).
Qed.

(* ================================================================== *)
(* The initial state                                                   *)
(* ================================================================== *)

(** Every declared component has a memory at startup: the initial memory is a
    `mkfmapf` over `domm (prog_interface tp)`, so membership IS existence.
    This is `ef_main_entry_run`'s `exists cm, getm m C = Some cm`. *)
Lemma initial_memory_component tp C :
  C \in domm (Intermediate.prog_interface tp) ->
  exists cm,
    getm (Transitional.Memory.prepare_procedures_initial_memory tp) C
    = Some cm.
Proof.
  move=> HC. rewrite /Transitional.Memory.prepare_procedures_initial_memory.
  rewrite mapmE /Transitional.Memory.prepare_procedures_initial_memory_aux.
  by rewrite mkfmapfE HC /=; eexists.
Qed.

(** `Register.init` is a literal seven-key map of `tUndef`, so every register
    starts DATA-tagged — including `R_RA`, which is what makes main's entry a
    junk push rather than a capability spill. *)
Lemma init_regs_tag r :
  Transitional.Register.get_tag r Transitional.Register.init = Some Other.
Proof. by case: r. Qed.

Lemma init_regs_tag_val r :
  tvtag (Transitional.Register.get r Transitional.Register.init) = Other.
Proof. by case: r. Qed.

Lemma init_regs_dom : TInv.regs_dom Transitional.Register.init.
Proof. by case=> /=; eexists. Qed.

(** Reserving procedure blocks does not touch CONTENT — [reserve_block] only
    bumps [nextblock] — so the buffers `prealloc` laid down survive into the
    initial memory untouched. With the accumulator threaded, this is a
    two-line induction. *)
Lemma reserve_blocks_content m n :
  Transitional.Memory.content (Transitional.Memory.reserve_blocks m n).1
  = Transitional.Memory.content m.
Proof.
  elim: n => [|n IH] //=.
  by case E: (Transitional.Memory.reserve_blocks m n) IH => [m' bs] /= <-.
Qed.

Lemma reserve_blocks_load m n b i :
  Transitional.Memory.load_b (Transitional.Memory.reserve_blocks m n).1 b i
  = Transitional.Memory.load_b m b i.
Proof.
  by rewrite /Transitional.Memory.load_b reserve_blocks_content.
Qed.

(** ★ The two cells main's entry reads. `gen_buffers` puts
    `inr [:: Undef; Int 0]` at block 1 of every component, `prealloc` tags both
    cells `Other` through `to_tagged_block`, and reserving procedure blocks
    leaves `content` alone — so the SCRATCH cell starts `Undef` and the FLAG
    cell starts `Int 0`, which is what makes main's `IBnz` fall through to its
    `IHalt` on the initial run. *)
Lemma initial_cells tp C ii :
  getm (Intermediate.prog_buffers tp) C
    = Some (mkfmap [:: (0, ii); (1, inr [:: Undef; Int 0])]) ->
  C \in domm (Intermediate.prog_interface tp) ->
  Transitional.Memory.load
    (Transitional.Memory.prepare_procedures_initial_memory tp) (C, 1, 0%Z)
    = Some (MVal Other Undef, def_mem_tag C false)
  /\ Transitional.Memory.load
       (Transitional.Memory.prepare_procedures_initial_memory tp) (C, 1, 1%Z)
     = Some (MVal Other (Int 0), def_mem_tag C false).
Proof.
  move=> Hbuf HC.
  have Hcm : getm (Transitional.Memory.prepare_procedures_initial_memory tp) C
           = Some (Transitional.Memory.reserve_component_blocks tp C
                     (Transitional.Memory.prealloc
                        (mapm (fun a => (C, a))
                           (odflt emptym (Intermediate.prog_buffers tp C))))
                     (elementsm (odflt emptym
                        (Intermediate.prog_procedures tp C)))).1.1.
  { rewrite /Transitional.Memory.prepare_procedures_initial_memory mapmE
            /Transitional.Memory.prepare_procedures_initial_memory_aux
            mkfmapfE HC /=. by []. }
  set Cmem := (Transitional.Memory.prealloc
                 (mapm (fun a => (C, a))
                    (odflt emptym (Intermediate.prog_buffers tp C)))).
  have Hchunk : getm (Transitional.Memory.content Cmem) 1
              = Some (Transitional.to_tagged_block C [:: Undef; Int 0]).
  { have Hb1 : getm (odflt emptym (Intermediate.prog_buffers tp C)) 1
             = Some (inr [:: Undef; Int 0]) by rewrite Hbuf.
    by rewrite /Cmem /Transitional.Memory.prealloc /= !mapmE Hb1. }
  have Hload : forall i : Z, (0 <= i)%Z ->
      Transitional.Memory.load
        (Transitional.Memory.prepare_procedures_initial_memory tp) (C, 1, i)
      = List.nth_error (Transitional.to_tagged_block C [:: Undef; Int 0])
          (Z.to_nat i).
  { move=> i Hi. rewrite /Transitional.Memory.load /= Hcm /=.
    rewrite /Transitional.Memory.reserve_component_blocks /=.
    case E: (Transitional.Memory.reserve_blocks _ _) => [Cmem' bs] /=.
    have Ec : Cmem' = (Transitional.Memory.reserve_blocks Cmem
                         (length (elementsm (odflt emptym
                            (Intermediate.prog_procedures tp C))))).1
      by rewrite E.
    rewrite /Transitional.Memory.load_b Ec reserve_blocks_content Hchunk.
    by have -> : (0 <=? i)%Z = true by apply/Z.leb_le. }
  by split; [rewrite (Hload 0%Z) | rewrite (Hload 1%Z)]; try lia.
Qed.

(* ================================================================== *)
(* Towards the initial [minj]                                          *)
(* ================================================================== *)

(** With the EMPTY renaming, four of `minj`'s ten fields are vacuous
    (`mj_load`, `mj_rng`, `mj_dom`, `mj_data` all quantify over `a C b = Some
    b'`), and the rest are structural facts about the two initial memories.
    `mj_wf_t` is the one with content: `prealloc` sets `nextblock` to one past
    the largest declared block, so every block it lays down is in range. *)
Lemma fold_max_ge (s : seq nat) acc : acc <= fold_left Nat.max s acc.
Proof.
  elim: s acc => [|x s IH] acc //=.
  apply: leq_trans (IH (Nat.max acc x)). by lia.
Qed.

Lemma fold_max_ub (s : seq nat) acc b : b \in s -> b <= fold_left Nat.max s acc.
Proof.
  elim: s acc => [|x s IH] acc //. rewrite inE => /orP [/eqP ->|Hin].
  - apply: leq_trans (fold_max_ge s (Nat.max acc x)). by lia.
  - exact: IH Hin.
Qed.

Lemma cwf_prealloc bufs :
  TInject.cwf (Transitional.Memory.prealloc bufs).
Proof.
  move=> b. rewrite /TInject.cdomm /Transitional.Memory.prealloc /= domm_map
    => Hin.
  by rewrite ltnS; exact: fold_max_ub.
Qed.

(** …and reserving procedure blocks keeps it: `content` is untouched and
    `nextblock` only grows. *)
Lemma reserve_blocks_nextblock m n :
  Transitional.Memory.nextblock m
  <= Transitional.Memory.nextblock (Transitional.Memory.reserve_blocks m n).1.
Proof.
  elim: n => [|n IH] //=.
  case E: (Transitional.Memory.reserve_blocks m n) IH => [m' bs] /= IH.
  by rewrite /Transitional.Memory.reserve_block /=; lia.
Qed.

Lemma cwf_reserve_blocks m n :
  TInject.cwf m -> TInject.cwf (Transitional.Memory.reserve_blocks m n).1.
Proof.
  move=> Hwf b. rewrite /TInject.cdomm reserve_blocks_content => Hin.
  apply: leq_trans (reserve_blocks_nextblock m n). exact: Hwf.
Qed.

(** ★ The question `mj_load` raised, settled by well-formedness rather than by
    a side condition: `Source.well_formed_buffer_value` forces every pointer in
    a static buffer to point at `(C, Block.local, _)` — the record's own comment
    calls this "buffer contents do not forge pointers into dynamic memory or
    into other components" — and `Block.local` is precisely the block
    `init_renaming` maps, identically. So every buffer value injects into
    itself. *)
Lemma val_inject_init_buffer C v :
  Source.well_formed_buffer_value C v -> val_inject init_renaming v v.
Proof.
  case: v => [z|[[C' b] o]|] //=; first by move=> _; exact: VI_int.
  - move=> /andP [Hb HC].
    have Eb : b = Block.local by apply/PeanoNat.Nat.eqb_eq.
    rewrite Eb. apply: VI_ptr. by rewrite /init_renaming eqxx.
  - by move=> _; exact: VI_undef.
Qed.

(** `mj_data` at the initial state: every cell of a component's block 0 is
    `Other`-tagged, because `prealloc` builds it either from `repeat tUndef`
    (the `inl` case) or from `to_tagged_block`, whose `to_tagged_cell` is
    `MVal Other` (the `inr` case). Both are `Other`, so a dereference through
    the α-image of a source pointer never lands on a capability husk. *)
Lemma initial_block0_data tp C ii i w :
  getm (Intermediate.prog_buffers tp) C
    = Some (mkfmap [:: (0, ii); (1, inr [:: Undef; Int 0])]) ->
  C \in domm (Intermediate.prog_interface tp) ->
  Transitional.Memory.load
    (Transitional.Memory.prepare_procedures_initial_memory tp)
    (C, Block.local, i) = Some w ->
  tvtag w.1 = Other.
Proof.
  move=> Hbuf HC.
  have Hcm : getm (Transitional.Memory.prepare_procedures_initial_memory tp) C
           = Some (Transitional.Memory.reserve_component_blocks tp C
                     (Transitional.Memory.prealloc
                        (mapm (fun a => (C, a))
                           (odflt emptym (Intermediate.prog_buffers tp C))))
                     (elementsm (odflt emptym
                        (Intermediate.prog_procedures tp C)))).1.1.
  { rewrite /Transitional.Memory.prepare_procedures_initial_memory mapmE
            /Transitional.Memory.prepare_procedures_initial_memory_aux
            mkfmapfE HC /=. by []. }
  set Cmem := (Transitional.Memory.prealloc
                 (mapm (fun a => (C, a))
                    (odflt emptym (Intermediate.prog_buffers tp C)))).
  have Hb0 : getm (odflt emptym (Intermediate.prog_buffers tp C)) Block.local
           = Some ii by rewrite Hbuf.
  have Hchunk : getm (Transitional.Memory.content Cmem) Block.local
              = Some (match (C, ii) with
                      | (c, inl size) => repeat (tUndef, def_mem_tag c false) size
                      | (c, inr chunk) => Transitional.to_tagged_block c chunk
                      end)
    by rewrite /Cmem /Transitional.Memory.prealloc /= !mapmE Hb0.
  rewrite /Transitional.Memory.load /= Hcm /=
          /Transitional.Memory.reserve_component_blocks /=.
  case E: (Transitional.Memory.reserve_blocks _ _) => [Cmem' bs] /=.
  have Ec : Cmem' = (Transitional.Memory.reserve_blocks Cmem
                       (length (elementsm (odflt emptym
                          (Intermediate.prog_procedures tp C))))).1
    by rewrite E.
  rewrite /Transitional.Memory.load_b Ec reserve_blocks_content Hchunk.
  case: (0 <=? i)%Z => //.
  move: Hchunk; case: ii Hbuf Hb0 => [sz|chunk] _ _ _ Hnth.
  - move: Hnth. elim: sz (Z.to_nat i) => [|sz IH] [|k] //=.
    + by move=> [<-].
    + exact: IH k.
  - move: Hnth. elim: chunk (Z.to_nat i) => [|v chunk IH] [|k] //=.
    + by move=> [<-].
    + exact: IH k.
Qed.

(* ================================================================== *)
(* The two [prealloc]s correspond                                      *)
(* ================================================================== *)

(** `mj_load`'s remaining obstacle: the source and target initial memories are
    built by DIFFERENT `prealloc`s — `Common/Memory.v:151` lays down
    `repeat Undef` / `chunk`, `Transitional.v` lays down
    `repeat tUndef` / `to_tagged_block c chunk`. The two `init_block`s are
    structurally parallel, so the target chunk's VALUE projection is the source
    chunk, cell for cell. *)
Lemma nth_error_map_omap {A B : Type} (f : A -> B) (l : seq A) k :
  List.nth_error [seq f x | x <- l] k = omap f (List.nth_error l k).
Proof. by elim: l k => [|x l IH] [|k] //=. Qed.

Lemma nth_error_repeat_if {A : Type} (x : A) n k :
  List.nth_error (repeat x n) k = if k < n then Some x else None.
Proof. by elim: n k => [|n IH] [|k] //=; rewrite IH ltnS. Qed.

Lemma chunk_vals C ib k :
  omap (fun w : tvalue * mem_tag => Transitional.val w.1)
    (List.nth_error
       (match ib with
        | inl size => repeat (tUndef, def_mem_tag C false) size
        | inr chunk => Transitional.to_tagged_block C chunk
        end) k)
  = List.nth_error
      (match ib with
       | inl size => repeat Undef size
       | inr chunk => chunk
       end) k.
Proof.
  case: ib => [sz|chunk].
  - by rewrite !nth_error_repeat_if; case: (k < sz).
  - rewrite /Transitional.to_tagged_block nth_error_map_omap.
    by case: (List.nth_error chunk k).
Qed.

(** The SOURCE side's block 0, via `ComponentMemory.load_prealloc` — the
    module seals `load`, so it cannot be unfolded directly. *)
Lemma source_block0_load p C ib i :
  getm (Source.prog_buffers p) C = Some ib ->
  Common.Memory.Memory.load (Source.prepare_buffers p) (C, Block.local, i)
  = if (0 <=? i)%Z
    then List.nth_error (match ib with
                         | inl size => repeat Undef size
                         | inr chunk => chunk
                         end) (Z.to_nat i)
    else None.
Proof.
  move=> Hsb.
  rewrite /Common.Memory.Memory.load /Source.prepare_buffers /= mapmE Hsb /=.
  rewrite Common.Memory.ComponentMemory.load_prealloc /=.
  case: (Z.leb_spec 0 i) => [Hi|Hi] //.
  move: Hsb; case: ib => [sz|chunk] //= _.
  rewrite nth_error_repeat_if.
  case: (Z.ltb_spec i (Z.of_nat sz)) => [Hlt|Hge].
  - by have -> : (Z.to_nat i < sz) by lia.
  - by have -> : (Z.to_nat i < sz) = false
      by apply/negbTE; rewrite -leqNgt; lia.
Qed.

Lemma buffer_chunk_wf C ib v k :
  Source.well_formed_buffer C ib ->
  List.nth_error (match ib with
                  | inl size => repeat Undef size
                  | inr chunk => chunk
                  end) k = Some v ->
  Source.well_formed_buffer_value C v.
Proof.
  case: ib => [sz|chunk] /=.
  - by move=> _; rewrite nth_error_repeat_if; case: (k < sz) => // -[<-].
  - move=> /List.forallb_forall Hall Hin. apply: Hall.
    by apply: List.nth_error_In Hin.
Qed.

(** ★ `mj_load` at the initial state. Both sides reduce to an `nth_error` on
    their own block-0 chunk; `chunk_vals` identifies them, so the two options
    are the SAME option, and each value injects into itself by
    `val_inject_init_buffer`. *)
Lemma initial_mj_load p tp C ib i :
  getm (Source.prog_buffers p) C = Some ib ->
  Source.well_formed_buffer C ib ->
  getm (Intermediate.prog_buffers tp) C
    = Some (mkfmap [:: (0, ib); (1, inr [:: Undef; Int 0])]) ->
  C \in domm (Intermediate.prog_interface tp) ->
  option_rel (val_inject init_renaming)
    (Common.Memory.Memory.load (Source.prepare_buffers p) (C, Block.local, i))
    (TMem.vload (Transitional.Memory.prepare_procedures_initial_memory tp)
       (C, Block.local, i)).
Proof.
  move=> Hsb Hwfb Hbuf HC.
  set tchunk := (match ib with
                 | inl size => repeat (tUndef, def_mem_tag C false) size
                 | inr chunk => Transitional.to_tagged_block C chunk
                 end).
  set schunk := (match ib with
                 | inl size => repeat Undef size
                 | inr chunk => chunk
                 end).
  (* --- the target's block 0 --- *)
  have Hcm : getm (Transitional.Memory.prepare_procedures_initial_memory tp) C
           = Some (Transitional.Memory.reserve_component_blocks tp C
                     (Transitional.Memory.prealloc
                        (mapm (fun a => (C, a))
                           (odflt emptym (Intermediate.prog_buffers tp C))))
                     (elementsm (odflt emptym
                        (Intermediate.prog_procedures tp C)))).1.1.
  { rewrite /Transitional.Memory.prepare_procedures_initial_memory mapmE
            /Transitional.Memory.prepare_procedures_initial_memory_aux
            mkfmapfE HC /=. by []. }
  set Cmem := (Transitional.Memory.prealloc
                 (mapm (fun a => (C, a))
                    (odflt emptym (Intermediate.prog_buffers tp C)))).
  have Hchunk : getm (Transitional.Memory.content Cmem) Block.local
              = Some tchunk
    by rewrite /Cmem /Transitional.Memory.prealloc /= !mapmE Hbuf /=.
  have Etgt : TMem.vload
                (Transitional.Memory.prepare_procedures_initial_memory tp)
                (C, Block.local, i)
            = if (0 <=? i)%Z
              then omap (fun w : tvalue * mem_tag => Transitional.val w.1)
                        (List.nth_error tchunk (Z.to_nat i))
              else None.
  { rewrite /TMem.vload /Transitional.Memory.load /= Hcm /=
            /Transitional.Memory.reserve_component_blocks /=.
    case E: (Transitional.Memory.reserve_blocks _ _) => [Cmem' bs] /=.
    have Ec : Cmem' = (Transitional.Memory.reserve_blocks Cmem
                         (length (elementsm (odflt emptym
                            (Intermediate.prog_procedures tp C))))).1
      by rewrite E.
    rewrite /Transitional.Memory.load_b Ec reserve_blocks_content Hchunk.
    by case: (0 <=? i)%Z. }
  (* --- the source's block 0 --- *)
  have Esrc : Common.Memory.Memory.load (Source.prepare_buffers p)
                (C, Block.local, i)
            = if (0 <=? i)%Z
              then List.nth_error schunk (Z.to_nat i) else None.
    by rewrite /schunk (source_block0_load i Hsb).
  rewrite Etgt Esrc chunk_vals -/schunk.
  case: (0 <=? i)%Z => //=.
  case E: (List.nth_error schunk (Z.to_nat i)) => [v|] //=.
  apply: val_inject_init_buffer. exact: (buffer_chunk_wf Hwfb E).
Qed.

(* ================================================================== *)
(* The four shape fields                                               *)
(* ================================================================== *)

(** `mj_local_t`: block 0 is in the target component's domain. `prealloc` is a
    `mapm` over the component's buffer map and `reserve_blocks` leaves
    `content` alone, so both `domm`s collapse and the field comes down to
    `Block.local \in domm bufs` — which `gen_buffers`' block-0 entry gives. *)
Lemma initial_local_t tp C cm bufs :
  getm (Transitional.Memory.prepare_procedures_initial_memory tp) C = Some cm ->
  getm (Intermediate.prog_buffers tp) C = Some bufs ->
  Block.local \in domm bufs ->
  Block.local \in TInject.cdomm cm.
Proof.
  rewrite /Transitional.Memory.prepare_procedures_initial_memory mapmE
          /Transitional.Memory.prepare_procedures_initial_memory_aux mkfmapfE.
  case: ifP => [_|_] //=. move=> [<-] Hbuf Hin.
  rewrite /TInject.cdomm /Transitional.Memory.reserve_component_blocks /=.
  case E: (Transitional.Memory.reserve_blocks _ _) => [Cmem' bs] /=.
  have Ec : Cmem' = (Transitional.Memory.reserve_blocks
                       (Transitional.Memory.prealloc
                          (mapm (fun a => (C, a))
                             (odflt emptym (Intermediate.prog_buffers tp C))))
                       (length (elementsm (odflt emptym
                          (Intermediate.prog_procedures tp C))))).1
    by rewrite E.
  by rewrite Ec reserve_blocks_content /Transitional.Memory.prealloc /=
             !domm_map Hbuf.
Qed.

(** The source initial memory is a `mapm` too, so a component memory THERE is
    always a `prealloc` of the singleton buffer map — which is all three
    source-side fields need. *)
Lemma prepare_buffers_get p C cm :
  getm (Source.prepare_buffers p) C = Some cm ->
  exists ib, getm (Source.prog_buffers p) C = Some ib
             /\ cm = Common.Memory.ComponentMemory.prealloc (mkfmap [(0, ib)]).
Proof.
  rewrite /Source.prepare_buffers mapmE.
  case E: (getm (Source.prog_buffers p) C) => [ib|] //= [<-].
  by exists ib.
Qed.

Lemma initial_wf_s p C cm :
  getm (Source.prepare_buffers p) C = Some cm -> Common.Memory.ComponentMemory.wf cm.
Proof.
  by move=> /prepare_buffers_get [ib [_ ->]]; exact: Common.Memory.ComponentMemory.wf_prealloc.
Qed.

Lemma initial_local_s p C cm :
  getm (Source.prepare_buffers p) C = Some cm ->
  Block.local \in Common.Memory.ComponentMemory.domm cm.
Proof.
  move=> /prepare_buffers_get [ib [_ ->]].
  by rewrite (Common.Memory.ComponentMemory.domm_prealloc _ _ erefl) mem_domm.
Qed.

(** `mj_domm`: the T memory has every component the source has. Both memories
    are keyed by the same interface — the source through `prog_buffers` (equal
    domains by well-formedness), the target through `prog_interface`. *)
Lemma initial_mj_domm p tp C cm :
  domm (Source.prog_buffers p) = domm (Intermediate.prog_interface tp) ->
  getm (Source.prepare_buffers p) C = Some cm ->
  exists cm',
    getm (Transitional.Memory.prepare_procedures_initial_memory tp) C
    = Some cm'.
Proof.
  move=> Hd /prepare_buffers_get [ib [Hib _]].
  apply: initial_memory_component. by rewrite -Hd mem_domm Hib.
Qed.

(** Having a component memory at startup means being declared — the converse of
    `initial_memory_component`, and what turns a successful target load into the
    `gen_buffers` shape the tag lemmas want. *)
Lemma initial_mem_dom tp C cm :
  getm (Transitional.Memory.prepare_procedures_initial_memory tp) C = Some cm ->
  C \in domm (Intermediate.prog_interface tp).
Proof.
  rewrite /Transitional.Memory.prepare_procedures_initial_memory mapmE
          /Transitional.Memory.prepare_procedures_initial_memory_aux mkfmapfE.
  by case: ifP => [_|_] //=.
Qed.

Lemma initial_cwf tp C cm :
  getm (Transitional.Memory.prepare_procedures_initial_memory tp) C = Some cm ->
  TInject.cwf cm.
Proof.
  rewrite /Transitional.Memory.prepare_procedures_initial_memory mapmE
          /Transitional.Memory.prepare_procedures_initial_memory_aux mkfmapfE.
  case: ifP => [_|_] //=. move=> [<-].
  rewrite /Transitional.Memory.reserve_component_blocks /=.
  case E: (Transitional.Memory.reserve_blocks _ _) => [Cmem' bs] /=.
  have Ec : Cmem' = (Transitional.Memory.reserve_blocks
                       (Transitional.Memory.prealloc
                          (mapm (fun a => (C, a))
                             (odflt emptym (Intermediate.prog_buffers tp C))))
                       (length (elementsm (odflt emptym
                          (Intermediate.prog_procedures tp C))))).1
    by rewrite E.
  rewrite Ec. apply: cwf_reserve_blocks. exact: cwf_prealloc.
Qed.

(* ================================================================== *)
(* Nothing is a capability at startup                                  *)
(* ================================================================== *)

(** `initial_block0_data` generalised off block 0 — and it needs NO premise at
    all. `prealloc`'s `init_block` is `repeat tUndef` on one branch and
    `to_tagged_block`, i.e. `map (to_tvalue = MVal Other)`, on the other, so
    every cell it lays down is `Other` whatever block it sits in. *)
Lemma prealloc_all_other C bufs b i w :
  Transitional.Memory.load_b
    (Transitional.Memory.prealloc (mapm (fun a => (C, a)) bufs)) b i = Some w ->
  tvtag w.1 = Other.
Proof.
  rewrite /Transitional.Memory.load_b /Transitional.Memory.prealloc /= !mapmE.
  case Eb: (getm bufs b) => [ib|] //=.
  case: (0 <=? i)%Z => //.
  case: ib Eb => [sz|chunk] _.
  - by rewrite nth_error_repeat_if; case: (Z.to_nat i < sz) => // -[<-].
  - rewrite /Transitional.to_tagged_block nth_error_map_omap.
    by case: (List.nth_error chunk (Z.to_nat i)) => [v|] //= [<-].
Qed.

Lemma initial_all_other tp C b i w :
  Transitional.Memory.load
    (Transitional.Memory.prepare_procedures_initial_memory tp) (C, b, i)
  = Some w ->
  tvtag w.1 = Other.
Proof.
  rewrite /Transitional.Memory.load /=
          /Transitional.Memory.prepare_procedures_initial_memory mapmE
          /Transitional.Memory.prepare_procedures_initial_memory_aux mkfmapfE.
  case: ifP => [_|_] //=.
  rewrite /Transitional.Memory.reserve_component_blocks /=.
  case E: (Transitional.Memory.reserve_blocks _ _) => [Cmem' bs] /=.
  have Ec : Cmem' = (Transitional.Memory.reserve_blocks
                       (Transitional.Memory.prealloc
                          (mapm (fun a => (C, a))
                             (odflt emptym (Intermediate.prog_buffers tp C))))
                       (length (elementsm (odflt emptym
                          (Intermediate.prog_procedures tp C))))).1
    by rewrite E.
  rewrite Ec reserve_blocks_load.
  exact: prealloc_all_other.
Qed.

(** ★ The initial `tag_inv`, over the EMPTY ledger. Three of its seven fields
    are vacuous because the ledger is empty; the one with content is `ti_data`
    — "the only live capability cells are the ledger's" — which holds because
    at startup there are no live cells AT ALL. That is `initial_all_other`.

    The ledger is empty rather than `[:: (CReg, InternalJump)]` because
    `Register.init` puts junk in `R_RA`: main's activation is entered by the
    MACHINE, not by a caller, so there is no capability to record until the
    wrapper's own `IJal`. *)
Lemma initial_tag_inv tp :
  TInv.tag_inv [::] (Transitional.Memory.prepare_procedures_initial_memory tp)
               Transitional.Register.init (Level 0).
Proof.
  split.
  - by move=> r _; rewrite (init_regs_tag_val r).
  - by [].
  - by [].
  - move=> q t. rewrite /TMem.tload.
    case E: (Transitional.Memory.load _ q) => [w|] //= [Et] Hlive.
    move: Hlive. rewrite -Et.
    have -> : tvtag w.1 = Other.
    { case: q E => [[C0 b0] i0]; exact: initial_all_other. }
    by [].
  - exact: List.NoDup_nil.
  - by [].
  - exact: init_regs_dom.
Qed.

(* ================================================================== *)
(* ★ The initial memory injection                                      *)
(* ================================================================== *)

(** All ten fields at once. The three premises are the compiler's static
    guarantees, and nothing else is needed:

    - every source buffer is well formed (`wfprog_buffer_values`);
    - `gen_buffers` puts the source buffer at block 0 and the scratch/flag pair
      at block 1 of the corresponding target buffer map;
    - the source's buffer domain is the target's interface domain.

    Note where the WORK went: only `mj_load` and `mj_data` have content, and
    both were done above. Everything here is dispatch — four fields are vacuous
    at `init_renaming` because it maps `Block.local` and nothing else, and the
    remaining four are the shape lemmas just proved. *)
Lemma initial_minj p tp :
  (forall C ib, getm (Source.prog_buffers p) C = Some ib ->
     Source.well_formed_buffer C ib) ->
  (forall C ib, getm (Source.prog_buffers p) C = Some ib ->
     getm (Intermediate.prog_buffers tp) C
     = Some (mkfmap [:: (0, ib); (1, inr [:: Undef; Int 0])])) ->
  domm (Source.prog_buffers p) = domm (Intermediate.prog_interface tp) ->
  TInject.minj init_renaming (Source.prepare_buffers p)
    (Transitional.Memory.prepare_procedures_initial_memory tp).
Proof.
  move=> Hwfb Hgen Hd.
  (* the shape of a component that HAS a target memory, used three times *)
  have Hshape : forall C cm,
      getm (Transitional.Memory.prepare_procedures_initial_memory tp) C
      = Some cm ->
      exists ib, getm (Source.prog_buffers p) C = Some ib
        /\ getm (Intermediate.prog_buffers tp) C
           = Some (mkfmap [:: (0, ib); (1, inr [:: Undef; Int 0])]).
  { move=> C cm /initial_mem_dom. rewrite -Hd mem_domm.
    case E: (getm (Source.prog_buffers p) C) => [ib|] // _.
    by exists ib; split=> //; exact: Hgen. }
  split.
  - (* mj_ok *) exact: init_renaming_ok.
  - (* mj_load *)
    move=> C b b' i. rewrite /init_renaming.
    case Eb: (b == Block.local); last by [].
    move=> [<-]. move/eqP: Eb => ->.
    case E: (getm (Source.prog_buffers p) C) => [ib|].
    + apply: initial_mj_load.
      * exact: E.
      * exact: (Hwfb _ _ E).
      * exact: (Hgen _ _ E).
      * by rewrite -Hd mem_domm E.
    + (* undeclared: both memories miss the component *)
      have -> : Common.Memory.Memory.load (Source.prepare_buffers p)
                  (C, Block.local, i) = None
        by rewrite /Common.Memory.Memory.load /= /Source.prepare_buffers mapmE E.
      have HC : C \notin domm (Intermediate.prog_interface tp)
        by rewrite -Hd mem_domm E.
      have -> : TMem.vload
                  (Transitional.Memory.prepare_procedures_initial_memory tp)
                  (C, Block.local, i) = None.
      { rewrite /TMem.vload /Transitional.Memory.load /=
                /Transitional.Memory.prepare_procedures_initial_memory mapmE
                /Transitional.Memory.prepare_procedures_initial_memory_aux
                mkfmapfE.
        by move/negbTE: HC => ->. }
      by [].
  - (* mj_wf_t *) exact: initial_cwf.
  - (* mj_local_t *)
    move=> C cm Hcm. case: (Hshape _ _ Hcm) => [ib [_ Hbuf]].
    apply: (initial_local_t Hcm Hbuf). by rewrite mem_domm.
  - (* mj_rng — vacuous: [init_renaming] only maps [Block.local] *)
    move=> C b b'. rewrite /init_renaming.
    by case Eb: (b == Block.local).
  - (* mj_wf_s *) exact: initial_wf_s.
  - (* mj_local_s *) exact: initial_local_s.
  - (* mj_dom — vacuous for the same reason *)
    move=> C b b'. rewrite /init_renaming.
    by case Eb: (b == Block.local).
  - (* mj_domm *) move=> C cm. exact: initial_mj_domm.
  - (* mj_data *)
    move=> C b b' i w. rewrite /init_renaming.
    case Eb: (b == Block.local); last by [].
    move=> [<-] Hl.
    have Hcm : exists cm,
        getm (Transitional.Memory.prepare_procedures_initial_memory tp) C
        = Some cm.
    { move: Hl. rewrite /Transitional.Memory.load /=.
      case E: (getm (Transitional.Memory.prepare_procedures_initial_memory tp) C)
        => [cm|] //= _. by exists cm. }
    case: Hcm => [cm Hcm]. case: (Hshape _ _ Hcm) => [ib [_ Hbuf]].
    apply: (initial_block0_data Hbuf _ Hl). exact: initial_mem_dom Hcm.
Qed.

End TStatic.
