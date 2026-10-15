(** * Stage 4, part 5 — `expr_inv` / `val_inv`, retargeted.

    See plan-i2t-redo.md §2.3 and §4 (Stage 4).

    Ports of `S2I/Simulation.v:405-480`. Almost pure assembly: every field maps
    onto a piece built in Stage 4 parts 1-4.

    | `Simulation.v` field | here |
    |---|---|
    | `ei_mem : mem_inject α mem tmem` | `TInject.minj` |
    | `ei_scrs` / `ei_flag` / `ei_scr_all` | `TSM.scrs_ok` (one field, three clauses) |
    | `ei_code : code_at G pc (c ++ rest)` | `TMacros.code_at_I` |
    | `ei_temps` / `ei_cap` | `TStack.frame_temps` / `frame_cap` |
    | `ei_stack` | `TSM.stack_match` (chain instead of `gps`) |
    | `ei_one` / `ei_sp` / `ei_arg` | same, over tagged registers |
    | `ei_plm` / `ei_dom` / `ei_pc` / `ei_comp` / `ei_cont` / `ei_priv` / `ei_scrp` / `ei_budget` / `ei_prot` / `ei_uniq` / `ei_mainnf` | verbatim |

    Two fields are NEW, and they are the whole T-specific content:

    - **`ei_ra` (T1)** — `R_RA` holds the current activation's return address
      with its capability tag. This is what `Simulation.v` cannot state: at the
      I level `R_RA` is `Undef` and the return address exists nowhere.
    - **`ei_tag`** — `TInv.tag_inv` over the induced ledger
      `(CReg, τ) :: TStack.ledger_of Sl`, i.e. the current capability in the
      register plus the spilled chain. T2/T3/T4 all live inside it.

    Note the register fields are now equalities on TAGGED values
    (`MVal Other (Int 1)`, …). That is not cosmetic: `ei_one`/`ei_sp` carrying
    `Other` is exactly what `TS.BinOp` and `TS.Store` need as their tag
    premises, so the macros' side conditions come straight out of the
    invariant. *)

Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Source.Language.
Require Import Source.GlobalEnv.
Require Import Source.CS.
Require Import Intermediate.Machine.
Require Import S2I.CompMonad.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import S2I.SimInject.
Require Import S2I.Simulation.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.
Require Import S2T.TMem.
Require Import S2T.TInv.
Require Import S2T.TStack.
Require Import S2T.TInject.
Require Import S2T.TMacros.
Require Import S2T.TStackMatch.
Require Import S2T.TDrain.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Require Import Coq.ZArith.ZArith.

Set Implicit Arguments.
Unset Strict Implicit.

Module TMatch.

(* [code] is shadowed by [Transitional.code]; the Intermediate one is top-level
   in [Intermediate/Machine.v] (its [Register]/[program] live in an inner
   [Intermediate] module, but [code] does not). *)
Notation icode := Intermediate.Machine.code.

Notation tmemory := Transitional.Memory.t.
Notation tregisters := Transitional.Register.t.

Section WithProgram.

(* the T-level code, the source program's interface, and the label map — the
   three things `Simulation.v` gets from its section variables `G` / `tp` *)
Variable cde : Transitional.code.
Variable iface : Program.interface.
Variable labelsP : NMap (NMap label).

(** The ledger a state induces: the current capability in [R_RA], then the
    spilled chain. *)
Definition ledger_at (t : value_tag) (Sl : seq TStack.ra_slot) : TInv.ledger :=
  (TInv.CReg, t) :: TStack.ledger_of Sl.

(** ★ MAIN's WRAPPER SITS RIGHT AFTER MAIN's HEADER.

    A pure fact about the compiled code, carried by the invariant because it is
    a REACHABILITY fact in disguise. `compile_proc` prefixes main's code with a
    HALT PAD when main's body is `immediately_final`, and then the cell one past
    main's header is an `IHalt` — neither wrapper shape. That makes `entry_ext`
    at `(main, main)` false as a static predicate.

    It is harmless for the simulation: an immediately-final main means the
    SOURCE's initial state is already final, so the program stops before any
    other component runs and no cross-component call to `main` can occur. But
    that argument is invisible to a static predicate, so the invariant carries
    its consequence instead — and being in a state that satisfies the invariant
    at all is exactly the evidence that the machine got past the pad. *)
Definition main_anchored (cde : Transitional.code) : Prop :=
  exists pcWm tlm,
    Transitional.find_plabel_in_code cde Component.main Procedure.main
      = Some pcWm
    /\ TMacros.code_at_I cde Component.main (Pointer.inc pcWm)
         (IConst (IInt 1) R_ONE :: tlm).

Record expr_inv (a : renaming) (scrs : NMap value) (C : Component.id)
       (stk : S.CS.stack) (mem : Common.Memory.Memory.t) (k : cont) (e : expr) (arg : value)
       (ret : Pointer.t) (rtag : value_tag) (Sl : seq TStack.ra_slot)
       (tmem : tmemory) (tregs : tregisters) (pct : pc_tag)
       (pc : Pointer.t) (fb : Block.id)
       (prot : seq (Component.id * Block.id)) (temps : seq value)
       (plm : NMap label) (c rest : icode)
       (s1 s2 : comp_env) (cap : nat)
  : Prop := ExprInv {
  ei_plm    : getm labelsP C = Some plm;
  ei_dom    : C \in domm iface;
  ei_mem    : TInject.minj a mem tmem;
  ei_scrs   : TSM.scrs_ok tmem iface scrs;
  ei_one    : Transitional.Register.get R_ONE tregs = MVal Other (Int 1);
  ei_sp     : Transitional.Register.get R_SP tregs
              = MVal Other (Ptr (C, fb, Z.of_nat (2 + size temps)));
  ei_arg    : val_inject a arg
                (Transitional.val (Transitional.Register.get R_ARG tregs));
  (* T1 — the field `Simulation.v` cannot state *)
  ei_ra     : Transitional.Register.get R_RA tregs = MVal rtag (Ptr ret);
  (* ★ a procedure BODY is always entered by the wrapper's [IJal], so its
     capability is an [InternalJump] — the [Ret n] of a cross-component call is
     spilled in the WRAPPER's frame, never held by the body. Recorded as a
     field rather than by specialising the parameter, so the diagrams that do
     not care are untouched. *)
  ei_rtag   : rtag = InternalJump;
  ei_pc     : Pointer.component pc = C;
  ei_comp   : compile_expr C (lbp C) (scr C) plm e s1 = Some (c, s2);
  ei_code   : TMacros.code_at_I cde C pc (c ++ rest);
  ei_cont   : cont_matchJ a C plm k rest temps;
  (* component-wide label uniqueness — what `TDrain.cont_matchJ_drain` consumes.
     `Simulation.v`'s `ei_uniq` is the per-procedure version; T resolves labels
     over the whole component array, so this is the form it needs. *)
  ei_uniq   : forall C0, TDrain.labels_uniq cde C0;
  ei_priv   : frame_priv a C fb;
  ei_scrp   : scratch_priv a;
  ei_temps  : TStack.frame_temps tmem C fb temps;
  ei_cap    : TStack.frame_cap tmem C fb cap;
  ei_budget : 3 + maxn (size temps + stack_need e) (kneed k (size temps))
              <= cap;
  ei_prot   : (C, fb) \notin prot;
  ei_stack  : TSM.stack_match cde labelsP a tmem scrs C fb prot stk ret Sl;
  (* T2 / T3 / T4 *)
  ei_tag    : TInv.tag_inv (ledger_at rtag Sl) tmem tregs pct;
  ei_anchor : main_anchored cde
}.

(** [val_inv]: the value is already in [R_COM] and the pc sits on the
    continuation's code. Same fields minus [ei_comp], with [ei_code] on [rest]
    alone, plus [vi_com]. *)
Record val_inv (a : renaming) (scrs : NMap value) (C : Component.id)
       (stk : S.CS.stack) (mem : Common.Memory.Memory.t) (k : cont) (v : value) (arg : value)
       (ret : Pointer.t) (rtag : value_tag) (Sl : seq TStack.ra_slot)
       (tmem : tmemory) (tregs : tregisters) (pct : pc_tag)
       (pc : Pointer.t) (fb : Block.id)
       (prot : seq (Component.id * Block.id)) (temps : seq value)
       (plm : NMap label) (rest : icode) (cap : nat)
  : Prop := ValInv {
  vi_plm    : getm labelsP C = Some plm;
  vi_dom    : C \in domm iface;
  vi_mem    : TInject.minj a mem tmem;
  vi_scrs   : TSM.scrs_ok tmem iface scrs;
  vi_one    : Transitional.Register.get R_ONE tregs = MVal Other (Int 1);
  vi_sp     : Transitional.Register.get R_SP tregs
              = MVal Other (Ptr (C, fb, Z.of_nat (2 + size temps)));
  vi_arg    : val_inject a arg
                (Transitional.val (Transitional.Register.get R_ARG tregs));
  vi_com    : val_inject a v
                (Transitional.val (Transitional.Register.get R_COM tregs));
  vi_ra     : Transitional.Register.get R_RA tregs = MVal rtag (Ptr ret);
  vi_rtag   : rtag = InternalJump;
  vi_pc     : Pointer.component pc = C;
  vi_code   : TMacros.code_at_I cde C pc rest;
  vi_cont   : cont_matchJ a C plm k rest temps;
  vi_uniq   : forall C0, TDrain.labels_uniq cde C0;
  vi_priv   : frame_priv a C fb;
  vi_scrp   : scratch_priv a;
  vi_temps  : TStack.frame_temps tmem C fb temps;
  vi_cap    : TStack.frame_cap tmem C fb cap;
  vi_budget : 3 + kneed k (size temps) <= cap;
  vi_prot   : (C, fb) \notin prot;
  vi_stack  : TSM.stack_match cde labelsP a tmem scrs C fb prot stk ret Sl;
  vi_tag    : TInv.tag_inv (ledger_at rtag Sl) tmem tregs pct;
  vi_anchor : main_anchored cde
}.

(* ================================================================== *)
(* What the invariant hands the macros                                *)
(* ================================================================== *)

End WithProgram.

End TMatch.
