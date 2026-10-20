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

Notation icode := Intermediate.Machine.code.

Notation tmemory := Transitional.Memory.t.
Notation tregisters := Transitional.Register.t.

Section WithProgram.

Variable cde : Transitional.code.
Variable iface : Program.interface.
Variable labelsP : NMap (NMap label).

Definition ledger_at (t : value_tag) (Sl : seq TStack.ra_slot) : TInv.ledger :=
  (TInv.CReg, t) :: TStack.ledger_of Sl.

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
  ei_ra     : Transitional.Register.get R_RA tregs = MVal rtag (Ptr ret);
  ei_rtag   : rtag = InternalJump;
  ei_pc     : Pointer.component pc = C;
  ei_comp   : compile_expr C (lbp C) (scr C) plm e s1 = Some (c, s2);
  ei_code   : TMacros.code_at_I cde C pc (c ++ rest);
  ei_cont   : cont_matchJ a C plm k rest temps;
  ei_uniq   : forall C0, TDrain.labels_uniq cde C0;
  ei_priv   : frame_priv a C fb;
  ei_scrp   : scratch_priv a;
  ei_temps  : TStack.frame_temps tmem C fb temps;
  ei_cap    : TStack.frame_cap tmem C fb cap;
  ei_budget : 3 + maxn (size temps + stack_need e) (kneed k (size temps))
              <= cap;
  ei_prot   : (C, fb) \notin prot;
  ei_stack  : TSM.stack_match cde labelsP a tmem scrs C fb prot stk ret Sl;
  ei_tag    : TInv.tag_inv (ledger_at rtag Sl) tmem tregs pct;
  ei_anchor : main_anchored cde
}.

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


End WithProgram.

End TMatch.
