(** * T2M — instantiating the simulation for COMPILED pairs.

    Discharges MStar's section context (size/wf premises, label/procedure
    and code-shape statics) for a linked pair of S2I outputs, and assembles
    [t2me_fwd_assembled]/[t2me_bwd_assembled] from [t2me_premises] + [run_fits]. *)

Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Values.
Require Import Common.Maps.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div fintype ssrint seq path.
From mathcomp Require Import ssralg intdiv zify.
From CoqUtils Require Import hseq word.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.WordExtra.
Require Import MicroPolicies.Int32.
Require Import MicroPolicies.Instance.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Symbolic.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Merged.
Require Import MicroPolicies.Recomposition.OffsetWord.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.EncodeCode.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import MicroPolicies.Recomposition.RSCDefs.
Require Import S2I.CompMonad.
Require Import S2I.Definitions.
Require Import S2I.Compiler.
Require Import S2I.LabelUniq.
Require Import Source.Language.
Require Import S2T.TSem.
Require Import S2T.TSim.
Require Import Common.Linking.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.CompCertExtensions.

Require Import T2M.MPos.
Require Import T2M.MPosT.
Require Import T2M.MMem.
Require Import T2M.MMemBase.
Require Import T2M.MInj.
Require Import T2M.MMatch.
Require Import T2M.MStep.
Require Import T2M.MAlloc.
Require Import T2M.MHeap.
Require Import T2M.MInit.
Require Import T2M.MStar.
Require Import T2M.MFlip.
Require Import T2M.MWalk.
Require Import T2M.MSig.
Require T2M.MDisc.
Require Import T2M.MSync.
Require T2M.MDefs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section Discharge.

Variables L P C : nat.
Variables a b : Intermediate.program.

Local Notation PB := (MDefs.PBw a b).
Local Notation PI := (MDefs.PIw a b).
Local Notation tp := (Intermediate.program_link a b).
Local Notation cdeW :=
  (Transitional.intermediate_to_transitional_gen PI tp).
Local Notation codeW :=
  (compiler_code L P C PB PI a ++ compiler_code L P C PB PI b).
Local Notation pc0 := (size (initial_memory (mt := mt) PB)).
Local Notation Wme :=
  (Definitions.program_link (compiler L P C PB PI a)
                            (compiler L P C PB PI b)).

Variable Hprem : MDefs.t2me_premises L P C a b.

(* ---- the pieces of the bundle ---- *)

Lemma disch_Hwfa : Intermediate.well_formed_program a.
Proof. by case: Hprem => -[_ _ ? _ _] _. Qed.

Lemma disch_Hwfb : Intermediate.well_formed_program b.
Proof. by case: Hprem => -[_ _ _ ? _] _. Qed.

Lemma disch_Hlinkable :
  linkable (Intermediate.prog_interface a) (Intermediate.prog_interface b).
Proof. by case: Hprem => -[_ _ _ _ ?] _. Qed.

Lemma disch_HPB :
  PB = Intermediate.prog_buffers (Intermediate.program_link a b).
Proof. by []. Qed.

Lemma disch_HNCws : MDefs.NC <= word_size mt.
Proof. by rewrite word_size_mt. Qed.

Lemma disch_HNCal : Merged.alloc_label < 2 ^ (word_size mt - MDefs.NC).
Proof.
rewrite /Merged.alloc_label word_size_mt /MDefs.NC.
by rewrite ltn_exp2l.
Qed.

(* ---- OBLIGATION: the size premises from [link_fits] ---- *)

Lemma disch_Hsmall :
  size (linearize_bufs PB) + size codeW < Merged.alloc_label.
Proof.
case: Hprem => _ [_ [_ _ Hlf]].
by case: Hlf => Hsz _.
Qed.

Lemma disch_Hbound : pc0 + size codeW < 2 ^ word_size mt.
Proof.
have Hsz := disch_Hsmall.
have Hal32 : Merged.alloc_label < 2 ^ word_size mt.
{ rewrite /Merged.alloc_label word_size_mt. by rewrite ltn_exp2l. }
have Hlin32 : size (linearize_bufs PB) < 2 ^ word_size mt by lia.
have Hpc0E : size (initial_memory (mt := mt) PB)
             = size (linearize_bufs PB)
  := initial_memory_size_eq Hlin32.
by lia.
Qed.

(* the T code's domain is the linked procedure map's *)
Lemma unzip1_cclg (T : Type) (PI' : Program.interface)
    (cenv : Intermediate.program) (l : list (Component.id * T)) :
  unzip1 (Transitional.compile_component_list_gen PI' cenv l) = unzip1 l.
Proof.
elim: l => [|[c ?] l IH] //=.
by rewrite IH.
Qed.

Lemma cdeW_domm (c : Component.id)
    (C_code : seq (Transitional.instr * mem_tag)) :
  cdeW c = Some C_code ->
  c \in domm (Intermediate.prog_procedures tp).
Proof.
move=> Hc.
have Hin : c \in domm cdeW by rewrite mem_domm Hc.
move: Hin.
rewrite /Transitional.intermediate_to_transitional_gen domm_mkfmap
        unzip1_cclg.
rewrite mem_domm /Maps.elementsm.
case: (Intermediate.prog_procedures tp) => str Ps /=.
rewrite /getm /=.
elim: str {Ps} => [|[k v] str IH] //=.
rewrite inE => /orP[/eqP ->|Hin].
- by rewrite eqxx.
- case: (c == k) => //. exact: IH.
Qed.

(* ---- OBLIGATION: the immediate fits from [t2m_ok] ---- *)

Lemma disch_Himm_a : MDefs.imm_fits a.
Proof. by case: Hprem => _ [_ [[_ _ ?] _ _]]. Qed.

Lemma disch_Himm_b : MDefs.imm_fits b.
Proof. by case: Hprem => _ [_ [_ [_ _ ?] _]]. Qed.

(* ---- the label/procedure/component bounds from [lin_ok_at] ---- *)

Lemma disch_Hlab_a : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures a cid = Some Cprocs ->
  Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Proof.
case: Hprem => _ [_ [[Hlin _ _] _ _]].
by case: Hlin => _ _ ? _ _.
Qed.

Lemma disch_Hlab_b : forall cid Cprocs Pid Pcode l0,
  Intermediate.prog_procedures b cid = Some Cprocs ->
  Cprocs Pid = Some Pcode -> List.In (ILabel l0) Pcode -> l0 < L.
Proof.
case: Hprem => _ [_ [_ [Hlin _ _] _]].
by case: Hlin => _ _ ? _ _.
Qed.

Lemma disch_Hcomp_a : forall cid,
  cid \in domm (Intermediate.prog_procedures a) -> cid < C.
Proof.
case: Hprem => _ [_ [[Hlin _ _] _ _]].
case: Hlin => _ _ _ _ Hcomp cid Hin.
apply: Hcomp.
by rewrite (Intermediate.wfprog_defined_procedures disch_Hwfa).
Qed.

Lemma disch_Hcomp_b : forall cid,
  cid \in domm (Intermediate.prog_procedures b) -> cid < C.
Proof.
case: Hprem => _ [_ [_ [Hlin _ _] _]].
case: Hlin => _ _ _ _ Hcomp cid Hin.
apply: Hcomp.
by rewrite (Intermediate.wfprog_defined_procedures disch_Hwfb).
Qed.

Lemma disch_Hproc_a : forall cid Cprocs Pid,
  Intermediate.prog_procedures a cid = Some Cprocs ->
  Pid \in domm Cprocs -> Pid < P.
Proof.
case: Hprem => _ [_ [[Hlin _ _] _ _]].
by case: Hlin => _ _ _ ? _.
Qed.

Lemma disch_Hproc_b : forall cid Cprocs Pid,
  Intermediate.prog_procedures b cid = Some Cprocs ->
  Pid \in domm Cprocs -> Pid < P.
Proof.
case: Hprem => _ [_ [_ [Hlin _ _] _]].
by case: Hlin => _ _ _ ? _.
Qed.

(* ---- OBLIGATION: label uniqueness of S2I output ---- *)

Lemma disch_Huniq_a : forall cid l0 Cprocs0,
  Intermediate.prog_procedures a cid = Some Cprocs0 ->
  sumn [seq count (ilab l0) (odflt [::] (Cprocs0 p')) | p' <- domm Cprocs0]
  <= 1.
Proof.
move=> cid l0 Cprocs0 Hc.
case: Hprem => -[[sa [_ Hca]] _ _ _ _] _.
exact: (compiled_labels_unique Hca _ Hc).
Qed.

Lemma disch_Huniq_b : forall cid l0 Cprocs0,
  Intermediate.prog_procedures b cid = Some Cprocs0 ->
  sumn [seq count (ilab l0) (odflt [::] (Cprocs0 p')) | p' <- domm Cprocs0]
  <= 1.
Proof.
move=> cid l0 Cprocs0 Hc.
case: Hprem => -[_ [sb [_ Hcb]] _ _ _] _.
exact: (compiled_labels_unique Hcb _ Hc).
Qed.

(* ---- the provenance backbone ---- *)

(* the linked T code's per-component segment IS the linearizer's *)
Lemma cdeW_code (c : Component.id)
    (C_code : seq (Transitional.instr * mem_tag)) :
  cdeW c = Some C_code ->
  C_code = Transitional.linearize_component_gen PI tp c.
Proof.
rewrite /Transitional.intermediate_to_transitional_gen.
elim: (Maps.elementsm (Intermediate.prog_procedures tp))
  => [|[k t] l IH] //=.
rewrite setmE.
case: (altP (c =P k)) => [->|_].
- by move=> [<-].
- exact: IH.
Qed.

(* every cell of a component's segment is a procedure HEADER or the
   translation of a body instruction *)
Lemma In_flatten_map (A B : Type) (f : A -> seq B) (l : seq A) (y : B) :
  List.In y (flatten (map f l)) ->
  exists x, List.In x l /\ List.In y (f x).
Proof.
elim: l => [|x0 l IH] //= Hy.
case: (List.in_app_or _ _ _ Hy) => [Hy'|Hy'].
- by exists x0; split; [left|].
- have [x [Hx Hy'']] := IH Hy'.
  by exists x; split; [right|].
Qed.

Lemma In_in (T : eqType) (x : T) (s : seq T) : List.In x s -> x \in s.
Proof.
elim: s => [|y s IH] //= [Exy|Hin].
- by rewrite Exy inE eqxx.
- by rewrite inE (IH Hin) orbT.
Qed.

Lemma lin_In_inv (c : Component.id) (i : Transitional.instr)
    (tg : mem_tag) :
  List.In (i, tg) (Transitional.linearize_component_gen PI tp c) ->
  (exists Cprocs p,
     [/\ Intermediate.prog_procedures tp c = Some Cprocs,
         p \in domm Cprocs
       & (i, tg) = (TrLabel (inr (c, p)),
                    Transitional.head_tag_gen PI c p)])
  \/ (exists Cprocs p Pcode i0,
        [/\ Intermediate.prog_procedures tp c = Some Cprocs,
            Cprocs p = Some Pcode,
            List.In i0 Pcode
          & Transitional.instr_to_transitional c i0 = (i, tg)]).
Proof.
rewrite /Transitional.linearize_component_gen.
case Hc: (getm (Intermediate.prog_procedures tp) c) => [Cprocs|] /=;
  last by [].
move=> Hin.
have [p [Hp Hyp]] := In_flatten_map Hin.
have Hpdom : p \in domm Cprocs := In_in Hp.
move: Hyp. rewrite /Transitional.linearize_proc_gen Hc /=.
case Hpc: (getm Cprocs p) => [Pcode|] /=.
- case=> [E|Hbody].
  + left. exists Cprocs, p. by split=> //; rewrite ?E.
  + right.
    move: Hbody => /List.in_map_iff [i0 [Hi0 Hin0]].
    exists Cprocs, p, Pcode, i0.
    by split.
- case=> [E|//].
  left. exists Cprocs, p. by split=> //; rewrite ?E.
Qed.

(* a linked procedure map entry comes from one side *)
Lemma procs_side (c : Component.id) (Cprocs : NMap Machine.code) :
  Intermediate.prog_procedures tp c = Some Cprocs ->
  Intermediate.prog_procedures a c = Some Cprocs \/
  Intermediate.prog_procedures b c = Some Cprocs.
Proof.
rewrite /Intermediate.program_link /= unionmE.
case E: (Intermediate.prog_procedures a c) => [v|] /=.
- move=> [<-]. by left.
- move=> ?. by right.
Qed.

(* [executing] lands inside the component's segment *)
Lemma executing_In (tpc : Pointer.t) (i : Transitional.instr)
    (tg : mem_tag) (c : Component.id) :
  Transitional.executing cdeW tpc i tg c ->
  List.In (i, tg) (Transitional.linearize_component_gen PI tp c).
Proof.
case=> C_code [Ec [Hcde [_ Hnth]]].
rewrite -(cdeW_code Hcde).
exact: List.nth_error_In Hnth.
Qed.

(* ---- no self-mov in S2I output: the boolean walk ---- *)

Definition selfmov (i0 : Machine.instr) : bool :=
  if i0 is IMov r1 r2
  then Nat.eqb (Intermediate.Register.to_nat r1)
               (Intermediate.Register.to_nat r2)
  else false.

Lemma compile_expr_movok (C0 : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (e : expr) :
  forall (s : comp_env) (c : Machine.code) (s' : comp_env),
  compile_expr C0 lbp scr P_labels e s = Some (c, s') ->
  ~~ has selfmov c.
Proof.
elim: e => [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
           |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc.
- by case: v Hc => [i|p|] //= [<- _].
- by move: Hc => /= [<- _].
- by move: Hc => /= [<- _].
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C0 lbp scr P_labels e2 s1) => [[c2 s2]|] //=.
  move=> [<- _].
  by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /= (negbTE (IH1 _ _ _ E1))
     (negbTE (IH2 _ _ _ E2)).
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C0 lbp scr P_labels e2 s1) => [[c2 s2]|] //=.
  move=> [<- _].
  by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /= (negbTE (IH1 _ _ _ E1)) (negbTE (IH2 _ _ _ E2)).
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C0 lbp scr P_labels e2 s1) => [[c2 s2]|] //=.
  case E3: (compile_expr C0 lbp scr P_labels e3 s2) => [[c3 s3]|] //=.
  case E4: (fresh_label C0 s3) => [[lconseq s4]|] //=.
  case E5: (fresh_label C0 s4) => [[lend s5]|] //=.
  move=> [<- _].
  by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /= (negbTE (IH1 _ _ _ E1)) (negbTE (IH2 _ _ _ E2))
     (negbTE (IH3 _ _ _ E3)).
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e s) => [[c1 s1]|] //=.
  move=> [<- _].
  by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /= (negbTE (IH _ _ _ E1)).
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e s) => [[c1 s1]|] //=.
  move=> [<- _].
  by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /= (negbTE (IH _ _ _ E1)).
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C0 lbp scr P_labels e2 s1) => [[c2 s2]|] //=.
  move=> [<- _].
  by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /= (negbTE (IH1 _ _ _ E1)) (negbTE (IH2 _ _ _ E2)).
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e s) => [[c1 s1]|] //=.
  case: (Component.eqb C' C0).
  + case E2: (find_proc_label P_labels P' s1) => [[tl s2]|] //=.
    move=> [<- _].
    by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /= (negbTE (IH _ _ _ E1)).
  + move=> [<- _].
    by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /= (negbTE (IH _ _ _ E1)).
- by move: Hc => /= [<- _].
Qed.

Lemma compile_proc_movok (C0 : Component.id) (lbp scr : Pointer.t)
    (P_labels : NMap label) (P0 : Procedure.id) (e : expr) :
  forall (s : comp_env) (c : Machine.code) (s' : comp_env),
  compile_proc C0 lbp scr P_labels P0 e s = Some (c, s') ->
  ~~ has selfmov c.
Proof.
move=> s c s' Hc.
move: Hc; rewrite /compile_proc.
cbv beta iota delta [Monads.bind Monads.ret compilation_monad
  CompMonad.Comp.bind CompMonad.Comp.ret].
case E0: (find_proc_label P_labels P0 s) => [[pl s0]|] //=.
case E1: (fresh_label C0 s0) => [[lmain s1]|] //=.
case E2: (fresh_label C0 s1) => [[lreturn s2]|] //=.
case E3: (compile_expr C0 lbp scr P_labels e s2) => [[pc0 s3]|] //=.
case: (Component.eqb C0 Component.main
       && Procedure.eqb P0 Procedure.main) => /=;
case: (immediately_final e) => /=;
move=> [<- _];
by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
   ?has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
   (negbTE (compile_expr_movok E3)).
Qed.

Lemma disch_Hself : forall tpc r1 r2 tg c,
  Transitional.executing cdeW tpc (TrMov r1 r2) tg c -> r1 <> r2.
Proof.
move=> tpc r1 r2 tg c Hex Er. subst r2.
have Hin := executing_In Hex.
case: (lin_In_inv Hin)
  => [[Cprocs [p [_ _ E]]]|[Cprocs [p [Pcode [i0 [Hp1 Hp2 Hp3 Ht]]]]]].
- by have /= EI := congr1 fst E; inversion EI.
-
  have Ei0 : i0 = IMov r1 r1.
  { case: i0 Ht {Hp3} =>
      [|l0|v0 r0|ra' rb'|op0 ra' rb' rc'|ra' rb'|ra' rb'|ra' rb'
       |r0 l0| |l0|c0' P0| |] //= Ht.
    - by case: Ht => -> ->.
    - by have /= EI := congr1 fst Ht; rewrite if_same in EI; inversion EI. }
  subst i0.
  have Hsm : selfmov (IMov r1 r1) by rewrite /= Nat.eqb_refl.
  have In_has : forall (A : Type) (pr : A -> bool) (x : A) (s0 : seq A),
      List.In x s0 -> pr x -> has pr s0.
  { move=> A pr x s0. elim: s0 => [|y s0 IH] //= [->|Hin0] Hp.
    - by rewrite Hp.
    - by rewrite (IH Hin0 Hp) orbT. }
  have Hhas : has selfmov Pcode := In_has _ _ _ _ Hp3 Hsm.
  case: (procs_side Hp1) => [Ha'|Hb'].
  + case: Hprem => -[[sa [_ Hca]] _ _ _ _] _.
    case: (compiled_proc_origin Hca Ha' Hp2)
      => [[plm [e0 [s0 [s1 Hcp]]]]|[lab Ecd]].
    * by rewrite (negbTE (compile_proc_movok Hcp)) in Hhas.
    * by rewrite Ecd /= in Hhas.
  + case: Hprem => -[_ [sb [_ Hcb]] _ _ _] _.
    case: (compiled_proc_origin Hcb Hb' Hp2)
      => [[plm [e0 [s0 [s1 Hcp]]]]|[lab Ecd]].
    * by rewrite (negbTE (compile_proc_movok Hcp)) in Hhas.
    * by rewrite Ecd /= in Hhas.
Qed.

(* ---- no mov FROM R_RA ---- *)

Definition ramov (i0 : Machine.instr) : bool :=
  if i0 is IMov r1 _
  then Nat.eqb (Intermediate.Register.to_nat r1)
               (Intermediate.Register.to_nat Machine.R_RA)
  else false.

(* ---- the R_RA flow is SP-mediated (push/pop only) ---- *)

Definition rabad (i0 : Machine.instr) : bool :=
  match i0 with
  | IStore r1 r2 =>
      Nat.eqb (Intermediate.Register.to_nat r2)
              (Intermediate.Register.to_nat Machine.R_RA)
      && negb (Nat.eqb (Intermediate.Register.to_nat r1)
                       (Intermediate.Register.to_nat Machine.R_SP))
  | ILoad r1 r2 =>
      Nat.eqb (Intermediate.Register.to_nat r2)
              (Intermediate.Register.to_nat Machine.R_RA)
      && negb (Nat.eqb (Intermediate.Register.to_nat r1)
                       (Intermediate.Register.to_nat Machine.R_SP))
  | _ => false
  end.

Lemma disch_Hjra : forall tpc r tg c,
  Transitional.executing cdeW tpc (TrJump r) tg c -> r = R_RA.
Proof.
move=> tpc r tg c Hex.
have Hin := executing_In Hex.
case: (lin_In_inv Hin)
  => [[Cprocs [p [_ _ E]]]|[Cprocs [p [Pcode [i0 [Hd1 Hd2 Hd3 Ht]]]]]].
- by [].
- case: i0 Ht {Hd1 Hd2 Hd3}
    => [|l0|v0 r0|r1 r2|op0 r1 r2 r3|r1 r2|r1 r2|r1 r2|r0 l0| |l0|c0' P0| |]
       //= Ht.
  all: have /= EI := congr1 fst Ht.
  all: rewrite ?if_same /= in EI.
  all: try by inversion EI.
  all: inversion EI; subst; reflexivity.
Qed.

(* ---- positional flatten machinery for the forward-branch static ---- *)

Lemma nth_flatten_inv (A : Type) (ll : seq (seq A)) (o : nat) (x : A) :
  List.nth_error (flatten ll) o = Some x ->
  exists n1 seg k,
    [/\ List.nth_error ll n1 = Some seg,
        List.nth_error seg k = Some x,
        o = sumn [seq size s0 | s0 <- take n1 ll] + k
      & k < size seg].
Proof.
elim: ll o => [|seg ll IH] o /=; first by case: o.
case: (ltnP o (size seg)) => [Hlt|Hge] Hnth.
- have Hlt' : (o < length seg)%coq_nat by apply/ltP.
  have Ha1 : List.nth_error (seg ++ flatten ll) o = List.nth_error seg o
    := List.nth_error_app1 seg (flatten ll) Hlt'.
  exists 0, seg, o.
  split=> //.
  by rewrite -Ha1.
- have Hge' : (length seg <= o)%coq_nat by apply/leP.
  have Ha1 : List.nth_error (seg ++ flatten ll) o
             = List.nth_error (flatten ll) (o - length seg)%coq_nat
    := List.nth_error_app2 seg (flatten ll) Hge'.
  have Hnth2 : List.nth_error (flatten ll) (o - size seg) = Some x.
  { have H2 : List.nth_error (flatten ll) (o - length seg)%coq_nat
              = Some x := eq_trans (esym Ha1) Hnth.
    exact: H2. }
  have [n1 [seg' [k [H1 H2 H3 H4]]]] := IH _ Hnth2.
  exists n1.+1, seg', k.
  split=> //=.
  by lia.
Qed.

(* at most one position satisfies a count-1-bounded predicate *)
Lemma count_pos_le1 (A : Type) (pr : A -> bool) (s : seq A)
    (k : nat) (x : A) :
  List.nth_error s k = Some x -> pr x -> 0 < count pr s.
Proof.
elim: s k => [|y s IH] [|k] //=.
- move=> [<-] ->. by lia.
- move=> Hk Hp.
  have := IH _ Hk Hp. by case: (pr y) => /=; lia.
Qed.

Lemma count_pos_uniq (A : Type) (pr : A -> bool) (s : seq A)
    (k1 k2 : nat) (x1 x2 : A) :
  count pr s <= 1 ->
  List.nth_error s k1 = Some x1 -> pr x1 ->
  List.nth_error s k2 = Some x2 -> pr x2 ->
  k1 = k2.
Proof.
elim: s k1 k2 => [|y s IH] [|k1] [|k2] //= Hc H1 P1 H2 P2.
- exfalso.
  case: H1 => E. subst y.
  have Hc2 := count_pos_le1 H2 P2.
  rewrite P1 /= in Hc. by lia.
- exfalso.
  case: H2 => E. subst y.
  have Hc1 := count_pos_le1 H1 P1.
  rewrite P2 /= in Hc. by lia.
- have Hc' : count pr s <= 1 by case: (pr y) Hc => /=; lia.
  by rewrite (IH _ _ Hc' H1 P1 H2 P2).
Qed.

(* a sum over a uniq seq with two distinct >=1 contributors is >= 2 *)
Lemma sumn_mem_le (T : eqType) (f : T -> nat) (s : seq T) (x : T) :
  x \in s -> f x <= sumn [seq f y | y <- s].
Proof.
elim: s => [|y s IH] //=.
rewrite inE => /orP[/eqP ->|Hx]; first by lia.
have := IH Hx. by lia.
Qed.

Lemma sumn_two (T : eqType) (f : T -> nat) (s : seq T) (p q : T) :
  uniq s -> p \in s -> q \in s -> p != q ->
  1 <= f p -> 1 <= f q -> 2 <= sumn [seq f y | y <- s].
Proof.
elim: s => [|y s IH] //= /andP[Hy Hu].
rewrite !inE => /orP[/eqP Ep|Hp] /orP[/eqP Eq|Hq] Hne Hfp Hfq.
- exfalso. subst. by rewrite eqxx in Hne.
- subst y. have := sumn_mem_le f Hq. by lia.
- subst y. have := sumn_mem_le f Hp. by lia.
- have := IH Hu Hp Hq Hne Hfp Hfq. by lia.
Qed.

Lemma disch_Hbf : forall tpc r l tg c pc',
  Transitional.executing cdeW tpc (TrBnz r l) tg c ->
  Transitional.find_label_in_comp cdeW c l = Some pc' ->
  BinInt.Z.le (Pointer.offset tpc) (Pointer.offset pc').
Proof.
move=> tpc r l tg c pc' Hex Hfind.
case: Hex => C_code [Ec [Hcde [Hoff Hnth]]].
have [cseg [xt [Hc2 Epc' Hoff' Hnth']]]
  := find_label_in_comp_nth disch_Hbound disch_Hsmall Hfind.
move: Hc2; rewrite Hcde => -[E2]. subst cseg.
have Hcc := cdeW_code Hcde.
rewrite Hcc in Hnth Hnth'.
move: Hnth Hnth'. rewrite /Transitional.linearize_component_gen.
case Hc: (getm (Intermediate.prog_procedures tp) c) => [Cprocs|];
  last first.
{ have Hd := cdeW_domm Hcde. by rewrite mem_domm Hc in Hd. }
rewrite /=.
move=> Hnth Hnth'.
have [n1 [seg1 [k1 [Hll1 Hseg1 Ho1 Hk1]]]] := nth_flatten_inv Hnth.
have [n2 [seg2 [k2 [Hll2 Hseg2 Ho2 Hk2]]]] := nth_flatten_inv Hnth'.
have HmE1 : List.nth_error
              (map (Transitional.linearize_proc_gen PI tp c)
                 (domm Cprocs)) n1
            = option_map (Transitional.linearize_proc_gen PI tp c)
                (List.nth_error (domm Cprocs) n1)
  := List.nth_error_map _ _ _.
have HmE2 : List.nth_error
              (map (Transitional.linearize_proc_gen PI tp c)
                 (domm Cprocs)) n2
            = option_map (Transitional.linearize_proc_gen PI tp c)
                (List.nth_error (domm Cprocs) n2)
  := List.nth_error_map _ _ _.
rewrite HmE1 in Hll1. rewrite HmE2 in Hll2.
case Ep1: (List.nth_error (domm Cprocs) n1) Hll1 => [p1|] //= [Eseg1].
case Ep2: (List.nth_error (domm Cprocs) n2) Hll2 => [p2|] //= [Eseg2].
move: Hseg1. rewrite -Eseg1 /Transitional.linearize_proc_gen Hc /=.
case Hpc1: (getm Cprocs p1) => [Pcode1|] /=; last first.
{
  case: k1 Hk1 {Ho1} => [|k1] /= Hk1.
  - by move=> [E _]; inversion E.
  - move=> Hn.
    have Hlt : (k1 < length (@nil (Transitional.instr * mem_tag)))%coq_nat.
    { apply/(proj1 (List.nth_error_Some _ _)). by rewrite Hn. }
    move: Hlt => /= Hlt. by lia. }
case: k1 Hk1 Ho1 => [|m1] /= Hk1 Ho1.
{ by move=> [E _]; inversion E. }
move=> Hb1.
have [i1 [Hi1 Ei1]] : exists i1,
    List.nth_error Pcode1 m1 = Some i1 /\
    Transitional.instr_to_transitional c i1 = (TrBnz r l, tg).
{ move: Hb1.
  have HmB : List.nth_error
               (map (Transitional.instr_to_transitional c) Pcode1) m1
             = option_map (Transitional.instr_to_transitional c)
                 (List.nth_error Pcode1 m1)
    := List.nth_error_map _ _ _.
  rewrite HmB.
  case E0: (List.nth_error Pcode1 m1) => [i1|] //= [Ey].
  by exists i1. }
have Ei1' : i1 = IBnz r l.
{ case: i1 Ei1 {Hi1}
    => [|l0|v0 r0|ra' rb'|op0 ra' rb' rc'|ra' rb'|ra' rb'|ra' rb'
        |r0 l0| |l0|c0' P0| |] //= Ht.
  - by case: Ht => -> ->.
  - by have /= EI := congr1 fst Ht; rewrite if_same in EI; inversion EI. }
subst i1.
move: Hseg2. rewrite -Eseg2 /Transitional.linearize_proc_gen Hc /=.
case Hpc2: (getm Cprocs p2) => [Pcode2|] /=; last first.
{ case: k2 Hk2 {Ho2} => [|k2] /= Hk2.
  - by move=> [E _]; inversion E.
  - move=> Hn.
    have Hlt : (k2 < length (@nil (Transitional.instr * mem_tag)))%coq_nat.
    { apply/(proj1 (List.nth_error_Some _ _)). by rewrite Hn. }
    move: Hlt => /= Hlt. by lia. }
case: k2 Hk2 Ho2 => [|m2] /= Hk2 Ho2.
{ by move=> [E _]; inversion E. }
move=> Hb2.
have [i2 [Hi2 Ei2]] : exists i2,
    List.nth_error Pcode2 m2 = Some i2 /\
    Transitional.instr_to_transitional c i2 = (TrLabel (inl l), xt).
{ move: Hb2.
  have HmB : List.nth_error
               (map (Transitional.instr_to_transitional c) Pcode2) m2
             = option_map (Transitional.instr_to_transitional c)
                 (List.nth_error Pcode2 m2)
    := List.nth_error_map _ _ _.
  rewrite HmB.
  case E0: (List.nth_error Pcode2 m2) => [i2|] //= [Ey].
  by exists i2. }
have Ei2' : i2 = ILabel l.
{ case: i2 Ei2 {Hi2}
    => [|l0|v0 r0|ra' rb'|op0 ra' rb' rc'|ra' rb'|ra' rb'|ra' rb'
        |r0 l0| |l0|c0' P0| |] //= Ht.
  - by case: Ht => E1 _; case: E1 => ->.
  - by have /= EI := congr1 fst Ht; rewrite if_same in EI; inversion EI. }
subst i2.
have [mL [HmnL HmL]] : exists m, m1 < m /\
    List.nth_error Pcode1 m = Some (ILabel l).
{ case: (procs_side Hc) => [Ha'|Hb'].
  - case: Hprem => _ [_ [[_ Hbfa _] _ _]].
    have [m0 [Hlt0 Hm0]] := Hbfa _ _ _ _ _ _ _ Ha' Hpc1 Hi1.
    by exists m0; split.
  - case: Hprem => _ [_ [_ [_ Hbfb _] _]].
    have [m0 [Hlt0 Hm0]] := Hbfb _ _ _ _ _ _ _ Hb' Hpc1 Hi1.
    by exists m0; split. }
set F := fun p' : Procedure.id =>
  count (ilab l) (odflt [::] (getm Cprocs p')).
have HF1 : 1 <= F p1.
{ rewrite /F Hpc1 /=.
  have Hcnt : 0 < count (ilab l) Pcode1
    := In_count_ilabel (List.nth_error_In _ _ HmL).
  by lia. }
have HF2 : 1 <= F p2.
{ rewrite /F Hpc2 /=.
  have Hcnt : 0 < count (ilab l) Pcode2
    := In_count_ilabel (List.nth_error_In _ _ Hi2).
  by lia. }
have Hsum : sumn [seq F p' | p' <- domm Cprocs] <= 1.
{ case: (procs_side Hc) => [Ha'|Hb'].
  - exact: disch_Huniq_a Ha'.
  - exact: disch_Huniq_b Hb'. }
have Hin1 : p1 \in domm Cprocs
  := In_in (List.nth_error_In _ _ Ep1).
have Hin2 : p2 \in domm Cprocs
  := In_in (List.nth_error_In _ _ Ep2).
have Ep12 : p2 = p1.
{ case: (altP (p2 =P p1)) => // Hne.
  have := sumn_two (f := F) (uniq_fset _) Hin1 Hin2 _ HF1 HF2.
  rewrite eq_sym in Hne.
  move=> /(_ Hne) H2.
  by have := leq_trans H2 Hsum. }
subst p2.
move: Hpc2; rewrite Hpc1 => -[E]. subst Pcode2.
have HcntP : count (ilab l) Pcode1 <= 1.
{ have H1 := sumn_mem_le F Hin1.
  have HF1' : F p1 = count (ilab l) Pcode1 by rewrite /F Hpc1.
  rewrite HF1' in H1.
  exact: leq_trans H1 Hsum. }
have Em2 : m2 = mL.
{ apply: (count_pos_uniq HcntP Hi2 _ HmL _) => /=; by rewrite eqxx. }
subst m2.
have Hn12 : n1 = n2.
{ have Hcnt1 : count (pred1 p1) (domm Cprocs) <= 1.
  { by rewrite (count_uniq_mem _ (uniq_fset _)) leq_b1. }
  apply: (count_pos_uniq Hcnt1 Ep1 _ Ep2 _) => /=; by rewrite eqxx. }
subst n2.
have Ho12 : BinInt.Z.to_nat (Pointer.offset tpc)
            < BinInt.Z.to_nat (Pointer.offset pc').
{ rewrite Ho1 Ho2. by lia. }
by lia.
Qed.

(* a RESOLVING label is an [ILabel] of one side, hence bounded *)
Lemma label_bound (c : Component.id) (l : label) (pc' : Pointer.t) :
  Transitional.find_label_in_comp cdeW c l = Some pc' -> l < L.
Proof.
move=> Hfind.
have [cseg [xt [Hc _ _ Hnth]]] := find_label_in_comp_nth disch_Hbound disch_Hsmall Hfind.
have Hin : List.In (TrLabel (inl l), xt) cseg
  := List.nth_error_In _ _ Hnth.
rewrite (cdeW_code Hc) in Hin.
case: (lin_In_inv Hin)
  => [[Cprocs [p [_ _ E]]]|[Cprocs [p [Pcode [i0 [Hp1 Hp2 Hp3 Ht]]]]]].
- by have /= EI := congr1 fst E; inversion EI.
- case: i0 Ht Hp3
    => [|l0|v0 r0|r1 r2|op0 r1 r2 r3|r1 r2|r1 r2|r1 r2|r0 l0| |l0|c0' P0| |]
       //= Ht Hp3.
  all: have /= EI := congr1 fst Ht.
  all: rewrite ?if_same /= in EI.
  all: try by inversion EI.
  all: inversion EI; subst.
  all: case: (procs_side Hp1) => [Ha'|Hb'].
  all: try by apply: (disch_Hlab_a Ha' Hp2 Hp3).
  all: by apply: (disch_Hlab_b Hb' Hp2 Hp3).
Qed.

Lemma disch_HlL_bnz : forall tpc r l tg c pc',
  Transitional.executing cdeW tpc (TrBnz r l) tg c ->
  Transitional.find_label_in_comp cdeW c l = Some pc' -> l < L.
Proof. move=> tpc r l tg c pc' _ Hfind. exact: label_bound Hfind. Qed.

Lemma disch_HlL_jal : forall tpc l tg c pc',
  Transitional.executing cdeW tpc (TrJalNat l) tg c ->
  Transitional.find_label_in_comp cdeW c l = Some pc' -> l < L.
Proof. move=> tpc l tg c pc' _ Hfind. exact: label_bound Hfind. Qed.

(* a RESOLVING procedure label is a HEADER, hence a declared procedure *)
Lemma disch_HpP : forall tpc c' pid tg c pc',
  Transitional.executing cdeW tpc (TrJalProc (c', pid)) tg c ->
  Transitional.find_plabel_in_code cdeW c' pid = Some pc' -> pid < P.
Proof.
move=> tpc c' pid tg c pc' _ Hfind.
have [cseg [xt [Hc _ _ Hnth]]] := find_plabel_in_code_nth disch_Hbound disch_Hwfa disch_Hwfb disch_Hlinkable disch_Hsmall Hfind.
have Hin : List.In (TrLabel (inr (c', pid)), xt) cseg
  := List.nth_error_In _ _ Hnth.
rewrite (cdeW_code Hc) in Hin.
case: (lin_In_inv Hin)
  => [[Cprocs [p [Hp1 Hp2 E]]]|[Cprocs [p [Pcode [i0 [Hp1 Hp2 Hp3 Ht]]]]]].
- have /= EI := congr1 fst E.
  inversion EI; subst.
  case: (procs_side Hp1) => [Ha'|Hb'].
  + exact: disch_Hproc_a Ha' Hp2.
  + exact: disch_Hproc_b Hb' Hp2.
- case: i0 Ht {Hp3}
    => [|l0|v0 r0|r1 r2|op0 r1 r2 r3|r1 r2|r1 r2|r1 r2|r0 l0| |l0|c0' P0| |]
       //= Ht.
  all: have /= EI := congr1 fst Ht.
  all: rewrite ?if_same /= in EI.
  all: by inversion EI.
Qed.

(* if every segment gives P-cells in-segment successors, so does the
   flattening *)
Lemma flatten_next (A : Type) (Pr : A -> Prop) (ll : seq (seq A))
    (o : nat) (x : A) :
  (forall seg, List.In seg ll -> forall k y,
      List.nth_error seg k = Some y -> Pr y ->
      exists y', List.nth_error seg k.+1 = Some y') ->
  List.nth_error (flatten ll) o = Some x -> Pr x ->
  exists x', List.nth_error (flatten ll) o.+1 = Some x'.
Proof.
elim: ll o => [|seg ll IH] o Hseg /=; first by case: o.
case: (ltnP o (size seg)) => [Hlt|Hge] Hnth HP.
- have Hlt' : (o < length seg)%coq_nat by apply/ltP.
  have Ha1 : List.nth_error (seg ++ flatten ll) o = List.nth_error seg o
    := List.nth_error_app1 seg (flatten ll) Hlt'.
  have Hnth1 : List.nth_error seg o = Some x by rewrite -Ha1.
  have [y' Hy'] := Hseg seg (or_introl (erefl _)) _ _ Hnth1 HP.
  exists y'.
  have Hlt1 : (o.+1 < length seg)%coq_nat.
  { apply/(proj1 (List.nth_error_Some _ _)). by rewrite Hy'. }
  have Ha2 : List.nth_error (seg ++ flatten ll) o.+1
             = List.nth_error seg o.+1
    := List.nth_error_app1 seg (flatten ll) Hlt1.
  exact: (eq_trans Ha2 Hy').
- have Hge' : (length seg <= o)%coq_nat by apply/leP.
  have Ha1 : List.nth_error (seg ++ flatten ll) o
             = List.nth_error (flatten ll) (o - length seg)%coq_nat
    := List.nth_error_app2 seg (flatten ll) Hge'.
  have Hnth2 : List.nth_error (flatten ll) (o - size seg) = Some x.
  { have H2 : List.nth_error (flatten ll) (o - length seg)%coq_nat = Some x
      := eq_trans (esym Ha1) Hnth.
    exact: H2. }
  have Hsub : forall seg0, List.In seg0 ll -> forall k y,
      List.nth_error seg0 k = Some y -> Pr y ->
      exists y', List.nth_error seg0 k.+1 = Some y'.
  { move=> seg0 Hin. exact: Hseg seg0 (or_intror Hin). }
  have [x' Hx'] := IH _ Hsub Hnth2 HP.
  exists x'.
  have Hge1 : (length seg <= o.+1)%coq_nat by lia.
  have Ha2 : List.nth_error (seg ++ flatten ll) o.+1
             = List.nth_error (flatten ll) (o.+1 - length seg)%coq_nat
    := List.nth_error_app2 seg (flatten ll) Hge1.
  apply: (eq_trans Ha2).
  rewrite -Hx'. congr (List.nth_error _ _).
  by rewrite minusE (subSn Hge).
Qed.

(* a jal/call cell always has a successor cell in its segment *)
Lemma succ_exists (tpc : Pointer.t) (i : Transitional.instr)
    (tg : mem_tag) (c : Component.id) :
  Transitional.executing cdeW tpc i tg c ->
  ((exists l, i = TrJalNat l) \/ (exists pl, i = TrJalProc pl)) ->
  exists i3 tg3, Transitional.executing cdeW (Pointer.inc tpc) i3 tg3 c.
Proof.
case=> C_code [Ec [Hcde [Hoff Hnth]]] Hshape.
have Hcc := cdeW_code Hcde.
rewrite Hcc in Hnth.
move: Hnth. rewrite /Transitional.linearize_component_gen.
case Hc: (getm (Intermediate.prog_procedures tp) c) => [Cprocs|] /=;
  last first.
{ have Hd := cdeW_domm Hcde.
  by rewrite mem_domm Hc in Hd. }
move=> Hnth.
have Hseg : forall seg,
    List.In seg (map (Transitional.linearize_proc_gen PI tp c)
                   (domm Cprocs)) ->
    forall k y, List.nth_error seg k = Some y ->
    ((exists l, y.1 = TrJalNat l) \/ (exists pl, y.1 = TrJalProc pl)) ->
    exists y', List.nth_error seg k.+1 = Some y'.
{ move=> seg /List.in_map_iff [p [Eseg Hp]] k y.
  rewrite -Eseg /Transitional.linearize_proc_gen Hc /=.
  case Hpc: (getm Cprocs p) => [Pcode|] /=; last first.
  -
    case: k => [|k] /=; last first.
    { move=> Hn.
      have Hlt : (k < length (@nil (Transitional.instr * mem_tag)))%coq_nat.
      { apply/(proj1 (List.nth_error_Some _ _)). by rewrite Hn. }
      move: Hlt => /= Hlt. by lia. }
    move=> [<-] Hsh. exfalso.
    by case: Hsh => [[l El]|[pl El]]; inversion El.
  - case: k => [|k] /=.
    +
      move=> [<-] Hsh. exfalso.
      by case: Hsh => [[l El]|[pl El]]; inversion El.
    +
      move=> Hk Hsh.
      have [i0 [Hi0 Ei0]] : exists i0,
          List.nth_error Pcode k = Some i0 /\
          Transitional.instr_to_transitional c i0 = y.
      { move: Hk.
        have Hmap : List.nth_error
                      (map (Transitional.instr_to_transitional c) Pcode) k
                    = option_map (Transitional.instr_to_transitional c)
                        (List.nth_error Pcode k)
          := List.nth_error_map _ _ _.
        rewrite Hmap.
        case E0: (List.nth_error Pcode k) => [i0|] //= [Ey].
        by exists i0. }
      have Hne1 : i0 <> IHalt.
      { move=> E0'; subst i0.
        case: Hsh => [[l El]|[pl El]];
        by rewrite -Ei0 /= in El; inversion El. }
      have Hne2 : i0 <> IReturn.
      { move=> E0'; subst i0.
        case: Hsh => [[l El]|[pl El]];
        by rewrite -Ei0 /= in El; inversion El. }
      have Hne3 : i0 <> IJump.
      { move=> E0'; subst i0.
        case: Hsh => [[l El]|[pl El]];
        by rewrite -Ei0 /= in El; inversion El. }
      case: (procs_side Hc) => [Ha'|Hb'].
      * case: Hprem => -[[sa [_ Hca]] _ _ _ _] _.
        have [i' Hi'] := compiled_proc_terminal Hca Ha' Hpc Hi0
                           Hne1 Hne2 Hne3.
        exists (Transitional.instr_to_transitional c i').
        exact: (List.map_nth_error _ _ _ Hi').
      * case: Hprem => -[_ [sb [_ Hcb]] _ _ _] _.
        have [i' Hi'] := compiled_proc_terminal Hcb Hb' Hpc Hi0
                           Hne1 Hne2 Hne3.
        exists (Transitional.instr_to_transitional c i').
        exact: (List.map_nth_error _ _ _ Hi'). }
have HP : ((exists l, (i, tg).1 = TrJalNat l)
           \/ (exists pl, (i, tg).1 = TrJalProc pl)).
{ by case: Hshape => [[l ->]|[pl ->]]; [left; exists l|right; exists pl]. }
have [cell' Hcell'] := flatten_next Hseg Hnth HP.
exists cell'.1, cell'.2.
exists (Transitional.linearize_component_gen PI tp c).
split; [|split; [|split]].
- rewrite Pointer.inc_preserves_component. exact: Ec.
- by rewrite Hcc in Hcde.
- rewrite inc_offset. by lia.
- rewrite /Transitional.linearize_component_gen Hc /=.
  have -> : BinInt.Z.to_nat (Pointer.offset (Pointer.inc tpc))
            = (BinInt.Z.to_nat (Pointer.offset tpc)).+1.
  { rewrite inc_offset. by lia. }
  rewrite Hcell'.
  by case: (cell').
Qed.

Lemma disch_Hsucc_jal : forall tpc l tg c,
  Transitional.executing cdeW tpc (TrJalNat l) tg c ->
  exists i3 tg3, Transitional.executing cdeW (Pointer.inc tpc) i3 tg3 c.
Proof.
move=> tpc l tg c Hex.
apply: (succ_exists Hex).
left. by exists l.
Qed.

Lemma disch_Hsucc_call : forall tpc pl tg c,
  Transitional.executing cdeW tpc (TrJalProc pl) tg c ->
  exists i3 tg3, Transitional.executing cdeW (Pointer.inc tpc) i3 tg3 c.
Proof.
move=> tpc pl tg c Hex.
apply: (succ_exists Hex).
right. by exists pl.
Qed.

Lemma disch_Hc1s : forall tpc i tg c,
  Transitional.executing cdeW tpc i tg c ->
  1 + Pointer.component tpc < 2 ^ MDefs.NC.
Proof.
move=> tpc i tg c Hex.
case: Hex => C_code [Ec [Hcde _]].
rewrite -Ec in Hcde.
have Hd := cdeW_domm Hcde.
have Hwf : Intermediate.well_formed_program tp
  := Intermediate.linking_well_formedness disch_Hwfa disch_Hwfb
       disch_Hlinkable.
case: Hprem => _ [_ [_ _ Hlf]].
case: Hlf => _ Hcol.
apply: Hcol.
rewrite (_ : domm (Definitions.prog_interface Wme)
             = domm (Intermediate.prog_interface tp)); last by [].
by rewrite (Intermediate.wfprog_defined_procedures Hwf).
Qed.

(* ---- OBLIGATION: the initial bridge ---- *)

Lemma disch_bridge :
  forall m : finpref_behavior,
  MDefs.run_fits cdeW tp (finpref_trace m) ->
  forall ts0, TSim.t_initial_base cdeW tp ts0 ->
    match_st L P C a b PB PI (amap0 PB) ts0
      (Merged.initial_state (Definitions.code Wme)
         (Definitions.prog_buffers Wme)
         (Definitions.prog_interface Wme)) /\
    heap_inv MDefs.NC (let '(tm, _, _, _) := ts0 in tm)
      (Symbolic.mem
         (Merged.initial_state (Definitions.code Wme)
            (Definitions.prog_buffers Wme)
            (Definitions.prog_interface Wme))).
Proof.
move=> m Hrf ts0 Hbase.
have Hfit4 := Hrf ts0 E0 ts0 Hbase (star_refl _ _ _)
                (ex_intro _ (finpref_trace m) (erefl _)).
case: Hfit4 => Hfit _.
have Hcl : Intermediate.closed_program tp.
{ by case: Hprem => _ [? _]. }
have [Cmain [_ [Hmp Hmm]]] := Intermediate.cprog_main_existence Hcl.
have Hal32 : Merged.alloc_label < 2 ^ word_size mt.
{ rewrite /Merged.alloc_label word_size_mt. by rewrite ltn_exp2l. }
have HbdLin : size (linearize_bufs PB) + size codeW < 2 ^ word_size mt.
{ have := disch_Hsmall. by lia. }
have Hvf : (forall c cm b0 blk o cell,
    Transitional.Memory.prepare_procedures_initial_memory tp c = Some cm ->
    getm (Transitional.Memory.content cm) b0 = Some blk ->
    List.nth_error blk o = Some cell ->
    MDefs.value_fits
      (Transitional.Memory.prepare_procedures_initial_memory tp)
      (Transitional.val cell.1)).
{ case: Hbase Hfit => pcb [Hfind ->] Hfit.
  by case: Hfit => _ Hmemf _. }
split.
- exact: (match_initial (erefl _) (erefl _) HbdLin disch_Hsmall
            Hmp Hmm disch_Hwfa disch_Hwfb disch_Hlinkable Hbase Hvf).
-
  apply: (heap_inv_init disch_Hbound disch_Hsmall disch_HNCws
            disch_HNCal (erefl MDefs.NC)).
  move=> w Hge.
  have Hal_lt : Merged.alloc_label < 2 ^ (word_size mt - MDefs.NC)
    := disch_HNCal.
  have Hw32 : (\val w : nat) < 2 ^ word_size mt := ltn_ord _.
  have Hlin32 : size (linearize_bufs PB) < 2 ^ word_size mt by lia.
  have Hpc0E : size (initial_memory (mt := mt) PB)
               = size (linearize_bufs PB)
    := initial_memory_size_eq Hlin32.
  have Hen : encode_code (Definitions.code Wme)
               (size (initial_memory (mt := mt)
                        (Definitions.prog_buffers Wme))) w = None.
  { case E: (encode_code _ _ _) => [v|] //.
    exfalso.
    have [n [Ew [Hn _]]] := encode_code_nth_inv E.
    have Hn' : n < size codeW by exact: Hn.
    have HpcE' : size (initial_memory (mt := mt)
                   (Definitions.prog_buffers Wme))
                 = size (linearize_bufs PB) by exact: Hpc0E.
    have Hnb : n + size (initial_memory (mt := mt)
                  (Definitions.prog_buffers Wme)) < 2 ^ word_size mt.
    { rewrite HpcE'. have := disch_Hsmall. by lia. }
    have Em1 : (\val (@word_of_nat (word_size mt)
                  (n + size (initial_memory (mt := mt)
                        (Definitions.prog_buffers Wme)))) : nat)
               = (n + size (initial_memory (mt := mt)
                     (Definitions.prog_buffers Wme)))
                 %% 2 ^ word_size mt
      := @valw_as_word (word_size mt) _.
    have Ev : (\val w : nat)
              = n + size (initial_memory (mt := mt)
                    (Definitions.prog_buffers Wme)).
    { rewrite Ew Em1. exact: modn_small Hnb. }
    have Hge2 : 2 ^ (word_size mt - MDefs.NC) <= (\val w : nat) := Hge.
    rewrite Ev HpcE' in Hge2.
    have := disch_Hsmall. by lia. }
  have Ewr : @word_of_nat (word_size mt) (\val w) = w.
  { apply: (@word_nat_inj (word_size mt)).
    have Em2 : (\val (@word_of_nat (word_size mt) (\val w)) : nat)
               = (\val w) %% 2 ^ word_size mt
      := @valw_as_word (word_size mt) _.
    rewrite Em2. exact: modn_small Hw32. }
  have Him : initial_memory (mt := mt) (Definitions.prog_buffers Wme) w
             = None.
  { rewrite -Ewr.
    apply: initial_memory_above; last exact: Hw32.
    rewrite (_ : Definitions.prog_buffers Wme = PB) //.
    have := disch_Hsmall. by lia. }
  by rewrite /Merged.initial_state /= unionmE Hen Him.
Qed.

(* ================================================================== *)
(* The frozen forward statement.                                      *)
(* ================================================================== *)

Theorem t2me_fwd_assembled : forall m,
    forall (MM : Component.id -> seq sv)
      (HMMd : forall c S, getm cdeW c = Some S -> comp_ok (c, 1, Z0) S (MM c))
      (Hcstd : forall pc iv r tg c p,
          Transitional.executing cdeW pc (TrConst iv r) tg c ->
          iv = IPtr p ->
          p = (c, 0, Z0) \/
          ((p = (c, 1, Z0) \/ p = (c, 1, BinInt.Z.one)) /\
           (r = R_AUX1 \/ r = R_AUX2)))
      (Huniqd : forall (c : Component.id) (S : TS.tcode) (l : label)
          (m0 m0' : nat) (t1 t2 : mem_tag),
          getm cdeW c = Some S ->
          nth_error S m0 = Some (TrLabel (inl l), t1) ->
          nth_error S m0' = Some (TrLabel (inl l), t2) ->
          m0 = m0')
      (Hdsy0 : MDefs.run_fits (MDefs.cde a b) tp (finpref_trace m) ->
          forall ts0, TSim.t_initial_base cdeW tp ts0 ->
          mm_dsync L P C a b PB PI MM cdeW (amap0 PB) ts0
            (Merged.initial_state (Definitions.code Wme)
               (Definitions.prog_buffers Wme)
               (Definitions.prog_interface Wme))),
  does_prefix (MDefs.tsem a b) m ->
  not_wrong_finpref m ->
  MDefs.run_fits (MDefs.cde a b) tp (finpref_trace m) ->
  does_prefix (MDefs.mesem L P C a b) m.
Proof.
move=> m MM HMMd Hcstd Huniqd Hdsy0 Hdp Hnw Hrf.
apply: (t2me_fwd_prefix HMMd Hcstd Huniqd disch_Hbound disch_HPB disch_Hwfa disch_Hwfb
          disch_Hlinkable disch_Hsmall disch_HNCws disch_HNCal
          (erefl MDefs.NC)
          disch_Himm_a disch_Himm_b disch_Hlab_a disch_Hlab_b
          disch_Hcomp_a disch_Hcomp_b disch_Huniq_a disch_Huniq_b
          disch_Hproc_a disch_Hproc_b disch_Hself disch_Hjra disch_Hbf
          disch_HlL_bnz disch_HlL_jal disch_HpP disch_Hsucc_jal
          disch_Hsucc_call disch_Hc1s
          (W := Wme) (m := m) _ _ _ _).
- move=> ts0 Hts0.
  split; last split.
  + exact: (proj1 (disch_bridge Hrf Hts0)).
  + exact: (proj2 (disch_bridge Hrf Hts0)).
  + exact: (Hdsy0 Hrf _ Hts0).
- exact: Hdp.
- exact: Hnw.
- exact: Hrf.
Qed.

(* The behaviour-directed backward statement: the verdict for a GIVEN
   T behaviour — what the S-hop composes with.                        *)

Theorem t2me_bwd_assembled_for : forall m bT,
    forall (MM : Component.id -> seq sv)
      (HMMd : forall c S, getm cdeW c = Some S -> comp_ok (c, 1, Z0) S (MM c))
      (Hcstd : forall pc iv r tg c p,
          Transitional.executing cdeW pc (TrConst iv r) tg c ->
          iv = IPtr p ->
          p = (c, 0, Z0) \/
          ((p = (c, 1, Z0) \/ p = (c, 1, BinInt.Z.one)) /\
           (r = R_AUX1 \/ r = R_AUX2)))
      (Huniqd : forall (c : Component.id) (S : TS.tcode) (l : label)
          (m0 m0' : nat) (t1 t2 : mem_tag),
          getm cdeW c = Some S ->
          nth_error S m0 = Some (TrLabel (inl l), t1) ->
          nth_error S m0' = Some (TrLabel (inl l), t2) ->
          m0 = m0')
      (Hdsy0 : MDefs.run_fits (MDefs.cde a b) tp (finpref_trace m) ->
          forall ts0, TSim.t_initial_base cdeW tp ts0 ->
          mm_dsync L P C a b PB PI MM cdeW (amap0 PB) ts0
            (Merged.initial_state (Definitions.code Wme)
               (Definitions.prog_buffers Wme)
               (Definitions.prog_interface Wme))),
  does_prefix (MDefs.mesem L P C a b) m ->
  MDefs.run_fits (MDefs.cde a b) tp (finpref_trace m) ->
  program_behaves (MDefs.tsem a b) bT ->
  CompCertExtensions.prefix m bT \/ behavior_improves_finpref bT m.
Proof.
move=> m bT MM HMMd Hcstd Huniqd Hdsy0 Hdp Hrf HbT.
apply: (t2me_bwd_prefix_for HMMd Hcstd Huniqd disch_Hbound disch_HPB disch_Hwfa disch_Hwfb
          disch_Hlinkable disch_Hsmall disch_HNCws disch_HNCal
          (erefl MDefs.NC)
          disch_Himm_a disch_Himm_b disch_Hlab_a disch_Hlab_b
          disch_Hcomp_a disch_Hcomp_b disch_Huniq_a disch_Huniq_b
          disch_Hproc_a disch_Hproc_b disch_Hself disch_Hjra disch_Hbf
          disch_HlL_bnz disch_HlL_jal disch_HpP disch_Hsucc_jal
          disch_Hsucc_call disch_Hc1s
          (Wdet := Wme) (m := m) (bT := bT) _ _ _ _).
- move=> ts0 Hts0.
  split; last split.
  + exact: (proj1 (disch_bridge Hrf Hts0)).
  + exact: (proj2 (disch_bridge Hrf Hts0)).
  + exact: (Hdsy0 Hrf _ Hts0).
- exact: Hdp.
- exact: Hrf.
- exact: HbT.
Qed.

(* The frozen backward statement.                                     *)

End Discharge.
