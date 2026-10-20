Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Maps.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
From extructures Require Import ord fmap fset.
Require Import Coq.micromega.Lia.

Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.CompCertExtensions.
Require Import Intermediate.Machine.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import MicroPolicies.Recomposition.BufferLayout.
Require Import MicroPolicies.Recomposition.Definitions.
Require Import MicroPolicies.Recomposition.LinearizeMerged.
Require Import Source.Language.
Require Import S2I.CompMonad.
Require Import S2I.Definitions.
Require Import S2I.Compiler.
Require Import S2I.LabelUniq.
Require Import T2M.MPos.
Require Import T2M.MStatic.
Require Import T2M.MSig.
Require Import T2M.MDisc.
Require Import T2M.MInj.
Require Import T2M.MSync.
Require Import T2M.MInit.
Require T2M.MDefs.
Require T2M.MCoh.
Require T2M.MDiscInit.
Require S2T.TSim.
Require Import Coq.Logic.ClassicalEpsilon.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Section Discharge2.

Variables L P C : nat.
Variables a b : Intermediate.program.

Local Notation PB := (MDefs.PBw a b).
Local Notation PI := (MDefs.PIw a b).
Local Notation tp := (Intermediate.program_link a b).
Local Notation cdeW :=
  (Transitional.intermediate_to_transitional_gen PI tp).

Variable Hprem : MDefs.t2me_premises L P C a b.

Definition auxreg (r : register) : bool :=
  match r with R_AUX1 | R_AUX2 => true | _ => false end.

Definition cstbad (C0 : Component.id) (i0 : Machine.instr) : bool :=
  match i0 with
  | IConst (IPtr (c', b', o')) r =>
      ~~ [|| [&& Nat.eqb c' C0, Nat.eqb b' 0 & Z.eqb o' 0],
             [&& Nat.eqb c' C0, Nat.eqb b' 1, Z.eqb o' 0 & auxreg r]
           | [&& Nat.eqb c' C0, Nat.eqb b' 1, Z.eqb o' 1 & auxreg r]]
  | _ => false
  end.

Lemma compile_expr_cstok (C0 : Component.id)
    (P_labels : NMap label) (e : expr) :
  forall (s : comp_env) (c : Machine.code) (s' : comp_env),
  compile_expr C0 (C0, 0, 0%Z) (C0, 1, 0%Z) P_labels e s = Some (c, s') ->
  ~~ has (cstbad C0) c.
Proof.
elim: e => [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
           |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc.
- by case: v Hc => [i|p|] //= [<- _].
- by move: Hc => /= [<- _].
- move: Hc => /= [<- _] /=.
  by rewrite !PeanoNat.Nat.eqb_refl.
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 (C0, 0, 0%Z) (C0, 1, 0%Z) P_labels e1 s)
    => [[c1 s1]|] //=.
  case E2: (compile_expr C0 (C0, 0, 0%Z) (C0, 1, 0%Z) P_labels e2 s1)
    => [[c2 s2]|] //=.
  move=> [<- _].
  by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
     (negbTE (IH1 _ _ _ E1)) (negbTE (IH2 _ _ _ E2)).
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 (C0, 0, 0%Z) (C0, 1, 0%Z) P_labels e1 s)
    => [[c1 s1]|] //=.
  case E2: (compile_expr C0 (C0, 0, 0%Z) (C0, 1, 0%Z) P_labels e2 s1)
    => [[c2 s2]|] //=.
  move=> [<- _].
  by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
     (negbTE (IH1 _ _ _ E1)) (negbTE (IH2 _ _ _ E2)).
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 (C0, 0, 0%Z) (C0, 1, 0%Z) P_labels e1 s)
    => [[c1 s1]|] //=.
  case E2: (compile_expr C0 (C0, 0, 0%Z) (C0, 1, 0%Z) P_labels e2 s1)
    => [[c2 s2]|] //=.
  case E3: (compile_expr C0 (C0, 0, 0%Z) (C0, 1, 0%Z) P_labels e3 s2)
    => [[c3 s3]|] //=.
  case E4: (fresh_label C0 s3) => [[lconseq s4]|] //=.
  case E5: (fresh_label C0 s4) => [[lend s5]|] //=.
  move=> [<- _].
  by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
     (negbTE (IH1 _ _ _ E1)) (negbTE (IH2 _ _ _ E2))
     (negbTE (IH3 _ _ _ E3)).
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 (C0, 0, 0%Z) (C0, 1, 0%Z) P_labels e s)
    => [[c1 s1]|] //=.
  move=> [<- _].
  by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
     (negbTE (IH _ _ _ E1)).
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 (C0, 0, 0%Z) (C0, 1, 0%Z) P_labels e s)
    => [[c1 s1]|] //=.
  move=> [<- _].
  by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
     (negbTE (IH _ _ _ E1)).
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 (C0, 0, 0%Z) (C0, 1, 0%Z) P_labels e1 s)
    => [[c1 s1]|] //=.
  case E2: (compile_expr C0 (C0, 0, 0%Z) (C0, 1, 0%Z) P_labels e2 s1)
    => [[c2 s2]|] //=.
  move=> [<- _].
  by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
     (negbTE (IH1 _ _ _ E1)) (negbTE (IH2 _ _ _ E2)).
-
  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 (C0, 0, 0%Z) (C0, 1, 0%Z) P_labels e s)
    => [[c1 s1]|] //=.
  case: (Component.eqb C' C0).
  + case E2: (find_proc_label P_labels P' s1) => [[tl s2]|] //=.
    move=> [<- _].
    by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
       ?PeanoNat.Nat.eqb_refl /=
       (negbTE (IH _ _ _ E1)).
  + move=> [<- _].
    by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
       ?PeanoNat.Nat.eqb_refl /=
       (negbTE (IH _ _ _ E1)).
- by move: Hc => /= [<- _].
Qed.

Lemma compile_proc_cstok (C0 : Component.id)
    (P_labels : NMap label) (P0 : Procedure.id) (e : expr) :
  forall (s : comp_env) (c : Machine.code) (s' : comp_env),
  compile_proc C0 (C0, 0, 0%Z) (C0, 1, 0%Z) P_labels P0 e s
    = Some (c, s') ->
  ~~ has (cstbad C0) c.
Proof.
move=> s c s' Hc.
move: Hc; rewrite /compile_proc.
cbv beta iota delta [Monads.bind Monads.ret compilation_monad
  CompMonad.Comp.bind CompMonad.Comp.ret].
case E0: (find_proc_label P_labels P0 s) => [[pl s0]|] //=.
case E1: (fresh_label C0 s0) => [[lmain s1]|] //=.
case E2: (fresh_label C0 s1) => [[lreturn s2]|] //=.
case E3: (compile_expr C0 (C0, 0, 0%Z) (C0, 1, 0%Z) P_labels e s2)
  => [[pc0 s3]|] //=.
case: (Component.eqb C0 Component.main
       && Procedure.eqb P0 Procedure.main) => /=;
case: (immediately_final e) => /=;
move=> [<- _];
by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
   ?has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
   ?PeanoNat.Nat.eqb_refl /=
   (negbTE (compile_expr_cstok E3)).
Qed.

Lemma disch_HcstT : forall tpc iv r tg c p,
  Transitional.executing cdeW tpc (TrConst iv r) tg c ->
  iv = IPtr p ->
  p = (c, 0, 0%Z) \/
  ((p = (c, 1, 0%Z) \/ p = (c, 1, 1%Z)) /\ (r = R_AUX1 \/ r = R_AUX2)).
Proof.
move=> tpc iv r tg c p Hex Eiv. subst iv.
have Hin := executing_In Hex.
case: (lin_In_inv Hin)
  => [[Cprocs [p0 [_ _ E]]]|[Cprocs [p0 [Pcode [i0 [Hp1 Hp2 Hp3 Ht]]]]]].
- by have /= EI := congr1 fst E; inversion EI.
- have Ei0 : i0 = IConst (IPtr p) r.
  { case: i0 Ht {Hp3} =>
      [|l0|v0 r0|ra' rb'|op0 ra' rb' rc'|ra' rb'|ra' rb'|ra' rb'
       |r0 l0| |l0|c0' P0| |] //= Ht.
    - by case: Ht => -> ->.
    - by have /= EI := congr1 fst Ht; rewrite if_same in EI; inversion EI. }
  subst i0.
  case Hbad: (cstbad c (IConst (IPtr p) r)); last first.
  { move: Hbad. rewrite /cstbad.
    case: p Hex Hin Ht Hp3 => [[c' b'] o'] _ _ _ _.
    move/negbFE.
    case/or3P => [/and3P [E1 E2 E3]|/and4P [E1 E2 E3 E4]
                 |/and4P [E1 E2 E3 E4]].
    - left.
      move/PeanoNat.Nat.eqb_eq: E1 => ->.
      move/PeanoNat.Nat.eqb_eq: E2 => ->.
      by move/Z.eqb_eq: E3 => ->.
    - right.
      move/PeanoNat.Nat.eqb_eq: E1 => ->.
      move/PeanoNat.Nat.eqb_eq: E2 => ->.
      move/Z.eqb_eq: E3 => ->.
      split; first by left.
      by case: r E4 => //=; [left|right].
    - right.
      move/PeanoNat.Nat.eqb_eq: E1 => ->.
      move/PeanoNat.Nat.eqb_eq: E2 => ->.
      move/Z.eqb_eq: E3 => ->.
      split; first by right.
      by case: r E4 => //=; [left|right]. }
  exfalso.
  have In_has : forall (A : Type) (pr : A -> bool) (x : A) (s0 : seq A),
      List.In x s0 -> pr x -> has pr s0.
  { move=> A pr x s0. elim: s0 => [|y s0 IH] //= [->|Hin0] Hp.
    - by rewrite Hp.
    - by rewrite (IH Hin0 Hp) orbT. }
  have Hhas : has (cstbad c) Pcode := In_has _ _ _ _ Hp3 Hbad.
  case: (procs_side Hp1) => [Ha'|Hb'].
  + case: Hprem => -[[sa [_ Hca]] _ _ _ _] _.
    case: (compiled_proc_origin Hca Ha' Hp2)
      => [[plm [e0 [s0 [s1 Hcp]]]]|[lab Ecd]].
    * by rewrite (negbTE (compile_proc_cstok Hcp)) in Hhas.
    * by rewrite Ecd /= in Hhas.
  + case: Hprem => -[_ [sb [_ Hcb]] _ _ _] _.
    case: (compiled_proc_origin Hcb Hb' Hp2)
      => [[plm [e0 [s0 [s1 Hcp]]]]|[lab Ecd]].
    * by rewrite (negbTE (compile_proc_cstok Hcp)) in Hhas.
    * by rewrite Ecd /= in Hhas.
Qed.

Lemma disch_HuniqT : forall (c : Component.id)
    (S : seq (Transitional.instr * mem_tag)) (l : label)
    (m m' : nat) (t1 t2 : mem_tag),
  cdeW c = Some S ->
  List.nth_error S m = Some (TrLabel (inl l), t1) ->
  List.nth_error S m' = Some (TrLabel (inl l), t2) ->
  m = m'.
Proof.
move=> c S l m m' t1 t2 Hcde Hm Hm'.
have Hcc := cdeW_code Hcde.
rewrite Hcc in Hm Hm'.
move: Hm Hm'. rewrite /Transitional.linearize_component_gen.
case Hc: (getm (Intermediate.prog_procedures tp) c) => [Cprocs|];
  last first.
{ have Hd := cdeW_domm Hcde. by rewrite mem_domm Hc in Hd. }
rewrite /=.
move=> Hm Hm'.
have [n1 [seg1 [k1 [Hll1 Hseg1 Ho1 Hk1]]]] := nth_flatten_inv Hm.
have [n2 [seg2 [k2 [Hll2 Hseg2 Ho2 Hk2]]]] := nth_flatten_inv Hm'.
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
{ case: k1 Hk1 {Ho1} => [|k1] /= Hk1.
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
    Transitional.instr_to_transitional c i1 = (TrLabel (inl l), t1).
{ move: Hb1.
  have HmB : List.nth_error
               (map (Transitional.instr_to_transitional c) Pcode1) m1
             = option_map (Transitional.instr_to_transitional c)
                 (List.nth_error Pcode1 m1)
    := List.nth_error_map _ _ _.
  rewrite HmB.
  case E0: (List.nth_error Pcode1 m1) => [i1|] //= [Ey].
  by exists i1. }
have Ei1' : i1 = ILabel l.
{ case: i1 Ei1 {Hi1}
    => [|l0|v0 r0|ra' rb'|op0 ra' rb' rc'|ra' rb'|ra' rb'|ra' rb'
        |r0 l0| |l0|c0' P0| |] //= Ht.
  - by case: Ht => E1 _; case: E1 => ->.
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
    Transitional.instr_to_transitional c i2 = (TrLabel (inl l), t2).
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
set F := fun p' : Procedure.id =>
  count (ilab l) (odflt [::] (getm Cprocs p')).
have HF1 : 1 <= F p1.
{ rewrite /F Hpc1 /=.
  have Hcnt : 0 < count (ilab l) Pcode1
    := In_count_ilabel (List.nth_error_In _ _ Hi1).
  by lia. }
have HF2 : 1 <= F p2.
{ rewrite /F Hpc2 /=.
  have Hcnt : 0 < count (ilab l) Pcode2
    := In_count_ilabel (List.nth_error_In _ _ Hi2).
  by lia. }
have Hsum : sumn [seq F p' | p' <- domm Cprocs] <= 1.
{ case: (procs_side Hc) => [Ha'|Hb'].
  - exact (disch_Huniq_a Hprem l Ha').
  - exact (disch_Huniq_b Hprem l Hb'). }
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
have Em12 : m1 = m2.
{ apply: (count_pos_uniq HcntP Hi1 _ Hi2 _) => /=; by rewrite eqxx. }
subst m2.
have Hn12 : n1 = n2.
{ have Hcnt1 : count (pred1 p1) (domm Cprocs) <= 1.
  { by rewrite (count_uniq_mem _ (uniq_fset _)) leq_b1. }
  apply: (count_pos_uniq Hcnt1 Ep1 _ Ep2 _) => /=; by rewrite eqxx. }
subst n2.
rewrite Ho1 Ho2. by [].
Qed.

Local Notation mem0' :=
  (Transitional.Memory.prepare_procedures_initial_memory tp).

Lemma compilation_preserves_buffers (p : Source.program)
    (tp' : Intermediate.program) :
  compile_program p = Some tp' ->
  Intermediate.prog_buffers tp' = gen_buffers (Source.prog_buffers p).
Proof.
rewrite /compile_program /run /= /Comp.bind /=.
case Eg: (gen_all_procedures_labels
            (elementsm (Source.prog_procedures p)) init_env)
  => [[labels cenv1]|]; last by [].
rewrite /=.
case Ec: (compile_components (gen_buffers (Source.prog_buffers p)) labels
            (elementsm (Source.prog_procedures p)) cenv1)
  => [[codeL cenv2]|]; last by rewrite /=.
rewrite /=.
by move=> [<-].
Qed.

Lemma reserve_blocks_content (m : Transitional.Memory.mem) (n : nat) :
  Transitional.Memory.content
    (Transitional.Memory.reserve_blocks m n).1
  = Transitional.Memory.content m.
Proof.
rewrite /Transitional.Memory.reserve_blocks.
elim: n => [|n IH] //.
rewrite iterS.
case E: (ssrnat.iter n _ _) => [mcur bs] /=.
rewrite E /= in IH.
by rewrite /Transitional.Memory.reserve_block /=.
Qed.

Lemma reserve_blocks_nextblock (m : Transitional.Memory.mem) (n : nat) :
  Transitional.Memory.nextblock m
  <= Transitional.Memory.nextblock
       (Transitional.Memory.reserve_blocks m n).1.
Proof.
rewrite /Transitional.Memory.reserve_blocks.
elim: n => [|n IH] //.
rewrite iterS.
case E: (ssrnat.iter n _ _) => [mcur bs] /=.
rewrite E /= in IH.
rewrite /Transitional.Memory.reserve_block /=.
by lia.
Qed.

Lemma mem0_getm_inv (c : Component.id)
    (cm : Transitional.Memory.mem) :
  getm mem0' c = Some cm ->
  Transitional.Memory.content cm
  = Transitional.Memory.content
      (Transitional.Memory.prealloc
         (mapm (fun a0 => (c, a0))
            (odflt emptym (getm (Intermediate.prog_buffers tp) c))))
  /\ Transitional.Memory.nextblock
       (Transitional.Memory.prealloc
          (mapm (fun a0 => (c, a0))
             (odflt emptym (getm (Intermediate.prog_buffers tp) c))))
     <= Transitional.Memory.nextblock cm.
Proof.
rewrite /Transitional.Memory.prepare_procedures_initial_memory
        /Transitional.Memory.prepare_procedures_initial_memory_aux.
rewrite mapmE mkfmapfE.
case: ifP => // Hin.
rewrite /= /Transitional.Memory.reserve_component_blocks.
case E: (Transitional.Memory.reserve_blocks _ _) => [Cmem' bs].
move=> [<-].
have EC : Cmem' = (Transitional.Memory.reserve_blocks
    (Transitional.Memory.prealloc
       (mapm (fun a0 => (c, a0))
          (odflt emptym (getm (Intermediate.prog_buffers tp) c))))
    (length (elementsm
       (odflt emptym (getm (Intermediate.prog_procedures tp) c))))).1.
{ by rewrite E. }
rewrite EC.
split.
- by rewrite reserve_blocks_content.
- exact (reserve_blocks_nextblock
    (Transitional.Memory.prealloc
       (mapm (fun a0 => (c, a0))
          (odflt emptym (getm (Intermediate.prog_buffers tp) c))))
    (length (elementsm
       (odflt emptym (getm (Intermediate.prog_procedures tp) c))))).
Qed.

Lemma tp_buffers_shape (c : Component.id)
    (bufs : {fmap Block.id -> nat + list value}) :
  getm (Intermediate.prog_buffers tp) c = Some bufs ->
  exists info,
    bufs = mkfmap [:: (0, info); (1, inr [:: Undef; Int 0])] /\
    (forall vs v, info = inr vs -> List.In v vs ->
       Source.well_formed_buffer_value c v).
Proof.
case: Hprem => -[[sa [Hwfa Hca]] [sb [Hwfb Hcb]] _ _ _] _.
rewrite /Intermediate.program_link /= unionmE.
case Ea: (getm (Intermediate.prog_buffers a) c) => [v0|] /=.
- move=> [<-].
  move: Ea.
  rewrite (compilation_preserves_buffers Hca) /gen_buffers mapmE.
  case Es: (getm (Source.prog_buffers sa) c) => [info|] //= [<-].
  exists info. split=> // vs v Einfo Hv. subst info.
  have Hwfb0 := Source.wfprog_buffer_values Hwfa Es.
  move: Hwfb0. rewrite /Source.well_formed_buffer.
  move/List.forallb_forall. by apply.
- move=> Eb.
  move: Eb.
  rewrite (compilation_preserves_buffers Hcb) /gen_buffers mapmE.
  case Es: (getm (Source.prog_buffers sb) c) => [info|] //= [<-].
  exists info. split=> // vs v Einfo Hv. subst info.
  have Hwfb0 := Source.wfprog_buffer_values Hwfb Es.
  move: Hwfb0. rewrite /Source.well_formed_buffer.
  move/List.forallb_forall. by apply.
Qed.

Lemma fold_max_acc (s : seq nat) (a0 : nat) :
  a0 <= fold_left Nat.max s a0.
Proof.
elim: s a0 => [|z s IH] a0 //=.
have := IH (Nat.max a0 z). by lia.
Qed.

Lemma fold_max_ge (s : seq nat) (x acc : nat) :
  x \in s -> x <= fold_left Nat.max s acc.
Proof.
elim: s acc => [|y s IH] acc //=.
rewrite inE => /orP [/eqP ->|Hx].
- have := fold_max_acc s (Nat.max acc y). by lia.
- exact: IH.
Qed.

Lemma mem0_bufs (c : Component.id) (cm : Transitional.Memory.mem) :
  getm mem0' c = Some cm ->
  exists bufs, getm (Intermediate.prog_buffers tp) c = Some bufs.
Proof.
move=> Hcm.
move: Hcm.
rewrite /Transitional.Memory.prepare_procedures_initial_memory
        /Transitional.Memory.prepare_procedures_initial_memory_aux.
rewrite mapmE mkfmapfE.
case: ifP => // Hin _.
have Hd : c \in domm (Intermediate.prog_buffers tp).
{ move: Hin.
  have Hwftp : Intermediate.well_formed_program tp.
  { case: Hprem => -[_ _ Hwa Hwb Hl] _.
    exact: Intermediate.linking_well_formedness Hwa Hwb Hl. }
  by rewrite (Intermediate.wfprog_defined_buffers Hwftp). }
move: Hd. rewrite mem_domm.
case E: (getm _ _) => [bufs|] // _.
by exists bufs.
Qed.

Lemma disch_P2 : forall c cm, getm mem0' c = Some cm ->
  2 <= Transitional.Memory.nextblock cm.
Proof.
move=> c cm Hcm.
have [_ Hnb] := mem0_getm_inv Hcm.
have [bufs Hbufs] := mem0_bufs Hcm.
have [info [Ebufs _]] := tp_buffers_shape Hbufs.
move: Hnb. rewrite Hbufs /= /Transitional.Memory.prealloc /= => Hnb.
set FL := fold_left _ _ _ in Hnb.
have H2 : 1 <= FL.
{ rewrite /FL. apply: fold_max_ge.
  by rewrite mem_domm mapmE Ebufs mkfmapE. }
by lia.
Qed.

Lemma disch_P5 : forall c S,
  cdeW c = Some S ->
  exists cm, getm mem0' c = Some cm.
Proof.
move=> c S Hcde.
have Hd := cdeW_domm Hcde.
have Hwftp : Intermediate.well_formed_program tp.
{ case: Hprem => -[_ _ Hwa Hwb Hl] _.
  exact: Intermediate.linking_well_formedness Hwa Hwb Hl. }
have Hin : c \in domm (Intermediate.prog_interface tp).
{ by rewrite (Intermediate.wfprog_defined_procedures Hwftp). }
rewrite /Transitional.Memory.prepare_procedures_initial_memory
        /Transitional.Memory.prepare_procedures_initial_memory_aux.
rewrite mapmE mkfmapfE Hin /=.
by eexists.
Qed.

Lemma disch_P3 : forall c cm, getm mem0' c = Some cm ->
  exists tg0 tg1,
    cell_at mem0' c 1 0 = Some (Transitional.tUndef, tg0)
    /\ cell_at mem0' c 1 1
       = Some (Transitional.to_tvalue (Int 0), tg1).
Proof.
move=> c cm Hcm.
have [Hcont _] := mem0_getm_inv Hcm.
have [bufs Hbufs] := mem0_bufs Hcm.
have [info [Ebufs _]] := tp_buffers_shape Hbufs.
exists (def_mem_tag c false), (def_mem_tag c false).
rewrite /cell_at Hcm Hcont /Transitional.Memory.prealloc /=.
rewrite mapmE mapmE Hbufs /= Ebufs mkfmapE /=.
by [].
Qed.

Lemma disch_P1 : forall c bk j cv tg,
  cell_at mem0' c bk j = Some (cv, tg) ->
  tvtag cv = Other /\
  (forall q, Transitional.val cv = Ptr q ->
     Pointer.component q = c /\ Pointer.block q = 0).
Proof.
move=> c bk j cv tg.
rewrite /cell_at.
case Hcm: (getm mem0' c) => [cm|] //.
have [Hcont _] := mem0_getm_inv Hcm.
have [bufs Hbufs] := mem0_bufs Hcm.
have [info [Ebufs Hwfv]] := tp_buffers_shape Hbufs.
rewrite Hcont /Transitional.Memory.prealloc /=.
rewrite mapmE mapmE Hbufs /= Ebufs mkfmapE /=.
have Hrep : forall (A : Type) (x y : A) (n j0 : nat),
    List.nth_error (repeat x n) j0 = Some y -> y = x.
{ move=> A x y. elim=> [|n IH] [|j0] //=.
  - by move=> [<-].
  - exact: IH. }
case Eb0: (bk == 0) => /=.
-
  case: info Ebufs Hwfv => [size|vs] Ebufs Hwfv /=.
  + move=> Hnth.
    have [E1 E2] : cv = Transitional.tUndef /\ tg = def_mem_tag c false.
    { by have := Hrep _ _ _ _ _ Hnth => -[-> ->]. }
    subst cv. by split.
  + move=> Hnth.
    have [v [Hv Ev]] : exists v,
        List.nth_error vs j = Some v
        /\ (Transitional.to_tagged_cell c v) = (cv, tg).
    { move: Hnth. rewrite /Transitional.to_tagged_block.
      have HmB : List.nth_error (map (Transitional.to_tagged_cell c) vs) j
                 = option_map (Transitional.to_tagged_cell c)
                     (List.nth_error vs j)
        := List.nth_error_map _ _ _.
      rewrite HmB.
      case E0: (List.nth_error vs j) => [v|] //= Ey.
      exists v. split=> //.
      by move: Ey => -[E1 E2]; rewrite -E1 -E2. }
    have Hwf : Source.well_formed_buffer_value c v.
    { apply: (Hwfv vs) => //.
      exact: List.nth_error_In Hv. }
    move: Ev. rewrite /Transitional.to_tagged_cell => -[Ecv _].
    subst cv.
    split=> //.
    move=> q /= Eq.
    move: Hwf. rewrite /Source.well_formed_buffer_value Eq.
    case/andP => /PeanoNat.Nat.eqb_eq Hb /PeanoNat.Nat.eqb_eq Hc0.
    by split.
- case Eb1: (bk == 1) => //=.
  case: j => [|[|j]] //=.
  + move=> [E1 _]. subst cv. by split.
  + move=> [E1 _]. subst cv. by split.
  + by case: j.
Qed.

Lemma lin_gen_split (pr : Intermediate.program) (c : Component.id) :
  getm (Intermediate.prog_procedures tp) c
    = getm (Intermediate.prog_procedures pr) c ->
  Transitional.linearize_component_gen PI tp c
  = Transitional.linearize_component_gen PI pr c.
Proof.
move=> E.
rewrite /Transitional.linearize_component_gen E.
congr flatten.
apply: eq_map => q.
by rewrite /Transitional.linearize_proc_gen E.
Qed.

Lemma cdeW_link_comp_ok (c : Component.id)
    (S : seq (Transitional.instr * mem_tag)) :
  getm cdeW c = Some S ->
  exists M, comp_ok (c, 1, 0%Z) S M.
Proof.
case: Hprem => -[[sa [Hwfa Hca]] [sb [Hwfb Hcb]] _ _ _] _.
rewrite /Transitional.intermediate_to_transitional_gen mkfmapE.
move=> /getm_def_In HIn.
have [ES [x HInx]] := MCoh.ccl_In HIn.
have Egetm : getm (Intermediate.prog_procedures tp) c = Some x
  := MCoh.In_getm HInx.
move: (Egetm). rewrite /= unionmE.
case Ea: (getm (Intermediate.prog_procedures a) c) => [xa|] /=.
- move=> [Ex]. subst xa.
  have [M HM] := MCoh.component_comp_ok PI Hca Ea.
  exists M.
  rewrite ES (@lin_gen_split a c); last by rewrite Egetm Ea.
  exact: HM.
- move=> Egb.
  have [M HM] := MCoh.component_comp_ok PI Hcb Egb.
  exists M.
  rewrite ES (@lin_gen_split b c); last by rewrite Egetm Egb.
  exact: HM.
Qed.

Lemma disch_HMM :
  exists MM : Component.id -> seq sv,
    forall c S, getm cdeW c = Some S -> comp_ok (c, 1, 0%Z) S (MM c).
Proof.
pose pick := fun c =>
  match getm cdeW c as o return (getm cdeW c = o -> seq sv) with
  | Some Sc => fun E =>
      proj1_sig (ClassicalEpsilon.constructive_indefinite_description
                   _ (cdeW_link_comp_ok E))
  | None => fun _ => [::]
  end (erefl _).
exists pick => c S E.
rewrite /pick.
move: (erefl _).
rewrite {2 3}E.
move=> E'.
exact: (proj2_sig (ClassicalEpsilon.constructive_indefinite_description
          _ (cdeW_link_comp_ok E'))).
Qed.

Theorem disch_dsy0 :
  exists MM : Component.id -> seq sv,
    (forall c S, getm cdeW c = Some S -> comp_ok (c, 1, 0%Z) S (MM c))
    /\ (forall m : finpref_behavior,
        MDefs.run_fits cdeW tp (finpref_trace m) ->
        forall ts0, S2T.TSim.TSim.t_initial_base cdeW tp ts0 ->
        mm_dsync L P C a b PB PI MM cdeW (amap0 PB) ts0
          (Merged.initial_state
             (Definitions.code (MDefs.Wme L P C a b))
             (Definitions.prog_buffers (MDefs.Wme L P C a b))
             (Definitions.prog_interface (MDefs.Wme L P C a b)))).
Proof.
have [MM HMM] := disch_HMM.
exists MM. split; first exact: HMM.
move=> m Hrf ts0 Hbase.
have Hfit4 := Hrf ts0 E0 ts0 Hbase (star_refl _ _ _)
                (ex_intro _ (finpref_trace m) (erefl _)).
case: Hfit4 => Hfit _.
case: Hbase Hfit => pcM [Hfind ->] Hfit.
have Hvf : (forall c cm b0 blk o cell,
    Transitional.Memory.prepare_procedures_initial_memory tp c
      = Some cm ->
    getm (Transitional.Memory.content cm) b0 = Some blk ->
    List.nth_error blk o = Some cell ->
    MDefs.value_fits
      (Transitional.Memory.prepare_procedures_initial_memory tp)
      (Transitional.val cell.1)).
{ by case: Hfit => _ Hmemf _. }
exists None, [::], (fun _ => [::]), Undef.
split.
- exact: (MDiscInit.dinv_initial HMM Hfind
            disch_P1 disch_P2 disch_P3 disch_P5).
- apply: sync_initial.
  + by [].
  + have Hsm := (@disch_Hsmall L P C a b Hprem).
    have Hal32 : Merged.alloc_label < 2 ^ Types.word_size Int32.mt.
    { rewrite /Merged.alloc_label Int32.word_size_mt.
      by rewrite ltn_exp2l. }
    by lia.
  + exact: (@disch_Hwfa L P C a b Hprem).
  + exact: (@disch_Hwfb L P C a b Hprem).
  + exact: (@disch_Hlinkable L P C a b Hprem).
  + exact: HMM.
  + exact: Hfind.
  + exact: Hvf.
Qed.

End Discharge2.
