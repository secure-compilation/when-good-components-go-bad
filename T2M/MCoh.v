(** * T2M disc_inv: compiler coherence for the stack-class map.

    [compile_expr_frag]: every compiled expression fragment carries a
    class map passing the fragment check, entering and leaving at
    (PBody, sg, None) (expressions have net-zero stack effect);
    assembled with MSig's frag algebra, E_if discharging promises. *)

Require Import Common.Definitions.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
Require Import Coq.micromega.Lia.

Require Import Intermediate.Machine.
Require Import MicroPolicies.Types.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import Source.Language.
Require Import S2I.CompMonad.
Require Import S2I.Definitions.
Require Import S2I.Compiler.
Require Import S2I.LabelUniq.
Require Import T2M.MSig.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* the top mid-body value (top taints + top custody), and the
   general-taint one *)
Local Notation bv sg :=
  (SV PBody sg None ADead ADead SCused true true true).
Local Notation bvt sg a b c := (SV PBody sg None a b c true true true).

(* exits weaken to the tops *)
Lemma sv_le_topt (ph : sphase) (sg : seq class3) (pd : option class3)
    (a1 a2 : taint) (c : scst) (o ek ag : bool) :
  sv_le (SV ph sg pd a1 a2 c o ek ag) (SV ph sg pd ADead ADead SCused o ek ag).
Proof.
exact: sv_le_taint (t_le_top a1) (t_le_top a2) (sc_le_top c).
Qed.

(* CU pushes preserve RA-freeness *)
Lemma nocra_rcons_u (sg : seq class3) :
  nocra sg -> nocra (rcons sg CU).
Proof. by rewrite /nocra has_rcons. Qed.

(* pushes preserve the body-baseline CArg at position 1 *)
Lemma bc_rcons (sg : seq class3) (k : class3) :
  nth_error sg 1 = Some CArg ->
  nth_error (rcons sg k) 1 = Some CArg.
Proof. by case: sg => [|x [|y r]]. Qed.

(* the emitted generic binop, at its post-pop taints *)
Lemma frag_binop_aux (scr0 : Pointer.t) (L : label -> option sv)
    (op : Values.binop) (tg : mem_tag) (sg : seq class3) (b : taint)
    (c : scst) :
  frag scr0 [:: (TrBinOp op R_AUX1 R_COM R_COM, tg)]
       [:: bvt sg AU b c] L (bvt sg AU b c) (bv sg).
Proof.
by case: op; rewrite /frag /= /frag_at /= sv_le_refl /= sv_le_topt.
Qed.

Section Coh.

Variable C0 : Component.id.
Variable lbp scr : Pointer.t.
Variable P_labels : NMap label.
Variable C : Component.id.

Local Notation tr c := (trc C c).

Theorem compile_expr_frag (e : expr) :
  forall (s : comp_env) (c : Machine.code) (s' : comp_env),
  compile_expr C0 lbp scr P_labels e s = Some (c, s') ->
  forall (sg : seq class3) (a1 a2 : taint) (sc : scst)
         (L : label -> option sv),
  nocra sg ->
  nth_error sg 1 = Some CArg ->
  exists M, frag scr (tr c) M L (bvt sg a1 a2 sc) (bv sg).
Proof.
elim: e => [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
           |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc sg a1 a2 sc L
           Hnc Hbc.
-  case: v Hc => [i|p|] //= [<- _].
  exists [:: bvt sg a1 a2 sc].
  by rewrite /frag /= /frag_at /= sv_le_refl /= sv_le_topt.
-  move: Hc => /= [<- _].
  exists [:: bvt sg a1 a2 sc].
  by rewrite /frag /= /frag_at /= sv_le_refl /= sv_le_topt.
-  move: Hc => /= [<- _].
  exists [:: bvt sg a1 a2 sc].
  by rewrite /frag /= /frag_at /= sv_le_refl /= sv_le_topt.
-  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C0 lbp scr P_labels e2 s1) => [[c2 s2]|] //=.
  move=> [<- _].
  have [M1 F1] := IH1 _ _ _ E1 sg a1 a2 sc L Hnc Hbc.
  have [M2 F2] := IH2 _ _ _ E2 (rcons sg CU) ADead ADead SCused L (nocra_rcons_u Hnc) (@bc_rcons sg CU Hbc).
  have Fp := @frag_push scr L R_COM (def_mem_tag C true)
               (def_mem_tag C true) sg ADead ADead ADead ADead SCused CU
               true (erefl _) (erefl _) (erefl _) (erefl _) (erefl _).
  have Fq := @frag_pop_u scr L R_AUX1 (def_mem_tag C true)
               (def_mem_tag C true) sg ADead ADead SCused true
               (bvt sg AU ADead SCused) isT isT isT (erefl _)
               (erefl _) (erefl _) (erefl _).
  have Fb := @frag_binop_aux scr L bop (def_mem_tag C true) sg ADead
               SCused.
  exists (M1 ++ [:: bv sg;
                    SV PBody sg (Some CU) ADead ADead SCused true true true]
             ++ M2
             ++ [:: bv (rcons sg CU);
                    SV PBody sg (Some CU) ADead ADead SCused true true true]
             ++ [:: bvt sg AU ADead SCused]).
  rewrite !trc_cat /= ?trc_cat /=.
  exact: (frag_cat F1 (frag_cat Fp (frag_cat F2 (frag_cat Fq Fb)))).
-  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C0 lbp scr P_labels e2 s1) => [[c2 s2]|] //=.
  move=> [<- _].
  have [M1 F1] := IH1 _ _ _ E1 sg a1 a2 sc L Hnc Hbc.
  have [M2 F2] := IH2 _ _ _ E2 sg ADead ADead SCused L Hnc Hbc.
  exists (M1 ++ M2).
  rewrite !trc_cat.
  exact: (frag_cat F1 F2).
-  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C0 lbp scr P_labels e2 s1) => [[c2 s2]|] //=.
  case E3: (compile_expr C0 lbp scr P_labels e3 s2) => [[c3 s3]|] //=.
  case E4: (fresh_label C0 s3) => [[lconseq s4]|] //=.
  case E5: (fresh_label C0 s4) => [[lend s5]|] //=.
  move=> [<- _].
  pose L' := fun l : label =>
    if Nat.eqb l lconseq then Some (bv sg)
    else if Nat.eqb l lend then Some (bv sg)
    else L l.
  have [M1 F1] := IH1 _ _ _ E1 sg a1 a2 sc L' Hnc Hbc.
  have [M3 F3] := IH3 _ _ _ E3 sg ADead ADead SCused L' Hnc Hbc.
  have [M2 F2] := IH2 _ _ _ E2 sg ADead ADead SCused L' Hnc Hbc.
  have Hp1 : is_true (match L' lconseq with
                      | Some w => sv_le (bv sg) w
                      | None => false
                      end).
  { by rewrite /L' PeanoNat.Nat.eqb_refl /= sv_le_refl. }
  have Hp2 : is_true (match L' lend with
                      | Some w => sv_le (bv sg) w
                      | None => false
                      end).
  { rewrite /L'.
    case: (Nat.eqb lend lconseq) => /=; first by rewrite sv_le_refl.
    by rewrite PeanoNat.Nat.eqb_refl /= sv_le_refl. }
  have Fb1 := @frag_bnz scr L' R_COM lconseq (def_mem_tag C true)
                sg ADead ADead SCused true true Hp1.
  have Fb2 := @frag_bnz scr L' R_ONE lend (def_mem_tag C true)
                sg ADead ADead SCused true true Hp2.
  have Flc := @frag_lbl scr L' lconseq (def_mem_tag C true) (bv sg).
  have Fle := @frag_lbl scr L' lend (def_mem_tag C true) (bv sg).
  have Fall := frag_cat F1 (frag_cat Fb1 (frag_cat F3 (frag_cat Fb2
                 (frag_cat Flc (frag_cat F2 Fle))))).
  have /and3P [/eqP Hsz1 _ _] := F1.
  have /and3P [/eqP Hsz3 _ _] := F3.
  have /and3P [/eqP Hsz2 _ _] := F2.
  exists (M1 ++ [:: bv sg] ++ M3 ++ [:: bv sg] ++ [:: bv sg]
             ++ M2 ++ [:: bv sg]).
  rewrite !trc_cat /= ?trc_cat /= ?trc_cat /=.
  apply: (frag_promise _ Fall).
  move=> l w.
  rewrite /L'.
  case El1: (Nat.eqb l lconseq) => /=.
  +    move=> [<-]. right.
    move/PeanoNat.Nat.eqb_eq: El1 => ->.
    have Hsz : size (M1 ++ [:: bv sg] ++ M3 ++ [:: bv sg])
               = size (tr c1
                       ++ [:: (TrBnz R_COM lconseq, def_mem_tag C true)]
                       ++ tr c3
                       ++ [:: (TrBnz R_ONE lend, def_mem_tag C true)]).
    { by rewrite !size_cat Hsz1 Hsz3. }
    have Hlc := @lbl_ok_here
      (tr c1 ++ [:: (TrBnz R_COM lconseq, def_mem_tag C true)]
             ++ tr c3
             ++ [:: (TrBnz R_ONE lend, def_mem_tag C true)])
      (tr c2 ++ [:: (TrLabel (inl lend), def_mem_tag C true)])
      (M1 ++ [:: bv sg] ++ M3 ++ [:: bv sg]) (M2 ++ [:: bv sg])
      lconseq (def_mem_tag C true) (bv sg) (sv_eqb^~ (bv sg))
      Hsz (sv_eqb_refl (bv sg)).
    rewrite -!catA in Hlc.
    exact: Hlc.
  + case El2: (Nat.eqb l lend) => /=.
    *      move=> [<-]. right.
      move/PeanoNat.Nat.eqb_eq: El2 => ->.
      have Hsz : size (M1 ++ [:: bv sg] ++ M3 ++ [:: bv sg]
                          ++ [:: bv sg] ++ M2)
                 = size (tr c1
                         ++ [:: (TrBnz R_COM lconseq, def_mem_tag C true)]
                         ++ tr c3
                         ++ [:: (TrBnz R_ONE lend, def_mem_tag C true)]
                         ++ [:: (TrLabel (inl lconseq),
                                 def_mem_tag C true)]
                         ++ tr c2).
      { by rewrite !size_cat Hsz1 Hsz3 Hsz2. }
      have Hle := @lbl_ok_here
        (tr c1 ++ [:: (TrBnz R_COM lconseq, def_mem_tag C true)]
               ++ tr c3
               ++ [:: (TrBnz R_ONE lend, def_mem_tag C true)]
               ++ [:: (TrLabel (inl lconseq), def_mem_tag C true)]
               ++ tr c2)
        [::]
        (M1 ++ [:: bv sg] ++ M3 ++ [:: bv sg] ++ [:: bv sg] ++ M2) [::]
        lend (def_mem_tag C true) (bv sg) (sv_eqb^~ (bv sg))
        Hsz (sv_eqb_refl (bv sg)).
      rewrite -!catA in Hle.
      exact: Hle.
    *      by move=> HL; left.
-  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e s) => [[c1 s1]|] //=.
  move=> [<- _].
  have [M1 F1] := IH _ _ _ E1 sg a1 a2 sc L Hnc Hbc.
  have Fa : frag scr [:: (TrAlloc R_COM R_COM, def_mem_tag C true)]
              [:: bv sg] L (bv sg) (bv sg).
  { by rewrite /frag /= /frag_at /= !sv_le_refl. }
  exists (M1 ++ [:: bv sg]).
  rewrite !trc_cat /= ?trc_cat /=.
  exact: (frag_cat F1 Fa).
-  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e s) => [[c1 s1]|] //=.
  move=> [<- _].
  have [M1 F1] := IH _ _ _ E1 sg a1 a2 sc L Hnc Hbc.
  have Fd : frag scr [:: (TrLoad R_COM R_COM, def_mem_tag C true)]
              [:: bv sg] L (bv sg) (bv sg).
  { by rewrite /frag /= /frag_at /= !sv_le_refl. }
  exists (M1 ++ [:: bv sg]).
  rewrite !trc_cat /= ?trc_cat /=.
  exact: (frag_cat F1 Fd).
-  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C0 lbp scr P_labels e2 s1) => [[c2 s2]|] //=.
  move=> [<- _].
  have [M2 F2] := IH2 _ _ _ E2 sg a1 a2 sc L Hnc Hbc.
  have [M1 F1] := IH1 _ _ _ E1 (rcons sg CU) ADead ADead SCused L (nocra_rcons_u Hnc) (@bc_rcons sg CU Hbc).
  have Fp := @frag_push scr L R_COM (def_mem_tag C true)
               (def_mem_tag C true) sg ADead ADead ADead ADead SCused CU
               true (erefl _) (erefl _) (erefl _) (erefl _) (erefl _).
  have Fq := @frag_pop_u scr L R_AUX1 (def_mem_tag C true)
               (def_mem_tag C true) sg ADead ADead SCused true
               (bvt sg AU ADead SCused) isT isT isT (erefl _)
               (erefl _) (erefl _) (erefl _).
  have Fs : frag scr [:: (TrStore R_COM R_AUX1, def_mem_tag C true);
                     (TrMov R_AUX1 R_COM, def_mem_tag C true)]
              [:: bvt sg AU ADead SCused; bvt sg AU ADead SCused] L
              (bvt sg AU ADead SCused) (bv sg).
  { by rewrite /frag /= /frag_at /= !sv_le_refl /= sv_le_topt. }
  exists (M2 ++ [:: bv sg;
                    SV PBody sg (Some CU) ADead ADead SCused true true true]
             ++ M1
             ++ [:: bv (rcons sg CU);
                    SV PBody sg (Some CU) ADead ADead SCused true true true]
             ++ [:: bvt sg AU ADead SCused; bvt sg AU ADead SCused]).
  rewrite !trc_cat /= ?trc_cat /=.
  exact: (frag_cat F2 (frag_cat Fp (frag_cat F1 (frag_cat Fq Fs)))).
-  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e s) => [[c1 s1]|] //=.
  case: (Component.eqb C' C0).
  +    case E2: (find_proc_label P_labels P' s1) => [[tl s2]|] //=.
    move=> [<- _].
    have [M1 F1] := IH _ _ _ E1 sg a1 a2 sc L Hnc Hbc.
    have Hkra : pushclass
                  (SV PBody sg None ADead ADead SCused true true true)
                  R_RA = Some CRa.
    { by rewrite /pushclass Hbc Hnc /=. }
    have Fp := @frag_push scr L R_RA (def_mem_tag C true)
                 (def_mem_tag C true) sg ADead ADead ADead ADead SCused
                 CRa true (erefl _) (erefl _) (erefl _) Hkra (erefl _).
    have Fj : frag scr [:: (TrJalNat tl, def_mem_tag C true)]
                [:: bv (rcons sg CRa)] L
                (bv (rcons sg CRa)) (bv (rcons sg CRa)).
    { have Hcra : (~~ nocra (rcons sg CRa)) = true.
      { by rewrite /nocra has_rcons /=. }
      by rewrite /frag /= /frag_at /= Hcra /= !sv_le_refl. }
    have Fq := @frag_pop_ra scr L (def_mem_tag C true)
                 (def_mem_tag C true) sg ADead ADead SCused true
                 (erefl _) (erefl _) (erefl _).
    exists (M1 ++ [:: bv sg;
                      SV PBody sg (Some CRa) ADead ADead SCused true true
                         true]
               ++ [:: bv (rcons sg CRa)]
               ++ [:: bv (rcons sg CRa);
                      SV PBody sg (Some CRa) ADead ADead SCused true true
                         true]).
    rewrite !trc_cat /= ?trc_cat /=.
    exact: (frag_cat F1 (frag_cat Fp (frag_cat Fj Fq))).
  +    move=> [<- _].
    have [M1 F1] := IH _ _ _ E1 sg a1 a2 sc L Hnc Hbc.
    have Hkra : pushclass
                  (SV PBody sg None ADead ADead SCused true true true)
                  R_RA = Some CRa.
    { by rewrite /pushclass Hbc Hnc /=. }
    have Fp1 := @frag_push scr L R_RA (def_mem_tag C true)
                  (def_mem_tag C true) sg ADead ADead ADead ADead SCused
                  CRa true (erefl _) (erefl _) (erefl _) Hkra (erefl _).
    have Fp2 := @frag_push scr L R_ARG (def_mem_tag C true)
                  (def_mem_tag C true) (rcons sg CRa)
                  ADead ADead ADead ADead SCused CU true (erefl _)
                  (erefl _) (erefl _) (erefl _) (erefl _).
    set sg2 := rcons (rcons sg CRa) CU.
    have Fsa : frag scr
                 [:: (TrConst (IPtr scr) R_AUX2, def_mem_tag C true);
                     (TrStore R_AUX2 R_SP, def_mem_tag C true)]
                 [:: bv sg2; bvt sg2 ADead AScr SCused] L
                 (bv sg2) (bvt sg2 ADead AScr SCpark).
    { rewrite /frag /= /frag_at /= ptr_eqb_refl /=.
      by rewrite !sv_le_refl. }
    have Fc : frag scr [:: (TrJalProc (C', P'), def_mem_tag C true)]
                [:: bvt sg2 ADead AScr SCpark] L
                (bvt sg2 ADead AScr SCpark)
                (SV PPost sg2 None ADead ADead SCused false true false).
    { have Hbc2 : nth1carg sg2 = true.
      { apply: nth1cargI.
        rewrite /sg2.
        exact: (@bc_rcons _ CU (@bc_rcons _ CRa Hbc)). }
      by rewrite /frag /= /frag_at /= Hbc2 /= !sv_le_refl. }
    have Fo : frag scr [:: (TrConst (IInt 1) R_ONE, def_mem_tag C true)]
                [:: SV PPost sg2 None ADead ADead SCused false true false]
                L (SV PPost sg2 None ADead ADead SCused false true false)
                (SV PPost sg2 None ADead ADead SCused true true false).
    { by rewrite /frag /= /frag_at /= !sv_le_refl. }
    have Fr : frag scr
                [:: (TrConst (IPtr scr) R_AUX2, def_mem_tag C true);
                    (TrLoad R_AUX2 R_SP, def_mem_tag C true)]
                [:: SV PPost sg2 None ADead ADead SCused true true false;
                    SV PPost sg2 None ADead AScr SCused true true false]
                L (SV PPost sg2 None ADead ADead SCused true true false)
                (SV PBody sg2 None ADead AScr SCused true true false).
    { have Hcra : (~~ nocra sg2) = true.
      { by rewrite /sg2 /nocra !has_rcons /=. }
      rewrite /frag /= /frag_at /= ptr_eqb_refl /= Hcra /=.
      by rewrite !sv_le_refl. }
    have Fq1 := @frag_pop_u scr L R_ARG (def_mem_tag C true)
                  (def_mem_tag C true) (rcons sg CRa) ADead AScr SCused
                  false (bvt (rcons sg CRa) ADead AScr SCused) isT isT
                  isT (erefl _) (erefl _) (erefl _) (erefl _).
    have Fq2 := @frag_pop_ra scr L (def_mem_tag C true)
                  (def_mem_tag C true) sg ADead AScr SCused true
                  (erefl _) (erefl _) (erefl _).
    apply: (ex_intro _ (M1
               ++ [:: bv sg;
                      SV PBody sg (Some CRa) ADead ADead SCused true true
                         true]
               ++ [:: bv (rcons sg CRa);
                      SV PBody (rcons sg CRa) (Some CU) ADead ADead
                         SCused true true true]
               ++ [:: bv sg2; bvt sg2 ADead AScr SCused]
               ++ [:: bvt sg2 ADead AScr SCpark]
               ++ [:: SV PPost sg2 None ADead ADead SCused false true
                         false]
               ++ [:: SV PPost sg2 None ADead ADead SCused true true
                         false;
                      SV PPost sg2 None ADead AScr SCused true true
                         false]
               ++ [:: SV PBody sg2 None ADead AScr SCused true true
                         false;
                      SV PBody (rcons sg CRa) (Some CU) ADead AScr
                         SCused true true false]
               ++ [:: bvt (rcons sg CRa) ADead AScr SCused;
                      SV PBody sg (Some CRa) ADead AScr SCused true true
                         true])).
    rewrite !trc_cat /= ?trc_cat /= if_same.
    apply: (frag_wout (vout := bvt sg ADead AScr SCused)).
    * exact: sv_le_topt.
    * exact: (frag_cat F1 (frag_cat Fp1 (frag_cat Fp2 (frag_cat Fsa
               (frag_cat Fc (frag_cat Fo (frag_cat Fr
               (frag_cat Fq1 Fq2)))))))).
-  move: Hc => /= [<- _].
  exists [:: bvt sg a1 a2 sc].
  by rewrite /frag /= /frag_at /= sv_le_refl.
Qed.

Arguments compile_expr_frag [e s c s'] _ sg a1 a2 sc L _ _.

(* ------------------------------------------------------------------ *)
(* The whole-procedure spine.                                         *)
(* ------------------------------------------------------------------ *)

(* the non-main wrapper (external entry) as an I-level literal *)
Local Notation wrapNM sz pl :=
  ([:: IConst (IInt 1) R_ONE; IMov R_SP R_AUX1;
       IConst (IInt sz) R_SP; IAlloc R_SP R_SP;
       IStore R_SP R_AUX1; IBinOp Add R_SP R_ONE R_SP;
       IConst (IPtr scr) R_AUX1; ILoad R_AUX1 R_AUX1;
       IStore R_SP R_AUX1; IBinOp Add R_SP R_ONE R_SP;
       IStore R_SP R_RA; IBinOp Add R_SP R_ONE R_SP;
       IJal pl;
       IBinOp Minus R_SP R_ONE R_SP; ILoad R_SP R_RA;
       IBinOp Minus R_SP R_ONE R_SP; ILoad R_SP R_AUX1;
       IConst (IPtr scr) R_AUX2; IStore R_AUX2 R_AUX1;
       IBinOp Minus R_SP R_ONE R_SP; ILoad R_SP R_SP;
       IReturn]).
(* the internal-entry head *)
Local Notation ihead sz pl :=
  ([:: ILabel pl; IMov R_SP R_AUX1;
       IConst (IInt sz) R_SP; IAlloc R_SP R_SP;
       IStore R_SP R_AUX1; IBinOp Add R_SP R_ONE R_SP;
       IStore R_SP R_ARG; IBinOp Add R_SP R_ONE R_SP;
       IMov R_COM R_ARG]).
(* the internal-entry head minus its label *)
Local Notation iheadRest sz :=
  ([:: IMov R_SP R_AUX1;
       IConst (IInt sz) R_SP; IAlloc R_SP R_SP;
       IStore R_SP R_AUX1; IBinOp Add R_SP R_ONE R_SP;
       IStore R_SP R_ARG; IBinOp Add R_SP R_ONE R_SP;
       IMov R_COM R_ARG]).
(* the body tail *)
Local Notation itail :=
  ([:: IBinOp Minus R_SP R_ONE R_SP; ILoad R_SP R_ARG;
       IBinOp Minus R_SP R_ONE R_SP; ILoad R_SP R_SP;
       IJump]).
(* the main wrapper *)
Local Notation wrapM sz pl lm lr :=
  ([:: IConst (IInt 1) R_ONE; IMov R_SP R_AUX1;
       IConst (IInt sz) R_SP; IAlloc R_SP R_SP;
       IStore R_SP R_AUX1; IBinOp Add R_SP R_ONE R_SP;
       IConst (IPtr scr) R_AUX1; ILoad R_AUX1 R_AUX1;
       IStore R_SP R_AUX1; IBinOp Add R_SP R_ONE R_SP;
       IStore R_SP R_RA; IBinOp Add R_SP R_ONE R_SP;
       IConst (IPtr (Pointer.add scr 1)) R_AUX1; ILoad R_AUX1 R_AUX2;
       IStore R_SP R_AUX2; IBinOp Add R_SP R_ONE R_SP;
       IBnz R_AUX2 lm;
       IConst (IInt 0) R_COM;
       ILabel lm;
       IConst (IInt 1) R_AUX2;
       IStore R_AUX1 R_AUX2;
       IJal pl;
       IBinOp Minus R_SP R_ONE R_SP; ILoad R_SP R_ARG;
       IBinOp Minus R_SP R_ONE R_SP; ILoad R_SP R_RA;
       IBinOp Minus R_SP R_ONE R_SP; ILoad R_SP R_AUX1;
       IConst (IPtr scr) R_AUX2; IStore R_AUX2 R_AUX1;
       IBinOp Minus R_SP R_ONE R_SP; ILoad R_SP R_SP;
       IBnz R_ARG lr;
       IHalt;
       ILabel lr;
       IReturn]).

(* the explicit class maps for the wrappers (mkmap would jam simpl:
   a vstep stuck on [ptr_eqb scr scr] would duplicate the tail into
   both match branches) *)
Local Notation mapNM :=
  ([:: sv0;
       SV PProlA [::] None ADead ADead SCnone true false false;
       SV PProlB [::] None ASp ADead SCnone true false false;
       SV PProlB [::] None ASp ADead SCnone true false false;
       SV PBody [::] None ASp ADead SCnone true false false;
       SV PBody [::] (Some CSp) ADead ADead SCnone true false false;
       SV PBody [:: CSp] None ADead ADead SCnone true false false;
       SV PBody [:: CSp] None AScr ADead SCnone true false false;
       SV PBody [:: CSp] None ASp ADead SCnone true false false;
       SV PBody [:: CSp] (Some CSp) ADead ADead SCnone true false false;
       SV PBody [:: CSp; CSp] None ADead ADead SCnone true false false;
       SV PBody [:: CSp; CSp] (Some CRa) ADead ADead SCnone true false false;
       SV PBody [:: CSp; CSp; CRa] None ADead ADead SCnone true false false;
       SV PBody [:: CSp; CSp; CRa] None ADead ADead SCused true false false;
       SV PBody [:: CSp; CSp] (Some CRa) ADead ADead SCused true false false;
       SV PBody [:: CSp; CSp] None ADead ADead SCused true false false;
       SV PBody [:: CSp] (Some CSp) ADead ADead SCused true false false;
       SV PBody [:: CSp] None ASp ADead SCused true false false;
       SV PBody [:: CSp] None ASp AScr SCused true false false;
       SV PBody [:: CSp] None ASp AScr SCrest true false false;
       SV PBody [::] (Some CSp) ADead AScr SCrest true false false;
       SV PTear [::] None ADead AScr SCrest true false false]).
Local Notation mapM :=
  ([:: sv0;
       SV PProlA [::] None ADead ADead SCnone true false false;
       SV PProlB [::] None ASp ADead SCnone true false false;
       SV PProlB [::] None ASp ADead SCnone true false false;
       SV PBody [::] None ASp ADead SCnone true false false;
       SV PBody [::] (Some CSp) ADead ADead SCnone true false false;
       SV PBody [:: CSp] None ADead ADead SCnone true false false;
       SV PBody [:: CSp] None AScr ADead SCnone true false false;
       SV PBody [:: CSp] None ASp ADead SCnone true false false;
       SV PBody [:: CSp] (Some CSp) ADead ADead SCnone true false false;
       SV PBody [:: CSp; CSp] None ADead ADead SCnone true false false;
       SV PBody [:: CSp; CSp] (Some CRa) ADead ADead SCnone true false false;
       SV PBody [:: CSp; CSp; CRa] None ADead ADead SCnone true false false;
       SV PBody [:: CSp; CSp; CRa] None AFlag ADead SCnone true false false;
       SV PBody [:: CSp; CSp; CRa] None AFlag AU SCnone true false false;
       SV PBody [:: CSp; CSp; CRa] (Some CU) AFlag ADead SCnone true false false;
       SV PBody [:: CSp; CSp; CRa; CU] None AFlag ADead SCnone true false false;
       SV PBody [:: CSp; CSp; CRa; CU] None AFlag ADead SCnone true false false;
       SV PBody [:: CSp; CSp; CRa; CU] None AFlag ADead SCnone true false false;
       SV PBody [:: CSp; CSp; CRa; CU] None AFlag ADead SCnone true false false;
       SV PBody [:: CSp; CSp; CRa; CU] None AFlag AU SCnone true false false;
       SV PBody [:: CSp; CSp; CRa; CU] None AFlag AU SCnone true false false;
       SV PBody [:: CSp; CSp; CRa; CU] None ADead ADead SCused true false false;
       SV PBody [:: CSp; CSp; CRa] (Some CU) ADead ADead SCused true false false;
       SV PBody [:: CSp; CSp; CRa] None ADead ADead SCused true false true;
       SV PBody [:: CSp; CSp] (Some CRa) ADead ADead SCused true false true;
       SV PBody [:: CSp; CSp] None ADead ADead SCused true false true;
       SV PBody [:: CSp] (Some CSp) ADead ADead SCused true false true;
       SV PBody [:: CSp] None ASp ADead SCused true false true;
       SV PBody [:: CSp] None ASp AScr SCused true false true;
       SV PBody [:: CSp] None ASp AScr SCrest true false true;
       SV PBody [::] (Some CSp) ADead AScr SCrest true false true;
       SV PTear [::] None ADead AScr SCrest true false true;
       SV PTear [::] None ADead AScr SCrest true false true;
       SV PTear [::] None ADead AScr SCrest true false true;
       SV PTear [::] None ADead AScr SCrest true false true]).

Theorem compile_proc_frag (P : Procedure.id) (e : expr) :
  forall (s : comp_env) (c : Machine.code) (s' : comp_env),
  compile_proc C0 lbp scr P_labels P e s = Some (c, s') ->
  forall (L : label -> option sv),
  exists M,
    frag scr (tr c) M L sv0 sv0 /\
    (forall pl', getm P_labels P = Some pl' ->
       lbl_ok (tr c) M pl' (fun w => sv_eqb w sv0_one)).
Proof.
move=> s c s' Hc L.
move: Hc; rewrite /compile_proc.
cbv beta iota delta [Monads.bind Monads.ret compilation_monad
  CompMonad.Comp.bind CompMonad.Comp.ret].
case E0: (find_proc_label P_labels P s) => [[pl s0]|] //=.
case E1: (fresh_label C0 s0) => [[lmain s1]|] //=.
case E2: (fresh_label C0 s1) => [[lreturn s2]|] //=.
case E3: (compile_expr C0 lbp scr P_labels e s2) => [[pc0 s3]|] //=.
set sz := Z.of_nat (4 + stack_need e).
have Hne : Nat.eqb lmain lreturn = false.
{ have [-> _] := fresh_label_inv E1.
  have [-> Hb] := fresh_label_inv E2.
  have [_ ->] := fresh_label_inv E1.
  apply/PeanoNat.Nat.eqb_neq. by lia. }
have Hne' : Nat.eqb lreturn lmain = false.
{ have [-> _] := fresh_label_inv E1.
  have [-> Hb] := fresh_label_inv E2.
  have [_ ->] := fresh_label_inv E1.
  apply/PeanoNat.Nat.eqb_neq. by lia. }
have Epl0 : getm P_labels P = Some pl.
{ move: E0. rewrite /find_proc_label /Comp.lift.
  by case: (getm P_labels P) => [x|] // [->]. }
have Escr : ptr_eqb scr scr = true := ptr_eqb_refl scr.
have Efl : ptr_eqb (Pointer.add scr 1) scr = false.
{ case: (scr) => [[c0 b0] o0].
  rewrite /ptr_eqb /=.
  have -> : Z.eqb (o0 + 1) o0 = false by apply/Z.eqb_neq; lia.
  by rewrite !andbF. }
have Efl' : ptr_eqb (Pointer.add scr 1) (Pointer.add scr 1) = true
  := ptr_eqb_refl _.
have [MC FC] := compile_expr_frag E3 [:: CSp; CArg] ADead ADead
                  SCnone L isT (erefl _).
have FB : frag scr (tr (ihead sz pl))
            (mkmap scr sv0_one (tr (ihead sz pl)))
            L sv0_one (bvt [:: CSp; CArg] ADead ADead SCnone).
{ by []. }
have FD : frag scr (tr itail)
            (mkmap scr (bv [:: CSp; CArg]) (tr itail)) L
            (bv [:: CSp; CArg]) sv0.
{ by []. }
case: (Component.eqb C0 Component.main
       && Procedure.eqb P Procedure.main) => /=;
case: (immediately_final e) => /=;
move=> [<- _].
-  have FA : frag scr (tr (IHalt :: wrapM sz pl lmain lreturn))
              (sv0 :: mapM) L sv0 sv0_one.
  { rewrite /frag /= /frag_at /lbl_ok /lbl_at /=
       !Escr ?Efl ?Efl' ?PeanoNat.Nat.eqb_refl ?Hne ?Hne' /=.
    by []. }
  exists ((sv0 :: mapM)
          ++ mkmap scr sv0_one (tr (ihead sz pl))
          ++ MC
          ++ mkmap scr (bv [:: CSp; CArg]) (tr itail)).
  split.
  + rewrite /= ?trc_cat /= ?trc_cat /=.
    exact: (frag_cat FA (frag_cat FB (frag_cat FC FD))).
  + move=> pl' Epl'.
    have Epl : pl' = pl by move: Epl'; rewrite Epl0 => -[].
    subst pl'.
    rewrite /= ?trc_cat /= ?trc_cat /=.
    have Hsz : size ((sv0 :: mapM) : seq sv)
               = size (tr (IHalt :: wrapM sz pl lmain lreturn))
      := erefl _.
    have HL := @lbl_ok_here
      (tr (IHalt :: wrapM sz pl lmain lreturn))
      (tr (iheadRest sz) ++ (tr pc0 ++ tr itail))
      ((sv0 :: mapM))
      (mkmap scr sv0_one (tr (iheadRest sz))
         ++ (MC ++ mkmap scr (bv [:: CSp; CArg]) (tr itail)))
      pl (def_mem_tag C true) sv0_one (sv_eqb^~ sv0_one)
      Hsz (sv_eqb_refl sv0_one).
    exact: HL.
-  have FA : frag scr (tr (wrapM sz pl lmain lreturn))
              mapM L sv0 sv0_one.
  { rewrite /frag /= /frag_at /lbl_ok /lbl_at /=
       !Escr ?Efl ?Efl' ?PeanoNat.Nat.eqb_refl ?Hne ?Hne' /=.
    by []. }
  exists (mapM
          ++ mkmap scr sv0_one (tr (ihead sz pl))
          ++ MC
          ++ mkmap scr (bv [:: CSp; CArg]) (tr itail)).
  split.
  + rewrite /= ?trc_cat /= ?trc_cat /=.
    exact: (frag_cat FA (frag_cat FB (frag_cat FC FD))).
  + move=> pl' Epl'.
    have Epl : pl' = pl by move: Epl'; rewrite Epl0 => -[].
    subst pl'.
    rewrite /= ?trc_cat /= ?trc_cat /=.
    have Hsz : size (mapM : seq sv)
               = size (tr (wrapM sz pl lmain lreturn))
      := erefl _.
    have HL := @lbl_ok_here
      (tr (wrapM sz pl lmain lreturn))
      (tr (iheadRest sz) ++ (tr pc0 ++ tr itail))
      (mapM)
      (mkmap scr sv0_one (tr (iheadRest sz))
         ++ (MC ++ mkmap scr (bv [:: CSp; CArg]) (tr itail)))
      pl (def_mem_tag C true) sv0_one (sv_eqb^~ sv0_one)
      Hsz (sv_eqb_refl sv0_one).
    exact: HL.
-  have FA : frag scr (tr (wrapNM sz pl)) mapNM L sv0 sv0_one.
  { rewrite /frag /= /frag_at /= !Escr /=.
    by []. }
  exists (mapNM
          ++ mkmap scr sv0_one (tr (ihead sz pl))
          ++ MC
          ++ mkmap scr (bv [:: CSp; CArg]) (tr itail)).
  split.
  + rewrite /= ?trc_cat /= ?trc_cat /=.
    exact: (frag_cat FA (frag_cat FB (frag_cat FC FD))).
  + move=> pl' Epl'.
    have Epl : pl' = pl by move: Epl'; rewrite Epl0 => -[].
    subst pl'.
    rewrite /= ?trc_cat /= ?trc_cat /=.
    have Hsz : size (mapNM : seq sv)
               = size (tr (wrapNM sz pl))
      := erefl _.
    have HL := @lbl_ok_here
      (tr (wrapNM sz pl))
      (tr (iheadRest sz) ++ (tr pc0 ++ tr itail))
      (mapNM)
      (mkmap scr sv0_one (tr (iheadRest sz))
         ++ (MC ++ mkmap scr (bv [:: CSp; CArg]) (tr itail)))
      pl (def_mem_tag C true) sv0_one (sv_eqb^~ sv0_one)
      Hsz (sv_eqb_refl sv0_one).
    exact: HL.
-  have FA : frag scr (tr (wrapNM sz pl)) mapNM L sv0 sv0_one.
  { rewrite /frag /= /frag_at /= !Escr /=.
    by []. }
  exists (mapNM
          ++ mkmap scr sv0_one (tr (ihead sz pl))
          ++ MC
          ++ mkmap scr (bv [:: CSp; CArg]) (tr itail)).
  split.
  + rewrite /= ?trc_cat /= ?trc_cat /=.
    exact: (frag_cat FA (frag_cat FB (frag_cat FC FD))).
  + move=> pl' Epl'.
    have Epl : pl' = pl by move: Epl'; rewrite Epl0 => -[].
    subst pl'.
    rewrite /= ?trc_cat /= ?trc_cat /=.
    have Hsz : size (mapNM : seq sv)
               = size (tr (wrapNM sz pl))
      := erefl _.
    have HL := @lbl_ok_here
      (tr (wrapNM sz pl))
      (tr (iheadRest sz) ++ (tr pc0 ++ tr itail))
      (mapNM)
      (mkmap scr sv0_one (tr (iheadRest sz))
         ++ (MC ++ mkmap scr (bv [:: CSp; CArg]) (tr itail)))
      pl (def_mem_tag C true) sv0_one (sv_eqb^~ sv0_one)
      Hsz (sv_eqb_refl sv0_one).
    exact: HL.
Qed.

(* compiled procedures end terminally (the trailing IJump) *)
Lemma compile_proc_ends (P : Procedure.id) (e : expr) :
  forall (s : comp_env) (c : Machine.code) (s' : comp_env),
  compile_proc C0 lbp scr P_labels P e s = Some (c, s') ->
  ends_term (tr c).
Proof.
move=> s c s' Hc.
move: Hc; rewrite /compile_proc.
cbv beta iota delta [Monads.bind Monads.ret compilation_monad
  CompMonad.Comp.bind CompMonad.Comp.ret].
case E0: (find_proc_label P_labels P s) => [[pl s0]|] //=.
case E1: (fresh_label C0 s0) => [[lmain s1]|] //=.
case E2: (fresh_label C0 s1) => [[lreturn s2]|] //=.
case E3: (compile_expr C0 lbp scr P_labels e s2) => [[pc0 s3]|] //=.
case: (Component.eqb C0 Component.main
       && Procedure.eqb P Procedure.main) => /=;
case: (immediately_final e) => /=;
move=> [<- _];
rewrite /= ?trc_cat /=;
do !(apply: ends_term_cons; first by []);
(apply: ends_term_cons; first by case: (tr pc0));
apply: ends_term_catr; by [].
Qed.

(* compiled procedures are nonempty *)
Lemma compile_proc_nonempty (P : Procedure.id) (e : expr) :
  forall (s : comp_env) (c : Machine.code) (s' : comp_env),
  compile_proc C0 lbp scr P_labels P e s = Some (c, s') ->
  c <> [::].
Proof.
move=> s c s' Hc.
move: Hc; rewrite /compile_proc.
cbv beta iota delta [Monads.bind Monads.ret compilation_monad
  CompMonad.Comp.bind CompMonad.Comp.ret].
case E0: (find_proc_label P_labels P s) => [[pl s0]|] //=.
case E1: (fresh_label C0 s0) => [[lmain s1]|] //=.
case E2: (fresh_label C0 s1) => [[lreturn s2]|] //=.
case E3: (compile_expr C0 lbp scr P_labels e s2) => [[pc0 s3]|] //=.
case: (Component.eqb C0 Component.main
       && Procedure.eqb P Procedure.main) => /=;
case: (immediately_final e) => /=;
by move=> [<- _].
Qed.

(* ---- the Jal inventory: every emitted IJal targets a P_labels
   entry ---- *)

Definition jalbad (i0 : Machine.instr) : bool :=
  if i0 is IJal l
  then ~~ has (fun kv => Nat.eqb kv.2 l) (elementsm P_labels)
  else false.

(* a successful find_proc_label yields a range member *)
Lemma find_proc_range (P : Procedure.id) (l : label) (s s' : comp_env) :
  find_proc_label P_labels P s = Some (l, s') ->
  has (fun kv => Nat.eqb kv.2 l) (elementsm P_labels).
Proof.
move=> E0.
have EG : getm P_labels P = Some l.
{ move: E0. rewrite /find_proc_label /Comp.lift.
  by case: (getm P_labels P) => [x|] // [->]. }
have HIn : List.In (P, l) (elementsm P_labels) := getm_def_In EG.
have In_has : forall (A : Type) (pr : A -> bool) (y : A) (s0 : seq A),
    List.In y s0 -> pr y -> has pr s0.
{ move=> A pr y s0. elim: s0 => [|z s0 IH] //= [->|Hin0] Hp.
  - by rewrite Hp.
  - by rewrite (IH Hin0 Hp) orbT. }
apply: In_has HIn _.
by rewrite /= PeanoNat.Nat.eqb_refl.
Qed.

Lemma compile_expr_jalok (e : expr) :
  forall (s : comp_env) (c : Machine.code) (s' : comp_env),
  compile_expr C0 lbp scr P_labels e s = Some (c, s') ->
  ~~ has jalbad c.
Proof.
elim: e => [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
           |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc.
- by case: v Hc => [i|p|] //= [<- _].
- by move: Hc => /= [<- _].
- by move: Hc => /= [<- _].
- move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C0 lbp scr P_labels e2 s1) => [[c2 s2]|] //=.
  move=> [<- _].
  by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
     (negbTE (IH1 _ _ _ E1)) (negbTE (IH2 _ _ _ E2)).
- move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C0 lbp scr P_labels e2 s1) => [[c2 s2]|] //=.
  move=> [<- _].
  by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
     (negbTE (IH1 _ _ _ E1)) (negbTE (IH2 _ _ _ E2)).
- move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C0 lbp scr P_labels e2 s1) => [[c2 s2]|] //=.
  case E3: (compile_expr C0 lbp scr P_labels e3 s2) => [[c3 s3]|] //=.
  case E4: (fresh_label C0 s3) => [[lconseq s4]|] //=.
  case E5: (fresh_label C0 s4) => [[lend s5]|] //=.
  move=> [<- _].
  by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
     (negbTE (IH1 _ _ _ E1)) (negbTE (IH2 _ _ _ E2))
     (negbTE (IH3 _ _ _ E3)).
- move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e s) => [[c1 s1]|] //=.
  move=> [<- _].
  by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
     (negbTE (IH _ _ _ E1)).
- move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e s) => [[c1 s1]|] //=.
  move=> [<- _].
  by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
     (negbTE (IH _ _ _ E1)).
- move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e1 s) => [[c1 s1]|] //=.
  case E2: (compile_expr C0 lbp scr P_labels e2 s1) => [[c2 s2]|] //=.
  move=> [<- _].
  by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
     (negbTE (IH1 _ _ _ E1)) (negbTE (IH2 _ _ _ E2)).
-  move: Hc; rewrite /= /Comp.bind /Comp.ret.
  case E1: (compile_expr C0 lbp scr P_labels e s) => [[c1 s1]|] //=.
  case: (Component.eqb C' C0).
  + case E2: (find_proc_label P_labels P' s1) => [[tl s2]|] //=.
    move=> [<- _].
    rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
       (negbTE (IH _ _ _ E1)) /=.
    by rewrite /jalbad (find_proc_range E2).
  + move=> [<- _].
    by rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
       (negbTE (IH _ _ _ E1)).
- by move: Hc => /= [<- _].
Qed.

Lemma compile_proc_jalok (P : Procedure.id) (e : expr) :
  forall (s : comp_env) (c : Machine.code) (s' : comp_env),
  compile_proc C0 lbp scr P_labels P e s = Some (c, s') ->
  ~~ has jalbad c.
Proof.
move=> s c s' Hc.
move: Hc; rewrite /compile_proc.
cbv beta iota delta [Monads.bind Monads.ret compilation_monad
  CompMonad.Comp.bind CompMonad.Comp.ret].
case E0: (find_proc_label P_labels P s) => [[pl s0]|] //=.
case E1: (fresh_label C0 s0) => [[lmain s1]|] //=.
case E2: (fresh_label C0 s1) => [[lreturn s2]|] //=.
case E3: (compile_expr C0 lbp scr P_labels e s2) => [[pc0 s3]|] //=.
case: (Component.eqb C0 Component.main
       && Procedure.eqb P Procedure.main) => /=;
case: (immediately_final e) => /=;
move=> [<- _];
rewrite /= !has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
   ?has_cat /= ?has_cat /= ?has_cat /= ?has_cat /=
   (negbTE (compile_expr_jalok E3)) /=;
by rewrite /jalbad (find_proc_range E0).
Qed.

End Coh.

(* ------------------------------------------------------------------ *)
(* The component-level origin: ONE label map for all of a             *)
(* component's procedures.                                            *)
(* ------------------------------------------------------------------ *)

(* the gen-fold's domain: only listed procedures get labels *)
Lemma gen_labels_aux_keys (comp : Component.id)
    (ps : list (Procedure.id * expr)) :
  forall (acc : NMap label) (s : comp_env) (m : NMap label)
         (s' : comp_env),
  gen_component_procedures_labels_aux comp acc ps s = Some (m, s') ->
  forall P, P \in domm m -> (P \in domm acc) \/ (P \in unzip1 ps).
Proof.
elim: ps => [|[P0 e0] ps IH] acc s m s' /=.
- rewrite /Comp.ret. move=> [<- _] P HP. by left.
- rewrite /Comp.bind.
  case E1: (fresh_label comp s) => [[l1 s1]|] //=.
  move=> Hrest P HP.
  have [Hacc | Hps] := IH _ _ _ _ Hrest _ HP.
  + move: Hacc. rewrite domm_set in_fsetU1.
    case/orP => [/eqP ->|Hacc'].
    * right. by rewrite /= mem_head.
    * by left.
  + right. by rewrite /= in_cons Hps orbT.
Qed.

Lemma gen_all_labels_keys (cs : list (Component.id * NMap expr)) :
  forall (acc : NMap (NMap label)) (s : comp_env)
         (ml : NMap (NMap label)) (s' : comp_env),
  gen_all_procedures_labels_aux acc cs s = Some (ml, s') ->
  uniq (unzip1 cs) ->
  forall (C : Component.id) (Cprocs : NMap expr) (plm : NMap label),
    List.In (C, Cprocs) cs ->
    getm ml C = Some plm ->
    forall P, P \in domm plm -> P \in unzip1 (elementsm Cprocs).
Proof.
elim: cs => [|[C0 Cprocs0] cs IH] acc s ml s' //=.
rewrite /Comp.bind.
case Eg: (gen_component_procedures_labels C0 (elementsm Cprocs0) s)
  => [[m0 s1]|]; last by [].
rewrite /=.
move=> Hrest /andP [Hnotin Huniq] C Cprocs plm HIn Hml P HP.
case: HIn => [Ehead | HIn'].
- case: Ehead => EC ECp. subst C0 Cprocs0.
  have Eml : getm ml C = Some m0.
  { rewrite (gen_all_labels_aux_untouched _ _ _ _ _ _ Hrest Hnotin).
    by rewrite setmE eqxx. }
  have Em0 : plm = m0 by move: Hml; rewrite Eml => -[].
  subst plm.
  have [Hacc | Hps] := gen_labels_aux_keys Eg HP; last by [].
  by move: Hacc; rewrite domm0 in_fset0.
- exact: (IH _ _ _ _ Hrest Huniq _ _ _ HIn' Hml _ HP).
Qed.

Theorem compiled_component_origin (p : Source.program)
    (tp : Intermediate.program) :
  compile_program p = Some tp ->
  forall (C : Component.id) (Cprocs : NMap Machine.code),
    Intermediate.prog_procedures tp C = Some Cprocs ->
    exists plm : NMap label,
      (forall (P : Procedure.id) (cd : Machine.code),
         getm Cprocs P = Some cd ->
         exists (e : expr) (s0 s1 : comp_env),
           compile_proc C (C, 0, 0%Z) (C, 1, 0%Z) plm P e s0
           = Some (cd, s1))
      /\ (forall P', P' \in domm plm -> P' \in domm Cprocs).
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
rewrite /Comp.ret. move=> [<-] C Cprocs /=.
move=> Hget.
have Hin_cs : C \in unzip1 (elementsm (Source.prog_procedures p)).
{ case Ein: (C \in unzip1 (elementsm (Source.prog_procedures p))) => //.
  have := compile_components_aux_untouched _ _ _ _ _ _ _ _ Ec (negbT Ein).
  move: Hget. rewrite mkfmapE => -> //. }
have [Cprocs_src HIn] := mem_unzip1_In Hin_cs.
have Huniq_cs := uniq_unzip1_elementsm (Source.prog_procedures p).
have [plm [sC [cds [sC' [Hpls Hloc Hcp Hout]]]]]
  := compile_components_aux_getC _ _ _ _ _ _ _ _ _ Ec Huniq_cs HIn.
have Ecp' : Cprocs = mkfmap cds.
{ move: Hget. rewrite mkfmapE Hout. by move=> [->]. }
subst Cprocs.
exists plm. split.
- move=> P cd.
  rewrite mkfmapE => /getm_def_In HInP.
  have [HInnil | [e [s0 [s1 Hcpc]]]]
    := compile_procedures_aux_origin Hcp HInP; first by [].
  by exists e, s0, s1.
- move=> P' HP'.
  have Hsrc : P' \in unzip1 (elementsm Cprocs_src).
  { exact: (gen_all_labels_keys Eg Huniq_cs HIn Hpls HP'). }
  have Hperm := compile_procedures_aux_keys Hcp.
  have Hcds : P' \in unzip1 cds.
  { rewrite (perm_mem Hperm) mem_cat Hsrc //. }
  by rewrite domm_mkfmap.
Qed.

(* List.In to ssr membership on nat-like seqs, and back *)
Lemma In_mem (T : eqType) (s : seq T) (x : T) :
  List.In x s -> x \in s.
Proof.
elim: s => [|y s IH] //= [->|Hx]; first exact: mem_head.
by rewrite in_cons IH // orbT.
Qed.

Lemma mem_In (T : eqType) (s : seq T) (x : T) :
  x \in s -> List.In x s.
Proof.
elim: s => [|y s IH] //=.
rewrite in_cons => /orP [/eqP ->|Hx]; first by left.
by right; exact: IH.
Qed.

(* the whole linearized component carries a passing class map *)
Theorem component_frag (p : Source.program) (tp : Intermediate.program)
    (PI : Program.interface) (C : Component.id)
    (Cprocs : NMap Machine.code) :
  compile_program p = Some tp ->
  Intermediate.prog_procedures tp C = Some Cprocs ->
  exists M,
    frag (C, 1, 0%Z) (linearize_component_gen PI tp C) M
      (fun _ => None) sv0 sv0.
Proof.
move=> Hcomp Hget.
have [plm [Horig Hdom]] := compiled_component_origin Hcomp Hget.
rewrite /linearize_component_gen Hget /=.
apply: frag_flatten => pc /List.in_map_iff [P [Epc HInP]].
have HP : P \in domm Cprocs := In_mem HInP.
move: HP. rewrite mem_domm.
case EP: (Cprocs P) => [cd|] // _.
have [e [s0 [s1 Hcp]]] := Horig _ _ EP.
have [Mp [Fp _]] := compile_proc_frag C Hcp (fun _ => None).
exists (sv0 :: Mp).
rewrite -Epc /linearize_proc_gen Hget /= EP /=.
have Fh := @frag_hdr (C, 1, 0%Z) (fun _ => None) (C, P)
             (head_tag_gen PI C P).
exact: (frag_cat Fh Fp).
Qed.

(* the full component package: the frag, the shared origin, and the
   entry-label witnesses transported to the component level *)
Theorem component_full (p : Source.program) (tp : Intermediate.program)
    (PI : Program.interface) (C : Component.id)
    (Cprocs : NMap Machine.code) :
  compile_program p = Some tp ->
  Intermediate.prog_procedures tp C = Some Cprocs ->
  exists (plm : NMap label) (M : seq sv),
    [/\ frag (C, 1, 0%Z) (linearize_component_gen PI tp C) M
          (fun _ => None) sv0 sv0,
        (forall P cd, getm Cprocs P = Some cd ->
           exists (e : expr) (s0 s1 : comp_env),
             compile_proc C (C, 0, 0%Z) (C, 1, 0%Z) plm P e s0
             = Some (cd, s1)),
        (forall P', P' \in domm plm -> P' \in domm Cprocs)
      & (forall P' pl', P' \in domm Cprocs ->
           getm plm P' = Some pl' ->
           lbl_ok (linearize_component_gen PI tp C) M pl'
             (fun w => sv_eqb w sv0_one))].
Proof.
move=> Hcomp Hget.
have [plm [Horig Hdom]] := compiled_component_origin Hcomp Hget.
exists plm.
have Hfold : forall ps : seq Procedure.id,
    (forall P, List.In P ps -> P \in domm Cprocs) ->
    exists M,
      frag (C, 1, 0%Z) (flatten (map (linearize_proc_gen PI tp C) ps)) M
        (fun _ => None) sv0 sv0
      /\ (forall P' pl', List.In P' ps -> getm plm P' = Some pl' ->
            lbl_ok (flatten (map (linearize_proc_gen PI tp C) ps)) M
              pl' (fun w => sv_eqb w sv0_one)).
{ elim=> [|P ps IH] Hsub.
  - exists [::]. split; first exact: frag_nil.
    by move=> ? ? [].
  - have HP : P \in domm Cprocs := Hsub P (or_introl (erefl _)).
    have [M2 [F2 HL2]] := IH (fun q Hq => Hsub q (or_intror Hq)).
    move: HP. rewrite mem_domm. case EP: (Cprocs P) => [cd|] // _.
    have [e [s0 [s1 Hcp]]] := Horig _ _ EP.
    have [Mp [Fp HLp]] := compile_proc_frag C Hcp (fun _ => None).
    have Fh := @frag_hdr (C, 1, 0%Z) (fun _ => None) (C, P)
             (head_tag_gen PI C P).
    have Fpiece : frag (C, 1, 0%Z) (linearize_proc_gen PI tp C P)
                    (sv0 :: Mp) (fun _ => None) sv0 sv0.
    { rewrite /linearize_proc_gen Hget /= EP /=.
      exact: (frag_cat Fh Fp). }
    exists ((sv0 :: Mp) ++ M2).
    split; first exact: (frag_cat Fpiece F2).
    move=> P' pl' HIn Epl'.
    have Hszp : size (sv0 :: Mp) = size (linearize_proc_gen PI tp C P).
    { by case/and3P: Fpiece => /eqP -> _ _. }
    case: HIn => [EPP | HIn'].
    + subst P'.
      have HLo := HLp _ Epl'.
      have HLo' : lbl_ok (linearize_proc_gen PI tp C P) (sv0 :: Mp)
                    pl' (fun w => sv_eqb w sv0_one).
      { rewrite /linearize_proc_gen Hget /= EP /=.
        exact: (lbl_ok_catr (c1 := [:: (TrLabel (inr (C, P)),
                                        head_tag_gen PI C P)])
                  (M1 := [:: sv0]) (erefl _) HLo). }
      exact: (lbl_ok_catl _ _ Hszp HLo').
    + have HLr := HL2 _ _ HIn' Epl'.
      exact: (lbl_ok_catr Hszp HLr).
}
have [M [FM HLM]] := Hfold (domm Cprocs)
                       (fun P HIn => In_mem HIn).
exists M.
rewrite /linearize_component_gen Hget /=.
split=> //.
move=> P' pl' HP' Epl'.
apply: HLM Epl'.
exact: mem_In HP'.
Qed.

(* the In-to-getm converse (keys are unique in an fmap's elements) *)
Lemma In_getm (A : Type) (m : NMap A) (k : nat) (v : A) :
  List.In (k, v) (elementsm m) -> getm m k = Some v.
Proof.
move=> HIn.
have Huniq : uniq (unzip1 (elementsm m)) := uniq_unzip1_elementsm m.
have Hgen : forall (s2 : seq (nat * A)),
    uniq (unzip1 s2) -> List.In (k, v) s2 -> getm_def s2 k = Some v.
{ elim=> [|[k0 v0] s2 IH] //= /andP [Hk0 Hu] [E|HIn'].
  - case: E => -> ->. by rewrite eqxx.
  - case Ek: (k == k0).
    + exfalso. move/eqP: Ek => Ek. subst k0.
      have Hk : k \in unzip1 s2.
      { have HmIn : List.In k (unzip1 s2)
          := List.in_map fst _ _ HIn'.
        exact: In_mem HmIn. }
      by rewrite Hk in Hk0.
    + exact: IH. }
rewrite -[in LHS](fmvalK m) mkfmapE.
exact: Hgen Huniq HIn.
Qed.

(* ...and ends terminally *)
Theorem component_ends (p : Source.program) (tp : Intermediate.program)
    (PI : Program.interface) (C : Component.id)
    (Cprocs : NMap Machine.code) :
  compile_program p = Some tp ->
  Intermediate.prog_procedures tp C = Some Cprocs ->
  ends_term (linearize_component_gen PI tp C).
Proof.
move=> Hcomp Hget.
have [plm [Horig Hdom]] := compiled_component_origin Hcomp Hget.
rewrite /linearize_component_gen Hget /=.
apply: ends_term_flatten => pc /List.in_map_iff [P [Epc HInP]].
have HP : P \in domm Cprocs := In_mem HInP.
move: HP. rewrite mem_domm.
case EP: (Cprocs P) => [cd|] // _.
have [e [s0 [s1 Hcp]]] := Horig _ _ EP.
rewrite -Epc /linearize_proc_gen Hget /= EP /=.
apply: ends_term_cons.
- have Hne := compile_proc_nonempty Hcp.
  by case: cd Hne {EP Hcp}.
- exact: compile_proc_ends Hcp.
Qed.

(* the component check itself: the Jal obligation discharged *)
Theorem component_comp_ok (p : Source.program)
    (tp : Intermediate.program) (PI : Program.interface)
    (C : Component.id) (Cprocs : NMap Machine.code) :
  compile_program p = Some tp ->
  Intermediate.prog_procedures tp C = Some Cprocs ->
  exists M, comp_ok (C, 1, 0%Z) (linearize_component_gen PI tp C) M.
Proof.
move=> Hcomp Hget.
have [plm [M [FM Horig Hdom HL]]] := component_full PI Hcomp Hget.
exists M.
apply: (comp_ok_of_frag FM).
- exact: (component_ends PI Hcomp Hget).
-  move=> n l tg Hn.
  have HInFlat : List.In (TrJalNat l, tg)
                   (linearize_component_gen PI tp C)
    := List.nth_error_In _ _ Hn.
  have In_flat : forall (A : Type) (x : A) (ss : seq (seq A)),
      List.In x (flatten ss) ->
      exists s0, List.In s0 ss /\ List.In x s0.
  { move=> A x. elim=> [|s0 ss IH] //= HIn.
    have := List.in_app_or _ _ _ HIn.
    case=> [Hx | Hrec]; first by exists s0; split; [left|].
    have [s1 [Hs1 Hx1]] := IH Hrec.
    by exists s1; split; [right|]. }
  move: HInFlat. rewrite {1}/linearize_component_gen Hget /=.
  move=> HInFlat2.
  have [piece [Hpiece HInpc]] := In_flat _ _ _ HInFlat2.
  move: Hpiece => /List.in_map_iff [P [Epc HInP]].
  have HP : P \in domm Cprocs := In_mem HInP.
  move: HP. rewrite mem_domm. case EP: (Cprocs P) => [cd|] // _.
  move: HInpc. rewrite -Epc /linearize_proc_gen Hget /= EP /=.
  case=> [Ehdr | HIncd]; first by [].  have [i0 [Ei0 HIn0]] : exists i0,
      instr_to_transitional C i0 = (TrJalNat l, tg) /\ List.In i0 cd.
  { move: HIncd => /List.in_map_iff [i0 [Ei0 HIn0]].
    by exists i0; split. }
  have El : i0 = IJal l.
  { case: i0 Ei0 {HIn0} =>
      [|l0|v0 r0|ra' rb'|op0 ra' rb' rc'|ra' rb'|ra' rb'|ra' rb'
       |r0 l0| |l0|c0' P0| |] //=.
    - by move=> [->].
    - by move=> E; move: E; case: (Nat.eqb C c0') => -[].
  }
  subst i0.  have [e [s0 [s1 Hcp]]] := Horig _ _ EP.
  have Hjok := compile_proc_jalok Hcp.
  have In_has : forall (A : Type) (pr : A -> bool) (y : A)
                       (s2 : seq A),
      List.In y s2 -> pr y -> has pr s2.
  { move=> A pr y s2. elim: s2 => [|z s2 IH] //= [->|Hin0] Hp.
    - by rewrite Hp.
    - by rewrite (IH Hin0 Hp) orbT. }
  have Hrange : has (fun kv => Nat.eqb kv.2 l) (elementsm plm).
  { case Hr: (has (fun kv => Nat.eqb kv.2 l) (elementsm plm)) => //.
    have Hbad : jalbad plm (IJal l) by rewrite /jalbad Hr.
    have := In_has _ _ _ _ HIn0 Hbad.
    by rewrite (negbTE Hjok). }
  case/hasP: Hrange => [[P'' l'']] Hmem /= /PeanoNat.Nat.eqb_eq El''.
  subst l''.
  have Egetm : getm plm P'' = Some l
    := In_getm (mem_In Hmem).
  have HP'' : P'' \in domm Cprocs.
  { apply: Hdom. by rewrite mem_domm Egetm. }
  exact: (HL _ _ HP'' Egetm).
Qed.

(* the linearizer's component list, inverted *)
Lemma ccl_In (PI : Program.interface) (cenv : Intermediate.program)
    (T : Type) (l : list (Component.id * T)) (c : Component.id) S :
  List.In (c, S) (compile_component_list_gen PI cenv l) ->
  S = linearize_component_gen PI cenv c /\ exists x, List.In (c, x) l.
Proof.
elim: l => [|[c0 t0] l IH] //= [E|HIn'].
- case: E => -> ->. split=> //. by exists t0; left.
- have [ES [x HInx]] := IH HIn'.
  split=> //. by exists x; right.
Qed.

(* comp_ok at the real linearized code *)
Theorem cdeW_comp_ok (p : Source.program) (tp : Intermediate.program)
    (PI : Program.interface) (c : Component.id)
    (S : seq (Transitional.instr * mem_tag)) :
  compile_program p = Some tp ->
  getm (intermediate_to_transitional_gen PI tp) c = Some S ->
  exists M, comp_ok (c, 1, 0%Z) S M.
Proof.
move=> Hcomp.
rewrite /intermediate_to_transitional_gen mkfmapE => /getm_def_In HIn.
have [ES [x HInx]] := ccl_In HIn.
subst S.
have Egetm : getm (Intermediate.prog_procedures tp) c = Some x
  := In_getm HInx.
exact: (component_comp_ok PI Hcomp Egetm).
Qed.

(* the per-component maps, packaged by (classical) choice *)
Theorem cdeW_maps (p : Source.program) (tp : Intermediate.program)
    (PI : Program.interface) :
  compile_program p = Some tp ->
  exists MM : Component.id -> seq sv,
    forall c S, getm (intermediate_to_transitional_gen PI tp) c = Some S ->
      comp_ok (c, 1, 0%Z) S (MM c).
Proof.
move=> Hcomp.
pose pick := fun c =>
  match getm (intermediate_to_transitional_gen PI tp) c
        as o return (getm (intermediate_to_transitional_gen PI tp) c = o
                     -> seq sv)
  with
  | Some Sc => fun E =>
      proj1_sig (ClassicalEpsilon.constructive_indefinite_description
                   _ (cdeW_comp_ok Hcomp E))
  | None => fun _ => [::]
  end (erefl _).
exists pick => c S E.
rewrite /pick.
move: (erefl _).
rewrite {2 3}E.
move=> E'.
exact: (proj2_sig (ClassicalEpsilon.constructive_indefinite_description
          _ (cdeW_comp_ok Hcomp E'))).
Qed.
