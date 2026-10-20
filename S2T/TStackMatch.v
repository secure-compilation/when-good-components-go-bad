Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import Intermediate.Machine.
Require Import S2I.Compiler.
Require Import S2I.Definitions.
Require Import S2I.SimInject.
Require Import S2I.Simulation.
Require Import MicroPolicies.LRC.
Require Import MicroPolicies.Transitional.
Require Import S2T.TSem.
Require Import S2T.TMem.
Require Import S2T.TInv.
Require Import S2T.TInject.
Require Import S2T.TStack.
Require Import S2T.TMacros.

Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fmap fset.

Require Import Coq.ZArith.ZArith.
From mathcomp Require Import zify.
Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.

Module TSM.

Notation mem := Transitional.Memory.t.


Inductive ext_frame_match (cde : Transitional.code) (m : mem)
                          (C : Component.id)
  : Block.id -> Pointer.t -> Z -> TStack.ra_slot -> Prop :=
| EF_std : forall fbE jal_ret v0 v1 s,
    Pointer.component jal_ret = C ->
    TMacros.code_at_I cde C jal_ret
      (pop R_RA ++ pop R_AUX1 ++ store_arg (scr C) R_AUX1 R_AUX2
         ++ pop R_SP ++ [:: IReturn]) ->
    TMem.vload m (C, fbE, 0%Z) = Some v0 ->
    TMem.vload m (C, fbE, 1%Z) = Some v1 ->
    TMem.tload m (C, fbE, 0%Z) = Some Other ->
    TMem.tload m (C, fbE, 1%Z) = Some Other ->
    TStack.ra_addr s = (C, fbE, 2%Z) ->
    TStack.slots_ok m [:: s] ->
    ext_frame_match cde m C fbE jal_ret 3%Z s
| EF_main : forall fbE jal_ret lret v0 v1 s z,
    Pointer.component jal_ret = C ->
    TMacros.code_at_I cde C jal_ret
      (pop R_ARG ++ pop R_RA ++ pop R_AUX1
         ++ store_arg (scr C) R_AUX1 R_AUX2
         ++ pop R_SP ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn]) ->
    TMem.vload m (C, fbE, 0%Z) = Some v0 ->
    TMem.vload m (C, fbE, 1%Z) = Some v1 ->
    TMem.tload m (C, fbE, 0%Z) = Some Other ->
    TMem.tload m (C, fbE, 1%Z) = Some Other ->
    TStack.ra_addr s = (C, fbE, 2%Z) ->
    TStack.slots_ok m [:: s] ->
    TMem.vload m (C, fbE, 3%Z) = Some (Int z) ->
    TMem.tload m (C, fbE, 3%Z) = Some Other ->
    z <> 0%Z ->
    ext_frame_match cde m C fbE jal_ret 4%Z s.

Lemma ext_frame_match_transport cde m m' C fbE jal_ret spE s :
  ext_frame_match cde m C fbE jal_ret spE s ->
  (forall (o : Z) w, TMem.vload m (C, fbE, o) = Some w ->
     TMem.vload m' (C, fbE, o) = Some w) ->
  (forall (o : Z) t, TMem.tload m (C, fbE, o) = Some t ->
     TMem.tload m' (C, fbE, o) = Some t) ->
  TStack.slots_ok m' [:: s] ->
  ext_frame_match cde m' C fbE jal_ret spE s.
Proof.
  move=> H Ltr Ttr Hs. case: H Ltr Ttr Hs.
  - move=> fbE0 jal_ret0 v0 v1 s0 Hc Hcode L0 L1 T0 T1 Ea Hs0 Ltr Ttr Hs.
    by apply: EF_std Hc Hcode (Ltr _ _ L0) (Ltr _ _ L1) (Ttr _ _ T0)
                     (Ttr _ _ T1) Ea Hs.
  - move=> fbE0 jal_ret0 lret v0 v1 s0 z Hc Hcode L0 L1 T0 T1 Ea Hs0 L3 T3 Hz
      Ltr Ttr Hs.
    by apply: EF_main Hc Hcode (Ltr _ _ L0) (Ltr _ _ L1) (Ttr _ _ T0)
                      (Ttr _ _ T1) Ea Hs (Ltr _ _ L3) (Ttr _ _ T3) Hz.
Qed.

Lemma ext_frame_cases cde m C fbE jal_ret spE s :
  ext_frame_match cde m C fbE jal_ret spE s ->
  (exists v0 v1,
     [/\ spE = 3%Z,
         TMacros.code_at_I cde C jal_ret
           (pop R_RA ++ pop R_AUX1 ++ store_arg (scr C) R_AUX1 R_AUX2
              ++ pop R_SP ++ [:: IReturn]),
         TMem.vload m (C, fbE, 0%Z) = Some v0
         /\ TMem.vload m (C, fbE, 1%Z) = Some v1
       & TMem.tload m (C, fbE, 0%Z) = Some Other
         /\ TMem.tload m (C, fbE, 1%Z) = Some Other])
  \/ (exists lret v0 v1 z,
        [/\ spE = 4%Z,
            TMacros.code_at_I cde C jal_ret
              (pop R_ARG ++ pop R_RA ++ pop R_AUX1
                 ++ store_arg (scr C) R_AUX1 R_AUX2
                 ++ pop R_SP
                 ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn]),
            TMem.vload m (C, fbE, 0%Z) = Some v0
            /\ TMem.vload m (C, fbE, 1%Z) = Some v1
            /\ TMem.vload m (C, fbE, 3%Z) = Some (Int z),
            TMem.tload m (C, fbE, 0%Z) = Some Other
            /\ TMem.tload m (C, fbE, 1%Z) = Some Other
            /\ TMem.tload m (C, fbE, 3%Z) = Some Other
          & z <> 0%Z]).
Proof.
  case=> [fbE0 jr v0 v1 s0 Hc Hcode L0 L1 T0 T1 Ea Hs0
         |fbE0 jr lret v0 v1 s0 z Hc Hcode L0 L1 T0 T1 Ea Hs0 L3 T3 Hz].
  - by left; exists v0, v1.
  - by right; exists lret, v0, v1, z.
Qed.

Lemma ext_frame_comp cde m C fbE jal_ret spE s :
  ext_frame_match cde m C fbE jal_ret spE s ->
  Pointer.component jal_ret = C.
Proof. by case. Qed.

Lemma ext_frame_slot cde m C fbE jal_ret spE s :
  ext_frame_match cde m C fbE jal_ret spE s ->
  TStack.ra_addr s = (C, fbE, 2%Z) /\ TStack.slots_ok m [:: s].
Proof. by case. Qed.

Lemma ext_frame_match_store cde m m' C fbE jal_ret spE s p c :
  ext_frame_match cde m C fbE jal_ret spE s ->
  Transitional.Memory.store m p c = Some m' ->
  (forall o : Z, (C, fbE, o) <> p) ->
  ext_frame_match cde m' C fbE jal_ret spE s.
Proof.
  move=> H Hst Hne.
  have Ltr : forall (o : Z) w, TMem.vload m (C, fbE, o) = Some w ->
             TMem.vload m' (C, fbE, o) = Some w.
  { move=> o w. by rewrite /TMem.vload (TMem.load_store_neq Hst (Hne o)). }
  have Ttr : forall (o : Z) t, TMem.tload m (C, fbE, o) = Some t ->
             TMem.tload m' (C, fbE, o) = Some t.
  { move=> o t. by rewrite /TMem.tload (TMem.load_store_neq Hst (Hne o)). }
  case: (ext_frame_slot H) => [Ea Hs].
  apply: (ext_frame_match_transport H Ltr Ttr).
  apply: (TStack.slots_ok_store _ Hst Hs).
  move=> s0 [Es|//] Eaddr. apply: (Hne 2%Z).
  by rewrite -Eaddr -Es Ea.
Qed.


Inductive stack_match (cde : Transitional.code) (labelsP : NMap (NMap label))
                      (a : renaming) (m : mem)
  : NMap value -> Component.id -> Block.id
    -> seq (Component.id * Block.id) -> S.CS.stack
    -> Pointer.t -> seq TStack.ra_slot -> Prop :=
| SM_init : forall scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1,
    TMem.vload m (Component.main, fb, 0%Z)
      = Some (Ptr (Component.main, fb_ext, 4%Z)) ->
    TMem.vload m (Component.main, fb, 1%Z) = Some vs1 ->
    TMem.tload m (Component.main, fb, 0%Z) = Some Other ->
    TMem.tload m (Component.main, fb, 1%Z) = Some Other ->
    TMem.vload m (Component.main, fb_ext, 0%Z) = Some v0 ->
    TMem.vload m (Component.main, fb_ext, 1%Z) = Some v1 ->
    TMem.tload m (Component.main, fb_ext, 0%Z) = Some Other ->
    TMem.tload m (Component.main, fb_ext, 1%Z) = Some Other ->
    TMem.vload m (Component.main, fb_ext, 2%Z) = Some vx ->
    TMem.vload m (Component.main, fb_ext, 3%Z) = Some (Int 0) ->
    TMem.tload m (Component.main, fb_ext, 3%Z) = Some Other ->
    frame_priv a Component.main fb_ext ->
    Pointer.component ret_ext = Component.main ->
    TMacros.code_at_I cde Component.main ret_ext
      (pop R_ARG ++ pop R_RA ++ pop R_AUX1
         ++ store_arg (scr Component.main) R_AUX1 R_AUX2
         ++ pop R_SP ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn]) ->
    fb <> fb_ext ->
    stack_match cde labelsP a m scrs0 Component.main fb
      [:: (Component.main, fb_ext)] [::] ret_ext [::]
| SM_internal : forall scrs C fb fb' prot stk oldarg targ k' rest' temps'
                       plm ret s Sl cap',
    getm labelsP C = Some plm ->
    Pointer.component ret = C ->
    TMacros.code_at_I cde C ret (pop R_RA ++ rest') ->
    cont_matchJ a C plm k' rest' temps' ->
    TMem.vload m (C, fb, 0%Z)
      = Some (Ptr (C, fb', Z.of_nat (2 + size temps' + 1))) ->
    TMem.vload m (C, fb, 1%Z) = Some targ ->
    TMem.tload m (C, fb, 0%Z) = Some Other ->
    TMem.tload m (C, fb, 1%Z) = Some Other ->
    val_inject a oldarg targ ->
    frame_priv a C fb' ->
    TStack.frame_temps m C fb' temps' ->
    TStack.ra_addr s = (C, fb', Z.of_nat (2 + size temps')) ->
    TStack.ra_tag s = InternalJump ->
    TStack.slots_ok m (s :: Sl) ->
    TStack.frame_cap m C fb' cap' ->
    3 + kneed k' (size temps') <= cap' ->
    (C, fb') \notin prot ->
    fb <> fb' ->
    stack_match cde labelsP a m scrs C fb' prot stk (TStack.ra_ret s) Sl ->
    stack_match cde labelsP a m scrs C fb ((C, fb') :: prot)
      (S.CS.Frame C oldarg k' :: stk) ret (s :: Sl)
| SM_external : forall scrs C C'' fb fbE spE fb'' prot stk oldarg targ
                       k'' rest'' temps'' plm'' jal_ret icall_ret vscr
                       junkARG sE s'' Sl cap'',
    C'' <> C ->
    getm labelsP C'' = Some plm'' ->
    ext_frame_match cde m C fbE jal_ret spE sE ->
    TStack.ra_ret sE = icall_ret ->
    TStack.ra_tag sE = Ret (size (TStack.ext_levels Sl)) ->
    frame_priv a C fbE ->
    TMem.vload m (C, fb, 0%Z) = Some (Ptr (C, fbE, spE)) ->
    TMem.vload m (C, fbE, 1%Z) = Some vscr ->
    TMem.vload m (C, fb, 1%Z) = Some junkARG ->
    TMem.tload m (C, fb, 0%Z) = Some Other ->
    TMem.tload m (C, fb, 1%Z) = Some Other ->
    Pointer.component icall_ret = C'' ->
    TMacros.code_at_I cde C'' icall_ret
      (IConst (IInt 1) R_ONE
         :: reload_sp (scr C'') ++ pop R_ARG ++ pop R_RA ++ rest'') ->
    cont_matchJ a C'' plm'' k'' rest'' temps'' ->
    frame_priv a C'' fb'' ->
    TStack.frame_temps m C'' fb'' temps'' ->
    TStack.ra_addr s'' = (C'', fb'', Z.of_nat (2 + size temps'')) ->
    TStack.ra_tag s'' = InternalJump ->
    TStack.slots_ok m (sE :: s'' :: Sl) ->
    TMem.vload m (C'', fb'', Z.of_nat (2 + size temps'' + 1)) = Some targ ->
    TMem.tload m (C'', fb'', Z.of_nat (2 + size temps'' + 1)) = Some Other ->
    val_inject a oldarg targ ->
    TStack.frame_cap m C'' fb'' cap'' ->
    3 + kneed k'' (size temps'') <= cap'' ->
    getm scrs C''
      = Some (Ptr (C'', fb'', Z.of_nat (2 + size temps'' + 2))) ->
    (C'', fb'') \notin prot ->
    (C, fbE) \notin ((C'', fb'') :: prot) ->
    fb <> fbE ->
    stack_match cde labelsP a m (setm scrs C vscr) C'' fb'' prot stk
      (TStack.ra_ret s'') Sl ->
    stack_match cde labelsP a m scrs C fb
      ((C, fbE) :: (C'', fb'') :: prot)
      (S.CS.Frame C'' oldarg k'' :: stk) jal_ret (sE :: s'' :: Sl).

Lemma stack_match_slots cde lP a m scrs C fb prot stk ret Sl :
  stack_match cde lP a m scrs C fb prot stk ret Sl ->
  TStack.slots_ok m Sl.
Proof.
  case.
  - move=> *. by move=> x [].
  - move=> *. assumption.
  - move=> *. assumption.
Qed.

Lemma stack_match_slots_prot cde lP a m scrs C0 fb0 prot stk ret Sl :
  stack_match cde lP a m scrs C0 fb0 prot stk ret Sl ->
  forall s, List.In s Sl ->
    (Pointer.component (TStack.ra_addr s), Pointer.block (TStack.ra_addr s))
    \in prot.
Proof.
  elim=> {C0 fb0 prot stk ret Sl scrs}.
  -
    by move=> *; contradiction.
  -
    move=> scrs C fb fb' prot stk oldarg targ k' rest' temps' plm ret s Sl cap'
      _ _ _ _ _ _ _ _ _ _ _ Es _ _ _ _ _ _ _ IH s0 [Es0|Hin].
    + by rewrite -Es0 Es /= in_cons eqxx.
    + by rewrite in_cons; apply/orP; right; exact: IH.
  -
    move=> scrs C C'' fb fbE spE fb'' prot stk oldarg targ k'' rest'' temps''
      plm'' jal_ret icall_ret vscr junkARG sE s'' Sl cap''
      _ _ Hext _ _ _ _ _ _ _ _ _ _ _ _ _ Es'' _ _ _ _ _ _ _ _ _ _ _ _ IH s0.
    case=> [EsE|[Es2|Hin]].
    + case: (ext_frame_slot Hext) => [EaE _].
      by rewrite -EsE EaE /= in_cons eqxx.
    + rewrite -Es2 Es'' /= !in_cons.
      by apply/orP; right; apply/orP; left; rewrite eqxx.
    + rewrite !in_cons. apply/orP; right. apply/orP; right. exact: IH.
Qed.

Lemma memory_load_alloc_eq ms C n ms' bs (j : Z) :
  Common.Memory.Memory.alloc ms C n = Some (ms', (C, bs, 0%Z)) ->
  Common.Memory.Memory.load ms' (C, bs, j)
  = (if ((0 <=? j) && (j <? Z.of_nat n))%Z then Some Undef else None).
Proof.
  rewrite /Common.Memory.Memory.alloc /Common.Memory.Memory.load.
  case E1: (getm ms C) => [cms|] //.
  case E2: (ComponentMemory.alloc cms n) => [cms' b0] [<- E3] /=.
  rewrite setmE eqxx -E3.
  exact: (ComponentMemory.load_after_alloc_eq _ _ _ _ E2).
Qed.

Lemma minj_alloc_ext a ms mt C n ms' bs :
  TInject.minj a ms mt ->
  Common.Memory.Memory.alloc ms C n = Some (ms', (C, bs, 0%Z)) ->
  exists mt' bt,
    [/\ Transitional.Memory.alloc mt C n = Some (mt', (C, bt, 0%Z)),
        rle a (extend a C bs bt),
        (forall (o : Z) w,
           Transitional.Memory.load mt (C, bt, o) = Some w -> False)
      & TInject.minj (extend a C bs bt) ms' mt'].
Proof.
  move=> HI Hal.
  have [cms [cms' [Ecms [Ecal Ems']]]] :
    exists cms cms', [/\ getm ms C = Some cms,
                        ComponentMemory.alloc cms n = (cms', bs)
                      & ms' = setm ms C cms'].
  { move: Hal. rewrite /Common.Memory.Memory.alloc.
    case E1: (getm ms C) => [cms|] //=.
    case E2: (ComponentMemory.alloc cms n) => [cms0 b0] [<- E3].
    by exists cms, cms0; rewrite E3 in E2 *. }
  case: (TInject.mj_domm HI Ecms) => [cmt Ecmt].
  have [mt' [bt Halt]] :
    exists mt' bt, Transitional.Memory.alloc mt C n = Some (mt', (C, bt, 0%Z)).
  { rewrite /Transitional.Memory.alloc Ecmt /=. by eexists; eexists. }
  have Hfresht := TStack.alloc_fresh_unloadable HI Halt.
  have Hbtfresh : forall b0, a C b0 <> Some bt
    by exact: (TInject.alloc_fresh_outside HI Halt).
  have Hbs : bs \notin ComponentMemory.domm cms
    by exact: (ComponentMemory.alloc_fresh _ _ _ _
                 (TInject.mj_wf_s HI Ecms) Ecal).
  have Hbsl : bs != Block.local.
  { apply/negP => /eqP Eloc. move: Hbs; rewrite Eloc.
    by rewrite (TInject.mj_local_s HI Ecms). }
  have Hnone : a C bs = None.
  { case E: (a C bs) => [b'|] //.
    case: (TInject.mj_dom HI E Hbsl) => [cm0 [Hcm0 Hin]].
    move: Hcm0; rewrite Ecms => -[E0]. by move: Hbs; rewrite E0 Hin. }
  have Hnew : forall Cx b0 bx, extend a C bs bt Cx b0 = Some bx ->
      a Cx b0 = Some bx \/ (Cx = C /\ b0 = bs /\ bx = bt).
  { move=> Cx b0 bx. rewrite /extend.
    case: ifP => [/andP [/eqP -> /eqP ->] [<-]|_ H]; [by right | by left]. }
  exists mt', bt. split.
  - exact: Halt.
  - exact: (extend_rle Hnone).
  - exact: Hfresht.
  - split.
    + exact: (extend_ok (TInject.mj_ok HI) Hbsl Hnone Hbtfresh).
    +
      move=> Cx b0 bx i Hab.
      case: (Hnew _ _ _ Hab) => [Hold|[EC [Eb0 Ebx]]]; last first.
      { subst Cx b0 bx.
        rewrite (TStack.vload_alloc_fresh_eq i Halt) (memory_load_alloc_eq i Hal).
        by case: (((0 <=? i) && (i <? Z.of_nat n))%Z); constructor. }
      have Hnes : (Cx, b0) <> (C, bs).
      { move=> [E1 E2]. move: Hnone. by rewrite -E1 -E2 Hold. }
      have Hnet : Pointer.component ((Cx, bx, i) : Pointer.t) <> C
               \/ Pointer.block ((Cx, bx, i) : Pointer.t)
                  <> Pointer.block ((C, bt, 0%Z) : Pointer.t).
      { rewrite /=. case: (@eqP _ Cx C) => [EC|HC]; last by left.
        right => Ebx. move: (Hbtfresh b0). by rewrite -EC -Ebx Hold. }
      rewrite /TMem.vload (TStack.load_alloc_other Halt Hnet).
      rewrite (memory_load_after_alloc _ _ _ _ _ _ _ _ Hal);
        last by move=> E; apply: Hnes; move: E => /= [-> ->].
      move: (TInject.mj_load HI i Hold). rewrite /TMem.vload.
      case: (Common.Memory.Memory.load ms (Cx, b0, i)) => [v0|];
        case: (Transitional.Memory.load mt (Cx, bx, i)) => [w1|] //=.
      exact: (val_inject_rle a (extend a C bs bt) v0 (Transitional.val w1.1)
                (extend_rle Hnone)).
    +
      move=> C0 cm0. case: (TInject.alloc_shape Halt) => [cm1 [Hcm1 _ Emt']].
      rewrite Emt' setmE. case: (C0 =P C) => [_|_];
        last exact: (TInject.mj_wf_t HI).
      move=> [<-]. exact: TInject.alloc_b_cwf (TInject.mj_wf_t HI Hcm1).
    +
      move=> C0 cm0. case: (TInject.alloc_shape Halt) => [cm1 [Hcm1 _ Emt']].
      rewrite Emt' setmE. case: (C0 =P C) => [_|_];
        last exact: (TInject.mj_local_t HI).
      move=> [<-]. rewrite TInject.alloc_b_cdomm_in.
      by apply/orP; right; exact: (TInject.mj_local_t HI Hcm1).
    +
      move=> C0 b0 b0' Hab Hb0.
      case: (TInject.alloc_shape Halt) => [cm1 [Hcm1 Ept Emt']].
      case: (Hnew _ _ _ Hab) => [Hold|[EC [Eb0 Ebx]]].
      { case: (TInject.mj_rng HI Hold Hb0) => [cm0 [Hcm0 Hin]].
        rewrite Emt' setmE. case: (C0 =P C) => [EC|_]; last by exists cm0.
        exists (Transitional.Memory.alloc_bis C cm1 n).1. split; first by [].
        rewrite TInject.alloc_b_cdomm_in. apply/orP; right.
        by move: Hcm0; rewrite EC Hcm1 => -[->]. }
      subst C0 b0 b0'. rewrite Emt' setmE eqxx.
      exists (Transitional.Memory.alloc_bis C cm1 n).1. split; first by [].
      rewrite TInject.alloc_b_cdomm_in. apply/orP; left.
      have Ebt : bt = Transitional.Memory.nextblock cm1
        by move: (f_equal Pointer.block Ept).
      by rewrite Ebt.
    +
      move=> C0 cm0. rewrite Ems' setmE. case: (C0 =P C) => [_|_];
        last exact: (TInject.mj_wf_s HI).
      move=> [<-]. exact: (ComponentMemory.wf_alloc _ _ _ _
                             (TInject.mj_wf_s HI Ecms) Ecal).
    +
      move=> C0 cm0. rewrite Ems' setmE. case: (C0 =P C) => [_|_];
        last exact: (TInject.mj_local_s HI).
      move=> [<-]. rewrite (ComponentMemory.domm_alloc_eq _ _ _ _ Ecal)
                           in_fsetU1.
      by apply/orP; right; exact: (TInject.mj_local_s HI Ecms).
    +
      move=> C0 b0 b0' Hab Hb0.
      case: (Hnew _ _ _ Hab) => [Hold|[EC [Eb0 Ebx]]].
      { case: (TInject.mj_dom HI Hold Hb0) => [cm0 [Hcm0 Hin]].
        rewrite Ems' setmE. case: (C0 =P C) => [EC|_]; last by exists cm0.
        exists cms'. split; first by [].
        rewrite (ComponentMemory.domm_alloc_eq _ _ _ _ Ecal) in_fsetU1.
        apply/orP; right. by move: Hcm0; rewrite EC Ecms => -[->]. }
      subst C0 b0 b0'. rewrite Ems' setmE eqxx.
      exists cms'. split; first by [].
      rewrite (ComponentMemory.domm_alloc_eq _ _ _ _ Ecal) in_fsetU1.
      by apply/orP; left.
    +
      move=> C0 cm0. rewrite Ems' setmE.
      case: (TInject.alloc_shape Halt) => [cm1 [Hcm1 _ Emt']].
      rewrite Emt' setmE.
      case: (C0 =P C) => [_|_]; first by move=> _; eexists.
      move=> HC0. exact: (TInject.mj_domm HI HC0).
    +
      move=> C0 b0 b0' i w Hab.
      case: (Hnew _ _ _ Hab) => [Hold|[EC [Eb0 Ebx]]]; last first.
      { subst C0 b0 b0' => Hl.
        have Ht : TMem.tload mt' (C, bt, i) = Some (tvtag w.1)
          by rewrite /TMem.tload Hl.
        exact: (TStack.tload_alloc_in_fresh Halt Ht). }
      have Hnet : Pointer.component ((C0, b0', i) : Pointer.t) <> C
               \/ Pointer.block ((C0, b0', i) : Pointer.t)
                  <> Pointer.block ((C, bt, 0%Z) : Pointer.t).
      { rewrite /=. case: (@eqP _ C0 C) => [EC|HC]; last by left.
        right => Ebx. move: (Hbtfresh b0). by rewrite -EC -Ebx Hold. }
      rewrite (TStack.load_alloc_other Halt Hnet).
      exact: (TInject.mj_data HI Hold).
Qed.

Lemma stack_match_nosite_rng cde lP a m scrs C0 fb0 prot stk ret Sl
      Cx b0 bx (i : Z) :
  stack_match cde lP a m scrs C0 fb0 prot stk ret Sl ->
  a Cx b0 = Some bx ->
  ~ List.In (TInv.CMem (Cx, bx, i)) (TInv.sites (TStack.ledger_of Sl)).
Proof.
  move=> Hsm Hab. move: Hsm Hab.
  elim=> {C0 fb0 prot stk ret Sl scrs}.
  - move=> scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
    by rewrite /TInv.sites /TStack.ledger_of /=.
  - move=> scrs1 C fb fb' prot1 stk1 oldarg targ k' rest' temps' plm ret1 s Sl1
      cap' _ _ _ _ _ _ _ _ _ Hpriv _ Es _ _ _ _ _ _ _ IH Hab.
    rewrite /TInv.sites /TStack.ledger_of /= => -[E|Hin];
      last exact: IH Hab Hin.
    have Ea : TStack.ra_addr s = (Cx, bx, i) by congruence.
    move: Ea; rewrite Es => -[EC Eb _].
    by move: (proj2 Hpriv b0); rewrite EC Eb; apply.
  - move=> scrs1 C C'' fb fbE spE fb'' prot1 stk1 oldarg targ k'' rest'' temps''
      plm'' jal_ret icall_ret vscr junkARG sE s'' Sl1 cap''
      _ _ Hext _ _ HprivE _ _ _ _ _ _ _ _ Hpriv2 _ Es'' _ _ _ _ _ _ _ _ _ _ _ _
      IH Hab.
    rewrite /TInv.sites /TStack.ledger_of /= => -[EE|[E2|Hin]];
      last exact: IH Hab Hin.
    + case: (ext_frame_slot Hext) => [EaE _].
      have Ea : TStack.ra_addr sE = (Cx, bx, i) by congruence.
      move: Ea; rewrite EaE => -[EC Eb _].
      by move: (proj2 HprivE b0); rewrite EC Eb; apply.
    + have Ea : TStack.ra_addr s'' = (Cx, bx, i) by congruence.
      move: Ea; rewrite Es'' => -[EC Eb _].
      by move: (proj2 Hpriv2 b0); rewrite EC Eb; apply.
Qed.

Lemma stack_match_rng_notin_prot cde lP a m scrs C0 fb0 prot stk ret Sl
      Cx b0 bx :
  stack_match cde lP a m scrs C0 fb0 prot stk ret Sl ->
  a Cx b0 = Some bx -> (Cx, bx) \notin prot.
Proof.
  move=> Hsm Hab. move: Hsm Hab.
  elim=> {C0 fb0 prot stk ret Sl scrs}.
  - move=> scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1
      _ _ _ _ _ _ _ _ _ _ _ HprivE _ _ _ Hab.
    apply/negP. case/orP => [/eqP E|]; last by [].
    case: E => EC Eb. by move: Hab; rewrite EC Eb; exact: (proj2 HprivE b0).
  - move=> scrs1 C fb fb' prot1 stk1 oldarg targ k' rest' temps' plm ret1 s Sl1
      cap' _ _ _ _ _ _ _ _ _ Hpriv _ _ _ _ _ _ _ _ _ IH Hab.
    apply/negP. case/orP => [/eqP E|Hin]; last first.
    { move: (IH Hab) => /negP H. exact: (H Hin). }
    case: E => EC Eb. by move: Hab; rewrite EC Eb; exact: (proj2 Hpriv b0).
  - move=> scrs1 C C'' fb fbE spE fb'' prot1 stk1 oldarg targ k'' rest'' temps''
      plm'' jal_ret icall_ret vscr junkARG sE s'' Sl1 cap''
      _ _ _ _ _ HprivE _ _ _ _ _ _ _ _ Hpriv2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ IH
      Hab.
    apply/negP. case/orP => [/eqP E|].
    { case: E => EC Eb. by move: Hab; rewrite EC Eb; exact: (proj2 HprivE b0). }
    case/orP => [/eqP E|Hin];
      last by move: (IH Hab) => /negP H; exact: (H Hin).
    case: E => EC Eb. by move: Hab; rewrite EC Eb; exact: (proj2 Hpriv2 b0).
Qed.

Lemma stack_match_nosite cde lP a m scrs C0 fb0 prot stk ret Sl :
  stack_match cde lP a m scrs C0 fb0 prot stk ret Sl ->
  (C0, fb0) \notin prot ->
  forall o : Z,
    ~ List.In (TInv.CMem (C0, fb0, o)) (TInv.sites (TStack.ledger_of Sl)).
Proof.
  move=> Hsm Hnp o. rewrite TStack.sites_ledger_of /TStack.addrs.
  move=> /List.in_map_iff [p [Ep Hin]].
  move: Hin => /List.in_map_iff [s [Es Hs]].
  have Ep' : p = (C0, fb0, o) by congruence.
  move: (stack_match_slots_prot Hsm Hs).
  rewrite Es Ep' /= => Hmem.
  by move: Hnp; rewrite Hmem.
Qed.

Lemma slots_ok_cons m x Sl :
  TStack.slots_ok m (x :: Sl) -> TStack.slots_ok m Sl.
Proof. by move=> H y Hin; apply: H; right. Qed.

Lemma stack_match_same cde lP a m m' scrs C0 fb0 prot stk ret Sl :
  (forall q, TMem.vload m' q = TMem.vload m q) ->
  (forall q, TMem.tload m' q = TMem.tload m q) ->
  stack_match cde lP a m scrs C0 fb0 prot stk ret Sl ->
  stack_match cde lP a m' scrs C0 fb0 prot stk ret Sl.
Proof.
  move=> Hv Ht Hsm.
  have Hs : forall S, TStack.slots_ok m S -> TStack.slots_ok m' S.
  { move=> S H s Hin. case: (H s Hin) => [H1 H2]. by rewrite Hv Ht. }
  have Hf : forall Cx bx tps, TStack.frame_temps m Cx bx tps ->
      TStack.frame_temps m' Cx bx tps.
  { move=> Cx bx tps H i Hi. by rewrite Hv Ht; exact: H Hi. }
  have Hc : forall Cx bx cp, TStack.frame_cap m Cx bx cp ->
      TStack.frame_cap m' Cx bx cp.
  { move=> Cx bx cp H j Hj. case: (H j Hj) => [w Hw]. by exists w; rewrite Hv. }
  have He : forall Cx fbE jr sp s, ext_frame_match cde m Cx fbE jr sp s ->
      ext_frame_match cde m' Cx fbE jr sp s.
  { move=> Cx fbE jr sp s H.
    apply: (ext_frame_match_transport H).
    - move=> o w Hw. by rewrite Hv.
    - move=> o t Ht0. by rewrite Ht.
    - by apply: Hs; case: (ext_frame_slot H). }
  elim: Hsm.
  - move=> scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1 L0 L1 T0 T1 E0 E1 E2 E3
      HprivE Hrc Hcode Hne.
    by apply: SM_init; rewrite ?Hv ?Ht; eassumption.
  - move=> scrs1 C fb fb' prot1 stk1 oldarg targ k' rest' temps' plm ret1 s Sl1
      cap' Hplm Hpc Hcode Hcont L0 L1 T0 T1 Hinj Hpriv Htemps Ea Etg Hslots Hcap
      Hbud Hprot Hne IH IH'.
    apply: SM_internal; try eassumption.
    + by rewrite Hv; exact: L0.
    + by rewrite Hv; exact: L1.
    + by rewrite Ht; exact: T0.
    + by rewrite Ht; exact: T1.
    + exact: Hf Htemps.
    + exact: Hs Hslots.
    + exact: Hc Hcap.
  - move=> scrs1 C C'' fb fbE spE fb'' prot1 stk1 oldarg targ k'' rest'' temps''
      plm'' jal_ret icall_ret vscr junkARG sE s'' Sl1 cap''
      Hne1 Hplm Hext Hret Etag Hpriv L0 L1 L2 T0 T1 Hpc Hcode Hcont Hpriv''
      Htemps'' Ea Etg2 Hslots L3 T4 Hinj Hcap Hbud Hscr Hprot1 Hprot2 Hne2 IH
      IH'.
    apply: SM_external; try eassumption.
    + exact: He Hext.
    + by rewrite Hv; exact: L0.
    + by rewrite Hv; exact: L1.
    + by rewrite Hv; exact: L2.
    + by rewrite Ht; exact: T0.
    + by rewrite Ht; exact: T1.
    + exact: Hf Htemps''.
    + exact: Hs Hslots.
    + by rewrite Hv; exact: L3.
    + by rewrite Ht; exact: T4.
    + exact: Hc Hcap.
Qed.

Lemma stack_match_raw cde lP a m m' scrs C0 fb0 prot stk ret Sl
      (bad : Component.id * Block.id -> bool) :
  (forall q, ~~ bad (Pointer.component q, Pointer.block q) ->
     TMem.vload m' q = TMem.vload m q) ->
  (forall q, ~~ bad (Pointer.component q, Pointer.block q) ->
     TMem.tload m' q = TMem.tload m q) ->
  ~~ bad (C0, fb0) ->
  (forall p, p \in prot -> ~~ bad p) ->
  stack_match cde lP a m scrs C0 fb0 prot stk ret Sl ->
  stack_match cde lP a m' scrs C0 fb0 prot stk ret Sl.
Proof.
  move=> Hrv Hrt.
  have Lv : forall Cx bx (o : Z), ~~ bad (Cx, bx) ->
      TMem.vload m' (Cx, bx, o) = TMem.vload m (Cx, bx, o).
  { move=> Cx bx o Hb. exact: (Hrv (Cx, bx, o) Hb). }
  have Lt : forall Cx bx (o : Z), ~~ bad (Cx, bx) ->
      TMem.tload m' (Cx, bx, o) = TMem.tload m (Cx, bx, o).
  { move=> Cx bx o Hb. exact: (Hrt (Cx, bx, o) Hb). }
  move=> Hb0 Hbp Hsm. move: Hb0 Hbp.
  elim: Hsm.
  -
    move=> scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1
           L0 L1 T0 T1 E0 E1 TE0 TE1 E2 E3 TE3 Hpriv Hcret Hcode Hne Hb0 Hbp.
    have Hbe : ~~ bad (Component.main, fb_ext)
      by apply: Hbp; apply/orP; left; exact: eqxx.
    have Lv0 : forall o : Z,
        TMem.vload m' (Component.main, fb, o)
        = TMem.vload m (Component.main, fb, o) by move=> o; exact: Lv.
    have Lt0 : forall o : Z,
        TMem.tload m' (Component.main, fb, o)
        = TMem.tload m (Component.main, fb, o) by move=> o; exact: Lt.
    have Lv1 : forall o : Z,
        TMem.vload m' (Component.main, fb_ext, o)
        = TMem.vload m (Component.main, fb_ext, o) by move=> o; exact: Lv.
    have Lt1 : forall o : Z,
        TMem.tload m' (Component.main, fb_ext, o)
        = TMem.tload m (Component.main, fb_ext, o) by move=> o; exact: Lt.
    apply: (@SM_init cde lP a m' scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1).
    + by rewrite Lv0.
    + by rewrite Lv0.
    + by rewrite Lt0.
    + by rewrite Lt0.
    + by rewrite Lv1.
    + by rewrite Lv1.
    + by rewrite Lt1.
    + by rewrite Lt1.
    + by rewrite Lv1.
    + by rewrite Lv1.
    + by rewrite Lt1.
    + exact: Hpriv.
    + exact: Hcret.
    + exact: Hcode.
    + exact: Hne.
  -
    move=> scrs1 C fb fb' prot1 stk1 oldarg targ k' rest' temps' plm ret1 s Sl1
           cap' Hplm Hcret Hcode Hcont L0 L1 T0 T1 Hinj Hpriv Htemps Ea Etag
           Hslots Hcap Hbud Hnp Hne _ IH Hb0 Hbp.
    have HbC : ~~ bad (C, fb')
      by apply: Hbp; apply/orP; left; exact: eqxx.
    have Hbp' : forall p, p \in prot1 -> ~~ bad p
      by move=> p Hp; apply: Hbp; apply/orP; right.
    have Hsm' := IH HbC Hbp'.
    have Lv0 : forall o : Z,
        TMem.vload m' (C, fb, o) = TMem.vload m (C, fb, o)
      by move=> o; exact: Lv.
    have Lt0 : forall o : Z,
        TMem.tload m' (C, fb, o) = TMem.tload m (C, fb, o)
      by move=> o; exact: Lt.
    have Lv1 : forall o : Z,
        TMem.vload m' (C, fb', o) = TMem.vload m (C, fb', o)
      by move=> o; exact: Lv.
    have Lt1 : forall o : Z,
        TMem.tload m' (C, fb', o) = TMem.tload m (C, fb', o)
      by move=> o; exact: Lt.
    apply: (@SM_internal cde lP a m' scrs1 C fb fb' prot1 stk1 oldarg targ
              k' rest' temps' plm ret1 s Sl1 cap').
    + exact: Hplm.
    + exact: Hcret.
    + exact: Hcode.
    + exact: Hcont.
    + by rewrite Lv0.
    + by rewrite Lv0.
    + by rewrite Lt0.
    + by rewrite Lt0.
    + exact: Hinj.
    + exact: Hpriv.
    + by move=> i Hi; rewrite Lv1 Lt1; exact: Htemps Hi.
    + exact: Ea.
    + exact: Etag.
    + move=> s0 [Es0|Hin]; last exact: (stack_match_slots Hsm') Hin.
      have Eaa : TStack.ra_addr s0 = (C, fb', Z.of_nat (2 + size temps'))
        by rewrite -Es0.
      case: (Hslots s0 (or_introl Es0)) => [A [B D]].
      by rewrite Eaa Lv1 Lt1 -Eaa.
    + by move=> j Hj; rewrite Lv1; exact: Hcap Hj.
    + exact: Hbud.
    + exact: Hnp.
    + exact: Hne.
    + exact: Hsm'.
  -
    move=> scrs1 C C'' fb fbE spE fb'' prot1 stk1 oldarg targ k'' rest'' temps''
           plm'' jal_ret icall_ret vscr junkARG sE s'' Sl1 cap''
           HneC Hplm Hext EretE EtagE HprivE L0 LE1 L1 T0 T1 Eic Hcode Hcont
           Hpriv Htemps Ea Etag Hslots Ltarg Ttarg Hinj Hcap Hbud Hscr Hnp
           HnpE Hne _ IH Hb0 Hbp.
    have HbE : ~~ bad (C, fbE)
      by apply: Hbp; apply/orP; left; exact: eqxx.
    have HbC : ~~ bad (C'', fb'')
      by apply: Hbp; apply/orP; right; apply/orP; left; exact: eqxx.
    have Hbp' : forall p, p \in prot1 -> ~~ bad p
      by move=> p Hp; apply: Hbp; apply/orP; right; apply/orP; right.
    have Hsm' := IH HbC Hbp'.
    have Lv0 : forall o : Z,
        TMem.vload m' (C, fb, o) = TMem.vload m (C, fb, o)
      by move=> o; exact: Lv.
    have Lt0 : forall o : Z,
        TMem.tload m' (C, fb, o) = TMem.tload m (C, fb, o)
      by move=> o; exact: Lt.
    have LvE : forall o : Z,
        TMem.vload m' (C, fbE, o) = TMem.vload m (C, fbE, o)
      by move=> o; exact: Lv.
    have LtE : forall o : Z,
        TMem.tload m' (C, fbE, o) = TMem.tload m (C, fbE, o)
      by move=> o; exact: Lt.
    have Lv1 : forall o : Z,
        TMem.vload m' (C'', fb'', o) = TMem.vload m (C'', fb'', o)
      by move=> o; exact: Lv.
    have Lt1 : forall o : Z,
        TMem.tload m' (C'', fb'', o) = TMem.tload m (C'', fb'', o)
      by move=> o; exact: Lt.
    have HslE : TStack.slots_ok m' [:: sE].
    { move=> s0 [Es0|//].
      case: (ext_frame_slot Hext) => [EaE _].
      have Eaa : TStack.ra_addr s0 = (C, fbE, 2%Z) by rewrite -Es0.
      case: (Hslots s0 (or_introl Es0)) => [A [B D]].
      by rewrite Eaa LvE LtE -Eaa. }
    apply: (@SM_external cde lP a m' scrs1 C C'' fb fbE spE fb'' prot1 stk1
              oldarg targ k'' rest'' temps'' plm'' jal_ret icall_ret vscr
              junkARG sE s'' Sl1 cap'').
    + exact: HneC.
    + exact: Hplm.
    + apply: (ext_frame_match_transport Hext) => //.
      * by move=> o w Hw; rewrite LvE.
      * by move=> o t Ht; rewrite LtE.
    + exact: EretE.
    + exact: EtagE.
    + exact: HprivE.
    + by rewrite Lv0.
    + by rewrite LvE.
    + by rewrite Lv0.
    + by rewrite Lt0.
    + by rewrite Lt0.
    + exact: Eic.
    + exact: Hcode.
    + exact: Hcont.
    + exact: Hpriv.
    + by move=> i Hi; rewrite Lv1 Lt1; exact: Htemps Hi.
    + exact: Ea.
    + exact: Etag.
    + move=> s0 [Es0|[Es0|Hin]]; last exact: (stack_match_slots Hsm') Hin.
      * case: (ext_frame_slot Hext) => [EaE _].
        have Eaa : TStack.ra_addr s0 = (C, fbE, 2%Z) by rewrite -Es0.
        case: (Hslots s0 (or_introl Es0)) => [A [B D]].
        by rewrite Eaa LvE LtE -Eaa.
      * have Eaa : TStack.ra_addr s0 = (C'', fb'', Z.of_nat (2 + size temps''))
          by rewrite -Es0.
        case: (Hslots s0 (or_intror (or_introl Es0))) => [A [B D]].
        by rewrite Eaa Lv1 Lt1 -Eaa.
    + by rewrite Lv1.
    + by rewrite Lt1.
    + exact: Hinj.
    + by move=> j Hj; rewrite Lv1; exact: Hcap Hj.
    + exact: Hbud.
    + exact: Hscr.
    + exact: Hnp.
    + exact: HnpE.
    + exact: Hne.
    + exact: Hsm'.
Qed.

Lemma stack_match_prot_nonscr cde lP a m scrs C0 fb0 prot stk ret Sl :
  stack_match cde lP a m scrs C0 fb0 prot stk ret Sl ->
  forall p, p \in prot -> p.2 <> 1.
Proof.
  elim.
  - move=> scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1
           _ _ _ _ _ _ _ _ _ _ _ Hpriv _ _ _ p /orP [/eqP E|//].
    by move: E => ->; case: Hpriv.
  - move=> scrs1 C fb fb' prot1 stk1 oldarg targ k' rest' temps' plm ret1 s Sl1
           cap' _ _ _ _ _ _ _ _ _ Hpriv _ _ _ _ _ _ _ _ _ IH p
           /orP [/eqP E|Hin]; last exact: IH Hin.
    by move: E => ->; case: Hpriv.
  - move=> scrs1 C C'' fb fbE spE fb'' prot1 stk1 oldarg targ k'' rest''
           temps'' plm'' jal_ret icall_ret vscr junkARG sE s'' Sl1 cap''
           _ _ _ _ _ HprivE _ _ _ _ _ _ _ _ Hpriv
           _ _ _ _ _ _ _ _ _ _ _ _ _ _ IH p
           /orP [/eqP E|/orP [/eqP E|Hin]]; last exact: IH Hin.
    + by move: E => ->; case: HprivE.
    + by move: E => ->; case: Hpriv.
Qed.

Lemma stack_match_prot_loaded cde lP a m scrs C0 fb0 prot stk ret Sl :
  stack_match cde lP a m scrs C0 fb0 prot stk ret Sl ->
  forall p, p \in prot ->
    exists (o : Z) w, Transitional.Memory.load m (p.1, p.2, o) = Some w.
Proof.
  elim.
  - move=> scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1
           _ _ _ _ E0 _ _ _ _ _ _ _ _ _ _ p /orP [/eqP E|//].
    case: (TMem.vload_load E0) => [w Hw]. exists 0%Z, w. by rewrite E.
  - move=> scrs1 C fb fb' prot1 stk1 oldarg targ k' rest' temps' plm ret1 s Sl1
           cap' _ _ _ _ _ _ _ _ _ _ _ Ea _ Hslots _ _ _ _ _ IH p
           /orP [/eqP E|Hin]; last exact: IH Hin.
    case: (Hslots s (or_introl erefl)) => [A _]. move: A; rewrite Ea => A.
    case: (TMem.vload_load A) => [w Hw].
    exists (Z.of_nat (2 + size temps')), w. by rewrite E.
  - move=> scrs1 C C'' fb fbE spE fb'' prot1 stk1 oldarg targ k'' rest''
           temps'' plm'' jal_ret icall_ret vscr junkARG sE s'' Sl1 cap''
           _ _ _ _ _ _ _ LE1 _ _ _ _ _ _ _ _ _ _ _ Ltarg
           _ _ _ _ _ _ _ _ _ IH p
           /orP [/eqP E|/orP [/eqP E|Hin]]; last exact: IH Hin.
    + case: (TMem.vload_load LE1) => [w Hw]. exists 1%Z, w. by rewrite E.
    + case: (TMem.vload_load Ltarg) => [w Hw].
      exists (Z.of_nat (2 + size temps'' + 1)), w. by rewrite E.
Qed.

Lemma stack_match_scrs_update cde lP a m scrs C0 fb0 prot stk ret Sl w :
  stack_match cde lP a m scrs C0 fb0 prot stk ret Sl ->
  stack_match cde lP a m (setm scrs C0 w) C0 fb0 prot stk ret Sl.
Proof.
  elim.
  - move=> scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1
           L0 L1 T0 T1 E0 E1 TE0 TE1 E2 E3 TE3 Hpriv Hcret Hcode Hne.
    exact: (@SM_init cde lP a m (setm scrs0 Component.main w) fb fb_ext
              ret_ext lret v0 v1 vx vs1 L0 L1 T0 T1 E0 E1 TE0 TE1 E2 E3 TE3
              Hpriv Hcret Hcode Hne).
  - move=> scrs1 C fb fb' prot1 stk1 oldarg targ k' rest' temps' plm ret1 s Sl1
           cap' Hplm Hcret Hcode Hcont L0 L1 T0 T1 Hinj Hpriv Htemps Ea Etag
           Hslots Hcap Hbud Hnp Hne _ IH.
    exact: (@SM_internal cde lP a m (setm scrs1 C w) C fb fb' prot1 stk1
              oldarg targ k' rest' temps' plm ret1 s Sl1 cap' Hplm Hcret
              Hcode Hcont L0 L1 T0 T1 Hinj Hpriv Htemps Ea Etag Hslots Hcap
              Hbud Hnp Hne IH).
  - move=> scrs1 C C'' fb fbE spE fb'' prot1 stk1 oldarg targ k'' rest''
           temps'' plm'' jal_ret icall_ret vscr junkARG sE s'' Sl1 cap''
           HneC Hplm Hext EretE EtagE HprivE L0 LE1 L1 T0 T1 Eic Hcode Hcont
           Hpriv Htemps Ea Etag Hslots Ltarg Ttarg Hinj Hcap Hbud Hscr Hnp
           HnpE Hne Htail _.
    have Hscr' : getm (setm scrs1 C w) C''
               = Some (Ptr (C'', fb'', Z.of_nat (2 + size temps'' + 2))).
    { rewrite setmE. case: eqP => [E|_]; last exact: Hscr. by case: HneC. }
    have Htail' : stack_match cde lP a m (setm (setm scrs1 C w) C vscr)
                    C'' fb'' prot1 stk1 (TStack.ra_ret s'') Sl1
      by rewrite setmxx.
    exact: (@SM_external cde lP a m (setm scrs1 C w) C C'' fb fbE spE fb''
              prot1 stk1 oldarg targ k'' rest'' temps'' plm'' jal_ret
              icall_ret vscr junkARG sE s'' Sl1 cap'' HneC Hplm Hext EretE
              EtagE HprivE L0 LE1 L1 T0 T1 Eic Hcode Hcont Hpriv Htemps Ea
              Etag Hslots Ltarg Ttarg Hinj Hcap Hbud Hscr' Hnp HnpE Hne
              Htail').
Qed.

Lemma stack_match_scrs_extend cde lP a m scrs C0 fb0 prot stk ret Sl Cx w :
  stack_match cde lP a m scrs C0 fb0 prot stk ret Sl ->
  getm scrs Cx = None ->
  stack_match cde lP a m (setm scrs Cx w) C0 fb0 prot stk ret Sl.
Proof.
  move=> Hsm; elim: Hsm.
  - move=> scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1
           L0 L1 T0 T1 E0 E1 TE0 TE1 E2 E3 TE3 Hpriv Hcret Hcode Hne _.
    exact: (@SM_init cde lP a m (setm scrs0 Cx w) fb fb_ext
              ret_ext lret v0 v1 vx vs1 L0 L1 T0 T1 E0 E1 TE0 TE1 E2 E3 TE3
              Hpriv Hcret Hcode Hne).
  - move=> scrs1 C fb fb' prot1 stk1 oldarg targ k' rest' temps' plm ret1 s Sl1
           cap' Hplm Hcret Hcode Hcont L0 L1 T0 T1 Hinj Hpriv Htemps Ea Etag
           Hslots Hcap Hbud Hnp Hne _ IH Hnone.
    exact: (@SM_internal cde lP a m (setm scrs1 Cx w) C fb fb' prot1 stk1
              oldarg targ k' rest' temps' plm ret1 s Sl1 cap' Hplm Hcret
              Hcode Hcont L0 L1 T0 T1 Hinj Hpriv Htemps Ea Etag Hslots Hcap
              Hbud Hnp Hne (IH Hnone)).
  - move=> scrs1 C C'' fb fbE spE fb'' prot1 stk1 oldarg targ k'' rest''
           temps'' plm'' jal_ret icall_ret vscr junkARG sE s'' Sl1 cap''
           HneC Hplm Hext EretE EtagE HprivE L0 LE1 L1 T0 T1 Eic Hcode Hcont
           Hpriv Htemps Ea Etag Hslots Ltarg Ttarg Hinj Hcap Hbud Hscr Hnp
           HnpE Hne Htail IH Hnone.
    have HneX : Cx <> C''
      by move=> E; move: Hnone; rewrite E Hscr.
    have Hscr' : getm (setm scrs1 Cx w) C''
               = Some (Ptr (C'', fb'', Z.of_nat (2 + size temps'' + 2))).
    { rewrite setmE. case: eqP => [E|_]; last exact: Hscr.
      by case: HneX. }
    have Htail' : stack_match cde lP a m (setm (setm scrs1 Cx w) C vscr)
                    C'' fb'' prot1 stk1 (TStack.ra_ret s'') Sl1.
    { case: (@eqP _ Cx C) => [EX|HneXC].
      - by rewrite EX setmxx.
      - rewrite setmC; last by apply/eqP => E; apply: HneXC.
        apply: IH. rewrite setmE. case: eqP => [E|_]; last exact: Hnone.
        by case: HneXC. }
    exact: (@SM_external cde lP a m (setm scrs1 Cx w) C C'' fb fbE spE fb''
              prot1 stk1 oldarg targ k'' rest'' temps'' plm'' jal_ret
              icall_ret vscr junkARG sE s'' Sl1 cap'' HneC Hplm Hext EretE
              EtagE HprivE L0 LE1 L1 T0 T1 Eic Hcode Hcont Hpriv Htemps Ea
              Etag Hslots Ltarg Ttarg Hinj Hcap Hbud Hscr' Hnp HnpE Hne
              Htail').
Qed.

Lemma stack_match_store cde lP a m m' scrs C0 fb0 prot stk ret Sl p c :
  stack_match cde lP a m scrs C0 fb0 prot stk ret Sl ->
  Transitional.Memory.store m p c = Some m' ->
  (Pointer.component p, Pointer.block p) \notin prot ->
  ((Pointer.component p, Pointer.block p) = (C0, fb0) ->
     (2 <= Pointer.offset p)%Z) ->
  TStack.slots_ok m' Sl ->
  stack_match cde lP a m' scrs C0 fb0 prot stk ret Sl.
Proof.
  move=> Hsm Hst.
  have Lneqr : forall q, q <> p ->
      Transitional.Memory.load m' q = Transitional.Memory.load m q.
  { move=> q Hq. exact: (TMem.load_store_neq Hst Hq). }
  have Lneq : forall q, q <> p -> TMem.vload m' q = TMem.vload m q.
  { move=> q Hq. by rewrite /TMem.vload Lneqr. }
  have Ftemps : forall Cx bx tps,
      (forall o : Z, (Cx, bx, o) <> p) ->
      TStack.frame_temps m Cx bx tps -> TStack.frame_temps m' Cx bx tps.
  { move=> Cx bx tps Hne H i Hi.
    rewrite /TMem.vload /TMem.tload (Lneqr _ (Hne _)). exact: H Hi. }
  have Fcap : forall Cx bx cp,
      (forall o : Z, (Cx, bx, o) <> p) ->
      TStack.frame_cap m Cx bx cp -> TStack.frame_cap m' Cx bx cp.
  { move=> Cx bx cp Hne H j Hj. case: (H j Hj) => w Hw. exists w.
    by rewrite (Lneq _ (Hne _)). }
  elim: Hsm.
  -
    move=> scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1
            L0 L1 T0 T1 E0 E1 TE0 TE1 E2 E3 TE3 HprivE Hrc Hcode Hne Hprot
            Hcur Hs.
    have NEcur : forall o : Z, (o < 2)%Z -> (Component.main, fb, o) <> p.
    { move=> o Ho E. rewrite -E /= in Hcur. by move: (Hcur erefl); lia. }
    have NEext : forall o : Z, (Component.main, fb_ext, o) <> p.
    { move=> o E. by move: Hprot; rewrite -E /= inE eqxx. }
    apply: SM_init; try eassumption.
    + rewrite Lneq; last by apply: NEcur; lia. exact: L0.
    + rewrite Lneq; last by apply: NEcur; lia. exact: L1.
    + rewrite /TMem.tload Lneqr; last by apply: NEcur; lia. exact: T0.
    + rewrite /TMem.tload Lneqr; last by apply: NEcur; lia. exact: T1.
    + rewrite Lneq; last exact: NEext. exact: E0.
    + rewrite Lneq; last exact: NEext. exact: E1.
    + rewrite /TMem.tload Lneqr; last exact: NEext. exact: TE0.
    + rewrite /TMem.tload Lneqr; last exact: NEext. exact: TE1.
    + rewrite Lneq; last exact: NEext. exact: E2.
    + rewrite Lneq; last exact: NEext. exact: E3.
    + rewrite /TMem.tload Lneqr; last exact: NEext. exact: TE3.
  -
    move=> scrsI C fb fb' prot' stk' oldarg targ k' rest' temps' plm ret' s Sl'
            cap' HgetP Hrc Hcode Hcont L0 L1 T0 T1 Hvi Hpriv Htemps Ea Et
            Hslots Hcap Hbud Hnp Hne Htail IH Hprot Hcur Hs.
    move: Hprot; rewrite inE negb_or => /andP [Hprot1 Hprot'].
    have NEcur : forall o : Z, (o < 2)%Z -> (C, fb, o) <> p.
    { move=> o Ho E. rewrite -E /= in Hcur. by move: (Hcur erefl); lia. }
    have NEsusp : forall o : Z, (C, fb', o) <> p.
    { move=> o E. by move: Hprot1; rewrite -E /= eqxx. }
    apply: SM_internal; try eassumption.
    + rewrite Lneq; last by apply: NEcur; lia. exact: L0.
    + rewrite Lneq; last by apply: NEcur; lia. exact: L1.
    + rewrite /TMem.tload Lneqr; last by apply: NEcur; lia. exact: T0.
    + rewrite /TMem.tload Lneqr; last by apply: NEcur; lia. exact: T1.
    + exact: (Ftemps _ _ _ NEsusp Htemps).
    + exact: (Fcap _ _ _ NEsusp Hcap).
    + apply: IH => //.
      * by move=> [E1 E2]; move: Hprot1; rewrite E1 E2 eqxx.
      * exact: slots_ok_cons Hs.
  -
    move=> scrsE C C'' fb fbE spE fb'' prot' stk' oldarg targ k'' rest'' temps''
            plm'' jal_ret icall_ret vscr junkARG sE s'' Sl' cap''
            HneC HgetP'' Hext EretE Etag HprivE L0 L1 L2 T0 T1 Hic Hcode''
            Hcont'' Hpriv'' Htemps'' Ea'' Etg2 Hslots Ltarg Ttarg Hvi Hcap''
            Hbud'' Hentry Hnp'' HnpE HneE Htail IH Hprot Hcur Hs.
    move: Hprot; rewrite !inE !negb_or => /andP [HprotE /andP [Hprot2 Hprot']].
    have NEcur : forall o : Z, (o < 2)%Z -> (C, fb, o) <> p.
    { move=> o Ho E. rewrite -E /= in Hcur. by move: (Hcur erefl); lia. }
    have NEE : forall o : Z, (C, fbE, o) <> p.
    { move=> o E. by move: HprotE; rewrite -E /= eqxx. }
    have NEsusp : forall o : Z, (C'', fb'', o) <> p.
    { move=> o E. by move: Hprot2; rewrite -E /= eqxx. }
    apply: SM_external; try eassumption.
    + apply: (ext_frame_match_store Hext Hst NEE).
    + rewrite Lneq; last by apply: NEcur; lia. exact: L0.
    + rewrite Lneq; last exact: NEE. exact: L1.
    + rewrite Lneq; last by apply: NEcur; lia. exact: L2.
    + rewrite /TMem.tload Lneqr; last by apply: NEcur; lia. exact: T0.
    + rewrite /TMem.tload Lneqr; last by apply: NEcur; lia. exact: T1.
    + exact: (Ftemps _ _ _ NEsusp Htemps'').
    + rewrite Lneq; last exact: NEsusp. exact: Ltarg.
    + rewrite /TMem.tload Lneqr; last exact: NEsusp. exact: Ttarg.
    + exact: (Fcap _ _ _ NEsusp Hcap'').
    + apply: IH => //.
      * by move=> [E1 E2]; move: Hprot2; rewrite E1 E2 eqxx.
      * exact: slots_ok_cons (slots_ok_cons Hs).
Qed.

Lemma stack_match_alloc cde lP a a' m m' scrs C0 fb0 prot stk ret Sl Ca n p :
  stack_match cde lP a m scrs C0 fb0 prot stk ret Sl ->
  Transitional.Memory.alloc m Ca n = Some (m', p) ->
  rle a a' ->
  (forall Cx b0 bx, a' Cx b0 = Some bx ->
     a Cx b0 = Some bx \/ (Cx = Ca /\ bx = Pointer.block p)) ->
  (forall (o : Z) w,
     Transitional.Memory.load m (Ca, Pointer.block p, o) = Some w -> False) ->
  TStack.slots_ok m' Sl ->
  stack_match cde lP a' m' scrs C0 fb0 prot stk ret Sl.
Proof.
  move=> Hsm Ha Hrle Hnew Hfresh.
  have Ltrr : forall q w, Transitional.Memory.load m q = Some w ->
      Transitional.Memory.load m' q = Some w.
  { move=> q w Hl.
    have Hne : Pointer.component q <> Ca \/ Pointer.block q <> Pointer.block p.
    { case: (@eqP _ (Pointer.component q) Ca) => [EC|HC]; last by left.
      case: (@eqP _ (Pointer.block q) (Pointer.block p)) => [EB|HB];
        last by right.
      by case: (Hfresh (Pointer.offset q) w);
         rewrite -EC -EB -TStack.ptr_expand. }
    by rewrite (TStack.load_alloc_other Ha Hne). }
  have Ltr : forall q w, TMem.vload m q = Some w -> TMem.vload m' q = Some w.
  { move=> q w. rewrite /TMem.vload.
    case Hl: (Transitional.Memory.load m q) => [w0|] //= E.
    by rewrite (Ltrr _ _ Hl). }
  have Hprv : forall Cx bx,
      (forall b0, a Cx b0 <> Some bx) ->
      (exists (o : Z) w, TMem.vload m (Cx, bx, o) = Some w) ->
      forall b0, a' Cx b0 <> Some bx.
  { move=> Cx bx Hold [o [w Hv]] b0 HA.
    case: (Hnew _ _ _ HA) => [HA0|[E1 E2]]; first exact: Hold HA0.
    subst Cx bx. move: Hv; rewrite /TMem.vload.
    case Hl: (Transitional.Memory.load m _) => [w0|] //= _.
    by case: (Hfresh o w0). }
  have Ft : forall Cx bx tps,
      TStack.frame_temps m Cx bx tps -> TStack.frame_temps m' Cx bx tps.
  { move=> Cx bx tps H i Hi. case: (H i Hi) => [Hv Ht].
    have [w0 Hl] := TMem.vload_load Hv.
    rewrite /TMem.vload /TMem.tload (Ltrr _ _ Hl). split.
    - by move: Hv; rewrite /TMem.vload Hl.
    - by move: Ht; rewrite /TMem.tload Hl. }
  have Ltrt : forall q t, TMem.tload m q = Some t ->
      Transitional.Memory.load m' q = Transitional.Memory.load m q.
  { move=> q t. rewrite /TMem.tload.
    case Hl: (Transitional.Memory.load m q) => [w|] //= _.
    exact: (Ltrr _ _ Hl). }
  have Fc : forall Cx bx cp,
      TStack.frame_cap m Cx bx cp -> TStack.frame_cap m' Cx bx cp.
  { move=> Cx bx cp H j Hj. case: (H j Hj) => w Hw. by exists w; exact: Ltr Hw. }
  elim: Hsm.
  -
    move=> scrs0 fb fb_ext ret_ext lret v0 v1 vx vs1
            L0 L1 T0 T1 E0 E1 TE0 TE1 E2 E3 TE3 HprivE Hrc Hcode Hne Hs.
    apply: SM_init; try eassumption.
    + exact: Ltr L0.
    + exact: Ltr L1.
    + by rewrite /TMem.tload (Ltrt _ _ T0).
    + by rewrite /TMem.tload (Ltrt _ _ T1).
    + exact: Ltr E0.
    + exact: Ltr E1.
    + by rewrite /TMem.tload (Ltrt _ _ TE0).
    + by rewrite /TMem.tload (Ltrt _ _ TE1).
    + exact: Ltr E2.
    + exact: Ltr E3.
    + by rewrite /TMem.tload (Ltrt _ _ TE3).
    + split; first by case: HprivE.
      apply: Hprv; first by case: HprivE.
      by exists 0%Z, v0.
  -
    move=> scrsI C fb fb' prot' stk' oldarg targ k' rest' temps' plm ret' s Sl'
            cap' HgetP Hrc Hcode Hcont L0 L1 T0 T1 Hvi Hpriv Htemps Ea Et
            Hslots Hcap Hbud Hnp Hne Htail IH Hs.
    apply: SM_internal; try eassumption.
    + apply: cont_matchJ_rle Hrle Hcont.
    + exact: Ltr L0.
    + exact: Ltr L1.
    + by rewrite /TMem.tload (Ltrt _ _ T0).
    + by rewrite /TMem.tload (Ltrt _ _ T1).
    + exact: val_inject_rle Hrle Hvi.
    + split; first by case: Hpriv.
      apply: Hprv; first by case: Hpriv.
      case: (Hslots s (or_introl erefl)) => [Hv _].
      exists (Z.of_nat (2 + size temps')), (Ptr (TStack.ra_ret s)).
      by rewrite -Ea.
    + exact: Ft Htemps.
    + exact: Fc Hcap.
    + apply: IH. exact: slots_ok_cons Hs.
  -
    move=> scrsE C C'' fb fbE spE fb'' prot' stk' oldarg targ k'' rest'' temps''
            plm'' jal_ret icall_ret vscr junkARG sE s'' Sl' cap''
            HneC HgetP'' Hext EretE Etag HprivE L0 L1 L2 T0 T1 Hic Hcode''
            Hcont'' Hpriv'' Htemps'' Ea'' Etg2 Hslots Ltarg Ttarg Hvi Hcap''
            Hbud'' Hentry Hnp'' HnpE HneE Htail IH Hs.
    case: (ext_frame_slot Hext) => [EaE HsE].
    apply: SM_external; try eassumption.
    + apply: (ext_frame_match_transport Hext).
      * move=> o w. exact: Ltr.
      * move=> o t Ht0. by rewrite /TMem.tload (Ltrt _ _ Ht0).
      * move=> x Hin. apply: Hs. case: Hin => [E|//]. rewrite E. by left.
    + split; first by case: HprivE.
      apply: Hprv; first by case: HprivE.
      case: (HsE sE (or_introl erefl)) => [Hv _].
      exists 2%Z, (Ptr (TStack.ra_ret sE)). by rewrite -EaE.
    + exact: Ltr L0.
    + exact: Ltr L1.
    + exact: Ltr L2.
    + by rewrite /TMem.tload (Ltrt _ _ T0).
    + by rewrite /TMem.tload (Ltrt _ _ T1).
    + apply: cont_matchJ_rle Hrle Hcont''.
    + split; first by case: Hpriv''.
      apply: Hprv; first by case: Hpriv''.
      case: (Hslots s'' (or_intror (or_introl erefl))) => [Hv _].
      exists (Z.of_nat (2 + size temps'')), (Ptr (TStack.ra_ret s'')).
      by rewrite -Ea''.
    + exact: Ft Htemps''.
    + exact: Ltr Ltarg.
    + by rewrite /TMem.tload (Ltrt _ _ Ttarg).
    + exact: val_inject_rle Hrle Hvi.
    + exact: Fc Hcap''.
    + apply: IH. exact: slots_ok_cons (slots_ok_cons Hs).
Qed.

Lemma stack_match_external_inv cde lP a m scrs C fb prot Cf oldarg k'' stk ret
      Sl :
  C <> Cf ->
  stack_match cde lP a m scrs C fb prot (S.CS.Frame Cf oldarg k'' :: stk) ret
              Sl ->
  exists fbE spE fb'' prot0 targ plm'' icall_ret vscr junkARG sE s'' Sl1 cap''
         temps'' rest'',
    [/\ Sl = sE :: s'' :: Sl1,
        prot = (C, fbE) :: (Cf, fb'') :: prot0,
        getm lP Cf = Some plm'',
        ext_frame_match cde m C fbE ret spE sE
      & TStack.ra_ret sE = icall_ret]
    /\ [/\ TStack.ra_tag sE = Ret (size (TStack.ext_levels Sl1)),
           TStack.ra_tag s'' = InternalJump,
           frame_priv a C fbE,
           TMem.vload m (C, fb, 0%Z) = Some (Ptr (C, fbE, spE))
         & TMem.vload m (C, fbE, 1%Z) = Some vscr]
    /\ [/\ TMem.vload m (C, fb, 1%Z) = Some junkARG,
           TMem.tload m (C, fb, 0%Z) = Some Other,
           TMem.tload m (C, fb, 1%Z) = Some Other,
           Pointer.component icall_ret = Cf
         & TMacros.code_at_I cde Cf icall_ret
             (IConst (IInt 1) R_ONE
                :: reload_sp (scr Cf) ++ pop R_ARG ++ pop R_RA ++ rest'')]
    /\ [/\ cont_matchJ a Cf plm'' k'' rest'' temps'',
           frame_priv a Cf fb'',
           TStack.frame_temps m Cf fb'' temps'',
           TStack.ra_addr s'' = (Cf, fb'', Z.of_nat (2 + size temps''))
         & TStack.slots_ok m (sE :: s'' :: Sl1)]
    /\ [/\ TMem.vload m (Cf, fb'', Z.of_nat (2 + size temps'' + 1)) = Some targ,
           TMem.tload m (Cf, fb'', Z.of_nat (2 + size temps'' + 1)) = Some Other,
           val_inject a oldarg targ,
           TStack.frame_cap m Cf fb'' cap''
         & 3 + kneed k'' (size temps'') <= cap'']
    /\ [/\ getm scrs Cf
           = Some (Ptr (Cf, fb'', Z.of_nat (2 + size temps'' + 2))),
           (Cf, fb'') \notin prot0,
           (C, fbE) \notin ((Cf, fb'') :: prot0),
           fb <> fbE
         & stack_match cde lP a m (setm scrs C vscr) Cf fb'' prot0 stk
             (TStack.ra_ret s'') Sl1].
Proof.
  move=> Hne H. inversion H; subst; first by [].
  exists fbE, spE, fb'', prot0, targ, plm'', (TStack.ra_ret sE), vscr,
         junkARG, sE, s'', Sl0, cap'', temps'', rest''.
  split; last split; last split; last split; last split;
    by split; try eassumption.
Qed.

Lemma ext_level_max sE s'' Sl k :
  TStack.ra_tag sE = Ret (size (TStack.ext_levels Sl)) ->
  TStack.ra_tag s'' = InternalJump ->
  TStack.levels_ok (sE :: s'' :: Sl) k ->
  k = (size (TStack.ext_levels Sl)).+1.
Proof.
  move=> HE HJ Hlv.
  have Eext : TStack.ext_levels (sE :: s'' :: Sl)
            = size (TStack.ext_levels Sl) :: TStack.ext_levels Sl
    by rewrite /TStack.ext_levels /= HE HJ /= -/(TStack.ext_levels Sl).
  by move: (TStack.levels_ok_size Hlv); rewrite Eext /=.
Qed.

Lemma stack_match_init_inv cde lP a m scrs C fb prot ret Sl :
  stack_match cde lP a m scrs C fb prot [::] ret Sl ->
  exists fb_ext lret v0 v1 vx vs1,
    [/\ [/\ C = Component.main, prot = [:: (Component.main, fb_ext)],
            Sl = [::]
          & fb <> fb_ext],
        [/\ TMem.vload m (Component.main, fb, 0%Z)
              = Some (Ptr (Component.main, fb_ext, 4%Z)),
            TMem.vload m (Component.main, fb, 1%Z) = Some vs1,
            TMem.tload m (Component.main, fb, 0%Z) = Some Other
          & TMem.tload m (Component.main, fb, 1%Z) = Some Other],
        [/\ TMem.vload m (Component.main, fb_ext, 0%Z) = Some v0,
            TMem.vload m (Component.main, fb_ext, 1%Z) = Some v1,
            TMem.vload m (Component.main, fb_ext, 2%Z) = Some vx,
            TMem.vload m (Component.main, fb_ext, 3%Z) = Some (Int 0)
          & [/\ TMem.tload m (Component.main, fb_ext, 0%Z) = Some Other,
                TMem.tload m (Component.main, fb_ext, 1%Z) = Some Other
              & TMem.tload m (Component.main, fb_ext, 3%Z) = Some Other]],
        frame_priv a Component.main fb_ext
      & [/\ Pointer.component ret = Component.main
          & TMacros.code_at_I cde Component.main ret
              (pop R_ARG ++ pop R_RA ++ pop R_AUX1
                 ++ store_arg (scr Component.main) R_AUX1 R_AUX2
                 ++ pop R_SP
                 ++ [:: IBnz R_ARG lret; IHalt; ILabel lret; IReturn])]].
Proof.
  move=> H. inversion H; subst. do 6!eexists. split.
  - by split=> //; eassumption.
  - by split=> //; eassumption.
  - by split=> //; try eassumption; split=> //; eassumption.
  - by eassumption.
  - by split=> //; eassumption.
Qed.

Lemma stack_match_internal_inv cde lP a m scrs C fb prot oldarg k' stk ret Sl :
  stack_match cde lP a m scrs C fb prot (S.CS.Frame C oldarg k' :: stk) ret Sl ->
  exists fb' prot0 targ rest' temps' plm s Sl1 cap',
    getm lP C = Some plm
    /\ prot = (C, fb') :: prot0
    /\ Sl = s :: Sl1
    /\ Pointer.component ret = C
    /\ TMacros.code_at_I cde C ret (pop R_RA ++ rest')
    /\ cont_matchJ a C plm k' rest' temps'
    /\ TMem.vload m (C, fb, 0%Z)
       = Some (Ptr (C, fb', Z.of_nat (2 + size temps' + 1)))
    /\ TMem.vload m (C, fb, 1%Z) = Some targ
    /\ TMem.tload m (C, fb, 0%Z) = Some Other
    /\ TMem.tload m (C, fb, 1%Z) = Some Other
    /\ val_inject a oldarg targ
    /\ frame_priv a C fb'
    /\ TStack.frame_temps m C fb' temps'
    /\ TStack.ra_addr s = (C, fb', Z.of_nat (2 + size temps'))
    /\ TStack.ra_tag s = InternalJump
    /\ TStack.slots_ok m (s :: Sl1)
    /\ TStack.frame_cap m C fb' cap'
    /\ 3 + kneed k' (size temps') <= cap'
    /\ (C, fb') \notin prot0
    /\ fb <> fb'
    /\ stack_match cde lP a m scrs C fb' prot0 stk (TStack.ra_ret s) Sl1.
Proof.
  move=> H. inversion H; subst.
  - by exists fb', prot0, targ, rest', temps', plm, s, Sl0, cap'.
  -
    by [].
Qed.


Definition scrs_ok (m : mem) (iface : Program.interface)
                   (scrs : NMap value) : Prop :=
  [/\ forall C' v, getm scrs C' = Some v ->
        TMem.vload m (C', 1, 0%Z) = Some v,
      TMem.vload m (Component.main, 1, 1%Z) = Some (Int 1)
      /\ TMem.tload m (Component.main, 1, 1%Z) = Some Other,
      forall C', C' \in domm iface ->
        exists v, TMem.vload m (C', 1, 0%Z) = Some v
    &
      forall C', C' \in domm iface ->
        TMem.tload m (C', 1, 0%Z) = Some Other].

Lemma scrs_ok_store m m' iface scrs p c :
  scrs_ok m iface scrs ->
  Transitional.Memory.store m p c = Some m' ->
  Pointer.block p <> 1 ->
  scrs_ok m' iface scrs.
Proof.
  move=> [H1 H2 H3 H4] Hst Hb.
  have Lraw : forall q, Pointer.block q = 1 ->
             Transitional.Memory.load m' q = Transitional.Memory.load m q.
  { move=> q Hq. rewrite (TMem.load_store_neq Hst) //.
    by move=> E; apply: Hb; rewrite -E Hq. }
  have Ltr : forall q, Pointer.block q = 1 ->
             TMem.vload m' q = TMem.vload m q
    by move=> q Hq; rewrite /TMem.vload Lraw.
  split.
  - move=> C' v Hv. by rewrite (Ltr (C', 1, 0%Z) erefl); exact: H1 Hv.
  - case: H2 => [H2v H2t]. split.
    + by rewrite (Ltr (Component.main, 1, 1%Z) erefl).
    + by rewrite /TMem.tload (Lraw (Component.main, 1, 1%Z) erefl).
  - move=> C' HC. by rewrite (Ltr (C', 1, 0%Z) erefl); exact: H3 HC.
  - move=> C' HC. by rewrite /TMem.tload (Lraw (C', 1, 0%Z) erefl);
                     exact: H4 HC.
Qed.

Lemma scrs_ok_store_same m m' iface scrs p cc c' :
  scrs_ok m iface scrs ->
  Transitional.Memory.load m p = Some cc ->
  Transitional.val c'.1 = Transitional.val cc.1 ->
  tvtag c'.1 = tvtag cc.1 ->
  Transitional.Memory.store m p c' = Some m' ->
  scrs_ok m' iface scrs.
Proof.
  move=> [H1 H2 H3 H4] Hld Ev Et Hst. split.
  - move=> C' v Hv. by rewrite (TMem.vload_store_same Hld Ev Hst); exact: H1 Hv.
  - case: H2 => [H2v H2t]. split.
    + by rewrite (TMem.vload_store_same Hld Ev Hst).
    + by rewrite (TMem.tload_store_same Hld Et Hst).
  - move=> C' HC. by rewrite (TMem.vload_store_same Hld Ev Hst); exact: H3 HC.
  - move=> C' HC. by rewrite (TMem.tload_store_same Hld Et Hst); exact: H4 HC.
Qed.

End TSM.
