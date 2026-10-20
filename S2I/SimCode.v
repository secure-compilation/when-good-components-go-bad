Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Memory.
Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import Source.Language.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.
Require Import S2I.CompMonad.
Require Import S2I.Compiler.
Require Import S2I.SimInject.
Require Import Lib.Extra.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype path.
From extructures Require Import ord fset fmap.
From mathcomp Require Import zify.
Require Import Coq.micromega.Lia.

Import Intermediate.

Set Bullet Behavior "Strict Subproofs".

Lemma register_to_nat_inj r1 r2 :
  Register.to_nat r1 = Register.to_nat r2 -> r1 = r2.
Proof. by case: r1; case: r2. Qed.

Lemma register_get_set_eq r v regs :
  Register.get r (Register.set r v regs) = v.
Proof. by rewrite /Register.get /Register.set setmE eqxx. Qed.

Lemma register_get_set_neq r r' v regs :
  r' <> r ->
  Register.get r (Register.set r' v regs) = Register.get r regs.
Proof.
  move=> Hne. rewrite /Register.get /Register.set setmE.
  case E: (Register.to_nat r == Register.to_nat r') => //.
  move/eqP: E => /register_to_nat_inj E. by case: Hne.
Qed.

Definition code_at (G : global_env) (pc : Pointer.t) (c : code) : Prop :=
  exists C_procs P_code pre post,
    [/\ getm (genv_procedures G) (Pointer.component pc) = Some C_procs,
        getm C_procs (Pointer.block pc) = Some P_code,
        P_code = pre ++ c ++ post
      & Pointer.offset pc = Z.of_nat (size pre)].

Lemma nth_error_cat_l (l1 l2 : code) :
  List.nth_error (l1 ++ l2) (size l1) = List.nth_error l2 0.
Proof. by elim: l1. Qed.

Lemma code_at_head {G pc i c} :
  code_at G pc (i :: c) -> executing G pc i.
Proof.
  move=> [C_procs [P_code [pre [post [HC HP Hcode Hoff]]]]].
  exists C_procs, P_code. split; first by [].
  split; first by [].
  split; first by rewrite Hoff; lia.
  by rewrite Hcode Hoff Nat2Z.id nth_error_cat_l.
Qed.

Lemma code_at_tail {G pc i c} :
  code_at G pc (i :: c) -> code_at G (Pointer.inc pc) c.
Proof.
  move=> [C_procs [P_code [pre [post [HC HP Hcode Hoff]]]]].
  exists C_procs, P_code, (pre ++ [:: i]), post.
  split.
  - by rewrite Pointer.inc_preserves_component.
  - by rewrite Pointer.inc_preserves_block.
  - by rewrite Hcode -catA.
  - case: pc Hoff {HC HP} => [[C b] o] /= Hoff.
    rewrite size_cat /= Hoff. lia.
Qed.

Lemma code_at_app_l {G pc c1 c2} :
  code_at G pc (c1 ++ c2) -> code_at G pc c1.
Proof.
  move=> [C_procs [P_code [pre [post [HC HP Hcode Hoff]]]]].
  exists C_procs, P_code, pre, (c2 ++ post).
  split=> //. by rewrite Hcode -catA.
Qed.

Section StepLemmas.

Variable G : global_env.

Lemma step_label gps mem regs pc l c :
  code_at G pc (ILabel l :: c) ->
  CS.step G (gps, mem, regs, pc) E0 (gps, mem, regs, Pointer.inc pc).
Proof. move=> /code_at_head H. exact: CS.Label H. Qed.

Lemma step_const gps mem regs pc v r c :
  code_at G pc (IConst v r :: c) ->
  CS.step G (gps, mem, regs, pc) E0
          (gps, mem, Register.set r (imm_to_val v) regs, Pointer.inc pc).
Proof. move=> /code_at_head H. exact: CS.Const H erefl. Qed.

Lemma step_mov gps mem regs pc r1 r2 c :
  code_at G pc (IMov r1 r2 :: c) ->
  CS.step G (gps, mem, regs, pc) E0
          (gps, mem, Register.set r2 (Register.get r1 regs) regs, Pointer.inc pc).
Proof. move=> /code_at_head H. exact: CS.Mov H erefl. Qed.

Lemma step_binop gps mem regs pc op r1 r2 r3 c :
  code_at G pc (IBinOp op r1 r2 r3 :: c) ->
  CS.step G (gps, mem, regs, pc) E0
          (gps, mem,
           Register.set r3 (eval_binop op (Register.get r1 regs)
                                           (Register.get r2 regs)) regs,
           Pointer.inc pc).
Proof. move=> /code_at_head H. exact: CS.BinOp H erefl. Qed.

Lemma step_load gps mem regs pc r1 r2 c ptr v :
  code_at G pc (ILoad r1 r2 :: c) ->
  Register.get r1 regs = Ptr ptr ->
  Pointer.component ptr = Pointer.component pc ->
  Memory.load mem ptr = Some v ->
  CS.step G (gps, mem, regs, pc) E0
          (gps, mem, Register.set r2 v regs, Pointer.inc pc).
Proof. move=> /code_at_head H H1 H2 H3. exact: CS.Load H H1 H2 H3 erefl. Qed.

Lemma step_store gps mem regs pc r1 r2 c ptr mem' :
  code_at G pc (IStore r1 r2 :: c) ->
  Register.get r1 regs = Ptr ptr ->
  Pointer.component ptr = Pointer.component pc ->
  Memory.store mem ptr (Register.get r2 regs) = Some mem' ->
  CS.step G (gps, mem, regs, pc) E0 (gps, mem', regs, Pointer.inc pc).
Proof. move=> /code_at_head H H1 H2 H3. exact: CS.Store H H1 H2 H3. Qed.

Lemma step_jal gps mem regs pc l c pc' :
  code_at G pc (IJal l :: c) ->
  find_label_in_component G pc l = Some pc' ->
  CS.step G (gps, mem, regs, pc) E0
          (Pointer.inc pc :: gps, mem, Register.set R_RA Undef regs, pc').
Proof. move=> /code_at_head H H1. exact: CS.Jal H H1 erefl. Qed.

Lemma step_jump gps mem regs pc pc' c :
  code_at G pc (IJump :: c) ->
  Pointer.component pc' = Pointer.component pc ->
  CS.step G (pc' :: gps, mem, regs, pc) E0 (gps, mem, regs, pc').
Proof. move=> /code_at_head H H1. exact: CS.Jump H H1. Qed.

Lemma step_bnz_nz gps mem regs pc r l c val pc' :
  code_at G pc (IBnz r l :: c) ->
  Register.get r regs = Int val ->
  (val <> 0)%Z ->
  find_label_in_procedure G pc l = Some pc' ->
  CS.step G (gps, mem, regs, pc) E0 (gps, mem, regs, pc').
Proof. move=> /code_at_head H H1 H2 H3. exact: CS.BnzNZ H H1 H2 H3. Qed.

Lemma step_bnz_z gps mem regs pc r l c :
  code_at G pc (IBnz r l :: c) ->
  Register.get r regs = Int 0 ->
  CS.step G (gps, mem, regs, pc) E0 (gps, mem, regs, Pointer.inc pc).
Proof. move=> /code_at_head H H1. exact: CS.BnzZ H H1. Qed.

Lemma step_alloc gps mem regs pc rptr rsize c size mem' ptr :
  code_at G pc (IAlloc rptr rsize :: c) ->
  Register.get rsize regs = Int size ->
  (size > 0)%Z ->
  Memory.alloc mem (Pointer.component pc) (Z.to_nat size) = Some (mem', ptr) ->
  CS.step G (gps, mem, regs, pc) E0
          (gps, mem', Register.set rptr (Ptr ptr) regs, Pointer.inc pc).
Proof. move=> /code_at_head H H1 H2 H3. exact: CS.Alloc H H1 H2 H3 erefl. Qed.

Lemma step_call gps mem regs pc C' P c b call_arg :
  code_at G pc (ICall C' P :: c) ->
  Pointer.component pc <> C' ->
  imported_procedure (genv_interface G) (Pointer.component pc) C' P ->
  EntryPoint.get C' P (genv_entrypoints G) = Some b ->
  Register.get R_COM regs = Int call_arg ->
  CS.step G (gps, mem, regs, pc)
          [:: ECall (Pointer.component pc) P call_arg C']
          (Pointer.inc pc :: gps, mem, Register.invalidate regs, (C', b, 0%Z)).
Proof. move=> /code_at_head H H1 H2 H3 H4. exact: CS.Call H H1 H2 H3 H4. Qed.

Lemma step_return gps' mem regs pc pc' c ret_arg :
  code_at G pc (IReturn :: c) ->
  Pointer.component pc <> Pointer.component pc' ->
  Register.get R_COM regs = Int ret_arg ->
  CS.step G (pc' :: gps', mem, regs, pc)
          [:: ERet (Pointer.component pc) ret_arg (Pointer.component pc')]
          (gps', mem, Register.invalidate regs, pc').
Proof. move=> /code_at_head H H1 H2. exact: CS.Return H H1 H2. Qed.

Lemma executing_halt pc c :
  code_at G pc (IHalt :: c) -> executing G pc IHalt.
Proof. exact: code_at_head. Qed.

Lemma exec_push gps mem regs pc r c C fb sp mem' :
  code_at G pc (push r ++ c) ->
  Register.get R_SP regs = Ptr (C, fb, sp) ->
  Register.get R_ONE regs = Int 1 ->
  Pointer.component pc = C ->
  Memory.store mem (C, fb, sp) (Register.get r regs) = Some mem' ->
  star CS.step G (gps, mem, regs, pc) E0
       (gps, mem', Register.set R_SP (Ptr (C, fb, (sp + 1)%Z)) regs,
        Pointer.inc (Pointer.inc pc)).
Proof.
  rewrite /push /= => Hcode HSP HONE Hcomp Hstore.
  eapply star_step with (t1 := E0) (t2 := E0); [| |by []].
  - eapply step_store;
      [exact: Hcode | exact: HSP | by rewrite /= Hcomp | exact: Hstore].
  - apply: star_one.
    have Hb := step_binop gps mem' regs (Pointer.inc pc) Add R_SP R_ONE R_SP
                 c (code_at_tail Hcode).
    by rewrite HSP HONE /= in Hb.
Qed.

Lemma exec_pop gps mem regs pc r c C fb sp v :
  code_at G pc (pop r ++ c) ->
  Register.get R_SP regs = Ptr (C, fb, sp) ->
  Register.get R_ONE regs = Int 1 ->
  Pointer.component pc = C ->
  Memory.load mem (C, fb, (sp - 1)%Z) = Some v ->
  star CS.step G (gps, mem, regs, pc) E0
       (gps, mem,
        Register.set r v (Register.set R_SP (Ptr (C, fb, (sp - 1)%Z)) regs),
        Pointer.inc (Pointer.inc pc)).
Proof.
  rewrite /pop /= => Hcode HSP HONE Hcomp Hload.
  eapply star_step with (t1 := E0) (t2 := E0); [| |by []].
  - have Hb := step_binop gps mem regs pc Minus R_SP R_ONE R_SP
                 _ Hcode.
    rewrite HSP HONE /= in Hb. exact: Hb.
  - apply: star_one.
    eapply step_load;
      [ exact: (code_at_tail Hcode)
      | by rewrite register_get_set_eq
      | by rewrite /= Pointer.inc_preserves_component Hcomp
      | exact: Hload].
Qed.

Lemma exec_load_arg gps mem regs pc buf r c v :
  code_at G pc (load_arg buf r ++ c) ->
  Pointer.component buf = Pointer.component pc ->
  Memory.load mem buf = Some v ->
  star CS.step G (gps, mem, regs, pc) E0
       (gps, mem, Register.set r v (Register.set r (Ptr buf) regs),
        Pointer.inc (Pointer.inc pc)).
Proof.
  rewrite /load_arg /= => Hcode Hcomp Hload.
  eapply star_step with (t1 := E0) (t2 := E0); [| |by []].
  - eapply step_const. exact: Hcode.
  - apply: star_one.
    eapply step_load;
      [ exact: (code_at_tail Hcode)
      | by rewrite register_get_set_eq
      | by rewrite Pointer.inc_preserves_component Hcomp
      | exact: Hload].
Qed.

Lemma exec_reload_sp gps mem regs pc buf c v :
  code_at G pc (reload_sp buf ++ c) ->
  Pointer.component buf = Pointer.component pc ->
  Memory.load mem buf = Some v ->
  star CS.step G (gps, mem, regs, pc) E0
       (gps, mem, Register.set R_SP v (Register.set R_AUX2 (Ptr buf) regs),
        Pointer.inc (Pointer.inc pc)).
Proof.
  rewrite /reload_sp /= => Hcode Hcomp Hload.
  eapply star_step with (t1 := E0) (t2 := E0); [| |by []].
  - eapply step_const. exact: Hcode.
  - apply: star_one.
    eapply step_load;
      [ exact: (code_at_tail Hcode)
      | by rewrite register_get_set_eq
      | by rewrite Pointer.inc_preserves_component Hcomp
      | exact: Hload].
Qed.

Lemma exec_store_arg gps mem regs pc buf r rtemp c mem' :
  code_at G pc (store_arg buf r rtemp ++ c) ->
  Pointer.component buf = Pointer.component pc ->
  rtemp <> r ->
  Memory.store mem buf (Register.get r regs) = Some mem' ->
  star CS.step G (gps, mem, regs, pc) E0
       (gps, mem', Register.set rtemp (Ptr buf) regs,
        Pointer.inc (Pointer.inc pc)).
Proof.
  rewrite /store_arg /= => Hcode Hcomp Hne Hstore.
  eapply star_step with (t1 := E0) (t2 := E0); [| |by []].
  - eapply step_const. exact: Hcode.
  - apply: star_one.
    eapply step_store;
      [ exact: (code_at_tail Hcode)
      | by rewrite register_get_set_eq
      | by rewrite Pointer.inc_preserves_component Hcomp
      | by rewrite (register_get_set_neq _ _ _ _ Hne)].
Qed.

End StepLemmas.

Lemma reserve_blocks_load {m n m' bs} :
  ComponentMemoryExtra.reserve_blocks m n = (m', bs) ->
  forall b i, ComponentMemory.load m' b i = ComponentMemory.load m b i.
Proof.
  rewrite /ComponentMemoryExtra.reserve_blocks.
  elim: n m' bs => [|n IH] m' bs /=; first by move=> [<- _].
  case E: (iter n _ (m, [::])) => [m0 bs0] /=.
  case E2: (ComponentMemory.reserve_block m0) => [m1 b1] [<- _] b i.
  rewrite (ComponentMemory.load_after_reserve_block _ _ _ E2).
  exact: (IH _ _ E).
Qed.

Lemma reserve_blocks_domm {m n m' bs} :
  ComponentMemoryExtra.reserve_blocks m n = (m', bs) ->
  ComponentMemory.domm m' = ComponentMemory.domm m.
Proof.
  rewrite /ComponentMemoryExtra.reserve_blocks.
  elim: n m' bs => [|n IH] m' bs /=; first by move=> [<- _].
  case E: (iter n _ (m, [::])) => [m0 bs0] /=.
  case E2: (ComponentMemory.reserve_block m0) => [m1 b1] [<- _].
  rewrite (ComponentMemory.domm_reserve_block _ _ _ E2).
  exact: (IH _ _ E).
Qed.

Lemma reserve_blocks_wf {m n m' bs} :
  ComponentMemoryExtra.reserve_blocks m n = (m', bs) ->
  ComponentMemory.wf m -> ComponentMemory.wf m'.
Proof.
  rewrite /ComponentMemoryExtra.reserve_blocks.
  elim: n m' bs => [|n IH] m' bs /=; first by move=> [<- _].
  case E: (iter n _ (m, [::])) => [m0 bs0] /=.
  case E2: (ComponentMemory.reserve_block m0) => [m1 b1] [<- _] Hwf.
  apply: ComponentMemory.wf_reserve_block E2.
  exact: (IH _ _ E).
Qed.

Lemma compilation_preserves_buffers {p tp} :
  compile_program p = Some tp ->
  Intermediate.prog_buffers tp = gen_buffers (Source.prog_buffers p).
Proof.
  rewrite /compile_program /Comp.run /= /Comp.bind /=.
  case E1: (gen_all_procedures_labels _ init_env) => [[labels cenv1]|] //=.
  case E2: (compile_components _ _ _ cenv1) => [[code cenv2]|] //=.
  rewrite /Comp.ret /=.
  by move=> [<-].
Qed.

Lemma static_value_inject (C0 : Component.id) v :
  Source.well_formed_buffer_value C0 v ->
  val_inject init_renaming v v.
Proof.
  case: v => [z|[[C b] o]|] /= => [_|Hb|_].
  - by constructor.
  - case/andP: Hb => /PeanoNat.Nat.eqb_eq -> _.
    apply: VI_ptr. by rewrite /init_renaming eqxx.
  - by constructor.
Qed.

Lemma nth_error_forallb {A : Type} (f : A -> bool) (l : list A) k v :
  List.nth_error l k = Some v -> List.forallb f l -> f v.
Proof.
  move=> Hnth Hall.
  have HIn := List.nth_error_In _ _ Hnth.
  exact: (proj1 (List.forallb_forall f l) Hall _ HIn).
Qed.

Lemma prepare_procedures_memory_getm tp C :
  getm (Intermediate.prepare_procedures_memory tp) C =
  if C \in domm (Intermediate.prog_interface tp) then
    Some (ComponentMemoryExtra.reserve_blocks
            (ComponentMemory.prealloc
               (odflt emptym (getm (Intermediate.prog_buffers tp) C)))
            (length (elementsm
               (odflt emptym (getm (Intermediate.prog_procedures tp) C))))).1
  else None.
Proof.
  rewrite /Intermediate.prepare_procedures_memory
          /Intermediate.prepare_procedures_initial_memory
          /Intermediate.prepare_procedures_initial_memory_aux.
  rewrite mapmE mkfmapfE.
  case: (C \in domm (Intermediate.prog_interface tp)) => //=.
  rewrite /Intermediate.reserve_component_blocks.
  by case E: (ComponentMemoryExtra.reserve_blocks _ _) => [m' bs] /=.
Qed.

Lemma initial_mem_inject p tp :
  Source.well_formed_program p ->
  compile_program p = Some tp ->
  mem_inject init_renaming (Source.prepare_buffers p)
             (Intermediate.prepare_procedures_memory tp).
Proof.
  move=> Hwf Hcomp.
  have Hbuf := compilation_preserves_buffers Hcomp.
  have Hintf := compilation_preserves_interface p tp Hcomp.
  have Hdomms : domm (Source.prepare_buffers p) = domm (Source.prog_buffers p).
  { by rewrite /Source.prepare_buffers domm_map. }
  have Hdommt : domm (Intermediate.prepare_procedures_memory tp)
                = domm (Source.prog_buffers p).
  { rewrite /Intermediate.prepare_procedures_memory
            /Intermediate.prepare_procedures_initial_memory
            /Intermediate.prepare_procedures_initial_memory_aux.
    rewrite domm_map domm_mkfmapf Hintf.
    exact: (Source.wfprog_defined_buffers Hwf). }
  have Hgets : forall C, getm (Source.prepare_buffers p) C
      = omap (fun ib => ComponentMemory.prealloc (mkfmap [:: (0, ib)]))
             (getm (Source.prog_buffers p) C).
  { move=> C. by rewrite /Source.prepare_buffers mapmE. }
  split.
  - exact: init_renaming_ok.
  - by rewrite Hdomms Hdommt.
  -
    move=> C cm. rewrite Hgets.
    case: (getm (Source.prog_buffers p) C) => [ib|] //= [<-].
    exact: ComponentMemory.wf_prealloc.
  -
    move=> C cm. rewrite prepare_procedures_memory_getm.
    case: (C \in domm (Intermediate.prog_interface tp)) => //= [[<-]].
    case E: (ComponentMemoryExtra.reserve_blocks _ _) => [m' bs] /=.
    apply: reserve_blocks_wf E _.
    exact: ComponentMemory.wf_prealloc.
  -
    move=> C cm. rewrite Hgets.
    case: (getm (Source.prog_buffers p) C) => [ib|] //= [<-].
    rewrite (ComponentMemory.domm_prealloc _ _ erefl).
    apply/dommP. exists ib. by rewrite /= setmE.
  -
    move=> C cm. rewrite prepare_procedures_memory_getm.
    case HC: (C \in domm (Intermediate.prog_interface tp)) => //=.
    move=> [<-].
    have HCb : C \in domm (Source.prog_buffers p).
    { by rewrite -(Source.wfprog_defined_buffers Hwf) -Hintf HC. }
    case/dommP: HCb => ib Eb.
    rewrite Hbuf /gen_buffers mapmE Eb /=.
    case E: (ComponentMemoryExtra.reserve_blocks _ _) => [m' bs] /=.
    rewrite (reserve_blocks_domm E)
            (ComponentMemory.domm_prealloc _ _ erefl).
    apply/dommP. exists ib. by rewrite /= setmE.
  -
    move=> C b b'. rewrite /init_renaming.
    by case: (b =P Block.local) => [->|] //= _ [_].
  -
    move=> C b b'. rewrite /init_renaming.
    by case: (b =P Block.local) => [_|] //= _ [_].
  -
    move=> C b b' i. rewrite /init_renaming.
    case: (b =P Block.local) => [E|]; last by [].
    subst b. move=> [<-].
    rewrite /Memory.load /= Hgets prepare_procedures_memory_getm.
    have <- : (C \in domm (Source.prog_buffers p))
              = (C \in domm (Intermediate.prog_interface tp)).
    { by rewrite Hintf -(Source.wfprog_defined_buffers Hwf). }
    rewrite mem_domm.
    case Ebc: (getm (Source.prog_buffers p) C) => [ib|] //=.
    case E: (ComponentMemoryExtra.reserve_blocks _ _) => [m' bs] /=.
    rewrite (reserve_blocks_load E).
    rewrite !ComponentMemory.load_prealloc.
    case: (0 <=? i)%Z => //=.
    rewrite Hbuf /gen_buffers mapmE Ebc /=.
    case: ib Ebc => [sz|chunk] Ebc /=.
    +
      case: (i <? Z.of_nat sz)%Z => //=. by constructor.
    +
      case Ev: (List.nth_error chunk (Z.to_nat i)) => [v|] //=.
      apply: static_value_inject.
      exact: (nth_error_forallb _ _ _ _ Ev
                (Source.wfprog_buffer_values Hwf Ebc)).
Qed.

Fixpoint labels_of (c : code) : seq label :=
  match c with
  | [::] => [::]
  | ILabel l :: c' => l :: labels_of c'
  | _ :: c' => labels_of c'
  end.

Lemma labels_of_cat c1 c2 :
  labels_of (c1 ++ c2) = labels_of c1 ++ labels_of c2.
Proof. by elim: c1 => [|i c1 IH] //=; case: i => *; rewrite //= IH. Qed.

Fixpoint find_label_aux (c : code) (l : label) (o : Z) : option Z :=
  match c with
  | [::] => None
  | ILabel l' :: c' =>
    if Nat.eqb l l' then Some o else find_label_aux c' l (1 + o)%Z
  | _ :: c' => find_label_aux c' l (1 + o)%Z
  end.

Lemma find_labelE c l : find_label c l = find_label_aux c l 0%Z.
Proof.
  rewrite /find_label.
  elim: c (0%Z) => [|i c IH] o //=.
  by case: i => [|l'|v r|r1 r2|op r1 r2 r3|r1 r2|r1 r2|r1 r2|r l0| |l0|C0 P0| |] /=;
    rewrite -?IH; case: c {IH}.
Qed.

Lemma find_label_aux_label c l l' o :
  find_label_aux (ILabel l' :: c) l o
  = if Nat.eqb l l' then Some o else find_label_aux c l (1 + o)%Z.
Proof. by []. Qed.

Lemma find_label_aux_skip i c l o :
  (forall l', i <> ILabel l') ->
  find_label_aux (i :: c) l o = find_label_aux c l (1 + o)%Z.
Proof. by case: i => // l' /(_ l'). Qed.

Lemma labels_of_label l' c : labels_of (ILabel l' :: c) = l' :: labels_of c.
Proof. by []. Qed.

Lemma find_label_aux_cat_notin pre l o rest :
  l \notin labels_of pre ->
  find_label_aux (pre ++ rest) l o
  = find_label_aux rest l (Z.of_nat (size pre) + o)%Z.
Proof.
  elim: pre o => [|i pre IH] o.
  - by move=> _; rewrite cat0s.
  - rewrite cat_cons.
    case: i => [|l'|v r|r1 r2|op r1 r2 r3|r1 r2|r1 r2|r1 r2|r l0| |l0|C0 P0| |];
      try by (move=> Hno;
              rewrite find_label_aux_skip // IH //;
              f_equal; rewrite [size (_ :: _)]/=; lia).
    rewrite (labels_of_label l' pre) in_cons negb_or => /andP [Hne Hno'].
    rewrite find_label_aux_label.
    have -> : Nat.eqb l l' = false.
    { apply/PeanoNat.Nat.eqb_neq => E. by rewrite E eqxx in Hne. }
    rewrite IH //. f_equal. rewrite [size (_ :: _)]/=. lia.
Qed.

Lemma find_label_position pre l post :
  l \notin labels_of pre ->
  find_label (pre ++ ILabel l :: post) l = Some (Z.of_nat (size pre)).
Proof.
  move=> Hnotin.
  rewrite find_labelE (find_label_aux_cat_notin _ _ _ _ Hnotin) /=.
  rewrite PeanoNat.Nat.eqb_refl. f_equal. lia.
Qed.

Lemma find_label_in_procedure_at G pc l C_procs P_code pre post :
  getm (genv_procedures G) (Pointer.component pc) = Some C_procs ->
  getm C_procs (Pointer.block pc) = Some P_code ->
  P_code = pre ++ ILabel l :: post ->
  l \notin labels_of pre ->
  find_label_in_procedure G pc l
  = Some (Pointer.component pc, Pointer.block pc, Z.of_nat (size pre)).
Proof.
  move=> HC HP Hcode Hnotin.
  rewrite /find_label_in_procedure HC HP Hcode.
  by rewrite (find_label_position _ _ _ Hnotin).
Qed.

Lemma iota_rcons a n : iota a n ++ [:: a + n] = iota a n.+1.
Proof.
  by elim: n a => [|n IH] a /=; [rewrite addn0|rewrite -addSnnS IH].
Qed.

Lemma reserve_blocks_ids {m n m' bs} :
  ComponentMemoryExtra.reserve_blocks m n = (m', bs) ->
  ComponentMemory.next_block m' = ComponentMemory.next_block m + n
  /\ bs = iota (ComponentMemory.next_block m) n.
Proof.
  rewrite /ComponentMemoryExtra.reserve_blocks.
  elim: n m' bs => [|n IH] m' bs /=.
  - move=> [<- <-]. by rewrite addn0.
  - case E: (iter n _ (m, [::])) => [m0 bs0] /=.
    case E2: (ComponentMemory.reserve_block m0) => [m1 b1] [<- <-].
    have [IH1 IH2] := IH _ _ E.
    have [Eb1 En1] := ComponentMemory.reserve_block_next _ _ _ E2.
    split.
    + rewrite En1 IH1. lia.
    + by rewrite IH2 Eb1 IH1 iota_rcons.
Qed.

Lemma In_assoc_nth {K : eqType} {V : Type} (l : seq (K * V)) (P : K) (cd : V)
      (k0 : K) (v0 : V) :
  List.In (P, cd) l ->
  exists i, [/\ i < size l, nth k0 (unzip1 l) i = P & nth v0 (unzip2 l) i = cd].
Proof.
  elim: l => [|[k v] l IH] //= HIn.
  case: HIn => [E|HIn].
  - case: E => -> ->. by exists 0.
  - have [i [Hi H1 H2]] := IH HIn.
    by exists i.+1.
Qed.

Lemma getm_def_zip_nth {K : ordType} {V : Type} (ks : seq K) (vs : seq V)
      (k0 : K) (v0 : V) i :
  uniq ks -> i < size ks -> i < size vs ->
  getm_def (zip ks vs) (nth k0 ks i) = Some (nth v0 vs i).
Proof.
  elim: ks vs i => [|k ks IH] [|v vs] [|i] //=.
  - by rewrite eqxx.
  - move=> /andP [Hk Huniq] Hik Hiv.
    have Hmem : nth k0 ks i \in ks by apply: mem_nth.
    have -> : (nth k0 ks i == k) = false.
    { apply/eqP => E. by rewrite -E Hmem in Hk. }
    exact: IH.
Qed.

Lemma getm_def_pmap_guard {V : Type} (f : nat * V -> option (nat * V))
      (cond : nat -> bool)
      (ks : seq nat) (vs : seq V) (k0 : nat) (v0 : V) i :
  (forall kv, f kv = if cond kv.1 then Some kv else None) ->
  uniq ks -> i < size ks -> i < size vs ->
  cond (nth k0 ks i) ->
  getm_def (pmap f (zip ks vs)) (nth k0 ks i)
  = Some (nth v0 vs i).
Proof.
  move=> Hf.
  elim: ks vs i => [|k ks IH] [|v vs] [|i] //=.
  - move=> _ _ _ Hcond. by rewrite Hf /= Hcond /= eqxx.
  - move=> /andP [Hk Huniq] Hik Hiv Hcond.
    have Hmem : nth k0 ks i \in ks by apply: mem_nth.
    have Hne : (nth k0 ks i == k) = false.
    { apply/eqP => E. by rewrite -E Hmem in Hk. }
    rewrite Hf /=. case: (cond k) => /=.
    + rewrite Hne. exact: IH.
    + exact: IH.
Qed.

Lemma nth_assoc_In {K : eqType} {V : Type} (l : seq (K * V)) k0 v0 i :
  i < size l ->
  List.In (nth k0 (unzip1 l) i, nth v0 (unzip2 l) i) l.
Proof.
  elim: l i => [|[k v] l IH] [|i] //=.
  - by move=> _; left.
  - move=> Hi. right. exact: IH.
Qed.

Lemma getm_zip_inv {V : Type} (bs : seq Block.id) (vs : seq V) b cd :
  size bs = size vs ->
  getm (mkfmap (zip bs vs)) b = Some cd ->
  exists i, [/\ i < size bs, nth 0 bs i = b & nth cd vs i = cd].
Proof.
  move=> Hsz. rewrite mkfmapE => /getm_def_In HIn.
  have [i [Hi H1 H2]] := In_assoc_nth _ _ _ 0 cd HIn.
  rewrite size_zip -Hsz minnn in Hi.
  rewrite unzip1_zip in H1; last by rewrite Hsz.
  rewrite unzip2_zip in H2; last by rewrite Hsz.
  by exists i.
Qed.

Lemma genv_procedures_getm tp C :
  getm (genv_procedures (prepare_global_env tp)) C =
  if C \in domm (Intermediate.prog_interface tp) then
    Some (Intermediate.reserve_component_blocks tp C
            (ComponentMemory.prealloc
               (odflt emptym (getm (Intermediate.prog_buffers tp) C)))
            (elementsm (odflt emptym (getm (Intermediate.prog_procedures tp) C)))).1.2
  else None.
Proof.
  rewrite /prepare_global_env /Intermediate.prepare_procedures_initial_memory
          /Intermediate.prepare_procedures_initial_memory_aux /=.
  rewrite mapmE mkfmapfE.
  by case: (C \in domm (Intermediate.prog_interface tp)).
Qed.

Lemma genv_entrypoints_getm tp C :
  getm (genv_entrypoints (prepare_global_env tp)) C =
  if C \in domm (Intermediate.prog_interface tp) then
    Some (Intermediate.reserve_component_blocks tp C
            (ComponentMemory.prealloc
               (odflt emptym (getm (Intermediate.prog_buffers tp) C)))
            (elementsm (odflt emptym (getm (Intermediate.prog_procedures tp) C)))).2
  else None.
Proof.
  rewrite /prepare_global_env /Intermediate.prepare_procedures_initial_memory
          /Intermediate.prepare_procedures_initial_memory_aux /=.
  rewrite mapmE mkfmapfE.
  by case: (C \in domm (Intermediate.prog_interface tp)).
Qed.

Lemma compiled_code_anchor tp C Cprocs P cd :
  C \in domm (Intermediate.prog_interface tp) ->
  getm (Intermediate.prog_procedures tp) C = Some Cprocs ->
  getm Cprocs P = Some cd ->
  exists b CprocsB,
    [/\ getm (genv_procedures (prepare_global_env tp)) C = Some CprocsB,
        getm CprocsB b = Some cd,
        (forall CI, getm (Intermediate.prog_interface tp) C = Some CI ->
          (P \in Component.export CI)
          || (Intermediate.prog_main tp
              && ((Component.main =? C) && (Procedure.main =? P))) ->
          EntryPoint.get C P (genv_entrypoints (prepare_global_env tp)) = Some b)
      & forall b' cd', getm CprocsB b' = Some cd' -> b' <> b ->
          exists P0, P0 <> P /\ getm Cprocs P0 = Some cd'].
Proof.
  move=> HC Hprocs HP.
  rewrite genv_procedures_getm HC Hprocs /=.
  rewrite /Intermediate.reserve_component_blocks.
  case Erb: (ComponentMemoryExtra.reserve_blocks _ _) => [cm' bs] /=.
  have [_ Ebs] := reserve_blocks_ids Erb.
  have Hlen := ComponentMemoryExtra.reserve_blocks_length _ _ _ _ Erb.
  have Huniqbs : uniq bs by rewrite Ebs; apply: iota_uniq.
  have HIn := getm_In_elementsm HP.
  have Huk : uniq (unzip1 (elementsm Cprocs)).
  { exact: (sorted_uniq (@Ord.lt_trans _) (@Ord.ltxx _) (valP Cprocs)). }
  have [i [Hi Hnth1 Hnth2]] := In_assoc_nth _ _ _ P cd HIn.
  have Hibs : i < size bs.
  { move: Hlen. rewrite /length -/(size _) -/(size _) => ->. by []. }
  exists (nth 0 bs i), (mkfmap (zip bs (unzip2 (elementsm Cprocs)))).
  split.
  - by [].
  - rewrite mkfmapE.
    rewrite (getm_def_zip_nth _ _ 0 cd i Huniqbs Hibs); last first.
    + by rewrite /unzip1 /unzip2 size_map.
    + by rewrite Hnth2.
  - move=> CI HCI Hguard.
    rewrite /EntryPoint.get genv_entrypoints_getm HC Hprocs /=.
    rewrite /Intermediate.reserve_component_blocks Erb /=.
    rewrite mkfmapE -Hnth1.
    apply: (getm_def_pmap_guard _
              (fun P0 => (P0 \in Component.export CI)
                 || (Intermediate.prog_main tp
                     && ((Component.main =? C) && (Procedure.main =? P0))))
              _ _ P 0 i).
    + by move=> [P0 b0] /=; rewrite HCI.
    + exact: Huk.
    + rewrite /unzip1 size_map. exact: Hi.
    + exact: Hibs.
    + rewrite Hnth1. exact: Hguard.
  -
    move=> b' cd' Hb' Hne.
    have Hsz2 : size bs = size (unzip2 (elementsm Cprocs)).
    { rewrite /unzip2 size_map. move: Hlen.
      rewrite /length -/(size _) -/(size _). by move=> ->. }
    have [i' [Hi' Hbnth Hcdnth]] := getm_zip_inv _ _ _ _ Hsz2 Hb'.
    have Hi'e : i' < size (elementsm Cprocs).
    { move: Hi'. move: Hlen. rewrite /length -/(size _) -/(size _).
      by move=> ->. }
    exists (nth P (unzip1 (elementsm Cprocs)) i').
    have HInP0 := nth_assoc_In (elementsm Cprocs) P cd' i' Hi'e.
    rewrite Hcdnth in HInP0.
    split.
    + move=> E.
      have Hu1 : i' < size (unzip1 (elementsm Cprocs))
        by rewrite /unzip1 size_map.
      have Hu2 : i < size (unzip1 (elementsm Cprocs))
        by rewrite /unzip1 size_map.
      have /eqP Ei : i' == i.
      { rewrite -(nth_uniq P Hu1 Hu2 Huk). apply/eqP. by rewrite Hnth1 E. }
      case: Hne. by rewrite -Hbnth Ei.
    + exact: In_elementsm_getm HInP0.
Qed.

Lemma compile_procedures_aux_untouchedP C lbp scr plm
      (ps : list (Procedure.id * expr)) acc s out s' P :
  compile_procedures_aux C lbp scr plm acc ps s = Some (out, s') ->
  P \notin unzip1 ps ->
  getm_def out P = getm_def acc P.
Proof.
  elim: ps acc s => [|[P0 e0] ps IH] acc s /=.
  - rewrite /Comp.ret. by move=> [<- _].
  - rewrite /Comp.bind.
    case Ep: (compile_proc C lbp scr plm P0 e0 s) => [[cd s1]|]; last by [].
    rewrite /=. move=> Hrest.
    rewrite in_cons negb_or => /andP [HneqP HnotinP].
    rewrite (IH _ _ Hrest HnotinP) /=.
    by rewrite (negbTE HneqP).
Qed.

Lemma compile_procedures_aux_getP C lbp scr plm
      (ps : list (Procedure.id * expr)) acc s out s' P e :
  compile_procedures_aux C lbp scr plm acc ps s = Some (out, s') ->
  uniq (unzip1 ps) ->
  List.In (P, e) ps ->
  exists s1 s2 cd,
    compile_proc C lbp scr plm P e s1 = Some (cd, s2)
    /\ getm_def out P = Some cd.
Proof.
  elim: ps acc s => [|[P0 e0] ps IH] acc s //=.
  rewrite /Comp.bind.
  case Ep: (compile_proc C lbp scr plm P0 e0 s) => [[cd0 s1]|]; last by [].
  rewrite /=. move=> Hrest /andP [HP0 Huniq] [E|HIn].
  - case: E => E1 E2. subst P0 e0.
    exists s, s1, cd0. split; first by [].
    by rewrite (compile_procedures_aux_untouchedP _ _ _ _ _ _ _ _ _ _ Hrest HP0) /= eqxx.
  - exact: IH Hrest Huniq HIn.
Qed.

Lemma compile_prog_procedures_spec {p tp} :
  Source.well_formed_program p ->
  compile_program p = Some tp ->
  exists labels cenv1,
    gen_all_procedures_labels (elementsm (Source.prog_procedures p)) init_env
      = Some (labels, cenv1)
    /\ forall C Cprocs P e,
         getm (Source.prog_procedures p) C = Some Cprocs ->
         getm Cprocs P = Some e ->
         exists plm Cprocs' cd s1 s2,
           [/\ getm labels C = Some plm,
               getm (Intermediate.prog_procedures tp) C = Some Cprocs',
               getm Cprocs' P = Some cd
             & compile_proc C (C, 0, 0%Z) (C, 1, 0%Z) plm P e s1 = Some (cd, s2)].
Proof.
  move=> Hwf.
  rewrite /compile_program /Comp.run /= /Comp.bind /=.
  case E1: (gen_all_procedures_labels _ init_env) => [[labels cenv1]|] //=.
  case E2: (compile_components _ _ _ cenv1) => [[code cenv2]|] //=.
  have Huniq : uniq (unzip1 (elementsm (Source.prog_procedures p))).
  { exact: (sorted_uniq (@Ord.lt_trans _) (@Ord.ltxx _)
              (valP (Source.prog_procedures p))). }
  have Hcore : forall C Cprocs P e,
      getm (Source.prog_procedures p) C = Some Cprocs ->
      getm Cprocs P = Some e ->
      exists plm cds cd s1 s2,
        [/\ getm labels C = Some plm,
            getm_def code C = Some (mkfmap cds),
            getm (mkfmap cds) P = Some cd
          & compile_proc C (C, 0, 0%Z) (C, 1, 0%Z) plm P e s1 = Some (cd, s2)].
  { move=> C Cprocs P e HgetC HgetP.
    have HIn := getm_In_elementsm HgetC.
    move: E2. rewrite /compile_components => E2.
    have [plm [sC [cds [sC' [Hpls Hag [Hcp Hout]]]]]]
      := compile_components_aux_getC _ _ _ _ _ _ _ _ _ E2 Huniq HIn.
    have HuniqP : uniq (unzip1 (elementsm Cprocs)).
    { exact: (sorted_uniq (@Ord.lt_trans _) (@Ord.ltxx _) (valP Cprocs)). }
    have HInP := getm_In_elementsm HgetP.
    move: Hcp. rewrite /compile_procedures => Hcp.
    have [s1 [s2 [cd [Hcpr Hcd]]]]
      := compile_procedures_aux_getP _ _ _ _ _ _ _ _ _ _ _ Hcp HuniqP HInP.
    exists plm, cds, cd, s1, s2.
    split=> //.
    by rewrite mkfmapE.
  }
  rewrite /Comp.ret /=.
  move=> [<-] /=. exists labels, cenv1. split; first by [].
  move=> C Cprocs P e HgetC HgetP.
  have [plm [cds [cd [s1 [s2 [Hplm Hcode Hcd Hcp]]]]]] := Hcore _ _ _ _ HgetC HgetP.
  exists plm, (mkfmap cds), cd, s1, s2.
  split=> //.
  by rewrite mkfmapE Hcode.
Qed.

Definition cnt (s : comp_env) (C : Component.id) : nat :=
  odflt 0 (getm (next_label s) C).

Lemma cnt_fresh_label C s l s' :
  fresh_label C s = Some (l, s') ->
  l = cnt s C /\ cnt s' C = (cnt s C).+1.
Proof.
  rewrite fresh_labelE => [[<- <-]].
  by rewrite /cnt /= setmE eqxx /=.
Qed.

Definition in_window (a b : nat) (l : label) : bool := (a <= l) && (l < b).

Lemma in_window_widen a a' b b' l :
  a' <= a -> b <= b' -> in_window a b l -> in_window a' b' l.
Proof. rewrite /in_window => Ha Hb /andP [H1 H2]. apply/andP. split; lia. Qed.

Lemma all_window_widen a a' b b' ls :
  a' <= a -> b <= b' ->
  all (in_window a b) ls -> all (in_window a' b') ls.
Proof.
  move=> Ha Hb /allP Hall. apply/allP => l Hl.
  exact: in_window_widen Ha Hb (Hall _ Hl).
Qed.

Lemma all_window_uniq_cat a b c ls1 ls2 :
  all (in_window a b) ls1 -> all (in_window b c) ls2 ->
  uniq ls1 -> uniq ls2 -> uniq (ls1 ++ ls2).
Proof.
  move=> /allP H1 /allP H2 U1 U2.
  rewrite cat_uniq U1 U2 andbT /=.
  apply/hasPn => l Hl2. apply/negP => Hl1.
  have /andP [_ Hb] := H1 _ Hl1.
  have /andP [Hb' _] := H2 _ Hl2.
  lia.
Qed.

Lemma all_window_notin a b l ls :
  all (in_window a b) ls -> ~~ in_window a b l -> l \notin ls.
Proof.
  move=> /allP Hall Hnot. apply/negP => Hl.
  by rewrite (Hall _ Hl) in Hnot.
Qed.

Lemma uniq_cat_notin (ls1 ls2 : seq label) :
  uniq ls1 -> uniq ls2 ->
  (forall x, x \in ls1 -> x \notin ls2) ->
  uniq (ls1 ++ ls2).
Proof.
  move=> U1 U2 Hdisj.
  rewrite cat_uniq U1 U2 andbT /=.
  apply/hasPn => x Hx2. apply/negP => Hx1.
  by move: (Hdisj _ Hx1); rewrite Hx2.
Qed.

Lemma notin_all_window x a b ls :
  all (in_window a b) ls -> (x < a) || (b <= x) -> x \notin ls.
Proof.
  move=> A H. apply: all_window_notin A _. rewrite /in_window. lia.
Qed.

Lemma uniq_if_labels a0 a1 a2 a3 (l1 l3 l2 : seq label) lc le :
  a0 <= a1 -> a1 <= a2 -> a2 <= a3 ->
  all (in_window a0 a1) l1 ->
  all (in_window a2 a3) l3 ->
  all (in_window a1 a2) l2 ->
  lc = a3 -> le = a3.+1 ->
  uniq l1 -> uniq l3 -> uniq l2 ->
  uniq (l1 ++ l3 ++ lc :: l2 ++ [:: le]).
Proof.
  move=> H01 H12 H23 A1 A3 A2 Elc Ele U1 U3 U2. subst lc le.
  apply: uniq_cat_notin U1 _ _; last first.
  - move=> x Hx. have /andP [Hxa Hxb] := allP A1 _ Hx.
    rewrite mem_cat in_cons mem_cat in_cons /= orbF !negb_or.
    apply/and4P. split.
    + apply: notin_all_window A3 _. lia.
    + rewrite -[_ == _]negbK. apply/negPn/negP. move/eqP => E. lia.
    + apply: notin_all_window A2 _. lia.
    + rewrite -[_ == _]negbK. apply/negPn/negP. move/eqP => E. lia.
  - apply: uniq_cat_notin U3 _ _; last first.
    + move=> x Hx. have /andP [Hxa Hxb] := allP A3 _ Hx.
      rewrite in_cons mem_cat in_cons /= orbF !negb_or.
      apply/and3P. split.
      * rewrite -[_ == _]negbK. apply/negPn/negP. move/eqP => E. lia.
      * apply: notin_all_window A2 _. lia.
      * rewrite -[_ == _]negbK. apply/negPn/negP. move/eqP => E. lia.
    + rewrite /= mem_cat in_cons /= orbF negb_or.
      apply/andP. split.
      * apply/andP. split.
        -- apply: notin_all_window A2 _. lia.
        -- rewrite -[_ == _]negbK. apply/negPn/negP. move/eqP => E. lia.
      * apply: uniq_cat_notin U2 _ _; first by [].
        move=> x Hx. have /andP [Hxa Hxb] := allP A2 _ Hx.
        rewrite in_cons /= orbF.
        rewrite -[_ == _]negbK. apply/negPn/negP. move/eqP => E. lia.
Qed.

Lemma all_if_labels a0 a1 a2 a3 b (l1 l3 l2 : seq label) lc le :
  a0 <= a1 -> a1 <= a2 -> a2 <= a3 -> a3.+2 <= b ->
  all (in_window a0 a1) l1 ->
  all (in_window a2 a3) l3 ->
  all (in_window a1 a2) l2 ->
  lc = a3 -> le = a3.+1 ->
  all (in_window a0 b) (l1 ++ l3 ++ lc :: l2 ++ [:: le]).
Proof.
  move=> H01 H12 H23 H3b A1 A3 A2 -> ->.
  apply/allP => x. rewrite mem_cat => /orP [Hx|].
  - have /andP [? ?] := allP A1 _ Hx. rewrite /in_window. lia.
  - rewrite mem_cat => /orP [Hx|].
    + have /andP [? ?] := allP A3 _ Hx. rewrite /in_window. lia.
    + rewrite in_cons => /orP [/eqP ->|].
      * rewrite /in_window. lia.
      * rewrite mem_cat => /orP [Hx|].
        -- have /andP [? ?] := allP A2 _ Hx. rewrite /in_window. lia.
        -- rewrite in_cons orbF => /eqP ->. rewrite /in_window. lia.
Qed.

Lemma compile_expr_labels C lbp scr plm e s c s' :
  compile_expr C lbp scr plm e s = Some (c, s') ->
  [/\ cnt s C <= cnt s' C,
      all (in_window (cnt s C) (cnt s' C)) (labels_of c)
    & uniq (labels_of c)].
Proof.
  elim: e s c s' => [v| | |bop e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2 e3 IH3
                    |e IH|e IH|e1 IH1 e2 IH2|C' P' e IH|] s c s' Hc.
  -
    case: v Hc => [i|p|] Hc.
    + move: Hc => /= [<- <-]. by split=> //; exact: leqnn.
    + by move: Hc.
    + by move: Hc.
  -
    move: Hc => /= [<- <-]. by split=> //; exact: leqnn.
  -
    move: Hc => /= [<- <-]. by split=> //; exact: leqnn.
  -
    move: Hc; rewrite /= /Comp.bind /Comp.ret.
    case E1: (compile_expr C lbp scr plm e1 s) => [[c1 s1]|]; last by [].
    rewrite /=.
    case E2: (compile_expr C lbp scr plm e2 s1) => [[c2 s2]|]; last by [].
    rewrite /=. move=> [<- <-].
    have [M1 A1 U1] := IH1 _ _ _ E1.
    have [M2 A2 U2] := IH2 _ _ _ E2.
    rewrite /push /pop ?labels_of_cat /= ?labels_of_cat /= ?cats0.
    split.
    + exact: leq_trans M1 M2.
    + rewrite all_cat. apply/andP. split.
      * by apply: all_window_widen A1; lia.
      * by apply: all_window_widen A2; lia.
    + exact: all_window_uniq_cat A1 A2 U1 U2.
  -
    move: Hc; rewrite /= /Comp.bind /Comp.ret.
    case E1: (compile_expr C lbp scr plm e1 s) => [[c1 s1]|]; last by [].
    rewrite /=.
    case E2: (compile_expr C lbp scr plm e2 s1) => [[c2 s2]|]; last by [].
    rewrite /=. move=> [<- <-].
    have [M1 A1 U1] := IH1 _ _ _ E1.
    have [M2 A2 U2] := IH2 _ _ _ E2.
    rewrite labels_of_cat.
    split.
    + exact: leq_trans M1 M2.
    + rewrite all_cat. apply/andP. split.
      * by apply: all_window_widen A1; lia.
      * by apply: all_window_widen A2; lia.
    + exact: all_window_uniq_cat A1 A2 U1 U2.
  -
    move: Hc; rewrite /= /Comp.bind /Comp.ret.
    case E1: (compile_expr C lbp scr plm e1 s) => [[c1 s1]|]; last by [].
    rewrite /=.
    case E2: (compile_expr C lbp scr plm e2 s1) => [[c2 s2]|]; last by [].
    rewrite /=.
    case E3: (compile_expr C lbp scr plm e3 s2) => [[c3 s3]|]; last by [].
    rewrite /=.
    case EL1: (fresh_label C s3) => [[lconseq s4]|]; last by [].
    rewrite /=.
    case EL2: (fresh_label C s4) => [[lend s5]|]; last by [].
    rewrite /=. move=> [<- <-].
    have [M1 A1 U1] := IH1 _ _ _ E1.
    have [M2 A2 U2] := IH2 _ _ _ E2.
    have [M3 A3 U3] := IH3 _ _ _ E3.
    have [Elc Hc4] := cnt_fresh_label _ _ _ _ EL1.
    have [Ele Hc5] := cnt_fresh_label _ _ _ _ EL2.
    rewrite Hc4 in Ele. rewrite Hc4 in Hc5.
    rewrite ?labels_of_cat /= ?labels_of_cat /= ?labels_of_cat /= ?cats0.
    have HB1 : cnt s1 C <= cnt s5 C by lia.
    have HB2 : cnt s2 C <= cnt s5 C by lia.
    split.
    + lia.
    + by apply: (all_if_labels (cnt s C) (cnt s1 C) (cnt s2 C) (cnt s3 C))
        => //; lia.
    + apply: (uniq_if_labels (cnt s C) (cnt s1 C) (cnt s2 C) (cnt s3 C))
        => //; lia.
  -
    move: Hc; rewrite /= /Comp.bind /Comp.ret.
    case E1: (compile_expr C lbp scr plm e s) => [[c0 s1]|]; last by [].
    rewrite /=. move=> [<- <-].
    have [M1 A1 U1] := IH _ _ _ E1.
    rewrite labels_of_cat /= ?cats0.
    by split.
  -
    move: Hc; rewrite /= /Comp.bind /Comp.ret.
    case E1: (compile_expr C lbp scr plm e s) => [[c0 s1]|]; last by [].
    rewrite /=. move=> [<- <-].
    have [M1 A1 U1] := IH _ _ _ E1.
    rewrite labels_of_cat /= ?cats0.
    by split.
  -
    move: Hc; rewrite /= /Comp.bind /Comp.ret.
    case E1: (compile_expr C lbp scr plm e1 s) => [[c1 s1]|]; last by [].
    rewrite /=.
    case E2: (compile_expr C lbp scr plm e2 s1) => [[c2 s2]|]; last by [].
    rewrite /=. move=> [<- <-].
    have [M1 A1 U1] := IH1 _ _ _ E1.
    have [M2 A2 U2] := IH2 _ _ _ E2.
    rewrite /push /pop ?labels_of_cat /= ?labels_of_cat /= ?cats0.
    split.
    + exact: leq_trans M1 M2.
    + rewrite all_cat. apply/andP. split.
      * by apply: all_window_widen A2; lia.
      * by apply: all_window_widen A1; lia.
    + apply: uniq_cat_notin U2 U1 _ => x Hx.
      have /andP [Hxa Hxb] := allP A2 _ Hx.
      apply: notin_all_window A1 _. lia.
  -
    move: Hc; rewrite /= /Comp.bind /Comp.ret /find_proc_label /Comp.lift.
    case E1: (compile_expr C lbp scr plm e s) => [[c1 s1]|]; last by [].
    rewrite /=.
    have [M1 A1 U1] := IH _ _ _ E1.
    case: (Component.eqb C' C).
    + case EL: (getm plm P') => [tl|]; last by [].
      rewrite /=. move=> [<- <-].
      rewrite /push /pop ?labels_of_cat /= ?labels_of_cat /= ?cats0.
      by split.
    + move=> [<- <-].
      rewrite /push /pop /store_arg /load_arg ?labels_of_cat /= ?labels_of_cat /= ?cats0.
      by split.
  -
    move: Hc => /= [<- <-]. by split=> //; exact: leqnn.
Qed.

Lemma labels_of_halt_pad b c :
  labels_of ((if b then [:: IHalt] else [::]) ++ c) = labels_of c.
Proof. by case: b. Qed.

Lemma compile_proc_labels C lbp scr plm P e s cd s' pl :
  compile_proc C lbp scr plm P e s = Some (cd, s') ->
  getm plm P = Some pl ->
  [/\ cnt s C <= cnt s' C,
      all (fun l => (l == pl) || in_window (cnt s C) (cnt s' C) l)
          (labels_of cd)
    & (pl < cnt s C -> uniq (labels_of cd))].
Proof.
  rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift /Comp.ret /=.
  case EL: (getm plm P) => [pl0|]; last by [].
  rewrite /= !fresh_labelE /=.
  case EE: (compile_expr C lbp scr plm e _) => [[pcode s4]|]; last by [].
  rewrite /=. move=> [<- <-] [Epl]. subst pl0.
  move: (compile_expr_labels _ _ _ _ _ _ _ _ EE) => [ME AE UE].
  rewrite {1}/cnt /= !setmE !eqxx /= -/(cnt s C) in ME.
  rewrite {1}/cnt /= !setmE !eqxx /= -/(cnt s C) in AE.
  rewrite !setmE !eqxx /= -/(cnt s C).
  case: (Component.eqb C Component.main && Procedure.eqb P Procedure.main).
  -
    rewrite labels_of_halt_pad /push /pop /load_arg /store_arg
            ?labels_of_cat /= ?labels_of_cat /= ?labels_of_cat /= ?cats0.
    split.
    + lia.
    + apply/andP; split.
      { apply/orP. right. rewrite /in_window. lia. }
      apply/andP; split.
      { apply/orP. right. rewrite /in_window. lia. }
      apply/andP; split.
      { by rewrite eqxx. }
      apply: sub_all AE => l /andP [? ?].
      apply/orP. right. rewrite /in_window. lia.
    + move=> Hpl. rewrite /=.
      apply/andP. split.
      { rewrite !in_cons !negb_or.
        apply/and3P. split.
        - rewrite -[_ == _]negbK. apply/negPn/negP. move/eqP => E. lia.
        - rewrite -[_ == _]negbK. apply/negPn/negP. move/eqP => E. lia.
        - apply: notin_all_window AE _. lia. }
      apply/andP. split.
      { rewrite !in_cons !negb_or.
        apply/andP. split.
        - rewrite -[_ == _]negbK. apply/negPn/negP. move/eqP => E. lia.
        - apply: notin_all_window AE _. lia. }
      apply/andP. split.
      { apply: notin_all_window AE _. lia. }
      exact: UE.
  -
    rewrite /push /pop /load_arg /store_arg
            ?labels_of_cat /= ?labels_of_cat /= ?labels_of_cat /= ?cats0.
    split.
    + lia.
    + apply/andP; split.
      { by rewrite eqxx. }
      apply: sub_all AE => l /andP [? ?].
      apply/orP. right. rewrite /in_window. lia.
    + move=> Hpl. rewrite /=.
      apply/andP. split.
      * apply: notin_all_window AE _. lia.
      * exact: UE.
Qed.

Lemma find_label_aux_notin c l o :
  l \notin labels_of c ->
  find_label_aux c l o = None.
Proof.
  elim: c o => [|i c IH] o //=.
  case: i => [|l'|v r|r1 r2|op r1 r2 r3|r1 r2|r1 r2|r1 r2|r l0| |l0|C0 P0| |];
    try by (move=> Hno; rewrite IH).
  rewrite in_cons negb_or => /andP [Hne Hno].
  have -> : Nat.eqb l l' = false.
  { apply/PeanoNat.Nat.eqb_neq => E. by rewrite E eqxx in Hne. }
  by rewrite IH.
Qed.

Lemma find_label_notin c l :
  l \notin labels_of c ->
  find_label c l = None.
Proof. move=> H. by rewrite find_labelE find_label_aux_notin. Qed.

Lemma find_label_in_component_at G pc pl C_procs bP cdP pre post :
  getm (genv_procedures G) (Pointer.component pc) = Some C_procs ->
  getm C_procs bP = Some cdP ->
  cdP = pre ++ ILabel pl :: post ->
  pl \notin labels_of pre ->
  (forall b cd, getm C_procs b = Some cd -> b <> bP -> pl \notin labels_of cd) ->
  find_label_in_component G pc pl
  = Some (Pointer.component pc, bP, Z.of_nat (size pre)).
Proof.
  move=> HC HB Hcode Hpre Hothers.
  rewrite /find_label_in_component HC.
  have HBin : List.In (bP, cdP) (elementsm C_procs) by exact: getm_In_elementsm.
  have : forall b cd, List.In (b, cd) (elementsm C_procs) ->
      getm C_procs b = Some cd.
  { move=> b cd HIn. exact: In_elementsm_getm. }
  elim: (elementsm C_procs) HBin => [|[b0 cd0] rest IH] //= HBin Hget.
  case: HBin => [E|HIn].
  -
    case: E => E1 E2. subst b0 cd0.
    rewrite /find_label_in_procedure /= HC HB Hcode.
    by rewrite (find_label_position _ _ _ Hpre).
  -
    have Hget0 : getm C_procs b0 = Some cd0 by apply: Hget; left.
    case Eb: (b0 == bP).
    +
      move/eqP: Eb => Eb. subst b0.
      have E0 : cd0 = cdP by move: Hget0; rewrite HB; case.
      subst cd0.
      rewrite /find_label_in_procedure /= HC HB Hcode.
      by rewrite (find_label_position _ _ _ Hpre).
    + have Hno : pl \notin labels_of cd0.
      { apply: Hothers Hget0 _. by apply/eqP; rewrite Eb. }
      rewrite /find_label_in_procedure /= HC Hget0.
      rewrite (find_label_notin _ _ Hno).
      apply: IH HIn _.
      move=> b cd HIn'. apply: Hget. by right.
Qed.

Lemma gen_component_labels_inj comp ps acc s m s' :
  gen_component_procedures_labels_aux comp acc ps s = Some (m, s') ->
  (forall P pl, getm acc P = Some pl -> pl < cnt s comp) ->
  (forall P P' pl, getm acc P = Some pl -> getm acc P' = Some pl -> P = P') ->
  [/\ (forall P pl, getm m P = Some pl -> pl < cnt s' comp)
    & (forall P P' pl, getm m P = Some pl -> getm m P' = Some pl -> P = P')].
Proof.
  elim: ps acc s => [|[P0 e0] ps IH] acc s /=.
  - rewrite /Comp.ret. move=> [<- <-] Hbnd Hinj. by split.
  - rewrite /Comp.bind fresh_labelE /=. move=> Hrest Hbnd Hinj.
    have Hbnd' : forall P pl,
        getm (setm acc P0 (cnt s comp)) P = Some pl ->
        pl < cnt {| next_label := setm (next_label s) comp
                      (1 + odflt 0 (getm (next_label s) comp)) |} comp.
    { move=> P pl. rewrite setmE /cnt /= setmE eqxx /= -/(cnt s comp).
      case: (P == P0) => [[<-]|H]; first by lia.
      have := Hbnd _ _ H. lia. }
    have Hinj' : forall P P' pl,
        getm (setm acc P0 (cnt s comp)) P = Some pl ->
        getm (setm acc P0 (cnt s comp)) P' = Some pl -> P = P'.
    { move=> P P' pl. rewrite !setmE.
      case EP: (P == P0); case EP': (P' == P0).
      - move/eqP: EP => ->. by move/eqP: EP' => ->.
      - move=> [E] H. subst pl.
        have := Hbnd _ _ H. rewrite -/(cnt s comp). lia.
      - move=> H [E]. subst pl.
        have := Hbnd _ _ H. rewrite -/(cnt s comp). lia.
      - exact: Hinj. }
    exact: IH Hrest Hbnd' Hinj'.
Qed.

Lemma compile_proc_mono C lbp scr plm P e s cd s' :
  compile_proc C lbp scr plm P e s = Some (cd, s') ->
  cnt s C <= cnt s' C.
Proof.
  rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift /Comp.ret /=.
  case EL: (getm plm P) => [pl0|]; last by [].
  rewrite /= !fresh_labelE /=.
  case EE: (compile_expr C lbp scr plm e _) => [[pcode s4]|]; last by [].
  rewrite /=. move=> [_ <-].
  move: (compile_expr_labels _ _ _ _ _ _ _ _ EE) => [ME _ _].
  rewrite {1}/cnt /= !setmE !eqxx /= -/(cnt s C) in ME.
  lia.
Qed.

Lemma compile_procedures_aux_mono C lbp scr plm
      (ps : list (Procedure.id * expr)) acc s out s' :
  compile_procedures_aux C lbp scr plm acc ps s = Some (out, s') ->
  cnt s C <= cnt s' C.
Proof.
  elim: ps acc s => [|[P0 e0] ps IH] acc s /=.
  - rewrite /Comp.ret. by move=> [_ <-].
  - rewrite /Comp.bind.
    case Ep: (compile_proc C lbp scr plm P0 e0 s) => [[cd0 s1]|]; last by [].
    rewrite /=. move=> Hrest.
    have := compile_proc_mono _ _ _ _ _ _ _ _ _ Ep.
    have := IH _ _ Hrest. lia.
Qed.

Lemma compile_procedures_aux_getP_window C lbp scr plm
      (ps : list (Procedure.id * expr)) acc s out s' P e :
  compile_procedures_aux C lbp scr plm acc ps s = Some (out, s') ->
  uniq (unzip1 ps) ->
  List.In (P, e) ps ->
  exists s1 s2 cd,
    [/\ compile_proc C lbp scr plm P e s1 = Some (cd, s2),
        getm_def out P = Some cd,
        cnt s C <= cnt s1 C
      & cnt s2 C <= cnt s' C].
Proof.
  elim: ps acc s => [|[P0 e0] ps IH] acc s //=.
  rewrite /Comp.bind.
  case Ep: (compile_proc C lbp scr plm P0 e0 s) => [[cd0 s1]|]; last by [].
  rewrite /=. move=> Hrest /andP [HP0 Huniq] [E|HIn].
  - case: E => E1 E2. subst P0 e0.
    have Hmono := compile_procedures_aux_mono _ _ _ _ _ _ _ _ _ Hrest.
    exists s, s1, cd0.
    split=> //.
    by rewrite (compile_procedures_aux_untouchedP _ _ _ _ _ _ _ _ _ _ Hrest HP0) /= eqxx.
  - have Hm0 := compile_proc_mono _ _ _ _ _ _ _ _ _ Ep.
    have [s2 [s3 [cd [Hcp Hout Ha Hb]]]] := IH _ _ Hrest Huniq HIn.
    exists s2, s3, cd.
    split=> //. lia.
Qed.

Lemma compile_proc_layout C lbp scr plm P e s cd s' pl :
  compile_proc C lbp scr plm P e s = Some (cd, s') ->
  getm plm P = Some pl ->
  exists ext rest,
    [/\ cd = ext ++ ILabel pl :: rest
      & (pl < cnt s C -> pl \notin labels_of ext)].
Proof.
  rewrite /compile_proc /find_proc_label /= /Comp.bind /Comp.lift /Comp.ret /=.
  case EL: (getm plm P) => [pl0|]; last by [].
  rewrite /= !fresh_labelE /=.
  case EE: (compile_expr C lbp scr plm e _) => [[pcode s4]|]; last by [].
  rewrite /=. move=> [<- _] [Epl]. subst pl0.
  rewrite !setmE !eqxx /= -/(cnt s C).
  case: (Component.eqb C Component.main && Procedure.eqb P Procedure.main).
  -
    do 2 eexists.
    split.
    + rewrite catA. reflexivity.
    + move=> Hpl. rewrite labels_of_halt_pad /= !in_cons orbF !negb_or.
      apply/andP. split.
      * rewrite -[_ == _]negbK. apply/negPn/negP. move/eqP => E. lia.
      * rewrite -[_ == _]negbK. apply/negPn/negP. move/eqP => E. lia.
  -
    do 2 eexists.
    split.
    + reflexivity.
    + by move=> _.
Qed.



Lemma compile_procedures_aux_inv C lbp scr plm
      (ps : list (Procedure.id * expr)) acc s out s' P0 cd0 :
  compile_procedures_aux C lbp scr plm acc ps s = Some (out, s') ->
  getm_def out P0 = Some cd0 ->
  getm_def acc P0 = Some cd0 \/
  exists e0 s1 s2,
    [/\ List.In (P0, e0) ps,
        compile_proc C lbp scr plm P0 e0 s1 = Some (cd0, s2),
        cnt s C <= cnt s1 C
      & cnt s2 C <= cnt s' C].
Proof.
  elim: ps acc s => [|[P1 e1] ps IH] acc s /=.
  - rewrite /Comp.ret. move=> [<- _] H. by left.
  - rewrite /Comp.bind.
    case Ep: (compile_proc C lbp scr plm P1 e1 s) => [[cd1 s1]|]; last by [].
    rewrite /=. move=> Hrest Hout.
    have Hm1 := compile_proc_mono _ _ _ _ _ _ _ _ _ Ep.
    have Hmono := compile_procedures_aux_mono _ _ _ _ _ _ _ _ _ Hrest.
    case: (IH _ _ Hrest Hout) => [Hacc|[e0 [sA [sB [HIn Hcp Ha Hb]]]]].
    + move: Hacc. rewrite /= .
      case EP: (P0 == P1).
      * move/eqP: EP => EP. subst P1. move=> [E]. subst cd1.
        right. exists e1, s, s1.
        by split=> //; left.
      * move=> Hacc. by left.
    + right. exists e0, sA, sB.
      split=> //; first by right.
      lia.
Qed.

Theorem compiled_component_labels {p tp} :
  Source.well_formed_program p ->
  compile_program p = Some tp ->
  exists labels cenv1,
    gen_all_procedures_labels (elementsm (Source.prog_procedures p)) init_env
      = Some (labels, cenv1)
    /\ forall C Cprocs,
         getm (Source.prog_procedures p) C = Some Cprocs ->
         exists plm lo Cprocs',
           [/\ getm labels C = Some plm,
               getm (Intermediate.prog_procedures tp) C = Some Cprocs',
               (forall P pl, getm plm P = Some pl -> pl < lo)
                 /\ (forall P P' pl, getm plm P = Some pl ->
                       getm plm P' = Some pl -> P = P'),
               (forall P e, getm Cprocs P = Some e ->
                  exists cd, getm Cprocs' P = Some cd)
             & forall P0 cd0, getm Cprocs' P0 = Some cd0 ->
                 (getm Cprocs P0 = None /\ labels_of cd0 = [::])
                 \/ exists e0 s1 s2 pl0,
                      [/\ getm Cprocs P0 = Some e0,
                          getm plm P0 = Some pl0,
                          compile_proc C (C, 0, 0%Z) (C, 1, 0%Z) plm P0 e0 s1
                            = Some (cd0, s2)
                        & lo <= cnt s1 C]].
Proof.
  move=> Hwf.
  have Huniq : uniq (unzip1 (elementsm (Source.prog_procedures p))).
  { exact: (sorted_uniq (@Ord.lt_trans _) (@Ord.ltxx _)
              (valP (Source.prog_procedures p))). }
  have [ml0 [sl0 [El0 [Hdom0 HlIn0]]]]
    := gen_all_procedures_labels_spec
         (elementsm (Source.prog_procedures p)) init_env Huniq.
  rewrite /compile_program /Comp.run /= /Comp.bind /=.
  case E1: (gen_all_procedures_labels _ init_env) => [[labels cenv1]|] //=.
  case E2: (compile_components _ _ _ cenv1) => [[code cenv2]|] //=.
  have Eml0 : ml0 = labels /\ sl0 = cenv1.
  { move: El0. rewrite E1. by case. }
  case: Eml0 => ? ?. subst ml0 sl0.
  have Hcore : forall C Cprocs,
      getm (Source.prog_procedures p) C = Some Cprocs ->
      exists plm lo cds,
        [/\ getm labels C = Some plm,
            getm_def code C = Some (mkfmap cds),
            (forall P pl, getm plm P = Some pl -> pl < lo)
              /\ (forall P P' pl, getm plm P = Some pl ->
                    getm plm P' = Some pl -> P = P'),
            (forall P e, getm Cprocs P = Some e ->
               exists cd, getm (mkfmap cds) P = Some cd)
          & forall P0 cd0, getm (mkfmap cds) P0 = Some cd0 ->
              exists e0 s1 s2 pl0,
                [/\ getm Cprocs P0 = Some e0,
                    getm plm P0 = Some pl0,
                    compile_proc C (C, 0, 0%Z) (C, 1, 0%Z) plm P0 e0 s1
                      = Some (cd0, s2)
                  & lo <= cnt s1 C]].
  { move=> C Cprocs HgetC.
    have HIn := getm_In_elementsm HgetC.
    have HuniqP : uniq (unzip1 (elementsm Cprocs)).
    { exact: (sorted_uniq (@Ord.lt_trans _) (@Ord.ltxx _) (valP Cprocs)). }
    move: E1. rewrite /gen_all_procedures_labels => E1.
    have [sC [plm [sC' [Hth1 Hgen [Hml Hth2]]]]]
      := gen_all_labels_aux_getC _ _ _ _ _ _ _ E1 Huniq HIn.
    move: Hgen. rewrite /gen_component_procedures_labels => Hgen.
    have Hbnd0 : forall P pl, getm (emptym : NMap label) P = Some pl ->
        pl < cnt sC C.
    { by move=> P pl; rewrite emptymE. }
    have Hinj0 : forall P P' pl,
        getm (emptym : NMap label) P = Some pl ->
        getm (emptym : NMap label) P' = Some pl -> P = P'.
    { by move=> P P' pl; rewrite emptymE. }
    have [Hbnd Hinj] := gen_component_labels_inj _ _ _ _ _ _ Hgen Hbnd0 Hinj0.
    move: E2. rewrite /compile_components => E2.
    have [plm2 [sC2 [cds [sC2' [Hpls Hth3 [Hcp Hout]]]]]]
      := compile_components_aux_getC _ _ _ _ _ _ _ _ _ E2 Huniq HIn.
    have Eplm : plm2 = plm. { move: Hpls. rewrite Hml. by case. }
    subst plm2.
    have Hlo2 : cnt sC2 C = cnt sC' C.
    { by rewrite /cnt Hth3 Hth2. }
    have [plm' [Hml' Hdomlbl]] := HlIn0 _ _ HIn.
    have Eplm' : plm' = plm. { move: Hml'. rewrite Hml. by case. }
    subst plm'.
    exists plm, (cnt sC' C), cds.
    split=> //.
    -
      move=> P e HgetP.
      have HInP := getm_In_elementsm HgetP.
      move: Hcp. rewrite /compile_procedures => Hcp'.
      have [s1 [s2 [cd [Hrun Hcd Hw1 Hw2]]]]
        := compile_procedures_aux_getP_window _ _ _ _ _ _ _ _ _ _ _
             Hcp' HuniqP HInP.
      exists cd. by rewrite mkfmapE.
    -
      move=> P0 cd0. rewrite mkfmapE => Hcd0.
      move: Hcp. rewrite /compile_procedures => Hcp'.
      case: (compile_procedures_aux_inv _ _ _ _ _ _ _ _ _ _ _ Hcp' Hcd0)
        => [Hacc|[e0 [s1 [s2 [HIn0 Hrun Hw1 Hw2]]]]]; first by [].
      have Hget0 : getm Cprocs P0 = Some e0 := In_elementsm_getm HIn0.
      have Hpl0 : exists pl0, getm plm P0 = Some pl0.
      { have := Hdomlbl P0. rewrite mem_domm Hget0 /=.
        case: (getm plm P0) => [pl0|] //= _. by exists pl0. }
      case: Hpl0 => pl0 Hpl0.
      exists e0, s1, s2, pl0.
      split=> //. by rewrite -Hlo2.
  }
  rewrite /Comp.ret /=.
  move=> [<-] /=. exists labels, cenv1. split; first by [].
  move=> C Cprocs HgetC.
  have [plm [lo [cds [Hml Hcode [Hbnd Hinj] Hfwd Hrev]]]] := Hcore _ _ HgetC.
  exists plm, lo, (mkfmap cds).
  split=> //.
  + by rewrite mkfmapE Hcode.
  + move=> P0 cd0 Hcd0. right. exact: Hrev Hcd0.
Qed.

Theorem compiled_jal_resolution {p tp} :
  Source.well_formed_program p ->
  compile_program p = Some tp ->
  exists labels cenv1,
    gen_all_procedures_labels (elementsm (Source.prog_procedures p)) init_env
      = Some (labels, cenv1)
    /\ forall C Cprocs P e plm pl,
         getm (Source.prog_procedures p) C = Some Cprocs ->
         getm Cprocs P = Some e ->
         getm labels C = Some plm ->
         getm plm P = Some pl ->
         C \in domm (Intermediate.prog_interface tp) ->
         forall pc, Pointer.component pc = C ->
         exists bP cd ext rest CprocsB,
           [/\ getm (genv_procedures (prepare_global_env tp)) C = Some CprocsB,
               getm CprocsB bP = Some cd,
               cd = ext ++ ILabel pl :: rest,
               (exists s1 s2,
                  compile_proc C (C, 0, 0%Z) (C, 1, 0%Z) plm P e s1
                    = Some (cd, s2))
             & find_label_in_component (prepare_global_env tp) pc pl
                 = Some (C, bP, Z.of_nat (size ext))].
Proof.
  move=> Hwf Hcomp.
  have [labels [cenv1 [Egen Hcc]]] := compiled_component_labels Hwf Hcomp.
  exists labels, cenv1. split; first by [].
  move=> C Cprocs P e plm pl HgetC HgetP Hml Hpl HCdom pc Hpc.
  have [plm' [lo [Cprocs' [Hml' HCp [Hbnd Hinj] Hfwd Hrev]]]] := Hcc _ _ HgetC.
  have E : plm' = plm. { move: Hml'. rewrite Hml. by case. }
  subst plm'.
  have [cd Hcd] := Hfwd _ _ HgetP.
  case: (Hrev _ _ Hcd) => [[Hnone _]|[e0 [s1 [s2 [pl0 [Hget0 Hpl0 Hrun Hw]]]]]].
  { by rewrite HgetP in Hnone. }
  have Ee : e0 = e. { move: Hget0. rewrite HgetP. by case. }
  have Epl0 : pl0 = pl. { move: Hpl0. rewrite Hpl. by case. }
  subst e0 pl0.
  have Hpllo := Hbnd _ _ Hpl.
  have Hpls1 : pl < cnt s1 C by lia.
  have [ext [rest [Ecd Hnotin]]]
    := compile_proc_layout _ _ _ _ _ _ _ _ _ _ Hrun Hpl.
  have Hnotin' := Hnotin Hpls1.
  have [bP [CprocsB [HgenvC HgetB Hentry Hothers]]]
    := compiled_code_anchor tp C Cprocs' P cd HCdom HCp Hcd.
  exists bP, cd, ext, rest, CprocsB.
  have HgenvC' : getm (genv_procedures (prepare_global_env tp))
                   (Pointer.component pc) = Some CprocsB.
  { by rewrite Hpc. }
  split=> //.
  - by exists s1, s2.
  - rewrite -Hpc.
    apply: (find_label_in_component_at _ _ _ _ _ _ ext rest HgenvC' HgetB Ecd
              Hnotin' _).
    move=> b0 cd0 Hb0 Hne0.
    have [P0 [HneP0 Hcd0]] := Hothers _ _ Hb0 Hne0.
    case: (Hrev _ _ Hcd0) => [[_ Hnil]|[e1 [sA [sB [pl1 [Hg1 Hp1 Hr1 Hw1]]]]]].
    + by rewrite Hnil.
    + have [Mono1 All1 _]
        := compile_proc_labels _ _ _ _ _ _ _ _ _ _ Hr1 Hp1.
      apply/negP => Hplin.
      have := allP All1 _ Hplin.
      case/orP => [/eqP Epl1|Hwin].
      * case: HneP0. apply: Hinj Hp1 _. by rewrite -Epl1.
      * move: Hwin => /andP [Hge _]. lia.
Qed.
