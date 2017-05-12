Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Events.
Require Import Common.Smallstep.
Require Import Intermediate.Machine.

Module CS.
  Import IntermediateMachine.
  
  Record program := {
    prog_interface : Program.interface;
    prog_memory : Memory.data;
    prog_entrypoints : EntryPoint.data;
    prog_entrypoints_wf :
      forall CI C,
        In CI prog_interface ->
        Component.name CI = C ->
        M.In C prog_entrypoints /\
        exists addrs, M.MapsTo C addrs prog_entrypoints
  }.

  Definition stack : Type := list (Component.id * Memory.address).

  Definition state : Type := 
    Component.id * stack * Memory.data * Register.data * Memory.address.

  Definition comp_of_state (s : state) : Component.id :=
    match s with (C,_,_,_,_) => C end.

  Definition mem_of_state (s : state) : Memory.data :=
    match s with (_,_,mem,_,_) => mem end.

  Record global_env := mkGlobalEnv {
    genv_interfaces : Program.interface;
    genv_entrypoints : EntryPoint.data;
  }.

  Definition initial_state_for (p : program) : state :=
    let mem := prog_memory p in
    let E := prog_entrypoints p in
    (0, [], mem, Register.empty, EntryPoint.get 0 0 E).

  (* predicates on states *)

  Definition initial_state p (s : state) : Prop :=
    match s with (C, d, mem, regs, pc) =>
      C = 0 /\ d = [] /\
      regs = Register.empty /\
      pc = EntryPoint.get 0 0 (prog_entrypoints p)
    end.

  Definition final_state (s : state) : Prop :=
    match s with (C, d, mem, regs, pc) =>
      executing Halt C mem pc
    end.

  Definition error_state (G : global_env) (s : state) : Prop :=
    match s with (C, d, mem, regs, pc) =>
      (* decoding error *)
      EncDec.decode (Memory.get mem C pc) = None
      (* call on the executing component *)
      \/ (exists P,
             executing (Call C P) C mem pc)
      (* illegal call, we cannot check priviledges *)
      \/ (exists C' P,
             executing (Call C' P) C mem pc ->
             let Is := genv_interfaces G in
             find (fun C'' => C =? Component.name C'') Is = None)
      (* illegal call to a not existing component *)
      \/ (exists C' P,
             executing (Call C' P) C mem pc ->
             let Is := genv_interfaces G in
             find (fun C'' => C' =? Component.name C'') Is = None)
      (* illegal call to a not imported component *)
      \/ (exists CI C' P,
             executing (Call C' P) C mem pc ->
             let Is := genv_interfaces G in
             find (fun C'' => C =? Component.name C'') Is = Some CI ->
             ~ (In (C',P) (Component.import CI)))
      (* illegal call to a not exported procedure *)
      \/ (exists C'I C' P,
             executing (Call C' P) C mem pc ->
             let Is := genv_interfaces G in
             find (fun C'' => C' =? Component.name C'') Is = Some C'I ->
             ~ (P < Component.export C'I))
      (* return with empty stack *)
      \/ (executing Return C mem pc -> d = [])
      (* return on the executing component *)
      \/ (exists addr (d' : stack),
             executing Return C mem pc ->
             d = (C, addr) :: d')
    end.

 Definition undefined_behavior_state (G : global_env) (s : state) : Prop :=
    match s with (C, d, mem, regs, pc) =>
      (* load failure *)
      (exists r1 r2,
          executing (Load r1 r2) C mem pc ->
          Memory.get mem C (Register.get r1 regs) = None)
      (* write failure *)
      \/ (exists r1 r2,
             executing (Store r1 r2) C mem pc ->
             Memory.set mem C (Register.get r1 regs) (Register.get r2 regs) = None)
    end.

  (* small-step semantics *)

  Definition eval_binop (e : binop) (a b : nat) : nat :=
    match e with
    | Add   => a + b
    | Minus => a - b
    | Mul   => a * b
    | Eq    => if a  =? b then 1 else 0
    | Leq   => if a <=? b then 1 else 0
    end.

  Reserved Notation "G |-CS s1 '=>[' t ']' s2" (at level 40).

  Inductive step (G : global_env) : state -> trace -> state -> Prop :=
  | Nop: forall mem C pc d regs,
      executing Nop C mem pc ->
      G |-CS (C,d,mem,regs,pc) =>[E0] (C,d,mem,regs,pc+1)

  | Const: forall mem C pc r cval d regs regs',
      executing (Const cval r) C mem pc ->
      regs' = Register.set r cval regs ->
      G |-CS (C,d,mem,regs,pc) =>[E0] (C,d,mem,regs',pc+1)

  | Mov: forall mem C pc r1 r2 regs regs' d,
      executing (Mov r1 r2) C mem pc ->
      regs' = Register.set r2 (Register.get r1 regs) regs ->
      G |-CS (C,d,mem,regs,pc) =>[E0] (C,d,mem,regs',pc+1)

  | BinOp: forall mem C pc r1 r1val r2 r2val r3 regs regs' d op,
      executing (BinOp op r1 r2 r3) C mem pc ->
      r1val = Register.get r1 regs ->
      r2val = Register.get r2 regs ->
      regs' = Register.set r3 (eval_binop op r1val r2val) regs ->
      G |-CS (C,d,mem,regs,pc) =>[E0] (C,d,mem,regs',pc+1)

  | Load: forall mem C pc r1 r2 regs regs' d addr memval,
      executing (Load r1 r2) C mem pc ->
      addr = Register.get r1 regs ->
      Some memval = Memory.get mem C addr ->
      regs' = Register.set r2 memval regs ->
      G |-CS (C,d,mem,regs,pc) =>[E0] (C,d,mem,regs',pc+1)

  | Store: forall mem C pc r1 r2 regs d addr value mem',
      executing (Store r1 r2) C mem pc->
      addr = Register.get r1 regs ->
      value = Register.get r2 regs ->
      Some mem' = Memory.set mem C addr value ->
      G |-CS (C,d,mem,regs,pc) =>[E0] (C,d,mem',regs,pc+1)

  | Jal: forall mem C pc val r regs regs' d,
      executing (Jal r) C mem pc->
      val = Register.get r regs ->
      regs' = Register.set r (pc+1) regs ->
      G |-CS (C,d,mem,regs,pc) =>[E0] (C,d,mem,regs',val)

  | Jump: forall mem C pc addr r regs d,
      executing (Jump r) C mem pc->
      Register.get r regs = addr ->
      G |-CS (C,d,mem,regs,pc) =>[E0] (C,d,mem,regs,addr)

  | BnzNZ: forall mem C pc offset r regs d,
      executing (Bnz r offset) C mem pc ->
      Register.get r regs <> 0 ->
      G |-CS (C,d,mem,regs,pc) =>[E0] (C,d,mem,regs,pc+offset)

  | BnzZ: forall mem C pc offset r regs d,
      executing (Bnz r offset) C mem pc ->
      Register.get r regs = 0 ->
      G |-CS (C,d,mem,regs,pc) =>[E0] (C,d,mem,regs,pc+1)

  | Call: forall mem C pc regs d d' C' P,
      executing (Call C' P) C mem pc ->
      call_is_public_and_exists (genv_interfaces G) C' P ->
      call_is_in_imports (genv_interfaces G) C C' P ->
      C' <> C ->
      d' = (C,pc+1) :: d ->
      let t := [ECall C P (Register.get Register.R_COM regs) C'] in
      let E := genv_entrypoints G in
      G |-CS (C,d,mem,regs,pc) =>[t]
             (C',d',mem,regs,EntryPoint.get C' P E)

  | Return: forall mem C pc pc' d' regs d C',
      executing Return C mem pc ->
      d = (C',pc') :: d' ->
      C <> C' ->
      let t := [ERet C (Register.get Register.R_COM regs) C'] in
      G |-CS (C,d,mem,regs,pc) =>[t] (C',d',mem,regs,pc')

  where "G |-CS s1 '=>[' t ']' s2" := (step G s1 t s2).

  (* complete program semantics *)

  Section SEMANTICS.
    Variable p : program.

    Definition semantics :=
      @Semantics_gen state global_env
                     step
                     (initial_state p)
                     final_state
                     (mkGlobalEnv (prog_interface p) (prog_entrypoints p)).
  End SEMANTICS.

  (* sanity checks *)

  Theorem states_characterization:
    forall G s,
      (exists t s', G |-CS s =>[t] s') \/
      final_state s \/
      error_state G s \/
      undefined_behavior_state G s.
  Proof.
    intros G s.
    destruct s as [[[[C d] mem] regs] pc].
    (* can we take a step? *)
    destruct (EncDec.decode (Memory.get mem C pc))
      as [instr | ?] eqn:Hdecode.
    (* case analysis on the current instruction *)
    - destruct instr.
      (* NOP *)
      + left. eexists. eexists. eapply Nop. auto.
      (* CONST *)
      + left. eexists.
        exists (C,d,mem,Register.set r n regs,pc+1).
        eapply Const; eauto.
      (* MOV *)
      + left. eexists.
        exists (C,d,mem,Register.set r0 (Register.get r regs) regs,pc+1).
        eapply Mov; eauto.
      (* BINOP *)
      + left. eexists.
        exists (C,d,mem,
                Register.set
                  r1 (eval_binop b (Register.get r regs) (Register.get r0 regs)) regs,
                pc+1).
        eapply BinOp; eauto.
      (* LOAD *)
      + (* check whether the load succeeds *)
        destruct (Memory.get mem C (Register.get r regs))
          as [memval | ?] eqn:Hload_result.
        (* SUCCESS *)
        * left. exists E0.
          exists (C,d,mem,Register.set r0 memval regs,pc+1).
          eapply Load; eauto.
        (* INVALID COMPONENT
           NOTE: with the new memory model there
                 will also be OUT OF BOUND *)
        * unfold undefined_behavior_state.
          right. right. right. left. exists r, r0. intros. auto.
      (* STORE *)
      + (* check whether the write succeeds *)
        destruct (Memory.set mem C (Register.get r regs) (Register.get r0 regs))
          as [mem' | ?] eqn:Hwrite_result.
        (* SUCCESS *)
        * left. exists E0.
          exists (C,d,mem',regs,pc+1).
          eapply Store; eauto.
        (* INVALID COMPONENT
           NOTE: with the new memory model there
                 will also be OUT OF BOUND *)
        * unfold undefined_behavior_state.
          right. right. right. right. exists r, r0.
          intros. auto. 
      (* BNZ *)
      + destruct (Register.get r regs =? 0) eqn:Hbranch;
          left; eexists; eexists.
        (* register is zero *)
        * rewrite beq_nat_true_iff in Hbranch.
          eapply BnzZ; eauto.
        (* register is not zero *)
        * rewrite beq_nat_false_iff in Hbranch.
          eapply BnzNZ; eauto.
      (* JUMP *)
      + left. eexists. exists (C,d,mem,regs,Register.get r regs).
        eapply Jump; eauto.
      (* JAL *)
      + left. eexists.
        exists (C,d,mem,Register.set r (pc+1) regs,Register.get r regs).
        eapply Jal; eauto.
      (* CALL *)
      + remember i as C'.
        remember i0 as P.
        destruct (C' =? C) eqn:Hcall_target.
        (* ERROR, call to the same component *)
        * unfold error_state.
          rewrite beq_nat_true_iff in Hcall_target.
          rewrite <- Hcall_target.
          eauto 7.
        * (* does the current component has an interface? *)
          destruct (find (fun C'' => C =? Component.name C'') (genv_interfaces G))
            as [CI | ?] eqn:Hcur_comp_existence.
          ** (* does the target component exist? *)
             rewrite beq_nat_false_iff in Hcall_target.
             destruct (find (fun C'' => C' =? Component.name C'') (genv_interfaces G))
               as [C'I | ?] eqn:Htarget_existence.
             *** (* can the component call the specified target? *)
                 destruct (find (fun entry =>
                                   match entry with
                                   | (C'',P') => andb (C'' =? C') (P' =? P)
                                   end) (Component.import CI))
                   as [[C'' P'] | ?] eqn:Hcomponent_import.
                 **** destruct (find_some
                                  (fun entry : nat * nat =>
                                     let (C'', P') := entry in (C'' =? C') && (P' =? P))
                                  _  Hcomponent_import) as [Hin_import Hcomp_names].
                      unfold andb in Hcomp_names.
                      assert (HC''C': C'' = C'). {
                        destruct (C'' =? C') eqn:HC''C'.
                        + apply beq_nat_true_iff in HC''C'. auto.
                        + inversion Hcomp_names.
                      }
                      rewrite HC''C' in Hcomp_names.
                      rewrite <- beq_nat_refl in Hcomp_names.
                      rewrite beq_nat_true_iff in Hcomp_names.
                      (* is the target procedure exported? *)
                      destruct (P <? Component.export C'I) eqn:Hproc_export.
                      ***** (* valid call, the procedure is exported *)
                            left.
                            exists [ECall C P (Register.get Register.R_COM regs) C'].
                            exists (C',(C,pc+1)::d,mem,regs,
                                    EntryPoint.get C' P (genv_entrypoints G)).
                            eapply Call; eauto.
                            ****** unfold call_is_public_and_exists.
                                   intros CI' Htarget_existence'.
                                   rewrite Htarget_existence in Htarget_existence'.
                                   inversion Htarget_existence' as [HC'IC'I'].
                                   rewrite <- HC'IC'I'.
                                   apply Nat.ltb_lt. auto.
                            ****** unfold call_is_in_imports.
                                   intros CI' Hcur_comp_existence'.
                                   rewrite Hcur_comp_existence in Hcur_comp_existence'.
                                   inversion Hcur_comp_existence' as [HCICI'].
                                   rewrite <- HCICI'.
                                   rewrite <- HC''C'. rewrite <- Hcomp_names. auto.
                      ***** (* ERROR, the procedure is not exported *)
                            right. right. left.
                            unfold error_state.
                            right. right. right. right. right. left.
                            exists C'I, C', P. intros.
                            unfold not. intro contra.
                            apply Nat.ltb_lt in contra.
                            rewrite Hproc_export in contra. inversion contra.
                 **** (* the target has not been imported *)
                      right. right. left.
                      unfold error_state.
                      right. right. right. right. left.
                      exists CI. exists C'. exists P. intros.
                      unfold not. intro contra.
                      pose (find_none
                              (fun entry : nat * nat =>
                                 let (C'', P') := entry in (C'' =? C') && (P' =? P))
                              (Component.import CI)
                              Hcomponent_import (C',P) contra) as contra'.
                      simpl in contra'. unfold andb in contra'.
                      rewrite <- beq_nat_refl, <- beq_nat_refl in contra'.
                      inversion contra'.
             *** (* ERROR, call to a component that doesn't exist *)
                 unfold error_state.
                 right. right. left.
                 right. right. right. left.
                 exists C', P. intros. auto.
          ** (* ERROR, we cannot check priviledges for the call *)
             right. right. left.
             unfold error_state.
             right. right. left.
             exists C, P. intros. auto.
      (* RETURN *)
      + (* case analysis on the stack *)
        destruct d as [? | [C' addr] d'] eqn:Hstack.
        (* ERROR, empty stack *)
        * unfold error_state. auto 11.
        (* non-empty stack, check the target component *)
        * destruct (C' =? C) eqn:Hreturn_target.
          (* ERROR, return to same component *)
          ** unfold error_state.
             rewrite beq_nat_true_iff in Hreturn_target.
             rewrite Hreturn_target.
             eauto 13.
          (* valid return *)
          ** left.
             exists [ERet C (Register.get Register.R_COM regs) C'].
             exists (C',d',mem,regs,addr).
             rewrite beq_nat_false_iff in Hreturn_target.
             eapply Return; eauto.
      (* HALT *)
      + unfold final_state. auto.
    (* we can't step because of a decode error *) 
    - unfold error_state. auto.
  Qed.
      
  Theorem determinism:
    forall G s t s1 s2,
      G |-CS s =>[t] s1 ->
      G |-CS s =>[t] s2 ->
      s1 = s2.
  Proof.
    intros G s t s1 s2 E1 E2.
    inversion E1; subst; inversion E2; subst;
      (* trivial cases *)
      try reflexivity;
      (* contradiction: different instructions at the same address *)
      try (match goal with
           | Hexec : executing _ ?COMP ?MEM ?PC,
             Hexec' : executing _ ?COMP ?MEM ?PC |- _ =>
             unfold executing in Hexec, Hexec';
             rewrite Hexec in Hexec';
             inversion Hexec'; subst; auto
           end);
      (* contradiction: different values in the same register *)
      try (match goal with
           | Hreg_neq : Register.get _ _ <> 0,
             Hreg_eq : Register.get _ _ = 0 |- _ =>
             exfalso; apply Hreg_neq; apply Hreg_eq
           end).
    (* load from the same memory address *)
    - match goal with
      | Hmemget1 : Some _ = Memory.get mem _ _,
        Hmemget2 : Some _ = Memory.get mem _ _ |- _ =>
        rewrite <- Hmemget1 in Hmemget2;
        inversion Hmemget2; subst; auto
      end.
    (* store at the same memory address *)
    - match goal with
      | Hmemset1 : Some _ = Memory.set mem C _ _,
        Hmemset2 : Some _ = Memory.set mem C _ _ |- _ =>
        rewrite <- Hmemset1 in Hmemset2;
        inversion Hmemset2; subst; auto
      end.
    (* return exactly to same component and address *)
    - match goal with
      | Hstack : (C', pc') :: d' = (_, _) :: _ |- _ =>
        inversion Hstack; subst; auto
      end.
  Qed.

  (* auxiliary lemmas *)

  Lemma step_implies_memory_existence:
    forall G s t s',
      G |-CS s =>[t] s' ->
      exists Cmem, M.MapsTo (comp_of_state s) Cmem (mem_of_state s).
  Proof.
    intros G s t s'.
    intros Hstep.
    destruct s
      as [[[[C d] mem] regs] pc] eqn:Hstate_s.
    inversion Hstep; subst;
      match goal with
      | Hexec : executing ?INSTR C mem ?PC |- _ =>
        unfold executing, Memory.get in Hexec;
          destruct (M.find (elt:=list nat) C mem)
          as [Cmem | ] eqn:HCmem;
          [ exists Cmem; simpl;
            apply (M.find_2 HCmem)
          | rewrite EncDec.decode_nothing in Hexec;
            inversion Hexec ]
      end.
  Qed.

  Lemma MapsTo_extraction:
    forall C cmem val (mem : M.t (list nat)),
      M.MapsTo C cmem (M.add C val mem) ->
      cmem = val.
  Proof.
    intros.
    apply F.add_mapsto_iff in H.
    destruct H.
    - destruct H. symmetry. auto.
    - exfalso. destruct H. destruct H. auto.
  Qed.

  Lemma epsilon_step_weakening:
    forall Is E C d1 mem mem' cmem cmem' regs regs' pc pc',
      let G := mkGlobalEnv Is E in
      M.MapsTo C cmem  mem ->
      M.MapsTo C cmem' mem' ->
      G |-CS (C,d1,mem,regs,pc) =>[E0] (C,d1,mem',regs',pc') ->
      forall E' d2 wmem,
        let G' := mkGlobalEnv Is E' in
        M.MapsTo C cmem wmem ->
        (G' |-CS (C,d2,wmem,regs,pc) =>[E0] (C,d2,wmem,regs',pc'))
        \/
        (forall wmem',
         wmem' = M.add C cmem' wmem ->
         G' |-CS (C,d2,wmem,regs,pc) =>[E0] (C,d2,wmem',regs',pc')).
  Proof.
    intros Is E C d1 mem mem' cmem cmem' regs regs' pc pc'.
    intros G HCmem HCmem' Hstep.
    intros E' d2 wmem G' HCwmem.
    inversion Hstep; subst.
    - left. apply Nop; auto.
    - left. apply Const with r cval; auto.
    - left. apply Mov with r1 r2; auto.
    - left. eapply BinOp; eauto.
    - left. eapply Load; try reflexivity.
      + assert (Hexec':
          executing (IntermediateMachine.Load r1 r2) C wmem pc). {
          unfold executing. unfold executing in H5.
          unfold Memory.get. unfold Memory.get in H5.
          rewrite (M.find_1 HCwmem).
          rewrite (M.find_1 HCmem') in H5.
          apply H5.
        } apply Hexec'.
      + assert (cmem = cmem'). {
          apply (F.MapsTo_fun HCmem HCmem').
        }
        unfold Memory.get. unfold Memory.get in H9.
        rewrite (M.find_1 HCwmem), H.
        rewrite (M.find_1 HCmem') in H9.
        apply H9.
    - unfold Memory.set in H10. 
      rewrite (M.find_1 HCmem) in H10. inversion H10. subst.
      remember (Register.get r1 regs') as r1val.
      remember (Register.get r2 regs') as r2val.
      right. intros wmem' HCwmem'.
      apply Store with r1 r2 r1val r2val; auto.
      unfold Memory.set in HCmem'.
      apply MapsTo_extraction in HCmem'.
      unfold Memory.set.
      rewrite (M.find_1 HCwmem).
      rewrite HCmem' in HCwmem'.
      rewrite HCwmem'. auto.
    - left. eapply Jal; eauto.
    - left. eapply Jump; eauto.
    - left. eapply BnzNZ.
      + assert (executing
                  (IntermediateMachine.Bnz r offset) C wmem pc). {
          unfold executing. unfold executing in H1.
          unfold Memory.get. unfold Memory.get in H1.
          rewrite (M.find_1 HCwmem).
          rewrite (M.find_1 HCmem') in H1.
          apply H1.
        } eauto.
      + auto.
    - left. eapply BnzZ.
      + assert (executing
                  (IntermediateMachine.Bnz r offset) C wmem pc). {
          unfold executing. unfold executing in H1.
          unfold Memory.get. unfold Memory.get in H1.
          rewrite (M.find_1 HCwmem).
          rewrite (M.find_1 HCmem') in H1.
          apply H1.
        } eauto.
      + auto.
  Qed.
End CS.