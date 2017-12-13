Require Import TargetSFI.CS.
Require Import TargetSFI.Machine.
Require Import TargetSFI.MachineGen.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Logic.Decidable.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Init.Logic.

Require Import Program.
Require Import EitherMonad.
Require Import SFITestUtil.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.
(* Suppress some annoying warnings: *)
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import CompCert.Events.
(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Common.Definitions.

Import CS.
Import Env.
Import RiscMachine.
Import RiscMachine.ISA.


Instance executing_dec (mem : RiscMachine.Memory.t) (pc : RiscMachine.address)
         ( i : RiscMachine.ISA.instr) : Dec (executing mem pc i).
Proof.
  apply Build_Dec. unfold ssrbool.decidable.
  unfold executing.
  destruct ( Memory.get_word mem pc0).
  - destruct w.
    + auto.
    + apply instr_eq_dec.
  - auto.
Defined.

Ltac rewrite_some v :=
  try (match goal with
       | H' : Some v = _ |- _ => rewrite H'
       | H' : _ = Some v |- _ => rewrite <- H'        
       end).

Theorem step_Equal_1:
  forall (g : Env.t) (mem1 mem2 mem': Memory.t)
         (pc pc': RiscMachine.pc)
         (regs regs' : RegisterFile.t) (t : trace) ,
    BinNatMap.Equal mem1 mem2 ->
    step g (mem1,pc,regs) t (mem',pc',regs') ->
    step g (mem2,pc,regs) t (mem',pc',regs').
Proof.
  intros g mem1 mem2 mem' pc pc' regs reg' t Hmem1 Hstep.
  apply Memory.Equal_sym in Hmem1.

  inversion Hstep; subst;
    try (match goal with
         | H' : executing _ _ _ |- _ =>
           apply executing_equal with (m1:=mem1) (m2:=mem2) in H'
         end);         
    try ( match goal with
          | H' :  Memory.Equal mem1 _ |- _ =>
            apply Memory.Equal_trans with (m1:=mem2) (m2:=mem1) (m3:=mem') in H'
          end
        );
    try assumption; try (apply Memory.Equal_sym in Hmem1; assumption); 
  [apply Nop
  | apply Const with (val:=val) (reg:=reg)
  | apply Mov with (reg_src:=reg_src) (reg_dst:=reg_dst) (val:=val)
  | apply BinOp with (op:=op) (reg_src1:=reg_src1) (reg_src2:=reg_src2)
                   (reg_dst:=reg_dst) (val1:=val1) (val2:=val2)
  | apply Load with (rptr:=rptr) (rd:=rd) (ptr:=ptr) (val:=val)
  | apply Store with (rptr:=rptr) (rs:=rs) (ptr:=ptr) (val:=val)
  | apply BnzNZ with (reg:=reg) (val:=val)
  | apply BnzZ with (reg:=reg) (offset:=offset)
  | apply Return with (reg:=reg)
  | apply Jump with (reg:=reg)
  | apply Jal
  | apply Call
  ];
  try assumption; try reflexivity. 

  rewrite_some val.
  apply Memory.get_value_Equal. apply Memory.Equal_sym in Hmem1; assumption. 

  subst.
  apply Memory.Equal_trans with (m1:=(Memory.set_value mem2 (Memory.to_address ptr) val))
                                (m3:=mem')
                                (m2:=(Memory.set_value mem1 (Memory.to_address ptr) val)).

  apply Memory.set_value_Equal with (m1:=mem2) (m2:=mem1)
                                    (ptr:=(Memory.to_address ptr)) (val:=val).
  assumption.  assumption. 
  
Qed.
  
Theorem step_Equal_2:
  forall (g : Env.t) (mem mem1 mem2 : Memory.t)
         (pc pc': RiscMachine.pc)
         (regs regs' : RegisterFile.t) (t : trace) ,
    BinNatMap.Equal mem1 mem2 ->
    step g (mem,pc,regs) t (mem1,pc',regs') ->
    step g (mem,pc,regs) t (mem2,pc',regs').
Proof.
  intros g mem mem1 mem2 pc pc' reg regs' t Hmem Hstep.
  inversion Hstep; subst;
    [apply Nop
    | apply Const with (val:=val) (reg:=reg0)
    | apply Mov with (reg_src:=reg_src) (reg_dst:=reg_dst) (val:=val)
    | apply BinOp with (op:=op) (reg_src1:=reg_src1) (reg_src2:=reg_src2)
                       (reg_dst:=reg_dst) (val1:=val1) (val2:=val2)
    | apply Load with (rptr:=rptr) (rd:=rd) (ptr:=ptr) (val:=val)
    | apply Store with (rptr:=rptr) (rs:=rs) (ptr:=ptr) (val:=val)
    | apply BnzNZ with (reg:=reg0) (val:=val)
    | apply BnzZ with (reg:=reg0) (offset:=offset)
    | apply Return with (reg:=reg0)
    | apply Jump with (reg:=reg0)
    | apply Jal
    | apply Call
    ];
    try ( match goal with
          | H' :  Memory.Equal mem _ |- _ =>
            apply Memory.Equal_trans with (m1:=mem) (m2:=mem1) (m3:=mem2) in H'
          end
        ); try assumption; try reflexivity.
  subst.
  rewrite_some val.
  apply Memory.Equal_trans with (m1:=(Memory.set_value mem (Memory.to_address ptr) val))
                                (m3:=mem2)
                                (m2:=mem1).
  assumption. assumption.
Qed.


Ltac exec_contra H :=
  match  goal with
  | [ H1 : executing _ _ _ |- _] =>
    unfold executing in H1; rewrite H in H1; inversion H1
  end.

Ltac unify_options := repeat
  match goal with
  | H1 : Some ?x = ?o , H2 : Some ?y = ?o |- _ =>
    assert (y = x) by congruence; clear H2; subst
  | H1 : Some ?x = ?o , H2 : ?o = Some ?y  |- _ =>
    assert (y = x) by congruence; clear H2; subst
  | H1 : ?o = Some ?x , H2 : Some ?y = ?o |- _ =>
    assert (y = x) by congruence; clear H2; subst
  | H1 : ?o = Some ?x , H2 : ?o = Some ?y |- _ =>
    assert (y = x) by congruence; clear H2; subst
                                              
  | H1 : Some _ = ?o , H2 : None = ?o |- _ => congruence
  | H1 : Some _ = ?o , H2 : ?o = None |- _ => congruence
  | H1 : ?o = Some _ , H2 : None = ?o |- _ => congruence
  | H1 : ?o = Some _ , H2 : ?o = None |- _ => congruence
  end.

Ltac right_inv := right; intro contra; inversion contra; subst.

Ltac inc_pc_contra H Hpc :=
  right_inv;
  try (rewrite N.eqb_refl in Hpc; inversion Hpc);
  exec_contra H.

Ltac regs_contra := 
  match goal with
  | H : RegisterFile.eqb ?r ?r = false |- _ =>
    rewrite RegisterFile.eqb_refl with
        (regs:=r) in H; inversion H
  end.

Ltac mem_contra :=
  match goal with
  | H1 : Memory.eqb ?m1 ?m2 = false, H2 : Memory.Equal ?m1 ?m2 |- _ =>
    apply Memory.eqb_Equal in H2;
    rewrite H2 in H1; inversion H1
  end.

Ltac zero_contra :=
  match goal with
  | H1 : ?v = 0, H2: ?v <> 0 |- False =>
    apply H2; apply H1
  end.

Ltac sfi_contra :=
  match goal with
  | H1 : ~ SFI.is_same_component ?pc ?mem,
         H2 : SFI.is_same_component_bool ?pc ?mem = true |- False =>
    apply H1; unfold SFI.is_same_component_bool in H2;
    apply N.eqb_eq in H2; apply H2
                                
 |  H' : SFI.is_same_component  _ _,
         H'' : SFI.is_same_component_bool  _ _ = _ 
    |- _ =>
    unfold SFI.is_same_component in H';
    unfold SFI.is_same_component_bool in H'';
    rewrite H' in H''; rewrite N.eqb_refl in H'';
    inversion H''
  
  end.

Ltac unfold_ret_trace :=
  match goal with
  | H' : Some _ = ret_trace ?g ?pc ?pc' ?gen_regs  |- _ =>
    unfold ret_trace in H';
    destruct (RegisterFile.get_register Register.R_COM gen_regs);
    destruct (get_component_name_from_id (SFI.C_SFI pc) g);
    destruct (get_component_name_from_id (SFI.C_SFI pc') g);
    inversion H'
  end.

Ltac unfold_call_trace :=
  match goal with
  | H' : Some _ = call_trace ?g ?pc ?pc' ?gen_regs  |- _ =>
    unfold call_trace in H';
    destruct (RegisterFile.get_register Register.R_COM gen_regs);
    destruct (get_component_name_from_id (SFI.C_SFI pc) g);
    destruct (get_component_name_from_id (SFI.C_SFI pc') g);
    destruct  (get_procedure pc' g);
    inversion H'
  end.

Ltac simplify_equality := repeat
  match goal with
  | H : ?x = ?x |- _ => clear H
  | H : Some ?x = Some ?y |- _ => inversion H; clear H; subst
  | H : Some _ = None |- False => inversion H
  | H : None = Some _ |- False => inversion H
  | H : IJump ?r1 = IJump ?r2 |- _ => inversion H; clear H; subst
  | H : IJal ?r1 = IJal ?r2 |- _ => inversion H; clear H; subst
  end.

Ltac ret_com_contra f H :=
  right; intro contra; inversion contra; exec_contra H;
  subst; unify_options;
  unfold_ret_trace; subst; simplify_equality;
  match goal with
  | H': (?z =? ?z) = false |- False =>
    rewrite f in H'; inversion H'
  end.

Ltac ret_comp_contra pc' H :=
  right; intro contra; inversion contra; exec_contra H; subst pc';
  subst; unify_options;
  unfold_ret_trace; subst; simplify_equality;
  match goal with
  | H': (?z =? ?z)%positive = false |- False =>
    rewrite Pos.eqb_refl in H'; inversion H'
  end.

Ltac call_ids_contra H pc'0 pc'1 ra:=
  right; intro contra; inversion contra; exec_contra H;
  subst pc'0; subst pc'1; subst ra; 
  subst; unify_options;
  unfold_call_trace; subst; simplify_equality;
  match goal with
  | H': (?z =? ?z)%positive = false |- False =>
    rewrite Pos.eqb_refl in H'; inversion H'
  end.


Ltac ret_env_contra pc' H :=
    right; intro contra; inversion contra; subst pc'; subst;
    exec_contra H; subst; simplify_equality;
    subst; unify_options; simplify_equality;
    unfold_ret_trace; subst; simplify_equality.

Ltac call_env_contra H pc'0 pc'1 ra:=
  right; intro contra; inversion contra; subst;
  exec_contra H;subst pc'0; subst pc'1; subst ra;  subst; simplify_equality;
  subst; unify_options; simplify_equality;
  unfold_call_trace; subst; simplify_equality.


Instance step_dec(g : Env.t) (st : MachineState.t) (t : trace)
         (st' : MachineState.t): Dec (step g st t st'). 
Proof.
  apply Build_Dec. unfold ssrbool.decidable.
  destruct st as [[mem pc] gen_regs].
  destruct st' as [[mem' pc'] gen_regs'].
  destruct (Memory.get_word mem pc) eqn:H.
  - destruct w.
    + right. unfold not. intro H1.
      inversion H1;
        try ( match goal with
              | H' : executing _ _ _ |- _ =>
                unfold executing in H'; subst; rewrite H in H'; auto
              end
            ).
    + destruct i as [|val reg|rs rd|op rs1 rs2 rd|rptr rd|rptr rs|r im|r|addr|].
      * (* INop *)
        destruct (Memory.eqb mem mem') eqn:Hmem.
        { (* mem = mem' *)
          apply Memory.eqb_Equal in Hmem.
          destruct t0.
          { (* empty trace *)
            destruct (N.eqb pc' (inc_pc pc)) eqn:Hpc.
            { (* pc' = pc+1 *)
              rewrite N.eqb_eq in Hpc. rewrite Hpc.
              destruct (RegisterFile.eqb gen_regs gen_regs') eqn:Hregs.
              { (* regs=regs'*)
                apply RegisterFile.eqb_eq in Hregs. rewrite Hregs.
                left. subst. apply Nop.
                unfold executing. rewrite H. reflexivity. assumption. 
              }
              { (* regs <> regs' *)
                right_inv;
                try ( apply RegisterFile.neqb_neq in Hregs;
                      apply Hregs; reflexivity);
                exec_contra H.
              }
            }
            { (* pc' <> pc+1 *) inc_pc_contra H Hpc. }
          }
          { (* non empty trace *) right_inv; exec_contra H. }
        }
        { (* mem <> mem' *) right_inv; try (mem_contra); exec_contra H. }
      * (* IConst *)
        destruct (Memory.eqb mem mem') eqn:Hmem.
        { (* mem = mem' *)
          apply Memory.eqb_Equal in Hmem.
          destruct t0.
          { (* empty trace *)
            destruct (N.eqb pc' (inc_pc pc)) eqn:Hpc.
            { (* pc' = pc+1 *)
              rewrite N.eqb_eq in Hpc. rewrite Hpc.
              destruct (RegisterFile.eqb
                          (RegisterFile.set_register reg val gen_regs)
                          gen_regs') eqn:Hregs.
              { (* regs[r<reg-val]=regs'*)                
                left. apply Const with (val:=val) (reg:=reg).
                unfold executing. rewrite H. auto.
                apply RegisterFile.eqb_eq. assumption. assumption. 
              }
              { (* regs[r<reg-val] <> regs' *)
                right_inv; try (exec_contra H);
                try ( apply RegisterFile.neqb_neq in Hregs;
                      apply Hregs; reflexivity).
                subst. 
                rewrite RegisterFile.eqb_refl with
                    (regs:=(RegisterFile.set_register reg val gen_regs)) in Hregs.
                inversion Hregs. 
              }
            }
            {  inc_pc_contra H Hpc. }
          }
          { (* non empty trace *)  right_inv; exec_contra H. }
        }
        { (* mem <> mem' *)  right_inv; try (mem_contra); exec_contra H. }

      * (* IMov *)
        destruct (Memory.eqb mem mem') eqn:Hmem.
        { (* mem = mem' *)
          apply Memory.eqb_Equal in Hmem.
          destruct t0.
          { (* empty trace *)
            destruct (N.eqb pc' (inc_pc pc)) eqn:Hpc.
            { (* pc' = pc+1 *)
              rewrite N.eqb_eq in Hpc. rewrite Hpc.
              destruct (RegisterFile.get_register rs gen_regs) eqn:Hval.
              { (* RegisterFile.get_register rs gen_regs = Some v *)               
                destruct (RegisterFile.eqb
                            (RegisterFile.set_register rd v gen_regs)
                            gen_regs') eqn:Hregs.
                { (* regs[rd<-v]=regs'*)                
                  left.
                  apply Mov with (reg_src:=rs) (reg_dst:=rd) (val:=v). 
                  unfold executing. rewrite H. auto.
                  symmetry. assumption. 
                  apply RegisterFile.eqb_eq. assumption. assumption. 
                }
                { (* regs[rd<-d] <> regs' *)
                  right_inv; try (exec_contra H).
                  subst. unify_options. regs_contra.                  
                }                
              }
              { (* RegisterFile.get_register rs gen_regs = None *)
                right_inv; try(exec_contra H); subst. unify_options. 
              }
            }
            { (* pc' <> pc+1 *)  inc_pc_contra H Hpc. }
          }
          { (* non empty trace *) right_inv; exec_contra H. }
        }
        { (* mem <> mem' *)  right_inv; try (mem_contra); exec_contra H. }
        
      *  (* IBinOp *)
        destruct (Memory.eqb mem mem') eqn:Hmem.
        { (* mem = mem' *)
          apply Memory.eqb_Equal in Hmem.
          destruct t0.
          { (* empty trace *)
            destruct (N.eqb pc' (inc_pc pc)) eqn:Hpc.
            { (* pc' = pc+1 *)
              rewrite N.eqb_eq in Hpc. rewrite Hpc.
              destruct (RegisterFile.get_register rs1 gen_regs) eqn:Hval1. rename v into v1.
              { (* RegisterFile.get_register rs gen_regs = Some v1 *)
                destruct (RegisterFile.get_register rs2 gen_regs) eqn:Hval2. rename v into v2.
                { (* RegisterFile.get_register rs2 gen_regs = Some v2 *)
                  destruct (RegisterFile.eqb
                            (RegisterFile.set_register rd (eval_binop op v1 v2) gen_regs)
                            gen_regs') eqn:Hregs.
                  { (* regs[rd<-v1 binop v2]=regs'*)                
                    left.
                    apply BinOp with (op:=op) (reg_src1:=rs1) (reg_src2:=rs2)
                                     (reg_dst:=rd) (val1:=v1) (val2:=v2).
                    unfold executing. rewrite H. reflexivity.
                    symmetry. assumption. symmetry. assumption. 
                    apply RegisterFile.eqb_eq. assumption. assumption. 
                  }
                  { (* regs[rd<-v1 binop v2]<>regs' *)
                    right_inv; try (exec_contra H).
                    subst. unify_options. 
                    subst result. 
                    regs_contra.
                  }                
                }
                { (* RegisterFile.get_register rs2 gen_regs = None *)
                  right_inv; try(exec_contra H). subst. unify_options.  
                }
              }
              { (* RegisterFile.get_register rs1 gen_regs = None *)
                right_inv; try(exec_contra H). subst. unify_options. 
              }
            }
            { (* pc' <> pc+1 *)  inc_pc_contra H Hpc. }
          }
          { (* non empty trace *) right_inv; exec_contra H. }
        }
        { (* mem <> mem' *)  right_inv; try (mem_contra); exec_contra H. }

      * (* ILoad *) 
        destruct (Memory.eqb mem mem') eqn:Hmem.
        { (* mem = mem' *)
          apply Memory.eqb_Equal in Hmem.
          destruct t0.
          { (* empty trace *)
            destruct (N.eqb pc' (inc_pc pc)) eqn:Hpc.
            { (* pc' = pc+1 *)
              rewrite N.eqb_eq in Hpc. rewrite Hpc.
              destruct (RegisterFile.get_register rptr gen_regs) eqn:Hptr.  
              { (* RegisterFile.get_register rd gen_regs = Some ptr *)
                rename v into ptr.
                destruct (Memory.get_value mem (Memory.to_address ptr)) eqn:Hval.
                { (* Memory.get_value mem (Memory.to_address ptr) = Some val *)
                  rename v into val. 
                  destruct (RegisterFile.eqb
                            (RegisterFile.set_register rd val gen_regs)
                            gen_regs') eqn:Hregs.
                  { (* regs[rd<-val]=regs'*)                
                    left.
                    apply Load with (rptr:=rptr) (rd:=rd) (ptr:=ptr) (val:=val).
                    unfold executing. rewrite H. auto.
                    symmetry. assumption. symmetry. assumption.  
                    apply RegisterFile.eqb_eq. assumption. assumption. 
                  }
                  { (* regs[rd<-d] <> regs' *)
                    right_inv; try (exec_contra H).
                    subst.
                    subst addr.  unify_options. regs_contra.
                  }                
                }
                { (* Memory.get_value mem (Memory.to_address ptr) = None *)
                  right_inv; try(exec_contra H). subst. subst addr. unify_options. 
                }
              }
              { (* RegisterFile.get_register rd gen_regs = None *)
                right_inv; try(exec_contra H). subst. unify_options.
              }
            }
            { (* pc' <> pc+1 *)  inc_pc_contra H Hpc. }
          }
          { (* non empty trace *) right_inv; exec_contra H. }
        }
        { (* mem <> mem' *)  right_inv; try (mem_contra); exec_contra H. }

      * (* Store *)
        destruct t0.
        { (* empty trace *)
          destruct (N.eqb pc' (inc_pc pc)) eqn:Hpc.
          { (* pc' = pc+1 *)
            rewrite N.eqb_eq in Hpc. rewrite Hpc.
            destruct (RegisterFile.get_register rptr gen_regs) eqn:Hptr.  
            { (* RegisterFile.get_register rd gen_regs = Some ptr *)
              rename v into ptr.
              destruct (RegisterFile.get_register rs gen_regs) eqn:Hval.
              { (*RegisterFile.get_register rs gen_regs = Some val *)
                rename v into val.                  
                destruct (RegisterFile.eqb gen_regs gen_regs') eqn:Hregs.
                { (* gen_regs = gen_regs' *)
                  apply RegisterFile.eqb_eq in Hregs. subst gen_regs'.
                  destruct (Memory.eqb
                              (Memory.set_value mem (Memory.to_address ptr) val)
                              mem') eqn:Hmem1.
                  { (*(Memory.set_value mem (Memory.to_address ptr) val)=mem'*)                
                    left.
                    apply Store with (rptr:=rptr) (rs:=rs) (ptr:=ptr) (val:=val).
                    unfold executing. rewrite H. auto.
                    symmetry. assumption. symmetry. assumption.  
                    apply Memory.eqb_Equal. assumption. 
                  }
                  { (*(Memory.set_value mem (Memory.to_address ptr) val)<>mem' *)
                    right_inv; try (exec_contra H).
                    subst. unify_options. mem_contra. 
                  }
                }
                { (* gen_regs <> gen_regs' *)
                  right_inv; try (exec_contra H). regs_contra.
                }
              }                
              { (*RegisterFile.get_register rs gen_regs = Some val *)
                right_inv; try(exec_contra H). subst. unify_options. 
              }
            }
            { (* RegisterFile.get_register rd gen_regs = None *)
              right_inv; try(exec_contra H). subst. unify_options. 
            }
          }
          { (* pc' <> pc+1 *)  inc_pc_contra H Hpc. }
        }
        { (* non empty trace *) right_inv; exec_contra H. }

      * (* Bnz *)
        destruct (Memory.eqb mem mem') eqn:Hmem.
        { (* mem = mem' *)
          apply Memory.eqb_Equal in Hmem.
          destruct t0.
          { (* empty trace *)
            destruct (RegisterFile.eqb gen_regs gen_regs') eqn:Hregs.
            { (* gen_regs = gen_regs' *)
              apply RegisterFile.eqb_eq in Hregs. subst gen_regs'.
              destruct (RegisterFile.get_register r gen_regs) eqn:Hval.
              rename v into val.
              { (*  (RegisterFile.get_register r gen_regs) = Some val *)
                destruct (Z.eqb val Z0) eqn:Hzero.
                { (* r = 0 *)
                  destruct (N.eqb pc' (inc_pc pc)) eqn:Hpc.
                  { (* pc' = pc+1 *)
                    rewrite N.eqb_eq in Hpc. rewrite Hpc.
                    left. apply BnzZ with (reg:=r) (offset:=im).
                    unfold executing. rewrite H. reflexivity.
                    apply Z.eqb_eq in Hzero. subst val. symmetry. assumption.
                    assumption. 
                  }
                  {
                    (* pc' <> pc+1 *)
                    inc_pc_contra H Hpc. subst. unify_options. 
                    apply Z.eqb_eq in Hzero.
                    zero_contra. 
                  }
                }
                { (* r <> 0 *)
                  destruct (N.eqb pc' (Z.to_N( Z.add (Z.of_N pc) im )) ) eqn:Hpc.
                  { (* pc' = pc + offset *)
                     left. rewrite N.eqb_eq in Hpc. rewrite Hpc. 
                    apply BnzNZ with (offset:=im) (G:=g)
                                           (mem:=mem) (mem':=mem')
                                           (pc:=pc) (gen_regs:=gen_regs)
                                           (reg:=r) (val:=val).
                    unfold executing. rewrite H. reflexivity.
                    symmetry. assumption.
                    intro Hzero'. subst val. inversion Hzero.
                    assumption. 
                  }
                  {  (* pc' <> pc + offset *)
                    inc_pc_contra H Hpc; subst. subst pc'0.
                    rewrite N.eqb_refl in Hpc. inversion Hpc.
                    unify_options. inversion Hzero. 
                  }
                }                
              }
              { (* RegisterFile.get_register r gen_regs = None *)
                right_inv; try(exec_contra H); subst; unify_options. 
              }
            }
            {  (* gen_regs <> gen_regs' *)
              right_inv; try (exec_contra H);
              rewrite RegisterFile.eqb_refl in Hregs; inversion Hregs. 
            }
          }
          { (* non empty trace *) right_inv; exec_contra H. }
        }
        { (* mem <> mem' *)  right_inv; try (mem_contra Hmem); exec_contra H. }

      * (* IJump *)
        destruct (Memory.eqb mem mem') eqn:Hmem.
        { (* mem = mem' *)
          apply Memory.eqb_Equal in Hmem.
          destruct (RegisterFile.eqb gen_regs gen_regs') eqn:Hregs.
          { (* gen_regs = gen_regs' *)
            apply RegisterFile.eqb_eq in Hregs. subst gen_regs'.
            destruct (RegisterFile.get_register r gen_regs) eqn:Hr.
            { (* RegisterFile.get_register reg gen_regs = Some val *)
              rename v into cptr.
              destruct (N.eqb pc' (Memory.to_address cptr)) eqn:Hpc.
              apply N.eqb_eq in Hpc. subst pc'. 
              { (* pc' = [r] *)
                  destruct(SFI.is_same_component_bool pc (Memory.to_address cptr)) eqn:Hsfi.
                  { (* SFI.is_same_component pc pc' *)
                    destruct t0.
                    { (* empty *) (* this is a Jump *)
                      left. apply Jump with (G:=g) (mem:=mem) (mem':=mem')
                                            (pc:=pc) (gen_regs:=gen_regs)
                                            (reg:=r) (addr:=cptr).
                      unfold executing. rewrite H. auto.
                      symmetry. assumption.
                      unfold SFI.is_same_component_bool in Hsfi.
                      unfold SFI.is_same_component. rewrite N.eqb_eq in Hsfi.
                      left. apply Hsfi.
                      assumption. 
                    }
                    { (* not empty *) (* contradiction *)
                      right_inv; exec_contra H. subst. subst pc'. unify_options.
                      sfi_contra.
                    }
                  }
                  { (* ~SFI.is_same_component pc pc' *)
                    destruct (SFI.is_same_component_bool
                                (Memory.to_address cptr)
                                SFI.MONITOR_COMPONENT_ID)
                             eqn:Hsfi_zero.
                    {
                      destruct t0.
                      { (* empty *) (* return to component zero *)
                        left. apply Jump with (G:=g) (mem:=mem) (mem':=mem')
                                            (pc:=pc) (gen_regs:=gen_regs)
                                            (reg:=r) (addr:=cptr).
                        unfold executing. rewrite H. auto.
                        symmetry. assumption.
                        unfold SFI.is_same_component_bool in Hsfi_zero.
                        unfold SFI.is_same_component. rewrite N.eqb_eq in Hsfi_zero.
                        right. assumption. auto.
                      }
                      {
                        (* not empty *) (* contradiction *)
                        right_inv; exec_contra H. subst. subst pc'. unify_options.
                        sfi_contra.
                      }
                    }
                    {                    
                      destruct t0 as [|e xt].
                      { (* empty *) (* contradiction *)
                        right_inv; exec_contra H; subst.
                        unfold_ret_trace. subst pc'.
                        destruct H7. 
                        unify_options.
                        sfi_contra.
                        unify_options. sfi_contra.
                      }
                      { (* not empty *) (* this should be a return *)
                        destruct xt.
                        { (* trace [e] *)
                          destruct e.
                          { (* ECall *)
                            right; intro contra; inversion contra; subst.
                            unfold_ret_trace. exec_contra H. 
                          }
                          { (* ERet *)
                            rename i into c. rename z into rcom. rename i0 into c'. 
                            destruct (RegisterFile.get_register Register.R_COM gen_regs)
                                     eqn:Hrcom.
                            rename v into rcom1.
                            destruct (get_component_name_from_id (SFI.C_SFI pc) g) eqn:Hc.
                            rename i into c1.
                            destruct (get_component_name_from_id
                                        (SFI.C_SFI
                                           (Memory.to_address cptr)) g) eqn:Hc'.
                            rename i into c1'.
                            destruct (Pos.eqb c c1) eqn:Haux.
                            rewrite Pos.eqb_eq in Haux. subst c1.
                            destruct (Pos.eqb c' c1') eqn:Haux.
                            rewrite Pos.eqb_eq in Haux. subst c1'.
                            destruct (Z.eqb rcom rcom1) eqn:Haux.
                            rewrite Z.eqb_eq in Haux. subst rcom1.
                          
                            left. apply Return with (reg:=r).
                            unfold executing. rewrite H. auto.
                            symmetry. assumption.
                            unfold ret_trace.
                            rewrite Hrcom. rewrite Hc. rewrite Hc'. simpl. reflexivity.

                            intro. sfi_contra.
                            intro. sfi_contra.
                            assumption.

                            (* rcom does not match *)
                            ret_com_contra Z.eqb_refl H. 
                         
                            (* c' does not match *)
                            ret_comp_contra pc' H. 
                          
                            (* c does not match *)
                            ret_comp_contra pc' H.
                          
                            (* Hc' failed *)
                            ret_env_contra pc' H.

                            (* Hc failed *)
                            ret_env_contra pc' H.
                            (* Hrcom failed *)
                            ret_env_contra pc' H.                          
                          }
                        }                                              
                        { (* trace [e;e';...] *)
                          right. intro contra.
                          inversion contra; clear contra; 
                            subst; exec_contra H; subst pc'; subst.
                          simplify_equality.
                          unfold_ret_trace. 
                        }
                      }
                    }
                  }
              }
              { (* pc' <> [r] *)
                right; intro contra;
                inversion contra; clear contra; subst; exec_contra H; subst pc'0;
                  subst; simplify_equality; unify_options;
                rewrite N.eqb_refl in Hpc; inversion Hpc.                
              }
            }
            { (* RegisterFile.get_register reg gen_regs = None *)
              right_inv; try(exec_contra H); subst; unify_options. 
            }
          }
          { (* gen_regs <> gen_regs' *)
            right_inv; try (exec_contra H);
              rewrite RegisterFile.eqb_refl in Hregs; inversion Hregs. 
          }
        }
        { (* mem <> mem' *)  right_inv; try (mem_contra Hmem); exec_contra H. }

      * destruct (Memory.eqb mem mem') eqn:Hmem.
        { (* mem = mem' *)
          apply Memory.eqb_Equal in Hmem.
          destruct (RegisterFile.eqb
                      (RegisterFile.set_register
                         Register.R_RA
                         (Z.of_N (inc_pc pc))
                         gen_regs)
                      gen_regs') eqn:Hregs.
          { (* gen_regs' okay *)
            destruct (N.eqb pc' addr) eqn:Hpc.
            apply N.eqb_eq in Hpc. subst addr. 
            { (* pc' = addr *)
              destruct(SFI.is_same_component_bool pc pc') eqn:Hsfi.
              { (* SFI.is_same_component pc pc' *)                
                destruct t0.
                { (* empty *) (* this is a Jal *)
                  left. apply Jal. 
                  unfold executing. rewrite H. auto.
                  apply RegisterFile.eqb_eq in Hregs. apply Hregs.
                  unfold  SFI.is_same_component_bool in Hsfi.
                  unfold  SFI.is_same_component. apply N.eqb_eq in Hsfi.
                  left. apply Hsfi.
                  assumption.
                }
                { (* not empty *) (* contradiction *)
                  right_inv; exec_contra H. subst. unify_options.
                      sfi_contra.
                }
              }
              { (* ~SFI.is_same_component pc pc' *)

                destruct (SFI.is_same_component_bool
                                pc
                                SFI.MONITOR_COMPONENT_ID)
                         eqn:Hsfi_zero.
                {
                  destruct t0 as [|e xt].
                  {  (* empty *) (* IJal from comp zero *)
                    left. apply Jal. 
                     unfold executing. rewrite H. auto.
                     apply RegisterFile.eqb_eq in Hregs. apply Hregs.
                     unfold  SFI.is_same_component_bool in Hsfi_zero.
                     unfold  SFI.is_same_component.
                     right.  
                     apply N.eqb_eq in Hsfi_zero.              
                     assumption.
                     assumption. 
                  }
                  { (* trace [e;e';...] *)
                    right. intro contra.
                    inversion contra; clear contra; 
                      subst; exec_contra H;
                        subst pc'0; subst pc'1; subst ra; subst;
                          simplify_equality.
                        sfi_contra.
                  }
                }
                {                                                         
                  destruct t0 as [|e xt].                  
                  { (* empty *) (* IJal contradiction *)
                    right_inv; exec_contra H; subst.

                    subst pc'0. subst pc'1. subst ra. simplify_equality.

                    destruct H8.
                    
                    sfi_contra. sfi_contra. 

                    unfold_call_trace.
                    
                  }
                  { (* not empty *) (* this should be a return *)
                    destruct xt.
                    { (* trace [e] *)
                      destruct e.
                      { (* ECall *)
                        
                        rename i into c. rename i0 into p.
                        rename z into rcom. rename i1 into c'. 
                        destruct (RegisterFile.get_register Register.R_COM gen_regs) eqn:Hrcom.
                        rename v into rcom1.
                        destruct (get_component_name_from_id (SFI.C_SFI pc) g) eqn:Hc.
                        rename i into c1.
                        destruct (get_component_name_from_id (SFI.C_SFI pc') g) eqn:Hc'.
                        rename i into c1'.
                        destruct (get_procedure pc' g) eqn:Hp.
                        rename i into p1.
                        
                        destruct (Pos.eqb c c1) eqn:Haux. rewrite Pos.eqb_eq in Haux. subst c1.
                        destruct (Pos.eqb c' c1') eqn:Haux. rewrite Pos.eqb_eq in Haux. subst c1'.
                        destruct (Pos.eqb p p1) eqn:Haux. rewrite Pos.eqb_eq in Haux. subst p1.
                        destruct (Z.eqb rcom rcom1) eqn:Haux. rewrite Z.eqb_eq in Haux. subst rcom1.
                        
                        left. apply Call.
                        unfold executing. rewrite H. auto.
                        apply RegisterFile.eqb_eq in Hregs. apply Hregs. 
                        unfold call_trace.
                        rewrite Hrcom. rewrite Hc. rewrite Hc'. rewrite Hp. simpl. reflexivity.

                        intro. sfi_contra. intro. sfi_contra. 
                        assumption.

                        (* rcom does not match *)
                        right; intro contra; inversion contra; exec_contra H;
                          subst pc'0; subst pc'1; subst ra; 
                            subst; unify_options.
                        unfold_call_trace. subst; simplify_equality;
                                             unify_options.
                        match goal with
                        | H': (?z =? ?z) = false |- False =>
                          rewrite Z.eqb_refl in H'; inversion H'
                        end.

                        (* p des not match *)
                        call_ids_contra H pc'0 pc'1 ra.                         
                        (* c' does not match *)
                        call_ids_contra H pc'0 pc'1 ra.                           
                        (* c does not match *)
                        call_ids_contra H pc'0 pc'1 ra.
                        (* Hp failed *)
                        call_env_contra H pc'0 pc'1 ra.
                        (* Hc' failed *)
                        call_env_contra H pc'0 pc'1 ra.
                        (* Hc failed *)
                        call_env_contra H pc'0 pc'1 ra.             
                        (* Hrcom failed *)
                        call_env_contra H pc'0 pc'1 ra.
                      }
                      { (* ERet *)
                        right; intro contra; inversion contra; exec_contra H;
                          subst pc'0; subst;
                            unify_options; simplify_equality. 
                        unfold_call_trace.
                      }
                    }
                    { (* trace [e;e';...] *)
                      right. intro contra.
                      inversion contra; clear contra; 
                        subst; exec_contra H;
                          subst pc'0; subst pc'1; subst ra; subst;
                            simplify_equality.
                      unfold_call_trace. 
                    }
                  }
                }
              }
            }
            { (* pc' <> [r] *)
              right; intro contra;
                inversion contra; clear contra; subst; exec_contra H;
                  subst pc'0; subst pc'1; subst ra; subst;
                    simplify_equality; unify_options;
                      rewrite N.eqb_refl in Hpc; inversion Hpc.                
            }
          }

          { (* gen_regs' not okay *)
            right_inv; try (exec_contra H);
              rewrite RegisterFile.eqb_refl in Hregs; inversion Hregs. 
          }
        }
        { (* mem <> mem' *)  right_inv; try (mem_contra Hmem); exec_contra H. }
      * (* Halt *)
        right.  intro contra; inversion contra; exec_contra H.
  - right. intro contra; inversion contra; exec_contra H.    
Qed.


Definition eqb_event (e1 e2: event) : bool :=
  match (e1,e2) with
  | (ECall c1 p1 a1 c1', ECall c2 p2 a2 c2') => (Component.eqb c1 c2)
                                                && (Procedure.eqb p1 p2)
                                                && (Z.eqb a1 a2)
                                                && (Component.eqb c1' c2')
  | (ERet c1 a1 c1', ERet c2 a2 c2') => (Component.eqb c1 c2)
                                        (* && (Z.eqb a1 a2) *) (* the return value should not be considered *)
                                        && (Component.eqb c1' c2')
  | _ => false
  end.

Definition trace_checker (t1 t2 : trace) : Checker :=
  let fix aux l1 l2 :=
      match (l1,l2) with
      | (nil,nil) => true
      | (e1::l1',e2::l2') => if (eqb_event e1 e2)
                             then aux l1' l2'
                             else false
      | _ => false
      end in checker (aux t1 t2).


Definition state_checker (s1 s2: MachineState.t) : Checker :=
  checker (
      (N.eqb (MachineState.getPC s1) (MachineState.getPC s2))
        && (RegisterFile.eqb (MachineState.getRegs s1) (MachineState.getRegs s2))
        && (Memory.eqb (MachineState.getMemory s1) (MachineState.getMemory s2))
    ).

Definition eval_step_complete_exec : Checker :=
  forAll genEnv (fun g =>
  forAll (genStateForEnv g) (fun st =>
  forAll (genTrace g st) (fun t =>
  forAll (genNextState g st t)
         (fun st' =>
            if (step g st t st')?
            then
              match (eval_step g st) with
              | EitherMonad.Right (t1,st1) =>
                conjoin [ (trace_checker t1 t); (state_checker st' st1) ]
              | _ =>
                checker false
              end
            else checker true (* at some point I want to have some incorrect cases to test *)
         )))).
              
                                                            

(*
What do I need to generate?
- G - global environment 
   (CN,E)
   CN - list of Component.id
   E - list of pairs (address,Procedure.id) where 
       address is the target of a Jal instruction 
       that is the compilation of a Call
- st current state
  mem
    mem[pc] = Instr ...
  pc address in mem 
  registers list of integers
   
- t trace 

- st' next state
 *)
(* I need the Prop to be decidable. *)

QuickChick eval_step_complete_exec.
                                   
  
