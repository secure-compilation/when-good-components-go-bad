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

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.
(* Suppress some annoying warnings: *)
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import CompCert.Events.
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

Theorem step_Equal_1:
  forall (g : Env.t) (mem1 mem2 mem': Memory.t)
         (pc pc': RiscMachine.pc)
         (regs regs' : RegisterFile.t) (t : trace) ,
    BinNatMap.Equal mem1 mem2 ->
    step g (mem1,pc,regs) t (mem',pc',regs') ->
    step g (mem2,pc,regs) t (mem',pc',regs').
Proof.
  intros g mem1 mem2 mem' pc pc' regs reg' t Hmem1 Hstep.
  
  inversion Hstep; subst.
  apply executing_equal with (m1:=mem1) (m2:=mem2) in H3.
  apply Memory.Equal_sym in Hmem1.
  apply Memory.Equal_trans with (m1:=mem2) (m2:=mem1) (m3:=mem') in H7. 
  apply Nop. assumption. assumption. assumption. assumption.

  apply executing_equal with (m1:=mem1) (m2:=mem2) in H4.
  apply Memory.Equal_sym in Hmem1.
  apply Memory.Equal_trans with (m1:=mem2) (m2:=mem1) (m3:=mem') in H8.
  apply Const with (val:=val) (reg:=reg). assumption. reflexivity. assumption. assumption. assumption. 

  apply executing_equal with (m1:=mem1) (m2:=mem2) in H5.
  apply Memory.Equal_sym in Hmem1.
  apply Memory.Equal_trans with (m1:=mem2) (m2:=mem1) (m3:=mem') in H9.
  apply Mov with (reg_src:=reg_src) (reg_dst:=reg_dst) (val:=val). 
  assumption. assumption. reflexivity. assumption. assumption. assumption.

  apply executing_equal with (m1:=mem1) (m2:=mem2) in H6.
  apply Memory.Equal_sym in Hmem1.
  apply Memory.Equal_trans with (m1:=mem2) (m2:=mem1) (m3:=mem') in H10.
  apply BinOp with (op:=op) (reg_src1:=reg_src1) (reg_src2:=reg_src2)
                   (reg_dst:=reg_dst) (val1:=val1) (val2:=val2).
  assumption.  assumption.  assumption. reflexivity.  assumption.  assumption.
  assumption.

  apply executing_equal with (m1:=mem1) (m2:=mem2) in H6.
  apply Memory.Equal_sym in Hmem1.
  apply Memory.Equal_trans with (m1:=mem2) (m2:=mem1) (m3:=mem') in H10.
  apply Load with (rptr:=rptr) (rd:=rd) (ptr:=ptr) (val:=val).
  assumption.  assumption.
  rewrite H8.
  apply Memory.get_value_Equal. apply Memory.Equal_sym. apply Hmem1.
  reflexivity.  assumption. assumption.  assumption.

  apply executing_equal with (m1:=mem1) (m2:=mem2) in H5.
  apply Memory.Equal_sym in Hmem1.
  apply Store with (rptr:=rptr) (rs:=rs) (ptr:=ptr) (val:=val). 
  assumption. assumption. assumption.
  apply Memory.set_value_Equal with (ptr:=(Memory.to_address ptr)) (val:=val) in Hmem1. 
  apply Memory.Equal_trans with (m1:=(Memory.set_value mem2 (Memory.to_address ptr) val))
                                (m2:=(Memory.set_value mem1 (Memory.to_address ptr) val))
                                (m3:=mem').
  assumption. assumption. assumption.

  apply executing_equal with (m1:=mem1) (m2:=mem2) in H5.
  apply Memory.Equal_sym in Hmem1.
  apply Memory.Equal_trans with (m1:=mem2) (m2:=mem1) (m3:=mem') in H9.
  apply BnzNZ with (reg:=reg) (val:=val).
  assumption. assumption. assumption. assumption. assumption. assumption.

  apply executing_equal with (m1:=mem1) (m2:=mem2) in H4.
  apply Memory.Equal_sym in Hmem1.
  apply Memory.Equal_trans with (m1:=mem2) (m2:=mem1) (m3:=mem') in H8.
  apply BnzZ with (reg:=reg) (offset:=offset).
  assumption. assumption. assumption. assumption. assumption.

  apply executing_equal with (m1:=mem1) (m2:=mem2) in H6.
  apply Memory.Equal_sym in Hmem1.
  apply Memory.Equal_trans with (m1:=mem2) (m2:=mem1) (m3:=mem') in H10.
  apply Return with (reg:=reg).
  assumption. assumption. assumption. assumption. assumption.
  assumption. assumption.

  apply executing_equal with (m1:=mem1) (m2:=mem2) in H5.
  apply Memory.Equal_sym in Hmem1.
  apply Memory.Equal_trans with (m1:=mem2) (m2:=mem1) (m3:=mem') in H9.
  apply Jump with (reg:=reg).
  assumption. assumption. assumption. assumption. assumption.
  assumption.

  apply executing_equal with (m1:=mem1) (m2:=mem2) in H4.
  apply Memory.Equal_sym in Hmem1.
  apply Memory.Equal_trans with (m1:=mem2) (m2:=mem1) (m3:=mem') in H8.
  apply Jal.
  assumption. auto. 
  assumption. assumption. assumption.

  apply executing_equal with (m1:=mem1) (m2:=mem2) in H6.
  apply Memory.Equal_sym in Hmem1.
  apply Memory.Equal_trans with (m1:=mem2) (m2:=mem1) (m3:=mem') in H10.
  apply Call. 
  assumption. auto. 
  assumption. assumption. assumption. assumption.
  assumption.
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
  inversion Hstep; subst.
  - (* Nop *)
    apply Nop. assumption.
    apply Memory.Equal_trans with (m1:=mem) (m2:=mem1) (m3:=mem2).
    assumption. assumption.
  - apply Const with (val:=val) (reg:=reg0).
    assumption. reflexivity.
    apply Memory.Equal_trans with (m1:=mem) (m2:=mem1) (m3:=mem2).
    assumption. assumption.
  - apply Mov with (reg_src:=reg_src) (reg_dst:=reg_dst) (val:=val).
    assumption. assumption. reflexivity.
    apply Memory.Equal_trans with (m1:=mem) (m2:=mem1) (m3:=mem2).
    assumption. assumption.
  - apply BinOp with (op:=op) (reg_src1:=reg_src1) (reg_src2:=reg_src2)
                   (reg_dst:=reg_dst) (val1:=val1) (val2:=val2).
    assumption. assumption. assumption. auto. 
    apply Memory.Equal_trans with (m1:=mem) (m2:=mem1) (m3:=mem2).
    assumption. assumption.
  - apply Load with (rptr:=rptr) (rd:=rd) (ptr:=ptr) (val:=val).
    assumption. assumption. auto. reflexivity.
    apply Memory.Equal_trans with (m1:=mem) (m2:=mem1) (m3:=mem2). assumption. assumption. 
  - apply Store with (rptr:=rptr) (rs:=rs) (ptr:=ptr) (val:=val).
    assumption. assumption. assumption.
    apply Memory.Equal_trans with (m1:= (Memory.set_value mem (Memory.to_address ptr) val))
                                  (m2:=mem1) (m3:=mem2). assumption. assumption.
  - apply BnzNZ with (reg:=reg0) (val:=val).
    assumption. assumption. assumption. 
    apply Memory.Equal_trans with (m1:=mem) (m2:=mem1) (m3:=mem2). assumption. assumption. 
  - apply BnzZ with (reg:=reg0) (offset:=offset).
    assumption. assumption.
    apply Memory.Equal_trans with (m1:=mem) (m2:=mem1) (m3:=mem2). assumption. assumption. 
  - apply Return with (reg:=reg0).
    assumption. assumption. assumption. assumption. 
    apply Memory.Equal_trans with (m1:=mem) (m2:=mem1) (m3:=mem2). assumption. assumption.
  - apply Jump with (reg:=reg0).
    assumption. assumption. assumption. 
    apply Memory.Equal_trans with (m1:=mem) (m2:=mem1) (m3:=mem2). assumption. assumption.
  - apply Jal.
    assumption. auto.
    apply Memory.Equal_trans with (m1:=mem) (m2:=mem1) (m3:=mem2). assumption. assumption.
  - apply Call. 
    assumption. auto. assumption. assumption.
    apply Memory.Equal_trans with (m1:=mem) (m2:=mem1) (m3:=mem2). assumption. assumption.
Qed.


Ltac exec_contra H :=
  match goal with
  | [ H1 : executing _ _ _ |- _] =>
    unfold executing in H1; rewrite H in H1; inversion H1
  end.

Ltac mem_contra Hmem :=
  match goal with
  | [ H1 : Memory.Equal _ _ |- _ ] =>
    apply Memory.eqb_Equal in H1; rewrite Hmem in H1; inversion H1
  end.

Ltac right_inv := right; intro contra; inversion contra; subst.

Ltac inc_pc_contra H Hpc :=
  right_inv;
  try (rewrite N.eqb_refl in Hpc; inversion Hpc);
  exec_contra H.

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
        { (* mem <> mem' *) right_inv; try (mem_contra Hmem); exec_contra H. }
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
        { (* mem <> mem' *)  right_inv; try (mem_contra Hmem); exec_contra H. }

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
                  subst.
                  rewrite Hval in H6. inversion H6. subst. 
                  rewrite RegisterFile.eqb_refl with
                      (regs:= (RegisterFile.set_register rd v gen_regs)) in Hregs.
                  inversion Hregs. 
                }                
              }
              { (* RegisterFile.get_register rs gen_regs = None *)
                right_inv; try(exec_contra H).
                subst. rewrite Hval in H6. inversion H6. 
              }
            }
            { (* pc' <> pc+1 *)  inc_pc_contra H Hpc. }
          }
          { (* non empty trace *) right_inv; exec_contra H. }
        }
        { (* mem <> mem' *)  right_inv; try (mem_contra Hmem); exec_contra H. }
        
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
                            (RegisterFile.set_register rd (executing_binop op v1 v2) gen_regs)
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
                    subst.
                    rewrite Hval1 in H6. inversion H6.
                    rewrite Hval2 in H7. inversion H7. subst.
                    subst result. 
                    rewrite RegisterFile.eqb_refl with
                        (regs:=  (RegisterFile.set_register rd
                                                            (executing_binop op v1 v2)
                                                            gen_regs)) in Hregs.
                    inversion Hregs. 
                  }                
                }
                { (* RegisterFile.get_register rs2 gen_regs = None *)
                  right_inv; try(exec_contra H).
                  subst. rewrite Hval2 in H7. inversion H7. 
                }
              }
              { (* RegisterFile.get_register rs1 gen_regs = None *)
                right_inv; try(exec_contra H).
                subst. rewrite Hval1 in H6. inversion H6. 
              }
            }
            { (* pc' <> pc+1 *)  inc_pc_contra H Hpc. }
          }
          { (* non empty trace *) right_inv; exec_contra H. }
        }
        { (* mem <> mem' *)  right_inv; try (mem_contra Hmem); exec_contra H. }

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
                    subst addr.
                    rewrite <- H6 in Hptr. inversion Hptr. subst. 
                    rewrite Hval in H7. inversion H7. subst. 
                    rewrite RegisterFile.eqb_refl with
                        (regs:= (RegisterFile.set_register rd val gen_regs)) in Hregs.
                    inversion Hregs. 
                  }                
                }
                { (* Memory.get_value mem (Memory.to_address ptr) = None *)
                  right_inv; try(exec_contra H). subst.
                  rewrite <- H6 in Hptr. inversion Hptr. subst. subst addr.
                  rewrite <- H7 in Hval. inversion Hval.  
                }
              }
              { (* RegisterFile.get_register rd gen_regs = None *)
                right_inv; try(exec_contra H). subst.
                rewrite Hptr in H6. inversion H6. 
              }
            }
            { (* pc' <> pc+1 *)  inc_pc_contra H Hpc. }
          }
          { (* non empty trace *) right_inv; exec_contra H. }
        }
        { (* mem <> mem' *)  right_inv; try (mem_contra Hmem); exec_contra H. }

      * (* Store *)
        
      Admitted.


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

Definition eqb_regs (regs1 regs2 : RegisterFile.t) : bool :=
    let fix aux l1 l2 :=
      match (l1,l2) with
      | (nil,nil) => true
      | (r1::l1',r2::l2') => if (Z.eqb r1 r2)
                             then aux l1' l2'
                             else false
      | _ => false
      end in (aux regs1 regs2).

Definition eqb_mem (mem1 mem2 : Memory.t) : bool :=
  Memory.equal mem1 mem2.

Definition state_checker (s1 s2: MachineState.t) : Checker :=
  checker (
      (N.eqb (MachineState.getPC s1) (MachineState.getPC s2))
        && (eqb_regs (MachineState.getRegs s1) (MachineState.getRegs s2))
        && (eqb_mem (MachineState.getMemory s1) (MachineState.getMemory s2))
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
              | Some (t1,st1) =>
                conjoin [ (trace_checker t1 t); (state_checker st' st1) ]
              | None =>
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
                                   
  
