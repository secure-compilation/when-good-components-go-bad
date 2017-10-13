Require Import TargetSFI.CS.
Require Import TargetSFI.Machine.
Require Import TargetSFI.MachineGen.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Logic.Decidable.

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
    
Instance step_dec(g : Env.t) (st : MachineState.t) (t : trace)
         (st' : MachineState.t): Dec (step g st t st'). 
Proof.
  apply Build_Dec. unfold ssrbool.decidable.
  destruct st as [[mem pc] gen_regs].
  destruct st' as [[mem' pc'] gen_regs'].
  destruct (Memory.get_word mem pc) eqn:H.
  - destruct w.
    + right. unfold not. intro H1. inversion H1.
      * unfold executing in H5. subst. rewrite H in H5. auto.
      * unfold executing in H5. subst. rewrite H in H5. auto.
      * unfold executing in H6. subst. rewrite H in H6. auto.
      * unfold executing in H7. subst. rewrite H in H7. auto.
      * unfold executing in H7. subst. rewrite H in H7. auto.
      * unfold executing in H7. subst. rewrite H in H7. auto.
      * unfold executing in H6. subst. rewrite H in H6. auto.
      * unfold executing in H6. subst. rewrite H in H6. auto.
      * unfold executing in H7. subst. rewrite H in H7. auto.
      * unfold executing in H6. subst. rewrite H in H6. auto.
      * unfold executing in H5. subst. rewrite H in H5. auto.
      * unfold executing in H7. subst. rewrite H in H7. auto.
    + destruct t0.
      * destruct (N.eqb pc' (inc_pc pc)) eqn:Hpc. rewrite N.eqb_eq in Hpc.
        rewrite Hpc. destruct (gen_regs = gen_regs') eqn:Hregs.
        left. apply Nop.
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
                                   
  
