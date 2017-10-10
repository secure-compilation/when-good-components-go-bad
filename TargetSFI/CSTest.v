Require Import TargetSFI.CS.
Require Import TargetSFI.Machine.
Require Import TargetSFI.MachineGen.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Logic.Decidable.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.
Import GenLow GenHigh.
(* Suppress some annoying warnings: *)
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import CompCert.Events.

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
    + right. unfold not. intro H1.
      (* TODO Learn how to write a tactic pattern here to match all the cases
      inversion H1; try (unfold executing in H5; subst; rewrite H in H5; auto).
      * *)
      Admitted.

Definition trace_checker (t1 t2 : trace) : Checker := checker true. (* TODO *)

Definition state_checker (s1 s2: MachineState.t) : Checker := checker true. (* TODO *)

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

(* QuickChick eval_step_complete. *)
                                   
  
