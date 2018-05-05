Require Import Coq.NArith.BinNat.

Require Import Common.Either.
Require Import TargetSFI.ExecutionError.

Require Import Tests.RSC_DC_MD_Test.
Require Import SFIPBTests.

Require Import TargetSFI.Machine.

Require Import I2SFI.Compiler.
Require Import SFIPBTests.

Definition update_log
           (G : Env.t)
           (st : MachineState.t) (t : CompCert.Events.trace)
           (st' : MachineState.t) (log : log_type CompCert.Events.event) :=
  let '(mem,pc,regs) := st in
  let '(test_log,addr_log) := log in
  let nlog :=
      if (Nat.eqb (List.count_occ N.eq_dec addr_log pc) 0%nat)
      then (addr_log ++ pc::nil)%list
      else addr_log
  in
  match t with
  | nil =>  (test_log,nlog)
  | _ => ((test_log ++ t)%list,nlog)
  end.

Definition sfi_eval 
           (p : sfi_program)
           (fuel : nat)
  :  (@Either (CompCert.Events.trace*MachineState.t*nat)%type ExecutionError)
     * Log
  := let (e,l) := (eval_program update_log p fuel) in
     let (test_log,_) := l in
     (e,test_log).

Definition sfi_rsc_correct (fuel : nat) :=
  let max_components := ((N.to_nat SFI.COMP_MAX) - 1)%nat in
  rsc_correct
    (genIConstCodeAddress CStore max_components) (* valid  jumps*)
    (genStoreAddresConstInstr CJump max_components) (* valid pointers *)
    3%nat
    max_components
    compile_program
    sfi_eval
    fuel.