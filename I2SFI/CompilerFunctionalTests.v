(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.NArith.BinNat.
Require Import Coq.Lists.List.

Require Import CompCert.Events.

Require Import I2SFI.Compiler.
Require Import I2SFI.CompMonad.
Require Import TargetSFI.Machine.
Require Import TargetSFI.CS.
Require Import Intermediate.Machine.
Require Import Common.Definitions.
Require Import Common.Maps.

Import MonadNotations.
Open Scope monad_scope.


(* Compute ( *)
(*     let COMP1_ID : positive := 1%positive in *)
(*     let PROC1_ID : positive := 1%positive in *)
(*     let BLOCK1_ID : positive := 1%positive in *)
(*     let component1_interface : Component.interface := *)
(*         (Component.mkCompInterface [PROC1_ID] []) in *)
(*     let program_interface : Program.interface := *)
(*         PMap.add COMP1_ID component1_interface (PMap.empty Component.interface) in *)
(*      let buffers := PMap.add COMP1_ID [(BLOCK1_ID,10%nat)] (PMap.empty (list (Block.id * nat))) in *)
(*      let proc1_code := (PMap.add PROC1_ID [] (PMap.empty Intermediate.Machine.code) ) in *)
(*      let procs := PMap.add COMP1_ID proc1_code *)
(*                            (PMap.empty (PMap.t Intermediate.Machine.code)) in *)
(*      let program : Intermediate.program := {| *)
(*            Intermediate.prog_interface := program_interface; *)
(*            Intermediate.prog_procedures := procs; *)
(*            Intermediate.prog_buffers := buffers; *)
(*            Intermediate.prog_main := (COMP1_ID,PROC1_ID) *)
(*          |} in *)
    
(*     let cn := gen_cn program_interface in *)
(*     let cid2SFIid := List.fold_left *)
(*        (fun acc '(cid,i)  => *)
(*           PMap.add cid (Env.index2SFIid i) acc) *)
(*        (List.combine cn (List.seq 0 (List.length cn))) *)
(*        (PMap.empty SFIComponent.id) in *)
(*     let procs_labels := exported_procs_labels procs program_interface in *)
(*     (PMap.elements cid2SFIid) *)
(*   ). *)

Definition test (instrs : Intermediate.Machine.code) 
  : Either (trace*MachineState.t) :=
  (* : Either sfi_program := *)
  (* : Either RiscMachine.Memory.t := *)
  let COMP1_ID : positive := 1%positive in
  let PROC1_ID : positive := 1%positive in
  let BLOCK1_ID : positive := 1%positive in
  let component1_interface : Component.interface :=
      (Component.mkCompInterface [PROC1_ID] []) in
  let program_interface : Program.interface :=
      PMap.add COMP1_ID component1_interface (PMap.empty Component.interface) in
  let buffers := PMap.add COMP1_ID [(BLOCK1_ID,10%nat)] (PMap.empty (list (Block.id * nat))) in
  let proc1_code := (PMap.add PROC1_ID (instrs++[Intermediate.Machine.IReturn])
                              (PMap.empty Intermediate.Machine.code) ) in
  let procs := PMap.add COMP1_ID proc1_code
                        (PMap.empty (PMap.t Intermediate.Machine.code)) in
  let program : Intermediate.program := {|
        Intermediate.prog_interface := program_interface;
        Intermediate.prog_procedures := procs;
        Intermediate.prog_buffers := buffers;
        Intermediate.prog_main := (COMP1_ID,PROC1_ID)
      |} in
  match compile_program program with
  | Left msg => Left (trace * MachineState.t)  msg
  | Right p =>
    match CS.eval_program (100%nat) p RiscMachine.RegisterFile.reset_all with
    | None => Left (trace * MachineState.t) "Execution failed"
    | Some res => Right (trace * MachineState.t) res
    end
  end.

(* Compute (test [Intermediate.Machine.INop]). *)

(* Compute (test [Intermediate.Machine.IConst (IInt 5%Z) R_AUX1 ]). *)

(* Compute (test [Intermediate.Machine.IConst (IInt 5%Z) R_AUX1 *)
(*                ;Intermediate.Machine.IMov R_AUX1 R_AUX2]). *)

(* Compute (test [Intermediate.Machine.IConst (IPtr (1%positive,1%positive,0%Z) ) R_AUX1 *)
(*                ; Intermediate.Machine.IConst (IInt 5%Z) R_AUX2 *)
(*                ; Intermediate.Machine.IStore R_AUX1 R_AUX2]). *)

(* Compute (test [Intermediate.Machine.IConst (IPtr (1%positive,1%positive,0%Z) ) R_AUX1 *)
(*                ; Intermediate.Machine.IConst (IInt 5%Z) R_AUX2 *)
(*                ; Intermediate.Machine.IStore R_AUX1 R_AUX2 *)
(*                ; Intermediate.Machine.IMov R_AUX1 R_AUX2 *)
(*                ; Intermediate.Machine.ILoad R_AUX2 R_AUX1 *)
(*         ]). *)

(* Compute (test [Intermediate.Machine.ILabel 7%positive *)
(*                ;Intermediate.Machine.IConst (IPtr (1%positive,1%positive,0%Z) ) R_AUX1 *)
(*                ; Intermediate.Machine.IConst (IInt 5%Z) R_AUX2 *)
(*                ; Intermediate.Machine.IStore R_AUX1 R_AUX2 *)
(*                ; Intermediate.Machine.IMov R_AUX1 R_AUX2 *)
(*                ; Intermediate.Machine.ILoad R_AUX2 R_AUX1 *)
(*                ; Intermediate.Machine.IConst (IInt 0%Z) R_AUX1 *)
(*                ;Intermediate.Machine.IBnz R_AUX1 7%positive]). *)


                                    