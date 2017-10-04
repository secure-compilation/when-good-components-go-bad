Require Import TargetSFI.CS.

Import CS.


  (* Definition eval_step_complete : Prop := *)
  (*   forall (G : Env.t)  (st : MachineState.t) (t : trace) (st' : MachineState.t), *)
  (*     (step G st t st') -> (eval_step G st = Some (t, st')). *)

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
                                   
  
