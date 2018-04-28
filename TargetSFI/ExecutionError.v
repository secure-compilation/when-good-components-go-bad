Require Import TargetSFI.Machine.

Inductive ExecutionError :=
| RegisterNotFound : MachineState.t -> RiscMachine.Register.t -> ExecutionError
| NoInfo : ExecutionError
| UninitializedMemory : MachineState.t -> RiscMachine.address -> ExecutionError
| CodeMemoryException : MachineState.t -> RiscMachine.address
                        -> RiscMachine.ISA.instr  -> ExecutionError
| DataMemoryException : MachineState.t -> RiscMachine.address
                        -> RiscMachine.value  -> ExecutionError
| MissingComponentId : MachineState.t -> SFIComponent.id -> Env.CN -> ExecutionError
| CallEventError : MachineState.t -> SFIComponent.id -> SFIComponent.id
                   -> Env.CN -> Env.E -> ExecutionError
| RetEventError : MachineState.t -> SFIComponent.id -> SFIComponent.id
                  -> Env.CN -> ExecutionError
| IllegalJalToZeroComponent : MachineState.t -> ExecutionError
| IllegalJumpFromZeroComponent : MachineState.t -> ExecutionError
.

Definition get_state (err : ExecutionError) : MachineState.t :=
  match err with
  | RegisterNotFound st _ => st 
  | NoInfo => MachineState.empty
  | UninitializedMemory st _ => st
  | CodeMemoryException st _ _ => st
  | DataMemoryException st _ _ => st
  | MissingComponentId st _ _ => st
  | CallEventError st _ _ _ _ => st
  | RetEventError st _ _ _ => st
  | IllegalJalToZeroComponent st => st
  | IllegalJumpFromZeroComponent st => st
  end.