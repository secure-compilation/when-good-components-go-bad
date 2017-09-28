Require Import ZArith.

Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Maps.

Require Import TargetSFI.Machine.

Require Import Env.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.

Require Export ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.

Require Import Coq.Strings.String.
Local Open Scope string.

Require Import CompCert.Events.

Definition show_pos (p : positive) := show_nat (Pos.to_nat p).

Definition show_N ( n : N ) := show_nat (N.to_nat n).

Instance show_Component_id : Show Component.id :=
  {|
    show := show_pos
  |}.

Instance show_CN : Show Env.CN := showList.

Instance show_addr : Show  RiscMachine.address :=
  {|
    show := show_N
  |}.

Instance show_Addr_Proc : Show (RiscMachine.address * Procedure.id) := showPair.

Instance show_E : Show Env.E := showList.

Instance show_env : Show Env.t :=
  {
    show := fun (G : Env.t) =>
              let (cn,e) := G in 
              (show cn) ++ (show e)
  }.

Instance show_event : Show event :=
  {|
    show := fun (e : event) =>
              match e with
              | ECall c1 pid arg c2 => "[ECall " ++ (show c1) ++ " "
                                                 ++ (show pid) ++ " "
                                                 ++ (show_int arg) ++ " "
                                                 ++ (show c2) ++ "]"
              |  ERet c1 arg c2 => "[ERet " ++ (show c1) ++ " "
                                                 ++ (show_int arg) ++ " "
                                                 ++ (show c2) ++ "]"
              end
  |}.

Instance show_trace : Show trace := showList.

Print MachineState.t.

Instance show_state : Show MachineState.t :=
  {|
    show := fun (st : MachineState.t) =>
              let '(mem,pc,gen_regs) := st in
              "PC: " ++ (show pc) ++ " "
                     ++ "registers: " ++ (show gen_regs)
                     (* TODO print memory *)                     
  |}.

(* TODO Arbitrary *)