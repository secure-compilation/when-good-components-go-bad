(**************************************************
 * Author: Ana Nora Evans (ananevans@virginia.edu)
 **************************************************)
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import CompCert.Events.

Require Import Common.Definitions.
Require Import Common.Maps.
Require Import Common.Either.

Require Import Intermediate.Machine.
Require Import Intermediate.CS.

Require Import IntermediateProgramGeneration.
Require Import Shrinkers.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.


(************************************************
 * Checkers
 ************************************************)
Definition log_checker
           {Log:Type}
           {ExecutionResult:Type} :=
  Log -> ExecutionResult -> Checker.

(*****************************************************
 * Checkers when target execution returned error
 ******************************************************)
Definition log_checker_error
           {Log:Type}
           {ExecutionError:Type}:=
  Log -> ExecutionError -> Checker.

Definition compile {TargetProgramType:Type} {CompilerErrorType:Type} :=
  Intermediate.program -> @Either TargetProgramType CompilerErrorType.

Definition eval
           {TargetProgramType:Type}
           {ExecutionResult:Type} {ExecutionError:Type}
           {Log:Type}
  :=
  TargetProgramType ->
  nat ->
  (@Either ExecutionResult ExecutionError) * Log.
  
Definition check_correct
           {CompilerErrorType:Type}
           {TargetProgramType:Type}
           {ExecutionResult:Type} {ExecutionError:Type}
           {Log:Type}
           `{Show CompilerErrorType}
           `{Show ExecutionResult}
           `{Show ExecutionError}
           
           (t : instr_gen)
           (wf : instr_weight)
           (cag : code_address_const_instr)
           (dag : data_address_const_instr)
           (max_components : nat)
           (generate_max_components : bool)
           (log_checker_error_fun : @log_checker_error Log
                                                       ExecutionError)
           (log_checker_fun : @log_checker Log
                                           ExecutionResult)
           (cf : @compile TargetProgramType CompilerErrorType)
           (ef : @eval TargetProgramType ExecutionResult ExecutionError
                  Log
           )
           (fuel : nat)
  : Checker :=
  forAllShrink
    (genIntermediateProgram
       t wf cag dag max_components false
    ) shrink
    ( fun ip =>
        match cf ip with
        | Common.Either.Left msg err =>
          whenFail ("Compilation error: " ++ msg ++ newline ++ (show err) ) false
        | Common.Either.Right p =>
          let '(res,log) := ef p fuel in
          match res with
          | Common.Either.Left msg err =>
            (whenFail ("Execution error of failed program: "
                         ++ (show err)))%string
            (log_checker_error_fun log err)
          | Common.Either.Right exec_res =>
            (* (whenFail ("memory of failed program: " ++ (show_mem (MachineState.getMemory st)))%string *)
            (whenFail ("Execution Result of failed program: "
                         ++ (show exec_res)))%string
            (log_checker_fun log exec_res)
          end
        end).


