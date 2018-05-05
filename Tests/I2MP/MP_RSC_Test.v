Require Import Coq.Strings.String.
Require Import Common.Either.
Require Import Intermediate.Machine.

Require Import Tests.RSC_DC_MD_Test.
Require Import Tests.IntermediateProgramGeneration.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.

(* TODO *)
(* type of the MP programs *)
Definition mp_program := unit.
Definition ExecutionResult := unit.
Definition ExecutionError := unit.

Definition mp_eval 
           (p : mp_program)
           (fuel : nat)
  :  (@Either ExecutionResult ExecutionError)
     * Log
  := ((Common.Either.Left "" tt),nil).

Definition CompilerError := string.
Definition compile_program
           `{Show CompilerError}
           (ip : Intermediate.program)
  : @Either mp_program CompilerError
  := Common.Either.Left "" "".

Definition mp_rsc_correct (fuel : nat) :=
  let max_components := 15%nat in
  let min_components := 8%nat in
  rsc_correct
    empty_cag
    empty_dag
    min_components
    max_components
    compile_program
    mp_eval
    fuel.