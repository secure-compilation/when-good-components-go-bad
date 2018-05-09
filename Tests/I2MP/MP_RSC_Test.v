From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrint seq.
From CoqUtils Require Import fmap word.

Require Import Coq.Strings.String.
Require Import Common.Either.
Require Import Intermediate.Machine.

Require Import MicroPolicies.Types.
Require Import MicroPolicies.Instance.
Require Import I2MP.Encode.
Require Import I2MP.Linearize.

Require Import Tests.RSC_DC_MD_Test.
Require Import Tests.IntermediateProgramGeneration.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Import QcNotation. Open Scope qc_scope.

(* TL Questions: *)
(* Do I really need compiler errors? *)

(* ASW: what about unrespected interfaces? *)

(* I do need traces, right? *)
(* YEP!! *)

(* What about execution errors? What's the needed level of details? *)
(* Doesn't NEED to be meaningful *)

(* REMINDER: if a compiled program has +16384 instructions, the alloc syscall
   won't work on the micro-policiy machine, due to address space layout and
   imm word size. *)

Definition mp_program := { fmap mword mt -> matom }.

Definition ExecutionResult := unit.
Definition ExecutionError := unit.

Fixpoint mp_exec (s : state) (fuel : nat)
  : (@Either ExecutionResult ExecutionError) * Log :=
  let list_of_option {A : Type} (o : option A) : list A := match o with
                         | None => nil
                         | Some x => cons x nil
                         end in
  match fuel with
  | O => (Common.Either.Right tt, nil)
  | S n => match stepf s with
           | Some (s', e) => let (r, l) := mp_exec s' n in
                             (r, (list_of_option e ++ l))%list
           | None => (Common.Either.Left "The machine either halted or failed" tt, nil)
           end
  end.


Definition mp_eval (p : mp_program) (fuel : nat)
  : (@Either ExecutionResult ExecutionError) * Log := mp_exec (load p) fuel.

Definition compile_program
           (ip : Intermediate.program)
  : @Either mp_program False := Common.Either.Right (encode (linearize ip)).

Instance show_false : Show False :=
  {| show := (fun f => match (f: False) with end) |}.

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
