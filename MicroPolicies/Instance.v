

Require Import Symbolic Exec.
Require Import Int32.

(* TL TODO: look at how to instanciate a module parameter!! *)

Definition mt := concrete_int_32_mt.

Definition sp : Symbolic.params.
Admitted.

Definition table : @Symbolic.syscall_table mt sp.
Admitted.

Definition step : Symbolic.state mt -> Symbolic.state mt -> Prop :=
  Symbolic.step table.

Definition stepf : Symbolic.state mt -> option (Symbolic.state mt) :=
  Exec.stepf table.
