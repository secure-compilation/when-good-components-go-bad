Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Language.

Import Source.

Record global_env : Type := mkGlobalEnv {
  genv_interface : Program.interface;
  genv_procedures : NMap.t (NMap.t expr);
  genv_buffers : NMap.t Block.id
}.

Definition init_genv (p: program) : global_env :=
  let '(bufs, _) := init_all p in
  {| genv_interface := prog_interface p;
     genv_procedures := prog_procedures p;
     genv_buffers := bufs |}.