Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Linking.
Require Import Source.Language.

Import Source.

Record global_env : Type := mkGlobalEnv {
  genv_interface : Program.interface;
  genv_procedures : NMap (NMap expr);
  genv_buffers : NMap Block.id
}.

Definition prepare_global_env (p: program) : global_env :=
  {| genv_interface := prog_interface p;
     genv_procedures := prog_procedures p;
     genv_buffers := snd (prepare_buffers p) |}.