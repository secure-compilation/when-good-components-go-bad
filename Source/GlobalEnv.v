Require Import Common.Definitions.
Require Import Common.Values.
Require Import Source.Language.

Record global_env : Type := mkGlobalEnv {
  genv_interface : Program.interface;
  genv_procedures : NMap.t (NMap.t expr);
  genv_buffers : NMap.t Block.id
}.
