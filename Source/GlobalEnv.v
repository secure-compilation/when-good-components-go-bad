Require Import Common.Definitions.
Require Import Common.Values.
Require Import Common.Linking.
Require Import Source.Language.

Import Source.

Record global_env : Type := mkGlobalEnv {
  genv_interface : Program.interface;
  genv_procedures : ZMap.t (ZMap.t expr);
  genv_buffers : ZMap.t Block.id
}.

Record well_formed_global_env (G: global_env) := {
  wfgenv_interface_soundness:
    sound_interface (genv_interface G);
  wfgenv_procedures_soundness:
    forall C, ZMap.In C (genv_procedures G) -> ZMap.In C (genv_interface G);
  wfgenv_buffers_soundness:
    forall C, ZMap.In C (genv_buffers G) -> ZMap.In C (genv_interface G)
}.

(* G contains G', moreover they share the same interface *)
Definition genv_extension (G G': global_env) : Prop :=
  ZMap.Equal (genv_interface G) (genv_interface G') /\
  forall C, (forall Cprocs,
           ZMap.MapsTo C Cprocs (genv_procedures G') ->
           ZMap.MapsTo C Cprocs (genv_procedures G)) /\
       (forall Cbufs,
           ZMap.MapsTo C Cbufs (genv_buffers G') ->
           ZMap.MapsTo C Cbufs (genv_buffers G)).

Definition init_genv (p: program) : global_env :=
  let '(bufs, _) := init_all p in
  {| genv_interface := prog_interface p;
     genv_procedures := prog_procedures p;
     genv_buffers := bufs |}.