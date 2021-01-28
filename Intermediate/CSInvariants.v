Require Import CompCert.Events.
Require Import CompCert.Smallstep.
Require Import CompCert.Behaviors.
Require Import Common.Definitions.
Require Import Common.Util.
Require Import Common.Linking.
Require Import Common.Memory.
Require Import Common.Reachability.
Require Import Common.Renaming.
Require Import Common.Traces.
Require Import Common.TracesInform.
Require Import Common.CompCertExtensions.
Require Import Intermediate.Machine.
Require Import Intermediate.GlobalEnv.
Require Import Intermediate.CS.
Require Import Lib.Extra.
Require Import Lib.Monads.

From mathcomp Require Import ssreflect eqtype ssrfun.
From mathcomp Require ssrbool.
From extructures Require Import fmap fset.

Set Bullet Behavior "Strict Subproofs".

Module CSInvariants.

Import Intermediate.

  
Definition is_prefix (s: CS.state) (p: program) t : Prop :=
  Star (CS.sem_non_inform p) (CS.initial_machine_state p) t s.

Inductive wf_ptr_wrt_cid_t (cid: Component.id) (t: trace event) : Pointer.t -> Prop
  :=
  | wf_ptr_own:
      forall p b o,
        wf_ptr_wrt_cid_t cid t (p, cid, b, o)
  | wf_ptr_shared:
      forall p c_other b o,
      addr_shared_so_far (c_other, b) t -> wf_ptr_wrt_cid_t cid t (p, c_other, b, o)
.

Inductive wf_load_wrt_t_pc
          (mem: Memory.t)
          (load_at: Pointer.t)
          (t: trace event)
          (pc: Pointer.t) : Pointer.t -> Prop :=
| wrt_load_ptr_wf_load:
    forall ptr,
      wf_ptr_wrt_cid_t (Pointer.component load_at) t ptr ->
      wf_load_wrt_t_pc mem load_at t pc ptr
| wrt_pc_wf_load:
    forall ptr,
      addr_shared_so_far (Pointer.component load_at, Pointer.block load_at) t ->
      wf_ptr_wrt_cid_t (Pointer.component pc) t ptr ->
      wf_load_wrt_t_pc mem load_at t pc ptr.
        
Definition wf_mem_wrt_t_pc (mem: Memory.t) (t: trace event) (pc: Pointer.t) : Prop :=
  forall load_at ptr,
    Memory.load mem load_at = Some (Ptr ptr) ->
    wf_load_wrt_t_pc mem load_at t pc ptr.

Definition wf_reg_wrt_t_pc (reg: Register.t) (t: trace event) (pc: Pointer.t) : Prop :=
  forall r ptr,
    Register.get r reg = Ptr ptr ->
    wf_ptr_wrt_cid_t (Pointer.component pc) t ptr.

Definition wf_state_t (s: CS.state) (t: trace event) : Prop :=
  wf_mem_wrt_t_pc (CS.state_mem s) t (CS.state_pc s) /\
  wf_reg_wrt_t_pc (CS.state_regs s) t (CS.state_pc s).

Lemma is_prefix_wf_state_t s p t:
  well_formed_program p ->
  is_prefix s p t ->
  wf_state_t s t.
Admitted.
  
End CSInvariants.
