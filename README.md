# SecurePtrs #

This repository contains the Coq development of the paper: **SecurePtrs: Proving
Secure Compilation Using Data-Flow Back-Translation and Turn-Taking
Simulation**.

### Prerequisites ###

This development has been built with the following combinations of Coq releases
and versioned libraries:

Coq 8.12.2
- Mathematical Components 1.11.0
- Extensional Structures 0.2.2

Dependencies can be installed through the OCaml package manager, OPAM.

- Coq (package `coq`) is available through the official
  [Ocaml OPAM repository](http://opam.ocaml.org/).
- Stable releases of Mathematical Components (packages `coq-mathcomp-ssreflect`,
  `coq-mathcomp-fingroup` and `coq-mathcomp-algebra`) and Extensional Structures
  (package `coq-extructures`) are available through the
  [Coq OPAM repository](https://coq.inria.fr/opam/released/).

### Build ###

Run `make` at the root to build the development.

### Definitions and theorems ###

At the top level, the development provides high-level proofs with the following
entry points:
- `RSC_DC_MD.v`: generic secure compilation proof
  against the assumptions in `RSC_DC_MD_Sigs.v` (Section 3.5)
- `RSC_DC_MD_Instance.v`: an instantiation of the assumptions
  from `RSC_DC_MD_Sigs.v` to our compilation chain  (Section 4.3)
- `RSC_DC.v`: general proofs about the class of properties preserved
  by RSC^DC (Appendix A)
- `RSC_DC_4_compcert.v`: proofs in `RSC_DC.v` adapted to the general CompCert
  trace model (Appendix A)

The correspondences between the main definitions and results in the paper and
in Coq are as follows.

Definition 3.2: Robustly Safe Compilation with Dynamic Compromise (RSC^DC)
- `RSC_DC.RSC_dc` in the simple trace model
- `RSC_DC_4_compcert.RSC_dc` in the CompCert trace model

Theorem A.2: RSC^DC characterization via Z_P
- `RSC_DC.main_thm` in the simple trace model
- `RSC_DC_4_compcert.main_thm` in the CompCert trace model

### Assumptions ###

The proof currently relies on the following assumptions:

TODO: Remove statements after explaining the assumptions, regroup as needed.

#### Back-translation ####

Axioms:
well_formed_events_well_formed_program
  : forall (T : Type) (procs : NMap (NMap T)) (t : seq event_inform),
    all (well_formed_event intf procs) t ->
    Source.well_formed_program (program_of_trace t)
pointer_of_alloc
  : forall (mem : Memory.t) (cid : Component.id) (sz : nat) 
      (mem' : Memory.t) (ptr' : Pointer.t) (nb : Block.id),
    Memory.alloc mem cid sz = Some (mem', ptr') ->
    next_block mem cid = Some nb -> ptr' = (Permission.data, cid, nb, 0%Z)
CSInvariants.CSInvariants.not_executing_can_not_share
  : forall (s : CS.CS.state) (p : Machine.Intermediate.program)
      (t : seq event) (e : event) (C : Component.id) 
      (b : Block.id),
    Machine.Intermediate.well_formed_program p ->
    Machine.Intermediate.closed_program p ->
    CSInvariants.CSInvariants.is_prefix s p (rcons t e) ->
    C <> cur_comp_of_event e ->
    (forall b' : Block.id, ~ addr_shared_so_far (C, b') t) ->
    ~ addr_shared_so_far (C, b) (rcons t e)
next_block_prepare_buffers
  : forall C : nat_ordType,
    component_buffer C ->
    next_block (Source.prepare_buffers p) C = Some LOCALBUF_blockid
next_block_initial_memory
  : forall C : nat_ordType,
    component_buffer C -> next_block initial_memory C = Some 1
next_block_alloc_neq
  : forall (m : Memory.t) (C : Component.id) (n : nat) 
      (m' : Memory.t) (b : Pointer.t) (C' : Component.id),
    Memory.alloc m C n = Some (m', b) ->
    C' <> C -> next_block m' C' = next_block m C'
next_block_alloc
  : forall (m : Memory.t) (C : Component.id) (n : nat) 
      (m' : Memory.t) (b : Pointer.t),
    Memory.alloc m C n = Some (m', b) ->
    next_block m C = Some (Pointer.block b) /\
    next_block m' C = Some (ssrnat.addn (Pointer.block b) 1)
load_prepare_buffers
  : forall (C : nat_ordType) (o : nat),
    component_buffer C ->
    Memory.load (Source.prepare_buffers p)
      (Permission.data, C, Block.local, Z.of_nat o) = 
    nth_error meta_buffer o
load_next_block_None
  : forall (mem : Memory.t) (ptr : Pointer.t) (b : Block.id),
    next_block mem (Pointer.component ptr) = Some b ->
    Pointer.block ptr >= b -> Memory.load mem ptr = None
ComponentMemory.load_next_block
CS.load_data_next_block
  : forall p : Source.program,
    Source.well_formed_program p ->
    Source.closed_program p ->
    forall (s : CS.state) (t : trace event) (s' : state (CS.sem p))
      (ptr : Pointer.t) (C : Component.id) (b : Block.id) 
      (o : Block.offset),
    CS.initial_state p s ->
    Star (CS.sem p) s t s' ->
    Memory.load (CS.s_memory s') ptr = Some (Ptr (Permission.data, C, b, o)) ->
    exists Cmem : ComponentMemory.t,
      CS.s_memory s' C = Some Cmem /\ b < ComponentMemory.next_block Cmem
CS.load_component_prog_interface_addr
  : forall p : Source.program,
    Source.well_formed_program p ->
    Source.closed_program p ->
    forall (s : CS.state) (t : trace event) (s' : state (CS.sem p))
      (ptr : Pointer.t) (v : value),
    CS.initial_state p s ->
    Star (CS.sem p) s t s' ->
    Memory.load (CS.s_memory s') ptr = Some v ->
    Pointer.component ptr \in domm (Source.prog_interface p)
CS.load_component_prog_interface
  : forall p : Source.program,
    Source.well_formed_program p ->
    Source.closed_program p ->
    forall (s : CS.state) (t : trace event) (s' : state (CS.sem p))
      (ptr ptr' : Pointer.t),
    CS.initial_state p s ->
    Star (CS.sem p) s t s' ->
    Memory.load (CS.s_memory s') ptr = Some (Ptr ptr') ->
    Pointer.component ptr' \in domm (Source.prog_interface p)
CSInvariants.CSInvariants.load_Some_component_buffer
  : forall (p : Machine.Intermediate.program) (s : CS.CS.state)
      (t : seq event) (e : event) (ptr : Pointer.t) 
      (v : value),
    Machine.Intermediate.well_formed_program p ->
    Machine.Intermediate.closed_program p ->
    CSInvariants.CSInvariants.is_prefix s p (rcons t e) ->
    Memory.load (mem_of_event e) ptr = Some v ->
    Pointer.component ptr \in domm (Machine.Intermediate.prog_interface p)
initialization_correct_component_memory
  : forall (C : Component.id) (mem mem' : Memory.t),
    (forall (C' : Component.id) (b : Block.id) (offset : Block.offset),
     C <> C' ->
     Memory.load mem (Permission.data, C', b, offset) =
     Memory.load mem' (Permission.data, C', b, offset)) ->
    (forall C' : Component.id,
     C <> C' -> next_block mem C' = next_block mem' C') ->
    forall C' : Component.id, C <> C' -> mem C' = mem' C'
initialization_correct
  : forall (C : nat_ordType) (stk : CS.stack) (mem : Memory.t) 
      (k : cont) (arg : value) (prefix : trace event_inform)
      (e : event_inform),
    component_buffer C ->
    postcondition_steady_state e mem C \/
    postcondition_uninitialized prefix e mem C ->
    exists (mem' : Memory.t) (i : Z),
      star CS.kstep (prepare_global_env p)
        [CState C, stk, mem, k, init_check C, arg] E0
        [CState C, stk, mem', k, E_val (Int i), arg] /\
      postcondition_steady_state e mem' C /\
      (forall offset : Z,
       offset <> INITFLAG_offset ->
       offset <> LOCALBUF_offset ->
       Memory.load mem (Permission.data, C, Block.local, offset) =
       Memory.load mem' (Permission.data, C, Block.local, offset)) /\
      (forall (C' : nat_ordType) (b : Block.id) (offset : Block.offset),
       C <> C' ->
       Memory.load mem (Permission.data, C', b, offset) =
       Memory.load mem' (Permission.data, C', b, offset)) /\
      (forall C' : nat_ordType,
       C <> C' -> next_block mem C' = next_block mem' C') /\
      (forall (C' : nat_ordType) (b : Block.id) (offset : Block.offset),
       C = C' ->
       b <> Block.local ->
       postcondition_steady_state e mem C ->
       Memory.load mem (Permission.data, C', b, offset) =
       Memory.load mem' (Permission.data, C', b, offset))
CS.eval_kstep_sound
  : forall (G : global_env) (st : CS.state) (t : trace event)
      (st' : CS.state),
    CS.eval_kstep G st = Some (t, st') -> CS.kstep G st t st'
definability_does_not_leak
  : CS.private_pointers_never_leak_S p (uniform_shift 1)
component_memory_after_store_neq
  : forall (mem : Memory.t) (ptr : Pointer.t) (v : value) 
      (mem' : Memory.t) (C : Component.id),
    Memory.store mem ptr v = Some mem' ->
    Pointer.component ptr <> C -> mem C = mem' C
component_memory_after_alloc_neq
  : forall (mem : Memory.t) (C : Component.id) (sz : nat) 
      (mem' : Memory.t) (ptr : Pointer.t) (C' : Component.id),
    Memory.alloc mem C sz = Some (mem', ptr) -> C' <> C -> mem C' = mem' C'
CS.comes_from_initial_state_mem_domm
  : forall p : Source.program,
    Source.well_formed_program p ->
    Source.closed_program p ->
    forall (s : CS.state) (t : trace event) (s' : state (CS.sem p)),
    CS.initial_state p s ->
    Star (CS.sem p) s t s' ->
    domm (CS.s_memory s') = domm (Source.prog_interface p)
Memory.alloc_after_load
  : forall (mem : Memory.t) (P : Permission.id) (C : Component.id)
      (b : Block.id) (o : Block.offset) (v : value) 
      (size : nat),
    Memory.load mem (P, C, b, o) = Some v ->
    exists (mem' : Memory.t) (b' : Block.id),
      b' <> b /\
      Memory.alloc mem C size = Some (mem', (Permission.data, C, b', 0%Z))
addr_shared_so_far_inv_2
  : forall (ret_val : value) (mem' : Memory.tt)
      (regs : Machine.Intermediate.Register.t) (C C' : Component.id)
      (s : stack_state) (prefix0 : seq event_inform)
      (eprev ecur : event_inform) (ecur_noninf : event),
    project_non_inform [:: ecur] = [:: ecur_noninf] ->
    well_formed_intermediate_prefix ((prefix0 ++ [:: eprev]) ++ [:: ecur]) ->
    forall
      mem0 mem mem1 mem1' mem2 mem3 mem4 mem5 mem6 mem7 mem8 mem9 : Memory.tt,
    C = cur_comp s ->
    forall vcom : value,
    Memory.load mem0 (Permission.data, cur_comp s, Block.local, 5%Z) =
    Some vcom ->
    Memory.store mem (Permission.data, C, Block.local, EXTCALL_offset)
      (Int 1) = Some mem1 ->
    Memory.store mem1 (Permission.data, C', Block.local, 5%Z) vcom =
    Some mem1' ->
    Memory.store mem1' (Permission.data, C', Block.local, 4%Z) Undef =
    Some mem2 ->
    Memory.store mem2 (Permission.data, C', Block.local, 6%Z) Undef =
    Some mem3 ->
    Memory.store mem3 (Permission.data, C', Block.local, 7%Z) Undef =
    Some mem4 ->
    Memory.store mem4 (Permission.data, C', Block.local, 8%Z) Undef =
    Some mem5 ->
    Memory.store mem5 (Permission.data, C', Block.local, 9%Z) Undef =
    Some mem6 ->
    Memory.store mem6 (Permission.data, C', Block.local, 10%Z) Undef =
    Some mem7 ->
    Memory.store mem7 (Permission.data, C', Block.local, EXTCALL_offset)
      (Int 0) = Some mem8 ->
    forall (Cb : Component.id) (b : Block.id) (addr' : addr_t),
    addr_shared_so_far (Cb, b)
      (rcons (project_non_inform (prefix0 ++ [:: eprev])) ecur_noninf) ->
    postcondition_event_registers
      (ERetInform (cur_comp s) ret_val mem' regs C') mem9 ->
    (forall C0 : nat_ordType,
     component_buffer C0 ->
     C0 = next_comp_of_event (ERetInform (cur_comp s) ret_val mem' regs C') ->
     postcondition_steady_state
       (ERetInform (cur_comp s) ret_val mem' regs C') mem9 C0) ->
    (forall C0 : nat_ordType,
     component_buffer C0 ->
     C0 <> next_comp_of_event (ERetInform (cur_comp s) ret_val mem' regs C') ->
     postcondition_steady_state
       (ERetInform (cur_comp s) ret_val mem' regs C') mem9 C0 \/
     postcondition_uninitialized (prefix0 ++ [:: eprev]) ecur mem9 C0) ->
    Reachability.Reachable (mem_of_event (ERet C vcom mem1 C')) 
      (fset1 addr') (Cb, S b)
addr_shared_so_far_inv_1
  : forall (ret_val : value) (mem' : Memory.tt),
    Machine.Intermediate.Register.t ->
    forall C C' : Component.id,
    C <> C' ->
    forall (prefix0 : seq event_inform) (eprev ecur : event_inform)
      (ecur_noninf : event),
    project_non_inform [:: ecur] = [:: ecur_noninf] ->
    well_formed_intermediate_prefix ((prefix0 ++ [:: eprev]) ++ [:: ecur]) ->
    forall
      (mem0 mem mem1 mem1' mem2 mem3 mem4 mem5 mem6 mem7 mem8 : Memory.tt)
      (vcom : value),
    Memory.load mem0 (Permission.data, C, Block.local, 5%Z) = Some vcom ->
    Memory.store mem (Permission.data, C, Block.local, EXTCALL_offset)
      (Int 1) = Some mem1 ->
    Memory.store mem1 (Permission.data, C', Block.local, 5%Z) vcom =
    Some mem1' ->
    Memory.store mem1' (Permission.data, C', Block.local, 4%Z) Undef =
    Some mem2 ->
    Memory.store mem2 (Permission.data, C', Block.local, 6%Z) Undef =
    Some mem3 ->
    Memory.store mem3 (Permission.data, C', Block.local, 7%Z) Undef =
    Some mem4 ->
    Memory.store mem4 (Permission.data, C', Block.local, 8%Z) Undef =
    Some mem5 ->
    Memory.store mem5 (Permission.data, C', Block.local, 9%Z) Undef =
    Some mem6 ->
    Memory.store mem6 (Permission.data, C', Block.local, 10%Z) Undef =
    Some mem7 ->
    Memory.store mem7 (Permission.data, C', Block.local, EXTCALL_offset)
      (Int 0) = Some mem8 ->
    forall (Cb : Component.id) (b : Block.id),
    Reachability.Reachable mem' (addr_of_value ret_val) (Cb, b) ->
    postcondition_event_registers ecur mem8 ->
    addr_shared_so_far (Cb, b)
      (rcons (project_non_inform (prefix0 ++ [:: eprev])) ecur_noninf) ->
    (forall C0 : nat_ordType,
     component_buffer C0 ->
     C0 = next_comp_of_event ecur -> postcondition_steady_state ecur mem8 C0) ->
    (forall C0 : nat_ordType,
     component_buffer C0 ->
     C0 <> next_comp_of_event ecur ->
     postcondition_steady_state ecur mem8 C0 \/
     postcondition_uninitialized (prefix0 ++ [:: eprev]) ecur mem8 C0) ->
    C = cur_comp_of_event ecur_noninf ->
    C' = next_comp_of_event ecur ->
    mem' = mem_of_event_inform ecur ->
    ret_val = arg_of_event ecur_noninf ->
    Reachability.Reachable mem1 (addr_of_value vcom) (Cb, S b)
addr_shared_so_far_ERet_Hsharedsrc
  : forall (ret_val : value) (mem' : Memory.t)
      (regs : Machine.Intermediate.Register.t) (C' : Component.id)
      (prefix suffix : seq event_inform) (s : stack_state),
    well_formed_intermediate_prefix
      (prefix ++ [:: ERetInform (cur_comp s) ret_val mem' regs C']) ->
    forall (prefix' : trace event) (mem0 : Memory.tt) (mem mem1 : Memory.t),
    Memory.store mem
      (Permission.data, cur_comp s, Block.local, EXTCALL_offset) 
      (Int 1) = Some mem1 ->
    forall vcom : value,
    Memory.load mem0
      (Permission.data, cur_comp s, Block.local, reg_offset E_R_COM) =
    Some vcom ->
    forall mem1' : Memory.t,
    Memory.store mem1 (Permission.data, C', Block.local, reg_offset E_R_COM)
      vcom = Some mem1' ->
    forall mem2 : Memory.t,
    Memory.store mem1' (Permission.data, C', Block.local, reg_offset E_R_ONE)
      Undef = Some mem2 ->
    forall mem3 : Memory.t,
    Memory.store mem2 (Permission.data, C', Block.local, reg_offset E_R_AUX1)
      Undef = Some mem3 ->
    forall mem4 : Memory.t,
    Memory.store mem3 (Permission.data, C', Block.local, reg_offset E_R_AUX2)
      Undef = Some mem4 ->
    forall mem5 : Memory.t,
    Memory.store mem4 (Permission.data, C', Block.local, reg_offset E_R_RA)
      Undef = Some mem5 ->
    forall mem6 : Memory.t,
    Memory.store mem5 (Permission.data, C', Block.local, reg_offset E_R_SP)
      Undef = Some mem6 ->
    forall mem7 : Memory.t,
    Memory.store mem6 (Permission.data, C', Block.local, reg_offset E_R_ARG)
      Undef = Some mem7 ->
    forall mem8 : Memory.t,
    Memory.store mem7 (Permission.data, C', Block.local, EXTCALL_offset)
      (Int 0) = Some mem8 ->
    forall (s' : stack_state) (cs' : CS.state),
    well_formed_state_r s'
      (prefix ++ [:: ERetInform (cur_comp s) ret_val mem' regs C']) suffix
      cs' ->
    forall (Cb : Component.id) (b : Block.id),
    addr_shared_so_far (Cb, b)
      (rcons prefix' (ERet (cur_comp s) vcom mem1 C')) ->
    exists addr : addr_t,
      sigma_shifting_wrap_bid_in_addr
        (sigma_shifting_lefttoright_addr_bid all_zeros_shift
           (uniform_shift 1)) addr = Some (Cb, b) /\
      event_renames_event_at_shared_addr all_zeros_shift 
        (uniform_shift 1) addr (ERet (cur_comp s) ret_val mem' C')
        (ERet (cur_comp s) vcom mem1 C') /\
      addr_shared_so_far addr
        (rcons (project_non_inform prefix)
           (ERet (cur_comp s) ret_val mem' C'))
addr_shared_so_far_ECall_Hshared_src
  : forall (P' : Procedure.id) (new_arg : value) (mem' : Memory.t)
      (regs : Machine.Intermediate.Register.t) (C' : Component.id)
      (prefix suffix : seq event_inform) (s : stack_state),
    well_formed_intermediate_prefix
      (prefix ++ [:: ECallInform (cur_comp s) P' new_arg mem' regs C']) ->
    forall (prefix' : trace event) (stk : CS.stack) 
      (mem0 : Memory.tt) (arg : value) (P : Procedure.id) 
      (mem : Memory.t) (vcom : value),
    Memory.load mem0
      (Permission.data, cur_comp s, Block.local, reg_offset E_R_COM) =
    Some vcom ->
    forall mem1 : Memory.t,
    Memory.store mem
      (Permission.data, cur_comp s, Block.local, EXTCALL_offset) 
      (Int 1) = Some mem1 ->
    forall mem2 : Memory.t,
    (forall offset : Z,
     offset <> INITFLAG_offset ->
     offset <> LOCALBUF_offset ->
     Memory.load mem1 (Permission.data, C', Block.local, offset) =
     Memory.load mem2 (Permission.data, C', Block.local, offset)) ->
    forall mem3 : Memory.t,
    Memory.store mem2 (Permission.data, C', Block.local, reg_offset E_R_ONE)
      Undef = Some mem3 ->
    forall mem4 : Memory.t,
    Memory.store mem3 (Permission.data, C', Block.local, reg_offset E_R_AUX1)
      Undef = Some mem4 ->
    forall mem5 : Memory.t,
    Memory.store mem4 (Permission.data, C', Block.local, reg_offset E_R_AUX2)
      Undef = Some mem5 ->
    forall mem6 : Memory.t,
    Memory.store mem5 (Permission.data, C', Block.local, reg_offset E_R_RA)
      Undef = Some mem6 ->
    forall mem7 : Memory.t,
    Memory.store mem6 (Permission.data, C', Block.local, reg_offset E_R_SP)
      Undef = Some mem7 ->
    forall mem8 : Memory.t,
    Memory.store mem7 (Permission.data, C', Block.local, reg_offset E_R_ARG)
      Undef = Some mem8 ->
    forall mem9 : Memory.t,
    Memory.store mem8 (Permission.data, C', Block.local, reg_offset E_R_COM)
      vcom = Some mem9 ->
    forall mem10 : Memory.t,
    Memory.store mem9 (Permission.data, C', Block.local, 1%Z) (Int 0) =
    Some mem10 ->
    well_formed_state_r
      {| cur_comp := C'; callers := cur_comp s :: callers s |}
      (prefix ++ [:: ECallInform (cur_comp s) P' new_arg mem' regs C'])
      suffix
      [CState C', {|
                  CS.f_component := cur_comp s;
                  CS.f_arg := arg;
                  CS.f_cont := Kassign1 (loc_of_reg E_R_COM)
                                 (Kseq
                                    (invalidate_metadata;;
                                     E_assign EXTCALL (E_val (Int 0));;
                                     E_call (cur_comp s) P (E_val (Int 0)))
                                    Kstop) |} :: stk, mem10, Kstop, 
      expr_of_trace C' P' (comp_subtrace C' t), vcom] ->
    forall (Cb : Component.id) (b : Block.id),
    addr_shared_so_far (Cb, b)
      (rcons prefix' (ECall (cur_comp s) P' vcom mem1 C')) ->
    exists addr : addr_t,
      sigma_shifting_wrap_bid_in_addr
        (sigma_shifting_lefttoright_addr_bid all_zeros_shift
           (uniform_shift 1)) addr = Some (Cb, b) /\
      event_renames_event_at_shared_addr all_zeros_shift 
        (uniform_shift 1) addr (ECall (cur_comp s) P' new_arg mem' C')
        (ECall (cur_comp s) P' vcom mem1 C') /\
      addr_shared_so_far addr
        (rcons (project_non_inform prefix)
           (ECall (cur_comp s) P' new_arg mem' C'))
addr_shared_so_far_ECall_Hshared_interm
  : forall (P P' : Procedure.id) (C C' : Component.id) 
      (s : stack_state) (prefix : seq event_inform) 
      (prefix' : seq event) (new_arg : value) (mem' : Memory.t)
      (regs : Machine.Intermediate.Register.t) (suffix : trace event_inform)
      (arg : value) (stk : seq CS.frame) (mem1 : Memory.tt)
      (mem10 : Memory.t) (vcom : value),
    well_formed_state_r {| cur_comp := C'; callers := C :: callers s |}
      (prefix ++ [:: ECallInform (cur_comp s) P' new_arg mem' regs C'])
      suffix
      [CState C', {|
                  CS.f_component := C;
                  CS.f_arg := arg;
                  CS.f_cont := Kassign1 (loc_of_reg E_R_COM)
                                 (Kseq
                                    (invalidate_metadata;;
                                     E_assign EXTCALL (E_val (Int 0));;
                                     E_call C P (E_val (Int 0))) Kstop) |}
                  :: stk, mem10, Kstop, expr_of_trace C' P'
                                          (comp_subtrace C' t), vcom] ->
    forall (Cb : Component.id) (b : Block.id),
    addr_shared_so_far (Cb, b)
      (rcons (project_non_inform prefix)
         (ECall (cur_comp s) P' new_arg mem' C')) ->
    addr_shared_so_far (Cb, S b) (rcons prefix' (ECall C P' vcom mem1 C'))

COQC Source/DefinabilityEnd.v
Axioms:
Source.well_formed_program_unlink
  : forall (Cs : {fset Component.id}) (p : Source.program),
    Source.well_formed_program p ->
    Source.well_formed_program (Source.program_unlink Cs p)
well_formed_events_well_formed_program
  : forall intf : Program.interface,
    closed_interface intf ->
    intf Component.main ->
    forall prog_buffers : NMap (nat + seq value),
    (forall (C : nat_ordType) (buf : nat + seq value),
     prog_buffers C = Some buf -> Buffer.well_formed_buffer buf) ->
    forall (T : Type) (procs : NMap (NMap T)) (t : seq event_inform),
    all (well_formed_event intf procs) t ->
    Source.well_formed_program (program_of_trace intf prog_buffers t)
star_well_formed_intermediate_prefix
  : forall (p : Intermediate.program) (t : trace event_inform)
      (s : state (I.CS.sem_inform p)),
    Intermediate.well_formed_program p ->
    Star (I.CS.sem_inform p) (I.CS.initial_machine_state p) t s ->
    well_formed_intermediate_prefix (Intermediate.prog_interface p)
      (Intermediate.prog_buffers p) t
pointer_of_alloc
  : forall intf : Program.interface,
    closed_interface intf ->
    intf Component.main ->
    forall prog_buffers : NMap (nat + seq value),
    domm intf = domm prog_buffers ->
    (forall (C : nat_ordType) (buf : nat + seq value),
     prog_buffers C = Some buf -> Buffer.well_formed_buffer buf) ->
    forall (t : trace event_inform) (T : Type) (t_procs : NMap (NMap T)),
    domm t_procs = domm intf ->
    all (well_formed_event intf t_procs) t ->
    forall p_interm : Intermediate.program,
    (exists s : CS.state,
       CSInvariants.CSInvariants.is_prefix s p_interm (project_non_inform t)) ->
    forall (mem : Memory.t) (cid : Component.id) (sz : nat) 
      (mem' : Memory.t) (ptr' : Pointer.t) (nb : Block.id),
    Memory.alloc mem cid sz = Some (mem', ptr') ->
    next_block mem cid = Some nb -> ptr' = (Permission.data, cid, nb, 0%Z)
CSInvariants.CSInvariants.not_executing_can_not_share
  : forall (s : CS.state) (p : Intermediate.program) 
      (t : seq event) (e : event) (C : Component.id) 
      (b : Block.id),
    Intermediate.well_formed_program p ->
    Intermediate.closed_program p ->
    CSInvariants.CSInvariants.is_prefix s p (rcons t e) ->
    C <> cur_comp_of_event e ->
    (forall b' : Block.id, ~ addr_shared_so_far (C, b') t) ->
    ~ addr_shared_so_far (C, b) (rcons t e)
next_block_prepare_buffers
  : forall intf : Program.interface,
    closed_interface intf ->
    intf Component.main ->
    forall prog_buffers : NMap (nat + seq value),
    domm intf = domm prog_buffers ->
    (forall (C : nat_ordType) (buf : nat + seq value),
     prog_buffers C = Some buf -> Buffer.well_formed_buffer buf) ->
    forall (t : trace event_inform) (T : Type) (t_procs : NMap (NMap T)),
    domm t_procs = domm intf ->
    all (well_formed_event intf t_procs) t ->
    forall p_interm : Intermediate.program,
    (exists s : CS.state,
       CSInvariants.CSInvariants.is_prefix s p_interm (project_non_inform t)) ->
    Intermediate.well_formed_program p_interm ->
    Intermediate.closed_program p_interm ->
    Intermediate.prog_interface p_interm = intf ->
    forall C : nat_ordType,
    Definability.component_buffer intf C ->
    next_block
      (Source.prepare_buffers (program_of_trace intf prog_buffers t)) C =
    Some LOCALBUF_blockid
next_block_initial_memory
  : forall intf : Program.interface,
    closed_interface intf ->
    intf Component.main ->
    forall prog_buffers : NMap (nat + seq value),
    domm intf = domm prog_buffers ->
    (forall (C : nat_ordType) (buf : nat + seq value),
     prog_buffers C = Some buf -> Buffer.well_formed_buffer buf) ->
    forall (t : trace event_inform) (T : Type) (t_procs : NMap (NMap T)),
    domm t_procs = domm intf ->
    all (well_formed_event intf t_procs) t ->
    forall p_interm : Intermediate.program,
    (exists s : CS.state,
       CSInvariants.CSInvariants.is_prefix s p_interm (project_non_inform t)) ->
    Intermediate.well_formed_program p_interm ->
    Intermediate.closed_program p_interm ->
    Intermediate.prog_interface p_interm = intf ->
    forall C : nat_ordType,
    Definability.component_buffer intf C ->
    next_block
      (mkfmapf
         (fun C0 : nat_ordType =>
          ComponentMemory.prealloc
            match prog_buffers C0 with
            | Some buf => [fmap (Block.local, buf)]
            | None => emptym
            end) (domm intf)) C = Some 1
next_block_alloc_neq
  : forall intf : Program.interface,
    closed_interface intf ->
    intf Component.main ->
    forall prog_buffers : NMap (nat + seq value),
    domm intf = domm prog_buffers ->
    (forall (C : nat_ordType) (buf : nat + seq value),
     prog_buffers C = Some buf -> Buffer.well_formed_buffer buf) ->
    forall (t : trace event_inform) (T : Type) (t_procs : NMap (NMap T)),
    domm t_procs = domm intf ->
    all (well_formed_event intf t_procs) t ->
    forall p_interm : Intermediate.program,
    (exists s : CS.state,
       CSInvariants.CSInvariants.is_prefix s p_interm (project_non_inform t)) ->
    forall (m : Memory.t) (C : Component.id) (n : nat) 
      (m' : Memory.t) (b : Pointer.t) (C' : Component.id),
    Memory.alloc m C n = Some (m', b) ->
    C' <> C -> next_block m' C' = next_block m C'
next_block_alloc
  : forall intf : Program.interface,
    closed_interface intf ->
    intf Component.main ->
    forall prog_buffers : NMap (nat + seq value),
    domm intf = domm prog_buffers ->
    (forall (C : nat_ordType) (buf : nat + seq value),
     prog_buffers C = Some buf -> Buffer.well_formed_buffer buf) ->
    forall (t : trace event_inform) (T : Type) (t_procs : NMap (NMap T)),
    domm t_procs = domm intf ->
    all (well_formed_event intf t_procs) t ->
    forall p_interm : Intermediate.program,
    (exists s : CS.state,
       CSInvariants.CSInvariants.is_prefix s p_interm (project_non_inform t)) ->
    forall (m : Memory.t) (C : Component.id) (n : nat) 
      (m' : Memory.t) (b : Pointer.t),
    Memory.alloc m C n = Some (m', b) ->
    next_block m C = Some (Pointer.block b) /\
    next_block m' C = Some (ssrnat.addn (Pointer.block b) 1)
load_prepare_buffers
  : forall intf : Program.interface,
    closed_interface intf ->
    intf Component.main ->
    forall prog_buffers : NMap (nat + seq value),
    domm intf = domm prog_buffers ->
    (forall (C : nat_ordType) (buf : nat + seq value),
     prog_buffers C = Some buf -> Buffer.well_formed_buffer buf) ->
    forall (t : trace event_inform) (T : Type) (t_procs : NMap (NMap T)),
    domm t_procs = domm intf ->
    all (well_formed_event intf t_procs) t ->
    forall p_interm : Intermediate.program,
    (exists s : CS.state,
       CSInvariants.CSInvariants.is_prefix s p_interm (project_non_inform t)) ->
    Intermediate.well_formed_program p_interm ->
    Intermediate.closed_program p_interm ->
    Intermediate.prog_interface p_interm = intf ->
    forall (C : nat_ordType) (o : nat),
    Definability.component_buffer intf C ->
    Memory.load
      (Source.prepare_buffers (program_of_trace intf prog_buffers t))
      (Permission.data, C, Block.local, Z.of_nat o) = 
    nth_error meta_buffer o
load_next_block_None
  : forall intf : Program.interface,
    closed_interface intf ->
    intf Component.main ->
    forall prog_buffers : NMap (nat + seq value),
    domm intf = domm prog_buffers ->
    (forall (C : nat_ordType) (buf : nat + seq value),
     prog_buffers C = Some buf -> Buffer.well_formed_buffer buf) ->
    forall (t : trace event_inform) (T : Type) (t_procs : NMap (NMap T)),
    domm t_procs = domm intf ->
    all (well_formed_event intf t_procs) t ->
    forall p_interm : Intermediate.program,
    (exists s : CS.state,
       CSInvariants.CSInvariants.is_prefix s p_interm (project_non_inform t)) ->
    Intermediate.well_formed_program p_interm ->
    Intermediate.closed_program p_interm ->
    Intermediate.prog_interface p_interm = intf ->
    forall (mem : Memory.t) (ptr : Pointer.t) (b : Block.id),
    next_block mem (Pointer.component ptr) = Some b ->
    Pointer.block ptr >= b -> Memory.load mem ptr = None
ComponentMemory.load_next_block
CS.load_data_next_block
  : forall p : Source.program,
    Source.well_formed_program p ->
    Source.closed_program p ->
    forall (s : Source.CS.CS.state) (t : trace event) 
      (s' : state (CS.sem p)) (ptr : Pointer.t) (C : Component.id)
      (b : Block.id) (o : Block.offset),
    Source.CS.CS.initial_state p s ->
    Star (CS.sem p) s t s' ->
    Memory.load (CS.s_memory s') ptr = Some (Ptr (Permission.data, C, b, o)) ->
    exists Cmem : ComponentMemory.t,
      CS.s_memory s' C = Some Cmem /\ b < ComponentMemory.next_block Cmem
CS.load_component_prog_interface_addr
  : forall p : Source.program,
    Source.well_formed_program p ->
    Source.closed_program p ->
    forall (s : Source.CS.CS.state) (t : trace event) 
      (s' : state (CS.sem p)) (ptr : Pointer.t) (v : value),
    Source.CS.CS.initial_state p s ->
    Star (CS.sem p) s t s' ->
    Memory.load (CS.s_memory s') ptr = Some v ->
    Pointer.component ptr \in domm (Source.prog_interface p)
CS.load_component_prog_interface
  : forall p : Source.program,
    Source.well_formed_program p ->
    Source.closed_program p ->
    forall (s : Source.CS.CS.state) (t : trace event) 
      (s' : state (CS.sem p)) (ptr ptr' : Pointer.t),
    Source.CS.CS.initial_state p s ->
    Star (CS.sem p) s t s' ->
    Memory.load (CS.s_memory s') ptr = Some (Ptr ptr') ->
    Pointer.component ptr' \in domm (Source.prog_interface p)
CSInvariants.CSInvariants.load_Some_component_buffer
  : forall (p : Intermediate.program) (s : CS.state) 
      (t : seq event) (e : event) (ptr : Pointer.t) 
      (v : value),
    Intermediate.well_formed_program p ->
    Intermediate.closed_program p ->
    CSInvariants.CSInvariants.is_prefix s p (rcons t e) ->
    Memory.load (mem_of_event e) ptr = Some v ->
    Pointer.component ptr \in domm (Intermediate.prog_interface p)
CS.intermediate_well_formed_events
  : forall p : Intermediate.program,
    Intermediate.well_formed_program p ->
    Intermediate.closed_program p ->
    forall (st : state (CS.sem_inform p)) (t : trace event_inform)
      (st' : state (CS.sem_inform p)),
    Star (CS.sem_inform p) st t st' ->
    all
      (well_formed_event (Intermediate.prog_interface p)
         (Intermediate.prog_procedures p)) t
initialization_correct_component_memory
  : forall (C : Component.id) (mem mem' : Memory.t),
    (forall (C' : Component.id) (b : Block.id) (offset : Block.offset),
     C <> C' ->
     Memory.load mem (Permission.data, C', b, offset) =
     Memory.load mem' (Permission.data, C', b, offset)) ->
    (forall C' : Component.id,
     C <> C' -> next_block mem C' = next_block mem' C') ->
    forall C' : Component.id, C <> C' -> mem C' = mem' C'
initialization_correct
  : forall intf : Program.interface,
    closed_interface intf ->
    intf Component.main ->
    forall prog_buffers : NMap (nat + seq value),
    domm intf = domm prog_buffers ->
    (forall (C : nat_ordType) (buf : nat + seq value),
     prog_buffers C = Some buf -> Buffer.well_formed_buffer buf) ->
    forall (t : trace event_inform) (T : Type) (t_procs : NMap (NMap T)),
    domm t_procs = domm intf ->
    all (well_formed_event intf t_procs) t ->
    forall p_interm : Intermediate.program,
    (exists s : CS.state,
       CSInvariants.CSInvariants.is_prefix s p_interm (project_non_inform t)) ->
    Intermediate.well_formed_program p_interm ->
    Intermediate.closed_program p_interm ->
    Intermediate.prog_interface p_interm = intf ->
    forall (C : nat_ordType) (stk : Source.CS.CS.stack) 
      (mem : Memory.t) (k : cont) (arg : value) (prefix : trace event_inform)
      (e : event_inform),
    Definability.component_buffer intf C ->
    postcondition_steady_state e mem C \/
    postcondition_uninitialized prog_buffers prefix e mem C ->
    exists (mem' : Memory.t) (i : Z),
      star CS.kstep
        (prepare_global_env (program_of_trace intf prog_buffers t))
        [CState C, stk, mem, k, init_check prog_buffers C, arg] E0
        [CState C, stk, mem', k, E_val (Int i), arg] /\
      postcondition_steady_state e mem' C /\
      (forall offset : Z,
       offset <> INITFLAG_offset ->
       offset <> LOCALBUF_offset ->
       Memory.load mem (Permission.data, C, Block.local, offset) =
       Memory.load mem' (Permission.data, C, Block.local, offset)) /\
      (forall (C' : nat_ordType) (b : Block.id) (offset : Block.offset),
       C <> C' ->
       Memory.load mem (Permission.data, C', b, offset) =
       Memory.load mem' (Permission.data, C', b, offset)) /\
      (forall C' : nat_ordType,
       C <> C' -> next_block mem C' = next_block mem' C') /\
      (forall (C' : nat_ordType) (b : Block.id) (offset : Block.offset),
       C = C' ->
       b <> Block.local ->
       postcondition_steady_state e mem C ->
       Memory.load mem (Permission.data, C', b, offset) =
       Memory.load mem' (Permission.data, C', b, offset))
CS.eval_kstep_sound
  : forall (G : global_env) (st : Source.CS.CS.state) 
      (t : trace event) (st' : Source.CS.CS.state),
    CS.eval_kstep G st = Some (t, st') -> CS.kstep G st t st'
definability_does_not_leak
  : forall intf : Program.interface,
    closed_interface intf ->
    intf Component.main ->
    forall prog_buffers : NMap (nat + seq value),
    domm intf = domm prog_buffers ->
    (forall (C : nat_ordType) (buf : nat + seq value),
     prog_buffers C = Some buf -> Buffer.well_formed_buffer buf) ->
    forall (t : trace event_inform) (T : Type) (t_procs : NMap (NMap T)),
    domm t_procs = domm intf ->
    all (well_formed_event intf t_procs) t ->
    forall p_interm : Intermediate.program,
    (exists s : CS.state,
       CSInvariants.CSInvariants.is_prefix s p_interm (project_non_inform t)) ->
    Intermediate.well_formed_program p_interm ->
    Intermediate.closed_program p_interm ->
    Intermediate.prog_interface p_interm = intf ->
    CS.private_pointers_never_leak_S (program_of_trace intf prog_buffers t)
      (uniform_shift 1)
component_memory_after_store_neq
  : forall (mem : Memory.t) (ptr : Pointer.t) (v : value) 
      (mem' : Memory.t) (C : Component.id),
    Memory.store mem ptr v = Some mem' ->
    Pointer.component ptr <> C -> mem C = mem' C
component_memory_after_alloc_neq
  : forall (mem : Memory.t) (C : Component.id) (sz : nat) 
      (mem' : Memory.t) (ptr : Pointer.t) (C' : Component.id),
    Memory.alloc mem C sz = Some (mem', ptr) -> C' <> C -> mem C' = mem' C'
Source.CS.CS.comes_from_initial_state_mem_domm
  : forall p : Source.program,
    Source.well_formed_program p ->
    Source.closed_program p ->
    forall (s : Source.CS.CS.state) (t : trace event) (s' : state (CS.sem p)),
    Source.CS.CS.initial_state p s ->
    Star (CS.sem p) s t s' ->
    domm (CS.s_memory s') = domm (Source.prog_interface p)
Memory.alloc_after_load
  : forall (mem : Memory.t) (P : Permission.id) (C : Component.id)
      (b : Block.id) (o : Block.offset) (v : value) 
      (size : nat),
    Memory.load mem (P, C, b, o) = Some v ->
    exists (mem' : Memory.t) (b' : Block.id),
      b' <> b /\
      Memory.alloc mem C size = Some (mem', (Permission.data, C, b', 0%Z))
addr_shared_so_far_inv_2
  : forall intf : Program.interface,
    closed_interface intf ->
    intf Component.main ->
    forall prog_buffers : NMap (nat + seq value),
    domm intf = domm prog_buffers ->
    (forall (C : nat_ordType) (buf : nat + seq value),
     prog_buffers C = Some buf -> Buffer.well_formed_buffer buf) ->
    forall (t : trace event_inform) (T : Type) (t_procs : NMap (NMap T)),
    domm t_procs = domm intf ->
    all (well_formed_event intf t_procs) t ->
    forall p_interm : Intermediate.program,
    (exists s : CS.state,
       CSInvariants.CSInvariants.is_prefix s p_interm (project_non_inform t)) ->
    Intermediate.well_formed_program p_interm ->
    Intermediate.closed_program p_interm ->
    Intermediate.prog_interface p_interm = intf ->
    forall (ret_val : value) (mem' : Memory.tt)
      (regs : Intermediate.Register.t) (C C' : Component.id)
      (s : stack_state) (prefix0 : seq event_inform)
      (eprev ecur : event_inform) (ecur_noninf : event),
    project_non_inform [:: ecur] = [:: ecur_noninf] ->
    well_formed_intermediate_prefix intf prog_buffers
      ((prefix0 ++ [:: eprev]) ++ [:: ecur]) ->
    forall
      mem0 mem mem1 mem1' mem2 mem3 mem4 mem5 mem6 mem7 mem8 mem9 : Memory.tt,
    C = cur_comp s ->
    forall vcom : value,
    Memory.load mem0 (Permission.data, cur_comp s, Block.local, 5%Z) =
    Some vcom ->
    Memory.store mem (Permission.data, C, Block.local, EXTCALL_offset)
      (Int 1) = Some mem1 ->
    Memory.store mem1 (Permission.data, C', Block.local, 5%Z) vcom =
    Some mem1' ->
    Memory.store mem1' (Permission.data, C', Block.local, 4%Z) Undef =
    Some mem2 ->
    Memory.store mem2 (Permission.data, C', Block.local, 6%Z) Undef =
    Some mem3 ->
    Memory.store mem3 (Permission.data, C', Block.local, 7%Z) Undef =
    Some mem4 ->
    Memory.store mem4 (Permission.data, C', Block.local, 8%Z) Undef =
    Some mem5 ->
    Memory.store mem5 (Permission.data, C', Block.local, 9%Z) Undef =
    Some mem6 ->
    Memory.store mem6 (Permission.data, C', Block.local, 10%Z) Undef =
    Some mem7 ->
    Memory.store mem7 (Permission.data, C', Block.local, EXTCALL_offset)
      (Int 0) = Some mem8 ->
    forall (Cb : Component.id) (b : Block.id) (addr' : addr_t),
    addr_shared_so_far (Cb, b)
      (rcons (project_non_inform (prefix0 ++ [:: eprev])) ecur_noninf) ->
    postcondition_event_registers
      (ERetInform (cur_comp s) ret_val mem' regs C') mem9 ->
    (forall C0 : nat_ordType,
     Definability.component_buffer intf C0 ->
     C0 = next_comp_of_event (ERetInform (cur_comp s) ret_val mem' regs C') ->
     postcondition_steady_state
       (ERetInform (cur_comp s) ret_val mem' regs C') mem9 C0) ->
    (forall C0 : nat_ordType,
     Definability.component_buffer intf C0 ->
     C0 <> next_comp_of_event (ERetInform (cur_comp s) ret_val mem' regs C') ->
     postcondition_steady_state
       (ERetInform (cur_comp s) ret_val mem' regs C') mem9 C0 \/
     postcondition_uninitialized prog_buffers (prefix0 ++ [:: eprev]) ecur
       mem9 C0) ->
    Reachability.Reachable (mem_of_event (ERet C vcom mem1 C')) 
      (fset1 addr') (Cb, S b)
addr_shared_so_far_inv_1
  : forall intf : Program.interface,
    closed_interface intf ->
    intf Component.main ->
    forall prog_buffers : NMap (nat + seq value),
    domm intf = domm prog_buffers ->
    (forall (C : nat_ordType) (buf : nat + seq value),
     prog_buffers C = Some buf -> Buffer.well_formed_buffer buf) ->
    forall (t : trace event_inform) (T : Type) (t_procs : NMap (NMap T)),
    domm t_procs = domm intf ->
    all (well_formed_event intf t_procs) t ->
    forall p_interm : Intermediate.program,
    (exists s : CS.state,
       CSInvariants.CSInvariants.is_prefix s p_interm (project_non_inform t)) ->
    Intermediate.well_formed_program p_interm ->
    Intermediate.closed_program p_interm ->
    Intermediate.prog_interface p_interm = intf ->
    forall (ret_val : value) (mem' : Memory.tt),
    Intermediate.Register.t ->
    forall C C' : Component.id,
    C <> C' ->
    forall (prefix0 : seq event_inform) (eprev ecur : event_inform)
      (ecur_noninf : event),
    project_non_inform [:: ecur] = [:: ecur_noninf] ->
    well_formed_intermediate_prefix intf prog_buffers
      ((prefix0 ++ [:: eprev]) ++ [:: ecur]) ->
    forall
      (mem0 mem mem1 mem1' mem2 mem3 mem4 mem5 mem6 mem7 mem8 : Memory.tt)
      (vcom : value),
    Memory.load mem0 (Permission.data, C, Block.local, 5%Z) = Some vcom ->
    Memory.store mem (Permission.data, C, Block.local, EXTCALL_offset)
      (Int 1) = Some mem1 ->
    Memory.store mem1 (Permission.data, C', Block.local, 5%Z) vcom =
    Some mem1' ->
    Memory.store mem1' (Permission.data, C', Block.local, 4%Z) Undef =
    Some mem2 ->
    Memory.store mem2 (Permission.data, C', Block.local, 6%Z) Undef =
    Some mem3 ->
    Memory.store mem3 (Permission.data, C', Block.local, 7%Z) Undef =
    Some mem4 ->
    Memory.store mem4 (Permission.data, C', Block.local, 8%Z) Undef =
    Some mem5 ->
    Memory.store mem5 (Permission.data, C', Block.local, 9%Z) Undef =
    Some mem6 ->
    Memory.store mem6 (Permission.data, C', Block.local, 10%Z) Undef =
    Some mem7 ->
    Memory.store mem7 (Permission.data, C', Block.local, EXTCALL_offset)
      (Int 0) = Some mem8 ->
    forall (Cb : Component.id) (b : Block.id),
    Reachability.Reachable mem' (addr_of_value ret_val) (Cb, b) ->
    postcondition_event_registers ecur mem8 ->
    addr_shared_so_far (Cb, b)
      (rcons (project_non_inform (prefix0 ++ [:: eprev])) ecur_noninf) ->
    (forall C0 : nat_ordType,
     Definability.component_buffer intf C0 ->
     C0 = next_comp_of_event ecur -> postcondition_steady_state ecur mem8 C0) ->
    (forall C0 : nat_ordType,
     Definability.component_buffer intf C0 ->
     C0 <> next_comp_of_event ecur ->
     postcondition_steady_state ecur mem8 C0 \/
     postcondition_uninitialized prog_buffers (...) ecur mem8 C0) ->
    C = cur_comp_of_event ecur_noninf ->
    C' = next_comp_of_event ecur ->
    mem' = mem_of_event_inform ecur ->
    ret_val = arg_of_event ecur_noninf ->
    Reachability.Reachable mem1 (addr_of_value vcom) (Cb, S b)
addr_shared_so_far_ERet_Hsharedsrc
  : forall intf : Program.interface,
    closed_interface intf ->
    intf Component.main ->
    forall prog_buffers : NMap (nat + seq value),
    domm intf = domm prog_buffers ->
    (forall (C : nat_ordType) (buf : nat + seq value),
     prog_buffers C = Some buf -> Buffer.well_formed_buffer buf) ->
    forall (t : trace event_inform) (T : Type) (t_procs : NMap (NMap T)),
    domm t_procs = domm intf ->
    all (well_formed_event intf t_procs) t ->
    forall p_interm : Intermediate.program,
    (exists s : CS.state,
       CSInvariants.CSInvariants.is_prefix s p_interm (project_non_inform t)) ->
    Intermediate.well_formed_program p_interm ->
    Intermediate.closed_program p_interm ->
    Intermediate.prog_interface p_interm = intf ->
    forall (ret_val : value) (mem' : Memory.t)
      (regs : Intermediate.Register.t) (C' : Component.id)
      (prefix suffix : seq event_inform) (s : stack_state),
    well_formed_intermediate_prefix intf prog_buffers
      (prefix ++ [:: ERetInform (cur_comp s) ret_val mem' regs C']) ->
    forall (prefix' : trace event) (mem0 : Memory.tt) (mem mem1 : Memory.t),
    Memory.store mem
      (Permission.data, cur_comp s, Block.local, EXTCALL_offset) 
      (Int 1) = Some mem1 ->
    forall vcom : value,
    Memory.load mem0
      (Permission.data, cur_comp s, Block.local, reg_offset E_R_COM) =
    Some vcom ->
    forall mem1' : Memory.t,
    Memory.store mem1 (Permission.data, C', Block.local, reg_offset E_R_COM)
      vcom = Some mem1' ->
    forall mem2 : Memory.t,
    Memory.store mem1' (Permission.data, C', Block.local, reg_offset E_R_ONE)
      Undef = Some mem2 ->
    forall mem3 : Memory.t,
    Memory.store mem2 (Permission.data, C', Block.local, reg_offset E_R_AUX1)
      Undef = Some mem3 ->
    forall mem4 : Memory.t,
    Memory.store mem3 (Permission.data, C', Block.local, reg_offset E_R_AUX2)
      Undef = Some mem4 ->
    forall mem5 : Memory.t,
    Memory.store mem4 (Permission.data, C', Block.local, reg_offset E_R_RA)
      Undef = Some mem5 ->
    forall mem6 : Memory.t,
    Memory.store mem5 (Permission.data, C', Block.local, reg_offset E_R_SP)
      Undef = Some mem6 ->
    forall mem7 : Memory.t,
    Memory.store mem6 (Permission.data, C', Block.local, reg_offset E_R_ARG)
      Undef = Some mem7 ->
    forall mem8 : Memory.t,
    Memory.store mem7 (Permission.data, C', Block.local, EXTCALL_offset)
      (Int 0) = Some mem8 ->
    forall (s' : stack_state) (cs' : Source.CS.CS.state),
    well_formed_state_r intf prog_buffers t T s'
      (prefix ++ [:: ERetInform (cur_comp s) ret_val mem' regs C']) suffix
      cs' ->
    forall (Cb : Component.id) (b : Block.id),
    addr_shared_so_far (Cb, b) (rcons prefix' (ERet ... vcom mem1 C')) ->
    exists addr : addr_t,
      sigma_shifting_wrap_bid_in_addr (...) addr = Some (Cb, b) /\
      event_renames_event_at_shared_addr all_zeros_shift 
        (...) addr (...) (...) /\ addr_shared_so_far addr (...)
addr_shared_so_far_ECall_Hshared_src
  : forall intf : Program.interface,
    closed_interface intf ->
    intf Component.main ->
    forall prog_buffers : NMap (nat + seq value),
    domm intf = domm prog_buffers ->
    (forall (C : nat_ordType) (buf : nat + seq value),
     prog_buffers C = Some buf -> Buffer.well_formed_buffer buf) ->
    forall (t : trace event_inform) (T : Type) (t_procs : NMap (NMap T)),
    domm t_procs = domm intf ->
    all (well_formed_event intf t_procs) t ->
    forall p_interm : Intermediate.program,
    (exists s : CS.state,
       CSInvariants.CSInvariants.is_prefix s p_interm (project_non_inform t)) ->
    Intermediate.well_formed_program p_interm ->
    Intermediate.closed_program p_interm ->
    Intermediate.prog_interface p_interm = intf ->
    forall (P' : Procedure.id) (new_arg : value) (mem' : Memory.t)
      (regs : Intermediate.Register.t) (C' : Component.id)
      (prefix suffix : seq event_inform) (s : stack_state),
    well_formed_intermediate_prefix intf prog_buffers
      (prefix ++ [:: ECallInform (cur_comp s) P' new_arg mem' regs C']) ->
    forall (prefix' : trace event) (stk : Source.CS.CS.stack)
      (mem0 : Memory.tt) (arg : value) (P : Procedure.id) 
      (mem : Memory.t) (vcom : value),
    Memory.load mem0
      (Permission.data, cur_comp s, Block.local, reg_offset E_R_COM) =
    Some vcom ->
    forall mem1 : Memory.t,
    Memory.store mem
      (Permission.data, cur_comp s, Block.local, EXTCALL_offset) 
      (Int 1) = Some mem1 ->
    forall mem2 : Memory.t,
    (forall offset : Z,
     offset <> INITFLAG_offset ->
     offset <> LOCALBUF_offset ->
     Memory.load mem1 (Permission.data, C', Block.local, offset) =
     Memory.load mem2 (Permission.data, C', Block.local, offset)) ->
    forall mem3 : Memory.t,
    Memory.store mem2 (Permission.data, C', Block.local, reg_offset E_R_ONE)
      Undef = Some mem3 ->
    forall mem4 : Memory.t,
    Memory.store mem3 (Permission.data, C', Block.local, reg_offset E_R_AUX1)
      Undef = Some mem4 ->
    forall mem5 : Memory.t,
    Memory.store mem4 (Permission.data, C', Block.local, reg_offset E_R_AUX2)
      Undef = Some mem5 ->
    forall mem6 : Memory.t,
    Memory.store mem5 (Permission.data, C', Block.local, reg_offset E_R_RA)
      Undef = Some mem6 ->
    forall mem7 : Memory.t,
    Memory.store mem6 (Permission.data, C', Block.local, reg_offset E_R_SP)
      Undef = Some mem7 ->
    forall mem8 : Memory.t,
    Memory.store mem7 (Permission.data, C', Block.local, reg_offset E_R_ARG)
      Undef = Some mem8 ->
    forall mem9 : Memory.t,
    Memory.store mem8 (Permission.data, C', Block.local, reg_offset E_R_COM)
      vcom = Some mem9 ->
    forall mem10 : Memory.t,
    Memory.store mem9 (Permission.data, C', Block.local, 1%Z) (Int 0) =
    Some mem10 ->
    well_formed_state_r intf prog_buffers t T
      {| cur_comp := C'; callers := cur_comp s :: callers s |}
      (prefix ++ [:: ECallInform (cur_comp s) P' new_arg mem' regs C'])
      suffix
      [CState C', {|
                  S.CS.f_component := cur_comp s;
                  S.CS.f_arg := arg;
                  S.CS.f_cont := Kassign1 (...) (...) |} :: stk, mem10, Kstop, 
      expr_of_trace C' P' (comp_subtrace C' t), vcom] ->
    forall (Cb : Component.id) (b : Block.id),
    addr_shared_so_far (Cb, b) (rcons prefix' (...)) ->
    exists addr : addr_t,
      sigma_shifting_wrap_bid_in_addr ... addr = Some ... /\
      event_renames_event_at_shared_addr all_zeros_shift ... addr ... ... /\
      addr_shared_so_far addr ...
addr_shared_so_far_ECall_Hshared_interm
  : forall intf : Program.interface,
    closed_interface intf ->
    intf Component.main ->
    forall prog_buffers : NMap (nat + seq value),
    domm intf = domm prog_buffers ->
    (forall (C : nat_ordType) (buf : nat + seq value),
     prog_buffers C = Some buf -> Buffer.well_formed_buffer buf) ->
    forall (t : trace event_inform) (T : Type) (t_procs : NMap (NMap T)),
    domm t_procs = domm intf ->
    all (well_formed_event intf t_procs) t ->
    forall p_interm : Intermediate.program,
    (exists s : CS.state,
       CSInvariants.CSInvariants.is_prefix s p_interm (project_non_inform t)) ->
    Intermediate.well_formed_program p_interm ->
    Intermediate.closed_program p_interm ->
    Intermediate.prog_interface p_interm = intf ->
    forall (P P' : Procedure.id) (C C' : Component.id) 
      (s : stack_state) (prefix : seq event_inform) 
      (prefix' : seq event) (new_arg : value) (mem' : Memory.t)
      (regs : Intermediate.Register.t) (suffix : trace event_inform)
      (arg : value) (stk : seq CS.frame) (mem1 : Memory.tt)
      (mem10 : Memory.t) (vcom : value),
    well_formed_state_r intf prog_buffers t T
      {| cur_comp := C'; callers := C :: callers s |}
      (prefix ++ [:: ECallInform (cur_comp s) P' new_arg mem' regs C'])
      suffix
      [CState C', {|
                  S.CS.f_component := C;
                  S.CS.f_arg := arg;
                  S.CS.f_cont := Kassign1 (loc_of_reg E_R_COM)
                                   (Kseq
                                      (E_seq invalidate_metadata
                                         (E_seq
                                            (E_assign EXTCALL (E_val (Int 0)))
                                            (E_call C P (E_val (Int 0)))))
                                      Kstop) |} :: stk, mem10, Kstop, 
      expr_of_trace C' P' (comp_subtrace C' t), vcom] ->
    forall (Cb : Component.id) (b : Block.id),
    addr_shared_so_far (Cb, b)
      (rcons (project_non_inform prefix)
         (ECall (cur_comp s) P' new_arg mem' C')) ->
    addr_shared_so_far (Cb, S b) (rcons prefix' (ECall C P' vcom mem1 C'))

#### Recombination ####

  Print Assumptions threeway_multisem_star_program.
Axioms:
in_unzip2
  : forall (X : eqType) (x : X) (xs : NMap X),
    x \in unzip2 xs -> exists n : nat_ordType, xs n = Some x
CS.genv_procedures_prog_procedures
  : forall (p : program) (cid : nat_ordType) (proc : option (NMap code)),
    well_formed_program p ->
    genv_procedures (globalenv (CS.sem_inform p)) cid = proc <->
    prog_procedures p cid = proc
genv_entrypoints_interface_some
  : forall (p p' : program) (C : Component.id) (P : Procedure.id)
      (b : Block.id),
    well_formed_program p ->
    well_formed_program p' ->
    prog_interface p = prog_interface p' ->
    EntryPoint.get C P (genv_entrypoints (prepare_global_env p)) = Some b ->
    exists b' : Block.id,
      EntryPoint.get C P (genv_entrypoints (prepare_global_env p')) = Some b'
FunctionalExtensionality.functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
Classical_Prop.classic : forall P : Prop, P \/ ~ P

Print Assumptions recombination_prefix_rel.
Axioms:
in_unzip2
  : forall (X : eqType) (x : X) (xs : NMap X),
    x \in unzip2 xs -> exists n : nat_ordType, xs n = Some x
CS.genv_procedures_prog_procedures
  : forall (p : program) (cid : nat_ordType) (proc : option (NMap code)),
    well_formed_program p ->
    genv_procedures (globalenv (CS.sem_inform p)) cid = proc <->
    prog_procedures p cid = proc
genv_entrypoints_interface_some
  : forall (p p' : program) (C : Component.id) (P : Procedure.id)
      (b : Block.id),
    well_formed_program p ->
    well_formed_program p' ->
    prog_interface p = prog_interface p' ->
    EntryPoint.get C P (genv_entrypoints (prepare_global_env p)) = Some b ->
    exists b' : Block.id,
      EntryPoint.get C P (genv_entrypoints (prepare_global_env p')) = Some b'
FunctionalExtensionality.functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
ClassicalEpsilon.constructive_indefinite_description
  : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
Classical_Prop.classic : forall P : Prop, P \/ ~ P

#### Top level ####

well_formed_compilable
  : forall p : Source.program,
    Source.well_formed_program p ->
    exists pc : Intermediate.program, compile_program p = Some pc
separate_compilation
  : forall (p c : Source.program) (p_comp c_comp : Intermediate.program),
    Source.well_formed_program p ->
    Source.well_formed_program c ->
    linkable (Source.prog_interface p) (Source.prog_interface c) ->
    compile_program p = Some p_comp ->
    compile_program c = Some c_comp ->
    compile_program (Source.program_link p c) =
    Some (Intermediate.program_link p_comp c_comp)
Compiler.order : Compiler.index -> Compiler.index -> Prop
Compiler.match_states
  : forall (p : Source.program) (tp : Intermediate.program),
    Compiler.index ->
    state (S.CS.sem p) -> state (I.CS.sem_non_inform tp) -> Prop
Source.linking_well_formedness
  : forall p1 p2 : Source.program,
    Source.well_formed_program p1 ->
    Source.well_formed_program p2 ->
    linkable (Source.prog_interface p1) (Source.prog_interface p2) ->
    Source.well_formed_program (Source.program_link p1 p2)
Compiler.index : Type
Compiler.fsim_record
  : forall (p : Source.program) (tp : Intermediate.program),
    fsim_properties Events.event (S.CS.sem p) (I.CS.sem_non_inform tp)
      Compiler.index Compiler.order Compiler.match_states
Compiler.compiler_preserves_non_leakage_of_private_pointers
  : forall (p : Source.program) (p_compiled : Intermediate.program)
      (metadata_size : Component.id -> nat),
    Source.closed_program p ->
    Source.well_formed_program p ->
    compile_program p = Some p_compiled ->
    S.CS.private_pointers_never_leak_S p metadata_size ->
    private_pointers_never_leak_I p_compiled metadata_size
Compiler.compilation_preserves_well_formedness
  : forall (p : Source.program) (p_compiled : Intermediate.program),
    Source.well_formed_program p ->
    compile_program p = Some p_compiled ->
    Intermediate.well_formed_program p_compiled
compilation_preserves_main
  : forall (p : Source.program) (p_compiled : Intermediate.program),
    Source.well_formed_program p ->
    compile_program p = Some p_compiled ->
    (exists main : expr, Source.prog_main p = Some main) <->
    Intermediate.prog_main p_compiled
compilation_has_matching_mains
  : forall (p : Source.program) (p_compiled : Intermediate.program),
    Source.well_formed_program p ->
    compile_program p = Some p_compiled -> matching_mains p p_compiled
backward_simulation_star
  : forall (p : Source.program) (p_compiled : Intermediate.program)
      (t : Events.trace Events.event)
      (s : state (I.CS.sem_non_inform p_compiled)),
    Source.closed_program p ->
    Source.well_formed_program p ->
    compile_program p = Some p_compiled ->
    Star (I.CS.sem_non_inform p_compiled)
      (I.CS.initial_machine_state p_compiled) t s ->
    exists (s' : state (S.CS.sem p)) (i : Compiler.index),
      Star (S.CS.sem p) (S.CS.initial_machine_state p) t s' /\
      Compiler.match_states i s' s

### License ###
- This code is licensed under the Apache License, Version 2.0 (see `LICENSE`)
- The code in the `CompCert` dir is adapted based on files in the
  `common` and `lib` dirs of CompCert and is thus dual-licensed under
  the INRIA Non-Commercial License Agreement and the GNU General
  Public License version 2 or later (see `Compcert/LICENSE`)
