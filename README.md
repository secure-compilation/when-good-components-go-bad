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

#### Logic axioms ####

```coq
FunctionalExtensionality.functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
Classical_Prop.classic : forall P : Prop, P \/ ~ P
ClassicalEpsilon.constructive_indefinite_description
  : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
```

#### Utility libraries ####

```coq
in_unzip2
  : forall (X : eqType) (x : X) (xs : NMap X),
    x \in unzip2 xs -> exists n : nat_ordType, xs n = Some x
```

#### Memory model ####

```coq
pointer_of_alloc
  : forall (mem : Memory.t) (cid : Component.id) (sz : nat) 
      (mem' : Memory.t) (ptr' : Pointer.t) (nb : Block.id),
    Memory.alloc mem cid sz = Some (mem', ptr') ->
    next_block mem cid = Some nb -> ptr' = (Permission.data, cid, nb, 0%Z)

Memory.alloc_after_load
  : forall (mem : Memory.t) (P : Permission.id) (C : Component.id)
      (b : Block.id) (o : Block.offset) (v : value) 
      (size : nat),
    Memory.load mem (P, C, b, o) = Some v ->
    exists (mem' : Memory.t) (b' : Block.id),
      b' <> b /\
      Memory.alloc mem C size = Some (mem', (Permission.data, C, b', 0%Z))

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

load_next_block_None
  : forall (mem : Memory.t) (ptr : Pointer.t) (b : Block.id),
    next_block mem (Pointer.component ptr) = Some b ->
    Pointer.block ptr >= b -> Memory.load mem ptr = None
ComponentMemory.load_next_block

component_memory_after_store_neq
  : forall (mem : Memory.t) (ptr : Pointer.t) (v : value) 
      (mem' : Memory.t) (C : Component.id),
    Memory.store mem ptr v = Some mem' ->
    Pointer.component ptr <> C -> mem C = mem' C
component_memory_after_alloc_neq
  : forall (mem : Memory.t) (C : Component.id) (sz : nat) 
      (mem' : Memory.t) (ptr : Pointer.t) (C' : Component.id),
    Memory.alloc mem C sz = Some (mem', ptr) -> C' <> C -> mem C' = mem' C'
```

#### Source language ####

```coq
Source.well_formed_program_unlink
  : forall (Cs : {fset Component.id}) (p : Source.program),
    Source.well_formed_program p ->
    Source.well_formed_program (Source.program_unlink Cs p)

next_block_prepare_buffers
  : forall C : nat_ordType,
    component_buffer C ->
    next_block (Source.prepare_buffers p) C = Some LOCALBUF_blockid

CS.eval_kstep_sound
  : forall (G : global_env) (st : CS.state) (t : trace event)
      (st' : CS.state),
    CS.eval_kstep G st = Some (t, st') -> CS.kstep G st t st'

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

CS.comes_from_initial_state_mem_domm
  : forall p : Source.program,
    Source.well_formed_program p ->
    Source.closed_program p ->
    forall (s : CS.state) (t : trace event) (s' : state (CS.sem p)),
    CS.initial_state p s ->
    Star (CS.sem p) s t s' ->
    domm (CS.s_memory s') = domm (Source.prog_interface p)
```

#### Target language ####

```coq
CSInvariants.CSInvariants.load_Some_component_buffer
  : forall (p : Machine.Intermediate.program) (s : CS.CS.state)
      (t : seq event) (e : event) (ptr : Pointer.t) 
      (v : value),
    Machine.Intermediate.well_formed_program p ->
    Machine.Intermediate.closed_program p ->
    CSInvariants.CSInvariants.is_prefix s p (rcons t e) ->
    Memory.load (mem_of_event e) ptr = Some v ->
    Pointer.component ptr \in domm (Machine.Intermediate.prog_interface p)

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
```

(From recombination)

```coq
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
```

(From definability. The first one concludes wf_int_pref, which is stated in definability, but plausibly belongs logically in here)

```coq
star_well_formed_intermediate_prefix
  : forall (p : Intermediate.program) (t : trace event_inform)
      (s : state (I.CS.sem_inform p)),
    Intermediate.well_formed_program p ->
    Star (I.CS.sem_inform p) (I.CS.initial_machine_state p) t s ->
    well_formed_intermediate_prefix (Intermediate.prog_interface p)
      (Intermediate.prog_buffers p) t
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
```

#### Back-translation ####

Axioms:

```coq
well_formed_events_well_formed_program
  : forall (T : Type) (procs : NMap (NMap T)) (t : seq event_inform),
    all (well_formed_event intf procs) t ->
    Source.well_formed_program (program_of_trace t)
next_block_initial_memory
  : forall C : nat_ordType,
    component_buffer C -> next_block initial_memory C = Some 1
load_prepare_buffers
  : forall (C : nat_ordType) (o : nat),
    component_buffer C ->
    Memory.load (Source.prepare_buffers p)
      (Permission.data, C, Block.local, Z.of_nat o) = 
    nth_error meta_buffer o
```

(This could be considered a memory model lemma, because the only reason it is admitted is due to the module type not exposing its reflection principle)

```coq
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
definability_does_not_leak
  : CS.private_pointers_never_leak_S p (uniform_shift 1)

addr_shared_so_far_inv_2
  : forall (ret_val : value) (mem' : Memory.tt)
      (regs : Machine.Intermediate.Register.t) (C C' : Component.id)
      (s : stack_state) (prefix0 : seq event_inform)
      (eprev ecur : event_inform) (ecur_noninf : event),
    ... ->
    Reachability.Reachable (mem_of_event (ERet C vcom mem1 C')) 
      (fset1 addr') (Cb, S b)
addr_shared_so_far_inv_1
  : forall (ret_val : value) (mem' : Memory.tt),
    ...
    Reachability.Reachable mem1 (addr_of_value vcom) (Cb, S b)
addr_shared_so_far_ERet_Hsharedsrc
  : forall (ret_val : value) (mem' : Memory.t)
      (regs : Machine.Intermediate.Register.t) (C' : Component.id)
      (prefix suffix : seq event_inform) (s : stack_state),
    ... ->
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
    ... ->
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
    ...
    addr_shared_so_far (Cb, S b) (rcons prefix' (ECall C P' vcom mem1 C'))
```

#### Top level ####

```coq
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
```

### License ###
- This code is licensed under the Apache License, Version 2.0 (see `LICENSE`)
- The code in the `CompCert` dir is adapted based on files in the
  `common` and `lib` dirs of CompCert and is thus dual-licensed under
  the INRIA Non-Commercial License Agreement and the GNU General
  Public License version 2 or later (see `Compcert/LICENSE`)
