# SecurePtrs #

This branch contains the Coq development of the paper:
- **[SecurePtrs: Proving Secure Compilation Using
     Data-Flow Back-Translation nd Turn-Taking Simulation](https://arxiv.org/abs/2110.01439)**.
   Akram El-Korashy, Roberto Blanco, Jérémy Thibault,
   Adrien Durier, Deepak Garg, and Catalin Hritcu.
   arXiv:2110.01439. October 2021.

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

The following list maps the definitions and statements in the paper to their
mechanized counterparts in Coq.

- Definition 2.1 (RSP~): see statement of Theorem `RSC` in `RSC.v` for an instance of this definition

- Assumption 2.3 (FCC): `S2I/Compiler.v`, Lemma `I_simulates_S`

- Lemma 2.4 (recomposition): `Intermediate/RecombinationRel.v`, Theorem `recombination_trace_rel`

- Assumption 2.5 (BCC): `S2I/Compiler.v`, Lemma `S_simulates_I`

- Definition 2.6 (observable events): `CompCert/Events.v`, Inductive type `event`

- Definition 3.2 (data-flow events) `Common/TracesInform.v`, Inductive type `event_inform`

- Lemma 3.4 (enrichment): `Intermediate/CS.v`, Lemma `star_sem_non_inform_star_sem_inform`

- Lemma 3.5 (data-flow back-translation): `Source/Definability.v`, Lemma `definability`

- Definition 3.9 (turn-taking memory relation): `Intermediate/RecombinationRelCommon.v`, Inductive proposition `mergeable_internal_states`

- Definition 3.10 (relation on interaction traces): `Common/RenamingOption.v`, Inductive proposition `traces_shift_each_other_option`

- Theorem 4.1 (RSP~): Theorem `RSC` in `RSC.v`

- Lemma 5.1 (trace prefix mimicking): `Source/Definability.v`, Lemma `definability_gen_rel_right`

- Definition A.2 (memory relation at observable events): `Intermediate/RecombinationRelCommon.v`, Inductive proposition `mergeable_border_states`

- Lemma A.3 (strengthening at observable events): `Intermediate/RecombinationRelStrengthening.v`, Theorem `threeway_multisem_event_lockstep_program_step`

- Lemma A.4 (option simulation): `Intermediate/RecombinationRelOptionSim.v`, Lemma `merge_states_silent_star`

- Lemma A.5 (lockstep simulation): `Intermediate/RecombinationRelLockstepSim.v`, Theorem `threeway_multisem_star_E0`

### Assumptions ###

The proof currently relies on the following assumptions:

#### Logical axioms ####

The following standard axioms are used occasionally in our proofs.

```coq
FunctionalExtensionality.functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
Classical_Prop.classic : forall P : Prop, P \/ ~ P
ClassicalEpsilon.constructive_indefinite_description
  : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
```

#### Utility libraries ####

Our proofs use a simple property which is not currently available in the map
library that we use.

```coq
in_unzip2
  : forall (X : eqType) (x : X) (xs : NMap X),
    x \in unzip2 xs -> exists n : nat_ordType, xs n = Some x
```

#### Back-translation ####

The proof of back-translation currently relies on a small number of reasonable
assumptions. The well-formedness of the back-translated program holds by
construction. Like similar proofs that talk more generally about all source and
target language programs, a few simple adaptations are needed to accommodate the
strengthened notion of program well-formedness.

```coq
well_formed_events_well_formed_program
  : forall (T : Type) (procs : NMap (NMap T)) (t : seq event_inform),
    all (well_formed_event intf procs) t ->
    Source.well_formed_program (program_of_trace t)
```

A small number of renaming and reachability properties of procedure calls:

```coq
addr_shared_so_far_ECall_Hshared_src
  : forall ... ->
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
  : forall ... ->
    addr_shared_so_far (Cb, S b) (rcons prefix' (ECall C P' vcom mem1 C'))
    
addr_shared_so_far_inv_1
  : forall ... ->
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

addr_shared_so_far_inv_2
  : ... ->
    Reachability.Reachable (mem_of_event (ERet C vcom mem1 C')) 
      (fset1 addr') (Cb, S b)
```

Finally, we need to show that a back-translated program does not leak private
pointers, i.e., pointers to the meta-data buffers. While this property holds by
construction, the invariants required for its proof are quite different from
those used by the definability theorem. For this reason, this is better served
by an independent proof.

```coq
definability_does_not_leak
  : CS.private_pointers_never_leak_S p (uniform_shift 1)
```

#### Top level ####

We assume a certain number of top-level properties of our compilation chain.
These properties are mostly glue lemmas that help us make the different parts of
the proof fit together.

All of these results are standard compiler results that, after careful
inspection, we expect to hold for our compiler. For this reason, proving those
was not a focus of this work.

*Lemmas regarding compilation and well-formedness conditions*: we assume that
every well-formed source program can be compiled (`well_formed_compilable`),
and that compiling preserves certain well-formedness conditions 
(`Compiler.compilation_preserves_well_formedness`,
` compilation_preserves_main`, `compilation_has_matching_mains`).
```coq
well_formed_compilable
  : forall p : Source.program,
    Source.well_formed_program p ->
    exists pc : Intermediate.program, compile_program p = Some pc
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
```

*Lemmas regarding linking:* we assume that he compiler satisfies
`separate_compilation`: compilation and linking commute.
```coq
separate_compilation
  : forall (p c : Source.program) (p_comp c_comp : Intermediate.program),
    Source.well_formed_program p ->
    Source.well_formed_program c ->
    linkable (Source.prog_interface p) (Source.prog_interface c) ->
    compile_program p = Some p_comp ->
    compile_program c = Some c_comp ->
    compile_program (Source.program_link p c) =
    Some (Intermediate.program_link p_comp c_comp)
```

*Compiler correctness:* we also assume compiler correctness, under the form of a CompCert-style
forward simulation `Compiler.fsim_record`. We also assume the existence
of a backward simulation `backward_simulation_star`.
Finally, we assume `Compiler.compiler_preserves_non_leakage_of_private_pointers`,
that states that our compiler preserves the privacy of the local buffer.
Such a result could likely be proved by stating fine grained simulation invariants
in the compiler correctness proof.
```
Compiler.order : Compiler.index -> Compiler.index -> Prop
Compiler.match_states
  : forall (p : Source.program) (tp : Intermediate.program),
    Compiler.index ->
    state (S.CS.sem p) -> state (I.CS.sem_non_inform tp) -> Prop
Compiler.index : Type
Compiler.fsim_record
  : forall (p : Source.program) (tp : Intermediate.program),
    fsim_properties Events.event (S.CS.sem p) (I.CS.sem_non_inform tp)
      Compiler.index Compiler.order Compiler.match_states
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
Compiler.compiler_preserves_non_leakage_of_private_pointers
  : forall (p : Source.program) (p_compiled : Intermediate.program)
      (metadata_size : Component.id -> nat),
    Source.closed_program p ->
    Source.well_formed_program p ->
    compile_program p = Some p_compiled ->
    S.CS.private_pointers_never_leak_S p metadata_size ->
    private_pointers_never_leak_I p_compiled metadata_size
```

### License ###
- This code is licensed under the Apache License, Version 2.0 (see `LICENSE`)
- The code in the `CompCert` dir is adapted based on files in the
  `common` and `lib` dirs of CompCert and is thus dual-licensed under
  the INRIA Non-Commercial License Agreement and the GNU General
  Public License version 2 or later (see `CompCert/LICENSE`)

### Index of definitions ###

The source language `SafeP` corresponds to `Source` in the code. The target language `Mach` corresponds to `Interm` in the code.

- Backtranslation function `↑`: function `procedures_of_trace` in `Source/Definability.v`
- Data-flow events `E`: inductive `event_inform` in `Common/Definitions.v`
- Turn-taking simulation invariant `state_rel_tt`: definition `mergeable_internal_states` in `RecombinationRelCommon.v`
- Turn-taking simulation relation `mem_rel_tt`: memory part of the `mergeable_internal_states` definition in `Intermediate/RecombinationRelCommon.v`
- Strong memory relation holding at all locations of the executing part `mem_rel_exec`: definition `mem_of_part_executing_rel_original_and_recombined` in `Intermediate/RecombinationRelCommon.v`
- Memory relation holding only at private locations of the non-executing part `mem_rel_not_exec`: definition `mem_of_part_not_executing_rel_original_and_recombined_at_internal` in `Intermediate/RecombinationRelCommon.v`
- Function `shared`: inductive `addr_shared_so_far` in `Common/RenamingOption.v`
- Function `private`: negation of the inductive `addr_shared_so_far` in `Common/RenamingOption.v`
- Linking `C ∪ P`: functions `program_link` in `Source/Language.v` and `Intermediate/Language.v`
- Trace relation `~`: definition `traces_shift_each_other_option` in `Common/RenamingOption.v`
- Compilation function `↓`: function `compile_program` in `S2I/Compiler.v`
- Step relation `⇝`: definitions `kstep` in `Source/CS.v`; `step_non_inform` for non-data-flow semantics and `step` for data-flow semantics in `Intermediate/CS.v`
- Reflexive transitive closure `^*`: inductive `star` in `CompCert/Smallstep.v`
- Non-data-flow events `e`: definition `event` in `CompCert/Events.v`
- Source expressions `exp`: definition `expr` in `Source/Language.v`
- Interm instructions `instr`: definition `instr` in `Intermediate/Machine.v`
- Values `v`: definition `value` in `Common/Values.v`
- Removal of all internal data-flow events `remove_df`: function `project_non_inform` in `Common/TracesInform.v`
- Back-translation `mimicking_state` invariant: definition `well_formed_state` in `Source/Definability.v`
- Trace concatenation `++`: function `Eapp` in `CompCert/Events.v`
- Border-state relation `state_rel_border`: definition `mergeable_border_states` in `Intermediate/REcombinationRelCommon.v`
- "Is executing in" relation: `is_program_component` and `is_context_component` in `Intermediate/CS.v`
