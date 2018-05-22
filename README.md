# When Good Components Go Bad #

This repository contains the Coq development of the paper:
- Carmine Abate, Arthur Azevedo de Amorim, Roberto Blanco, Ana Nora Evans,
  Guglielmo Fachini, Catalin Hritcu, Théo Laurent, Benjamin C. Pierce,
  Marco Stronati, Andrew Tolmach.
  **[When Good Components Go Bad: Formally Secure Compilation Despite
     Dynamic Compromise](https://arxiv.org/abs/1802.00588)**. February 2018.

### IEEE S&P Reviews ###

File `sp2019-reviews-answers.txt` contains the reviews we received on
a previous IEEE S&P submission together with answers and explanations
of how we have improved the paper in response to this helpful feedback.

### Prerequisites ###

This development requires Coq v8.7.1, v8.7.2 or v8.8.0 to work, as well as the following libraries:
- [Mathematical Components](https://math-comp.github.io/math-comp/) 1.6.4 or 1.7.0
- [CoqUtils 17c7869](https://github.com/arthuraa/coq-utils/commit/17c78698c348ae15288fc8c147dc67e1df115596)
- [Extensional Structures 4d29a4d](https://github.com/arthuraa/extructures/commit/4d29a4d6da518f40b85876dd703eb5f71970f5db)

### Replaying the proofs ###

    $ make -j4

### Running the tests ###

Our tests are known to work with [QuickChick](https://github.com/QuickChick/QuickChick) 
branch 8.7 (with coq 8.7.1 or 8.7.2) and version 1.0.1 (with coq 8.8.0) and OCaml
from 4.02.3 to 4.06.

Running the tests (to be simplified):

    $ make clean
    $ make -j4
    $ ./run_extracted_examples.sh
    $ rm sfi_safety_properties.exe
    $ ./run_sfi_tests.sh

More thorough mutation tests are on the `nora-testing-experiments` branch.

### Top-level theorems ###

At the top level, the development provides high-level proofs with the following
entry points:
- `RSC_DC_MD.v`: generic secure compilation proof (Section 3.5) and
  its instantiation for our compiler (Section 4.3)
- `RSC_DC.v`: general proofs about the class of properties preserved
  by RSC^DC (Appendix A)
- `RSC_DC_4_compcert.v`: proofs in `RSC_DC.v` adapted to the general CompCert
  trace model (Appendix A)

The correspondences between the main definitions and results in the paper and
in Coq are as follows.

Definition 3.2: Robustly Safe Compilation with Dynamic Compromise (RSC^DC)
- `RSC_DC.RSC_dc` in the simple trace model
- `RSC_DC_4_compcert.RSC_dc` in the CompCert trace model

Definition 3.3: Robustly Safe Compilation with Dynamic Compromise and Mutual
Distrust (RSC^DC_MD)
- `RSC_DC_MD.RSC_DC_MD`

Definition A.1: Z_P class of safety properties preserved by RSC^DC
- `RSC_DC.Z_class` (proof-friendly definition)
  and `RSC_DC.Z_p_equivalent`
  (proof of equivalence between the proof-friendly and the paper definitions)
  in the simple trace model
- `RSC_DC_4_compcert.Z_class` (proof-friendly definition)
  and `RSC_DC_4_compcert.Z_p_equivalent`
  (proof of equivalence between the proof-friendly and the paper definitions)
  in the CompCert trace model

Theorem A.2: RSC^DC characterization via Z_P
- `RSC_DC.main_thm` in the simple trace model
- `RSC_DC_4_compcert.main_thm` in the CompCert trace model

Assumption B.2: Decomposition
- `Intermediate.Decomposition.decomposition_with_safe_behavior`
- `Intermediate.Decomposition.decomposition_with_refinement`

Assumption B.3: Composition
- `Intermediate.Composition.composition_prefix`

Assumption B.4: Definability
- `Source.Definability.definability_with_linking`

Assumption B.5: Compiler Correctness
- `S2I.Compiler.I_simulates_S` and
  `CompCert.Behaviors.forward_simulation_same_safe_behavior`
  for Forward Compiler Correctness
- `S2I.Compiler.S_simulates_I` and
  `CompCert.Behaviors.backward_simulation_behavior_improves`
  for Backward Compiler Correctness

Assumption B.6: Separate Compilation
- `S2I.Compiler.separate_compilation_weaker`

Assumption B.7: Blame
- `Source.PS.PS.blame_program`

### License ###
- This code is licensed under the Apache License, Version 2.0 (see `LICENSE`)
- The code in the `CompCert` dir is adapted based on files in the
  `common` and `lib` dirs of CompCert and is thus dual-licensed under
  the INRIA Non-Commercial License Agreement and the GNU General
  Public License version 2 or later (see `Compcert/LICENSE`)
