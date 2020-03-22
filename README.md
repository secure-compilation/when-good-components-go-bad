# When Good Components Go Bad #

This repository contains the Coq development of the paper:
- Carmine Abate, Arthur Azevedo de Amorim, Roberto Blanco, Ana Nora Evans,
  Guglielmo Fachini, Catalin Hritcu, Théo Laurent, Benjamin C. Pierce,
  Marco Stronati, Andrew Tolmach.
  **[When Good Components Go Bad: Formally Secure Compilation Despite
     Dynamic Compromise](https://arxiv.org/abs/1802.00588)**.
     In 25th ACM Conference on Computer and Communications Security
     (CCS 2018), October 2018.

### Prerequisites ###

This development has been built with the following combinations of Coq releases
and versioned libraries:

Coq 8.7.2
- Mathematical Components 1.6.4
- Extensional Structures 0.1.0
- [Coq Utils 0.1](https://github.com/arthuraa/coq-utils/releases/tag/v0.1)

Coq 8.8.2
- Mathematical Components 1.7.0
- Extensional Structures 0.1.0
- Coq Utils 0.1

Coq 8.9.1
- Mathematical Components 1.9.0
- Extensional Structures 0.2.0
- [Coq Utils 6334def](https://github.com/arthuraa/coq-utils/tree/6334def1a259a3ce4285cc020f641298fc0c7420)

Coq 8.10.2
- Mathematical Components 1.9.0
- Extensional Structures dev (source hash
  [adc14db3](https://github.com/arthuraa/extructures/tree/adc14db3757e373b73c2af0509c72871b6d0d57f))
- Coq Void 0.1.0
- Deriving dev (source hash
  [db78af07](https://github.com/arthuraa/deriving/tree/db78af0799aede75edb47c72114e91e5ef11f77b))
- [Coq Utils 504aa42](https://github.com/arthuraa/coq-utils/tree/504aa4285d631b166ae36e0f40a3a8f77cbde224)

Most dependencies can be installed through the OCaml package manager, OPAM.

- Coq (package `coq`) is available through the official
  [Ocaml OPAM repository](http://opam.ocaml.org/).
- Stable releases of Mathematical Components (packages `coq-mathcomp-ssreflect`,
  `coq-mathcomp-fingroup` and `coq-mathcomp-algebra`), Extensional Structures
  (package `coq-extructures`) and Coq Void (package `coq-void`) are available
  through the
  [Coq OPAM repository](https://coq.inria.fr/opam/released/).
- Development versions of Extensional Structures (package `coq-extructures`) and
  Deriving (package `coq-deriving`) are available through the
  [Coq OPAM development repository](https://coq.inria.fr/opam/extra-dev/).
- Coq Utils needs to be built from source and, if necessary, its route added to
  the `_CoqProject` project description file.

### Replaying the proofs ###

    $ make -j4

### Running the tests ###

In order to run our tests, the following additional dependencies are needed:

Coq 8.7.2
- QuickChick 1.0.0

Stable releases of QuickChick (package `coq-quickchick`) are available through
the Coq OPAM repository.

Running the tests (to be simplified):

    $ make clean
    $ make -j4
    $ ./run_extracted_examples.sh --force-extraction
    $ rm sfi_safety_properties.exe
    $ ./run_sfi_tests.sh

More thorough mutation tests are on the `nora-testing-experiments` branch.

### Top-level theorems ###

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

### License ###
- This code is licensed under the Apache License, Version 2.0 (see `LICENSE`)
- The code in the `CompCert` dir is adapted based on files in the
  `common` and `lib` dirs of CompCert and is thus dual-licensed under
  the INRIA Non-Commercial License Agreement and the GNU General
  Public License version 2 or later (see `Compcert/LICENSE`)
