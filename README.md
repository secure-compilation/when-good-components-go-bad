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

This development has been built and tested under Coq 8.12.2, using Mathematical Components 1.11.0,
Extensional Structures 0.3.0 and Coq Utils commit #81eaf5b6c2ed5.

We recommend the installation via the OCaml package manager, OPAM:
- Create a new switch for this development: `opam switch create wgcgb ocaml-base-compiler.4.10.2`
  (don't forget to run `eval $(opam env)` as instructed by the command).
- Add the Coq OPAM repositories: `opam repo add coq-released https://coq.inria.fr/opam/released/` then
  `opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev`.
- Pin Coq to 8.12.2: `opam pin add coq 8.12.2`.
- Pin the Mathematical Components library to 1.11.0:
  `opam pin add coq-mathcomp-ssreflect 1.11.0` then `opam install coq-mathcomp-fingroup coq-mathcomp-algebra`.
- Pin the Extensional Structures to 0.3.0: `opam pin add coq-extructures 0.3.0`. This should install `coq-deriving` version
  0.1.1 automatically (as a dependency). Otherwise, pin `coq-deriving` to 0.1.1: `opam pin add coq-deriving 0.1.1`.
- With that, you have everything required to build the Coq Utils version we are using:
  first, pin it to the commit 81eaf5b6c2ed5:
  `opam pin add -e coq-utils git@github.com:arthuraa/coq-utils.git#81eaf5b6c2ed5`. Then, remove the two lines 
  for the dependency on `coq-extructures` and `coq-deriving`. Then add at the end `version: "81eaf5b6c2ed5"`.

### Replaying the proofs ###

    $ make -j4

### Running the tests ###

In order to run our tests, the following additional dependencies are needed:

Coq 8.12.0
- QuickChick 1.4.0

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
