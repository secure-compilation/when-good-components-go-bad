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

This development requires Coq v8.9.1 to work, as well as the following libraries:
- [Mathematical Components](https://math-comp.github.io/math-comp/) 1.9.0 or dev / on branch master
- [CoqUtils](https://github.com/arthuraa/coq-utils) on branch master (tested with commit [54c1269](https://github.com/arthuraa/coq-utils/commit/54c1269e1e85e14404e9dab3805e9db448f419f0)),
- [Coq Void](https://github.com/arthuraa/coq-void) v0.1.0 or dev / on branch master
  (tested with commit
  [4a88dcd](https://github.com/arthuraa/coq-void/commit/4a88dcd55421c356e8930a4a62de1682d1bb3fa4)),
- [Deriving](https://github.com/arthuraa/deriving) dev / on branch master
  (tested with commit
  [82ed345](https://github.com/arthuraa/deriving/commit/82ed3450039f51ce36833cc447be24c39dc9ef65)),
- [Extensional Structures](https://github.com/arthuraa/extructures) on
  branch master (tested with commit
  [c2d88c2](https://github.com/arthuraa/extructures/commit/c2d88c2bad3b02f78ca25c41b4cb59251ae4f702)),
- [QuickChick](https://github.com/QuickChick/QuickChick) v1.1.0 or 8.9.dev for the testing (see below).

For convenience, you can install all the dependencies on opam (with
the repo coq-released and coq-extra-dev) with

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
$ opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev

# if you didn't clone with --recurse-submodules
$ git submodule init
$ git submodule update

$ opam pin add coq-utils ./coq-utils
$ opam install coq-quickchick
```

Note that this will activate the development repositories for many coq projects. You may
want to pin some packages to a specific version with `opam pin
<coq-package> <version>`

### Replaying the proofs ###

    $ make -j4

### Running the tests ###

Our tests are known to work with [QuickChick](https://github.com/QuickChick/QuickChick) branch 8.9 and
OCaml from 4.02.3 to 4.06.

Running the tests (to be simplified):

    $ make -f Makefile.Test clean
    $ make -f Makefile.Test -j4
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
