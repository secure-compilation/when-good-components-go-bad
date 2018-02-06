## When Good Components Go Bad ##

This repository contains the Coq development of the paper:
- Guglielmo Fachini, Cătălin Hriţcu, Marco Stronati, Arthur Azevedo de Amorim, Ana Nora Evans, Carmine Abate, Roberto Blanco, Théo Laurent, Benjamin C. Pierce, and Andrew Tolmach. **[When Good Components Go Bad: Formally Secure Compilation Despite Dynamic Compromise](https://arxiv.org/abs/1802.00588)**. February 2018.

## Top-level theorems:
- `RSC_DC_MD.v` -- secure compilation for our compiler
- `RSC_DC.v` -- general proofs about the class of properties preserved by RSC_DC

## Prerequisites

This development requires Coq v8.7.1 to work, as well as the following libraries:
- Mathematical Components 1.6.4 (https://math-comp.github.io/math-comp/)
- CoqUtils master branch (https://github.com/arthuraa/coq-utils)

### Replaying the proofs ###

    $ make -j4

### Running the tests ###

Our tests are known to work with QuickChick branch 8.7
(https://github.com/QuickChick/QuickChick) and OCaml from 4.02.3 to 4.06.

Running the tests:

    $ make -j4
    $ ./run_extracted_examples.sh
    $ make test

More thorough mutation tests are on the `nora-testing-experiments` branch.

### License ###
- This code is licensed under the Apache License, Version 2.0 (see `LICENSE`)
- The code in the `CompCert` dir is taken from the `common` and `lib` dirs of CompCert and is thus dual-licensed under the INRIA Non-Commercial License Agreement and the GNU General Public License version 2 or later (see `Compcert/LICENSE`)
