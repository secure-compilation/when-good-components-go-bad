
This development requires Coq v8.7.1 to work, as well as the following libraries:
- Mathematical Components 1.6.4 (https://math-comp.github.io/math-comp/)
- CoqUtils (https://github.com/arthuraa/coq-utils)
These dependencies are also provided for convenience in `Dependencies`

Top-level theorems:
- `RSC_DC_MD.v` -- secure compilation for our compiler
- `RSC_DC.v` -- general proofs about the properties preserved by RSC_DC

Replaying the proofs:

    $ make -j4

Our tests are known to work with QuickChick branch 8.7
(https://github.com/QuickChick/QuickChick) and OCaml from 4.02.3 to 4.06.

Running the tests:

    $ make -j4
    $ ./run_extracted_examples.sh
    $ make test
