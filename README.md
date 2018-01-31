
This development requires Coq v8.7.1 to work, as well as the following libraries:
- Mathematical Components 1.6.4 (https://math-comp.github.io/math-comp/)
- CoqUtils (https://github.com/arthuraa/coq-utils)

Our tests also use QuickChick branch 8.7 (https://github.com/QuickChick/QuickChick)

Top-level theorems:
- `RSC_DC_MD.v` -- secure compilation for our compiler
- `RSC_DC.v` -- general proofs about the properties preserved by RSC_DC

Replaying the proofs:

    $ make -j4

Running the tests for SFI:

    $ make test
