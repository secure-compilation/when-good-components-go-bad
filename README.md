### Prerequisites ###

This development was tested with:

- Rocq 9.1.1 (`rocq-core`, `rocq-stdlib` 9.0.0), with OCaml 5.4.1
- Mathematical Components 2.5.0 (`rocq-mathcomp-ssreflect`,
  `rocq-mathcomp-fingroup`, `rocq-mathcomp-algebra`)
- Hierarchy Builder 1.10.2 (`rocq-hierarchy-builder`)
- MathComp Zify 1.6.0 (`coq-mathcomp-zify`)
- Deriving 0.2.3 (`coq-deriving`)
- [Extensional Structures](https://github.com/arthuraa/extructures) 0.6.0
- Coq Utils:
  [arthuraa/coq-utils@b54d78a](https://github.com/arthuraa/coq-utils/tree/b54d78a)
  (branch `coq-9.0`)

We recommend using OPAM and create a new switch:

    $ opam switch create rsc-dc-md ocaml-base-compiler.5.4.1
    $ opam switch rsc-dc-md
    $ eval $(opam env)
    $ opam repo add rocq-released https://rocq-prover.org/opam/released
    $ opam install rocq-core.9.1.1 rocq-stdlib rocq-mathcomp-ssreflect \
        rocq-mathcomp-fingroup rocq-mathcomp-algebra rocq-hierarchy-builder \
        coq-mathcomp-zify coq-deriving

Then pin Extensional Structures to its 0.6.0 release:

    $ opam pin add extructures git+https://github.com/arthuraa/extructures.git#v0.6.0

Then build and install Coq Utils from source:

    $ git clone -b coq-9.0 https://github.com/arthuraa/coq-utils.git
    $ cd coq-utils && git checkout b54d78a && make && make install
    
### Replaying the proofs ###

    $ make -j
