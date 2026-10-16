# Blame-aware Recomposition for Secure Compilation Proofs of Low-Level Compartment Isolation

This is the artifact for the CSF Fall submission.

### Prerequisites ###

This development was tested with:

- Rocq 9.1.1 (`rocq-core`, `rocq-stdlib` 9.0.0), with OCaml 5.4.1
- Mathematical Components 2.5.0 (`rocq-mathcomp-ssreflect`,
  `rocq-mathcomp-fingroup`, `rocq-mathcomp-algebra`)
- Hierarchy Builder 1.10.2 (`rocq-hierarchy-builder`)
- MathComp Zify 1.6.0 (`coq-mathcomp-zify`)
- Deriving 0.2.3 (`coq-deriving`)
- [Extensional Structures](https://github.com/arthuraa/extructures) 0.6.0
- Coq Utils: [arthuraa/coq-utils@b54d78a](https://github.com/arthuraa/coq-utils/tree/b54d78a) (branch `coq-9.0`) is required, but a local copy is included in this artifact

We recommend using OPAM and creating a new switch:

    $ opam switch create rsc-dc-md ocaml-base-compiler.5.4.1
    $ opam switch rsc-dc-md
    $ eval $(opam env)
    $ opam repo add rocq-released https://rocq-prover.github.io/opam/released
    $ opam install rocq-core.9.1.1 rocq-stdlib.9.0.0 \
        rocq-mathcomp-ssreflect.2.5.0 rocq-mathcomp-fingroup.2.5.0 \
        rocq-mathcomp-algebra.2.5.0 rocq-hierarchy-builder.1.10.2 \
        coq-mathcomp-zify.1.6.0+2.3+8.18 coq-deriving.0.2.3

Then pin Extensional Structures to its 0.6.0 release:

    $ opam pin add extructures git+https://github.com/arthuraa/extructures.git#v0.6.0

Our artifact includes a local copy of `coq-utils` updated for the current version of Rocq, so you do not need to install it.

### Replaying the proofs ###

    $ make -j4
    
Building everything can take up to 30 minutes.

### Structure of the artifact ###

The artifact is divided into several directories. The main three directories, `rsc_dc_md`, `rsc_dc_md_micropolicies`, and `compilation_chain`, each have their own `README.md` file.

- `coq-utils` is a local updated copy of `coq-utils`
- `common` contains various dependencies of the rest of the development
- `rsc_dc_md` contains a generic proof that blame-aware recomposition can be used to replace recomposition and implies the security theorem
- `rsc_dc_md_micropolicies` contains the updated micro-policy backend, as well as the proof of blame-aware recomposition and the proof of `RSC_DC_MD` between the overlay semantics and the low-level semantics.
- `compilation_chain` contains the entire compilation chain from source to micro-policy machine, the proof of blame-aware recomposition, and the proof of `RSC_DC_MD` between the source and the low-level semantics, with an explicit assumption that the runs used in the proof fit in the low-level machine limits.
