# Nanopass Back-Translation of Call-Return Trees for Mechanized Secure Compilation Proofs #

### Prerequisites ###

This development has been built and tested with the following combinations of Coq releases
and versioned libraries:

Coq 8.12.2
- Mathematical Components 1.11.0
- [Extensional Structures dev #d5dafd24990](https://github.com/arthuraa/extructures#d5dafd24990)
- [Deriving dev #c74147d](https://github.com/arthuraa/deriving#c74147d44c46223)
- [CoqUtils master #7d7b930833fd23498d50d67f274747d425d35e4d](https://github.com/arthuraa/coq-utils/commit/7d7b930833fd23498d50d67f274747d425d35e4d)
- QuickChick 8.12.dev

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
- QuickChick can be installed via OPAM

### Replaying the proofs ###

    $ make -j4
    
### Overview ###

Source/DefSimLanguages.v   contains the definition of the intermediate tree languages.
Source/DefSimComp.v        contains the definition of the step of the back-translation.
Source/DefSimSimulations.v contains the simulation theorems and proofs.

Some results are admitted, but we are currently working on making them disappear
in the following weeks.
The admits are mainly of two kinds:
- unicity results: proving the unicity of the locations that appear is a very
  technical task that we didn't complete yet
- well-formedness properties: this includes proofs that all procedures
  are generated, that the code is well-formed, etc. These are quite
  technical tasks that do not pose a major challenge
  
The following theorems are still admitted:
- `give_nums_app_comm`,`wf_trees_unique_key`, `build_event_expression_correct`, `sim4`, `sim5` are lemmas that require 
  proving and/or using unicity conditions. These proofs are tedious and technical, but do not 
  pose a theoretical challenge
- `wf_compile`, `find_proc_callers`, `find_procedure_find`, `find_proc_some`, `find_main`, `initial_buffers` are lemmas that require
  proving  well-formedness lemmas about the program we back-translate
- `sim6` is not proved yet, and heavily use these well-formedness lemmas; the proof should be easy to close
  once these are proved.

### License ###
- This code is licensed under the Apache License, Version 2.0 (see `LICENSE`)
- The code in the `CompCert` dir is adapted based on files in the
  `common` and `lib` dirs of CompCert and is thus dual-licensed under
  the INRIA Non-Commercial License Agreement and the GNU General
  Public License version 2 or later (see `Compcert/LICENSE`)
