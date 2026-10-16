# Generic Blame-Aware Recomposition Proof Technique

This directory contains the generic proof that blame-aware recomposition implies RSC_DC_MD, as described in Section 2 of the paper.

The main theorem is `RSC_DC_MD` in file `RSC_DC_MD_Target.v`:
``` coq
  Theorem RSC_DC_MD:
    forall m,
      does_prefix (CS.sem2 (program_link p Ct)) m ->
      not_wrong_finpref m ->
    exists Cs beh,
      prog_interface Cs = prog_interface Ct /\
      well_formed_program Cs /\
      linkable (prog_interface p) (prog_interface Cs) /\
      closed_program (program_link p Cs) /\
      program_behaves (CS.sem1 (program_link p Cs)) beh /\
      (prefix m beh \/ behavior_improves_blame beh m p).

```
and is a one-to-one match with the definition from the paper.

The proof follows that of the paper.

The theorem depends on the following hypotheses, appearing in the module type `Target_Sig`:
- `sem1` is the overlay semantics
- `sem2` is the low-level semantics
- `sem_restricted_UB` is our definition of the UB-restricting semantics

- `recomposition_blame_prefix` and its variant `recomposition_blame_prefix_final_UB` is the statement of blame-aware recomposition
- `definability_with_linking` is back-translation

There is a number of additional axioms in `Target_Sig`. These axioms state standard properties that should hold of the semantics we consider.
