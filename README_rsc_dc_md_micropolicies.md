# Blame-Aware Recomposition for the Micro-Policy Backend

This directory contains the instantiation of our proof technique to the micro-policy backend, as described in Sections 3 and 4 of the paper.

More precisely, this directory proves RSC_DC_MD between the overlay semantics and the low-level semantics of our micro-policy machine.

The main theorem is `RSC_DC_MD_MicroPolicies` in file `RSC_DC_MD_MicroPolicies.v`:
``` coq
  Theorem RSC_DC_MD_MicroPolicies :
    does_prefix M.Trec.sem'' In.fm
    \/ (exists m',
          does_prefix M.Trec.sem'' (FGoes_wrong m')
          /\ trace_finpref_prefix m' In.fm
          /\ undef_in m' (prog_interface In.p)).
```

Module type `MicroPoliciesInput` contains the inputs of our proof: 
- Partial programs `P` and `P'` and contexts `C` and `C'`, as well as well-formedness conditions on them. The well-formedness conditions are conditions that can be statically checked of micro-policy programs: they implement the interfaces, they contain the correct entry points, their code has been correctly tagged, they fit within the bounds of the machine, etc. This is given by predicate `wf_mp`.
- Then, there are several conditions on the number of compartments and on the size of the code, to ensure all programs and their recomposition fit properly in the machine.
- Then comes the finite trace being produced, as well as a condition of it being short enough to be back-translatable (long enough traces cannot be back-translated).

The theorem only depends on these inputs, as shown by `Print Assumptions`. In particular, we have a back-translation from traces to micro-policy machine programs that runs in the overlay semantics, so that we can run the proof of Section 2.

The development is organized as follows:
- `MicroPolicies/`: contains the definitions of the low-level micro-policy machine (`LRC.v`) and the overlay semantics (`Merged.v`) 
- `MicroPolicies/Recomposition/`: contains blame-aware recomposition (Section 4.2). The recomposition diagrams are proved in `RecompositionInit.v`, `StepSilentStrong{1,2}.v`, `StepSilentWeak{1,2}.v`, `StepEventCall.v` and `StepEventReturn.v`; `RecompositionTop.v` proves `recomposition_blame` from these diagrams.
- `BackTranslationMeMP/`: contains the back-translation of a trace into a micro-policy program.
- `MicroPolicies/Recomposition/RSC_ME_MP_Faithful.v`: puts recomposition and
  back-translation together.
