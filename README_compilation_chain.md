# Secure Compilation to the Micro-Policy Backend

This directory contains the full compilation chain from the source language to the micro-policy machine, and proves RSC_DC_MD between the source semantics and the low-level semantics of the micro-policy machine.

The proof is predicated on a few conditions on the source executions appearing in the proof, namely that they don't overflow the concrete low-level limits of the micro-policy machine.

Bridging the gap between infinite and finite memory model is still an active research problem; to get a full end-to-end theorem, we suggest replacing unbounded arithmetic in the source with bounded arithmetic.

The main theorem is `RSC_DC_MD_CompilationChainMP` in file `RSC_DC_MD_CompilationChainMP.v`:
``` coq
  Theorem RSC_DC_MD_CompilationChainMP :
    exists Cs beh,
      Source.prog_interface Cs = prog_interface In.c /\
      Source.well_formed_program Cs /\
      linkable (Source.prog_interface In.p) (Source.prog_interface Cs) /\
      Source.closed_program (Source.program_link In.p Cs) /\
      program_behaves (S.CS.sem (Source.program_link In.p Cs)) beh /\
      (CompCertExtensions.prefix In.fm beh
       \/ behavior_improves_blame_mp beh In.fm In.p).
```
