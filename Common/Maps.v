From CoqUtils Require Export ord fmap fset.
From mathcomp Require Export ssrbool.

Definition NMap T := {fmap nat -> T}.

Definition elementsm {A: Type} : NMap A -> list (nat * A) := @FMap.fmval nat_ordType A _.
