From CoqUtils Require Export ord fmap fset.
From mathcomp Require Export ssrbool.

Definition NMap := FMap.fmap_type nat_ordType.

Definition elementsm {A: Type} : @NMap A -> list (nat * A) := @FMap.fmval nat_ordType A.
