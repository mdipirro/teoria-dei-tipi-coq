From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Definition pf {A} (x: A) (y: A) (z: A) (w1: eq x y) (w2: eq y z) : eq x z.
Proof.
rewrite w1 w2.
apply: erefl.
Defined.