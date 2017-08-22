From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Definition pf1 (x: nat): eq (x + 0) x.
Proof.
rewrite //=.
Defined.

Definition pf2 (x: nat): eq (0 + x) x.
Proof.
rewrite //=.
Defined.