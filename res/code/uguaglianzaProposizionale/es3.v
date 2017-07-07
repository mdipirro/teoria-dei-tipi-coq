From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

(* Sia P y = Id(A, y, y) = eq y y*)
Definition pf {A} {P} (x: A) (y: A) (z: P x) (w: eq x y) : eq y y.
Proof.
rewrite //=.
Defined.

Definition pf2 {A} (x: A) (y: A) (z: A) (w1: eq x y) (w2: eq y z) : eq x z.
Proof.
rewrite w1 w2.
apply: erefl.
Defined.