From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

(* Sia P y = Id(A, y, y) = eq y y*)
Definition pf {A} {P} (x: A) (y: A) (z: P x) (w: eq x y) : eq y y.
Proof.
rewrite //=.
Defined.