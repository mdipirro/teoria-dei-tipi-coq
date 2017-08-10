From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Lemma a_equal_b {A} (a b: A) : a = b.
Proof.
Admitted.

Definition pf {A} (a b: A) : eq a b.
Proof.
apply a_equal_b.
Defined. 