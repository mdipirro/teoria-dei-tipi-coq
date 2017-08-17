From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Definition q {A} {B} (x: A) (y: A) (f: A -> B) (w: eq x y) : eq (f x) (f y).
Proof.
rewrite w.
apply: erefl.
Defined.