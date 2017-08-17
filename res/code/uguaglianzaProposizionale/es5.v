From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Definition pf (x: unit) : eq x tt.
Proof.
case: x.
apply: erefl.
Defined.