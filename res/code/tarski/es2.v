From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Lemma eq_0_1 : unit.
Proof.
apply tt.
Qed.

Lemma not_eq_0_1 : (unit -> Empty_set).
Proof.
move=> s.
Qed.
