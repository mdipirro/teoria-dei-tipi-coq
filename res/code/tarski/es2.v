From mathcomp Require Import ssreflect.

Lemma eq_0_1 : unit.
Proof.
apply tt.
Qed.

Lemma neq_0_1 : (unit -> Empty_set) -> Empty_set.
Proof.
move=> x.
apply x.
apply tt.
Qed.