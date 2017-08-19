From mathcomp Require Import ssreflect.

Definition eq_0_1 : unit.
Proof.
apply tt.
Defined.

Definition neq_0_1 : (unit -> Empty_set) -> Empty_set.
Proof.
move=> x.
apply x.
apply tt.
Defined.