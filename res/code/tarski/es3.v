From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

(*Lemma not_eq_0_1 : ~ (0 = 1).
Proof.
by [].
Qed.*)

Definition f (x: nat) : Set :=
match x with
  | 0 => Empty_set
  | S _ => unit
end.

Lemma not_eq_0_1 (x: Set) (y: Set) (w: eq x y) : (eq 0 1) -> Empty_set.
Proof.
move=> hp.
Qed.