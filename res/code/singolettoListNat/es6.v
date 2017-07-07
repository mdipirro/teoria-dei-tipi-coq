From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Fixpoint add2 (x: nat) (y: nat) : nat :=
  match x with
  | 0 => y
  | (S c) => S (add2 c y)
  end.

Lemma add2_0_y (y: nat) : add2 0 y = y.
Proof.
rewrite //=.
Qed.