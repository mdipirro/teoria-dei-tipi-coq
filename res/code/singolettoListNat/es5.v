From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Fixpoint add1 (x: nat) (y: nat) : nat :=
  match y with
  | 0 => x
  | (S c) => S (add1 x c)
  end.

Lemma add1_x_0 (x: nat) : add1 x 0 = x.
Proof.
rewrite //=.
Qed.