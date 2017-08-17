From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Fixpoint add1 (x: nat) (y: nat) : nat :=
match x with
  | 0 => y
  | S n => S (add1 n y)
end.

Fixpoint add2 (x: nat) (y: nat) : nat :=
match y with
  | 0 => x
  | S n => S (add2 x n)
end.

Lemma add1_x_0 (x: nat) : add1 x 0 = x.
Proof.
by [].
Qed.

Lemma add2_0_y (y: nat) : add2 0 y = y.
Proof.
elim: y.
  by [].
move=> n hp.
by rewrite //= hp.
Qed.

Lemma add1_x_S (x: nat) (n: nat) : add1 x (S n) = S (add1 x n).
Proof.
by [].
Qed.

Lemma add2_S_y (n: nat) (y: nat) : add2 (S n) y = S (add2 n y).
Proof.
elim: y.
  by [].
move=> m hp.
by rewrite //= hp.
Qed.

Lemma add1_comm (x: nat) (y: nat) : add1 x y = add1 y x.
Proof.
elim: x.
  by [].
move=> n hp.
by rewrite //= hp.
Qed.

Lemma pf (x: nat) (y: nat) : (add1 x y) = (add2 x y).
Proof.
elim: x.
  by rewrite add1_comm add1_x_0 add2_0_y.
move=> n hp.
by rewrite add1_comm add1_x_S add2_S_y //= add1_comm hp.
Qed.