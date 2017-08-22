From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Fixpoint add1 (x: nat) (y: nat) : nat :=
  match y with
  | 0 => x
  | (S c) => S (add1 x c)
  end.

Fixpoint molt (x: nat) (y: nat) : nat :=
  match y with
  | 0 => 0
  | (S c) => add1 x (molt x c)
  end.

Lemma molt_x_0 (x: nat) : molt x 0 = 0.
Proof.
rewrite //=.
Qed.