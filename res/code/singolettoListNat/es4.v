From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Definition bin (x: nat) (y: nat) :=
  match y with
  | 0 => 0  
  | S c => x
  end.

Lemma bin_x_0 (x: nat) (y: nat) : bin x 0 = 0.
Proof.
case: y.
  rewrite //=.
rewrite //=.
Qed.