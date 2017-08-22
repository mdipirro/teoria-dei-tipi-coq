From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Definition p (n: nat) : nat :=
  match n with
  | 0 => 0
  | S m => m
  end.

Lemma p_0_0 : p 0 = 0.
Proof.
apply: erefl.
Qed.

Lemma p_Sn_n (n: nat) : p (S n) = n.
Proof.
apply: erefl.
Qed.