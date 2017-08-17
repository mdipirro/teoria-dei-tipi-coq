From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Lemma ax1 (x: nat) : ~ ((S x) = 0).
Proof.
by [].
Qed.

Lemma ax3 (x: nat) : x + 0 = x.
Proof.
by [].
Qed.

Lemma ax4 (x: nat) (y: nat) : x + (S y) = S (x + y).
Proof.
by [].
Qed.

Lemma ax5 (x: nat) : x * 0 = 0.
Proof.
by [].
Qed.

Lemma ax6 (x: nat) (y: nat) : x * (S y) = x * y + x.
Proof.
by [].
Qed.