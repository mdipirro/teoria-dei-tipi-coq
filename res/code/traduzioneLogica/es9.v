From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Lemma ex_falso P : False -> P.
Proof.
apply: (fun (abs : False) => match abs with end).
Qed.

Lemma ax1 (x: nat) : ~ ((S x) = 0).
Proof.
by [].
Qed.

Theorem eq_add_S : forall n m:nat, S n = S m -> n = m.
Proof.
  intros n m Sn_eq_Sm.
  replace (n=m) with (pred (S n) = pred (S m)) by auto using pred_Sn.
  rewrite Sn_eq_Sm; trivial.
Qed.

Lemma ax2 (x: nat) (y: nat) : S x = S y -> x = y.
Proof.
move=> hp.
replace (x = y) with (pred (S x) = pred (S y)) by auto using pred_Sn.
by rewrite hp.
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

Lemma ax7 : 
  forall (x: nat) (P: nat -> Prop), P 0 -> (forall y: nat, P (S y)) -> P x.
Proof.
move=> x P P0 hp.
elim: x.
  apply: P0.
move=> n Pn.
apply: hp.
Qed.