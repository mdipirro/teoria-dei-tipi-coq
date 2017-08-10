From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Lemma ex_falso P : False -> P.
Proof.
apply: (fun (abs : False) => match abs with end).
Qed.

Lemma ax1 : forall n: nat, 0 <> S n.
Proof.
by [].
Qed.

Theorem ax2 : forall n m: nat, S n = S m -> n = m.
Proof.
move=> n m Sn_eq_Sm.
replace (n=m) with (pred (S n) = pred (S m)) by auto using pred_Sn.
by rewrite Sn_eq_Sm.
Qed.

Lemma ax3 : forall n: nat, n + 0 = n.
Proof.
by [].
Qed.

Lemma ax4 : forall n m: nat, n + (S m) = S (n + m).
Proof.
by [].
Qed.

Lemma ax5 : forall n: nat, n * 0 = 0.
Proof.
by [].
Qed.

Lemma ax6 : forall n m: nat, n * (S m) = n * m + n.
Proof.
by [].
Qed.

Lemma ax7 : 
  forall (n: nat) (P: nat -> Prop), P 0 -> (forall m: nat, P (S m)) -> P n.
Proof.
move=> x P P0 hp.
elim: x.
  apply: P0.
move=> n Pn.
apply: hp.
Qed.