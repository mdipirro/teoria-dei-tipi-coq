From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Definition cod (w: nat) : sum unit nat :=
  match w with
  | 0 => inl tt
  | S n => inr (S n)
  end.

Definition dec (z: sum unit nat) : nat :=
  match z with 
  | inl _ => 0
  | inr m => m
  end.

Lemma dec_cod_0_0 : dec (cod 0) = 0.
Proof.
apply: erefl.
Qed.

Lemma dec_cod_Sn_Sn (n: nat): dec (cod (S n)) = S n.
Proof.
apply: erefl.
Qed.