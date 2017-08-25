From mathcomp Require Import ssreflect.

Definition f (A B: Prop) (s: sumbool A B) : sum A B.
Proof.
destruct s.
  apply (inl a).
apply (inr b).
Defined.

Definition g (A B: Prop) (s: sum A B) : sumbool A B.
Proof.
destruct s.
  apply (left a).
apply (right b).
Defined.

Arguments f {_ _} _.
Arguments g {_ _} _.

Definition pf1 (A B: Prop) (s: sumbool A B) : g (f s) = s.
Proof.
by destruct s.
Defined.

Definition pf2 (A B: Prop) (s: sum A B) : (f (g s)) = s.
Proof.
by destruct s.
Defined.