From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Definition iduni {A} (a: A) (p: a = a): p = (erefl a).
Proof.
Admitted.

Lemma C_Iduni {A} (a: A): (iduni a (erefl a)) = (erefl (erefl a)).
Proof.
Admitted.

Definition pf {A} (a: A) (b: A):
  forall w1: a = b, 
    (forall w2: a = b, (w1 = w2)).
Proof.
move=> w1 w2.
destruct w1.
by destruct (iduni a w2).
Defined.