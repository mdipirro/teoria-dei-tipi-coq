From mathcomp Require Import ssreflect.

Inductive MartinLof (A: Type) : A -> A -> Type :=
| ml_refl x : MartinLof A x x.

Definition iduni {A} (a: A) (p: MartinLof A a a): 
MartinLof _ p (ml_refl A a).
Proof.
Admitted.

Lemma C_Iduni {A} (a: A): 
MartinLof _ (iduni a (ml_refl A a)) (ml_refl (MartinLof A a a) (ml_refl A a)).
Proof.
Admitted.

Definition pf1 {A} (a: A) (b: A):
  forall w1: MartinLof A a b, 
    (forall w2: MartinLof A a b, MartinLof (MartinLof A a b) w1 w2).
Proof.
intros.
destruct w1.
by destruct (iduni x w2).
Defined.