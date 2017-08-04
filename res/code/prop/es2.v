From mathcomp Require Import ssreflect.

Definition T (a: Prop) := Type.

Definition perogni {A} (c: A -> Prop) : Prop := forall x: A, c x.

Definition implicazione (a b : Prop) : Prop := forall x: T a, b.

Definition esiste {A} (a b: Prop) (c: A -> Prop) : Prop := forall p: Prop,
  implicazione (forall x: A, implicazione (c x) p) p.



