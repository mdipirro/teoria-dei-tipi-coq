From mathcomp Require Import ssreflect.

Definition T (a: Prop) := Type.

Definition implicazione (a b : Prop) : Prop := forall x: T a, b.

(* Quantificatore esistenziale *)
Definition esiste {A} (a: Prop) (c: A -> Prop) : Prop := forall p: Prop,
  implicazione (forall x: A, implicazione (c x) p) p.

Definition esiste_el {A} : forall g a: Prop, forall C: A -> Prop,
(implicazione g (esiste a C)) -> Prop.
Proof.
move=> g a C hp.
apply a.
Defined.

(* Quantificatore universale *)
(* Definito come primitivo in Coq*)