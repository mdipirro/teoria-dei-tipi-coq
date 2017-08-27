From mathcomp Require Import ssreflect.

Definition T (a: Prop) := Type.

Definition implicazione (a b : Prop) : Prop := forall x: T a, b.

(* Quantificatore esistenziale *)
Definition esiste {A} (a: Prop) (c: A -> Prop) : Prop := forall p: Prop,
  implicazione (forall x: A, implicazione (c x) p) p.

Lemma esiste_f (A: Type) (G D : Prop) (Ax : A -> Prop) (z: A) (az: Ax z) :
forall h: (forall c: G /\ (Ax z), D), 
  forall c: G /\ (exists x: A, Ax x), D.
Proof.
intros.
apply (h (conj (proj1 c) az)).
Qed.

Lemma esiste_re (A: Type) (G: Prop) (Ax: A -> Prop) (t: A): 
forall h: (forall c: G, Ax t), forall c: G, (exists x: A, Ax x).
Proof.
intros.
exists t.
apply (h c).
Qed.

(* Quantificatore universale *)

Lemma perogni_f (A: Type) (G: Prop) (Ax : A -> Prop) : 
forall h: (forall c: G, forall z: A, Ax z), forall c: G, forall x: A, Ax x.
Proof.
intros.
apply (h c).
Qed.

Lemma perogni_re (A : Type) (G D : Prop) (Ax: A -> Prop) (t: A): 
forall h: (forall c: G /\ (Ax t), D),
  forall c: G /\ (forall x: A, Ax x), D.
Proof.
intros.
apply (h (conj (proj1 c) ((proj2 c) t))).
Qed.