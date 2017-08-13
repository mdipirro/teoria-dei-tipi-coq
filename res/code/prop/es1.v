From mathcomp Require Import ssreflect.

Definition T (a: Prop) := Type.

(* Implicazione *)

Definition implicazione (a b : Prop) : Prop := forall x: T a, b.

Lemma implicazione_f (G A B : Prop) : 
forall h: (forall c: G /\ A, B), forall c: G, A -> B.
Proof.
intros.
apply (h (conj c H)).
Qed.

Lemma implicazione_re (G G' A B D : Prop) : 
forall h: ((forall c1: G, A) /\ (forall c2: B /\ G', D)),
  forall c: G /\ (forall x: A, B) /\ G', D.
Proof.
intros.
destruct h.
destruct c.
destruct H2.
apply (H0 (conj (H2 (H H1)) H3)).
Qed.

(* Congiunzione *)
Definition congiunzione (a b: Prop) : Prop := forall p: Prop, 
  implicazione (forall x: T a, forall y: T b, p) p.

Lemma congiunzione_f (G A B : Prop) : 
forall h: ((forall h1: G, A) /\ (forall h2: G, B)),
  forall c: G, A /\ B.
Proof.
intros.
destruct h.
apply (conj (H c) (H0 c)).
Qed.

Lemma congiunzione_re1 (G A B D : Prop): forall h: (forall c: G /\ A, D),
  forall c: G /\ (A /\ B), D.
Proof.
intros.
apply (h (conj (proj1 c) ((proj1 (proj2 c))))).
Qed.

Lemma congiunzione_re2 (G A B D : Prop): forall h: (forall c: G /\ B, D),
  forall c: G /\ (A /\ B), D.
Proof.
intros.
apply (h (conj (proj1 c) ((proj2 (proj2 c))))).
Qed.

(* Disgiunzione *)
Definition disgiunzione (a b: Prop) : Prop := forall p: Prop,
  implicazione (congiunzione (a -> p) (b -> p)) p.

Lemma disgiunzione_f (G A B D : Prop) : 
forall h: ((forall c1: G /\ A, D) /\ (forall c2: G /\ B, D)),
  forall c: G /\ (A \/ B), D.
Proof.
intros.
destruct h.
destruct c.
destruct H2.
  apply (H (conj H1 H2)).
apply (H0 (conj H1 H2)).
Qed.

Lemma disgiunzione_re1 (G A B : Prop) : forall h: (forall c: G, A),
  forall c: G, A \/ B.
Proof.
intros.
apply (or_introl (h c)).
Qed.

Lemma disgiunzione_re2 (G A B : Prop) : forall h: (forall c: G, B),
  forall c: G, A \/ B.
Proof.
intros.
apply (or_intror (h c)).
Qed.