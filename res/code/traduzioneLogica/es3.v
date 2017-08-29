From mathcomp Require Import ssreflect.

Inductive Boole :=
Inductive Boole :=
  | inlb (a: unit)
  | inrb (b: unit).

Definition dis (z: eq (inlb tt) (inrb tt)) : unit.
Proof.
Admitted.

Definition f {A} {B} (z: A + B) :
  sigT (fun x: Boole => prod ((eq x (inrb tt)) -> A) (eq x (inlb tt) -> B)).
Proof.
case z.
  move=> a.
  exists (inrb tt).
  rewrite //=.
move=> b.
  exists (inlb tt).
  rewrite //=.
Defined.

Lemma eq_inla_inltt (a: unit) : eq (inlb a) (inlb tt).
Proof.
by case a.
Qed.

Lemma eq_inra_inrtt (a: unit) : eq (inrb a) (inrb tt).
Proof.
by case a.
Qed.

Definition g {A} {B} 
  (w: sigT (fun x: Boole => prod ((eq x (inrb tt)) -> A) (eq x (inlb tt) -> B))) :
  A + B.
Proof.
destruct w.
destruct p.
destruct x.
apply (inr (b (eq_inla_inltt a0))).
apply (inl (a (eq_inra_inrtt b0))).
Defined.