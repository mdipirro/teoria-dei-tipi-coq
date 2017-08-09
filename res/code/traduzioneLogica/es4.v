From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

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

Definition pf1 {A} {B} (x: A + B): 
  eq x (g (f x)).
Proof.
by case x.
Defined.

Axiom functional_estensionality : forall A B: Type, forall f g : A -> B,
  (forall x : A, f x = g x) -> f = g.

Lemma boole_equality {A} {B} : forall x y: Boole, x = y ->
(prod ((eq x (inrb tt)) -> A) (eq x (inlb tt) -> B)) =
(prod ((eq y (inrb tt)) -> A) (eq y (inlb tt) -> B)).
Proof.
move=> x y exy.
destruct x.
  destruct y.
    by rewrite (eq_inla_inltt a) (eq_inla_inltt a0).
  by rewrite (eq_inla_inltt a) (eq_inra_inrtt b).
by rewrite exy.
Qed.

(* TODO *)
Definition pf2 {A} {B} 
  (y: sigT (fun x: Boole => prod ((eq x (inrb tt)) -> A) (eq x (inlb tt) -> B))) :
  eq y (f (g y)).
Proof.
case: (f (g y)).
  move=> x p.
  destruct y.
  
Defined.
