From mathcomp Require Import ssreflect.

Inductive MartinLof (A: Type) : A -> A -> Prop :=
| ml_refl x : MartinLof A x x.

Inductive Leibniz (A: Type) : A -> A -> Prop :=
| l_refl x : Leibniz A x x.

Definition f {A} {x y: A} (l: Leibniz A x y) : MartinLof A x y :=
  match l with l_refl a => ml_refl A a end.

Definition g {A} {x y : A} (m: MartinLof A x y) : Leibniz A x y :=
  match m with ml_refl z => l_refl A z end.

(* Equivalenza *)
Lemma equiv_ml_l : forall A x y, MartinLof A x y <-> Leibniz A x y.
Proof.
move=> A x y.
split.
  move=> m.
  apply (g m).
move=> l.
apply (f l).
Qed.

(* Isomorfismo *)
Definition pf1 {A} (x y : A) (l: Leibniz A x y) : g (f l) = l :=
  match l with l_refl _ => eq_refl end.

Definition pf2 {A} (x y : A) (m: MartinLof A x y) : f (g m) = m :=
  match m with ml_refl _ => eq_refl end.