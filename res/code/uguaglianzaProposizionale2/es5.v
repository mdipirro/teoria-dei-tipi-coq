From mathcomp Require Import ssreflect.

Module Leibniz.

Axiom eq : forall A, A -> A -> Prop.
Axiom refl : forall A, forall x : A, eq A x x.
Axiom el : forall (A : Type) (C : A -> A -> Type),
  (forall x : A, C x x) ->
    forall a b : A, forall p : eq A a b, C a b.
Axiom el_refl : forall (A : Type) (C : A -> A -> Type)
    (CR : forall x : A, C x x),
    forall x : A, el A C CR x x (refl A x) = CR x.

End Leibniz.

Module MartinLof.

Axiom eq : forall A, A -> A -> Prop.
Axiom refl : forall A, forall x : A, eq A x x.
Axiom el : forall (A : Type) (C : forall x y : A, eq A x y -> Prop),
  (forall x : A, C x x (refl A x)) ->
    forall a b : A, forall p : eq A a b, C a b p.
Axiom el_refl : forall (A : Type) (C : forall x y : A, eq A x y -> Prop)
    (CR : forall x : A, C x x (refl A x)),
    forall x : A, el A C CR x x (refl A x) = CR x.

End MartinLof.

Definition f {A} (x y: A) (m: MartinLof.eq A x y) : Leibniz.eq A x y.
Proof.
apply: (MartinLof.el A (fun a b p => Leibniz.eq A a b) _ x y m) => x0.
exact: Leibniz.refl A x0.
Defined.

Definition g {A} (x y: A) (p: Leibniz.eq A x y) : MartinLof.eq A x y.
Proof.
apply: (Leibniz.el A (fun a b => MartinLof.eq A a b) _ x y).
move=> x0.
exact: MartinLof.refl A x0.
apply p.
Defined.

(* Equivalenza *)
Lemma equiv_ml_l : forall A x y, MartinLof.eq A x y <-> Leibniz.eq A x y.
Proof.
move=> A x y.
split.
  move=> m.
  apply (f x y m).
move=> l.
apply (g x y l).
Qed.

Definition pf1 {A} (x y: A) (m: MartinLof.eq A x y) : eq m (g x y (f x y m)).
Proof.
apply: (MartinLof.el A (fun x y p => p = g x y (f x y p))) => x0.
by rewrite /f MartinLof.el_refl /g Leibniz.el_refl.
Qed.


Definition pf2 {A} (x y: A) (m: Leibniz.eq A x y) : eq m (f x y (g x y m)).
Proof.
Check (Leibniz.el A (fun x y => p = f x y (g x y p))).
apply: (Leibniz.el A (fun a b => m = f x y (g x y m))).
move=> x0.
rewrite /g Leibniz.el_refl.
Qed.

(*

Inductive MartinLof (A: Type) : A -> A -> Prop :=
| ml_refl x : MartinLof A x x.

Inductive Leibniz (A: Type) : A -> A -> Prop :=
| l_refl x : Leibniz A x x.

Definition f {A} {x y: A} (l: Leibniz A x y) : MartinLof A x y :=
  match l with l_refl a => ml_refl A a end.

Definition g {A} {x y : A} (m: MartinLof A x y) : Leibniz A x y :=
  match m with ml_refl z => l_refl A z end.

Lemma equiv_ml_l : forall A x y, MartinLof A x y <-> Leibniz A x y.
Proof.
move=> A x y.
split.
  move=> m.
  apply (g m).
move=> l.
apply (f l).
Qed.

Definition pf1 {A} (x y : A) (l: Leibniz A x y) : g (f l) = l :=
  match l with l_refl _ => eq_refl end.

Definition pf2 {A} (x y : A) (m: MartinLof A x y) : f (g m) = m :=
  match m with ml_refl _ => eq_refl end.
*)