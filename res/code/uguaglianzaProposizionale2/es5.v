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
Axiom UIP : forall (A: Type) (x y: A) (p1 p2: eq A x y), p1 = p2. 

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
apply: (MartinLof.el A (fun x y p => p = g x y (f x y p))).
move=> x0.
by rewrite /f MartinLof.el_refl /g Leibniz.el_refl.
Defined.


Definition pf2 {A} (x y: A) (m: Leibniz.eq A x y) : eq m (f x y (g x y m)).
Proof.
move: (m).
apply: (Leibniz.el A (fun x y => forall m, m = f x y (g x y m)) _ x y m).
move=> z p.
apply: (Leibniz.UIP A z z p (f z z (g z z p))).
Defined.
