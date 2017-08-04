From mathcomp Require Import ssreflect.

Module Leibniz.

Axiom eq : forall A, A -> A -> Prop.
Axiom refl : forall A, forall x : A, eq A x x.
Axiom el : forall (A : Type) (C : A -> A -> Prop),
  (forall x : A, C x x) ->
    forall a b : A, forall p : eq A a b, C a b.
Axiom el_refl : forall (A : Type) (C : A -> A -> Prop)
    (CR : forall x : A, C x x),
    forall x : A, el A C CR x x (refl A x) = CR x.

End Leibniz.

Module Gentzen.

Axiom eq : forall A, A -> A -> Prop.
Axiom refl : forall A, forall x : A, eq A x x.
Axiom el : forall (A : Type) (a: A) (C : A -> A -> Prop),
  C a a -> forall b : A, forall p : eq A a b, C a b.
Axiom el_refl : forall (A : Type) (a: A) (C : A -> A -> Prop)
    (CR : C a a), el A a C CR a (refl A a) = CR.

End Gentzen.

Definition f {A} (x y: A) (l: Leibniz.eq A x y) : Gentzen.eq A x y.
Proof.
apply: (Leibniz.el A (fun a b => Gentzen.eq A a b) _ x y).
move=> x0.
exact: Gentzen.refl A x0.
apply l.
Defined.

Definition g {A} (x y: A) (g: Gentzen.eq A x y) : Leibniz.eq A x y.
Proof.
Check (Gentzen.el A x (fun a b => Leibniz.eq A x a) _ y g).
apply: (Gentzen.el A x (fun a p => Leibniz.eq A x a) _ y g).
move=> x0.
exact: Leibniz.refl A x0.
apply l.
Defined.