From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Module MartinLof.

Axiom eq : forall A, A -> A -> Type.
Axiom refl : forall A, forall x : A, eq A x x.
Axiom el : forall (A : Type) (C : forall x y : A, eq A x y -> Type),
  (forall x : A, C x x (refl A x)) ->
    forall a b : A, forall p : eq A a b, C a b p.
Axiom el_refl : forall (A : Type) (C : forall x y : A, eq A x y -> Type)
    (CR : forall x : A, C x x (refl A x)),
    forall x : A, el A C CR x x (refl A x) = CR x.

End MartinLof.

Definition q_p {A} {B} (x: A) (y: A) (f: A -> B) (w: eq x y) :
eq (f x) (f y).
Proof.
rewrite w.
apply: erefl.
Defined.

Definition q_m {A} {B} (x: A) (y: A) (f: A -> B) (w: MartinLof.eq A x y) : 
MartinLof.eq B (f x) (f y).
Proof.
apply: (MartinLof.el A (fun a b p => MartinLof.eq B (f a) (f b)) _ x y w).
move=> x0.
exact: MartinLof.refl B (f x0).
Qed.