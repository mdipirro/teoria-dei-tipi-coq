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

Module PathInduction.
Axiom eq : forall A, A -> A -> Prop.
Axiom refl : forall A, forall x : A, eq A x x.
Axiom el : forall (A : Type) (x : A) (P : forall a : A, eq A x a -> Prop),
    P x (refl A x) -> forall y : A, forall p : eq A x y, P y p.
Axiom el_refl : forall (A : Type) (x : A) (P : forall y : A, eq A x y -> Prop)
    (PR : P x (refl A x)),
    el A x P PR x (refl A x) = PR.

End PathInduction.

Definition f {A} (x y: A) (m: MartinLof.eq A x y) : PathInduction.eq A x y.
Proof.
apply: (MartinLof.el A (fun a b p => PathInduction.eq A a b) _ x y m).
move=> x0.
exact: PathInduction.refl A x0.
Defined.

Definition g {A} (x y: A) (p: PathInduction.eq A x y) : MartinLof.eq A x y.
Proof.
apply: (PathInduction.el A x (fun a p => MartinLof.eq A x a) _ y p).
exact: MartinLof.refl A x.
Defined.

Definition pf1 {A} (x y: A) (m: MartinLof.eq A x y) : eq m (g x y (f x y m)).
Proof.
apply: (MartinLof.el A (fun x y p => p = g x y (f x y p))) => x0.
by rewrite /f MartinLof.el_refl /g PathInduction.el_refl.
Qed.

Definition pf2 {A} (x y: A) (m: PathInduction.eq A x y) : eq m (f x y (g x y m)).
Proof.
apply: (PathInduction.el A x (fun y p => p = f x y (g x y p))).
by rewrite /f /g PathInduction.el_refl MartinLof.el_refl.
Qed.