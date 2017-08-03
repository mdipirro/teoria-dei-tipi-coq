From mathcomp Require Import ssreflect.

(* Da rivedere *)

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

(*

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
apply: (MartinLof.el A (fun a b p => Leibniz.eq A a b) _ x y m).
move=> x0.
exact: Leibniz.refl A x0.
Defined.

Definition g {A} (x y: A) (p: Leibniz.eq A x y) : MartinLof.eq A x y.
Proof.
Check (Leibniz.el A (fun a p => MartinLof.eq A x a) _ x y p).
apply: (Leibniz.el A (fun a p => MartinLof.eq A x a) _ x y p).
exact: MartinLof.refl A x.
Defined.

*)