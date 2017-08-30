From mathcomp Require Import ssreflect.

Module LeibnizR.

Definition eq {A} (a b : A) : Prop :=
  forall P : A -> Prop, P a -> P b.

Definition refl {A} (a : A) : eq a a :=
  fun P x => x.

Definition e_id_r (A : Type) (C : A -> A -> Prop) (a b : A) (p : eq a b) 
(c : C a a) : C a b := p (C a) c.

Definition c_id_r (A : Type) (C : A -> A -> Prop) (a : A) (c : C a a)
: e_id_r A C a a (refl a) c = c := eq_refl.

Axiom UIP : forall (A: Type) (x y: A) (p1 p2: eq x y), p1 = p2. 

End LeibnizR.

Module Leibniz.

Definition eq {A} (a b : A) : Prop :=
  forall P : A -> Prop, P a -> P b.

Definition refl {A} (a : A) : eq a a :=
  fun P x => x.

Definition e_id_l (A : Type) (C : A -> A -> Prop) (a b : A) (p : eq a b)
(c : forall x, C x x) : C a b := p (C a) (c a).

Definition c_id_l (A : Type) (C : A -> A -> Prop) (a : A) (c : forall x, C x x) 
: e_id_l A C a a (refl a) c = c a := eq_refl.

Axiom UIP : forall (A: Type) (x y: A) (p1 p2: eq x y), p1 = p2. 

End Leibniz.

Definition f {A} (x y: A) (l: Leibniz.eq x y) : LeibnizR.eq x y.
Proof.
apply: (Leibniz.e_id_l A (fun a b => LeibnizR.eq a b) x y l).
move=> x0.
apply: LeibnizR.refl x0.
Defined.

Definition g {A} (x y: A) (r: LeibnizR.eq x y) : Leibniz.eq x y.
Proof.
apply: (LeibnizR.e_id_r A (fun a b => Leibniz.eq a b) x y r).
move=> x0.
apply: Leibniz.refl x0.
Defined.

(* Equivalenza *)
Lemma equiv_ml_l (A: Type) : forall x y: A, Leibniz.eq x y <-> LeibnizR.eq x y.
Proof.
move=> x y.
split.
  move=> l.
  apply (f x y l).
move=> r.
apply (g x y r).
Qed.

(* Isomorfismo *)

Definition pf1 {A} (x y: A) (l: Leibniz.eq x y) : eq l (g x y (f x y l)).
Proof.
apply: (Leibniz.e_id_l A (fun x y => forall l, l = f x y (g x y l)) x y l).
move=> x0 l0.
apply: (LeibnizR.UIP A x0 x0 l0 (f x0 x0 (g x0 x0 l0))).
Defined.

Definition pf2 {A} (x y: A) (r: Leibniz.eq x y) : eq r (f x y (g x y r)).
Proof.
apply: (LeibnizR.e_id_r A (fun x y => forall r, r = f x y (g x y r)) x y r).
move=> r0.
apply: (Leibniz.UIP A x x r0 (f x x (g x x r0))).
Defined.
