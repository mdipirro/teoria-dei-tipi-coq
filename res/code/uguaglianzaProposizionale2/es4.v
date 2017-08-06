From mathcomp Require Import ssreflect.

Module Leibniz.
(*
Variables (A : Type) (C : A -> A -> Prop).

Definition e_id_l {a b : A} (p : a = b) (c : forall x, C x x) : C a b :=
  match p with eq_refl => c a end.

Definition c_id_l (a : A) (c : forall x, C x x) :
                  e_id_l (eq_refl a) c = c a :=
  eq_refl.*)

Axiom eq : forall A, A -> A -> Prop.
Axiom refl : forall A, forall x : A, eq A x x.
Axiom el : forall (A : Type) (C : A -> A -> Prop),
  (forall x : A, C x x) ->
    forall a b : A, forall p : eq A a b, C a b.
Axiom el_refl : forall (A : Type) (C : A -> A -> Prop)
    (CR : forall x : A, C x x),
    forall x : A, el A C CR x x (refl A x) = CR x.

End Leibniz.

Module LeibnizR.
(*
Variables (A : Type) (C : A -> A -> Type).

Definition e_id_g {a b : A} (p : a = b) (c : C a a) : C a b :=
  match p with eq_refl => fun c => c end c.

Definition c_id_g (a : A) (c : C a a) : e_id_g (eq_refl a) c = c :=
  eq_refl.*)


Axiom eq : forall A, A -> A -> Prop.
Axiom refl : forall A, forall x : A, eq A x x.
Axiom el : forall (A : Type) (a: A) (C : A -> A -> Prop),
  C a a -> forall b : A, forall p : eq A a b, C a b.
Axiom el_refl : forall (A : Type) (a: A) (C : A -> A -> Prop)
    (CR : C a a), el A a C CR a (refl A a) = CR.

End LeibnizR.

Definition f {A} (x y: A) (l: Leibniz.eq A x y) : LeibnizR.eq A x y.
Proof.
Check (Leibniz.el A (fun a b => LeibnizR.eq A a b) _ x y).
apply: (Leibniz.el A (fun a b => LeibnizR.eq A a b) _ x y).
move=> x0.
apply: LeibnizR.refl A x0.
apply l.
Defined.

Definition g {A} (x y: A) (g: LeibnizR.eq A x y) : Leibniz.eq A x y.
Proof.
Check (LeibnizR.el A x (fun a b => Leibniz.eq A x a) _ y g).
apply: (LeibnizR.el A x (fun a p => Leibniz.eq A x a) _ y g).
move=> x0.
exact: Leibniz.refl A x0.
apply l.
Defined.