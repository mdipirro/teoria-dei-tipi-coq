From mathcomp Require Import ssreflect.

Module Leibniz.

  Definition eq {A} (a b : A) : Prop :=
    forall P : A -> Prop, P a -> P b.

  Definition refl {A} (a : A) : eq a a :=
    fun P x => x.

  Definition e_id_l (A : Type) (C : A -> A -> Prop) (a b : A) (p : eq a b)
  (c : forall x, C x x) : C a b := p (C a) (c a).

  Definition c_id_l (A : Type) (C : A -> A -> Prop) (a : A) (c : forall x, C x x) 
  : e_id_l A C a a (refl a) c = c a := eq_refl.

End Leibniz.

Module Gentzen.

Definition eq {A} (a b : A) : Prop :=
    forall P : A -> Prop, P a -> P b.

  Definition refl {A} (a : A) : eq a a :=
    fun P x => x.

  Definition e_id_g (A : Type) (C : A -> A -> Prop) (a b : A) (p : eq a b) 
  (c : C a a) : C a b := p (C a) c.

  Definition c_id_g (A : Type) (C : A -> A -> Prop) (a : A) (c : C a a)
  : e_id_g A C a a (refl a) c = c := eq_refl.

End Gentzen.

Definition q_l {A} {B} (x: A) (y: A) (f: A -> B) (w: Leibniz.eq x y) :
Leibniz.eq (f x) (f y).
Proof.
apply (Leibniz.e_id_l A (fun a b => Leibniz.eq a b) x y w (fun x => Leibniz.refl x)).
apply: Leibniz.refl.
Defined.

Definition q_g {A} {B} (x: A) (y: A) (f: A -> B) (w: Gentzen.eq x y) :
Gentzen.eq (f x) (f y).
Proof.
apply (Gentzen.e_id_g A (fun a b => Gentzen.eq a b) x y w (Gentzen.refl x)).
apply: Leibniz.refl.
Defined.

