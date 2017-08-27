From mathcomp Require Import ssreflect.
Require Import Coq.Logic.FunctionalExtensionality.

Definition pf {A} {B: A -> Type} (f g: forall x : A, B x)
(w: forall x: A, f x = g x) : (fun x => f x) = (fun x => g x).
Proof.
extensionality x.
apply (w x).
Qed.

Definition pf' {A} {B: A -> Type} (f g: forall x : A, B x)
(w: forall x: A, ext.eq _ (f x) (g x)) : 
  ext.eq _ (fun x => f x) (fun x => g x).
Proof.
apply: ext.el_refl _ (fun x : A => f x) (fun x : A => g x)
    (ext.refl _ (fun x : A => f x)).
Qed.