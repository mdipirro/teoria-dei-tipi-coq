From mathcomp Require Import ssreflect.
Require Import Coq.Logic.FunctionalExtensionality.

Definition pf {A} {B: A -> Type} (f : forall x : A, B x) :
  f = fun x => f x.
Proof.
  extensionality x.
  reflexivity.
Qed.

Definition pf' {A} {B: A -> Type} (f : forall x : A, B x) :
  ext.eq _ f (fun x => f x).
Proof.
apply: ext.el_refl _ f (fun x : A => f x) (ext.refl _ f).
Qed.