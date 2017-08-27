From mathcomp Require Import ssreflect.
Require Import Coq.Logic.FunctionalExtensionality.

Definition pf {A} {B: A -> Type} (f : forall x : A, B x) :
  f = fun x => f x.
Proof.
  extensionality x.
  reflexivity.
Qed.
