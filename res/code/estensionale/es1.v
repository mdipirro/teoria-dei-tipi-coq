From mathcomp Require Import ssreflect.
Require Import Coq.Logic.FunctionalExtensionality.

Definition pf {A} {B: A -> Type} (f g: forall x : A, B x)
(w: forall x: A, f x = g x) : (fun x => f x) = (fun x => g x).
Proof.
extensionality x.
apply (w x).
Qed.