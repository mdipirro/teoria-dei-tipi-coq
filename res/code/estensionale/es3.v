From mathcomp Require Import ssreflect.
Require Import Coq.Logic.FunctionalExtensionality.

Inductive sig (B: Type) (C: B -> Type) :=
  sigI (b : B) (c: C b).
Arguments sigI {_ _} _ _.

Module WeakSum.

Axiom wsig : forall (B: Type) (C: B -> Type), Type.
Axiom pair : forall (B: Type) (C: B -> Type) (b: B) (c: C b), wsig B C.
Axiom el : forall (B: Type) (C: B -> Type) (M : Type),
       (forall (b: B) (c: C b), M) -> forall s: wsig B C, M.
Axiom el_pair : forall (B: Type) (C: B -> Type) (M: Type),
       (forall (b: B) (c: C b), M) -> M.

End WeakSum.

Definition f (B: Type) (C: B -> Type) (s: sig B C) : WeakSum.wsig B C.
Proof.
destruct s.
exact: WeakSum.pair B C b c.
Defined.

Definition g (B: Type) (C: B -> Type) (w: WeakSum.wsig B C) : sig B C.
Proof.
apply: (WeakSum.el B C (sig B C) (fun b c => sigI b c)) w.
Defined.

Arguments f {_ _} _.
Arguments g {_ _} _.

Definition pf1 (B: Type) (C: B -> Type) (s: sig B C) : g (f s) = s.
Proof.
destruct s.
destruct (sigI b c).
apply (WeakSum.el B C _ (fun b c => g (WeakSum.pair B C b c) = sigI b c) 
  (WeakSum.pair B C b c)).