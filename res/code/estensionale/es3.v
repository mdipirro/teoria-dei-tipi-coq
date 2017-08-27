From mathcomp Require Import ssreflect.

Inductive sig (B: Type) (C: B -> Type) :=
  sigI (b : B) (c: C b).
Arguments sigI {_ _} _ _.

Module WeakSum.

Axiom wsig : forall (B: Type) (C: B -> Type), Type.
Axiom pair : forall (B: Type) (C: B -> Type) (b: B) (c: C b), wsig B C.
Arguments pair {_ _} _ _.
Axiom el : forall (B: Type) (C: B -> Type) (M : Type)
  (s: wsig B C) (m: forall (x: B) (y: C x), M), M.
Arguments el {_ _ _} _ _.
Axiom el_pair : forall (B: Type) (C: B -> Type) (M : Type)
  (b: B) (c: C b) (m: forall (x: B) (y: C x), M), 
    el (pair b c) m = m b c.
Arguments el_pair {_ _ _} _ _ _.

End WeakSum.

Definition f (B: Type) (C: B -> Type) (s: sig B C) : WeakSum.wsig B C.
Proof.
destruct s.
exact: WeakSum.pair b c.
Defined.

Definition g (B: Type) (C: B -> Type) (w: WeakSum.wsig B C) : sig B C.
Proof.
apply: (WeakSum.el w (fun b c => sigI b c)).
Defined.