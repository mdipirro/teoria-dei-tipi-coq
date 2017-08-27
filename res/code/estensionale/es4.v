From mathcomp Require Import ssreflect.

Module List.

Axiom ndList : forall C: Type, Type.
Axiom nil : forall C, ndList C.
Axiom cons : forall C, forall (c: C) (l: ndList C), ndList C.
Arguments nil {_}.
Arguments cons {_} _ _.
Axiom el : forall (C L: Type), forall (a: L) (s: ndList C)
  (l: forall (x: C) (z: L), L), L.
Axiom c1 : forall (C L: Type), forall (a: L) (l: forall (x: C) (z: L), L), 
  el C L a nil l = a.
Axiom c2 : forall (C L: Type), forall (s: ndList C) (c: C) (a: L) 
  (l: forall (x: C) (z: L), L), 
    el C L a (cons c s) l = l c (el C L a s l).
Axiom c_eta : forall (C L: Type), forall (a: L) (l: forall (x: C) (z: L), L)
  (t: forall y: ndList C, L) (s: ndList C) (eq1: t nil = a) 
  (eq2: forall (x: C) (z: ndList C), t (cons x z) = l x (t z)),
    el C L a s l = t s.

End List.

Definition f {C} (l: list C) : List.ndList C.
Proof.
elim: l.
  exact List.nil.
move=> c l H.
exact (List.cons c H).
Defined.

Definition g {C} (n: List.ndList C) : list C.
Proof.
apply: (List.el C (list C) nil n (fun c l => cons c l)).
Defined.