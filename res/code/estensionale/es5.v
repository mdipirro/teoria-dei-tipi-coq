From mathcomp Require Import ssreflect.
Require Import Coq.Logic.FunctionalExtensionality.

Print list_rect.

Module List.

Axiom ndList : forall C: Type, Type.
Axiom nil : forall C, ndList C.
Axiom cons : forall C, forall (c: C) (l: ndList C), ndList C.
Arguments nil {_}.
Arguments cons {_} _ _.
Axiom el : forall (C L: Type) (P : ndList C -> Set),
       P nil ->
       (forall (c: C) (s: ndList C), P s -> P (cons c s)) ->
       forall s: ndList C, P s.
(*Axiom c1 : forall (C L : Type) (P : ndList C -> Set),
       P nil ->
       (forall (c: C) (s: ndList C), P s -> P (cons c s)) ->
       forall s: ndList C, el C L P .
Axiom c2 : forall C L (P: ndList C -> Set), forall (s: ndList C) (a: L) (c: C)
  (l: C -> L -> L), P (cons C c s).
Axiom c_eta : forall C L (P: ndList C -> L), forall (a: L) (l: C -> L -> L)
  (t: forall y: ndList C, L) (s: ndList C) (u1: t (nil C) = a)
  (u2: forall (x: C) (z: ndList C), t (cons C x z) = l x (t z)),
    P s = t s.*)

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
Check (List.el C (list C) _ n (fun c l p => cons c l)).
