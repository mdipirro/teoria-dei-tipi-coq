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

Arguments f {_} _.
Arguments g {_} _.

Definition pf1 (C: Type) (l: list C) : ext.eq _ (g (f l)) l.
Proof.
elim: l.
  simpl.
  apply: (ext.el_refl (list C) (g List.nil) nil
    (ext.refl (list C) (g List.nil))).
move=> a l H.
apply: (ext.el_refl (list C) (g (f (cons a l))) (cons a l)
    (ext.refl (list C) (g (f (cons a l))))).
Defined.

Definition pf2 (C: Type) (l: List.ndList C) : ext.eq _ (f (g l)) l.
Proof.
apply: (ext.el_refl (List.ndList C) (f (g l)) l
  (ext.refl (List.ndList C) (f (g l)))).
Defined.