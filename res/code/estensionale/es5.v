From mathcomp Require Import ssreflect.
Require Import Coq.Logic.FunctionalExtensionality.

Print list_rec.

Module ext.

Axiom eq: forall C, C -> C -> Type.
Axiom refl: forall C, forall c: C, eq C c c.
Axiom el: forall C, forall (c d: C) (p: eq C c d), c = d.
(*Definition comp: forall C, forall (c d: C) (p: eq C c d), eq p (refl C c).*)

End ext.

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

Definition g (C: Type) (n: List.ndList C) : list C.
Proof.
apply: (List.el C (list C) nil n (fun c l => cons c l)).
Defined.

Definition pf1_1 {C} : g C (f nil) = nil.
Proof.
simpl.
apply: (List.c1 C (list C) nil (fun c l => cons c l)).
Defined.

Definition pf1_2 {C} (c: C) (l: list C) : g C (f (cons c l)) = cons c l.
Proof.
simpl.
apply: (List.c2 C (list C) (List.cons c (f l)) c l (fun c l => cons c l)).
Defined.

(*
elim: l.
  simpl.
  apply: (List.c1 C (list C) nil (fun c l => cons c l)).
intros.
simpl.
replace (g C (List.cons a (f l))) with (cons a l).
exact: ext.refl.
Check (eq_sym (ext.el (list C) ((g C (f l))) l X)).

Check (List.c_eta C (list C) nil (fun c l => cons c l) (g C) (List.cons a (f l))
g_nil_nil g_cons).
replace (a :: l)%list with (a :: List.el C (list C) l (f l)
  (fun (c : C) (l : list C) => c :: l))%list.
apply: (List.c2 C (list C) (f l) a l (fun c l => cons c l)).
*)