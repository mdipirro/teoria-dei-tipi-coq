From mathcomp Require Import ssreflect.
Require Import Coq.Logic.FunctionalExtensionality.

Module WeakSum.

Axiom wsig : forall (B: Type) (C: B -> Type), Type.
Axiom pair : forall (B: Type) (C: B -> Type) (b: B) (c: C b), wsig B C.
Arguments pair {_ _} _ _.
Axiom el : forall (B: Type) (C: B -> Type) (M : Type)
  (s: wsig B C) (m: forall (x: B) (y: C x), M), M.
Arguments el {_ _ _} _ _.
Axiom el_pair : forall (B: Type) (C: B -> Type) (M : Type)
  (b: B) (c: C b) (m: forall (x: B) (y: C x), M), 
    ext.eq _ (el (pair b c) m) (m b c).
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

Arguments f {_ _} _.
Arguments g {_ _} _.

(*Definition pf1 (B: Type) (C: B -> Type) (s: sig B C) : g (f s) = s.
Proof.
destruct s.
simpl.
case (g (WeakSum.pair b c)) => b0 c0.
replace (sigI b0 c0) with 
  (WeakSum.el (WeakSum.pair b c) (fun (x : B) (_ : C x) => sigI b c)).
apply: (WeakSum.el_pair b c (fun x y => sigI b c)).
Check (WeakSum.el_pair b c (fun x y => sigI b0 c0)).
Admitted.*)

Definition pf2 (B: Type) (C: B -> Type) (w: WeakSum.wsig B C) : 
  ext.eq _ (f (g w)) w.
Proof.
case (g w) => b c.
simpl.
Check (ext.el _ (WeakSum.pair b c) w).
