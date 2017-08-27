From mathcomp Require Import ssreflect.

Module Nat.

Axiom ndNat : Type.
Axiom zero : ndNat.
Axiom succ : forall (m: ndNat), ndNat.
Axiom el : forall D, forall (d: D) (m: ndNat)
  (e: forall (x: ndNat) (z: D), D), D.
Axiom c1 : forall D, forall (d: D) (e: forall (x: ndNat) (z: D), D), 
  el D d zero e = d.
Axiom c2 : forall D, forall (m: ndNat) (d: D) (e: forall (x: ndNat) (z: D), D), 
    el D d (succ m) e = e m (el D d m e).
Axiom c_eta : forall D, forall (d: D) (e: forall (x: ndNat) (z: D), D)
  (t: forall y: ndNat, D) (m: ndNat) (eq1: t zero = d) 
  (eq2: forall (x: ndNat) (z: D), t (succ x) = e x (t x)),
    el D d m e = t m.

End Nat.

Fixpoint f (n: nat) : Nat.ndNat :=
match n with
  | 0 => Nat.zero
  | S m => Nat.succ (f m)
end.

Definition g (n: Nat.ndNat) : nat.
Proof.
apply: (Nat.el nat 0 n (fun x z => z)).
Defined.
