From mathcomp Require Import ssreflect.

Inductive sig (B: Type) (C: B -> Type) :=
  sigI (b : B) (c: C b).
Arguments sigI {_ _} _ _.

Module ExtIndSum.

Axiom esum : forall (B: Type) (C: B -> Type), Type.
Axiom esumI : forall (B: Type) (C: B -> Type) (b: B) (c: C b), esum B C.
Arguments esumI {_ _} _ _.
Axiom pi_1 : forall (B: Type) (C: B -> Type) (d: esum B C), B.
Arguments pi_1 {_ _} _.
Axiom pi_2 : forall (B: Type) (C: B -> Type) (d: esum B C), C (pi_1 d).
Arguments pi_2 {_ _} _.
Axiom beta_1 : forall (B: Type) (C: B -> Type) (b: B) (c: C b),
  pi_1 (esumI b c) = b.
Axiom eta : forall (B: Type) (C: B -> Type) (d: esum B C),
  esumI (pi_1 d) (pi_2 d) = d.
(*Axiom beta_2 : forall (B: Type) (C: B -> Type) (b: B) (c: C b),
  pi_2 (esumI b c) = c.*)

End ExtIndSum.

Definition f (B: Type) (C: B -> Type) (s: sig B C) : ExtIndSum.esum B C.
Proof.
destruct s.
apply (ExtIndSum.esumI b c).
Defined.

Definition g (B: Type) (C: B -> Type) (e: ExtIndSum.esum B C) : sig B C.
Proof.
apply (sigI (ExtIndSum.pi_1 e) (ExtIndSum.pi_2 e)).
Defined.

Arguments f {_ _} _.
Arguments g {_ _} _.

Definition pf1 (B: Type) (C: B -> Type) (s: sig B C) : 
  ext.eq _ (g (f s)) s.
Proof.
destruct s.
simpl.
apply: ext.el_refl (sig B C) (g (ExtIndSum.esumI b c)) (sigI b c) 
  (ext.refl (sig B C) (g (ExtIndSum.esumI b c))).
Defined.

Definition pf2 (B: Type) (C: B -> Type) (e: ExtIndSum.esum B C) : 
  ext.eq _ (f (g e)) e.
Proof.
simpl.
rewrite ExtIndSum.eta.
apply ext.refl.
Defined.

