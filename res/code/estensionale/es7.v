From mathcomp Require Import ssreflect.

Module sum.

Axiom sum : forall (C D: Type), Type.
Axiom inl : forall C D (c: C), sum C D.
Axiom inr : forall C D (d: D), sum C D.
Arguments inl {_ _} _.
Arguments inr {_ _} _.
Axiom el : forall A C D (p: sum C D) (ac: forall x: C, A)
  (ad: forall y: D, A), A.
Arguments el {_ _ _} _ _ _.
Axiom c1 : forall A C D (c: C) (ac: forall x: C, A) (ad: forall y: D, A), 
  el (inl c) ac ad = ac c.
Axiom c2 : forall A C D (d: D) (ac: forall x: C, A) (ad: forall y: D, A), 
  el (inr d) ac ad = ad d.
Axiom eta : forall A C D (p: sum C D) (t: forall z: sum C D, A), 
  el p (fun x => t (inl x)) (fun y => t (inr y)) = t p.
Arguments c1 {_ _ _} _ _ _.
Arguments c2 {_ _ _} _ _ _.
Arguments eta {_ _ _} _ _.

End sum.

Definition f {C D} (s: sum C D) : sum.sum C D.
Proof.
destruct s.
  apply (sum.inl c).
apply (sum.inr d).
Defined.

Definition g {C D} (s: sum.sum C D) : sum C D.
Proof.
apply: (sum.el s (fun x => inl x) (fun y => inr y)).
Defined.

Arguments f {_ _} _.
Arguments g {_ _} _.

Definition pf1 {C D} (s: sum C D) : ext.eq (sum C D) (g (f s)) s.
Proof.
destruct s.
  simpl.
  apply: ext.el_refl (sum C D) (g (sum.inl c)) (inl c) 
    (ext.refl (sum C D) (g (sum.inl c))).
simpl.
apply: ext.el_refl (sum C D) (g (sum.inr d)) (inr d) 
    (ext.refl (sum C D) (g (sum.inr d))).
Defined.

Definition pf2 {C D} (s: sum.sum C D) : ext.eq (sum.sum C D) (f (g s)) s.
Proof.
apply: ext.el_refl (sum.sum C D) (f (g s)) s
    (ext.refl (sum.sum C D) (f (g s))).
Defined.