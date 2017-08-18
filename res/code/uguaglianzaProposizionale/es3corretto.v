From mathcomp Require Import ssreflect.

(* Definizioni di Leibniz e Gentzen come in (2) *)

Definition pf_l {A} {P} (x: A) (y: A) (z: P x) (w: Leibniz.eq x y) : 
Leibniz.eq y y.
Proof.
apply: Leibniz.refl.
Qed.

Definition pf_r {A} {P} (x: A) (y: A) (z: P x) (w: Gentzen.eq x y) : 
Gentzen.eq y y.
Proof.
apply: Gentzen.refl.
Qed.