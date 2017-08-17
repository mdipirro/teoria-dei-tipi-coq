From mathcomp Require Import ssreflect.

(* Definizioni di Leibniz e Gentzen come in (2) *)

Definition pf_l (x: unit) : Leibniz.eq x tt.
Proof.
case: x.
apply: Leibniz.refl.
Qed.

Definition pf_g (x: unit) : Gentzen.eq x tt.
Proof.
case: x.
apply: Gentzen.refl.
Qed.