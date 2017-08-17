From mathcomp Require Import ssreflect.

(* Definizioni di Leibniz e Gentzen come in (2) *)

Definition pf1_l (x: nat): Leibniz.eq (x + 0) x.
Proof.
elim: x.
  apply: Leibniz.refl.
move=> n hp.
rewrite //=.
apply (Leibniz.e_id_l nat (fun a b => Leibniz.eq b a) (n + 0) n 
  hp (fun x => Leibniz.refl x)).
apply: Leibniz.refl.
Qed.

Definition pf2_l (x: nat): Leibniz.eq (0 + x) x.
Proof.
elim: x.
  apply: Leibniz.refl.
move=> n hp.
rewrite //=.
Qed.

Definition pf1_g (x: nat): Gentzen.eq (x + 0) x.
Proof.
elim: x.
  apply: Gentzen.refl.
move=> n hp.
rewrite //=.
apply (Gentzen.e_id_g nat (fun a b => Gentzen.eq b a) (n + 0) n 
  hp (Gentzen.refl (n + 0))).
apply: Gentzen.refl.
Qed.

Definition pf2_g (x: nat): Gentzen.eq (0 + x) x.
Proof.
elim: x.
  apply: Gentzen.refl.
move=> n hp.
rewrite //=.
Qed.


