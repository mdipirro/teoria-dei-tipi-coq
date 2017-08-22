From mathcomp Require Import ssreflect.

(* Definizioni di Leibniz e Gentzen come in (2) *)

Definition pf_l {A} (x: A) (y: A) (z: A) (w1: Leibniz.eq x y) 
(w2: Leibniz.eq y z) : Leibniz.eq x z.
Proof.
apply (Leibniz.e_id_l A (fun a b => Leibniz.eq a b) y z w2 (fun x => Leibniz.refl x)).
apply (Leibniz.e_id_l A (fun a b => Leibniz.eq a b) x y w1 (fun x => Leibniz.refl x)).
Qed.

Definition pf_g {A} (x: A) (y: A) (z: A) (w1: Gentzen.eq x y) 
(w2: Gentzen.eq y z) : Gentzen.eq x z.
Proof.
apply (Gentzen.e_id_g A (fun a b => Gentzen.eq a b) y z w2 (Gentzen.refl y)).
apply (Gentzen.e_id_g A (fun a b => Gentzen.eq a b) x y w1 (Gentzen.refl x)).
Qed.