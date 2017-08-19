From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Definition pf_p {A} (x: A) (y: A) (z: A) (w1: eq x y) (w2: eq y z) : eq x z.
Proof.
rewrite w1 w2.
apply: erefl.
Defined.

(*
Dato che nell'esercizio 10.3 è stato dimostrato l'isomorfismo tra l'uguaglianza
di MartinLof e quella con Path Induction (quella di Coq), lo uso per svolgere
questo esercizio. Le funzioni f e g sono quelle definite in 10.3 e la
definizione di MartinLof è quella data in precedenza.

La definizione di pf_m si basa sulla transitività dell'uguaglianza, di cui ho
due prove w1 e w2 e sull'isomorfismo con l'uguaglianza di Coq. In questo modo
la definizione di pf_m è molto più semplice e leggibile.
*)

Definition f {A} (x y: A) (m: MartinLof.eq A x y) : x = y.
Proof.
apply: (MartinLof.el A (fun a b p => a = b) _ x y m).
move=> x0.
exact: erefl.
Defined.

Definition g {A} (x y: A) (p: x = y) : MartinLof.eq A x y.
Proof.
rewrite p.
exact: MartinLof.refl A y.
Defined. 

Definition pf_m {A} (x: A) (y: A) (z: A) (w1: MartinLof.eq A x y)
(w2: MartinLof.eq A y z) : MartinLof.eq A x z.
Proof.
replace x with y.
  apply w2.
apply (eq_sym (f x y w1)).
Defined.
