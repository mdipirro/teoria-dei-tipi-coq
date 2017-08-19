From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

(* Definizione di MartinLof come sopra *)

Definition pf_p {A} {P} (x: A) (y: A) (z: P x) (w: eq x y) : eq y y.
Proof.
rewrite //=.
Defined.

Definition pf_m {A} {P} (x: A) (y: A) (z: P x) (w: MartinLof.eq A x y) : 
MartinLof.eq A y y.
Proof.
apply: (MartinLof.el A (fun a b p => MartinLof.eq A b b) _ x y w) => x0.
exact: MartinLof.refl A x0.
Qed.