From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

(* eta conversione del prodotto *)
Lemma eta_conversione {A} {B} (z: prod A B) : pair (fst z) (snd z) = z.
Proof.
destruct z.
rewrite //=.
Qed.

(* eta conversione in uguaglianza proposizionale *)
Definition pf {A} {B} (z: prod A B) : eq (pair (fst z) (snd z)) z.
Proof.
destruct z.
rewrite //=.
Defined.
