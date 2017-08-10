From mathcomp Require Import ssreflect.

(* eta conversione in uguaglianza proposizionale *)
Definition pf {A} {B} (z: prod A B) : eq (pair (fst z) (snd z)) z.
Proof.
destruct z.
rewrite //=.
Defined.
