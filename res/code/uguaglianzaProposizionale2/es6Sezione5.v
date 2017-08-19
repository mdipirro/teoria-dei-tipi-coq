From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

(* Definizione di MartinLof come sopra *)

Definition pf1_p (x: nat): eq (x + 0) x.
Proof.
rewrite //=.
Defined.

Definition pf2_p (x: nat): eq (0 + x) x.
Proof.
rewrite //=.
Defined.

Definition pf1_m (x: nat): MartinLof.eq nat (x + 0) x.
Proof.
elim: x.
  apply: MartinLof.refl.
move=> n hp.
rewrite //=.
apply: (MartinLof.el nat (fun a b p => MartinLof.eq nat (S a) (S b))
  _ (n + 0) n hp) => x.
apply: MartinLof.refl.
Defined.

Definition pf2_m (x: nat): MartinLof.eq nat (0 + x) x.
Proof.
rewrite //=.
apply: MartinLof.refl.
Defined.