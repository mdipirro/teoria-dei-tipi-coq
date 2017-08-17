From mathcomp Require Import ssreflect.
Open Scope list_scope.

(*Naturali positivi*)
Definition nat_positivo := {n: nat | ~ n = 0}.

Lemma not_Sn_zero (n: nat): ~((S n) = 0).
Proof.
case n.
  by [].
by [].
Qed.

Definition tre_positivo : nat_positivo := exist _ 3 (not_Sn_zero 2).

(*
Non corretta (giustamente):
Definition zero_positivo: nat_positivo := exist _ 0 (not_Sn_zero 0).
*)

(*Lista non vuota*)
Definition lista_non_vuota (A: Type) := { l: list A  | ~ l = nil }.

Lemma not_xnil_nil {A} (x: A) : ~(x :: nil = nil).
Proof.
move=> E.
change (match x :: nil with nil => True | cons _ _ => False end).
rewrite E.
apply: I.
Qed.

Lemma not_xxs_nil {A} (x: A) (xs: list A) : ~ (x :: xs = nil).
Proof.
move=> E.
change (match x :: xs with nil => True | cons _ _ => False end).
rewrite E.
apply: I.
Qed.

Definition non_vuota : lista_non_vuota nat := 
exist _ (1 :: 2 :: 3 :: 4 :: nil) (not_xxs_nil 1 (2 :: 3 :: 4 :: nil)).
