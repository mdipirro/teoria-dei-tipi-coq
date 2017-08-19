From mathcomp Require Import ssreflect.

Lemma ex_falso P : False -> P.
Proof.
move=> abs.
case: abs.
Qed.

(* Dimostrazione base di 0 <> 1 *)
Lemma not_id_0_1_base : 0 = 1 -> Empty_set.
Proof.
move=> abs.
by apply ex_falso.
Qed.

(* Definizione di k *)

Definition k (x: nat) : Set :=
match x with
  | 0 => Empty_set
  | S _ => unit
end.

(* Dimostro il se e solo se dimostrando separatamente le due direzioni *)

Definition T (u: Set) : Type := u.

Lemma Tx_Ty (x y: Set) (w: x = y) : forall z: T x, T y.
Proof.
move=> Tx.
by rewrite (eq_sym w).
Qed.

Lemma Ty_Tx (x y: Set) (w: x = y) : forall z: T y, T x.
Proof.
move=> Ty.
by rewrite w.
Qed.
