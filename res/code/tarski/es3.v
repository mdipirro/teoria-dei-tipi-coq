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

Definition k (x: nat) : Set :=
match x with
  | 0 => Empty_set
  | S n => unit
end.

Definition T (u: Set) : Type := u.

Lemma eq_simm (A: Type) (x y: A) : (x = y) -> (y = x).
Proof.
move=> xy.
by rewrite //=.
Qed.

Lemma Tx_Ty (x y: Set) (w: x = y) : forall z: T x, T y.
Proof.
move=> Tx.
by rewrite (eq_simm Set x y w).
Qed.

Lemma Ty_Tx (x y: Set) (w: x = y) : forall z: T y, T x.
Proof.
move=> Ty.
by rewrite w.
Qed.
