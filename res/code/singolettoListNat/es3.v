From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.
Open Scope list_scope.

Inductive vec (A : Type) : nat -> Type :=
| Nil : vec A 0
| Cons : forall n : nat, A -> vec A n -> vec A (S n).

Arguments Nil {_}.
Arguments Cons {_} {_} x xs.

Definition non_vuota : vec nat 3 := (Cons 1 (Cons 2 (Cons 3 Nil))).

Fixpoint back {A} {n: nat} (v: vec A (S n)) : vec A n.
Proof.
inversion v.
destruct n.
  apply X0.
apply (Cons X (back _ _ X0)).
Defined.

Definition front {A} {n: nat} (v: vec A (S n)) : vec A n.
Proof.
inversion v.
apply X0.
Defined.

Definition last {A} {n: nat} (v: vec A (S n)) : A.
Proof.
inversion v.
apply X.
Defined.

Fixpoint first {A} {n : nat} (v : vec A (S n)) : A.
Proof.
inversion v.
destruct n.
  apply X.
apply (first _ _ X0).
Defined.

Eval compute in back non_vuota.
Eval compute in front non_vuota.
Eval compute in last non_vuota.
Eval compute in first non_vuota.
