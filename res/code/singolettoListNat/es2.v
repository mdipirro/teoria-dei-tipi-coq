From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.
Open Scope list_scope.

Fixpoint append {A} (x: list A) (y: list A): list A :=
  match y with
  | nil => x
  | cons e es => e :: (append x es)
  end.

Lemma appendxnil {A} (x: list A) : append x nil = x.
Proof.
elim x.
  by [].
move=> a l hp.
by [].
Qed.