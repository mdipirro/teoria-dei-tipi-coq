From mathcomp Require Import ssreflect.
Open Scope list_scope.

Fixpoint append {A} (l: list A) (a: A): list A :=
  match l with
  | nil => a :: nil
  | cons x xs => x :: (append xs a)
  end.

Fixpoint reverse {A} (l: list A): list A :=
  match l with
  | nil => nil
  | cons x xs => append (reverse xs) x
  end.