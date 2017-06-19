Fixpoint append {A} (x : list A) (y : list A) :=
  match y with
  | nil => x
  | s :: c => append (appendEnd x s) c
  end.
