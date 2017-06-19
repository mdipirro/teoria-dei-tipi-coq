Fixpoint front {A} (x : list A) : list A :=
  match x with
  | nil => nil
  | a :: nil => nil
  | s :: c => s :: front c
  end.

Eval compute in front (1 :: 2 :: 3 :: nil).
Eval compute in front (1 :: nil).
Eval compute in front nil.
