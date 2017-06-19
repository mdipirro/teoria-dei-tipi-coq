Definition appendStart {A} (x : list A) (y : A) := y :: x.

Eval compute in appendStart (1 :: nil) 0.

Fixpoint appendEnd {A} (x : list A) (y : A) :=
  match x with
  | nil => y :: nil
  | s :: c => s :: (appendEnd c y)
  end.

Eval compute in appendEnd (1 :: nil) 2.
