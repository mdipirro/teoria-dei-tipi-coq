Fixpoint appendEnd (x : list n1) (y : n1) :=
  match x with
  | nil => y :: nil
  | s :: c => s :: (appendEnd c y)
  end.

Eval compute in appendEnd (x0 :: nil) x0.
