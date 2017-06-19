Definition appendStart (x : list n1) (y : n1) := y :: x.

Check x0 :: nil.
Check appendStart nil x0.
Eval compute in appendStart nil x0.
