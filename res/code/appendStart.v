Inductive list (A : Type) :=
  nil | cons (a : A) (tl : list A).

Arguments nil {_}.
Arguments cons {_} a tl.

Infix "::" := cons.

Inductive n1 := x0.

Print list.
Print n1.
Definition appendStart (x : list n1) (y : n1) := y :: x.

Check x0 :: nil.
Check appendStart nil x0.
Eval compute in appendStart nil x0.
