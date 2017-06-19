Inductive list (A : Type) :=
  nil | cons (a : A) (tl : list A).

Arguments nil {_}.
Arguments cons {_} a tl.

Infix "::" := cons.

Inductive n1 := x0.
