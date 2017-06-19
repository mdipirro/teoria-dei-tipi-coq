Definition first {A} (x : notNil A) : A.
Proof.
case: x.
move=> lt.
case: lt.
  move=> abs.
  apply: ex_falso.
  apply: abs.
  apply: erefl.
move=> a lt hyp.
apply: a.
Defined.

Eval compute in back n123n.
