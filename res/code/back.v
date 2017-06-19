Definition notNil (A : Type) := { lt : list A | ~ lt = nil }.

Lemma ex_falso P : False -> P.
Proof. move=> abs. case: abs. Qed.

Definition back {A} (x : notNil A) : list A.
Proof.
case: x.
move=> lt.
case: lt.
  move=> abs.
  apply: ex_falso.
  apply: abs.
  apply: erefl.
move=> p lt _.
apply: lt.
Defined.

Lemma not_123_nil : ~ ( (1 :: 2 :: 3 :: nil) = nil).
Proof.
move=> E.
change (match (1 :: 2 :: 3 :: nil) with nil => True | (_ :: _) => False end).
rewrite E.
apply: I.
Qed.

Definition n123n : notNil nat := exist _ (1 :: 2 :: 3 :: nil) not_123_nil.

Eval compute in back n123n.
