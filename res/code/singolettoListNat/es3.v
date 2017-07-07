From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.
Open Scope list_scope.

(*Fixpoint back {A} (l: lista_non_vuota A) : list A.
Proof.
case l.
move=> xs pf.
case xs.
  apply nil.
move=> e es.
case es.
  apply (e :: nil).
move=> y ys.
apply (e :: (back (exist _ ys not_xnil_nil))).
Defined.

Print back.*)

Definition lista_non_vuota (A: Type) := { l: list A  | ~ l = nil }.

Lemma ex_falso P : False -> P.
Proof. move=> abs. case: abs. Qed.

Lemma not_xnil_nil {A} (x: A) : ~(x :: nil = nil).
Proof.
move=> E.
change (match x :: nil with nil => True | cons _ _ => False end).
rewrite E.
apply: I.
Qed.

Lemma not_xxs_nil {A} (x: A) (xs: list A) : ~ (x :: xs = nil).
Proof.
move=> E.
change (match x :: xs with nil => True | cons _ _ => False end).
rewrite E.
apply: I.
Qed.

Definition front {A} (l: lista_non_vuota A) : list A.
Proof.
case: l.
move=> xs _.
case xs.
  apply nil.
move=> e es.
apply: es.
Defined.

Definition last {A} (l: lista_non_vuota A) : A.
Proof.
case: l.
move=> xs.
case: xs.
  move=> abs.
  apply: ex_falso.
  apply: abs.
  apply: erefl.
move=> e es _.
apply: e.
Defined.

(*Fixpoint first {A} (l: lista_non_vuota A) : A.
Proof.
case: l.
move=> xs.
case: xs.
  move=> abs.
  apply: ex_falso.
  apply: abs.
  apply: erefl.
move=> e es _.
elim: es.
  apply: e.
Defined.*)


Definition non_vuota : lista_non_vuota nat := 
exist _ (1 :: 2 :: 3 :: 4 :: nil) (not_xxs_nil 1 (2 :: 3 :: 4 :: nil)).
Eval compute in (front non_vuota).
Eval compute in (last non_vuota).
Eval compute in (first non_vuota).