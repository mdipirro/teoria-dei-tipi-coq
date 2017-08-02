From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Inductive N5 := zero | uno | due | tre | quattro.

Definition minore_di_5 := {x| x < 5}.


(* Trovo l'isomorfismo rispetto a nat *)
Definition f (n: minore_di_5) : N5 :=
match n with
  exist m _ =>  match m with
                  | 0 => zero
                  | 1 => uno
                  | 2 => due
                  | 3 => tre
                  | 4 => quattro
                  | S (S (S (S (S _)))) => quattro
                end
end.

Lemma l_0_5 : 0 < 5.
Proof.
Admitted.

Lemma l_1_5 : 1 < 5.
Proof.
Admitted.

Lemma l_2_5 : 2 < 5.
Proof.
Admitted.

Lemma l_3_5 : 3 < 5.
Proof.
Admitted.

Lemma l_4_5 : 4 < 5.
Proof.
Admitted.

Definition g (n: N5) : minore_di_5 :=
match n with
  | zero => exist _ 0 l_0_5
  | uno => exist _ 1 l_1_5
  | due => exist _ 2 l_2_5
  | tre => exist _ 3 l_3_5
  | quattro => exist _ 4 l_4_5
end.

Definition pf1 (x: minore_di_5) : eq x (g (f x)).
Proof.
case: x.
move=> x p.
simpl.
destruct x.
rewrite //=.


