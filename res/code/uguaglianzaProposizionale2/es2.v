From mathcomp Require Import ssreflect.
Notation erefl := refl_equal.

Inductive N5 := zero | uno | due | tre | quattro.

Definition minore_di_5 := {x| x < 5}.


(* Trovo l'isomorfismo rispetto a {x| x<5} *)
Definition f (n: minore_di_5) : N5 :=
match n with
  | exist 0 _ => zero
  | exist 1 _ => uno
  | exist 2 _ => due
  | exist 3 _ => tre
  | exist 4 _ => quattro
  | exist _ _ => quattro
end.

(*Definition f (n: minore_di_5) : N5 :=
match n with
  exist 0 _ =>  match m with
                  | 0 => zero
                  | 1 => uno
                  | 2 => due
                  | 3 => tre
                  | 4 => quattro
                  | S (S (S (S (S _)))) => quattro
                end
end.*)

Axiom l_0_5 : 0 < 5.
Axiom l_1_5 : 1 < 5.
Axiom l_2_5 : 2 < 5.
Axiom l_3_5 : 3 < 5.
Axiom l_4_5 : 4 < 5.

Definition g (n: N5) : minore_di_5 :=
match n with
  | zero => exist _ 0 l_0_5
  | uno => exist _ 1 l_1_5
  | due => exist _ 2 l_2_5
  | tre => exist _ 3 l_3_5
  | quattro => exist _ 4 l_4_5
end.

(*Definition pf1 (x: minore_di_5) : g (f x) = x :=
match g (f x) with
  | x => erefl
end.

Definition pf1 (x: minore_di_5) : eq x (g (f x)).
Proof.
case: x.
move=> n p.
simpl.
apply (erefl (g zero)).
auto.
case: x.
move=> x p0.
apply: erefl.
Defined.*)

Definition pf2 (n: N5) : f (g n) = n.
Proof.
by case n.
Qed.
