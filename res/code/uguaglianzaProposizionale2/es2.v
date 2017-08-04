From mathcomp Require Import ssreflect.
Require Import Coq.Logic.EqdepFacts.
Notation erefl := refl_equal.

Inductive N3 := zero | one | two.

Definition less_than_3 := {x| x < 3}.


(* Trovo l'isomorfismo rispetto a {x| x<5} *)
Definition lt3_to_N3 (n: less_than_3) : N3 :=
match n with
  | exist 0 _ => zero
  | exist (S m) _ => match m with 
                    | 0 => one
                    | S _ => two
                   end
end.

Axiom l_0_3 : 0 < 3.
Axiom l_1_3 : 1 < 3.
Axiom l_2_3 : 2 < 3.
Axiom l_SSSp_3 : forall p: nat, S (S (S p)) < 3.
Axiom eq_l03 : forall h: 0 < 3, l_0_3 = h.
Axiom eq_l13 : forall h: 1 < 3, l_1_3 = h.
Axiom eq_l23 : forall h: 2 < 3, l_2_3 = h.
(*Axiom eq_lSSSp3 : forall h: forall p: nat, S (S (S p)) < 3, l_2_3 = h.*)

Definition N3_to_lt3 (n: N3) : less_than_3 :=
match n with
  | zero => exist _ 0 l_0_3
  | one => exist _ 1 l_1_3
  | two => exist _ 2 l_2_3
end.

Definition eq_lt3_lt3 (x: less_than_3) : eq x (N3_to_lt3 (lt3_to_N3 x)).
Proof.
destruct x as [ n h ].
destruct n as [ | [ | [ | p ]]]; simpl in *.
replace h with l_0_3.
apply: erefl.
apply: eq_l03.
replace h with l_1_3.
apply: erefl.
apply: eq_l13.
replace h with l_2_3.
apply: erefl.
apply: eq_l23.

Defined.

Definition eq_n3_n3 (n: N3) : lt3_to_N3 (N3_to_lt3 n) = n.
Proof.
by case n.
Defined.
