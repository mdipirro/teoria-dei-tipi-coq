From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Inductive N3 := zero | uno | due.

Definition minore_di_tre := {x| x < 3}.

Lemma l_0_3 : 0 < 3.
Proof.
by [].
Qed.

Lemma l_1_3 : 1 < 3.
Proof.
by [].
Qed.

Lemma l_2_3 : 2 < 3.
Proof.
by [].
Qed.

(* Trovo l'isomorfismo rispetto a {x| x<5} *)
Definition f (n: minore_di_tre) : N3 :=
match n with
  | exist 0 _ => zero
  | exist (S m) _ => match m with 
                    | 0 => uno
                    | S _ => due
                   end
end.

Definition g (n: N3) : minore_di_tre :=
match n with
  | zero => exist _ 0 l_0_3
  | uno => exist _ 1 l_1_3
  | due => exist _ 2 l_2_3
end.

Definition pf1 (x: minore_di_tre) : x = (g (f x)).
Proof.
by apply: val_inj; case: x => [[| [|[|x]]] Px].
Defined.

Definition pf2 (n: N3) : f (g n) = n.
Proof.
by case n.
Defined.
