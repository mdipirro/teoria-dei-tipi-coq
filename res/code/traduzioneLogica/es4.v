From mathcomp Require Import ssreflect.

Definition pf1 {A} {B} (x: A + B): 
  eq x (g (f x)).
Proof.
by case x.
Defined.

Definition pf2 {A} {B} 
  (y: sigT (fun x: Boole => prod ((eq x (inrb tt)) -> A) (eq x (inlb tt) -> B))) :
  eq y (f (g y)).
Proof.
Admitted.
