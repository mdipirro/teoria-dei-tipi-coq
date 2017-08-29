Definition pf1 {A} {B} (x: A + B): 
  eq x (g (f x)).
Proof.
by case x.
Defined.

Axiom functional_extensionality : forall (A B: Type) (f g : A -> B),
  (forall x : A, f x = g x) -> f = g.
Axiom UIP_refl : forall (A:Set) (x:A) (p: x=x), p = refl_equal x.

Definition pf2 {A} {B} 
  (y: sigT (fun x: Boole => prod ((eq x (inrb tt)) -> A) (eq x (inlb tt) -> B))) :
  eq y (f (g y)).
Proof.
case: (f (g y)).
  move=> x p.
  destruct y.
  destruct p.
  destruct x0.
  destruct x.
  destruct p0.
      destruct a0.
      destruct a1.
      rewrite (functional_extensionality _ _ a2 a).
      rewrite (functional_extensionality _ _ b0 b).
          reflexivity.
        move=> x.
        rewrite (UIP_refl Boole (inlb tt) x).
        
Admitted.