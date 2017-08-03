Inductive PathInduction (A: Type) (x : A) : A -> Type :=
| pi_refl : PathInduction A x x.

Inductive MartinLof (A: Type) : A -> A -> Type :=
| ml_refl x : MartinLof A x x.

Definition f {A} {x y: A} (p: PathInduction A x y) : MartinLof A x y :=
  match p with pi_refl _ _ => ml_refl A x end.

Definition g {A} {x y: A} (p: MartinLof A x y) : PathInduction A x y :=
  match p with ml_refl _ z => pi_refl A z end.

Definition pf1 {A} (x y: A) (p: PathInduction A x y) : g (f p) = p :=
  match p with pi_refl _ _ => eq_refl end.

Definition pf2 {A} (x y: A) (p: MartinLof A x y) : f (g p) = p :=
  match p with ml_refl _ _ => eq_refl end.