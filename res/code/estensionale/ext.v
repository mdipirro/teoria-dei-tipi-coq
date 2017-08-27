Module ext.

Axiom eq : forall C, C -> C -> Prop.
Axiom refl : forall (C: Type) (c: C), eq C c c.
Axiom el : forall (C: Type) (c d: C) (p: eq C c d), c = d.
Axiom el_refl : forall (C: Type) (c d: C) (p: eq C c c), eq C c d.

End ext.