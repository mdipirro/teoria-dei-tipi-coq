(*Definizione semplice di bool*)
Inductive B := T | F.

(*Definizione a partire dal singoletto*)

Inductive BS :=
  | inl (a: unit)
  | inr (b: unit).

Check inl.
Check inr.

(*Esempi di creazione*)
Definition true_semplice: B := T.
Definition false_semplice: B := F.
Check true_semplice.
Check false_semplice.

Definition true_somma: BS := inl tt.
Definition false_somma: BS := inr tt.
Check true_somma.
Check false_somma.