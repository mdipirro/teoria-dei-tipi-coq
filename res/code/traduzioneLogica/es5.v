From mathcomp Require Import ssreflect.

(* Assiomi *)

Lemma ax_id G A G' D D': forall (g : G) (a : A) (g': G'), D + A + D'.
move=> g a g'.
apply (inl (inr a)).
Qed.

Lemma ax_falso (G G' D : Type) : False -> D.
Proof.
apply: (fun (abs : False) => match abs with end).
Qed.

Lemma ax_true (G D D' : Type) : forall g: G, D + True + D'.
Proof.
move=> g.
apply (inl (inr I)).
Qed.

(* Scambio *)
(* Le regole sono valide per la commutativita' di X nella teoria dei tipi *)

(* And *)
(* La regola di &S conserva la validita' dei sequenti in quanto
nell'interpretazione CHM i termini nel contesto vengono interpretati come
AND*)

Lemma and_d_1 G A B D : forall (g: G) (and: A * B), A + D.
Proof.
move=> g and.
apply (inl (fst and)).
Qed.

Lemma and_d_2 G A B D : forall (g: G) (and: A * B), B + D.
Proof.
move=> g and.
apply (inl (snd and)).
Qed.

(* Or *)
Lemma or_s G A B D: forall (h: forall c': G * (A + B), D) (c: G * A)
(or: A + B), D.
Proof.
move=> h c or.
case: or.
  move=> a.
  apply (h (pair (fst c) (inl a))).
move=> b.
apply (h (pair (fst c) (inr b))).
Qed.

(* La regola di VD conserva la validita' dei sequenti in quanto
nell'interpretazione CHM i termini nelle conclusioni vengono interpretati come
OR*)

(* Not *)
(* Le regole not_s e not_d non conservano la loro validita' in quanto 
non siamo in logica classica *)

(* Implicazione *)
(* Lemma impl_s_1 G A B D : forall (h: (forall c': G * (forall a: A, B), D))
(g: G), D.
Proof.
move=> h c.
Qed.*)

Lemma impl_d G A B D : forall (h: forall c': G, (forall a: A, B) + D) 
(c: G * A), B + D.
Proof.
move=> h c.
destruct h.
    apply (fst c).
  apply (inl (b (snd c))).
apply (inr d).
Qed.

(* Per ogni *)
Lemma perogni_s G A (Ax: A -> Type) D: forall (h: (forall c': G * (forall a: A, Ax a), D))
(g: G) (po: (forall a: A, Ax a)) (t: A) (a_t: Ax t), D.
Proof.
move=> h g p0 t a_t.
apply (h (pair g p0)).
Qed.

Lemma perogni_d G A (Ax: A -> Type) D: forall (h: (forall c': G, (forall a: A, Ax a) + D))
(g: G) (w: A), (Ax w) + D.
Proof.
move=> h g w.
destruct h.
    apply g.
  apply (inl (a w)).
apply (inr d).
Qed.

(* Esiste *)
Inductive sig (A : Type) (P : A -> Type) :=
  sigI (a : A) (p : P a).
Arguments sigI {_ _} _ _.

Lemma esiste_s G A (Ax: A -> Type) D: forall (h: forall c': G * (sig A Ax), D) (w: A)
(c: G * Ax w), D.
Proof.
move=> h w c.
apply (h (pair (fst c) (sigI w (snd c)))).
Qed.

Lemma esiste_d G A (Ax: A -> Type) D: forall (h: (forall c': G, (sig A Ax) + D)) (g: G)
(t: A), (Ax t) + (sig A Ax) + D.
Proof.
move=> h g t.
destruct h.
    apply g.
  apply (inl (inr s)).
auto.
Qed.

(* Uguaglianza *)
Lemma eq_s_1 S A (G: A -> Type) (D: A -> Type) D' : forall (t s: A)
(h: (forall c': S * ((G s) * (t = s)), D s)) (si: S) (e: t = s) (gt: G s), (D t) + D'.
Proof.
move=> t s h si e gt.
rewrite e.
apply (inl (h (pair si (pair gt e)))). (* Risolvere questione G t / G s in ipotesi: 
adesso è G s, ma va G t *)
Qed.

Lemma eq_s_2 S A (G: A -> Type) (D: A -> Type) D' : forall (t s: A)
(h: (forall c': S * ((G t) * (s = t)), D t)) (si: S) (e: s = t) (gs: G t), (D s) + D'.
Proof.
move=> t s h si e gs.
rewrite e.
apply (inl (h (pair si (pair gs e)))). (* Risolvere questione G t / G s in ipotesi: 
adesso è G t, ma va G s *)
Qed.

Lemma ax_eq G D A : forall g: G, forall t: A, (t = t) + D.
Proof.
move=> g t.
apply (inl (eq_refl t)).
Qed.