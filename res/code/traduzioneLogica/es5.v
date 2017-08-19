From mathcomp Require Import ssreflect.

(* Assiomi *)

Lemma ax_id G A G' D D': forall h: G * A * G', D + A + D'.
Proof.
intros.
destruct h.
apply (inl (inr (snd p))).
Qed.

Lemma ax_falso (G G' D : Type) : Empty_set -> D.
Proof.
apply: (fun (abs : Empty_set) => match abs with end).
Qed.

Lemma ax_true (G D D' : Type) : forall h: G, D + True + D'.
Proof.
intros.
apply (inl (inr I)).
Qed.

(* Scambio *)
Lemma sc_sx S G' O G D S' : forall h: (forall c: S * G' * O * G * D, S'),
forall c: S * G * O * G' * D, S'.
Proof.
intros.
apply (h 
(pair 
  (pair 
    (pair (pair (fst (fst (fst (fst c)))) (snd (fst c))) (snd (fst (fst c))))
  (snd (fst (fst (fst c)))))
(snd c))
).
Qed.

Lemma sc_dx S D' O G D S' : forall h: (forall c: G, S + D' + O + D + S'),
forall c: G, S + D + O + D' + S'.
Proof.
intros.
destruct h.
apply c.
destruct s.
destruct s.
destruct s.
        apply (inl (inl (inl (inl s)))).
      apply (inl (inr d)).
    apply (inl (inl (inr o))).
  apply (inl (inl (inl (inr d)))).
apply (inr s).
Qed.

(* And *)
Lemma and_s G A B D : forall h: (forall c: G * A * B, D),
  forall c: G * (A * B), D.
Proof.
intros.
apply (h (pair (pair (fst c) (fst (snd c))) (snd (snd c)))).
Qed.

Lemma and_d G A B D :
forall h: ((forall c1: G, A + D) * (forall c2: G, B + D)),
  forall c: G, (A * B) + D.
Proof.
intros.
destruct h.
destruct s.
    apply c.
  destruct s0.
      apply c.
    apply (inl (pair a b)).
  apply (inr d).
apply (inr d).
Qed.

(* Or *)
Lemma or_s G A B D : 
forall h: (forall c1: G * A, D) * (forall c2: G * B, D),
  forall c: G * (A + B), D.
Proof.
intros.
destruct h.
destruct c.
destruct s.
  apply (d (pair g a)).
apply (d0 (pair g b)).
Qed.

Lemma or_d G A B D : forall h: (forall c: G, A + B + D),
  forall c': G, (A + B) + D.
Proof.
intros.
apply (h c').
Qed.

(* Not *)
Lemma not_s G A D : forall h: (forall c: G, A + D), 
  forall c: G * (forall x: A, Empty_set), D.
Proof.
intros.
destruct h.
    apply (fst c).
  apply (ax_falso G G D ((snd c) a)).
apply d.
Qed.

(* La regola not_d non conserva la sua validita' in quanto non siamo in 
logica classica *)

(* Implicazione *)
Lemma impl_s G A B D : 
forall h: (forall c1: G, A + D) * (forall c2: G * B, D),
  forall c: G * (forall a: A, B), D.
Proof.
intros.
destruct h.
destruct c.
destruct s.
    apply g.
  apply (d (pair g (b a))).
apply d0.
Qed.

(* La regola impl_d non conserva la sua validita' 
Lemma impl_d G A B D : forall (h: forall c: G * A, B + D),
  forall c: G, (forall a: A, B) + D.
*)

(* Per ogni *)
Lemma perogni_s G A (Ax: A -> Type) D (t: A) (a_t: Ax t): 
forall (h: (forall c: G * (forall x: A, Ax x) * (Ax t), D)),
  forall c: G * (forall x: A, Ax x), D.
Proof.
intros.
destruct c.
apply (h (pair (pair g a) a_t)).
Qed.

(* La regola perogni_d non conserva la sua validita'
Lemma perogni_d G A (Ax: A -> Type) D (w: A): 
forall h: (forall c: G, (Ax w) + D), forall c: G, (forall x: A, Ax x) + D.
*)

(* Esiste *)
Inductive sig (A : Type) (P : A -> Type) :=
  sigI (a : A) (p : P a).
Arguments sigI {_ _} _ _.

Lemma esiste_s G A (Ax: A -> Type) D (w: A) (a_w: Ax w):
forall h: (forall c: G * (Ax w), D),
  forall c: G * (sig A Ax), D.
Proof.
intros.
apply (h (pair (fst c) a_w)).
Qed.

Lemma esiste_d G A (Ax: A -> Type) D (t: A):
forall h: (forall c: G, (Ax t) + (sig A Ax) + D),
  forall c: G, (sig A Ax) + D.
Proof.
intros.
destruct h.
    apply c.
  destruct s.
    apply (inl (sigI t a)).
  apply (inl s).
apply (inr d).
Qed.

(* Uguaglianza *)
Lemma eq_s_1 S A (G: A -> Type) (D: A -> Type) D' (t s: A) : 
forall h: (forall c: S * (t = s) * (G t), (D t) + D'),
  forall c: S * (G s) * (t = s), (D s) + D'.
Proof.
intros.
destruct h.
    destruct c.
    rewrite -e in p.
    destruct p.
    apply (pair (pair s0 e) g).
  destruct c.
  rewrite e in d.
  apply (inl d).
apply (inr d).
Qed.

Lemma eq_s_2 S A (G: A -> Type) (D: A -> Type) D' (t s: A) : 
forall h: (forall c: S * (s = t) * (G s), (D s) + D'),
  forall c: S * (G t) * (s = t), (D t) + D'.
Proof.
intros.
destruct h.
    destruct c.
    rewrite -e in p.
    destruct p.
    apply (pair (pair s0 e) g).
  destruct c.
  rewrite e in d.
  apply (inl d).
apply (inr d).
Qed.

Lemma ax_eq G D A (t: A) : forall g: G, (t = t) + D.
Proof.
intros.
apply (inl (eq_refl t)).
Qed.