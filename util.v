Require Import Coq.Reals.Reals.
Require Import Fourier.
Set Implicit Arguments.
Open Local Scope R_scope.

Definition decision (P: Prop): Set := { P } + { ~ P }.

Record decideable_overestimator (A: Type) (Ideal: A -> Prop) :=
  { doe_pred: A -> Prop
  ; doe_dec: forall a, decision (doe_pred a)
  ; doe_correct: forall a, Ideal a -> doe_pred a
  }.

Definition pair_eq_dec (X Y: Set)
  (X_eq_dec: forall x x': X, {x=x'}+{x<>x'})
  (Y_eq_dec: forall y y': Y, {y=y'}+{y<>y'})
    (p: prod X Y) (p': prod X Y): decision (p=p').
Proof with auto.
  destruct p. destruct p'. unfold decision.
  destruct (X_eq_dec x x0); destruct (Y_eq_dec y y0);
    subst; try auto; right; intro; inversion H...
Defined.

Hint Unfold decision.

Definition and_dec (P Q: Prop) (Pdec: decision P) (Qdec: decision Q):
  decision (P/\Q).
Proof. unfold decision. tauto. Qed.

Hint Resolve and_dec.

Definition unsumbool (A B: Prop) (sb: {A}+{B}): bool :=
  if sb then true else false.

Definition conj_fst (A B: Prop) (P: A /\ B): A :=
    match P with conj r _ => r end.
  Definition conj_snd (A B: Prop) (P: A /\ B): B :=
    match P with conj _ r => r end.

Lemma Rmax_le x y z: x <= z -> y <= z -> Rmax x y <= z.
Proof with auto.
  intros. unfold Rmax. destruct (Rle_dec x y)...
Qed.

Lemma Rmin_le x y z: z <= x -> z <= y -> z <= Rmin x y.
Proof with auto.
  intros. unfold Rmin. destruct (Rle_dec x y)...
Qed.

Definition opt_to_bool A (o: option A): bool :=
  match o with Some _ => true | None => false end.
