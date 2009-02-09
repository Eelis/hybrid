Require Import Coq.Reals.Reals.
Set Implicit Arguments.
Open Local Scope R_scope.

Definition Time := R.
Definition Duration: Set := { r: R | r >= 0 }.

Program Definition duration_plus (d d': Duration): Duration := d + d'.
Next Obligation.
  destruct d. destruct d'. simpl.
  replace 0 with (0+0).
    apply Rplus_ge_compat; auto.
  field.
Qed.

Program Definition immediately: Duration := 0.
Next Obligation. right. reflexivity. Defined.

Definition pair_eq_dec (X Y: Set)
  (X_eq_dec: forall x x': X, {x=x'}+{x<>x'})
  (Y_eq_dec: forall y y': Y, {y=y'}+{y<>y'})
    (p: prod X Y) (p': prod X Y): {p=p'}+{p<>p'}.
Proof with auto.
  destruct p. destruct p'.
  destruct (X_eq_dec x x0); destruct (Y_eq_dec y y0);
    subst; try auto; right; intro; inversion H...
Defined.

Definition and_dec (P Q: Prop) (Pdec: {P}+{~P}) (Qdec: {Q}+{~Q}):
  {P/\Q}+{~(P/\Q)}.
Proof. tauto. Qed.

Lemma inc_weak (g: Time -> R):
  (forall t t', t < t' -> g t < g t') ->
  (forall t t', t <= t' -> g t <= g t').
Proof with auto with real. intros. destruct H0... right... Qed.

Definition unsumbool (A B: Prop) (sb: {A}+{B}): bool :=
  if sb then true else false.

Definition conj_fst (A B: Prop) (P: A /\ B): A :=
    match P with conj r _ => r end.
  Definition conj_snd (A B: Prop) (P: A /\ B): B :=
    match P with conj _ r => r end.

Section geometry.

  Definition Point: Set := (R * R)%type.

  Inductive Square: Set :=
    MkSquare (x y x' y': R) (xp: x <= x') (yp: y <= y').

  Definition in_square (p: Point) (s: Square): Prop :=
    let (x, y, x', y', _, _) := s in x <= fst p <= x' /\ y <= snd p <= y'.

  Definition in_square_dec (p: Point) (s: Square):
    { in_square p s } + { ~ in_square p s }.
  Proof.
    destruct p. destruct s.
    unfold in_square. simpl.
    destruct (Rle_dec x r); [idtac | right; firstorder].
    destruct (Rle_dec r x'); [idtac | right; firstorder].
    destruct (Rle_dec y r0); [idtac | right; firstorder].
    destruct (Rle_dec r0 y'); [idtac | right; firstorder].
    left. firstorder.
  Qed.

End geometry.
