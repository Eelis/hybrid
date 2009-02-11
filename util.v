Require Import Coq.Reals.Reals.
Require Import Fourier.
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
    decision (in_square p s).
  Proof.
    destruct p. destruct s. unfold decision.
    unfold in_square. simpl.
    destruct (Rle_dec x r); [idtac | right; firstorder].
    destruct (Rle_dec r x'); [idtac | right; firstorder].
    destruct (Rle_dec y r0); [idtac | right; firstorder].
    destruct (Rle_dec r0 y'); [idtac | right; firstorder].
    left. firstorder.
  Qed.

  Definition ranges_overlap (a b: prod R R): Prop :=
    fst a <= snd b /\ fst b <= snd a.

Hint Resolve Rle_dec.

  Definition ranges_overlap_dec (a b: prod R R):
    decision (ranges_overlap a b).
  Proof. unfold ranges_overlap. auto. Defined.

  Hint Resolve ranges_overlap_dec.

  Definition squares_overlap (a b: Square): Prop :=
    let (ax, ay, ax', ay', _, _) := a in
    let (bx, by, bx', by', _, _) := b in
      ranges_overlap (ax, ax') (bx, bx') /\
      ranges_overlap (ay, ay') (by, by').

  Definition squares_overlap_dec (a b: Square):
    decision (squares_overlap a b).
  Proof.
    destruct a. destruct b. unfold squares_overlap. auto.
  Defined.

  Lemma squares_share_point a b p: in_square p a -> in_square p b ->
    squares_overlap a b.
      (* todo: this also holds in reverse *)
  Proof with auto.
    unfold in_square, squares_overlap, ranges_overlap.
    destruct a. destruct b. destruct p.
    simpl.
    intros.
    destruct H. destruct H. destruct H1.
    destruct H0. destruct H0. destruct H4.
    split; split; fourier.
  Qed.

  Hint Resolve squares_overlap_dec.

End geometry.
