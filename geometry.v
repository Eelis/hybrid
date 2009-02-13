Require Import Coq.Reals.Reals.
Require Import Fourier.
Require Import util.
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

Lemma inc_weak (g: Time -> R):
  (forall t t', t < t' -> g t < g t') ->
  (forall t t', t <= t' -> g t <= g t').
Proof with auto with real. intros. destruct H0... right... Qed.

  Definition Point: Set := (R * R)%type.

  Definition in_range (ab: prod R R) (r: R): Prop :=
    fst ab <= r <= snd ab.

  Definition in_range_dec (ab: prod R R) (r: R):
    decision (in_range ab r).
  Proof. unfold in_range. intros. apply and_dec; apply Rle_dec. Defined.

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

  Section mapping.

    Variables (fx: R -> R) (fy: R -> R)
      (fxi: increasing fx) (fyi: increasing fy).

    Definition map_square (s: Square): Square.
      intros.
      destruct s.
      exact (MkSquare (fxi xp) (fyi yp)).
    Defined.

    Definition in_map_square p s: in_square p s ->
      in_square (fx (fst p), fy (snd p)) (map_square s).
    Proof with auto with real.
      intros.
      destruct s.
      simpl. simpl in H.
      destruct H. destruct H. destruct H0...
    Qed.

  End mapping.
