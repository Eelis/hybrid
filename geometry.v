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

  Definition Point: Set := (R * R)%type.

  Definition Range: Set := { r: R * R | fst r <= snd r }.

  Definition range_left (r: Range): R := fst (proj1_sig r).
  Definition range_right (r: Range): R := snd (proj1_sig r).

  Definition in_range (r: Range) (x: R): Prop :=
    range_left r <= x <= range_right r.

  Definition in_range_dec (r: Range) (x: R):
    decision (in_range r x).
  Proof. unfold in_range. intros. apply and_dec; apply Rle_dec. Defined.

  Definition Square: Set := prod Range Range.

  Definition in_square (p: Point) (s: Square): Prop :=
    in_range (fst s) (fst p) /\ in_range (snd s) (snd p).

  Definition in_square_dec (p: Point) (s: Square):
    decision (in_square p s).
  Proof. intros. apply and_dec; apply in_range_dec. Qed.

  Definition ranges_overlap (a b: Range): Prop :=
    range_left a <= range_right b /\ range_left b <= range_right a.

Hint Resolve Rle_dec.

  Definition ranges_overlap_dec (a b: Range):
    decision (ranges_overlap a b).
  Proof. unfold ranges_overlap. auto. Defined.

  Hint Resolve ranges_overlap_dec.

  Definition squares_overlap (a b: Square): Prop :=
    ranges_overlap (fst a) (fst b) /\ ranges_overlap (snd a) (snd b).

  Definition squares_overlap_dec (a b: Square):
    decision (squares_overlap a b).
  Proof. intros. apply and_dec; apply ranges_overlap_dec. Qed.

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

  Program Definition map_range (f: R -> R) (fi: increasing f) (r: Range): Range
    := (f (fst r), f (snd r)).
  Next Obligation. destruct r. simpl. apply fi. assumption. Defined.

  Definition in_map_range p r (f: R -> R) (i: increasing f): in_range r p ->
    in_range (map_range i r) (f p).
  Proof with auto with real.
    unfold in_range, range_left, range_right.
    destruct r. simpl. intros. destruct H...
  Qed.

  Section mapping.

    Variables (fx: R -> R) (fy: R -> R)
      (fxi: increasing fx) (fyi: increasing fy).

    Definition map_square (s: Square): Square :=
      (map_range fxi (fst s), map_range fyi (snd s)).

    Definition in_map_square p s: in_square p s ->
      in_square (fx (fst p), fy (snd p)) (map_square s).
    Proof with auto with real.
      unfold in_square.
      intros.
      destruct H. destruct s.
      simpl in *.
      split; apply in_map_range...
    Qed.

  End mapping.
