Require Export CRsign.
Require Export CRln.
Require Export c_util.
Require Export util.
Require Export dec_overestimator.
Set Implicit Arguments.
Open Local Scope CR_scope.

Definition Range: Type := { r: CR * CR | fst r <= snd r }.

Definition range_left (r: Range): CR := fst (proj1_sig r).
Definition range_right (r: Range): CR := snd (proj1_sig r).

Definition in_range (r: Range) (x: CR): Prop :=
  range_left r <= x /\ x <= range_right r.

Definition in_range_dec eps (r : Range) (x : CR) : bool :=
  CRle_dec eps (range_left r, x) && CRle_dec eps (x, range_right r).

Lemma over_in_range eps r : in_range_dec eps r >=> in_range r.
Proof with auto.
  intros eps r x rxf [rx xr].
  unfold in_range_dec in rxf.
  band_discr; estim (over_CRle eps).
Qed.

Definition Square: Type := (Range * Range)%type.

Definition Point: Type := ProdCSetoid CRasCSetoid CRasCSetoid.

Definition in_square (p : Point) (s : Square) : Prop :=
  let (px, py) := p in
  let (sx, sy) := s in
    in_range sx px /\ in_range sy py.

Definition in_square_dec eps (p : Point) (s : Square) : bool :=
  let (px, py) := p in
  let (sx, sy) := s in
    in_range_dec eps sx px && in_range_dec eps sy py.

Lemma over_in_square eps p : in_square_dec eps p >=> in_square p.
Proof with auto.
  intros eps [px py] [sx sy] ps [inx iny]. simpl in ps.
  band_discr.
  estim (@over_in_range eps sx)...
  estim (@over_in_range eps sy)...
Qed.

Definition ranges_overlap (r : Range * Range) : Prop :=
  let (a, b) := r in
    range_left a <= range_right b /\ range_left b <= range_right a.

Definition ranges_overlap_dec eps (r : Range * Range) : bool :=
  let (a, b) := r in
    CRle_dec eps (range_left a, range_right b) &&
    CRle_dec eps (range_left b, range_right a).

Lemma over_ranges_overlap eps : ranges_overlap_dec eps >=> ranges_overlap.
Proof.
  intros eps [rx ry] rf [r1 r2].
  unfold ranges_overlap_dec in rf.
  band_discr; estim (over_CRle eps). 
Qed.

Definition squares_overlap (s : Square * Square) : Prop :=
  let (a, b) := s in
  let (ax, ay) := a in
  let (bx, by) := b in
    ranges_overlap (ax, bx) /\ ranges_overlap (ay, by).

Definition squares_overlap_dec eps (s : Square * Square) : bool :=
  let (a, b) := s in
  let (x1, y1) := a in
  let (x2, y2) := b in
    ranges_overlap_dec eps (x1, x2) && ranges_overlap_dec eps (y1, y2).

Lemma over_squares_overlap eps : squares_overlap_dec eps >=> squares_overlap.
Proof.
  intros eps [[x1 y1] [x2 y2]] so [o1 o2].
  unfold squares_overlap_dec in so.
  band_discr; estim (over_ranges_overlap eps).
Qed.

Lemma squares_share_point a b p: in_square p a -> in_square p b ->
  squares_overlap (a, b).
    (* todo: this also holds in reverse *)
Proof.
  destruct a. destruct b. destruct p. simpl. 
  unfold in_range. intros. destruct_and.
  repeat split; eapply CRle_trans; eauto.
Qed.

Definition map_range (f: CR -> CR) (fi: increasing f) (r: Range): Range.
  intros.
  exists (f (fst (proj1_sig r)), f (snd (proj1_sig r))).
  simpl.
  apply fi.
  destruct r.
  assumption.
Defined. (* for some reason Program Definition won't work here.. *)

Definition in_map_range p r (f: CR -> CR) (i: increasing f): in_range r p ->
  in_range (map_range i r) (f p).
Proof with auto with real.
  unfold in_range, range_left, range_right.
  destruct r. simpl. intros. destruct H...
Qed.

Section mapping.

  Variables (fx: CR -> CR) (fy: CR -> CR)
    (fxi: increasing fx) (fyi: increasing fy).

  Definition map_square (s: Square): Square :=
    (map_range fxi (fst s), map_range fyi (snd s)).

  Definition in_map_square p s: in_square p s ->
    in_square (fx (fst p), fy (snd p)) (map_square s).
  Proof with auto with real.
    unfold in_square.
    intros. destruct p. destruct s.
    destruct H. 
    simpl in *.
    split; apply in_map_range...
  Qed.

End mapping.
