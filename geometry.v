Require Export CRsign.
Require Export CRln.
Require Export c_util.
Require Export util.
Require Export dec_overestimator.
Set Implicit Arguments.
Open Local Scope CR_scope.

Definition QRange: Set := sig (uncurry Qle).
Definition Range: Type := sig (fun r: CR * CR => fst r <= snd r).

Program Coercion unqrange (r: QRange): Range := ('(fst r), '(snd r)).
Next Obligation.
  apply <- CRle_Qle.
  destruct r.
  assumption.
Qed.

Hint Immediate CRle_refl.

Program Definition unit_qrange (c: Q): QRange := (c, c).
Next Obligation. apply Qle_refl. Qed.

Program Definition unit_range (c: CR): Range := (c, c).

Section option_setoid.

  Variable s: CSetoid.

  Let cmp (a b: option s): Prop :=
    match a, b with
    | Some x, Some y => x [=] y
    | None, None => True
    | _, _ => False
    end.

  Let ap (a b: option s): CProp :=
    match a, b with
    | Some x, Some y => cs_ap x y
    | None, None => False
    | _, _ => True
    end.

  Let is: is_CSetoid (option s) cmp ap.
  Proof with auto.
    destruct s.
    apply Build_is_CSetoid; intro.
          destruct x.
            simpl.
            apply (ax_ap_irreflexive cs_crr _ _ cs_proof).
          repeat intro...
        destruct x; destruct y; simpl; auto.
        apply (ax_ap_symmetric cs_crr _ cs_ap cs_proof).
      destruct x; destruct y; destruct z; simpl; auto.
      apply (ax_ap_cotransitive cs_crr _ cs_ap cs_proof)...
    repeat intro.
    split; intro.
      destruct x; destruct y; simpl in *; auto.
      apply (ax_ap_tight cs_crr _ cs_ap cs_proof s0 s1)...
    destruct x; destruct y; simpl in *; try intro; auto.
    apply (ax_ap_tight cs_crr _ cs_ap cs_proof s0 s1)...
  Qed.

  Definition option_setoid: CSetoid := Build_CSetoid (option s) cmp ap is.

End option_setoid.

Definition optCR: CSetoid := option_setoid CRasCSetoid.

Definition OCRle (r: optCR * optCR): Prop :=
  match r with
  | (Some l, Some u) => l <= u
  | _ => True
  end.

Definition OQle (r: option Q * option Q): Prop :=
  match r with
  | (Some l, Some u) => (l <= u)%Q
  | _ => True
  end.

Definition CRmin_of_upper_bounds (a b: option CR): option CR :=
  match a, b with
  | None, _ => b
  | _, None => a
  | Some a, Some b => Some (CRmin a b)
  end.

Definition OpenQRange: Set := sig OQle.
Definition OpenRange: Type := sig OCRle.

Program Definition unoqrange (r: OpenQRange): OpenRange
  := (option_map inject_Q (fst r), option_map inject_Q (snd r)).

Next Obligation.
  destruct r as [[[x|] [y|]] H]; auto.
  simpl. apply <- CRle_Qle. assumption.
Qed.

Coercion unoqrange: OpenQRange >-> OpenRange.
  (* Should  be a [Program Coercion], but that's broken in 8.2
   (it has since been fixed). *)

Coercion open_range (r: Range): OpenRange :=
  match r with
  | exist (x, y) H => exist _ (Some x, Some y) H
  end.

Coercion open_qrange (r: QRange): OpenQRange :=
  match r with
  | exist (x, y) H => exist _ (Some x, Some y) H
  end.

Program Definition unbounded_qrange: OpenQRange := (None, None).
Program Definition unbounded_range: OpenRange := (None, None).

Definition qrange_left (r: QRange): Q := fst (proj1_sig r).
Definition qrange_right (r: QRange): Q := snd (proj1_sig r).

Definition range_left (r: Range): CR := fst (proj1_sig r).
Definition range_right (r: Range): CR := snd (proj1_sig r).

Definition oqrange_left (r: OpenQRange): option Q := fst (proj1_sig r).
Definition oqrange_right (r: OpenQRange): option Q := snd (proj1_sig r).

Definition orange_left (r: OpenRange): option CR := fst (proj1_sig r).
Definition orange_right (r: OpenRange): option CR := snd (proj1_sig r).

Definition in_range (r: Range) (x: CR): Prop :=
  range_left r <= x /\ x <= range_right r.

Definition in_orange (r: OpenRange) (x: CR): Prop :=
  match orange_left r with
  | Some l => l <= x
  | None => True
  end /\
  match orange_right r with
  | Some u => x <= u
  | None => True
  end.

Lemma in_orange_wd (r r': OpenRange): fst (`r) [=] fst (`r') -> snd (`r) [=] snd (`r') ->
  forall x x', x == x' -> in_orange r x -> in_orange r' x'.
Proof with auto.
  destruct r. destruct r'.
  unfold in_orange, orange_left, orange_right.
  simpl proj1_sig.
  intros.
  destruct H2.
  destruct x.
  destruct x0.
  simpl @fst in *. simpl @snd in *.
  split.
    destruct s1...
    rewrite <- H1.
    destruct s; [| simpl in H; tauto].
    simpl in H.
    rewrite <- H...
  destruct s2...
  rewrite <- H1.
  destruct s0; [| simpl in H0; tauto].
  simpl in H0.
  rewrite <- H0...
Qed.

Lemma in_unbounded_range x: in_orange unbounded_range x.
Proof with auto. intros. split; simpl; auto. Qed.

Hint Immediate in_unbounded_range.

Definition in_range_dec eps (r : Range) (x : CR) : bool :=
  CRle_dec eps (range_left r, x) && CRle_dec eps (x, range_right r).

Definition in_orange_dec eps (r : OpenRange) (x : CR) : bool :=
  match orange_left r with
  | Some l => CRle_dec eps (l, x)
  | None => true
  end &&
  match orange_right r with
  | Some u => CRle_dec eps (x, u)
  | None => true
  end.

Lemma over_in_range eps r : in_range_dec eps r >=> in_range r.
Proof with auto.
  intros eps r x rxf [rx xr].
  unfold in_range_dec in rxf.
  band_discr; estim (over_CRle eps).
Qed.

Lemma over_in_orange eps r : in_orange_dec eps r >=> in_orange r.
Proof with auto.
  intros eps r.
  apply over_and; repeat intro;
    [destruct (orange_left r) | destruct (orange_right r)];
    try discriminate; apply (over_CRle eps H)...
Qed.

Definition Square: Type := (Range * Range)%type.
Definition OpenQSquare: Set := (OpenQRange * OpenQRange)%type.
Definition OpenSquare: Type := (OpenRange * OpenRange)%type.

Coercion open_square (s: Square): OpenSquare
  := (fst s: OpenRange, snd s: OpenRange).

Coercion unoqsquare (s: OpenQSquare): OpenSquare :=
  (fst s: OpenRange, snd s: OpenRange).

Definition unbounded_square: OpenSquare
  := (unbounded_range, unbounded_range).

Definition Point: CSetoid := ProdCSetoid CRasCSetoid CRasCSetoid.

Definition in_square (p : Point) (s : Square) : Prop :=
  let (px, py) := p in
  let (sx, sy) := s in
    in_range sx px /\ in_range sy py.

Definition in_osquare (p : Point) (s : OpenSquare) : Prop :=
  in_orange (fst s) (fst p) /\
  in_orange (snd s) (snd p).

Lemma in_unbounded_square p: in_osquare p unbounded_square.
Proof with auto. intros. split; apply in_unbounded_range. Qed.

Definition in_square_dec eps (p : Point) (s : Square) : bool :=
  let (px, py) := p in
  let (sx, sy) := s in
    in_range_dec eps sx px && in_range_dec eps sy py.

Definition in_osquare_dec eps (p : Point) (s : OpenSquare) : bool :=
  in_orange_dec eps (fst s) (fst p) &&
  in_orange_dec eps (snd s) (snd p).

Lemma over_in_square eps p : in_square_dec eps p >=> in_square p.
Proof with auto.
  intros eps [px py] [sx sy] ps [inx iny]. simpl in ps.
  band_discr.
  estim (@over_in_range eps sx)...
  estim (@over_in_range eps sy)...
Qed.

Lemma over_in_osquare eps p : in_osquare_dec eps p >=> in_osquare p.
  (* hm, isn't it rather arbitrary that the point is named here
   and not the square? *)
Proof.
  intros.
  apply over_and; repeat intro; apply (over_in_orange eps H); auto.
Qed.

Definition ranges_overlap (r : Range * Range) : Prop :=
  let (a, b) := r in
    range_left a <= range_right b /\ range_left b <= range_right a.

Definition oranges_overlap (r : OpenRange * OpenRange) : Prop :=
  match orange_left (fst r), orange_right (snd r) with
  | Some l, Some r => l <= r
  | _, _ => True
  end /\
  match orange_left (snd r), orange_right (fst r) with
  | Some l, Some r => l <= r
  | _, _ => True
  end.

Hint Immediate CRmax_ub_l.
Hint Immediate CRmax_ub_r.
Hint Immediate CRmin_lb_l.
Hint Immediate CRmin_lb_r.
Hint Immediate CRle_refl.
Hint Resolve CRmax_lub.

Lemma overlapping_oranges_share_point (r: OpenRange * OpenRange):
  oranges_overlap r -> exists p, in_orange (fst r) p /\ in_orange (snd r) p.
Proof with auto.
  intros [[[a e] b] [[c f] d]] [H H0].
  unfold in_orange.
  unfold orange_left, orange_right in *.
  simpl @fst in *. simpl @snd in *.
  destruct a.
    destruct c; [| eauto].
    exists (CRmax s s0).
    destruct e; destruct f...
  destruct c. eauto.
  destruct e.
    destruct f; [| eauto].
    exists (CRmin s s0)...
  destruct f. eauto.
  exists ('0)...
Qed.

Definition ranges_overlap_dec eps (r : Range * Range) : bool :=
  let (a, b) := r in
    CRle_dec eps (range_left a, range_right b) &&
    CRle_dec eps (range_left b, range_right a).

Definition oranges_overlap_dec eps (r: OpenRange * OpenRange): bool :=
  match orange_left (fst r), orange_right (snd r) with
  | Some l, Some r => CRle_dec eps (l, r)
  | _, _ => true
  end &&
  match orange_left (snd r), orange_right (fst r) with
  | Some l, Some r => CRle_dec eps (l, r)
  | _, _ => true
  end.

Lemma over_ranges_overlap eps : ranges_overlap_dec eps >=> ranges_overlap.
Proof.
  intros eps [rx ry] rf [r1 r2].
  unfold ranges_overlap_dec in rf.
  band_discr; estim (over_CRle eps). 
Qed.

Lemma over_oranges_overlap eps: oranges_overlap_dec eps >=> oranges_overlap.
Proof with try discriminate; auto.
  intros.
  apply over_and; repeat intro.
    destruct (orange_left (fst a))...
    destruct (orange_right (snd a))...
    apply (over_CRle eps H)...
  destruct (orange_left (snd a))...
  destruct (orange_right (fst a))...
  apply (over_CRle eps H)...
Qed.

Definition squares_overlap (s : Square * Square) : Prop :=
  let (a, b) := s in
  let (ax, ay) := a in
  let (bx, by) := b in
    ranges_overlap (ax, bx) /\ ranges_overlap (ay, by).

Definition osquares_overlap (s: OpenSquare * OpenSquare): Prop :=
  oranges_overlap (fst (fst s), fst (snd s)) /\
  oranges_overlap (snd (fst s), snd (snd s)).

Definition squares_overlap_dec eps (s : Square * Square) : bool :=
  let (a, b) := s in
  let (x1, y1) := a in
  let (x2, y2) := b in
    ranges_overlap_dec eps (x1, x2) && ranges_overlap_dec eps (y1, y2).

Definition osquares_overlap_dec eps (s : OpenSquare * OpenSquare): bool :=
  oranges_overlap_dec eps (fst (fst s), fst (snd s)) &&
  oranges_overlap_dec eps (snd (fst s), snd (snd s)).

Lemma over_squares_overlap eps : squares_overlap_dec eps >=> squares_overlap.
Proof.
  intros eps [[x1 y1] [x2 y2]] so [o1 o2].
  unfold squares_overlap_dec in so.
  band_discr; estim (over_ranges_overlap eps).
Qed.

Lemma over_osquares_overlap eps: osquares_overlap_dec eps >=> osquares_overlap.
Proof.
  intros.
  apply over_and; repeat intro;
   apply (over_oranges_overlap eps H); auto.
Qed.

Lemma ranges_share_point a b p: in_range a p -> in_range b p ->
  ranges_overlap (a, b).
Proof.
  intros a b p [c d] [e f]. split; eapply CRle_trans; eauto.
Qed.

Lemma oranges_share_point a b p: in_orange a p -> in_orange b p ->
  oranges_overlap (a, b).
Proof with auto.
  intros [[a b] c] [[d e] f] p [g h] [i j].
  unfold oranges_overlap, orange_left, orange_right in *.
  simpl @fst in *. simpl @snd in *.
  split.
    destruct a...
    destruct e...
    eapply CRle_trans; eauto.
  destruct d...
  destruct b...
  eapply CRle_trans; eauto.
Qed.

Lemma squares_share_point a b p: in_square p a -> in_square p b ->
  squares_overlap (a, b).
    (* todo: this also holds in reverse *)
Proof.
  intros [a b] [c d] [e f] [g h] [i j].
  split; eapply ranges_share_point; eauto.
Qed.

Lemma osquares_share_point a b p: in_osquare p a -> in_osquare p b ->
  osquares_overlap (a, b).
Proof.
  intros [a b] [c d] [e f] [g h] [i j].
  split; eapply oranges_share_point; eauto.
Qed.

Program Definition map_range (f: CR -> CR) (fi: increasing f) (r: Range): Range :=
  (f (fst (proj1_sig r)), f (snd (proj1_sig r))).

Next Obligation. destruct r. apply fi. assumption. Qed.

Program Definition map_orange (f: CR -> CR) (fi: increasing f) (r: OpenRange): OpenRange
  := (option_map f (fst (`r)), option_map f (snd (`r))).

Next Obligation. destruct r as [[[a|] [b|]] m]; simpl; auto. Qed.

Definition in_map_range p r (f: CR -> CR) (i: increasing f): in_range r p ->
  in_range (map_range i r) (f p).
Proof with auto with real.
  unfold in_range, range_left, range_right.
  destruct r. simpl. intros. destruct H...
Qed.

Definition in_map_orange p r (f: CR -> CR) (i: increasing f): in_orange r p ->
  in_orange (map_orange i r) (f p).
Proof.
  intros.
  destruct r.
  unfold in_orange, orange_left, orange_right in *.
  destruct x. destruct H.
  destruct s; destruct s0; simpl; auto.
Qed.

Section scaling.

  Variables (s: CR) (H: '0 <= s).

  Hint Resolve CRle_mult.

  Program Definition scale_orange (r: OpenRange): OpenRange :=
    (option_map (CRmult s) (fst (`r)), option_map (CRmult s) (snd (`r))) .
  Next Obligation. destruct r as [[[a|] [b|]] h]; simpl; auto. Qed.

  Lemma in_scale_orange p r : in_orange r p ->
    in_orange (scale_orange r) (s * p).
  Proof with simpl; auto.
    intros.
    destruct r.
    unfold in_orange, orange_left, orange_right in *.
    unfold scale_orange.
    destruct x.
    simpl in *.
    destruct H0.
    destruct s0; destruct s1...
  Qed.

End scaling.

Section mapping.

  Variables (fx: CR -> CR) (fy: CR -> CR)
    (fxi: increasing fx) (fyi: increasing fy).

  Definition map_square (s: Square): Square :=
    (map_range fxi (fst s), map_range fyi (snd s)).

  Definition map_osquare (s: OpenSquare): OpenSquare :=
    (map_orange fxi (fst s), map_orange fyi (snd s)).

  Definition in_map_square p s: in_square p s ->
    in_square (fx (fst p), fy (snd p)) (map_square s).
  Proof with auto.
    unfold in_square.
    intros. destruct p. destruct s.
    destruct H.
    simpl in *.
    split; apply in_map_range...
  Qed.

  Definition in_map_osquare p s: in_osquare p s ->
    in_osquare (fx (fst p), fy (snd p)) (map_osquare s).
  Proof with auto.
    unfold in_osquare.
    intros. destruct p. destruct s.
    destruct H.
    simpl in *.
    split; apply in_map_orange...
  Qed.

End mapping.
