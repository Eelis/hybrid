Require Export CRsign.
Require Export CRln.
Require Export c_util.
Require Export util.
Set Implicit Arguments.
Open Local Scope CR_scope.

Lemma CR_epsilon_sign_dec_neg x e: CR_epsilon_sign_dec e x = Lt -> CRneg x.
Proof.
  intros.
  apply CRneg_char with e.
  unfold CR_epsilon_sign_dec in H.
  destruct (QMinMax.Qle_total (approximate x e) (2 * e)).
    destruct (QMinMax.Qle_total (- (2) * e) (approximate x e)).
      discriminate.
    assumption.
  discriminate.
Defined.

Lemma proper_sign_dec (e: Qpos) (x: CR): option (sum (CRpos x) (CRneg x)).
Proof.
  intros.
  set (CR_epsilon_sign_dec e x).
  unfold CR_epsilon_sign_dec in c.
  destruct (QMinMax.Qle_total (approximate x e) (2 * e)).
    destruct (QMinMax.Qle_total (- (2) * e) (approximate x e)).
      exact None.
    apply Some. right. apply CRneg_char with e. assumption.
  apply Some. left. apply CRpos_char with e. assumption.
Defined.

Lemma weak_lt_dec (e: Qpos) (x y: CR): option (sum (x < y) (y < x)).
Proof.
  unfold CRlt.
  intros.
  destruct (proper_sign_dec e (y - x)).
    destruct s.
      apply Some. left. assumption.
    apply Some. right.
    apply t6.
    assumption.
  exact None.
Defined.

Lemma weak_le_dec (e: Qpos) (x y: CR): weak_decision (x <= y).
Proof.
  intros.
  destruct (weak_lt_dec e x y).
    destruct s.
      apply definitely.
      apply CRlt_le.
      assumption.
    apply definitely_not.
    intro.
    apply (def_leEq _ _ _ _ _ CRisCOrdField x y); assumption.
  apply indeterminate.
Defined.

Definition one_way_weak_lt_dec (e: Qpos) (x y: CR): option (x < y) :=
  match weak_lt_dec e x y with
  | Some (inl c) => Some c
  | _ => None
  end.

Definition Range: Type := { r: CR * CR | fst r <= snd r }.

Definition range_left (r: Range): CR := fst (proj1_sig r).
Definition range_right (r: Range): CR := snd (proj1_sig r).

Definition in_range (r: Range) (x: CR): Prop :=
  range_left r <= x /\ x <= range_right r.

Definition in_range_dec (e: Qpos) (r: Range) (x: CR):
    weak_decision (in_range r x) :=
  weak_and_dec (weak_le_dec e (range_left r) x) (weak_le_dec e x (range_right r)).

Definition Square: Type := prod Range Range.

Definition Point: Type := ProdCSetoid CRasCSetoid CRasCSetoid.

Definition in_square (p: Point) (s: Square): Prop :=
  in_range (fst s) (fst p) /\ in_range (snd s) (snd p).

Definition in_square_dec (p: Point) (s: Square) (e: Qpos):
    weak_decision (in_square p s) :=
  weak_and_dec (in_range_dec e (fst s) (fst p)) (in_range_dec e (snd s) (snd p)).

Definition ranges_overlap (a b: Range): Prop :=
  range_left a <= range_right b /\ range_left b <= range_right a.

Definition ranges_overlap_dec e a b: weak_decision (ranges_overlap a b) :=
  weak_and_dec
    (weak_le_dec e (range_left a) (range_right b))
    (weak_le_dec e (range_left b) (range_right a)).

Definition squares_overlap (a b: Square): Prop :=
  ranges_overlap (fst a) (fst b) /\ ranges_overlap (snd a) (snd b).

Definition squares_overlap_dec e (a b: Square):
    weak_decision (squares_overlap a b) :=
  weak_and_dec
    (ranges_overlap_dec e (fst a) (fst b))
    (ranges_overlap_dec e (snd a) (snd b)).

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
  split.
    split; apply CRle_trans with c...
  split; apply CRle_trans with c0...
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
      intros.
      destruct H. destruct s.
      simpl in *.
      split; apply in_map_range...
    Qed.

  End mapping.


