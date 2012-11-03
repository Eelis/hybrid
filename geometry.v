Require Export CRsign.
Require Export CRln.
Require Import Morphisms.
Require Export c_util.
Require Export util.
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

Definition OCRle (x y: optCR): Prop :=
  match x, y with
  | Some l, Some u => l <= u
  | _, _ => True
  end.

Program Definition overestimate_OCRle eps x y: overestimation (OCRle x y) :=
  match x, y with
  | Some l, Some u => overestimate_CRle eps l u
  | _, _ => true
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
Definition OpenRange: Type := sig (uncurry OCRle).

Definition above (c: CR): OpenRange := exist _ (Some c, None) I.
Definition below (c: CR): OpenRange := exist _ (None, Some c) I.

Definition qabove (q: Q): OpenQRange := exist _ (Some q, None) I.
Definition qbelow (q: Q): OpenQRange := exist _ (None, Some q) I.

Program Definition unoqrange (r: OpenQRange): OpenRange
  := (option_map inject_Q_CR (fst r), option_map inject_Q_CR (snd r)).

Next Obligation.
  destruct r as [[[x|] [y|]] H]; auto.
  unfold OCRle, uncurry.
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

Next Obligation. exact I. Qed.

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
  opt_prop (orange_left r) (flip CRle x) /\
  opt_prop (orange_right r) (CRle x).

Instance in_orange_mor: Proper (proj1_sig_relation (product_conj_relation (@st_eq _) (@st_eq _)) ==> @st_eq _ ==> iff) in_orange.
Proof with auto.
  intros [[x y] a] [[x' y'] a'] [H H0] x0 y0 e.
  unfold in_orange, orange_left, orange_right.
  simpl @fst in *. simpl @snd in *.
  unfold opt_prop, flip.
  destruct x; destruct y; destruct x'; destruct y';
    simpl in H, H0; try (elimtype False; assumption);
    try rewrite H; try rewrite H0; try rewrite e; split...
Qed.

Instance in_orange_mor' r: Proper (@st_eq _ ==> iff) (in_orange r).
Proof with auto. revert r. intros [[a b] e] x y H. apply in_orange_mor... split... Qed.

Lemma in_unbounded_range x: in_orange unbounded_range x.
Proof with auto. intros. split; simpl; auto. Qed.

Hint Immediate in_unbounded_range.

Definition overestimate_in_range eps r x: overestimation (in_range r x) :=
  overestimate_conj
    (overestimate_CRle eps (range_left r) x)
    (overestimate_CRle eps x (range_right r)).

Definition overestimate_in_orange eps r x: overestimation (in_orange r x) :=
  overestimate_conj
    (opt_overestimation _ (dep_flip _ (overestimate_CRle eps) x) (orange_left r))
    (opt_overestimation _ (overestimate_CRle eps x) (orange_right r)).

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
  in_range (fst s) (fst p) /\ in_range (snd s) (snd p).

Definition in_osquare (p : Point) (s : OpenSquare) : Prop :=
  in_orange (fst s) (fst p) /\ in_orange (snd s) (snd p).

Lemma in_unbounded_square p: in_osquare p unbounded_square.
Proof with auto. intros. split; apply in_unbounded_range. Qed.

Definition overestimate_in_square eps p s: overestimation (in_square p s) :=
  overestimate_conj
    (overestimate_in_range eps (fst s) (fst p))
    (overestimate_in_range eps (snd s) (snd p)).

Definition overestimate_in_osquare eps p s: overestimation (in_osquare p s) :=
  overestimate_conj
    (overestimate_in_orange eps (fst s) (fst p))
    (overestimate_in_orange eps (snd s) (snd p)).

Definition ranges_overlap (a b: Range): Prop :=
  range_left a <= range_right b /\ range_left b <= range_right a.

Definition oranges_overlap (a b: OpenRange): Prop :=
  match orange_left a, orange_right b with
  | Some l, Some r => l <= r
  | _, _ => True
  end /\
  match orange_left b, orange_right a with
  | Some l, Some r => l <= r
  | _, _ => True
  end.

Hint Immediate CRmax_ub_l.
Hint Immediate CRmax_ub_r.
Hint Immediate CRmin_lb_l.
Hint Immediate CRmin_lb_r.
Hint Immediate CRle_refl.
Hint Resolve CRmax_lub.

Lemma overlapping_oranges_share_point (a b: OpenRange):
  oranges_overlap a b -> exists p, in_orange a p /\ in_orange b p.
Proof with auto.
  revert a b.
  intros [[a b] e] [[c d] f] [H H0].
  unfold in_orange.
  unfold orange_left, orange_right in *.
  simpl @fst in *. simpl @snd in *.
  unfold opt_prop, flip.
  destruct a.
    destruct c; [| eauto].
    exists (CRmax s s0).
    destruct b; destruct d...
  destruct c. eauto.
  destruct b.
    destruct d; [| eauto].
    exists (CRmin s s0)...
  destruct d. eauto.
  exists 0...
Qed.

(* Because of the following Coq bug, we cannot use "overestimator" below:
     http://coq.inria.fr/bugs/show_bug.cgi?id=2122 *)

Definition overestimate_ranges_overlap eps a b: overestimation (ranges_overlap a b) :=
  overestimate_conj
    (overestimate_CRle eps (range_left a) (range_right b))
    (overestimate_CRle eps (range_left b) (range_right a)).

Definition overestimate_oranges_overlap eps a b: overestimation (oranges_overlap a b) :=
  overestimate_conj
    (overestimate_OCRle eps (orange_left a) (orange_right b))
    (overestimate_OCRle eps (orange_left b) (orange_right a)).

Definition squares_overlap (a b: Square): Prop :=
    ranges_overlap (fst a) (fst b) /\ ranges_overlap (snd a) (snd b).

Definition osquares_overlap (a b: OpenSquare): Prop :=
  oranges_overlap (fst a) (fst b) /\
  oranges_overlap (snd a) (snd b).

Definition overestimate_osquares_overlap eps a b: overestimation (osquares_overlap a b) :=
  overestimate_conj
    (overestimate_oranges_overlap eps (fst a) (fst b))
    (overestimate_oranges_overlap eps (snd a) (snd b)).

Definition overestimate_squares_overlap eps (a b: Square): overestimation (squares_overlap a b) :=
  overestimate_conj
    (overestimate_ranges_overlap eps (fst a) (fst b))
    (overestimate_ranges_overlap eps (snd a) (snd b)).

Lemma ranges_share_point a b p: in_range a p -> in_range b p ->
  ranges_overlap a b.
Proof.
  intros [c d] [e f]. split; eapply CRle_trans; eauto.
Qed.

Lemma oranges_share_point a b p: in_orange a p -> in_orange b p ->
  oranges_overlap a b.
Proof with auto.
  revert a b p.
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
  squares_overlap a b.
    (* todo: this also holds in reverse *)
Proof.
  revert a b p.
  intros [a b] [c d] [e f] [g h] [i j].
  split; eapply ranges_share_point; eauto.
Qed.

Lemma osquares_share_point a b p: in_osquare p a -> in_osquare p b ->
  osquares_overlap a b.
Proof.
  revert a b p.
  intros [a b] [c d] [e f] [g h] [i j].
  split; eapply oranges_share_point; eauto.
Qed.

Program Definition map_range (f: CR -> CR) (fi: increasing f) (r: Range): Range :=
  (f (fst (proj1_sig r)), f (snd (proj1_sig r))).

Hint Unfold OCRle.

Program Definition map_orange (f: CR -> CR) (fi: increasing f) (r: OpenRange): OpenRange
  := (option_map f (fst (`r)), option_map f (snd (`r))).
Next Obligation. unfold uncurry. destruct r as [[[a|] [b|]] m]; simpl; auto. Qed.

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
  unfold in_orange, orange_left, orange_right, opt_prop, flip in *.
  destruct x. destruct H.
  destruct s; destruct s0; simpl; auto.
Qed.

Section scaling.

  Variables (s: CR) (H: 0 <= s).

  Hint Resolve CRle_mult.

  Program Definition scale_orange (r: OpenRange): OpenRange :=
    (option_map (CRmult s) (fst (`r)), option_map (CRmult s) (snd (`r))) .
  Next Obligation. unfold uncurry. destruct r as [[[a|] [b|]] h]; simpl; auto. Qed.

  Lemma in_scale_orange p r : in_orange r p ->
    in_orange (scale_orange r) (s * p).
  Proof with simpl; auto.
    intros.
    destruct r.
    unfold in_orange, orange_left, orange_right in *.
    unfold scale_orange.
    destruct x.
    simpl in *.
    unfold opt_prop, flip.
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
