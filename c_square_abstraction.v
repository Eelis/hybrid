Require c_abstraction.
Require c_square_flow_conditions.
Require Import util.
Require Import list_util.
Require Import c_util.
Require Import c_geometry.
Require Import c_monotonic_flow.
Require c_concrete.
Require Import List.
Set Implicit Arguments.
Open Local Scope CR_scope.

Section contents.

  Variables
    (Location Xinterval Yinterval: Set)
    (Location_eq_dec: forall l l': Location, {l=l'}+{l<>l'})
    (Xinterval_eq_dec: forall i i': Xinterval, {i=i'}+{i<>i'})
    (Yinterval_eq_dec: forall i i': Yinterval, {i=i'}+{i<>i'}).

  Definition SquareInterval: Set := prod Xinterval Yinterval.

  Definition SquareInterval_eq_dec (i i': SquareInterval): {i=i'}+{i<>i'}.
    unfold SquareInterval.
    apply (pair_eq_dec Xinterval_eq_dec Yinterval_eq_dec).
  Defined.

  Variables
    (locations: list Location) (locations_complete: forall l, List.In l locations)
    (Xintervals: list Xinterval) (Xintervals_complete: forall i, List.In i Xintervals)
    (Yintervals: list Yinterval) (Yintervals_complete: forall i, List.In i Yintervals)
    (NoDup_Xintervals: NoDup Xintervals)
    (NoDup_Yintervals: NoDup Yintervals).

  Definition squareIntervals: list SquareInterval :=
    flat_map (fun i => map (pair i) Yintervals) Xintervals.

  Lemma squareIntervals_complete: forall s, List.In s squareIntervals.
  Proof with auto.
    destruct s.
    unfold squareIntervals.
    destruct (in_flat_map (fun i => map (pair i) Yintervals) Xintervals (x, y)).
    apply H0.
    exists x.
    split...
    apply in_map...
  Qed.

  Lemma NoDup_squareIntervals: NoDup squareIntervals.
  Proof with auto.
    unfold squareIntervals.
    apply NoDup_flat_map; intros...
      destruct (fst (in_map_iff (pair a) Yintervals x) H1).
      destruct (fst (in_map_iff (pair b) Yintervals x) H2).
      destruct H3. destruct H4.
      subst. inversion H4...
    apply NoDup_map...
    intros. inversion H2...
  Qed.

  Variable initial: Location -> Xinterval -> Yinterval -> bool.

  Variables
    (Xinterval_bounds: forall i: Xinterval, Range)
    (Yinterval_bounds: forall i: Yinterval, Range).

  Definition square (s: SquareInterval): Square :=
    (Xinterval_bounds (fst s), Yinterval_bounds (snd s)).

  Definition in_region (p: Point) (s: SquareInterval): Prop :=
    in_square p (square s).

  Variables
    (xflow yflow: Location -> Flow CRasCSetoid)
    (xflow_inv yflow_inv: Location -> CR -> CR -> Time)
    (xflow_correct: forall l x x', xflow l x (xflow_inv l x x') == x')
    (yflow_correct: forall l y y', yflow l y (yflow_inv l y y') == y')
    (xmono: forall l, mono (xflow l)) (ymono: forall l, mono (yflow l)).

  Let Point := ProdCSetoid CRasCSetoid CRasCSetoid.

  Variables
    (concrete_initial: Location * Point -> Prop)
    (concrete_invariant: Location * Point -> Prop)
    (concrete_invariant_initial: forall p: Location * c_geometry.Point,
      concrete_initial p -> concrete_invariant p)
    (concrete_guard: Location * c_geometry.Point -> Location -> Prop)
    (reset: Location -> Location -> Point -> Point).

  Definition abstract_guard (ls: prod (prod Location SquareInterval) Location): Prop
    := exists p, c_geometry.in_square p (square (snd (fst ls))) /\
	concrete_guard (fst (fst ls), p) (snd ls).

  Definition abstract_invariant (ls: prod Location SquareInterval): Prop :=
    exists p,
      c_geometry.in_square p (square (snd ls)) /\
      concrete_invariant (fst ls, p).

  (* If one's invariants can be expressed as a single square for each
   location, we can decide it for the abstract system by computing
   overlap with regions: *)

  Hypothesis invariant_squares: Location -> Square.
  Hypothesis invariant_squares_correct: forall l p,
    concrete_invariant (l, p) -> in_square p (invariant_squares l).

  Definition invariant_dec (e: Qpos) u: option (~ abstract_invariant u).
  Proof with auto.
    intros.
    apply opt_neg_impl with (squares_overlap (invariant_squares (fst u))
    (square (snd u))).
      intros. destruct H. destruct H.
      apply squares_share_point with x...
    apply weak_decision_to_opt_neg.
    apply (squares_overlap_dec e).
  Defined.

  Variable
    (invariant_decider: forall u, option (~ abstract_invariant u)).

  Definition continuous_transition_condition'
    (l: prod Location (prod SquareInterval SquareInterval)): Prop :=
     c_square_flow_conditions.practical_decideable (xflow_inv (fst l)) (yflow_inv (fst l))
      (xmono (fst l)) (ymono (fst l)) (square (fst (snd l))) (square (snd (snd l)))
    /\ abstract_invariant (fst l, fst (snd l))
    /\ abstract_invariant (fst l, snd (snd l)).
     (* Note how we only check the invariant at s and s', not at
      points in between. *)

  Lemma kaas (e: Qpos): forall u, option (~ continuous_transition_condition' u).
	 (* todo: rename *)
    intros.
    unfold continuous_transition_condition'.
    apply opt_neg_conj.
      apply weak_decision_to_opt_neg.
      apply c_square_flow_conditions.decide_practical.
      exact e.
    apply opt_neg_conj; apply invariant_decider.
  Defined.

  Hypothesis invariant_wd: forall l l', l = l' -> forall p p', p[=]p' ->
    (concrete_invariant (l, p) <-> concrete_invariant (l', p')).

  Hypothesis NoDup_locations: NoDup locations.

  Let concrete_system: c_concrete.System :=
    @c_concrete.Build_System Point Location Location_eq_dec 
      locations locations_complete NoDup_locations concrete_initial
      concrete_invariant concrete_invariant_initial invariant_wd
      (fun l: Location => product_flow (xflow l) (yflow l))
      concrete_guard reset.

  Variables
    (xreset yreset: Location -> Location -> CR -> CR)
    (xresetinc: forall l l', increasing (xreset l l'))
    (yresetinc: forall l l', increasing (yreset l l'))
    (reset_components: forall p l l',
      reset l l' p = (xreset l l' (fst p), yreset l l' (snd p))).

  Variable guard_decider: forall u, option (~ abstract_guard u).

  Definition disc_overestimation (ss: (Location * SquareInterval) *
    (Location * SquareInterval)): Prop :=
    let (source, target) := ss in
    let (l, s) := source in
    let (l', s') := target in
       abstract_invariant (l, s) /\
       abstract_invariant (l', s') /\
       abstract_guard (l, s, l') /\
       squares_overlap
         (map_square (xresetinc l l') (yresetinc l l') (square s))
         (square s').

  Lemma disc_overestimation_dec (e: Qpos) s: option (~ disc_overestimation s).
  Proof with auto.
    intros.
    unfold disc_overestimation.
    destruct s. destruct p. destruct p0.
    apply opt_neg_conj. apply invariant_decider.
    apply opt_neg_conj. apply invariant_decider.
    apply opt_neg_conj. apply guard_decider.
    apply weak_decision_to_opt_neg.
    apply (squares_overlap_dec e).
  Defined.

  Variables
    (absXinterval: CR -> Xinterval)
    (absYinterval: CR -> Yinterval).

  Definition absInterval (p: Point): SquareInterval :=
    (absXinterval (fst p), absYinterval (snd p)).

  Lemma disc_overestimation_valid u:
    c_abstraction.disc_trans_cond concrete_system in_region u ->
    disc_overestimation u.
  Proof with auto.
    intros.
    destruct u.
    destruct H. destruct H. destruct H. destruct H0.
    unfold disc_overestimation.
    destruct p. destruct p0.
    destruct H1. destruct H2. destruct H3.
    simpl @fst in *. simpl @snd in *.
    split.
      unfold abstract_invariant.
      simpl @snd. simpl @fst.
      exists x...
    split.
      unfold abstract_invariant.
      simpl @fst. simpl @snd.
      exists x0...
    split.
      unfold abstract_guard.
      simpl @fst. simpl @snd.
      exists x...
    apply squares_share_point with (reset l l0 x).
      rewrite reset_components.
      apply in_map_square...
    rewrite reset_components in H2.
    rewrite reset_components.
    destruct x0.
    inversion H2.
    unfold in_square.
    simpl @fst. simpl @snd.
    destruct H0.
    destruct H0. destruct H7.
    simpl @fst in *. simpl @snd in *.
    split.
      split; rewrite H5...
    split; rewrite H6...
  Qed.

  Definition disc_decider (e: Qpos) u:
    option (~ c_abstraction.disc_trans_cond concrete_system in_region u)
      := opt_neg_impl (@disc_overestimation_valid u) (disc_overestimation_dec e u).

  Lemma cont_overestimation_valid u:
    c_abstraction.cont_trans_cond concrete_system in_region u ->
    continuous_transition_condition' u.
  Proof with auto.
    intros.
    unfold continuous_transition_condition'.
    destruct u.
    destruct H. destruct H. destruct H.
    destruct H0. destruct H1. destruct H2.
    destruct H2. simpl @fst in *. simpl @snd in *.
    split.
      apply c_square_flow_conditions.ideal_implies_practical_decideable.
          intros.
          apply xflow_correct.
        intros.
        apply yflow_correct.
      unfold c_square_flow_conditions.ideal.
      exists x.
      split...
      exists (proj1_sig x1).
      destruct x1.
      split... apply (CRnonNeg_le_zero x1)...
      simpl proj1_sig in *.
      unfold c_square_flow_conditions.f.
      unfold concrete_system in H3.
      unfold c_concrete.flow in H3.
      simpl bsm in H3.
      unfold in_square.
      destruct H0. destruct H0. destruct H4.
      simpl @fst. simpl @snd.
      destruct x0.
      inversion H3.
      split.
        split; rewrite H7...
      split; rewrite H8...
    split.
      unfold abstract_invariant.
      exists x.
      split...
      simpl @fst.
      apply (c_concrete.invariant_wd concrete_system (refl_equal l) x
       (c_concrete.flow concrete_system l x (' 0)))...
        symmetry.
        apply flow_zero.
      apply H2...
        apply CRle_refl.
      destruct x1...
      apply (CRnonNeg_le_zero x1)...
    unfold abstract_invariant.
    exists x0.
    split...
    simpl @fst.
    apply (c_concrete.invariant_wd concrete_system (refl_equal l) _ x0 H3).
    apply H2.
      destruct x1...
      apply (CRnonNeg_le_zero x1)...
    apply CRle_refl.
  Qed.

  Definition cont_decider (e: Qpos) u: option
    (~ c_abstraction.cont_trans_cond concrete_system in_region u)
      := opt_neg_impl (@cont_overestimation_valid u) (kaas e u).



  (* If one's initial location can be expressed as a simple square
   in a single location, we can decide it for the abstract system
   by checking overlap with regions. *)

  Variables (initial_location: Location) (initial_square: Square)
    (initial_representative:
      forall (p: c_concrete.State concrete_system),
      c_concrete.initial p -> (fst p = initial_location /\
       in_square (snd p) initial_square)).

  Lemma initial_dec u: option
    (~ c_abstraction.initial_condition concrete_system in_region u).
  Proof with auto.
    simpl.
    unfold c_abstraction.initial_condition.
    unfold c_concrete.initial.
    unfold concrete_system.
    destruct u.
    simpl c_concrete.Point.
    destruct (Location_eq_dec l initial_location).
      subst.
      destruct (squares_overlap_dec (1#100) initial_square (square s)).
          exact None.
        apply Some. intro. destruct H.
        simpl @snd in H. simpl @fst in H. destruct H.
        apply n.
        apply squares_share_point with x...
        apply (initial_representative H0).
      exact None.
    apply Some. intro. destruct H. destruct H.
    apply n.
    destruct (initial_representative H0)...
  Defined.

End contents.
