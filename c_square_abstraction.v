Require c_abstraction.
Require c_square_flow_conditions.
Require Import util.
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
    (Yintervals: list Yinterval) (Yintervals_complete: forall i, List.In i Yintervals).

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

  Let concrete_system: c_concrete.System :=
    @c_concrete.Build_System Point Location Location_eq_dec 
      locations locations_complete concrete_initial
      concrete_invariant concrete_invariant_initial invariant_wd
      (fun l: Location => product_flow (xflow l) (yflow l))
      concrete_guard reset.

  Variables
    (xreset yreset: Location -> Location -> CR -> CR)
    (xresetinc: forall l l', increasing (xreset l l'))
    (yresetinc: forall l l', increasing (yreset l l'))
    (reset_components: forall p l l',
      reset l l' p = (xreset l l' (fst p), yreset l l' (snd p))).
(*
  Variables
    (guard_squares: Location -> Location -> option Square)
    (guard_squares_correct: forall l l' p,
      concrete_guard l l' p -> squares_overlap (guard_squares l l') (abs p)).

  Definition make_guard_decider: forall u, option (~ abstract_guard u).
  Proof with auto.
    intros.
    destruct u. destruct p.
    set (guard_squares l0 l).
  *)  

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
    simpl fst in *. simpl snd in *.
    split.
      unfold abstract_invariant.
      simpl snd. simpl fst.
      exists x...
    split.
      unfold abstract_invariant.
      simpl fst. simpl snd.
      exists x0...
    split.
      unfold abstract_guard.
      simpl fst. simpl snd.
      exists x...
    apply squares_share_point with (reset l l0 x).
      rewrite reset_components.
      apply in_map_square...
    rewrite reset_components in H2.
    rewrite reset_components.
    destruct x0.
    inversion H2.
    unfold in_square.
    simpl fst. simpl snd.
    destruct H0.
    destruct H0. destruct H7.
    simpl fst in *. simpl snd in *.
    split.
      split; rewrite H5...
    split; rewrite H6...
  Qed.


  Definition disc_decider (e: Qpos) u:
    option (~ c_abstraction.disc_trans_cond concrete_system in_region u).
  Proof.
    intros.
    apply opt_neg_impl with (disc_overestimation u).
      apply (disc_overestimation_dec e).
    apply disc_overestimation_valid.
  Defined.

  Lemma cont_overestimation_valid u:
    c_abstraction.cont_trans_cond concrete_system in_region u ->
    continuous_transition_condition' u.
  Proof with auto.
    intros.
    unfold continuous_transition_condition'.
    destruct u.
    destruct H. destruct H. destruct H.
    destruct H0. destruct H1. destruct H2.
    destruct H2. simpl fst in *. simpl snd in *.
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
      simpl fst. simpl snd.
      destruct x0.
      inversion H3.
      split.
        split; rewrite H7...
      split; rewrite H8...
    split.
      unfold abstract_invariant.
      exists x.
      split...
      simpl fst.
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
    simpl fst.
    apply (c_concrete.invariant_wd concrete_system (refl_equal l) _ x0 H3).
    apply H2.
      destruct x1...
      apply (CRnonNeg_le_zero x1)...
    apply CRle_refl.
  Qed.

  Lemma cont_decider (e: Qpos): forall u, option
    (~ c_abstraction.cont_trans_cond concrete_system in_region u).
  Proof.
    intros.
    apply opt_neg_impl with (continuous_transition_condition' u).
      apply (kaas e).
    apply cont_overestimation_valid.
  Defined.

End contents.
