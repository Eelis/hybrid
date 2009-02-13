Require abstraction.
Require square_flow_conditions.
Require Import monotonic_flow.
Require Import Reals.
Require Import util.
Require Import geometry.
Require Import List.
Set Implicit Arguments.
Open Local Scope R_scope.

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
    (Xinterval_bounds: forall i: Xinterval, { ab: R * R | fst ab <= snd ab })
    (Yinterval_bounds: forall i: Yinterval, { ab: R * R | fst ab <= snd ab }).

  Definition square (s: SquareInterval): Square :=
    MkSquare
      (proj2_sig (Xinterval_bounds (fst s)))
      (proj2_sig (Yinterval_bounds (snd s))).

  Definition in_region (p: Point) (s: SquareInterval): Prop :=
    in_square p (square s).

  Variables
    (xflow yflow: Location -> R -> Time -> R)
    (xflow_inv yflow_inv: Location -> R -> R -> Time)
    (xflows: forall l, concrete.flows (xflow l))
    (yflows: forall l, concrete.flows (yflow l))
    (xflow_correct: forall l x x', xflow l x (xflow_inv l x x') = x')
    (yflow_correct: forall l y y', yflow l y (yflow_inv l y y') = y')
    (xmono: forall l, mono (xflow l)) (ymono: forall l, mono (yflow l)).

  Variables
    (concrete_initial: Location * Point -> Prop)
    (concrete_invariant: Location * Point -> Prop)
    (concrete_invariant_initial: forall p: Location * Point,
      concrete_initial p -> concrete_invariant p)
    (concrete_guard: Location * Point -> Location -> Prop)
    (reset: Location -> Location -> Point -> Point).

  Definition abstract_guard (ls: prod (prod Location SquareInterval) Location): Prop
    := exists p, in_square p (square (snd (fst ls))) /\
	concrete_guard (fst (fst ls), p) (snd ls).

  Definition abstract_invariant (ls: prod Location SquareInterval): Prop :=
    exists p,
      in_square p (square (snd ls)) /\ concrete_invariant (fst ls, p).

  Variables
    (invariant_decider: decideable_overestimator abstract_invariant).

  Definition continuous_transition_condition'
    (l: prod Location (prod SquareInterval SquareInterval)): Prop :=
     square_flow_conditions.practical_decideable (xflow_inv (fst l)) (yflow_inv (fst l))
      (xmono (fst l)) (ymono (fst l)) (square (fst (snd l))) (square (snd (snd l)))
    /\ doe_pred invariant_decider (fst l, fst (snd l))
    /\ doe_pred invariant_decider (fst l, snd (snd l)).
     (* Note how we only check the invariant at s and s', not at
      points in between. *)

  Let concrete_system: concrete.System :=
    @concrete.Build_System Point Location concrete_initial
      concrete_invariant concrete_invariant_initial
      (fun l => concrete.product_flow (xflow l) (yflow l))
      (fun l => concrete.product_flows (xflows l) (yflows l)) concrete_guard reset.

  Variables
    (xreset yreset: Location -> Location -> R -> R)
    (xresetinc: forall l l', increasing (xreset l l'))
    (yresetinc: forall l l', increasing (yreset l l'))
    (reset_components: forall p l l',
      reset l l' p = (xreset l l' (fst p), yreset l l' (snd p))).

  Variable guard_decider: decideable_overestimator abstract_guard.

  Definition disc_overestimation (ss: (Location * SquareInterval) *
    (Location * SquareInterval)): Prop :=
    let (source, target) := ss in
    let (l, s) := source in
    let (l', s') := target in
       doe_pred invariant_decider (l, s) /\
       doe_pred invariant_decider (l', s') /\
       doe_pred guard_decider (l, s, l') /\
       squares_overlap
         (map_square (xresetinc l l') (yresetinc l l') (square s))
         (square s').

  Lemma make_disc_decider:
    decideable_overestimator
      (abstraction.discrete_transition_condition concrete_system in_region).
  Proof with auto.
    apply (Build_decideable_overestimator (abstraction.discrete_transition_condition concrete_system in_region) disc_overestimation).
      intros.
      unfold disc_overestimation.
      destruct a. destruct p. destruct p0.
      apply and_dec. apply doe_dec.
      apply and_dec. apply doe_dec.
      apply and_dec. apply doe_dec.
      apply squares_overlap_dec.
    intros.
    destruct a.
    destruct H.
    destruct H.
    unfold disc_overestimation.
    destruct H. destruct H0.
    destruct p. destruct p0.
    destruct H1. destruct H2. destruct H3.
    simpl fst in *. simpl snd in *.
    subst x0.
    split.
      apply doe_correct.
      unfold abstract_invariant.
      exists x...
    split.
      apply doe_correct.
      unfold abstract_invariant.
      exists (reset l l0 x)...
    split.
      apply doe_correct.
      unfold abstract_guard.
      exists x...
    apply squares_share_point with (reset l l0 x)...
    rewrite reset_components.
    rewrite reset_components in H0.
    apply in_map_square...
  Qed.

  Hint Resolve squares_overlap_dec.

  Variables
    (absXinterval: R -> Xinterval)
    (absYinterval: R -> Yinterval).

  Definition absInterval (p: Point): SquareInterval :=
    (absXinterval (fst p), absYinterval (snd p)).

  Lemma cont_decider: decideable_overestimator
    (abstraction.continuous_transition_condition concrete_system in_region).
  Proof with auto with real.
    apply (Build_decideable_overestimator (abstraction.continuous_transition_condition concrete_system in_region)
      continuous_transition_condition').
      intros.
      unfold continuous_transition_condition'.
      apply and_dec.
        apply (square_flow_conditions.decide_practical (xflows (fst a)) (yflows (fst a)) (xflow_inv (fst a)) (yflow_inv (fst a))
          (xflow_correct (fst a)) (yflow_correct (fst a)) (xmono (fst a)) (ymono (fst a)) (square (fst (snd a))) (square (snd (snd a)))).
      apply and_dec; apply doe_dec.
    intros.
    unfold continuous_transition_condition'.
    destruct H. destruct H. destruct H.
    destruct H0. destruct H1. destruct H2.
    destruct H2. simpl fst in *. simpl snd in *.
    subst x0.
    split.
      destruct a. simpl fst. simpl snd.
      apply square_flow_conditions.ideal_implies_practical_decideable.
              exact (xflows l).
            exact (yflows l).
          exact (xflow_correct l).
        exact (yflow_correct l).
      unfold square_flow_conditions.ideal.
      exists x.
      split...
      exists (proj1_sig x1).
      destruct x1.
      split...
    clear H1.
    split.
      apply doe_correct.
      unfold abstract_invariant.
      simpl fst. simpl snd.
      exists x.
      split...
      rewrite <- (concrete.flow_zero (concrete.flow_flows concrete_system (fst a))) with x.
      apply H2. destruct x1...
    apply doe_correct.
    destruct a. simpl in *.
    unfold abstract_invariant.
    simpl fst. simpl snd.
    exists (concrete.product_flow (xflow l) (yflow l) x (proj1_sig x1)).
    split...
    apply H2. destruct x1...
  Qed.

End contents.
