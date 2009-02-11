Require Import Reals.
Require Import List.
Require Import util.
Require concrete.
Require abstract.
Require square_flow_conditions.
Require Import monotonic_flow.
Set Implicit Arguments.
Open Local Scope R_scope.

Section contents.

  (* Suppose we wish to abstract a concrete system.. *)

  Variable concrete_system: concrete.System.

  Let Location := concrete.Location concrete_system.
  Let Point := concrete.Point concrete_system.
    (* convenience *)

  (* We will need decideable equality on the system's locations, as
   well as a set of regions (which can contain Points), and
   exhaustive lists of locations and regions. *)

  Variables
    (Location_eq_dec: forall l l': Location, decision (l=l'))
    (Region: Set) (Region_eq_dec: forall i i': Region, decision (i=i'))
    (in_region: concrete.Point concrete_system -> Region -> Prop)
    (select_region: Point -> Region)
    (locations: list Location) (locations_complete: forall l, List.In l locations)
    (regions: list Region) (regions_complete: forall i, List.In i regions).

  (* We can now define the abstract states: *)

  Let State: Set := prod Location Region.

  Definition State_eq_dec (s s': State): decision (s=s').
    unfold State.
    apply (pair_eq_dec Location_eq_dec Region_eq_dec).
  Defined.

  Definition states: list State :=
    flat_map (fun l => map (pair l) regions) locations.

  Lemma states_complete: forall s, List.In s states.
  Proof with auto.
    destruct s.
    unfold states.
    destruct (in_flat_map (fun l => map (pair l) regions) locations (l, r)).
    apply H0.
    exists l.
    split...
    apply in_map...
  Qed.

  (* Next, we define the "ideal" criteria for when there should be
   transitions between abstract states, as well as for when
   an abstract state should be initial. *)

  Definition initial_condition (l: State): Prop :=
    exists p, in_region p (snd l) /\
    concrete.initial concrete_system (fst l, p).

  Definition continuous_transition_condition
    (l: prod Location (prod Region Region)): Prop :=
    exists p, exists q,
      in_region p (fst (snd l)) /\ in_region q (snd (snd l)) /\
      concrete.cont_trans (fst l, p) (fst l, q).

  Definition discrete_transition_condition
    (l: prod State State): Prop :=
    exists p, exists q,
      in_region p (snd (fst l)) /\ in_region q (snd (snd l)) /\
      concrete.disc_trans (fst (fst l), p) (fst (snd l), q).

  (* These are not decideable, however, so we'll let users specify
   weak deciders for these conditions. *)

  Variables
    (cont_decider: decideable_overestimator continuous_transition_condition)
    (disc_decider: decideable_overestimator discrete_transition_condition)
    (initial_decider: decideable_overestimator initial_condition).

  (* Using these, we can define the abstract transitions.. *)

  Definition canContTrans (l: Location) (s s': Region): bool :=
    unsumbool (doe_dec cont_decider (l, (s, s'))).
  Definition canDiscTrans (s s': State): bool :=
    unsumbool (doe_dec disc_decider (s, s')).

  Definition contTrans (s: State): list State :=
    map (pair (fst s)) (filter (canContTrans (fst s) (snd s)) regions).
  Definition discreteTrans (s: State): list State :=
    filter (canDiscTrans s) states.
      (* a more efficient implementation would grow the graph *)

  Definition initial (s: State): bool :=
    unsumbool (doe_dec initial_decider s).

  (* .. and the abstract system itself: *)

  Definition abstract_system: abstract.System :=
    abstract.Build_System State_eq_dec initial contTrans discreteTrans.

  (* Next, we will show that this abstract system respects the concrete
   system by the following abstraction function: *)

  Definition absFunc (s: concrete.State concrete_system): State :=
    match s with
    | pair l p => pair l (select_region p)
    end.

  Lemma fst_absFunc s: fst (absFunc s) = fst s.
  Proof. destruct s. reflexivity. Qed.

  Hypothesis regions_cover_invariants: forall l p,
    concrete.invariant concrete_system (l, p) ->
    in_region p (select_region p).

  Lemma respectsInit
    (s: concrete.Location concrete_system * concrete.Point concrete_system):
    concrete.initial concrete_system s ->
    abstract.initial abstract_system (absFunc s) = true.
  Proof with auto.
    intros.
    destruct s.
    unfold absFunc.
    simpl.
    unfold initial.
    destruct (doe_dec initial_decider (l, select_region p))...
    elimtype False. apply n. clear n.
    apply doe_correct.
    unfold initial_condition.
    exists p.
    split...
    simpl snd.
    apply regions_cover_invariants with l.
    apply concrete.invariant_initial...
  Qed.

  Lemma respectsDisc (s1 s2: concrete.State concrete_system):
    concrete.disc_trans s1 s2 ->
    In (absFunc s2) (abstract.disc_trans abstract_system (absFunc s1)).
  Proof with auto.
    intros.
    unfold abstract.disc_trans, abstract_system, discreteTrans.
    destruct (filter_In (canDiscTrans (absFunc s1)) (absFunc s2) states).
    apply H1.
    split.
      apply states_complete.
    unfold canDiscTrans.
    destruct (doe_dec disc_decider (absFunc s1, absFunc s2))...
    elimtype False.
    apply n.
    clear n H0 H1.
    apply doe_correct.
    unfold discrete_transition_condition.
    simpl fst. simpl snd.
    destruct H.
    destruct H0.
    destruct H1.
    exists (snd s1).
    exists (snd s2).
    simpl snd.
    repeat rewrite fst_absFunc.
    simpl in H0.
    simpl concrete.Location. simpl concrete.Point.
    split.
      destruct s1. simpl.
      apply regions_cover_invariants with l...
    split.
      destruct s2. simpl.
      apply regions_cover_invariants with l...
    unfold concrete.disc_trans.
    simpl fst. simpl snd.
    destruct s1.
    split...
    split...
    split...
    destruct s2...
  Qed.

  Lemma respectsCont s1 s2: (concrete.cont_trans s1 s2) ->
    In (absFunc s2) (abstract.cont_trans abstract_system (absFunc s1)).
  Proof with auto with real.
    intros.
    unfold abstract_system.
    simpl abstract.cont_trans.
    destruct s1. destruct s2.
    unfold concrete.cont_trans in H.
    unfold contTrans.
    destruct H. destruct H0. destruct H0. simpl in * |-. subst.
    rewrite fst_absFunc.
    simpl fst.
    rename l0 into l.
    simpl absFunc.
    apply in_map.
    simpl fst. simpl snd.
    destruct (filter_In
      (canContTrans l (select_region p)) (select_region (concrete.flow concrete_system l p (proj1_sig x))) regions).
    clear H. apply H1. clear H1.
    split.
      apply regions_complete.
    unfold canContTrans.
    set (@doe_dec (prod Location (prod Region Region))
        continuous_transition_condition cont_decider
        (@pair Location (prod Region Region) l
           (@pair Region Region (select_region p)
              (select_region (concrete.flow concrete_system l p (proj1_sig x)))))).
    simpl.
    destruct d...
    elimtype False. apply n. clear n.
    apply doe_correct.
    unfold continuous_transition_condition.
    simpl fst. simpl snd.
    exists p. exists (concrete.flow concrete_system l p (proj1_sig x)).
    split.
      apply regions_cover_invariants with l.
      rewrite <- (concrete.flow_zero (concrete.flow_flows concrete_system l)) with p.
      destruct x...
    split.
      apply regions_cover_invariants with l.
      destruct x...
    unfold concrete.cont_trans.
    simpl fst. simpl snd.
    split...
    exists x...
  Qed.

  Theorem respect: abstract.Respects abstract_system absFunc.
  Proof abstract.Build_Respects abstract_system absFunc respectsInit respectsDisc respectsCont.

  Lemma result:
    { abstract_system: abstract.System &
    { f: concrete.State concrete_system -> abstract.State abstract_system
    | abstract.Respects abstract_system f } }.
  Proof.
    exists abstract_system.
    exists absFunc.
    apply respect.
  Defined.

End contents.

Section squares.

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
      (discrete_transition_condition concrete_system in_region).
  Proof with auto.
    apply (Build_decideable_overestimator (discrete_transition_condition concrete_system in_region) disc_overestimation).
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
    (continuous_transition_condition concrete_system in_region).
  Proof with auto with real.
    apply (Build_decideable_overestimator (continuous_transition_condition concrete_system in_region)
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

End squares.
