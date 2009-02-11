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

  Variables
    (Location Xinterval Yinterval: Set)
    (Location_eq_dec: forall l l': Location, {l=l'}+{l<>l'})
    (Xinterval_eq_dec: forall i i': Xinterval, {i=i'}+{i<>i'})
    (Yinterval_eq_dec: forall i i': Yinterval, {i=i'}+{i<>i'})
    (Xinterval_bounds: forall i: Xinterval, { ab: R * R | fst ab <= snd ab })
    (Yinterval_bounds: forall i: Yinterval, { ab: R * R | fst ab <= snd ab }).

  Definition SquareInterval: Set := prod Xinterval Yinterval.

  Definition SquareInterval_eq_dec (i i': SquareInterval): {i=i'}+{i<>i'}.
    unfold SquareInterval.
    apply (pair_eq_dec Xinterval_eq_dec Yinterval_eq_dec).
  Defined.

  Definition square (s: SquareInterval): Square :=
    MkSquare
      (proj2_sig (Xinterval_bounds (fst s)))
      (proj2_sig (Yinterval_bounds (snd s))).

  Let State: Set := prod Location SquareInterval.

  Definition State_eq_dec (s s': State): {s=s'}+{s<>s'}.
    unfold State.
    apply (pair_eq_dec Location_eq_dec SquareInterval_eq_dec).
  Defined.

  Variable initial: Location -> Xinterval -> Yinterval -> bool.

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

  Definition states: list State :=
    flat_map (fun l => map (pair l) squareIntervals) locations.

  Lemma states_complete: forall s, List.In s states.
  Proof with auto.
    destruct s.
    unfold states.
    destruct (in_flat_map (fun l => map (pair l) squareIntervals) locations (l, s)).
    apply H0.
    exists l.
    split...
    apply in_map...
    apply squareIntervals_complete.
  Qed.

  Definition in_range (ab: prod R R) (r: R): Prop :=
    fst ab <= r <= snd ab.

  Definition in_range_dec (ab: prod R R) (r: R):
    {in_range ab r} + {~ in_range ab r}.
  Proof. unfold in_range. intros. apply and_dec; apply Rle_dec. Defined.

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
    (guard: Location * Point -> Location -> Prop)
    (reset: Location -> Location -> Point -> Point).

  Definition abstract_invariant (ls: prod Location SquareInterval): Prop :=
    exists p,
      in_square p (square (snd ls)) /\ concrete_invariant (fst ls, p).

  Variable concrete_invariant_decider:
     decideable_overestimator abstract_invariant.

  Definition condition (l: Location) (s s': SquareInterval): Prop :=
    square_flow_conditions.practical_decideable (xflow_inv l) (yflow_inv l)
      (xmono l) (ymono l) (square s) (square s')
    /\ doe_pred concrete_invariant_decider (l, s)
    /\ doe_pred concrete_invariant_decider (l, s').
     (* Note how we only check the invariant at s and s', not at
      points in between. *)

  Hint Resolve squares_overlap_dec.

  Definition condition_dec l s s': decision (condition l s s').
  Proof with auto.
    intros.
    apply and_dec.
      apply (square_flow_conditions.decide_practical (xflows l) (yflows l) (xflow_inv l) (yflow_inv l)
        (xflow_correct l) (yflow_correct l) (xmono l) (ymono l) (square s) (square s')).
    apply and_dec; apply doe_dec.
  Qed.

  Definition canTrans (l: Location) (s s': SquareInterval): bool :=
    unsumbool (condition_dec l s s').

  Definition contTrans (s: State): list State :=
    map (pair (fst s)) (filter (canTrans (fst s) (snd s)) squareIntervals).

  Definition discreteTrans (s: State): list State := states.
    (* todo *)

  Let concrete_system: concrete.System :=
    @concrete.Build_System Point Location concrete_initial
      concrete_invariant concrete_invariant_initial
      (fun l => concrete.product_flow (xflow l) (yflow l))
      (fun l => concrete.product_flows (xflows l) (yflows l)) guard reset.

  Definition abstract_system: abstract.System :=
    abstract.Build_System State_eq_dec (fun s => initial (fst s) (fst (snd s)) (snd (snd s))) contTrans discreteTrans.

  Variables
    (absXinterval: R -> Xinterval)
    (absYinterval: R -> Yinterval).

  Definition absFunc (s: concrete.State concrete_system):
      State :=
    match s with
    | pair l (pair x y) => pair l (absXinterval x, absYinterval y)
    end.

  Lemma fst_absFunc s: fst (absFunc s) = fst s.
  Proof. destruct s. destruct p. reflexivity. Qed.

  Hypothesis respectsInitH: forall l x y,
    concrete.initial concrete_system (l, (x, y)) ->
      initial l (absXinterval x) (absYinterval y) = true.

  Lemma respectsInit
    (s: concrete.Location concrete_system * concrete.Point concrete_system):
    concrete.initial concrete_system s ->
    abstract.initial abstract_system (absFunc s) = true.
  Proof.
    intros.
    destruct s. destruct p.
    simpl.
    apply respectsInitH.
    assumption.
  Qed.

  Lemma respectsDisc (s1 s2: concrete.State concrete_system):
    concrete.disc_trans s1 s2 ->
    In (absFunc s2) (abstract.disc_trans abstract_system (absFunc s1)).
  Proof with auto.
    intros.
    unfold abstract.disc_trans, abstract_system, discreteTrans.
    apply states_complete.
  Qed. (* currently trivial because discrete transition matrix is complete.
  should become more interesting when we become more picky *)

  Hypothesis squares_cover_invariants: forall l x y,
    concrete.invariant concrete_system (l, (x, y)) ->
    in_square (x, y) (square (absXinterval x, absYinterval y)).

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
    destruct x. rename x into t. rename r into tpos.
    simpl absFunc.
    apply in_map.
    destruct p.
    simpl fst. simpl snd.
    destruct (filter_In
      (canTrans l (absXinterval r, absYinterval r0))
      (absXinterval (xflow l r t),
      absYinterval (yflow l r0 t)) squareIntervals).
    clear H.
    apply H1. clear H1.
    split.
      apply squareIntervals_complete.
    unfold canTrans.
    destruct (condition_dec l (absXinterval r, absYinterval r0)
     (absXinterval (xflow l r t), absYinterval (yflow l r0 t)))...
    elimtype False.
    apply n.
    clear n.
    unfold condition.
    split.
      apply square_flow_conditions.ideal_implies_practical_decideable.
              exact (xflows l).
            exact (yflows l).
          exact (xflow_correct l).
        exact (yflow_correct l).
      unfold square_flow_conditions.ideal.
      exists (r, r0).
      split.
        simpl.
        apply (@squares_cover_invariants l r r0).
        set (H0 0).
        clearbody c.
        rewrite (concrete.flow_zero (concrete.product_flows (xflows l) (yflows l))) in c.
        apply c.
        split...
      exists t.
      split...
      unfold f.
      simpl xflow.
      simpl yflow.
      simpl.
      apply squares_cover_invariants with l.
      apply (H0 t)...
    rename r into x. rename r0 into y.
    split.
      assert (concrete_invariant (l, (x, y))).
        rewrite <- (concrete.flow_zero
          (concrete.product_flows (xflows l) (yflows l)) (x, y))...
      apply doe_correct.
      unfold abstract_invariant.
      exists (x, y).
      split...
      apply (@squares_cover_invariants l x y)...
    apply doe_correct.
    exists (xflow l x t, yflow l y t).
    split.
      simpl snd.
      apply (@squares_cover_invariants l (xflow l x t) (yflow l y t))...
      apply H0...
    apply H0...
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
