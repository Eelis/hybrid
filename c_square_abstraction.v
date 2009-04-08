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

Open Scope CR_scope.

Section contents.

  Variables
    (Location Xinterval Yinterval: Set)
    (Location_eq_dec: forall l l': Location, decision (l = l'))
    (Xinterval_eq_dec: forall i i': Xinterval, decision (i = i'))
    (Yinterval_eq_dec: forall i i': Yinterval, decision (i = i')).

  Definition SquareInterval: Set := (Xinterval * Yinterval)%type.

  Definition SquareInterval_eq_dec (i i': SquareInterval): decision (i = i').
    dec_eq. apply Yinterval_eq_dec. apply Xinterval_eq_dec.
  Defined.

  (* FIXME, abstract the triple, list + its completness + NoDups *)
  Variables
    (locations: list Location) 
    (locations_complete: forall l, List.In l locations)
    (Xintervals: list Xinterval) 
    (Xintervals_complete: forall i, List.In i Xintervals)
    (Yintervals: list Yinterval) 
    (Yintervals_complete: forall i, List.In i Yintervals)
    (NoDup_Xintervals: NoDup Xintervals)
    (NoDup_Yintervals: NoDup Yintervals).

  Definition squareIntervals: list SquareInterval :=
    flat_map (fun i => map (pair i) Yintervals) Xintervals.

  Lemma squareIntervals_complete: forall s, List.In s squareIntervals.
  Proof with auto.
    destruct s.
    destruct (in_flat_map (fun i => map (pair i) Yintervals) Xintervals (x, y)).
    apply H0.
    exists x.
    split...
    apply in_map...
  Qed.

  Lemma NoDup_squareIntervals: NoDup squareIntervals.
  Proof with auto.
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
    (Xinterval_range: Xinterval -> OpenRange)
    (Yinterval_range: Yinterval -> OpenRange).

  Definition square (s: SquareInterval): OpenSquare :=
    (Xinterval_range (fst s), Yinterval_range (snd s)).

  Definition in_region (p: Point) (s: SquareInterval): Prop :=
    in_osquare p (square s).

  Variables
    (xflow yflow: Location -> Flow CRasCSetoid)
    (xflow_invr yflow_invr: Location -> OpenRange -> OpenRange -> OpenRange)
    (xflow_invr_correct: forall l, range_flow_inv_spec (xflow l) (xflow_invr l))
    (yflow_invr_correct: forall l, range_flow_inv_spec (yflow l) (yflow_invr l)).

  Let Point := ProdCSetoid CRasCSetoid CRasCSetoid.

  Variables
    (concrete_initial: Location * Point -> Prop)
    (concrete_invariant: Location * Point -> Prop)
    (concrete_invariant_initial: forall p: Location * c_geometry.Point,
      concrete_initial p -> concrete_invariant p)
    (concrete_guard: Location * c_geometry.Point -> Location -> Prop)
    (reset: Location -> Location -> Point -> Point).

  Definition abstract_guard (ls: (Location * SquareInterval) * Location): Prop
    := exists p, c_geometry.in_osquare p (square (snd (fst ls))) /\
	concrete_guard (fst (fst ls), p) (snd ls).

  Definition abstract_invariant (ls: Location * SquareInterval): Prop :=
    exists p,
      c_geometry.in_osquare p (square (snd ls)) /\
      concrete_invariant (fst ls, p).

  (* If one's invariants can be expressed as a single square for each
   location, we can decide it for the abstract system by computing
   overlap with regions: *)

  Hypothesis invariant_squares: Location -> OpenSquare.
  Hypothesis invariant_squares_correct: forall l p,
    concrete_invariant (l, p) -> in_osquare p (invariant_squares l).

Ltac bool_contradict id :=
  match goal with
  | id: ?X = false |- _ =>
      absurd (X = true); [congruence | idtac]
  | id: ?X = true |- _ =>
      absurd (X = false); [congruence | idtac]
  end.

  Definition invariant_dec eps (li : Location * SquareInterval) : bool :=
    let (l, i) := li in
      osquares_overlap_dec eps (invariant_squares l, square i).

  Lemma over_invariant eps: invariant_dec eps >=> abstract_invariant.
  Proof with auto.
    intros eps [l i] id [p [pi lp]].
    bool_contradict id.
    estim (over_osquares_overlap eps).
    apply osquares_share_point with p...
  Qed.

  Definition do_invariant eps: dec_overestimator abstract_invariant
    := mk_DO (over_invariant eps).

  Variable  invariant_decider: dec_overestimator abstract_invariant.

  Definition cont_trans_cond_dec eps 
   (p : Location * (SquareInterval * SquareInterval)) : bool :=
   let (l, si) := p in
   let (i1, i2) := si in
     c_square_flow_conditions.decide_practical (xflow_invr l) (yflow_invr l) (square i1) (square i2) eps tt &&
     invariant_dec eps (l, i1) &&
     invariant_dec eps (l, i2).

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

  Variable guard_decider : dec_overestimator abstract_guard.

  Definition disc_overestimation_dec eps (ss: (Location * SquareInterval) *
    (Location * SquareInterval)) : bool :=
    let (source, target) := ss in
    let (l, s) := source in
    let (l', s') := target in
      invariant_dec eps (l, s) &&
      invariant_dec eps (l', s') &&
      (do_pred guard_decider) (l, s, l') &&
      osquares_overlap_dec eps (map_osquare (xresetinc l l') (yresetinc l l') 
        (square s), square s').

  Lemma over_disc_trans eps : 
    disc_overestimation_dec eps >=> c_abstraction.disc_trans_cond concrete_system in_region.
  Proof with auto.
    intros eps [[l1 s1] [l2 s2]] cond 
      [p [q [ps1 [qs2 [guard [res [inv1 inv2]]]]]]].
    unfold disc_overestimation_dec in cond.
    band_discr.
      bool_solver.
        bool_solver.
          estim (over_invariant eps). exists p...
        estim (over_invariant eps). exists q...
      estim ((do_correct guard_decider)). exists p...
    estim (over_osquares_overlap eps).
    apply osquares_share_point with (reset l1 l2 p); rewrite reset_components.
    apply in_map_osquare... destruct p. destruct q.
    rewrite reset_components in res. inversion res. 
    destruct ps1. destruct qs2. destruct H3. destruct H4. simpl in *.
    split. 
      replace (fst (square s2)) with (Xinterval_range (fst s2))...
      split.
        destruct (orange_left (Xinterval_range (fst s2)))...
        rewrite H...
      destruct (orange_right (Xinterval_range (fst s2)))...
      rewrite H...
    replace (snd (square s2)) with (Yinterval_range (snd s2))...
    split.
      destruct (orange_left (Yinterval_range (snd s2)))...
      rewrite H0...
    destruct (orange_right (Yinterval_range (snd s2)))...
    rewrite H0...
  Qed.

  Definition do_odisc_trans eps:
    dec_overestimator (c_abstraction.disc_trans_cond concrete_system in_region)
      := mk_DO (over_disc_trans eps).

  Variables
    (absXinterval: CR -> Xinterval)
    (absYinterval: CR -> Yinterval).

  Definition absInterval (p: Point): SquareInterval :=
    (absXinterval (fst p), absYinterval (snd p)).

  Lemma over_cont_trans eps : 
    cont_trans_cond_dec eps >=> c_abstraction.cont_trans_cond concrete_system in_region.
  Proof with auto.
    intros eps [l [i1 i2]] cond [p [q [pi1 [qi2 ct]]]].
    destruct ct as [lp_lq [[t tpos] [ctc cteq]]].
    bool_contradict cond.
    unfold cont_trans_cond_dec.
    bool_solver.
      bool_solver.
        eapply (over_true _ (c_square_flow_conditions.over_decide_practical eps)).
        apply c_square_flow_conditions.ideal_implies_practical_decideable with (xflow l) (yflow l)...
            intros. apply xflow_invr_correct with x...
          intros. apply yflow_invr_correct with y...
        exists p. split...
        exists t. split. 
          apply (CRnonNeg_le_zero t)...
        simpl bsm in cteq. 
        destruct p. destruct q. inversion cteq.    
        destruct pi1. destruct qi2. destruct H3. destruct H4.
        split. 
          split.
            destruct (orange_left (fst (square i2)))...
            rewrite H...
          destruct (orange_right (fst (square i2)))...
          rewrite H...
        split.
          destruct (orange_left (snd (square i2)))...
          rewrite H0...
        destruct (orange_right (snd (square i2)))...
        rewrite H0...
      estim (over_invariant eps). exists p. split... 
      apply (c_concrete.invariant_wd concrete_system (refl_equal l) p
        (c_concrete.flow concrete_system l p (' 0))).
        symmetry. apply flow_zero. 
      apply ctc. apply CRle_refl.    
      apply (CRnonNeg_le_zero t)...
    estim (over_invariant eps). exists q. split... 
    apply (c_concrete.invariant_wd concrete_system (refl_equal l) _ q cteq).
    apply ctc. 
      apply (CRnonNeg_le_zero t)...
    apply CRle_refl.
  Qed.    

  Definition do_cont_trans (eps: Qpos):
    dec_overestimator (c_abstraction.cont_trans_cond concrete_system in_region)
      := mk_DO (over_cont_trans eps).

  (* If one's initial location can be expressed as a simple square
   in a single location, we can decide it for the abstract system
   by checking overlap with regions. *)

  Variables (initial_location: Location) (initial_square: OpenSquare)
    (initial_representative:
      forall (s : c_concrete.State concrete_system),
        let (l, p) := s in
          c_concrete.initial s -> 
          l = initial_location /\ in_osquare p initial_square).

  Definition initial_dec eps (s : Location * SquareInterval) : bool :=
    let (l, si) := s in
      osquares_overlap_dec eps (initial_square, square si) &&
      decision_to_bool (Location_eq_dec l initial_location).

  Lemma over_initial eps : 
    initial_dec eps >=> c_abstraction.initial_condition concrete_system in_region.
  Proof with auto.
    intros eps [l i] id [p [pi lp]].
    destruct (initial_representative (l, p) lp). subst.
    unfold initial_dec in id. band_discr.
      estim (over_osquares_overlap eps).
      apply osquares_share_point with p...
    set (w := Location_eq_dec initial_location initial_location).
    dependent inversion w. ref. contradiction n. ref.
  Qed.

  Definition do_initial eps := mk_DO (over_initial eps).

End contents.
