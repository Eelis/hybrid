Require abstraction.
Require square_flow_conditions.
Require Import util.
Require Import list_util.
Require Import c_util.
Require Import geometry.
Require Import monotonic_flow.
Require concrete.
Require Import List.
Require EquivDec.
Set Implicit Arguments.

Open Scope CR_scope.

Section contents.

  Inductive Reset :=
    | Reset_id
    | Reset_const (c: CR)
    | Reset_map (m: sigT increasing).
  (* we distinguish between const and map because
  for a const reset function with value c, a range with an infinite
  bound [a, inf) should be mapped to [c, c], not to [c, inf).
  we distinguish between id and map because it lets us
  avoid senseless discrete transitions between adjacent regions. *)

  Definition apply_Reset (r: Reset) (v: CR): CR :=
    match r with
    | Reset_id => v
    | Reset_const c => c
    | Reset_map m => proj1_sigT _ _ m v
    end.

  Context
    {Xinterval Yinterval Location: Set}
    {Location_eq_dec: EquivDec.EqDec Location eq}
    {Xinterval_eq_dec: EquivDec.EqDec Xinterval eq}
    {Yinterval_eq_dec: EquivDec.EqDec Yinterval eq}
    {locations: ExhaustiveList Location}
    {Xintervals: ExhaustiveList Xinterval}
    {Yintervals: ExhaustiveList Yinterval}.

  Definition SquareInterval: Set := (Xinterval * Yinterval)%type.

  Variables
    (NoDup_Xintervals: NoDup Xintervals)
    (NoDup_Yintervals: NoDup Yintervals).

  Lemma NoDup_squareIntervals: NoDup (@ExhaustivePairList Xinterval Yinterval _ _).
  Proof with auto.
    unfold exhaustive_list.
    simpl.
    apply NoDup_flat_map; intros...
      destruct (fst (in_map_iff (pair a) Yintervals x) H1).
      destruct (fst (in_map_iff (pair b) Yintervals x) H2).
      destruct H3. destruct H4.
      subst. inversion H4...
    apply NoDup_map...
    intros. inversion H2...
  Qed.

  Variables
    (Xinterval_range: Xinterval -> OpenRange)
    (Yinterval_range: Yinterval -> OpenRange).

  Definition square: SquareInterval -> OpenSquare :=
    prod_map Xinterval_range Yinterval_range.

  Definition in_region (p: Point) (s: SquareInterval): Prop :=
    in_osquare p (square s).

  Variables
    (absXinterval: CR -> Xinterval)
    (absYinterval: CR -> Yinterval).

  Definition absInterval (p: Point): SquareInterval :=
    (absXinterval (fst p), absYinterval (snd p)).

  Variable initial: Location -> Xinterval -> Yinterval -> bool.

  Variables
    (xflow yflow: Location -> Flow CRasCSetoid)
    (xflow_invr yflow_invr: Location -> OpenRange -> OpenRange -> OpenRange)
    (xflow_invr_correct: forall l, range_flow_inv_spec (xflow l) (xflow_invr l))
    (yflow_invr_correct: forall l, range_flow_inv_spec (yflow l) (yflow_invr l)).

  Let Point := ProdCSetoid CRasCSetoid CRasCSetoid.

  Variables
    (concrete_initial: Location * Point -> Prop)
    (concrete_invariant: Location * Point -> Prop)
    (concrete_invariant_initial: forall p: Location * geometry.Point,
      concrete_initial p -> concrete_invariant p)
    (concrete_guard: Location * geometry.Point -> Location -> Prop)
    (reset: Location -> Location -> Point -> Point).

  Definition abstract_guard (ls: (Location * SquareInterval) * Location): Prop
    := exists p, geometry.in_osquare p (square (snd (fst ls))) /\
	concrete_guard (fst (fst ls), p) (snd ls).

  Definition abstract_invariant (ls: Location * SquareInterval): Prop :=
    exists p,
      geometry.in_osquare p (square (snd ls)) /\
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
     square_flow_conditions.decide_practical (xflow_invr l) (yflow_invr l) (square i1) (square i2) eps tt &&
     invariant_dec eps (l, i1) &&
     invariant_dec eps (l, i2).

  Hypothesis invariant_wd: forall l l', l = l' -> forall p p', p[=]p' ->
    (concrete_invariant (l, p) <-> concrete_invariant (l', p')).

  Hypothesis NoDup_locations: NoDup locations.

  Variables (reset_x reset_y: Location -> Location -> Reset).

  Hypothesis reset_components: forall p l l',
    reset l l' p = (apply_Reset (reset_x l l') (fst p), apply_Reset (reset_y l l') (snd p)).

  Variables
    (absXinterval_correct: forall p l, concrete_invariant (l, p) ->
      in_orange (Xinterval_range (absXinterval (fst p))) (fst p))
    (absYinterval_correct: forall p l, concrete_invariant (l, p) ->
      in_orange (Yinterval_range (absYinterval (snd p))) (snd p))
    (absXinterval_wd: forall x x', x == x' -> absXinterval x = absXinterval x')
    (absYinterval_wd: forall y y', y == y' -> absYinterval y = absYinterval y').

  Lemma absInterval_wd (p p': Point): p [=] p' -> absInterval p = absInterval p'.
  Proof with auto.
    intros.
    unfold absInterval.
    destruct p. destruct p'.
    inversion_clear H.
    f_equal.
      apply absXinterval_wd...
    apply absYinterval_wd...
  Qed.

  Instance SquareInterval_eq_dec: EquivDec.EqDec SquareInterval eq.
    repeat intro.
    cut (decision (x = y)). auto.
    dec_eq. apply Yinterval_eq_dec. apply Xinterval_eq_dec.
  Defined.

  Definition concrete_system: concrete.System :=
    @concrete.Build_System Point Location Location_eq_dec
      locations NoDup_locations concrete_initial
      concrete_invariant concrete_invariant_initial invariant_wd
      (fun l: Location => product_flow (xflow l) (yflow l))
      concrete_guard reset.

  Variable guard_decider: dec_overestimator abstract_guard.

  Definition map_orange' (f: sigT increasing): OpenRange -> OpenRange
    := let (_, y) := f in map_orange y.

  Let State := prod Location SquareInterval.

  Definition disc_trans_regions (eps: Qpos) (l l': Location) (r: SquareInterval): list SquareInterval
    :=
    if do_pred guard_decider (l, r, l') && do_pred invariant_decider (l, r) then
    let xs := match reset_x l l' with
      | Reset_const c => filter (fun r' => oranges_overlap_dec eps
        (unit_range c: OpenRange, Xinterval_range r')) Xintervals
      | Reset_map f => filter (fun r' => oranges_overlap_dec eps
        (map_orange' f (Xinterval_range (fst r)), Xinterval_range r')) Xintervals
      | Reset_id => [fst r] (* x reset is id, so we can only remain in this x range *)
      end in
    let ys := match reset_y l l' with
      | Reset_const c => filter (fun r' => oranges_overlap_dec eps
        (unit_range c: OpenRange, Yinterval_range r')) Yintervals
      | Reset_map f => filter (fun r' => oranges_overlap_dec eps
        (map_orange' f (Yinterval_range (snd r)), Yinterval_range r')) Yintervals
      | Reset_id => [snd r] (* x reset is id, so we can only remain in this x range *)
      end
     in flat_map (fun x => filter (fun s => do_pred invariant_decider (l', s)) (map (pair x) ys)) xs
   else [].

  Definition disc_trans (eps: Qpos) (s: State): list State :=
    let (l, r) := s in
    flat_map (fun l' => map (pair l') (disc_trans_regions eps l l' r)) locations.

  Lemma NoDup_disc_trans eps s: NoDup (disc_trans eps s).
  Proof with auto.
    intros.
    unfold disc_trans.
    destruct s.
    apply NoDup_flat_map...
      intros.
      destruct (fst (in_map_iff _ _ _) H1).
      destruct (fst (in_map_iff _ _ _) H2).
      destruct H3. destruct H4.
      subst.
      inversion_clear H4...
    intros.
    apply NoDup_map.
      intros.
      inversion_clear H2...
    unfold disc_trans_regions.
    destruct (do_pred guard_decider (l, s, x) && do_pred invariant_decider (l, s))...
    apply NoDup_flat_map...
        intros.
        destruct (fst (filter_In _ _ _) H2).
        destruct (fst (filter_In _ _ _) H3).
        destruct (fst (in_map_iff _ _ _) H4).
        destruct (fst (in_map_iff _ _ _) H6).
        destruct H8. destruct H9.
        subst x0. inversion_clear H9...
      intros.
      apply NoDup_filter.
      apply NoDup_map.
        intros.
        inversion_clear H3...
      destruct (reset_y l x)...
    destruct (reset_x l x)...
  Qed.

  Lemma in_region_wd x x' r: x [=] x' -> in_region x r -> in_region x' r.
  Proof with auto.
    unfold in_region.
    intros.
    destruct H0.
    destruct r.
    simpl in H0, H1. unfold square. simpl.
    destruct x. destruct x'.
    simpl in H0, H1.
    inversion_clear H.
    split; simpl.
      apply (@in_orange_wd (Xinterval_range x0) (Xinterval_range x0)) with s; try reflexivity...
    apply (@in_orange_wd (Yinterval_range y) (Yinterval_range y)) with s0; try reflexivity...
  Qed.

  Hint Resolve absXinterval_correct absYinterval_correct.
  Hint Resolve in_map_orange.

  Lemma respects_disc (eps: Qpos) (s1 s2 : concrete.State concrete_system):
    let (l1, p1) := s1 in
    let (l2, p2) := s2 in
    concrete.disc_trans s1 s2 ->
    In (l2, absInterval p2) (disc_trans eps (l1, absInterval p1)).
  Proof with simpl; auto.
    destruct s1. destruct s2.
    intros.
    unfold concrete.Point, concrete_system in s, s0.
    unfold concrete.Location, concrete_system in l, l0.
    unfold concrete.disc_trans in H.
    destruct H. destruct H0. destruct H1.
    unfold disc_trans.
    apply <- in_flat_map.
    exists l0.
    split...
    apply in_map.
    unfold disc_trans_regions.
    case_eq (do_pred guard_decider (l, absInterval s, l0)); intro.
      case_eq (do_pred invariant_decider (l, absInterval s)); intro.
        clear H3 H4.
        simpl andb.
        cbv iota.
        apply <- in_flat_map.
        exists (fst (absInterval s0)).
        rewrite reset_components in H0.
        simpl @fst in H0. simpl @snd in H0.
        split.
          destruct (reset_x l l0).
              left. inversion_clear H0...
            simpl in H0.
            apply in_filter...
            apply not_false_is_true.
            intro.
            apply (over_oranges_overlap eps H3).
            apply oranges_share_point with (fst s0)...
              inversion_clear H0.
              simpl. split...
            eauto.
          apply in_filter...
          apply not_false_is_true.
          intro.
          apply (over_oranges_overlap eps H3).
          simpl in H0.
          apply oranges_share_point with (fst s0)...
            destruct s0.
            inversion_clear H0.
            simpl @fst.
            unfold map_orange'.
            destruct m.
            simpl proj1_sigT.
            eauto.
          eauto.
        unfold absInterval.
        simpl.
        apply in_filter.
          apply in_map.
          destruct (reset_y l l0).
              left. simpl in H0. inversion_clear H0...
            apply in_filter...
            apply not_false_is_true.
            intro.
            apply (over_oranges_overlap eps H3).
            apply oranges_share_point with (snd s0).
              simpl in H0.
              inversion_clear H0.
              simpl @snd.
              split...
            eauto.
          apply in_filter...
          apply not_false_is_true.
          intro.
          apply (over_oranges_overlap eps H3).
          apply oranges_share_point with (snd s0)...
            destruct s0. destruct m.
            inversion_clear H0.
            simpl @snd.
            unfold map_orange'.
            eauto.
          eauto.
        intros.
        apply not_false_is_true.
        intro.
        apply (do_correct invariant_decider _ H3).
        unfold abstract_invariant.
        simpl.
        exists s0.
        split...
        split... eauto.
        eauto.
      elimtype False.
      apply (do_correct invariant_decider _ H4).
      unfold abstract_invariant.
      simpl.
      exists s. split... split... eauto. eauto.
      apply (do_correct guard_decider (l, absInterval s, l0) H3).
    unfold abstract_guard.
    simpl @fst. simpl @snd.
    exists s... split... split... eauto. eauto.
  Qed.

  Lemma over_cont_trans eps : 
    cont_trans_cond_dec eps >=> abstraction.cont_trans_cond concrete_system in_region.
  Proof with auto.
    intros eps [l [i1 i2]] cond [p [q [pi1 [qi2 ct]]]].
    destruct ct as [lp_lq [[t tpos] [ctc cteq]]].
    bool_contradict cond.
    unfold cont_trans_cond_dec.
    bool_solver.
      bool_solver.
        eapply (over_true _ (square_flow_conditions.over_decide_practical eps)).
        apply square_flow_conditions.ideal_implies_practical_decideable with (xflow l) (yflow l)...
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
      apply (concrete.invariant_wd concrete_system (refl_equal l) p
        (concrete.flow concrete_system l p (' 0))).
        symmetry. apply flow_zero. 
      apply ctc. apply CRle_refl.    
      apply (CRnonNeg_le_zero t)...
    estim (over_invariant eps). exists q. split... 
    apply (concrete.invariant_wd concrete_system (refl_equal l) _ q cteq).
    apply ctc. 
      apply (CRnonNeg_le_zero t)...
    apply CRle_refl.
  Qed.

  Definition do_cont_trans (eps: Qpos):
    dec_overestimator (abstraction.cont_trans_cond concrete_system in_region)
      := mk_DO (over_cont_trans eps).

  (* If one's initial location can be expressed as a simple square
   in a single location, we can decide it for the abstract system
   by checking overlap with regions. *)

  Variables (initial_location: Location) (initial_square: OpenSquare)
    (initial_representative:
      forall (s : concrete.State concrete_system),
        let (l, p) := s in
          concrete.initial s ->
          l = initial_location /\ in_osquare p initial_square).

  Definition initial_dec eps (s : Location * SquareInterval) : bool :=
    let (l, si) := s in
      osquares_overlap_dec eps (initial_square, square si) &&
      decision_to_bool (Location_eq_dec l initial_location).

  Lemma over_initial eps : 
    initial_dec eps >=> abstraction.initial_condition concrete_system in_region.
  Proof with auto.
    intros eps [l i] id [p [pi lp]].
    destruct (initial_representative (l, p) lp). subst.
    unfold initial_dec in id. band_discr.
      estim (over_osquares_overlap eps).
      apply osquares_share_point with p...
    set (w := Location_eq_dec initial_location initial_location).
    dependent inversion w. ref. contradiction c. ref.
  Qed.

  Definition do_initial eps := mk_DO (over_initial eps).

End contents.
