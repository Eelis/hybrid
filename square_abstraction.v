Require interval_abstraction hinted_abstract_continuous_transitions
  square_flow_conditions concrete EquivDec.
Require Import List util list_util c_util geometry monotonic_flow stability.

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

  (* If one has a concrete hybrid system.. *)

  Variable chs: concrete.System.

  (* .. and points in that system basically correspond to points in the plane.. *)

  Variables px py: 
    morpher (@st_eq (concrete.Point chs) ==> @st_eq CRasCSetoid)%signature.

  Hypothesis xyp: geometry.Point -> concrete.Point chs.
  Definition pxy (p: concrete.Point chs): geometry.Point := (px p, py p).

  Hypotheses
    (xyp_pxy: forall p, xyp (pxy p) = p)
    (px_xyp: forall p, px (xyp p) = fst p)
    (py_xyp: forall p, py (xyp p) = snd p).

  (* .. and flow in that system is separable over the two axes.. *)

  Variables
    (xflow yflow: concrete.Location chs -> Flow CRasCSetoid)
    (xflow_invr yflow_invr: concrete.Location chs -> OpenRange -> OpenRange -> OpenRange)
    (xflow_invr_correct: forall l, range_flow_inv_spec (xflow l) (xflow_invr l))
    (yflow_invr_correct: forall l, range_flow_inv_spec (yflow l) (yflow_invr l)).

  Hypothesis flow_separable: forall l p t,
    concrete.flow chs l p t = xyp (product_flow (xflow l) (yflow l) (pxy p) t).

  (* .. and on both axes, abstraction parameters can be formed based on
   OpenRange regions.. *)

  Context
    {Xinterval Yinterval: Set}
    {Xinterval_eq_dec: EquivDec.EqDec Xinterval eq}
    {Yinterval_eq_dec: EquivDec.EqDec Yinterval eq}
    {Xintervals: ExhaustiveList Xinterval}
    {Yintervals: ExhaustiveList Yinterval}.

  Variables
    (NoDup_Xintervals: NoDup Xintervals)
    (NoDup_Yintervals: NoDup Yintervals)
    (Xinterval_range: Xinterval -> OpenQRange)
    (Yinterval_range: Yinterval -> OpenQRange)
    (absXinterval: forall (l: concrete.Location chs) (p: concrete.Point chs), concrete.invariant (l, p) ->
      DN (sig (fun i: Xinterval => in_orange (Xinterval_range i) (px p))))
    (absYinterval: forall (l: concrete.Location chs) (p: concrete.Point chs), concrete.invariant (l, p) ->
      DN (sig (fun i: Yinterval => in_orange (Yinterval_range i) (py p)))).
        (* No need for LazyProp, because these are not used in computation anyway. *)

  Definition ap: abstract.Parameters chs :=
    abstract.param_prod
      (interval_abstraction.parameters chs px NoDup_Xintervals Xinterval_range absXinterval)
      (interval_abstraction.parameters chs py NoDup_Yintervals Yinterval_range absYinterval).

  Definition square: abstract.Region ap -> OpenQSquare :=
    prod_map Xinterval_range Yinterval_range.

  (*  .. then we can define useful things.

  For instance, we can easily make an invariant overestimator (if one's
  invariant can be overestimated by a list of open squares): *)

  Program Definition make_invariant_overestimator
    (invariant_squares: forall l: concrete.Location chs, sig (fun s: OpenSquare =>
      forall p, concrete.invariant (l, p) -> in_osquare (pxy p) s)) eps:
        overestimator (@abstract.invariant _ ap) :=
    fun li => osquares_overlap_dec eps (invariant_squares (fst li)) (square (snd li)).
  Next Obligation. Proof with auto.
    intros inv_squares eps li H [p [A B]].
    apply (overestimation_false _ H).
    destruct inv_squares.
    apply osquares_share_point with (pxy p)...
  Qed.

  (* Similarly, if one's initial condition can be overestimated by
   an open square, we can make an initial_dec thingy. *)

  Section make_initial_overestimator.

    Variables
      (initial_location: concrete.Location chs)
      (initial_square: OpenSquare)
      (initial_representative: forall s, concrete.initial s ->
        fst s = initial_location /\ in_osquare (pxy (snd s)) initial_square).

    Program Definition make_initial_overestimator (eps: Qpos): overestimator
      (@abstract.Initial _ ap) := fun s =>
        (overestimate_conj (osquares_overlap_dec eps (initial_square) (square (snd s)))
          (weaken_decision (concrete.Location_eq_dec chs (fst s) initial_location))).

    Next Obligation. Proof with auto.
      intros eps [l i] H [p [A B]].
      apply (overestimation_false _ H).
      destruct (initial_representative _ B).
      split...
      apply osquares_share_point with (pxy p)...
    Qed.

  End make_initial_overestimator.

  (* And similarly, if one's guard conditions can be overestimated by
  open squares, we can make a guard_dec thingy. *)

  Obligation Tactic := idtac.

  Definition GuardSquare l l' := sig
    (fun s: option OpenSquare => forall p, concrete.guard chs (l, p) l' ->
      match s with
      | None => False
      | Some v => in_osquare (pxy p) v
      end).

  Program Definition guard_dec (guard_square: forall l l', GuardSquare l l') eps:
    overestimator (@abstract.guard _ ap) := fun l r l' =>
      match guard_square l l' with
      | Some s => osquares_overlap_dec eps s (square r)
      | None => false
      end.

  Next Obligation. Proof with auto.
    intros gs eps l r l' fv s e H [x [A B]].
    apply (overestimation_false _ H).
    unfold abstract.guard in B.
    apply osquares_share_point with (pxy x)...
    destruct gs.
    simpl in fv.
    subst. subst...
  Qed.

  Next Obligation.
    intros gs eps l r l' fv s e [p [B C]].
    subst.
    destruct gs.
    simpl in s. subst. eauto.
  Qed.

  (* If the safety condition can be overestimated by a list of unsafe
   osquares, then we can select the unsafe abstract states automatically: *)

  Section square_safety.

    Variables
      (unsafe_concrete: concrete.State chs -> Prop)
      (unsafe_squares: concrete.Location chs -> list OpenSquare)
      (unsafe_squares_correct: forall s, unsafe_concrete s -> exists q,
        In q (unsafe_squares (fst s)) /\ in_osquare (pxy (snd s)) q)
      (eps: Qpos).

    Program Definition unsafe_abstract:
      sig (fun ss => LazyProp (forall s, unsafe_concrete s ->
       forall r, abstract.abs s r -> In r ss))
      := flat_map (fun l => map (pair l) (flat_map (fun q =>
        filter (fun s => osquares_overlap_dec eps q (square s)) exhaustive_list
        ) (unsafe_squares l))) (concrete.locations chs).

    Next Obligation. Proof with auto.
      intros _ s H r H0.
      apply <- in_flat_map.
      destruct H0.
      destruct s.
      exists l.
      split...
      destruct r.
      simpl in H0.
      subst.
      apply (in_map (pair l0)).
      destruct (unsafe_squares_correct H) as [x [H0 H2]].
      apply <- in_flat_map.
      eauto 10 using overestimation_true, osquares_share_point, in_filter.
    Qed.

  End square_safety.

  (* Everything above is pretty simplistic. We now prepare for more complex
   transition overestimators, for which we will require some more stuff: *)

  Variables
    (invariant_overestimator: overestimator (@abstract.invariant _ ap))
    (guard_decider: overestimator (@abstract.guard _ ap))
    (reset_x reset_y: concrete.Location chs -> concrete.Location chs -> Reset)
    (reset_components: forall p l l', pxy (concrete.reset chs l l' p) =
      (apply_Reset (reset_x l l') (px p), apply_Reset (reset_y l l') (py p))).

  Section disc_trans_regions.

    Variables (eps: Qpos) (l l': concrete.Location chs) (r: abstract.Region ap).

    Definition map_orange' (f: sigT increasing): OpenRange -> OpenRange
      := let (_, y) := f in map_orange y.

    Definition x_regions :=
      match reset_x l l' with
      | Reset_const c => filter (fun r' => oranges_overlap_dec eps
        (unit_range c: OpenRange) (Xinterval_range r')) Xintervals
      | Reset_map f => filter (fun r' => oranges_overlap_dec eps
        (map_orange' f (Xinterval_range (fst r))) (Xinterval_range r')) Xintervals
      | Reset_id => [fst r] (* x reset is id, so we can only remain in this x range *)
      end.

    Definition y_regions :=
      match reset_y l l' with
      | Reset_const c => filter (fun r' => oranges_overlap_dec eps
        (unit_range c: OpenRange) (Yinterval_range r')) Yintervals
      | Reset_map f => filter (fun r' => oranges_overlap_dec eps
        (map_orange' f (Yinterval_range (snd r))) (Yinterval_range r')) Yintervals
      | Reset_id => [snd r] (* x reset is id, so we can only remain in this x range *)
      end.

    Definition disc_trans_regions: list (abstract.Region ap)
      :=
      if overestimation_bool (guard_decider l r l') &&
          overestimation_bool (invariant_overestimator (l, r)) then
       filter (fun s => overestimation_bool (invariant_overestimator (l', s))) (cart x_regions y_regions)
     else [].

  End disc_trans_regions.

  Definition raw_disc_trans (eps: Qpos) (s: abstract.State ap): list (abstract.State ap) :=
    let (l, r) := s in
    flat_map (fun l' => map (pair l') (disc_trans_regions eps l l' r)) (concrete.locations chs).

  Lemma NoDup_disc_trans eps s: NoDup (raw_disc_trans eps s).
  Proof with auto.
    intros.
    unfold raw_disc_trans.
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
      destruct andb...
      apply NoDup_filter.
      simpl.
      apply NoDup_cart.
        unfold x_regions.
        destruct (reset_x l x)...
      unfold y_regions.
      destruct (reset_y l x)...
    apply concrete.NoDup_locations.
  Qed.

  Hint Resolve in_map_orange.

  Definition is_id_reset (r: Reset): bool :=
    match r with
    | Reset_id => true
    | _ => false
    end.

  Hint Unfold abstract.invariant abstract.guard.

  Lemma respects_disc (eps: Qpos) (s1 s2 : concrete.State chs):
    concrete.disc_trans s1 s2 -> forall i1, abstract.in_region ap (snd s1) i1 ->
    DN (exists i2, abstract.in_region ap (snd s2) i2 /\
    In (fst s2, i2) (raw_disc_trans eps (fst s1, i1))).
  Proof with simpl; auto.
    destruct s1.
    destruct s2.
    intros [g [e [inv_src inv_dst]]] r H0.
    simpl in e.
    subst s0.
    rewrite <- (xyp_pxy (concrete.reset chs l l0 s)) in inv_dst.
    rewrite reset_components in inv_dst.
    apply (DN_bind (@absXinterval l0 (xyp (apply_Reset (reset_x l l0) (px s), apply_Reset (reset_y l l0) (py s))) inv_dst)). intros [xi xin].
    apply (DN_bind (@absYinterval l0 (xyp (apply_Reset (reset_x l l0) (px s), apply_Reset (reset_y l l0) (py s))) inv_dst)). intros [yi yin].
    apply DN_return.
    rewrite px_xyp in xin. rewrite py_xyp in yin.
    simpl @fst in xin. simpl @snd in yin.
    exists ( if is_id_reset (reset_x l l0) then fst r else xi,
      if is_id_reset (reset_y l l0) then snd r else yi).
    split.
      split.
        unfold abstract.in_region.
        simpl in *.
        unfold interval_abstraction.in_region.
        rewrite <- (xyp_pxy (concrete.reset chs l l0 s)).
        rewrite reset_components.
        rewrite px_xyp.
        destruct reset_x...
        intuition.
      unfold abstract.in_region.
      simpl in *.
      unfold interval_abstraction.in_region.
      rewrite <- (xyp_pxy (concrete.reset chs l l0 s)).
      rewrite reset_components.
      rewrite py_xyp.
      destruct reset_y...
      intuition.
    unfold raw_disc_trans.
    apply <- in_flat_map.
    exists l0.
    split...
    apply in_map.
    unfold disc_trans_regions.
    rewrite (overestimation_true (guard_decider l r l0)); [| eauto 20].
    rewrite (overestimation_true (invariant_overestimator (l, r))); [| eauto 20].
    simpl andb.
    cbv iota.
    apply in_filter.
      simpl.
      apply in_cart.
        simpl @fst.
        unfold x_regions.
        destruct reset_x; auto.
          apply in_filter; auto.
          apply overestimation_true.
          apply oranges_share_point with c...
          split...
        apply in_filter; auto.
        apply overestimation_true.
        apply oranges_share_point with (apply_Reset (Reset_map m) (px s))...
        destruct m.
        simpl.
        simpl in i.
        apply in_map_orange.
        destruct H0...
      simpl @snd.
      unfold y_regions.
      destruct reset_y; auto.
        apply in_filter; auto.
        apply overestimation_true.
        apply oranges_share_point with c...
        split...
      apply in_filter; auto.
      apply overestimation_true.
      apply oranges_share_point with (apply_Reset (Reset_map m) (py s))...
      destruct m.
      simpl.
      simpl in i.
      apply in_map_orange.
      destruct H0...
    apply overestimation_true.
    unfold abstract.invariant.
    simpl.
    exists (xyp (apply_Reset (reset_x l l0) (px s), apply_Reset (reset_y l l0) (py s))).
    split...
    unfold interval_abstraction.in_region.
    destruct H0.
    rewrite px_xyp, py_xyp.
    split; simpl.
      destruct (reset_x l l0)...
    destruct (reset_y l l0)...
  Qed.

  Program Definition disc_trans (eps: Qpos) (s: abstract.State ap):
    sig (fun l: list (abstract.State ap) => LazyProp (NoDup l /\ abstract.DiscRespect s l))
    := raw_disc_trans eps s.
  Next Obligation. Proof with auto.
    split.
      apply NoDup_disc_trans.
    unfold abstract.DiscRespect.
    intros.
    apply (DN_fmap (respects_disc eps H0 H1)). intro.
    destruct H2.
    destruct H2.
    exists x...
    destruct s2...
    split...
    simpl concrete.location.
    simpl @fst in H3.
    destruct s...
  Qed.

  Obligation Tactic := idtac.

  Program Definition cont_trans_cond_dec eps l r r':
    overestimation (hinted_abstract_continuous_transitions.condition ap l r r') :=
      square_flow_conditions.decide_practical
        (xflow_invr l) (yflow_invr l) (square r) (square r') eps &&
      invariant_overestimator (l, r) &&
      invariant_overestimator (l, r').

  Next Obligation. Proof with auto.
    intros eps l i1 i2 cond.
    intros [p [q [pi [qi [H2 [[t tn] [ctc cteq]]]]]]].
    simpl in ctc. simpl @snd in cteq. simpl @fst in cteq.
    clear H2.
    simpl in cteq.
    destruct (andb_false_elim _ _ cond); clear cond.
      destruct (andb_false_elim _ _ e); clear e.
        apply (overestimation_false _ e0). clear e0.
        apply square_flow_conditions.ideal_implies_practical_decideable with (xflow l) (yflow l)...
            intros. apply xflow_invr_correct with x...
          intros. apply yflow_invr_correct with y...
        unfold square_flow_conditions.ideal.
        exists (pxy p). split...
        exists t. split. 
          apply (CRnonNeg_le_zero t)...
        unfold square_flow_conditions.f.
        simpl @fst. simpl @snd.
        rewrite <- cteq in qi.
        rewrite flow_separable in qi.
        simpl in qi.
        unfold interval_abstraction.in_region in qi.
        rewrite px_xyp in qi.
        rewrite py_xyp in qi.
        simpl in qi.
        destruct qi.
        split...
      apply (overestimation_false _ e0).
      unfold abstract.invariant.
      exists p.
      split...
      simpl @fst.
      rewrite (curry_eq concrete.invariant).
      rewrite <- (flow_zero (concrete.flow chs l) p).
      simpl. apply ctc... apply (CRnonNeg_le_zero t)...
    apply (overestimation_false _ e).
    exists q.
    split...
    rewrite (curry_eq concrete.invariant).
    rewrite <- cteq.
    simpl. apply ctc... apply (CRnonNeg_le_zero t)...
  Qed.

End contents.
