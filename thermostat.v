Require Import List.
Require Import util.
Require Import list_util.
Require Import geometry.
Require Import monotonic_flow.
Require concrete.
Require abstract.
Require abstraction.
Require square_abstraction.
Require abstract_as_graph.
Require CRln.
Require CRexp.
Require EquivDec.
Set Implicit Arguments.

Open Local Scope CR_scope.

Lemma half_pos: '0 < '(1#2).
Proof.
  exists ((1#2)%Qpos).
  rewrite CRminus_Qminus.
  apply (CRle_Qle (QposAsQ (1#2)) ((1#2)-0)%Q).
  firstorder.
Defined.

Definition above (c: CR): OpenRange := exist OCRle (Some c, None) I.
Definition below (c: CR): OpenRange := exist OCRle (None, Some c) I.

Let PointCSetoid: CSetoid := ProdCSetoid CRasCSetoid CRasCSetoid.

(* Locations *)

Inductive Location: Set := Heat | Cool | Check.

Instance Location_eq_dec: EquivDec.EqDec Location eq.
Proof. repeat intro. cut (decision (x=y)). auto. dec_eq. Defined.

Instance locations: ExhaustiveList Location :=
  { exhaustive_list := Heat :: Cool :: Check :: nil }.
Proof. intro l. destruct l; compute; tauto. Defined.

Lemma NoDup_locations: NoDup locations.
  apply decision_true with (NoDup_dec Location_eq_dec locations).
  vm_compute. reflexivity.
Qed.

(* States *)

Let State : Type := (Location * Point)%type.

Definition point: State -> Point := snd.
Definition loc: State -> Location := fst.
Definition clock: State -> CR := fst ∘ point.
Definition temp: State -> CR := snd ∘ point.

(* Invariant *)

Definition invariant (s: State): Prop :=
  '(1#10) <= temp s /\ (* todo: get down to 0 *)
  '0 <= clock s /\
  match loc s with
  | Heat => temp s <= '10 /\ clock s <= '3
  | Cool => '5 <= temp s
  | Check => clock s <= '1
  end.

Lemma invariant_wd: forall l l', l = l' ->
  forall (p p': PointCSetoid), p[=]p' -> (invariant (l, p) <-> invariant (l', p')).
Proof with auto.
  unfold invariant.
  intros l l' le. subst.
  intros [x y] [x' y'] pe.
  inversion_clear pe.
  simpl loc. unfold temp, clock. unfold Basics.compose. simpl @fst. simpl @snd.
  destruct l'; try rewrite H; try rewrite H0; split...
Qed.

Program Definition invariant_squares (l: Location): OpenSquare :=
  match l with
  | Cool => (above ('0), above ('5))
  | Heat => (('0, '3), ('0, '10)): Square
  | Check => (('0, '1): Range, above ('(1#10)))
  end.

Solve Obligations using intros; CRle_constants.

Lemma invariant_squares_correct (l : Location) (p : Point):
  invariant (l, p) -> in_osquare p (invariant_squares l).
Proof with auto.
  unfold invariant, in_osquare, in_orange, orange_left, orange_right.
  destruct l; simpl; intuition.
  unfold temp in *.
  unfold Basics.compose in *.
  apply CRle_trans with ('(1#10))...
  CRle_constants.
Qed.

(* Initial state *)

Program Definition initial_square: OpenSquare := (('0, '0), ('5, '10)): Square.
Solve Obligations using intros; CRle_constants.

Definition initial_location := Heat.
Definition initial (s: State): Prop :=
  loc s = initial_location /\ in_osquare (point s) initial_square.

Lemma initial_invariant (s: State): initial s -> invariant s.
Proof with auto.
  destruct s as [l [c t]].
  unfold initial, invariant, initial_square.
  simpl.
  intros [H [[H0 H1] [H2 H3]]].
  subst.
  unfold initial_location, temp, clock, compose.
  simpl in *.
  split...
    apply CRle_trans with ('5)...
    CRle_constants.
  split... split...
  unfold Basics.compose.
  apply CRle_trans with ('0)...
  CRle_constants.
Qed.

(* Flow *)

Definition clock_flow (l: Location): Flow CRasCSetoid := flow.positive_linear.f.

Definition temp_flow (l: Location): Flow CRasCSetoid :=
  match l with
  | Heat => flow.scale.flow ('(5#2)) flow.positive_linear.f (* todo: get this closer to 2 *)
  | Cool => flow.decreasing_exponential.f
  | Check => flow.scale.flow ('(1#2)) flow.decreasing_exponential.f
  end.

Definition flow l := product_flow (clock_flow l) (temp_flow l).

(* Flow inverses *)

Lemma meh: '0 < '(5#2).
Proof.
  exists ((5#2)%Qpos).
  rewrite CRminus_Qminus.
  apply (CRle_Qle (QposAsQ (1#2)) ((1#2)-0)%Q).
  firstorder.
Defined.

Definition clock_flow_inv (l: Location) (a b: OpenRange): OpenRange :=
  square_flow_conditions.one_axis.flow_range
    _ flow.positive_linear.inv_correct flow.positive_linear.mono a b.

Definition temp_flow_inv (l: Location): OpenRange -> OpenRange -> OpenRange :=
  match l with
  | Heat => flow.scale.inv meh (square_flow_conditions.one_axis.flow_range
    _ flow.positive_linear.inv_correct flow.positive_linear.mono)
  | Cool => flow.decreasing_exponential.inv
  | Check => flow.scale.inv half_pos flow.decreasing_exponential.inv
  end.

Lemma clock_rfis l: range_flow_inv_spec (clock_flow l) (clock_flow_inv l).
Proof with auto.
  intro.
  unfold range_flow_inv_spec. intros.
  apply square_flow_conditions.one_axis.flow_range_covers with p...
Qed.

Lemma temp_rfis l: range_flow_inv_spec (temp_flow l) (temp_flow_inv l).
Proof with auto.
  destruct l; simpl temp_flow.
      apply flow.scale.inv_correct.
      unfold range_flow_inv_spec. intros.
      apply square_flow_conditions.one_axis.flow_range_covers with p...
    apply flow.decreasing_exponential.inv_correct.
  apply flow.scale.inv_correct, flow.decreasing_exponential.inv_correct.
Qed.

(* Reset *)

Definition clock_reset (l l': Location): square_abstraction.Reset :=
  match l, l' with
  | Cool, Heat | Heat, Check | Check, Heat => square_abstraction.Reset_const ('0)
  | _, _ => square_abstraction.Reset_id (* dummy *)
  end.

Definition temp_reset (l l': Location): square_abstraction.Reset :=
  square_abstraction.Reset_id. (* dummy *)

Definition reset (l l': Location) (p: Point): Point :=
  (square_abstraction.apply_Reset (clock_reset l l') (fst p)
  , square_abstraction.apply_Reset (temp_reset l l') (snd p)).

(* Guards *)

Definition guard_square (l l': Location): option OpenSquare :=
  match l, l' with
  | Heat, Cool => Some (unbounded_range, above ('9))
  | Cool, Heat => Some (unbounded_range, below ('6))
  | Heat, Check => Some (above ('(21#10)), unbounded_range)
  | Check, Heat => Some (above ('(1#2)), unbounded_range)
  | _, _ => None
  end.

Definition guard (s: State) (l: Location): Prop :=
  match guard_square (fst s) l with
  | None => False
  | Some q => in_osquare (snd s) q
  end.

(* Concrete system *)

Definition concrete_system: concrete.System :=
  concrete.Build_System _ _ NoDup_locations initial invariant
  initial_invariant invariant_wd flow guard reset.

(* intervals *)

Inductive ClockInterval: Set := CI0_D | CID_12 | CI12_1 | CI1_2 | CI2_3 | CI3_.
Inductive TempInterval: Set := TIC_45 | TI45_5 | TI5_6 | TI6_9 | TI9_10 | TI10_.

Program Definition ClockInterval_bounds (i: ClockInterval): OpenRange :=
  match i with
  | CI0_D => ('0, '(1#10)): Range
  | CID_12 => ('(1#10), '(1#2)): Range
  | CI12_1 => ('(1#2), '(11#10)): Range
  | CI1_2 => ('(11#10), '2): Range
  | CI2_3 => ('2, '3): Range
  | CI3_ => (Some ('3), None)
  end.

Solve Obligations using intros; CRle_constants.

Program Definition TempInterval_bounds (i: TempInterval): OpenRange :=
  match i with
  | TIC_45 => ('(1#10), '(9#2)): Range
  | TI45_5 => ('(9#2), '5): Range
  | TI5_6 => ('5, '6): Range
  | TI6_9 => ('6, '9): Range
  | TI9_10 => ('9, '10): Range
  | TI10_ => (Some ('10), None)
  end.

Solve Obligations using intros; CRle_constants.

Instance clock_intervals: ExhaustiveList ClockInterval
  := { exhaustive_list := CI0_D :: CID_12 :: CI12_1 :: CI1_2 :: CI2_3 :: CI3_ :: nil }.
Proof. intro i. destruct i; compute; tauto. Defined.

Instance temp_intervals: ExhaustiveList TempInterval
  := { exhaustive_list := TIC_45 :: TI45_5 :: TI5_6 :: TI6_9 :: TI9_10 :: TI10_ :: nil }.
Proof. intro i. destruct i; compute; tauto. Defined.

Program Definition s_absClockInterval (r: CR):
    { i | '0 <= r -> in_orange (ClockInterval_bounds i) r } :=
  if CR_le_le_dec r ('(1#10)) then CI0_D else
  if CR_le_le_dec r ('(1#2)) then CID_12 else
  if CR_le_le_dec r ('(11#10)) then CI12_1 else
  if CR_le_le_dec r ('2) then CI1_2 else
  if CR_le_le_dec r ('3) then CI2_3 else CI3_.

Solve Obligations using
  unfold in_orange, orange_left, orange_right; simpl; auto.

Program Definition s_absTempInterval (r: CR):
    { i | '(1#10) <= r -> in_orange (TempInterval_bounds i) r } :=
  if CR_le_le_dec r ('(9#2)) then TIC_45 else
  if CR_le_le_dec r ('5) then TI45_5 else
  if CR_le_le_dec r ('6) then TI5_6 else
  if CR_le_le_dec r ('9) then TI6_9 else
  if CR_le_le_dec r ('10) then TI9_10 else TI10_.

Solve Obligations using
  unfold in_orange, orange_left, orange_right; simpl; auto.

Definition absClockInterval (r: CR): ClockInterval := proj1_sig (s_absClockInterval r).
Definition absTempInterval (r: CR): TempInterval := proj1_sig (s_absTempInterval r).

Ltac absInterval_wd_helper r r' H v :=
  set (e := @CR_le_le_dec_wd r r' v v H (genericSetoid_Reflexive _ _)); clearbody e;
  destruct (CR_le_le_dec r v) in *; destruct (CR_le_le_dec r' v) in *; auto; try discriminate; clear e.

Lemma absClockInterval_wd (r r': CR): st_eq r r' -> absClockInterval r = absClockInterval r'.
Proof.
  unfold absClockInterval, s_absClockInterval. intros.
  absInterval_wd_helper r r' H ('(1#10)).
  absInterval_wd_helper r r' H ('(1#2)).
  absInterval_wd_helper r r' H ('(11#10)).
  absInterval_wd_helper r r' H ('2).
  absInterval_wd_helper r r' H ('3).
Qed.

Lemma absTempInterval_wd (r r': CR): st_eq r r' -> absTempInterval r = absTempInterval r'.
Proof.
  unfold absTempInterval, s_absTempInterval. intros.
  absInterval_wd_helper r r' H ('(9#2)).
  absInterval_wd_helper r r' H ('5).
  absInterval_wd_helper r r' H ('6).
  absInterval_wd_helper r r' H ('9).
  absInterval_wd_helper r r' H ('10).
Qed.

Instance ClockInterval_eq_dec: EquivDec.EqDec ClockInterval eq.
Proof. repeat intro. cut (decision (x=y)). auto. dec_eq. Defined.
Instance TempInterval_eq_dec: EquivDec.EqDec TempInterval eq.
Proof. repeat intro. cut (decision (x=y)). auto. dec_eq. Defined.

Lemma NoDup_clock_intervals: NoDup clock_intervals.
  apply decision_true with (NoDup_dec ClockInterval_eq_dec clock_intervals).
  vm_compute. ref.
Qed.

Lemma NoDup_temp_intervals: NoDup temp_intervals.
  apply decision_true with (NoDup_dec TempInterval_eq_dec temp_intervals).
  vm_compute. ref.
Qed.

Lemma regions_cover_invariants l (p: concrete.Point concrete_system):
  concrete.invariant (l, p) ->
  square_abstraction.in_region ClockInterval_bounds TempInterval_bounds p
    (square_abstraction.absInterval absClockInterval absTempInterval p).
Proof with auto.
  simpl concrete.invariant.
  destruct p.
  intros.
  unfold square_abstraction.in_region.
  unfold square_abstraction.absInterval.
  simpl.
  unfold absClockInterval, absTempInterval.
  destruct (s_absClockInterval s). destruct (s_absTempInterval s0). simpl.
  destruct H. destruct H0.
  split...
Qed.

Definition Region: Set := prod ClockInterval TempInterval.

Definition guard_dec eps (ls : Location * Region * Location) :=
  let (lr, l2) := ls in
  let (l1, r) := lr in
    match guard_square l1 l2 with
    | Some s => osquares_overlap_dec eps
      (s, square_abstraction.square ClockInterval_bounds TempInterval_bounds r)
    | None => false
    end.

Lemma over_guard eps : 
  guard_dec eps >=> square_abstraction.abstract_guard ClockInterval_bounds TempInterval_bounds guard.
Proof with auto.
  intros eps [[l r] l'] gf [p [in_p g]].
  unfold guard_dec in gf. unfold guard in g.
  simpl @fst in *. simpl @snd in *.  
  destruct (guard_square l l'); try contradiction.
  apply (over_osquares_overlap eps gf).
  apply osquares_share_point with p...
Qed.

Definition initial_dec eps :=
  square_abstraction.initial_dec (Location:=Location)
    ClockInterval_bounds TempInterval_bounds
    initial_location initial_square eps.

Lemma over_initial eps: initial_dec eps >=>
  abstraction.initial_condition concrete_system
  (square_abstraction.in_region ClockInterval_bounds TempInterval_bounds).
Proof.
  apply square_abstraction.over_initial. intros [a b]. auto.
Qed.

Hint Immediate positive_CRpos.
Hint Resolve CRpos_nonNeg.

Lemma lin_dus a b t: a <= b -> CRplus b t <= a -> t <= '0.
Proof with auto.
  intros.
  assert (b + t <= b).
    apply CRle_trans with a...
  set (t2 (-b) H1).
  assert (t <= '0).
    rewrite (Ropp_def CR_ring_theory) in c.
    rewrite <- (Radd_assoc CR_ring_theory) in c.
    rewrite <- t11 in c...
  unfold CRle.
  unfold CRle in H2.
  rewrite (Radd_0_l CR_ring_theory) in *.
  apply CRnonPos_nonNeg.
  set (CRnonNeg_nonPos H2).
  rewrite (Ropp_opp t3 CR_ring_eq_ext CR_ring_theory) in c0...
Qed.

Lemma lin_dus' a b (p: Qpos) t: a <= b -> scale.raw ('p) positive_linear.f b t <= a -> t <= '0.
Proof with auto.
  unfold scale.raw.
  simpl bsm.
  intros.
  assert (b + 'p * t <= b).
    apply CRle_trans with a...
  set (t2 (-b) H1).
  assert ('p * t <= '0).
    rewrite (Ropp_def CR_ring_theory) in c.
    rewrite <- (Radd_assoc CR_ring_theory) in c.
    rewrite <- t11 in c...
  unfold CRle.
  unfold CRle in H2.
  rewrite (Radd_0_l CR_ring_theory) in *.
  apply CRnonPos_nonNeg.
  set (CRnonNeg_nonPos H2).
  rewrite (Ropp_opp t3 CR_ring_eq_ext CR_ring_theory) in c0.
  apply CRnonNeg_nonPos_mult_inv with ('p)...
  apply CRpos_nonNeg. apply Qpos_CRpos.
Qed.

Definition hints (l: Location) (r r': Region): option
  (r <> r' /\
  (forall p: Point,
   square_abstraction.in_region ClockInterval_bounds TempInterval_bounds p
     r ->
   forall t: Time,
   square_abstraction.in_region ClockInterval_bounds TempInterval_bounds
     (concrete.flow concrete_system l p t) r' -> t <= '0)).
  intros.
  destruct r. destruct r'.
  destruct (and_dec (ClockInterval_eq_dec c CID_12) (ClockInterval_eq_dec c0 CI0_D)).
    destruct a.
    subst.
    apply Some.
    split. rewrite H, H0. intro. inversion_clear H1.
    intros.
    destruct p. 
    unfold Equivalence.equiv in H, H0. subst.
    destruct H2. destruct H1.
    apply (lin_dus (fst H1) (snd H)).
  destruct (and_dec (ClockInterval_eq_dec c CI12_1) (ClockInterval_eq_dec c0 CID_12)).
    destruct a.
    subst.
    apply Some.
    split. rewrite H, H0. intro. inversion_clear H1.
    intros.
    destruct p. 
    unfold Equivalence.equiv in H, H0. subst.
    destruct H2. destruct H1.
    apply (lin_dus (fst H1) (snd H)).
  destruct (and_dec (ClockInterval_eq_dec c CI1_2) (ClockInterval_eq_dec c0 CI12_1)).
    destruct a.
    subst.
    apply Some.
    split. rewrite H, H0. intro. inversion_clear H1.
    intros.
    destruct p. 
    unfold Equivalence.equiv in H, H0. subst.
    destruct H2. destruct H1.
    apply (lin_dus (fst H1) (snd H)).
  case_eq l; intro.
      destruct (and_dec (TempInterval_eq_dec t TI45_5) (TempInterval_eq_dec t0 TIC_45)).
        destruct a.
        unfold Equivalence.equiv in H0, H1.
        subst.
        apply Some.
        split. intro. inversion_clear H.
        intros.
        destruct p. destruct H. destruct H0.
        unfold in_orange in H2. simpl in H2.
        apply (@lin_dus' ('(9#2)) s0 ((5#2)%Qpos) t (fst H1) (snd H2)).
      destruct (and_dec (TempInterval_eq_dec t TI5_6) (TempInterval_eq_dec t0 TI45_5)).
        destruct a.
        unfold Equivalence.equiv in H0, H1.
        subst.
        apply Some.
        split. intro. inversion_clear H.
        intros.
        destruct p. destruct H. destruct H0.
        apply (@lin_dus' ('5) s0 ((5#2)%Qpos) t (fst H1) (snd H2)).
      destruct (and_dec (TempInterval_eq_dec t TI6_9) (TempInterval_eq_dec t0 TI5_6)).
        destruct a.
        unfold Equivalence.equiv in H0, H1.
        subst.
        apply Some.
        split. intro. inversion_clear H.
        intros.
        destruct p. destruct H. destruct H0.
        apply (@lin_dus' ('6) s0 ((5#2)%Qpos) t (fst H1) (snd H2)).
      destruct (and_dec (TempInterval_eq_dec t TI9_10) (TempInterval_eq_dec t0 TI6_9)).
        destruct a.
        unfold Equivalence.equiv in H0, H1.
        subst.
        apply Some.
        split. intro. inversion_clear H.
        intros.
        destruct p. destruct H. destruct H0.
        apply (@lin_dus' ('9) s0 ((5#2)%Qpos) t (fst H1) (snd H2)).
      destruct (and_dec (TempInterval_eq_dec t TI10_) (TempInterval_eq_dec t0 TI9_10)).
        destruct a.
        unfold Equivalence.equiv in H0, H1.
        subst.
        apply Some.
        split. intro. inversion_clear H.
        intros.
        destruct p. destruct H. destruct H0.
        apply (@lin_dus' ('10) s0 ((5#2)%Qpos) t (fst H1) (snd H2)).
      exact None.
    exact None.
  exact None.
Defined.
  (* todo: this is awful. should be automatable if we lift monotonicity *)

Lemma chicken: forall x : concrete.Location concrete_system * concrete.Point concrete_system,
  concrete.invariant x ->
  square_abstraction.in_region ClockInterval_bounds TempInterval_bounds
    (snd x) (square_abstraction.absInterval absClockInterval absTempInterval (snd x)).
Proof with auto.
  intros.
  destruct x as [a [b c]]. simpl.
  destruct H as [U [V W]]...
  split.
    unfold absClockInterval.
    simpl. destruct (s_absClockInterval b)...
  unfold absTempInterval.
  simpl. destruct (s_absTempInterval c)...
      (* todo: this should be done generically by square_abstraction *)
Qed.

Lemma cont_trans_dec (eps: Qpos): dec_overestimator
  (abstraction.cont_trans_cond concrete_system
     (square_abstraction.in_region ClockInterval_bounds TempInterval_bounds)).
Proof with auto.
  intros.
  eapply (@square_abstraction.do_cont_trans _ _ _ _ _ _ _ _ _ ClockInterval_bounds TempInterval_bounds clock_flow temp_flow clock_flow_inv temp_flow_inv).
        apply clock_rfis.
      apply temp_rfis.
    eexact invariant_squares_correct.
  exact eps.
Defined.

Definition abstract_system (eps : Qpos) : abstract.System concrete_system.
Proof with auto.
  intro eps.
  eapply (@abstraction.abstract_system' _ _ _ concrete_system _
   (fun a b e r => @square_abstraction.in_region_wd _ _ Location
     _ _ _ _ _ _ ClockInterval_bounds TempInterval_bounds a b r e)
  (square_abstraction.NoDup_squareIntervals NoDup_clock_intervals NoDup_temp_intervals)
  _
   (square_abstraction.absInterval_wd _ _  absClockInterval_wd absTempInterval_wd)
   chicken (cont_trans_dec eps) (mk_DO (over_initial eps)) hints regions_cover_invariants).
    apply (square_abstraction.NoDup_disc_trans
      NoDup_clock_intervals NoDup_temp_intervals
      (square_abstraction.do_invariant ClockInterval_bounds TempInterval_bounds _ _ invariant_squares_correct eps)
      NoDup_locations
      clock_reset temp_reset (mk_DO (over_guard eps)) eps).
  apply (@square_abstraction.respects_disc _ _ _ _ _ _ _ _ _ ClockInterval_bounds TempInterval_bounds)...
    unfold absClockInterval. intros.
    destruct (s_absClockInterval (fst p))... destruct H. destruct H0...
  unfold absTempInterval. intros.
  destruct (s_absTempInterval (snd p))... destruct H...
Defined.

Definition abs_sys: abstract.System concrete_system := abstract_system (1#100).

Definition vs := abstract_as_graph.vertices abs_sys.
Definition g := abstract_as_graph.g abs_sys.
Definition graph := flat_map (@digraph.edges g) vs.

Definition unsafe_abstract_states :=
  List.flat_map (fun l => map (fun ci => (l, (ci, TIC_45))) clock_intervals) locations.

Definition thermo_is_safe := 
  forall s : concrete.State concrete_system,
    let (l, p) := s in
    let (x, y) := p in
      List.In (l, (absClockInterval x, absTempInterval y)) unsafe_abstract_states ->
      ~concrete.reachable s.

Definition unsafe : bool :=
  abstract_as_graph.some_reachable abs_sys unsafe_abstract_states.

Theorem unsafe_correct : unsafe = false -> thermo_is_safe.
Proof.
  unfold unsafe, thermo_is_safe. intros srf [l [px py]] su.
  apply abstract_as_graph.states_unreachable with 
    abs_sys unsafe_abstract_states (l, (absClockInterval px, absTempInterval py)); 
    trivial.
Qed.

Theorem thermo_safe : thermo_is_safe.
Proof. Time apply unsafe_correct; vm_compute; ref. Qed.

Print Assumptions thermo_safe.
