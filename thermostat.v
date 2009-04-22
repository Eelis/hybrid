Require Import List.
Require Import util.
Require Import list_util.
Require Import c_geometry.
Require Import c_monotonic_flow.
Require c_concrete.
Require c_abstract.
Require c_abstraction.
Require c_square_abstraction.
Require abstract_as_graph.
Require Import CRln.
Require Import CRexp.
Require EquivDec.
Set Implicit Arguments.

Open Local Scope CR_scope.

Definition deci: Q := (1#10).
Definition centi: Q := (1#100).

Lemma deci_pos: '0 < '(1#10).
Proof.
  exists ((1#10)%Qpos).
  rewrite CRminus_Qminus.
  apply (CRle_Qle (QposAsQ (1#10)) ((1#10)-0)%Q).
  firstorder.
Defined.

Lemma centi_pos: '0 < '(1#100).
Proof.
  exists ((1#100)%Qpos).
  rewrite CRminus_Qminus.
  apply (CRle_Qle (QposAsQ (1#100)) ((1#100)-0)%Q).
  firstorder.
Defined.

Definition r0_1: Range. exists ('0, '1); CRle_constants. Defined.
Definition r0_12: Range. exists ('0, '(1#2)); CRle_constants. Defined.
Definition r0_3: Range. exists ('0, '3); CRle_constants. Defined.
Definition r12_1: Range. exists ('(1#2), '1); CRle_constants. Defined.
Definition r1_2: Range. exists ('1, '2); CRle_constants. Defined.
Definition r2_3: Range. exists ('2, '3); CRle_constants. Defined.

Definition r45_5: Range. exists ('(9#2), '5); CRle_constants. Defined.
Definition r3_45: Range. exists ('3, '(9#2)); CRle_constants. Defined.
Definition r5_6: Range. exists ('5, '6); CRle_constants. Defined.
Definition r6_9: Range. exists ('6, '9); CRle_constants. Defined.
Definition r9_10: Range. exists ('9, '10); CRle_constants. Defined.
Definition r5_10: Range. exists ('5, '10); CRle_constants. Defined.

Definition r0_10: Range. exists ('0, '10); CRle_constants. Defined.
Definition rC_45: Range. exists ('deci, '(9#2)); CRle_constants. Defined.

Definition above (c: CR): OpenRange := existT OCRle (Some c, None) I.
Definition below (c: CR): OpenRange := existT OCRle (None, Some c) I.

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
  'deci <= temp s /\ '0 <= clock s /\
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

Definition invariant_squares (l: Location): OpenSquare :=
  match l with
  | Cool => (above ('0), above ('5))
  | Heat => (r0_3: OpenRange, r0_10: OpenRange)
  | Check => (r0_1: OpenRange, above ('deci))
  end.

Lemma invariant_squares_correct (l : Location) (p : Point):
  invariant (l, p) -> in_osquare p (invariant_squares l).
Proof with auto.
  unfold invariant, in_osquare, in_orange, orange_left, orange_right.
  destruct l; simpl; intuition.
  unfold temp in *.
  unfold Basics.compose in *.
  apply CRle_trans with ('deci)...
  CRle_constants.
Qed.

(* Initial state *)

Definition initial_square: OpenSquare := (unit_range ('0): OpenRange, r5_10: OpenRange).
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

Definition clock_flow (l: Location): Flow CRasCSetoid := c_flow.positive_linear.f 1.

Definition temp_flow (l: Location): Flow CRasCSetoid :=
  match l with
  | Heat => c_flow.positive_linear.f 2
  | Cool => c_flow.decreasing_exponential.f
  | Check => c_flow.scale.flow ('(1#100)) c_flow.decreasing_exponential.f
  end.

(* Flow inverses *)

Definition clock_flow_inv (l: Location) (a b: OpenRange): OpenRange :=
  c_square_flow_conditions.one_axis.flow_range
    _ (c_flow.positive_linear.inv_correct 1) (c_flow.positive_linear.mono 1) a b.

Definition temp_flow_inv (l: Location) (a b: OpenRange): OpenRange :=
  match l with
  | Heat => c_square_flow_conditions.one_axis.flow_range
    _ (c_flow.positive_linear.inv_correct 2) (c_flow.positive_linear.mono 2) a b
  | Cool => c_flow.decreasing_exponential.inv a b
  | Check => c_flow.scale.inv centi_pos c_flow.decreasing_exponential.inv a b
  end.

Lemma clock_rfis l: range_flow_inv_spec (clock_flow l) (clock_flow_inv l).
Proof with auto.
  intro.
  unfold range_flow_inv_spec. intros.
  apply c_square_flow_conditions.one_axis.flow_range_covers with p...
Qed.

Lemma temp_rfis l: range_flow_inv_spec (temp_flow l) (temp_flow_inv l).
Proof with auto.
  destruct l; simpl temp_flow.
      unfold range_flow_inv_spec. intros.
      apply c_square_flow_conditions.one_axis.flow_range_covers with p...
    apply c_flow.decreasing_exponential.inv_correct.
  apply c_flow.scale.inv_correct, c_flow.decreasing_exponential.inv_correct.
Qed.

(* Reset *)

Definition clock_reset (l l': Location): c_square_abstraction.Reset :=
  match l, l' with
  | Cool, Heat | Heat, Check | Check, Heat => c_square_abstraction.Reset_const ('0)
  | _, _ => c_square_abstraction.Reset_id (* dummy *)
  end.

Definition temp_reset (l l': Location): c_square_abstraction.Reset :=
  c_square_abstraction.Reset_id. (* dummy *)

Definition reset (l l': Location) (p: Point): Point :=
  (c_square_abstraction.apply_Reset (clock_reset l l') (fst p)
  , c_square_abstraction.apply_Reset (temp_reset l l') (snd p)).

(* Guards *)

Definition guard_square (l l': Location): option OpenSquare :=
  match l, l' with
  | Heat, Cool => Some (unbounded_range, above ('9))
  | Cool, Heat => Some (unbounded_range, below ('6))
  | Heat, Check => Some (above ('2), unbounded_range)
  | Check, Heat => Some (above ('(1#2)), unbounded_range)
  | _, _ => None
  end.

Definition guard (s: State) (l: Location): Prop :=
  match guard_square (fst s) l with
  | None => False
  | Some q => in_osquare (snd s) q
  end.

Definition concrete_system: c_concrete.System :=
  @c_concrete.Build_System PointCSetoid Location Location_eq_dec
  locations NoDup_locations initial invariant
  initial_invariant invariant_wd
  (fun l => product_flow (clock_flow l) (temp_flow l)) guard reset.

(* intervals *)

Inductive ClockInterval: Set := CI0_12 | CI12_1 | CI1_2 | CI2_3 | CI3_.
Inductive TempInterval: Set
  := TIC_45 | TI45_5 | TI5_6 | TI6_9 | TI9_10 | TI10_.

Definition ClockInterval_bounds (i: ClockInterval): OpenRange :=
  match i with
  | CI0_12 => r0_12
  | CI12_1 => r12_1 | CI1_2 => r1_2 | CI2_3 => r2_3
  | CI3_ => above ('3)
  end.

Definition TempInterval_bounds (i: TempInterval): OpenRange :=
  match i with
  | TIC_45 => rC_45
  | TI45_5 => r45_5
  | TI5_6 => r5_6
  | TI6_9 => r6_9
  | TI9_10 => r9_10
  | TI10_ => above ('10)
  end.

Instance clock_intervals: ExhaustiveList ClockInterval
  := { exhaustive_list := CI0_12 :: CI12_1 :: CI1_2 :: CI2_3 :: CI3_ :: nil }.
Proof. intro i. destruct i; compute; tauto. Defined.

Instance temp_intervals: ExhaustiveList TempInterval
  := { exhaustive_list := TIC_45 :: TI45_5 :: TI5_6 :: TI6_9 :: TI9_10 :: TI10_ :: nil }.
Proof. intro i. destruct i; compute; tauto. Defined.

Definition s_absClockInterval (r: CR):
  { i: ClockInterval | '0 <= r -> in_orange (ClockInterval_bounds i) r }.
Proof with auto.
  intro.
  unfold in_orange, orange_left, orange_right.
  destruct (CR_le_le_dec r ('(1#2))). exists CI0_12. simpl...
  destruct (CR_le_le_dec r ('1)). exists CI12_1...
  destruct (CR_le_le_dec r ('2)). exists CI1_2...
  destruct (CR_le_le_dec r ('3)). exists CI2_3...
  exists CI3_. simpl...
Defined.

Definition s_absTempInterval (r: CR):
  { i: TempInterval | 'deci <= r -> in_orange (TempInterval_bounds i) r }.
Proof with auto.
  intro.
  unfold in_orange, orange_left, orange_right.
  destruct (CR_le_le_dec r ('(9#2))). exists TIC_45. simpl...
  destruct (CR_le_le_dec r ('5)). exists TI45_5...
  destruct (CR_le_le_dec r ('6)). exists TI5_6...
  destruct (CR_le_le_dec r ('9)). exists TI6_9...
  destruct (CR_le_le_dec r ('10)). exists TI9_10...
  exists TI10_. simpl...
Defined.

Definition absClockInterval (r: CR): ClockInterval := proj1_sig (s_absClockInterval r).
Definition absTempInterval (r: CR): TempInterval := proj1_sig (s_absTempInterval r).

Lemma absClockInterval_wd: forall (r r': CR), st_eq r r' -> absClockInterval r = absClockInterval r'.
Admitted.

Lemma absTempInterval_wd: forall (r r': CR), st_eq r r' -> absTempInterval r = absTempInterval r'.
Admitted.

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

Lemma regions_cover_invariants l (p: c_concrete.Point concrete_system):
  c_concrete.invariant (l, p) ->
  c_square_abstraction.in_region ClockInterval_bounds TempInterval_bounds p
    (c_square_abstraction.absInterval absClockInterval absTempInterval p).
Proof with auto.
  simpl c_concrete.invariant.
  destruct p.
  intros.
  unfold c_square_abstraction.in_region.
  unfold c_square_abstraction.absInterval.
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
      (s, c_square_abstraction.square ClockInterval_bounds TempInterval_bounds r)
    | None => false
    end.

Lemma over_guard eps : 
  guard_dec eps >=> c_square_abstraction.abstract_guard ClockInterval_bounds TempInterval_bounds guard.
Proof with auto.
  intros eps [[l r] l'] gf [p [in_p g]].
  unfold guard_dec in gf. unfold guard in g.
  simpl @fst in *. simpl @snd in *.  
  destruct (guard_square l l'); try contradiction.
  apply (over_osquares_overlap eps gf).
  apply osquares_share_point with p...
Qed.

Definition initial_dec eps :=
  c_square_abstraction.initial_dec (Location:=Location) 
    ClockInterval_bounds TempInterval_bounds
    initial_location initial_square eps.

Lemma over_initial eps: initial_dec eps >=>
  c_abstraction.initial_condition concrete_system
  (c_square_abstraction.in_region ClockInterval_bounds TempInterval_bounds).
Proof.
  apply c_square_abstraction.over_initial. intros [a b]. auto.
Qed.

Lemma lin_dus a b p t: a <= b -> positive_linear.raw p b t <= a -> t [=] '0.
Admitted.

Definition hints (l: Location) (r r': Region): option
  (r <> r' /\
  (forall p: Point,
   c_square_abstraction.in_region ClockInterval_bounds TempInterval_bounds p
     r ->
   forall t: Time,
   c_square_abstraction.in_region ClockInterval_bounds TempInterval_bounds
     (c_concrete.flow concrete_system l p t) r' -> t[=]' 0)).
  intros.
  destruct r. destruct r'.
  destruct (and_dec (ClockInterval_eq_dec c CI12_1) (ClockInterval_eq_dec c0 CI0_12)).
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
        apply (lin_dus (fst H1) (snd H2)).
      destruct (and_dec (TempInterval_eq_dec t TI5_6) (TempInterval_eq_dec t0 TI45_5)).
        destruct a.
        unfold Equivalence.equiv in H0, H1.
        subst.
        apply Some.
        split. intro. inversion_clear H.
        intros.
        destruct p. destruct H. destruct H0.
        apply (lin_dus (fst H1) (snd H2)).
      destruct (and_dec (TempInterval_eq_dec t TI6_9) (TempInterval_eq_dec t0 TI5_6)).
        destruct a.
        unfold Equivalence.equiv in H0, H1.
        subst.
        apply Some.
        split. intro. inversion_clear H.
        intros.
        destruct p. destruct H. destruct H0.
        apply (lin_dus (fst H1) (snd H2)).
      destruct (and_dec (TempInterval_eq_dec t TI9_10) (TempInterval_eq_dec t0 TI6_9)).
        destruct a.
        unfold Equivalence.equiv in H0, H1.
        subst.
        apply Some.
        split. intro. inversion_clear H.
        intros.
        destruct p. destruct H. destruct H0.
        apply (lin_dus (fst H1) (snd H2)).
      exact None.
    exact None.
  exact None.
Defined.
  (* todo: this is awful. should be automatable if we lift monotonicity *)

Lemma chicken: forall x : c_concrete.Location concrete_system * c_concrete.Point concrete_system,
  c_concrete.invariant x ->
  c_square_abstraction.in_region ClockInterval_bounds TempInterval_bounds
    (snd x) (c_square_abstraction.absInterval absClockInterval absTempInterval (snd x)).
Proof with auto.
  intros.
  destruct x as [a [b c]]. simpl.
  destruct H as [U [V W]]...
  split.
    unfold absClockInterval.
    simpl. destruct (s_absClockInterval b)...
  unfold absTempInterval.
  simpl. destruct (s_absTempInterval c)...
      (* todo: this should be done generically by c_square_abstraction *)
Qed.

Lemma cont_trans_dec (eps: Qpos): dec_overestimator
  (c_abstraction.cont_trans_cond concrete_system
     (c_square_abstraction.in_region ClockInterval_bounds TempInterval_bounds)).
Proof with auto.
  intros.
  eapply (@c_square_abstraction.do_cont_trans _ _ _ _ _ _ _ _ _ ClockInterval_bounds TempInterval_bounds clock_flow temp_flow clock_flow_inv temp_flow_inv).
        apply clock_rfis.
      apply temp_rfis.
    eexact invariant_squares_correct.
  exact eps.
Defined.

Definition abstract_system (eps : Qpos) : c_abstract.System concrete_system.
Proof with auto.
  intro eps.
  eapply (@c_abstraction.abstract_system' _ _ _ concrete_system _ 
   (fun a b e r => @c_square_abstraction.in_region_wd _ _ Location
     _ _ _ _ _ _ ClockInterval_bounds TempInterval_bounds a b r e)
  (c_square_abstraction.NoDup_squareIntervals NoDup_clock_intervals NoDup_temp_intervals)
  _
   (c_square_abstraction.absInterval_wd _ _  absClockInterval_wd absTempInterval_wd)
   chicken (cont_trans_dec eps) (mk_DO (over_initial eps)) hints regions_cover_invariants).
    apply (c_square_abstraction.NoDup_disc_trans
      NoDup_clock_intervals NoDup_temp_intervals
      (c_square_abstraction.do_invariant ClockInterval_bounds TempInterval_bounds _ _ invariant_squares_correct eps)
      NoDup_locations
      clock_reset temp_reset (mk_DO (over_guard eps)) eps).
  apply (@c_square_abstraction.respects_disc _ _ _ _ _ _ _ _ _ ClockInterval_bounds TempInterval_bounds)...
    unfold absClockInterval. intros.
    destruct (s_absClockInterval (fst p))... destruct H. destruct H0...
  unfold absTempInterval. intros.
  destruct (s_absTempInterval (snd p))... destruct H...
Defined.

Definition abs_sys: c_abstract.System concrete_system := abstract_system (1#100).

Definition vs := abstract_as_graph.vertices abs_sys.
Definition g := abstract_as_graph.g abs_sys.
Definition graph := flat_map (@digraph.edges g) vs.

Definition unsafe_abstract_states :=
  List.flat_map (fun l => map (fun ci => (l, (ci, TIC_45))) clock_intervals) locations.

Definition thermo_is_safe := 
  forall s : c_concrete.State concrete_system,
    let (l, p) := s in
    let (x, y) := p in
      List.In (l, (absClockInterval x, absTempInterval y)) unsafe_abstract_states ->
      ~c_concrete.reachable s.

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
