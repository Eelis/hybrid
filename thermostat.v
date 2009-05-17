Require Import List.
Require Import util.
Require Import list_util.
Require Import geometry.
Require Import monotonic_flow.
Require Import hs_solver.
Require decreasing_exponential_flow.
Require concrete.
Require abstract.
Require abstraction.
Require square_abstraction.
Require abstract_as_graph.
Require CRln.
Require CRexp.
Require EquivDec.
Set Implicit Arguments.

Module dec_exp_flow := decreasing_exponential_flow.

Open Local Scope CR_scope.

Program Definition half_pos : '0 < '(1#2) := _.

Program Definition two_pos : '0 < '2 := _.

Definition deci: Qpos := (1#10)%Qpos.
Definition centi: Qpos := (1#100)%Qpos.
Definition milli: Qpos := (1#1000)%Qpos.

Definition above (c: CR): OpenRange := exist OCRle (Some c, None) I.
Definition below (c: CR): OpenRange := exist OCRle (None, Some c) I.

Let PointCSetoid: CSetoid := ProdCSetoid CRasCSetoid CRasCSetoid.

(* Locations *)

Inductive Location: Set := Heat | Cool | Check.

Instance Location_eq_dec: EquivDec.EqDec Location eq.
Proof. hs_solver. Defined.

Instance locations: ExhaustiveList Location :=
  { exhaustive_list := Heat :: Cool :: Check :: nil }.
Proof. hs_solver. Defined.

Lemma NoDup_locations: NoDup locations.
Proof. hs_solver. Qed.

(* States *)

Let State : Type := (Location * Point)%type.

Definition point: State -> Point := snd.
Definition loc: State -> Location := fst.
Definition clock: State -> CR := fst ∘ point.
Definition temp: State -> CR := snd ∘ point.

(* Invariant *)

Definition invariant (s: State): Prop :=
  '0 <= clock s /\
  match loc s with
  | Heat => temp s <= '10 /\ clock s <= '3
  | Cool => '5 <= temp s
  | Check => clock s <= '1
  end.

Lemma invariant_wd: forall l l', l = l' ->
  forall (p p': PointCSetoid), p[=]p' -> (invariant (l, p) <-> invariant (l', p')).
Proof.
  unfold invariant. grind ltac:(destruct l').
Qed.

Program Definition invariant_squares (l: Location): OpenSquare :=
  match l with
  | Cool => (above ('0), above ('5))
  | Heat => (('0, '3): Range, below ('10))
  | Check => (('0, '1): Range, unbounded_range)
  end.

Lemma invariant_squares_correct (l : Location) (p : Point):
  invariant (l, p) -> in_osquare p (invariant_squares l).
Proof.
  unfold invariant. grind ltac:(destruct l).
Qed.

(* Initial state *)

Program Definition initial_square: OpenSquare := (('0, '0), ('5, '10)): Square.

Definition initial_location := Heat.
Definition initial (s: State): Prop :=
  loc s = initial_location /\ in_osquare (point s) initial_square.

Lemma initial_invariant (s: State): initial s -> invariant s.
Proof.
  unfold initial, invariant, initial_location, initial_square.
  hs_solver.
Qed.

(* Flow *)

Definition clock_flow (l: Location): Flow CRasCSetoid := flow.positive_linear.f.

Definition temp_flow (l: Location): Flow CRasCSetoid :=
  match l with
  | Heat => flow.scale.flow ('2) flow.positive_linear.f
  | Cool => dec_exp_flow.f
  | Check => flow.scale.flow ('(1#2)) dec_exp_flow.f
  end.

Definition flow l := product_flow (clock_flow l) (temp_flow l).

(* Flow inverses *)

Definition clock_flow_inv (l: Location) (a b: OpenRange): OpenRange :=
  square_flow_conditions.one_axis.flow_range
    _ flow.positive_linear.inv_correct flow.positive_linear.mono a b.

Definition temp_flow_inv (l: Location): OpenRange -> OpenRange -> OpenRange :=
  match l with
  | Heat => flow.scale.inv two_pos (square_flow_conditions.one_axis.flow_range
    _ flow.positive_linear.inv_correct flow.positive_linear.mono)
  | Cool => dec_exp_flow.inv milli
  | Check => flow.scale.inv half_pos (dec_exp_flow.inv milli)
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
    apply dec_exp_flow.inv_correct.
  apply flow.scale.inv_correct, dec_exp_flow.inv_correct.
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
  ( square_abstraction.apply_Reset (clock_reset l l') (fst p)
  , square_abstraction.apply_Reset (temp_reset l l') (snd p)).

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

(* Concrete system *)

Definition concrete_system: concrete.System :=
  concrete.Build_System _ _ NoDup_locations initial invariant
  initial_invariant invariant_wd flow guard reset.

Definition concrete_state_unsafe (s: concrete.State concrete_system): Prop :=
  temp s <= '(45#10).

(* intervals *)

Inductive ClockInterval: Set := CI0_C | CIC_12 | CI12_1 | CI1_2 | CI2_3 | CI3_.
Inductive TempInterval: Set := TI_5 | TI5_6 | TI6_8 | TI8_9 | TI9_10 | TI10_.

Program Definition ClockInterval_qbounds (i: ClockInterval): OpenQRange :=
  (match i with
  | CI0_C => (0, centi): QRange
  | CIC_12 => (centi, 1#2): QRange
  | CI12_1 => (1#2, 1+centi): QRange
  | CI1_2 => (1+centi, 2-centi): QRange
  | CI2_3 => (2-centi, 3): QRange
  | CI3_ => (Some 3, None)
  end)%Q.

Definition ClockInterval_bounds (i: ClockInterval): OpenRange := ClockInterval_qbounds i.

Program Definition TempInterval_qbounds (i: TempInterval): OpenQRange :=
  (match i with
  | TI_5 => (None, Some (5-centi))
  | TI5_6 => (5-centi, 6): QRange
  | TI6_8 => (6, 8): QRange
  | TI8_9 => (8, 9-deci): QRange
  | TI9_10 => (9-deci, 10): QRange
  | TI10_ => (Some 10, None)
  end)%Q.

Definition TempInterval_bounds (i: TempInterval): OpenRange :=
  TempInterval_qbounds i.

Instance clock_intervals: ExhaustiveList ClockInterval
  := { exhaustive_list := CI0_C :: CIC_12 :: CI12_1 :: CI1_2 :: CI2_3 :: CI3_ :: nil }.
Proof. hs_solver. Defined.

Instance temp_intervals: ExhaustiveList TempInterval
  := { exhaustive_list := TI_5 :: TI5_6 :: TI6_8 :: TI8_9 :: TI9_10 :: TI10_ :: nil }.
Proof. hs_solver. Defined.

Program Definition s_absClockInterval (r: CR):
    { i | '0 <= r -> in_orange (ClockInterval_bounds i) r } :=
  if CR_le_le_dec r ('centi) then CI0_C else
  if CR_le_le_dec r ('(1#2)) then CIC_12 else
  if CR_le_le_dec r ('(1+centi)) then CI12_1 else
  if CR_le_le_dec r ('(2-centi)) then CI1_2 else
  if CR_le_le_dec r ('3) then CI2_3 else CI3_.

Program Definition s_absTempInterval (r: CR):
    { i | in_orange (TempInterval_bounds i) r } :=
  if CR_le_le_dec r ('(5-centi)) then TI_5 else
  if CR_le_le_dec r ('6) then TI5_6 else
  if CR_le_le_dec r ('8) then TI6_8 else
  if CR_le_le_dec r ('(9-deci)) then TI8_9 else
  if CR_le_le_dec r ('10) then TI9_10 else TI10_.

Program Definition absClockInterval (r: CR): ClockInterval := s_absClockInterval r.
Program Definition absTempInterval (r: CR): TempInterval := s_absTempInterval r.

Lemma absClockInterval_wd (r r': CR): st_eq r r' -> absClockInterval r = absClockInterval r'.
Proof.
  unfold absClockInterval, s_absClockInterval. hs_solver.
Qed.

Lemma absTempInterval_wd (r r': CR): st_eq r r' -> absTempInterval r = absTempInterval r'.
Proof.
  unfold absTempInterval, s_absTempInterval. hs_solver.
Qed.

Instance ClockInterval_eq_dec: EquivDec.EqDec ClockInterval eq.
Proof. hs_solver. Defined.

Instance TempInterval_eq_dec: EquivDec.EqDec TempInterval eq.
Proof. hs_solver. Defined.

Lemma NoDup_clock_intervals: NoDup clock_intervals.
Proof. hs_solver. Qed.

Lemma NoDup_temp_intervals: NoDup temp_intervals.
Proof. hs_solver. Qed.

Lemma regions_cover_invariants l (p: concrete.Point concrete_system):
  concrete.invariant (l, p) ->
  square_abstraction.in_region ClockInterval_bounds TempInterval_bounds p
    (square_abstraction.absInterval absClockInterval absTempInterval p).
Proof with auto.
  destruct p.
  simpl concrete.invariant. unfold invariant.
  unfold square_abstraction.in_region, square_abstraction.absInterval,
    absClockInterval, absTempInterval.
  simplify_hyps. simplify_proj. split...
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

Let in_region := square_abstraction.in_region ClockInterval_bounds TempInterval_bounds.

Definition he (f: Flow CRasCSetoid) (flow_inc: forall x, strongly_increasing (f x)) (t: Time) (x b: CR):
  b <= x -> f x t <= b -> t <= '0.
Proof with auto.
  intros.
  apply (@strongly_increasing_inv_mild (f x) (flow_inc x))...
  rewrite (flow_zero f).
  apply CRle_trans with b...
Qed.

Lemma heat_temp_flow_inc: (forall x : CRasCSetoid, strongly_increasing (temp_flow Heat x)).
  repeat intro.
  simpl.
  unfold scale.raw.
  unfold positive_linear.f.
  simpl.
  apply CRlt_wd with (' 2 * x0 + x) (' 2 * x' + x).
      apply (Radd_comm CR_ring_theory).
    apply (Radd_comm CR_ring_theory).
  apply t1.
  apply (CRmult_lt_pos_r H).
  apply (Qpos_CRpos (2#1)%Qpos).
Qed.

Lemma clock_flow_inc: forall l x, strongly_increasing (clock_flow l x).
Proof with auto.
  intros.
  unfold clock_flow.
  repeat intro.
  simpl.
  apply CRlt_wd with (x0 + x) (x' + x).
      apply (Radd_comm CR_ring_theory).
    apply (Radd_comm CR_ring_theory).
  apply t1.
  assumption.
Qed.

Definition clock_hints (l: Location) (r r': Region): r <> r' -> option
  (abstraction.AltHint concrete_system in_region l r r').
Proof with auto.
  intros.
  unfold abstraction.AltHint, in_region, square_abstraction.in_region,
    square_abstraction.square, in_osquare.
  simpl.
  destruct r. destruct r'.
  unfold in_orange at 1 3.
  unfold ClockInterval_bounds.
  simpl.
  destruct (ClockInterval_qbounds c).
  destruct (ClockInterval_qbounds c0).
  destruct x. destruct x0.
  destruct o1. destruct o4.
      simpl.
      destruct (Qeq_dec q q0).
        constructor.
        intros.
        destruct H0. destruct H1. destruct H0. destruct H1.
        apply (@he (clock_flow l) ) with (fst p) ('q)...
          apply clock_flow_inc.
        simpl.
        rewrite q1...
      exact None.
    exact None.
  exact None.
Defined.

Definition temp_hints (l: Location) (r r': Region): r <> r' -> option
  (abstraction.AltHint concrete_system in_region l r r').
Proof with auto.
  intros.
  destruct r. destruct r'.
  destruct l.
      unfold abstraction.AltHint, in_region, square_abstraction.in_region,
        square_abstraction.square, in_osquare.
      simpl.
      unfold in_orange at 2 4.
      unfold orange_right at 1. unfold orange_left at 2.
      unfold TempInterval_bounds.
      destruct (TempInterval_qbounds t).
      destruct (TempInterval_qbounds t0).
      destruct x.
      destruct x0.
      destruct o1.
        destruct o4.
          simpl.
          destruct (Qeq_dec q q0).
            constructor.
            intros.
            destruct H0. destruct H1.
            destruct H2. destruct H3.
            apply (@he (temp_flow Heat) heat_temp_flow_inc t1 (snd p) ('q) H2).
            rewrite q1...
          exact None.
        exact None.
      exact None.
    exact None.
  exact None.
Defined.

Definition hints (l: Location) (r r': Region) (E: r <> r') :=
  options (clock_hints l E) (temp_hints l E).

Definition in_region_wd: forall (x x': concrete.Point concrete_system),
  x[=]x' -> forall r, in_region x r -> in_region x' r
  := @square_abstraction.in_region_wd ClockInterval TempInterval Location
    _ _ _ _ _ _ ClockInterval_bounds TempInterval_bounds.

Lemma chicken: forall x : concrete.Location concrete_system * concrete.Point concrete_system,
  concrete.invariant x ->
  square_abstraction.in_region ClockInterval_bounds TempInterval_bounds
    (snd x) (square_abstraction.absInterval absClockInterval absTempInterval (snd x)).
Proof with auto.
  intros.
  destruct x as [a [b c]]. simpl.
  destruct H as [V W]...
  split.
    unfold absClockInterval.
    simpl. destruct (s_absClockInterval b)...
  unfold absTempInterval.
  simpl. destruct (s_absTempInterval c)...
      (* todo: this should be done generically by square_abstraction *)
Qed.

Definition abstract_system (eps : Qpos) : abstract.System concrete_system.
Proof with auto.
  intro eps.
  eapply (@abstraction.abstract_system' _ _ _ concrete_system in_region
   in_region_wd
   (square_abstraction.NoDup_squareIntervals NoDup_clock_intervals NoDup_temp_intervals) _
  chicken
    (@square_abstraction.do_cont_trans _ _ _ _ _ _ _ _ _
    ClockInterval_bounds TempInterval_bounds clock_flow temp_flow
    clock_flow_inv temp_flow_inv clock_rfis temp_rfis _ _ _ _ _ _ invariant_squares_correct _ _ eps)
    (mk_DO (over_initial eps)) (abstraction.dealt_hints in_region_wd hints) regions_cover_invariants).
    apply (square_abstraction.NoDup_disc_trans
      NoDup_clock_intervals NoDup_temp_intervals
      (square_abstraction.do_invariant ClockInterval_bounds TempInterval_bounds _ _ invariant_squares_correct eps)
      NoDup_locations
      clock_reset temp_reset (mk_DO (over_guard eps)) eps).
  apply (@square_abstraction.respects_disc _ _ _ _ _ _ _ _ _ ClockInterval_bounds TempInterval_bounds absClockInterval absTempInterval clock_flow temp_flow)...
    unfold absClockInterval. intros.
    destruct (s_absClockInterval (fst p))... destruct H...
  unfold absTempInterval. intros.
  destruct (s_absTempInterval (snd p))...
Defined.

Definition abs_sys: abstract.System concrete_system := abstract_system milli.

Definition vs := abstract_as_graph.vertices abs_sys.
Definition g := abstract_as_graph.g abs_sys.
Definition graph := flat_map (@digraph.edges g) vs.

Definition thermo_is_safe := 
  forall s : concrete.State concrete_system,
    concrete_state_unsafe s -> ~ concrete.reachable s.

Definition unsafe_abstract_states :=
  List.flat_map (fun l => map (fun ci => (l, (ci, TI_5))) clock_intervals) locations.

Definition unsafe : bool :=
  abstract_as_graph.some_reachable abs_sys unsafe_abstract_states.

Definition unsafe_abstracts_cover_unsafe_concretes:
  forall s, concrete_state_unsafe s ->
  forall r, abstract.abs abs_sys s r -> In r unsafe_abstract_states.
Proof with auto.
  intros [l [c t]] H [l' [ci ti]] [H0 [_ tin]].
  subst.
  apply <- in_flat_map.
  exists l'. split...
  simpl.
  replace ti with TI_5. destruct ci; auto 10.
  destruct tin.
  destruct ti; auto; elimtype False;
    apply (util.flip (@CRlt_le_asym _ _) (CRle_trans H1 H)), CRlt_Qlt;
    vm_compute...
Qed.

Theorem unsafe_correct: unsafe = false -> thermo_is_safe.
Proof with auto.
  unfold unsafe, thermo_is_safe.
  intros srf [l [px py]] su.
  apply (abstract_as_graph.states_unreachable (ahs:=abs_sys) concrete_state_unsafe unsafe_abstract_states)...
  apply unsafe_abstracts_cover_unsafe_concretes.
Qed.

Theorem thermo_safe : thermo_is_safe.
Proof. Time apply unsafe_correct; vm_compute; ref. Qed.

Print Assumptions thermo_safe.
