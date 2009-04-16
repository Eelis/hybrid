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
Set Implicit Arguments.

Open Local Scope CR_scope.

Definition centi: Q := (1#100).

Definition r01: Range. exists ('0, '1); CRle_constants. Defined.
Definition r15_1: Range. exists ('(1#2), '1); CRle_constants. Defined.
Definition r1_2: Range. exists ('1, '2); CRle_constants. Defined.
Definition r2_3: Range. exists ('2, '3); CRle_constants. Defined.
Definition r45_5: Range. exists ('(9#2), '5); CRle_constants. Defined.
Definition r5_6: Range. exists ('5, '6); CRle_constants. Defined.
Definition r6_9: Range. exists ('6, '9); CRle_constants. Defined.
Definition r9_10: Range. exists ('9, '10); CRle_constants. Defined.
Definition r5_10: Range. exists ('5, '10); CRle_constants. Defined.
Definition rC_10: Range. exists ('centi, '10); CRle_constants. Defined.

Inductive Location: Set := Heat | Cool | Check.

Definition Location_eq_dec (l l': Location): decision (l=l'). dec_eq. Defined.

Definition locations: list Location := Heat :: Cool :: Check :: nil.

Lemma NoDup_locations: NoDup locations.
  apply decision_true with (NoDup_dec Location_eq_dec locations).
  vm_compute. reflexivity.
Qed.

Lemma locations_complete l: In l locations.
Proof. destruct l; compute; tauto. Qed.

Let State : Type := (Location * Point)%type.

Definition point: State -> Point := snd.
Definition loc: State -> Location := fst.
Definition clock: State -> CR := fst ∘ point.
Definition temp: State -> CR := snd ∘ point.

Definition world: OpenSquare := unbounded_square.

Definition above (c: CR): OpenRange := existT OCRle (Some c, None) I.
Definition below (c: CR): OpenRange := existT OCRle (None, Some c) I.


Definition invariant (s: State): Prop :=
  'centi <= temp s /\
  match loc s with
  | Heat => temp s <= '10 /\ clock s <= '3
  | Cool => '5 <= temp s
  | Check => clock s <= '1
  end.

Let PointCSetoid: CSetoid := ProdCSetoid CRasCSetoid CRasCSetoid.

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
  | Cool => (unbounded_range, above ('5))
  | Heat => (below ('3), rC_10: OpenRange)
  | Check => (below ('1), above ('centi))
  end.

Lemma invariant_squares_correct (l : Location) (p : Point):
  invariant (l, p) -> in_osquare p (invariant_squares l).
Proof.
  unfold invariant, in_osquare, in_orange, orange_left, orange_right.
  destruct l; simpl; intuition.
Qed.

Definition initial_square: OpenSquare := (r01: OpenRange, r5_10: OpenRange).
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
  split...
  apply CRle_trans with ('1)...
  CRle_constants.
Qed.

Definition clock_flow (l: Location): Flow CRasCSetoid := c_flow.positive_linear.f 1.

Definition temp_flow (l: Location): Flow CRasCSetoid :=
  match l with
  | Heat => c_flow.positive_linear.f 2
  | Cool => c_flow.decreasing_exponential.f
  | Check => c_flow.scale.flow ('(1#2)) c_flow.decreasing_exponential.f
  end.

Definition clock_flow_inv (l: Location) (a b: OpenRange): OpenRange :=
  c_square_flow_conditions.one_axis.flow_range
    _ (c_flow.positive_linear.inv_correct 1) (c_flow.positive_linear.mono 1) a b.

Lemma half_pos: '0 < '(1#2).
Proof.
  exists ((1#2)%Qpos).
  rewrite CRminus_Qminus.
  apply (CRle_Qle (QposAsQ (1#2)) ((1#2)-0)%Q).
  firstorder.
Defined.
(* simpler but too opaque: apply CRlt_Qlt. reflexivity.*)

Definition temp_flow_inv (l: Location) (a b: OpenRange): OpenRange :=
  match l with
  | Heat => c_square_flow_conditions.one_axis.flow_range
    _ (c_flow.positive_linear.inv_correct 2) (c_flow.positive_linear.mono 2) a b
  | Cool => c_flow.decreasing_exponential.inv a b
  | Check => c_flow.scale.inv half_pos c_flow.decreasing_exponential.inv a b
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

Definition clock_reset (l l': Location) (c: CR): CR :=
  match l, l' with
  | Cool, Heat => '0
  | Heat, Check => '0
  | Check, Heat => '0
  | _, _ => c (* dummy *)
  end.

Definition temp_reset (l l': Location) (t: CR): CR := t. (* cannot reset temperature *)

Definition reset (l l': Location) (p: Point): Point :=
  (clock_reset l l' (fst p), temp_reset l l' (snd p)).

Lemma clock_reset_inc l l': increasing (clock_reset l l').
Proof with auto.
  do 5 intro.
  unfold clock_reset.
  destruct l; destruct l'...
Qed.

Lemma temp_reset_inc l l': increasing (temp_reset l l').
Proof. intros. intro. auto. Qed.

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
  locations locations_complete NoDup_locations initial invariant
  initial_invariant invariant_wd
  (fun l => product_flow (clock_flow l) (temp_flow l)) guard reset.

(* intervals: *)

Inductive ClockInterval: Set := CI_15 | CI15_1 | CI1_2 | CI2_3 | CI3_.
Inductive TempInterval: Set := TI_45 | TI45_5 | TI5_6 | TI6_9 | TI9_10 | TI10_.

Definition ClockInterval_eq_dec (i i': ClockInterval): decision (i=i'). dec_eq. Defined.
Definition TempInterval_eq_dec (i i': TempInterval): decision (i=i'). dec_eq. Defined.

Definition ClockInterval_bounds (i: ClockInterval): OpenRange :=
  match i with
  | CI_15 => below ('(1#2))
  | CI15_1 => r15_1 | CI1_2 => r1_2 | CI2_3 => r2_3
  | CI3_ => above ('3)
  end.

Definition TempInterval_bounds (i: TempInterval): OpenRange :=
  match i with
  | TI_45 => below ('(9#2))
  | TI45_5 => r45_5
  | TI5_6 => r5_6
  | TI6_9 => r6_9
  | TI9_10 => r9_10
  | TI10_ => above ('10)
  end.

Definition clock_intervals: list ClockInterval := CI_15 :: CI15_1 :: CI1_2 :: CI2_3 :: CI3_ :: nil.
Definition temp_intervals: list TempInterval := TI_45 :: TI45_5 :: TI5_6 :: TI6_9 :: TI9_10 :: TI10_ :: nil.

Lemma clock_intervals_complete: forall i, List.In i clock_intervals.
Proof. destruct i; compute; tauto. Qed.

Lemma temp_intervals_complete: forall i, List.In i temp_intervals.
Proof. destruct i; compute; tauto. Qed.

Lemma NoDup_clock_intervals: NoDup clock_intervals.
  apply decision_true with (NoDup_dec ClockInterval_eq_dec clock_intervals).
  vm_compute. ref.
Qed.

Lemma NoDup_temp_intervals: NoDup temp_intervals.
  apply decision_true with (NoDup_dec TempInterval_eq_dec temp_intervals).
  vm_compute. ref.
Qed.

Definition s_absClockInterval (r: CR):
  { i: ClockInterval | in_orange (ClockInterval_bounds i) r }.
Proof with auto.
  intro.
  unfold in_orange, orange_left, orange_right.
  destruct (CR_le_le_dec r ('(1#2))). exists CI_15. simpl...
  destruct (CR_le_le_dec r ('1)). exists CI15_1...
  destruct (CR_le_le_dec r ('2)). exists CI1_2...
  destruct (CR_le_le_dec r ('3)). exists CI2_3...
  exists CI3_. simpl...
Defined.

Definition s_absTempInterval (r: CR):
  { i: TempInterval | in_orange (TempInterval_bounds i) r }.
Proof with auto.
  intro.
  unfold in_orange, orange_left, orange_right.
  destruct (CR_le_le_dec r ('(9#2))). exists TI_45. simpl...
  destruct (CR_le_le_dec r ('5)). exists TI45_5...
  destruct (CR_le_le_dec r ('6)). exists TI5_6...
  destruct (CR_le_le_dec r ('9)). exists TI6_9...
  destruct (CR_le_le_dec r ('10)). exists TI9_10...
  exists TI10_. simpl...
Defined.

Definition absClockInterval (r: CR): ClockInterval := proj1_sig (s_absClockInterval r).
Definition absTempInterval (r: CR): TempInterval := proj1_sig (s_absTempInterval r).

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
  split...
Qed.

Let Region := c_square_abstraction.SquareInterval ClockInterval TempInterval.

Definition guard_dec eps (ls : Location * Region * Location) :=
  let (lr, l2) := ls in
  let (l1, r) := lr in
    match guard_square l1 l2 with
    | Some s => osquares_overlap_dec eps (s,
        c_square_abstraction.square ClockInterval_bounds TempInterval_bounds r)
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
    Location_eq_dec ClockInterval_bounds TempInterval_bounds initial_location initial_square eps.

Lemma over_initial eps : 
  initial_dec eps >=> 
  c_abstraction.initial_condition concrete_system 
  (c_square_abstraction.in_region ClockInterval_bounds TempInterval_bounds).
Proof with auto.
  apply c_square_abstraction.over_initial.
  intros. destruct s...
Qed.

Definition abstract_system (eps : Qpos) : c_abstract.System concrete_system.
Proof with auto.
  intro eps. eapply c_abstraction.abstract_system.
              eexact (c_square_abstraction.SquareInterval_eq_dec ClockInterval_eq_dec TempInterval_eq_dec).
            eexact (c_square_abstraction.squareIntervals_complete _ clock_intervals_complete _ temp_intervals_complete).
          eexact (c_square_abstraction.NoDup_squareIntervals NoDup_clock_intervals NoDup_temp_intervals).
        eapply (@c_square_abstraction.do_cont_trans Location ClockInterval TempInterval Location_eq_dec locations locations_complete ClockInterval_bounds TempInterval_bounds clock_flow temp_flow clock_flow_inv temp_flow_inv).
              apply clock_rfis.
            apply temp_rfis.
          eexact invariant_squares_correct.
        exact eps.
      eapply c_square_abstraction.do_odisc_trans.
                eexact invariant_squares_correct.
              eexact clock_reset_inc.
            eexact temp_reset_inc.
          destruct p; ref.
        eexact (mk_DO (over_guard eps)).
      eexact eps.
    eexact (mk_DO (over_initial eps)).
  unfold c_abstraction.RegionsCoverInvariants.
  eexact regions_cover_invariants.
Defined.

Print Assumptions abstract_system.

Definition abs_sys: c_abstract.System concrete_system := abstract_system (1#100).

Definition vs := abstract_as_graph.vertices abs_sys.
Definition g := abstract_as_graph.g abs_sys.
Definition graph := flat_map (@digraph.edges g) vs.

Time Eval vm_compute in (List.length graph).
