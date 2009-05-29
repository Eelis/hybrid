Require Import util list_util.
Require Import geometry.
Require Import monotonic_flow.
Require Import hs_solver.
Require decreasing_exponential_flow.
Require abstract abstraction square_abstraction.
Require EquivDec.

Require Import thermostat.conc.
Module conc_thermo := thermostat.conc.

Set Implicit Arguments.

Open Local Scope CR_scope.

Definition half_pos: CRpos ('(1#2)) := Qpos_CRpos (1#2).
Definition two_pos: CRpos ('2) := positive_CRpos 2.

Hint Resolve two_pos.

Definition above (c: CR): OpenRange := exist _ (Some c, None) I.
Definition below (c: CR): OpenRange := exist _ (None, Some c) I.

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
      unfold temp_flow_inv.
      apply flow.scale.inv_correct.
      unfold range_flow_inv_spec. intros.
      apply square_flow_conditions.one_axis.flow_range_covers with p...
    apply dec_exp_flow.inv_correct.
  apply flow.scale.inv_correct, dec_exp_flow.inv_correct.
Qed.

(* Abstract regions: *)

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

Lemma regions_cover_invariants l p:
  invariant (l, p) ->
  square_abstraction.in_region ClockInterval_bounds TempInterval_bounds p
    (square_abstraction.absInterval absClockInterval absTempInterval p).
Proof with auto.
  destruct p.
  unfold invariant.
  unfold square_abstraction.in_region, square_abstraction.absInterval,
    absClockInterval, absTempInterval.
  simplify_hyps. simplify_proj. split...
Qed.

Definition Region: Set := prod ClockInterval TempInterval.

Let in_region := square_abstraction.in_region ClockInterval_bounds TempInterval_bounds.

Definition in_region_wd: forall (x x': concrete.Point conc_thermo.system),
  x[=]x' -> forall r, in_region x r -> in_region x' r
  := @square_abstraction.in_region_wd _ _ Location
    _ _ _ _ _ _ ClockInterval_bounds TempInterval_bounds.

(* Abstracted initial: *)

Program Definition initial_square: OpenSquare := (('0, '0), ('5, '10)): Square.
Definition initial_location := Heat.

Lemma initial_representative: forall s: concrete.State conc_thermo.system,
  let (l, p) := s in
    concrete.initial s -> l = initial_location /\ in_osquare p initial_square.
Proof.
  intros [l s] [H [H0 [H1 H2]]].
  unfold in_osquare, in_orange.
  simpl. rewrite H2. auto.
Qed.

Let initial_dec := square_abstraction.initial_dec
  ClockInterval_bounds TempInterval_bounds _ _ initial_representative .

(* Abstracted invariant: *)

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

(* Abstracted guard: *)

Definition guard_square (l l': Location): option OpenSquare :=
  match l, l' with
  | Heat, Cool => Some (unbounded_range, above ('9))
  | Cool, Heat => Some (unbounded_range, below ('6))
  | Heat, Check => Some (above ('2), unbounded_range)
  | Check, Heat => Some (above ('(1#2)), unbounded_range)
  | _, _ => None
  end.

Lemma guard_squares_correct: forall s l',
  concrete.guard conc_thermo.system s l' <->
  match guard_square (loc s) l' with
  | None => False
  | Some v => in_osquare (point s) v
  end.
Proof.
  destruct s as [l [x y]].
  destruct l; destruct l'; repeat split; simpl; auto; intros [[A B] [C D]]; auto.
Qed.

Let guard_dec := square_abstraction.guard_dec
  ClockInterval_bounds TempInterval_bounds guard_square guard_squares_correct.

(* Hints: *)

Definition he (f: Flow CRasCSetoid) (flow_inc: forall x, strongly_increasing (f x)) (t: Time) (x b: CR):
  b <= x -> f x t <= b -> t <= '0.
Proof with auto.
  intros.
  apply (@strongly_increasing_inv_mild (f x) (flow_inc x))...
  rewrite (flow_zero f).
  apply CRle_trans with b...
Qed.

Definition clock_hints (l: Location) (r r': Region): r <> r' -> option
  (abstraction.AltHint conc_thermo.system in_region l r r').
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
        simpl.
        rewrite q1...
      exact None.
    exact None.
  exact None.
Defined.

Definition temp_hints (l: Location) (r r': Region): r <> r' -> option
  (abstraction.AltHint conc_thermo.system in_region l r r').
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
            apply (@he (temp_flow Heat)) with (snd p) ('q)...
              unfold temp_flow...
            rewrite q1...
          exact None.
        exact None.
      exact None.
    exact None.
  exact None.
Defined.

Definition hints (l: Location) (r r': Region) (E: r <> r') :=
  options (clock_hints l E) (temp_hints l E).

(* The abstract system: *)

Definition system (eps: Qpos): abstract.System conc_thermo.system.
Proof with auto.
  intro eps.
  eapply (@abstraction.abstract_system _ _ _ (square_abstraction.NoDup_squareIntervals NoDup_clock_intervals NoDup_temp_intervals) conc_thermo.system in_region
   in_region_wd _
   (fun x => @regions_cover_invariants (fst x) (snd x))
(abstraction.dealt_hints in_region_wd hints)
    (square_abstraction.cont_trans_cond_dec
    ClockInterval_bounds TempInterval_bounds clock_flow temp_flow
    clock_flow_inv temp_flow_inv clock_rfis temp_rfis _ _ _ _ _ _ invariant_squares_correct _ _ eps)
    (initial_dec eps)  regions_cover_invariants).
    Focus 2.
    apply (square_abstraction.NoDup_disc_trans
      NoDup_clock_intervals NoDup_temp_intervals
      (square_abstraction.invariant_dec ClockInterval_bounds TempInterval_bounds _ _ invariant_squares_correct eps)
      NoDup_locations
      clock_reset temp_reset (guard_dec eps) eps).
  apply (square_abstraction.respects_disc absClockInterval absTempInterval)...
    unfold absClockInterval. intros.
    destruct (s_absClockInterval (fst p))... destruct H...
  unfold absTempInterval. intros.
  destruct (s_absTempInterval (snd p))...
Defined.
