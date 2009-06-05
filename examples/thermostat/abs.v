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

Lemma absClockInterval_correct p l (i: invariant (l, p)):
  in_orange (ClockInterval_bounds (absClockInterval (fst p))) (fst p).
Proof.
  intros p l [A B]. unfold absClockInterval.
  destruct_call s_absClockInterval. auto.
Qed.

Lemma absTempInterval_correct p l (i: invariant (l, p)):
  in_orange (TempInterval_bounds (absTempInterval (snd p))) (snd p).
Proof.
  intros p l [A B]. unfold absTempInterval.
  destruct_call s_absTempInterval. auto.
Qed.

Definition ap: abstract.Parameters conc.system :=
  square_abstraction.ap NoDup_clock_intervals NoDup_temp_intervals
  _ _ _ _ _ _ _ _ _ _ _ _ _ absClockInterval_correct absTempInterval_correct.

(* Abstracted initial: *)

Program Definition initial_square: OpenSquare := (('0, '0), ('5, '10)): Square.
Definition initial_location := Heat.

Lemma initial_representative: forall s: concrete.State conc_thermo.system,
  concrete.initial s -> loc s = initial_location /\
  in_osquare (point s) initial_square.
Proof.
  intros [l s] [H [H0 [H1 H2]]].
  unfold in_osquare, in_orange.
  simpl. rewrite H2. auto.
Qed.

Let initial_dec := @square_abstraction.initial_dec
  _ _ _ _ _ _ _ _ _ NoDup_clock_intervals NoDup_temp_intervals
  _ _ _ _ _ _ initial_invariant _ _ invariant_wd NoDup_locations
  _ _ absClockInterval_correct absTempInterval_correct
  _ _ initial_representative.

(* Abstracted invariant: *)

Program Definition invariant_squares (l: Location): OpenSquare :=
  match l with
  | Cool => (above ('0), above ('5))
  | Heat => (('0, '3): Range, below ('10))
  | Check => (('0, '1): Range, unbounded_range)
  end.

Lemma invariant_squares_correct (l : Location) (p : Point):
  invariant (l, p) -> in_osquare p (invariant_squares l).
Proof. unfold invariant. grind ltac:(destruct l). Qed.

Let invariant_dec :=
  square_abstraction.invariant_dec
    ClockInterval_bounds TempInterval_bounds _ _ invariant_squares_correct.

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

Definition clock_hints (l: Location) (r r': abstract.Region ap): r <> r' ->
  option (abstraction.AltHint ap l r r').
Proof with auto.
  intros l [ci ti] [ci' ti'] H.
  unfold abstraction.AltHint, abstract.in_region, square_abstraction.in_region,
    square_abstraction.square, in_osquare.
  simpl.
  unfold square_abstraction.in_region, in_osquare,
    in_orange at 1 3, ClockInterval_bounds.
  simpl @fst. simpl @snd.
  destruct (ClockInterval_qbounds ci) as [[ci_lo ci_hi] ci_le].
  destruct (ClockInterval_qbounds ci') as [[ci'_lo ci'_hi] ci'_le].
  destruct ci_lo; [idtac | exact None].
  destruct ci'_hi; [idtac | exact None].
  destruct (Qeq_dec q q0) as [A|B]; [idtac | exact None].
  apply Some.
  intros p [[H0 H4] H2] t [[H1 H5] H3].
  apply (strongly_increasing_inv_mild) with (clock_flow l (fst p))...
  rewrite flow_zero.
  apply CRle_trans with ('q)...
  rewrite A...
Defined.

Definition temp_hints (l: Location) (r r': abstract.Region ap): r <> r' -> option
  (abstraction.AltHint ap l r r').
Proof with auto.
  intros l [ci ti] [ci' ti'] H.
  destruct l; [idtac | exact None | exact None].
  unfold abstraction.AltHint, abstract.in_region, square_abstraction.in_region,
   square_abstraction.square, in_osquare.
  simpl.
  unfold square_abstraction.in_region, in_osquare.
  simpl @fst. simpl @snd.
  unfold in_orange at 2 4.
  unfold orange_right at 1. unfold orange_left at 2.
  unfold TempInterval_bounds.
  destruct (TempInterval_qbounds ti) as [[ti_lo ti_hi] ti_le].
  destruct (TempInterval_qbounds ti') as [[ti'_lo ti'_hi] ti'_le].
  destruct ti_lo; [idtac | exact None].
  destruct ti'_hi; [idtac | exact None].
  simpl.
  destruct (Qeq_dec q q0); [idtac | exact None].
  apply Some.
  intros p [H0 [H2 H4]] t [H1 [H3 H5]].
  apply (strongly_increasing_inv_mild) with (temp_flow Heat (snd p))...
    unfold temp_flow...
  rewrite flow_zero.
  apply CRle_trans with ('q)...
  rewrite q1...
Defined.
  (* Todo: Automate these two above. *)

Definition hints (l: Location) (r r': abstract.Region ap) (E: r <> r') :=
  options (clock_hints l E) (temp_hints l E).

(* The abstract system: *)

Program Definition disc_trans_dec eps :=
  square_abstraction.disc_trans
    NoDup_clock_intervals NoDup_temp_intervals
    clock_flow temp_flow _ initial_invariant reset invariant_wd NoDup_locations
    absClockInterval absTempInterval
    (invariant_dec eps) clock_reset temp_reset _
    absClockInterval_correct absTempInterval_correct (guard_dec eps) eps.

Let cont_trans eps := abstraction.cont_trans
    (@abstraction.dealt_hints _ ap hints)
    (square_abstraction.cont_trans_cond_dec
      clock_flow_inv temp_flow_inv clock_rfis temp_rfis
      invariant_squares invariant_squares_correct eps).

Definition system (eps: Qpos): abstract.System ap :=
  abstract.Build_System (initial_dec eps) (disc_trans_dec eps) (cont_trans eps).

(* Abstract safety *)

  (* The concrete unsafety condition was specified as a predicate on
   concrete states. Our task is to come up with a list of corresponding abstract
   states. The square_abstraction module can generate this list if we can
   overestimate the concrete unsafety condition with a list of open squares, which
   we can. So let us define these, first. *)

  Obligation Tactic := Qle_constants.
  Program Definition unsafe_square: OpenSquare :=
    (unbounded_range, below ('(45#10))).

  Definition unsafe_squares (l: Location): list OpenSquare := unsafe_square :: nil.

  (* Of course, we must prove that these actually cover the unsafe
  concrete states: *)

  Definition unsafe_squares_representative s: unsafe s ->
    exists q, In q (unsafe_squares (fst s)) /\ in_osquare (snd s) q.
  Proof.
    unfold unsafe. intuition.
    exists unsafe_square.
    simpl. repeat split; auto.
  Qed.

  (* We can now invoke square_abstraction's unsafe_abstract to obtain a list
  of abstract states that cover the unsafe concrete states. This list will be a key
  ingredient in safe.v. *)

  Definition unsafe_abstract: Qpos ->
    sig (fun ss: list (abstract.State conc.system (abstract.Region ap)) =>
    LazyProp (forall s, unsafe s -> forall r, abstract.abs ap s r -> In r ss))
      := square_abstraction.unsafe_abstract
        NoDup_clock_intervals NoDup_temp_intervals
        _ _ _ _ absClockInterval_correct absTempInterval_correct unsafe
        _ unsafe_squares_representative.
