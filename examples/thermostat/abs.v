Require Import util list_util bnat.
Require Import geometry.
Require Import monotonic_flow.
Require Import hs_solver.
Require Import interval_spec.
Require decreasing_exponential_flow.
Require abstract abstraction square_abstraction.
Require EquivDec.

Require Import hybrid.examples.thermostat.conc.
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

Program Definition clock_spec: interval_spec.IntervalSpec 0 5 :=
  (interval_spec.bound 0 _
  (interval_spec.bound centi _
  (interval_spec.bound (1#2) _
  (interval_spec.bound (1+centi) _
  (interval_spec.bound (2-centi) _
  (interval_spec.highest 3)))))).

Program Definition temp_spec: interval_spec.IntervalSpec (5-centi) 4 :=
  (interval_spec.bound (5-centi) _
  (interval_spec.bound 6 _
  (interval_spec.bound 8 _
  (interval_spec.bound (9-deci) _
  (interval_spec.highest 10))))).

Definition ClockInterval_bounds := interval_spec.spec_bounds clock_spec.
Definition TempInterval_bounds := interval_spec.bounds temp_spec.

Definition clock_interval := interval_spec.select_interval' fst invariant clock_spec (fun _ _ => fst).
Definition temp_interval := interval_spec.select_interval snd invariant temp_spec.

Definition ap: abstract.Parameters conc.system :=
  square_abstraction.ap (NoDup_bnats 6) (NoDup_bnats 6)
  _ _ _ _ _ _ _ _ _ _ _ clock_interval temp_interval.

(* Abstracted initial: *)

Obligation Tactic := CRle_constants.
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
  _ _ _ _ _ _ _ _ _ (NoDup_bnats 6) (NoDup_bnats 6)
  _ _ _ _ _ _ initial_invariant _ _ invariant_wd NoDup_locations
  clock_interval temp_interval _ _ initial_representative.

(* Abstracted invariant: *)

Obligation Tactic := program_simpl; CRle_constants.

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
    square_abstraction.square, in_osquare, ap, square_abstraction.ap,
    square_abstraction.in_region, square_abstraction.square, prod_map.
  simpl @fst. simpl @snd.
  destruct (spec_bounds clock_spec ci) as [[ci_lo ci_hi] ci_le].
  destruct (spec_bounds clock_spec ci') as [[ci'_lo ci'_hi] ci'_le].
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
  unfold ap, square_abstraction.ap, square_abstraction.in_region,
   square_abstraction.square, prod_map.
  simpl @fst. simpl @snd.
  destruct (bounds temp_spec ti) as [[ti_lo ti_hi] ti_le].
  destruct (bounds temp_spec ti') as [[ti'_lo ti'_hi] ti'_le].
  destruct ti_lo; [idtac | exact None].
  destruct ti'_hi; [idtac | exact None].
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
    (NoDup_bnats 6) (NoDup_bnats 6)
    clock_flow temp_flow _ initial_invariant reset invariant_wd NoDup_locations
    clock_interval temp_interval
    (invariant_dec eps) clock_reset temp_reset _
    (guard_dec eps) eps.

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
        (NoDup_bnats 6) (NoDup_bnats 6)
        _ _ clock_interval temp_interval unsafe
        _ unsafe_squares_representative.
