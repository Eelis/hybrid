Require Import util list_util bnat.
Require Import geometry.
Require Import monotonic_flow.
Require Import hs_solver.
Require Import interval_spec.
Require Import tactics.
Require decreasing_exponential_flow.
Require abstract square_abstraction.
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

Hint Resolve square_flow_conditions.one_axis.flow_range_covers.

Lemma clock_rfis l: range_flow_inv_spec (clock_flow l) (clock_flow_inv l).
Proof.
  unfold clock_flow_inv; crunch.
Qed.

Lemma temp_rfis l: range_flow_inv_spec (temp_flow l) (temp_flow_inv l).
Proof. 
  destruct l; crunch.
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

Definition clock_interval := interval_spec.select_interval' system fst_mor clock_spec (fun _ _ => fst).
Definition temp_interval := interval_spec.select_interval system snd_mor temp_spec.

Definition ap: abstract.Space conc.system :=
  square_abstraction.ap _ _ _ (NoDup_bnats 6) (NoDup_bnats 6)
  _ _ clock_interval temp_interval.

(* Abstracted initial: *)

Obligation Tactic := CRle_constants.
Program Definition initial_square: OpenSquare := ((0, 0), ('5, '10)): Square.
Definition initial_location := Heat.

Lemma initial_representative: forall s: concrete.State system,
  concrete.initial s -> location s = initial_location /\
  in_osquare (point s) initial_square.
Proof.
  intros [l s] [H [H0 [H1 H2]]].
  unfold in_osquare, in_orange.
  simpl. unfold util.flip. rewrite H2. auto.
Qed.

Let initial_dec := @square_abstraction.make_initial_overestimator
  _ _ _ _ _ _ _ _ _ (NoDup_bnats 6) (NoDup_bnats 6) _ _
  clock_interval temp_interval _ _ initial_representative.

(* Abstracted invariant: *)

Definition px := @fst_mor CRasCSetoid CRasCSetoid.
Definition py := @snd_mor CRasCSetoid CRasCSetoid.

Obligation Tactic := idtac.

Program Definition invariant_squares (l: concrete.Location system):
  sig (fun s: OpenSquare => forall p, concrete.invariant (l, p) ->
    in_osquare (square_abstraction.pxy system px py p) s) :=
  match l with
  | Cool => (above 0, above ('5))
  | Heat => ((0, '3): Range, below ('10)): OpenSquare
  | Check => ((0, 1): Range, unbounded_range): OpenSquare
  end.

Solve Obligations using
  simpl @concrete.invariant; unfold invariant; grind ltac:(destruct l).

Let invariant_dec: Qpos -> overestimator (@abstract.invariant _ ap)
  := square_abstraction.make_invariant_overestimator invariant_squares.

(* Abstracted guard: *)

Definition GuardSquare l l' := fun s: option OpenSquare =>
  forall p, concrete.guard system (l, p) l' ->
    match s with
    | None => False
    | Some v => in_osquare (square_abstraction.pxy system px py p) v
    end.
  (* todo: why can't we use square_abstraction.GuardSquare below? *)

Obligation Tactic := program_simpl.

Program Definition guard_square (l l': concrete.Location system):
   sig (GuardSquare l l') :=
  match l, l' return square_abstraction.GuardSquare system _ _ l l' with
  | Heat, Cool => Some (unbounded_range, above ('9))
  | Cool, Heat => Some (unbounded_range, below ('6))
  | Heat, Check => Some (above ('2), unbounded_range)
  | Check, Heat => Some (above ('(1#2)), unbounded_range)
  | _, _ => None
  end.

Solve Obligations using
  intros; subst; repeat split; simpl; auto; intros [[A B] [C D]]; auto.
  (* todo: this takes ridiculously long *)

Let guard_dec: Qpos -> overestimator (abstract.guard ap)
 := square_abstraction.guard_dec guard_square.

(* Hints: *)

Lemma invariant_implies_lower_clock_bound l (p: concrete.Point system):
   concrete.invariant (l, p) -> 0 <= fst_mor p.
Proof. intros [H _]. assumption. Defined.

Definition clock_hints (l: Location) (r r': abstract.Region ap) (E: r <> r'):
  option (abstract_cont_trans_over.strong_redundant ap l E).
Proof with auto.
  unfold ap, abstract_cont_trans_over.strong_redundant.
  unfold square_abstraction.ap, containers.In, abstract.in_region, abstract.prod_space,
   abstract.in_region, interval_abstraction.space,
   interval_abstraction.in_region, abstract.Region.
  intros.
  assert (forall x, strongly_increasing (fst_mor ∘ concrete.flow system l x)).
    intros. cut (strongly_increasing (clock_flow l (fst x)))...
  destruct (bnat_eq_dec (fst r) (fst r')). exact None.
  apply (util.flip (@option_map _ _) (@interval_abstraction.hints system fst_mor _ _ _ (NoDup_bnats 6)
   (interval_spec.spec_bounds clock_spec)
   (interval_spec.select_interval' system fst_mor clock_spec
     invariant_implies_lower_clock_bound)
   l (fst r) (fst r') c X)).
  intuition. (* todo: takes too long *)
  apply H with p...
Defined.

Definition temp_hints (l: Location) (r r': abstract.Region ap) (E: r <> r'): option
  (abstract_cont_trans_over.strong_redundant ap l E).
Proof with auto.
  destruct l; intros; [| exact None | exact None].
  unfold abstract_cont_trans_over.strong_redundant, ap, square_abstraction.ap, containers.In, abstract.in_region, abstract.prod_space,
   abstract.in_region, interval_abstraction.space,
   interval_abstraction.in_region, abstract.Region.
  intros.
  assert (forall x, strongly_increasing (snd_mor ∘ concrete.flow system Heat x)).
    intros. cut (strongly_increasing (temp_flow Heat (snd x)))...
    unfold temp_flow...
  destruct (bnat_eq_dec (snd r) (snd r')). exact None.
  apply (util.flip (@option_map _ _) (@interval_abstraction.hints system snd_mor _ _ _ (NoDup_bnats 6)
   (interval_spec.bounds temp_spec)
   (interval_spec.select_interval system snd_mor temp_spec)
   Heat (snd r) (snd r') c X)).
  intuition. apply H with p...
Defined.

Definition hints (l: Location) (r r': abstract.Region ap) (E: r <> r') :=
  options (clock_hints l E) (temp_hints l E).

(* "Annotated" reset function which knows when it's constant and id: *)

Definition clock_reset (l l': Location): square_abstraction.Reset :=
  match l, l' with
  | Cool, Heat | Heat, Check | Check, Heat => square_abstraction.Reset_const 0
  | _, _ => square_abstraction.Reset_id (* dummy *)
  end.

(* Hm, changing the Reset_const ('0) to Reset_map (increasing_const' ('0)) triples the computation time and
 makes the proof fail, but I forgot why.. *)

Definition temp_reset (l l': Location): square_abstraction.Reset :=
  square_abstraction.Reset_id. (* dummy *)

(* The abstract system: *)

Obligation Tactic := program_simpl.

Program Definition disc_trans_dec eps :=
  square_abstraction.disc_trans
    (@id (concrete.Point system)) _ _ _
    (invariant_dec eps) (guard_dec eps) clock_reset temp_reset _ eps.

Next Obligation. intros. destruct l; destruct l'; reflexivity. Qed.

Program Let cont_trans eps := abstract_cont_trans_over.cont_trans
    (square_abstraction.cont_trans_cond_dec
    (@id (concrete.Point system)) _ _ _
      _ clock_flow_inv temp_flow_inv clock_rfis temp_rfis
      _ (invariant_dec eps) eps)
    (@abstract_cont_trans_over.weaken_hints _ ap hints).

Definition system (eps: Qpos): abstract.System ap :=
  abstract.Build_System (initial_dec eps) (disc_trans_dec eps) (abstract_cont_trans_over.cont_sharing_overestimator_from_substantial_overestimator (cont_trans eps)).

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
    sig (fun ss: list (abstract.State ap) =>
    LazyProp (forall s, unsafe s -> forall r, abstract.abs s r -> In r ss))
      := square_abstraction.unsafe_abstract
        (NoDup_bnats 6) (NoDup_bnats 6)
        _ _ clock_interval temp_interval unsafe
        _ unsafe_squares_representative.
