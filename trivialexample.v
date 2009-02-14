Require Export Coq.Reals.Reals.
Require Export Coq.Relations.Relations.
Require Import List.
Require Import Fourier.
Require Import util.
Require Import geometry.
Require Import monotonic_flow.
Require concrete.
Require abstract.
Require respect.
Require abstraction.
Require square_abstraction.
Set Implicit Arguments.

Inductive Location: Set := Up | Down.

Definition Location_eq_dec (l l': Location): {l=l'}+{l<>l'}.
  destruct l; destruct l'; auto; right; discriminate.
Defined.

Definition locations: list Location := Up :: Down :: List.nil.

Lemma locations_complete l: List.In l locations.
Proof. destruct l; compute; tauto. Qed.

Let State: Set := prod Location Point.

Definition initial (s: State): Prop := s = (Up, (0, 0)%R).

Definition invariant (s: State): Prop :=
  match fst s with
  | Up => (0 <= fst (snd s) <= 2 /\ 0 <= snd (snd s) <= 2)%R
  | Down => (1 <= fst (snd s) <= 3 /\ 1 <= snd (snd s) <= 3)%R
  end.

Program Definition invariant_squares (l: Location): Square :=
  match l with
  | Up => ((0, 2), (0, 2))
  | Down => ((1, 3), (1, 3))
  end.

Solve Obligations using simpl; auto with real.
Next Obligation. fourier. Qed.
Next Obligation. fourier. Qed.

Lemma invariant_squares_correct (l : Location) (p : Point):
  invariant (l, p) -> in_square p (invariant_squares l).
Proof.
  intros. destruct p.
  destruct l;
   destruct H; destruct H; destruct H0;
   split; split; assumption.
Qed.

Lemma invariant_initial s: initial s -> invariant s.
Proof.
  destruct s. unfold initial, invariant.
  simpl. intros. inversion H. subst.
  simpl. split; auto with real.
Qed.

Definition Xflow (l: Location) (x: R) (t: Time): R :=
  match l with Up => x + t | Down => x - t end.
Definition Yflow (l: Location) (y: R) (t: Time): R :=
  match l with Up => y + t | Down => y - t end.

Lemma Xflows l: concrete.flows (Xflow l).
  intros. apply concrete.Build_flows; destruct l; simpl; intros; field.
Qed.
Lemma Yflows l: concrete.flows (Yflow l).
  intros. apply concrete.Build_flows; destruct l; simpl; intros; field.
Qed.

Lemma Xmono l: mono (Xflow l).
Proof. destruct l; [left | right]; compute; intros; fourier. Qed.
Lemma Ymono l: mono (Yflow l).
Proof. destruct l; [left | right]; compute; intros; fourier. Qed.

Definition Xflow_inv (l: Location) (x x': R): Time :=
  match l with Up => x' - x | Down => x - x' end.
Definition Yflow_inv (l: Location) (y y': R): Time :=
  match l with Up => y' - y | Down => y - y' end.

Lemma Xflow_inv_correct l x x': Xflow l x (Xflow_inv l x x') = x'.
Proof. destruct l; compute; intros; field. Qed.
Lemma Yflow_inv_correct l y y': Yflow l y (Yflow_inv l y y') = y'.
Proof. destruct l; compute; intros; field. Qed.

Definition guard (s: State) (l: Location): Prop :=
  match fst s, l with
  | Up, Down => (fst (snd s) > 1 /\ snd (snd s) > 1)%R
  | Down, Up => (fst (snd s) < 2 /\ snd (snd s) < 2)%R
  | _, _ => False
  end.

Definition reset (l l': Location) (p: Point): Point := p.

Definition concrete_system: concrete.System :=
  concrete.Build_System _ _ invariant_initial _
  (fun l => concrete.product_flows (Xflows l) (Yflows l)) guard reset.

Inductive Interval: Set := I01 | I12 | I23.

Definition Interval_eq_dec (i i': Interval): {i=i'}+{i<>i'}.
  destruct i; destruct i'; auto; right; discriminate.
Defined.

Program Definition interval_bounds (i: Interval):
  { ab: R * R | fst ab <= snd ab } :=
    match i with I01 => (0, 1) | I12 => (1, 2) | I23 => (2, 3) end.
Solve Obligations using simpl; auto with real.

Definition intervals: list Interval := I01 :: I12 :: I23 :: List.nil.

Lemma intervals_complete: forall i, List.In i intervals.
Proof. destruct i; compute; auto. Qed.

Definition absInterval (r: R): Interval :=
  if Rle_dec r 1 then I01 else
  if Rle_dec r 2 then I12 else I23.

Lemma regions_cover_invariants l p: concrete.invariant concrete_system (l, p) ->
  square_abstraction.in_region interval_bounds interval_bounds p
    (square_abstraction.absInterval absInterval absInterval p).
Proof with auto.
  intros.
  destruct p. rename r into x. rename r0 into y.
  unfold square_abstraction.absInterval, square_abstraction.in_region.
  simpl.
  simpl in H.
  unfold invariant in H. simpl in H.
  unfold absInterval.
  simpl.
  destruct l.
    destruct H. destruct H. destruct H0.
    split.
      destruct (Rle_dec x 1); simpl.
	split...
      destruct (Rle_dec x 2); simpl.
	set (Rnot_le_lt _ _ n).
        unfold in_range, range_left, range_right. simpl. split; fourier.
      set (Rnot_le_lt _ _ n0).
      split; fourier.
    unfold in_range, range_left, range_right. simpl.
    destruct (Rle_dec y 1); simpl...
    set (Rnot_le_lt _ _ n).
    destruct (Rle_dec y 2); simpl.
      split; fourier.
    set (Rnot_le_lt _ _ n0).
    split; fourier.
  destruct H. destruct H. destruct H0.
  unfold in_square, in_range, range_left, range_right. simpl.
  split.
    destruct (Rle_dec x 1); simpl. split... fourier.
    set (Rnot_le_lt _ _ n).
    destruct (Rle_dec x 2); simpl...
    set (Rnot_le_lt _ _ n0).
    split; fourier.
  destruct (Rle_dec y 1); simpl. split; fourier.
  set (Rnot_le_lt _ _ n).
  destruct (Rle_dec y 2); simpl. split; fourier.
  set (Rnot_le_lt _ _ n0).
  split; fourier.
Qed.

Definition invariant_overestimation
  (ls: prod Location (square_abstraction.SquareInterval Interval Interval)): Prop
  := squares_overlap (invariant_squares (fst ls))
    (square_abstraction.square interval_bounds interval_bounds (snd ls)).

Definition invariant_overestimator: decideable_overestimator
  (square_abstraction.abstract_invariant interval_bounds interval_bounds invariant).
Proof with auto.
  apply (Build_decideable_overestimator
    (square_abstraction.abstract_invariant interval_bounds interval_bounds invariant)
     invariant_overestimation).
    unfold invariant_overestimation.
    intros.
    apply squares_overlap_dec.
  intros.
  unfold invariant_overestimation.
  unfold square_abstraction.abstract_invariant in H.
  destruct H.
  destruct H.
  apply squares_share_point with x...
  apply invariant_squares_correct...
Defined.

Lemma increasing_id: increasing id.
Proof. unfold increasing. auto. Qed.

Definition component_reset (l l': Location): R -> R := id.

Lemma crinc l l': increasing (component_reset l l').
  intros.
  apply increasing_id.
Qed.

Definition guard_overestimator:
  decideable_overestimator
  (square_abstraction.abstract_guard interval_bounds interval_bounds guard).
Proof with auto.
  apply Build_decideable_overestimator with (fun _ => True)...
Defined.

Definition disc_overestimator:
  decideable_overestimator
    (abstraction.discrete_transition_condition
     concrete_system (square_abstraction.in_region interval_bounds interval_bounds)).
Proof with auto.
  apply square_abstraction.make_disc_decider with component_reset component_reset.
          exact invariant_overestimator.
        exact crinc.
      exact crinc.
    destruct p.
    reflexivity.
  exact guard_overestimator.
Qed.

Lemma initial_overestimator: decideable_overestimator
  (abstraction.initial_condition concrete_system
     (square_abstraction.in_region interval_bounds interval_bounds)).
Proof with auto.
  apply (Build_decideable_overestimator
    (abstraction.initial_condition concrete_system
     (square_abstraction.in_region interval_bounds interval_bounds)) (fun s => s = (Up, (I01, I01)))).
    intros.
    apply abstraction.State_eq_dec.
      apply Location_eq_dec.
    apply square_abstraction.SquareInterval_eq_dec; apply Interval_eq_dec.
  intros.
  destruct H. destruct H. simpl in H0. unfold initial in H0.
  destruct a.
  simpl in H0.
  inversion H0.
  subst. clear H0.
  simpl in H.
  unfold square_abstraction.in_region in H.
  destruct s.
  simpl in H. destruct H. destruct H. destruct H0.
  unfold range_left, range_right in *.
  destruct i; destruct i0; simpl in *; try auto; elimtype False; fourier.
Qed.

Definition abstract_system:
  {s : abstract.System &
  {f : concrete.State concrete_system -> abstract.State s
     | respect.Respects s f} }.
Proof with auto.
  apply (@abstraction.result concrete_system
    Location_eq_dec
    (square_abstraction.SquareInterval Interval Interval)
    (square_abstraction.SquareInterval_eq_dec Interval_eq_dec Interval_eq_dec)
    (square_abstraction.in_region interval_bounds interval_bounds)
    (square_abstraction.absInterval absInterval absInterval)
    locations locations_complete
    (square_abstraction.squareIntervals intervals intervals)
    (square_abstraction.squareIntervals_complete _ intervals_complete _ intervals_complete)).
        apply square_abstraction.cont_decider with Xflow_inv Yflow_inv.
                exact Xflow_inv_correct.
              exact Yflow_inv_correct.
            exact Xmono.
          exact Ymono.
        exact invariant_overestimator.
      apply disc_overestimator.
    exact initial_overestimator.
  intros.
  apply regions_cover_invariants with l...
Qed.

Print Assumptions abstract_system.
