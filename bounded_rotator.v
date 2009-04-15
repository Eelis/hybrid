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
Set Implicit Arguments.

Open Local Scope CR_scope.

Inductive Location: Set := Up | Right | Down | Left.

Definition Location_eq_dec (l l': Location): decision (l=l').
Proof. dec_eq. Defined.

Definition locations: list Location := Up :: Right :: Down :: Left :: nil.

Lemma NoDup_locations: NoDup locations.
  apply decision_true with (NoDup_dec Location_eq_dec locations).
  vm_compute. ref.  
Qed.

Lemma locations_complete l: In l locations.
Proof. destruct l; compute; tauto. Qed.

Let State : Type := (Location * Point)%type.

Definition point: State -> Point := snd.
Definition loc: State -> Location := fst.
Definition x: State -> CR := fst ∘ point.
Definition y: State -> CR := snd ∘ point.

Definition r05: Range. exists ('0, '5); CRle_constants. Defined.
Definition r_1: OpenRange. exists (None, Some ('1)). simpl. auto. Defined.
Definition r01: Range. exists ('0, '1); CRle_constants. Defined.
Definition r12: Range. exists ('1, '2); CRle_constants. Defined.
Definition r23: Range. exists ('2, '3); CRle_constants. Defined.
Definition r34: Range. exists ('3, '4); CRle_constants. Defined.
Definition r45: Range. exists ('4, '5); CRle_constants. Defined.
Definition r4_: OpenRange. exists (Some ('4), None). simpl. trivial. Defined.
Definition r009: Range. exists ('0, '(9#10)); CRle_constants. Defined.
Definition r_09: OpenRange. exists (None, Some ('(9#10))). simpl. trivial. Defined.
Definition r415: Range. exists ('(41#10), '5); CRle_constants. Defined.
Definition r41_: OpenRange. exists (Some ('(41#10)), None). simpl. trivial. Defined.

(* Our invariant: *)

Definition world: OpenSquare := (r05: OpenRange, r05: OpenRange).
Definition invariant (s: State): Prop := in_osquare (point s) world.

Let PointCSetoid: CSetoid := ProdCSetoid CRasCSetoid CRasCSetoid.

Lemma invariant_wd: forall l l', l = l' ->
  forall (p p': PointCSetoid), p[=]p' ->
   (invariant (l, p) <-> invariant (l', p')).
Proof with auto.
  unfold invariant, in_osquare, in_orange, orange_left, orange_right.
  intros. subst l'. destruct p. destruct p'.
  simpl @fst. simpl @snd. inversion H0. simpl.
  rewrite H. rewrite H1. split...
Qed.

Definition invariant_squares (l: Location): OpenSquare := world.

Lemma invariant_squares_correct (l : Location) (p : Point):
  invariant (l, p) -> in_osquare p (invariant_squares l).
Proof. auto. Qed.

(* Our initial states: *)

Definition initial_square: OpenSquare := (r009: OpenRange, r05: OpenRange).
Definition initial_location := Up.
Definition initial (s: State): Prop :=
  loc s = initial_location /\ in_osquare (point s) initial_square.

Lemma invariant_initial s: initial s -> invariant s.
Proof with auto.
  destruct s. destruct p.
  unfold initial, invariant, in_osquare, in_orange.
  simpl. intros [A [[B C] [D E]]].
  split... split...
  unfold range_right in *. simpl in *.
  apply CRle_trans with ('(9#10))...
  CRle_constants.
Qed.

(* Our flow functions: *)

Definition xf (l: Location): Flow CRasCSetoid :=
  match l with
  | Up => c_flow.positive_linear.f 1
  | Right => c_flow.positive_linear.f 10
  | Down => c_flow.negative_linear.f 1
  | Left => c_flow.negative_linear.f 10
  end.

Definition x_flow_inv (l: Location) (a b: OpenRange): OpenRange :=
  match l with
  | Up => c_square_flow_conditions.one_axis.flow_range _ (c_flow.positive_linear.inv_correct 1) (c_flow.positive_linear.mono 1) a b
  | Right => c_square_flow_conditions.one_axis.flow_range _ (c_flow.positive_linear.inv_correct 10) (c_flow.positive_linear.mono 10) a b
  | Down => c_square_flow_conditions.one_axis.flow_range _ (c_flow.negative_linear.inv_correct 1) (c_flow.negative_linear.mono 1) a b
  | Left => c_square_flow_conditions.one_axis.flow_range _ (c_flow.negative_linear.inv_correct 10) (c_flow.negative_linear.mono 10) a b
  end.

Definition yf (l: Location): Flow CRasCSetoid :=
  match l with
  | Up => c_flow.positive_linear.f 10
  | Right => c_flow.negative_linear.f 1
  | Down => c_flow.negative_linear.f 10
  | Left => c_flow.positive_linear.f 1
  end.

Definition y_flow_inv (l: Location) (a b: OpenRange): OpenRange :=
  match l with
  | Up => c_square_flow_conditions.one_axis.flow_range _ (c_flow.positive_linear.inv_correct 10) (c_flow.positive_linear.mono 10) a b
  | Right => c_square_flow_conditions.one_axis.flow_range _ (c_flow.negative_linear.inv_correct 1) (c_flow.negative_linear.mono 1) a b
  | Down => c_square_flow_conditions.one_axis.flow_range _ (c_flow.negative_linear.inv_correct 10) (c_flow.negative_linear.mono 10) a b
  | Left => c_square_flow_conditions.one_axis.flow_range _ (c_flow.positive_linear.inv_correct 1) (c_flow.positive_linear.mono 1) a b
  end.

Lemma x_rfis l: range_flow_inv_spec (xf l) (x_flow_inv l).
Proof with auto.
  destruct l; simpl xf;
      unfold range_flow_inv_spec; intros;
      apply c_square_flow_conditions.one_axis.flow_range_covers with p...
Qed.

Lemma y_rfis l: range_flow_inv_spec (yf l) (y_flow_inv l).
Proof with auto.
  destruct l; simpl yf;
   unfold range_flow_inv_spec; intros;
   apply c_square_flow_conditions.one_axis.flow_range_covers with p...
Qed.

(* Next, our reset function: *)

Definition xreset (l l': Location) (x: CR): CR :=
  match l, l' with
  | Right, Down => x + '(1#10)
  | Left, Up => x - '(1#10)
  | _, _ => x
  end. (* todo: hm, either this adjustment should be necessary for all
    four discrete transitions, or for none at all.. *)

Definition yreset (l l': Location) (y: CR): CR :=
  match l, l' with
  | Up, Right => y + '(1#10)
  | Down, Left => y - '(1#10)
  | _, _ => y (* this is a superfluous clause *)
  end.

Definition reset (l l': Location) (p: Point): Point :=
  (xreset l l' (fst p), yreset l l' (snd p)).

(* .. whose components we show to increase: *)

Lemma xreset_inc l l': increasing (xreset l l').
Proof with auto.
  destruct l; destruct l'; unfold xreset, increasing...
    intros. apply t2...
  intros. apply t2...
Defined.

Lemma yreset_inc l l': increasing (yreset l l').
Proof with auto.
  destruct l; destruct l'; unfold yreset, increasing...
    intros. apply t2...
  intros. apply t2...
Defined.

(* Last but not least, we define the guard conditions: *)

Definition guard_square (l l': Location): option OpenSquare :=
  match l, l' with
  | Up, Right   => Some (open_square (r05, r415))
  | Right, Down => Some (open_square (r415, r05))
  | Down, Left  => Some (open_square (r05, r009))
  | Left, Up    => Some (open_square (r009, r05))
  | _, _ => None
  end.

Definition guard (s: State) (l: Location): Prop :=
  match guard_square (fst s) l with
  | None => False
  | Some q => in_osquare (snd s) q
  end.

(* Finally, we define our concrete system. *)

Definition concrete_system: c_concrete.System :=
  @c_concrete.Build_System PointCSetoid Location Location_eq_dec
  locations locations_complete NoDup_locations initial invariant
  invariant_initial invariant_wd
  (fun l => product_flow (xf l) (yf l)) guard reset.

(* Next, for the abstraction, we define our intervals. *)

Inductive Interval: Set := I01 | I12 | I23 | I34 | I45.

Definition Interval_eq_dec (i i': Interval): decision (i=i').
Proof. dec_eq. Defined.

Definition interval_bounds (i: Interval): OpenRange :=
  match i with
  | I01 => r01 | I12 => r12 | I23 => r23 | I34 => r34 | I45 => r45
  end.

Definition intervals: list Interval := I01 :: I12 :: I23 :: I34 :: I45 :: nil.

Lemma intervals_complete: forall i, List.In i intervals.
Proof. destruct i; compute; tauto. Qed.

Lemma NoDup_intervals: NoDup intervals.
  apply decision_true with (NoDup_dec Interval_eq_dec intervals).
  vm_compute. ref.
Qed.

Definition s_absInterval (r: CR):
  { i: Interval | in_orange r05 r -> in_orange (interval_bounds i) r }.
Proof with auto.
  intro.
  unfold in_orange, orange_left, orange_right.
  unfold r05.
  simpl.
  destruct (CR_le_le_dec r ('1)).
    exists I01. intros. destruct H. simpl. split...
  destruct (CR_le_le_dec r ('2)).
    exists I12. intros. destruct H. simpl. split...
  destruct (CR_le_le_dec r ('3)).
    exists I23. intros. destruct H. simpl. split...
  destruct (CR_le_le_dec r ('4)).
    exists I34. intros. destruct H. simpl. split...
  exists I45. intros. destruct H. simpl. split...
Defined.

Definition absInterval (r: CR): Interval := proj1_sig (s_absInterval r).

Lemma regions_cover_invariants l (p: c_concrete.Point concrete_system):
  c_concrete.invariant (l, p) ->
  c_square_abstraction.in_region interval_bounds interval_bounds p
    (c_square_abstraction.absInterval absInterval absInterval p).
Proof with auto.
  simpl c_concrete.invariant.
  destruct p.
  intros.
  unfold c_square_abstraction.in_region.
  unfold c_square_abstraction.absInterval.
  simpl.
  unfold absInterval.
  destruct (s_absInterval c). destruct (s_absInterval c0). simpl.
  destruct H.
  split...
Qed.

Let Region := c_square_abstraction.SquareInterval Interval Interval.

Definition guard_dec eps (ls : Location * Region * Location) :=
  let (lr, l2) := ls in
  let (l1, r) := lr in
    match guard_square l1 l2 with
    | Some s => osquares_overlap_dec eps (s,
        c_square_abstraction.square interval_bounds interval_bounds r)
    | None => false
    end.

Lemma over_guard eps : 
  guard_dec eps >=> c_square_abstraction.abstract_guard interval_bounds interval_bounds guard.
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
    Location_eq_dec interval_bounds interval_bounds Up initial_square eps.

Lemma over_initial eps : 
  initial_dec eps >=> 
  c_abstraction.initial_condition concrete_system
  (c_square_abstraction.in_region interval_bounds interval_bounds).
Proof with auto.
  apply c_square_abstraction.over_initial.
  intros. destruct s...
Qed.

Definition abstract_system (eps : Qpos) : c_abstract.System concrete_system.
Proof with auto.
  intro eps. eapply c_abstraction.abstract_system.
              eexact (c_square_abstraction.SquareInterval_eq_dec Interval_eq_dec Interval_eq_dec).
            eexact (c_square_abstraction.squareIntervals_complete _ intervals_complete _ intervals_complete).
          eexact (c_square_abstraction.NoDup_squareIntervals NoDup_intervals NoDup_intervals).
        eapply (@c_square_abstraction.do_cont_trans Location Interval Interval Location_eq_dec locations locations_complete interval_bounds interval_bounds xf yf x_flow_inv y_flow_inv).
              exact x_rfis.
            exact y_rfis.
          eexact invariant_squares_correct.
        exact eps.
      eapply c_square_abstraction.do_odisc_trans.
                eexact invariant_squares_correct.
              eexact xreset_inc.
            eexact yreset_inc.
          destruct p; ref.
        eexact (mk_DO (over_guard eps)).
      eexact eps.
    eexact (mk_DO (over_initial eps)).
  unfold c_abstraction.RegionsCoverInvariants.
  eexact regions_cover_invariants.
Defined.

Definition abs_sys := abstract_system (1#100).

Definition vs := abstract_as_graph.vertices abs_sys.
Definition g := abstract_as_graph.g abs_sys.
Definition graph := flat_map (@digraph.edges g) vs.
Time Eval vm_compute in (List.length graph).

Definition unsafe_abstract_states :=
  List.map (fun l => (l, (I23, I23))) locations.

(** Specification of what does it mean for the rotator example to be safe.
    It means that none of the abstract states in the list 
    [unsafe_abstract_states] is reachable. *)
Definition rotator_is_safe := 
  forall s : c_concrete.State concrete_system,
    let (l, p) := s in
    let (x, y) := p in
      List.In (l, (absInterval x, absInterval y)) unsafe_abstract_states ->
      ~c_concrete.reachable s.

Definition unsafe : bool :=
  abstract_as_graph.some_reachable abs_sys unsafe_abstract_states.

(** This theorem guarantees that validating in the extracted program that
    [unsafe = false], ensures that rotator is indeed safe. *)
Theorem unsafe_correct : unsafe = false -> rotator_is_safe.
Proof.
  unfold unsafe, rotator_is_safe. intros srf [l [px py]] su.
  apply abstract_as_graph.states_unreachable with 
    abs_sys unsafe_abstract_states (l, (absInterval px, absInterval py)); 
    trivial.
Qed.

(** Instead of validating this condition in the extracted program we can
    also do it directly in Coq (though it will be slower) *)
Theorem rotator_safe : rotator_is_safe.
Proof.
  Time apply unsafe_correct; vm_compute; ref.
Time Qed.

Print Assumptions rotator_safe.

(** We extract the program to verify safety of the rotator example. *)
(*Recursive Extraction unsafe.*)
 (* TODO: For this to work we need to make sure that the computations
    do not depend on lemmas using axioms. *)
