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
Proof. destruct l; destruct l'; auto; right; discriminate. Defined.

Definition locations: list Location := Up :: Right :: Down :: Left :: nil.

Lemma NoDup_locations: NoDup locations.
  apply decision_true with (NoDup_dec Location_eq_dec locations).
  vm_compute. reflexivity.
Qed.

Lemma locations_complete l: In l locations.
Proof. destruct l; compute; tauto. Qed.

Let State: Type := prod Location Point.

Definition point: State -> Point := snd.
Definition loc: State -> Location := fst.
Definition x: State -> CR := fst ∘ point.
Definition y: State -> CR := snd ∘ point.

Definition r05: Range. exists ('0, '5); CRle_constants. Defined.
Definition r01: Range. exists ('0, '1); CRle_constants. Defined.
Definition r12: Range. exists ('1, '2); CRle_constants. Defined.
Definition r23: Range. exists ('2, '3); CRle_constants. Defined.
Definition r34: Range. exists ('3, '4); CRle_constants. Defined.
Definition r45: Range. exists ('4, '5); CRle_constants. Defined.
Definition r009: Range. exists ('0, '(9#10)); CRle_constants. Defined.
Definition r415: Range. exists ('(41#10), '5); CRle_constants. Defined.

(* Our invariant: *)

Definition world: Square := (r05, r05).
Definition invariant (s: State): Prop := in_square (point s) world.

Let PointCSetoid: CSetoid := ProdCSetoid CRasCSetoid CRasCSetoid.

Lemma invariant_wd: forall l l', l = l' ->
  forall (p p': PointCSetoid), p[=]p' ->
   (invariant (l, p) <-> invariant (l', p')).
Proof with auto.
  unfold invariant, in_square, in_range, range_left, range_right.
  intros. subst l'. destruct p. destruct p'.
  simpl @fst. simpl @snd. inversion H0.
  rewrite H. rewrite H1. split...
Defined.

Definition invariant_squares (l: Location): Square := world.

Lemma invariant_squares_correct (l : Location) (p : Point):
  invariant (l, p) -> in_square p (invariant_squares l).
Proof. auto. Qed. (* todo: is this stuff still necessary? *)

(* Our initial states: *)

Definition initial_square := (r009, r05).
Definition initial_location := Up.
Definition initial (s: State): Prop :=
  loc s = initial_location /\ in_square (point s) initial_square.

Lemma invariant_initial s: initial s -> invariant s.
Proof with auto.
  destruct s. destruct p.
  unfold initial, invariant, in_square, in_range.
  simpl. intros [A [[B C] [D E]]].
  split... split...
  unfold range_right in *. simpl in *.
  apply CRle_trans with ('(9#10))...
  CRle_constants.
Qed.

(* Our flow functions: *)

Definition Xflow (l: Location) (x: CR) (t: Time): CR :=
  match l with
  | Up => x + t
  | Right => x + '10*t
  | Down => x - t
  | Left => x - '10*t
  end.

Definition Yflow (l: Location) (y: CR) (t: Time): CR :=
  match l with
  | Up => y + '10*t
  | Right => y - t
  | Down => y - '10*t
  | Left => y + t
  end.

(* .. which we now show to be morphisms over CR: *)

Definition xm: Location ->
  binary_setoid_morphism CRasCSetoid CRasCSetoid CRasCSetoid.
Proof.
  intro l. apply (Build_binary_setoid_morphism _ _ _ (Xflow l)).
  intros. unfold Xflow.
  destruct l; try auto; rewrite H; rewrite H0; reflexivity.
Defined.

Definition ym: Location ->
  binary_setoid_morphism CRasCSetoid CRasCSetoid CRasCSetoid.
Proof.
  intro l. apply (Build_binary_setoid_morphism _ _ _ (Yflow l)).
  intros. unfold Yflow.
  destruct l; try auto; rewrite H; rewrite H0; reflexivity.
Defined.

(* .. and then show to satisfy the flow identities: *)

Definition xf: Location -> Flow CRasCSetoid.
Proof with auto.
  intro l.
  apply (Build_Flow (xm l)); intros;
   simpl bsm; unfold Xflow; destruct l.
                apply CRadd_0_r.
              rewrite CRmult_0_r.
              apply CRadd_0_r.
            rewrite CRopp_0.
            apply CRadd_0_r.
          rewrite CRmult_0_r.
          rewrite CRopp_0.
          apply CRadd_0_r.
        apply (Radd_assoc CR_ring_theory).
      rewrite (Rmul_comm CR_ring_theory).
      rewrite (Rdistr_l CR_ring_theory).
      rewrite (Radd_assoc CR_ring_theory).
      repeat rewrite (Rmul_comm CR_ring_theory ('10)).
      reflexivity.
    rewrite (@Ropp_add _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory ).
    apply (Radd_assoc CR_ring_theory).
  rewrite <- (Radd_assoc CR_ring_theory).
  do 2 rewrite (Radd_comm CR_ring_theory x0).
  apply add_both_sides.
  do 3 rewrite CRopp_mult_l.
  repeat rewrite (Rmul_comm CR_ring_theory (-'10)).
  apply (Rdistr_l CR_ring_theory).
Defined.

Definition yf: Location -> Flow CRasCSetoid.
Proof.
  intro l.
  apply (Build_Flow (ym l)); intros;
   simpl bsm; unfold Yflow; destruct l.
                rewrite CRmult_0_r.
                apply CRadd_0_r.
              rewrite CRopp_0.
              apply CRadd_0_r.
            rewrite CRmult_0_r.
            rewrite CRopp_0.
            apply CRadd_0_r.
          apply CRadd_0_r.
        rewrite CRmult_comm.
        rewrite (Rdistr_l CR_ring_theory).
        rewrite (Radd_assoc CR_ring_theory).
        repeat rewrite (Rmul_comm CR_ring_theory ('10)).
        reflexivity.
      rewrite (@Ropp_add _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory ).
      rewrite (Radd_assoc CR_ring_theory).
      reflexivity.
    do 3 rewrite CRopp_mult_l.
    repeat rewrite (Rmul_comm CR_ring_theory (-'10)).
    rewrite (Rdistr_l CR_ring_theory).
    rewrite (Radd_assoc CR_ring_theory).
    reflexivity.
  apply (Radd_assoc CR_ring_theory).
Defined.

(* .. and then show to be monotonic: *)

Lemma xflow_mono l: mono (xf l).
Proof with auto.
  unfold mono.
  destruct l; [left | left | right | right]; intros; intro; intros; simpl.
        apply t1_rev...
      apply t1_rev.
      apply CRmult_lt_pos_r...
      apply positive_CRpos.
    apply t1_rev.
    apply CRlt_opp_compat...
  apply t1_rev.
  apply CRlt_opp_compat.
  apply CRmult_lt_pos_r...
  apply positive_CRpos.
Defined.

Lemma yflow_mono l: mono (yf l).
Proof with auto.
  unfold mono.
  destruct l; [left | right | right | left]; intros; intro; intros; simpl.
        apply t1_rev.
        apply CRmult_lt_pos_r...
        apply positive_CRpos.
      apply t1_rev.
      apply CRlt_opp_compat...
    apply t1_rev.
    apply CRlt_opp_compat...
    apply CRmult_lt_pos_r...
    apply positive_CRpos.
   apply t1_rev...
 Defined.

(* .. and then show to have inverses: *)

Definition x_flow_inv (l: Location) (x x': CR): Time :=
  match l with
  | Up => (x' - x)
  | Right => '(1#10) * (x' - x)
  | Down => x - x'
  | Left => '(1#10) * (x - x')
  end.

Definition y_flow_inv (l: Location) (y y': CR): Time :=
  match l with
  | Up => '(1#10) * (y' - y)
  | Right => y - y'
  | Down => '(1#10) * (y - y')
  | Left => y' - y
  end.

Lemma x_flow_inv_correct l x x': xf l x (x_flow_inv l x x') == x'.
Proof.
  simpl bsm.
  unfold Xflow, x_flow_inv.
  intros.
  destruct l.
        symmetry.
        apply t11.
      rewrite (Rmul_assoc CR_ring_theory).
      rewrite CRmult_Qmult.
      rewrite Qmult_inv.
        rewrite (Rmul_1_l CR_ring_theory).
        symmetry. apply t11.
      reflexivity.
    rewrite <- diff_opp.
    symmetry. apply t11.
  rewrite (Rmul_assoc CR_ring_theory).
  rewrite CRmult_Qmult.
  rewrite Qmult_inv.
    rewrite (Rmul_1_l CR_ring_theory).
    rewrite <- diff_opp.
    symmetry. apply t11.
  reflexivity.
Defined.

Lemma y_flow_inv_correct l y y': yf l y (y_flow_inv l y y') == y'.
Proof.
  simpl bsm. unfold Yflow, y_flow_inv. intros. destruct l.
        rewrite (Rmul_assoc CR_ring_theory).
        rewrite CRmult_Qmult.
        rewrite Qmult_inv.
          rewrite (Rmul_1_l CR_ring_theory).
          symmetry. apply t11.
        reflexivity.
      rewrite <- diff_opp.
      symmetry. apply t11.
    rewrite (Rmul_assoc CR_ring_theory).
    rewrite CRmult_Qmult.
    rewrite Qmult_inv.
      rewrite (Rmul_1_l CR_ring_theory).
      rewrite <- diff_opp.
      symmetry. apply t11.
    reflexivity.
  symmetry. apply t11.
Defined.

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

Definition guard_square (l l': Location): option Square :=
  match l, l' with
  | Up, Right   => Some (r05, r415)
  | Right, Down => Some (r415, r05)
  | Down, Left  => Some (r05, r009)
  | Left, Up    => Some (r009, r05)
  | _, _ => None
  end.

  (* this is a squarified version of the guard. here's what we really
  want (and what we should get back if we generalize the theorems
  to work with squares with optional bounds): *)
  (*
  Definition guard (s: State) (l: Location): Prop :=
    match loc s, l with
    | Up, Right   => '2 <= x s
    | Right, Down => y s <= '3
    | Down, Left  => x s <= '3
    | Left, Up    => '2 <= y s
    | _, _ => False
    end.
  *)

Definition guard (s: State) (l: Location): Prop :=
  match guard_square (fst s) l with
  | None => False
  | Some q => in_square (snd s) q
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
Proof. destruct i; destruct i'; auto; right; discriminate. Defined.

Definition interval_bounds (i: Interval): Range :=
  match i with
  | I01 => r01 | I12 => r12 | I23 => r23 | I34 => r34 | I45 => r45
  end.

Definition intervals: list Interval := I01 :: I12 :: I23 :: I34 :: I45 :: nil.

Lemma intervals_complete: forall i, List.In i intervals.
Proof. destruct i; compute; tauto. Qed.

Lemma NoDup_intervals: NoDup intervals.
  apply decision_true with (NoDup_dec Interval_eq_dec intervals).
  vm_compute. reflexivity.
Defined.

Definition s_absInterval (r: CR):
  { i: Interval | in_range r05 r -> in_range (interval_bounds i) r }.
Proof with auto.
  intro.
  unfold in_range, range_left, range_right.
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
  unfold c_square_abstraction.in_region.
  unfold invariant, in_square, in_range, range_left, range_right.
  destruct p.
  simpl @fst. simpl @snd.
  intros.
  unfold absInterval.
  destruct (s_absInterval c). destruct (s_absInterval c0). simpl.
  destruct H.
  split.
    apply i...
  apply i0...
Defined.

Let Region := c_square_abstraction.SquareInterval Interval Interval.

Definition guard_overestimation
  (ls: Location * Region * Location): Prop
  := match guard_square (fst (fst ls)) (snd ls) with
  | Some s => squares_overlap s
     (c_square_abstraction.square interval_bounds interval_bounds (snd (fst ls)))
  | None => False
  end.

Definition guard_dec (e: Qpos) u:
  option (~ c_square_abstraction.abstract_guard interval_bounds interval_bounds guard u).
Proof with auto.
  intros.
  apply opt_neg_impl with (guard_overestimation u).
    unfold guard_overestimation.
    unfold c_square_abstraction.abstract_guard, guard.
    destruct u. destruct p.
    simpl @fst. simpl @snd.
    intros. destruct H. destruct H.
    destruct (guard_square l0 l)...
    apply squares_share_point with x0...
  apply weak_decision_to_opt_neg.
  unfold guard_overestimation.
  destruct guard_square.
    apply (squares_overlap_dec e).
  apply definitely_not.
  intro. assumption.
Defined.

Definition invariant_dec: Qpos -> forall u,
  option (~ c_square_abstraction.abstract_invariant
     interval_bounds interval_bounds invariant u) :=
  c_square_abstraction.invariant_dec
    interval_bounds interval_bounds invariant invariant_squares
    invariant_squares_correct.

Lemma initial_representative (p : c_concrete.State concrete_system):
 c_concrete.initial p ->
  fst p = initial_location /\ in_square (snd p) initial_square.
Proof. auto. Qed.

Definition initial_dec: forall u, option
  (~ c_abstraction.initial_condition concrete_system
     (c_square_abstraction.in_region interval_bounds interval_bounds) u)
  := c_square_abstraction.initial_dec interval_bounds interval_bounds xf yf initial_representative.

Definition abstract_system (e: Qpos): c_abstract.System concrete_system.
Proof with auto.
  intro.
  apply (@c_abstraction.abstract_system concrete_system
    (c_square_abstraction.SquareInterval Interval Interval)
    (c_square_abstraction.SquareInterval_eq_dec Interval_eq_dec Interval_eq_dec)
    (c_square_abstraction.in_region interval_bounds interval_bounds)
    (c_square_abstraction.squareIntervals intervals intervals)
    (c_square_abstraction.squareIntervals_complete _ intervals_complete _ intervals_complete)
    (c_square_abstraction.NoDup_squareIntervals NoDup_intervals NoDup_intervals)
    (c_square_abstraction.absInterval absInterval absInterval)).
        exact (c_square_abstraction.cont_decider
         Location_eq_dec locations_complete xf yf x_flow_inv y_flow_inv
         x_flow_inv_correct y_flow_inv_correct xflow_mono yflow_mono
         initial invariant_initial guard reset (invariant_dec e)
         invariant_wd NoDup_locations e).
      refine (c_square_abstraction.disc_decider Location_eq_dec
        locations_complete xf yf initial
       invariant_initial reset (invariant_dec e) invariant_wd
       NoDup_locations xreset yreset xreset_inc yreset_inc _ _ e).
        destruct p. reflexivity.
      exact (guard_dec e).
    exact initial_dec.
  exact regions_cover_invariants.
Defined.

Definition abs_sys := abstract_system (1#100).

Definition unsafe_abstract_state:
  c_abstract.State concrete_system (c_abstract.Region abs_sys)
  := (Up, (I23, I23)).

Theorem safe (p: c_concrete.Point concrete_system):
  absInterval (fst p) = I23 -> absInterval (snd p) = I23 ->
   ~ c_concrete.reachable (Up: c_concrete.Location concrete_system, p).
Proof with auto.
  cut (forall s : c_concrete.State concrete_system,
     (fst s, (absInterval (fst (snd s)), absInterval (snd (snd s)))) =
     unsafe_abstract_state -> ~ c_concrete.reachable s).
    intros.
    apply H.
    simpl @fst. simpl @snd.
    simpl in *.
    rewrite H0. rewrite H1. reflexivity.
  apply semidec_true with (abstract_as_graph.semidecide_reachable2 abs_sys (Up, (I23, I23))).
  vm_compute...
Qed.
  (* note: the time to compute the above currently appears to be
   linear in the amount of initial abstract states, which should be
   easy to fix *)

Print Assumptions safe.
