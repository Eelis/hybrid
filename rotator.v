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

Definition world: Square := (r05, r05).
Definition oworld: OpenSquare := unbounded_square.
Definition invariant (s: State): Prop := in_square (point s) world.
Definition oinvariant (s: State): Prop := True.

Let PointCSetoid: CSetoid := ProdCSetoid CRasCSetoid CRasCSetoid.

Lemma invariant_wd: forall l l', l = l' ->
  forall (p p': PointCSetoid), p[=]p' ->
   (invariant (l, p) <-> invariant (l', p')).
Proof with auto.
  unfold invariant, in_square, in_range, range_left, range_right.
  intros. subst l'. destruct p. destruct p'.
  simpl @fst. simpl @snd. inversion H0. simpl.
  rewrite H. rewrite H1. split...
Qed.

Lemma oinvariant_wd: forall l l', l = l' ->
  forall (p p': PointCSetoid), p[=]p' ->
   (oinvariant (l, p) <-> oinvariant (l', p')).
Proof. split; trivial. Qed.

Definition invariant_squares (l: Location): Square := world.
Definition oinvariant_squares (l: Location): OpenSquare := unbounded_square.

Lemma invariant_squares_correct (l : Location) (p : Point):
  invariant (l, p) -> in_square p (invariant_squares l).
Proof. auto. Qed. (* todo: is this stuff still necessary? *)

Lemma oinvariant_squares_correct (l : Location) (p : Point):
  oinvariant (l, p) -> in_osquare p (oinvariant_squares l).
Proof. intros. apply in_unbounded_square. Qed.

(* Our initial states: *)

Definition initial_square: Square := (r009, r05).
Definition initial_osquare: OpenSquare := (r_09, unbounded_range).
Definition initial_location := Up.
Definition initial (s: State): Prop :=
  loc s = initial_location /\ in_square (point s) initial_square.

Definition oinitial (s: State): Prop :=
  loc s = initial_location /\ in_osquare (point s) initial_osquare.

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
Qed.

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

Definition guard_square (l l': Location): option Square :=
  match l, l' with
  | Up, Right   => Some (r05, r415)
  | Right, Down => Some (r415, r05)
  | Down, Left  => Some (r05, r009)
  | Left, Up    => Some (r009, r05)
  | _, _ => None
  end.

Definition guard_osquare (l l': Location): option OpenSquare :=
  match l, l' with
  | Up, Right   => Some (unbounded_range, r41_)
  | Right, Down => Some (r41_, unbounded_range)
  | Down, Left  => Some (unbounded_range, r_09)
  | Left, Up    => Some (r_09, unbounded_range)
  | _, _ => None
  end.

Definition guard (s: State) (l: Location): Prop :=
  match guard_square (fst s) l with
  | None => False
  | Some q => in_square (snd s) q
  end.

Definition oguard (s: State) (l: Location): Prop :=
  match guard_osquare (fst s) l with
  | None => False
  | Some q => in_osquare (snd s) q
  end.

(* Finally, we define our concrete system. *)

Definition concrete_system: c_concrete.System :=
  @c_concrete.Build_System PointCSetoid Location Location_eq_dec
  locations locations_complete NoDup_locations initial invariant
  invariant_initial invariant_wd
  (fun l => product_flow (xf l) (yf l)) guard reset.

Definition oconcrete_system: c_concrete.System :=
  @c_concrete.Build_System PointCSetoid Location Location_eq_dec
  locations locations_complete NoDup_locations oinitial oinvariant
  (fun _ _ => I) oinvariant_wd
  (fun l => product_flow (xf l) (yf l)) oguard reset.

(* Next, for the abstraction, we define our intervals. *)

Inductive Interval: Set := I01 | I12 | I23 | I34 | I45.

Inductive OInterval: Set := OI_1 | OI12 | OI23 | OI34 | OI4_.

Definition Interval_eq_dec (i i': Interval): decision (i=i').
Proof. dec_eq. Defined.

Definition OInterval_eq_dec (i i': OInterval): decision (i=i').
Proof. dec_eq. Defined.

Definition interval_bounds (i: Interval): Range :=
  match i with
  | I01 => r01 | I12 => r12 | I23 => r23 | I34 => r34 | I45 => r45
  end.

Definition ointerval_bounds (i: OInterval): OpenRange :=
  match i with
  | OI_1 => r_1 | OI12 => r12 | OI23 => r23 | OI34 => r34 | OI4_ => r4_
  end.

Definition intervals: list Interval := I01 :: I12 :: I23 :: I34 :: I45 :: nil.
Definition ointervals: list OInterval := OI_1 :: OI12 :: OI23 :: OI34 :: OI4_ :: nil.

Lemma intervals_complete: forall i, List.In i intervals.
Proof. destruct i; compute; tauto. Qed.

Lemma ointervals_complete: forall i, List.In i ointervals.
Proof. destruct i; compute; tauto. Qed.

Lemma NoDup_intervals: NoDup intervals.
  apply decision_true with (NoDup_dec Interval_eq_dec intervals).
  vm_compute. ref.
Qed.

Lemma NoDup_ointervals: NoDup ointervals.
  apply decision_true with (NoDup_dec OInterval_eq_dec ointervals).
  vm_compute. ref.
Qed.

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

Definition s_oabsInterval (r: CR):
  { i: OInterval | in_orange (ointerval_bounds i) r }.
Proof with auto.
  intro.
  unfold in_orange, orange_left, orange_right.
  destruct (CR_le_le_dec r ('1)). exists OI_1. simpl...
  destruct (CR_le_le_dec r ('2)). exists OI12...
  destruct (CR_le_le_dec r ('3)). exists OI23...
  destruct (CR_le_le_dec r ('4)). exists OI34...
  exists OI4_. simpl...
Defined.

Definition absInterval (r: CR): Interval := proj1_sig (s_absInterval r).
Definition oabsInterval (r: CR): OInterval := proj1_sig (s_oabsInterval r).

Lemma regions_cover_invariants l (p: c_concrete.Point concrete_system):
  c_concrete.invariant (l, p) ->
  c_square_abstraction.in_region interval_bounds interval_bounds p
    (c_square_abstraction.absInterval absInterval absInterval p).
Proof with auto.
  simpl c_concrete.invariant.
  destruct p.
  intros.
  unfold absInterval. simpl.
  destruct (s_absInterval c). destruct (s_absInterval c0). simpl.
  destruct H...
Qed.

Lemma oregions_cover_invariants l (p: c_concrete.Point oconcrete_system):
  c_concrete.invariant (l, p) ->
  c_square_abstraction.in_oregion ointerval_bounds ointerval_bounds p
    (c_square_abstraction.absInterval oabsInterval oabsInterval p).
Proof with auto.
  simpl c_concrete.invariant.
  destruct p.
  intros.
  unfold c_square_abstraction.in_oregion.
  unfold c_square_abstraction.absInterval.
  simpl.
  unfold oabsInterval.
  destruct (s_oabsInterval c). destruct (s_oabsInterval c0). simpl.
  split...
Qed.

Let Region := c_square_abstraction.SquareInterval Interval Interval.
Let ORegion := c_square_abstraction.SquareInterval OInterval OInterval.

Definition guard_overestimation (ls : Location * Region * Location) : Prop :=
  let (lr, l2) := ls in
  let (l1, r) := lr in
    match guard_square l1 l2 with
    | Some s => squares_overlap (s, 
        c_square_abstraction.square interval_bounds interval_bounds r)
    | None => False
    end.

Definition oguard_overestimation (ls : Location * ORegion * Location) : Prop :=
  let (lr, l2) := ls in
  let (l1, r) := lr in
    match guard_osquare l1 l2 with
    | Some s => osquares_overlap (s, 
        c_square_abstraction.osquare ointerval_bounds ointerval_bounds r)
    | None => False
    end.

Definition guard_dec eps (ls : Location * Region * Location) :=
  let (lr, l2) := ls in
  let (l1, r) := lr in
    match guard_square l1 l2 with
    | Some s => squares_overlap_dec eps (s,
        c_square_abstraction.square interval_bounds interval_bounds r)
    | None => false
    end.

Definition oguard_dec eps (ls : Location * ORegion * Location) :=
  let (lr, l2) := ls in
  let (l1, r) := lr in
    match guard_osquare l1 l2 with
    | Some s => osquares_overlap_dec eps (s,
        c_square_abstraction.osquare ointerval_bounds ointerval_bounds r)
    | None => false
    end.

Lemma over_guard eps : 
  guard_dec eps >=> c_square_abstraction.abstract_guard interval_bounds interval_bounds guard.
Proof with auto.
  intros eps [[l r] l'] gf [p [in_p g]].
  unfold guard_dec in gf. unfold guard in g.
  simpl @fst in *. simpl @snd in *.  
  destruct (guard_square l l'); try contradiction.
  apply (over_squares_overlap eps _ gf).
  apply squares_share_point with p...
Qed.

Lemma over_oguard eps : 
  oguard_dec eps >=> c_square_abstraction.abstract_oguard ointerval_bounds ointerval_bounds oguard.
Proof with auto.
  intros eps [[l r] l'] gf [p [in_p g]].
  unfold oguard_dec in gf. unfold oguard in g.
  simpl @fst in *. simpl @snd in *.  
  destruct (guard_osquare l l'); try contradiction.
  apply (over_osquares_overlap eps gf).
  apply osquares_share_point with p...
Qed.

Definition abs_invariant eps :=
  c_square_abstraction.do_invariant interval_bounds interval_bounds invariant invariant_squares eps.

Definition invariant_dec eps :=
  c_square_abstraction.invariant_dec interval_bounds interval_bounds
    invariant_squares eps.

Definition initial_dec eps :=
  c_square_abstraction.initial_dec (Location:=Location) 
    Location_eq_dec interval_bounds interval_bounds Up initial_square eps.

Definition oinitial_dec eps :=
  c_square_abstraction.oinitial_dec (Location:=Location) 
    Location_eq_dec ointerval_bounds ointerval_bounds Up initial_osquare eps.

Lemma over_initial eps : 
  initial_dec eps >=> 
  c_abstraction.initial_condition concrete_system 
  (c_square_abstraction.in_region interval_bounds interval_bounds).
Proof with auto.
  apply c_square_abstraction.over_initial.
  intros. destruct s... 
Qed.

Lemma over_oinitial eps : 
  oinitial_dec eps >=> 
  c_abstraction.initial_condition oconcrete_system 
  (c_square_abstraction.in_oregion ointerval_bounds ointerval_bounds).
Proof with auto.
  apply c_square_abstraction.over_oinitial.
  intros. destruct s...
Qed.

Definition oabstract_system (eps : Qpos) : c_abstract.System oconcrete_system.
Proof.
  intro eps. eapply c_abstraction.abstract_system.
              eexact (c_square_abstraction.SquareInterval_eq_dec OInterval_eq_dec OInterval_eq_dec).
            eexact (c_square_abstraction.squareIntervals_complete _ ointervals_complete _ ointervals_complete).
          eexact (c_square_abstraction.NoDup_squareIntervals NoDup_ointervals NoDup_ointervals).
        eapply (@c_square_abstraction.do_ocont_trans Location OInterval OInterval Location_eq_dec locations locations_complete ointerval_bounds ointerval_bounds xf yf x_flow_inv y_flow_inv).
                    (**)
                    eexact x_flow_inv_correct.
                  eexact y_flow_inv_correct.
                eexact xflow_mono.
              eexact yflow_mono.
            eexact (fun _: Location => world). (* silly *)
          eexact oinvariant_squares_correct.
        exact eps.
      eapply c_square_abstraction.do_odisc_trans.
                eexact oinvariant_squares_correct.
              eexact xreset_inc.
            eexact yreset_inc.
          destruct p; ref.
        eexact (mk_DO (over_oguard eps)).
      eexact eps.
    eexact (mk_DO (over_oinitial eps)).
  unfold c_abstraction.RegionsCoverInvariants.
  eexact oregions_cover_invariants.
Defined.

Definition abstract_system (eps : Qpos) : c_abstract.System concrete_system.
Proof.
  intro eps. eapply c_abstraction.abstract_system.
              eexact (c_square_abstraction.SquareInterval_eq_dec Interval_eq_dec Interval_eq_dec).
            eexact (c_square_abstraction.squareIntervals_complete _ intervals_complete _ intervals_complete).
          eexact (c_square_abstraction.NoDup_squareIntervals NoDup_intervals NoDup_intervals).
        eapply (@c_square_abstraction.do_cont_trans Location Interval Interval Location_eq_dec locations locations_complete interval_bounds interval_bounds xf yf x_flow_inv y_flow_inv).
                    eexact x_flow_inv_correct.
                  eexact y_flow_inv_correct.
                eexact xflow_mono.
              eexact yflow_mono.
            eexact invariant_squares_correct.
          exact (fun _ => unbounded_square). (* silly *)
        eexact eps.
      eapply c_square_abstraction.do_disc_trans.
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
Definition oabs_sys := oabstract_system (1#100).

Definition vs := abstract_as_graph.vertices abs_sys.
Definition ovs := abstract_as_graph.vertices oabs_sys.
Definition g := abstract_as_graph.g abs_sys.
Definition og := abstract_as_graph.g oabs_sys.
Definition graph := flat_map (@digraph.edges g) vs.
Definition ograph := flat_map (@digraph.edges og) ovs.
Time Eval vm_compute in (List.length graph).

Definition unsafe_abstract_states :=
  List.map (fun l => (l, (I23, I23))) locations.
Definition unsafe_oabstract_states :=
  List.map (fun l => (l, (OI23, OI23))) locations.

(** Specification of what does it mean for the rotator example to be safe.
    It means that none of the abstract states in the list 
    [unsafe_abstract_states] is reachable. *)
Definition rotator_is_safe := 
  forall s : c_concrete.State concrete_system,
    let (l, p) := s in
    let (x, y) := p in
      List.In (l, (absInterval x, absInterval y)) unsafe_abstract_states ->
      ~c_concrete.reachable s.

Definition orotator_is_safe := 
  forall s : c_concrete.State oconcrete_system,
    let (l, p) := s in
    let (x, y) := p in
      List.In (l, (oabsInterval x, oabsInterval y)) unsafe_oabstract_states ->
      ~c_concrete.reachable s.

Definition unsafe : bool :=
  abstract_as_graph.some_reachable abs_sys unsafe_abstract_states.

Definition ounsafe : bool :=
  abstract_as_graph.some_reachable oabs_sys unsafe_oabstract_states.

(** This theorem guarantees that validating in the extracted program that
    [unsafe = false], ensures that rotator is indeed safe. *)
Theorem unsafe_correct : unsafe = false -> rotator_is_safe.
Proof.
  unfold unsafe, rotator_is_safe. intros srf [l [px py]] su.
  apply abstract_as_graph.states_unreachable with 
    abs_sys unsafe_abstract_states (l, (absInterval px, absInterval py)); 
    trivial.
Qed.

Theorem ounsafe_correct : ounsafe = false -> orotator_is_safe.
Proof.
  unfold ounsafe, orotator_is_safe. intros srf [l [px py]] su.
  apply abstract_as_graph.states_unreachable with 
    oabs_sys unsafe_oabstract_states (l, (oabsInterval px, oabsInterval py)); 
    trivial.
Qed.

(** Instead of validating this condition in the extracted program we can
    also do it directly in Coq (though it will be slower) *)
Theorem rotator_safe : rotator_is_safe.
Proof.
  Time apply unsafe_correct; vm_compute; ref.
Time Qed.

(* hm, the orotator isn't actually safe, because the infinite boundaries now provide
plenty of space for the slight flow skewage to make the center reachable :-( *)

(*
Theorem orotator_safe : orotator_is_safe.
Proof.
  Time apply ounsafe_correct; vm_compute; ref.
Time Qed.
*)

Print Assumptions rotator_safe.

(** We extract the program to verify safety of the rotator example. *)
(*Recursive Extraction unsafe.*)
 (* TODO: For this to work we need to make sure that the computations
    do not depend on lemmas using axioms. *)
