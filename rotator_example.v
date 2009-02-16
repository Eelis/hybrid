Require Import List.
Require Import util.
Require Import c_geometry.
Require Import c_monotonic_flow.
Require c_concrete.
Require abstract.
Require c_respect.
Require c_abstraction.
Require c_square_abstraction.
Require Import CRln.
Set Implicit Arguments.

Open Local Scope CR_scope.

Inductive Location: Set := Up | Right | Down | Left.

Definition Location_eq_dec (l l': Location): {l=l'}+{l<>l'}.
  destruct l; destruct l'; auto; right; discriminate.
Defined.

Definition locations: list Location := Up :: Right :: Down :: Left :: nil.

Lemma locations_complete l: In l locations.
Proof. destruct l; compute; tauto. Qed.

Let State: Type := prod Location Point.

Implicit Arguments fst [[A] [B]].
Implicit Arguments snd [[A] [B]].
  (* todo: move to util *)

Definition point: State -> Point := snd.
Definition loc: State -> Location := fst.
Definition x: State -> CR := compose fst point.
Definition y: State -> CR := compose snd point.

Definition initial (s: State): Prop := fst s = Up /\ snd s [=] ('0, '0).

Ltac CRle_constants := apply inject_Q_le; compute; discriminate.

Definition r05: Range.
  exists ('0, '5); CRle_constants.
Defined. (* for some reason Program Definition doesn't work here.. *)

Definition world: Square := (r05, r05).

Definition invariant (s: State): Prop := in_square (point s) world.

Definition invariant_squares (l: Location): Square := world.

Lemma invariant_squares_correct (l : Location) (p : Point):
  invariant (l, p) -> in_square p (invariant_squares l).
Proof. auto. Qed.

Lemma invariant_initial s: initial s -> invariant s.
Proof.
  destruct s. destruct p. unfold initial, invariant. simpl @fst. simpl @snd.
  intros. destruct H. subst l. inversion H0.
  unfold in_square, in_range, range_left, range_right.
  simpl @fst. simpl @snd.
  split.
    split; rewrite H; CRle_constants.
  split; rewrite H1; CRle_constants.
Qed.

Definition Xflow (l: Location) (x: CR) (t: Time): CR :=
  match l with
  | Up => x + t
  | Right => x + t+t
  | Down => x - t
  | Left => x - t-t
  end.

Definition Yflow (l: Location) (y: CR) (t: Time): CR :=
  match l with
  | Up => y + t+t
  | Right => y - t
  | Down => y - t-t
  | Left => y + t
  end.

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

Definition xf: Location -> Flow CRasCSetoid.
Proof with auto.
  intro l.
  apply (Build_Flow (xm l)); intros;
   simpl bsm; unfold Xflow; destruct l.
                apply CRadd_0_r.
              rewrite CRadd_0_r.
              apply CRadd_0_r.
            rewrite CRopp_Qopp.
            replace ((- 0)%Q) with 0...
            apply CRadd_0_r.
          rewrite CRopp_Qopp.
          replace ((- 0)%Q) with 0...
          rewrite CRadd_0_r.
          apply CRadd_0_r.
        apply (Radd_assoc CR_ring_theory).
      rewrite <- (Radd_assoc CR_ring_theory).
      rewrite <- (Radd_assoc CR_ring_theory).
      rewrite (Radd_assoc CR_ring_theory t').
      rewrite (Radd_comm CR_ring_theory t').
      rewrite (Radd_assoc CR_ring_theory x0).
      rewrite (Radd_assoc CR_ring_theory (x0 + t)).
      rewrite (Radd_assoc CR_ring_theory (x0 + t)).
      reflexivity.
    rewrite (@Ropp_add _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory ).
    apply (Radd_assoc CR_ring_theory).
  admit.
Defined.

Definition yf: Location -> Flow CRasCSetoid.
Proof with auto.
  intro l.
  apply (Build_Flow (ym l)); intros;
   simpl bsm; unfold Yflow; destruct l; admit.
Defined.

Lemma xflow_mono l: mono (xf l).
Proof with auto.
  unfold mono.
  destruct l; [left | left | right | right]; intros; intro; intros; simpl.
        apply t1_rev...
      admit.
    admit.
  admit.
Defined. (* all these admits are boring arithmetic *)

Lemma yflow_mono l: mono (yf l).
Proof with auto.
  unfold mono.
  destruct l; [left | right | right | left]; intros; intro; intros; simpl.
        admit.
      admit.
    admit.
  apply t1_rev...
Defined. (* all these admits are boring arithmetic *)

Definition x_flow_inv (l: Location) (x x': CR): Time :=
  match l with
  | Up => (x' - x)
  | Right => '(1#2) * (x' - x)
  | Down => x - x'
  | Left => '(1#2) * (x - x')
  end.

Definition y_flow_inv (l: Location) (y y': CR): Time :=
  match l with
  | Up => '(1#2) * (y' - y)
  | Right => y - y'
  | Down => '(1#2) * (y' - y)
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
      rewrite <- (Radd_assoc CR_ring_theory).
      rewrite <- (Rdistr_l CR_ring_theory).
      rewrite CRplus_Qplus.
      rewrite Qhalves_add_to_1.
      rewrite CRmult_1_l.
      symmetry. apply t11.
    rewrite (@Ropp_add _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory ).
    rewrite (@Ropp_opp _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory).
    rewrite (Radd_comm CR_ring_theory (-x0)).
    symmetry.
    apply t11.
  rewrite <- (Radd_assoc CR_ring_theory).
  admit.
Qed.

Lemma y_flow_inv_correct l y y': yf l y (y_flow_inv l y y') == y'.
Proof.
Admitted.

Definition xreset (l l': Location): CR -> CR := id.
Definition reset (l l': Location) (p: Point): Point := p.

Let PointCSetoid: CSetoid := ProdCSetoid CRasCSetoid CRasCSetoid.

Lemma invariant_wd: forall l l', l = l' -> forall (p p': PointCSetoid), p[=]p' ->
  (invariant (l, p) <-> invariant (l', p')).
Proof with auto.
  unfold invariant, in_square, in_range, range_left, range_right.
  intros. subst l'. destruct p. destruct p'.
  simpl @fst. simpl @snd. inversion H0.
  rewrite H. rewrite H1. split...
Qed.

Definition guard_square (l l': Location): option Square.
Proof.
  intros l l'.
  refine (match l, l' with
    | Up, Right   => Some (existT _ ('2, '5) _, existT _ ('0, '5) _)
    | Right, Down => Some (existT _ ('0, '5) _, existT _ ('0, '3) _)
    | Down, Left  => Some (existT _ ('0, '3) _, existT _ ('0, '5) _)
    | Left, Up    => Some (existT _ ('0, '5) _, existT _ ('2, '5) _)
    | _, _ => None
    end); CRle_constants.
Defined.
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

Definition concrete_system: c_concrete.System :=
  @c_concrete.Build_System PointCSetoid Location Location_eq_dec
  locations locations_complete initial invariant
  invariant_initial invariant_wd
  (fun l => product_flow (xf l) (yf l)) guard reset.

Inductive Interval: Set := I01 | I12 | I23 | I34 | I45.

Definition Interval_eq_dec (i i': Interval): {i=i'}+{i<>i'}.
  destruct i; destruct i'; auto; right; discriminate.
Defined.

Definition interval_bounds (i: Interval): Range.
Proof.
  intro i.
  destruct i.
          exists ('0, '1). CRle_constants.
        exists ('1, '2). CRle_constants.
      exists ('2, '3). CRle_constants.
    exists ('3, '4). CRle_constants.
  exists ('4, '5). CRle_constants.
Defined. (* for some reason Program Definition didn't work here.. *)

Definition intervals: list Interval := I01 :: I12 :: I23 :: I34 :: I45 :: nil.

Lemma intervals_complete: forall i, List.In i intervals.
Proof. destruct i; compute; tauto. Qed.

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

Definition absInterval (r: CR): Interval :=
  proj1_sig (s_absInterval r).

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
Qed.

Definition invariant_overestimation
  (ls: prod Location (c_square_abstraction.SquareInterval Interval Interval)): Prop
  := squares_overlap (invariant_squares (fst ls))
    (c_square_abstraction.square interval_bounds interval_bounds (snd ls)).


Definition guard_overestimation
  (ls: Location * c_square_abstraction.SquareInterval Interval Interval * Location): Prop
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
    apply weak_decision_to_opt_neg.
    unfold guard_overestimation.
    destruct guard_square.
      apply (squares_overlap_dec e).
    apply definitely_not.
    intro. assumption.
  unfold guard_overestimation.
  unfold c_square_abstraction.abstract_guard, guard.
  destruct u. destruct p.
  simpl @fst. simpl @snd.
  intros. destruct H. destruct H.
  destruct (guard_square l0 l)...
  apply squares_share_point with x0...
Defined.

Definition invariant_dec (e: Qpos):
  forall u,
  option
    (~ c_square_abstraction.abstract_invariant
     interval_bounds interval_bounds invariant u).
Proof with auto.
  intros.
  apply opt_neg_impl with (invariant_overestimation u).
    apply weak_decision_to_opt_neg.
    unfold invariant_overestimation.
    apply (squares_overlap_dec e).
  intros.
  unfold invariant_overestimation.
  unfold c_square_abstraction.abstract_invariant in H.
  destruct H.
  destruct H.
  apply squares_share_point with x0...
Defined.

Lemma increasing_id: increasing id.
Proof. unfold increasing. auto. Qed.

Definition component_reset (l l': Location): CR -> CR := id.

Lemma crinc l l': increasing (component_reset l l').
  intros.
  apply increasing_id.
Qed.

Lemma initial_dec u: option
  (~ c_abstraction.initial_condition concrete_system
     (c_square_abstraction.in_region interval_bounds interval_bounds) u).
Proof with auto.
  simpl.
  unfold c_abstraction.initial_condition.
  unfold c_concrete.initial.
  simpl.
  intros.
  unfold initial.
  destruct u.
  simpl.
  exact None. (* todo *)
Defined.
(*
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
*)

Definition abstract_system (e: Qpos):
  {s : abstract.System &
  {f : c_concrete.State concrete_system -> abstract.State s
     | c_respect.Respects s f } }.
Proof with auto.
  intro.
  apply (@c_abstraction.result concrete_system
    (c_square_abstraction.SquareInterval Interval Interval)
    (c_square_abstraction.SquareInterval_eq_dec Interval_eq_dec Interval_eq_dec)
    (c_square_abstraction.in_region interval_bounds interval_bounds)
    (c_square_abstraction.absInterval absInterval absInterval)
    (c_square_abstraction.squareIntervals intervals intervals)
    (c_square_abstraction.squareIntervals_complete _ intervals_complete _ intervals_complete)).
        exact (c_square_abstraction.cont_decider
         Location_eq_dec locations locations_complete xf yf x_flow_inv y_flow_inv
         x_flow_inv_correct y_flow_inv_correct xflow_mono yflow_mono
         initial invariant_initial guard reset (invariant_dec e)
         invariant_wd e).
      refine (c_square_abstraction.disc_decider Location_eq_dec
        locations locations_complete xf yf initial
       invariant_initial reset (invariant_dec e) invariant_wd
       xreset xreset crinc crinc _ _ e).
        destruct p. reflexivity.
      exact (guard_dec e).
    exact initial_dec.
  exact regions_cover_invariants.
Defined.

Let abs_sys: abstract.System := proj1_sigT _ _ (abstract_system ((1#100)%Qpos)).
Let abs_state := abstract.State abs_sys.
Definition initstate: abstract.State abs_sys := (Up, (I01, I12)).
Definition other_state: abstract.State abs_sys := (Up, (I12, I12)).

Eval vm_compute in (abstract.initial other_state).
(* Eval vm_compute in (abstract.states abs_sys).*)

Definition all_transitions: list (abs_state * abs_state) :=
  flat_map (fun s => map (pair s) (abstract.cont_trans s ++ abstract.disc_trans s))
   (abstract.states abs_sys).

Print Assumptions all_transitions.

(*
Eval vm_compute in length (all_transitions).

Set Printing Depth 10000.
Set Printing Width 1000000.

Eval vm_compute in all_transitions.
*)

(*
Set Extraction Optimize.
Set Extraction AutoInline.

Extraction Inline flat_map map app.

(* Extraction Language Haskell. *)
Extraction "generated_transitions" all_transitions.

Eval vm_compute in all_transitions.

Eval vm_compute in (abstract.cont_trans ((Up, (I01, I23)):abstract.State abs_sys)).

Print Assumptions abs_sys.
*)
